(**************************************************************************)
(*                                                                        *)
(*                              OCamlPro TypeRex                          *)
(*                                                                        *)
(*   Copyright OCamlPro 2011-2016. All rights reserved.                   *)
(*   This file is distributed under the terms of the GPL v3.0             *)
(*      (GNU Public Licence version 3.0).                                 *)
(*                                                                        *)
(*     Contact: <typerex@ocamlpro.com> (http://www.ocamlpro.com/)         *)
(*                                                                        *)
(*  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,       *)
(*  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES       *)
(*  OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND              *)
(*  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS   *)
(*  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN    *)
(*  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN     *)
(*  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE      *)
(*  SOFTWARE.                                                             *)
(**************************************************************************)


open StringCompat

(* LLDB API *)
open LLDBEnums
open LLDBOCaml

(* ocp-lldb modules *)
open LLDBTypes
open LLDBGlobals

open Longident
open Path
open Types

#ifndef OCAML_NON_OCP
open StringCompat
open GcprofTypes
#endif

let max_indent = ref 10

(*verbose flag*)
let vf = ref false

let tydecl_tbl = ref @@ Hashtbl.create 100

let string_of_tag tag =
  match tag with
  | 246 -> "lazy"
  | 247 -> "closure"
  | 248 -> "object"
  | 249 -> "infix"
  | 250 -> "forward"
  | 251 -> "abstract"
  | 252 -> "string"
  | 253 -> "double"
  | 254 -> "double[]"
  | 255 -> "custom"
  | _ -> "value"


(* Print a constructor or label, giving it the same prefix as the type
   it comes from. Attempt to omit the prefix if the type comes from
   a module that has been opened. *)

let tree_of_qualified lookup_fun env ty_path name =
  match ty_path with
  | Pident id ->
    name
  | Pdot(p, s, pos) ->
    if try
         match (lookup_fun (Lident name) env).desc with
         | Tconstr(ty_path', _, _) -> Path.same ty_path ty_path'
         | _ -> false
      with Not_found -> false
        then name
        else Printf.sprintf "%s.%s" (Path.name p) name
      | Papply _ -> Path.name ty_path

    let tree_of_constr =
      tree_of_qualified
        (fun lid env -> (Env.lookup_constructor lid env).cstr_res)

    and tree_of_label =
      tree_of_qualified (fun lid env -> (Env.lookup_label lid env).lbl_res)


let pointer_kind mem heap addr =
  let range =  (addr,Int64.add addr 1L) in
  if Int64.logand addr 1L <> 0L then
    Value
  else
    if
      addr >= heap.caml_young_start && addr <= heap.caml_young_end
    then
      MinorAddress
    else
      if ChunkSet.mem range heap.caml_major_heap then
        MajorAddress
      else
        try
          let m = ChunkMap.find range mem.data_fragments in
          ModuleData m
        with Not_found ->
          try
            let m = ChunkMap.find range mem.code_fragments in
            ModuleCode m
          with Not_found ->
            Pointer

let debug_path s path =
  match s with
  | [] -> assert false
  | (indent, head, ty) :: tail ->
    let head = Printf.sprintf "%s (<- %s)" head path in
    (indent, head, ty) :: tail

let label_name_arg = function
#if OCAML_VERSION < "4.02"
   (lbl_name, _, lbl_arg) -> (lbl_name, lbl_arg)
#else
    { ld_id = lbl_name; ld_type = lbl_arg } -> (lbl_name, lbl_arg)
#endif

let constructor_info
#if OCAML_VERSION < "4.02"
   (constr_name, constr_args,ret_type)
#else
    { cd_id =constr_name; cd_args = constr_args; cd_res = ret_type }
#endif
    = (constr_name, constr_args,ret_type)

type context = {
  mem : LLDBTypes.mem_info;
  heap : LLDBTypes.heap_info;
  process : sbProcess;
#ifndef OCAML_NON_OCP
  locs : GcprofTypes.locations;
#endif
}

type value_type =
    List of Env.t * type_expr
  | Tuple of type_expr list
  | Array of Env.t * type_expr
  | Option of Env.t * type_expr
  | Ref of Env.t * type_expr
  | Record of Env.t * type_expr * type_expr list * Path.t * type_declaration * label_declaration list
  | Variant of Env.t * type_expr * type_expr list * Path.t * type_declaration * constructor_declaration list
  | FLOAT | INT32 | INT64 | CHAR | BOOL | STR | INT | NINT | UNIT | Nope

let extract_constant_ctors ~cases =
  let constant_ctors, _ =
    List.fold_left
    (fun (constant_ctors, next_ctor_number) ctor_decl ->
      let ident = ctor_decl.cd_id in
      match ctor_decl.cd_args with
        | [] ->
            (next_ctor_number, ident)::constant_ctors, next_ctor_number + 1
        | _ -> constant_ctors, next_ctor_number)
    ([], 0) cases
  in constant_ctors

let find_decl_value ty env path ty_list =
  let handle_decl decl =
    match decl.type_kind with
      | Type_record (lbl_list, record_repr) -> Record(env, ty, ty_list, path, decl, lbl_list)
      | Type_variant constr_list -> Variant (env, ty, ty_list, path, decl, constr_list)
      | Type_open
      | Type_abstract -> Printf.printf "unsupported type decl\n";Nope
  in

 match Env.find_type path env with
   | exception exn -> begin
     let tds = !tydecl_tbl in
     try
       let td = Hashtbl.find tds (Path.name path) in handle_decl td
     with _ -> Printf.printf "type decl not found\n"; Nope
   end

   | decl -> handle_decl decl

let find_type (env, ty) =
  let ty = Ctype.expand_head env ty in
    match ty.desc with
    | Tlink _ -> assert false
    | Tvar _
    | Tarrow (_, _, _, _)
    | Tobject (_, _)
    | Tfield (_, _, _, _)
    | Tnil
    | Tsubst _
    | Tvariant _
    | Tunivar _
    | Tpoly (_, _)
    | Tpackage (_, _, _) -> Nope

    | Ttuple ty_args -> Tuple ty_args
    | Tconstr (path, [ty_arg], _) ->
      if Path.same path Predef.path_list then begin
          List (env, ty_arg)
      end else
      if Path.same path Predef.path_array then begin
          Array (env, ty_arg)
      end else
      if Path.same path Predef.path_option then begin
          Option (env, ty_arg)
      end else
      if Path.name path = "Pervasives.ref" then begin
          Ref (env, ty_arg)
      end else begin
          Printf.printf "poly unk path: %s\n" (Path.name path);
          find_decl_value ty env path [ty_arg]
      end

    | Tconstr (path, [], _) ->
      if Path.same path Predef.path_float then begin
          FLOAT
      end else
      if Path.same path Predef.path_int32 then begin
          INT32
      end else
      if Path.same path Predef.path_int64 then begin
          INT64
      end else
      if Path.same path Predef.path_nativeint then begin
          NINT
      end else
      if Path.same path Predef.path_string then begin
          STR
      end else
      if Path.same path Predef.path_int then begin
          INT
      end else
      if Path.same path Predef.path_char then begin
          CHAR
      end else
      if Path.same path Predef.path_bool then begin
          BOOL
      end else
      if Path.same path Predef.path_unit then begin
          UNIT
      end else begin
          Printf.printf "single unk path: %s\n" (Path.name path);
          find_decl_value ty env path []
      end

    | Tconstr(path, ty_list, _) ->
      Printf.printf "mult unk path: %s\n" (Path.name path);
      find_decl_value ty env path ty_list

let get_header_of_block c v =
  let header = LLDBUtils.getMem64 c.process (Int64.sub v 8L) in
  LLDBOCamlDatarepr.parse_header c.mem header

#ifdef OCAML_NON_OCP
let string_of_type_expr env ty = Symtbl.print_type env ty
#else
let string_of_type_expr env ty = GcprofLocations.string_of_type_expr env ty
#endif

let rec print_gen_value c indent addr types =
  if indent > !max_indent && (not !vf) then [ indent, "...", ""] else
  match pointer_kind c.mem c.heap addr with
  | ModuleCode m ->
    [ indent,
      Printf.sprintf "0x%Lx" addr,
      Printf.sprintf "code of module %S" m ]
  | MinorAddress
  | MajorAddress
  | ModuleData _ as zone ->
    begin
    let h = get_header_of_block c addr in
#ifndef OCAML_NON_OCP
    match h.locid with
    | None ->
#endif
      (*    Printf.eprintf
            "0x%Lx: 0x%Lx{ tag=%d wosize=%d gc=%x zone=%s } (%s)\n%!"
            addr header h.tag h.wosize h.gc
            zone
            (string_of_tag h.tag); *)
      print_value c indent addr types
#ifndef OCAML_NON_OCP
    | Some locid ->
      (*    Printf.eprintf
            "0x%Lx: 0x%Lx { tag=%d wosize=%d gc=%x zone=%s locid=%d } (%s)%s\n%!"
            addr header h.tag h.wosize h.gc zone locid
            (string_of_tag h.tag)
            (
            try
            let s = GcprofLocations.to_strings locs locid in
            GcprofTypes.(Printf.sprintf "%s@%s{%s,%s}"
            s.sloc_type s.sloc_loc s.sloc_kind
            (String.concat "." s.sloc_path))
            with _ ->
            "invalid-locid"
            ); *)
      let sloc = GcprofLocations.to_strings c.locs locid in
      let loc_info = try
                       Some GcprofTypes.(Printf.sprintf "%s{%s,%s}"
                         (*s.sloc_type*) sloc.sloc_loc sloc.sloc_kind
                                           (String.concat "." sloc.sloc_path))
        with _ -> None in
      let env = c.locs.locs_env in
      let li = c.locs.locs_info.(locid) in
      let types =
        match li.loc_type with
        | (Not_applicable | RecClosure _) -> types
        | Expr ty -> begin
              (*if the type in the locid is alpha, keep the most accurate type*)
              let s = GcprofLocations.string_of_type_expr env ty in
              if s = "'a" then types else (env, ty) :: types end
      in
      let s = print_value c indent addr types in
      match loc_info with
      | None -> s
      | Some loc_info ->
        match s with
        | [] -> assert false
        | (indent, descr, ty) :: tail ->
          let ty =Printf.sprintf "%s@%s"
            (match ty with
            | "" | "?" ->
              sloc.sloc_type
            | _ -> ty) loc_info in
          (indent, descr, ty) :: tail
#endif
    end
  | Value -> print_value c indent addr types
  | Pointer -> let nv = LLDBUtils.getMem64 c.process addr in print_value c indent nv types

and print_value c indent addr types =
  match types with
    | [] -> [indent, Printf.sprintf "Val %Ld - %Ld" addr (Int64.shift_right addr 1), ""]
    | (env, ty) :: types ->
      let s = print_typed_valueh c indent addr (env,ty) in
        match s with
        | [] -> assert false
        | (indent, head, type_info) :: tail ->
          let type_info = if type_info = "" then
              let s = string_of_type_expr env ty in
              if s <> "'a" then s else ""
            else type_info in
          (indent, head, type_info) :: tail

and print_typed_valueh c indent v (env,ty) =
  let ocaml_value = Int64.to_int (Int64.shift_right v 1) in
  let type_res = find_type (env, ty) in
  match type_res with
    | FLOAT -> begin
        try let h = get_header_of_block c v in print_raw_value c indent h v with _ -> print_float indent v end
    | INT -> print_int indent ocaml_value
    | BOOL -> print_bool indent ocaml_value
    | UNIT -> print_unit indent ocaml_value
    | CHAR -> print_ch indent ocaml_value
    | INT32 | INT64 | NINT -> print_boxed_value c indent v type_res
    | STR ->
          let h = get_header_of_block c v in print_raw_value c indent h v
    | List (env,tys) ->
      (indent, "<list>", "") ::
        print_list_value c indent env tys v 0
    | Tuple ty_args ->
      let h = get_header_of_block c v in
      let ty_args = Array.of_list ty_args in
      let len = Array.length ty_args in
      if len <> h.wosize then
        debug_path
          ([indent, Printf.sprintf "0x%Lx" v, ""])
          (Printf.sprintf
             "WARNING(tuple size %d <> block size %d)"
             len h.wosize)
      else
      (indent, "<tuple>", string_of_type_expr env ty) ::
           (print_tuple "tuple" env ty_args c indent v 0 h.wosize)
    | Array (envv,tty) ->
      let h = get_header_of_block c v in
      if h.tag = 254 then print_raw_value c indent h v else
      (indent,
       Printf.sprintf "<array[%d]>" h.wosize,
       string_of_type_expr env ty) ::
           (print_array (envv,tty) c indent v 0 h.wosize)
    | Option (env, ty) ->
      print_option c indent env ty v
    | Ref (env, ty) ->
      let nv = LLDBUtils.getMem64 c.process v in
      (indent, "<ref>", "") ::
      print_typed_valueh c (indent+2) nv (env,ty)
    | Record(env, ty, ty_list, path, decl, lbl_list) ->
        print_record c indent v env ty decl path ty_list lbl_list
    | Variant(env, ty, ty_list, path, decl, constr_list) ->
      if Int64.logand v 1L = 0L then
        let h = get_header_of_block c v in
        print_block_variant c indent h v env path decl ty ty_list constr_list
      else
        print_const_variant indent ocaml_value constr_list
    | Nope -> [indent, "typed value unhandled", ""]

and print_float indent n =
  [ indent, Printf.sprintf "%f" (Int64.float_of_bits n), ""]

and print_int indent n =
  [ indent, string_of_int n, "" ]

and print_ch indent n =
  let s =
    if n >= 0 && n < 256 then
      Printf.sprintf "%C" (char_of_int n)
    else Printf.sprintf "invalid(char,%d)" n in [ indent, s, "" ]

and print_bool indent n =
  let s =
    match n with
      | 0 -> "false"
      | 1 -> "true"
      | _ -> Printf.sprintf "invalid(bool,%d)" n in [ indent, s, "" ]

and print_unit indent n =
  let s =
    match n with
      | 0 -> "()"
      | _ -> Printf.sprintf "invalid(unit,%d)" n in [ indent, s, "" ]

and print_option c indent env ty n =
    match Int64.compare n Int64.one with
      | 0 -> [indent, "None", ""]
      | _ ->  let nv = LLDBUtils.getMem64 c.process n in
              print_typed_valueh c (indent+2) nv (env,ty)

and print_boxed_value c indent n tr =
  let v = LLDBUtils.getMem64 c.process (Int64.add n (Int64.of_int (8))) in
  match tr with
    | INT32 -> [ indent, Printf.sprintf "%ld" (Int64.to_int32 v), ""]
    | INT64 -> [ indent, Printf.sprintf "%Ld" v, ""]
    | NINT -> [ indent, Printf.sprintf "%nd" (Int64.to_nativeint v), ""]
    | _ -> [indent, "boxed value unhandled", ""]

 and print_list_value c indent env ty addr i =
     if i = 5 && (not !vf) then
       [indent, "... </list>", ""]
     else
       let head_v = LLDBUtils.getMem64 c.process
         (Int64.add addr (Int64.of_int (8 * 0))) in
       let head = print_gen_value c (indent+2) head_v [env, ty] in
       let tail_addr = LLDBUtils.getMem64 c.process
         (Int64.add addr (Int64.of_int (8 * 1))) in
       if tail_addr = 1L then
         head @ [ indent, "</list>", "" ]
       else
         head @
           print_list_value c indent env ty tail_addr (i+1)

 and print_raw_value c indent h addr =
     if indent > !max_indent && (not !vf) then
       [ indent, "...", "" ]
     else
         match h.tag with
         | 251 ->
           (indent,
            Printf.sprintf "<block[%d] tag=%d>" h.wosize h.tag
              , "?") ::
             (print_block c indent addr 0 h.wosize)

         | 252 ->
           let len = LLDBOCamlDatarepr.parse_string_length c.process h addr in
           let maxlen = min 50 len in
           let b = Bytes.create maxlen in
           let nRead = SBProcess.readMemory c.process addr b maxlen
             LLDBUtils.sbError in
           if nRead > 0 then
             let b = Bytes.sub_string b 0 nRead in
             [ indent, Printf.sprintf "(len %d) %S" len b, "string" ]
           else
             [ indent, "<unreadable string>", "string" ]

         | 253 ->
           let v = LLDBUtils.getMem64 c.process addr in
          [ indent, Printf.sprintf "%f" (Int64.float_of_bits v), "float"]

         | 254 ->
           let res = ref [] in
           for i = 0 to h.wosize - 1 do
               let v = LLDBUtils.getMem64 c.process
               (Int64.add addr (Int64.of_int (i * 8))) in
               let s = [ indent+2, Printf.sprintf "%f" (Int64.float_of_bits v), "float"] in
               let s = match s with
               | [] -> assert false
               | (_, head, ty) :: tail ->
                       (indent+2, Printf.sprintf "%d: %s" i head, ty)
                       :: tail
               in
             res := !res @ s
           done;
           !res

         | 255 -> begin
           let structop = LLDBUtils.getMem64 c.process addr in
           let v = LLDBUtils.getMem64 c.process
             (Int64.add addr (Int64.of_int (8))) in
           let identifier_ptr = LLDBUtils.getMem64 c.process structop in
           let id = LLDBOCamlDatarepr.read_null_terminated_string c.process c.mem identifier_ptr in
           match id with
               | "_i" -> [ indent+4, Printf.sprintf "%ld" (Int64.to_int32 v), "int32"]
               | "_n" -> [ indent+4, Printf.sprintf "%nd" (Int64.to_nativeint v), "nativeint"]
               | "_j" -> [ indent+4, Printf.sprintf "%Ld" v, "int64"]

               | _ ->
               let s =
                 Printf.sprintf
                   "<ptr>0x%Lx: { tag=%d wosize=%d gc=%x } (%s) id=%s</ptr>"
                   addr h.tag h.wosize h.gc
                   (string_of_tag h.tag) id
               in
               [ indent, s, "" ]
         end

         | _ ->
           let s =
             Printf.sprintf
               "<ptr>0x%Lx: { tag=%d wosize=%d gc=%x } (%s)</ptr>"
               addr h.tag h.wosize h.gc
               (string_of_tag h.tag)
           in
           [ indent, s, "" ]

 and print_block c indent addr i len =
     if i = len then
       [ indent, "</block>", "?" ]
     else
       if i = 5 && (not !vf) then
         [ indent+2, "...", "_"; indent, "</block>", "" ]
       else
         let v = LLDBUtils.getMem64 c.process
           (Int64.add addr (Int64.of_int (i * 8))) in
         let s = print_gen_value c (indent+4) v [] in
         let s = match s with
           | [] -> assert false
           | (_, head, ty) :: tail ->
             (indent+2, Printf.sprintf "%d: %s" i head, ty)
             :: tail
         in
         s @ print_block c indent addr (i+1) len

 and print_tuple constr_name env ty_args c indent addr i len =
     if i = len then
       [ indent, Printf.sprintf "</%s>" constr_name, "" ]
     else
       let v = LLDBUtils.getMem64 c.process
         (Int64.add addr (Int64.of_int (i * 8))) in
       let s = print_gen_value c (indent+4) v [env,ty_args.(i)] in
       let s = match s with
         | [] -> assert false
         | (_, head, ty) :: tail ->
           (indent+2, Printf.sprintf "%d: %s" i head, ty)
           :: tail
       in
       s @ print_tuple constr_name env ty_args c indent addr (i+1) len

 and print_array (env, ty_arg) c indent addr i len =
     if i = len then
       [ indent, "</array>", "" ]
     else
       if i = 5 && (not !vf) then
         [ indent+2, "...", "_"; indent, "</array>", "" ]
       else
         let v = LLDBUtils.getMem64 c.process
           (Int64.add addr (Int64.of_int (i * 8))) in
         let s = print_gen_value c (indent+2) v [env, ty_arg] in
         let s = match s with
           | [] -> assert false
           | (_, head, ty) :: tail ->
             (indent+2, Printf.sprintf "%d: %s" i head, ty)
             :: tail
         in
         s @ print_array (env, ty_arg) c indent addr (i+1) len

and print_record c indent addr env ty decl path ty_list lbl_list =

     let fields = List.mapi (fun pos lbl ->
       let (lbl_name, lbl_arg) = label_name_arg lbl
       in
       (pos, lbl_name, lbl_arg)) lbl_list in


     (indent, "{",
      string_of_type_expr env ty
     ) ::
       (List.flatten
          (List.map (fun (pos, lbl_name, lbl_arg) ->
            let types =
              try
                [env,
                 Ctype.apply env decl.type_params
                   lbl_arg ty_list]
              with
              | Ctype.Cannot_apply -> []
            in
            let name = Ident.name lbl_name in
                 (* PR#5722: print full module path only
                    for first record field *)
            let lid =
              if pos = 0 then tree_of_label env path name
              else name in
            let v = LLDBUtils.getMem64 c.process
              (Int64.add addr (Int64.of_int (8 * pos))) in
            let s = print_gen_value c (indent+4) v types in
            match s with
            | [] -> assert false
            | (_, head, ty) :: tail ->
              (indent+2,
               Printf.sprintf "%s= %s" lid head,
               ty) :: tail
           )
             fields)) @
       [ indent, "}", "" ]

and print_const_variant indent ocaml_value constr_list =
  let const_ctors = extract_constant_ctors constr_list in
  if ocaml_value >= 0 && ocaml_value < List.length const_ctors
  then
    let ident =
      try Some (List.assoc ocaml_value const_ctors)
      with Not_found -> None in
    begin match ident with
      | Some ident -> [indent, Printf.sprintf "%s" (Ident.name ident), ""]
      | None -> [indent, "unhandled const variant", ""]
    end
  else
    [indent, "unhandled const variant", ""]

and print_block_variant c indent h addr env path decl ty ty_list constr_list =
  let tag =
    Cstr_block h.tag
  in
  let (constr_name, constr_args,ret_type) =
    constructor_info
      (Datarepr.find_constr_by_tag tag constr_list) in
  let constr_name = Ident.name constr_name in
  let type_params =
    match ret_type with
      Some t ->
        begin match (Ctype.repr t).desc with
          Tconstr (_,params,_) ->
            params
        | _ -> assert false end
    | None -> decl.type_params
  in
  let printed_args =
#if OCAML_VERSION >= "4.03"
    match constr_args with
    | Cstr_record lbl_list ->
      print_record c indent addr env ty decl path ty_list lbl_list
    | Cstr_tuple constr_args ->
#endif
    match
      try `Value (List.map
                    (function ty ->
                      Ctype.apply env type_params ty ty_list )
                    constr_args)
      with  Ctype.Cannot_apply as exn -> `Exception exn
    with
    | `Exception exn ->
      [indent, (Printf.sprintf "%s (Ctype.Cannot_apply)" constr_name), ""]
    | `Value ty_args ->
      let ty_args = Array.of_list ty_args in
      let len = Array.length ty_args in
      if len <> h.wosize then
        [indent,
        (Printf.sprintf
           "WARNING(%s size %d <> block size %d)" constr_name
           len h.wosize),
         ""]
      else
        (print_tuple constr_name env ty_args c indent addr 0 h.wosize)
  in (indent, Printf.sprintf "<%s>" constr_name, string_of_type_expr env ty) :: printed_args


let print_value target mem heap initial_addr types type_decls verbose =
#ifndef OCAML_NON_OCP
  let loctbls, locs = if mem.standard_header then
      [||], { locs_env = Memprof_env.initial;
              locs_info = [||];
              locs_cache = [||];
            }
    else
      LLDBOCamlLocids.load target
  in
#endif
  vf := verbose;
  tydecl_tbl := type_decls;
  let process = SBTarget.getProcess target in
  let c = {
    process; mem; heap;
#ifndef OCAML_NON_OCP
    locs;
#endif
  } in
  let lines = print_gen_value c 0 initial_addr types in
  List.iter (fun (indent, line, ty) ->
    for i = 1 to indent do print_char ' '; done;
    print_string line;
    if ty <> "" then begin
      print_string " : ";
      print_string ty;
    end;
    print_newline ()
  ) lines;
  vf := false;
