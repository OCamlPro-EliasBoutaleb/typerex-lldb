open Typedtree
open Cmt_format
open Zipper

open Location
open Lexing

open Printf

type type_and_env = Env.t * Types.type_expr

type module_info =
  { type_decls : (string * Types.type_declaration) list;
    mod_name : string;
  }

type function_info =
  { fun_type : type_and_env;
    fun_name : string;
    fun_args : (string * Env.t * Types.type_expr * Location.t) list;
    fun_loc : Location.t;
  }

type value_bind_info =
  { vb_type : type_and_env;
    vb_name : string;
    vb_loc : Location.t;
  }

type sym_info =
    Module of module_info
  | Function of function_info
  | ValueBind of value_bind_info
  | FuncArg of string * Env.t * Types.type_expr * Location.t

let print_type (env,typ) =
  Format.pp_print_string Format.str_formatter "  ";
  Printtyp.wrap_printing_env env
    (fun () -> Printtyp.type_scheme Format.str_formatter typ);
  Format.flush_str_formatter ()

let string_of_loc loc =
  let (filename, line1, col1) = Location.get_pos_info loc.Location.loc_start in
  let (_, line2, col2) = Location.get_pos_info loc.Location.loc_end in
  if line1 = line2 then
    Printf.sprintf "%s: L%d:C%d" filename line1 col1
  else
    Printf.sprintf "%s: L%d:C%d-L%d:C%d" filename line1 col1 line2 col2

let id_to_string s =
  let open Format in
  fprintf str_formatter "%a" (Ident.print) s;
  flush_str_formatter ()

let create_module n = leaf @@ Module {mod_name=n; type_decls=[]}
let create_vb n e t l = leaf @@ ValueBind {vb_name=n; vb_type=e,t; vb_loc=l}
let create_fun n e t a l = leaf @@ Function {fun_name=n; fun_type=e,t; fun_args=a; fun_loc=l}

let tds = ref []
let tydecl_tbl = ref @@ Hashtbl.create 100

let root n = (create_module n, Top : sym_info zipper)
let curr_node = ref @@ root ""

let strip s = if s = "" then s else List.hd @@ Str.split (Str.regexp "/") s

let get_curr t =
  match t with
  | Branch(x, _) ->
    match x with
    | Module mi -> ("mod", mi.mod_name)
    | Function fi -> ("func", fi.fun_name)
    | ValueBind vb -> ("vb", vb.vb_name)
    | _ -> ("not", "handled")

let capture_func_args e =

  let ident patt case_len =
    match patt.pat_desc with
    | Tpat_var (s,_) -> assert (case_len = 1); 
                        id_to_string s
    | _ -> 
            (*assert (case_len > 1); *)
            "param"
  in

  let rec h expr acc =
    match expr.exp_desc with
    | Texp_function (_, l, _partial) ->

      assert (List.length l > 0);
      begin
        let case = List.hd l in
        let id = ident case.c_lhs (List.length l) in
        let patt = case.c_lhs in

        let param_env, param_type, param_loc =
          (patt.pat_env, patt.pat_type, patt.pat_loc) in

        h case.c_rhs (fun ys -> acc ((id, param_env, param_type, param_loc)::ys))
      end
    | _ -> acc [] in

  h e (fun ys -> ys)

let append_and_goto_child n it =
  last_child_of_pos @@move_down@@ insert_down n it

module IterArg = struct
  include TypedtreeIter.DefaultIteratorArgument

  let enter_structure_item si =

    let r = match si.str_desc with
      | Tstr_value (_, [vb]) -> [vb]
      | Tstr_value (_, vbs) -> [List.hd vbs]
      | _ -> [] in

    match r with
    | [] -> ()
    | [bind] ->
      begin
        match bind.vb_pat.pat_desc with
        | Tpat_var (s,_) ->
          let ns = id_to_string s in
          begin
            match bind.vb_expr.exp_desc with
            | Texp_function _ ->
                (let args = capture_func_args (bind.vb_expr) in
                let funn = create_fun ns bind.vb_expr.exp_env bind.vb_expr.exp_type args bind.vb_loc in
                curr_node := append_and_goto_child !curr_node funn);
            | _ ->
              let vb = create_vb ns bind.vb_expr.exp_env bind.vb_expr.exp_type bind.vb_loc in
              curr_node := append_and_goto_child !curr_node vb
          end
        | _ -> ()
      end
    | _ -> ()

  let leave_structure_item si =

    let r = match si.str_desc with
      | Tstr_value (_, [vb]) -> [vb]
      | Tstr_value (_, vbs) -> [List.hd vbs]
      | _ -> [] in

    match r with
    | [] -> ()
    | [v] ->
      begin
        match v.vb_pat.pat_desc with
        | Tpat_var (s,_) ->
          curr_node := (move_up !curr_node)
        | _ -> ()
      end
    | hd :: tl -> ()

  let enter_binding bind =
    let ident =
      match bind.vb_pat.pat_desc with
      | Tpat_var (s,_) -> id_to_string s
      | _ -> ""
    in

    let nt, n =  get_curr @@ current_tree !curr_node in

    if ident <> "" && ident <> n then begin
      match bind.vb_expr.exp_desc with
      | Texp_function _ ->
        let args = capture_func_args (bind.vb_expr) in
        let funn = create_fun ident bind.vb_expr.exp_env bind.vb_expr.exp_type args bind.vb_loc in
        let upd = last_child_of_pos @@ move_down @@ insert_down !curr_node funn in curr_node := upd;
      | _ ->
        let vb = create_vb ident bind.vb_expr.exp_env bind.vb_expr.exp_type bind.vb_loc in
        let upd = insert_down !curr_node vb in curr_node := upd
    end

  let leave_binding bind =

    let ident =
      match bind.vb_pat.pat_desc with
      | Tpat_var (s,_) -> id_to_string s
      | _ -> ""
    in

    let nt, n = get_curr @@ current_tree !curr_node in
    if ident <> "" && ident <> n then begin
      match bind.vb_expr.exp_desc with
      | Texp_function _ ->
        let upd = move_up !curr_node in curr_node := upd
      | _ -> ()
    end

  let leave_type_declaration td =
    let ident = id_to_string td.typ_id in
    tds := !tds @ [ident, td.typ_type];

    Hashtbl.add !tydecl_tbl (strip ident) td.typ_type

end

module MyIterator = TypedtreeIter.MakeIterator (IterArg)

let change s =
  Str.replace_first (Str.regexp "/") "_" s

let dump_dot t n =

  let print x =
    let s = match x with
      | Module mi ->
        "MOD"^mi.mod_name
      | Function fi ->
        "FUN"^fi.fun_name
      | ValueBind vb ->
        "VB"^vb.vb_name
      | _ -> "" in change s in

  let rec trav t =
    match t with
    | Branch(x, []) ->
      [sprintf "    %s;\n" (print x)]
    | Branch(x, cs) ->
      List.map
        (fun c ->
           match c with Branch(cc,_) ->
             sprintf "    %s -> %s;\n" (print x) (print cc)
        ) cs
      @ List.concat @@ List.map trav cs in

  let oc = open_out (n ^ ".dot") in
  fprintf oc "digraph BST {\n";
  fprintf oc "    nodesep=0.4;\n";
  fprintf oc "    ranksep=0.5;\n";
  fprintf oc "    node [fontname=\"Arial\"];\n";

  List.iter (output_string oc) (trav t);
  fprintf oc "}\n"; close_out oc

let sym_printer indent t =
  let is_in x =
    match x with
    | Module mi -> sprintf "ins mod %s " mi.mod_name
    | Function fi -> sprintf "ins func %s" fi.fun_name
    | ValueBind vb -> sprintf "ins vb %s " vb.vb_name
    | _ -> "nope " in

  let print x =
    let s = match x with
      | Module mi ->
        sprintf "mod %s\n" mi.mod_name
      | Function fi ->
        let s = sprintf "func %s : %s\n" fi.fun_name (print_type fi.fun_type) in
        let args = List.fold_left
            (fun ass (n, e, t, _) -> ass ^ (sprintf "  %s : %s\n" n (print_type (e,t))))
            "" fi.fun_args in
        s ^  "args are : " ^ args
      | ValueBind vb ->
        sprintf "vb %s : %s\n" vb.vb_name (print_type vb.vb_type)
      | _ -> "" in change s in

  let rec trav t =
    match t with

    | Branch(x, cs) ->
      List.map
        (fun c ->
           match c with Branch(cc,_) ->
             (is_in x) ^ (print cc)
        ) cs
      @ List.concat @@ List.map trav cs in
  trav t

let find_sym tree sym_name =

  let test a b sym = if a = b || b = (strip a) then Some sym else None in

  let test_func a sym_name sym args =
    if a = sym_name || sym_name = (strip a) then
      Some sym
    else
      try
        let (n,e,t,l) =
          List.find
            (fun (n,_,_,_) -> sym_name = n || sym_name = (strip n))
            args in Some (FuncArg (n,e,t,l))
      with _ -> None
  in

  let is_match t =
    match t with
      Branch(n, cs) ->
      match n with
      | Module mi -> test mi.mod_name sym_name n
      | Function fi -> test_func fi.fun_name sym_name n fi.fun_args
      | ValueBind vb -> test vb.vb_name sym_name n
      | _ -> None in

  let rec trav matchs z =
    try
      let (t,p) = go_ahead z in
      match (is_match t) with
      | Some x -> trav ((x, traverse_collect p)::matchs) (t,p)
      | _ -> trav matchs (t,p)
    with exn -> matchs
  in

  let n x =
    let s = match x with
      | Module mi -> mi.mod_name
      | Function fi -> fi.fun_name
      | ValueBind vb -> vb.vb_name
      | FuncArg (ns,_,_,_) -> ns in
    strip s in

  let rec build_path = function
    | [] -> ""
    | hd :: tl -> (n hd) ^ "." ^ build_path tl in

  let loc = function
    | Function fi -> string_of_loc fi.fun_loc
    | ValueBind vb -> string_of_loc vb.vb_loc
    | FuncArg (_,_,_,l) -> string_of_loc l
    | _ -> failwith "loc : shouldnt happen" in

  let get_type_env = function
    | Function fi -> fi.fun_type
    | ValueBind vb -> vb.vb_type
    | FuncArg (_,e,t,_) -> e,t
    | _ -> failwith "te : shouldnt happen" in

  let ms = trav [] (tree, Top) in
  match ms with
  | [] -> []
  | l ->
    List.map
      (fun (x,ps) ->
         ((build_path ps) ^ (n x), loc x, get_type_env x, (n x))
      ) l

let vb structure =

  let mod_name =
    let it = List.hd structure.str_items in
    let s = it.str_loc.loc_start.pos_fname in
    Filename.chop_extension @@ String.capitalize s in
  curr_node := root mod_name;
  MyIterator.iter_structure structure;

  let res = match !curr_node with
    | (final, Top) ->
      begin
        match final with
        | Branch (v, cs) ->
          match v with
          | Module mi -> Branch (Module {mi with type_decls = !tds}, cs)
          | _ -> final
      end
    | _ -> failwith "problem with tree building" in
  (*let ls = sym_printer 0 res in*)
  (*List.iter (print_endline) ls;*)
  (*dump_dot res mod_name;*)
  tds := [];
  curr_node := root "";
  res, !tydecl_tbl

