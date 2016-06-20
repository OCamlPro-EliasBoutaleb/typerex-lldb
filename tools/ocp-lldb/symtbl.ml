open Typedtree

let print_type env typ =
  Format.pp_print_string Format.str_formatter "  ";
  Printtyp.wrap_printing_env env
                   (fun () -> Printtyp.type_scheme Format.str_formatter typ);
  Format.flush_str_formatter ()

let print_stack x = String.concat ", " x

let id_to_string s =
    let open Format in
    fprintf str_formatter "%a" (Ident.print) s;
    flush_str_formatter ()

let vb_tbl = ref @@ Hashtbl.create 100
let typ_tbl = ref @@ Hashtbl.create 100
let tydecl_tbl = ref @@ Hashtbl.create 100
let sc = ref []

let while_cnt = ref 0
let mk_while_id x =
    while_cnt := !while_cnt + 1;
    Printf.sprintf "while_%d_from_%s" !while_cnt x

let strip s = if s = "" then s else List.hd @@ Str.split (Str.regexp "/") s

let capture_func_args e =

  let ident patt =
    match patt.pat_desc with
      | Tpat_var (s,_) -> id_to_string s
      | _ -> ""
  in

  let rec h expr =
  match expr.exp_desc with
  | Texp_function (_, l, _partial) ->

    assert (List.length l > 0);
    let fn_scope = try List.hd !sc with _ -> failwith "not in a function" in
    if List.length l > 1 then Printf.printf "function keyword/partial application detected for %s\n" fn_scope else
    begin
      let case = List.hd l in

      let id = ident case.c_lhs in

      let patt = case.c_lhs in

      let param_loc, param_env, param_type =
          (patt.pat_loc, patt.pat_env, patt.pat_type) in

      let gen_type = print_type param_env param_type in

      if id <> "" then
        Hashtbl.add !vb_tbl id (param_loc, gen_type, fn_scope);
        Hashtbl.add !typ_tbl id (param_env, param_type);

    h case.c_rhs
    end
  | _ -> () in

  h e

module IterArg = struct
  include TypedtreeIter.DefaultIteratorArgument

  let enter_expression expr =
    let curr_scope = try List.hd !sc with _ -> "toplevel" in
    match expr.exp_desc with
    | Texp_let (rf, (lvb::_), e) ->
        begin
        match lvb.vb_expr.exp_desc with
        | Texp_let (_, _, _) ->
            begin
                match lvb.vb_pat.pat_desc with
                  | Tpat_var (s,_) ->
                    let es = id_to_string s in
                    if es <> curr_scope then sc := es :: !sc
                  | _ -> ()
            end
        | _ -> ()
        end
    | Texp_for (s, _, _, _, _, _) ->
        let es = id_to_string s in
        if es <> curr_scope then sc := es :: !sc
    | Texp_ifthenelse _ -> ()
    | Texp_while _ ->
        let ns = mk_while_id curr_scope in sc := ns :: !sc
    | _ -> ()

  let leave_expression expr =
    match expr.exp_desc with
    | Texp_for (s, _, _, _, _, _) ->
        begin
        let es = id_to_string s in
        match !sc with
          | [] -> ()
          | hd :: tl -> if es = hd then sc := tl
        end
    | Texp_ifthenelse _ -> ()
    | Texp_while _ ->
        begin
        match !sc with
          | [] -> ()
          | hd :: tl -> sc := tl
        end
    | _ -> ()

  let enter_binding bind =
    let ident =
      match bind.vb_pat.pat_desc with
        | Tpat_var (s,_) -> id_to_string s
        | _ -> ""
    in

    let saved_let = ref "" in
    begin
    match bind.vb_expr.exp_desc with
    | Texp_let (rf, (lvb::_), e) ->
        begin
        match bind.vb_pat.pat_desc with
          | Tpat_var (s,_) ->
            let curr_scope = try List.hd !sc with _ -> "toplevel" in
            let ns = id_to_string s in
            if ns = curr_scope then saved_let := ns; sc := List.tl !sc
          | _ -> ()
        end
    | _ -> () end;

    let final_scope = try List.hd !sc with _ -> "toplevel" in

    let gen_type = print_type bind.vb_expr.exp_env bind.vb_expr.exp_type in
    Hashtbl.add !vb_tbl ident (bind.vb_expr.exp_loc, gen_type, final_scope);
    Hashtbl.add !typ_tbl (strip ident) (bind.vb_expr.exp_env, bind.vb_expr.exp_type);

    match bind.vb_pat.pat_desc with
      | Tpat_var (s,_) ->
        begin
          let ns = id_to_string s in
          match bind.vb_expr.exp_desc with
          | Texp_function _ ->
              if ns <> final_scope then sc := ns :: !sc;
              capture_func_args (bind.vb_expr)
          | Texp_let (rf, (lvb::_), e) ->
              begin
                if ns = !saved_let then sc := ns :: !sc;
                if final_scope = "toplevel" then sc := ns :: !sc
              end
          | _ -> ()
        end
      | _ -> ()

  let leave_binding bind =
    match bind.vb_expr.exp_desc with
    | Texp_function _
    | Texp_let _ ->
      begin
      match bind.vb_pat.pat_desc with
        | Tpat_var (s,_) ->
            begin
            let es = id_to_string s in
            match !sc with
              | [] -> ()
              | hd :: tl ->
                if es = hd then sc := tl
            end
        | _ -> ()
      end
    | _ -> ()

  let leave_type_declaration td =
    let ident = id_to_string td.typ_id in
    Hashtbl.add !tydecl_tbl (strip ident) td.typ_type

end

module MyIterator = TypedtreeIter.MakeIterator (IterArg)

let vb structure =
  MyIterator.iter_structure structure;

  if !LLDBGlobals.verbose then begin
    Printf.printf "got %d vbs\n" (Hashtbl.length !vb_tbl);
    Hashtbl.iter (fun k (tl,ty,scope) ->  Printf.printf "%s : %s with scope inside %s\n" k ty scope) !vb_tbl;
    Printf.printf "got %d ids and typ\n" (Hashtbl.length !typ_tbl);
    Printf.printf "got %d tyd\n" (Hashtbl.length !tydecl_tbl)
  end;

  let res = (Hashtbl.copy !typ_tbl, Hashtbl.copy !tydecl_tbl, Hashtbl.copy !vb_tbl) in
  Hashtbl.clear !typ_tbl; Hashtbl.clear !tydecl_tbl; Hashtbl.clear !vb_tbl;
  res

