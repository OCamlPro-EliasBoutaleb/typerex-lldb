(*This utility translates LLDB flag enumerations from C++ to OCaml.*)
(*The bitwise expression parsing is naive (only handling the expressions already*)
(*present in lldb-enumerations.h.*)

(*A calclator expression parser might be in order to be comprehensive.*)

open Genlex
open StringCompat

(*token filtering*)
let rec simplify_tokens in_enum tokens rem =
  match tokens with

  | Ident "FLAGS_ENUM" :: Kwd "(" :: Ident name :: Kwd ")" :: Kwd "{" :: tokens ->
      simplify_tokens 1 tokens (Kwd "{" :: Ident name :: Ident "enum" :: rem)
  | Ident "typedef" :: Ident "enum" :: tokens
  | Ident "enum" :: tokens ->
      simplify_tokens 1 tokens (Ident "enum" :: rem)

  | Kwd "}" :: Ident _ :: Kwd ";" :: tokens
  | Kwd "}" :: Kwd ";" :: tokens ->
    simplify_tokens 0 tokens
      (if in_enum = 1 then (Kwd ";" :: Kwd "}" :: rem) else rem)
  | token :: tokens ->
    if in_enum = 1 then
      simplify_tokens in_enum tokens (token :: rem)
    else
      simplify_tokens in_enum tokens rem
  | [] ->
    assert (in_enum = 0);
    List.rev rem

let string_of_token token =
  match token with
  | Ident id -> Printf.sprintf "Ident \"%s\"" id
  | Kwd id   -> Printf.sprintf "Kwd \"%s\"" id
  | Int n    -> Printf.sprintf "Int %d" n
  | Char c   -> Printf.sprintf "Char '%c'" c
  | String s -> Printf.sprintf "String \"%s\"" (String.escaped s)
  | Float n  -> Printf.sprintf "Float %f" n

let lexer = Genlex.make_lexer [ "."; "{"; "}"; "("; ")"; "::"; ";"; ",";
                              "["; "]"; ":"; "&"; "*"; "="; "~"; "**"; "<<"; "0x"; "|" ]

let tokens_of_string lexer s =
  let str1 = Stream.of_string s in
  let str2 = lexer str1 in
  let list = ref [] in
  let error =
    try
      Stream.iter (fun token ->
        list := token :: !list) str2;
      None
    with
      Stream.Error error ->
        Some (Stream.count str1, error)
  in List.rev !list, error

let parse_tokens enums tokens =
  begin
    let rec get_enums in_enum fls tokens =

      match tokens with
      (*entering inside an enum*)
      | Ident "enum" :: Ident name :: Kwd "{" :: tokens ->
        (*Printf.eprintf "now in enum %s\n%!" name; *)
        get_enums (Some (name, [], 0)) [] tokens
      (*leaving an enum*)
      | Kwd ";" :: tokens ->
        begin match in_enum with
        | None -> begin match tokens with [] -> print_endline "none left";
            | t1::tl ->
                Printf.printf "t1 %s\n" (string_of_token t1);
            exit 0; end
        | Some (name, flags, _) ->
          (*Printf.eprintf "Adding enum %S\n%!" name; *)
          enums := (name, List.rev flags) :: !enums
        end;
        get_enums None [] tokens;

      | Kwd "," :: Kwd "}" :: tokens
      | Kwd "," :: tokens
      | Kwd "}" :: tokens ->
        begin match in_enum with
        | None ->
          (*Printf.eprintf "no enum: discarding\n%!";*)
          assert false
        | Some (enum_name, flags, prev_enum) ->
          let in_enum =
            let in_fun = List.rev fls in
            match in_fun with

            (*handling flag enums*)
            | Ident flag :: Kwd "=" :: Kwd "(" :: Int n :: Ident "u" :: Kwd "<<" :: Int s :: Kwd ")" :: enum_rest
            | Ident flag :: Kwd "=" :: Int n :: Ident "u" :: Kwd "<<" :: Int s :: enum_rest ->
                (*Printf.eprintf "got a flag named %s of val %d from %s\n%!" flag (n lsl s) enum_name;*)
                let num = n lsl s in
                Some(enum_name, (flag, num)::flags, num)
            (*some enums might be defined using bitmasks as hex numbers*)
            | Ident flag :: Kwd "=" :: Kwd "(" :: Int 0 :: Ident hex :: Kwd ")" ::  enum_rest
            | Ident flag :: Kwd "=" :: Int 0 :: Ident hex :: enum_rest ->
                let hex_str =
                  if String.get hex 0 = 'x' then
                    if String.get hex (String.length hex - 1) = 'u'
                    then ("0" ^ (String.sub hex 0 (String.length hex - 2)))
                    else ("0" ^ hex)
                  else "0" in
                let num = int_of_string hex_str in
                (*Printf.eprintf "got a hex flag named %s from %s\n%!" flag enum_name;*)
                Some(enum_name, (flag, num)::flags, num+1)

            | Ident flag :: Kwd "=" :: Kwd "(" :: Ident f1 :: Kwd "|" :: Int n :: Kwd "|" :: Ident f2 :: Kwd ")" :: enum_rest
            | Ident flag :: Kwd "=" :: Kwd "(" :: Ident f1 :: Kwd "|" :: Ident f2 :: Kwd "|" :: Int n :: Kwd ")" :: enum_rest ->
                (*Printf.eprintf "ignore that %s flag\n" flag;*)
                let (_, x1) = List.find (fun (n1, _) -> n1 = f1) flags in
                let (_, x2) = List.find (fun (n2, _) -> n2 = f2) flags in
                let num = x1 lor (x2 lor n) in
                Some (enum_name, (flag, num)::flags, num)

            | Ident flag :: Kwd "=" :: Kwd "(" :: Ident f1 :: Kwd "|" :: Ident f2 :: Kwd "|" :: Ident f3 :: Kwd ")" :: enum_rest ->
                (*Printf.eprintf "ignore that %s one flag too\n" flag;*)
                let (_, x1) = List.find (fun (n1, _) -> n1 = f1) flags in
                let (_, x2) = List.find (fun (n2, _) -> n2 = f2) flags in
                let (_, x3) = List.find (fun (n3, _) -> n3 = f3) flags in
                let num = x1 lor (x2 lor x3) in
                Some (enum_name, (flag, num)::flags, num)
                (*Some (enum_name, flags, 0)*)
            | Ident flag :: Kwd "=" :: Kwd "(" :: Kwd "(" :: rest ->
              (*ignore*)
                Some (enum_name, flags, prev_enum)

            (*handling non-flags enum*)
            | Ident flag :: Kwd "=" :: Int n :: enum_rest ->
                (*Printf.eprintf "got a enum named %s from %s of val non spe %d\n%!" flag enum_name n;*)
                Some (enum_name, (flag,n)::flags, n+1)
            | Ident flag :: Kwd "=" :: Ident other_fl :: enum_rest ->
                begin
                (*Printf.eprintf "unhandled %s: need dict check for %s\n%!" flag other_fl;*)
                try
                    let _ = List.find (fun (n1, _) -> n1 = other_fl) flags in Some (enum_name, flags, prev_enum)
                with _ ->
                    (*begin*)
                    match other_fl with
                      "true" -> Some (enum_name, (flag,1)::flags, prev_enum)
                    | "false" -> Some (enum_name, (flag,0)::flags, prev_enum)
                    (*ignore here : already handled*)
                    | _ -> Some (enum_name, flags, prev_enum)
                    (*end*)
                end

            | Ident flag :: enum_rest ->
                let incr_enum = prev_enum + 1 in
                (*Printf.eprintf "gotta check prev enum value for enum %s : was %d, now incr to %d\n%!" flag prev_enum incr_enum;*)
                Some (enum_name, (flag,prev_enum)::flags, incr_enum)
            | _ ->
                (*Printf.eprintf "sorry, unhandled enum\n%!";*)
                Some (enum_name, flags, -42)
          in
          get_enums in_enum [] tokens
        end;
      (*accumumate flag tokens for subsequent handling*)
      | token :: tokens ->
        ();
        (*Printf.eprintf "passing %s\n%!" (string_of_token token);*)
        get_enums in_enum (token :: fls) tokens
      | [] ->
        match in_enum with
        | None -> ()
        | Some (name, _, _) ->
          Printf.eprintf "unfinished enum %s\n%!" name
    in

    get_enums None [] tokens;
  end

let read_file filename enums =
  let basename = Filename.basename filename in
  Printf.eprintf "Reading %S\n%!" basename;
  let s =
    let ic = open_in_bin filename in
    let size = in_channel_length ic in
    let s = Bytes.create size in
    really_input ic s 0 size;
    close_in ic;
    s
  in
  let rec clear_eol s pos len =
    if pos < len && Bytes.get s pos <> '\n' then begin
      Bytes.set s pos ' ';
      clear_eol s (pos+1) len
    end

    in
  let rec clear_comment s pos len =
    let c = Bytes.get s pos in
    Bytes.set s pos ' ';
    if pos < len-1 && (c <> '*' || Bytes.get s (pos+1) <> '/') then begin
      clear_comment s (pos+1) len
    end else
      Bytes.set s (pos+1) ' '
  in
  let rec iter s pos len =
    if pos < len then
      let c = Bytes.get s pos in
      begin
        match c with
        | '#' ->
          clear_eol s pos len
      | '\r' -> Bytes.set s pos ' '
      | '/' when pos +1 < len && Bytes.get s (pos+1) = '/' ->
        clear_eol s pos len
      | ' ' when pos +1 < len && Bytes.get s (pos+1) = '(' ->
        Bytes.set s pos '('; Bytes.set s (pos+1) ' '
      | '/' when pos +1 < len && Bytes.get s (pos+1) = '*'->
        Printf.eprintf "clear comment\n%!";
        clear_comment s pos len
      | _ -> ()
      end      ;
      iter s (pos+1) len
    else Bytes.to_string s
  in
  let s = iter s 0 (Bytes.length s) in

  let tokens, error = tokens_of_string lexer s in

  (*Printf.eprintf "before simpl :\n%!";*)
  (*List.iter (fun token ->*)
  (*Printf.eprintf "%s " (string_of_token token)) tokens;*)
  (*Printf.eprintf "\n%!";*)

  match error with
  | None ->
      let tokens = simplify_tokens 0 tokens [] in
      (*Printf.eprintf "after simpl :\n%!";*)
      (*List.iter (fun token ->*)
      (*Printf.eprintf "%s " (string_of_token token)) tokens;*)
      (*Printf.eprintf "\n%!";*)
      parse_tokens enums tokens
  | Some (pos, error) ->
    Printf.eprintf "Exception %S\n%!" error;
    Printf.eprintf "Error at pos %d\n%!" pos;
    exit 2

let read_file filename enums =
  try
    read_file filename enums
  with exn ->
    Printf.eprintf "Warning: read_file %S: %s\n%!"
      filename (Printexc.to_string exn)

let strip_1st_letter s = String.sub s 1 (String.length s - 1)

let _ =
  let enums = ref [] in
  read_file Sys.argv.(1) enums;

  let enoc = open_out "LLDBEnumsGen.ml" in
  List.iteri (fun i (enum_name, enum_flags) ->
  if not (enum_flags = []) then begin
    Printf.fprintf enoc "type %s = \n" (String.uncapitalize enum_name);
    List.iter (fun (enum_flag, _) ->
        Printf.fprintf enoc "| %s\n" (strip_1st_letter enum_flag)
    ) enum_flags;
    Printf.fprintf enoc "\n";

    Printf.fprintf enoc "let int_to_%s n = \n" enum_name;
    Printf.fprintf enoc "  match n with\n";
    List.iter (fun (enum_flag, integer) ->
        Printf.fprintf enoc "  | %d -> %s\n" integer (strip_1st_letter enum_flag)
    ) enum_flags;
    Printf.fprintf enoc "  | _ -> failwith (Printf.sprintf \"int_to_%s: unhandled constant %%d\" n)\n" enum_name;

    Printf.fprintf enoc "\n";

    Printf.fprintf enoc "let string_of_%s = function\n" enum_name;
    List.iter (fun (enum_flag, integer) ->
        Printf.fprintf enoc "  | %s -> \"%s\"\n" (strip_1st_letter enum_flag) enum_flag
    ) enum_flags;

    Printf.fprintf enoc "\n"
  end
  ) !enums;
  close_out enoc
