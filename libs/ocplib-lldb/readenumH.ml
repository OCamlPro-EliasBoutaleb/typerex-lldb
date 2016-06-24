open Genlex

let rec simplify_tokens in_enum tokens rem =
  match tokens with
  | Ident "FLAGS_ENUM" :: Kwd "(" :: Ident name :: Kwd ")" :: Kwd "{" :: tokens ->
      simplify_tokens 1 tokens (Kwd "{" ::  Kwd ")"  :: Ident name :: Kwd "(" :: Ident "FLAGS_ENUM" :: rem)
  | Ident "enum" :: tokens ->
    let rec iter tokens =
      match tokens with
      | Kwd "}" :: Kwd ";" :: tokens -> tokens
      | _ :: tokens -> iter tokens
      | []  -> assert false
    in
    simplify_tokens in_enum (iter tokens) rem
  | Kwd "}" :: Kwd ";" :: tokens ->
    simplify_tokens 0 tokens
      (if in_enum > 0 then (Kwd ";" :: Kwd "}" :: rem) else rem)
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
                              "["; "]"; ":"; "&"; "*"; "="; "~"; "**"; "<<"; "0x" ]

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
      | Ident "FLAGS_ENUM" :: Kwd "(" :: Ident name :: Kwd ")" :: Kwd "{" :: tokens ->
        Printf.eprintf "now in enum %s\n%!" name; 
        get_enums (Some (name, [])) [] tokens
      | Kwd ";" :: tokens ->
        begin match in_enum with
        | None -> begin match tokens with [] -> print_endline "none left";
            | t1::tl ->
                Printf.printf "t1 %s\n" (string_of_token t1);
            exit 0; end
        | Some (name, flags) ->
          Printf.eprintf "Adding enum %S\n%!" name; 
          enums := (name, List.rev flags) :: !enums
        end;
        get_enums None [] tokens;

      | Kwd "," :: tokens
      | Kwd "}" :: tokens ->
        begin match in_enum with
        | None ->
          Printf.eprintf "no enum: discarding\n%!";
          assert false
        | Some (enum_name, flags) ->
          let in_enum =
            let in_fun = List.rev fls in
            match in_fun with
            | Ident flag :: Kwd "=" :: Kwd "(" :: Int n :: Ident "u" :: Kwd "<<" :: Int s :: Kwd ")" :: tokens
            | Ident flag :: Kwd "=" :: Int n :: Ident "u" :: Kwd "<<" :: Int s :: tokens ->
                Printf.eprintf "got a flag named %s of val %d from %s\n%!" flag (n lsl s) enum_name;
                Some(enum_name, (flag, n lsl s)::flags)
            | Ident flag :: Kwd "=" :: Kwd "(" :: Int 0 :: Ident hex :: Kwd ")" ::  tokens
            | Ident flag :: Kwd "=" :: Int 0 :: Ident hex :: tokens ->
                let hex_str = 
                  if String.get hex 0 = 'x' then
                    if String.get hex (String.length hex - 1) = 'u'
                    then ("0" ^ (String.sub hex 0 (String.length hex - 2)))
                    else ("0" ^ hex)
                  else "0" in
                Printf.eprintf "got a flag named %s from %s\n%!" flag enum_name;
                Some(enum_name, (flag, int_of_string hex_str)::flags)
            | _ ->
                Some (enum_name, flags)
          in
          get_enums in_enum [] tokens
        end;
      | token :: tokens ->

        (*does not get last enum flag coz no colon*)
        (*match token with*)
          (*| Kwd "," ->*)
          (*| _ ->*)
        Printf.eprintf "passing %s\n%!" (string_of_token token);
        get_enums in_enum (token :: fls) tokens
      | [] ->
        match in_enum with
        | None -> ()
        | Some (name, _) ->
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
      s.[pos] <- ' ';
      clear_eol s (pos+1) len
    end

    in
  let rec clear_comment s pos len =
    let c = Bytes.get s pos in
    s.[pos] <- ' ';
    if pos < len-1 && (c <> '*' || Bytes.get s (pos+1) <> '/') then begin
      clear_comment s (pos+1) len
    end else
      s.[pos+1] <- ' '
  in
  let rec iter s pos len =
    if pos < len then
      let c = Bytes.get s pos in
      begin
        match c with
        | '#' ->
          clear_eol s pos len
      | '\r' -> s.[pos] <- ' '
      | '/' when pos +1 < len && Bytes.get s (pos+1) = '/' ->
        clear_eol s pos len
      | ' ' when pos +1 < len && Bytes.get s (pos+1) = '(' ->
        s.[pos] <- '('; s.[pos+1] <- ' '
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

  Printf.eprintf "before simpl :\n%!";
  List.iter (fun token ->
  Printf.eprintf "%s " (string_of_token token)) tokens;
  Printf.eprintf "\n%!";

  match error with
  | None -> 
      let tokens = simplify_tokens 0 tokens [] in
      Printf.eprintf "after simpl :\n%!";
      List.iter (fun token ->
      Printf.eprintf "%s " (string_of_token token)) tokens;
      Printf.eprintf "\n%!";
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

let _ =
  let enums = ref [] in
  read_file Sys.argv.(1) enums;

  let enoc = open_out "LLDBEn.ml" in
  List.iteri (fun i (enum_name, enum_flags) -> ()
    (*Printf.fprintf enoc "\n";*)
    (*Printf.fprintf enoc "#define LLDB_%-25s %2d\n" class_name (i+1);*)
    (*Printf.fprintf enoc "#define Val_%s(ptr) Val_final(LLDB_%s, ptr)\n"*)
  ) !enums;
  close_out enoc
