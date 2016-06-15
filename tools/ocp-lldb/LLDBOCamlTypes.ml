(**************************************************************************)
(*                                                                        *)
(*                             ocp-lldb                                   *)
(*                                                                        *)
(*  Copyright 2012-2016, OCamlPro                                         *)
(*                                                                        *)
(*  All rights reserved.  See accompanying files for the terms under      *)
(*  which this file is distributed. In doubt, contact us at               *)
(*  contact@ocamlpro.com (http://www.ocamlpro.com/)                       *)
(*                                                                        *)
(**************************************************************************)

open LLDBEnums
open LLDBOCaml
open LLDBTypes

let sbError = SBError.create ()

let get_symbol target sym_name =
  let symcontextlist = SBTarget.findSymbols target sym_name ESymbolTypeAny in
  match SBSymbolContextList.getSize symcontextlist with
  | 0 ->
    Printf.kprintf failwith "no symbol %s\n%!" sym_name;
  | n ->
    Printf.printf "got %d symbol for %s\n%!" n sym_name;
    let sctx = SBSymbolContextList.getContextAtIndex symcontextlist 0 in
    let sym = SBSymbolContext.getSymbol sctx in
    sym

let get_ttree_from_symbol sym len =
  let addr = SBSymbol.getStartAddress sym in
  let ofs = SBAddress.getOffset addr in
  let section = SBAddress.getSection addr in
  let sect_name = SBSection.getName section in
  let sect_data = SBSection.getSectionData section in

  let buffer = Bytes.create len in
  let bytes_read = SBData.readRawData sect_data sbError (Int64.to_int ofs) buffer len in
  Printf.printf "ofs 0x%Lx of section %s ; read %d out of %d bytes\n" ofs sect_name bytes_read len;

  let (ttree : Typedtree.structure) = Marshal.from_bytes buffer 0 in ttree

let get_size_from_symbol target sym =
  let sym_name = SBSymbol.getName sym in
  let addr = SBSymbol.getStartAddress sym in
  let ofs = SBAddress.getOffset addr in
  let section = SBAddress.getSection addr in
  let sect_name = SBSection.getName section in
  let sect_data = SBSection.getSectionData section in
  let size = SBData.getUnsignedInt64 sect_data sbError (Int64.to_int ofs) in
  Printf.printf "%s at ofs 0x%Lx of section %s\n%!" sym_name ofs sect_name; size

let load_tt target modname =
  let res = try
    let ttree_sym_name = Printf.sprintf "caml%s__ttree" modname in
    let ttree_size_sym_name = Printf.sprintf "caml%s__ttree_size" modname in
    Some (get_symbol target ttree_sym_name, get_symbol target ttree_size_sym_name)
  with Not_found ->
      Printf.eprintf "Error: could not find module %S\n%!" modname; None
  in
  match res with
  | Some (a, b) ->
      Printf.eprintf "Loading typedtree information...\n%!";
      let ttree_size = get_size_from_symbol target b in
      let t = get_ttree_from_symbol a (Int64.to_int ttree_size) in
      Printf.printf "ttree_size = 0x%Lx\n%!" ttree_size;
      Some (Symtbl.vb t)
  | None -> None

