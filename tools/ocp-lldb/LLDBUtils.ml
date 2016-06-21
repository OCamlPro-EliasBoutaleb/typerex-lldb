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


(* LLDB API *)

open StringCompat

open LLDBEnums
open LLDBOCaml


(* ocp-lldb modules *)
open LLDBTypes

let get_cached f =
  let last_modules = ref None in
  let nfaked_process = ref 1_000_000_000 in

  let get_modules target =
    let pid =
      try
        let process = SBTarget.getProcess target in
        Int64.to_int (SBProcess.getProcessID process)
      with _ ->
        incr nfaked_process;
        !nfaked_process
    in
    try
      match !last_modules with
      | None -> raise Not_found
      | Some (last_pid, last_modules) ->
        if last_pid <> pid then raise Not_found;
        last_modules
    with Not_found ->
      let modules = f target in
      last_modules := Some (pid, modules);
      modules
  in
  get_modules


let int64_of_string s =
  try Int64.of_string s
  with e ->
    Printf.kprintf failwith "int64.of_string %S" s


module LittleEndian = struct
  (*** FOUND in LittleEndian.ml *)
  let get_uint8_64 s pos = Int64.of_int (int_of_char (Bytes.get s pos))
  let get_uint16_64 s pos =
    let c1 = get_uint8_64 s pos in
    let c2 = get_uint8_64 s (pos+1) in
    Int64.logor c1 (Int64.shift_left c2 8), pos+2
  let get_uint32_64 s pos =
    let c1,pos = get_uint16_64 s pos in
    let c2,pos = get_uint16_64 s pos in
    Int64.logor c1 (Int64.shift_left c2 16), pos
  let get_uint64 s pos =
    let c1,pos = get_uint32_64 s pos in
    let c2,pos = get_uint32_64 s pos in
    Int64.logor c1 (Int64.shift_left c2 32), pos
end

let symbol_address target sym_name =
  let symcontextlist = SBTarget.findSymbols target sym_name ESymbolTypeAny in
  match SBSymbolContextList.getSize symcontextlist with
  | 0 ->
    Printf.kprintf failwith "no symbol %s\n%!" sym_name;
  | n ->
    let sctx = SBSymbolContextList.getContextAtIndex symcontextlist 0 in
    let sym = SBSymbolContext.getSymbol sctx in
    let addr = SBSymbol.getStartAddress sym in
    SBAddress.getLoadAddress addr target

let sbError = SBError.create ()
let getMem64 process addr =
  let nRead = SBProcess.readMemory process addr buffer 8 sbError in
  if nRead <> 8 then begin
    Printf.kprintf failwith "getMem64: failed to read bytes from 0x%Lx"
      addr
  end;
  let next,_ = LittleEndian.get_uint64 buffer 0 in
  next

let getMem32 process addr =
  let nRead = SBProcess.readMemory process addr buffer 4 sbError in
  if nRead <> 4 then begin
    Printf.kprintf failwith "getMem32: failed to read bytes from 0x%Lx"
      addr
  end;
  let next,_ = LittleEndian.get_uint32_64 buffer 0 in
  Int64.to_int next


(*** FOUND IN gc_stats.ml *)
let symbol_value target sym_name typ =
  let symcontextlist = SBTarget.findSymbols target sym_name ESymbolTypeAny in
  match SBSymbolContextList.getSize symcontextlist with
  | 0 ->
    Printf.kprintf failwith "no symbol %s\n%!" sym_name;
  | n ->
    let sctx = SBSymbolContextList.getContextAtIndex symcontextlist 0 in
    let sym = SBSymbolContext.getSymbol sctx in
    let addr = SBSymbol.getStartAddress sym in
    let typ = SBTarget.findFirstType target typ in
    SBTarget.createValueFromAddress target sym_name addr typ

(*** FOUND IN gc_stats.ml *)
let long_symbol_value target sym =
  SBValue.getValueAsUnsigned1 (symbol_value target sym "long") (-42L)

(*** FOUND IN gc_stats.ml *)

let double_symbol_value target sym =
  Int64.float_of_bits (long_symbol_value target sym)


let get_cached_with_symbol_check f symbol =
  let last_modules = ref None in
  let nfaked_process = ref 1_000_000_000 in

  let get_modules target =
    let pid, symbol_value =
      try
        let process = SBTarget.getProcess target in
        let pid = Int64.to_int (SBProcess.getProcessID process) in
        let symbol_addr = symbol_address target symbol in
        let symbol_value =  getMem64 process symbol_addr in
        (pid, symbol_value)
      with _ ->
        incr nfaked_process;
        !nfaked_process, 0L
    in

    try
      match !last_modules with
      | None -> raise Not_found
      | Some (last_pid, last_value, last_modules) ->
        if last_pid <> pid ||
          last_value <> symbol_value then raise Not_found;
        last_modules
    with Not_found ->
      let modules = f target in
      last_modules := Some (pid, symbol_value, modules);
      modules
  in
  get_modules

let get_stack_and_heap_ranges pid =
  let open Str in
  let in_channel = open_in (Printf.sprintf "/proc/%Ld/maps" pid) in
  let res = ref ("","") in
  begin
  try
    while true do
      let line = input_line in_channel in
      try
        ignore (search_forward (regexp_string "[stack]") line 0);
        res := (List.hd @@ split_delim (regexp " ") line), snd !res
      with Not_found ->
        try
          ignore (Str.search_forward (regexp_string "[heap]") line 0);
          res := fst !res, (List.hd @@ split_delim (regexp " ") line)
        with Not_found -> ();
    done
  with End_of_file -> close_in in_channel
  end;
  !res

let test_offset s ofs =
  let parse ic =
    let f x y = x,y in
    Scanf.sscanf ic "%Lx-%Lx" f in
  let x, y = parse s in
  ofs >= x && ofs <= y

let addr2section_lookup target addr =
  let a = SBTarget.resolveLoadAddress target addr in
  if SBAddress.isValid a then
    let section = SBAddress.getSection a in
    if SBSection.isValid section then
      Printf.printf "%Lx is from section %s\n" addr (SBSection.getName section)
