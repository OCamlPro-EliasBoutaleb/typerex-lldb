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
open LLDBEnums
open LLDBOCaml

(* ocp-lldb modules *)
open LLDBTypes
open LLDBGlobals

(*thanks ms*)
let demangle mangled =
  let str = Bytes.copy mangled in
  let rec loop i j =
    if j >= Bytes.length str then i
    else if str.[j] = '_' && j + 1 < Bytes.length str && str.[j + 1] = '_' then
      (Bytes.set str i '.';
       loop (i + 1) (j + 2))
    else (
      Bytes.set str i str.[j];
      loop (i + 1) (j + 1))
  in
  let len = loop 0 0 in
  Bytes.sub str 4 (len-4)


(*this retrives the current module from the current frame, though it uses the mangled symbol*)
let get_current_module target =
  let process = SBTarget.getProcess target in
  let thread = SBProcess.getSelectedThread process in
  let frame = SBThread.getSelectedFrame thread in
  let name = SBFrame.getFunctionName frame in
  let mod_n = List.hd @@ Str.split (Str.regexp "\.") (demangle name) in
  mod_n

let ocaml_break_narg1 debugger funname =
  let b = Buffer.create 1000 in
  let target = SBDebugger.getSelectedTarget debugger in
  let ima = LLDBOCamlCode.get_compilation_units target in
  let modname, funname =
    try
      let pos = String.index funname '.' in
      let modname = String.sub funname 0 pos in
      let funname = String.sub funname (pos+1)
          (String.length funname -pos-1) in
      (modname, funname)
    with _ ->
      Printf.kprintf failwith "%S is not a fully-qualified function"
        funname
  in
  (try
     let cu = StringMap.find modname ima.ima_cus_by_name in
     let prefix = Printf.sprintf "caml%s__%s_" modname funname in
     let prefixlen = String.length prefix in
     Printf.eprintf "Need to match %S\n%!" prefix;
     StringMap.iter (fun sym line ->
         try
           let len = String.length sym in
           if len <= prefixlen || String.sub sym 0 prefixlen <> prefix then
             raise Exit;
           for i = prefixlen to len-1 do
             match sym.[i] with
               '0'..'9' -> ()
             | _ -> raise Exit
           done;
           (* MATCH *)
           Printf.eprintf "%s matches: setting %s:%d\n%!" sym
             cu.cu_basename line;
           let main_bp = SBTarget.breakpointCreateByLocation target
               cu.cu_basename              line in
           let nlocs = SBBreakpoint.getNumLocations main_bp in
           let id = SBBreakpoint.getID main_bp in
           Printf.bprintf b "Breakpoint %d set on %d locations\n%!"
             id nlocs;
           let _locs =
             Array.init nlocs
               (fun i ->
                  let addr = SBBreakpointLocation.getAddress
                      (SBBreakpoint.getLocationAtIndex main_bp i) in
                  let sym = SBAddress.getSymbol addr in
                  Printf.bprintf b "    (%d.%d) %s\n%!"
                    id (1+i) (SBSymbol.getName sym))
           in
           ()
         with Exit -> ()
       ) cu.cu_symbols
   with Not_found ->
     Printf.eprintf "Error: could not find module %S\n%!" modname);
  Buffer.contents b

let ocaml_gcstats debugger =
  let target = SBDebugger.getSelectedTarget debugger in
  let s = LLDBOCamlGcstats.compute_gc_stats target in
  LLDBOCamlGcstats.sprintf s

let ocaml_modules debugger =
  let b = Buffer.create 1000 in
  let target = SBDebugger.getSelectedTarget debugger in
  let ima = LLDBOCamlCode.get_compilation_units target in
  let units = ref [] in
  let nunits = ref 0 in
  Array.iter (fun cu ->
      match cu.cu_modname with
      | None -> ()
      | Some modname ->
        units := modname :: !units;
        incr nunits
    ) ima.ima_cus;
  Printf.bprintf b "Found %d OCaml modules in executable\n" !nunits;
  List.iteri (fun i modname ->
      Printf.bprintf b "[%3d] %s\n" i modname
    ) !units;
  Buffer.contents b

let ocaml_globals_map debugger =
  let b = Buffer.create 1000 in
  let target = SBDebugger.getSelectedTarget debugger in
  let (inited, globals_map) = LLDBOCamlGlobals.load_globals_map target in
  Array.iteri (fun i (modname, crc1, crc2, deps) ->
      Printf.bprintf b "[%d] %c %-30s %s %s %s\n" i
        (if i = inited then '*' else '.')
        modname (Digest.to_hex crc1) (Digest.to_hex crc2)
        (String.concat "," deps)
    ) globals_map;
  Buffer.contents b

(*WARN : does not display the current module in square bracket, but the entry point module file.*)
let ocaml_current debugger =
  let b = Buffer.create 1000 in
  let target = SBDebugger.getSelectedTarget debugger in
  let (inited, globals_map) = LLDBOCamlGlobals.load_globals_map target in
  for i = 0 to inited-1 do
    let (modname, _, _, _) = globals_map.(i) in
    Printf.bprintf b "%s " modname;
  done;
  let (modname, _, _, _) = globals_map.(inited) in
  Printf.bprintf b "[%s]\n" modname;
  Buffer.contents b

let ocaml_code debugger =
  let b = Buffer.create 1000 in
  let target = SBDebugger.getSelectedTarget debugger in
  let code_fragments = LLDBOCamlCode.get_code_info target in
  Array.iteri (fun i { code_start; code_end } ->
      Printf.bprintf b "%d -> 0x%Lx - 0x%Lx (%Ld bytes)\n"
        i code_start code_end (Int64.sub code_end code_start)
    ) code_fragments;
  Printf.bprintf b "%!";
  Buffer.contents b

let ocaml_heap debugger =
  let b = Buffer.create 1000 in
  let target = SBDebugger.getSelectedTarget debugger in
  let heap = LLDBOCamlHeap.get_heap_info target in
  Printf.bprintf b "minor heap: 0x%Lx - 0x%Lx (size %Ld kB)\n%!"
    heap.caml_young_start
    heap.caml_young_end
    (Int64.div (Int64.sub heap.caml_young_end heap.caml_young_start) 1024L);
  let sizeL = ref 0L in
  List.iter (fun (chunk_begin, chunk_end) ->
      sizeL := Int64.add !sizeL (Int64.sub chunk_end chunk_begin)
    ) heap.caml_chunks;
  Printf.bprintf b "major heap: size %Ld kB\n" (Int64.div !sizeL 1024L);
  List.iter (fun (chunk_begin, chunk_end) ->
      Printf.bprintf b "   0x%Lx - 0x%Lx (size %Ld kB)\n%!"
        chunk_begin chunk_end
        (Int64.div (Int64.sub chunk_end chunk_begin) 1024L)
    ) heap.caml_chunks;
  Buffer.contents b

let ocaml_targets debugger =
  let b = Buffer.create 1000 in
  let target = SBDebugger.getSelectedTarget debugger in
  let nm = SBTarget.getNumModules target in
  Printf.bprintf b "%d components in executable\n%!" nm;

  let _modules = Array.init nm (fun i ->
      let m = SBTarget.getModuleAtIndex target i in
      Printf.bprintf b "component %S\n" (SBModule.to_string m);
      let n = SBModule.getNumCompileUnits m in
      let _cus = Array.init n (fun i ->
          SBModule.getCompileUnitAtIndex m i
        ) in
      Printf.bprintf b "%d compilation units in this component\n%!" n
    ) in
  Buffer.contents b

let ocaml_target debugger =
  let b = Buffer.create 1000 in
  let target = SBDebugger.getSelectedTarget debugger in
  let ima = LLDBOCamlCode.get_compilation_units target in
  Printf.bprintf b "%d compilation units in this component\n%!"
    (Array.length ima.ima_cus);
  Array.iteri (fun i cu ->
      match cu.cu_modname with
      | None ->
        Printf.bprintf b "{\n";
        Printf.bprintf b "  cu_descr = %S\n" cu.cu_descr;
        Printf.bprintf b "  cu_basename = %S\n" cu.cu_basename;
        Printf.bprintf b "  cu_dirname = %S\n" cu.cu_dirname;
        Printf.bprintf b "  cu_symbols = { %d symbols }\n"
          (StringMap.cardinal cu.cu_symbols);
        Printf.bprintf b "}\n";
      | Some modname ->
        Printf.bprintf b "%3d -> %s\n%!" i modname;
        Printf.bprintf b "  %s ... %s\n" cu.cu_dirname cu.cu_basename;
        StringMap.iter (fun name line ->
            Printf.bprintf b "  %s -> %s:%d\n"
              name cu.cu_basename line
          ) cu.cu_symbols;
    ) ima.ima_cus;
  Printf.bprintf b "%!";
  Buffer.contents b

let ocaml_target_narg1 debugger modname =
  let b = Buffer.create 1000 in
  let target = SBDebugger.getSelectedTarget debugger in
  let ima = LLDBOCamlCode.get_compilation_units target in
  begin
    try
      let cu = StringMap.find modname ima.ima_cus_by_name in
      Printf.bprintf b "  %s ... %s\n" cu.cu_dirname cu.cu_basename;
      StringMap.iter (fun name line ->
          Printf.bprintf b "  %s -> %s:%d\n"
            name cu.cu_basename line
        ) cu.cu_symbols;
      Printf.bprintf b "%!"
    with Not_found ->
      Printf.bprintf b "Compilation unit not found\n%!"
  end;
  Buffer.contents b

let ocaml_paths debugger =
  let b = Buffer.create 1000 in
  let target = SBDebugger.getSelectedTarget debugger in
  let ima = LLDBOCamlCode.get_compilation_units target in
  let paths = ref StringMap.empty in
  Array.iter (fun cu ->
      try
        let r = StringMap.find cu.cu_dirname !paths in
        r := cu.cu_basename :: !r
      with Not_found ->
        paths :=
          StringMap.add cu.cu_dirname (ref [cu.cu_basename]) !paths
    ) ima.ima_cus;
  StringMap.iter (fun path files ->
      Printf.bprintf b "Path: %s\n%!" path
    ) !paths;
  Printf.bprintf b "You can use 'settings set target.source-map PATH1 PATH2'\n";
  Printf.bprintf b "to translate these paths to yours.\n%!";
  Buffer.contents b

let strip s = if s = "" then s else List.hd @@ Str.split (Str.regexp "/") s

let print_var target value name et tds vf =
  let b = Buffer.create 1000 in
  let heap = LLDBOCamlHeap.get_heap_info target in
  let mem = LLDBOCamlHeap.get_memory_info target in

  (match et with
   | [et] ->
     begin
       let typ = Symtbl.print_type et in
       if SBValue.isInScope value
       then begin
         let final = SBValue.getValueAsUnsigned1 value (-42L) in
         if final <> (-42L)
         then Printf.bprintf b "%s = %s" name (LLDBOCamlValue.print_value target mem heap final [et] tds vf)
         else Printf.bprintf b "%s = not available : %s\n" name typ
       end
       else Printf.bprintf b "%s = not in scope : %s\n" name typ
     end
   | _ ->
     begin
       Printf.bprintf b "%s : <type unavailable>" name;
       let final = SBValue.getValueAsUnsigned1 value (-42L) in
       if final <> (-42L) then begin
         Printf.bprintf b " = ";
         let s = LLDBOCamlValue.print_value target mem heap final et tds vf in
         Printf.bprintf b "%s" s;
       end;
       Printf.bprintf b "\n"
     end);
  Buffer.contents b

let ocaml_print_locals debugger var vf =
  let b = Buffer.create 10000 in
  let target = SBDebugger.getSelectedTarget debugger in
  let process = SBTarget.getProcess target in
  let thread = SBProcess.getSelectedThread process in
  let frame = SBThread.getSelectedFrame thread in

  let curr_modname = get_current_module target in

  let get_type_and_env z var =
    match (Symtbl.find_sym z var) with
    | (_,_,te,_) :: _ -> [te]
    | _ -> [] in

  match LLDBOCamlTypes.load_tt target curr_modname with
  | Some (et, tds) ->
    begin

      if var = ""
      then begin

        (* Variables introduced further down in the backend such as `bound` and `i_$stamp` in a for loop
           might appear in the DWARF. Those variables are then processed.*)

        let values = SBFrame.getVariables frame true true false true in
        let size = SBValueList.getSize values in
        for i = 0 to size - 1 do

          let value = SBValueList.getValueAtIndex values i in
          let name = SBValue.getName value in
          (
            let re = get_type_and_env et name in
            let s = print_var target value name re tds vf in Printf.bprintf b "%s" s
          )
        done;
        Buffer.contents b
      end else
        let re = get_type_and_env et var in
        print_var target (SBFrame.findVariable frame var) var re tds vf;

    end
  | None -> Printf.sprintf "ttree not found\n"

#ifndef OCAML_NON_OCP

let ocaml_locids debugger =
  let target = SBDebugger.getSelectedTarget debugger in
  let _locs = LLDBOCamlLocids.load target in
  Printf.sprintf "Location table loaded.\n%!"

let ocaml_globals_narg1 debugger modname =
  let target = SBDebugger.getSelectedTarget debugger in
  let heap = LLDBOCamlHeap.get_heap_info target in
  let mem = LLDBOCamlHeap.get_memory_info target in
  LLDBOCamlGlobals.print_module_globals target mem heap modname

let ocaml_globals debugger =
  let target = SBDebugger.getSelectedTarget debugger in
  LLDBOCamlGlobals.print_globals target

let ocaml_global_narg1 debugger global =
  let (modname, ident) =
    try
      let pos = String.index global '.' in
      let modname = String.sub global 0 pos in
      let funname = String.sub global (pos+1)
          (String.length global -pos-1) in
      (modname, funname)
    with _ ->
      Printf.kprintf failwith "%S is not a fully-qualified function"
        global
  in

  let target = SBDebugger.getSelectedTarget debugger in
  let heap = LLDBOCamlHeap.get_heap_info target in
  let mem = LLDBOCamlHeap.get_memory_info target in
  LLDBOCamlGlobals.print_module_global target mem heap modname ident

let ocaml_args_narg1 debugger nargs =
  let nargs = try
      int_of_string nargs
    with _ -> failwith "Argument of 'args' should be a number"
  in
  let target = SBDebugger.getSelectedTarget debugger in
  let heap = LLDBOCamlHeap.get_heap_info target in
  let mem = LLDBOCamlHeap.get_memory_info target in
  LLDBOCamlStack.print_args target mem heap nargs

let ocaml_reg_narg1 debugger reg =
  let target = SBDebugger.getSelectedTarget debugger in
  let heap = LLDBOCamlHeap.get_heap_info target in
  let mem = LLDBOCamlHeap.get_memory_info target in
  LLDBOCamlStack.print_reg target mem heap reg

#endif

let ocaml_set variable values =
  try
    match variable, values with
    | "max_indent", [ v ] -> LLDBOCamlValue.max_indent := int_of_string v
    | _, _ -> raise Not_found
  with exn ->
    Printf.eprintf "Exception %S while setting variable %S\n%!"
      (Printexc.to_string exn) variable

let ocaml_command debugger args =
  match Array.to_list args with
  | [ ("break" | "b"); funname ] -> ocaml_break_narg1 debugger funname
  | [ "debug" ] ->
    verbose := true;
    Printf.sprintf "Debug mode set\n%!"

  | "set" :: variable :: values -> ocaml_set variable values; ""
  | [ "modules" ] -> ocaml_modules debugger
  | [ "globals_map" ] -> ocaml_globals_map debugger
  | [ "current" ] -> ocaml_current debugger
  | [ "gcstats" ] -> ocaml_gcstats debugger
  | [ "code" ] -> ocaml_code debugger
  | [ "heap" ] -> ocaml_heap debugger
  | [ "targets" ] -> ocaml_targets debugger
  | [ "target" ] -> ocaml_target debugger
  | [ "target"; modname ] -> ocaml_target_narg1 debugger modname
  | [ "paths" ] -> ocaml_paths debugger
  | [ "print"; "locals"] -> ocaml_print_locals debugger "" false
  | [ "print"; "var"; var_name] -> ocaml_print_locals debugger var_name false
  | [ "printv"; "locals"] -> ocaml_print_locals debugger "" true
  | [ "printv"; "var"; var_name] -> ocaml_print_locals debugger var_name true

#ifndef OCAML_NON_OCP
  | [ "locids" ] -> ocaml_locids debugger
  | [ "globals"; modname ] -> ocaml_globals_narg1 debugger modname
  | [ "globals" ] -> ocaml_globals debugger
  | [ "global"; global ] -> ocaml_global_narg1 debugger global
  | [ "args"; nargs ] -> ocaml_args_narg1 debugger nargs
  | [ "reg"; reg ] -> ocaml_reg_narg1 debugger reg
#endif

  | [ "help" ] | [] ->

    let b = Buffer.create 1000 in
    Printf.bprintf b "Help on OCaml commands:\n";
    Printf.bprintf b "  'ocaml modules': list OCaml modules in executable\n%!";
    Printf.bprintf b "  'ocaml globals_map': extract and display globals_map\n%!";
    Printf.bprintf b "  'ocaml current': list evaluated modules until now\n%!";
    Printf.bprintf b "  'ocaml break Module.function': set a breakpoint on an OCaml function\n%!";
    Printf.bprintf b "  'ocaml heap' : print heap information\n%!";
    Printf.bprintf b "  'ocaml gcstats' : print GC stats\n%!";
    Printf.bprintf b "  'ocaml code' : print code segments\n%!";
    Printf.bprintf b "  'ocaml targets' : print information on binary components\n%!";
    Printf.bprintf b "  'ocaml paths' : print paths to sources\n%!";
    Printf.bprintf b "  'ocaml args NARGS' : print NARGS first arguments\n";
    Printf.bprintf b "  'ocaml reg RAX' : print register as an OCaml value\n";
    Printf.bprintf b "  'ocaml globals MODULE' : print all globals of MODULE\n";
    Printf.bprintf b "  'ocaml global MODULE.VALUE' : print fully-qualified global\n";
    Printf.bprintf b "  'ocaml print(v) locals' : list all available OCaml variables\n%!";
    Printf.bprintf b "  'ocaml print(v) var VARIABLE' : print information on OCaml variable\n%!";
    Printf.bprintf b "  'ocaml typeof VARIABLE' : print type information of an OCaml variable\n%!";

    Printf.bprintf b "  'ocaml target Module' : print target info on Module\n%!";

    Printf.bprintf b "  'ocaml print 0xFFF' : print information on value at 0xFFF\n%!";
    Printf.bprintf b "  'ocaml target' : print target info\n%!";

    Printf.bprintf b "%!";
    Buffer.contents b

  | _ ->
    let b = Buffer.create 1000 in
    Printf.bprintf b "No such command:\n";
    Array.iteri (fun i cmd ->
      Printf.bprintf b "[%d] -> %S\n%!" i cmd
    ) args;
    Printf.bprintf b "Use 'ocaml help' for help\n%!";
    Buffer.contents b

let ocaml_command debugger args =
  (try
    ocaml_command debugger args
  with e ->
    Printf.sprintf "ocaml_command: exception %s\n%!"
      (Printexc.to_string e))
