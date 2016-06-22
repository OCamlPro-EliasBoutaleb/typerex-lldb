open LLDBEnums
open LLDBOCaml

let handleCommand debugger interp cmd =
  let result = SBCommandReturnObject.create () in
  let _ = SBCommandInterpreter.handleCommand interp cmd result false in
  let s = SBCommandReturnObject.getOutput result in
  Printf.printf "%s" s

let run_one_liner target_path one_liner = ()

let run_batch target_path script_path =

  SBDebugger.initialize ();
  let debugger = SBDebugger.create false in

 (*When we step or continue, don't return from the function until the process*)
 (*stops. We do this by setting the async mode to false.*)
  SBDebugger.setAsync debugger false;

  let _ = SBDebugger.createTargetByName debugger target_path in
  let interp = SBDebugger.getCommandInterpreter debugger in

  SBCommandInterpreter.addCommand interp
    "ocaml" (LLDBOCamlCommand.ocaml_command debugger) "help for ocaml";

  (*exception raised if the file does not exist*)
  let in_channel = open_in script_path in
  begin
  try
    while true do
      let cmd = String.trim @@ input_line in_channel in
        if cmd <> "" then handleCommand debugger interp cmd
    done
  with End_of_file -> close_in in_channel
  end;

  SBDebugger.destroy debugger;
  SBDebugger.terminate ();
  exit 0;

