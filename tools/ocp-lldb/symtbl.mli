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

val find_sym : sym_info Zipper.tree -> string -> (string * string * type_and_env * string) list
val vb : Typedtree.structure -> sym_info Zipper.tree * (string, Types.type_declaration) Hashtbl.t
val print_type : Env.t * Types.type_expr -> string
