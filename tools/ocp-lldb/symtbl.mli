val vb : Typedtree.structure -> unit

val typ_tbl : (string, Env.t * Types.type_expr) Hashtbl.t ref
val print_type : Env.t -> Types.type_expr -> string
val vb_tbl : (string, Location.t * string * string) Hashtbl.t ref
val tydecl_tbl : (string, Types.type_declaration) Hashtbl.t ref

