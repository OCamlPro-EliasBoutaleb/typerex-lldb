val vb : Typedtree.structure ->
    (string, Env.t * Types.type_expr) Hashtbl.t *
    (string, Types.type_declaration) Hashtbl.t *
    (string, Location.t * string * string) Hashtbl.t

val print_type : Env.t -> Types.type_expr -> string

