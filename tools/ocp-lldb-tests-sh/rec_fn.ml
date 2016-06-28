(*need to step into recursive call then next to break right before next recursive call*)
(*doing next only plainly skip the other recursive calls*)

(*how and where should the list argument should be read in sigma?*)

(*TODO*)
(*add bp for base recursion case *)

let rec sigma f = function
    (*bp absent*)
    | [] -> 0
    (*bp present*)
    | x :: l -> f x + sigma f l

let _=
    (*bp present*)
    sigma (fun x -> x * x) [1; 2; 3]
    (*bp absent - return value is discarded but we might want to store that value*)
