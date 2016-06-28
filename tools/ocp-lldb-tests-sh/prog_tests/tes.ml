Random.self_init();;

let z = 18

let ass x = let ah = 45 * 34 in ("dd", 3 + Random.int x)

let rec main x =
    let g = Random.int 123 in
    let a = 42 in
    let b = 43 in
    let c = 44 in
    let d = 45 in
    let e = 46 in
    let f = 47 in
    let k =
        let bb = 3 + Random.int 12 in
        2 + bb + (snd @@ ass bb) in
    let h = g + a * b + c / d + e * f + k in
    let i ar =
        let wou = 3 + Random.int 12 in
        2 + ar + (snd @@ ass wou) in
    if x = 0 then h else h * (main (x-1))

let q = 18

let _ =
    main (Random.int 4)
