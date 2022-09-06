let aa = fun x y ->
    let a = 50 in
        x*y = 30;;

aa 5 6;;

// constrains values to be 0 or a
let bool a x = x*(x-a) = 0;;

let map (f,m) (a,b,c,d) =
    f a;
    f b;
    f c;
    f d;;

map (bool 1,0) c;;
//map (bool 1,0) c c;;

fun f -> f a;;
