let aa = fun x y ->
    let a = 5 in
        x + y;
        x*y=3;;

aa 5 6;;

let bool x = x*(x-1) = 0;;

let map f (a,b,c,d) =
    f a;
    f b;
    f c;
    f d;;

map bool (5, 6, 7, 8);;

fun f -> f a;;
