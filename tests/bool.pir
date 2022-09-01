let aa = fun x y ->
    let a = 5 in
        x + y;
        x*y=3;;

aa 5 6;;

let bool a x = x*(x-a) = 0;;

let map (f,m) (a,b,c,d) =
    f a;
    f b;
    f c;
    f d;;

map (bool 1,0) c;;

fun f -> f a;;
