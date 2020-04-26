module LioStar.Ghost

unfold type erased (a: Type) = a

unfold let reveal #a (x: erased a): Tot a = x
unfold let hide #a (x: a): erased a = x

let tot_to_gtot (f : 'a -> Tot 'b) (x : 'a) : Tot 'b = f x

////////////////////////////////////////////////////////////////////////////////
// The following are all defined notions and need not be trusted
////////////////////////////////////////////////////////////////////////////////
let return (#a:Type) (x:a) : erased a = hide x

unfold let bind (#a:Type) (#b:Type) (x:erased a) (f: (a -> Tot (erased b)))
  : Tot (erased b)
  = let y = x in
    f y

irreducible
let elift1 (#a #b:Type)
           (f:(a -> Tot b))
           (x:erased a)
  : Tot (y:erased b{reveal y == f (reveal x)})
  = xx <-- x ;
    return (f xx)

irreducible
let elift2 (#a #b #c:Type)
           (f:(a -> b -> Tot c))
           (x:erased a)
           (y:erased b)
  : Tot (z:erased c{reveal z == f (reveal x) (reveal y)})
  = xx <-- x ;
    yy <-- y;
    return (f xx yy)

irreducible
let elift3 (#a #b #c #d:Type)
           (f:(a -> b -> c -> Tot d))
           (ga:erased a)
           (gb:erased b)
           (gc:erased c)
  : Tot (gd:erased d{reveal gd == f (reveal ga) (reveal gb) (reveal gc)})
  = a <-- ga;
    b <-- gb;
    c <-- gc;
    return (f a b c)

irreducible
let elift1_p (#a #b:Type)
             (#p:(a -> Type))
             ($f:(x:a{p x} -> Tot b))
             (r:erased a{p (reveal r)})
  : Tot (z:erased b{reveal z == f (reveal r)})
  = let x : (x:a { p x }) = reveal r in
    return (f x)

irreducible
let elift2_p (#a #b #c:Type)
             (#p: (a -> b -> Type))
             ($f:(xa:a -> xb:b{p xa xb} -> Tot c))
             (ra:erased a)
             (rb:erased b{p (reveal ra) (reveal rb)})
  : Tot (rc:erased c{reveal rc == f (reveal ra) (reveal rb)})
  = let x = reveal ra in
    let y : (y:b { p x y }) = reveal rb in
    return (f x y)

irreducible
let elift1_pq (#a #b:Type)
              (#p:(a -> Type))
              (#q:(x:a{p x} -> b -> Type))
              ($f:(x:a{p x} -> Tot (y:b{q x y})))
              (r:erased a{p (reveal r)})
             : Tot (z:erased b{reveal z == f (reveal r)})
  = let x : (x:a { p x }) = reveal r in
    return (f x)

irreducible
let elift2_pq (#a #b #c:Type)
              (#p:(a -> b -> Type))
              (#q:(x:a -> y:b{p x y} -> c -> Type))
              ($f:(x:a -> y:b{p x y} -> Tot (z:c{q x y z})))
              (ra:erased a)
              (rb:erased b{p (reveal ra) (reveal rb)})
             : Tot (z:erased c{reveal z == f (reveal ra) (reveal rb)})
  = let x = reveal ra in
    let y : (y:b{p x y}) = reveal rb in
    return (f x y)

