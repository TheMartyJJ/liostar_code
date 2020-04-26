module MMU.Example


include Core.LioStar (* this include enable LioStar *)
//include Core.Lio     (* this include enable Lio in FStar *)

(* ****** Example *)

(* Code example **)
type components = x:labels{(E? x \/ M? x \/ C? x)}
module U8 = FStar.UInt8
module Addr = FStar.UInt32
type byte = U8.t

assume val write_memory : (addr:Addr.t)
  -> (data:byte) 
  -> Ifc (unit) 
  (requires fun l0 -> True)
  (ensures fun l0 x l1 ->
    l0 `eq` l1
  ) 

assume val read_memory : (addr:Addr.t) 
  -> IfcClearance (byte) 
  (requires fun l0 p0 -> p0 l0)
  (ensures fun l0 x l1 p0 p1 ->
    l0 `eq` l1
    /\ p0 == p1
    /\ prop_monotonicity p0 p1 /\ p1 l0
  ) 


let taskSize = 512ul
let pageSize = 32ul

type virtual_address = {vatag:components; page:Addr.t; offset:Addr.t}
let tag2nb t = match t with
 | Bot -> 0ul
 | C   -> 1ul 
 | CM  -> 4ul
 | M   -> 2ul
 | E   -> 3ul


let isBound va = 
  let ts, ps, t, p, o = Addr.(v taskSize, v pageSize, v (tag2nb va.vatag), v va.page, v va.offset) in
  let m = FStar.Mul.op_Star in
  (ts `m` t) + (ps `m` p) + o < pow2 Addr.n

let translation va b : IfcClearance (Addr.t) 
  (requires fun l0 p0 -> p0 l0
    /\ isBound va)
  (ensures fun l0 x l1 p0 p1 -> l0 `eq` l1 
    /\ (let ts, ps, t, p, o = Addr.(v taskSize, v pageSize, v (tag2nb va.vatag), v va.page, v va.offset) in
           let m = FStar.Mul.op_Star in
           (ts `m` t) + (ps `m` p) + o = Addr.v x)
    /\ p0 == p1)= 
    Addr.add 
      (Addr.add 
        (Addr.mul taskSize (tag2nb va.vatag))
        (Addr.mul pageSize va.page)
      )
      va.offset

let readMMU (actor:components) p o : IfcClearance (labeled byte)
  (requires fun l0 p0 -> p0 (join l0 actor)
   /\ isBound ({vatag=actor; page=p; offset=o}))
  (ensures fun l0 x l1 p0 p1 ->
    (mapAB (labelOf x)) `eq` actor
    /\ p0 == p1
    /\ l0 `eq` l1
  ) = 
  //let x =  toLabeled actor read in
  let real = translation ({vatag=actor; page=p; offset=o}) false in
  labelUNSAFE (read_memory real) (mapBA actor)

let writeMMU (data:labeled byte) (dst:components) p o : IfcClearance (unit) 
  (requires fun l0 p0 -> p0 l0
    /\ isBound ({vatag=dst; page=p; offset=o}))
  (ensures fun l0 x l1 p0 p1 ->
    l0 `eq` l1
    /\ p0 == p1
  ) = 
  write_memory (translation ({vatag=dst; page=p; offset=o}) true) (unlabelUNSAFE data)


let actor_pure p0 = p0 E /\ p0 M /\ p0 C

let taskC () : IfcClearance (unit) 
  (requires fun l0 p0 -> l0 `eq` Bot
    /\ p0 CM
  )
  (ensures fun l0 x l1 p0 p1 -> 
    p0 == p1
    /\ p1 l1 /\ prop_monotonicity p0 p1 /\ p1 l0) =
  let x = label 1uy C in
  let y = label 2uy C in
  writeMMU x M 0ul 0ul; 
  writeMMU y M 0ul 1ul; 
  ()

let taskM () : IfcClearance (unit)
  (requires fun l0 p0 -> l0 `eq` Bot
    /\ p0 M
  )
  (ensures fun l0 x l1 p0 p1 -> 
    p0 == p1
    /\ p1 l1 /\ prop_monotonicity p0 p1 /\ p1 l0) =
                                         // Bot
  let x = unlabel (readMMU M 0ul 0ul) in // M
  let y = unlabel (readMMU M 0ul 1ul) in // M
  let r = label (U8.add_underspec x y) M in
  writeMMU r M 0ul 2ul

let instanceOS  () : IfcClearance (unit) 
  (requires fun l0 p0 -> l0 `eq` Bot
    /\ p0 CM /\ p0 M
  )
  (ensures fun l0 x l1 p0 p1 -> 
    p0 == p1
    /\ p1 l1 /\ prop_monotonicity p0 p1 /\ p1 l0) =
  let _ = toLabeled () taskC in
  let _ = toLabeled () taskM in
  ()

module I32 = FStar.Int32
module U32 = FStar.UInt32
                   
let help () : IfcClearance (unit)
    (requires fun l0 p0 -> l0 `eq` Bot /\ p0 CM /\ p0 M)
    (ensures fun l0 x l1 p0 p1 -> p0 == p1 /\ p1 l1 /\ prop_monotonicity p0 p1 /\ p1 l0) = instanceOS ()

let rec tryAlot (step:U32.t) : IfcClearance (unit) (decreases %[U32.v step])
(requires fun l0 p0 -> l0 `eq` Bot /\ p0 CM /\ p0 M)
  (ensures fun l0 x l1 p0 p1 -> l0 `eq` l1 /\ p0 == p1) =
  let _ = toLabeled  () (help) in
  if (step `U32.gt` 0ul) then
    tryAlot (step `U32.sub` 1ul)
  else
    ()


assume val mkBigStack : (_:unit) -> Ifc (unit)
  (requires fun _ -> True)
  (ensures fun l0 x l1 -> l0 `eq` l1)


let topall (l:labels) : GTot Type0 = l `canFlow` E

let main () : IfcClearance (I32.t)
  (requires fun l0 p0 -> l0 `eq` Bot /\ p0 == topall)
  (ensures fun l0 x l1 p0 p1 -> True) = //l0 `eq` l1) =
  mkBigStack ();
  assert(topall CM);
  tryAlot (75000000ul);
  0l 

