module Bus.Example


//include Core.LioStar (* this include enable LioStar *)
include Core.Lio     (* this include enable Lio in FStar *)

(* ****** Example *)

(* Code example **)
type components = x:labels{(E? x \/ M? x \/ C? x)}
module U8 = FStar.UInt8
type byte = U8.t

assume val write : (actor:components) 
  -> (data:byte) 
  -> Ifc (unit) 
  (requires fun l0 -> True)
  (ensures fun l0 x l1 ->
    l0 `eq` l1
  ) 

assume val read : (actor:components) 
  -> IfcClearance (byte) 
  (requires fun l0 p0 -> p0 (join l0 actor))
  (ensures fun l0 x l1 p0 p1 ->
    l0 `eq` l1
    /\ p0 == p1
    /\ prop_monotonicity p0 p1 /\ p1 l0
  ) 


assume val getSource : unit
  -> Ifc (components) 
  (requires fun l0 -> True)
  (ensures fun l0 x l1 ->
    l0 `eq` l1 
  ) 
  
assume val getDestination : unit
  -> Ifc (components) 
  (requires fun l0 -> True)
  (ensures fun l0 x l1 ->
    l0 `eq` l1 
  ) 


let readBUS (actor:components) : IfcClearance (labeled byte)
  (requires fun l0 p0 -> p0 (join l0 actor))
  (ensures fun l0 x l1 p0 p1 ->
    (mapAB (labelOf x)) `eq` actor
    /\ p0 == p1
    /\ l0 `eq` l1
  ) = 
  //let x =  toLabeled actor read in
  labelUNSAFE (read actor) (mapBA actor)

let writeBUS (data:labeled byte) (dst:components) : Ifc (unit) 
  (requires fun l0 -> True)
  (ensures fun l0 x l1 ->
    l0 `eq` l1
  ) = 
  let c = get () in
  write dst (unlabelUNSAFE data)


let actor_pure p0 = p0 E /\ p0 M /\ p0 C

let receive (starting:bool) : IfcClearance (unit) 
  (requires fun l0 p0 -> l0 `eq` Bot
    /\ actor_pure p0 /\ (starting ==> p0 CM)
  )
  (ensures fun l0 x l1 p0 p1 -> 
    p0 == p1) =
  let src = getSource () in
  let dst = getDestination () in
  let msg = readBUS src in

  let x = unlabel msg in
  let msg = label (U8.add_underspec x 1uy) (labelOf msg) in
  
  if starting then (
    (* starting mode only C can talk to M *)
    if (C? src && M? dst) then (
      raise (mapBA CM);
      writeBUS msg dst
    ) else ()
  )else  
    (* in other mode only logging is possible *)
    if (E? dst) then (
      writeBUS msg E
    ) else ()


module I32 = FStar.Int32
module U32 = FStar.UInt32
                   
let help (p:bool) : IfcClearance (unit)
    (requires fun l0 p0 -> l0 `eq` Bot /\ actor_pure p0 /\ (p ==> p0 CM))
    (ensures fun l0 x l1 p0 p1 -> p0 == p1 /\ p1 l1 /\ prop_monotonicity p0 p1 /\ p1 l0) = receive p

let rec tryAlot (n:bool) (step:U32.t) : IfcClearance (unit) (decreases %[U32.v step])
(requires fun l0 p0 -> l0 `eq` Bot /\ actor_pure p0 /\ (n ==> p0 CM))
  (ensures fun l0 x l1 p0 p1 -> l0 `eq` l1 /\ p0 == p1) =
  let _ = toLabeled  n (help) in
  if (step `U32.gt` 0ul) then
    tryAlot false (step `U32.sub` 1ul)
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
  let _ = toLabeled true (help) in
  setClearance (fun l -> ~(CM? l));
  tryAlot false (75000000ul);
  0l 

