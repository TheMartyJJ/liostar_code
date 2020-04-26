module Clients.Dummy

open LioStar.Effect.Parameters
open LioStar.Effect
module U32 = FStar.Int32

// let eq x y = (x `U32.lte` y) && (y `U32.lte` x)
let eq x y = x `U32.eq` y

let eqLabeled (v1 v2 :labeled U32.t) : Ifc bool
	(requires fun c -> unlabel_pre v1 c /\ unlabel_pre v2 c)
	(ensures fun c1 x c2 ->
          c2.cur == labelOf v2 `join` (labelOf v1 `g_join` c1.cur)
        )
 = let i1 = unlabel v1 in
   // current label raised to the label of v1 
   let i2 = unlabel v2 in
   // current label raised to the label of v2 
   i1 `eq` i2

let checkLabeled (l:labelType) (i:U32.t) (lv:labeled U32.t) : Ifc bool 
	(requires fun c -> label_pre l c
                      /\ preCanReach (labelOf lv) c
                      /\ preCanReach l c)
	(ensures fun l0 x l1 -> True)
= let lv' = label i l in
  // exception if current label cannot flow to l 
  eqLabeled lv lv'

let main (): Ifc U32.t
    (fun c -> 
         label_pre H c
       /\ preCanReach H c
    )
    (fun _ _ _ -> True)
  = if checkLabeled H 1l (label 2l H)
    then 0l
    else 1l



