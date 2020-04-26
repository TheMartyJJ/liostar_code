module Clients.Dummy

open LioStar.Box
open LioStar.Effect.Parameters
open LioStar.Effect
module G = LioStar.Ghost

let eqLabeled (v1 v2 :labeled int) : Ifc bool
	(requires fun c -> unlabel_pre v1 c /\ unlabel_pre v2 c)
	(ensures fun c1 x c2 ->
          G.reveal c2.cur == G.reveal (labelOf v2) `join` (labelOf v1 `g_join` c1.cur)
        )
 = let i1 = unlabel v1 in
   // current label raised to the label of v1 
   let i2 = unlabel v2 in
   // current label raised to the label of v2 
   (i1 > i2 = false) && (i1 < i2 = false)

let checkLabeled (l:labelType) (i:int) (lv:labeled int) : Ifc bool 
	(requires fun c -> label_pre (G.hide l) c
                      /\ unlabel_pre lv c
                      /\ preCanReach l c)
	(ensures fun l0 x l1 -> True)
= let lv' = label i (G.hide l) in
  // exception if current label cannot flow to l 
  eqLabeled lv lv'

