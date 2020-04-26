module Clients.Dummy

open LioStar.Effect.Parameters
open LioStar.Effect
module G = LioStar.Ghost

let eqLabeled (v1 v2 :labeled int) : Ifc bool
 = let i1 = unlabel v1 in
   // current label raised to the label of v1 
   let i2 = unlabel v2 in
   // current label raised to the label of v2 
   (i1 > i2 = false) && (i1 < i2 = false)

let checkLabeled (l:labelType) (i:int) (lv:labeled int) : Ifc bool 
= let lv' = label i l in
  // exception if current label cannot flow to l 
  eqLabeled lv lv'

