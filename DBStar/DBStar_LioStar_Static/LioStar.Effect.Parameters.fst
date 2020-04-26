module LioStar.Effect.Parameters

module LU = LatticeUsed
type stateType = unit
type labelType = LU.labels
let canFlow (a b: labelType): bool = LU.canFlow' a b
let join (a b: labelType): labelType = LU.join' a b



let lemma_relation_canFlow_join
  : l1: labelType -> l2: labelType
  -> Lemma (l1 `join` l2 == l2 ==> l1 `canFlow` l2)
  = fun _ _ -> ()
  
let lemma_canFlow_reflexivity
  : l: _ -> Lemma (ensures (l `canFlow` l))
  = fun _ -> ()


