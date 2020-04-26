module LioStar.Effect.Parameters

assume new type stateType
assume new type labelType
assume val canFlow: labelType -> labelType -> bool
assume val join: labelType -> labelType -> labelType

assume val lemma_relation_canFlow_join
  : l1: labelType -> l2: labelType
  -> Lemma (l1 `join` l2 == l2 ==> l1 `canFlow` l2)

assume val lemma_canFlow_reflexivity
  : l: _ -> Lemma (ensures (l `canFlow` l))
