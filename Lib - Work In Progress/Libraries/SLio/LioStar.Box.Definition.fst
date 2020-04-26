module LioStar.Box.Definition

module G = LioStar.Ghost

noeq
type box 
  (labelType: Type0)
  (canFlow: labelType -> labelType -> bool)
  (labeled: Type0 -> Type0)
  (labelOf: ((#a: Type0) -> labeled a -> labelType))
  (a: Type0)
= {
  value: labeled a; 
  label: (b: labelType{G.reveal (labelOf value) `canFlow` b})
}
