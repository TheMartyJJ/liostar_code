module LioStar.Effect.Parameters
open LioStar.Box.Definition
open Lattice
open FStar.Tactics.Typeclasses

module G = LioStar.Ghost

assume new type labelType

[@tcinstance]
assume val labelTypeHasLattice: lattice labelType

private
let box' labeled labelOf a = box labelType canFlow labeled labelOf a

assume new type stateTypeMaker:
    (labeled: (Type0 -> Type0))
  -> (labelOf: (#a: Type0 -> labeled a -> G.erased labelType))
  -> Type0

