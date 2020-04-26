module LioStar.Effect.Parameters
open LioStar.Box.Definition

module G = LioStar.Ghost
open Lattice
open FStar.Tactics.Typeclasses

include LatticeUsed

private
let box' labeled labelOf a = box labelType labelTypeHasLattice.canFlow labeled labelOf a

type stateTypeMaker:
    (labeled: (Type0 -> Type0))
  -> (labelOf: (#a: Type0 -> labeled a -> labelType))
  -> Type0
  = fun _ _ -> unit

