module LioStar.Effect.Parameters
open Lattice
open FStar.Tactics.Typeclasses



// type stateType = {}


// type stateTypeMaker:
//     (labeled: (Type0 -> Type0))
//   -> (labelOf: (#a: Type0 -> labeled a -> labelType))
//   -> Type0
//   = fun _ _ -> unit


assume new type labelType

[@tcinstance]
assume val labelTypeHasLattice : lattice labelType