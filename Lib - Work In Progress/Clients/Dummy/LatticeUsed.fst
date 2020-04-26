module LatticeUsed

open Lattice
open FStar.Tactics.Typeclasses

type labelType = 
  | H
  | L

// [@tcinstance]
// inline_for_extraction unfold 
// let labelTypeHasLattice: lattice nat = admit (); makeSimpleLattice #nat (<=) (fun x y -> if x > y then x else y)

let tcanFlow x y =
    match x, y with
    | L, L | L, H | H, H -> true
    | _ -> false

let tjoin x y =
    match x, y with
    | _, H | H, _ -> H
    | _ -> L
  
let teq x y =
  match x, y with
  | H, H | L, L -> true
  | _ -> false

instance labelTypeHasLattice: lattice labelType
=
{ equals  = teq;
  canFlow = tcanFlow;
  join    = tjoin;
  lawJoin = (fun _ _ _ -> ());// 3
  lawFlowReflexivity  = (fun _ -> ()); //x;//fun _ -> x;
  lawFlowAntisymetry  = (fun _ _ -> ()); //y;//fun _ _ -> y;
  lawFlowTransitivity = (fun _ _ _ -> ()); //z;//3
}


