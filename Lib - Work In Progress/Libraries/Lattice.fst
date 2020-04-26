module Lattice

(*** Lattice definition *)

open FStar.Tactics.Typeclasses

// unfold let reflexivity f x = x `f` x
// unfold let antisymetry f eq x y = (x `f` y /\ y `f` x) `eq` 

class lattice a = {
  equals:a->a->bool;
  
  (* lattice operations *)
  canFlow : a -> a -> bool;
  // meet: a -> a -> Tot a;
  join: a -> a -> a;

  (* lattice constants *) 
  // bottom: a;
  // top:a;

  (* lattice properties *)
  // lawBot: (l:a) -> Lemma (ensures (bottom `canFlow` l)); 
  lawFlowReflexivity : l:a -> Lemma (l `canFlow` l);
  lawFlowAntisymetry : x: a -> y: a -> Lemma 
    ((x `canFlow` y /\ y `canFlow` x) ==> x `equals` y);
  
  lawFlowTransitivity : x: a -> y: a -> z: a -> Lemma 
    ((x `canFlow` y /\ y `canFlow` z) ==> x `canFlow` z);
  
  // lawMeet : (z:a) -> x: a -> y: a -> Lemma 
  //   (ensures z `equals` (x `meet` y) 
  //            ==> z `canFlow` x /\ z `canFlow` y /\ 
  //                (forall (l:a) . l `canFlow` x /\ l `canFlow` y ==> l `canFlow` z));
  
  lawJoin : z: a -> x: a -> y: a -> Lemma 
    (z `equals` (x `join` y) ==> 
     x `canFlow` z /\ y `canFlow` z /\ (forall (l:a) . x `canFlow` l /\ y `canFlow` l 
        ==> z `canFlow` l));
}



let makeSimpleLattice (#a: eqtype) (canFlow: a -> a -> bool) (join: _ {
    (forall l. l `canFlow` l)
  /\ (forall x y. (x `canFlow` y /\ y `canFlow` x) ==> x = y)
  /\ (forall x y z. (x `canFlow` y /\ y `canFlow` z) ==> x `canFlow` z)
  /\ (forall x y z l. z = (x `join` y) ==> 
     x `canFlow` z /\ y `canFlow` z /\ (forall (l:a) . x `canFlow` l /\ y `canFlow` l 
        ==> z `canFlow` l))
}) : lattice a = 
{ equals  = (=);
  canFlow = canFlow;
  join    = join;
  lawJoin = (fun _ _ _ -> admit ());// 3
  lawFlowReflexivity  = (fun _ -> ()); //x;//fun _ -> x;
  lawFlowAntisymetry  = (fun _ _ -> ()); //y;//fun _ _ -> y;
  lawFlowTransitivity = (fun _ _ _ -> ()); //z;//3
}


