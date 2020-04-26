module Core.Lattice

(*** Lattice definition *)

open FStar.Tactics.Typeclasses

class lattice a = {
  value:(b:Type{b === a}); // trick to keep type knowledge
  equals:a->a->Tot bool;
  (* lattice operations *)
  canFlow : a -> a -> Tot bool;
  meet: a -> a -> Tot a;
  join: a -> a -> Tot a;

  (* lattice constants *) 
  bottom: a;
  top:a;

  (* lattice properties *)
  lawBot: (l:a) -> Lemma (ensures (bottom `canFlow` l)); 
  lawFlowReflexivity : (l:a) -> Lemma (ensures (l `canFlow` l));
  
  lawFlowAntisymetry : (l1:a) -> (l2:a) -> Lemma 
    (ensures (l1 `canFlow` l2 /\ l2 `canFlow` l1) ==> (l1 `equals` l2));
  
  lawFlowTransitivity : (l1:a) -> (l2:a) -> (l3:a) -> Lemma 
    (ensures (l1 `canFlow` l2 /\ l2 `canFlow` l3) ==> (l1 `canFlow` l3));
  
  lawMeet : (z:a) -> (l1:a) -> (l2:a) -> Lemma 
    (ensures z `equals` (l1 `meet` l2) 
             ==> z `canFlow` l1 /\ z `canFlow` l2 /\ 
                 (forall (l:a) . l `canFlow` l1 /\ l `canFlow` l2 ==> l `canFlow` z));
  
  lawJoin : (z:a) -> (l1:a) -> (l2:a) -> Lemma 
    (ensures z `equals` (l1 `join` l2) ==> 
             l1 `canFlow` z /\ l2 `canFlow` z /\ (forall (l:a) . l1 `canFlow` l /\ l2 `canFlow` l 
                ==> z `canFlow` l));  
}
