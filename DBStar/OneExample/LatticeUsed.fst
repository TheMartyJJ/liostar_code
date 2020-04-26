module LatticeUsed

module S = StateFull
open Core.Lattice
module G = FStar.Ghost

type labels =
 | Bot
 | C
 | CM
 | M
 | E

let meet' a b = match a, b with
   | Bot, _ -> a
   | C, _ -> (match b with 
             |Bot -> b 
             | M -> Bot
             | _ -> a)
   | CM, _ -> (match b with 
             |Bot | C  | M -> b 
             | _ -> a)
   | M, _ -> (match b with 
             |Bot -> b 
             | C -> Bot
             | _ -> a)
   | E, _ -> b
  
let join' a b = match a, b with
   | Bot, _ -> b
   | C, _ -> (match b with 
             |Bot -> a 
             | M -> CM
             | _ -> b)
   | CM, _ -> (match b with 
             |Bot | C | M -> a 
             | _ -> b)
   | M, _ -> (match b with 
             |Bot -> a
             | C -> CM
             | _ -> b)
   | E, _ -> a
  
let canFlow' (a b:labels) = 
  a = meet' a b

let eq (a b:labels) = a = b


instance latticeUsed :  lattice labels = {
  value = labels;
  equals=eq;
  
  canFlow = canFlow';
  meet = meet';
  join = join';
  
  bottom = Bot;
  top=E;

  lawBot = (fun l -> ());
  lawFlowReflexivity = (fun l -> ());
  lawFlowAntisymetry = (fun l1 l2 -> ());
  lawFlowTransitivity = (fun l1 l2 l3 -> ());
  lawMeet = (fun z l1 l2 -> ());
  lawJoin = (fun z l1 l2 -> ());
}
