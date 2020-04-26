module Test

module  G = FStar.Ghost

open LioStar.Effect.Parameters
open LioStar.Effect
open LioStar.Map
module L = FStar.List.Tot
module LP = FStar.List.Pure

(*
let behead (l:list 'a) : list 'a = 
  match l with
  | [] -> []
  | hd :: tl -> tl


let rec map (#a #b:Type0)
         #pre
         (#post) //:_{(forall c0 x c1. post c0 x c1 ==> pre c1})
         stateINV
         ($f:(p:a) -> Ifc (b) (requires pre p) (ensures post p) )
         (l:list a)
         : Ifc (list (labeled b))
 (requires fun c0 -> 
   (forall t. L.memP t l ==> 
      (toLabeled_pre pre t c0)) 
   //\ (forall t c0 r c1. (pre t c0 ==> stateINV c0.state) /\ (post t c0 r c1 ==> stateINV c1.state)))
   )
 (ensures fun c0 x c1 ->
   c1 == {c0 with state=c1.state}
   /\ L.length l = L.length x 
   /\ L.fold_right (fun (box,v) acc -> acc 
                     /\ (exists (s s':(z:_{stateINV z})) (p1:G.erased (labelType -> Type0)). 
                          let l:labelType = G.reveal labelOf box in
                          (G.reveal p1) l
                          /\ post v 
                                 ({c0 with state=s})
                                 (valueOf box) 
                                 ({cur=G.hide l;state=s'; prop=p1})
                       ))
                  (LP.zip x l) True   
   ) = match l with
  | [] -> []
  | hd::tl -> toLabeled f hd  :: map stateINV f tl
*)
module I32 = FStar.Int32

let add (vl:labeled I32.t) : Ifc (I32.t)
  (requires fun c ->  (G.reveal c.prop) ((G.reveal c.cur) `join` (G.reveal labelOf vl))
  )
  (ensures fun c0 x c1 -> 
    let l:(z:labelType) = ((G.reveal c0.cur) `join` (G.reveal labelOf vl)) in 
    (G.reveal c0.prop) l
    /\ c1 == {c0 with cur=G.hide l}
    ) //\ I32.v x = I32.v (valueOf vl) + 1)
= let v = unlabel vl in
  if I32.lt v 1000l then 
    I32.add v 1l
  else v
  
let rec mkLabels (li:list 'a) (l:G.erased labelType): Ifc (list (labeled 'a))
  (requires fun c -> G.reveal c.cur `canFlow` G.reveal l)
  (ensures fun c0 x c1 -> c0 == c1)
  = match li with
  | [] -> []
  | hd :: tl -> label hd l :: mkLabels tl l

module LU = LatticeUsed
let main () : Ifc (I32.t)
  (requires fun c -> G.reveal c.cur = LU.Bot /\ G.reveal c.prop == (fun _ -> True))
  (ensures fun _ _ _ -> True)
  = 
  let l = [9l; 2l; 0l] in
  let l' = mkLabels l (G.hide LU.Bot) in
  let l'' = map (fun _ -> True) add l' in
  (match l'' with 
    | hd :: tl -> unlabel hd
    | _ -> 0l)
