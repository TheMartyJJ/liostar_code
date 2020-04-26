module LioStar.Map

module G = FStar.Ghost
module L = FStar.List.Tot
module LP = FStar.List.Pure
open LioStar.Effect.Parameters
open LioStar.Effect

let behead (l:list 'a) : list 'a = 
  match l with
  | [] -> []
  | hd :: tl -> tl

unfold let map_pre
  pre post
  (stateInv: G.erased (stateType -> Type0))
  l c0
  = 
     (forall t.
       L.memP t l ==> (forall s. pre t ({c0 with state = s}))
     ) 
   /\ G.reveal stateInv c0.state
   /\ (forall t c0 r c1. post t c0 r c1 ==> G.reveal stateInv c1.state)

val g_fold_right: ('a -> 'b -> GTot 'b) -> list 'a -> 'b -> GTot 'b
let rec g_fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (g_fold_right f tl x)

unfold let map_post
  #a #b
  pre post
  (stateInv: G.erased (stateType -> Type0))
  (l1: list a)
  c0 (l2: list (labeled b)) c1
  : GTot Type0
  =  c1.cur == c0.cur 
   /\ G.reveal stateInv c1.state
   /\ L.length l1 == L.length l2 
   /\ g_fold_right (
       fun (v, lv) acc -> acc 
          /\ (exists ctx0
               ctx1.
                 post v ctx0 (valueOf lv) ctx1
               /\ labelOf lv == ctx1.cur
            )
       ) (LP.zip l1 l2) True
   
let rec map (#a #b:Type0) #pre #post
         (stateInv: G.erased (stateType -> Type0))
         ($f:(p:a) -> Ifc b (requires pre p) (ensures post p) )
         (l:list a): Ifc (list (labeled b))
 (requires map_pre pre post stateInv l)
 (ensures map_post pre post stateInv l) 
= match l with
  | [] -> []
  | hd::tl -> toLabeled f hd :: map stateInv f tl


let rec concat #a
        (max: labelType
           {forall x c0 r c1. unlabel_post x c0 r c1 ==> G.reveal c1.cur `canFlow` max})
        (l:list (labeled a))
        : Ifc (list a)
    (requires fun c -> (forall vl. L.memP vl l ==> unlabel_pre vl c)
                (*/\ (let m = (L.fold_right (fun cur acc -> 
                    let r:labelType = (G.reveal (labelOf cur)) in
                        G.hide (join r (G.reveal acc))) 
                          l 
                          (G.reveal c.cur)) 
                in (G.reveal c.prop) m)*)
    )
    (ensures fun c0 x c1 -> 
      (match l with
      | hd :: tl -> (match x with | [] -> True | hdx :: _ -> 
                (*let m = (L.fold_right (fun cur acc -> 
                    let r:labelType = (G.reveal (labelOf cur)) in
                        G.hide (join r (G.reveal acc))) 
                          l 
                          (G.reveal c0.cur)) 
                in
                (c1 == {c0 with cur=m})*)
                unlabel_post hd c0 hdx c1)
      | _ -> True)
    )
=
 match l with
 | [] -> []
 | hd :: tl -> 
   let c = concat max tl in
   //admitP(let c0 = IFC?.get () in  (G.reveal c0.prop) (labelOf hd));
   admit (); 
   unlabel hd :: c

