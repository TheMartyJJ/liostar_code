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
   /\ c1.prop == c0.prop
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
