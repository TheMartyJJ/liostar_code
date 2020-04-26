module LioStar.Box

open LioStar.Effect.Parameters
open LioStar.Effect
open LioStar.Map
module L = FStar.List.Tot
module LP = FStar.List.Pure
module G = FStar.Ghost
module LU = LatticeUsed

noeq
type box a = {
  value: labeled a; 
  label: (b: labelType{G.reveal (labelOf value) `canFlow` b})
}

let unbox #a (bv:box a)
  : Ifc a
    (requires unlabel_pre bv.value)
    (ensures unlabel_post bv.value)
= unlabel bv.value

// not useful 
let labelBox #a (bv:box a) : Tot labelType = bv.label
let valueBox #a (bv:box a) : Tot (labeled a) = bv.value


let toLabeledBox
  #a #b #pre #post
  (max: labelType {forall x c0 r c1. post x c0 r c1 ==> G.reveal c1.cur `canFlow` max})
  ($f: (x: a) -> Ifc b (pre x) (post x))
  (x: a)
  : Ifc (box b)
        (requires toLabeled_pre pre x)
        (ensures fun c0 bv c1 -> 
          match bv with
          | {value;label} -> toLabeled_post post x c0 value c1
        )
= let v = toLabeled f x in
  { value = v
  ; label = max
  }

private 
let unsafe_wrap max (x: labeled 'a) =
    { value = x
    ; label = (admitP (labelOf x `canFlow` max);max)
    }
private
inline_for_extraction let openv (x: box 'a): labeled 'a = x.value

let rec map_with_value (f: 'a -> 'b -> 'c) (v: 'a) (l: list 'b)
  : list 'c
  = match l with
  | []    -> []
  | hd::tl -> f v hd :: map_with_value f v tl
  
private
let rec proof max (l: list (labeled 'a))
  : Lemma (L.map openv (map_with_value unsafe_wrap max l) == l)
  = match l with
  | [] -> ()
  | _::tl -> proof max tl

let map0 (#a #b:Type0) #pre #post
         (stateInv: G.erased (stateType -> Type0))
         (max: labelType
           {forall x c0 r c1. post x c0 r c1 ==> G.reveal c1.cur `canFlow` max})
         ($f:(p:a) -> Ifc b (pre p) (post p) )
         (l:list a): Ifc (list (box b))
 (requires map_pre pre post stateInv l)
 (ensures fun c0 x c1 -> 
          map_post pre post stateInv l c0 (L.map openv x) c1
 )
= let l' = map stateInv f l in
  proof max l';
  map_with_value unsafe_wrap max l'

let rec map (#a #b:Type0) #pre #post
         (stateInv: G.erased (stateType -> Type0))
         ($f:(p:a) -> Ifc b (requires pre p) (ensures post p) )
         (l:list a): Ifc (list (box b))
 (requires map_pre pre post stateInv l)
 (ensures fun c0 x c1 ->  map_post pre post stateInv l  c0 (L.map openv x) c1) 
= match l with
  | [] -> []
  | hd::tl -> (toLabeledBox LU.E f hd) :: map stateInv f tl


(*
let rec concat #a
        #pre #post
        (max: labelType
           {forall x c0 r c1. post x c0 r c1 ==> G.reveal c1.cur `canFlow` max})
        (l:list (labeled a))
        : Ifc (list a)
    (requires fun c -> True)
    (ensures fun c0 x c1 -> 
      c1 == {c0 with cur=(L.fold_right (fun cur acc -> 
                let r:labelType = (G.reveal (labelOf cur)) in
                G.hide (join r (G.reveal acc))
        ) 
        l 
        (G.reveal c0.cur))}
    )
=
 match l with
 | [] -> []
 | hd :: tl -> 
   let c =  concat tl in
   unlabel hd :: c
*)
