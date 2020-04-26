module DBStar.LioStar.Static

module  G = FStar.Ghost

open Core.LioStar.Static

module L = FStar.List.Tot
module LP = FStar.List.Pure
module G   = FStar.Ghost
module I32 = FStar.Int32
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8  = FStar.UInt8
module B   = LowStar.Buffer
module CS  = C.String
module LU = LatticeUsed


type fixedString = U64.t

noeq
type box 'a = {
  data0:labeled 'a; 
  tag0:(b:labelType{G.reveal (labelOf data0) = b})
}


noeq
type paper = {
  id : (i:U32.t{U32.v i > 0});
  pdf: fixedString;
  review1:option (box (fixedString));
}

let labelBox (b:box 'a) : labelType = b.tag0
let unbox (b:box 'a) : Ifc ('a) 
  (requires fun c -> (G.reveal c.prop) (join (G.reveal c.cur) (G.reveal (labelOf b.data0)))
  /\ (let l : (z:labelType{(G.reveal c.prop) z}) = (join (G.reveal c.cur) (G.reveal (labelOf b.data0))) in True)
  )
  (ensures fun c0 x c1 -> 
   (let l : (z:labelType{(G.reveal c0.prop) z}) = (join (G.reveal c0.cur) (G.reveal (labelOf b.data0))) in c1 == {c0 with cur=G.hide l})
  )
=
  unlabel b.data0

assume val mkBigStack : unit -> Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)
  
assume val mkDB : U32.t -> Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)
  
assume val syncDB : unit -> Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)
  


assume val getMaxId_g : unit -> GTot (n:nat{n > 0})
assume val getMaxId : unit -> Ifc (u:U32.t{U32.v u = (getMaxId_g ())})
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)
  
assume val getFreeId : unit -> Ifc (u:U32.t{U32.v u > 0 /\ U32.v u <= (getMaxId_g ())})
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)
  

assume val setById : (u:U32.t{U32.v u > 0 /\ U32.v u <= (getMaxId_g ())}) -> box paper -> Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)
  
assume val getById : (u:U32.t{U32.v u > 0 /\ U32.v u <= (getMaxId_g ())}) -> Ifc (box paper)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)
 

assume val loadDB : unit -> Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)
 

assume val print : U32.t -> Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)

assume val printPaper : (box paper) -> Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)

let rec fetchFor_h (i:U32.t{U32.v i <= getMaxId_g ()}) (lbl:labelType) : Ifc (list (box paper))
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)
  (decreases (U32.v i))
=
  match i with
  | 0ul -> []
  | _ -> let p = getById i in
        if lbl = labelBox p then (
          print i;
          p :: fetchFor_h (U32.sub i 1ul) lbl
        ) else
          fetchFor_h (U32.sub i 1ul) lbl

let save (lp:box paper) : Ifc (box paper)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> 
    c1 == {c0 with cur=G.hide (join (G.reveal (labelOf lp.data0)) (G.reveal c0.cur))})
=
  let j = (unbox lp).id in
  if (U32.gte (U32.sub j 1ul) (getMaxId ()) ) then
    ()
  else (
    assert(U32.v j - 1 < (getMaxId_g ()));
    setById j lp;
    ()
  );
  lp
  
let rec fetchPapers_h (i:U32.t{U32.v i <= getMaxId_g ()}) : IfcClearance (list (labeled paper))
  (requires fun l0 p0 -> p0 l0)
  (ensures fun l0 x l1 p0 p1 -> l0 `eq` l1 /\ p0 == p1)
  (decreases (U32.v i))
 = 
  match i with
  | 0ul -> []
  | _ -> (getById i) :: (fetchPapers_h (U32.sub i 1ul))
  

let fetchPapers (_:unit) : IfcClearance (list (labeled paper))
  (requires fun l0 p0 -> p0 l0)
  (ensures fun l0 x l1 p0 p1 -> l0 `eq` l1 /\ p0 == p1) = 
  (fetchPapers_h (getMaxId ()))


let rec map (#a #b:Type0)
         #pre
         (#post) //:_{(forall c0 x c1. post c0 x c1 ==> pre c1})
         stateINV
         ($f:(p:a) -> Ifc (b) (requires pre p) (ensures post p) )
         (l:list a)
         : Ifc (list (labeled b))
 (requires fun c0 -> 
   (forall t. L.memP t l ==> 
      (pre t c0)) 
   /\ (forall t c0 r c1. (pre t c0 ==> stateINV c0.state) /\ (post t c0 r c1 ==> stateINV c1.state)))
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
  | hd::tl -> toLabeled hd f  :: map stateINV f tl

let rec concat #a
           (l:list (labeled a))
           : Ifc (list a)
    (requires fun c0 -> True)
    (ensures fun c0 x c1 -> 
      
      l1 `eq` (L.fold_right (fun cur acc -> join (labelOf cur) acc) l l0)
    )
=
 match l with
 | [] -> []
 | hd :: tl -> 
   let c =  concat tl in
   unlabel hd :: c
