module Core.LioStar

include Bus.Lattice
module S = StateFull
module G = FStar.Ghost

(* rename operations *)
let canFlow = canFlow'
let join = join'
let meet = meet'
let eq = eq

(* This example part help to configure if using fully static/dynamic 
 *  - To enable static set isErased to true and then uncomment the erased mapXX
 *  - To enbale dynamic set isErased to false and then uncomment the erased mapXX
 *)
type targets =
  | MetaProof
  | C_Erased
  | C_Concrete

let target: targets = C_Concrete

unfold type alpha = normalize_term(match target with
       | C_Concrete | MetaProof -> labels
       | C_Erased -> G.erased labels
       )
unfold type beta = labels

(* non-erased mapXX *)
unfold let mapAB (a:alpha) : Tot beta = a  (* helper for dynamic version *)
unfold let mapBA (b:beta) : alpha = b      (* helper for dynamic version *)

(* Erased mapXX *)
// unfold let mapAB (a:alpha) : GTot beta = G.reveal a (* helper for static version *)
// unfold let mapBA (b:beta) : alpha = G.hide b        (* helper for static version *)

// noeq
// type context = {
//   prop:labels -> GTot Type0;     (* clearance proposition *)
//   cur:(a:alpha{prop (mapAB a)}) (* current refined to always hold clearance *)
// }
// unfold let metaIsUnchanged =(fun c0 c1 -> True)
type components = x:labels{(E? x \/ M? x \/ C? x)}
noeq
type context = {
  prop:labels -> GTot Type0;     (* clearance proposition *)
  cur:(a:alpha{prop (mapAB a)});(* current refined to always hold clearance *)
  src:components;
  dst:components;
  read:FStar.UInt8.t;
}
unfold let metaIsUnchanged =(fun c0 c1 -> c0.src = c1.src && c0.dst = c1.dst && c0.read = c1.read)

let prop_monotonicity p0 p1 =   (* property on clearance propositions *)
  (forall l. p1 l ==> p0 l)

(***** Effect definition ******)

total
new_effect IFC = S.STATE_h context (* defintion of statefull effect *)

let post (a:Type) = IFC?.post a    (* syntaxic sugar *)


effect Ifc (a:Type) (req:labels -> GTot Type0) (ens:labels -> a -> labels -> GTot Type0) =
  IFC a (fun (c0:context) (p:post a)  -> 
                   req (mapAB c0.cur) /\
                   (forall (r:a) (c1:context). 
                   (req (mapAB c0.cur) /\ ens (mapAB c0.cur) r (mapAB c1.cur)
                   /\ c0.prop == c1.prop
                   /\ (metaIsUnchanged c0 c1)
                   ) ==> p (r,c1) )) 

effect IfcClearance (a:Type) (req:labels -> (labels -> GTot Type0) -> GTot Type0) (ens:labels -> a -> labels -> (labels -> GTot Type0) -> (labels -> GTot Type0) -> GTot Type0) =
  IFC a (fun (c0:context) (p:post a)  -> 
                   req (mapAB c0.cur) c0.prop /\
                   (forall (r:a) (c1:context). 
                   (req (mapAB c0.cur) c0.prop  
                   /\ ens (mapAB c0.cur) r (mapAB c1.cur) c0.prop  c1.prop
                   /\ metaIsUnchanged c0 c1) ==> p (r,c1) )) 

effect IfcTop (a:Type) (req:labels -> GTot Type0) (ens:labels -> a -> labels -> GTot Type0) =
  IfcClearance a (fun l0 p0 -> req l0 /\ (forall l. p0 l))
                 (fun l0 r l1 p0 p1 -> p0 == p1 /\ ens l0 r l1)

(**** Exposed functions *)

(* getCurrent and IFC?.get are switch depending on isErased value
 * idem for setCurrent and IFC?.set
 * 
 * If isErased is true getCurrent and setCurrent will be irrelevant
 * If isErased is false then get/put will be replaced by the getcurrent/setcurrent C implementation
 *) 
assume val setCurrent : (l:alpha) -> IfcClearance (unit)
  (requires fun l0 p0 -> True)
  (ensures fun l0 x l1 p0 p1 -> l1 `eq` (mapAB l)  /\ p1 == p0)

assume val getCurrent : (_:unit) -> IfcClearance (alpha)
  (requires fun l0 p0 -> True)
  (ensures fun l0 x l1 p0 p1 -> l0 `eq` l1 /\  (mapAB x) `eq` l1 /\ p0 == p1)

assume val fail : string -> IfcClearance (unit)
  (requires fun l0 p0 -> True)
  (ensures fun l0 _ l1 p0 p1 ->  l0 `eq` l1 /\ p0 == p1) 
  
(* this getter behave like getCurrent but with effect primitive which are erased at the end *)
noextract
let pure_get () : IfcClearance (alpha)
  (requires fun l0 p0 -> True)
  (ensures fun l0 x l1 p0 p1 -> l0 `eq` l1 /\  (mapAB x) `eq` l1 /\ p0 == p1)
  = let c = IFC?.get () in c.cur
(*
let pure_get_context () : IfcClearance (context)
  (requires fun l0 p0 -> True)
  (ensures fun l0 x l1 p0 p1 -> l0 `eq` l1 /\ p0 == p1)
  = let c = IFC?.get () in c *)
  
(* idem than previous getter *)  
noextract
let pure_set (l:alpha) : IfcClearance (unit)
  (requires fun l0 p0 -> p0 (mapAB l))
  (ensures fun l0 x l1 p0 p1 -> l1 `eq` (mapAB l)  /\ p1 == p0)
  = let c = IFC?.get () in IFC?.put ({c with cur=l})

unfold noextract let get = normalize_term(match target with
                 | MetaProof | C_Erased -> pure_get
                 | C_Concrete -> getCurrent
                 )
unfold noextract let put = normalize_term(match target with
                 | MetaProof | C_Erased -> pure_set
                 | C_Concrete -> setCurrent
                 )

(* same that setCurrent but never brokes non-interference *)
unfold
let raise (l:alpha) : IfcClearance (unit)
  (requires fun l0 p0 -> p0 ( l0 `join` (mapAB l)) )
  (ensures fun l0 x l1 p0 p1 -> 
   l1 `eq` ( l0 `join` (mapAB l)) (* current label is joined with the one given in parameter *)
   /\ p0 == p1
  ) = 
  let a = get () in
  let c = IFC?.get () in
  let b:(x:alpha{c.prop (mapAB x)}) = mapBA ((mapAB a) `join` (mapAB l)) in
  put (b)
  
(* type hidden to user *)
private
noeq
type labeled' 'a = {data:'a; tag:alpha}

(* public exposition *)
type labeled 'a = labeled' 'a
let labelOf (vl:labeled 'a) : (alpha) = vl.tag
let valueOf (vl:labeled 'a) : GTot ('a) = vl.data


(* creating a label *)

inline_for_extraction
let labelUNSAFE (v:'a) (l:alpha) : Tot (labeled 'a) 
  // (requires fun l0 -> True)
  // (ensures fun l0 x l1 -> 
  //   (mapAB (labelOf x)) `eq` (mapAB l)
  //   /\ (valueOf x) == v
  //   /\ l1 `eq` l0
  // )
= {data=v; tag=l}

inline_for_extraction
let unlabelUNSAFE (vl:labeled 'a) : IfcClearance ('a)
  (requires fun l p -> True)
  (ensures fun l0 x l1 p0 p1 -> 
    x == (valueOf vl)
    /\ p0 == p1
    /\ l0 `eq` l1
  ) =
  vl.data


inline_for_extraction
let label (v:'a) (l:alpha) : Ifc (labeled 'a) 
  (requires fun l0 -> l0 `canFlow` (mapAB l))
  (ensures fun l0 x l1 -> 
    (mapAB (labelOf x)) `eq` (mapAB l)
    /\ (valueOf x) == v
    /\ l1 `eq` l0
  )
= labelUNSAFE v l

(* unlabel a labeled value *)
inline_for_extraction
let unlabel (vl:labeled 'a) : IfcClearance ('a)
  (requires fun l p -> p (join l (mapAB (labelOf vl))))
  (ensures fun l0 x l1 p0 p1 -> 
    l1 `eq` (l0 `join` (mapAB (labelOf vl)))
    /\ x == (valueOf vl)
    /\ p0 == p1
  ) =
  raise (mapAB (labelOf vl));
  vl.data


let toLabeled #a
              #b
              (params:b)
              (#pre)
              (#post:_{(forall l0 x l1 p0 p1.  post l0 x l1 p0 p1 ==> (prop_monotonicity p0 p1 /\ p1 l0))})
              ($call:(p:b) -> IfcClearance a (requires pre p) (ensures fun l0 x l1 p0 p1 -> post l0 x l1 p0 p1 ))
    : IfcClearance (labeled a) 
      (requires fun l0 p0 -> pre params l0 p0)
      (ensures fun l0 x l1 p0 p1 -> l0 `eq` l1
        /\ (post l0 (valueOf x) (mapAB (labelOf x)) p0 p1)
        /\ p1 l1
        /\ p1 l0
      ) =
      let n0 = get () in           (* save current label *)
      let c0 = IFC?.get () in
      let r  = (call params) in    (* call the function *)
      let c1 = IFC?.get () in
      let n1 = get () in           (* save get the new current label *)
      assert(post (mapAB n0) r (mapAB n1) c0.prop c1.prop);
      let vl = label r n1 in  (* label the result to the current label *)
      IFC?.put ({c0 with prop=c1.prop});       
      put (n0);                            (* restore the current label *)
      vl                                   (* returns the value *)

let setClearance (pl:labels -> GTot Type0) : IfcClearance unit
  (requires fun l p -> pl l (* current label must be validated by the new clearance *)
    /\ prop_monotonicity p pl) (* clearance is only updated if monotonic *)
  (ensures fun l0 x l1 p0 p1 -> 
    l1 `eq` l0
    /\ p1 == pl) = 
  let c0 = IFC?.get () in
  let c1 = {c0 with prop=pl} in
  IFC?.put c1

(* Concrete box *)
noeq
type concrete_box' 'a = {
  data0:labeled 'a; 
  tag0:(b:beta{mapAB (labelOf data0) `eq` b})
}


(* public exposition *)
type concrete_box 'a = concrete_box' 'a
let ct_labelOf (vl:concrete_box 'a) : (beta) = vl.tag0
let ct_valueOf (vl:concrete_box 'a) : GTot ('a) = valueOf (vl.data0)

inline_for_extraction
let ct_label (v:'a) (l:beta) : Ifc (concrete_box 'a) 
  (requires fun l0 -> l0 `canFlow` l)
  (ensures fun l0 x l1 -> 
    (ct_labelOf x) `eq` l
    /\ (ct_valueOf x) == v
    /\ l1 `eq` l0
  )
= let r = (label v (mapBA l)) in
  assert( mapAB (labelOf r) `eq` l);
  {data0=r; tag0=l}

inline_for_extraction
let ct_unlabel (vl:concrete_box 'a) : IfcClearance ('a)
  (requires fun l p -> p (join l (ct_labelOf vl)))
  (ensures fun l0 x l1 p0 p1 -> 
    l1 `eq` (l0 `join` (ct_labelOf vl))
    /\ x == (ct_valueOf vl)
    /\ p0 == p1
  ) =
  let a = unlabel (vl.data0) in
  a
