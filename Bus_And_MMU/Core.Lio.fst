module Core.Lio

include Bus.Lattice
module S = StateFull



let canFlow = canFlow'
let join = join'
let meet = meet'
let eq = eq

(* these types alpha/beta and mapAB/mapBA helpers are here to match with LioStar and by unfolding just syntaxic sugar *)
unfold type alpha = labels
unfold type beta  = labels

unfold let mapAB (a:alpha) : Tot beta = a 
unfold let mapBA (b:beta) : alpha = b

noeq
type context = {
  cur:(l:labels) (* extracted context *)
}

(* As context don't have clearance,
 * we don't check for clearance so we 
 * define a clearance which is always true
 *)
let noclearance = (fun l -> True)

let prop_monotonicity p0 p1 = True (* as clearance is not a concern, we always return true *)

(***** Effect definition *)
total
new_effect IFC = S.STATE_h context (* defintion of statefull effect *)

let post (a:Type) = IFC?.post a  (* syntaxic sugar *)

effect Ifc (a:Type) (req:labels -> GTot Type0) (ens:labels -> a -> labels -> GTot Type0) =
  IFC a (fun (c0:context) (p:post a)  -> 
                   req (mapAB c0.cur) /\
                   (forall (r:a) (c1:context). 
                   (req (mapAB c0.cur) /\ ens (mapAB c0.cur) r (mapAB c1.cur)) ==> p (r,c1) )) 



effect IfcClearance (a:Type) (req:labels -> (labels -> GTot Type0) -> GTot Type0) (ens:labels -> a -> labels -> (labels -> GTot Type0) -> (labels -> GTot Type0) -> GTot Type0) =
  IFC a (fun (c0:context) (p:post a)  -> 
                   req (mapAB c0.cur) noclearance /\
                   (forall (r:a) (c1:context). 
                   (req (mapAB c0.cur) noclearance  /\ ens (mapAB c0.cur) r (mapAB c1.cur) noclearance noclearance) ==> p (r,c1) ))              
                   
(* These helpers are C functions that actually store the context *)
assume val setCurrent : (l:labels) -> Ifc (unit)
  (requires fun l0 -> True)
  (ensures fun l0 x l1 -> l1 `eq` l)

assume val getCurrent : (_:unit) -> Ifc (labels)
  (requires fun l0 -> True)
  (ensures fun l0 x l1 -> l0 `eq` l1 /\  x `eq` l1)

assume val fail : string -> Ifc (unit)
  (requires fun l0 -> True)
  (ensures fun l0 _ l1 ->  l0 `eq` l1) 

(* use syntaxic sugar *)
unfold let get = getCurrent
unfold let put = setCurrent

(* *** Exposed functions *)

(* same that setCurrent but never brokes non-interference *)
unfold
let raise (l:labels) : Ifc (unit)
  (requires fun l0 -> True)
  (ensures fun l0 x l1 -> 
    l1 `eq` ( l0 `join` (l)) (* current label is joined with the one given in parameter *)
  ) = 
  let a = get () in
  let b = (a `join` (l)) in
  setCurrent b
  
(* type hidden to user *)
noeq
type labeled' 'a = {
  data:'a; 
  tag:labels
}

(* public exposition *)
type labeled 'a = labeled' 'a
let labelOf (vl:labeled 'a) 
 : (labels) = vl.tag
let valueOf (vl:labeled 'a) 
 : GTot ('a) = vl.data


inline_for_extraction
let labelUNSAFE (v:'a) (l:labels) : Ifc (labeled 'a) 
  (requires fun l0 -> True)
  (ensures fun l0 x l1 -> 
    ((labelOf x)) `eq` (l)
    /\ (valueOf x) == v
    /\ l1 `eq` l0
  )
= {data=v; tag=l}

(* creating a label *)
inline_for_extraction
let label (v:'a) (l:labels) : Ifc (labeled 'a) 
  (requires fun l0 -> True (*l0 `canFlow` (l)*))
  (ensures fun l0 x l1 -> 
    ((labelOf x)) `eq` (l)
    /\ (valueOf x) == v
    /\ l1 `eq` l0
  )
= 
  let l0 = get () in
  let r = labelUNSAFE v l in
  (if l0 `canFlow` l then
    ()
  else 
    fail "invalid labelling");
  r

(* unlabel a value *)
inline_for_extraction
let unlabelUNSAFE (vl:labeled 'a) : Ifc ('a)
  (requires fun l -> True)
  (ensures fun l0 x l1 -> 
    l1 `eq` l0
    /\ x == (valueOf vl)
  ) =
  vl.data
  
(* unlabel a value *)
inline_for_extraction
let unlabel (vl:labeled 'a) : Ifc ('a)
  (requires fun l -> True)
  (ensures fun l0 x l1 -> 
    l1 `eq` (l0 `join` ((labelOf vl)))
    /\ x == (valueOf vl) 
  ) =
  //let z =get () in
  raise (labelOf vl); (* we raise label to join *)
  unlabelUNSAFE vl

let toLabeled #a
              #b
              (params:b)
              #pre
              #post
              ($call:(p:b) -> IfcClearance a (requires pre p) (ensures post))
    : IfcClearance (labeled a) 
      (requires fun l0 p0 -> pre params l0 p0)
      (ensures fun l0 x l1 p0 p1 -> l0 `eq` l1
        /\ (post l0 (valueOf x) ((labelOf x)) p0 p1)
      ) =
      let n0 = get () in           (* save current label *)
      let r  = (call params) in    (* call the function *)  
      let n1 = get () in           (* save get the new current label *)
      assert(post n0 r n1 noclearance noclearance);
      let vl = label r n1 in       (* label the result to the current label *)
      put n0;                      (* restore the current label *)
      vl                           (* returns the value *)

let setClearance (pl:labels -> GTot Type0) : IfcClearance unit
  (requires fun l p -> True)
  (ensures fun l0 x l1 p0 p1 -> 
    l1 `eq` l0
    /\ p0 == p1
    ) = ()
