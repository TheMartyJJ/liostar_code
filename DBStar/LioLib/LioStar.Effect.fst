module LioStar.Effect

module S = StateFull
module G = FStar.Ghost

/// Parameters to be used for the IFC effect
open LioStar.Effect.Parameters

/// The next two lines make sure the lemmas `lemma_relation_canFlow_join` and `lemma_canFlow_reflexivity`
/// are indeed implemented, and furnishes the right properties
let _: l1: labelType -> l2: labelType -> Lemma (l1 `join` l2 == l2 ==> l1 `canFlow` l2) = lemma_relation_canFlow_join
let _: l: _ -> Lemma (ensures (l `canFlow` l)) [SMTPat (l `canFlow` l)] = lemma_canFlow_reflexivity

/// Utilitaries
// Partial order on "clearance" propositions
unfold let (>=) p0 p1 = forall l. p1 l ==> p0 l
unfold let g_join x y = G.reveal x `join` G.reveal y
let _ = assert ((fun (_: unit) -> True) >= (fun (_: unit) -> False))

/// A context has a invariant on current labels, a current label, and an arbitrary state
noeq type context = {
  prop:  G.erased (labelType -> Type0);
  cur:   (cur: labelType); // { (G.reveal prop) cur });
  state: stateType;
}

/// A labeled value is like a tuple. Only the value is computationally relevant
private noeq type labeled' a = {
  value: a;
  label: labelType;
}
type labeled = labeled'
let labelOf (vl:labeled 'a): Tot (labelType) = vl.label
let valueOf (vl:labeled 'a): GTot 'a = vl.value

/// IFC effect definition
total new_effect IFC = S.STATE_h context
effect Ifc
  (a: Type)
  (pre: context-> GTot Type0)
  (post: context -> a -> context-> GTot Type0)
  = IFC a (fun c0 p -> pre c0
                  /\ (forall r c1. post c0 r c1 ==> p (r, c1))
          )

effect IfcDyn
  (a: Type)
  = Ifc a (requires fun c0 -> True)(ensures fun c0 x c1 ->True)

(*
assume val getCurrent : unit -> Ifc (labelType * (G.erased (labelType -> Type0)))
  (requires fun c -> True)
  (ensures fun c0 x c1 -> fst x == c1.cur /\ snd x == c1.prop /\ c0 == c1) 
  *)

(*noextract
let getCurrent () : Ifc (labelType * (G.erased (labelType -> Type0))) 
  (requires fun c -> True)
  (ensures fun c0 x c1 -> fst x == c1.cur /\ snd x == c1.prop /\ c0 == c1) 
=
  let c = IFC?.get () in
  (c.cur, c.prop)

noextract
let setCurrent (l:labelType) (p:(G.erased (labelType -> Type0))) :Ifc (unit)
  (requires fun c -> (G.reveal p) l)
  (ensures fun c0 x c1 -> (G.reveal p) l /\ c1 == {c0 with cur=l; prop=p}) 
= let c = IFC?.get () in
  IFC?.put ({c with cur=l; prop=p}*)
noextract
let getCurrent () : IfcDyn (labelType) =
  let c = IFC?.get () in
  c.cur

noextract
let setCurrent (l:labelType) :IfcDyn (unit) = let c = IFC?.get () in
  IFC?.put ({c with cur=l})




(*
private
assume val setCurrent : (l:labelType) -> (p:(G.erased (labelType -> Type0)))  -> Ifc (unit)
  (requires fun c -> (G.reveal p) l)
  (ensures fun c0 x c1 -> (G.reveal p) l /\ c1 == {c0 with cur=l; prop=p}) 
*)

/// Trusted primitive (1/3)
/// Raise update the context such that
/// - the current label can raise with respect to the IFC lattice
/// - the invariant on labels can be tighten only
let raise (l:labelType) (p:(G.erased (labelType -> Type0))) : IfcDyn (unit) = let c0 = getCurrent () in
  admit ();setCurrent (c0 `join` l)

/// unlabel unwraps a labeled piece of information, but polluate the current label in the context
unfold let unlabel_pre vl c = G.reveal c.prop (c.cur `join` labelOf vl)
unfold let unlabel_post vl c0 x c1
  = G.reveal c0.prop (c0.cur `join` labelOf vl)
  /\ c1 == {c0 with cur = (c0.cur `join` labelOf vl)}
  /\ x == valueOf vl

let unlabel (vl:labeled 'a) : IfcDyn ('a) = let c0 = IFC?.get () in
  IFC?.put ({
    c0 with
    cur = (c0.cur `join` labelOf vl)
  }); vl.value

noextract 
let fail s : Tot unit = ()

let failing #a (s:string) : Tot a = fail s; admit()

unfold let label_pre l c = c.cur `canFlow` l
unfold let label_post v l c0 x c1 =  l == labelOf x /\ v == valueOf x /\ c0 == c1

let label
  #a (v: a)
  (l:labelType)
  : IfcDyn (labeled a) 
= let c = getCurrent () in
  if c `canFlow` l then
    {value = v; label = l}
  else (failing "invalid labeling")

/// To label encapsulate an IFC computation into an abstract box
/// Note that $f$ can restricts the invariant on labels
/// This invariant will be discared after the call of `toLabeled` 
unfold let toLabeled_pre pre x = pre x
unfold let toLabeled_post post x c0 lv c1 =
            c1 == {c0 with state=c1.state}
          /\ ( let l = (labelOf lv) in
              exists (p1: G.erased (labelType -> Type0) {(G.reveal p1) l}).
                ( post x c0
                       (valueOf lv)
                       ({c1 with cur=l; prop=p1})
                )
            )
let toLabeled
  #a #b   ($f: (x: a) -> IfcDyn b)
  (params: a)
  : IfcDyn (labeled b)
= let c0 = getCurrent () in
  let r  = f params    in
  let c1 = getCurrent () in
  let vl = label r c1 in
  admit ();setCurrent c0;
  vl


[@ (CPrologue "
extern void setCurrent ( labels l );
extern labels getCurrent( void *unit);
extern void fail(const char *s);
")]
let dump () : Ifc (unit)
  (requires fun c -> True)
  (ensures fun c0 x c1 -> True) = ()