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
  cur:   (cur: G.erased labelType { G.reveal prop (G.reveal cur) });
  state: stateType;
}

/// A labeled value is like a tuple. Only the value is computationally relevant
private noeq type labeled' a = {
  value: a;
  label: G.erased labelType;
}
type labeled = labeled'
let labelOf (vl:labeled 'a): Tot (G.erased labelType) = vl.label
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

/// Trusted primitive (1/3)
/// Raise update the context such that
/// - the current label can raise with respect to the IFC lattice
/// - the invariant on labels can be tighten only
inline_for_extraction
let raise (l:G.erased labelType) (p:(G.erased (labelType -> Type0))) : Ifc (unit)
  (requires fun c -> 
      G.reveal p (G.hide (G.reveal c.cur `join` G.reveal l)) // is there bug : join is missing
    /\ G.reveal c.prop >= G.reveal p
  )
  (ensures fun c0 x c1 ->
      G.reveal p (G.reveal c0.cur `join` G.reveal l)
    /\ ( let l' : (l':labelType{G.reveal p l'}) = G.reveal c0.cur `join` G.reveal l in
        c1 == {c0 with prop=p; cur=G.hide l'}
      )
  ) 
= let c0 = IFC?.get () in
  IFC?.put ({c0 with cur=G.hide (G.reveal c0.cur `join` G.reveal l); prop=p})// is there bug : join is missing

/// unlabel unwraps a labeled piece of information, but polluate the current label in the context
unfold let unlabel_pre vl c = G.reveal c.prop (c.cur `g_join` labelOf vl)
unfold let unlabel_post vl c0 x c1
  = G.reveal c0.prop (c0.cur `g_join` labelOf vl)
  /\ c1 == {c0 with cur = G.hide (c0.cur `g_join` labelOf vl)}
  /\ x == valueOf vl
  
inline_for_extraction
let unlabel (vl:labeled 'a) : Ifc ('a)
  (requires unlabel_pre vl)
  (ensures unlabel_post vl)
= let c0 = IFC?.get () in
  IFC?.put ({
    c0 with
    cur = G.hide (c0.cur `g_join` labelOf vl)
  }); vl.value

unfold let label_pre l c = G.reveal c.cur `canFlow` G.reveal l
unfold let label_post v l c0 x c1 =  l == labelOf x /\ v == valueOf x /\ c0 == c1

inline_for_extraction
let label
  #a (v: a)
  (l:G.erased labelType)
  : Ifc (labeled a) 
                    // todo: be sure about that invariant
    (requires fun c -> label_pre l c)
    (ensures fun c0 x c1 -> label_post v l c0 x c1)
= {value = v; label = l}

/// To label encapsulate an IFC computation into an abstract box
/// Note that $f$ can restricts the invariant on labels
/// This invariant will be discared after the call of `toLabeled` 
unfold let toLabeled_pre pre x = pre x
unfold let toLabeled_post post x c0 lv c1 =
            c1 == {c0 with state=c1.state}
          /\ ( let l = G.reveal (labelOf lv) in
              exists (p1: G.erased (labelType -> Type0) {(G.reveal p1) l}).
                ( post x c0
                       (valueOf lv)
                       ({c1 with cur=l; prop=p1})
                )
            )
let toLabeled
  #a #b #pre #post
  ($f: (x: a) -> Ifc b (pre x) (post x))
  (params: a)
  : Ifc (labeled b)
        (requires toLabeled_pre pre params)
        (ensures toLabeled_post post params)
= let c0 = IFC?.get () in
  let r  = f params    in
  let c1 = IFC?.get () in
  let vl = label r c1.cur in
  IFC?.put ({c0 with state=c1.state});
  vl



