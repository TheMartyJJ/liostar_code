/// This module is a auto-generated copy of `LioStar.Effect.fst`
/// Usage: make a symbolic link of this file to some other directory as `LioStar.Effect.fst`
module LioStar.Effect

module S = BasicState
module G = LioStar.Ghost

/// Parameters to be used for the IFC effect
open LioStar.Effect.Parameters

module L = Lattice

let join = labelTypeHasLattice.L.join
let canFlow = labelTypeHasLattice.L.canFlow

let _: l: _ -> Lemma (ensures (l `canFlow` l)) [SMTPat (l `canFlow` l)]
  = labelTypeHasLattice.L.lawFlowReflexivity

/// Utilitaries
// Partial order on "clearance" propositions
unfold let (>=) p0 p1 = forall l. p1 l ==> p0 l
unfold let g_join (x y: G.erased labelType) = G.reveal x `join` G.reveal y
let _ = assert ((fun (_: unit) -> True) >= (fun (_: unit) -> False))

/// A labeled value is like a tuple. Only the value is computationally relevant
private noeq type labeled' a = {
  value: a;
  label: G.erased labelType;
}
type labeled = labeled'
let labelOf (vl:labeled 'a): Tot (G.erased labelType) = vl.label
let erasedValueOf (vl:labeled 'a): Tot (G.erased 'a) = G.hide vl.value
let valueOf (vl:labeled 'a): GTot 'a = vl.value

unfold type stateType = stateTypeMaker labeled labelOf

/// A context has a invariant on current labels, a current label, and an arbitrary state
noeq type context = {
  prop:  G.erased (labelType -> Type0);
  cur:   (cur: G.erased labelType { G.reveal prop (G.reveal cur) });
  state: stateType;
}


/// IFC effect definition
total (* macro expansion begins *) reifiable (* macro expansion ends *) new_effect IFC = S.STATE_h context

(* M_ACRO
irreducible let is_true (prop: Type0) = prop
let lemma_is_true prop: Lemma (is_true prop /\ is_true prop == prop)
                        [SMTPat (is_true prop)]
                        = admit ()
*)

effect Ifc
  (a: Type)
  (pre: context-> GTot Type0)
  (post: context -> a -> context-> GTot Type0)
  = IFC a (fun c0 p -> (* M_ACRO is_true (pre c0) /\  *) pre c0
                  /\ (forall r c1. pre c0 /\ post c0 r c1 ==> ((* M_ACRO is_true (p (r, c1)) /\ *) p (r, c1)))
          )

/// Trusted primitive (1/3)
/// Raise update the context such that
/// - the current label can raise with respect to the IFC lattice
/// - the invariant on labels can be tighten only
let raise (l:G.erased labelType) (p:(G.erased (labelType -> Type0))) : Ifc (unit)
  (requires fun c -> 
      G.reveal p (G.reveal c.cur `join` G.reveal l) // is there bug : join is missing
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
unfold let preCanReach (l: labelType) (c: context)
  = G.reveal c.prop (G.reveal c.cur `join` l)
unfold let unlabel_pre vl c = preCanReach (G.reveal (labelOf vl)) c
unfold let unlabel_post' vl l0 (p0: G.erased (labelType -> Type0)) x (l1: G.erased labelType) p1
  = G.reveal p0 (l0 `g_join` labelOf vl)
  /\ G.reveal l1 == l0 `g_join` labelOf vl
  /\ p1 == p0
  /\ x == valueOf vl
unfold let unlabel_post vl c0 x c1
  = unlabel_post' vl c0.cur c0.prop x c1.cur c1.prop
  /\ c0.state == c1.state

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

let label
  #a (v: a)
  (l:G.erased labelType)
  : Ifc (labeled a) 
                    // todo: be sure about that invariant
    (requires fun c -> label_pre l c)
    (ensures fun c0 x c1 -> label_post v l c0 x c1)
= {value = v; label = l}

/// Conditional definitions for the Meta* theorem generator

(* macro expansion begins *)
assume val placeholder: (#a: Type) -> a
let erase (a:Type) (vl:labeled a) (l:labelType) : Tot (labeled a)
= if (let G.E x = labelOf vl in x) `canFlow` l
  then vl
  else placeholder #(labeled a)
let axiom_phAbsorbMkLabeled' (#a: Type0) (v: labelType)
  : Lemma (Mklabeled' #a placeholder (G.hide v) == placeholder)
  [SMTPat (Mklabeled' #a placeholder (G.hide v))] = admit ()
(* macro expansion ends *)

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
                       ({c1 with cur=G.hide l; prop=p1})
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

/// Define a few effect synonyms
/// Their name follow the convention:
///   Ifc_PreLevel_PostLevel, where PreLevel=None|All|St PostLevel=All|AllRO|St|StRO|RetRO|None

let preType = context -> Type0
let postType a = context -> a -> context -> Type0

unfold let preNone: preType = fun _ -> True
unfold let preSt (pre: stateType -> Type0): preType
  = fun c0 -> pre c0.state 
unfold let postAllRO #a (post: context -> a -> Type0): postType a
  = fun c0 r c1 -> c0 == c1 /\ post c0 r
unfold let postStRO #a (post: stateType -> a -> Type0): postType a
  = fun c0 r c1 -> c0 == c1 /\ post c0.state r
unfold let postSt #a (post: stateType -> a -> stateType -> Type0): postType a
  = fun c0 r c1 -> c0.cur == c1.cur /\ c0.prop == c1.prop /\ post c0.state r c1.state
unfold let postRetRO #a (post: a -> Type0): postType a
  = fun c0 r c1 -> c0 == c1 /\ post r
unfold let postNone #a (post: a -> Type0): postType a
  = fun c0 r c1 -> True

/// The following two primitives shall be used only for building up new primitives
noextract
let setStateAsUnit (s: stateType)
  : Ifc unit preNone (postSt (fun _ _ s1 -> s1 == s))
  = IFC?.put ({(IFC?.get ()) with state = s})
noextract
let getStateAsUnit ()
  : Ifc stateType preNone (postStRO (fun s r -> s == r))
  = let s = IFC?.get () in s.state

effect IfcState (u: Type)
  (pre: stateType -> Type0)
  (post: stateType -> u -> stateType -> Type0)
  = Ifc u (preSt pre) (postSt post)
