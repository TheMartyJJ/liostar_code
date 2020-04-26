/// This module is a auto-generated copy of `LioStar.Effect.fst`
/// Usage: make a symbolic link of this file to some other directory as `LioStar.Effect.fst`
module LioStar.Effect

module S = BasicState
module G = FStar.Ghost

/// Parameters to be used for the IFC effect
open LioStar.Effect.Parameters

module L = Lattice

let join = labelTypeHasLattice.L.join
let canFlow = labelTypeHasLattice.L.canFlow

/// Utilitaries
unfold let g_join x y = G.reveal x `join` G.reveal y
noextract 
let fail s : Tot unit = ()
unfold let failing #a (s:string) : Admit a = fail s; admit()

/// A context has a clearance, a current label, and an arbitrary state
noeq type context = {
  // clearance: labelType;
  cur:   labelType;
  state: stateType;
}

private noeq type labeled' a = {
  value: a;
  label: labelType;
}
type labeled = labeled'
let labelOf (vl:labeled 'a): Tot labelType = vl.label
let valueOf (vl:labeled 'a): Tot 'a = vl.value

/// IFC effect definition
new_effect IFC = S.STATE_h context
effect Ifc (a: Type)
  = IFC a (fun _ p -> forall tuple. p tuple)

noextract
let getCurrent () : Ifc (labelType) 
= (IFC?.get ()).cur

noextract
let setCurrent (l:labelType) :Ifc (unit)
= IFC?.put ({(IFC?.get ()) with cur=l})


/// Trusted primitive (1/3)
/// Raise update the context such that
/// - the current label can raise with respect to the IFC lattice
/// - the invariant on labels can be tighten only
let raise (l:labelType) : Ifc (unit)
= setCurrent (getCurrent () `join` l)

/// unlabel unwraps a labeled piece of information, but polluate the current label in the context
let unlabel (vl:labeled 'a) : Ifc ('a)
= let c0 = IFC?.get () in
  setCurrent (getCurrent () `join` labelOf vl);
  vl.value

let label
  #a (v: a) (l:labelType)
  : Ifc (labeled a) 
= let c = getCurrent () in
  if c `canFlow` l then
    {value = v; label = l}
  else (failing "invalid labeling")

/// To label encapsulate an IFC computation into an abstract box
/// Note that $f$ can restricts the invariant on labels
/// This invariant will be discared after the call of `toLabeled` 
let toLabeled
  #a #b
  ($f: (x: a) -> Ifc b) (params: a)
  : Ifc (labeled b)
= let c0 = getCurrent () in
  let r  = f params    in
  let c1 = getCurrent () in
  let vl = label r c1 in
  setCurrent c0;
  vl

[@ (CPrologue "
extern void setCurrent ( labels l );
extern labels getCurrent( void *unit);
extern void fail(const char *s);
")]
let dump () : Ifc unit = ()
