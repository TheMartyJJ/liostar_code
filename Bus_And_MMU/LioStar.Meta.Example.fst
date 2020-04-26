module LioStar.Meta.Example

open Core.LioStar

open FStar.Tactics
// open LioStar.Meta
open LioStar.Meta.Helpers

open MetaTools.PatchTerm
open MetaTools.Compiled
module L = FStar.List.Tot

module BUS = Bus.Example
module BUS = Bus.Lattice

let addition (x: labeled int) (y: labeled int): IfcTop (labeled int) (fun _ -> True) (fun _ _ _ -> True)
 = labelUNSAFE (unlabel x + unlabel y) Bot

assume val placeholder: (#a: Type) -> a
let axiom_phAbsorbPlusL n: Lemma (placeholder + n = placeholder)
  [SMTPat (placeholder + n)] = admit ()
let axiom_phAbsorbPlusR n: Lemma (n + placeholder = placeholder)
  [SMTPat (n + placeholder)] = admit ()
let axiom_phAbsorbMinus (): Lemma (- placeholder = placeholder) = admit ()
let lemma_phAbsorbMinusL n: Lemma (n - placeholder = placeholder) [SMTPat (n - placeholder)] = 
  axiom_phAbsorbMinus (); axiom_phAbsorbPlusR n
let lemma_phAbsorbMinusR n: Lemma (placeholder - n = placeholder) [SMTPat (placeholder - n)] =  axiom_phAbsorbPlusL n
let axiom_phAbsorbLeL v: Lemma (placeholder < v = placeholder)
  [SMTPat (placeholder < v)] = admit ()
let axiom_phAbsorbLeR v: Lemma (v < placeholder = placeholder)
  [SMTPat (v < placeholder)] = admit ()

let axiom_phAbsorbMkLabeled' (#a: eqtype) (v: alpha)
  : Lemma (Mklabeled' #a placeholder v = placeholder)
  [SMTPat (Mklabeled' #a placeholder v)] = admit ()


let erase (a:Type) (vl:labeled a) (l:labels) : Tot (labeled a)
= if labelOf vl `canFlow` l
  then vl
  else labelUNSAFE placeholder (labelOf vl)


let strings_to_names = L.map (String.split ['.'])
let strings_to_pnames
  : list (bool * string) -> list (bool * name) 
  =
  L.map (fun (exactMatch, x) -> exactMatch, String.split ['.'] x)

let asd: decls = _ by (
    let t = generate_patched_defs
      (strings_to_pnames [
        false, "Core.LioStar";
        false, "Bus";
      ]) (`erase) (`labels) (`addition)
    in
    exact (quote t)
)

let _ = assert (alpha == labels)

%splice[] (
    let t = generate_patched_defs
      (strings_to_pnames [
        false, "Core.LioStar";
        // false, "Bus";
      ]) (`erase) (`labels) (`addition)
    in
    t
)

let mkContext cur src dst value = {
  prop = (fun _ -> True);
  cur = cur;
  src = src;
  dst = dst;
  read = value;
}

unfold let ctx startLabel = { prop = (fun _ -> True);
     cur = startLabel;
     src = C;
     dst = C;
     read = 0uy;}

let get_compute2 (f: _ -> _ -> IfcTop _ (const True) (fun _ _ _ -> True))
    x y = 
      let v, l = (reify (f x y) (ctx Bot)) in
      labelUNSAFE v l.cur

let xx = get_compute2 addition (labelUNSAFE 3 C) (labelUNSAFE 3 CM)

let test l x y
  : Lemma (get_compute2 (addition_patched l) x y
        == erase _ (get_compute2 addition x y) l)
  = ()

%splice[] (
    let t = generate_patched_defs
      (strings_to_pnames [
        true, `%Bus.Example.components;
        true, `%Bus.Example.byte;
        false, "Core.LioStar";
      ]) (`erase) (`labels) (`Bus.Example.receive)
    in
    // fail (term_to_string (quote t));
    t
)


let get_compute1 #pre #post ($f: (p: _) -> IfcClearance _ (pre p) (post p))
    x 
    = let v, l = reify (admit (); f x) (ctx Bot) in
      labelUNSAFE v l.cur

let asdasd x = get_compute1 Bus.Example.receive x

let xtest l x
  : Lemma (get_compute1 (receive_patched l) x
        // == magic ())
        == erase _ (get_compute1 Bus.Example.receive x) l)
  = ()//assert (get_compute1 (receive_patched l) x
    //    == magic ()) by (compute (); dump "x")


