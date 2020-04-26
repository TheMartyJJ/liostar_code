module Meta

open FStar.Tactics
open FStar.Tactics.Typeclasses
open ValueErasers.Generator

open LioStar.Effect
open LioStar.Effect.Parameters
open ExampleNiki

open Data.Serialize.Helpers
open MetaTools.PatchTerm
open MetaTools.BrowseTerm
module L = FStar.List.Tot

module G = LioStar.Ghost


let getResult (x: 'a * context): labeled 'a
  = mkLabel (fst x) (snd x).cur

let reify1
  #a #ret #wp
  [| hasEraser ret |]
  ($f: (x: a) -> IFC ret (wp x))
  : lErase: labelType -> c0: context -> x: a{wp x c0 (fun _ -> True)} -> Tot (labeled ret)
  = fun lErase c0 x -> erase_value lErase (getResult (reify (f x) c0))

let reify2
  #a #b #ret #wp
  [| hasEraser ret |]
  ($f: (x: a) -> (y: b) -> IFC ret (wp x y))
  : lErase: labelType -> c0: context -> x: a -> y: b{wp x y c0 (fun _ -> True)} -> Tot (labeled ret)
  = fun lErase c0 x y -> erase_value lErase (getResult (reify (f x y) c0))

let reify3
  #a #b #c #ret #wp
  [| hasEraser ret |]
  ($f: (x: a) -> (y: b) -> (z: c) -> IFC ret (wp x y z))
  : lErase: labelType -> c0: context -> x: a -> y:b -> z: c{wp x y z c0 (fun _ -> True)} -> Tot (labeled ret)
  = fun lErase c0 x y z -> erase_value lErase (getResult (reify (f x y z) c0))
  
let reify4
  #a #b #c #d #ret #wp
  [| hasEraser ret |]
  ($f: (x: a) -> (y: b) -> (z: c) -> (t: d) -> IFC ret (wp x y z t))
  : lErase: labelType -> c0: context -> x: a -> y:b -> z: c -> t: d{wp x y z t c0 (fun _ -> True)} -> Tot (labeled ret)
  = fun lErase c0 x y z t -> erase_value lErase (getResult (reify (f x y z t) c0))

let reify5
  #a #b #c #d #e #ret #wp
  [| hasEraser ret |]
  ($f: (x: a) -> (y: b) -> (z: c) -> (t: d) -> (u: e) -> IFC ret (wp x y z t u))
  : lErase: labelType -> c0: context -> x: a -> y:b -> z: c -> t: d -> u: e{wp x y z t u c0 (fun _ -> True)} -> Tot (labeled ret)
  = fun lErase c0 x y z t u -> erase_value lErase (getResult (reify (f x y z t u) c0))



let reify1'
  #a #ret #wp
  [| hasEraser ret |]
  ($f: (lErase: labelType) -> (x: a) -> IFC ret (wp x))
  : lErase: labelType -> c0: context -> x: a{wp x c0 (fun _ -> True)} -> Tot (labeled ret)
  = fun lErase c0 x -> erase_value lErase (getResult (reify (f lErase x) c0))

let reify2'
  #a #b #ret #wp
  [| hasEraser ret |]
  ($f: (lErase: labelType) -> (x: a) -> (y: b) -> IFC ret (wp x y))
  : lErase: labelType -> c0: context -> x: a -> y: b{wp x y c0 (fun _ -> True)} -> Tot (labeled ret)
  = fun lErase c0 x y -> erase_value lErase (getResult (reify (f lErase x y) c0))

let reify3'
  #a #b #c #ret #wp
  [| hasEraser ret |]
  ($f: (lErase: labelType) -> (x: a) -> (y: b) -> (z: c) -> IFC ret (wp x y z))
  : lErase: labelType -> c0: context -> x: a -> y:b -> z: c{wp x y z c0 (fun _ -> True)} -> Tot (labeled ret)
  = fun lErase c0 x y z -> erase_value lErase (getResult (reify (f lErase x y z) c0))
  
let reify4'
  #a #b #c #d #ret #wp
  [| hasEraser ret |]
  ($f: (lErase: labelType) -> (x: a) -> (y: b) -> (z: c) -> (t: d) -> IFC ret (wp x y z t))
  : lErase: labelType -> c0: context -> x: a -> y:b -> z: c -> t: d{wp x y z t c0 (fun _ -> True)} -> Tot (labeled ret)
  = fun lErase c0 x y z t -> erase_value lErase (getResult (reify (f lErase x y z t) c0))

let reify5'
  #a #b #c #d #e #ret #wp
  [| hasEraser ret |]
  ($f: (lErase: labelType) -> (x: a) -> (y: b) -> (z: c) -> (t: d) -> (u: e) -> IFC ret (wp x y z t u))
  : lErase: labelType -> c0: context -> x: a -> y:b -> z: c -> t: d -> u: e{wp x y z t u c0 (fun _ -> True)} -> Tot (labeled ret)
  = fun lErase c0 x y z t u -> erase_value lErase (getResult (reify (f lErase x y z t u) c0))

let mk (f: term): Tac _
  = let l = [
             `reify1';`reify2';`reify3';`reify4';`reify5'
            ;`reify1 ;`reify2 ;`reify3 ;`reify4 ;`reify5
            ]
    in
    // let r = map (fun rFun -> call1 rFun f) l in
    // fail (term_to_string (quote r));
    let l = map (fun rFun -> match trytac (fun () -> tc (top_env ()) (call1 rFun f)) with
                  | Some t -> Some (t, call1 rFun f)
                  | None   -> None
        ) l
    in
    let l: list (x: _ {Some? x}) = admit (); L.filter (Some?) l in
    let l = L.map (fun (Some x) -> x) l in
    let r = match l with
    | [] -> fail "Cannot apply reifyn or reifyn' (with n=1,2,3,4 or 5) (might be an eraser missing; try manually with reifyn or reifyn')"
    | [x] | [x;_] -> x
    | _ -> fail "More than two solutions found, this is not possible"
    in
    // fail (term_to_string (quote r));
    r

let reifyN (f: term)
  (#[(let r = snd (mk f) in exact r)] f')
  = f'

let strings_to_pnames
  : list (bool * string) -> list (bool * name) 
  =
  L.map (fun (exactMatch, x) -> exactMatch, String.split ['.'] x)

let axiom_phAbsorbPlusL n:  Lemma (placeholder + n = placeholder)
  [SMTPat (placeholder + n)] = admit ()
let axiom_phAbsorbPlusR n:  Lemma (n + placeholder = placeholder)
  [SMTPat (n + placeholder)] = admit ()
let axiom_phAbsorbMinus (): Lemma (- placeholder = placeholder) = admit ()
let lemma_phAbsorbMinusL n: Lemma (n - placeholder = placeholder) [SMTPat (n - placeholder)] = 
  axiom_phAbsorbMinus (); axiom_phAbsorbPlusR n
let lemma_phAbsorbMinusR n: Lemma (placeholder - n = placeholder) [SMTPat (placeholder - n)] =  axiom_phAbsorbPlusL n
let axiom_phAbsorbLeL v:    Lemma (placeholder < v = placeholder)
  [SMTPat (placeholder < v)] = admit ()
let axiom_phAbsorbLeR v:    Lemma (v < placeholder = placeholder)
  [SMTPat (v < placeholder)] = admit ()


#set-options "--ugly"
let td: decls = _ by (
    let t = generate_patched_defs
      (strings_to_pnames [
        false, "LioStar";
        // false, "Meta";
        // false, "Core.Lattice";
      ]) (`erase) (`labelType) (`checkLabeled)
    in
    // fail (term_to_string (quote t));
    exact (quote t)
)

let xx = fun global_arg_patch_fun_0 ->
  let x1 l i lv =
    let xx = l == 34 in
    let lv' =
      LioStar.Effect.label i (LioStar.Effect.erase _ (LioStar.Ghost.hide l) global_arg_patch_fun_0)
    in
    true
  in
  x1

let _= global_arg_patch_fun_0: labelType
            -> Prims.Tot
              (l: labelType
                  -> Prims.Tot
                    (i: int
                        -> Prims.Tot
                          (lv: labeled int
                              -> LioStar.Effect.Ifc bool
                                  (fun c ->
                                      label_pre (LioStar.Ghost.hide l) c /\ unlabel_pre lv c /\
                                      preCanReach l c)
                                  (fun _ _ _ -> l_True))))

// let eqLabeled_patched _ = eqLabeled



let def = (`(fun global_arg_patch_fun_0 l i _ ->
            let lv' =
              erase #int
                (label i (
                  // erase _ 
                    (LioStar.Ghost.hide l)
                    // global_arg_patch_fun_0
                  )
                )
                global_arg_patch_fun_0
            in
            true))

let hey: unit = _ by (
  let t = tc (top_env ()) def in
  exact (`())
)


let f :
  global_arg_patch_fun_0: labelType
            -> Prims.Tot
              (l: labelType
                  -> Prims.Tot
                    (i: int
                        -> Prims.Tot
                          (lv: labeled int
                              -> LioStar.Effect.Ifc bool
                                  (fun c ->
                                      label_pre (LioStar.Ghost.hide l) c /\ unlabel_pre lv c /\
                                      preCanReach l c)
                                  (fun _ _ _ -> l_True))))
  =        (fun global_arg_patch_fun_0 (l: labelType) i _ ->
            let lv' =
              erase _
                (label i (erase _ (LioStar.Ghost.hide l <: labelType) global_arg_patch_fun_0))
                global_arg_patch_fun_0
            in
            true)





#push-options "--lax --print_implicits --print_full_names"
%splice[] td
 

%splice[] (
  
    let td = generate_patched_defs
      (strings_to_pnames [
        false, "LioStar";
        // false, "Meta";
        // false, "Core.Lattice";
      ]) (`erase) (`labelType) (`checkLabeled)
    in
    // fail (term_to_string (quote t));
    // fail (term_to_string (quote td));
    td
    // let Some (checkLabeled_typ, checkLabeled_def) = admit (); MetaTools.Util.sglet_of_name ["ExampleNiki";"checkLabeled"] in
    // let [_;checkLabeled'] = admit (); td in
    // // fail (term_to_string (quote checkLabeled'));
    // let Sg_Let _ fv us typ def = inspect_sigelt checkLabeled' in
    // [ pack_sigelt (Sg_Let false fv [] typ checkLabeled_def) ]
    // let t = [a] in
    // []//t
)

#pop-options

// let test = reify (eqLabeled_patched 0 (mkLabel 3 (G.hide 12)) (mkLabel 3 (G.hide 12))) ({cur = G.hide 0; prop = G.hide (fun _ -> True); state = ()})

// let x = _ by (
//   call1 (`rFun) f
// )


let axiom_phAbsorb (#a: Type0)
  : Lemma (__proj__Mklabeled'__item__label (placeholder #(labeled a)) == placeholder)
  [SMTPat (__proj__Mklabeled'__item__label (placeholder #(labeled a)))] = admit ()

let axiom_phAbsorb' (#a: Type0)
  : Lemma (__proj__Mklabeled'__item__value (placeholder #(labeled a)) == placeholder)
  [SMTPat (__proj__Mklabeled'__item__value (placeholder #(labeled a)))] = admit ()

let axiom_phAbsorb'' (#a: Type0) (bodyThen bodyElse: a)
  : Lemma ((if placeholder #bool then bodyThen else bodyElse) == placeholder #a)
  // [SMTPat ((if placeholder #bool then bodyThen else bodyElse) == placeholder #a)]
  = admit ()
  
// let axiom_phAbsorb''' (#a: eqtype) (bodyThen bodyElse: a)
//   : Lemma ((if placeholder #bool then bodyThen else bodyElse) = placeholder #a)
//   [SMTPat ((if placeholder #bool then bodyThen else bodyElse))]
//   = admit ()

let axiomx_phAbsorb''' (#a: eqtype) (bodyThen bodyElse: a)
  : Lemma ((iF (placeholder #bool) bodyThen bodyElse) = placeholder #a)
  [SMTPat (iF (placeholder #bool) bodyThen bodyElse)]
  = admit ()


// let axiom_phAbsorb'''' (#a: eqtype) (bodyThen bodyElse: a)
//   : Lemma (
//     ( match placeholder #bool with
//     | true -> bodyThen
//     | false -> bodyElse)
//     = placeholder #a
//   )
//   [SMTPat (bodyThen)]
//   = admit ()

let eqLabeled_patched_tot = reifyN (`eqLabeled_patched)
let eqLabeled_tot = reifyN (`eqLabeled)

let emptyState = ({cur = G.hide 0; prop = G.hide (fun _ -> True); state = ()})

// let _ = assert ( forall c l x y. eqLabeled_patched_tot )
// let x = eqLabeled_patched_tot 100 emptyState (mkLabel 1 (G.hide 112)) (mkLabel 3 (G.hide 12))

let c = emptyState
let l = 10
let x = mkLabel 12 (G.hide 12)
let y = mkLabel 1 (G.hide 123)

let _ = assert ( forall c l x y.
     eqLabeled_patched_tot l c x y
  == eqLabeled_tot l c x y
  )

// let y _ = eqLabeled_patched (admit (); 1) (mkLabel 3 (G.hide 12)) (mkLabel 3 (G.hide 12))



