module LioStar.Meta

open Core.LioStar // We need `LIO` effect
module LIOStar = Core.LioStar
open Bus.Example
// open Bus.Lattice

// assume type labels
// assume type canFlow : labels -> labels -> bool
// assume type labeled (a: Type0)
// assume val labelOf : (vl:labeled 'a) -> labels

// assume val labelUNSAFE : (v:'a) -> (l:labels) ->  labeled 'a 

module L = FStar.List.Tot
open FStar.Tactics
open LioStar.Meta.Helpers

// Let's define `placeholder`: a polymorphic and irreducible value that is absorbant
assume val placeholder: (#a: Type) -> a
// We axiomatize its absorbant behaviour for primops
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
// let axiom_phAbsorbEqL (a:eqtype) v: Lemma ((placeholder #a = v) = placeholder)
//   [SMTPat (placeholder #a = v)] = admit ()
// let axiom_phAbsorbEqR (a:eqtype) v: Lemma ((v = placeholder #a) = placeholder)
//   [SMTPat (v = placeholder #a)] = admit ()
// let axiom_phAbsorbIf a (bThen bElse: a): Lemma ((if placeholder #bool then bThen else bElse) == placeholder #a)
  (*[SMTPat (if placeholder #bool then bThen else bElse)]*)// = admit ()
// the following should be derived for every constructor
let axiom_phAbsorbUncons_Some a: Lemma (Some? (placeholder #(option a)) = placeholder #bool)
  [SMTPat (Some? (placeholder #(option a)))] = admit ()
// let axiom_phAbsorbMatch a (body1 ...: a): Lemma (match placeholder with | SomePattern1 -> body1 | ...  == placeholder #a) = admit ()
// etc...

// foldMapTerm acts as a (specialized and restrictive) bottom-up fold/map over F* ASTs 
let rec foldMapTerm #st
    (f         : term_view -> (getTree: term -> Tac term) -> term -> Tac (term * st))
    // every sub-term (starting with the deepest) is fed in `f`
    // then with the tuple outcome (new_term, val), the subterm is replaced by `new_term` in the AST
    // and `val` is mappend to the current `st` value
    (stIsMonoid: monoid st)
    (stToString: st -> string)     // for debug purposes
    (getTree   : term -> Tac term) // given a subterm, get the whole tree
    t
    : Tac (r:term * st) =
  let h (cb: term -> Tac term_view): term -> Tac (r:term * st) = foldMapTerm f stIsMonoid stToString (fun x -> getTree (pack (cb x)))
  in let patch_bv (cb: bv -> Tac term_view) (v: bv) =
    let v = inspect_bv v
    in let sort, s = h (fun sort -> 
        let r = cb (pack_bv ({v with bv_sort=sort})) in
        r
      ) v.bv_sort
    in pack_bv ({v with bv_sort=sort}), s
  in let patch_binder (cb: binder -> Tac term_view) b =
    let v, q = inspect_binder b
    in let v, s = patch_bv (fun v -> 
       let r = cb (pack_binder v q) in
       r
      ) v
    in pack_binder v q, s
  in
  let (++) = stIsMonoid.mappend in
  let tv, s = match inspect t with
          | Tv_BVar f -> let f, s = patch_bv (fun x -> Tv_BVar x) f in Tv_BVar f, s
          | Tv_App    l (r, q) -> 
                      let l, s0 = h (fun l -> Tv_App l (r, q)) l in
                      let r, s1 = h (fun r -> Tv_App l (r, q)) r in
                      Tv_App l (r, q), s0 ++ s1
          | Tv_Abs    b t ->
                      let b, s0 = patch_binder (fun b -> Tv_Abs b t) b
                      in let t, s1 = h (fun t -> Tv_Abs b t) t
                      in Tv_Abs b t, s0 ++ s1
          | Tv_Arrow  b c -> 
                      let b, s0 = patch_binder (fun b -> Tv_Arrow b c) b in
                      let c, s1 =
                        match inspect_comp c with
                        | C_Total ret decr -> 
                          let ret, s1 = h (fun ret -> Tv_Arrow b (pack_comp (C_Total ret decr))) ret in
                          pack_comp (C_Total ret decr), s1
                        | _ -> c, s0
                      in
                      // TODO: open `c` (comp_view)
                      Tv_Arrow b c, s0
          | Tv_Refine b t ->
                      let b, s0 = patch_bv (fun b -> Tv_Refine b t) b
                      in let t, s1 = h (fun t -> Tv_Refine b t) t
                      in Tv_Refine b t, s0 ++ s1
          | Tv_Let r attrs var typ body ->
                      let var,  s0 = patch_bv (fun var -> Tv_Let r attrs var typ body) var  in
                      let typ,  s1 = h        (fun typ -> Tv_Let r attrs var typ body) typ  in
                      let body, s2 = h        (fun body-> Tv_Let r attrs var typ body) body in
                      Tv_Let r attrs var typ body, s0 ++ s1 ++ s2
          | Tv_Match t brs' -> 
                    let brs = withIndexes brs' in
                    let raw = map (
                      fun (i, (pat, ter)) ->
                        let ter, s0
                          = h (fun ter -> Tv_Match t (replaceAt brs' i (pat, ter))) ter
                        in (pat, ter), s0
                      ) brs
                    in let t', st' = h (fun t -> Tv_Match t brs') t in
                      Tv_Match t                               (L.map fst raw)
                    , st' ++ mconcat stIsMonoid (L.map snd raw)
           | Tv_AscribedT e t tac -> 
                    let e, s0 = h (fun e -> Tv_AscribedT e t tac) e in
                    let t, s1 = h (fun t -> Tv_AscribedT e t tac) t in
                    ( match tac with
                    | Some tac -> let tac, s2 = h (fun tac -> Tv_AscribedT e t (Some tac)) tac 
                                 in Tv_AscribedT e t (Some tac), s0 ++ s1 ++ s2
                    | _        ->    Tv_AscribedT e t (None    ), s0 ++ s1           )
           | Tv_AscribedC e c tac -> 
                    let e, s0 = h (fun e -> Tv_AscribedC e c None) e in
                    ( match tac with
                    | Some tac -> let tac, s1 = h (fun tac -> Tv_AscribedC e c (Some tac)) tac
                                 in Tv_AscribedC e c (Some tac), s0 ++ s1
                    | _        ->    Tv_AscribedC e c (None    ), s0           )
           | tv -> tv, stIsMonoid.mempty
  in 
  let t', s' = f tv getTree (pack tv) in
  t', s ++ s'


let erase (a:Type) (vl:labeled a) (l:labels) : Tot (labeled a)
= if labelOf vl `canFlow` l
  then vl
  else labelUNSAFE placeholder (labelOf vl)

let erase_term_unsafe (t:term) (l:term) = 
  mk_e_app (`erase) [(`_); t; l]

[@plugin]
let replace_bv (a:fv) (b:fv) (t: term) : Tac term =
  let t',_ 
    = foldMapTerm (fun _ _ t ->
      (match inspect t with
      | Tv_FVar x -> 
        if compare_fv a x = FStar.Order.Eq
        then pack (Tv_FVar b)
        else t
      | _         -> t
      ), ()
    ) unitIsMonoid (const "()") (fun t -> t) t
  in
  t'


let rec last (x: list 'a {Cons? x}): 'a =
  match x with
  | [x] -> x
  | _::tl -> last tl

let rewriteName x = x ^ "_erased"

[@plugin]
let fvName_to_erasedFvName (blacklist: list name) (f: fv): Tac fv = 
  let n = inspect_fv f in                 guard (List.length (List.rev n) >= 1);
  let simpleName::_ = List.rev n in
  let fv = pack_fv (cur_module () @ [rewriteName simpleName]) in
  let oSig = lookup_typ (top_env ()) n in guard (Some? oSig);
  let Some oSig = oSig in
  match inspect_sigelt oSig with
  | Sg_Let _ _ _ _ _ -> 
           if ( match inspect_fv f with
        | "Prims"::_ -> true
        | "FStar"::_ -> true
        // | "Bus"::"Example"::[name] -> (prefixOfStr "uu_" name)
        // | ["Bus";"Example";"receive"] -> false
        | "Core"::_ -> true // Exclude primitives
        | name -> 
               prefixOfStr "uu_" (last (admit (); name)) || L.mem name blacklist
        ) then f else fv
  | _ -> f

[@plugin]
let modif  (blacklist: list name) (m:term) cb (t : term) : Tac (r:term * list fv) =
  let t', fvs
    = foldMapTerm (fun tv getTree t' ->
      let fvs = match inspect t' with
               | Tv_FVar f -> 
                  let f' = fvName_to_erasedFvName blacklist f in
                  if compare_fv f f' = FStar.Order.Eq
                  then [] else [f]
               | _ -> []
      in
      let erased_t' = erase_term_unsafe t' m in
      let wt = getTree erased_t' in
      ( let disp message = 
            ()
            // dump ("Try to erase :\n" ^ term_to_string wt ^ "\n"^message)
        in
        (if   typechecks wt
         then (disp ("YES!"); erased_t')
         else (disp ("NOP! original: " ^ (string_of_bool (typechecks (getTree erased_t')))); t')
        )
      ), fvs
    ) listIsMonoid fvs_to_string cb t
  in
  t', fvs

type sigelt' = 
    (r:bool)
  * (
      (fv:fv)
    // * ( (us:list univ_name)
      * ( (typ:typ)
        * (def:term)
        )
      // )
    )

let sg_Let (r:bool) (fv:fv) (typ:typ) (def:term)
     = r, (fv, (typ, def))

let sigelt'_to_Sg_Let (s: sigelt'): sigelt_view
  = let r, (fv, (typ, def)) = s in
    Sg_Let r fv [] typ def

let sigelt'_to_sigelt (s: sigelt'): Tac sigelt
  = pack_sigelt (sigelt'_to_Sg_Let s)

let rec mk_erased_toplevel'helper  (blacklist: list name) (listFinished: list fv) (f: fv)
    : Tac (list fv * (list ((fv * sigelt') * list fv))) =
    if   
      ( List.Tot.existsb (fun x -> compare_fv x f = FStar.Order.Eq) listFinished
      )
    then [], []
    else (
      let n = inspect_fv f in
      let oSig = lookup_typ (top_env ()) n in guard (Some? oSig);
      let Some oSig = oSig in
      match inspect_sigelt oSig with
      | Sg_Let r _ us typ_ def ->
          let f' = fvName_to_erasedFvName blacklist f in
          let label_var: bv = pack_bv ({
                  bv_ppname = "my_current_label_special_name_for_now";
                  bv_sort = `(labels);
                  bv_index = 0;
              }) in
          let label_binder = pack_binder label_var Q_Explicit in
          let wrap_abs = fun body -> pack (Tv_Abs label_binder body) in
          let def', fvs: _ * list fv = modif blacklist
                        // (fvName_to_erasedFvName t)
                        (pack (Tv_Var label_var))
                        wrap_abs def
          in
          let fvs = L.filter (fun v -> not (exists_in_list eq_fv v listFinished))
                             (rm_dup_in_list eq_fv fvs) in
          let se = (sg_Let r f' (*us*) (Tv_Arrow label_binder (pack_comp (C_Total typ_ None))) (wrap_abs def')) in
          let dependencies = 
              fold_left (fun (listFinished', decls) todo_fv -> 
                let listFinished' = rm_dup_in_list eq_fv listFinished' in
                let listFinished'', decls' = mk_erased_toplevel'helper  blacklist listFinished' todo_fv in
                let listFinished'' = rm_dup_in_list eq_fv listFinished'' in
                listFinished'', decls' @ decls
              ) (rm_dup_in_list eq_fv (f::listFinished@fvs), [(f, se), fvs]) fvs
          in
          dependencies
      | _ -> [], []
    )

[@plugin]
let makeFvErased_in_term  (blacklist: list name) (t: term) (fvToRename: list fv): Tac term =
  fold_left (fun acc name
             -> replace_bv name (fvName_to_erasedFvName blacklist name) acc)
             t
             fvToRename

[@plugin]
let mk_erased_toplevel'  (blacklist: list name) (f: fv): Tac (list ((originalName: fv) * sigelt')) =
  let toplevels: list ((fv * sigelt') * list fv) = snd (mk_erased_toplevel'helper blacklist [] f) in
  let toplevels: list (fv * _ * list fv) = List.Tot.map (fun ((f, s), lv) -> (f, sigelt'_to_Sg_Let s, lv)) toplevels in
  let toplevels: list (fv * sigelt_view * list fv)
    = rm_dup_in_list (fun (x, _, _) (y, _, _) -> eq_fv x y) toplevels
  in
  let toplevels = L.sortWith (fun (na, _, da) (nb, _, db) -> 
    if exists_in_list eq_fv na db
    then 1
    else (if exists_in_list eq_fv nb da
          then -1
          else 0)
  ) toplevels in
  let toplevels = map (fun (name, t_, dependencies) ->
            let dependencies = name::dependencies in
            let Sg_Let r f us typ_ def = admit (); t_ in
            let def = makeFvErased_in_term blacklist def dependencies in
            (name, sg_Let r f (*us*) typ_ def, dependencies)
      ) toplevels in
  let lets: list (fv * sigelt') = map (fun (originalName, se, _) -> originalName, se) toplevels in
  lets

let mk_erased_toplevel (blacklist: list name) f: Tac unit = 
  let defs: list (fv * sigelt') = mk_erased_toplevel' blacklist f in
  let names: list fv = L.map fst defs in
  let sigelt's: list sigelt' = L.map snd defs in
  let sigelt's  = map (
    fun (r, (fv, (typ, def))) ->
       r, (fv, (makeFvErased_in_term blacklist typ names, def))
  ) sigelt's in
  let sigelts: list sigelt = map sigelt'_to_sigelt sigelt's in
  exact (quote sigelts)

(*
let label = labelUNSAFE

let add (x: labeled int) (y: labeled int): IfcTop (labeled int) (fun _ -> True) (fun _ _ _ -> True)
 = labelUNSAFE (unlabel x + unlabel y) (LIOStar.get ())

%splice[add_erased] (mk_erased_toplevel (fun x -> x ^ "_erased") (lookup (`add)))
*)

(*
unfold let ctx startLabel = { prop = (fun _ -> True);
     cur = startLabel;
     src = C;
     dst = C;
     read = 0uy;}

let get_compute (f: _ -> _ -> IfcTop _ (const True) (const3 True))
    x y = fst (reify (f x y) (ctx Bot))

let test l x y
  : Lemma (get_compute (add_erased l) x y
        == erase _ (get_compute add x y) l)
  = ()

%splice[result_erasure] (insert_tactic_result_as "result_erasure" (fun _ -> 
  mk_erased_toplevel' (fun x -> x ^ "_erased") (fv_of_term (`receive))
))

let ddd n = let x = [let Some x = admit(); L.nth result_erasure n in x] in
  exact (quote x)

%splice[getMetaSrc_erased]    (ddd 0)
%splice[getMetaDst_erased]    (ddd 1)
%splice[byte_erased]          (ddd 2)
%splice[components_erased]    (ddd 3)
%splice[getMetaRead_erased]   (ddd 5)
%splice[readBUS_erased]       (ddd 6)
%splice[write_erased]         (ddd 7)
%splice[writeBUS_erased]      (ddd 8)
%splice[receive_erased]       (ddd 4)

let mkContext cur src dst value = {
  prop = (fun _ -> True);
  cur = cur;
  src = src;
  dst = dst;
  read = value;
}

let r_erased 
  starting src dst value
  = reify (receive_erased Bot starting) (mkContext Bot src dst value)
let r
  starting src dst value
  = reify (receive            starting) (mkContext Bot src dst value)

let _ = assert (
  forall starting src dst value.
    r_erased starting src dst value == r starting src dst value
  ) by (
    unfold_def (`r_erased);
    dump "x")

%splice[receive_erased] (mk_erased_toplevel (fun x -> x ^ "_erased") (fv_of_term (`receive)))

let _ = 2
   

// let r: int * context = reify (unlabel (xxxx_erased)) ({cur = Bot})
let r: int * context = reify (unlabel (add_erased Bot (label 3 E) (label 10 Bot))) 
    (mkContext Bot C M 0uy)
let rr = fst r

 // let _ = assert (rr == magic (1)) by (compute (); dump "x")

let lemma_ph_add_left x
  : Lemma (placeholder + x == placeholder)
    [SMTPat (placeholder + x)]
  = assert (placeholder + x == placeholder) by (
      apply_lemma (quote (placeholder_absorbant int int))
    )

let _ = assert (rr = placeholder)
*)
