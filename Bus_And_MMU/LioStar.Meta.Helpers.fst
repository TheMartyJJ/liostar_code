module LioStar.Meta.Helpers

open FStar.Tactics
open FStar.Tactics.Typeclasses
module L = FStar.List.Tot


let opt_bind (def: 'b) (x: option 'a) (f: 'a -> Tac 'b) =
  match x with
  | Some x -> f x
  | None   -> def

unfold let fromOption def x: Tac _ = match x with | Some x -> x | None -> def 
unfold let (<*>) #a #b (f: a -> Tac b) (x:option a): Tac _ = match x with | Some x -> Some (f x) | None -> None
unfold let (<..>) #l #l' #r (f: l ->  l') (x: l*r): (l'*r)
  = let x, y = x in (f x, y)
unfold let (<.>) #l #l' #r (f: l -> Tac l') (x: l*r): Tac (l'*r)
  = let x, y = x in (f x, y)
unfold let fmap #t (f: t -> t -> t) #lt #lt' (x: (lt -> lt') * t) (y: lt * t): Tac _
      = let (l0,r0), (l1,r1) = x, y in l0 l1, r0 `f` r1
unfold let flip f x y = f y x
unfold let tup x y = (x,y)

let rec withIndexes_helpher l (i: nat) = match l with
    | [] -> []
    | hd::tl -> (i, hd)::withIndexes_helpher tl (i+1)

let withIndexes (l: list 'a): list (nat * 'a)
  = withIndexes_helpher l 0

let rec replaceAt_helper (pos: nat) v l (i: nat) = match l with
    | [] -> []
    | hd::tl -> (if i = pos then v else hd)::replaceAt_helper pos v tl (i+1)

let replaceAt (l: list 'a) (pos: nat) (v: 'a): list 'a
  = replaceAt_helper pos v l 0

// let typechecks (t: term): Tac bool
//   = match trytac (fun _ -> tc t) with
//   | Some t -> true
//   | None -> false

let rec mkListN_helper (n: nat): list nat
    = if n = 0 then [] else n::mkListN_helper (n - 1)

let mkListN (n: nat): list nat =
  mkListN_helper n

let rec mk_abs (bs : list binder) (body : term) : Tac term (decreases bs) =
    match bs with
    | [] -> body
    | b::bs -> pack (Tv_Abs b (mk_abs bs body))

// we won't actually use typeclasses, due to some instantiation problems in meta context
class monoid a = {
  mempty: a;
  mappend: a -> a -> a;
}
instance listIsMonoid #a : monoid (list a) = {
  mempty = [];
  mappend = (@);
}
instance unitIsMonoid : monoid unit = {
  mempty = ();
  mappend = (fun _ _ -> ());
}

let mconcat m = List.Tot.fold_left m.mappend m.mempty

unfold let const x = fun _ -> x 
unfold let const3 x = fun _ -> x 

let fv_to_string v: Tot _ = String.concat "." (inspect_fv v)
let fvs_to_string lv = "[" ^ String.concat "; " (L.map fv_to_string lv) ^ "]"

let rec prefixOf (#a:eqtype) (prefix l: list a) =
  match prefix, l with
  | hdP::tlP, hdL::tlL -> if hdP = hdL then prefixOf tlP tlL else false
  | [], _ -> true
  | _ -> false
let prefixOfStr prefix str = prefixOf (String.list_of_string prefix) (String.list_of_string str)

let rec exists_in_list  (eq: 'a -> 'a -> bool) (v: 'a) (l: list 'a) =
  match l with
  | [] -> false
  | hd::tl -> 
    if eq hd v then true else exists_in_list eq v tl

let rec rm_dup_in_list_helper #a (eq: a -> a -> bool) (l: list a) (seen: list a)
    : list a
    = match l with
    | [] -> []
    | hd::tl -> if exists_in_list eq hd seen
              then rm_dup_in_list_helper eq tl seen
              else hd::rm_dup_in_list_helper eq tl (hd::seen) 

let rm_dup_in_list (eq: 'a -> 'a -> bool) (l: list 'a) =
  rm_dup_in_list_helper eq l []

let eq_fv v1 v2 = compare_fv v1 v2 = FStar.Order.Eq 

let getFirst t = match t with | Tv_Var b -> "Var"  | Tv_FVar f -> "FVar" | Tv_BVar f -> "BVar" | Tv_App l (r, q) -> "App" | Tv_Abs b t -> "Abs" | Tv_Arrow b t -> "Arrow" | Tv_Refine b t -> "Refine" | Tv_Type u -> "Type" | Tv_Const c -> "Const" | Tv_Uvar u t -> "Uvar" | Tv_Let _ r b t1 t2 -> "Let" | Tv_Match t brs -> "Match" | Tv_AscribedT e t tac -> "AscribedT" |  Tv_AscribedC e c tac -> "AscribedC" | Tv_Unknown -> "Unknown"


let writeToFile file content
  = let _ = launch_process "sh" ["-c"; "cat - > " ^ file] content in
    ()

let insert_tactic_result_as (name: string) #a (f: unit -> Tac a): Tac unit
  = let ns = cur_module () in
    let v = f () in
    let v = quote v in
    let x: list sigelt = [
        pack_sigelt (Sg_Let false (pack_fv (ns @ [name])) [] (quote a) v)
    ] in
    exact (quote x)

let lookup t = match inspect t with
                   | Tv_FVar f -> f
                   | _ -> fail "Not FV"







// let _ = assert (addition_erased Bot == magic ()) by (
//   unfold_def (`addition_erased);
//   squash_intro ();
//   let def = term_to_string (cur_goal ()) in
//   writeToFile "addition_erased.fst" def;
//   admit_all ()
//   )
  
// let makePostEraser (t: typ): Tac unit =
//   let t = norm_term [primops; iota; delta; zeta] t in
//   let x = match inspect t with
//   | Tv_BVar f          -> fail "bvar not supported"
//   | Tv_App    l (r, q) -> 
//   ( match collect_app t with
//     | f, args -> f
//     | _ -> t
//   )
//   | Tv_Abs    b t      -> fail "abs not supported"
//   | Tv_Arrow  b c      -> fail "cannot erase arrow type!"
//   | Tv_Refine b t      -> let {bv_sort} = inspect_bv b in bv_sort 
//   | Tv_Let r attrs var typ body -> fail "cannot erase a let"
//   | Tv_Match t brs'    ->  fail "cannot erase a match"
//   | _ -> fail "cannot erase that"
//   in
//   ()
