module Test

include Bus.Lattice
module S = StateFull

noeq type labeled (l: Type0) (v: Type u#n): Type u#n = {
  value: v; 
  label: l;
}

noeq type is_lio: Type u#2 = {
  labelType: Type u#0;
  stateType: Type u#1;
  stateDescriptor: Type u#0 -> Type u#0;
  readState: (a: Type0) -> stateDescriptor a -> stateType
    -> option (labeled labelType a);
  writeState: (a: Type0) -> stateDescriptor a -> stateType
    -> option (labeled labelType a) -> stateType;

  ge: labelType -> labelType -> bool; // this could be Type0, actually
  join: labelType -> labelType -> bool;
  bot: labelType;
}

noeq
type ctx (lio: is_lio) = {
  cur: lio.labelType;
  prop: (prop: (lio.labelType -> Type0)
        {prop cur});
  state: lio.stateType
}

type pre_t (lio: is_lio)
  = ctx lio -> Type0
type post_t (lio: is_lio) (a:Type)
  = labeled lio.labelType a -> ctx lio -> Type0
type wp_t (lio: is_lio) (a:Type)
  = wp:(post_t lio a -> pre_t lio){
  forall (p q:post_t lio a).
    (forall x m. p x m ==> q x m) ==>
    (forall m. wp p m ==> wp q m)
}

type repr (a:Type) (lio: is_lio) (wp:wp_t lio a) =
  m:ctx lio ->
  PURE (labeled lio.labelType a & ctx lio) (fun p -> wp (fun r m1 -> p (r, m1)) m)

let return (a:Type) (lio: is_lio) (x: a)
: repr a lio (fun p m -> p ({value = x; label = lio.bot}) m)
= fun m -> ({value = x; label = lio.bot}, m)

let bind (a:Type) (b:Type) (lio: is_lio)
  (wp_f:wp_t lio a)
  (wp_g:a -> wp_t lio b)
  (f:repr a lio wp_f) (g:(x:a -> repr b lio (wp_g x)))
  : repr b lio (fun p -> wp_f (fun x -> (wp_g x.value) p))
= fun m ->
  let (x, m) = f m in
  (g x.value) m

let subcomp (a:Type) (lio: is_lio)
  (wp_f:wp_t lio a) (wp_g:wp_t lio a)
  (f:repr a lio wp_f)
: Pure (repr a lio wp_g)
  (requires forall p m. wp_g p m ==> wp_f p m)
  (ensures fun _ -> True)
= f

let if_then_else (a:Type) (lio: is_lio)
  (wp_f:wp_t lio a) (wp_g:wp_t lio a)
  (f:repr a lio wp_f) (g:repr a lio wp_g)
  (p:Type0)
: Type
= repr a lio (fun post m -> (p ==> wp_f post m) /\ ((~ p) ==> wp_g post m))

total reifiable reflectable
layered_effect {
  IFC : (a:Type) -> (lio: is_lio) -> wp_t lio a -> Effect
  with repr         = repr         ;
       return       = return       ;
       bind         = bind         ;
       subcomp      = subcomp      ;
       if_then_else = if_then_else 
}
