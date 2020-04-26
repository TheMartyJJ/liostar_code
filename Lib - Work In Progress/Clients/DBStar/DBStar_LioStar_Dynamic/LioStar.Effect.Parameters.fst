module LioStar.Effect.Parameters

open LioStar.Box.Definition

module G   = FStar.Ghost
module L   = FStar.List.Tot
module LP  = FStar.List.Pure
module G   = FStar.Ghost
module I32 = FStar.Int32
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8  = FStar.UInt8
module B   = LowStar.Buffer
module LU  = LatticeUsed

module LU = LatticeUsed
type labelType = LU.labels
let canFlow (a b: labelType): bool = LU.canFlow' a b
let join (a b: labelType): labelType = LU.join' a b



let lemma_relation_canFlow_join
  : l1: labelType -> l2: labelType
  -> Lemma (l1 `join` l2 == l2 ==> l1 `canFlow` l2)
  = fun _ _ -> ()
  
let lemma_canFlow_reflexivity
  : l: _ -> Lemma (ensures (l `canFlow` l))
  = fun _ -> ()


type fixedString = U64.t

type db_id = (i: U32.t {U32.v i >= 0 && U32.v i <= 1000})

noeq
type paper box = {
  id : db_id;
  pdf: fixedString;
  review1:option (box (fixedString));
}

let box' labeled labelOf a = box labelType canFlow labeled labelOf a

unfold type database box = list (
  db_id * box (paper box)
) 

unfold type stateTypeMaker labeled labelOf: Type
  = option (database (box' labeled labelOf))
