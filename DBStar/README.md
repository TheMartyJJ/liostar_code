# README

This repo furnishes the LioStar library along with examples.

The library lives in the directory `./LioStarLib/`. We cannot use `layered_effect` for now for letting an user parametrize the library, because of issues we had with extraction. Instead, the parameters are patched into the library for each example.

## LioStar program

A LioStar program is a directory that contains a `LioStar.Effect.Parameters.fst` file. This file should contain definitions for the following definitions:

```ocaml
type stateType
type labelType
val canFlow: labelType -> labelType -> bool
val join: labelType -> labelType -> labelType

val lemma_relation_canFlow_join
  : l1: labelType -> l2: labelType
  -> Lemma (l1 `join` l2 == l2 ==> l1 `canFlow` l2)

val lemma_canFlow_reflexivity
  : l: _ -> Lemma (ensures (l `canFlow` l))
```
