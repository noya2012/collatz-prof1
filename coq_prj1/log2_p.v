Require Import Nat.
Require Import Lia.
Require Import PeanoNat.
Require Import Arith.
Require Import Coq.Classes.RelationClasses.
Require Import NZAxioms NZMulOrder NZPow.


Module LogarithmDefs.
(** Base-2 Logarithm *)

(** Interface of a log2 function, then its specification on naturals *)

Module Type Log2 (Import A : Typ).
 Parameter Inline log2 : t -> t.
End Log2.

Module Type NZLog2Spec (A : NZOrdAxiomsSig')(B : Pow' A)(C : Log2 A).
 Import A B C.
 Axiom log2_spec : forall a, 0<a -> 2^(log2 a) <= a < 2^(S (log2 a)).
 Axiom log2_nonpos : forall a, a<=0 -> log2 a == 0.
End NZLog2Spec.
Module Type NZLog2 (A : NZOrdAxiomsSig)(B : Pow A) := Log2 A <+ NZLog2Spec A B.
Module Type NZLog2Prop
 (Import A : NZOrdAxiomsSig')
 (Import B : NZPow' A)
 (Import C : NZLog2 A B)
 (Import D : NZMulOrderProp A)
 (Import E : NZPowProp A B D).

Lemma log2_upper_bound : forall n,
  1 <= n ->
  2^(log2 n) <= n.
Proof.
  intros n Hn.
  assert (H: 0 < n).
  { (* 证明 0 < n *)
    apply lt_le_trans with 1.
    - apply lt_0_1.
    - exact Hn.
  }
  destruct (log2_spec n H).
  assumption.
Qed.

  End NZLog2Prop.
End LogarithmDefs.



(* 首先证明一些log2的基本性质 *)
Lemma log2_spec_high : forall n,
  n >= 1 ->
  n < 2^(S (log2 n)).
Proof.
  intros n Hn.
  apply Nat.log2_spec.
  assumption.
Qed.

(* log2的基本性质 *)
Lemma log2_lower_bound : forall n,
  n >= 1 ->
  2^(log2 n) > n/2.
Proof.
  intros n Hn.
  (* 使用log2的定义性质 *)
  assert (H1: n < 2^(S (log2 n))).
  {
    apply log2_spec_high.
    assumption.
  }
  (* 2^(S n) = 2 * 2^n *)
  replace (2^(S (log2 n))) with (2 * 2^(log2 n)) in H1.
  - (* n < 2 * 2^(log2 n) 意味着 n/2 < 2^(log2 n) *)
    apply Nat.div_lt_upper_bound in H1.
    + assumption.
    + lia.
  - rewrite Nat.pow_succ_r'.
    reflexivity.
Qed.