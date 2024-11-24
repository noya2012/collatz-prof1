Require Import Nat.
Require Import List.
Require Import Lia.
Import ListNotations.
Require Import PeanoNat.
Require Import Ring.
Require Import Arith.
(* noya2012@126.com 306000250@qq.com  zeng  *)
(* 定义考拉兹操作   文档使用coq ide8.9 版本*)
Inductive CollatzOp : Type :=
  | R0 : CollatzOp
  | R1 : CollatzOp.

(* 定义合法输入的性质 *)
Definition valid_input (n: nat) := n >= 1.

(* 辅助定义：将bool转换为Prop *)
Definition is_even (n: nat) := Nat.even n = true.
Definition is_odd (n: nat) := Nat.even n = false.

(* 定义单步考拉兹操作 *)
Definition collatz_step (n : nat) : nat :=
  if Nat.even n then n / 2
  else 3 * n + 1.

(* 定义二元组合的合法性，考虑输入条件 *)
Definition valid_binary_combination (n: nat) (op1 op2 : CollatzOp) : Prop :=
  valid_input n /\
  match op1, op2 with
  | R1, R1 => False  (* R1R1永远非法 *)
  | R0, R1 => is_even n  (* R0R1要求n是偶数 *)
  | R1, R0 => is_odd n   (* R1R0要求n是奇数 *)
  | R0, R0 => is_even n  (* R0R0要求n是偶数 *)
  end.

(* 对于偶数大于等于1的输入，R0R0可能合法 *)
Theorem R0R0_valid_for_even : forall n,
  n >= 1 -> is_even n ->
  valid_binary_combination n R0 R0.
Proof.
  intros n Hge Heven.
  unfold valid_binary_combination.
  split.
  - unfold valid_input. exact Hge.
  - exact Heven.
Qed.

(* 对于偶数大于等于1的输入，R0R1可能合法 *)
Theorem R0R1_valid_for_even : forall n,
  n >= 1 -> is_even n ->
  valid_binary_combination n R0 R1.
Proof.
  intros n Hge Heven.
  unfold valid_binary_combination.
  split.
  - unfold valid_input. exact Hge.
  - exact Heven.
Qed.

(* 对于奇数大于等于1的输入，R1R0可能合法 *)
Theorem R1R0_valid_for_odd : forall n,
  n >= 1 -> is_odd n ->
  valid_binary_combination n R1 R0.
Proof.
  intros n Hge Hodd.
  unfold valid_binary_combination.
  split.
  - unfold valid_input. exact Hge.
  - exact Hodd.
Qed.

(* 证明：R1R1永远非法 *)
Theorem R1R1_always_invalid : forall n,
  ~ valid_binary_combination n R1 R1.
Proof.
  intros n.
  unfold valid_binary_combination.
  intros [_ H].
  exact H.
Qed.

(* 二元组合的完备性定理 *)
Theorem binary_combination_completeness : forall n,
  valid_input n ->
  (valid_binary_combination n R0 R0) \/
  (valid_binary_combination n R0 R1) \/
  (valid_binary_combination n R1 R0).
Proof.
  intros n Hvalid.
  (* 任何数要么是奇数要么是偶数 *)
  assert (H: is_even n \/ is_odd n).
  {
    unfold is_even, is_odd.
    destruct (Nat.even n) eqn:E.
    - left. reflexivity.
    - right. reflexivity.
  }
  destruct H as [Heven | Hodd].
  - (* n 是偶数的情况 *)
    left. (* 选择 R0R0 *)
    unfold valid_binary_combination.
    split.
    + exact Hvalid.
    + exact Heven.
  - (* n 是奇数的情况 *)
    right. right. (* 选择 R1R0 *)
    unfold valid_binary_combination.
    split.
    + exact Hvalid.
    + exact Hodd.
Qed.

(* 修改：任何大于等于1的数要么是奇数要么是偶数 *)
Lemma even_or_odd : forall n,
  n >= 1 -> is_even n \/ is_odd n.
Proof.
  intros n H.
  unfold is_even, is_odd.
  destruct (Nat.even n) eqn:E.
  - left. reflexivity.
  - right. reflexivity.
Qed.
(* 定义三元组合的合法性 *)
Definition valid_ternary_combination (n: nat) (op1 op2 op3: CollatzOp) : Prop :=
  valid_input n /\
  match op1, op2, op3 with
  | R1, R1, _ => False  (* R1R1*永远非法 *)
  | _, R1, R1 => False  (* *R1R1永远非法 *)
  | R1, R0, R1 => is_odd n   (* R1R0R1要求n是奇数 *)
  | R0, R0, R0 => is_even n  (* R0R0R0要求n是偶数 *)
  | R0, R0, R1 => is_even n  (* R0R0R1要求n是偶数 *)
  | R0, R1, R0 => is_even n  (* R0R1R0要求n是偶数 *)
  | R1, R0, R0 => is_odd n   (* R1R0R0要求n是奇数 *)
  end.
(* 证明：R1R1R1永远非法 *)
Theorem R1R1R1_always_invalid : forall n,
  ~ valid_ternary_combination n R1 R1 R1.
Proof.
  intros n.
  unfold valid_ternary_combination.
  intros [_ H].
  exact H.
Qed.

(* 证明：R0R1R1永远非法 *)
Theorem R0R1R1_always_invalid : forall n,
  ~ valid_ternary_combination n R0 R1 R1.
Proof.
  intros n.
  unfold valid_ternary_combination.
  intros [_ H].
  exact H.
Qed.

(* 修改：对于偶数大于等于1的输入，R0R0R0可能合法 *)
Theorem R0R0R0_valid_for_even : forall n,
  n >= 1 -> is_even n ->
  valid_ternary_combination n R0 R0 R0.
Proof.
  intros n Hge Heven.
  unfold valid_ternary_combination.
  split.
  - unfold valid_input. exact Hge.
  - exact Heven.
Qed.

(* 证明：对于奇数大于等于1的输入，R1R0R0可能合法 *)
Theorem R1R0R0_valid_for_odd : forall n,
  n >= 1 -> is_odd n ->
  valid_ternary_combination n R1 R0 R0.
Proof.
  intros n Hge Hodd.
  unfold valid_ternary_combination.
  split.
  - unfold valid_input. exact Hge.
  - exact Hodd.
Qed.
(* 对偶数输入，R0R0R1可能合法 *)
Theorem R0R0R1_valid_for_even : forall n,
  n >= 1 -> is_even n ->
  valid_ternary_combination n R0 R0 R1.
Proof.
  intros n Hge Heven.
  unfold valid_ternary_combination.
  split.
  - unfold valid_input. exact Hge.
  - exact Heven.
Qed.

(* 对奇数输入，R1R0R1可能合法 *)
Theorem R1R0R1_valid_for_odd : forall n,
  n >= 1 -> is_odd n ->
  valid_ternary_combination n R1 R0 R1.
Proof.
  intros n Hge Hodd.
  unfold valid_ternary_combination.
  split.
  - unfold valid_input. exact Hge.
  - exact Hodd.
Qed.

(* 对偶数输入，R0R1R0可能合法 *)
Theorem R0R1R0_valid_for_even : forall n,
  n >= 1 -> is_even n ->
  valid_ternary_combination n R0 R1 R0.
Proof.
  intros n Hge Heven.
  unfold valid_ternary_combination.
  split.
  - unfold valid_input. exact Hge.
  - exact Heven.
Qed.
(* 证明：R1R1R0永远非法 *)
Theorem R1R1R0_always_invalid : forall n,
  ~ valid_ternary_combination n R1 R1 R0.
Proof.
  intros n.
  unfold valid_ternary_combination.
  intros [_ H].
  exact H.
Qed.
(* 证明：三元组合的完备性 *)
Theorem ternary_combination_completeness : forall n,
  valid_input n ->
  (valid_ternary_combination n R0 R0 R0) \/
  (valid_ternary_combination n R0 R0 R1) \/
  (valid_ternary_combination n R0 R1 R0) \/
  (valid_ternary_combination n R1 R0 R0) \/
  (valid_ternary_combination n R1 R0 R1).
Proof.
  intros n Hvalid.
  unfold valid_input in Hvalid.
  assert (H := even_or_odd n Hvalid).
  destruct H as [Heven | Hodd].
  - (* n是偶数的情况 *)
    left.
    unfold valid_ternary_combination.
    split.
    + exact Hvalid.
    + exact Heven.
  - (* n是奇数的情况 *)
    right. right. right. right.
    unfold valid_ternary_combination.
    split.
    + exact Hvalid.
    + exact Hodd.
Qed.

Require Import Nat.
Require Import Lia.

(* 入口函数定义 *)
Definition entry_number (d n: nat) : nat :=
  (2 * (2^d) * n) + (2^d - 2).

(* 2的幂大于0的引理 *)
Lemma gt_0_2_pow : forall n, 2^n > 0.
Proof.
  induction n.
  - simpl. lia.
  - simpl. lia.
Qed.

(* 2的幂大于等于2的引理 *)
Lemma pow2_ge_2 : forall n,
  n >= 1 -> 2^n >= 2.
Proof.
  intros n H.
  induction n.
  - inversion H.
  - simpl. 
    assert (H1: 2^n > 0) by apply gt_0_2_pow.
    lia.
Qed.
