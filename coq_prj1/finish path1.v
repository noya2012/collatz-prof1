Require Import Nat.
Require Import Lia.
Require Import PeanoNat.
Require Import Arith.
(* noya2012@126.com 306000250@qq.com  zeng  *)
(* 导入基础定义文件 *)

Load "collatz_part_four.v".
(* 证明：当n是偶数时，nth_sequence_value的下一个值是当前值除以2 *)
Theorem nth_sequence_value_div2 : forall n i,
  valid_input n ->
  valid_operation (nth_sequence_value n i) R0 ->
  nth_sequence_value n (S i) = (nth_sequence_value n i) / 2.
Proof.
  intros n i Hvalid Hop.
  rewrite nth_sequence_value_succ.  (* 使用已有的nth_sequence_value_succ *)
  unfold collatz_step.
  unfold valid_operation in Hop.
  rewrite Hop.
  reflexivity.
Qed.

(* Helper lemma: R0 operations strictly decrease values *)
Lemma R0_strict_descent : forall n,
  valid_input n -> 
  is_even n ->
  collatz_step n < n.
Proof.
  intros n Hvalid Heven.
  unfold collatz_step, is_even in *.
  rewrite Heven.
  
  (* 证明 n >= 2 *)
  assert (H: n >= 2). {
    unfold valid_input in Hvalid.
    apply Nat.even_spec in Heven.
    destruct Heven as [k Hk].
    rewrite Hk in *.
    assert (k >= 1) by lia.
    lia.
  }
  
  (* 现在证明 n/2 < n *)
  apply Nat.div_lt; lia.
Qed.

(* Helper lemma: R1 operations have bounded growth *)
Lemma R1_bounded_growth : forall n,
  valid_input n ->
  is_odd n ->
  collatz_step n <= 3 * n + 1.
Proof.
  intros n Hvalid Hodd.
  unfold collatz_step, valid_input, is_odd in *.
  
  (* 使用Hodd *)
  rewrite Hodd.
  (* 证明 3 * n + 1 <= 3 * n + 1 *)
  lia.
Qed.

Theorem binary_ternary_connection : forall n op1 op2,
  valid_binary_combination n op1 op2 ->
  exists op3,
  valid_ternary_combination n op1 op2 op3.
Proof.
  intros n op1 op2 Hvalid.
  unfold valid_binary_combination in Hvalid.
  unfold valid_ternary_combination.
  destruct Hvalid as [Hinput Hcomb].
  
  (* 分析所有可能的二元组合情况 *)
  destruct op1, op2; simpl in *.
  
  - (* Case R0 R0: 当前是偶数，可以再加一个R0 *)
    exists R0.
    split.
    + exact Hinput.
    + exact Hcomb.
    
  - (* Case R0 R1: 当前是偶数，可以加R0 *)
    exists R0.
    split.
    + exact Hinput.
    + exact Hcomb.
    
  - (* Case R1 R0: 当前是奇数，可以加R0 *)
    exists R0.
    split.
    + exact Hinput.
    + exact Hcomb.
    
  - (* Case R1 R1: 这种情况是不可能的 *)
    contradiction.
Qed.

(* 证明除以2会使值变小的引理 *)
Lemma div2_decreases : forall n,
  valid_input n ->
  is_even n ->
  n/2 < n.
Proof.
  intros n Hvalid Heven.
  apply Nat.div_lt; try lia.
  unfold valid_input in Hvalid; lia.
Qed.

(* 偶数且大于等于1必然大于等于2 *)
Lemma even_ge_1_implies_ge_2 : forall n,
  n >= 1 ->
  is_even n ->
  n >= 2.
Proof.
  intros n Hge1 Heven.
  unfold is_even in Heven.
  destruct n.
  - (* n = 0 *)
    lia.
  - (* n = S n' *)
    destruct n.
    + (* n = 1 *)
      (* 1不是偶数 *)
      simpl in Heven.
      discriminate.
    + (* n >= 2 *)
      lia.
Qed.

(* 除以2保持valid_input *)
Lemma div2_valid : forall n,
  valid_input n ->
  is_even n ->
  valid_input (n/2).
Proof.
  intros n Hvalid Heven.
  unfold valid_input in *.
  (*证明n >= 2 *)
  assert (H: n >= 2).
  { apply even_ge_1_implies_ge_2; auto. }
  
  (* 使用n >= 2直接证明n/2 >= 1 *)
  apply Nat.div_le_lower_bound.
  - lia.  (* 2 > 0 *)
  - lia.  (* n >= 2 = 2 * 1 *)
Qed.

(* 辅助引理：三元组合的前两步产生valid结果 *)
Lemma ternary_first_two_valid : forall n op1 op2 op3,
  valid_input n ->
  valid_ternary_combination n op1 op2 op3 ->
  valid_input (nth_sequence_value n 2).
Proof.
  intros n op1 op2 op3 Hvalid Htern.
  destruct op1, op2, op3.
  - (* R0R0R0 *)
    apply R0R0_continuity.
    split.
    + exact Hvalid.
    + destruct Htern as [_ H].
      exact H.
  - (* R0R0R1 *)
    apply R0R0_continuity.
    split.
    + exact Hvalid.
    + destruct Htern as [_ H].
      exact H.
  - (* R0R1R0 *)
    apply R0R1_continuity.
    split.
    + exact Hvalid.
    + destruct Htern as [_ H].
      exact H.
  - (* R0R1R1 - 不可能 *)
    destruct Htern as [_ H].
    contradiction.
  - (* R1R0R0 *)
    apply R1R0_continuity.
    split.
    + exact Hvalid.
    + destruct Htern as [_ H].
      exact H.
  - (* R1R0R1 *)
    apply R1R0_continuity.
    split.
    + exact Hvalid.
    + destruct Htern as [_ H].
      exact H.
  - (* R1R1R0 - 不可能 *)
    destruct Htern as [_ H].
    contradiction.
  - (* R1R1R1 - 不可能 *)
    destruct Htern as [_ H].
    contradiction.
Qed.

(* nth_sequence_value n 1 等价于 collatz_step n *)
Lemma nth_sequence_value_1 : forall n,
  nth_sequence_value n 1 = collatz_step n.
Proof.
  intros n.
  unfold nth_sequence_value.
  simpl.
  reflexivity.
Qed.

Require Import Nat.
Require Import Lia.

(* 1. 4的基本性质 *)
Lemma four_eq_pow2_2 : 4 = 2^2.
Proof. reflexivity. Qed.

(* 2. 幂的乘法性质  *)
Lemma pow_mul_r : forall a b c,
  (a^b)^c = a^(b*c).
Proof.
  intros a b c.
  induction c.
  - simpl. rewrite Nat.mul_0_r. reflexivity.
  - simpl.
    rewrite IHc.
    rewrite Nat.mul_succ_r.
    rewrite <- Nat.pow_add_r.
    f_equal.
    lia.
Qed.

(* 3. 幂的分配律 *)
Lemma pow_distrib : forall a b c,
  a^(b + c) = a^b * a^c.
Proof.
  intros.
  apply Nat.pow_add_r.
Qed.

(* 4. 4的幂展开引理 *)
Lemma pow4_expand : forall k,
  4^k = 2^(2*k).
Proof.
  intro k.
  rewrite four_eq_pow2_2.
  rewrite pow_mul_r.
  reflexivity.
Qed.



  (*  序列值严格小于初始值：n * 4^r1s / 2^r0s < n *)
Theorem value_descent : forall n r0s r1s,
  valid_input n -> n > 1 ->
  r0s > 2 * r1s ->
  n * 4^r1s / 2^r0s < n.
Proof.
  intros n r0s r1s Hvalid Hgt1 Hr0s.
  
  (* 使用4的幂展开引理 *)
  rewrite pow4_expand.
  
  (* 使用r0s > 2*r1s的条件 *)
  assert (H_compare: 2*r1s < r0s) by exact Hr0s.
  
  (* 使用幂的单调性 *)
  assert (H_pow_mono: 2^(2*r1s) < 2^r0s).
  {
    apply pow2_strict_monotone.
    exact H_compare.
  }
  
  (* 证明2^r0s > 0 *)
  assert (H_pow_pos: 2^r0s > 0).
  { apply pow2_gt_0. }
  
  (* 证明2^r0s <> 0 *)
  assert (H_pow_neq_0: 2^r0s <> 0).
  { 
    apply Nat.neq_0_lt_0.
    exact H_pow_pos.
  }
  
  (* 使用除法的性质 *)
  apply Nat.div_lt_upper_bound.
  - exact H_pow_neq_0.
  - (* 处理不等式 *)
    rewrite Nat.mul_comm.
    apply Nat.mul_lt_mono_pos_r.
    + (* 证明 0 < n *)
      apply Nat.lt_trans with 1.
      * apply Nat.lt_0_1.
      * exact Hgt1.
    + exact H_pow_mono.
Qed.
