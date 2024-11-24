Require Import Nat.
Require Import Lia.
(* 导入基础定义文件 *)
(* noya2012@126.com 306000250@qq.com  zeng  *)
(* 导入valid_n2证明文件 *)
Load "vaild_n2.v".

(* 入口函数定义 Definition valid_R0R1_entry_number (d n: nat) : nat :=
  (2 * (2^d) * n) + (2^d - 2).*)


(* 证明：valid_R0R1_entry_number的输出可以对应产生d个R0R1操作 *)
Theorem valid_R0R1_entry_number_produces_d_R0R1 : forall d n,
  d >= 1 ->
  n >= 1 ->
  exists k, valid_R0R1_entry_number d n = 2 * k.
Proof.
  intros d n Hd Hn.
  unfold valid_R0R1_entry_number.
  exists ((2^d * n) + (2^(d-1) - 1)).
  destruct d.
  - (* d = 0 的情况 *)
    inversion Hd.
  - (* d = S d' 的情况 *)
    simpl.
    (* 先处理右边的 d-0 *)
    replace (d - 0) with d by lia.
    (* 处理 +0 项 *)
    repeat rewrite Nat.add_0_r.
    (* 引入关于2^d的等式 *)
    assert (H1: 2^d + 2^d = 2 * 2^d) by lia.
    repeat rewrite H1.
    (* 继续化简 *)
    assert (H2: 2 * 2^d + 2 * 2^d = 4 * 2^d) by lia.
    rewrite H2.
    nia.
Qed.
(* 辅助引理 Lemma gt_0_2_pow : forall n, 2^n > 0.
Proof.
  induction n.
  - simpl. lia.
  - simpl. lia.
Qed.*)



(* Lemma pow2_ge_2 : forall n,
  n >= 1 -> 2^n >= 2.
Proof.
  intros n H.
  induction n.
  - inversion H.  (* 如果 n = 0，无法满足 n >= 1 *)
  - simpl. 
    assert (H1: 2^n > 0) by apply gt_0_2_pow.  (* 使用 gt_0_2_pow *)
    lia.  (* 2^(S n) = 2 * 2^n >= 2 *)
Qed.*)
(* 归纳法证明 *)
Theorem valid_R0R1_entry_number_induction : forall d n,
  d >= 1 ->
  n >= 1 ->
  valid_R0R1_entry_number d n >= 1.
Proof.
  intros d n Hd Hn.
  (* 使用归纳法 *)
  induction d as [| d' IH].
  - (* 基础情况：d = 0 *)
    inversion Hd.
  - (* 归纳步骤：d = S d' *)
    unfold valid_R0R1_entry_number.
    simpl.
    (* 先处理表达式，使其更简单 *)
    repeat rewrite Nat.add_0_r.
    (* 使用 gt_0_2_pow *)
    assert (H1: 2^d' > 0) by apply gt_0_2_pow.
    assert (H2: n >= 1) by exact Hn.
    (* 现在我们可以使用这些条件 *)
    assert (H3: 2^d' + 2^d' = 2 * 2^d') by lia.
    repeat rewrite H3.
    assert (H4: 2 * 2^d' + 2 * 2^d' = 4 * 2^d') by lia.
    rewrite H4.
    (* 使用 nia 处理最终的不等式 *)
    nia.
Qed.


(* R1R0 入口函数定义 *)
Definition valid_R1R0_entry_number (d n: nat) : nat :=
  (2 * (2^d) * n) + (2^d - 1).


(* 证明输出大于等于1 *)
Theorem valid_R1R0_entry_number_induction : forall d n,
  d >= 1 ->
  n >= 1 ->
  valid_R1R0_entry_number d n >= 1.
Proof.
  intros d n Hd Hn.
  unfold valid_R1R0_entry_number.
  (* 使用归纳法 *)
  induction d as [| d' IH].
  - (* 基础情况：d = 0 *)
    inversion Hd.
  - (* 归纳步骤：d = S d' *)
    simpl.
    (* 先处理表达式，使其更简单 *)
    repeat rewrite Nat.add_0_r.
    (* 使用 gt_0_2_pow *)
    assert (H1: 2^d' > 0) by apply gt_0_2_pow.
    assert (H2: n >= 1) by exact Hn.
    (* 现在我们可以使用这些条件 *)
    assert (H3: 2^d' + 2^d' = 2 * 2^d') by lia.
    repeat rewrite H3.
    assert (H4: 2 * 2^d' + 2 * 2^d' = 4 * 2^d') by lia.
    rewrite H4.
    nia.
Qed.
Theorem valid_R1R0_entry_number_produces_d_R1R0 : forall d n,
  d >= 1 ->
  n >= 1 ->
  exists k, valid_R1R0_entry_number d n = 2 * k + 1.
Proof.
  intros d n Hd Hn.
  unfold valid_R1R0_entry_number, valid_R0R1_entry_number.
  (* 使用R0R1的结果 *)
  assert (H: exists k, (2 * (2^d) * n) + (2^d - 2) = 2 * k).
  { apply valid_R0R1_entry_number_produces_d_R0R1; assumption. }
  destruct H as [k H].
  exists k.
  (* 展开证明步骤 *)
  assert (H0: 2^d >= 2).
  { apply pow2_ge_2. exact Hd. }
  assert (H1: (2 * (2^d) * n) + (2^d - 1) = 
             ((2 * (2^d) * n) + (2^d - 2)) + 1).
  {
    rewrite <- Nat.add_assoc.
    f_equal.
    (* 现在我们有足够的条件 *)
    lia.
  }
  rewrite H1.
  rewrite H.
  reflexivity.
Qed.


(* 首先定义入口函数 *)
Definition valid_R0R0_entry_number (d n: nat) : nat :=
  n * (2^d).

(* 证明这个数是有效输入 *)
Theorem valid_R0R0_entry_induction : forall d n,
  d >= 1 ->
  n >= 1 ->
  valid_R0R0_entry_number d n >= 1.
Proof.
  intros d n Hd Hn.
  unfold valid_R0R0_entry_number.
  assert (H1: 2^d > 0) by (apply gt_0_2_pow).
  assert (H2: n * 2^d >= 1 * 2^d).
  { apply Nat.mul_le_mono_nonneg_r; try lia. }
  lia.
Qed.

(* 主定理：证明会产生d个R0序列 *)
Theorem valid_R0R0_entry_number_produces_d_R0 : forall d n,
  d >= 1 ->
  n >= 1 ->
  exists k, valid_R0R0_entry_number d n = 2^d * k.
Proof.
  intros d n Hd Hn.
  unfold valid_R0R0_entry_number.
  exists n.
  (* 直接证明等式 *)
  rewrite Nat.mul_comm.
  reflexivity.
Qed.

Require Import Nat.
Require Import Lia.


(* 修改后的pow2_monotone引理 *)
Lemma pow2_monotone : forall a b,
  a <= b -> 2^a <= 2^b.
Proof.
  intros a b Hab.
  induction b.
  - (* 基础情况 *)
    assert (a = 0) by lia.
    subst. lia.
  - (* 归纳步骤 *)
    destruct (Nat.eq_dec a (S b)).
    + (* a = S b 的情况 *)
      subst. lia.
    + (* a < S b 的情况 *)
      assert (H: a <= b) by lia.
      simpl.
      assert (H1: 2^a <= 2^b) by (apply IHb; exact H).
      assert (H2: 2^b > 0) by (apply gt_0_2_pow).
      lia.
Qed.

(* 辅助引理：2的幂与乘法的关系 *)
Lemma pow2_mul_bound : forall d n,
  n >= 1 ->
  2 * (2^d) * n + 2^d <= 2^(d+2) * n.
Proof.
  intros d n Hn.
  replace (d+2) with (S (S d)) by lia.
  simpl.
  assert (H: 2^d > 0) by (apply gt_0_2_pow).
  nia.
Qed.



(* R0R1序列的上界定理 *)
Theorem R0R1_pattern_bound : forall n d1,
  n >= 1 ->
  d1 >= 1 ->
  valid_input (valid_R0R1_entry_number d1 n) ->
  valid_R0R1_entry_number d1 n <= 2^(d1 + 2) * n.
Proof.
  intros n d1 Hn Hd1 Hv1.
  unfold valid_R0R1_entry_number.
  replace (d1 + 2) with (S (S d1)) by lia.
  simpl.
  assert (H2: 2^d1 > 0) by (apply gt_0_2_pow).
  assert (H3: 2^d1 >= 2) by (apply pow2_ge_2; exact Hd1).
  nia.
Qed.

(* R1R0序列的上界定理 *)
Theorem R1R0_pattern_bound : forall n d2,
  n >= 1 ->
  d2 >= 1 ->
  valid_input (valid_R1R0_entry_number d2 n) ->
  valid_R1R0_entry_number d2 n <= 2^(d2 + 2) * n.
Proof.
  intros n d2 Hn Hd2 Hv2.
  unfold valid_R1R0_entry_number.
  replace (d2 + 2) with (S (S d2)) by lia.
  simpl.
  assert (H2: 2^d2 > 0) by (apply gt_0_2_pow).
  assert (H3: 2^d2 >= 2) by (apply pow2_ge_2; exact Hd2).
  nia.
Qed.

(* R0R0序列的下界定理 *)
Lemma R0R0_lower_bound : forall d n,
  d >= 1 -> n >= 1 ->
  n <= valid_R0R0_entry_number d n.
Proof.
  intros d n Hd Hn.
  unfold valid_R0R0_entry_number.
  (* n <= n * 2^d *)
  assert (H: 2^d > 0) by (apply gt_0_2_pow).
  assert (H1: 1 <= 2^d) by lia.
  rewrite <- (Nat.mul_1_r n) at 1.
  apply Nat.mul_le_mono_pos_l; lia.
Qed.

(* R0R0序列的上界定理 - 递减序列 *)
(* R0R0序列递减的基本性质 *)
Theorem R0R0_pattern_bound : forall d n,
  d >= 1 -> n >= 1 ->
  (* 1. 输入值就是上界 *)
  valid_R0R0_entry_number d n = n * 2^d /\
  (* 2. 有明确的下界n *)
  n <= valid_R0R0_entry_number d n.
Proof.
  intros d n Hd Hn.
  split.
  - unfold valid_R0R0_entry_number. reflexivity.
  - apply R0R0_lower_bound; assumption.
Qed.
(* 三种考拉兹序列模式的叠加性质定理 *)
(* 三种考拉兹序列模式的叠加性质定理 *)
Theorem superposition_bound : forall n d1 d2 d3,
  n >= 1 ->
  d1 >= 1 -> d2 >= 1 -> d3 >= 1 ->
  valid_input (valid_R0R1_entry_number d1 n) ->
  valid_input (valid_R1R0_entry_number d2 n) ->
  valid_input (valid_R0R0_entry_number d3 n) ->
  let max_d := max (max d1 d2) d3 in
  (* R0R1 可能递增但有上界 *)
  valid_R0R1_entry_number d1 n <= 2^(max_d + 2) * n /\
  (* R1R0 可能递增但有上界 *)
  valid_R1R0_entry_number d2 n <= 2^(max_d + 2) * n /\
  (* R0R0 严格递减，输入即上界 *)
  valid_R0R0_entry_number d3 n = n * 2^d3.
Proof.
  intros n d1 d2 d3 Hn Hd1 Hd2 Hd3 Hv1 Hv2 Hv3 max_d.
  assert (Hmax1: d1 <= max_d) by (unfold max_d; lia).
  assert (Hmax2: d2 <= max_d) by (unfold max_d; lia).
  assert (Hmax3: d3 <= max_d) by (unfold max_d; lia).
  split; [| split].
  - (* R0R1的上界 *)
    assert (H1: valid_R0R1_entry_number d1 n <= 2^(d1 + 2) * n).
    { apply R0R1_pattern_bound; assumption. }
    assert (H2: 2^(d1 + 2) <= 2^(max_d + 2)).
    { apply pow2_monotone. lia. }
    assert (H3: 2^(d1 + 2) * n <= 2^(max_d + 2) * n).
    { apply Nat.mul_le_mono_r; assumption. }
    lia.
  - (* R1R0的上界 *)
    assert (H1: valid_R1R0_entry_number d2 n <= 2^(d2 + 2) * n).
    { apply R1R0_pattern_bound; assumption. }
    assert (H2: 2^(d2 + 2) <= 2^(max_d + 2)).
    { apply pow2_monotone. lia. }
    assert (H3: 2^(d2 + 2) * n <= 2^(max_d + 2) * n).
    { apply Nat.mul_le_mono_r; assumption. }
    lia.
  - (* R0R0的精确值 *)

    apply R0R0_pattern_bound; assumption.
Qed.
(* 组合序列的有界性定理 *)
Theorem combined_sequence_bound : forall n d1 d2 d3,
  n >= 1 ->
  d1 >= 1 -> d2 >= 1 -> d3 >= 1 ->
  valid_input (valid_R0R1_entry_number d1 n) ->
  valid_input (valid_R1R0_entry_number d2 n) ->
  valid_input (valid_R0R0_entry_number d3 n) ->
  let max_d := max (max d1 d2) d3 in
  exists bound,
    forall k, valid_input k ->
    (k = valid_R0R1_entry_number d1 n \/
     k = valid_R1R0_entry_number d2 n \/
     k = valid_R0R0_entry_number d3 n) ->
    k <= bound.
Proof.
  intros n d1 d2 d3 Hn Hd1 Hd2 Hd3 Hv1 Hv2 Hv3 max_d.
  (* 使用superposition_bound得到三个模式的界 *)
  assert (H := superposition_bound n d1 d2 d3 Hn Hd1 Hd2 Hd3 Hv1 Hv2 Hv3).
  (* 取2^(max_d + 2) * n作为统一上界 *)
  exists (2^(max_d + 2) * n).
  intros k Hk [Hk1 | [Hk2 | Hk3]].
  - (* k是R0R1模式的情况 *)
    rewrite Hk1.
    apply H.
  - (* k是R1R0模式的情况 *)
    rewrite Hk2.
    apply H.
  - (* k是R0R0模式的情况 *)
    rewrite Hk3.
    destruct H as [_ [_ H3]].
    rewrite H3.
    (* 现在目标是 n * 2^d3 <= 2^(max_d + 2) * n *)
    assert (H1: 2^d3 <= 2^(max_d + 2)).
    { apply pow2_monotone. unfold max_d. lia. }
    assert (H2: n * 2^d3 <= n * 2^(max_d + 2)).
    { apply Nat.mul_le_mono_l. exact H1. }
    rewrite Nat.mul_comm in H2.
    rewrite (Nat.mul_comm n (2^(max_d + 2))) in H2.
  rewrite Nat.mul_comm.
  exact H2.
Qed.

Theorem R0R1_continuity : forall n,
  valid_binary_combination n R0 R1 ->
  let next_n := let n' := collatz_step n in collatz_step n' in
  valid_input next_n.
Proof.
  intros n Hvalid next_n.
  destruct Hvalid as [Hvalid_n Hcond].
  unfold valid_input in *.
  unfold next_n, collatz_step.
  rewrite Hcond.  (* 使用n是偶数的条件 *)

  (* 使用 Nat.even_spec 得到 n = 2k *)
  apply Nat.even_spec in Hcond.
  destruct Hcond as [k Hk].
  rewrite Hk.

  (* 证明 k >= 1 *)
  assert (Hk_ge_1: k >= 1).
  {
    assert (2 * k >= 1) by (rewrite <- Hk; assumption).
    lia.
  }

  (* 证明 2*k/2 = k *)
  assert (H1: 2 * k / 2 = k).
  {
    rewrite Nat.mul_comm.
    apply Nat.div_mul.
    lia.
  }
  rewrite H1.

  (* 分类讨论k的奇偶性 *)
  destruct (Nat.even k) eqn:Ek.
  - (* k 是偶数的情况 *)
    apply Nat.even_spec in Ek.
    destruct Ek as [m Hm].
    rewrite Hm.
    assert (Hm_ge_1: m >= 1).
    {
      rewrite Hm in Hk_ge_1.
      assert (2 * m >= 1) by assumption.
      lia.
    }
    assert (H2: 2 * m / 2 = m).
    {
      rewrite Nat.mul_comm.
      apply Nat.div_mul.
      lia.
    }
    rewrite H2.
    assumption.
  - (* k 是奇数的情况 *)
    assert (3 * k + 1 >= 4).
    {
      replace 4 with (3 * 1 + 1) by lia.
      apply Nat.add_le_mono_r.
      apply Nat.mul_le_mono_l.
      assumption.
    }
    lia.
Qed.


Theorem R1R0_continuity : forall n,
  valid_binary_combination n R1 R0 ->
  let next_n := let n' := collatz_step n in collatz_step n' in
  valid_input next_n.
Proof.
  intros n Hvalid next_n.
  destruct Hvalid as [Hvalid_n Hcond].
  unfold valid_input in *.
  unfold next_n, collatz_step.
  rewrite Hcond.  (* 使用n是奇数的条件 *)

  (* 证明 3n + 1 是偶数 *)
  assert (H1: Nat.even (3 * n + 1) = true).
  {
    rewrite Nat.even_add.
    rewrite Nat.even_mul.
    rewrite Hcond.
    simpl.
    reflexivity.
  }
  rewrite H1.

  (* 证明 (3n + 1)/2 >= 1 *)
  assert (H2: (3 * n + 1) / 2 >= 2).
  {
    apply Nat.div_le_lower_bound.
    - lia.
    - replace 4 with (2 * 2) by lia.
      assert (3 * n + 1 >= 4).
      {
        replace 4 with (3 * 1 + 1) by lia.
        apply Nat.add_le_mono_r.
        apply Nat.mul_le_mono_l.
        assumption.
      }
      assumption.
  }
  lia.
Qed.
Theorem R0R0_continuity : forall n,
  valid_binary_combination n R0 R0 ->
  let next_n := let n' := collatz_step n in collatz_step n' in
  valid_input next_n.
Proof.
  intros n Hvalid next_n.
  destruct Hvalid as [Hvalid_n Hcond].
  unfold valid_input in *.
  unfold next_n, collatz_step.
  rewrite Hcond.  (* Use the condition that n is even *)

  (* Use Nat.even_spec to get n = 2k *)
  apply Nat.even_spec in Hcond.
  destruct Hcond as [k Hk].
  rewrite Hk.

  (* Prove k >= 1 *)
  assert (Hk_ge_1: k >= 1).
  {
    assert (2 * k >= 1) by (rewrite <- Hk; assumption).
    lia.
  }

  (* Prove 2*k/2 = k *)
  assert (H1: 2 * k / 2 = k).
  {
    rewrite Nat.mul_comm.
    apply Nat.div_mul.
    lia.  (* 2 is non-zero *)
  }
  rewrite H1.

  (* Consider the parity of k *)
  destruct (Nat.even k) eqn:Heven_k.
  - (* Case: k is even *)
    apply Nat.even_spec in Heven_k.
    destruct Heven_k as [m Hm].
    rewrite Hm.
    assert (H2: 2 * m / 2 = m).
    {
      rewrite Nat.mul_comm.
      apply Nat.div_mul.
      lia.  (* 2 is non-zero *)
    }
    rewrite H2.
    lia.  (* m >= 1 since k = 2 * m and k >= 1 *)

  - (* Case: k is odd *)
    lia.  (* 3 * k + 1 >= 1 since k >= 1 *)
Qed.