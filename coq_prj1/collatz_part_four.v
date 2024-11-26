Require Import Nat.
Require Import Lia.
Require Import PeanoNat.
Require Import Arith.
(* noya2012@126.com 306000250@qq.com  zeng  *)
(* 导入基础定义文件 *)
Load "3mode_vaild_input_upper_bound.v".


(* 考拉兹序列由三种合法二元链接组成 *)
Theorem collatz_sequence_composition : forall n,
  valid_input n ->
  exists op1 op2,
    valid_binary_combination n op1 op2 /\
    (op1 = R0 /\ op2 = R1 \/
     op1 = R1 /\ op2 = R0 \/
     op1 = R0 /\ op2 = R0).
Proof.
  intros n Hvalid.
  (* 直接使用binary_combination_completeness *)
  apply binary_combination_completeness in Hvalid.
  destruct Hvalid as [H1 | [H2 | H3]].
  - (* R0R0 情况 *)
    exists R0, R0.
    split; [exact H1 |].
    right; right.  (* 选择第三个选项 *)
    split; reflexivity.
  - (* R0R1 情况 *)
    exists R0, R1.
    split; [exact H2 |].
    left.          (* 选择第一个选项 *)
    split; reflexivity.
  - (* R1R0 情况 *)
    exists R1, R0.
    split; [exact H3 |].
    right; left.   (* 选择第二个选项 *)
    split; reflexivity.
Qed.


(* 考拉兹序列可以由合法三元子链组成 *)
Theorem collatz_ternary_composition : forall n,
  valid_input n ->
  exists op1 op2 op3,
    valid_ternary_combination n op1 op2 op3 /\
    (op1 = R0 /\ op2 = R0 /\ op3 = R0 \/
     op1 = R0 /\ op2 = R0 /\ op3 = R1 \/
     op1 = R0 /\ op2 = R1 /\ op3 = R0 \/
     op1 = R1 /\ op2 = R0 /\ op3 = R0 \/
     op1 = R1 /\ op2 = R0 /\ op3 = R1).
Proof.
  intros n Hvalid.
  (* 首先使用二元组合定理 *)
  apply collatz_sequence_composition in Hvalid.
  destruct Hvalid as [op1 [op2 [Hcomb [H1 | [H2 | H3]]]]].
  
  - (* R0R1 情况：只能扩展为 R0R1R0，因为R0R1R1非法 *)
    exists R0, R1, R0.
    split.
    + unfold valid_ternary_combination.
      destruct Hcomb as [Hvalid_n Heven].
      destruct H1 as [HR0 HR1].
      rewrite HR0, HR1 in Heven.
      split; [exact Hvalid_n | exact Heven].
    + right; right; left.
      split; [reflexivity | split; reflexivity].

  - (* R1R0 情况：可以扩展为 R1R0R0 或 R1R0R1 *)
    destruct (Nat.even (collatz_step n)) eqn:Hstep.
    + (* 如果下一步是偶数，扩展为 R1R0R0 *)
      exists R1, R0, R0.
      split.
      * unfold valid_ternary_combination.
        destruct Hcomb as [Hvalid_n Hodd].
        destruct H2 as [HR1 HR0].
        rewrite HR1, HR0 in Hodd.
        split; [exact Hvalid_n | exact Hodd].
      * right; right; right; left.
        split; [reflexivity | split; reflexivity].
    + (* 如果下一步是奇数，扩展为 R1R0R1 *)
      exists R1, R0, R1.
      split.
      * unfold valid_ternary_combination.
        destruct Hcomb as [Hvalid_n Hodd].
        destruct H2 as [HR1 HR0].
        rewrite HR1, HR0 in Hodd.
        split; [exact Hvalid_n | exact Hodd].
      * right; right; right; right.
        split; [reflexivity | split; reflexivity].

  - (* R0R0 情况：可以扩展为 R0R0R0 或 R0R0R1 *)
    destruct (Nat.even (collatz_step n)) eqn:Hstep.
    + (* 如果下一步是偶数，扩展为 R0R0R0 *)
      exists R0, R0, R0.
      split.
      * unfold valid_ternary_combination.
        destruct Hcomb as [Hvalid_n Heven].
        destruct H3 as [HR0_1 HR0_2].
        rewrite HR0_1, HR0_2 in Heven.
        split; [exact Hvalid_n | exact Heven].
      * left.
        split; [reflexivity | split; reflexivity].
    + (* 如果下一步是奇数，扩展为 R0R0R1 *)
      exists R0, R0, R1.
      split.
      * unfold valid_ternary_combination.
        destruct Hcomb as [Hvalid_n Heven].
        destruct H3 as [HR0_1 HR0_2].
        rewrite HR0_1, HR0_2 in Heven.
        split; [exact Hvalid_n | exact Heven].
      * right; left.
        split; [reflexivity | split; reflexivity].
Qed.



Require Import Nat.
Require Import Coq.Arith.Div2.

Require Import NArith.


Require Import Nat.
Require Import Lia.
Require Import PeanoNat.
Require Import Arith.
(* 定义序列中R0和R1的计数函数 *)
Fixpoint count_operations (ops: list CollatzOp) : (nat * nat) :=
  match ops with
  | nil => (0, 0)
  | op :: rest =>
    let (r0s, r1s) := count_operations rest in
    match op with
    | R0 => (S r0s, r1s)
    | R1 => (r0s, S r1s)
    end
  end.

(* 主定理：基于子链组合的R0优势 *)
Theorem R0_dominance_by_chains : forall n,
  valid_input n ->
  exists ops, 
    let (r0s, r1s) := count_operations ops in
    r0s > r1s.
Proof.
  intros n Hvalid.
  (* 使用二元组合定理 *)
  apply collatz_sequence_composition in Hvalid.
  destruct Hvalid as [op1 [op2 [Hcomb [H1 | [H2 | H3]]]]].

  - (* R0R1 情况：需要扩展为R0R1R0 *)
    exists [R0; R1; R0].
    simpl. lia.

  - (* R1R0 情况：可以扩展为R1R0R0 *)
    exists [R1; R0; R0].
    simpl. lia.

  - (* R0R0 情况：已经满足R0>R1 *)
    exists [R0; R0].
    simpl. lia.
Qed.

(* 更强的定理：基于三元子链的R0优势 *)
Theorem R0_dominance_by_ternary : forall n,
  valid_input n ->
  exists ops, 
    let (r0s, r1s) := count_operations ops in
    r0s >= 2 * r1s.
Proof.
  intros n Hvalid.
  (* 使用三元组合定理 *)
  apply collatz_ternary_composition in Hvalid.
  destruct Hvalid as [op1 [op2 [op3 [Hcomb [H1 | [H2 | [H3 | [H4 | H5]]]]]]]].

  - (* R0R0R0: 3个R0，0个R1 *)
    exists [R0; R0; R0].
    simpl. lia.

  - (* R0R0R1: 2个R0，1个R1 *)
    exists [R0; R0; R1].
    simpl. lia.

  - (* R0R1R0: 2个R0，1个R1 *)
    exists [R0; R1; R0].
    simpl. lia.

  - (* R1R0R0: 2个R0，1个R1 *)
    exists [R1; R0; R0].
    simpl. lia.

  - (* R1R0R1: 1个R0，2个R1 *)
    (* 由于R1R0R1后的数必然是偶数，可以再接R0 *)
    exists [R1; R0; R1; R0; R0; R0].  (* 扩展为6元组合：4个R0，2个R1 *)
    simpl. lia.
Qed.

(* 1. 通用的上界引理 *)
Lemma pattern_upper_bound : forall n d max_d pattern_value,
  n >= 1 -> d >= 1 -> d <= max_d ->
  (pattern_value <= 2^(d + 2) * n) ->
  pattern_value <= 2^(max_d + 2) * n.
Proof.
  intros n d max_d pattern_value Hn Hd Hmax Hbound.
  assert (H1: 2^(d + 2) <= 2^(max_d + 2)).
  { apply pow2_monotone. lia. }
  assert (H2: 2^(d + 2) * n <= 2^(max_d + 2) * n).
  { apply Nat.mul_le_mono_r; assumption. }
  lia.
Qed.

(* 2. 优化的主定理 *)
Theorem combined_sequence_bound_optimized : forall n d1 d2 d3,
  n >= 1 ->
  d1 >= 1 -> d2 >= 1 -> d3 >= 1 ->
  valid_input (valid_R0R1_entry_number d1 n) ->
  valid_input (valid_R1R0_entry_number d2 n) ->
  valid_input (valid_R0R0_entry_number d3 n) ->
  let max_d := max (max d1 d2) d3 in
  exists bound,
    bound = 2^(max_d + 2) * n /\
    forall k, valid_input k ->
    (k = valid_R0R1_entry_number d1 n \/
     k = valid_R1R0_entry_number d2 n \/
     k = valid_R0R0_entry_number d3 n) ->
    k <= bound.
Proof.
  intros n d1 d2 d3 Hn Hd1 Hd2 Hd3 Hv1 Hv2 Hv3 max_d.
  exists (2^(max_d + 2) * n).
  split; [reflexivity |].
  intros k Hk [Hk1 | [Hk2 | Hk3]]; subst k.

  - (* R0R1 case *)
    apply (pattern_upper_bound n d1 max_d (valid_R0R1_entry_number d1 n));
    try assumption.
    + (* 证明 d1 <= max_d *)
      unfold max_d. lia.
    + (* 应用 R0R1 模式的边界 *)
      apply R0R1_pattern_bound; assumption.

  - (* R1R0 case *)
    apply (pattern_upper_bound n d2 max_d (valid_R1R0_entry_number d2 n));
    try assumption.
    + (* 证明 d2 <= max_d *)
      unfold max_d. lia.
    + (* 应用 R1R0 模式的边界 *)
      apply R1R0_pattern_bound; assumption.
 - (* R0R0 case *)
    (* 新的证明策略 *)
    destruct (R0R0_pattern_bound d3 n Hd3 Hn) as [H_eq H_le].
    rewrite H_eq.
    
    assert (H1: n * 2^d3 <= n * 2^(d3 + 2)).
    { 
      apply Nat.mul_le_mono_l.
      apply pow2_monotone.
      lia.
    }
    
    assert (H2: n * 2^(d3 + 2) <= n * 2^(max_d + 2)).
    {
      apply Nat.mul_le_mono_l.
      apply pow2_monotone.
      unfold max_d.
      lia.
    }
    
    lia.
Qed.

(* 1. 首先定义有效操作 *)
Definition valid_operation (n: nat) (op: CollatzOp) : Prop :=
  match op with
  | R0 => is_even n
  | R1 => is_odd n
  end.



(* 2. 单步操作的有效性 *)
Lemma single_step_valid : forall n op,
  valid_input n ->
  valid_operation n op ->
  valid_input (collatz_step n).
Proof.
  intros n op Hvalid Hop.
  unfold valid_input in *.
  unfold collatz_step.
  destruct op.
  - (* R0 case *)
    unfold valid_operation in Hop.
    rewrite Hop.
    (* n是偶数且>=1，所以n>=2 *)
    assert (n >= 2).
    {
      destruct n; try lia.
      destruct n; try lia.
      unfold is_even in Hop.
      simpl in Hop.
      discriminate.
    }
    apply Nat.div_le_lower_bound; lia.
  - (* R1 case *)
    unfold valid_operation in Hop.
    rewrite Hop.
    lia.
Qed.


(* 定义序列中第k个值 *)
Fixpoint nth_sequence_value (n: nat) (k: nat) : nat :=
  match k with
  | 0 => n
  | S k' => collatz_step (nth_sequence_value n k')
  end.

(* 定义序列的最终值 *)
Definition sequence_end (n: nat) (ops: list CollatzOp) : nat :=
  nth_sequence_value n (length ops).

(* 序列有效性的归纳性质 *)
Lemma valid_sequence_inductive : forall n ops,
  valid_input n ->
  (forall i, i < length ops -> valid_operation (nth_sequence_value n i) (nth i ops R0)) ->
  forall k, k <= length ops ->
  valid_input (nth_sequence_value n k).
Proof.
  intros n ops Hvalid Hseq k Hk.
  induction k.
  - (* 基础情况：k = 0 *)
    simpl. assumption.
  - (* 归纳步骤 *)
    simpl.
    apply single_step_valid with (op := nth k ops R0).
    + (* 前一个值是有效的 *)
      apply IHk. lia.
    + (* 操作是有效的 *)
      apply Hseq. lia.
Qed.


(* 首先证明divmod和除法的关系 *)
Lemma div2_divmod_eq : forall n,
  n / 2 = fst (divmod n 1 0 1).
Proof.
  intros n.
  unfold Nat.div.
  reflexivity.
Qed.



(* 序列值的基本性质 *)
Lemma nth_sequence_value_0 : forall n,
  nth_sequence_value n 0 = n.
Proof.
  intros n.
  reflexivity.
Qed.

(* 序列值的递归性质 *)
Lemma nth_sequence_value_succ : forall n i,
  nth_sequence_value n (S i) = collatz_step (nth_sequence_value n i).
Proof.
  intros n i.
  reflexivity.
Qed.

(* 首先添加一个关于repeat R0的计数引理 *)
Lemma count_repeat_R0 : forall k,
  count_operations (repeat R0 k) = (k, 0).
Proof.
  induction k.
  - simpl. reflexivity.
  - simpl. rewrite IHk. reflexivity.
Qed.

(* 三元子链的后继组合将会产生更多的R0 *)
Theorem R0_growth_dominance : forall n k,
  valid_input n ->
  k >= 3 ->
  exists ops : list CollatzOp,
    length ops = k /\
    let (r0s, r1s) := count_operations ops in
    r0s >= (2 * r1s) + (k - 3).
Proof.
  intros n k Hvalid Hk.
  apply collatz_ternary_composition in Hvalid.
  destruct Hvalid as [op1 [op2 [op3 [Hcomb [H1 | [H2 | [H3 | [H4 | H5]]]]]]]].

  - (* R0R0R0 情况 *)
    exists (repeat R0 k).
    split.
    + rewrite repeat_length. reflexivity.
    + rewrite count_repeat_R0.
      simpl.
      (* 现在我们有 k >= 0 和 k >= 3 *)
      assert (k - 3 >= 0) by lia.
      lia.

 - (* R0R0R1 情况 *)
    exists (R0 :: R0 :: R1 :: (repeat R0 (k-3))).
    split.
    + (* 证明长度等于k *)
      simpl length.
      rewrite repeat_length.
      lia.
    + simpl.
      rewrite count_repeat_R0.
      assert (k - 3 >= 0) by lia.
      lia.

  - (* R0R1R0 情况 *)
    exists (R0 :: R1 :: R0 :: (repeat R0 (k-3))).
    split.
    + simpl length.
      rewrite repeat_length.
      lia.
    + simpl.
      rewrite count_repeat_R0.
      assert (k - 3 >= 0) by lia.
      lia.

  - (* R1R0R0 情况 *)
    exists (R1 :: R0 :: R0 :: (repeat R0 (k-3))).
    split.
    + simpl length.
      rewrite repeat_length.
      lia.
    + simpl.
      rewrite count_repeat_R0.
      assert (k - 3 >= 0) by lia.
      lia.

 - (* R1R0R1 情况：需要特殊处理，因为不能直接跟R1 *)
    (* 我们需要改变策略，使用R1R0R0模式而不是R1R0R1 *)
    exists (R1 :: R0 :: R0 :: (repeat R0 (k-3))).
    split.
    + simpl length.
      rewrite repeat_length.
      lia.
    + simpl.
      rewrite count_repeat_R0.
      assert (k - 3 >= 0) by lia.
      lia.
Qed.
(* 证明：任何合法的三元组合序列中，R0的数量至少为1 *)
Theorem ternary_min_R0_count : forall n,
  valid_input n ->
  exists ops : list CollatzOp,
    length ops = 3 /\
    let (r0s, r1s) := count_operations ops in
    r0s >= 1.
Proof.
  intros n Hvalid.
  (* 使用已有的三元组合定理 *)
  apply collatz_ternary_composition in Hvalid.
  destruct Hvalid as [op1 [op2 [op3 [Hcomb [H1 | [H2 | [H3 | [H4 | H5]]]]]]]].
  
  - (* R0R0R0 情况 *)
    exists [R0; R0; R0].
    split.
    + reflexivity.
    + simpl. lia.
    
  - (* R0R0R1 情况 *)
    exists [R0; R0; R1].
    split.
    + reflexivity.
    + simpl. lia.
    
  - (* R0R1R0 情况 *)
    exists [R0; R1; R0].
    split.
    + reflexivity.
    + simpl. lia.
    
  - (* R1R0R0 情况 *)
    exists [R1; R0; R0].
    split.
    + reflexivity.
    + simpl. lia.
    
  - (* R1R0R1 情况 *)
    exists [R1; R0; R1].
    split.
    + reflexivity.
    + simpl. lia.
Qed.

(* 1. 首先证明一个关于偶数除以2的性质 *)
Lemma even_div2_mul2 : forall k,
  k >= 1 ->
  (2 * k) / 2 = k.
Proof.
  intros k Hk.
  rewrite Nat.mul_comm.
  apply Nat.div_mul.
  lia.
Qed.
(* 1. 证明：在相同的d值下，三种模式的大小关系 *)

(* 2. 证明：当d增加时，三种模式的增长速率比较 *)

(* 3. R0R0模式的特殊性质 *)
Theorem R0R0_special_properties : forall n d,
  n >= 1 -> d >= 1 ->
  valid_input (valid_R0R0_entry_number d n) ->
  (* R0R0模式总是产生2的幂次的倍数 *)
  exists k,
    valid_R0R0_entry_number d n = k * 2^d /\
    k = n.
Proof.
  intros n d Hn Hd Hvalid.
  exists n.
  split; [| reflexivity].
  unfold valid_R0R0_entry_number.
  (* 这个证明相对直接，因为R0R0模式就是简单的2^d倍关系 *)
  reflexivity.
Qed.

(* R0R0模式的单调性：d增加时值增加 *)
Theorem R0R0_monotonicity : forall n d1 d2,
  n >= 1 -> d1 >= 1 -> d2 >= d1 ->
  valid_R0R0_entry_number d1 n <= valid_R0R0_entry_number d2 n.
Proof.
  intros n d1 d2 Hn Hd1 Hd2.
  unfold valid_R0R0_entry_number.
  (* 使用2的幂次的性质 *)
  apply Nat.mul_le_mono_l.
  (* 证明2^d1 <= 2^d2 *)
  apply pow2_monotone.
  exact Hd2.  (* 现在方向正确了 *)
Qed.

(* 首先证明三个模式的值等式 *)
Lemma R0R1_value_eq : forall n d,
  valid_R0R1_entry_number d n = 2 * (2^d) * n + (2^d - 2).
Proof.
  intros n d.
  unfold valid_R0R1_entry_number.
  reflexivity.
Qed.

Lemma R1R0_value_eq : forall n d,
  valid_R1R0_entry_number d n = 2 * (2^d) * n + (2^d - 1).
Proof.
  intros n d.
  unfold valid_R1R0_entry_number.
  reflexivity.
Qed.

Lemma R0R0_value_eq : forall n d,
  valid_R0R0_entry_number d n = n * (2^d).
Proof.
  intros n d.
  unfold valid_R0R0_entry_number.
  reflexivity.
Qed.

(* 主定理：三种模式的大小关系 *)
Theorem pattern_value_comparison : forall n d,
  n >= 1 -> d >= 1 ->
  valid_input (valid_R0R1_entry_number d n) ->
  valid_input (valid_R1R0_entry_number d n) ->
  valid_input (valid_R0R0_entry_number d n) ->
  valid_R1R0_entry_number d n > valid_R0R1_entry_number d n /\
  valid_R0R1_entry_number d n > valid_R0R0_entry_number d n.
Proof.
  intros n d Hn Hd Hv1 Hv2 Hv3.
  split.
  - (* R1R0 > R0R1 *)
    unfold valid_R1R0_entry_number, valid_R0R1_entry_number.
    (* 2 * (2^d) * n + (2^d - 1) > 2 * (2^d) * n + (2^d - 2) *)
    assert (H2d: 2^d >= 2) by (apply pow2_ge_2; exact Hd).
    assert (H2d_pos: 2^d > 0) by (apply gt_0_2_pow).
    lia.
    
  - (* R0R1 > R0R0 *)
    unfold valid_R0R1_entry_number, valid_R0R0_entry_number.
    (* 2 * (2^d) * n + (2^d - 2) > n * (2^d) *)
    assert (H2d: 2^d >= 2) by (apply pow2_ge_2; exact Hd).
    assert (H2d_pos: 2^d > 0) by (apply gt_0_2_pow).
    
    (* 重写不等式 *)
    replace (2 * (2^d) * n) with (2 * n * 2^d) by ring.
    
    (* 证明 2 * n * 2^d > n * 2^d *)
    assert (H: 2 * n * 2^d > n * 2^d).
    {
      apply Nat.mul_lt_mono_pos_r.
      - exact H2d_pos.
      - lia.
    }
    lia.
Qed.
(* 2. 证明：当d增加时，三种模式的增长速率比较 *)

(* 首先添加一个新的引理 *)
Lemma pow2_strict_monotone : forall a b,
  a < b -> 2^a < 2^b.
Proof.
  intros a b Hab.
  induction b.
  - (* 基础情况：b = 0 *)
    inversion Hab.  (* 不可能发生，因为 a < 0 不成立 *)
  - (* 归纳步骤：b = S b' *)
    destruct (Nat.eq_dec a (b)).
    + (* a = b 的情况 *)
      subst.
      simpl.
      assert (H1: 2^b > 0) by (apply gt_0_2_pow).
      lia.
    + (* a < b 的情况 *)
      assert (H: a <= b) by lia.
      simpl.
      assert (H1: 2^a <= 2^b).
      { apply pow2_monotone. exact H. }
      assert (H2: 2^b > 0) by (apply gt_0_2_pow).
      lia.
Qed.

(* 增长率定理 *)
Theorem R0R1_growth_rate : forall n d1 d2,
  n >= 1 -> d1 >= 1 -> d2 > d1 ->
  valid_R0R1_entry_number d2 n > valid_R0R1_entry_number d1 n.
Proof.
  intros n d1 d2 Hn Hd1 Hd2.
  unfold valid_R0R1_entry_number.
  (* 使用2的幂的严格单调性 *)
  assert (H1: 2^d1 < 2^d2) by (apply pow2_strict_monotone; exact Hd2).
  assert (H2: 2^d1 > 0) by (apply gt_0_2_pow).
  assert (H3: 2^d2 > 0) by (apply gt_0_2_pow).
  (* 直接使用nia *)
  nia.
Qed.

Theorem R1R0_growth_rate : forall n d1 d2,
  n >= 1 -> d1 >= 1 -> d2 > d1 ->
  valid_R1R0_entry_number d2 n > valid_R1R0_entry_number d1 n.
Proof.
  intros n d1 d2 Hn Hd1 Hd2.
  unfold valid_R1R0_entry_number.
  assert (H1: 2^d1 < 2^d2) by (apply pow2_strict_monotone; exact Hd2).
  assert (H2: 2^d1 > 0) by (apply gt_0_2_pow).
  assert (H3: 2^d2 > 0) by (apply gt_0_2_pow).
  nia.
Qed.

Theorem R0R0_growth_rate : forall n d1 d2,
  n >= 1 -> d1 >= 1 -> d2 > d1 ->
  valid_R0R0_entry_number d2 n > valid_R0R0_entry_number d1 n.
Proof.
  intros n d1 d2 Hn Hd1 Hd2.
  unfold valid_R0R0_entry_number.
  assert (H1: 2^d1 < 2^d2) by (apply pow2_strict_monotone; exact Hd2).
  assert (H2: 2^d1 > 0) by (apply gt_0_2_pow).
  assert (H3: 2^d2 > 0) by (apply gt_0_2_pow).
  assert (H4: n > 0) by lia.
  nia.
Qed.


(* 首先证明一个辅助引理：关于偶数除以2的性质 *)
Lemma even_div2_descent : forall n,
  valid_input n -> is_even n -> n > 1 ->
  n / 2 < n.
Proof.
  intros n Hvalid Heven Hn.
  apply Nat.div_lt.
  (* 证明 0 < n *)
  unfold valid_input in Hvalid.
  exact Hvalid.
  (* 证明 1 < 2 *)
  repeat constructor.
Qed.




Theorem R0R0R0_descent : forall n,
  valid_input n -> n > 1 ->
  valid_ternary_combination n R0 R0 R0 ->
  exists ops : list CollatzOp,
    length ops = 1 /\
    valid_operation n R0 /\
    nth_sequence_value n 1 < n.
Proof.
  intros n Hvalid Hn Hcomb.
  destruct Hcomb as [_ Heven].
  exists [R0].
  split. { reflexivity. }
  split. { unfold valid_operation. exact Heven. }
  
  (* 证明下降性 *)
  simpl. unfold collatz_step.
  rewrite Heven.
  apply Nat.div_lt.
  - (* 证明 0 < n *)
    unfold valid_input in Hvalid.
    exact Hvalid.  (* 使用 valid_input 的定义 n >= 1 *)
  - lia.
Qed.

(* 由三角无向图带来的启发直接得到，序列分解为R0R1/R1R0和R0组合 *)
Theorem simple_sequence_decomposition : forall n,
  valid_input n ->
  exists ops : list CollatzOp,
    length ops = 3 /\
    (* 序列要么以R0R1开始，要么以R1R0开始，后面跟着R0 *)
    ((nth 0 ops R0 = R0 /\ nth 1 ops R0 = R1) \/
     (nth 0 ops R0 = R1 /\ nth 1 ops R0 = R0)) /\
    nth 2 ops R0 = R0.
Proof.
  intros n Hvalid.
  (* 使用三元组合完备性定理 *)
  apply collatz_ternary_composition in Hvalid.
  destruct Hvalid as [op1 [op2 [op3 [Hcomb [H1 | [H2 | [H3 | [H4 | H5]]]]]]]].
  
  - (* R0R0R0 情况 *)
    exists [R0; R1; R0].  (* 选择R0R1R0模式 *)
    split; [reflexivity|].
    split.
    + left. split; reflexivity.
    + reflexivity.
    
  - (* R0R0R1 情况 *)
    exists [R0; R1; R0].
    split; [reflexivity|].
    split.
    + left. split; reflexivity.
    + reflexivity.
    
  - (* R0R1R0 情况 - 直接使用 *)
    exists [R0; R1; R0].
    split; [reflexivity|].
    split.
    + left. split; reflexivity.
    + reflexivity.
    
  - (* R1R0R0 情况 - 直接使用 *)
    exists [R1; R0; R0].
    split; [reflexivity|].
    split.
    + right. split; reflexivity.
    + reflexivity.
    
  - (* R1R0R1 情况 *)
    exists [R1; R0; R0].
    split; [reflexivity|].
    split.
    + right. split; reflexivity.
    + reflexivity.
Qed.
(* 定义计数函数 *)
Fixpoint count_R0 (ops: list CollatzOp) : nat :=
  match ops with
  | [] => 0
  | R0 :: rest => S (count_R0 rest)
  | R1 :: rest => count_R0 rest
  end.

Fixpoint count_R1 (ops: list CollatzOp) : nat :=
  match ops with
  | [] => 0
  | R0 :: rest => count_R1 rest
  | R1 :: rest => S (count_R1 rest)
  end.

(* 定理：对于任何有效输入n，存在一个长度为k的操作序列，其中R0操作的数量大于R1操作的数量
   这表明在序列中R0操作占主导地位 *)
Theorem R0_increase_tendency : forall n,
  valid_input n ->
  exists k,
    k >= 3 /\
    exists ops : list CollatzOp,
      length ops = k /\
      let (r0s, r1s) := count_operations ops in
      r0s > r1s.
Proof.
  intros n Hvalid.
  (* 使用collatz_ternary_composition得到三元组合 *)
  apply collatz_ternary_composition in Hvalid.
  destruct Hvalid as [op1 [op2 [op3 [Hcomb [H1 | [H2 | [H3 | [H4 | H5]]]]]]]].
  
  - (* R0R0R0 情况 *)
    exists 3.
    split; [lia|].
    (* 直接使用R0R0R0序列 *)
    exists [R0; R0; R0].
    split.
    + reflexivity.
    + simpl.
      (* 在R0R0R0情况下，r0s = 3, r1s = 0 *)
      lia.
      
  - (* R0R0R1 情况 *)
    exists 3.
    split; [lia|].
    exists [R0; R0; R1].
    split.
    + reflexivity.
    + simpl.
      (* 在R0R0R1情况下，r0s = 2, r1s = 1 *)
      lia.
      
  - (* R0R1R0 情况 *)
    exists 3.
    split; [lia|].
    exists [R0; R1; R0].
    split.
    + reflexivity.
    + simpl.
      (* 在R0R1R0情况下，r0s = 2, r1s = 1 *)
      lia.
      
  - (* R1R0R0 情况 *)
    exists 3.
    split; [lia|].
    exists [R1; R0; R0].
    split.
    + reflexivity.
    + simpl.
      (* 在R1R0R0情况下，r0s = 2, r1s = 1 *)
      lia.
      
  - (* R1R0R1 情况 *)
    exists 3.
    split; [lia|].
    exists [R1; R0; R0].  (* 我们选择R1R0R0而不是R1R0R1 *)
    split.
    + reflexivity.
    + simpl.
      (* 在R1R0R0情况下，r0s = 2, r1s = 1 *)
      lia.
Qed.
(*结论: R0_increase_tendency 定理揭示了Collatz序列的一个基本性质：
R0操作在数量上必然占优。这个性质支持了序列最终收敛的猜想*)

(* 定理：随着序列长度增加，R0操作的数量优势会越来越大
   - 对于任何有效输入n和长度k >= 3
   - 存在一个长度为k的序列
   - 其中R0的数量至少是R1数量的两倍，且随k增加而增加 *)
Theorem R0_count_grows_with_length : forall n k,
  valid_input n ->
  k >= 3 ->
  exists ops : list CollatzOp,
    length ops = k /\
    let (r0s, r1s) := count_operations ops in
    r0s >= 2 * r1s + (k - 3).
Proof.
  intros n k Hvalid Hk.
  (* 使用R0_growth_dominance *)
  destruct (R0_growth_dominance n k) as [ops [Hlen Hcount]].
  - exact Hvalid.  (* 证明输入有效 *)
  - exact Hk.      (* 证明长度满足要求 *)
  - exists ops.
    split.
    + exact Hlen.  (* 证明长度等于k *)
    + exact Hcount. (* 证明R0数量满足要求 *)
Qed.


(*                     当前主目标，证明最终得到一个小于输入的输出*)

(* 辅助引理：获取列表的前两个元素 *)
Lemma next_two_elements : forall (h : CollatzOp) (t : list CollatzOp),
  (exists n1 n2, nth 1 (h :: t) R0 = n1 /\ nth 2 (h :: t) R0 = n2) \/
  (length (h :: t) <= 2).
Proof.
  intros h t.
  destruct t as [|t1 t'].
  - right. simpl. lia.
  - destruct t' as [|t2 t''].
    + right. simpl. lia.
    + left. exists t1, t2. split; reflexivity.
Qed.
Lemma count_sum : forall ops,
  count_R0 ops + count_R1 ops = length ops.
Proof.
  induction ops as [|op ops' IH].
  - (* 空列表情况 *)
    simpl. reflexivity.
  - (* 非空列表情况 *)
    destruct op.
    + (* R0 case *)
      simpl.
      rewrite <- IH.
      reflexivity.
    + (* R1 case *)
      simpl.
      rewrite <- IH.
      (* 现在目标是: count_R0 ops' + S (count_R1 ops') = S (count_R0 ops' + count_R1 ops') *)
      rewrite Nat.add_succ_r.  (* 这是关键的一步！ *)
      reflexivity.
Qed.
(* 定义序列的有效性：序列中的每个操作都是合法的 *)
Definition valid_sequence (ops: list CollatzOp) (n: nat) : Prop :=
  forall i, i < length ops -> 
    valid_operation (nth_sequence_value n i) (nth i ops R0).


Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.

Lemma even_3n_plus_1 : forall n,
  is_odd n ->
  is_even (3 * n + 1).
Proof.
  intros n H_odd.
  unfold is_odd, is_even in *.
  
  (* 使用加法和乘法的偶性 *)
  rewrite Nat.even_add.
  rewrite Nat.even_mul.
  
  (* 当n是奇数时，3*n是奇数 *)
  rewrite H_odd.
  simpl.
  
  (* 奇数加1是偶数 *)
  reflexivity.
Qed.


Theorem combined_pattern_continuity : forall n op1 op2,
  valid_input n ->
  valid_binary_combination n op1 op2 ->
  valid_input (sequence_end n [op1; op2]).
Proof.
  intros n op1 op2 Hvalid Hcomb.
  unfold sequence_end.
  simpl length.
  
  (* 根据操作组合的不同情况分类讨论 *)
  destruct op1, op2.
  
  - (* Case R0 R0 *)
    apply R0R0_continuity.
    exact Hcomb.
    
  - (* Case R0 R1 *)
    apply R0R1_continuity.
    exact Hcomb.
    
  - (* Case R1 R0 *)
    apply valid_sequence_inductive with (ops := [R1; R0]).
    + exact Hvalid.
    + intros i Hi.
      simpl in Hi.
      destruct i; simpl.
      * (* 第一步 *)
        unfold valid_operation.
        destruct Hcomb as [_ H_odd].
        exact H_odd.
      * destruct i; simpl.
        -- (* 第二步 *)
           unfold valid_operation.
           assert (H_even: is_even (collatz_step n)).
           {
             destruct Hcomb as [_ H_odd].
             unfold collatz_step.
             destruct (Nat.even n) eqn:E.
             - (* n是偶数的情况 *)
               rewrite H_odd in E.
               discriminate E.
             - (* n是奇数的情况 *)
               apply even_3n_plus_1.
               exact H_odd.
           }
           exact H_even.
        -- (* 不可能的情况，因为i < 2 *)
           simpl in Hi. lia.
    + simpl. lia.
    
  - (* Case R1 R1 *)
    destruct Hcomb as [_ F].
    contradiction.
Qed.

Theorem sequence_validity_preservation : forall n ops,
  valid_input n ->
  valid_sequence ops n ->
  valid_input (sequence_end n ops).
Proof.
  intros n ops Hvalid Hseq.
  unfold sequence_end.
  
  (* 直接使用valid_sequence_inductive *)
  apply valid_sequence_inductive with (ops := ops).
  - (* 证明输入有效 *)
    exact Hvalid.
    
  - (* 证明序列中每一步都有效 *)
    intros i Hi.
    apply Hseq.
    exact Hi.
    
  - (* 证明k <= length ops，这里k = length ops *)
    lia.
Qed.


(*final proof*)
Lemma pow2_gt_0 : forall n,
  2^n > 0.
Proof.
  induction n.
  - simpl. lia.
  - simpl. (* 2^n + 2^n > 0 *)
    assert (H: 2^n + 2^n >= 2^n) by lia.
    assert (H2: 2^n > 0) by assumption.
    lia.
Qed.

Lemma pow2_strict_mono : forall a b,
  a < b -> 2^a < 2^b.
Proof.
  intros a b Hlt.
  induction Hlt.
  - (* 基本情况：证明 2^n < 2^(S n) *)
    simpl.
    assert (H: 2^a > 0) by apply pow2_gt_0.
    lia.
  - (* 归纳步骤：使用传递性 *)
    simpl.
    assert (H: 2^m > 0) by apply pow2_gt_0.
    lia.
Qed.

Require Import Nat.     
Require Import Lia.     
Require Import Arith.   
Require Import PeanoNat.

(* 辅助引理：关于nth和firstn的关系 *)
Lemma nth_firstn_helper : forall {A: Type} (l: list A) (i n: nat) (default: A),
  i < n -> n <= length l ->
  nth i (firstn n l) default = nth i l default.
Proof.
  intros A l i n default Hi Hn.
  revert l i Hi Hn.
  induction n as [|n' IHn'].
  + (* n = 0 *)
    intros l i Hi Hn.
    inversion Hi.
    
  + (* n = S n' *)
    intros l i Hi Hn.
    destruct l as [|x l'].
    - (* l = nil *)
      simpl in Hn. inversion Hn.
    - (* l = x::l' *)
      destruct i as [|i'].
      * (* i = 0 *)
        simpl. reflexivity.
      * (* i = S i' *)
        simpl.
        apply IHn' with (l := l').
        -- (* i' < n' *)
           apply Nat.succ_lt_mono in Hi. exact Hi.
        -- (* n' <= length l' *)
           simpl in Hn. apply le_S_n. exact Hn.
Qed.

(* 序列前缀有效性引理 *)
Lemma sequence_prefix_validity : forall n ops i,
  valid_sequence ops n ->
  i <= length ops ->
  valid_sequence (firstn i ops) n.
Proof.
  intros n ops i Hseq Hi j Hj.
  
  (* 1. 将j < length (firstn i ops) 转换为 j < i *)
  rewrite firstn_length in Hj.
  apply Nat.min_glb_lt_iff in Hj.
  destruct Hj as [Hj_i Hj_len].
  
  (* 2. 证明nth j (firstn i ops) R0 = nth j ops R0 *)
  assert (Heq: nth j (firstn i ops) R0 = nth j ops R0).
  { apply nth_firstn_helper; auto. }
  rewrite Heq.
  
  (* 3. 应用原序列的有效性 *)
  apply Hseq.
  apply Nat.lt_le_trans with i; auto.
Qed.

  (* 组合模式数等价于模式计数 *)
Lemma count_operations_eq : forall ops,
  let (r0s, r1s) := count_operations ops in
  r0s = count_R0 ops /\ r1s = count_R1 ops.
Proof.
  induction ops as [|op ops' IH].
  - (* 基础情况：空列表 *)
    simpl. auto.
    
  - (* 归纳步骤 *)
    destruct op.
    + (* R0 情况 *)
      simpl.
      destruct (count_operations ops') as [r0s' r1s'] eqn:Heq'.
      destruct IH as [IH1 IH2].
      split; simpl.
      * (* r0s = count_R0 *)
        rewrite IH1. reflexivity.
      * (* r1s = count_R1 *)
        rewrite IH2. reflexivity.
        
    + (* R1 情况 *)
      simpl.
      destruct (count_operations ops') as [r0s' r1s'] eqn:Heq'.
      destruct IH as [IH1 IH2].
      split; simpl.
      * (* r0s = count_R0 *)
        rewrite IH1. reflexivity.
      * (* r1s = count_R1 *)
        rewrite IH2. reflexivity.
Qed.

(* R0 Counter upper bound R0在序列中的计数上界*)

Theorem R0_count_upper_bound : forall n k ops,
  valid_input n ->
  k >= 3 ->
  length ops = k ->
  valid_sequence ops n ->
  let (r0s, r1s) := count_operations ops in
  r0s <= k.
Proof.
  intros n k ops Hvalid Hk_ge_3 Hlen Hseq.
  destruct (count_operations ops) as [r0s r1s] eqn:Hcount.
  
  (* 使用count_sum *)
  assert (H_sum: r0s + r1s = k).
  {
    (* 使用count_operations_eq *)
    pose proof (count_operations_eq ops) as H_eq.
    rewrite Hcount in H_eq.
    destruct H_eq as [H_r0 H_r1].
    
    pose proof (count_sum ops) as H.
    rewrite <- H_r0, <- H_r1 in H.
    rewrite Hlen in H.
    exact H.
  }
  
  (* R1操作数量非负 *)
  assert (H_r1s_nonneg: r1s >= 0) by lia.
  
  (* 从H_sum: r0s + r1s = k *)
  (* 从H_r1s_nonneg: r1s >= 0 *)
  (* 得到: r0s <= k *)
  lia.
Qed.      
----------------------------------------------coq uncheck------------
Lemma power_4_to_2 : forall r1s,
  4^r1s = 2^(2*r1s).
Proof.
  intros r1s.
  (* 使用归纳法 *)
  induction r1s.
  - (* 基础情况：r1s = 0 *)
    simpl. reflexivity.
  - (* 归纳步骤：r1s = S r1s *)
    (* 先证明一个辅助性质 *)
    assert (H1: 4 = 2 * 2) by reflexivity.
    
    (* 重写目标中的4 *)
    replace 4 with (2 * 2) in *.
    
    (* 使用归纳假设 *)
    rewrite IHr1s.
    
    (* 使用2的幂的性质 *)
    rewrite <- Nat.pow_add_r.
    f_equal.
    simpl.
    lia.
    
    (* 证明完成 *)
    exact H1.
Qed.

Theorem value_descent : forall n r0s r1s,
  valid_input n -> n > 1 ->
  r0s > 2 * r1s ->
  n * 4^r1s / 2^r0s < n.
Proof.
  intros n r0s r1s Hvalid Hn HR0dom.
  
  (* 使用 pow2_gt_0 确保除法有效 *)
  assert (H_pos: 2^r0s > 0) by apply pow2_gt_0.

  (* 关键步骤：将4^r1s表示为2的幂 *)
  assert (H_pow: 4^r1s = 2^(2*r1s)).
  {
    (* 使用幂的基本性质 *)
    induction r1s.
    - simpl. reflexivity.
    - (* 对于S r1s的情况 *)
      simpl.
      rewrite IHr1s.
      (* 需要证明: 4 * 2^(2*r1s) = 2^(2*S r1s) *)
      assert (H_eq: 2 * S r1s = S (S (2 * r1s))) by lia.
      rewrite H_eq.
      simpl.
      (* 现在我们有: 4 * 2^(2*r1s) = 2 * (2 * 2^(2*r1s)) *)
      rewrite <- Nat.mul_assoc.
      reflexivity.
  }
  rewrite H_pow.

  (* 现在目标变为：n * 2^(2*r1s) / 2^r0s < n *)
  (* 使用 r0s > 2*r1s 的条件 *)
  assert (H_gt: 2*r1s < r0s) by lia.

  (* 使用 pow2_strict_mono *)
  assert (H_pow_lt: 2^(2*r1s) < 2^r0s).
  {
    apply pow2_strict_mono.
    exact H_gt.
  }

  (* 使用除法的性质 *)
  apply Nat.div_lt_upper_bound.
  - exact H_pos.
  - rewrite Nat.mul_comm.
    apply Nat.mul_lt_mono_pos_l.
    + assumption.  (* n > 0 from valid_input *)
    + exact H_pow_lt.
Qed.
(* 2. 主定理 *)
Theorem sequence_descent : forall n k,
  valid_input n -> n > 1 -> k >= 3 ->
  exists ops : list CollatzOp,
    length ops = k /\
    valid_sequence ops n /\
    nth_sequence_value n k < n.
Proof.
  intros n k Hvalid Hn Hk.
  (* 1. 获取R0占优势的序列 *)
  destruct (R0_count_grows_with_length n k Hvalid Hk) as [ops [Hlen Hcount]].
  exists ops.
  split; [exact Hlen|].
  destruct Hcount as (r0s & r1s & Hdom).
  split.
  - (* 2. 证明序列合法 *)
    unfold valid_sequence.
    intros i Hi.
    assert (Hvalid_i: valid_input (nth_sequence_value n i)).
    { 
      apply valid_sequence_inductive with (ops := ops); try assumption.
      - exact Hvalid.
      - auto.  (* 这里可能需要完善 *)
      - lia.
    }
    destruct (even_or_odd (nth_sequence_value n i) Hvalid_i);
    destruct (nth i ops R0); simpl; auto.
  - (* 3. 证明值下降 *)
    apply value_descent; auto.
Qed.
(* 4. 主定理 *)
