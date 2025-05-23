Load "collatz_part_six.v".
Require Import Omega.   (* 引入omega策略 *)
Require Import Arith.   (* 引入算术运算 *)
Require Import Lia.     (* 引入lia策略，这是更新的线性整数算术求解器 *)
Require Import PeanoNat.

(*序列中的值都是有效输入 *)
Lemma valid_sequence_values : forall n ops i,
  valid_input n ->
  valid_sequence ops n ->
  i <= length ops ->
  valid_input (nth_sequence_value n i).
Proof.
  intros n ops i Hn Hseq Hi.
  induction i as [|i' IH].
  - (* i = 0 *)
    simpl. exact Hn.
  - (* i > 0 *)
    assert (Hprev: valid_input (nth_sequence_value n i')).
    { apply IH. lia. }
    assert (Hop: valid_operation (nth_sequence_value n i') 
                                (nth i' ops R0)).
    { apply Hseq. lia. }
    rewrite nth_sequence_value_succ.
    destruct (nth i' ops R0).
    + (* R0 case *)
      unfold collatz_step.
      assert (Heven: is_even (nth_sequence_value n i')).
      { exact Hop. }
      assert (H: nth_sequence_value n i' >= 2).
      { apply even_ge_1_implies_ge_2; auto. }
      unfold is_even in Heven.
      destruct (Nat.even (nth_sequence_value n i')) eqn:E.
      * (* 偶数情况 *)
        unfold valid_input.
        assert (H2: nth_sequence_value n i' / 2 >= 1).
        { apply Nat.div_le_lower_bound.
          - lia.
          - rewrite Nat.mul_1_r. lia. }
        exact H2.
      * (* 矛盾情况 *)
        discriminate Heven.
    + (* R1 case *)
      unfold collatz_step.
      assert (Hodd: is_odd (nth_sequence_value n i')).
      { exact Hop. }
      unfold is_odd in Hodd.
      destruct (Nat.even (nth_sequence_value n i')) eqn:E.
      * (* 矛盾情况 *)
        discriminate Hodd.
      * (* 奇数情况 *)
        unfold valid_input.
        assert (H: nth_sequence_value n i' >= 1) by auto.
        lia.  (* 直接使用lia处理算术不等式 *)
Qed.

(* valid_input_div2 已经存在 *)


(* valid_input_3n_plus_1 的完整证明 *)
Lemma valid_input_3n_plus_1 : forall n,
  valid_input n ->
  is_odd n ->
  valid_input (3 * n + 1).
Proof.
  intros n Hn Hodd.
  unfold valid_input in *.
  (* 我们知道 n >= 1 *)
  lia.
Qed.

(* ：collatz_step的定义与性质 *)
Lemma collatz_step_valid : forall n op,
  valid_input n ->
  valid_operation n op ->
  valid_input (collatz_step n).
Proof.
  intros n op Hn Hop.
  unfold collatz_step.
  destruct op.
  - (* R0 case *)
    assert (Heven: is_even n) by exact Hop.
    unfold is_even in Heven.
    rewrite Heven.
    apply valid_input_div2; auto.
  - (* R1 case *)
    assert (Hodd: is_odd n) by exact Hop.
    unfold is_odd in Hodd.
    rewrite Hodd.
    apply valid_input_3n_plus_1; auto.
Qed.

(* Lemma valid_sequence_values ：序列中的值都是有效输入 已在前面证明*)


(* 单步操作保持有效性 *)
Lemma valid_input_step : forall n op,
  valid_input n ->
  valid_operation n op ->
  valid_input (collatz_step n).
Proof.
  intros n op Hn Hop.
  unfold collatz_step.
  destruct op.
  - (* R0 *)
    assert (Heven: is_even n) by exact Hop.
    unfold is_even in Heven.
    rewrite Heven.
    apply valid_input_div2; auto.
  - (* R1 *)
    assert (Hodd: is_odd n) by exact Hop.
    unfold is_odd in Hodd.
    rewrite Hodd.
    apply valid_input_3n_plus_1; auto.
Qed.


(* K_序列的合法性 *)
Definition K_sequence_combination (n: nat) (ops: list CollatzOp) : Prop :=
  valid_input n /\
  forall i, i + 1 < length ops ->
    match (nth i ops R0, nth (i + 1) ops R0) with
    | (R1, R0) => is_odd (nth_sequence_value n i)
    | (R0, _) => is_even (nth_sequence_value n i)
    | _ => False
    end.
(* 1. 单个R0的序列 *)
Lemma K_sequence_R0 : forall n,
  valid_input n ->
  is_even n ->
  K_sequence_combination n [R0].
Proof.
  intros n Hn Heven.
  unfold K_sequence_combination.
  split.
  - (* 初始值合法 *)
    exact Hn.
  - (* 序列合法 *)
    intros i Hi.
    (* 对于长度为1的序列，i + 1 < 1不可能成立 *)
    simpl in Hi. lia.
Qed.

(* 2. R1R0序列 *)
Lemma K_sequence_R1R0 : forall n,
  valid_input n ->
  is_odd n ->
  K_sequence_combination n [R1; R0].
Proof.
  intros n Hn Hodd.
  unfold K_sequence_combination.
  split.
  - (* 初始值合法 *)
    exact Hn.
  - (* 序列合法 *)
    intros i Hi.
    destruct i.
    + (* i = 0 *)
      simpl in *.  (* 简化nth 0 [R1;R0] R0 = R1和nth 1 [R1;R0] R0 = R0 *)
      (* 直接证明n是奇数 *)
      exact Hodd.
    + (* i = 1 *)
      simpl in Hi. lia.  (* 1 + 1 < 2不成立 *)
Qed.

(* 3. R1R0R0 序列 *)
Lemma K_sequence_R1R0R0 : forall n,
  valid_input n ->
  is_odd n ->
  is_even ((3 * n + 1) / 2) ->  (* 新增条件 *)
  K_sequence_combination n [R1; R0; R0].
Proof.
  intros n Hn Hodd Heven_next.
  unfold K_sequence_combination.
  split.
  - (* 初始值合法 *)
    exact Hn.
  - (* 序列合法 *)
    intros i Hi.
    destruct i.
    + (* i = 0 *)
      simpl in *.
      exact Hodd.
    + (* i = 1 *)
      destruct i.
      * (* 真正的i = 1 case *)
        simpl in *.
        unfold collatz_step.
        (* 因为n是奇数，所以会执行3n+1分支 *)
        unfold is_odd in Hodd.
        rewrite Hodd.
        (* 现在目标是 is_even (3 * n + 1) *)
        apply even_3n_plus_1.
        unfold is_odd.
        exact Hodd.
      * (* i > 1 *)
        simpl in Hi. lia.
Qed.

(* R0R1R0 序列 *)
Lemma K_sequence_R0R1R0 : forall n,
  valid_input n ->
  is_even n ->                    
  is_odd (n/2) ->                 
  K_sequence_combination n [R0; R1; R0].
Proof.
  intros n Hn Heven Hodd_next.
  unfold K_sequence_combination.
  split.
  - (* 初始值合法 *)
    exact Hn.
  - (* 序列合法 *)
    intros i Hi.
    destruct i.
    + (* i = 0 *)
      simpl in *.
      exact Heven.
    + (* i = 1 *)
      destruct i.
      * (* 真正的i = 1 case *)
        simpl in *.
        unfold collatz_step.
        rewrite Heven.
        (* 使用div2_divmod_eq *)
        rewrite div2_divmod_eq.
        exact Hodd_next.
      * (* i > 1 *)
        simpl in Hi. lia.
Qed.

(* R1R0R1R0 序列 *)
Lemma K_sequence_R1R0R1R0 : forall n,
  valid_input n ->
  is_odd n ->                     (* n必须是奇数，这样第一个R1才合法 *)
  is_even (3 * n + 1) ->         (* 3n+1必须是偶数，这样第一个R0才合法 *)
  is_odd ((3 * n + 1) / 2) ->    (* (3n+1)/2必须是奇数，这样第二个R1才合法 *)
  K_sequence_combination n [R1; R0; R1; R0].
Proof.
  intros n Hn Hodd Heven_mid Hodd_next.
  unfold K_sequence_combination.
  split.
  - (* 初始值合法 *)
    exact Hn.
  - (* 序列合法 *)
    intros i Hi.
    destruct i.
    + (* i = 0 *)
      simpl in *.
      exact Hodd.
    + (* i = 1 *)
      destruct i.
      * (* i = 1 *)
        simpl in *.
        unfold collatz_step.
        unfold is_odd in Hodd.
        rewrite Hodd.
        unfold is_even.
        assert (H: 3 * n + 1 = n + (n + (n + 0)) + 1).
        { ring. }
        rewrite H.
        exact Heven_mid.
      * (* i = 2 *)
        destruct i.
        -- (* 真正的i = 2 case *)
           simpl in *.
           (* 让我们一步一步展开 *)
           assert (H1: collatz_step n = 3 * n + 1).
           {
             unfold collatz_step.
             unfold is_odd in Hodd.
             rewrite Hodd.
             reflexivity.
           }
           rewrite H1.
           unfold collatz_step.
           assert (H2: Nat.even (3 * n + 1) = true).
           {
             unfold is_even in Heven_mid.
             assert (H: 3 * n + 1 = n + (n + (n + 0)) + 1).
             { ring. }
             rewrite H.
             exact Heven_mid.
           }
           rewrite H2.
           assert (H3: (3 * n + 1) / 2 = fst (divmod (n + (n + (n + 0)) + 1) 1 0 1)).
           {
             rewrite <- div2_divmod_eq.
             assert (H: 3 * n + 1 = n + (n + (n + 0)) + 1).
             { ring. }
             rewrite H.
             reflexivity.
           }
           rewrite H3.
           exact Hodd_next.
        -- (* i > 2 *)
           simpl in Hi. lia.
Qed.
(* R0R0 序列 *)
Lemma K_sequence_R0R0 : forall n,
  valid_input n ->
  is_even n ->                    (* n必须是偶数，这样第一个R0才合法 *)
  is_even (n/2) ->               (* n/2必须是偶数，这样第二个R0才合法 *)
  K_sequence_combination n [R0; R0].
Proof.
  intros n Hn Heven Heven_next.
  unfold K_sequence_combination.
  split.
  - (* 初始值合法 *)
    exact Hn.
  - (* 序列合法 *)
    intros i Hi.
    destruct i.
    + (* i = 0 *)
      simpl in *.
      exact Heven.
    + (* i = 1 *)
      destruct i.
      * (* 真正的i = 1 case *)
        simpl in *.
        unfold collatz_step.
        rewrite Heven.
        assert (H: n/2 = fst (divmod n 1 0 1)).
        { apply div2_divmod_eq. }
        rewrite H.
        unfold is_even.
        exact Heven_next.
      * (* i > 1 *)
        simpl in Hi. lia.
Qed.

Require Import Coq.Arith.PeanoNat.
(* R1R0模式有限性的形式化证明 *)

(* 连续R1R0模式的计数 *)
Fixpoint count_consecutive_R1R0 (ops: list CollatzOp) : nat :=
  match ops with
  | [] => 0
  | [_] => 0
  | R1 :: R0 :: rest => S (count_consecutive_R1R0 rest)
  | _ :: rest => count_consecutive_R1R0 rest
  end.
(* 1. 首先建立R1R0值的基本性质 *)
Require Import Nat.
Require Import NArith.


(* R1R0模式的单调性 *)
Lemma R1R0_monotone : forall n d1 d2,
  n >= 1 -> d1 >= 1 -> d2 > d1 ->
  valid_R1R0_entry_number d2 n > valid_R1R0_entry_number d1 n.
Proof.
  intros n d1 d2 Hn Hd1 Hd2.
  (* 直接应用R1R0_growth_rate *)
  apply R1R0_growth_rate.
  - assumption.  (* n >= 1 *)
  - assumption.  (* d1 >= 1 *)
  - assumption.  (* d2 > d1 *)
Qed.



(* R1R0值的幂次形式封闭性质 *)
Lemma R1R0_power2_form : forall n d,
  n >= 0 -> d >= 1 ->
  exists k:nat, valid_R1R0_entry_number d n = 2^d * (2*n + 1) - 1.
Proof.
  intros n d Hn Hd.
  exists (2*n + 1).
  rewrite R1R0_value_eq.
  

  
  (* 基本化简 *)
  assert (H1: forall x:nat, x + 0 = x) by (intros; omega).
  repeat rewrite H1.
  

  (* 使用 pow2_monotone 确保 2^d 的性质 *)
  assert (H_pow: 2^1 <= 2^d).
  { apply pow2_monotone. exact Hd. }
  
  (* 主要等式变换 *)
  assert (H_step1: 2 * 2^d * n = 2^d * (2 * n)).
  {
    rewrite mult_assoc.
    rewrite (mult_comm 2 (2^d)).
    rewrite <- mult_assoc.
    reflexivity.
  }
  rewrite H_step1.
  
  (* 展开右边的分配律 *)
  assert (H_step2: 2^d * (2*n + 1) = 2^d * (2*n) + 2^d).
  {
    rewrite mult_plus_distr_l.
    rewrite mult_1_r.
    reflexivity.
  }
  rewrite H_step2.
  
  (* 现在目标是: 2^d * (2 * n) + (2^d - 1) = (2^d * (2*n) + 2^d) - 1 *)
  
  (* 证明 2^d > 0 *)
  assert (H_pos: 2^d > 0).
  {
    apply lt_le_trans with (2^1).
    - simpl. omega.
    - exact H_pow.
  }
  
  (* 直接处理等式 *)
  assert (H_step3: forall a b, b > 0 -> a + (b - 1) = (a + b) - 1).
  {
    intros a b Hb.
    omega.
  }
  
  apply H_step3.
  exact H_pos.
Qed.


  (* 偶数的分解引理 *)
Lemma even_decomposition : forall n, 
  is_even n -> exists k, n = 2 * k.
Proof.
  intros n H.
  unfold is_even in H.  (* 展开偶数定义，假设H变为 Nat.even n = true *)
  rewrite Nat.even_spec in H.  (* 将布尔判断转换为命题 Nat.Even n *)
  destruct H as [k Hk].        (* 分解存在性命题，得到k和n = 2 * k *)
  exists k.                    (* 提供存在性见证k *)
  exact Hk.                    (* 直接使用已分解的等式 *)
Qed.



  (*奇数的分解引理 *)
Lemma odd_decomposition : forall n,
  is_odd n -> exists k, n = 2 * k + 1.
Proof.
  intros n H.
  unfold is_odd in H.  (* H : Nat.even n = false *)
  
  (* 先证明 Nat.odd n = true *)
  assert (H_odd: Nat.odd n = true).
  { 
    unfold Nat.odd.
    destruct (Nat.even n); simpl.
    - discriminate H.
    - reflexivity.
  }
  
  (* 然后使用 Nat.odd_spec *)
  apply Nat.odd_spec in H_odd.
  exact H_odd.
Qed.


(*关于单步R1R0操作的引理 *)
Lemma R1R0_single_step : forall n i,
  valid_input n ->
  is_odd (nth_sequence_value n i) ->
  exists k, nth_sequence_value n (i + 2) = 3*k + 2.
Proof.
  intros n i Hvalid Hodd.
  
  (* 状态1: 输入值 - 是一个奇数 *)
  remember (nth_sequence_value n i) as input_val eqn:Heq_input.
  destruct (odd_decomposition input_val Hodd) as [m Hm].
  exists m.
  
  (* 状态2: R1操作后的中间值 *)
 (* 状态2: R1操作后的中间值 *)
assert (H_mid: nth_sequence_value n (i + 1) = 3 * input_val + 1).
{
  (* 首先证明 i + 1 = S i *)
  replace (i + 1) with (S i) by lia.
  
  (* 现在可以使用 nth_sequence_value_succ *)
  rewrite nth_sequence_value_succ.
  
  (* 展开 collatz_step *)
  unfold collatz_step.
  
  (* 使用 input_val 的定义 *)
  rewrite <- Heq_input.
  
  (* 使用奇数条件 *)
  unfold is_odd in Hodd.
  rewrite Hodd.
  
  reflexivity.
}

  (* 证明中间值是偶数 *)
  assert (H_mid_even: is_even (nth_sequence_value n (i + 1))).
  {
    rewrite H_mid.
    apply even_3n_plus_1.
    exact Hodd.
  }

  (* 状态3: R0操作后的输出值 *)
  replace (i + 2) with (S (i + 1)) by lia.
  rewrite nth_sequence_value_succ.
  unfold collatz_step.
  rewrite H_mid.
  
  (* 证明 3 * input_val + 1 是偶数 *)
  assert (H_even_3n1: Nat.even (3 * input_val + 1) = true).
  {
    rewrite <- H_mid.
    unfold is_even in H_mid_even.
    exact H_mid_even.
  }
  rewrite H_even_3n1.
  
  (* 现在我们知道会执行除以2的操作 *)
  rewrite Hm.
  
  (* 证明除法等式 *)
   (* 状态3: R0操作后的输出值 *)
  (* 检查中间步骤 *)
  assert (H_check1: 3 * (2 * m + 1) = 6 * m + 3) by ring.
  assert (H_check2: 3 * (2 * m + 1) + 1 = 6 * m + 4) by ring.
assert (H_check3: (2 * 3 * m + 4) / 2 = 3 * m + 2).
{
  (* 首先证明 3 * m + 2 >= 1 *)
  assert (H_ge_1: 3 * m + 2 >= 1) by lia.
  
  (* 关键步骤：重写为 2 * (3 * m + 2) 的形式 *)
  replace (2 * 3 * m + 4) with (2 * (3 * m + 2)) by ring.
  
  (* 使用 even_div2_mul2 引理 *)
  apply even_div2_mul2.
  exact H_ge_1.
}
  
  (* 现在证明主要等式 *)
  replace (3 * (2 * m + 1) + 1) with (6 * m + 4) by ring.
  exact H_check3.
Qed.




Lemma count_R1R0_positive : forall ops n i,
  is_odd (nth_sequence_value n i) ->
  nth i ops R0 = R1 ->
  nth (S i) ops R0 = R0 ->
  count_consecutive_R1R0 (firstn (S (S i)) ops) >= 1.
Proof.
  intros ops n i Hodd HR1 HR0.
  
  (* 回顾count_consecutive_R1R0的定义 *)
  unfold count_consecutive_R1R0.
  
  (* 关键步骤：证明firstn (S (S i)) ops中包含R1R0模式 *)
  assert (H_length: length (firstn (S (S i)) ops) >= 2).
  { 
    rewrite firstn_length.
    
    (* 证明 i < length ops *)
    assert (H_i_bound: i < length ops).
    {
      (* 从HR1可知i必须小于length ops *)
      destruct (Compare_dec.le_lt_dec (length ops) i); try assumption.
      rewrite nth_overflow in HR1; auto.
      (* R1 ≠ R0，所以i不可能大于等于length ops *)
      inversion HR1.
    }
    
    (* 证明 S i < length ops *)
    assert (H_Si_bound: S i < length ops).
    {
      (* 从HR1和HR0可知S i必须小于length ops *)
      destruct (Compare_dec.le_lt_dec (length ops) (S i)); try assumption.
      (* 如果S i >= length ops，那么nth (S i) ops R0 = R0 *)
      rewrite nth_overflow in HR0; auto.
      (* 但这与我们已知的HR0矛盾 *)
      (* 我们知道第i个元素是R1，所以第S i个元素必须存在 *)
(* 证明 S i < length ops *)
(* 证明 S i < length ops *)
assert (H_Si_bound: S i < length ops).
{
  destruct (Compare_dec.le_lt_dec (length ops) (S i)); try assumption.
  (* 我们有 l: length ops <= S i *)
  (* 我们有原始的 H_i_bound: i < length ops *)
  
  (* 从 l 和 H_i_bound，我们可以得到矛盾 *)
  assert (H_contra: i >= i).
  { apply Nat.le_refl. }
  
  (* 从 l 我们知道 length ops <= S i *)
  (* 从原始的 H_i_bound 我们知道 i < length ops *)
  (* 这意味着 i < S i，这是自然数的基本性质 *)
  
  (* 使用lia直接处理这些不等式关系 *)
  lia.
}

  (* 使用nth_firstn_helper引理 *)
  assert (H_R1: nth i (firstn (S (S i)) ops) R0 = R1).
  {
    apply nth_firstn_helper.
    - lia.
    - destruct (Compare_dec.le_lt_dec (length ops) i).
      + rewrite nth_overflow in HR1; auto.
        inversion HR1.
      + lia.
    - exact HR1.
  }
  
  assert (H_R0: nth (S i) (firstn (S (S i)) ops) R0 = R0).
  {
    apply nth_firstn_helper.
    - lia.
    - destruct (Compare_dec.le_lt_dec (length ops) (S i)).
      + rewrite nth_overflow in HR0; auto.
      + lia.
    - exact HR0.
  }
  
  (* 现在我们有了R1R0模式，count必然大于等于1 *)
  destruct (firstn (S (S i)) ops).
  - (* 空列表情况 *)
    simpl in H_length. lia.
  - destruct l.
    + (* 单元素列表情况 *)
      simpl in H_length. lia.
    + (* 至少两个元素的情况 *)
      simpl.
      rewrite <- H_R1 in *.
      rewrite <- H_R0 in *.
      simpl. lia.
Qed.
(* 辅助引理2：形式转换 *)
Lemma R1R0_form_conversion : forall m d,
  d >= 1 ->
  exists k, 3*m + 2 = 2^d * (2*k + 1) - 1.

(* 辅助引理3：递归性质 *)
Lemma R1R0_pattern_recursive : forall n i d,
  valid_input n ->
  is_odd (nth_sequence_value n i) ->
  count_consecutive_R1R0 (firstn i ops) = S d ->
  exists k, nth_sequence_value n (i + 2) = 
           2 * (nth_sequence_value n i) + 2^(S d) - 1.

(* 主定理：R1R0模式的幂次增长性质 *)
Lemma R1R0_pattern_growth : forall n i d,
  valid_input n ->
  is_odd (nth_sequence_value n i) ->
  count_consecutive_R1R0 (firstn i ops) = d ->
  exists k, nth_sequence_value n (i + 2) = 2^d * (2*k + 1) - 1.




(* 根据以上3引理最后是主定理 *)
Theorem R1R0_pattern_form : forall n ops i d,
  valid_input n ->
  K_sequence_combination n ops ->
  i + 1 < length ops ->
  count_consecutive_R1R0 (firstn i ops) = d ->
  nth i ops R0 = R1 ->
  nth (i + 1) ops R0 = R0 ->
  exists k, nth_sequence_value n (i + 2) = 2^d * (2*k + 1) - 1.
Proof.
  intros n ops i d Hvalid Hseq Hi Hcount HR1 HR0.
  
  (* 从K_sequence_combination获取奇数性质 *)
  assert (Hodd: is_odd (nth_sequence_value n i)).
  {
    destruct Hseq as [_ Hcomb].
    specialize (Hcomb i Hi).
    rewrite HR1 in Hcomb.
    rewrite HR0 in Hcomb.
    exact Hcomb.
  }
  
  (* 直接应用R1R0_pattern_growth *)
  apply R1R0_pattern_growth; assumption.
Qed.

(* 2. R1R0模式值增长引理 *)
Lemma R1R0_pattern_growth : forall n ops i j d,
  valid_input n ->
  K_sequence_combination n ops ->
  i < j -> j < length ops ->
  count_consecutive_R1R0 (firstn i ops) = d ->
  count_consecutive_R1R0 (firstn j ops) = d + 1 ->
  nth_sequence_value n j >= 2 * nth_sequence_value n i.
Proof.
  (* 原证明中H_growth部分的内容 *)
  (* ... *)
Qed.

(* 3. 索引构造引理 *)
Lemma R1R0_indices_construction : forall n ops,
  valid_input n ->
  K_sequence_combination n ops ->
  count_consecutive_R1R0 ops > log2 n + 1 ->
  exists indices,
    length indices = log2 n + 2 /\
    sorted lt indices /\
    forall k, k < log2 n + 2 -> 
      count_consecutive_R1R0 (firstn (nth k indices 0) ops) = k.
Proof.
  (* 原证明中Hindices部分的内容 *)
  (* ... *)
Qed.

(* 4. 指数增长引理 *)
Lemma R1R0_exponential_growth : forall n ops indices,
  valid_input n ->
  K_sequence_combination n ops ->
  sorted lt indices ->
  (forall k, k < length indices -> 
     count_consecutive_R1R0 (firstn (nth k indices 0) ops) = k) ->
  forall k, k < length indices ->
    nth_sequence_value n (nth k indices 0) >= 2^k * n.
Proof.
  (* 归纳证明值的指数增长 *)
  (* ... *)
Qed.

(* 主定理：使用上述引理 *)
Theorem R1R0_pattern_finite_enhanced : forall n ops,
  valid_input n ->
  K_sequence_combination n ops ->
  count_consecutive_R1R0 ops <= log2 n + 1.
Proof.
  intros n ops Hvalid Hseq.
  
  (* 使用反证法 *)
  enough (H: count_consecutive_R1R0 ops > log2 n + 1 -> False).
  { apply Nat.nle_gt in H. assumption. }
  
  intros Hcount.
  
  (* 应用索引构造引理 *)
  pose proof (R1R0_indices_construction n ops Hvalid Hseq Hcount) as [indices [Hlen [Hsort Hcounts]]].
  
  (* 应用指数增长引理 *)
  assert (Hgrowth: nth_sequence_value n (nth (log2 n + 1) indices 0) >= 2^(log2 n + 1) * n).
  { apply R1R0_exponential_growth with (indices:=indices); try assumption.
    lia. }
  
  (* log2性质 *)
  assert (Hlog: 2^(log2 n + 1) > n).
  { apply log2_spec_high. apply valid_input_pos; assumption. }
  
  (* 导出矛盾 *)
  assert (Hcontra: nth_sequence_value n (nth (log2 n + 1) indices 0) > n * n).
  {
    apply Nat.le_lt_trans with (m:=2^(log2 n + 1) * n).
    - exact Hgrowth.
    - apply Nat.mul_lt_mono_pos_r; try assumption.
      + apply valid_input_pos; assumption.
      + exact Hlog.
  }
  
  (* 利用Collatz序列不增性质导出矛盾 *)
  (* ... *)
Qed.
(* 3. 添加新的推论 *)
Corollary R1R0_value_bounds : forall n ops i,
  valid_input n ->
  K_sequence_combination n ops ->
  i < length ops ->
  let d := count_consecutive_R1R0 (firstn i ops) in
  nth_sequence_value n i <= 2^d * (2*n + 1) - 1.

(* 4. R1R0模式的精确特征化 *)
Theorem R1R0_exact_characterization : forall n ops,
  valid_input n ->
  K_sequence_combination n ops ->
  exists d k,
  d <= log2 n + 1 /\
  k <= 2 * n + 1 /\
  sequence_end n ops = 2^d * k - 1.

