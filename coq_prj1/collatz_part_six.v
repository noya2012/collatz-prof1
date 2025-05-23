Require Import Nat.
Require Import Lia.
Require Import List.
Import ListNotations.
Load "collatz_part_five.v".
Require Import Nat.
Require Import Lia.
Require Import PeanoNat.
Require Import Arith.
Require Import Coq.Classes.RelationClasses.
Load "log2_p.v".

(* “我们必须知道，我们必将知道。”（"Wir müssen wissen. Wir werden wissen."） *)
(*从这里我们根据前面得到的信息，开始全局证明 
我们使用人工推导和机器推导的结合，利用本框架可靠的序列分解构造方法*)


(* 偶数除以2后仍然有效 *)
Lemma valid_input_div2 : forall n,
  valid_input n ->
  is_even n ->
  valid_input (n / 2).
Proof.
  intros n Hvalid Heven.
  (* 使用nth_sequence_value_div2 *)
  assert (valid_operation n R0) by (unfold valid_operation; auto).
  
  (* 证明sequence_end n [R0] = n / 2 *)
  assert (sequence_end n [R0] = n / 2).
  {
    unfold sequence_end.
    simpl length.
    unfold nth_sequence_value.
    simpl.
    unfold collatz_step.
    unfold is_even in Heven.
    destruct (Nat.even n); try discriminate Heven.
    reflexivity.
  }
  
  (* 使用sequence_validity_preservation *)
  assert (valid_sequence [R0] n).
  {
    unfold valid_sequence.
    intros i Hi.
    simpl in Hi.
    destruct i; try lia.
    simpl.
    auto.
  }
  
  (* 应用序列有效性保持定理并重写 *)
  rewrite <- H0.
  apply sequence_validity_preservation with (ops := [R0]); auto.
Qed.



(*根据Theorem simple_sequence_decomposition 我们有
K折叠递归结构 *)
Fixpoint build_k_steps (n: nat) (k: nat) : list CollatzOp :=
  match k with
  | 0 => []
  | S k' => 
    let prev_ops := build_k_steps n k' in
    let curr_n := sequence_end n prev_ops in
    if Nat.even curr_n 
    then prev_ops ++ [R0]          (* 偶数：添加R0 *)
    else prev_ops ++ [R1; R0]      (* 奇数：添加R1R0 *)
  end.



(* 子序列有效性引理 *)
Lemma subsequence_valid : forall n op ops,
  valid_sequence (op :: ops) n ->
  valid_sequence ops (collatz_step n).
Proof.
  intros n op ops Hvalid.
  unfold valid_sequence in *.
  intros i Hi.
  (* 先证明一个关于nth_sequence_value的基本性质 *)
  assert (Hseq: forall k, k <= i -> 
    nth_sequence_value (collatz_step n) k = nth_sequence_value n (S k)).
  { intros k Hk.
    induction k.
    - (* k = 0 *)
      rewrite nth_sequence_value_0.
      rewrite nth_sequence_value_succ.
      reflexivity.
    - (* k = S k' *)
      rewrite nth_sequence_value_succ.
      rewrite IHk by lia.
      rewrite nth_sequence_value_succ.
      reflexivity. }

  rewrite Hseq by lia.
  specialize (Hvalid (S i)).
  simpl in Hvalid.
  apply Hvalid.
  simpl. lia.
Qed.
(* 序列末尾值的有效性 *)
Lemma sequence_end_valid : forall n ops,
  valid_input n ->
  valid_sequence ops n ->
  valid_input (sequence_end n ops).
Proof.
  intros n ops Hvalid Hvalid_seq.
  unfold sequence_end.
  apply valid_sequence_inductive with (ops := ops).
  - exact Hvalid.
  - exact Hvalid_seq.
  - reflexivity.
Qed.

(* 添加第几个末尾值 *)
Lemma nth_append_last : forall (l : list CollatzOp) (x : CollatzOp),
  nth (length l) (l ++ [x]) R0 = x.
Proof.
  induction l; simpl.
  - reflexivity.
  - apply IHl.
Qed.

(* 性质：添加R0后，R0计数增加1，R1计数不变 *)
Lemma count_operations_app_R0 : forall ops,
  let (r0s, r1s) := count_operations ops in
  let (new_r0s, new_r1s) := count_operations (ops ++ [R0]) in
  new_r0s = r0s + 1 /\ new_r1s = r1s.
Proof.
  induction ops as [|op ops' IH].
  
  - (* 基础情况：空列表 *)
    simpl.
    split; reflexivity.
    
  - (* 归纳步骤 *)
    simpl.
    destruct op.
    + (* op = R0 *)
      destruct (count_operations ops') as [r0s' r1s'] eqn:Hold.
      destruct (count_operations (ops' ++ [R0])) as [new_r0s' new_r1s'] eqn:Hnew.
      destruct IH as [IH1 IH2].
      simpl in *.
      split.
      * (* R0计数 *)
        rewrite IH1. reflexivity.
      * (* R1计数 *)
        rewrite IH2. reflexivity.
        
    + (* op = R1 *)
      destruct (count_operations ops') as [r0s' r1s'] eqn:Hold.
      destruct (count_operations (ops' ++ [R0])) as [new_r0s' new_r1s'] eqn:Hnew.
      destruct IH as [IH1 IH2].
      simpl in *.
      split.
      * (* R0计数 *)
        rewrite IH1. reflexivity.
      * (* R1计数 *)
        rewrite IH2. reflexivity.
Qed.

(* 性质：添加R1R0后，R0计数增加1，R1计数增加1 *)
Lemma nth_append_two : forall (l : list CollatzOp) (x y : CollatzOp),
  nth (length l) (l ++ [x; y]) R0 = x /\
  nth (S (length l)) (l ++ [x; y]) R0 = y.
Proof.
  intros l x y. (* 先引入所有参数 *)
  induction l; simpl.
  - split; reflexivity.
  - destruct (IHl) as [H1 H2].
    split.
    + exact H1.
    + exact H2.
Qed.

(* 性质：添加R1R0后，R0计数增加1，R1计数增加1 *)
Lemma count_operations_app_R1R0 : forall ops,
  let (r0s, r1s) := count_operations ops in
  let (r0s_new, r1s_new) := count_operations (ops ++ [R1; R0]) in
  r0s_new = S r0s /\ r1s_new = S r1s.
Proof.
  intros ops.
  induction ops as [|op ops' IH].
  
  - (* 空列表情况 *)
    simpl. 
    split; reflexivity.
    
  - (* 非空列表情况 *)
    simpl.
    destruct op;
    destruct (count_operations ops') as [r0s' r1s'];
    destruct (count_operations (ops' ++ [R1; R0])) as [r0s_new' r1s_new'];
    destruct IH as [IH1 IH2].
    
    + (* op = R0 *)
      split.
      * (* r0s_new = S r0s *)
        simpl. rewrite IH1. reflexivity.
      * (* r1s_new = S r1s *)
        simpl. rewrite IH2. reflexivity.
        
    + (* op = R1 *)
      split.
      * (* r0s_new = S r0s *)
        simpl. rewrite IH1. reflexivity.
      * (* r1s_new = S r1s *)
        simpl. rewrite IH2. reflexivity.
Qed.

(* 序列构造的性质 *)
Lemma build_k_steps_valid : forall n k,
  valid_input n ->
  valid_sequence (build_k_steps n k) n.
Proof.
  intros n k Hvalid.
  induction k as [|k' IHk].
  
  - (* k = 0 *)
    simpl. unfold valid_sequence. intros. simpl in H. lia.
    
  - (* k = S k' *)
    simpl build_k_steps.
    remember (sequence_end n (build_k_steps n k')) as curr_n.
    
    (* 证明curr_n是有效输入 *)
    assert (Hvalid_curr : valid_input curr_n).
    { rewrite Heqcurr_n.
      apply sequence_end_valid with (ops := build_k_steps n k').
      - exact Hvalid.
      - exact IHk. }
    
    destruct (Nat.even curr_n) eqn:Heven.
    
    + (* 偶数情况：添加R0 *)
      assert (Hvalid_new: valid_sequence (build_k_steps n k' ++ [R0]) n).
      { unfold valid_sequence in *. intros i Hi.
        rewrite app_length in Hi. simpl in Hi.
        destruct (Nat.eq_dec i (length (build_k_steps n k'))) as [Heq|Hneq].
        - (* 新添加的R0 *)
          rewrite Heq.
          unfold valid_operation.
          assert (Hseq: curr_n = nth_sequence_value n (length (build_k_steps n k'))).
          { unfold sequence_end in Heqcurr_n.
            exact Heqcurr_n. }
          rewrite <- Hseq.
          rewrite nth_append_last.
          unfold is_even. exact Heven.
        - (* 使用原序列的有效性 *)
          assert (i < length (build_k_steps n k')) by lia.
          assert (nth i (build_k_steps n k' ++ [R0]) R0 = nth i (build_k_steps n k') R0).
          { rewrite app_nth1; auto. }
          rewrite H0.
          apply IHk.
          exact H. }
      exact Hvalid_new.
      
    + (* 奇数情况：添加R1R0 *)
      assert (Hvalid_new: valid_sequence (build_k_steps n k' ++ [R1; R0]) n).
      { unfold valid_sequence in *. intros i Hi.
        rewrite app_length in Hi. simpl in Hi.
        destruct (Nat.eq_dec i (length (build_k_steps n k'))) as [Heq1|Hneq1].
        - (* 第一个新操作R1 *)
          rewrite Heq1.
          unfold valid_operation.
          assert (Hseq: curr_n = nth_sequence_value n (length (build_k_steps n k'))).
          { unfold sequence_end in Heqcurr_n.
            exact Heqcurr_n. }
          rewrite <- Hseq.
          pose proof (nth_append_two (build_k_steps n k') R1 R0) as [H1 H2].
          rewrite H1.
          unfold is_odd.
          exact Heven.
        - destruct (Nat.eq_dec i (S (length (build_k_steps n k')))) as [Heq2|Hneq2].
          + (* 第二个新操作R0 *)
            rewrite Heq2.
            unfold valid_operation.
            assert (Hodd: is_odd curr_n).
            { unfold is_odd. exact Heven. }
            pose proof (nth_append_two (build_k_steps n k') R1 R0) as [H1 H2].
            rewrite H2.
            assert (Hstep: nth_sequence_value n (S (length (build_k_steps n k'))) = 3 * curr_n + 1).
            { 
              rewrite nth_sequence_value_succ.
              unfold collatz_step.
              assert (Hseq: nth_sequence_value n (length (build_k_steps n k')) = curr_n).
              { symmetry. exact Heqcurr_n. }
              rewrite Hseq.
              rewrite Heven.
              reflexivity.
            }
            rewrite Hstep.
            unfold is_even.
            apply even_3n_plus_1.
            exact Hodd.
          + (* 使用原序列的有效性 *)
            assert (i < length (build_k_steps n k')) by lia.
            assert (nth i (build_k_steps n k' ++ [R1; R0]) R0 = nth i (build_k_steps n k') R0).
            { rewrite app_nth1; auto. }
            rewrite H0.
            apply IHk.
            exact H. }
      exact Hvalid_new.
Qed.


(* R0和R1计数之和等于总长度的引理 *)
Lemma count_sum_c2 : forall ops,
  let (r0s, r1s) := count_operations ops in
  r0s + r1s = length ops.
Proof.
  induction ops as [|op ops' IH].
  - (* 空列表情况 *)
    simpl. reflexivity.
  - (* 非空列表情况 *)
    simpl.
    destruct (count_operations ops') as [r0s' r1s'].
    (* 使用归纳假设 *)
    assert (r0s' + r1s' = length ops') by exact IH.
    destruct op.
    + (* R0 case - 对应偶数情况 *)
      simpl.
      (* 需要证明：S r0s' + r1s' = S (length ops') *)
      lia.
    + (* R1 case - 对应奇数情况 *)
      simpl.
      (* 需要证明：r0s' + S r1s' = S (length ops') *)
      lia.
Qed.



(* 关于序列构造的辅助引理 *)
Lemma build_k_steps_Sn : forall n k,
  valid_input n ->
  build_k_steps n (S k) = 
  let prev_ops := build_k_steps n k in
  let curr_n := sequence_end n prev_ops in
  if Nat.even curr_n 
  then prev_ops ++ [R0]
  else prev_ops ++ [R1; R0].
Proof.
  intros n k Hvalid.
  simpl. reflexivity.
Qed.

(* R1计数单调递增 *)
Lemma R1_count_monotone : forall n k,
  valid_input n ->
  let (_, r1s) := count_operations (build_k_steps n k) in
  let (_, r1s') := count_operations (build_k_steps n (S k)) in
  r1s' <= r1s + 1.
Proof.
  intros n k Hvalid.
  simpl build_k_steps.
  
  (* 先处理当前序列的计数 *)
  destruct (count_operations (build_k_steps n k)) as [r0s r1s] eqn:Hcount.
  
  (* 处理下一个序列的计数 *)
  destruct (Nat.even (sequence_end n (build_k_steps n k))) eqn:Heven.
  
  - (* 偶数情况：添加R0 *)
    destruct (count_operations (build_k_steps n k ++ [R0])) as [r0s' r1s'] eqn:Hcount'.
    specialize (count_operations_app_R0 (build_k_steps n k)).
    intros H_app.
    rewrite Hcount in H_app.
    rewrite Hcount' in H_app.
    destruct H_app as [_ Heq].
    rewrite Heq. lia.
    
  - (* 奇数情况：添加R1R0 *)
    destruct (count_operations (build_k_steps n k ++ [R1; R0])) as [r0s' r1s'] eqn:Hcount'.
    specialize (count_operations_app_R1R0 (build_k_steps n k)).
    intros H_app.
    rewrite Hcount in H_app.
    rewrite Hcount' in H_app.
    destruct H_app as [_ Heq].
    rewrite Heq. lia.
Qed.


(* 序列长度至少为k *)
Lemma build_k_steps_length_min : forall n k,
  valid_input n ->
  length (build_k_steps n k) >= k.
Proof.
  induction k; intros Hvalid.
  - simpl. lia.
  - simpl build_k_steps.
    remember (sequence_end n (build_k_steps n k)) as curr_n.
    destruct (Nat.even curr_n).
    + rewrite app_length. simpl.
      specialize (IHk Hvalid).
      lia.
    + rewrite app_length. simpl.
      specialize (IHk Hvalid).
      lia.
Qed.

(* 序列长度至少为k 且最多为2k *)
Lemma build_k_steps_length_bound : forall n k,
  valid_input n ->
  k <= length (build_k_steps n k) <= 2 * k.
Proof.
  induction k; intros Hvalid.
  - (* 基础情况: k = 0 *)
    simpl. split; lia.
    
  - (* 归纳步骤: k = S k' *)
    simpl build_k_steps.
    remember (sequence_end n (build_k_steps n k)) as curr_n.
    destruct (Nat.even curr_n).
    
    + (* 偶数情况: 添加R0 *)
      rewrite app_length. simpl.
      specialize (IHk Hvalid).
      split.
      * (* 下界: S k <= length *)
        lia.
      * (* 上界: length <= 2 * S k *)
        lia.
      
    + (* 奇数情况: 添加R1R0 *)
      rewrite app_length. simpl.
      specialize (IHk Hvalid).
      split.
      * (* 下界: S k <= length *)
        lia.
      * (* 上界: length <= 2 * S k *)
        lia.
Qed.


(* R0计数等于k *)
Lemma R0_count_eq_k : forall n k ops,
  valid_input n ->
  k >= 1 ->
  build_k_steps n k = ops ->
  let (r0s, _) := count_operations ops in
  r0s = k.
Proof.
  intros n k ops Hvalid Hk Heq.
  generalize dependent ops.
  induction k as [|k' IHk].

  - (* k = 0 *)
    intros ops Heq.
    lia.

  - (* k = S k' *)
    intros ops Heq.
    simpl build_k_steps in Heq.
    remember (sequence_end n (build_k_steps n k')) as curr_n.
    
    assert (Hvalid_curr : valid_input curr_n).
    { rewrite Heqcurr_n.
      apply sequence_end_valid with (ops := build_k_steps n k').
      - exact Hvalid.
      - apply build_k_steps_valid; auto. }
    
    destruct (Nat.even curr_n) eqn:Heven.
    
    + (* 偶数情况：添加R0 *)
      rewrite <- Heq.
      destruct k' as [|k''].
      
      * (* k' = 0 *)
        simpl.
        destruct (count_operations (build_k_steps n 0)) as [r0s_old r1s_old].
        destruct (count_operations (build_k_steps n 0 ++ [R0])) as [r0s_new r1s_new].
        simpl in *.
        reflexivity.
        
      * (* k' = S k'' *)
        destruct (count_operations (build_k_steps n (S k''))) as [r0s_old r1s_old].
        assert (H_prev: let (r0s, _) := count_operations (build_k_steps n (S k'')) in r0s = S k'').
        {
          apply IHk.
          - lia.
          - reflexivity.
        }
(* 先处理原始列表的计数 *)
destruct (count_operations (build_k_steps n (S k''))) as [r0s' r1s'] eqn:Heq_old.
(* 处理添加R0后的列表计数 *)
destruct (count_operations (build_k_steps n (S k'') ++ [R0])) as [r0s_new r1s_new] eqn:Heq_new.
   assert (r0s_new = S r0s').
    {
      (* 使用 count_operations_app_R0 引理 *)
      pose proof (count_operations_app_R0 (build_k_steps n (S k''))) as H_count.
      rewrite Heq_old in H_count.
      rewrite Heq_new in H_count.
      destruct H_count as [H_count _].  (* 只需要R0计数部分 *)
      rewrite Nat.add_1_r in H_count.   (* r0s + 1 = S r0s *)
      exact H_count.
    }
    rewrite H.
    rewrite H_prev.
    reflexivity.

     + (* 奇数情况：添加R1R0 *)
      rewrite <- Heq.
      destruct k' as [|k''].
      
      * (* k' = 0 *)
        simpl.
        destruct (count_operations (build_k_steps n 0)) as [r0s_old r1s_old].
        destruct (count_operations (build_k_steps n 0 ++ [R1; R0])) as [r0s_new r1s_new].
        simpl in *.
        reflexivity.
        
      * (* k' = S k'' *)
        destruct (count_operations (build_k_steps n (S k''))) as [r0s_old r1s_old].
        assert (H_prev: let (r0s, _) := count_operations (build_k_steps n (S k'')) in r0s = S k'').
        {
          apply IHk.
          - lia.
          - reflexivity.
        }
        (* 先处理原始列表的计数 *)
        destruct (count_operations (build_k_steps n (S k''))) as [r0s' r1s'] eqn:Heq_old.
        (* 处理添加R1R0后的列表计数 *)
        destruct (count_operations (build_k_steps n (S k'') ++ [R1; R0])) as [r0s_new r1s_new] eqn:Heq_new.
     assert (r0s_new = S r0s').
    {
      (* 使用 count_operations_app_R1R0 引理 *)
      pose proof (count_operations_app_R1R0 (build_k_steps n (S k''))) as H_count.
      rewrite Heq_old in H_count.
      rewrite Heq_new in H_count.
      destruct H_count as [H_count _].  (* 只需要R0计数部分 *)
      exact H_count.
    }
    rewrite H.
    rewrite H_prev.
    reflexivity.
Qed.




(* 主定理：证明在k步序列中，R0操作次数恰好为k，则R1操作次数不超过k，且总长度不超过2k。
   这表明R0操作（n/2）在序列中占主导地位，支持了序列最终会收敛的直觉。 *)
Theorem build_k_steps_structure : forall n k,
  valid_input n ->
  k >= 2 ->
  exists ops r0s r1s,
  build_k_steps n k = ops /\
  count_operations ops = (r0s, r1s) /\
  r0s = k /\           (* 加强：R0的数量精确等于k *)
  r1s <= k /\          (* R1的数量最多为k *)
  r1s = length ops - k (* 新增：R1的精确值 *) /\
  length ops <= 2 * k. (* 总长度最多为2k *)
Proof.
  intros n k Hvalid Hk.
  
  (* 使用R0_count_eq_k得到R0的精确值 *)
  assert (HR0: let (r0s, _) := count_operations (build_k_steps n k) in r0s = k).
  { apply (R0_count_eq_k n k (build_k_steps n k)).
    - exact Hvalid.
    - lia.
    - reflexivity. }
  
  (* 使用build_k_steps_length_bound得到长度上界 *)
  assert (Hlen: length (build_k_steps n k) <= 2 * k).
  { apply build_k_steps_length_bound. assumption. }
  
  (* 使用count_sum_c2得到R0s + R1s = length *)
  assert (Hsum: let (r0s, r1s) := count_operations (build_k_steps n k) in
               r0s + r1s = length (build_k_steps n k)).
  { apply count_sum_c2. }
  
  destruct (count_operations (build_k_steps n k)) as [r0s r1s] eqn:Hcount.
  exists (build_k_steps n k), r0s, r1s.
  
  split; [reflexivity|].
  split; [assumption|].
  split.
  - (* r0s = k *)
    rewrite HR0. reflexivity.
  - split.
    + (* r1s <= k *)
      assert (r0s + r1s <= 2 * k).
      { rewrite Hsum. assumption. }
      rewrite HR0 in H.
      lia.
    + split.
      * (* r1s = length ops - k *)
        rewrite <- Hsum.
        rewrite HR0.
        lia.
      * (* length <= 2 * k *)
        assumption.
Qed.




(* 动态性质的定理  所有合法k长度序列的结构证明了R0的增长是线性和可预测的
限制了R1的增长速率
支持了"R0操作在序列中占主导地位"的结论 *)

Theorem build_k_steps_increment_basic : forall n k,
  valid_input n ->
  k >= 2 ->
  let (r0s_k, r1s_k) := count_operations (build_k_steps n k) in
  let (r0s_next, r1s_next) := count_operations (build_k_steps n (S k)) in
  r0s_next = r0s_k + 1 /\                    (* R0精确增加1 *)
  r1s_next <= r1s_k + 1.                     (* R1最多增加1 *)
Proof.
  intros n k Hvalid Hk.
  
  (* 对k应用build_k_steps_structure *)
  destruct (build_k_steps_structure n k Hvalid Hk) 
    as [ops_k [r0s_k' [r1s_k' [Heq_k [Hcount_k [Hr0s_k [Hr1s_k _]]]]]]].
  
  (* 获取build_k_steps_Sn的等式并简化 *)
  pose proof (build_k_steps_Sn n k Hvalid) as H_build.
  rewrite Heq_k in H_build.
  
  (* 解构当前的count_operations *)
  destruct (count_operations (build_k_steps n k)) as [r0s_k r1s_k] eqn:Hcount1.
  destruct (count_operations (build_k_steps n (S k))) as [r0s_next r1s_next] eqn:Hcount2.
  
  (* 分情况讨论sequence_end n ops_k是偶数还是奇数 *)
  destruct (Nat.even (sequence_end n ops_k)) eqn:E.
  
  - (* 偶数情况：添加[R0] *)
    split.
    + (* r0s_next = r0s_k + 1 *)
      (* 建立等式链 *)
      assert (H_chain: exists r0s_new r1s_new,
        count_operations (ops_k ++ [R0]) = (r0s_new, r1s_new) /\
        r0s_new = r0s_k + 1).
      {
        destruct (count_operations ops_k) as [r0s_old r1s_old] eqn:Hold.
        exists (r0s_old + 1), r1s_old.
        pose proof (count_operations_app_R0 ops_k) as H_count.
        rewrite Hold in H_count.
        rewrite Heq_k in Hcount1.
        rewrite Hold in Hcount1.
        injection Hcount1 as Hr0s_eq Hr1s_eq.
        split.

- (* 证明count_operations (ops_k ++ [R0]) = (r0s_old + 1, r1s_old) *)
  destruct (count_operations (ops_k ++ [R0])) eqn:Hnew.
  destruct H_count as [H_r0' H_r1'].
  f_equal; auto.
        - (* 证明r0s_old + 1 = r0s_k + 1 *)
          rewrite Hr0s_eq.
          reflexivity.
      }
      
      (* 使用等式链完成证明 *)
      destruct H_chain as [r0s_new [r1s_new [H_new H_eq]]].
      rewrite H_build in Hcount2.
      simpl in Hcount2.
      rewrite E in Hcount2.
      rewrite H_new in Hcount2.
      injection Hcount2 as H_next _.
      rewrite <- H_next.
      exact H_eq.
      
    + (* r1s_next <= r1s_k + 1 *)
      destruct (count_operations ops_k) as [r0s_old r1s_old] eqn:Hold.
      rewrite Heq_k in Hcount1.
      rewrite Hold in Hcount1.
      injection Hcount1 as Hr0s_eq Hr1s_eq.
      rewrite H_build in Hcount2.
      simpl in Hcount2.
      rewrite E in Hcount2.
      pose proof (count_operations_app_R0 ops_k) as H_count.
      rewrite Hold in H_count.
      destruct (count_operations (ops_k ++ [R0])) eqn:Hnew.
      destruct H_count as [_ H_r1].
      injection Hcount2 as _ H_r1_next.
      rewrite <- H_r1_next.
      rewrite <- Hr1s_eq.
      rewrite H_r1.
      lia.

  - (* 奇数情况：添加[R1;R0] *)
    split.
    + (* r0s_next = r0s_k + 1 *)
      assert (H_chain: exists r0s_new r1s_new,
        count_operations (ops_k ++ [R1; R0]) = (r0s_new, r1s_new) /\
        r0s_new = r0s_k + 1).
      {
        destruct (count_operations ops_k) as [r0s_old r1s_old] eqn:Hold.
        exists (S r0s_old), (S r1s_old).
        pose proof (count_operations_app_R1R0 ops_k) as H_count.
        rewrite Hold in H_count.
        rewrite Heq_k in Hcount1.
        rewrite Hold in Hcount1.
        injection Hcount1 as Hr0s_eq Hr1s_eq.
        split.
        - (* 证明count_operations (ops_k ++ [R1; R0]) = (S r0s_old, S r1s_old) *)
          destruct (count_operations (ops_k ++ [R1; R0])) eqn:Hnew.
          destruct H_count as [H_r0' H_r1'].
          f_equal.
          + (* 证明 n0 = S r0s_old *)
            exact H_r0'.
          + (* 证明 n1 = S r1s_old *)
            exact H_r1'.
        - (* 证明S r0s_old = r0s_k + 1 *)
          rewrite Hr0s_eq.
          lia.
      }
      
      (* 使用等式链完成证明 *)
      destruct H_chain as [r0s_new [r1s_new [H_new H_eq]]].
      rewrite H_build in Hcount2.
      simpl in Hcount2.
      rewrite E in Hcount2.
      rewrite H_new in Hcount2.
      injection Hcount2 as H_next _.
      rewrite <- H_next.
      exact H_eq.
      
    + (* r1s_next <= r1s_k + 1 *)
      destruct (count_operations ops_k) as [r0s_old r1s_old] eqn:Hold.
      rewrite Heq_k in Hcount1.
      rewrite Hold in Hcount1.
      injection Hcount1 as Hr0s_eq Hr1s_eq.
      rewrite H_build in Hcount2.
      simpl in Hcount2.
      rewrite E in Hcount2.
      pose proof (count_operations_app_R1R0 ops_k) as H_count.
      rewrite Hold in H_count.
      destruct (count_operations (ops_k ++ [R1; R0])) eqn:Hnew.
      destruct H_count as [_ H_r1].
      injection Hcount2 as _ H_r1_next.
      rewrite <- H_r1_next.
      rewrite <- Hr1s_eq.
      rewrite H_r1.
      lia.
Qed.


(* 3. R0操作数单调递增 *)
Lemma build_k_steps_R0_monotone : forall n k1 k2,
  valid_input n -> 
  k2 > k1 -> 
  k1 >= 2 ->  (* 添加这个条件，与主定理保持一致 *)
  let (r0s1, _) := count_operations (build_k_steps n k1) in
  let (r0s2, _) := count_operations (build_k_steps n k2) in
  r0s2 > r0s1.
Proof.
  intros n k1 k2 Hvalid Hk12 Hk1_ge_2.
  
  (* 1. 现在我们可以得到k1, k2 >= 2 *)
  assert (Hk2: k2 >= 2) by lia.
  
  (* 2. 获取k1和k2对应的序列性质 *)
  destruct (count_operations (build_k_steps n k1)) as [r0s1 r1s1] eqn:Heq1.
  destruct (count_operations (build_k_steps n k2)) as [r0s2 r1s2] eqn:Heq2.
  
  (* 3. 使用build_k_steps_structure *)
  assert (Hstr1 := build_k_steps_structure n k1 Hvalid Hk1_ge_2).
  assert (Hstr2 := build_k_steps_structure n k2 Hvalid Hk2).
  
  (* 4. 解构structure的结果 *)
  destruct Hstr1 as [ops1 [r0s1' [r1s1' [Heq1' [Hcount1' [Hr0s1' [Hr1s1' [Hr1s1_len' Hlen1']]]]]]]].
  destruct Hstr2 as [ops2 [r0s2' [r1s2' [Heq2' [Hcount2' [Hr0s2' [Hr1s2' [Hr1s2_len' Hlen2']]]]]]]].
  
  (* 5. 建立等价关系 *)
  rewrite Heq1' in Heq1. rewrite Hcount1' in Heq1.
  rewrite Heq2' in Heq2. rewrite Hcount2' in Heq2.
  injection Heq1 as Hr0s1_eq Hr1s1_eq.
  injection Heq2 as Hr0s2_eq Hr1s2_eq.
  subst r0s1' r1s1' r0s2' r1s2'.
  
  (* 6. 重写目标 *)
  rewrite Hr0s1', Hr0s2'.  (* r0s1 = k1, r0s2 = k2 *)
  
  (* 7. 目标简化为 k2 > k1，这正是我们的假设 *)
  exact Hk12.
Qed.

(* 2. R1操作数增长有界 *)
Lemma build_k_steps_R1_bounded : forall n k,
  valid_input n ->
  k >= 2 ->  (* 保持与主定理条件一致 *)
  let (r0s, r1s) := count_operations (build_k_steps n k) in
  r1s <= r0s.
Proof.
  intros n k Hvalid Hk_ge_2.
  
  (* 1. 获取序列的操作计数 *)
  destruct (count_operations (build_k_steps n k)) as [r0s r1s] eqn:Heq.
  
  (* 2. 使用build_k_steps_structure *)
  assert (Hstr := build_k_steps_structure n k Hvalid Hk_ge_2).
  destruct Hstr as [ops [r0s' [r1s' [Heq' [Hcount' [Hr0s' [Hr1s' [Hr1s_len' Hlen']]]]]]]].
  
  (* 3. 建立等价关系 *)
  rewrite Heq' in Heq.
  rewrite Hcount' in Heq.
  injection Heq as Hr0s_eq Hr1s_eq.
  subst r0s' r1s'.
  
  (* 4. 重写目标 *)
  rewrite Hr0s'.  (* r0s = k *)
  rewrite Hr1s_len'.  (* r1s = length ops - k *)
  
  (* 5. 使用序列长度的上界 *)
  assert (H: length ops - k <= k).
  {
    apply (Nat.le_trans _ (2 * k - k)).
    - apply Nat.sub_le_mono_r.
      exact Hlen'.
    - assert (H_aux: 2 * k - k = k) by lia.
      rewrite H_aux.
      apply Nat.le_refl.
  }
  exact H.
Qed.

