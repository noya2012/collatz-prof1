Require Import Nat.
Require Import Lia.
Load "collatz_part_one.v".  (* 使用 Load 而不是 Require Import *)
(* noya2012@126.com 306000250@qq.com  zeng  *)
(* 入口函数定义 *)
Definition valid_R0R1_entry_number (d n: nat) : nat :=
  (2 * (2^d) * n) + (2^d - 2).

(* R0R1操作的定义 *)
Definition apply_R0R1 (n: nat) : nat :=
  let n' := collatz_step n in      (* 先执行R0 *)
  collatz_step n'.                 (* 再执行R1 *)

(* 执行d次R0R1操作 *)
Fixpoint apply_d_R0R1 (n: nat) (d: nat) : nat :=
  match d with
  | 0 => n
  | S d' => apply_d_R0R1 (apply_R0R1 n) d'
  end.

(* 已证明的定理 *)
Theorem valid_n2 : forall d n,
  d >= 1 ->
  n >= 1 ->
  valid_input (valid_R0R1_entry_number d n).
Proof.
  intros d n Hd Hn.
  unfold valid_input, valid_R0R1_entry_number.
  assert (H2d: 2^d >= 2) by (apply pow2_ge_2; exact Hd).
  assert (Hpos: 2^d > 0) by apply gt_0_2_pow.
  (* 分解证明步骤 *)
  assert (H1: n >= 1) by exact Hn.
  assert (H2: 2 * n >= 2) by lia.
  assert (H3: 2 * 2^d * n >= 2^d * 2).
  { 
    replace (2 * 2^d * n) with (2^d * (2 * n)) by lia.
    assert (2 * n >= 2) by lia.
    nia.
  }
  nia.
Qed.

(* 证明输出能被2整除 *)
Theorem valid_n2_div2 : forall d n,
  d >= 1 ->
  exists k, valid_R0R1_entry_number d n = 2 * k.
Proof.
  intros d n Hd.
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

