/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakCall
public import LeanPool.OrderMaintenance.Impl.Memory
public import LeanPool.OrderMaintenance.Proof.Word.PeakIns
public import LeanPool.OrderMaintenance.Proof.Word.Wrap


/-!
# Theorem W, option (A), stage A3: tools for the machine-only code

* **Peak-only rules.** The machine-only proofs bound the peak of a piece of code with the
  postcondition `TT` (nothing but the budget): `wpB B c TT m`. The state facts the next piece
  needs come from the existing `wp` theorems (`WrapM`, `RebuildM`, `OpsM`, …), combined by
  `wpB_and` / `wpB_seq_of`; their statements are unchanged. `dpk_le_of` turns a budget proof from
  the state with the peak reset into a bound on `dpk`.
* **The budget** of one operation at word size `K` with handle width `KH`:
  `BW K KH = 2^(2K+4) + 2^KH`; a core procedure's peak `< 2^(wPk K KH)` is within it (`pk_BW`).
* **The capacities of the proof parameters are small**: `CapsW (wK P) (capsOf P)` for
  `P = proofParams N` (`capsW_wK`), from `memOf_eq` / `core_mem` (and a direct bound for `N < 64`);
  monotone in `K` (`CapsW.mono`).
* **A core ready for a call** at word size `K` (`CoreK`): proof parameters, `wK ≤ K`, `WB K`,
  handles below `2^KH`; it gives the hypotheses of the five A2 wrappers.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
  OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp wpB dpk)

/-! ### Peak-only rules -/

/-- The postcondition of a peak-only proof. -/
abbrev TT : State → Nat → Prop := fun _ _ => True

theorem wpB_and {B : Nat} {c : Stmt} {Q : State → Nat → Prop} {s : State} (h : wp c Q s)
    (hp : wpB B c TT s) : wpB B c Q s := by
  unfold wpB wp Machine.Out.Ok at *
  exact ⟨h.1, hp.2.1, h.2⟩

theorem wpB_T {B : Nat} {c : Stmt} {Q : State → Nat → Prop} {s : State} (h : wpB B c Q s) : wpB
  B c TT s :=
  Machine.wpB_mono le_rfl (fun _ _ _ => trivial) h

/-- A sequence whose first part's state facts come from a `wp` theorem. -/
theorem wpB_seq_of {B : Nat} {c d : Stmt} {Qc : State → Nat → Prop} {s : State} (hc : wp c Qc s)
    (hpc : wpB B c TT s) (hd : ∀ s' n, Qc s' n → wpB B d TT s') : wpB B (.seq c d) TT s :=
  Machine.wpB_seq (Machine.wpB_mono le_rfl (fun s' n hq => wpB_T (hd s' n hq)) (wpB_and hc hpc))

/-- A sequence, both parts by budget proofs. -/
theorem wpB_seq_T {B : Nat} {c d : Stmt} {Qc : State → Nat → Prop} {s : State} (hc : wpB B c Qc s)
    (hd : ∀ s' n, Qc s' n → wpB B d TT s') : wpB B (.seq c d) TT s :=
  Machine.wpB_seq (Machine.wpB_mono le_rfl (fun s' n hq => wpB_T (hd s' n hq)) hc)

theorem wpB_assign_seq {B : Nat} {x : Reg} {e : Expr} {d : Stmt} {s : State} (v : Nat)
    (he : e.eval s = some v) (hB : e.maxv s ≤ B)
    (h : ∀ s', s'.loc = State.upd s.loc x v → s'.mem = s.mem → s'.cap = s.cap → wpB B d TT s') :
    wpB B (.seq (.assign x e) d) TT s :=
  wpB_seq_T (Machine.wpB_assign_g (Q := fun s' _ => wpB B d TT s') v he hB (fun s' a b c => h s'
    a b c))
    (fun _ _ h => h)

theorem wpB_store_seq {B : Nat} {a : Arr} {i e : Expr} {d : Stmt} {s : State} (j v : Nat)
    (hi : i.eval s = some j) (he : e.eval s = some v) (hj : j < s.cap a) (hBi : i.maxv s ≤ B)
    (hBe : e.maxv s ≤ B)
    (h : ∀ s', s'.loc = s.loc → s'.mem = (s.write a j v).mem → s'.cap = s.cap → wpB B d TT s') :
    wpB B (.seq (.store a i e) d) TT s :=
  wpB_seq_T (Machine.wpB_store_g (Q := fun s' _ => wpB B d TT s') j v hi he hj hBi hBe
    (fun s' a b c => h s' a b c)) (fun _ _ h => h)

theorem wpB_ite_T {B : Nat} {c : Expr} {t f : Stmt} {s : State} (v : Nat) (hc : c.eval s = some v)
    (hB : c.maxv s ≤ B)
    (h : ∀ s', s'.loc = s.loc → s'.mem = s.mem → s'.cap = s.cap → wpB B (if v ≠ 0 then t else f)
      TT s') :
    wpB B (.ite c t f) TT s :=
  Machine.wpB_ite v hc hB (wpB_T (h _ rfl rfl rfl))

theorem wpB_skip_T {B : Nat} {s : State} : wpB B .skip TT s := Machine.wpB_skip trivial

/-- A sequence with a postcondition, the first part's state facts from a `wp` theorem. -/
theorem wpB_seq_ofQ {B : Nat} {c d : Stmt} {Qc Q : State → Nat → Prop} {s : State} (hc : wp c Qc s)
    (hpc : wpB B c TT s) (hd : ∀ s' n, Qc s' n → wpB B d (fun s'' m => Q s'' (n + m)) s') :
    wpB B (.seq c d) Q s :=
  Machine.wpB_seq (Machine.wpB_mono le_rfl (fun s' n hq => hd s' n hq) (wpB_and hc hpc))

/-- A conditional with a postcondition, forgetting the bumped state. -/
theorem wpB_ite_Q {B : Nat} {c : Expr} {t f : Stmt} {Q : State → Nat → Prop} {s : State} (v : Nat)
    (hc : c.eval s = some v) (hB : c.maxv s ≤ B)
    (h : ∀ s', s'.loc = s.loc → s'.mem = s.mem → s'.cap = s.cap →
      wpB B (if v ≠ 0 then t else f) (fun s'' n => Q s'' (1 + c.cost + n)) s') :
    wpB B (.ite c t f) Q s :=
  Machine.wpB_ite v hc hB (h _ rfl rfl rfl)

/-- Two facts about the same run. -/
theorem wpB_and2 {B : Nat} {c : Stmt} {Q R : State → Nat → Prop} {s : State} (h : wp c Q s)
    (hp : wpB B c R s) : wpB B c (fun s' n => Q s' n ∧ R s' n) s := by
  unfold wpB wp Machine.Out.Ok at *
  exact ⟨h.1, hp.2.1, h.2, hp.2.2⟩

/-- A value is at most the peak of its expression. -/
theorem eval_le_maxv {s : State} : ∀ {e : Expr} {v : Nat}, e.eval s = some v → v ≤ e.maxv s
  | .lit _, v, h => by simp [Expr.eval] at h; simp [h]
  | .var _, v, h => by simp [Expr.eval] at h; simp [h]
  | .load _ _, v, h => by
    simp only [Expr.maxv]; rw [h]; simp
  | .bin _ _ _, v, h => by
    simp only [Expr.maxv]; rw [h]; simp
  | .un _ _, v, h => by
    simp only [Expr.maxv]; rw [h]; simp

/-- Truncated subtraction introduces no peak above its operands and the Boolean value one. -/
theorem tsubE_maxv_le {s : State} {a b : Expr} {B : Nat}
    (ha : a.maxv s ≤ B) (hb : b.maxv s ≤ B) (hB : 1 ≤ B) :
    (tsubE a b).maxv s ≤ B := by
  cases hae : a.eval s with
  | none =>
    cases hbe : b.eval s <;>
      simp [tsubE, Expr.maxv, Expr.eval, hae, hbe, ha, hb]
  | some x =>
    cases hbe : b.eval s with
    | none => simp [tsubE, Expr.maxv, Expr.eval, hae, hbe, ha, hb]
    | some y =>
      have hx := (eval_le_maxv hae).trans ha
      have hy := (eval_le_maxv hbe).trans hb
      have hxy : x ≤ B + y := Nat.le_add_right_of_le hx
      by_cases h : y ≤ x <;>
        simp [tsubE, Expr.maxv, Expr.eval, BinOp.eval, hae, hbe, h, ha, hb, hx, hy, hB, hxy]

/-- Addition bounds every intermediate value by the sum of the operand peak bounds. -/
theorem addE_maxv_le {s : State} {a b : Expr} {A B : Nat}
    (ha : a.maxv s ≤ A) (hb : b.maxv s ≤ B) :
    (Expr.bin .add a b).maxv s ≤ A + B := by
  cases hx : a.eval s with
  | none =>
    simp only [Expr.maxv, Expr.eval, hx, Option.bind_none, Option.getD_none, sup_le_iff]
    omega
  | some x =>
    cases hy : b.eval s with
    | none =>
      simp only [Expr.maxv, Expr.eval, hx, hy, Option.bind_some, Option.bind_none,
        Option.getD_none, sup_le_iff]
      omega
    | some y =>
      have hx' := (eval_le_maxv hx).trans ha
      have hy' := (eval_le_maxv hy).trans hb
      simp only [Expr.maxv, Expr.eval, hx, hy, BinOp.eval, Option.bind_some,
        Option.getD_some, sup_le_iff]
      omega

/-- Equality comparison adds only a Boolean value to the operand peak bounds. -/
theorem eqE_maxv_le {s : State} {a b : Expr} {B : Nat}
    (ha : a.maxv s ≤ B) (hb : b.maxv s ≤ B) (hB : 1 ≤ B) :
    (Expr.bin .eq a b).maxv s ≤ B := by
  cases hx : a.eval s with
  | none =>
    cases hy : b.eval s <;> simp [Expr.maxv, Expr.eval, hx, hy, ha, hb]
  | some x =>
    cases hy : b.eval s with
    | none => simp [Expr.maxv, Expr.eval, hx, hy, ha, hb]
    | some y =>
      simp only [Expr.maxv, Expr.eval, hx, hy, BinOp.eval, Option.bind_some,
        Option.getD_some, sup_le_iff]
      refine ⟨⟨ha, hb⟩, ?_⟩
      split <;> omega

/-- **From a budget proof at the reset state to `dpk`.** -/
theorem dpk_le_of {B : Nat} {c : Stmt} {m : State} (h : wpB B c TT {
  m with
  peak := 0
}) : dpk c
  m ≤ B := by
  have := h.peak_le
  simp only [Nat.zero_max] at this
  exact this

/-! ### The budget -/

/-- **The budget of one operation**: `2^(2K+4) + 2^KH`. -/
abbrev BW (K KH : Nat) : Nat := 2 ^ (2 * K + 4) + 2 ^ KH

/-- Every word budget contains a positive power of two. -/
theorem one_le_BW (K KH : Nat) : 1 ≤ BW K KH :=
  Nat.one_le_two_pow.trans (Nat.le_add_right (2 ^ (2 * K + 4)) (2 ^ KH))

theorem pk_BW {K KH x : Nat} (h : x < 2 ^ wPk K KH) : x ≤ BW K KH := le_of_lt (lt_pow_max_add h)

theorem pow_BW (K : Nat) : 16 * 2 ^ K ≤ 2 ^ (2 * K + 4) := by
  have : 2 ^ (2 * K + 4) = 16 * 2 ^ K * 2 ^ K := by
    rw [show 2 * K + 4 = K + K + 4 by omega, pow_add, pow_add]
    ring
  rw [this]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos K)

theorem lt_K_BW {K KH x : Nat} (h : x < 2 ^ K) : x ≤ BW K KH := by
  have := pow_BW K; have := Nat.two_pow_pos KH; unfold BW; omega

/-- Close a word-budget inequality using positivity and the square-width power bound. -/
macro "proveBudget" K:ident KH:ident : tactic =>
  `(tactic| (
    have := Nat.two_pow_pos $KH
    have := Nat.two_pow_pos (2 * $K + 4)
    have := Nat.two_pow_pos $K
    have := pow_BW $K
    try unfold BW
    omega))

/-! ### The capacities of the proof parameters -/

theorem CapsW.mono {K K' : Nat} {κ : Caps} (h : CapsW K κ) (hK : K ≤ K') : CapsW K' κ :=
  ⟨fun k => lt_pow_mono (h.lst k) hK, fun k => lt_pow_mono (h.lcap k) hK, lt_pow_mono h.path hK,
    le_trans h.sixteen (Nat.pow_le_pow_right (by norm_num) hK), fun t => lt_pow_mono (h.tbl t) hK,
    lt_pow_mono h.pw hK, fun k => lt_pow_mono (h.arr k) hK, fun k => lt_pow_mono (h.lcap2 k) hK⟩

theorem size_lt_64 {N : Nat} (h : N < 64) : Nat.size N ≤ 6 := Nat.size_le.mpr (by simpa using h)

/-- The cells of a core of the proof parameters, for `N < 64` (`L = 8`). -/
theorem memOf_small {N : Nat} (h : N < 64) : memOf (capsOf (proofParams N)) ≤ 1000000 := by
  have hL : pL N = 8 := by unfold pL; have := size_lt_64 h; omega
  rw [memOf_eq, nbMax_proof, cb_proof]
  simp only [pp_N, pp_H, hL]
  have hd : vth 8 + 1 - vcm 8 = 17 := by decide
  have hH : vH 8 = 3 := by decide
  have hcb : vcb N 8 ≤ 8 := by
    unfold vcb; rw [hd]
    have : N / 17 ≤ 3 := by omega
    omega
  have hnb : vnb N 8 = 5 + 41 * vcb N 8 := by unfold vnb; rw [hH]
  rw [hnb, hH]
  omega

/-- **The cells of a core of the proof parameters are below `2^(wK P)`.** -/
theorem memOf_lt_wK (N : Nat) : memOf (capsOf (proofParams N)) < 2 ^ wK (proofParams N) := by
  have hK : wK (proofParams N) = 64 * pL N := rfl
  have h8 := pL_ge N
  rcases Nat.lt_or_ge N 64 with h | h
  · refine lt_of_le_of_lt (memOf_small h) (lt_of_lt_of_le (show 1000000 < 2 ^ 20 by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (show 20 ≤ wK (proofParams N) by rw [hK]; omega)))
  · have hm := core_mem h
    have hN : N < 2 ^ pL N := lt_of_lt_of_le (Nat.lt_size_self N) (Nat.pow_le_pow_right (by
      norm_num) (le_max_right _ _))
    have h1 : 40000 * N < 2 ^ (16 + pL N) := by
      rw [pow_add]; have : (40000 : Nat) < 2 ^ 16 := by norm_num
      exact Nat.mul_lt_mul'' this hN
    exact lt_of_le_of_lt hm (lt_pow_mono h1 (by
      rw [hK]
      omega))

/-- **The capacities of the proof parameters are below `2^(wK P)`**, the index arithmetic of the
compiled code included. -/
theorem capsW_wK (N : Nat) : CapsW (wK (proofParams N)) (capsOf (proofParams N)) := by
  have hM := memOf_lt_wK N
  rw [memOf_eq] at hM
  set P := proofParams N
  have h16 : 16 ≤ 2 ^ wK P := by
    have : 4 ≤ wK P := by change 4 ≤ 64 * pL N; have := pL_ge N; omega
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) this)
  have hch : (cb P + 2) * (P.H + 1) = cb P * P.H + cb P + 2 * P.H + 2 := by ring
  refine ⟨fun k => ?_, fun k => ?_, ?_, h16, fun t => ?_, ?_, fun k => ?_, fun k => ?_⟩
  · cases k <;> simp only [capsOf] <;> omega
  · cases k <;> simp only [capsOf] <;> omega
  · simp only [capsOf]; rw [hch]; omega
  · cases t <;> simp only [capsOf] <;> omega
  · simp only [capsOf]; omega
  · cases k <;> simp only [capsOf] <;> omega
  · cases k <;> simp only [capsOf] <;> omega

theorem capsW_at {K : Nat} {P : Params} (hP : P = proofParams P.N) (hK : wK P ≤ K) : CapsW K
  (capsOf P) := by
  rw [hP] at hK ⊢; exact (capsW_wK _).mono hK

theorem proom_at {K : Nat} {P : Params} (hP : P = proofParams P.N) (hK : wK P ≤ K) : PRoom K P := by
  rw [hP] at hK ⊢; exact (proom_wK _).mono hK

theorem wK_ge512 {P : Params} (hP : P = proofParams P.N) : 512 ≤ wK P := by
  rw [hP]; exact wK_ge _

/-! ### A core ready for a call -/

/-- **A core ready for a call** at word size `K`, handle width `KH`. -/
structure CoreK (K KH : Nat) (c : Core) : Prop where
  pmk : c.P = proofParams c.P.N
  wk : wK c.P ≤ K
  wb : WB K c
  hh : ∀ i, (c.E.getX i).h < 2 ^ KH

theorem CoreK.caps {K KH : Nat} {c : Core} (h : CoreK K KH c) : CapsW K (capsOf c.P) := capsW_at
  h.pmk h.wk
theorem CoreK.room {K KH : Nat} {c : Core} (h : CoreK K KH c) : PRoom K c.P := proom_at h.pmk h.wk
theorem CoreK.k8 {K KH : Nat} {c : Core} (h : CoreK K KH c) : 512 ≤ K := le_trans (wK_ge512
  h.pmk) h.wk

end OrderMaintenance.Impl
