/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.TopParams
public import LeanPool.OrderMaintenance.Proof.Top.PrepContract
public import Mathlib.NumberTheory.Harmonic.Bounds
public import LeanPool.OrderMaintenance.Proof.Cost.Params
public import LeanPool.OrderMaintenance.Proof.Cost.Wrap


/-!
# M5: the cost proof's assumptions for the proof parameters (`CostSetup`)

The game has `n_f = 1 + 2⌊N/(θ + 1 − c_max)⌋` counters and runs rounds of length
`R_f = ⌊J/reservationBudget⌋ + 1`, where `J = 13H + 2` bounds a top-structure job.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Zeroing

/-- The game's counter count. -/
def nfP (P : Params) : Nat := 1 + 2 * (P.N / (P.theta + 1 - cmax P))

/-- The game's round length. -/
def RfP (P : Params) : Nat := topJ P / P.reservationBudget + 1

/-- The chunks have room: `θ + 1 − c_max ≥ 8`. -/
theorem d_ge (N : Nat) : 8 ≤ (proofParams N).theta + 1 - cmax (proofParams N) := by
  have hL := pL_ge N
  simp only [cmax, kC, unitsOf, umax, kG, gmin, proofParams]
  generalize pL N = L at hL
  have hg : (2 * L - 2) / 2 = L - 1 := by omega
  rw [hg]
  have hM : 8 * L ≤ L * L := Nat.mul_le_mul_right L hL
  have hq : 3 * L * L / (L - 1) ≤ 3 * L + 4 := by
    apply Nat.div_le_of_le_mul
    have : (L - 1) * (3 * L + 4) = 3 * (L * L) + L - 4 := by
      cases L with
      | zero => omega
      | succ k => simp only [Nat.add_sub_cancel]; ring_nf; omega
    rw [this]; ring_nf; omega
  generalize 3 * L * L / (L - 1) = q at hq
  generalize hMM : L * L = M at hM
  have h3 : 3 * L * L = 3 * M := by rw [← hMM]; ring
  have h2 : 2 * L * L = 2 * M := by rw [← hMM]; ring
  rw [h3, h2]
  omega

theorem N_lt (N : Nat) : N < 2 ^ pL N :=
  lt_of_lt_of_le (Nat.lt_size_self N) (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

theorem H_eq (N : Nat) : (proofParams N).H = pL N / 3 + 1 := rfl

theorem topJ_eq (P : Params) (hs : P.s = 11) : topJ P = 13 * P.H + 2 := by
  unfold topJ walkLeft; rw [hs]; omega

/-- `R_f ≤ L`. -/
theorem Rf_le (N : Nat) : RfP (proofParams N) ≤ pL N := by
  have hL := pL_ge N
  unfold RfP; rw [topJ_eq _ rfl, H_eq]
  change (13 * (pL N / 3 + 1) + 2) / 8 + 1 ≤ pL N
  omega

/-- The game's counters, beyond the first, are fewer than `2^(L-2)`. -/
theorem nf_lt (N : Nat) : nfP (proofParams N) - 1 < 2 ^ (pL N - 2) := by
  have hL := pL_ge N
  have hd := d_ge N
  have hN := N_lt N
  unfold nfP
  rw [show (proofParams N).N = N from rfl]
  have h8 : N / ((proofParams N).theta + 1 - cmax (proofParams N)) ≤ N / 8 :=
    Nat.div_le_div_left hd (by norm_num)
  have hp : 2 ^ pL N = 4 * 2 ^ (pL N - 2) := by
    rw [show pL N = (pL N - 2) + 2 by omega, pow_add]; simp; ring
  generalize N / ((proofParams N).theta + 1 - cmax (proofParams N)) = q at h8
  rw [hp] at hN
  omega

/-- `H_m + 1 ≤ L` for the game's counters. -/
theorem Hn_le (N : Nat) : Hn (nfP (proofParams N) - 1) + 1 ≤ (pL N : ℝ) := by
  have hL := pL_ge N
  have hm := nf_lt N
  generalize nfP (proofParams N) - 1 = m at hm
  have h1 : Hn m ≤ 1 + Real.log m := harmonic_le_one_add_log m
  have h2 : Real.log m ≤ (pL N : ℝ) - 2 := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp; have : (8 : ℝ) ≤ pL N := by exact_mod_cast hL
      linarith
    · have hmr : (m : ℝ) ≤ (2 : ℝ) ^ (pL N - 2) := by exact_mod_cast hm.le
      have hl := Real.log_le_log (by exact_mod_cast hpos) hmr
      rw [Real.log_pow] at hl
      have h2 : Real.log 2 < 1 := by
        have hlog := Real.log_lt_sub_one_of_pos
          (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
        norm_num at hlog
        exact hlog
      have hc : ((pL N - 2 : ℕ) : ℝ) = (pL N : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [hc] at hl
      have hpos' : (0 : ℝ) ≤ (pL N : ℝ) - 2 := by
        have : (8 : ℝ) ≤ pL N := by exact_mod_cast hL
        linarith
      nlinarith
  linarith

/-- **I5** for the proof parameters. -/
theorem I5_proof (N : Nat) : ((proofParams N).theta : ℝ) +
    RfP (proofParams N) * (Hn (nfP (proofParams N) - 1) + 1) ≤ (proofParams N).T := by
  have hH := Hn_le N
  have hR : (RfP (proofParams N) : ℝ) ≤ pL N := by exact_mod_cast Rf_le N
  have hθ : ((proofParams N).theta : ℝ) = 2 * (pL N : ℝ) * pL N := by
    change ((2 * pL N * pL N : ℕ) : ℝ) = _; push_cast; ring
  have hT : ((proofParams N).T : ℝ) = 3 * (pL N : ℝ) * pL N := by
    change ((3 * pL N * pL N : ℕ) : ℝ) = _; push_cast; ring
  rw [hθ, hT]
  have hHn : 0 ≤ Hn (nfP (proofParams N) - 1) := by
    have := Hn_mono (Nat.zero_le (nfP (proofParams N) - 1)); simpa [Hn] using this
  have hR0 : (0 : ℝ) ≤ RfP (proofParams N) := Nat.cast_nonneg _
  have : (RfP (proofParams N) : ℝ) * (Hn (nfP (proofParams N) - 1) + 1) ≤ (pL N : ℝ) * pL N :=
    mul_le_mul hR hH (by linarith) (by linarith)
  linarith

/-- The tree holds the chunks. -/
theorem capc_proof (N : Nat) : 2 + 2 * (N / ((proofParams N).theta + 1 - cmax (proofParams N))) ≤
    capT (proofParams N) := by
  have hL := pL_ge N
  have hm := nf_lt N
  unfold nfP at hm
  rw [show (proofParams N).N = N from rfl] at hm
  unfold capT
  rw [Wd_eq (P := proofParams N) rfl _, H_eq, Nat.add_sub_cancel]
  have h8 : 2 ^ (pL N - 2) ≤ 8 ^ (pL N / 3) := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 ≤ 2 ^ (pL N - 2) := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (pL N - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize N / ((proofParams N).theta + 1 - cmax (proofParams N)) = q at hm ⊢
  omega

/-- The preparation budget: `H(N') + 1 ≤ L(N) + 2` for `N' ≤ 4N`. -/
theorem prepB_proof (N N' : Nat) (h : N' ≤ 4 * N) : (proofParams N').H + 1 ≤ (proofParams N).L +
  2 := by
  rw [H_eq]
  change pL N' / 3 + 1 + 1 ≤ pL N + 2
  have hs : Nat.size N' ≤ Nat.size N + 2 := by
    rw [Nat.size_le]
    have := Nat.lt_size_self N
    rw [pow_add]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have hz : N' = 0 := by omega
      subst hz
      positivity
    · have : 4 * N < 4 * 2 ^ Nat.size N := by omega
      calc N' ≤ 4 * N := h
        _ < 2 ^ Nat.size N * 2 ^ 2 := by rw [Nat.mul_comm]; simpa using this
  unfold pL
  omega

theorem pow_ge_add (m : Nat) (hm : 7 ≤ m) : m + 6 ≤ 2 ^ (m - 2) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [show m + 1 - 2 = (m - 2) + 1 by omega, pow_succ]; omega

/-- Small capacities: `L + 6 ≤ N/2` for `N ≥ 64`. -/
theorem small_proof (N : Nat) (h : 64 ≤ N) : (proofParams N).L + 6 ≤ N / 2 := by
  change pL N + 6 ≤ N / 2
  unfold pL
  have hs : 7 ≤ Nat.size N := Nat.lt_size.mpr (by omega)
  have hle : 2 ^ (Nat.size N - 1) ≤ N := Nat.lt_size.mp (by omega)
  have hp := pow_ge_add _ hs
  have : 2 ^ (Nat.size N - 1) = 2 * 2 ^ (Nat.size N - 2) := by
    rw [show Nat.size N - 1 = (Nat.size N - 2) + 1 by omega, pow_succ]; ring
  omega

/-- **The core's correctness conditions** for the proof parameters. -/
theorem core_proof (N : Nat) : CoreP (proofParams N) := by
  have hL := pL_ge N
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold fbGS
    simp only [proofParams, Nat.shiftLeft_eq, one_mul]
    generalize pL N = L at hL
    exact lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  · unfold fbGPC fbGS
    simp only [proofParams, Nat.shiftLeft_eq, one_mul]
    generalize pL N = L at hL
    have h1 : 3 * L * L / 2 / max 1 (2 * L / 2) ≤ 3 * L * L / ((2 * L - 2) / 2) := by
      rw [show max 1 (2 * L / 2) = L by omega]
      calc 3 * L * L / 2 / L ≤ 3 * L * L / L := Nat.div_le_div_right (Nat.div_le_self _ _)
        _ ≤ 3 * L * L / ((2 * L - 2) / 2) := Nat.div_le_div_left (by omega) (by omega)
    generalize 3 * L * L / ((2 * L - 2) / 2) = q at h1 ⊢
    generalize 3 * L * L / 2 / max 1 (2 * L / 2) = r at h1 ⊢
    generalize Nat.log2 _ = lg
    generalize (3 * L * L + 2 * ((q + 1) / 3 + 1)) / ((2 * L - 2) / 2) = cs
    exact lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  · simp only [proofParams]; exact Nat.one_le_two_pow
  · unfold fbGS
    simp only [proofParams, Nat.shiftLeft_eq, one_mul]
    generalize pL N = L at hL
    rw [show max 1 (2 * L / 2) = L by omega]
    generalize hU : 2 * L + (2 * L / 3 + 1) + (2 * L / 3 + 1 - (2 * L - 2) / 2) = U
    generalize hX : 2 * L + (2 * L / 3 + 1) = X
    apply (Nat.lt_div_iff_mul_lt (by omega)).mpr
    rw [pow_add]
    have hB : 2 * (L + 1) ≤ 2 ^ (Nat.log2 X + 2) := by
      have := Nat.lt_log2_self (n := X); rw [pow_succ]; omega
    have hA : 1 ≤ 2 ^ U := Nat.one_le_two_pow
    generalize 2 ^ U = A at hA ⊢
    generalize 2 ^ (Nat.log2 X + 2) = B at hB ⊢
    have h1 : 2 * (A * (L + 1)) ≤ A * B := by nlinarith
    have h2 : L + 1 ≤ A * (L + 1) := by nlinarith
    omega

theorem pp_proof (N : Nat) : topPP (proofParams N) :=
  ⟨topParams_8 rfl rfl rfl, by rw [H_eq]; have := pL_ge N; omega⟩

/-- **The cost proof's assumptions hold** for the proof parameters. -/
theorem costSetup : CostSetup proofParams TopInv topPI topMu topNu topPP topJ capT nfP RfP where
  top := topContract'
  prep := prepContract
  pp := pp_proof
  core := core_proof
  gp := gparams_proof
  cp := cparams_proof
  lp := lparams_proof
  kR _ := by change 1 ≤ 8; omega
  R _ := le_rfl
  n1 _ := by unfold nfP; omega
  I5 := I5_proof
  size N := by unfold nfP; rw [show (proofParams N).N = N from rfl]; omega
  capc := capc_proof
  PN _ := rfl
  prepB := prepB_proof
  small := small_proof

/-- **Theorem A for the proof parameters** (Level F): the structure never fails and answers as the
specification. -/
theorem theoremA_proof (KB : Nat) :
    ∃ om, OrderMaintenance.init proofParams KB = .ok om ∧
      ∀ ops, OrderMaintenance.Spec.Valid OrderMaintenance.Spec.State.empty ops →
        om.runOps proofParams ops = .ok (OrderMaintenance.Spec.run
          OrderMaintenance.Spec.State.empty ops) :=
  theoremA core_proof KB

/-- **The wrapper's cost theorem for the proof parameters** (Level F), with no assumptions left:
the cost invariant holds initially and after every valid operation, so every core insertion
takes no FALLBACK and a bounded amount of background work. -/
theorem wrapper_cost_proof {KB : Nat} (hKB : 4 ≤ KB) :
    (∃ om, OrderMaintenance.init proofParams KB = .ok om ∧
      WC proofParams TopInv topPI topMu topNu topJ nfP RfP om OrderMaintenance.Spec.State.empty) ∧
    ∀ om Sp op, WC proofParams TopInv topPI topMu topNu topJ nfP RfP om Sp → op.Valid Sp →
      ∃ om', om.apply proofParams op = .ok ((OrderMaintenance.Spec.step Sp op).2, om') ∧
        WC proofParams TopInv topPI topMu topNu topJ nfP RfP om' (OrderMaintenance.Spec.step Sp
          op).1 :=
  wrapper_cost costSetup hKB

end OrderMaintenance.Proof.Top
