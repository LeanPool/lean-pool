/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedChernoff

/-!
# MomentBoostedIndependentEndpoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Internal sharp independent-family endpoint for moment-boosted tails

This file is a deterministic probability lemma used internally by the
large-cube proof.  Starting with a one-sided tail whose exponent retains the
factor `sigma⁻¹`, it optimizes the truncated-MGF estimate of
`MomentBoostedChernoff.lean` for one independent finite family.  Its constant
is a fixed numerical base raised only to `1 / sigma`; it therefore does not
introduce the forbidden `p^12` loss when `sigma = 2 / p`.

It is not a source-facing stream statement.  Finite-range coloring and the
actual stream variables are supplied separately.

Reference: ABK26, Proposition `p.concentration`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open HCPolySupport HCPolySupport.IndependentSums
open scoped BigOperators

noncomputable section

/-- A deliberately generous, fixed numerical variance envelope. -/
noncomputable def momentBoostedIndependentVariance (sigma : ℝ) : ℝ :=
  4 * (8192 : ℝ) ^ (2 / sigma)

theorem momentBoostedIndependentVariance_pos {sigma : ℝ} :
    0 < momentBoostedIndependentVariance sigma := by
  unfold momentBoostedIndependentVariance
  positivity

theorem sqrt_momentBoostedIndependentVariance {sigma : ℝ} (hsigma : 0 < sigma) :
    Real.sqrt (momentBoostedIndependentVariance sigma) =
      2 * (8192 : ℝ) ^ (1 / sigma) := by
  rw [Real.sqrt_eq_rpow]
  unfold momentBoostedIndependentVariance
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 8192) _)]
  norm_num
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8192)]
  congr 2
  field_simp [hsigma.ne']

theorem two_le_sqrt_momentBoostedIndependentVariance
    {sigma : ℝ} (hsigma : 0 < sigma) :
    2 ≤ Real.sqrt (momentBoostedIndependentVariance sigma) := by
  rw [sqrt_momentBoostedIndependentVariance hsigma]
  have hpow : 1 ≤ (8192 : ℝ) ^ (1 / sigma) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  nlinarith

private theorem momentBoostedFixedBase_le_largeBase {sigma : ℝ}
    (hsigma : 0 < sigma) :
    (48 : ℝ) ^ (2 / sigma) ≤ (8192 : ℝ) ^ (2 / sigma) := by
  exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity)

/-- The MGF quadratic coefficient is bounded by the fixed variance envelope. -/
theorem momentBoostedIndependentVariance_dominates {sigma : ℝ}
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1) :
    (1 : ℝ) / 2 + Real.exp 1 / 2 + (48 : ℝ) ^ (2 / sigma) / 2 ≤
      momentBoostedIndependentVariance sigma := by
  have hfixed : (1 : ℝ) / 2 + Real.exp 1 / 2 ≤ 2 := by
    have hexp : Real.exp 1 < 3 :=
      lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith
  have hbase : 1 ≤ (8192 : ℝ) ^ (2 / sigma) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hkernel := momentBoostedFixedBase_le_largeBase hsigma
  calc
    (1 : ℝ) / 2 + Real.exp 1 / 2 + (48 : ℝ) ^ (2 / sigma) / 2 ≤
        2 + (8192 : ℝ) ^ (2 / sigma) / 2 := by linarith
    _ ≤ 4 * (8192 : ℝ) ^ (2 / sigma) := by nlinarith
    _ = momentBoostedIndependentVariance sigma := rfl

/-- The cutoff which balances the MGF tilt against the strengthened tail. -/
def momentBoostedIndependentTilt (sigma D R t : ℝ) : ℝ :=
  t ^ (sigma - 1) / (4 * Real.sqrt D * Real.sqrt R)

/-- The truncation cutoff associated with the independent moment-boosted tilt. -/
def momentBoostedIndependentCutoff (sigma D R t : ℝ) : ℝ :=
  (Real.sqrt D * Real.sqrt R / sigma) ^ (1 / (1 - sigma)) * t

private theorem momentBoostedIndependent_cutoff_admissible
    {sigma D R t : ℝ} (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hD : 0 < D) (hR : 0 < R) (ht : 0 < t) :
    momentBoostedIndependentTilt sigma D R t =
      momentBoostedKernelCoeff sigma *
        (momentBoostedIndependentCutoff sigma D R t) ^ (sigma - 1) := by
  unfold momentBoostedIndependentTilt momentBoostedIndependentCutoff
  have hbase : 0 ≤ Real.sqrt D * Real.sqrt R / sigma := by positivity
  have hpow :
      ((Real.sqrt D * Real.sqrt R / sigma) ^ (1 / (1 - sigma))) ^
          (sigma - 1) =
        (Real.sqrt D * Real.sqrt R / sigma) ^ (-1 : ℝ) := by
    rw [← Real.rpow_mul hbase]
    congr 1
    field_simp [sub_ne_zero.mpr hsigma_one.ne.symm]
    ring
  rw [Real.mul_rpow (Real.rpow_nonneg hbase _) ht.le, hpow,
    Real.rpow_neg_one]
  unfold momentBoostedKernelCoeff
  field_simp [hsigma.ne', (Real.sqrt_pos.2 hD).ne',
    (Real.sqrt_pos.2 hR).ne']

private theorem momentBoostedIndependent_mgf_decay
    {sigma D R t : ℝ} (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hD : 0 < D) (hR : 0 < R) (ht : 1 ≤ t) :
    let l := momentBoostedIndependentTilt sigma D R t;
    -l * (16 * Real.sqrt D * Real.sqrt R * t) + R * (l ^ (2 : ℕ) * D) ≤
      -2 * t ^ sigma := by
  dsimp
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.2 hD
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hlin :
      (t ^ (sigma - 1) / (4 * Real.sqrt D * Real.sqrt R)) *
          (16 * Real.sqrt D * Real.sqrt R * t) = 4 * t ^ sigma := by
    calc
      (t ^ (sigma - 1) / (4 * Real.sqrt D * Real.sqrt R)) *
          (16 * Real.sqrt D * Real.sqrt R * t) =
          4 * (t ^ (sigma - 1) * t) := by
            field_simp [hsD.ne', hsR.ne']
            ring
      _ = 4 * t ^ sigma := by
            have hmul : t ^ (sigma - 1) * t = t ^ (sigma - 1) * t ^ (1 : ℝ) := by
              rw [Real.rpow_one]
            rw [hmul, ← Real.rpow_add ht0]
            congr 2
            ring
  have hquad :
      R * ((t ^ (sigma - 1) / (4 * Real.sqrt D * Real.sqrt R)) ^ (2 : ℕ) * D) =
        t ^ (2 * sigma - 2) / 16 := by
    calc
      R * ((t ^ (sigma - 1) / (4 * Real.sqrt D * Real.sqrt R)) ^ (2 : ℕ) * D) =
          (t ^ (sigma - 1)) ^ (2 : ℕ) / 16 := by
            field_simp [hsD.ne', hsR.ne', pow_two]
            rw [Real.sq_sqrt hD.le, Real.sq_sqrt hR.le]
            ring
      _ = t ^ (2 * sigma - 2) / 16 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
            congr 2
            ring
  have hpow : t ^ (2 * sigma - 2) ≤ t ^ sigma :=
    Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have htpow : 0 ≤ t ^ sigma := Real.rpow_nonneg ht0.le _
  calc
    -(t ^ (sigma - 1) / (4 * Real.sqrt D * Real.sqrt R)) *
          (16 * Real.sqrt D * Real.sqrt R * t) +
        R * ((t ^ (sigma - 1) / (4 * Real.sqrt D * Real.sqrt R)) ^ (2 : ℕ) * D) =
        -(4 * t ^ sigma) + t ^ (2 * sigma - 2) / 16 := by
          rw [show
            -(t ^ (sigma - 1) / (4 * Real.sqrt D * Real.sqrt R)) *
                (16 * Real.sqrt D * Real.sqrt R * t) =
              -((t ^ (sigma - 1) / (4 * Real.sqrt D * Real.sqrt R)) *
                (16 * Real.sqrt D * Real.sqrt R * t)) by ring,
            hlin, hquad]
    _ ≤ -(4 * t ^ sigma) + t ^ sigma / 16 := by linarith
    _ ≤ -2 * t ^ sigma := by nlinarith

private theorem momentBoostedIndependent_cutoff_tail_absorption
    {sigma D R t : ℝ} (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hD : 0 < D) (hR : 0 < R) (hR_one : 1 ≤ R) (ht : 1 ≤ t)
    (hcoeff : 2 + 2 / sigma ≤
      (Real.sqrt D / sigma) ^ (sigma / (1 - sigma)) / (2 * sigma)) :
    R * Real.exp
        (-((momentBoostedIndependentCutoff sigma D R t) ^ sigma / (2 * sigma))) ≤
      Real.exp (-2 * t ^ sigma) := by
  let z : ℝ := R ^ (sigma / (2 * (1 - sigma))) * t ^ sigma
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hbeta : 0 < sigma / (2 - sigma) := div_pos hsigma (by linarith)
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR_one
  have hcard : R ^ (sigma / (2 - sigma)) ≤ z := by
    have hle : sigma / (2 - sigma) ≤ sigma / (2 * (1 - sigma)) := by
      have hleft : 0 < 2 - sigma := by linarith
      have hright : 0 < 2 * (1 - sigma) := by
        nlinarith [sub_pos.mpr hsigma_one]
      apply (div_le_div_iff₀ hleft hright).2
      nlinarith
    calc
      R ^ (sigma / (2 - sigma)) ≤ R ^ (sigma / (2 * (1 - sigma))) :=
        Real.rpow_le_rpow_of_exponent_le hR_one hle
      _ ≤ R ^ (sigma / (2 * (1 - sigma))) * t ^ sigma := by
        rw [← mul_one (R ^ (sigma / (2 * (1 - sigma))))]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.one_le_rpow ht hsigma.le) (Real.rpow_nonneg hR0.le _)
  have hlog : Real.log R ≤ (2 / sigma) * z := by
    calc
      Real.log R ≤ R ^ (sigma / (2 - sigma)) / (sigma / (2 - sigma)) := by
        simpa using Real.log_le_rpow_div hR0.le hbeta
      _ ≤ z / (sigma / (2 - sigma)) :=
        div_le_div_of_nonneg_right hcard hbeta.le
      _ = ((2 - sigma) / sigma) * z := by
        field_simp [hsigma.ne']
      _ ≤ (2 / sigma) * z := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        field_simp [hsigma.ne']
        linarith
  have hRexp : R ≤ Real.exp ((2 / sigma) * z) := by
    rw [← Real.exp_log hR0]
    exact Real.exp_le_exp.2 hlog
  have hcutoff_pow :
      (momentBoostedIndependentCutoff sigma D R t) ^ sigma / (2 * sigma) =
        ((Real.sqrt D / sigma) ^ (sigma / (1 - sigma)) / (2 * sigma)) * z := by
    unfold momentBoostedIndependentCutoff
    have hbase : 0 ≤ Real.sqrt D * Real.sqrt R / sigma := by positivity
    have hleft : 0 ≤ Real.sqrt D / sigma := by positivity
    have hsR : 0 ≤ Real.sqrt R := Real.sqrt_nonneg _
    calc
      (((Real.sqrt D * Real.sqrt R / sigma) ^ (1 / (1 - sigma)) * t) ^ sigma) /
          (2 * sigma) =
          ((Real.sqrt D * Real.sqrt R / sigma) ^ (sigma / (1 - sigma)) *
            t ^ sigma) / (2 * sigma) := by
              rw [Real.mul_rpow (Real.rpow_nonneg hbase _) ht0.le,
                ← Real.rpow_mul hbase]
              congr 2
              field_simp [sub_ne_zero.mpr hsigma_one.ne.symm]
      _ = ((Real.sqrt D / sigma) ^ (sigma / (1 - sigma)) / (2 * sigma)) *
          ((Real.sqrt R) ^ (sigma / (1 - sigma)) * t ^ sigma) := by
            rw [show Real.sqrt D * Real.sqrt R / sigma =
              (Real.sqrt D / sigma) * Real.sqrt R by ring,
              Real.mul_rpow hleft hsR]
            ring
      _ = ((Real.sqrt D / sigma) ^ (sigma / (1 - sigma)) / (2 * sigma)) * z := by
            congr 1
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le]
            congr 1
            field_simp [sub_ne_zero.mpr hsigma_one.ne.symm]
  have hz0 : 0 ≤ z := by positivity
  rw [hcutoff_pow]
  calc
    R * Real.exp
        (-(((Real.sqrt D / sigma) ^ (sigma / (1 - sigma)) / (2 * sigma)) * z)) ≤
        Real.exp ((2 / sigma) * z) * Real.exp
          (-(((Real.sqrt D / sigma) ^ (sigma / (1 - sigma)) / (2 * sigma)) * z)) :=
      mul_le_mul_of_nonneg_right hRexp (by positivity)
    _ = Real.exp
        (((2 / sigma) -
          (Real.sqrt D / sigma) ^ (sigma / (1 - sigma)) / (2 * sigma)) * z) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-2 * z) := Real.exp_le_exp.2 (by
      nlinarith [hcoeff])
    _ ≤ Real.exp (-2 * t ^ sigma) := Real.exp_le_exp.2 (by
      have htz : t ^ sigma ≤ z := by
        rw [← one_mul (t ^ sigma)]
        exact mul_le_mul_of_nonneg_right
          (Real.one_le_rpow hR_one (by
            exact div_nonneg hsigma.le (by linarith)))
          (Real.rpow_nonneg ht0.le _)
      linarith)

private theorem momentBoostedIndependent_union_coefficient
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigma_one : sigma < 1) :
    2 + 2 / sigma ≤
      (Real.sqrt (momentBoostedIndependentVariance sigma) / sigma) ^
        (sigma / (1 - sigma)) / (2 * sigma) := by
  let A : ℝ := 8192
  let q : ℝ := sigma / (1 - sigma)
  have hq : 0 < q := div_pos hsigma (sub_pos.mpr hsigma_one)
  have hA_one : 1 ≤ A := by norm_num [A]
  have hroot : A ^ (1 / sigma) ≤
      Real.sqrt (momentBoostedIndependentVariance sigma) / sigma := by
    have hfactor : 1 ≤ 2 / sigma := by
      rw [one_le_div hsigma]
      linarith
    calc
      A ^ (1 / sigma) = 1 * A ^ (1 / sigma) := by ring
      _ ≤ (2 / sigma) * A ^ (1 / sigma) :=
        mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (by positivity) _)
      _ = Real.sqrt (momentBoostedIndependentVariance sigma) / sigma := by
        rw [sqrt_momentBoostedIndependentVariance hsigma]
        simp only [A]
        field_simp [hsigma.ne']
  have hpow : (A ^ (1 / sigma)) ^ q ≤
      (Real.sqrt (momentBoostedIndependentVariance sigma) / sigma) ^ q :=
    Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hroot hq.le
  have hpow_eq : (A ^ (1 / sigma)) ^ q = A ^ (1 / (1 - sigma)) := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ A)]
    congr 1
    dsimp [q]
    field_simp [hsigma.ne', sub_ne_zero.mpr hsigma_one.ne.symm]
  have hexponent : 1 ≤ 1 / (1 - sigma) := by
    apply (le_div_iff₀ (sub_pos.mpr hsigma_one)).2
    linarith
  have hlarge : (8 : ℝ) ≤
      (Real.sqrt (momentBoostedIndependentVariance sigma) / sigma) ^ q := by
    calc
      (8 : ℝ) ≤ A := by norm_num [A]
      _ ≤ A ^ (1 / (1 - sigma)) := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hA_one hexponent
      _ = (A ^ (1 / sigma)) ^ q := hpow_eq.symm
      _ ≤ _ := hpow
  change 2 + 2 / sigma ≤
    (Real.sqrt (momentBoostedIndependentVariance sigma) / sigma) ^ q /
      (2 * sigma)
  apply (le_div_iff₀ (mul_pos (by norm_num) hsigma)).2
  have heq : (2 + 2 / sigma) * (2 * sigma) = 4 * sigma + 4 := by
    field_simp [hsigma.ne']
    ring
  rw [heq]
  exact (by linarith : 4 * sigma + 4 ≤ 8).trans hlarge

/-- A sharp one-sided `Gamma_sigma` tail for an independent centered finite
family at its true square-root cardinality scale. -/
theorem isBigOWith_gammaSigma_finset_sum_momentBoosted_independent
    {Omega iota : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : iota → Omega → ℝ} {s : Finset iota}
    {sigma : ℝ}
    (hs : s.Nonempty)
    (h_indep : iIndepFun X mu)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) mu)
    (h_sq : ∀ i ∈ s, Integrable (fun omega => |X i omega| ^ (2 : ℕ)) mu)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hX : ∀ i ∈ s, IsBigOWith mu (momentBoostedGammaSigma sigma) (X i) 1)
    (hmean : ∀ i ∈ s, ∫ omega, X i omega ∂mu = 0)
    (hsecond : ∀ i ∈ s, ∫ omega, |X i omega| ^ (2 : ℕ) ∂mu ≤ 1) :
    IsBigOWith mu (gammaSigma sigma) (fun omega => ∑ i ∈ s, X i omega)
      (16 * Real.sqrt (momentBoostedIndependentVariance sigma) *
        Real.sqrt (s.card : ℝ)) := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  let D : ℝ := momentBoostedIndependentVariance sigma
  let R : ℝ := s.card
  let l : ℝ := momentBoostedIndependentTilt sigma D R t
  let L : ℝ := momentBoostedIndependentCutoff sigma D R t
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast hs.card_pos
  have hR_one : 1 ≤ R := by
    dsimp [R]
    exact_mod_cast Nat.succ_le_of_lt hs.card_pos
  have hD : 0 < D := by
    exact momentBoostedIndependentVariance_pos
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hDtwo : 2 ≤ Real.sqrt D := by
    dsimp [D]
    exact two_le_sqrt_momentBoostedIndependentVariance hsigma
  have hl : 0 ≤ l := by
    dsimp [l, momentBoostedIndependentTilt]
    positivity
  have hlone : l ≤ 1 := by
    dsimp [l, momentBoostedIndependentTilt]
    have hpow : t ^ (sigma - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
    have hden : 1 ≤ 4 * Real.sqrt D * Real.sqrt R := by
      have hrootR : 1 ≤ Real.sqrt R := (Real.one_le_sqrt).2 hR_one
      nlinarith
    calc
      t ^ (sigma - 1) / (4 * Real.sqrt D * Real.sqrt R) ≤
          1 / (4 * Real.sqrt D * Real.sqrt R) :=
        div_le_div_of_nonneg_right hpow (by positivity)
      _ ≤ 1 := (div_le_one₀ (by positivity)).2 hden
  have hL : 1 ≤ L := by
    dsimp [L, momentBoostedIndependentCutoff]
    have hbase : 1 ≤ Real.sqrt D * Real.sqrt R / sigma := by
      have hrootR : 1 ≤ Real.sqrt R := (Real.one_le_sqrt).2 hR_one
      apply (le_div_iff₀ hsigma).2
      nlinarith
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow hbase (by
        exact div_nonneg zero_le_one (sub_nonneg.mpr hsigma_one.le))) ht
  have hlL : l ≤ momentBoostedKernelCoeff sigma * L ^ (sigma - 1) := by
    dsimp [l, L]
    rw [momentBoostedIndependent_cutoff_admissible hsigma hsigma_one hD hR ht0]
  have htail := measureReal_upperTailEvent_finset_sum_le_momentBoosted
    (mu := mu) (X := X) (s := s) (a := 16 * Real.sqrt D * Real.sqrt R * t)
    (sigma := sigma) (l := l) (L := L) (C2 := 1)
    h_indep h_meas h_int h_sq hmean hsecond hsigma hsigma_one hX hl hlone hL hlL
  have hmgf :
      Real.exp (-l * (16 * Real.sqrt D * Real.sqrt R * t) + R *
        (l ^ (2 : ℕ) * ((1 : ℝ) / 2 + Real.exp 1 / 2 +
          (48 : ℝ) ^ (2 / sigma) / 2))) ≤
        Real.exp (-2 * t ^ sigma) := by
    apply Real.exp_le_exp.2
    calc
      -l * (16 * Real.sqrt D * Real.sqrt R * t) + R *
          (l ^ (2 : ℕ) * ((1 : ℝ) / 2 + Real.exp 1 / 2 +
            (48 : ℝ) ^ (2 / sigma) / 2)) ≤
          -l * (16 * Real.sqrt D * Real.sqrt R * t) + R * (l ^ (2 : ℕ) * D) := by
            have hproxy := momentBoostedIndependentVariance_dominates hsigma hsigma_one
            have hmul := mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hproxy (sq_nonneg l)) hR.le
            simpa [D, mul_assoc, mul_left_comm, mul_comm] using
              add_le_add_left hmul (-l * (16 * Real.sqrt D * Real.sqrt R * t))
      _ ≤ -2 * t ^ sigma := by
        exact momentBoostedIndependent_mgf_decay hsigma hsigma_one hD hR ht
  have hunion : R * (momentBoostedGammaSigma sigma L)⁻¹ ≤
      Real.exp (-2 * t ^ sigma) := by
    rw [momentBoostedGammaSigma_inv]
    exact momentBoostedIndependent_cutoff_tail_absorption hsigma hsigma_one
      hD hR hR_one ht (momentBoostedIndependent_union_coefficient hsigma hsigma_one)
  calc
    mu.real (upperTailEvent (fun omega => ∑ i ∈ s, X i omega)
        ((16 * Real.sqrt D * Real.sqrt R) * t)) ≤
        Real.exp (-l * (16 * Real.sqrt D * Real.sqrt R * t) + R *
          (l ^ (2 : ℕ) * ((1 : ℝ) / 2 + Real.exp 1 / 2 +
            (48 : ℝ) ^ (2 / sigma) / 2))) +
          R * (momentBoostedGammaSigma sigma L)⁻¹ := by
            simpa [D, R, mul_assoc, mul_left_comm, mul_comm] using htail
    _ ≤ Real.exp (-2 * t ^ sigma) + Real.exp (-2 * t ^ sigma) :=
      add_le_add hmgf hunion
    _ = 2 * Real.exp (-2 * t ^ sigma) := by ring
    _ ≤ Real.exp (-(t ^ sigma)) :=
      two_mul_exp_neg_two_mul_le_exp_neg (Real.one_le_rpow ht hsigma.le)

end

end Algsuperdiff.Section3.Provider.Stream
