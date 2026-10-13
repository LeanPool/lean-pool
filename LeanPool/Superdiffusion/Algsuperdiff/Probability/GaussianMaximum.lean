/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Operations

/-!
# GaussianMaximum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Finite maxima with one-sided Gaussian tails

This module packages the finite-maximum estimate needed for the cutoff
argument.  It assumes neither independence nor identically distributed
variables: the only probabilistic input is the literal one-sided Gaussian
tail for each member of the finite family.
-/

namespace Algsuperdiff.Probability

open MeasureTheory
open HCPolySupport IndependentSums

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The literal J2 Gaussian upper-tail estimate, at positive scale `A`, is the `Γ₂`
weak-Orlicz estimate used by the finite-maximum A in CoarseGraining. -/
theorem isBigOWith_gammaSigma_two_of_gaussian_tail
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {A : ℝ}
    (hTail : ∀ t : ℝ, 1 ≤ t →
      μ {ω | A * t < X ω} ≤ ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ)))) ) :
    IsBigOWith μ (gammaSigma 2) X A := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  have hMeasure := hTail t ht
  have hFinite : μ {ω | A * t < X ω} ≠ ⊤ := measure_ne_top _ _
  change (μ {ω | A * t < X ω}).toReal ≤ Real.exp (-(t ^ (2 : ℝ)))
  rw [← ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.exp (-(t ^ (2 : ℝ))))]
  exact (ENNReal.toReal_le_toReal hFinite ENNReal.ofReal_ne_top).2 hMeasure

omit [MeasurableSpace Ω] in
/-- Pointwise nonnegativity passes to a nonempty finite supremum. -/
theorem finset_sup'_nonneg {s : Finset ι} (hs : s.Nonempty)
    {X : ι → Ω → ℝ} (hX : ∀ i ∈ s, ∀ ω, 0 ≤ X i ω) :
    ∀ ω, 0 ≤ s.sup' hs (fun i => X i ω) := by
  intro ω
  rcases hs with ⟨i, hi⟩
  exact (hX i hi ω).trans (Finset.le_sup' (fun j => X j ω) hi)

/-- A finite supremum of measurable variables is measurable. -/
theorem measurable_finset_sup' {s : Finset ι} (hs : s.Nonempty)
    {X : ι → Ω → ℝ} (hX : ∀ i ∈ s, Measurable (X i)) :
    Measurable (fun ω => s.sup' hs (fun i => X i ω)) := by
  let Y : Ω → ℝ := s.sup' hs X
  have hY : Measurable Y := Finset.measurable_sup' hs hX
  have hY_eq : Y = fun ω => s.sup' hs (fun i => X i ω) := by
    funext ω
    exact Finset.sup'_apply hs X ω
  rw [← hY_eq]
  exact hY

/-- A nonempty finite family with literal J2 tails has an integrable maximum.
The conclusion includes the singleton case; `max 1 (log card)` is essential
there, since `log 1 = 0`. -/
theorem integrable_finset_sup'_of_gaussian_tail
    [IsProbabilityMeasure μ] {s : Finset ι} (hs : s.Nonempty)
    {X : ι → Ω → ℝ} {A : ℝ} (hA : 0 < A)
    (hX_nonneg : ∀ i ∈ s, ∀ ω, 0 ≤ X i ω)
    (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hTail : ∀ i ∈ s, ∀ t : ℝ, 1 ≤ t →
      μ {ω | A * t < X i ω} ≤ ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ)))) ) :
    Integrable (fun ω => s.sup' hs (fun i => X i ω)) μ := by
  by_cases hCard : 2 ≤ s.card
  · have hTail' : ∀ i ∈ s, IsBigOWith μ (gammaSigma 2) (X i) A := by
      intro i hi
      exact isBigOWith_gammaSigma_two_of_gaussian_tail (hTail i hi)
    let Y : Ω → ℝ := fun ω => s.sup' hs (fun i => X i ω)
    let K : ℝ := (3 * Real.log (s.card : ℝ)) ^ ((2 : ℝ)⁻¹) * A
    have hCardReal : (2 : ℝ) ≤ s.card := by exact_mod_cast hCard
    have hLog : Real.log 2 ≤ Real.log (s.card : ℝ) :=
      Real.log_le_log (by norm_num) hCardReal
    have hBase : 0 < 3 * Real.log (s.card : ℝ) := by
      nlinarith [Real.log_two_gt_d9]
    have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos hBase _) hA
    have hY_nonneg : ∀ ω, 0 ≤ Y ω := by
      simpa [Y] using finset_sup'_nonneg hs hX_nonneg
    have hY_meas : AEMeasurable Y μ := by
      simpa [Y] using (measurable_finset_sup' hs hX_meas).aemeasurable
    have hY_tail : IsBigOWith μ (gammaSigma 2) Y K := by
      simpa [Y, K] using isBigOWith_gammaSigma_finset_sup'
        (μ := μ) (s := s) hs (X := X) (A := A) (σ := 2) (by norm_num) hCard hTail'
    have hInt := integrable_rpow_of_isBigOWith_gammaSigma
      (μ := μ) (Y := Y) (K := K) (σ := 2) (p := 1)
      (by norm_num) hK (by norm_num) hY_nonneg hY_meas hY_tail
    simpa [Y, Real.rpow_one] using hInt
  · have hCardLe : s.card ≤ 1 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hCard)
    have hCardEq : s.card = 1 := Nat.le_antisymm hCardLe hs.card_pos
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hCardEq
    have hTail' : IsBigOWith μ (gammaSigma 2) (X i) A :=
      isBigOWith_gammaSigma_two_of_gaussian_tail (hTail i (by simp))
    have hInt := integrable_rpow_of_isBigOWith_gammaSigma
      (μ := μ) (Y := X i) (K := A) (σ := 2) (p := 1)
      (by norm_num) hA (by norm_num) (hX_nonneg i (by simp))
      (hX_meas i (by simp)).aemeasurable hTail'
    simpa [Real.rpow_one] using hInt

/-- Quantitative expectation bound for a nonempty finite maximum with literal
J2 tails.  For a family of size at least two this is the usual
`sqrt (3 log card)` bound; the `max 1` is the explicit, nondegenerate
singleton convention. -/
theorem integral_finset_sup'_le_of_gaussian_tail
    [IsProbabilityMeasure μ] {s : Finset ι} (hs : s.Nonempty)
    {X : ι → Ω → ℝ} {A : ℝ} (hA : 0 < A)
    (hX_nonneg : ∀ i ∈ s, ∀ ω, 0 ≤ X i ω)
    (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hTail : ∀ i ∈ s, ∀ t : ℝ, 1 ≤ t →
      μ {ω | A * t < X i ω} ≤ ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ)))) ) :
    ∫ ω, s.sup' hs (fun i => X i ω) ∂μ ≤
      gammaMomentConst 2 * Real.sqrt (3 * max 1 (Real.log (s.card : ℝ))) * A := by
  by_cases hCard : 2 ≤ s.card
  · have hTail' : ∀ i ∈ s, IsBigOWith μ (gammaSigma 2) (X i) A := by
      intro i hi
      exact isBigOWith_gammaSigma_two_of_gaussian_tail (hTail i hi)
    let Y : Ω → ℝ := fun ω => s.sup' hs (fun i => X i ω)
    let K : ℝ := (3 * Real.log (s.card : ℝ)) ^ ((2 : ℝ)⁻¹) * A
    have hCardReal : (2 : ℝ) ≤ s.card := by exact_mod_cast hCard
    have hLog : Real.log 2 ≤ Real.log (s.card : ℝ) :=
      Real.log_le_log (by norm_num) hCardReal
    have hBase : 0 < 3 * Real.log (s.card : ℝ) := by
      nlinarith [Real.log_two_gt_d9]
    have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos hBase _) hA
    have hY_nonneg : ∀ ω, 0 ≤ Y ω := by
      simpa [Y] using finset_sup'_nonneg hs hX_nonneg
    have hY_meas : AEMeasurable Y μ := by
      simpa [Y] using (measurable_finset_sup' hs hX_meas).aemeasurable
    have hY_tail : IsBigOWith μ (gammaSigma 2) Y K := by
      simpa [Y, K] using isBigOWith_gammaSigma_finset_sup'
        (μ := μ) (s := s) hs (X := X) (A := A) (σ := 2) (by norm_num) hCard hTail'
    have hMoment := integral_rpow_le_of_isBigOWith_gammaSigma
      (μ := μ) (Y := Y) (K := K) (σ := 2) (p := 1)
      (by norm_num) hK (by norm_num) hY_nonneg hY_meas hY_tail
    have hRoot : (3 * Real.log (s.card : ℝ)) ^ ((2 : ℝ)⁻¹) =
        Real.sqrt (3 * Real.log (s.card : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      norm_num
    have hRootLe : (3 * Real.log (s.card : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
        Real.sqrt (3 * max 1 (Real.log (s.card : ℝ))) := by
      rw [hRoot]
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
    have hMoment' : ∫ ω, Y ω ∂μ ≤
        gammaMomentConst 2 * ((3 * Real.log (s.card : ℝ)) ^ ((2 : ℝ)⁻¹) * A) := by
      simpa [K, Real.rpow_one, mul_assoc, mul_left_comm, mul_comm] using hMoment
    calc
      ∫ ω, s.sup' hs (fun i => X i ω) ∂μ = ∫ ω, Y ω ∂μ := by rfl
      _ ≤ gammaMomentConst 2 * ((3 * Real.log (s.card : ℝ)) ^ ((2 : ℝ)⁻¹) * A) := hMoment'
      _ ≤ gammaMomentConst 2 * Real.sqrt
          (3 * max 1 (Real.log (s.card : ℝ))) * A := by
        have hMiddle : gammaMomentConst 2 *
            ((3 * Real.log (s.card : ℝ)) ^ ((2 : ℝ)⁻¹)) ≤
            gammaMomentConst 2 * Real.sqrt
              (3 * max 1 (Real.log (s.card : ℝ))) :=
          mul_le_mul_of_nonneg_left hRootLe (gammaMomentConst_pos (by norm_num)).le
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hMiddle hA.le
  · have hCardLe : s.card ≤ 1 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hCard)
    have hCardEq : s.card = 1 := Nat.le_antisymm hCardLe hs.card_pos
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hCardEq
    have hTail' : IsBigOWith μ (gammaSigma 2) (X i) A :=
      isBigOWith_gammaSigma_two_of_gaussian_tail (hTail i (by simp))
    have hMoment := integral_rpow_le_of_isBigOWith_gammaSigma
      (μ := μ) (Y := X i) (K := A) (σ := 2) (p := 1)
      (by norm_num) hA (by norm_num) (hX_nonneg i (by simp))
      (hX_meas i (by simp)).aemeasurable hTail'
    have hRoot : 1 ≤ Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    have hScale : gammaMomentConst 2 * A ≤ gammaMomentConst 2 * Real.sqrt 3 * A := by
      calc
        gammaMomentConst 2 * A = (gammaMomentConst 2 * A) * 1 := by ring
        _ ≤ (gammaMomentConst 2 * A) * Real.sqrt 3 := by
          exact mul_le_mul_of_nonneg_left hRoot
            (mul_nonneg (gammaMomentConst_pos (by norm_num)).le hA.le)
        _ = gammaMomentConst 2 * Real.sqrt 3 * A := by ring
    calc
      ∫ ω, ({i} : Finset ι).sup' (by simp) (fun j => X j ω) ∂μ = ∫ ω, X i ω ∂μ := by simp
      _ ≤ gammaMomentConst 2 * A := by
        simpa [Real.rpow_one, mul_assoc, mul_left_comm, mul_comm] using hMoment
      _ ≤ gammaMomentConst 2 * Real.sqrt 3 * A := hScale
      _ = gammaMomentConst 2 * Real.sqrt
          (3 * max 1 (Real.log (({i} : Finset ι).card : ℝ))) * A := by norm_num

/-- The logarithm of a triadic descendant count has the elementary
dimension--depth bound used to turn the preceding estimate into a
`sqrt (1 + q)` estimate. -/
theorem max_log_three_pow_le (d q : ℕ) :
    max 1 (Real.log (((3 ^ d) ^ q : ℕ) : ℝ)) ≤
      (1 + (d : ℝ) * Real.log 3) * (1 + q) := by
  have hLog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hDim : 0 ≤ (d : ℝ) * Real.log 3 :=
    mul_nonneg (Nat.cast_nonneg _) hLog
  have hDepth : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  rw [max_le_iff]
  constructor
  · nlinarith [mul_nonneg hDim hDepth]
  · simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    nlinarith [mul_nonneg hDim hDepth]

/-- The descendant-card specialization of the finite Gaussian-maximum
estimate, with a constant depending only on the dimension. -/
theorem integral_finset_sup'_le_of_gaussian_tail_of_card_eq_three_pow_sqrt
    [IsProbabilityMeasure μ] {s : Finset ι} (hs : s.Nonempty)
    {X : ι → Ω → ℝ} {A : ℝ} (hA : 0 < A) {d q : ℕ}
    (hCard : s.card = (3 ^ d) ^ q)
    (hX_nonneg : ∀ i ∈ s, ∀ ω, 0 ≤ X i ω)
    (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hTail : ∀ i ∈ s, ∀ t : ℝ, 1 ≤ t →
      μ {ω | A * t < X i ω} ≤ ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ)))) ) :
    ∫ ω, s.sup' hs (fun i => X i ω) ∂μ ≤
      (gammaMomentConst 2 * Real.sqrt (3 * (1 + (d : ℝ) * Real.log 3))) *
        Real.sqrt (1 + q) * A := by
  have hMax : max 1 (Real.log (s.card : ℝ)) ≤
      (1 + (d : ℝ) * Real.log 3) * (1 + q) := by
    rw [hCard]
    exact max_log_three_pow_le d q
  have hDim : 0 ≤ 3 * (1 + (d : ℝ) * Real.log 3) := by
    have hLog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  have hSqrt : Real.sqrt (3 * max 1 (Real.log (s.card : ℝ))) ≤
      Real.sqrt (3 * ((1 + (d : ℝ) * Real.log 3) * (1 + q))) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hMax (by norm_num)
  have hSplit : Real.sqrt (3 * ((1 + (d : ℝ) * Real.log 3) * (1 + q))) =
      Real.sqrt (3 * (1 + (d : ℝ) * Real.log 3)) * Real.sqrt (1 + q) := by
    rw [show 3 * ((1 + (d : ℝ) * Real.log 3) * (1 + q)) =
      (3 * (1 + (d : ℝ) * Real.log 3)) * (1 + q) by ring]
    exact Real.sqrt_mul hDim _
  calc
    ∫ ω, s.sup' hs (fun i => X i ω) ∂μ ≤
        gammaMomentConst 2 * Real.sqrt (3 * max 1 (Real.log (s.card : ℝ))) * A :=
      integral_finset_sup'_le_of_gaussian_tail (μ := μ) hs hA hX_nonneg hX_meas hTail
    _ ≤ gammaMomentConst 2 * Real.sqrt
        (3 * ((1 + (d : ℝ) * Real.log 3) * (1 + q))) * A := by
      have hGamma : 0 ≤ gammaMomentConst 2 := (gammaMomentConst_pos (by norm_num)).le
      have hMiddle := mul_le_mul_of_nonneg_left hSqrt hGamma
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hMiddle hA.le
    _ = (gammaMomentConst 2 * Real.sqrt (3 * (1 + (d : ℝ) * Real.log 3))) *
        Real.sqrt (1 + q) * A := by rw [hSplit]; ring

end

end Algsuperdiff.Probability
