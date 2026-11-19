/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.ApproximateEigenvector
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Inverse

/-!
# Approximate first eigenfunctions of the heat-model generator

In the heat model `ν = m.tilted (-U)` with `U ∈ C²`, closed unit gradient `Tbar` and generator
`A = Tbar†Tbar = -ℒ`, suppose the literature Poincaré constant is `C_P(ν) = C` with `0 < C < ∞`
and put
`λ = C⁻¹`. For every `η > 0` there is a centered `f ∈ D(A)` with `‖f‖₂ = 1` and
`‖A f - λ f‖₂ ≤ λ η` (`exists_centered_approx_eigenfunction`). This replaces the first
eigenfunction `L f = -λ₁ f` of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), (19).

The argument: since `C_P(ν) = C`, the gap `Var(u) ≤ C' ‖Tbar u‖²` fails for `C' = C / (1 + η')`
(`literatureConstant_le_of_gap`), which produces a centered unit `y ∈ D(Tbar)` with
`‖Tbar y‖² ≤ λ (1 + η')`. The gap `λ ‖y‖² ≤ ‖Tbar y‖²` on centered vectors
(`closedWeightedOperator_id_gap_of_literature_le`) and the abstract
`Generated.exists_approx_eigenvector_of_gap` give a centered `z ∈ D(A)` within `√(η' / 8)` of `y`
with `‖A z - λ z‖ ≤ λ √(η' / 2)`; normalizing `z` and taking `η' = min 1 (η² / 2)` gives the claim.
Centered means orthogonal to `ker Tbar`, the constants (`orthogonal_ker_iff_mean_eq_zero`).

This is not an eigenfunction: no compactness of the resolvent is proved and no exact eigenvalue
is claimed to be attained.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory

namespace FunctionalInequalities.KLS.LogConcave

open Analysis.Semigroup Analysis.Semigroup.Generated

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty)

/-- If `C_P(ν) = C > 0`, then for every `ε > 0` some centered unit `y ∈ D(Tbar)` has
`‖Tbar y‖² ≤ C⁻¹ (1 + ε)`: otherwise `Var(u) ≤ C / (1 + ε) · ‖Tbar u‖²` on `D(Tbar)` and
`C_P(ν) ≤ C / (1 + ε) < C`. -/
private theorem exists_centered_unit_near_optimal {C : NNReal} (hC : 0 < C)
    (hCP : Poincare.LocalSlope.Intrinsic.optimalConstant ν = (C : ENNReal)) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      L2.mean ν (y : Lp ℝ 2 (ν : Measure V)) = 0 ∧ ‖(y : Lp ℝ 2 (ν : Measure V))‖ = 1 ∧
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi y‖ ^ 2 ≤
        (C : ℝ)⁻¹ * (1 + ε) := by
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi with hTdef
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  by_contra hcon
  push Not at hcon
  set C' : NNReal := Real.toNNReal ((C : ℝ) / (1 + ε)) with hC'
  have hC'r : ((C' : NNReal) : ℝ) = (C : ℝ) / (1 + ε) :=
    Real.coe_toNNReal _ (by positivity)
  have hgap : ∀ u : T.domain,
      ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤ (C' : ℝ) * ‖T u‖ ^ 2 := by
    intro u
    set c : T.domain := ⟨L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
      center_mem_closedWeightedOperator_domain m hν hi u⟩ with hc
    have hTc : T c = T u := closedWeightedOperator_center m hν hi u
    change ‖(c : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤ (C' : ℝ) * ‖T u‖ ^ 2
    rcases eq_or_lt_of_le (norm_nonneg (c : Lp ℝ 2 (ν : Measure V))) with h0 | hpos
    · rw [← h0, sq, zero_mul]
      exact mul_nonneg C'.2 (sq_nonneg _)
    · set a := ‖(c : Lp ℝ 2 (ν : Measure V))‖ with ha
      have hy := hcon (a⁻¹ • c) (by
        change L2.mean ν (a⁻¹ • (c : Lp ℝ 2 (ν : Measure V))) = 0
        rw [L2.mean_smul]
        change a⁻¹ * L2.mean ν (L2.center ν (u : Lp ℝ 2 (ν : Measure V))) = 0
        rw [L2.mean_center, mul_zero]) (by
        change ‖a⁻¹ • (c : Lp ℝ 2 (ν : Measure V))‖ = 1
        rw [norm_smul, norm_inv, norm_norm, ← ha, inv_mul_cancel₀ hpos.ne'])
      rw [LinearPMap.map_smul, hTc, norm_smul, norm_inv, norm_norm, ← ha, mul_pow,
        inv_pow] at hy
      rw [hC'r]
      have ha2 : 0 < a ^ 2 := by positivity
      have h1 : (C : ℝ)⁻¹ * (1 + ε) * a ^ 2 < ‖T u‖ ^ 2 := by
        have h := mul_lt_mul_of_pos_right hy ha2
        have hcancel : (a ^ 2)⁻¹ * ‖T u‖ ^ 2 * a ^ 2 = ‖T u‖ ^ 2 := by
          field_simp
        rwa [hcancel] at h
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      have h2 := mul_lt_mul_of_pos_left h1 hCr
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hCr.ne', one_mul] at h2
      linarith
  have hle := literatureConstant_le_of_gap m hν hi C' hgap
  rw [hCP] at hle
  have hle' : (C : ℝ) ≤ (C' : ℝ) := by exact_mod_cast hle
  rw [hC'r] at hle'
  have hlt : (C : ℝ) / (1 + ε) < C := div_lt_self hCr (by linarith)
  linarith

variable {U : V → ℝ} (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)

include hνU hU in
/-- **Approximate first eigenfunctions in the heat model.** If `C_P(ν) = C` with `0 < C < ∞`,
then for every `η > 0` some centered `f ∈ D(A)`, `A = Tbar†Tbar`, has `‖f‖ = 1` and
`‖A f - C⁻¹ f‖ ≤ C⁻¹ η`. -/
theorem exists_centered_approx_eigenfunction {C : NNReal} (hC : 0 < C)
    (hCP : Poincare.LocalSlope.Intrinsic.optimalConstant ν = (C : ENNReal)) {η : ℝ} (hη : 0 < η) :
    ∃ f : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      L2.mean ν (f : Lp ℝ 2 (ν : Measure V)) = 0 ∧ ‖(f : Lp ℝ 2 (ν : Measure V))‖ = 1 ∧
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) f -
          (C : ℝ)⁻¹ • (f : Lp ℝ 2 (ν : Measure V))‖ ≤ (C : ℝ)⁻¹ * η := by
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi with hTdef
  have hT : T.IsClosed := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  have hd : Dense (T.domain : Set (Lp ℝ 2 (ν : Measure V))) :=
    hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  set lam : ℝ := (C : ℝ)⁻¹ with hlamdef
  have hlam : 0 < lam := inv_pos.mpr hCr
  have horth_iff := orthogonal_ker_iff_mean_eq_zero m hν hi hνU hU
  -- the gap `λ ‖y‖² ≤ ‖Tbar y‖²` on `(ker Tbar)ᗮ`
  have hgap : ∀ y : T.domain,
      (∀ k : T.domain, T k = 0 → ⟪(y : Lp ℝ 2 (ν : Measure V)), (k : Lp ℝ 2 (ν : Measure V))⟫ = 0)
        → lam * ‖(y : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤ ‖T y‖ ^ 2 := by
    intro y hy
    have hmy : L2.mean ν (y : Lp ℝ 2 (ν : Measure V)) = 0 := (horth_iff _).mp hy
    have h := hν.closedWeightedOperator_id_gap_of_literature_le m hi C hCP.le y
    simp only [L2.center, hmy, L2.const_zero, sub_zero] at h
    have h2 := mul_le_mul_of_nonneg_left h hlam.le
    rwa [← mul_assoc, hlamdef, inv_mul_cancel₀ hCr.ne', one_mul] at h2
  -- the perturbation size
  set η' : ℝ := min 1 (η ^ 2 / 2) with hη'def
  have hη'pos : 0 < η' := lt_min one_pos (by positivity)
  have hη'1 : η' ≤ 1 := min_le_left _ _
  have hη'2 : η' ≤ η ^ 2 / 2 := min_le_right _ _
  obtain ⟨y, hym, hy1, hTy⟩ :=
    exists_centered_unit_near_optimal m hν hi hC hCP hη'pos
  obtain ⟨z, hz, hyz, hAz⟩ := exists_approx_eigenvector_of_gap T hT hd hlam hgap y
    ((horth_iff _).mpr hym) hy1 hTy
  -- `‖z‖ ≥ 1 / 2`
  set δ := Real.sqrt (η' / 8) with hδ
  set σ := Real.sqrt (η' / 2) with hσ
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hδ2 : δ ^ 2 = η' / 8 := Real.sq_sqrt (by positivity)
  have hσ2 : σ ^ 2 = η' / 2 := Real.sq_sqrt (by positivity)
  have hδhalf : δ ≤ 1 / 2 := by nlinarith
  have hση : 2 * σ ≤ η := by nlinarith
  have hznorm : 1 / 2 ≤ ‖(z : Lp ℝ 2 (ν : Measure V))‖ := by
    have := norm_sub_norm_le (y : Lp ℝ 2 (ν : Measure V)) (z : Lp ℝ 2 (ν : Measure V))
    rw [hy1] at this
    linarith
  set a := ‖(z : Lp ℝ 2 (ν : Measure V))‖ with ha
  have hapos : 0 < a := by linarith
  refine ⟨a⁻¹ • z, ?_, ?_, ?_⟩
  · apply (horth_iff _).mp
    intro k hk
    change ⟪a⁻¹ • (z : Lp ℝ 2 (ν : Measure V)), (k : Lp ℝ 2 (ν : Measure V))⟫ = 0
    rw [real_inner_smul_left, hz k hk, mul_zero]
  · change ‖a⁻¹ • (z : Lp ℝ 2 (ν : Measure V))‖ = 1
    rw [norm_smul, norm_inv, norm_norm, ← ha, inv_mul_cancel₀ hapos.ne']
  · change ‖adjointComp T (a⁻¹ • z) - lam • a⁻¹ • (z : Lp ℝ 2 (ν : Measure V))‖ ≤ lam * η
    rw [LinearPMap.map_smul, smul_comm lam a⁻¹, ← smul_sub, norm_smul, norm_inv, norm_norm,
      ← ha, inv_mul_le_iff₀ hapos]
    have h1 : lam * σ ≤ lam * (η / 2) := mul_le_mul_of_nonneg_left (by linarith) hlam.le
    have h2 : lam * η * (1 / 2) ≤ lam * η * a :=
      mul_le_mul_of_nonneg_left hznorm (by positivity)
    nlinarith [hAz, h1, h2]

end FunctionalInequalities.KLS.LogConcave
