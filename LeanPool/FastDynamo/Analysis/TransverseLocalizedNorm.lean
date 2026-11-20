/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.TransverseWeightedLeibniz
public import LeanPool.FastDynamo.Analysis.WholePlaneExteriorCutoff

/-!
# Support-localised norms and Hölder bounds on the transverse torus

`eq:background-local-coefficients` bounds the
background coefficients by multiples of the indicator of a measurable set, and the
contributions they generate are absorbed by a localised energy term of
`eq:background-coercivity`.

This module holds the localisation itself: `‖1_S f‖₂` for an `L²` field on the transverse
torus, its elementary properties, and the four Hölder bounds that convert an
"`‖A‖ ≤ C·1_S` almost everywhere" coefficient bound into an estimate in terms of `‖1_S f‖₂`.
Everything is generic in the fibre type `ι` and in the measurable set `S`: no background
operator, no cell, no velocity and no spectral parameter occurs.  The application is in
`Global/TorusBackgroundWeightedEnergy.lean`, which imports this module.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

section Localised

variable {ι : Type*} [Fintype ι]

/-- `‖1_S f‖₂`, the `L²` norm of an `L²` field restricted to a measurable set. -/
def transverseLocalizedNorm (S : Set TransverseTorus) (hS : MeasurableSet S)
    (f : TransverseVecL2 ι) : ℝ :=
  ‖l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι) transverseMeasure S hS f‖

/-- The localised norm is nonnegative. -/
theorem transverseLocalizedNorm_nonneg (S : Set TransverseTorus) (hS : MeasurableSet S)
    (f : TransverseVecL2 ι) : 0 ≤ transverseLocalizedNorm S hS f :=
  norm_nonneg _

/-- `‖1_S f‖₂² = ∫_S |f|²`: the localised norm squared is the paper's `∫_{𝒞_n}|h|²`. -/
theorem transverseLocalizedNorm_sq (S : Set TransverseTorus) (hS : MeasurableSet S)
    (f : TransverseVecL2 ι) :
    transverseLocalizedNorm S hS f ^ 2 =
      ∫ x in S, ‖f x‖ ^ 2 ∂transverseMeasure := by
  rw [transverseLocalizedNorm, sq_norm_transverseVecL2_eq_integral,
    ← integral_indicator hS]
  refine integral_congr_ae ?_
  filter_upwards [l2MeasurableSetRestriction_coe_ae (E := EuclideanSpace ℂ ι)
    transverseMeasure S hS f] with x hx
  rw [hx]
  by_cases hxS : x ∈ S
  · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hxS]
  · rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hxS, norm_zero,
      zero_pow two_ne_zero]

/-- Restriction to a measurable set commutes with multiplication by a scalar `L∞`
coefficient. -/
theorem l2MeasurableSetRestriction_scalarVectorMulTransverseVec
    (S : Set TransverseTorus) (hS : MeasurableSet S)
    (a : TransverseScalarLInf) (f : TransverseVecL2 ι) :
    l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι) transverseMeasure S hS
        (scalarVectorMulTransverseVec ι a f) =
      scalarVectorMulTransverseVec ι a
        (l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι) transverseMeasure S hS f) := by
  apply Lp.ext
  filter_upwards [l2MeasurableSetRestriction_coe_ae (E := EuclideanSpace ℂ ι)
      transverseMeasure S hS (scalarVectorMulTransverseVec ι a f),
    scalarVectorMulTransverseVec_coe_ae a f,
    scalarVectorMulTransverseVec_coe_ae a
      (l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι) transverseMeasure S hS f),
    l2MeasurableSetRestriction_coe_ae (E := EuclideanSpace ℂ ι)
      transverseMeasure S hS f] with x h1 h2 h3 h4
  rw [h1, h3, h4]
  by_cases hxS : x ∈ S
  · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hxS, h2]
  · rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hxS, smul_zero]

/-- A pairing against a field supported in `S` only sees the restriction of the test
field. -/
theorem abs_re_inner_le_localized {S : Set TransverseTorus} (hS : MeasurableSet S)
    {X : TransverseVecL2 ι} (Y : TransverseVecL2 ι)
    (hX : ∀ᵐ x ∂transverseMeasure, x ∉ S → X x = 0) :
    |(inner ℂ Y X : ℂ).re| ≤ transverseLocalizedNorm S hS Y * ‖X‖ := by
  have hinner : (inner ℂ Y X : ℂ) =
      inner ℂ (l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι)
        transverseMeasure S hS Y) X := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hX, l2MeasurableSetRestriction_coe_ae (E := EuclideanSpace ℂ ι)
      transverseMeasure S hS Y] with x hx hy
    by_cases hxS : x ∈ S
    · rw [hy, Set.indicator_of_mem hxS]
    · rw [hx hxS, inner_zero_right, inner_zero_right]
  rw [hinner]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  exact norm_inner_le_norm _ _

/-- **Localised Hölder for a product multiplier.**  If `|a||b| ≤ C 1_S` almost everywhere
then `‖a(bf)‖₂ ≤ C‖1_S f‖₂`.  With `a` a component of `(u_n^bg)_⊥`, `b = β_n` and `C = C√ε`
this is the transport half of `eq:background-local-coefficients`. -/
theorem norm_scalarVectorMulTransverseVec_comp_le_of_ae_indicator
    {S : Set TransverseTorus} (hS : MeasurableSet S)
    {a b : TransverseScalarLInf} {C : ℝ} (hC : 0 ≤ C)
    (hab : ∀ᵐ x ∂transverseMeasure, ‖a x‖ * ‖b x‖ ≤ S.indicator (fun _ ↦ C) x)
    (f : TransverseVecL2 ι) :
    ‖scalarVectorMulTransverseVec ι a (scalarVectorMulTransverseVec ι b f)‖ ≤
      C * transverseLocalizedNorm S hS f := by
  have hmain : ‖scalarVectorMulTransverseVec ι a
      (scalarVectorMulTransverseVec ι b f)‖ ≤
      ‖(C : ℂ) • l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι)
        transverseMeasure S hS f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hab,
      scalarVectorMulTransverseVec_coe_ae a (scalarVectorMulTransverseVec ι b f),
      scalarVectorMulTransverseVec_coe_ae b f,
      Lp.coeFn_smul (C : ℂ) (l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι)
        transverseMeasure S hS f),
      l2MeasurableSetRestriction_coe_ae (E := EuclideanSpace ℂ ι)
        transverseMeasure S hS f] with x hx h1 h2 h3 h4
    rw [h1, h2, h3]
    simp only [Pi.smul_apply, norm_smul]
    rw [h4, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC, ← mul_assoc]
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
      rw [Set.indicator_of_mem hxS] at hx
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    · rw [Set.indicator_of_notMem hxS]
      rw [Set.indicator_of_notMem hxS] at hx
      have h0 : ‖a x‖ * ‖b x‖ = 0 :=
        le_antisymm hx (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      rw [h0, zero_mul, norm_zero, mul_zero]
  refine le_trans hmain (le_of_eq ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  rfl

/-- **Localised Hölder for a vector multiplier.**  If `|A| ≤ C 1_S` almost everywhere then
`‖A g_i‖₂ ≤ C‖1_S f‖₂` for `g_i` any coordinate of `f`.  With `A = ∂_j (u_n^bg)_⊥` this is the
stretching half of `eq:background-local-coefficients`. -/
theorem norm_vectorScalarMulTransverseVec_coord_le_of_ae_indicator
    {S : Set TransverseTorus} (hS : MeasurableSet S)
    {A : TransverseVecLInf ι} {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ᵐ x ∂transverseMeasure, ‖A x‖ ≤ S.indicator (fun _ ↦ C) x)
    (i : ι) (f : TransverseVecL2 ι) :
    ‖vectorScalarMulTransverseVec ι A (transverseCoordL2 i f)‖ ≤
      C * transverseLocalizedNorm S hS f := by
  have hcoe : (vectorScalarMulTransverseVec ι A (transverseCoordL2 i f) :
      TransverseTorus → EuclideanSpace ℂ ι) =ᵐ[transverseMeasure]
      fun x ↦ (transverseCoordL2 i f : TransverseTorus → ℂ) x •
        (A : TransverseTorus → EuclideanSpace ℂ ι) x :=
    vectorScalarMulL2_coe_ae transverseMeasure A (transverseCoordL2 i f)
  have hmain : ‖vectorScalarMulTransverseVec ι A (transverseCoordL2 i f)‖ ≤
      ‖(C : ℂ) • l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι)
        transverseMeasure S hS f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hA, hcoe,
      (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL f,
      Lp.coeFn_smul (C : ℂ) (l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι)
        transverseMeasure S hS f),
      l2MeasurableSetRestriction_coe_ae (E := EuclideanSpace ℂ ι)
        transverseMeasure S hS f] with x hx h1 h2 h3 h4
    have hcoord : (transverseCoordL2 i f : TransverseTorus → ℂ) x = (f x) i := h2
    rw [h1, hcoord, h3]
    simp only [Pi.smul_apply, norm_smul]
    rw [h4, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
      rw [Set.indicator_of_mem hxS] at hx
      calc ‖(f x) i‖ * ‖A x‖ ≤ ‖f x‖ * C := by
            exact mul_le_mul (PiLp.norm_apply_le _ i) hx (norm_nonneg _) (norm_nonneg _)
        _ = C * ‖f x‖ := mul_comm _ _
    · rw [Set.indicator_of_notMem hxS]
      rw [Set.indicator_of_notMem hxS] at hx
      have h0 : ‖A x‖ = 0 := le_antisymm hx (norm_nonneg _)
      rw [h0, mul_zero, norm_zero, mul_zero]
  refine le_trans hmain (le_of_eq ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  rfl

end Localised

end

end FastDynamo
