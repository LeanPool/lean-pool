/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Weighted change of variables along one-dimensional fibers

Tonelli and the one-dimensional Jacobian formula for a C¹ map preserving the first coordinate.
Only volume measures occur. The product norm plays no role in Hausdorff normalization.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace FunctionalInequalities.Analysis

section Tonelli
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite ν]

/-- Tonelli on an arbitrary measurable set, using its fibers. -/
theorem setLIntegral_prod_fibers {A : Set (X × Y)} (hA : MeasurableSet A) {f : X × Y → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ p in A, f p ∂μ.prod ν = ∫⁻ x, ∫⁻ y in {y | (x, y) ∈ A}, f (x, y) ∂ν ∂μ := by
  rw [← lintegral_indicator hA, lintegral_prod _ (hf.indicator hA).aemeasurable]
  apply lintegral_congr
  intro x
  have hx : MeasurableSet {y : Y | (x, y) ∈ A} :=
    hA.preimage (measurable_const.prodMk measurable_id)
  rw [← lintegral_indicator hx]
  apply lintegral_congr
  intro y
  by_cases hp : (x, y) ∈ A <;> simp [hp]

/-- Reverse-order Tonelli on an arbitrary Borel subset of a product. -/
theorem setLIntegral_prod_fibers_symm [SFinite μ] {A : Set (X × Y)} (hA : MeasurableSet A)
    {f : X × Y → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p in A, f p ∂μ.prod ν = ∫⁻ y, ∫⁻ x in {x | (x, y) ∈ A}, f (x, y) ∂μ ∂ν := by
  rw [← lintegral_indicator hA, lintegral_prod_symm _ (hf.indicator hA).aemeasurable]
  apply lintegral_congr
  intro y
  have hy : MeasurableSet {x : X | (x, y) ∈ A} :=
    hA.preimage (measurable_id.prodMk measurable_const)
  rw [← lintegral_indicator hy]
  apply lintegral_congr
  intro x
  by_cases hp : (x, y) ∈ A <;> simp [hp]

end Tonelli

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- The derivative in the level coordinate varies continuously with both coordinates. -/
theorem continuous_deriv_snd {ψ : H × ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (fun p : H × ℝ => deriv (fun t => ψ (p.1, t)) p.2) := by
  have hd : ∀ p : H × ℝ, deriv (fun t => ψ (p.1, t)) p.2 = fderiv ℝ ψ p (0, 1) := by
    intro p
    have hpath : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (((hψ.differentiable one_ne_zero p).hasFDerivAt).comp_hasDerivAt p.2 hpath).deriv
  simp_rw [hd]
  exact (hψ.continuous_fderiv (by simp)).clm_apply continuous_const

/-- Weighted substitution for a C¹ vertical map, on an arbitrary injective Borel piece.
The weight is arbitrary ENNReal-valued; no finite measure or integrability is assumed. -/
theorem setLIntegral_image_verticalMap {ψ : H × ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {A : Set (H × ℝ)}
    (hA : MeasurableSet A) (hi : InjOn (fun p : H × ℝ => (p.1, ψ p)) A) {f : H × ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ q in (fun p : H × ℝ => (p.1, ψ p)) '' A, f q ∂(volume : Measure (H × ℝ)) =
      ∫⁻ p in A,
        ENNReal.ofReal |deriv (fun t => ψ (p.1, t)) p.2| *
          f (p.1, ψ p) ∂(volume : Measure (H × ℝ)) := by
  have hc : Continuous (fun p : H × ℝ => (p.1, ψ p)) := continuous_fst.prodMk hψ.continuous
  have hI := hA.image_of_continuousOn_injOn hc.continuousOn hi
  have hd : ∀ p : H × ℝ, deriv (fun t => ψ (p.1, t)) p.2 = fderiv ℝ ψ p (0, 1) := by
    intro p
    have hpath : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (((hψ.differentiable one_ne_zero p).hasFDerivAt).comp_hasDerivAt p.2 hpath).deriv
  have hm :
    Measurable
      (fun p : H × ℝ => ENNReal.ofReal |deriv (fun t => ψ (p.1, t)) p.2| * f (p.1, ψ p)) := by
    simp_rw [hd]
    exact
      ((hψ.continuous_fderiv (by simp)).clm_apply
            continuous_const).abs.measurable.ennreal_ofReal.mul
        (hf.comp hc.measurable)
  rw [Measure.volume_eq_prod, setLIntegral_prod_fibers hI hf, setLIntegral_prod_fibers hA hm]
  apply lintegral_congr
  intro y
  have hAy : MeasurableSet {t : ℝ | (y, t) ∈ A} :=
    hA.preimage (measurable_const.prodMk measurable_id)
  have himg :
    {s : ℝ | (y, s) ∈ (fun p : H × ℝ => (p.1, ψ p)) '' A} =
      (fun t => ψ (y, t)) '' {t : ℝ | (y, t) ∈ A} := by
    ext s
    constructor
    · rintro ⟨⟨z, t⟩, hp, he⟩
      have hz : z = y := congrArg Prod.fst he
      subst z
      exact ⟨t, hp, congrArg Prod.snd he⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(y, t), ht, rfl⟩
  rw [himg]
  apply lintegral_image_eq_lintegral_abs_deriv_mul hAy
  · intro t ht
    exact
      ((hψ.differentiable one_ne_zero (y, t)).comp t
          ((differentiableAt_const _).prodMk differentiableAt_id)).hasDerivAt.hasDerivWithinAt
  · intro t ht s hs he
    exact congrArg Prod.snd (hi ht hs (Prod.ext rfl he))

end FunctionalInequalities.Analysis
