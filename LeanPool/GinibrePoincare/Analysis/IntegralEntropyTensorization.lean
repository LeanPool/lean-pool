/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/IntegralEntropyTensorization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.EntropyProductDecomposition

/-!
# Integral Entropy Tensorization
-/


@[expose] public section

open MeasureTheory Filter
namespace GinibrePoincare
noncomputable section

/-- The scalar Gibbs inequality, including a zero numerator. -/
theorem mul_log_sub_mul_log_ge_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a - b ≤ a * Real.log a - a * Real.log b := by
  by_cases hz : a = 0
  · simp [hz, hb.le]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hb hap)) ha
    rw [Real.log_div hb.ne' hz] at h
    have he : a * (b / a - 1) = b - a := by field_simp
    rw [he] at h
    nlinarith

/-- A mixed logarithmic marginal moment is integrable whenever the marginal's
own logarithmic moment is. Zeros of the marginal cause no integrability gap. -/
theorem integrable_mul_log_fiberMoment
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (h : α × β → ℝ) (hm : Measurable h) (hi : Integrable h (μ.prod ν))
    (hn : ∀ p, 0 ≤ h p)
    (hl : Integrable (fun x => (∫ y, h (x, y) ∂ν) *
      Real.log (∫ y, h (x, y) ∂ν)) μ) :
    Integrable (fun p => h p * Real.log (∫ y, h (p.1, y) ∂ν)) (μ.prod ν) := by
  have hA := hm.stronglyMeasurable.integral_prod_right' (ν := ν)
  apply (integrable_prod_iff (f := fun p => h p * Real.log (∫ y, h (p.1, y) ∂ν))
    (hm.mul (hA.measurable.log.comp measurable_fst)).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hi.prod_right_ae] with x hx
    exact hx.mul_const _
  · have he (x : α) : (∫ y, ‖h (x, y) * Real.log (∫ y, h (x, y) ∂ν)‖ ∂ν) =
        ‖(∫ y, h (x, y) ∂ν) * Real.log (∫ y, h (x, y) ∂ν)‖ := by
      simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hn (x, _))]
      rw [integral_mul_const, abs_of_nonneg (integral_nonneg (fun y => hn (x, y)))]
    simpa only [he] using hl.norm

/-- Nonnegative densities vanish almost everywhere on zero-mass fibers. -/
theorem ae_zero_or_pos_fiberMoment
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (h : α × β → ℝ) (hm : Measurable h) (hi : Integrable h (μ.prod ν))
    (hn : ∀ p, 0 ≤ h p) :
    ∀ᵐ p ∂μ.prod ν, h p = 0 ∨ 0 < ∫ y, h (p.1, y) ∂ν := by
  have hA := hm.stronglyMeasurable.integral_prod_right' (ν := ν)
  apply (Measure.ae_prod_iff_ae_ae (by
    exact (measurableSet_eq_fun hm measurable_const).union
      (measurableSet_lt measurable_const (hA.measurable.comp measurable_fst)))).mpr
  filter_upwards [hi.prod_right_ae] with x hx
  by_cases hp : 0 < ∫ y, h (x, y) ∂ν
  · exact Eventually.of_forall (fun y => Or.inr hp)
  · have hz : (∫ y, h (x, y) ∂ν) = 0 :=
      le_antisymm (not_lt.mp hp) (integral_nonneg (fun y => hn (x, y)))
    exact ((integral_eq_zero_iff_of_nonneg (fun y => hn (x, y)) hx).mp hz).mono
      (fun y hy => Or.inl hy)

/-- Continuous-measure entropy tensorization in its unnormalized matrix form.
Only the actual logarithmic moments must be integrable; no entropy inequality
or Gaussian LSI is assumed. -/
theorem integral_entropy_matrix_tensorization
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (h : α × β → ℝ) (hm : Measurable h) (hi : Integrable h (μ.prod ν))
    (hn : ∀ p, 0 ≤ h p)
    (hl : Integrable (fun p => h p * Real.log (h p)) (μ.prod ν))
    (hAlog : Integrable (fun x => (∫ y, h (x, y) ∂ν) *
      Real.log (∫ y, h (x, y) ∂ν)) μ)
    (hBlog : Integrable (fun y => (∫ x, h (x, y) ∂μ) *
      Real.log (∫ x, h (x, y) ∂μ)) ν)
    (hT : 0 < ∫ p, h p ∂μ.prod ν) :
    (∫ x, (∫ y, h (x, y) ∂ν) * Real.log (∫ y, h (x, y) ∂ν) ∂μ) +
      (∫ y, (∫ x, h (x, y) ∂μ) * Real.log (∫ x, h (x, y) ∂μ) ∂ν) ≤
        (∫ p, h p * Real.log (h p) ∂μ.prod ν) +
          (∫ p, h p ∂μ.prod ν) * Real.log (∫ p, h p ∂μ.prod ν) := by
  let A : α → ℝ := fun x => ∫ y, h (x, y) ∂ν
  let B : β → ℝ := fun y => ∫ x, h (x, y) ∂μ
  let T := ∫ p, h p ∂μ.prod ν
  have hAi : Integrable A μ := hi.integral_prod_left
  have hBi : Integrable B ν := hi.integral_prod_right
  have hAm : Measurable A := hm.stronglyMeasurable.integral_prod_right'.measurable
  have hBm : Measurable B := hm.stronglyMeasurable.integral_prod_left'.measurable
  have hAp := ae_zero_or_pos_fiberMoment μ ν h hm hi hn
  have hBp' := ae_zero_or_pos_fiberMoment ν μ (h ∘ Prod.swap)
    (hm.comp measurable_swap) hi.swap (fun p => hn p.swap)
  have hBp : ∀ᵐ p ∂μ.prod ν, h p = 0 ∨ 0 < B p.2 := by
    simpa [B, Function.comp_def] using Measure.measurePreserving_swap.quasiMeasurePreserving.ae hBp'
  have hmA : Integrable (fun p => h p * Real.log (A p.1)) (μ.prod ν) :=
    integrable_mul_log_fiberMoment μ ν h hm hi hn hAlog
  have hmB : Integrable (fun p => h p * Real.log (B p.2)) (μ.prod ν) := by
    have hs := integrable_mul_log_fiberMoment ν μ (h ∘ Prod.swap)
      (hm.comp measurable_swap) hi.swap (fun p => hn p.swap) hBlog
    simpa [B, Function.comp_def] using hs.swap
  have heA : (∫ p, h p * Real.log (A p.1) ∂μ.prod ν) = ∫ x, A x * Real.log (A x) ∂μ := by
    rw [integral_prod _ hmA]
    simp only [integral_mul_const, A]
  have heB : (∫ p, h p * Real.log (B p.2) ∂μ.prod ν) = ∫ y, B y * Real.log (B y) ∂ν := by
    rw [integral_prod_symm _ hmB]
    simp only [integral_mul_const, B]
  have htA : (∫ x, A x ∂μ) = T := (integral_prod _ hi).symm
  have htB : (∫ y, B y ∂ν) = T := (integral_prod_symm _ hi).symm
  have hv : Integrable (fun p => A p.1 * B p.2 / T) (μ.prod ν) :=
    (hAi.mul_prod hBi).div_const T
  have hvint : (∫ p, A p.1 * B p.2 / T ∂μ.prod ν) = T := by
    rw [integral_div, integral_prod_mul, htA, htB]
    field_simp [show T ≠ 0 from hT.ne']
  have hineq : ∀ᵐ p ∂μ.prod ν,
      h p - A p.1 * B p.2 / T ≤
        h p * Real.log (h p) - h p * Real.log (A p.1) -
          h p * Real.log (B p.2) + h p * Real.log T := by
    filter_upwards [hAp, hBp] with p hpA hpB
    by_cases hz : h p = 0
    · have hvn : 0 ≤ A p.1 * B p.2 / T :=
        div_nonneg (mul_nonneg (integral_nonneg (fun y => hn (p.1, y)))
          (integral_nonneg (fun x => hn (x, p.2)))) hT.le
      simp only [hz, zero_mul, zero_sub, sub_self, add_zero]
      linarith
    · have hpa : 0 < A p.1 := hpA.resolve_left hz
      have hpb : 0 < B p.2 := hpB.resolve_left hz
      have hg := mul_log_sub_mul_log_ge_sub (hn p) (div_pos (mul_pos hpa hpb) hT)
      rw [Real.log_div (mul_pos hpa hpb).ne' hT.ne', Real.log_mul hpa.ne' hpb.ne'] at hg
      dsimp only [A, B] at hg ⊢
      nlinarith
  have hg := integral_mono_ae (hi.sub hv)
    (((hl.sub hmA).sub hmB).add (hi.mul_const (Real.log T))) hineq
  simp only [Pi.sub_apply, Pi.add_apply] at hg
  rw [integral_sub hi hv, hvint,
    integral_add (f := fun p => h p * Real.log (h p) - h p * Real.log (A p.1) - h p * Real.log (B
      p.2)) ((hl.sub hmA).sub hmB) (hi.mul_const (Real.log T)),
    integral_sub (f := fun p => h p * Real.log (h p) - h p * Real.log (A p.1)) (hl.sub hmA) hmB,
      integral_sub hl hmA,
    heA, heB, integral_mul_const] at hg
  change T - T ≤ _ at hg
  change _ ≤ _ + T * Real.log T
  dsimp only [A, B] at hg
  linarith

/-- Integral entropy tensorization, including zero total mass. -/
theorem integral_entropy_matrix_tensorization_nonneg
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (h : α × β → ℝ) (hm : Measurable h) (hi : Integrable h (μ.prod ν))
    (hn : ∀ p, 0 ≤ h p)
    (hl : Integrable (fun p => h p * Real.log (h p)) (μ.prod ν))
    (hAlog : Integrable (fun x => (∫ y, h (x, y) ∂ν) *
      Real.log (∫ y, h (x, y) ∂ν)) μ)
    (hBlog : Integrable (fun y => (∫ x, h (x, y) ∂μ) *
      Real.log (∫ x, h (x, y) ∂μ)) ν) :
    (∫ x, (∫ y, h (x, y) ∂ν) * Real.log (∫ y, h (x, y) ∂ν) ∂μ) +
      (∫ y, (∫ x, h (x, y) ∂μ) * Real.log (∫ x, h (x, y) ∂μ) ∂ν) ≤
        (∫ p, h p * Real.log (h p) ∂μ.prod ν) +
          (∫ p, h p ∂μ.prod ν) * Real.log (∫ p, h p ∂μ.prod ν) := by
  by_cases hp : 0 < ∫ p, h p ∂μ.prod ν
  · exact integral_entropy_matrix_tensorization μ ν h hm hi hn hl hAlog hBlog hp
  · have hz : (∫ p, h p ∂μ.prod ν) = 0 :=
      le_antisymm (not_lt.mp hp) (integral_nonneg hn)
    have hzero := (integral_eq_zero_iff_of_nonneg hn hi).mp hz
    have hAzero := (integral_eq_zero_iff_of_nonneg
      (fun x => integral_nonneg (fun y => hn (x, y))) hi.integral_prod_left).mp
      ((integral_prod _ hi).symm.trans hz)
    have hBzero := (integral_eq_zero_iff_of_nonneg
      (fun y => integral_nonneg (fun x => hn (x, y))) hi.integral_prod_right).mp
      ((integral_prod_symm _ hi).symm.trans hz)
    have he : (∫ p, h p * Real.log (h p) ∂μ.prod ν) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hzero] with p hp
      simp [hp]
    have heA : (∫ x, (∫ y, h (x, y) ∂ν) * Real.log (∫ y, h (x, y) ∂ν) ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hAzero] with x hx
      simp [hx]
    have heB : (∫ y, (∫ x, h (x, y) ∂μ) * Real.log (∫ x, h (x, y) ∂μ) ∂ν) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hBzero] with y hy
      simp [hy]
    rw [he, heA, heB, hz]
    simp

/-- Entropy of a product observable is bounded by the sum of the two averaged
fiber entropies. This is the integral tensorization inequality itself. -/
theorem squareEntropy_prod_tensorization
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α × β → ℝ) (hm : Measurable f)
    (hsq : Integrable (fun p => f p ^ 2) (μ.prod ν))
    (hlog : Integrable (fun p => f p ^ 2 * Real.log (f p ^ 2)) (μ.prod ν))
    (hAlog : Integrable (fun x => fiberSquareMoment ν f x *
      Real.log (fiberSquareMoment ν f x)) μ)
    (hBlog : Integrable (fun y => (∫ x, f (x, y) ^ 2 ∂μ) *
      Real.log (∫ x, f (x, y) ^ 2 ∂μ)) ν) :
    squareEntropy (μ.prod ν) f ≤
      (∫ x, squareEntropy ν (fun y => f (x, y)) ∂μ) +
        (∫ y, squareEntropy μ (fun x => f (x, y)) ∂ν) := by
  have ht := integral_entropy_matrix_tensorization_nonneg μ ν (fun p => f p ^ 2)
    (hm.pow_const 2) hsq (fun p => sq_nonneg (f p)) hlog hAlog hBlog
  unfold fiberSquareMoment at hAlog
  unfold squareEntropy
  dsimp only
  rw [integral_sub hlog.integral_prod_left hAlog,
    integral_sub hlog.integral_prod_right hBlog,
    ← integral_prod _ hlog, ← integral_prod_symm _ hlog]
  linarith

/-- A bounded nonnegative density has a genuine integrable logarithmic moment
under a finite measure, despite the logarithm's singularity at zero. -/
theorem integrable_mul_log_of_bounded_nonneg
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (h : α → ℝ) (hm : Measurable h) (C : ℝ)
    (hb : ∀ x, h x ∈ Set.Icc 0 C) :
    Integrable (fun x => h x * Real.log (h x)) μ := by
  obtain ⟨D, hD⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) C)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  apply memLp_one_iff_integrable.mp
  apply MemLp.of_bound (Real.continuous_mul_log.measurable.comp hm).aestronglyMeasurable D
  exact Eventually.of_forall (fun x => hD (h x) (hb x))

/-- Bounded measurable observables satisfy integral entropy tensorization under
any two probability laws. All logarithmic integrability conditions are discharged. -/
theorem squareEntropy_prod_tensorization_bounded
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hm : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ p, |f p| ≤ C) :
    squareEntropy (μ.prod ν) f ≤
      (∫ x, squareEntropy ν (fun y => f (x, y)) ∂μ) +
        (∫ y, squareEntropy μ (fun x => f (x, y)) ∂ν) := by
  have hsqb (p : α × β) : f p ^ 2 ∈ Set.Icc 0 (C ^ 2) := by
    constructor
    · exact sq_nonneg _
    · nlinarith [sq_abs (f p), abs_nonneg (f p), hb p]
  have hi : Integrable (fun p => f p ^ 2) (μ.prod ν) :=
    memLp_one_iff_integrable.mp (memLp_of_bounded
      (Eventually.of_forall hsqb) (hm.pow_const 2).aestronglyMeasurable 1)
  apply squareEntropy_prod_tensorization μ ν f hm hi
    (integrable_mul_log_of_bounded_nonneg _ _ (hm.pow_const 2) (C ^ 2) hsqb)
  · have hAm : Measurable (fiberSquareMoment ν f) :=
      (hm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
    apply integrable_mul_log_of_bounded_nonneg μ _ hAm (C ^ 2)
    intro x
    refine ⟨fiberSquareMoment_nonneg ν f x, ?_⟩
    have hix : Integrable (fun y => f (x, y) ^ 2) ν :=
      memLp_one_iff_integrable.mp (memLp_of_bounded
        (Eventually.of_forall (fun y => hsqb (x, y)))
        ((hm.pow_const 2).comp measurable_prodMk_left).aestronglyMeasurable 1)
    simpa [fiberSquareMoment] using integral_mono hix (integrable_const (C ^ 2))
      (fun y => (hsqb (x, y)).2)
  · have hBm : Measurable (fun y => ∫ x, f (x, y) ^ 2 ∂μ) :=
      (hm.pow_const 2).stronglyMeasurable.integral_prod_left'.measurable
    apply integrable_mul_log_of_bounded_nonneg ν _ hBm (C ^ 2)
    intro y
    refine ⟨integral_nonneg (fun x => sq_nonneg (f (x, y))), ?_⟩
    have hiy : Integrable (fun x => f (x, y) ^ 2) μ :=
      memLp_one_iff_integrable.mp (memLp_of_bounded
        (Eventually.of_forall (fun x => hsqb (x, y)))
        ((hm.pow_const 2).comp measurable_prodMk_right).aestronglyMeasurable 1)
    simpa using integral_mono hiy (integrable_const (C ^ 2))
      (fun x => (hsqb (x, y)).2)

end
end GinibrePoincare
