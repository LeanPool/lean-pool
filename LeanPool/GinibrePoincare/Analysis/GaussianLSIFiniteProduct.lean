/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianLSIFiniteProduct.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianLSIProduct
public import LeanPool.GinibrePoincare.Analysis.CompactLipschitzLSIExtension

/-!
# Gaussian LSI finite product

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gaussianProduct_lsi_compactLipschitz`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Recursive real coordinate space of dimension `n + 1`. -/
abbrev GaussianProductSpace : ℕ → Type
  | 0 => ℝ
  | n + 1 => GaussianProductSpace n × ℝ

instance (n : ℕ) : NormedAddCommGroup (GaussianProductSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (NormedAddCommGroup ℝ)
  | succ n ih => letI := ih; exact inferInstanceAs (NormedAddCommGroup (GaussianProductSpace n × ℝ))
instance (n : ℕ) : NormedSpace ℝ (GaussianProductSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (NormedSpace ℝ ℝ)
  | succ n ih => letI := ih; exact inferInstanceAs (NormedSpace ℝ (GaussianProductSpace n × ℝ))
instance (n : ℕ) : MeasurableSpace (GaussianProductSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSpace ℝ)
  | succ n ih => letI := ih; exact inferInstanceAs (MeasurableSpace (GaussianProductSpace n × ℝ))
instance (n : ℕ) : BorelSpace (GaussianProductSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (BorelSpace ℝ)
  | succ n ih => let := ih; exact inferInstanceAs (BorelSpace (GaussianProductSpace n × ℝ))
instance (n : ℕ) : SecondCountableTopology (GaussianProductSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (SecondCountableTopology ℝ)
  | succ n ih => let := ih; exact inferInstanceAs (SecondCountableTopology (GaussianProductSpace n ×
      ℝ))

/-- The actual product of `n + 1` centered Gaussians with variance `v`. -/
def gaussianProductLaw (v : ℝ≥0) : (n : ℕ) → Measure (GaussianProductSpace n)
  | 0 => gaussianReal 0 v
  | n + 1 => (gaussianProductLaw v n).prod (gaussianReal 0 v)
instance (v : ℝ≥0) (n : ℕ) : IsProbabilityMeasure (gaussianProductLaw v n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 v))
  | succ n ih => let := ih; exact inferInstanceAs
      (IsProbabilityMeasure ((gaussianProductLaw v n).prod (gaussianReal 0 v)))

/-- Unit coordinate directions, with the last coordinate listed first. -/
def gaussianProductDirection : (n : ℕ) → Fin (n + 1) → GaussianProductSpace n
  | 0, _ => (1 : ℝ)
  | n + 1, i => Fin.cases (0, 1) (fun j => (gaussianProductDirection n j, 0)) i

/-- Sum of squared actual Fréchet coordinate derivatives. -/
def gaussianProductEnergy (n : ℕ) (f : GaussianProductSpace n → ℝ)
    (p : GaussianProductSpace n) : ℝ :=
  ∑ i, (fderiv ℝ f p (gaussianProductDirection n i)) ^ 2

theorem gaussianProductDirection_norm (n : ℕ) (i : Fin (n + 1)) :
    ‖gaussianProductDirection n i‖ = 1 := by
  induction n with
  | zero => change ‖(1 : ℝ)‖ = 1; simp
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change ‖((0 : GaussianProductSpace n), (1 : ℝ))‖ = 1
      simp [Prod.norm_def]
    · change ‖(gaussianProductDirection n j, (0 : ℝ))‖ = 1
      simp [Prod.norm_def, ih]

/-- Restricting to a left fiber differentiates by composition with the coordinate inclusion. -/
theorem fderiv_gaussian_product_fiber_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E × ℝ → ℝ) (hf : ContDiff ℝ 1 f) (x : E) (y : ℝ) :
    fderiv ℝ (fun t => f (t, y)) x =
      (fderiv ℝ f (x, y)).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
  have hm : HasFDerivAt (fun t : E => (t, y)) (ContinuousLinearMap.inl ℝ E ℝ) x := by
    convert! (hasFDerivAt_id x).prodMk (hasFDerivAt_const y x) using 1
  simpa only [Function.comp_def] using
    (((hf.differentiable one_ne_zero (x, y)).hasFDerivAt).comp x hm).fderiv

/-- The derivative in the new real coordinate is the corresponding Fréchet derivative. -/
theorem deriv_gaussian_product_fiber_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E × ℝ → ℝ) (hf : ContDiff ℝ 1 f) (x : E) (y : ℝ) :
    deriv (fun t => f (x, t)) y = fderiv ℝ f (x, y) (0, 1) := by
  simpa only [Function.comp_def, id_eq] using
    (((hf.differentiable one_ne_zero (x, y)).hasFDerivAt).comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))).deriv

theorem gaussianProductEnergy_nonneg (n : ℕ) (f : GaussianProductSpace n → ℝ)
    (p : GaussianProductSpace n) : 0 ≤ gaussianProductEnergy n f p :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem gaussianProductEnergy_continuous (n : ℕ) (f : GaussianProductSpace n → ℝ)
    (hf : ContDiff ℝ 1 f) : Continuous (gaussianProductEnergy n f) := by
  unfold gaussianProductEnergy
  apply continuous_finsetSum
  intro i hi
  exact ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).pow 2

/-- A uniform derivative bound controls the sum of all coordinate energies. -/
theorem gaussianProductEnergy_le (n : ℕ) (f : GaussianProductSpace n → ℝ)
    (D : ℝ) (hd : ∀ p, ‖fderiv ℝ f p‖ ≤ D) (p : GaussianProductSpace n) :
    gaussianProductEnergy n f p ≤ (n + 1 : ℝ) * D ^ 2 := by
  have hb (i : Fin (n + 1)) : |fderiv ℝ f p (gaussianProductDirection n i)| ≤ D := by
    simpa [gaussianProductDirection_norm] using
      ((fderiv ℝ f p).le_opNorm (gaussianProductDirection n i)).trans
        (by simpa [gaussianProductDirection_norm] using hd p)
  calc
    gaussianProductEnergy n f p ≤ ∑ _ : Fin (n + 1), D ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [hb i, abs_nonneg (fderiv ℝ f p (gaussianProductDirection n i)),
        sq_abs (fderiv ℝ f p (gaussianProductDirection n i))]
    _ = (n + 1 : ℝ) * D ^ 2 := by simp

theorem gaussianProductEnergy_integrable (v : ℝ≥0) (n : ℕ)
    (f : GaussianProductSpace n → ℝ) (hf : ContDiff ℝ 1 f)
    (D : ℝ) (hd : ∀ p, ‖fderiv ℝ f p‖ ≤ D) :
    Integrable (gaussianProductEnergy n f) (gaussianProductLaw v n) := by
  apply memLp_one_iff_integrable.mp
  apply memLp_of_bounded (a := 0) (b := (n + 1 : ℝ) * D ^ 2) _
    (gaussianProductEnergy_continuous n f hf).aestronglyMeasurable 1
  exact Eventually.of_forall (fun p =>
    ⟨gaussianProductEnergy_nonneg n f p, gaussianProductEnergy_le n f D hd p⟩)

/-- Adding a coordinate splits the Dirichlet energy into its two actual fiber energies. -/
theorem gaussianProductEnergy_succ (n : ℕ) (f : GaussianProductSpace (n + 1) → ℝ)
    (hf : ContDiff ℝ 1 f) (x : GaussianProductSpace n) (y : ℝ) :
    gaussianProductEnergy (n + 1) f (x, y) =
      gaussianProductEnergy n (fun t => f (t, y)) x +
        (deriv (fun t => f (x, t)) y) ^ 2 := by
  change (∑ i : Fin (n + 1 + 1), (fderiv ℝ f (x, y) (gaussianProductDirection (n + 1) i)) ^ 2) = _
  rw [Fin.sum_univ_succ]
  change (fderiv ℝ f (x, y) (0, 1)) ^ 2 +
    (∑ i : Fin (n + 1), (fderiv ℝ f (x, y) (gaussianProductDirection n i, 0)) ^ 2) = _
  rw [deriv_gaussian_product_fiber_right f hf]
  unfold gaussianProductEnergy
  simp only [fderiv_gaussian_product_fiber_left f hf, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply]
  exact add_comm _ _

private theorem bounded_squareEntropy_nonneg
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E → ℝ) (hm : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) :
    0 ≤ squareEntropy μ f := by
  have hs (x : E) : f x ^ 2 ∈ Set.Icc 0 (C ^ 2) := by
    refine ⟨sq_nonneg _, ?_⟩
    nlinarith [hb x, abs_nonneg (f x), sq_abs (f x)]
  apply squareEntropy_nonneg μ f
    (memLp_one_iff_integrable.mp (memLp_of_bounded
      (Eventually.of_forall hs) (hm.pow_const 2).aestronglyMeasurable 1))
    (integrable_mul_log_of_bounded_nonneg μ _ (hm.pow_const 2) (C ^ 2) hs)

/-- The sharp LSI for every finite real Gaussian product. The input conditions
are actual C¹ regularity and boundedness of the function and its derivative. -/
theorem gaussianProduct_lsi_bounded_C1 (v : ℝ≥0) (n : ℕ) :
    ∀ (f : GaussianProductSpace n → ℝ), ContDiff ℝ 1 f →
      ∀ C D : ℝ, 0 ≤ C → (∀ p, |f p| ≤ C) → (∀ p, ‖fderiv ℝ f p‖ ≤ D) →
        squareEntropy (gaussianProductLaw v n) f ≤
          (2 * (v : ℝ)) * ∫ p, gaussianProductEnergy n f p ∂gaussianProductLaw v n := by
  induction n with
  | zero =>
    intro f hf C D hC hb hd
    change ContDiff ℝ 1 (f : ℝ → ℝ) at hf
    have hvf : MemLp f 2 (gaussianReal 0 v) :=
      MemLp.of_bound hf.continuous.aestronglyMeasurable C
        (Eventually.of_forall (fun x => by simpa using hb x))
    have hdf : MemLp (deriv f) 2 (gaussianReal 0 v) :=
      MemLp.of_bound (hf.continuous_deriv le_rfl).aestronglyMeasurable D
        (Eventually.of_forall (fun x => by simpa [norm_deriv_eq_norm_fderiv] using hd x))
    have he := (gaussianReal_lsi_variance_C1 v f hf hvf hdf).2
    simpa [gaussianProductLaw, gaussianProductEnergy, gaussianProductDirection,
      fderiv_apply_one_eq_deriv] using he
  | succ n ih =>
    intro f hf C D hC hb hd
    let μ := gaussianProductLaw v n
    let ν := gaussianReal 0 v
    let R : GaussianProductSpace n × ℝ → ℝ := fun p => (fderiv ℝ f p (0, 1)) ^ 2
    let L : GaussianProductSpace n × ℝ → ℝ :=
      fun p => gaussianProductEnergy n (fun t => f (t, p.2)) p.1
    have hR : Continuous R := ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).pow 2
    have hRb (p : GaussianProductSpace n × ℝ) : |fderiv ℝ f p (0, 1)| ≤ D := by
      simpa [Prod.norm_def] using ((fderiv ℝ f p).le_opNorm (0, 1)).trans
        (by simpa [Prod.norm_def] using hd p)
    have hRi : Integrable R (μ.prod ν) := by
      apply memLp_one_iff_integrable.mp
      apply memLp_of_bounded (a := 0) (b := D ^ 2) _ hR.aestronglyMeasurable 1
      apply Eventually.of_forall
      intro p
      refine ⟨sq_nonneg _, ?_⟩
      dsimp only [R]
      nlinarith [hRb p, abs_nonneg (fderiv ℝ f p (0, 1)), sq_abs (fderiv ℝ f p (0, 1))]
    have hsplit (p : GaussianProductSpace n × ℝ) :
        gaussianProductEnergy (n + 1) f p = L p + R p := by
      rcases p with ⟨x, y⟩
      rw [gaussianProductEnergy_succ n f hf, deriv_gaussian_product_fiber_right f hf]
    have hLi : Integrable L (μ.prod ν) := by
      have ht := (gaussianProductEnergy_integrable v (n + 1) f hf D hd).sub hRi
      apply ht.congr
      exact Eventually.of_forall (fun p => by simp only [hsplit, Pi.sub_apply]; ring)
    have htotal : (∫ p, gaussianProductEnergy (n + 1) f p ∂μ.prod ν) =
        (∫ p, L p ∂μ.prod ν) + ∫ p, R p ∂μ.prod ν := by
      simp_rw [hsplit]
      exact integral_add hLi hRi
    have hleft (y : ℝ) : 0 ≤ squareEntropy μ (fun x => f (x, y)) ∧
        squareEntropy μ (fun x => f (x, y)) ≤ (2 * (v : ℝ)) * ∫ x, L (x, y) ∂μ := by
      have hcf : ContDiff ℝ 1 (fun x => f (x, y)) := hf.comp (by fun_prop)
      have hdf (x : GaussianProductSpace n) : ‖fderiv ℝ (fun x => f (x, y)) x‖ ≤ D := by
        rw [fderiv_gaussian_product_fiber_left f hf]
        calc
          _ ≤ ‖fderiv ℝ f (x, y)‖ * ‖ContinuousLinearMap.inl ℝ (GaussianProductSpace n) ℝ‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖fderiv ℝ f (x, y)‖ * 1 :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ (GaussianProductSpace
                n) ℝ) (norm_nonneg _)
          _ ≤ D := by simpa using hd (x, y)
      exact ⟨bounded_squareEntropy_nonneg μ _ hcf.continuous.measurable C (fun x => hb (x, y)),
        ih _ hcf C D hC (fun x => hb (x, y)) hdf⟩
    have hright (x : GaussianProductSpace n) : 0 ≤ squareEntropy ν (fun y => f (x, y)) ∧
        squareEntropy ν (fun y => f (x, y)) ≤ (2 * (v : ℝ)) * ∫ y, R (x, y) ∂ν := by
      have hcf : ContDiff ℝ 1 (fun y => f (x, y)) := hf.comp (by fun_prop)
      have hvf : MemLp (fun y => f (x, y)) 2 ν :=
        MemLp.of_bound hcf.continuous.aestronglyMeasurable C
          (Eventually.of_forall (fun y => by simpa using hb (x, y)))
      have hdf : MemLp (deriv (fun y => f (x, y))) 2 ν := by
        apply MemLp.of_bound (hcf.continuous_deriv le_rfl).aestronglyMeasurable D
        apply Eventually.of_forall
        intro y
        simpa [deriv_gaussian_product_fiber_right f hf] using hRb (x, y)
      have he := (gaussianReal_lsi_variance_C1 v _ hcf hvf hdf).2
      refine ⟨bounded_squareEntropy_nonneg ν _ hcf.continuous.measurable C (fun y => hb (x, y)), ?_⟩
      simpa only [deriv_gaussian_product_fiber_right f hf, R] using he
    have hiL := integral_mono_of_nonneg (Eventually.of_forall (fun y => (hleft y).1))
      (hLi.integral_prod_right.const_mul (2 * (v : ℝ)))
      (Eventually.of_forall (fun y => (hleft y).2))
    have hiR := integral_mono_of_nonneg (Eventually.of_forall (fun x => (hright x).1))
      (hRi.integral_prod_left.const_mul (2 * (v : ℝ)))
      (Eventually.of_forall (fun x => (hright x).2))
    rw [integral_const_mul, ← integral_prod_symm _ hLi] at hiL
    rw [integral_const_mul, ← integral_prod _ hRi] at hiR
    have ht := squareEntropy_prod_tensorization_bounded μ ν f hf.continuous.measurable C hC hb
    change squareEntropy (μ.prod ν) f ≤ (2 * (v : ℝ)) * ∫ p, gaussianProductEnergy (n + 1) f p
        ∂μ.prod ν
    rw [htotal]
    exact ht.trans (by linarith)

/-- The sharp finite-product Gaussian LSI on the actual compact C¹ core. -/
theorem gaussianProduct_lsi_C1 (v : ℝ≥0) (n : ℕ)
    (f : GaussianProductSpace n → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    squareEntropy (gaussianProductLaw v n) f ≤
      (2 * (v : ℝ)) * ∫ p, gaussianProductEnergy n f p ∂gaussianProductLaw v n := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf.continuous
  obtain ⟨D, hD⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv one_ne_zero)
  apply gaussianProduct_lsi_bounded_C1 v n f hf |C| D (abs_nonneg C)
  · intro p
    exact (hC p).trans (le_abs_self C)
  · exact hD

instance (n : ℕ) : FiniteDimensional ℝ (GaussianProductSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (FiniteDimensional ℝ ℝ)
  | succ n ih => let := ih; exact inferInstanceAs
      (FiniteDimensional ℝ (GaussianProductSpace n × ℝ))

/-- Product Lebesgue (Haar) measure in the same recursive coordinate space. -/
def gaussianProductHaar : (n : ℕ) → Measure (GaussianProductSpace n)
  | 0 => volume
  | n + 1 => (gaussianProductHaar n).prod volume

instance (n : ℕ) : (gaussianProductHaar n).IsAddHaarMeasure := by
  induction n with
  | zero => exact inferInstanceAs (volume : Measure ℝ).IsAddHaarMeasure
  | succ n ih => let := ih; exact inferInstanceAs
      (((gaussianProductHaar n).prod (volume : Measure ℝ)).IsAddHaarMeasure)

theorem gaussianProductLaw_absolutelyContinuous (v : ℝ≥0) (hv : v ≠ 0) (n : ℕ) :
    gaussianProductLaw v n ≪ gaussianProductHaar n := by
  induction n with
  | zero => exact gaussianReal_absolutelyContinuous 0 hv
  | succ n ih => exact ih.prod (gaussianReal_absolutelyContinuous 0 hv)

theorem gaussianProductLaw_zero (n : ℕ) : gaussianProductLaw 0 n = Measure.dirac 0 := by
  induction n with
  | zero => exact gaussianReal_zero_var 0
  | succ n ih =>
    change (gaussianProductLaw 0 n).prod (gaussianReal 0 0) = _
    rw [ih, gaussianReal_zero_var, Measure.dirac_prod_dirac]
    rfl

/-- The sharp finite-dimensional Gaussian LSI for actual compact Lipschitz
observables, including zero variance. The derivative is the actual Fréchet derivative. -/
theorem gaussianProduct_lsi_compactLipschitz (v : ℝ≥0) (n : ℕ)
    (f : GaussianProductSpace n → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) :
    squareEntropy (gaussianProductLaw v n) f ≤
      (2 * (v : ℝ)) * ∫ p, gaussianProductEnergy n f p ∂gaussianProductLaw v n := by
  by_cases hv : v = 0
  · subst v
    rw [gaussianProductLaw_zero]
    simp [squareEntropy]
  · exact compactLipschitz_lsi_of_C1 (gaussianProductHaar n) (gaussianProductLaw v n)
      (gaussianProductLaw_absolutelyContinuous v hv n) (gaussianProductDirection n)
      (2 * (v : ℝ)) (gaussianProduct_lsi_C1 v n) f hf hc

end
end GinibrePoincare
