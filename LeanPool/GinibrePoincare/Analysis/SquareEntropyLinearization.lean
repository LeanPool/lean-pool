/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/SquareEntropyLinearization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEntropy
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.DerivativeTest

/-! # Linearizing square entropy on an actual probability space

The Gaussian matrix Poincaré argument uses the ordinary Gaussian inequality,
independently of the Ginibre symmetric Poincaré theorem. This module supplies
its entropy-to-variance step, including differentiation under the integral.
-/

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology
namespace GinibrePoincare
noncomputable section

private def entropyPerturbation (t x : ℝ) := (1 + t * x)^2 * Real.log ((1 + t*x)^2)
private def entropyPerturbationD (t x : ℝ) :=
  2*x*(1+t*x)*(Real.log ((1+t*x)^2)+1)
private def entropyPerturbationDD (t x : ℝ) :=
  2*x^2*(Real.log ((1+t*x)^2)+3)

private theorem entropyPerturbation_deriv (t x : ℝ) (h : 1 + t * x ≠ 0) :
    HasDerivAt (fun t => entropyPerturbation t x) (entropyPerturbationD t x) t := by
  have ha := (hasDerivAt_id t).mul_const x |>.const_add 1
  have hb := ha.pow 2
  convert hb.mul (hb.log (pow_ne_zero 2 h)) using 1
  · funext s; rfl
  · dsimp [entropyPerturbationD]; simp only [pow_one, one_mul]; field_simp [h]

private theorem entropyPerturbationD_deriv (t x : ℝ) (h : 1 + t * x ≠ 0) :
    HasDerivAt (fun t => entropyPerturbationD t x) (entropyPerturbationDD t x) t := by
  have ha := (hasDerivAt_id t).mul_const x |>.const_add 1
  have hb := ha.pow 2
  convert (ha.const_mul (2*x)).mul ((hb.log (pow_ne_zero 2 h)).add_const 1) using 1
  · funext s; rfl
  · have hh : 1+x*t ≠ 0 := by simpa [mul_comm] using h
    dsimp [entropyPerturbationDD]
    simp only [pow_one, one_mul]
    field_simp [h, hh]; ring

private theorem entropyPerturbation_nonzero {M r t x : ℝ} (hM : 0 ≤ M)
    (hr : r = 1 / (2 * (M + 1))) (ht : t ∈ Icc (-r) r) (hx : x ∈ Icc (-M) M) :
    1+t*x ≠ 0 := by
  have habst : |t| ≤ r := abs_le.mpr ht
  have habsx : |x| ≤ M := abs_le.mpr hx
  have hm : 0 < 2*(M+1) := by positivity
  have hp : |t*x| ≤ r*M := by
    rw [abs_mul]
    exact mul_le_mul habst habsx (abs_nonneg _) (by rw [hr]; positivity)
  have hrm : r*M < 1 := by rw [hr, div_mul_eq_mul_div, one_mul]; apply (div_lt_iff₀ hm).mpr;
                             nlinarith
  have hl := (neg_le_neg hp).trans (neg_abs_le (t*x))
  linarith

private theorem entropyPerturbation_bounds (M : ℝ) (hM : 0 ≤ M) :
    ∃ B : ℝ, ∀ t ∈ Icc (-(1/(2*(M+1)))) (1/(2*(M+1))),
      ∀ x ∈ Icc (-M) M,
      ‖entropyPerturbationD t x‖ ≤ B ∧ ‖entropyPerturbationDD t x‖ ≤ B := by
  let r := 1/(2*(M+1))
  let S : Set (ℝ × ℝ) := Icc (-r) r ×ˢ Icc (-M) M
  have ha : Continuous (fun p : ℝ × ℝ => 1+p.1*p.2) := by fun_prop
  have hl : ContinuousOn (fun p : ℝ × ℝ => Real.log ((1+p.1*p.2)^2)) S :=
    (ha.pow 2).continuousOn.log (fun p hp => pow_ne_zero 2
      (entropyPerturbation_nonzero hM rfl hp.1 hp.2))
  have hd : ContinuousOn (fun p : ℝ × ℝ => ‖entropyPerturbationD p.1 p.2‖) S := by
    unfold entropyPerturbationD
    exact (((continuous_const.mul continuous_snd).mul ha).continuousOn.mul
      (hl.add continuous_const.continuousOn)).norm
  have hdd : ContinuousOn (fun p : ℝ × ℝ => ‖entropyPerturbationDD p.1 p.2‖) S := by
    unfold entropyPerturbationDD
    exact ((continuous_const.mul (continuous_snd.pow 2)).continuousOn.mul
      (hl.add continuous_const.continuousOn)).norm
  obtain ⟨B₁, hB₁⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hd
  obtain ⟨B₂, hB₂⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hdd
  refine ⟨max B₁ B₂, fun t ht x hx => ⟨?_, ?_⟩⟩
  · exact (hB₁ (mem_image_of_mem _ (show (t, x) ∈ S from ⟨ht, hx⟩))).trans (le_max_left _ _)
  · exact (hB₂ (mem_image_of_mem _ (show (t, x) ∈ S from ⟨ht, hx⟩))).trans (le_max_right _ _)

/-- The second variation of the logarithmic moment of `(1+t f)²`, for a bounded
measurable observable. Both derivatives are derived under the actual integral. -/
theorem squareLogPerturbation_second_derivative {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M) :
    let A := fun t : ℝ => ∫ x, (1+t*f x)^2 * Real.log ((1+t*f x)^2) ∂μ
    let A' := fun t : ℝ => ∫ x, 2*f x*(1+t*f x)*(Real.log ((1+t*f x)^2)+1) ∂μ
    (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt A (A' t) t) ∧
      HasDerivAt A' (6 * ∫ x, f x^2 ∂μ) 0 := by
  dsimp only
  let r := 1/(2*(M+1))
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨B, hB⟩ := entropyPerturbation_bounds M hM
  have hx (x : X) : f x ∈ Icc (-M) M := abs_le.mp (hb x)
  have hm (t : ℝ) : AEStronglyMeasurable (fun x => entropyPerturbation t (f x)) μ := by
    unfold entropyPerturbation
    exact (((measurable_const.add (measurable_const.mul hf)).pow_const 2).mul
      ((measurable_const.add (measurable_const.mul hf)).pow_const 2).log).aestronglyMeasurable
  have hdm (t : ℝ) : AEStronglyMeasurable (fun x => entropyPerturbationD t (f x)) μ := by
    unfold entropyPerturbationD
    exact (((measurable_const.mul hf).mul (measurable_const.add (measurable_const.mul hf))).mul
      (((measurable_const.add (measurable_const.mul hf)).pow_const 2).log.add
        measurable_const)).aestronglyMeasurable
  have hddm (t : ℝ) : AEStronglyMeasurable (fun x => entropyPerturbationDD t (f x)) μ := by
    unfold entropyPerturbationDD
    exact ((measurable_const.mul (hf.pow_const 2)).mul
      (((measurable_const.add (measurable_const.mul hf)).pow_const 2).log.add
        measurable_const)).aestronglyMeasurable
  have hbounded : Integrable f μ := (integrable_const M).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hb x)
  have hi (t : ℝ) : Integrable (fun x => entropyPerturbation t (f x)) μ := by
    have hc : Continuous (fun y : ℝ => entropyPerturbation t y) := by
      exact Real.continuous_mul_log.comp (by fun_prop)
    obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc.norm.continuousOn
    exact (integrable_const C).mono' (hm t) (ae_of_all _ fun x => hC (mem_image_of_mem _ (hx x)))
  constructor
  · filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hr) hr] with t ht
    have hs : Icc (-r) r ∈ 𝓝 t := mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
      (Eventually.of_forall hm) (hi t) (hdm t)
      (ae_of_all _ fun x s hs => (hB s hs (f x) (hx x)).1)
      (integrable_const B)
      (ae_of_all _ fun x s hs => entropyPerturbation_deriv s (f x)
        (entropyPerturbation_nonzero hM rfl hs (hx x)))).2
  · have hs : Icc (-r) r ∈ 𝓝 (0 : ℝ) := mem_of_superset
      (Ioo_mem_nhds (neg_neg_of_pos hr) hr) Ioo_subset_Icc_self
    have hdi : Integrable (fun x => entropyPerturbationD 0 (f x)) μ := by
      simpa [entropyPerturbationD] using hbounded.const_mul 2
    have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
      (Eventually.of_forall hdm) hdi (hddm 0)
      (ae_of_all _ fun x s hs => (hB s hs (f x) (hx x)).2)
      (integrable_const B)
      (ae_of_all _ fun x s hs => entropyPerturbationD_deriv s (f x)
        (entropyPerturbation_nonzero hM rfl hs (hx x)))).2
    change HasDerivAt (fun t => ∫ x, entropyPerturbationD t (f x) ∂μ) _ 0
    convert hh using 1
    simp only [entropyPerturbationDD, zero_mul, add_zero, one_pow, Real.log_one, zero_add]
    rw [show (fun x => 2*f x^2*3) = (fun x => 6*(f x^2)) by funext x; ring, integral_const_mul]

/-- A twice differentiable function has nonpositive second derivative at a local
maximum. The derivative-test proof also works without continuity of the second derivative. -/
theorem localMaximum_second_derivative_nonpos (G : ℝ → ℝ) (x : ℝ)
    (hmax : IsLocalMax G x) (hc : ContinuousAt G x) : deriv (deriv G) x ≤ 0 := by
  by_contra h
  have hp : 0 < deriv (deriv G) x := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hp hmax.deriv_eq_zero hc
  have he : G =ᶠ[𝓝 x] fun _ => G x := by
    filter_upwards [hmax, hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hd : deriv G =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [he.eventuallyEq_nhds] with y hy
    simpa using hy.deriv_eq
  have hz : deriv (deriv G) x = 0 := by
    simpa using hd.deriv_eq
  linarith

/-- Linearization of square LSI on a probability space. A bound for all affine
perturbations of a bounded observable gives the variance bound with half the
entropy coefficient. This is a reduction used with proved Gaussian LSI below. -/
theorem squareEntropy_affine_bound_variance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M) (C : ℝ)
    (hlsi : ∀ t : ℝ, squareEntropy μ (fun x => 1+t*f x) ≤ C*t^2) :
    (∫ x, f x^2 ∂μ) - (∫ x, f x ∂μ)^2 ≤ C/2 := by
  let a := ∫ x, f x ∂μ
  let b := ∫ x, f x^2 ∂μ
  let m := fun t : ℝ => 1+2*t*a+t^2*b
  let m' := fun t : ℝ => 2*a+2*t*b
  let A := fun t : ℝ => ∫ x, (1+t*f x)^2 * Real.log ((1+t*f x)^2) ∂μ
  let A' := fun t : ℝ => ∫ x, 2*f x*(1+t*f x)*(Real.log ((1+t*f x)^2)+1) ∂μ
  let G := fun t : ℝ => A t - m t*Real.log (m t) - C*t^2
  let G' := fun t : ℝ => A' t - m' t*(Real.log (m t)+1) - 2*C*t
  have hi : Integrable f μ := (integrable_const M).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hb x)
  have hi2 : Integrable (fun x => f x^2) μ := by
    apply (integrable_const (M^2)).mono' (hf.pow_const 2).aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hb x, sq_abs (f x), abs_nonneg (f x)]
  have hm (t : ℝ) : (∫ x, (1+t*f x)^2 ∂μ) = m t := by
    have he : (fun x => (1+t*f x)^2) = fun x => 1+2*t*f x+t^2*f x^2 := by
      funext x; ring
    rw [he, integral_add (f := fun x => 1+2*t*f x) (g := fun x => t^2*f x^2) ((integrable_const
        1).add (hi.const_mul (2*t)))
      (hi2.const_mul (t^2)), integral_add (f := fun _ => (1 : ℝ)) (g := fun x => 2*t*f x)
          (integrable_const 1) (hi.const_mul (2*t)),
      integral_const, integral_const_mul, integral_const_mul]
    simp [m, a, b]
  have hmD (t : ℝ) : HasDerivAt m (m' t) t := by
    convert (((hasDerivAt_id t).const_mul 2).mul_const a |>.const_add 1).add
      (((hasDerivAt_id t).pow 2).mul_const b) using 1
    · funext s; rfl
    · dsimp [m']; ring
  have hmDD : HasDerivAt m' (2*b) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const b).const_add (2*a) using 1 <;>
      simp [m']
  have hm0 : m 0 = 1 := by simp [m]
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), m t ≠ 0 :=
    (hmD 0).continuousAt.eventually_ne (by simp [m])
  obtain ⟨hAD, hADD⟩ := squareLogPerturbation_second_derivative μ f hf M hM hb
  have hGD : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt G (G' t) t := by
    filter_upwards [hAD, hn] with t ht hnt
    convert (ht.sub ((hmD t).mul ((hmD t).log hnt))).sub
      (((hasDerivAt_id t).pow 2).const_mul C) using 1
    · funext s; rfl
    · change A' t - m' t*(Real.log (m t)+1)-2*C*t =
        A' t - (m' t*Real.log (m t)+m t*(m' t/m t))-C*(2*t^1*1)
      field_simp [hnt]
  change HasDerivAt A' (6*b) 0 at hADD
  have hGDD : HasDerivAt G' (4*(b-a^2)-2*C) 0 := by
    have hlog := (hmD 0).log (by simp [m]) |>.add_const 1
    convert (hADD.sub (hmDD.mul hlog)).sub
      ((hasDerivAt_id (0 : ℝ)).const_mul (2*C)) using 1
    · funext s; rfl
    · simp [m, m']
      ring
  have hzero : G 0 = 0 := by simp [G, A, m]
  have hmax : IsLocalMax G 0 := by
    apply Eventually.of_forall
    intro t
    change G t ≤ G 0
    rw [hzero]
    have hh := hlsi t
    unfold squareEntropy at hh
    rw [hm t] at hh
    change A t - m t*Real.log (m t) ≤ C*t^2 at hh
    dsimp [G]; linarith
  have he : deriv G =ᶠ[𝓝 (0 : ℝ)] G' := hGD.mono fun _ ht => ht.deriv
  have hsecond : deriv (deriv G) 0 = 4*(b-a^2)-2*C :=
    he.deriv_eq.trans hGDD.deriv
  have hc := (hGD.self_of_nhds).continuousAt
  have hh := localMaximum_second_derivative_nonpos G 0 hmax hc
  rw [hsecond] at hh
  change b-a^2 ≤ C/2
  linarith

end
end GinibrePoincare
