/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BernoulliTaylorEnergy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.TaylorDifferenceQuotient

/-!
# Bernoulli Taylor Energy
-/


@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace GinibrePoincare
noncomputable section

/-- Mesh of the cube with `n+1` signs. -/
def bernoulliMesh (n : ℕ) : ℝ := (Real.sqrt ((n : ℝ) + 1))⁻¹

/-- Center of a coordinate fiber: `n` signs with the `n+1` normalization. -/
def bernoulliFiberCenter (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  bernoulliMesh n * ∑ k ∈ Finset.range n, ω k

/-- The mesh is strictly positive at every finite stage. -/
theorem bernoulliMesh_pos (n : ℕ) : 0 < bernoulliMesh n := by
  unfold bernoulliMesh
  positivity

/-- The Taylor remainder vanishes along the binomial meshes. -/
theorem bernoulliMesh_tendsto_zero : Tendsto bernoulliMesh atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))

/-- Removing one sign leaves the same standard Gaussian limit. -/
theorem bernoulliFiberCenter_clt :
    TendstoInDistribution bernoulliFiberCenter atTop id
      (fun _ => rademacherProduct) (gaussianReal 0 1) := by
  let c : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) / ((n : ℝ) + 1))
  have hc : Tendsto c atTop (𝓝 1) := by
    simpa [c, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hcm : TendstoInMeasure rademacherProduct (fun n (_ : ℕ → ℝ) => c n)
      atTop (fun _ => (1 : ℝ)) :=
    tendstoInMeasure_of_tendsto_ae (by fun_prop) (ae_of_all _ (fun _ => hc))
  have h := normalizedBernoulliSum_clt.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop) hcm (by fun_prop)
  have he (n : ℕ) (ω : ℕ → ℝ) : c n * normalizedBernoulliSum n ω =
      bernoulliFiberCenter n ω := by
    by_cases hn : n = 0
    · simp [hn, normalizedBernoulliSum, bernoulliFiberCenter]
    · have hnn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnn).ne'
      dsimp [c, normalizedBernoulliSum, bernoulliFiberCenter, bernoulliMesh]
      rw [Real.sqrt_div (Nat.cast_nonneg n)]
      field_simp
  convert! h using 1
  · funext n ω
    exact (he n ω).symm
  · funext x
    simp

/-- Test integrals for the coordinate-fiber centers converge to Gaussian integrals. -/
theorem bernoulliFiberCenter_integral_tendsto (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, f (bernoulliFiberCenter n ω) ∂rademacherProduct)
      atTop (𝓝 (∫ x, f x ∂gaussianReal 0 1)) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    bernoulliFiberCenter_clt.tendsto f
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at h
  simp_rw [integral_map (bernoulliFiberCenter_clt.forall_aemeasurable _)
    f.continuous.aestronglyMeasurable] at h
  exact h

/-- The normalized discrete fiber energy, expressed as a centered quotient. -/
def bernoulliTaylorEnergy (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  2 * ∫ ω, (centeredDifference f (bernoulliMesh n) (bernoulliFiberCenter n ω)) ^ 2
    ∂rademacherProduct


/-- The quotient normalization is exactly the `(n+1)/2` coordinate-fiber energy. -/
theorem bernoulliTaylorEnergy_eq_jump (n : ℕ) (f : ℝ → ℝ) :
    bernoulliTaylorEnergy n f = ((n : ℝ) + 1) / 2 *
      ∫ ω, (f (bernoulliFiberCenter n ω + bernoulliMesh n) -
        f (bernoulliFiberCenter n ω - bernoulliMesh n)) ^ 2 ∂rademacherProduct := by
  unfold bernoulliTaylorEnergy
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
  unfold centeredDifference
  dsimp [bernoulliMesh]
  field_simp
  nlinarith [hsq]

/-- Taylor and the binomial CLT give the sharp limiting derivative energy. -/
theorem bernoulliTaylorEnergy_tendsto (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    Tendsto (fun n => bernoulliTaylorEnergy n f) atTop
      (𝓝 (2 * ∫ x, (deriv f x) ^ 2 ∂gaussianReal 0 1)) := by
  obtain ⟨L, hL⟩ := (hf.continuous_deriv (by norm_num)).bounded_above_of_compact_support hc.deriv
  have hc2 : HasCompactSupport (iteratedDeriv 2 f) := by
    simpa only [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
      iteratedDeriv_zero] using hc.deriv.deriv
  obtain ⟨M, hM⟩ := (hf.continuous_iteratedDeriv 2 le_rfl).bounded_above_of_compact_support hc2
  let g : ℝ → ℝ := fun x => (deriv f x) ^ 2
  have hg : Continuous g := (hf.continuous_deriv (by norm_num)).pow 2
  have hgc : HasCompactSupport g := hc.deriv.mono (by
    intro x hx hz
    exact hx (by simp [g, hz]))
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  let G : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨g, hg⟩ (2 * C)
    (fun x y => (dist_le_norm_add_norm _ _).trans (by
      change ‖g x‖ + ‖g y‖ ≤ 2 * C
      linarith [hC x, hC y]))
  have hlim := bernoulliFiberCenter_integral_tendsto G
  let Q : ℕ → ℝ := fun n => ∫ ω,
    (centeredDifference f (bernoulliMesh n) (bernoulliFiberCenter n ω)) ^ 2 ∂rademacherProduct
  let A : ℕ → ℝ := fun n => ∫ ω, (deriv f (bernoulliFiberCenter n ω)) ^ 2 ∂rademacherProduct
  have he (n : ℕ) : |Q n - A n| ≤
      (M * bernoulliMesh n / 2) * (2 * L + M * bernoulliMesh n / 2) := by
    exact centeredDifference_integral_square_error rademacherProduct (bernoulliFiberCenter n)
      (by unfold bernoulliFiberCenter; fun_prop) f hf L M
      (fun x => by simpa only [Real.norm_eq_abs] using hL x)
      (fun x => by simpa only [Real.norm_eq_abs] using hM x) (bernoulliMesh_pos n)
  have herr : Tendsto (fun n => |Q n - A n|) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => abs_nonneg _) he
    have ht := (bernoulliMesh_tendsto_zero.const_mul M).div_const 2
    simpa using ht.mul (ht.const_add (2 * L))
  have hdiff : Tendsto (fun n => Q n - A n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr herr
  have hQ := hdiff.add hlim
  have hQ' : Tendsto Q atTop (𝓝 (∫ x, (deriv f x) ^ 2 ∂gaussianReal 0 1)) := by
    simpa [A, G, g] using hQ
  exact hQ'.const_mul 2

/-- The analytic limiting step: actual finite binomial bounds imply Gaussian LSI.
The finite bound is still an explicit hypothesis; its identification with the
proved recursively presented cube inequality is a separate probability bridge. -/
theorem gaussian_lsi_of_binomial_fiber_bounds (f : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hfinite : ∀ n, squareEntropy rademacherProduct
      (fun ω => f (normalizedBernoulliSum (n + 1) ω)) ≤ bernoulliTaylorEnergy n f) :
    squareEntropy (gaussianReal 0 1) f ≤
      2 * ∫ x, (deriv f x) ^ 2 ∂gaussianReal 0 1 := by
  exact le_of_tendsto_of_tendsto'
    ((normalizedBernoulliSum_entropy_tendsto f hf.continuous hc).comp
      (tendsto_add_atTop_nat 1))
    (bernoulliTaylorEnergy_tendsto f hf hc) hfinite

end
end GinibrePoincare
