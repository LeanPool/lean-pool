/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticRadialConfinement.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPotential
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Quantitative radial confinement
The radial Laplacian inequality integrates twice to a quadratic lower bound.
The calculus theorem records the scalar Laplacian condition explicitly; its
identification with planar derivatives is a separate analytic calculation.
-/

@[expose] public section
open Set
namespace GinibrePoincare
noncomputable section

/-- The radial subharmonic differential inequality implies the sharp radial
quadratic lower bound, with no convexity assumption on the profile. -/
theorem radial_laplacian_quadratic_lower_bound (Q : ℝ → ℝ) (ρ : ℝ)
    (hQ : Differentiable ℝ Q) (hdQ : Differentiable ℝ (deriv Q))
    (hcurv : ∀ r : ℝ, 0 < r → 2 * ρ * r ≤ r * deriv (deriv Q) r + deriv Q r)
    (r : ℝ) (hr : 0 ≤ r) :
    ρ / 2 * r ^ 2 + Q 0 ≤ Q r := by
  let H : ℝ → ℝ := fun t => t * deriv Q t - ρ * t ^ 2
  have hHd : Differentiable ℝ H :=
    (differentiable_id.mul hdQ).sub ((differentiable_id.pow 2).const_mul ρ)
  have hHder (t : ℝ) :
      deriv H t = deriv Q t + t * deriv (deriv Q) t - 2 * ρ * t := by
    have hd := ((hasDerivAt_id t).mul ((hdQ t).hasDerivAt)).sub
      (((hasDerivAt_id t).pow 2).const_mul ρ)
    change HasDerivAt H _ t at hd
    convert hd.deriv using 1; dsimp; ring
  have hHmono : MonotoneOn H (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hHd.continuous.continuousOn
      hHd.differentiableOn
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    rw [hHder]
    linarith [hcurv t ht']
  have hfirst (t : ℝ) (ht : 0 < t) : ρ * t ≤ deriv Q t := by
    have h := hHmono (show (0 : ℝ) ∈ Ici 0 from Set.mem_Ici.mpr (le_refl 0)) ht.le ht.le
    dsimp [H] at h
    nlinarith
  let K : ℝ → ℝ := fun t => Q t - ρ / 2 * t ^ 2
  have hKd : Differentiable ℝ K :=
    hQ.sub ((differentiable_id.pow 2).const_mul (ρ / 2))
  have hKder (t : ℝ) : deriv K t = deriv Q t - ρ * t := by
    have hd := ((hQ t).hasDerivAt).sub (((hasDerivAt_id t).pow 2).const_mul (ρ / 2))
    change HasDerivAt K _ t at hd
    convert hd.deriv using 1; dsimp; ring
  have hKmono : MonotoneOn K (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hKd.continuous.continuousOn
      hKd.differentiableOn
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    rw [hKder]
    exact sub_nonneg.mpr (hfirst t ht')
  have hfinal := hKmono (show (0 : ℝ) ∈ Ici 0 from Set.mem_Ici.mpr (le_refl 0)) hr hr
  dsimp [K] at hfinal
  nlinarith

/-- For a rotational strongly convex potential, the quadratic lower bound
already follows directly from the midpoint inequality. -/
theorem rhoConvexPotential_quadratic_lower_bound (ρ : ℝ) {V : Potential}
    (hVr : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) (z : ℂ) :
    ρ / 2 * Complex.normSq z + V 0 ≤ V z := by
  have heven : V (-z) = V z := by
    have h := hVr (-1) z (by simp)
    simpa using h
  have h := hc.2 (Set.mem_univ z) (Set.mem_univ (-z))
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hzero : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • (-z) = 0 := by simp
  rw [hzero] at h
  simp only [Complex.normSq_zero, mul_zero, sub_zero, Complex.normSq_neg, heven,
    smul_eq_mul] at h
  linarith

/-- A twice differentiable strongly convex scalar profile has the correct
second-derivative lower bound, in the paper's normalization. -/
theorem strongConvex_profile_second_derivative (Q : ℝ → ℝ) (ρ : ℝ)
    (hQ : Differentiable ℝ Q) (hdQ : Differentiable ℝ (deriv Q))
    (hc : ConvexOn ℝ Set.univ (fun r => Q r - ρ / 2 * r ^ 2)) (r : ℝ) :
    ρ ≤ deriv (deriv Q) r := by
  let ψ := fun t => Q t - ρ / 2 * t ^ 2
  have hψ : Differentiable ℝ ψ := hQ.sub ((differentiable_id.pow 2).const_mul (ρ / 2))
  have hfirst : deriv ψ = fun t => deriv Q t - ρ * t := by
    funext t
    have hd := ((hQ t).hasDerivAt).sub (((hasDerivAt_id t).pow 2).const_mul (ρ / 2))
    change HasDerivAt ψ _ t at hd
    convert hd.deriv using 1; dsimp; ring
  have hm : Monotone (deriv ψ) := by
    exact monotoneOn_univ.mp (hc.monotoneOn_deriv (fun t _ => hψ t))
  have hn := hm.deriv_nonneg (x := r)
  rw [hfirst] at hn
  have hd := ((hdQ r).hasDerivAt).sub ((hasDerivAt_id r).const_mul ρ)
  change HasDerivAt (fun t => deriv Q t - ρ * t) _ r at hd
  rw [hd.deriv] at hn
  simp only [mul_one] at hn
  linarith

/-- The restriction of the actual planar C² strongly convex potential to a
real radius satisfies Q'' ≥ ρ. Rotation invariance is unnecessary for this step. -/
theorem rhoConvexPotential_axis_second_derivative (ρ : ℝ) {V : Potential}
    (hV : ContDiff ℝ 2 V) (hc : IsRhoConvexPotential ρ V) (r : ℝ) :
    ρ ≤ deriv (deriv (fun t : ℝ => V (t : ℂ))) r := by
  let Q := fun t : ℝ => V (t : ℂ)
  have hQ : ContDiff ℝ 2 Q := hV.comp Complex.ofRealCLM.contDiff
  have hcQ : ConvexOn ℝ Set.univ (fun t : ℝ => Q t - ρ / 2 * t ^ 2) := by
    have h := hc.comp_linearMap Complex.ofRealCLM.toLinearMap
    simpa [Function.comp_def, Q, Complex.normSq_ofReal, pow_two] using h
  have hQd : Differentiable ℝ Q := hQ.differentiable (by norm_num)
  have hQ' : ContDiff ℝ 1 (deriv Q) := (show ContDiff ℝ (1 + 1) Q from hQ).deriv'
  exact strongConvex_profile_second_derivative Q ρ hQd
    (hQ'.differentiable (by norm_num)) hcQ r

/-- Effective potential of the positive-radius Kostlan density. -/
def radialEffectivePotential (n k : ℕ) (Q : ℝ → ℝ) (r : ℝ) : ℝ :=
  (n : ℝ) * Q r - (2 * (k : ℝ) - 1) * Real.log r

/-- The exact curvature computation for a general radial Kostlan density. -/
theorem radialEffectivePotential_second_derivative (n k : ℕ) (Q : ℝ → ℝ)
    (hQ : Differentiable ℝ Q) (hdQ : Differentiable ℝ (deriv Q)) (r : ℝ) (hr : 0 < r) :
    deriv (deriv (radialEffectivePotential n k Q)) r =
      (n : ℝ) * deriv (deriv Q) r + (2 * (k : ℝ) - 1) / r ^ 2 := by
  have hfirst : ∀ t : ℝ, 0 < t →
      deriv (radialEffectivePotential n k Q) t =
        (n : ℝ) * deriv Q t - (2 * (k : ℝ) - 1) * t⁻¹ := by
    intro t ht
    exact (((hQ t).hasDerivAt.const_mul (n : ℝ)).sub
      ((Real.hasDerivAt_log ht.ne').const_mul (2 * (k : ℝ) - 1))).deriv
  have he : deriv (radialEffectivePotential n k Q) =ᶠ[nhds r]
      (fun t => (n : ℝ) * deriv Q t - (2 * (k : ℝ) - 1) * t⁻¹) := by
    filter_upwards [eventually_gt_nhds hr] with t ht
    exact hfirst t ht
  rw [he.deriv_eq]
  have hd := (((hdQ r).hasDerivAt).const_mul (n : ℝ)).sub
    (((hasDerivAt_id r).inv hr.ne').const_mul (2 * (k : ℝ) - 1))
  change HasDerivAt (fun t => (n : ℝ) * deriv Q t - (2 * (k : ℝ) - 1) * t⁻¹) _ r at hd
  rw [hd.deriv]
  dsimp
  ring

/-- The scalar Bakry–Émery curvature bound for the actual radial density,
with the exact `nρ` constant and the positive logarithmic-barrier term. -/
theorem rhoConvexPotential_radial_curvature (n k : ℕ) (hk : 1 ≤ k) (ρ : ℝ)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hc : IsRhoConvexPotential ρ V)
    (r : ℝ) (hr : 0 < r) :
    (n : ℝ) * ρ ≤
      deriv (deriv (radialEffectivePotential n k (fun t : ℝ => V (t : ℂ)))) r := by
  let Q := fun t : ℝ => V (t : ℂ)
  have hQ : ContDiff ℝ 2 Q := hV.comp Complex.ofRealCLM.contDiff
  have hQd : Differentiable ℝ Q := hQ.differentiable (by norm_num)
  have hQ' : ContDiff ℝ 1 (deriv Q) := (show ContDiff ℝ (1 + 1) Q from hQ).deriv'
  rw [radialEffectivePotential_second_derivative n k Q hQd
    (hQ'.differentiable (by norm_num)) r hr]
  have haxis := rhoConvexPotential_axis_second_derivative ρ hV hc r
  have hnonneg : 0 ≤ (2 * (k : ℝ) - 1) / r ^ 2 := by
    apply div_nonneg _ (sq_nonneg r)
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  exact (mul_le_mul_of_nonneg_left haxis (Nat.cast_nonneg n)).trans (le_add_of_nonneg_right hnonneg)

end
end GinibrePoincare
