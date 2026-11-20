/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexRadialLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexRadialDensity
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticRadiusLaw
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Strong convex radial law

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `radialConfinementProbabilityDensity_eq_sqrt_map`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
namespace GinibrePoincare
noncomputable section

/-- Genuine positive-half-line square-coordinate change of variables. -/
theorem radialConfinementDensity_square_lintegral (n k : ℕ) (Q : ℝ → ℝ)
    (g : ℝ → ℝ≥0∞) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ k * Real.exp (-(n : ℝ) * Q (Real.sqrt s))) * g s) =
      2 * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (radialConfinementDensity n k Q r) * g (r ^ 2) := by
  have himage : (fun r : ℝ => r ^ 2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext s
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact pow_pos (show 0 < r from hr) 2
    · intro hs
      exact ⟨Real.sqrt s, Real.sqrt_pos.mpr hs, Real.sq_sqrt hs.le⟩
  have hinj : InjOn (fun r : ℝ => r ^ 2) (Ioi (0 : ℝ)) := by
    intro x hx y hy he
    change 0 < x at hx
    change 0 < y at hy
    change x ^ 2 = y ^ 2 at he
    nlinarith
  have hdf (r : ℝ) : HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * r) (Ioi 0) r := by
    simpa only [Nat.reduceSub, pow_one, Nat.cast_ofNat] using hasDerivWithinAt_pow 2 r
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun r hr => hdf r) hinj
    (fun s => ENNReal.ofReal (s ^ k * Real.exp (-(n : ℝ) * Q (Real.sqrt s))) * g s)
  simp only [himage] at h
  rw [h]
  rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hrpos : 0 < r := hr
  dsimp only
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hrpos,
    abs_of_pos (mul_pos (by norm_num) hrpos)]
  unfold radialConfinementDensity
  rw [max_eq_left hrpos.le]
  have hp : (2 * r) * ((r ^ 2) ^ k * Real.exp (-(n : ℝ) * Q r)) =
      2 * (r ^ (2 * k + 1) * Real.exp (-(n : ℝ) * Q r)) := by
    rw [← pow_mul, pow_add, pow_one]
    ring
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hp,
    ENNReal.ofReal_mul (by norm_num)]
  norm_num
  rw [mul_assoc]

/-- The unnormalised radial law on `(0, ∞)`: Lebesgue measure on `Ioi 0` with density
`radialConfinementDensity n k Q`. -/
def rawRadialConfinementLaw (n k : ℕ) (Q : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun r => ENNReal.ofReal (radialConfinementDensity n k Q r))

theorem rawPotentialSquaredRadiusLaw_lintegral (n k : ℕ) (V : Potential)
    (hV : Continuous V) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ s, g s ∂rawPotentialSquaredRadiusLaw n k V =
      2 * ∫⁻ r, g (r ^ 2) ∂rawRadialConfinementLaw n k (fun r : ℝ => V (r : ℂ)) := by
  unfold rawPotentialSquaredRadiusLaw radialPowerMeasure rawRadialConfinementLaw
  have htilt : Measurable (fun s : ℝ => ENNReal.ofReal
      (Real.exp (-(n : ℝ) * potentialSquaredRadiusProfile V s))) := by
    exact (Real.continuous_exp.comp (continuous_const.mul
      (hV.comp (Complex.continuous_ofReal.comp Real.continuous_sqrt)))).measurable.ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ htilt hg]
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (htilt.mul hg)]
  rw [lintegral_withDensity_eq_lintegral_mul _
    (f := fun r => ENNReal.ofReal (radialConfinementDensity n k (fun t : ℝ => V (t : ℂ)) r))
    (g := fun r => g (r ^ 2))
    (radialConfinementDensity_continuous n k (hV.comp
        Complex.continuous_ofReal)).measurable.ennreal_ofReal
    (hg.comp (by fun_prop))]
  simp only [Pi.mul_apply]
  have he : (fun s : ℝ => ENNReal.ofReal (s ^ ((k + 1) - 1)) *
      (ENNReal.ofReal (Real.exp (-(n : ℝ) * potentialSquaredRadiusProfile V s)) * g s))
          =ᵐ[volume.restrict (Ioi 0)]
      (fun s => ENNReal.ofReal (s ^ k * Real.exp (-(n : ℝ) * V (Real.sqrt s : ℂ))) * g s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change 0 < s at hs
    simp only [Nat.add_sub_cancel, potentialSquaredRadiusProfile]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hs.le k)]
  rw [lintegral_congr_ae he]
  exact radialConfinementDensity_square_lintegral n k (fun r : ℝ => V (r : ℂ)) g

theorem rawPotentialSquaredRadiusLaw_eq_square_map (n k : ℕ) (V : Potential)
    (hV : Continuous V) :
    rawPotentialSquaredRadiusLaw n k V =
      (2 : ℝ≥0∞) • (rawRadialConfinementLaw n k (fun r : ℝ => V (r : ℂ))).map (fun r => r ^ 2) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_smul_measure, lintegral_map hg (by fun_prop)]
  exact rawPotentialSquaredRadiusLaw_lintegral n k V hV g hg

theorem rawRadialConfinementLaw_eq_full (n k : ℕ) (Q : ℝ → ℝ)
    (hQ : Continuous Q) : rawRadialConfinementLaw n k Q =
      (volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal (radialConfinementDensity n k Q r))
          := by
  rw [rawRadialConfinementLaw, ← restrict_withDensity measurableSet_Ioi]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_withDensity_iff (radialConfinementDensity_continuous n k hQ).measurable.ennreal_ofReal]
  apply Filter.Eventually.of_forall
  intro r hr
  by_contra hn
  have hz := radialConfinementDensity_zero n k Q (le_of_not_gt hn)
  exact hr (by rw [hz]; simp)

theorem rawRadialConfinementLaw_mass (n k : ℕ) (Q : ℝ → ℝ)
    (hQ : Continuous Q) (hi : Integrable (radialConfinementDensity n k Q) volume) :
    rawRadialConfinementLaw n k Q univ = ENNReal.ofReal (∫ r, radialConfinementDensity n k Q r) :=
        by
  rw [rawRadialConfinementLaw_eq_full n k Q hQ, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (radialConfinementDensity_nonneg n k Q))).symm

theorem radialConfinementProbabilityDensity_eq_normalizedLaw (n k : ℕ) (Q : ℝ → ℝ)
    (hQ : Continuous Q) (hi : Integrable (radialConfinementDensity n k Q) volume) :
    (volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal (radialConfinementProbabilityDensity n
        k Q r)) =
      (rawRadialConfinementLaw n k Q univ)⁻¹ • rawRadialConfinementLaw n k Q := by
  rw [rawRadialConfinementLaw_mass n k Q hQ hi, rawRadialConfinementLaw_eq_full n k Q hQ]
  rw [← withDensity_smul _ (radialConfinementDensity_continuous n k hQ).measurable.ennreal_ofReal]
  congr 1
  ext r
  change ENNReal.ofReal (radialConfinementDensity n k Q r /
    ∫ t, radialConfinementDensity n k Q t) =
      (ENNReal.ofReal (∫ t, radialConfinementDensity n k Q t))⁻¹ *
        ENNReal.ofReal (radialConfinementDensity n k Q r)
  rw [ENNReal.ofReal_div_of_pos (radialConfinementDensity_mass_pos n k Q hi),
    div_eq_mul_inv, mul_comm]

/-- The normalized radial density has exactly the existing squared-radius law
under r↦r². Normalization cancels the Jacobian's factor two. -/
theorem radialConfinementProbabilityDensity_square_map (n k : ℕ) (V : Potential)
    (hV : Continuous V)
    (hi : Integrable (radialConfinementDensity n k (fun r : ℝ => V (r : ℂ))) volume) :
    ((volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal
      (radialConfinementProbabilityDensity n k (fun t : ℝ => V (t : ℂ)) r))).map (fun r => r ^ 2) =
      potentialSquaredRadiusLaw n k V := by
  let R := rawRadialConfinementLaw n k (fun r : ℝ => V (r : ℂ))
  have hS := rawPotentialSquaredRadiusLaw_eq_square_map n k V hV
  have hmass : rawPotentialSquaredRadiusLaw n k V univ = 2 * R univ := by
    rw [hS, smul_apply, smul_eq_mul, Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp only [preimage_univ]
    rfl
  rw [radialConfinementProbabilityDensity_eq_normalizedLaw n k (fun r : ℝ => V (r : ℂ))
    (hV.comp Complex.continuous_ofReal) hi,
    Measure.map_smul _ ((show Measurable (fun r : ℝ => r ^ 2) by fun_prop).aemeasurable),
    potentialSquaredRadiusLaw, hmass, hS, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
    (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
  rw [mul_assoc, mul_comm (R univ)⁻¹, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), one_mul]

/-- The actual normalized positive-radius law is the square-root pushforward
of the normalized non-quadratic Kostlan squared-radius law. -/
theorem radialConfinementProbabilityDensity_eq_sqrt_map (n k : ℕ) (V : Potential)
    (hV : Continuous V)
    (hi : Integrable (radialConfinementDensity n k (fun r : ℝ => V (r : ℂ))) volume) :
    (volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal
      (radialConfinementProbabilityDensity n k (fun t : ℝ => V (t : ℂ)) r)) =
      (potentialSquaredRadiusLaw n k V).map Real.sqrt := by
  rw [← radialConfinementProbabilityDensity_square_map n k V hV hi,
    Measure.map_map Real.continuous_sqrt.measurable (by fun_prop)]
  have he : (fun r : ℝ => Real.sqrt (r ^ 2)) =ᵐ[
      (volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal
        (radialConfinementProbabilityDensity n k (fun t : ℝ => V (t : ℂ)) r))] id := by
    apply (ae_withDensity_iff
      (radialConfinementProbabilityDensity_continuous n k
        (Q := fun t : ℝ => V (t : ℂ)) (hV.comp
            Complex.continuous_ofReal)).measurable.ennreal_ofReal).mpr
    apply Filter.Eventually.of_forall
    intro r hr
    have hrpos : 0 < r := by
      by_contra hn
      have hz := radialConfinementDensity_zero n k (fun t : ℝ => V (t : ℂ)) (le_of_not_gt hn)
      exact hr (by simp [radialConfinementProbabilityDensity, hz])
    simp [Real.sqrt_sq_eq_abs, abs_of_pos hrpos]
  change _ = Measure.map (fun r : ℝ => Real.sqrt (r ^ 2)) _
  rw [Measure.map_congr he, Measure.map_id]

end
end GinibrePoincare
