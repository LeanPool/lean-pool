/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialVandermondeDensity.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CollisionNull

/-!
# General potential Vandermonde density

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialVandermondeMultiplier_withDensity`,
`potentialMeasure_absolutelyContinuous_configurationVolume`,
`potentialVandermondeMultiplier_ne_zero_ae`, `potentialVandermondeMultiplier_normSq`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
namespace GinibrePoincare
noncomputable section

/-- The multiplier `Z^(-1/2) * Δ(z) * exp (-n ∑ i, V (z i) / 2)`, where `Δ` is the Vandermonde
determinant and `Z` the partition function `potentialPartition n V`. -/
def potentialVandermondeMultiplier (n : ℕ) (V : Potential) (z : Configuration n) : ℂ :=
  ((Real.sqrt (potentialPartition n V).toReal : ℂ)⁻¹) * vandermonde z *
    (Real.exp (-(n : ℝ) * (∑ i, V (z i)) / 2) : ℂ)

theorem potentialVandermondeMultiplier_continuous (n : ℕ) {V : Potential}
    (hV : Continuous V) : Continuous (potentialVandermondeMultiplier n V) := by
  unfold potentialVandermondeMultiplier
  apply Continuous.mul ((continuous_vandermonde.const_mul _))
  apply Complex.continuous_ofReal.comp
  apply Real.continuous_exp.comp
  exact ((continuous_finsetSum Finset.univ (fun (i : Fin n) _ => hV.comp (continuous_apply
      i))).const_mul (-(n : ℝ))).div_const 2

theorem configurationVolume_absolutelyContinuous_potentialMeasure (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤) :
    configurationVolume n ≪ potentialMeasure n V := by
  unfold potentialMeasure rawPotentialMeasure
  apply (withDensity_absolutelyContinuous' (measurable_potentialDensity n hV).aemeasurable _).trans
    (Measure.absolutelyContinuous_smul (ENNReal.inv_ne_zero.mpr hfin.ne))
  have hf : ∀ᵐ z ∂configurationVolume n, z ∉ collisionSet n := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using configurationVolume_collisionSet hn
  filter_upwards [hf] with z hz
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (potentialWeight_nonneg n V z)
    (Ne.symm ((potentialWeight_eq_zero_iff n V z).not.mpr hz))))

theorem potentialVandermondeMultiplier_enorm_sq (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (_ : potentialPartition n V < ⊤)
    (z : Configuration n) :
    ‖potentialVandermondeMultiplier n V z‖ₑ ^ (2 : ℝ) =
      (potentialPartition n V)⁻¹ * ENNReal.ofReal (potentialWeight n V z) := by
  have hpos := potentialPartition_pos n hn hV
  have hsquare (x : ℂ) : ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (Complex.normSq x) := by
    rw [ENNReal.rpow_two, ← Complex.sq_norm]
    simp
  let S : ℝ := (∑ i, V (z i))
  have he : Real.exp (-(n : ℝ) * S / 2) ^ 2 = Real.exp (-(n : ℝ) * S) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hs : Real.sqrt (potentialPartition n V).toReal ^ 2 = (potentialPartition n V).toReal :=
    Real.sq_sqrt ENNReal.toReal_nonneg
  rw [hsquare]
  unfold potentialVandermondeMultiplier
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_inv,
    Complex.normSq_ofReal, Complex.normSq_ofReal]
  simp only [← pow_two, hs]
  rw [mul_assoc, ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  have hi : ENNReal.ofReal ((potentialPartition n V).toReal⁻¹) = (potentialPartition n V)⁻¹ := by
    rw [← ENNReal.toReal_inv]
    exact ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hpos.ne')
  rw [hi]
  congr 1
  unfold potentialWeight vandermondeWeight
  simp only [neg_mul] at he ⊢
  dsimp only [S] at he
  rw [he, mul_comm]

theorem potentialVandermondeMultiplier_withDensity (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤) :
    (configurationVolume n).withDensity
      (fun z => ‖potentialVandermondeMultiplier n V z‖ₑ ^ (2 : ℝ)) =
      potentialMeasure n V := by
  simp_rw [potentialVandermondeMultiplier_enorm_sq n hn hV hfin]
  unfold potentialMeasure rawPotentialMeasure
  exact withDensity_smul _ (measurable_potentialDensity n hV)

theorem potentialMeasure_absolutelyContinuous_configurationVolume (n : ℕ) (V : Potential) :
    potentialMeasure n V ≪ configurationVolume n := by
  unfold potentialMeasure rawPotentialMeasure
  exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

theorem potentialVandermondeMultiplier_ne_zero_ae (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤) :
    ∀ᵐ z ∂configurationVolume n, potentialVandermondeMultiplier n V z ≠ 0 := by
  have hf : ∀ᵐ z ∂configurationVolume n, z ∉ collisionSet n := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using configurationVolume_collisionSet hn
  filter_upwards [hf] with z hz
  have hZ : Real.sqrt (potentialPartition n V).toReal ≠ 0 :=
    (Real.sqrt_pos.mpr (ENNReal.toReal_pos (potentialPartition_pos n hn hV).ne' hfin.ne)).ne'
  unfold potentialVandermondeMultiplier
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hZ))
    ((vandermonde_eq_zero_iff z).not.mpr hz))
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

theorem potentialVandermondeMultiplier_normSq (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (z : Configuration n) :
    Complex.normSq (potentialVandermondeMultiplier n V z) =
      (potentialPartition n V).toReal⁻¹ * potentialWeight n V z := by
  have he := congrArg ENNReal.toReal (potentialVandermondeMultiplier_enorm_sq n hn hV hfin z)
  simpa [eNorm, ENNReal.rpow_two, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (potentialWeight_nonneg n V z), Complex.sq_norm] using he

end
end GinibrePoincare
