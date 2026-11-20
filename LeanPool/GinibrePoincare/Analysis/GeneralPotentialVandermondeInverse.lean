/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialVandermondeInverse.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialVandermondeL2

/-!
# General potential Vandermonde inverse

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialInverseVandermonde_lintegral`, `potentialInverseVandermonde_memLp`,
`potentialVandermondeL2_surjective`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
namespace GinibrePoincare
noncomputable section

/-- The function `z ↦ (potentialVandermondeMultiplier n V z)⁻¹ * v z`, dividing an `L²` function
of Lebesgue measure by the Vandermonde multiplier. -/
def potentialInverseVandermondeFunction (n : ℕ) (V : Potential)
    (v : Lp ℂ 2 (configurationVolume n)) : Configuration n → ℂ :=
  fun z => (potentialVandermondeMultiplier n V z)⁻¹ * v z

theorem potentialInverseVandermonde_lintegral (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (v : Lp ℂ 2 (configurationVolume n)) :
    (∫⁻ z, ‖potentialInverseVandermondeFunction n V v z‖ₑ ^ (2 : ℝ) ∂potentialMeasure n V) =
      ∫⁻ z, ‖v z‖ₑ ^ (2 : ℝ) ∂configurationVolume n := by
  let m := potentialVandermondeMultiplier n V
  let d := fun z => ‖m z‖ₑ ^ (2 : ℝ)
  have hd : Measurable d :=
    (ENNReal.continuous_rpow_const.comp (potentialVandermondeMultiplier_continuous n
        hV).enorm).measurable
  have ht : ∀ᵐ z ∂configurationVolume n, d z < ⊤ := by
    apply Filter.Eventually.of_forall
    intro z
    dsimp only [d, m]
    rw [potentialVandermondeMultiplier_enorm_sq n hn hV hfin]
    exact ENNReal.mul_lt_top (ENNReal.inv_ne_top.mpr (potentialPartition_pos n hn hV).ne').lt_top
      ENNReal.ofReal_lt_top
  rw [← potentialVandermondeMultiplier_withDensity n hn hV hfin]
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hd ht]
  apply lintegral_congr_ae
  filter_upwards [potentialVandermondeMultiplier_ne_zero_ae n hn hV hfin] with z hz
  change ‖m z‖ₑ ^ (2 : ℝ) * ‖(m z)⁻¹ * v z‖ₑ ^ (2 : ℝ) = ‖v z‖ₑ ^ (2 : ℝ)
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← enorm_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]

theorem potentialInverseVandermonde_memLp (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (v : Lp ℂ 2 (configurationVolume n)) :
    MemLp (potentialInverseVandermondeFunction n V v) 2 (potentialMeasure n V) := by
  have hf : AEStronglyMeasurable (potentialInverseVandermondeFunction n V v)
      (potentialMeasure n V) :=
    (potentialVandermondeMultiplier_continuous n hV).measurable.inv.aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable v).mono_ac
        (potentialMeasure_absolutelyContinuous_configurationVolume n V))
  rw [memLp_iff, eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hf,
    eLpNorm'_eq_lintegral_enorm]
  norm_num only [ENNReal.toReal_ofNat]
  rw [potentialInverseVandermonde_lintegral n hn hV hfin v]
  have hv := (Lp.memLp v).eLpNorm_lt_top
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (Lp.aestronglyMeasurable v),
    eLpNorm'_eq_lintegral_enorm] at hv
  exact hv

theorem potentialVandermondeL2_surjective (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤) :
    Function.Surjective (potentialVandermondeL2 n hn hV hfin) := by
  intro v
  let hm := potentialInverseVandermonde_memLp n hn hV hfin v
  let w := hm.toLp (potentialInverseVandermondeFunction n V v)
  refine ⟨w, ?_⟩
  apply Lp.ext
  filter_upwards [potentialVandermondeL2_coeFn_public n hn hV hfin w,
    (configurationVolume_absolutelyContinuous_potentialMeasure n hn hV hfin).ae_eq hm.coeFn_toLp,
    potentialVandermondeMultiplier_ne_zero_ae n hn hV hfin] with z hz hw hmz
  rw [hz]
  change _ * hm.toLp _ z = _
  rw [hw]
  change _ * ((potentialVandermondeMultiplier n V z)⁻¹ * v z) = _
  rw [← mul_assoc, mul_inv_cancel₀ hmz, one_mul]

/-- The genuine normalized Vandermonde gauge unitary for the actual
nonquadratic log-gas and unweighted configuration Lebesgue space. -/
def potentialVandermondeL2Equiv (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤) :
    Lp ℂ 2 (potentialMeasure n V) ≃ₗᵢ[ℂ] Lp ℂ 2 (configurationVolume n) :=
  LinearIsometryEquiv.ofSurjective (potentialVandermondeL2 n hn hV hfin)
    (potentialVandermondeL2_surjective n hn hV hfin)

end
end GinibrePoincare
