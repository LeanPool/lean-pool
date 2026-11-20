/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialVandermondeL2.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialVandermondeDensity

/-!
# General potential Vandermonde L 2

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialVandermondeL2_coeFn_public`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
namespace GinibrePoincare
noncomputable section

private theorem potentialVandermonde_lintegral {n : ℕ}
    (hn : 0 < n) {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤) (u : Lp ℂ 2
        (potentialMeasure n V)) :
    (∫⁻ z, ‖potentialVandermondeMultiplier n V z * u z‖ₑ ^ (2 : ℝ)
      ∂configurationVolume n) =
      ∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ) ∂potentialMeasure n V := by
  let d := fun z : Configuration n ↦
    ‖potentialVandermondeMultiplier n V z‖ₑ ^ (2 : ℝ)
  have hd : Measurable d := by
    unfold d potentialVandermondeMultiplier
    exact (ENNReal.continuous_rpow_const.comp
      (potentialVandermondeMultiplier_continuous n hV).eNorm).measurable
  have hdtop : ∀ᵐ z ∂configurationVolume n, d z < ⊤ :=
    Filter.Eventually.of_forall fun z ↦ by
      unfold d
      rw [potentialVandermondeMultiplier_enorm_sq n hn hV hfin]
      exact ENNReal.mul_lt_top (ENNReal.inv_ne_top.mpr (potentialPartition_pos n hn hV).ne').lt_top
        (by  exact ENNReal.ofReal_ne_top.lt_top)
  calc
    _ = ∫⁻ z, d z * ‖u z‖ₑ ^ (2 : ℝ) ∂configurationVolume n := by
      apply lintegral_congr
      intro z
      unfold d
      rw [eNorm_mul, ENNReal.mul_rpow_of_nonneg]
      positivity
    _ = ∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ)
        ∂(configurationVolume n).withDensity d := by
      exact (lintegral_withDensity_eq_lintegral_mul_non_measurable
        _ hd hdtop _).symm
    _ = _ := by
      have hm := potentialVandermondeMultiplier_withDensity n hn hV hfin
      change (∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ)
        ∂(configurationVolume n).withDensity d) = _
      rw [hm]

theorem potentialVandermonde_memLp {n : ℕ}
    (hn : 0 < n) {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤) (u : Lp ℂ 2
        (potentialMeasure n V)) :
    MemLp (fun z ↦ potentialVandermondeMultiplier n V z * u z) 2
      (configurationVolume n) := by
  have hac := configurationVolume_absolutelyContinuous_potentialMeasure n hn hV hfin
  have hf : AEStronglyMeasurable
      (fun z ↦ potentialVandermondeMultiplier n V z * u z)
      (configurationVolume n) :=
    ((potentialVandermondeMultiplier_continuous n hV).aestronglyMeasurable).mul
      ((Lp.aestronglyMeasurable u).mono_ac hac)
  rw [memLp_iff]
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hf,
    eLpNorm'_eq_lintegral_eNorm]
  norm_num only [ENNReal.toReal_ofNat]
  rw [potentialVandermonde_lintegral hn hV hfin u]
  have hu := (Lp.memLp u).eLpNorm_lt_top
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (Lp.aestronglyMeasurable u),
    eLpNorm'_eq_lintegral_eNorm] at hu
  exact hu

theorem potentialVandermonde_norm {n : ℕ}
    (hn : 0 < n) {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤) (u : Lp ℂ 2
        (potentialMeasure n V)) :
    ‖(potentialVandermonde_memLp hn hV hfin u).toLp
        (fun z ↦ potentialVandermondeMultiplier n V z * u z)‖ = ‖u‖ := by
  simp only [Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (potentialVandermonde_memLp hn hV hfin u).coeFn_toLp]
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (potentialVandermonde_memLp hn hV hfin
      u).aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (Lp.aestronglyMeasurable u),
    eLpNorm'_eq_lintegral_eNorm, eLpNorm'_eq_lintegral_eNorm]
  norm_num only [ENNReal.toReal_ofNat]
  rw [potentialVandermonde_lintegral hn hV hfin u]

/-- Normalized multiplication by the Vandermonde as a genuine complex linear
isometry from the actual potential law’s `L²` into configuration Lebesgue `L²`. -/
def potentialVandermondeL2 (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤) :
    Lp ℂ 2 (potentialMeasure n V) →ₗᵢ[ℂ]
      Lp ℂ 2 (configurationVolume n) := by
  exact
    { toFun := fun u ↦ (potentialVandermonde_memLp hn hV hfin u).toLp
          (fun z ↦ potentialVandermondeMultiplier n V z * u z)
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [(potentialVandermonde_memLp hn hV hfin (u + v)).coeFn_toLp,
          (potentialVandermonde_memLp hn hV hfin u).coeFn_toLp,
          (potentialVandermonde_memLp hn hV hfin v).coeFn_toLp,
          (configurationVolume_absolutelyContinuous_potentialMeasure n hn hV hfin).ae_eq
            (Lp.coeFn_add u v),
          Lp.coeFn_add
            ((potentialVandermonde_memLp hn hV hfin u).toLp _)
            ((potentialVandermonde_memLp hn hV hfin v).toLp _)] with z huv hu hv hadd hout
        rw [huv, hout]
        simp only [Pi.add_apply] at hadd ⊢
        rw [hadd, hu, hv, mul_add]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [(potentialVandermonde_memLp hn hV hfin (c • u)).coeFn_toLp,
          (potentialVandermonde_memLp hn hV hfin u).coeFn_toLp,
          (configurationVolume_absolutelyContinuous_potentialMeasure n hn hV hfin).ae_eq
            (Lp.coeFn_smul c u),
          Lp.coeFn_smul c ((potentialVandermonde_memLp hn hV hfin u).toLp _)] with z hcu hu hin hout
        rw [hcu]
        simp only [RingHom.id_apply]
        rw [hout]
        simp only [Pi.smul_apply] at hin ⊢
        rw [hin, hu]
        simp only [smul_eq_mul]
        ring
      norm_map' := potentialVandermonde_norm hn hV hfin }

/-- Almost-everywhere representative of the actual normalized Vandermonde isometry. -/
theorem potentialVandermondeL2_coeFn_public (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (u : Lp ℂ 2 (potentialMeasure n V)) :
    (potentialVandermondeL2 n hn hV hfin u : Configuration n → ℂ) =ᵐ[configurationVolume n]
      fun z => potentialVandermondeMultiplier n V z * u z :=
  (potentialVandermonde_memLp hn hV hfin u).coeFn_toLp

end
end GinibrePoincare
