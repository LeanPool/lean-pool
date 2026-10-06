/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientFiber
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessFiniteRank

/-!
# Compactness Gradient Energy

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- Finite integrated spatial gradient energy gives `L²` membership of the
matrix field in its Hilbert carrier. -/
theorem memLp_gradient_fiber_of_integrated_energy
    {K : Set Vec3} {J : Set ℝ}
    (u : (Vec3 × ℝ) → Vec3)
    (Du : (Vec3 × ℝ) → Fin 3 → Vec3)
    (hDuMeas : Measurable Du)
    (henergy : (∫⁻ t in J, ∫⁻ x in K,
      ENNReal.ofReal (CKN.spatialGradientSq u Du (x,t)) ∂volume) < ⊤) :
    MemLp (fun z : (Vec3 × ℝ) => toCompactnessGradientFiber (Du z)) 2
      ((volume.restrict K).prod (volume.restrict J)) := by
  let F : (Vec3 × ℝ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (CKN.spatialGradientSq u Du z)
  have hF : Measurable F := by
    unfold F CKN.spatialGradientSq
    fun_prop
  have hμeq : (volume.restrict K).prod (volume.restrict J) =
      (volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ J) := by
    change (volume.restrict K).prod (volume.restrict J) =
      ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (K ×ˢ J)
    rw [Measure.prod_restrict]
  have hfinite : (∫⁻ z : (Vec3 × ℝ), F z
      ∂((volume.restrict K).prod (volume.restrict J))) < ⊤ := by
    rw [hμeq]
    change (∫⁻ z in K ×ˢ J, F z ∂(volume : Measure ParabolicPoint)) < ⊤
    rw [lintegral_parabolic_rectangle_eq_iterated F hF]
    exact henergy
  let g : (Vec3 × ℝ) → CompactnessGradientFiber := fun z =>
    toCompactnessGradientFiber (Du z)
  have hg : Measurable g := by
    unfold g toCompactnessGradientFiber
    fun_prop
  have hpoint (z : (Vec3 × ℝ)) :
      ‖g z‖ₑ ^ (2 : ℝ) = F z := by
    calc
      ‖g z‖ₑ ^ (2 : ℝ) =
          ENNReal.ofReal ‖g z‖ ^ (2 : ℕ) := by
            norm_num [← ofReal_norm, ENNReal.rpow_natCast]
      _ = ENNReal.ofReal (‖g z‖ ^ 2) :=
        (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
      _ = F z := by
        unfold g F
        rw [norm_toCompactnessGradientFiber_sq u Du z]
  have hfinite' : (∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ)
      ∂((volume.restrict K).prod (volume.restrict J))) < ⊤ := by
    simpa only [hpoint] using hfinite
  have hsm : AEStronglyMeasurable g
      ((volume.restrict K).prod (volume.restrict J)) :=
    hg.aestronglyMeasurable
  have hnorm : MemLp (fun z => ‖g z‖) 2
      ((volume.restrict K).prod (volume.restrict J)) := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num) (by norm_num) hsm.norm]
    simpa [ENNReal.toReal_ofNat] using hfinite'
  exact (memLp_norm_iff hsm).mp hnorm

/-- An integrated spatial energy bound controls the corresponding Hilbert
`L²` norm with the same constant. -/
theorem norm_toLp_gradient_fiber_le
    {μ : Measure (Vec3 × ℝ)}
    (u : (Vec3 × ℝ) → Vec3)
    (Du : (Vec3 × ℝ) → Fin 3 → Vec3)
    (hf : MemLp (fun z => toCompactnessGradientFiber (Du z)) 2 μ)
    (G : ℝ≥0∞) (hG : G < ⊤)
    (henergy : (∫⁻ z,
      ENNReal.ofReal (CKN.spatialGradientSq u Du z) ∂μ) ≤ G) :
    ‖hf.toLp (fun z => toCompactnessGradientFiber (Du z))‖ ≤
      (G ^ (1 / 2 : ℝ)).toReal := by
  let g : (Vec3 × ℝ) → CompactnessGradientFiber := fun z =>
    toCompactnessGradientFiber (Du z)
  have hpoint (z : (Vec3 × ℝ)) :
      ‖g z‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (CKN.spatialGradientSq u Du z) := by
    calc
      ‖g z‖ₑ ^ (2 : ℝ) =
          ENNReal.ofReal ‖g z‖ ^ (2 : ℕ) := by
            norm_num [← ofReal_norm, ENNReal.rpow_natCast]
      _ = ENNReal.ofReal (‖g z‖ ^ 2) :=
        (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
      _ = _ := by
        unfold g
        rw [norm_toCompactnessGradientFiber_sq u Du z]
  have hroot : eLpNorm g 2 μ ≤ G ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num) (by norm_num) hf.aestronglyMeasurable]
    calc
      (∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) =
          (∫⁻ z, ENNReal.ofReal (CKN.spatialGradientSq u Du z) ∂μ) ^
            (1 / 2 : ℝ) := by
            congr 1
            exact lintegral_congr fun z => hpoint z
      _ ≤ G ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow henergy (by norm_num)
  rw [Lp.norm_toLp]
  exact ENNReal.toReal_mono
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hG.ne).ne hroot

end CKN.Leray
