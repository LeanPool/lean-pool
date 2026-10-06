/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGrowthL2
public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Local quadratic data for Gaussian averages

The pointwise growth assumption supplies the missing local square integrability of the
field in `lem:bu-gaussian`.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The spatial domain in `lem:bu-gaussian`. -/
@[expose] abbrev buHalfSpace : Set Vec3 := {x : Vec3 | 0 < x 2}

/-- The open space-time domain in `lem:bu-gaussian`. -/
@[expose] abbrev buHalfCylinder : Set ParabolicPoint :=
  spaceTimeSet buHalfSpace (Ioo 0 1)

/-- The solution and its weak derivatives have finite local quadratic data under the
source hypotheses of `lem:bu-gaussian`. -/
theorem buGaussian_local_quadratic_l2
    (A : ℝ)
    (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtw : ParabolicPoint → Vec3)
    (hderiv : HasSpaceTimeWeakDerivs buHalfSpace (Ioo 0 1) w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint, S ⊆ buHalfCylinder → Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) +
        ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hgrowth : ∀ z ∈ buHalfCylinder,
      vec3EuclideanNorm (w z) ≤ Real.exp (A * vec3EuclideanNorm z.1 ^ 2)) :
    ∀ S : Set ParabolicPoint, S ⊆ buHalfCylinder → Bornology.IsBounded S →
      (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hA0pos : 0 < ((1 / (10 : ℝ) ^ 12) / 2) := by positivity
  have hAbar : 0 < max A ((1 / (10 : ℝ) ^ 12) / 2) :=
    hA0pos.trans_le (le_max_right _ _)
  have hgrowthBar : ∀ z ∈ buHalfCylinder,
      vec3EuclideanNorm (w z) ≤
        Real.exp (max A ((1 / (10 : ℝ) ^ 12) / 2) * vec3EuclideanNorm z.1 ^ 2) := by
    intro z hz
    apply le_trans (hgrowth z hz)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have hL2w := bu_growth_implies_local_l2
    (max A ((1 / (10 : ℝ) ^ 12) / 2)) hAbar w hgrowthBar
  intro S hS hSb
  have hWfin : (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    hL2w S (by simpa [buHalfCylinder] using hS) hSb
  have hDfin := hL2 S hS hSb
  let W : ParabolicPoint → ℝ≥0∞ := fun z => ‖w z‖ₑ ^ (2 : ℝ)
  let G : ParabolicPoint → ℝ≥0∞ := fun z =>
    ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)
  have hWmeas : AEMeasurable W (volume.restrict S) := by
    dsimp [W]
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (hderiv.1.mono_set hS |>.aestronglyMeasurable.enorm)
  have hsplit := lintegral_add_left' hWmeas
    (μ := volume.restrict S) (f := W) (g := G)
  have hsum : (∫⁻ z in S, W z + G z) < ⊤ := by
    rw [hsplit]
    exact ENNReal.add_lt_top.mpr ⟨hWfin, hDfin⟩
  apply lt_of_le_of_lt ?_ hsum
  apply lintegral_mono
  intro z
  simp only [W, G]
  exact le_of_eq (by ac_rfl)

end ESS
