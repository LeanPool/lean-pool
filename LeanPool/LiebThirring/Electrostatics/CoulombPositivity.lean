/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.Basic
public import LeanPool.LiebThirring.Electrostatics.Gaussian
public import LeanPool.LiebThirring.Electrostatics.CoulombPositivityKernel
import all LeanPool.LiebThirring.Electrostatics.Basic

/-!
# Coulomb symmetry and positivity

The defining iterated integral, exposed without changing the shared definitions.

Symmetry by Tonelli; no energy-finiteness assumption is needed.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring

/-- The defining iterated integral, exposed without changing the shared definitions. -/
theorem coulombEnergy_eq_lintegral (α β : Measure Position) :
    coulombEnergy α β = ∫⁻ x, ∫⁻ y, coulombKernel x y ∂β ∂α := by
  rfl

/-- Symmetry by Tonelli; no energy-finiteness assumption is needed. -/
theorem coulombEnergy_symm (α β : Measure Position) [SFinite α] [SFinite β] :
    coulombEnergy α β = coulombEnergy β α := by
  rw [coulombEnergy_eq_lintegral, coulombEnergy_eq_lintegral,
    lintegral_lintegral_swap measurable_coulombKernel.aemeasurable]
  simp_rw [coulombKernel_symm]

/-- The Gaussian feature used to represent the Coulomb kernel. -/
@[expose] noncomputable def coulombFeature (x : Position) (u : ℝ × Position) : ℝ≥0∞ :=
  gaussianFeature (2 / Real.sqrt Real.pi) (u.1 ^ 2) x u.2

/-- The parameter-space measure for the Gaussian Coulomb representation. -/
@[expose] noncomputable def coulombFeatureMeasure : Measure (ℝ × Position) :=
  (volume.restrict (Ioi 0)).prod volume

/-- Joint measurability of the Coulomb feature. -/
theorem measurable_coulombFeature : Measurable (Function.uncurry coulombFeature) := by
  unfold coulombFeature gaussianFeature gaussianMass
  fun_prop

/-- The Coulomb kernel is an integral Gram kernel, including the diagonal. -/
theorem coulombKernel_eq_lintegral_feature (x y : Position) :
    coulombKernel x y =
      ∫⁻ u, coulombFeature x u * coulombFeature y u ∂coulombFeatureMeasure := by
  rw [coulombKernel_eq_lintegral_gaussian]
  rw [coulombFeatureMeasure, lintegral_prod _ (by
    exact ((measurable_coulombFeature.of_uncurry_left).mul
      (measurable_coulombFeature.of_uncurry_left)).aemeasurable)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [coulombFeature, mul_comm (t ^ 2), neg_mul] using
    (lintegral_gaussianFeature_mul (sq_pos_of_pos ht) (by positivity) x y).symm

instance : SFinite coulombFeatureMeasure := by
  unfold coulombFeatureMeasure
  infer_instance

/-- The nonnegative feature transform of a positive charge. -/
@[expose] noncomputable def coulombTransform (α : Measure Position) (u : ℝ × Position) : ℝ≥0∞ :=
  ∫⁻ x, coulombFeature x u ∂α

theorem measurable_coulombTransform (α : Measure Position) [SFinite α] :
    Measurable (coulombTransform α) :=
  measurable_coulombFeature.lintegral_prod_left

/-- Coulomb energies are integral Gram pairings of the feature transforms. -/
theorem coulombEnergy_eq_lintegral_transform (α β : Measure Position)
    [SFinite α] [SFinite β] :
    coulombEnergy α β = ∫⁻ u, coulombTransform α u * coulombTransform β u
      ∂coulombFeatureMeasure := by
  rw [coulombEnergy_eq_lintegral]
  simp_rw [coulombKernel_eq_lintegral_feature]
  exact lintegral_gram_pairing α β coulombFeatureMeasure coulombFeature
    measurable_coulombFeature

/-- Extended Coulomb Cauchy–Schwarz. S-finiteness suffices, even when energies are infinite. -/
theorem coulombEnergy_mul_self_le (α β : Measure Position) [SFinite α] [SFinite β] :
    coulombEnergy α β ^ 2 ≤ coulombEnergy α α * coulombEnergy β β := by
  simp only [coulombEnergy_eq_lintegral_transform, ← pow_two]
  exact lintegral_mul_sq_le coulombFeatureMeasure (measurable_coulombTransform α)
    (measurable_coulombTransform β)

/-- Finite self-energies imply finite mutual energy, without circular Coulomb Fubini. -/
theorem coulombEnergy_ne_top (α β : Measure Position) [SFinite α] [SFinite β]
    (hα : coulombEnergy α α ≠ ⊤) (hβ : coulombEnergy β β ≠ ⊤) :
    coulombEnergy α β ≠ ⊤ := by
  have h := coulombEnergy_mul_self_le α β
  intro htop
  rw [htop] at h
  norm_num at h
  exact ENNReal.mul_ne_top hα hβ h

/-- Positivity of the signed form for the difference of two finite-energy charges. -/
theorem two_mul_coulombEnergy_le (α β : Measure Position) [SFinite α] [SFinite β]
    (hα : coulombEnergy α α ≠ ⊤) (hβ : coulombEnergy β β ≠ ⊤) :
    2 * coulombEnergy α β ≤ coulombEnergy α α + coulombEnergy β β := by
  have hm := coulombEnergy_ne_top α β hα hβ
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by norm_num) hm)
    (ENNReal.add_ne_top.mpr ⟨hα, hβ⟩)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_add hα hβ]
  have hcs := ENNReal.toReal_mono (ENNReal.mul_ne_top hα hβ)
    (coulombEnergy_mul_self_le α β)
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul] at hcs
  have hnonneg := ENNReal.toReal_nonneg (a := coulombEnergy α β)
  have hsquare := sq_nonneg ((coulombEnergy α α).toReal - (coulombEnergy β β).toReal)
  have ha := ENNReal.toReal_nonneg (a := coulombEnergy α α)
  have hb := ENNReal.toReal_nonneg (a := coulombEnergy β β)
  nlinarith only [hcs, hnonneg, hsquare, ha, hb]

end LiebThirring

end
