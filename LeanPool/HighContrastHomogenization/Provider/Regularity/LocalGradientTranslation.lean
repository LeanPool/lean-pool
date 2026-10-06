/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LocalGradientTopology

/-!
# High-contrast homogenization: Provider.Regularity.LocalGradientTranslation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Translation of projective local gradients

Translating a local gradient class moves each exhaustion cube off centre, so a
compatible translate is read off a larger cube.  A fixed index shift, depending
only on the translation vector, suffices for every cube of the exhaustion, and
the resulting componentwise maps are norm-nonincreasing continuous linear maps.

They assemble into a translation operator on the projective carrier which is
linear, measurable, and compatible with the raw-field constructor.  This is the
covariance carrier for translation-covariant local gradient families.
-/

open scoped ENNReal

namespace HCPolySupport
namespace HighContrast

noncomputable section

open MeasureTheory

variable {d : ℕ}

/-! ## The cube-index shift of a translation -/

theorem exists_translationDepth (z : Vec d) :
    ∃ N : ℕ, 1 + 2 * ‖z‖ ≤ (3 : ℝ) ^ N :=
  ((tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 3)).eventually_ge_atTop (1 + 2 * ‖z‖)).exists

/-- An exhaustion-index shift large enough that translation by `z` carries
every centered cube into the shifted one. -/
@[expose]
def translationDepth (z : Vec d) : ℕ :=
  Classical.choose (exists_translationDepth z)

theorem translationDepth_spec (z : Vec d) :
    1 + 2 * ‖z‖ ≤ (3 : ℝ) ^ translationDepth z :=
  Classical.choose_spec (exists_translationDepth z)

/-- Translation by `z` carries the `n`th exhaustion cube into the cube shifted
by the translation depth. -/
theorem add_mem_localGradientCube (z : Vec d) (n : ℕ) {x : Vec d}
    (hx : x ∈ localGradientCube d n) :
    x + z ∈ localGradientCube d (n + translationDepth z) := by
  rw [localGradientCube, mem_openCubeSet_originCube_iff] at hx
  rw [localGradientCube, mem_openCubeSet_originCube_iff]
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  have hzi : |z i| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
  have ht0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hA1 : (1 : ℝ) ≤ (3 : ℝ) ^ (n : ℤ) := by
    rw [zpow_natCast]
    exact one_le_pow₀ (by norm_num)
  have hB : 1 + 2 * ‖z‖ ≤ (3 : ℝ) ^ ((translationDepth z : ℕ) : ℤ) := by
    rw [zpow_natCast]
    exact translationDepth_spec z
  have hcast : ((n + translationDepth z : ℕ) : ℤ) =
      (n : ℤ) + ((translationDepth z : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hcast, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  simp only [Pi.add_apply]
  set A : ℝ := (3 : ℝ) ^ (n : ℤ) with hAdef
  set B : ℝ := (3 : ℝ) ^ ((translationDepth z : ℕ) : ℤ) with hBdef
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA1
  have hAB : A * (1 + 2 * ‖z‖) ≤ A * B := mul_le_mul_of_nonneg_left hB hA0
  have hAt : ‖z‖ ≤ A * ‖z‖ := le_mul_of_one_le_left ht0 hA1
  have hexp : A * (1 + 2 * ‖z‖) = A + 2 * (A * ‖z‖) := by ring
  have hkey : (1 / 2 : ℝ) * A + ‖z‖ ≤ (1 / 2 : ℝ) * (A * B) := by
    linarith only [hAB, hAt, hexp]
  constructor
  · linarith only [hlo, neg_abs_le (z i), hzi, hkey]
  · linarith only [hhi, le_abs_self (z i), hzi, hkey]

/-! ## Translation on one local class -/

private theorem measurableSet_localGradientCube (d m : ℕ) :
    MeasurableSet (localGradientCube d m) :=
  (isOpen_openCubeSet (originCube d (m : ℤ))).measurableSet

private theorem measurePreserving_translate_localGradientCube (z : Vec d)
    (m : ℕ) :
    MeasurePreserving (fun x : Vec d => x + z)
      (volume.restrict ((fun x : Vec d => x + z) ⁻¹' localGradientCube d m))
      (volume.restrict (localGradientCube d m)) :=
  (measurePreserving_add_right volume z).restrict_preimage
    (measurableSet_localGradientCube d m)

private theorem subset_preimage_translate {z : Vec d} {n m : ℕ}
    (hsub : ∀ x ∈ localGradientCube d n, x + z ∈ localGradientCube d m) :
    localGradientCube d n ⊆ (fun x : Vec d => x + z) ⁻¹' localGradientCube d m :=
  fun x hx => hsub x hx

/-- A locally square-integrable vector field stays locally square-integrable
after translation. -/
theorem memVectorL2_translate_localGradientCube (z : Vec d) (f : Vec d → Vec d)
    (hf : ∀ n, MemVectorL2 (localGradientCube d n) f) (n : ℕ) :
    MemVectorL2 (localGradientCube d n) (fun x => f (x + z)) := by
  have hcomp := (hf (n + translationDepth z)).comp_measurePreserving
    (measurePreserving_translate_localGradientCube z (n + translationDepth z))
  exact hcomp.mono_measure (Measure.restrict_mono_set volume
    (subset_preimage_translate
      (fun _ hx => add_mem_localGradientCube z n hx)))

/-! ## Translation on the projective carrier -/

end

end HighContrast
end HCPolySupport
