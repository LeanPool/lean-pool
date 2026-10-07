/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionBundleParts

/-!
# Square integrability of smooth space-time tests

A compactly supported smooth test and each first spatial derivative
are square integrable on every measurable time slab. These test
classes pass the ordered weak-derivative identities to limits.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A compactly supported smooth scalar test and all first spatial
partials belong to `L²` on an arbitrary time slab
(`prop:lps-smoothing`). -/
theorem lps_spaceTimeTest_spatial_memLp_two
    {φ : ParabolicPoint → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => φ p))
    (hφc : HasCompactSupport (fun p : Vec3 × ℝ => φ p))
    (I : Set ℝ) :
    MemLp φ 2 (volume.restrict (spaceTimeSet univ I)) ∧
      ∀ j : Fin 3, MemLp (fun z => spatialPartial φ j z)
        2 (volume.restrict (spaceTimeSet univ I)) := by
  let ψ : Vec3 × ℝ → ℝ := fun p => φ p
  have hφmem : MemLp φ 2 (volume.restrict (spaceTimeSet univ I)) := by
    exact (hφ.continuous.memLp_of_hasCompactSupport
      (μ := (volume : Measure (Vec3 × ℝ))) hφc).restrict _
  have hDψc (v : Vec3 × ℝ) :
      Continuous (fun p => fderiv ℝ ψ p v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDψs (v : Vec3 × ℝ) :
      HasCompactSupport (fun p => fderiv ℝ ψ p v) :=
    hφc.fderiv_apply (𝕜 := ℝ) v
  refine ⟨hφmem, fun j => ?_⟩
  have heq : (fun z : ParabolicPoint => spatialPartial φ j z) =
      fun p => fderiv ℝ ψ p (basisVec j, 0) :=
    funext fun z => spatialPartial_eq_fderiv_apply hφ j z.1 z.2
  rw [heq]
  exact ((hDψc _).memLp_of_hasCompactSupport
    (μ := (volume : Measure (Vec3 × ℝ))) (hDψs _)).restrict _

end ESS
