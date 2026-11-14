/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepTriangle
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourFinalInterior
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepThreeWindows

/-!
# RootPayloadPrefix

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. Item (f): the `toNat` cast bridge, named -/

/-- **The `toNat` cast bridge.**  For `n ≤ m`, the real cast of the natural window
length is the real difference. -/
theorem toNat_sub_cast_real {m n : ℤ} (h : n ≤ m) :
    (((m - n).toNat : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
  have h0 : ((m - n).toNat : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
  exact_mod_cast congrArg (fun w : ℤ => (w : ℝ)) h0

/-! ## 3. Item (d): the affine-minimizer family on the Step-3 windows -/

/-- **Item (d), proved: the affine-minimizer family exists.**

Every Step-4/6 producer binds a pair `(c, slope) : (ℤ → ℝ) × (ℤ → Vec d)`
minimizing the affine distance on `stepThreeWindow z m j` for all `j ≤ m`.  The
family is built scale by scale from the proved
`ExcessDecay.exists_isAffineMinimizer_truncatedWindow` — `stepThreeWindow` IS
`truncatedWindow` by definition — with the `H¹` datum's own `L²` membership
restricted to the window. -/
theorem exists_stepThreeWindow_affineMinimizerFamily {m : ℤ} {z : Vec d}
    (hzm : z ∈ openCubeSet (originCube d m))
    (u : H1Function (openCubeSet (originCube d m))) :
    ∃ (c : ℤ → ℝ) (slope : ℤ → Vec d),
      ∀ j : ℤ, j ≤ m →
        Support.IsAffineMinimizer (stepThreeWindow z m j) u.toFun (c j) (slope j) := by
  classical
  have hex : ∀ j : ℤ, ∃ p : ℝ × Vec d,
      j ≤ m →
        Support.IsAffineMinimizer (stepThreeWindow z m j) u.toFun p.1 p.2 := by
    intro j
    by_cases hj : j ≤ m
    · obtain ⟨cj, gj, hcg⟩ :=
        exists_isAffineMinimizer_truncatedWindow (m := m) (k := j) hzm (by omega)
          (u := u.toFun)
          (u.memL2.mono_measure
            (Measure.restrict_mono (truncatedWindow_subset_domain z m j) le_rfl))
      exact ⟨(cj, gj), fun _ => hcg⟩
    · exact ⟨(0, 0), fun hcontra => absurd hcontra hj⟩
  exact ⟨fun j => (hex j).choose.1, fun j => (hex j).choose.2,
    fun j hj => (hex j).choose_spec hj⟩

end

end Algsuperdiff.Section4.Provider.Regularity
