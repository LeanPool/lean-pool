/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTensorPhysicalMap
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalMap

/-!
# Linearized complex physical tensor path

Fixing a complex physical L² path in the first factor gives a continuous
complex tensor path, linear in the second factor.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The clamped physical tensor path with a prescribed physical L²
first factor and an unknown complex physical second factor. -/
@[expose]
def regularisedComplexLinearTensorPath
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (g : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (v : C(RegularizedMildTimeInterval T,
      ComplexVectorL2)) :
    ℝ → ComplexTensorL2 :=
  fun s => regularisedTensorPhysicalMap ρ ε hε
    (g (regularizedMildTimeClamp T hT s))
    (v (regularizedMildTimeClamp T hT s))

/-- The prescribed L² path and complex physical path produce a
continuous physical tensor path. -/
theorem regularisedComplexLinearTensorPath_continuous
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (g : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (v : C(RegularizedMildTimeInterval T,
      ComplexVectorL2)) :
    Continuous (regularisedComplexLinearTensorPath ρ ε hε T hT g v) := by
  unfold regularisedComplexLinearTensorPath
  exact (regularisedTensorPhysicalMap ρ ε hε).continuous₂.comp₂
    (g.continuous.comp (regularizedMildTimeClamp_continuous T hT))
    (v.continuous.comp (regularizedMildTimeClamp_continuous T hT))

/-- A uniform physical L² bound makes the linearized tensor path
bounded linearly in the complex physical trajectory norm. -/
theorem regularisedComplexLinearTensorPath_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (g : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (v : C(RegularizedMildTimeInterval T,
      ComplexVectorL2))
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ q, ‖g q‖ ≤ B)
    (s : ℝ) :
    ‖regularisedComplexLinearTensorPath ρ ε hε T hT g v s‖ ≤
      regularisedTensorPhysicalConstant ρ ε hε * B * ‖v‖ := by
  let F := regularisedTensorPhysicalMap ρ ε hε
  let q := regularizedMildTimeClamp T hT s
  have hC := (regularisedTensorPhysicalMap_norm_le ρ ε hε).1
  change ‖F (g q) (v q)‖ ≤
    regularisedTensorPhysicalConstant ρ ε hε * B * ‖v‖
  calc
    ‖F (g q) (v q)‖ ≤ ‖F‖ * ‖g q‖ * ‖v q‖ := F.le_opNorm₂ _ _
    _ ≤ regularisedTensorPhysicalConstant ρ ε hε * B * ‖v q‖ := by
      have h1 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (regularisedTensorPhysicalMap_norm_le ρ ε hε).2
          (norm_nonneg (g q))) (norm_nonneg (v q))
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hg q) hC) (norm_nonneg (v q))
      exact h1.trans h2
    _ ≤ regularisedTensorPhysicalConstant ρ ε hε * B * ‖v‖ :=
      mul_le_mul_of_nonneg_left (v.norm_coe_le_norm q)
        (mul_nonneg hC hB)

/-- The physical tensor path is linear in its second trajectory. -/
theorem regularisedComplexLinearTensorPath_sub
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (g u v : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (s : ℝ) :
    regularisedComplexLinearTensorPath ρ ε hε T hT g (u - v) s =
      regularisedComplexLinearTensorPath ρ ε hε T hT g u s -
        regularisedComplexLinearTensorPath ρ ε hε T hT g v s := by
  simp only [regularisedComplexLinearTensorPath, ContinuousMap.sub_apply, map_sub]

end CKN.Leray

end
