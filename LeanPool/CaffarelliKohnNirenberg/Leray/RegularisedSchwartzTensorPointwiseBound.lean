/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzConvolutionBound
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzTensorBilinear

/-!
# Pointwise bilinear tensor bound

The mollifier L²-to-pointwise estimate controls the rank-one tensor
at each spatial point before taking its L² norm.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- One mollifier constant controls the pointwise tensor norm by the
first field's L² norm and the second field's pointwise norm. -/
theorem regularisedSchwartzTensorBilinear_pointwise_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g f : 𝓢(L2Vec3, ComplexVec3)) (x : L2Vec3),
        ‖regularisedSchwartzTensorBilinear ρ ε hε g f x‖ ≤
          C * ‖g.toLp 2‖ * ‖f x‖ := by
  obtain ⟨C, hC, hMollify⟩ :=
    regularisedSchwartzMollify_norm_le ρ ε hε
  refine ⟨C, hC, ?_⟩
  intro g f x
  rw [regularisedSchwartzTensorBilinear_apply,
    regularisedComplexTensorOuter_norm]
  exact mul_le_mul_of_nonneg_right (hMollify g x) (norm_nonneg _)

end CKN.Leray

end
