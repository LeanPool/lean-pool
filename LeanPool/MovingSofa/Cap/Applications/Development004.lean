/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Bounds.Applications.Development002
/-!
# Moving sofa: related mathematical developments

* `Cap.Injectivity`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The injectivity condition for balanced maximum caps

Every balanced maximum cap of rotation angle `π / 2` satisfies the injectivity condition: its
surface measure has densities that are unique up to null sets, its inner corner is continuously
differentiable, and the two frame components of the corner velocity have strict signs on the open
rotation interval.

The theorem lives downstream of `MovingSofa/Cap/Regularity.lean` because its inputs
`balancedMaximumCap_hasDensities` and `balancedMaximumCap_arm_gt_one` depend on that module.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem balancedMaximumCap_injectivity (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) : SatisfiesInjectivityCondition K := by
  obtain ⟨hD, hf, hg⟩ := balancedMaximumCap_arm_gt_one K hK
  obtain ⟨-, -, -, -, hC1, -, hderiv⟩ := nondegenerateCap_continuity K hD
  refine ⟨balancedMaximumCap_hasDensities K hK, hC1, fun t ht ↦ ?_⟩
  have hmem : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨ht.1.le, ht.2.le⟩
  have hvn : inner ℝ (tangentVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm]; exact inner_normalVector_tangentVector t
  rw [(hderiv ⟨t, hmem⟩).1.derivWithin (uniqueDiffOn_Icc (by positivity) t hmem)]
  refine ⟨?_, ?_⟩
  · have h := hf ⟨t, hmem⟩ ht.1
    simp only [inner_add_left, real_inner_smul_left, inner_normalVector_self, hvn, mul_one,
      mul_zero, add_zero]
    linarith
  · have h := hg ⟨t, hmem⟩ ht.2
    simp only [inner_add_left, real_inner_smul_left, inner_normalVector_tangentVector,
      inner_tangentVector_self, mul_one, mul_zero, zero_add]
    linarith

end MovingSofa

end

end

end
