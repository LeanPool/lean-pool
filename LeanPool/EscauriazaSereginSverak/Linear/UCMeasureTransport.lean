/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffOperatorSq

/-!
# Almost-everywhere statements in product coordinates

The canonical space-time homeomorphism preserves the product Lebesgue
measure on a normalized cylinder.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS



/-- Integrability on a normalized CKN cylinder transfers to product
coordinates through the canonical homeomorphism. -/
theorem uc_integrableOn_parabolic_to_product
    (ρ : ℝ) {F : ParabolicPoint → ℝ}
    (hF : IntegrableOn F (ucCylinder ρ) volume) :
    IntegrableOn (fun z : Vec3 × ℝ => F (parabolicHomeomorph.symm z))
      (vec3Ball 0 ρ ×ˢ Ioo (0 : ℝ) 2) volume := by
  have h := (parabolicHomeomorphSymm_measurePreserving.integrableOn_comp_preimage
    parabolicHomeomorph.symm.measurableEmbedding
    (f := F) (s := ucCylinder ρ)).2 hF
  have hpre : parabolicHomeomorph.symm ⁻¹' ucCylinder ρ =
      vec3Ball 0 ρ ×ˢ Ioo (0 : ℝ) 2 := by
    ext z
    rfl
  rw [hpre] at h
  exact h


end ESS
