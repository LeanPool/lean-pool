/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpacetimeTestTranslation

/-!
# The translated physical vacuum system on the same Hilbert space

Translation relabels the original Weyl operators and keeps the same unit
vacuum. Every model field is proved from the literal test transformation.
The resulting local algebra is the original algebra of the translated set.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {m : ℝ}

/-- Translated. -/
def FreeFieldVacuum.translated (V : FreeFieldVacuum m H) (a : Spacetime) :
    FreeFieldVacuum m H where
  weyl F := V.weyl (spacetimeTranslate a F)
  vacuum := V.vacuum
  weyl_mem_unitary F := V.weyl_mem_unitary _
  weyl_mul F G := by
    rw [spacetimeTranslate_add, ← oneParticleInner_spacetimeTranslate m a F G]
    exact V.weyl_mul _ _
  vacuum_norm := V.vacuum_norm
  vacuum_weyl F := by
    rw [V.vacuum_weyl, oneParticleInner_spacetimeTranslate]
  cyclic := by
    have hrange : (Set.range fun F => V.weyl (spacetimeTranslate a F) V.vacuum) =
        Set.range fun F => V.weyl F V.vacuum := by
      ext x
      constructor
      · rintro ⟨F, rfl⟩
        exact ⟨spacetimeTranslate a F, rfl⟩
      · rintro ⟨F, rfl⟩
        exact ⟨spacetimeTranslate (-a) F,
          congrArg (fun G => V.weyl G V.vacuum) (spacetimeTranslate_cancel_neg a F)⟩
    change (Submodule.span ℂ (Set.range fun F =>
      V.weyl (spacetimeTranslate a F) V.vacuum)).topologicalClosure = ⊤
    rw [hrange]
    exact V.cyclic

theorem FreeFieldVacuum.localAlgebra_translated (V : FreeFieldVacuum m H)
    (a : Spacetime) (O : Set Spacetime) :
    localAlgebra (V.translated a) O = localAlgebra V ((fun x => x - a) ⁻¹' O) := by
  unfold localAlgebra
  congr 1
  ext A
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine ⟨spacetimeTranslate a F, ?_, rfl⟩
    intro x hx
    rw [tsupport_spacetimeTranslate] at hx
    exact hF hx
  · rintro ⟨G, hG, rfl⟩
    refine ⟨spacetimeTranslate (-a) G, ?_, ?_⟩
    · intro x hx
      rw [tsupport_spacetimeTranslate] at hx
      have h := hG hx
      change (x - -a) - a ∈ O at h
      simpa only [sub_neg_eq_add, add_sub_cancel_right] using h
    · change V.weyl G = V.weyl (spacetimeTranslate a (spacetimeTranslate (-a) G))
      rw [spacetimeTranslate_cancel_neg]

theorem FreeFieldVacuum.localAlgebra_translated_doubleCone_zero
    (V : FreeFieldVacuum m H) (a : Spacetime) (R : ℝ) :
    localAlgebra (V.translated a) (doubleCone 0 R) = localAlgebra V (doubleCone a R) := by
  rw [V.localAlgebra_translated]
  congr 1
  ext x
  simp only [Set.mem_preimage, doubleCone, Set.mem_ofPred_eq,
    Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, sub_zero]

end VacuumBellSeparation
