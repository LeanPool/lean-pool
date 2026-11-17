/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeExtensionBounds.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeForcingExtension

/-!
# A fixed inverse arithmetic bound through extensions

The forward image of the old zero-jump remains unchanged in every extension.
Consequently the inverse value at a join x is bounded by five jumps of x join
B, where B is any fixed representative of that old image. The bound does not
supply a uniform program index; it is the input to the later generic program
selection argument.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeExtensionBounds

open OracleJump PersistentRestrictions ConePersistence ConePresentation

noncomputable section

/-- Any extension has inverse values bounded using the same old oracle B. -/
theorem inverse_bound_of_extension {I J : CountableIdeal} {a : Degree}
    (ρ : I ≃o Cone I a) (σ : J ≃o Cone J a)
    (hIJ : I.carrier ⊆ J.carrier) (he : ConePersistence.Extends hIJ ρ σ)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (B : Oracle) (hB : degree B = (ρ ⟨degree (jump FixedArithmetic.zero), hz⟩).val)
    (X : Oracle) (hX : degree X ∈ J.carrier) :
    ∃ Y : Oracle,
      degree Y = (σ.symm ⟨a ⊔ degree X,
        J.join_mem (ConePresentation.base_mem σ) hX, le_sup_left⟩).val ∧
      Reduces Y (iterate (join X B) 5) := by
  have haJ := ConePresentation.base_mem σ
  let τ := ConePresentation.lift σ haJ
  let z : PersistentLocality.ideal J :=
    ⟨degree (jump FixedArithmetic.zero), hIJ hz⟩
  let y : Set.Ici (⟨a, haJ⟩ : PersistentLocality.ideal J) :=
    ⟨⟨a ⊔ degree X, J.join_mem haJ hX⟩, by
      change a ≤ a ⊔ degree X
      exact le_sup_left⟩
  obtain ⟨Y, Z, hY, hZ, hYZ⟩ := ConeIdealLocality.inverse_arithmetic τ z rfl y
  have hb : ConeIdealCoding.image τ z = degree B := by
    change (σ ⟨degree (jump FixedArithmetic.zero), hIJ hz⟩).val = degree B
    exact (he ⟨degree (jump FixedArithmetic.zero), hz⟩).trans hB.symm
  have haB : a ≤ degree B :=
    hB.symm ▸ (ρ ⟨degree (jump FixedArithmetic.zero), hz⟩).property.2
  have hZB : Reduces Z (join X B) := by
    change degree Z ≤ degree X ⊔ degree B
    rw [hZ, hb]
    exact sup_le (sup_le (haB.trans le_sup_right) le_sup_left) le_sup_right
  exact ⟨Y, hY, reduces_trans hYZ (iterate_mono hZB 5)⟩

/-- The estimate holds for every representative of the inverse degree,
not only the representative produced by the decoder. -/
theorem representative_bound_of_extension {I J : CountableIdeal} {a : Degree}
    (ρ : I ≃o Cone I a) (σ : J ≃o Cone J a)
    (hIJ : I.carrier ⊆ J.carrier) (he : ConePersistence.Extends hIJ ρ σ)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (B : Oracle) (hB : degree B = (ρ ⟨degree (jump FixedArithmetic.zero), hz⟩).val)
    (X Y : Oracle) (hX : degree X ∈ J.carrier)
    (hY : degree Y = (σ.symm ⟨a ⊔ degree X,
      J.join_mem (ConePresentation.base_mem σ) hX, le_sup_left⟩).val) :
    Reduces Y (iterate (join X B) 5) := by
  obtain ⟨Z, hZ, hbound⟩ := inverse_bound_of_extension ρ σ hIJ he hz B hB X hX
  exact reduces_trans ((degree_eq_iff Y Z).mp (hY.trans hZ.symm)).1 hbound

end
end OAI.TuringRigidity.ConeExtensionBounds
