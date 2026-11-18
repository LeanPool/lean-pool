/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConePersistentRestriction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConePersistentLocality

/-!
# Arithmetic restrictions without assuming persistence

Suppose a cone isomorphism on K extends a map on I, and J is an intermediate
countable jump ideal. If H presents J and H' belongs to K, locality restricts
the map to J and its entire indexed graph is recursive in H^(11).

Neither the map on K nor its restriction to J is assumed persistent. This is
the arithmetic candidate lemma needed to prove that a persistent extension
exists without reasoning in a circle. The whole arithmetic ideal J(H) need
not be contained in K: H' alone suffices for the coding argument.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConePersistentRestriction

open EncodedForcing OracleJump ArithmeticHierarchy PersistentRestrictions
open ConePersistence ConePresentation ConePersistentLocality

noncomputable section

/-- Restrict a possibly nonpersistent larger map and compute its index graph
from the eleventh jump of the intermediate ideal's presentation. -/
theorem restriction {a : Degree} {I J K : CountableIdeal}
    (ρ : I ≃o Cone I a) (τ : K ≃o Cone K a)
    (hIK : I.carrier ⊆ K.carrier) (he : ConePersistence.Extends hIK ρ τ)
    (hza : degreeJump a ∈ I.carrier)
    (hIJ : I.carrier ⊆ J.carrier) (hJK : J.carrier ⊆ K.carrier)
    (hjump : IdealLocality.JumpClosed (PersistentLocality.ideal J))
    {H : Oracle} (hpres : Presented J H)
    (hHK : degree (jump H) ∈ K.carrier) :
    ∃ σ : J ≃o Cone J a,
      ConePersistence.Extends hIJ ρ σ ∧ ConePersistence.Extends hJK σ τ ∧
      RecursivePred (iterate H 11) (ConePresentation.Graph σ hpres) := by
  obtain ⟨σ, hρ, hτ⟩ := restrict_extension ρ τ hIK he hza hIJ hJK hjump
  have haK := ConePresentation.base_mem τ
  let τ' := ConePresentation.lift τ haK
  let z₁ : Cone I a := ⟨degreeJump a, hza, degree_le_jump a⟩
  let zK : Set.Ici (⟨a, haK⟩ : PersistentLocality.ideal K) :=
    ⟨⟨degreeJump a, hIK hza⟩, Set.mem_Ici.mpr (degree_le_jump a)⟩
  have hpre : (τ'.symm zK).val ≤ degree H := by
    change (τ.symm ⟨z₁.val, hIK z₁.property.1, z₁.property.2⟩).val ≤ degree H
    rw [ConePersistence.extends_inverse he z₁]
    exact presentation_bound hpres (hIJ (ρ.symm z₁).property)
  have hH : degree H ∈ (PersistentLocality.ideal K).carrier :=
    K.lower (reduces_jump H) hHK
  let b : PersistentLocality.ideal K := ⟨degree (jump H), hHK⟩
  have hbound : ConeIdealCoding.image τ' b ≤ degree (iterate H 6) := by
    obtain ⟨X, Y, hX, hY, hXY⟩ := ConeIdealLocality.image_arithmetic τ' zK rfl b
    have hYH : Reduces Y (jump H) := by
      change degree Y ≤ degree (jump H)
      rw [hY]
      exact sup_le le_rfl (hpre.trans (reduces_jump H))
    rw [← hX]
    exact reduces_trans hXY (iterate_mono hYH 5)
  obtain ⟨_, hr⟩ := graph_sigma_of_bound τ' H hH
    (presentation_bound hpres (hIJ (zero_jump_mem hza))) b rfl
    (iterate H 6) (ConePresentation.reduces_iterate H 6) hbound
  have hgraph : ∀ v, IdealGraph τ' H hH v ↔ ConePresentation.Graph σ hpres v := by
    intro v
    change (τ ⟨degree (columns H (Nat.unpair v).1), _⟩).val =
      degree (columns H (Nat.unpair v).2) ↔ _
    exact Iff.of_eq (congrArg (fun x : Degree => x = degree (columns H (Nat.unpair v).2))
      (hτ (presentationEntry hpres (Nat.unpair v).1)))
  exact ⟨σ, hρ, hτ, Form.congr (n := 0) (s := true) hr hgraph⟩

end
end OAI.TuringRigidity.ConePersistentRestriction
