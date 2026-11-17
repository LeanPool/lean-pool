/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConePersistentLocality.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeIdealLocality
public import LeanPool.TuringConeRigidity.TuringTwoConePersistence
public import LeanPool.TuringConeRigidity.TuringConePresentation

/-!
# Prescribed jump-ideal extensions of persistent two-cone maps

The initial ideal contains both base jumps. Persistence first supplies an
extension to a larger ideal; two-sided locality restricts it to the prescribed
intermediate jump ideal. Both extension agreements are retained. The resulting
restriction is not yet claimed persistent or arithmetically presented.

For two-cone partial maps, the cone types could both be empty in an arbitrary
ideal. Base membership is therefore supplied explicitly (or follows from the
base-jump hypotheses), rather than inferred merely from an order isomorphism.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConePersistentLocality

open OracleJump ArithmeticHierarchy PersistentRestrictions IdealInterpretation
open ConePersistence (Cone)
open TwoConeIdealCodes (val)

noncomputable section

def lift {I : CountableIdeal} {a b : Degree} (ρ : Cone I a ≃o Cone I b)
    (ha : a ∈ I.carrier) (hb : b ∈ I.carrier) :
    Set.Ici (⟨a, ha⟩ : PersistentLocality.ideal I) ≃o
      Set.Ici (⟨b, hb⟩ : PersistentLocality.ideal I) :=
  (ConePresentation.coneBridge I a ha).symm.trans
    (ρ.trans (ConePresentation.coneBridge I b hb))

def unlift {I : CountableIdeal} {a b : Degree}
    (ha : a ∈ I.carrier) (hb : b ∈ I.carrier)
    (σ : Set.Ici (⟨a, ha⟩ : PersistentLocality.ideal I) ≃o
      Set.Ici (⟨b, hb⟩ : PersistentLocality.ideal I)) : Cone I a ≃o Cone I b :=
  (ConePresentation.coneBridge I a ha).trans
    (σ.trans (ConePresentation.coneBridge I b hb).symm)

/-- Locality restricts any larger extension, without assuming it persistent. -/
theorem restrict_extension {a b : Degree} {I J K : CountableIdeal}
    (ρ : Cone I a ≃o Cone I b) (τ : Cone K a ≃o Cone K b)
    (hIK : I.carrier ⊆ K.carrier) (he : TwoConePersistence.Extends hIK ρ τ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    (hIJ : I.carrier ⊆ J.carrier) (hJK : J.carrier ⊆ K.carrier)
    (hjump : IdealLocality.JumpClosed (PersistentLocality.ideal J)) :
    ∃ σ : Cone J a ≃o Cone J b,
      TwoConePersistence.Extends hIJ ρ σ ∧ TwoConePersistence.Extends hJK σ τ := by
  have haI : a ∈ I.carrier := I.lower (degree_le_jump a) hza
  have hbI : b ∈ I.carrier := I.lower (degree_le_jump b) hzb
  have haJ := hIJ haI
  have hbJ := hIJ hbI
  have haK := hIK haI
  have hbK := hIK hbI
  let za : Cone I a := ⟨degreeJump a, hza, degree_le_jump a⟩
  let zb : Cone I b := ⟨degreeJump b, hzb, degree_le_jump b⟩
  let α : PersistentLocality.ideal K := ⟨a, haK⟩
  let β : PersistentLocality.ideal K := ⟨b, hbK⟩
  let τ' := lift τ haK hbK
  let zaK : Set.Ici α :=
    ⟨⟨za.val, hIK za.property.1⟩, Set.mem_Ici.mpr za.property.2⟩
  let zbK : Set.Ici β :=
    ⟨⟨zb.val, hIK zb.property.1⟩, Set.mem_Ici.mpr zb.property.2⟩
  have hpost : val (τ' zaK) ∈ J.carrier := by
    change (τ ⟨za.val, hIK za.property.1, za.property.2⟩).val ∈ J.carrier
    rw [he za]
    exact hIJ (ρ za).property.1
  have hpre : val (τ'.symm zbK) ∈ J.carrier := by
    change (τ.symm ⟨zb.val, hIK zb.property.1, zb.property.2⟩).val ∈ J.carrier
    rw [TwoConePersistence.extends_inverse he zb]
    exact hIJ (ρ.symm zb).property.1
  obtain ⟨σ, hσ⟩ := TwoConeIdealLocality.restrict_jump_ideal τ' zaK rfl zbK rfl
    hJK hJK haJ hbJ hjump hpost hpre
  refine ⟨unlift haJ hbJ σ, ?_, ?_⟩
  · intro x
    change val (σ ⟨⟨x.val, hIJ x.property.1⟩, Set.mem_Ici.mpr x.property.2⟩) = (ρ x).val
    exact (hσ ⟨⟨x.val, hIJ x.property.1⟩, Set.mem_Ici.mpr x.property.2⟩).trans (he x)
  · intro x
    change (τ ⟨x.val, hJK x.property.1, x.property.2⟩).val =
      val (σ ⟨⟨x.val, x.property.1⟩, Set.mem_Ici.mpr x.property.2⟩)
    exact (hσ ⟨⟨x.val, x.property.1⟩, Set.mem_Ici.mpr x.property.2⟩).symm

/-- Persistence supplies an isomorphism on exactly the prescribed jump ideal. -/
theorem persistent_jump_extension {a b : Degree} (I J : CountableIdeal)
    (ρ : Cone I a ≃o Cone I b) (hp : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    (hIJ : I.carrier ⊆ J.carrier)
    (hjump : IdealLocality.JumpClosed (PersistentLocality.ideal J)) :
    ∃ σ : Cone J a ≃o Cone J b, TwoConePersistence.Extends hIJ ρ σ := by
  obtain ⟨c, hc⟩ := CountableBound.countable_bounded J.carrier J.countable
  obtain ⟨K, hIK, τ, hcK, he⟩ := hp c
  have hJK : J.carrier ⊆ K.carrier := fun x hx => K.lower (hc x hx) hcK
  obtain ⟨σ, hρ, _⟩ := restrict_extension ρ τ hIK he hza hzb hIJ hJK hjump
  exact ⟨σ, hρ⟩

/-- For jump-closed initial ideals it suffices to assume the two bases belong. -/
theorem persistent_jump_extension_of_jump_closed {a b : Degree} (I J : CountableIdeal)
    (ρ : Cone I a ≃o Cone I b) (hp : TwoConePersistence.Persistent I ρ)
    (ha : a ∈ I.carrier) (hb : b ∈ I.carrier)
    (hI : IdealLocality.JumpClosed (PersistentLocality.ideal I))
    (hIJ : I.carrier ⊆ J.carrier)
    (hJ : IdealLocality.JumpClosed (PersistentLocality.ideal J)) :
    ∃ σ : Cone J a ≃o Cone J b, TwoConePersistence.Extends hIJ ρ σ :=
  persistent_jump_extension I J ρ hp (hI a ha) (hI b hb) hIJ hJ

/-- In particular, persistence supplies the extension needed for a later
arithmetic presentation of the graph. That graph theorem is not asserted here. -/
theorem arithmetic_ideal_extension {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (hp : TwoConePersistence.Persistent I ρ)
    {H : Oracle} (hpres : ConePresentation.Presented I H)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier) :
    ∃ σ : Cone (JumpIdeal.generated (degree H)) a ≃o Cone (JumpIdeal.generated (degree H)) b,
      TwoConePersistence.Extends (ConePresentation.presentation_subset_generated hpres) ρ σ :=
  persistent_jump_extension I (JumpIdeal.generated (degree H)) ρ hp hza hzb
    (ConePresentation.presentation_subset_generated hpres) (JumpIdeal.closed _)

end
end OAI.TuringRigidity.TwoConePersistentLocality
