/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConePersistentExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConePersistentRestriction

/-!
# Persistent extensions of partial cone isomorphisms

A persistent cone isomorphism extends persistently to every prescribed
countable jump ideal containing its domain, assuming only that a' is in the
starting ideal. The proof diagonalizes against the countably many arithmetic
candidate graphs, using the restriction theorem without assuming that the
candidate restriction is persistent.

We also give a semantic arithmetic-extension characterization of persistence.
This is not yet a formal projective-complexity or forcing-absoluteness theorem.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConePersistentExtension

open EncodedForcing OracleJump ArithmeticHierarchy PersistentRestrictions
open ConePersistence ConePresentation ConePersistentLocality

noncomputable section

/-- Failure of persistence has a single degree witnessing the obstruction. -/
theorem nonpersistent_witness {a : Degree} {J : CountableIdeal}
    {σ : J ≃o Cone J a} (h : ¬ ConePersistence.Persistent J σ) :
    ∃ x, ∀ (K : CountableIdeal) (hJK : J.carrier ⊆ K.carrier) (τ : K ≃o Cone K a),
      x ∈ K.carrier → ¬ ConePersistence.Extends hJK σ τ := by
  classical
  simpa only [ConePersistence.Persistent, not_forall, not_exists, not_and] using h

/-- The cone version of the persistent-extension argument: the extension on
the prescribed jump ideal can itself be chosen persistent. -/
theorem persistent_extension {a : Degree} (I J : CountableIdeal)
    (ρ : I ≃o Cone I a) (hp : ConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hIJ : I.carrier ⊆ J.carrier)
    (hjump : IdealLocality.JumpClosed (PersistentLocality.ideal J)) :
    ∃ σ : J ≃o Cone J a,
      ConePersistence.Extends hIJ ρ σ ∧ ConePersistence.Persistent J σ := by
  classical
  by_contra hn
  have hnot (σ : J ≃o Cone J a) (he : ConePersistence.Extends hIJ ρ σ) :
      ¬ ConePersistence.Persistent J σ := fun hpσ => hn ⟨σ, he, hpσ⟩
  obtain ⟨H, hpres⟩ := ConePresentation.presentation_exists J
  let S : Set (J ≃o Cone J a) :=
    {σ | RecursivePred (iterate H 11) (ConePresentation.Graph σ hpres)}
  have hS : S.Countable := recursive_maps_countable hpres _
  have : Countable S := hS.to_subtype
  have hwitness (σ : S) : ∃ x, ConePersistence.Extends hIJ ρ σ.val →
      ∀ (K : CountableIdeal) (hJK : J.carrier ⊆ K.carrier) (τ : K ≃o Cone K a),
        x ∈ K.carrier → ¬ ConePersistence.Extends hJK σ.val τ := by
    by_cases he : ConePersistence.Extends hIJ ρ σ.val
    · obtain ⟨x, hx⟩ := nonpersistent_witness (hnot σ.val he)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨⊥, fun h => (he h).elim⟩
  choose w hw using hwitness
  obtain ⟨b, hb⟩ := CountableBound.countable_bounded
    (Set.range w ∪ Set.Iic (degree (jump H)))
    ((Set.countable_range w).union (countable_principal_lower _))
  obtain ⟨K, hIK, τ, hbK, he⟩ := hp b
  have hHK : degree (jump H) ∈ K.carrier :=
    K.lower (hb _ (Or.inr (Set.mem_Iic.mpr le_rfl))) hbK
  have hJK : J.carrier ⊆ K.carrier := fun x hx =>
    K.lower ((presentation_bound hpres hx).trans (reduces_jump H)) hHK
  obtain ⟨σ, hρ, hτ, hr⟩ := ConePersistentRestriction.restriction ρ τ hIK he hza
    hIJ hJK hjump hpres hHK
  let s : S := ⟨σ, hr⟩
  have hwK : w s ∈ K.carrier := K.lower (hb (w s) (Or.inl ⟨s, rfl⟩)) hbK
  exact hw s hρ K hJK τ hwK hτ

/-- For a jump-closed starting ideal, the needed a' membership is automatic:
the existence of the cone isomorphism already puts a in the ideal. -/
theorem persistent_extension_of_jump_closed {a : Degree} (I J : CountableIdeal)
    (ρ : I ≃o Cone I a) (hp : ConePersistence.Persistent I ρ)
    (hjumpI : IdealLocality.JumpClosed (PersistentLocality.ideal I))
    (hIJ : I.carrier ⊆ J.carrier)
    (hjumpJ : IdealLocality.JumpClosed (PersistentLocality.ideal J)) :
    ∃ σ : J ≃o Cone J a,
      ConePersistence.Extends hIJ ρ σ ∧ ConePersistence.Persistent J σ :=
  persistent_extension I J ρ hp (hjumpI a (ConePresentation.base_mem ρ)) hIJ hjumpJ

/-- Arbitrary persistent partial maps, not merely restrictions of a global
map, have persistent jump-closed extensions containing any countable seed. -/
theorem persistent_countable_jump_extension {a : Degree} (I : CountableIdeal)
    (ρ : I ≃o Cone I a) (hp : ConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (S : Set Degree) (hS : S.Countable) :
    ∃ (J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier) (σ : J ≃o Cone J a),
      S ⊆ J.carrier ∧ IdealLocality.JumpClosed (PersistentLocality.ideal J) ∧
      ConePersistence.Extends hIJ ρ σ ∧ ConePersistence.Persistent J σ := by
  obtain ⟨b, hb⟩ := CountableBound.countable_bounded (I.carrier ∪ S) (I.countable.union hS)
  let J := JumpIdeal.generated b
  let hIJ : I.carrier ⊆ J.carrier := fun x hx =>
    J.lower (hb x (Or.inl hx)) (JumpIdeal.includes b)
  obtain ⟨σ, he, hpσ⟩ := persistent_extension I J ρ hp hza hIJ (JumpIdeal.closed b)
  exact ⟨J, hIJ, σ, fun x hx => J.lower (hb x (Or.inr hx)) (JumpIdeal.includes b),
    JumpIdeal.closed b, he, hpσ⟩

/-- A semantic condition on all presentations of larger countable jump
ideals. Formalizing its projective complexity is a separate next step. -/
def ArithmeticExtensions {a : Degree} (I : CountableIdeal) (ρ : I ≃o Cone I a) : Prop :=
  ∀ (J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier),
    IdealLocality.JumpClosed (PersistentLocality.ideal J) →
    ∀ (H : Oracle) (hpres : Presented J H),
      ∃ σ : J ≃o Cone J a, ConePersistence.Extends hIJ ρ σ ∧
        RecursivePred (iterate H 11) (ConePresentation.Graph σ hpres)

/-- Persistence is equivalent to the existence of arithmetic extensions on
every presented countable jump ideal. This is a mathematical equivalence,
not yet a coded Pi-1-1 formula or an absoluteness theorem. -/
theorem persistent_iff_arithmetic_extensions {a : Degree} (I : CountableIdeal)
    (ρ : I ≃o Cone I a) (hza : degreeJump a ∈ I.carrier) :
    ConePersistence.Persistent I ρ ↔ ArithmeticExtensions I ρ := by
  constructor
  · intro hp J hIJ hjump H hpres
    obtain ⟨σ, he, hpσ⟩ := persistent_extension I J ρ hp hza hIJ hjump
    exact ⟨σ, he, (arithmetic_presentation_of_persistent σ hpσ hpres (hIJ hza)).2⟩
  · intro h x
    obtain ⟨b, hb⟩ := CountableBound.countable_bounded (insert x I.carrier) (I.countable.insert x)
    let J := JumpIdeal.generated b
    let hIJ : I.carrier ⊆ J.carrier := fun y hy =>
      J.lower (hb y (Or.inr hy)) (JumpIdeal.includes b)
    obtain ⟨H, hpres⟩ := ConePresentation.presentation_exists J
    obtain ⟨σ, he, _⟩ := h J hIJ (JumpIdeal.closed b) H hpres
    exact ⟨J, hIJ, σ, J.lower (hb x (Or.inl rfl)) (JumpIdeal.includes b), he⟩

end
end OAI.TuringRigidity.ConePersistentExtension
