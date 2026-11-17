/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConePersistentExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeGraphPresentation

/-!
# Persistent extensions of partial two-cone isomorphisms

A persistent map between the two cones of a countable ideal extends
persistently to every prescribed larger countable jump ideal. The initial
ideal must contain both base jumps, but need not itself be jump-closed.

The obstruction argument counts all eleven-jump candidate graphs, not only
persistent maps. The arithmetic restriction theorem does not assume that
its larger map or its restriction is persistent, so there is no circularity.

We also characterize persistence by arithmetic extensions on all presented
jump ideals, using the conventional partial graph. This is a semantic
characterization, not yet a coded projective-complexity or absoluteness result.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConePersistentExtension

open EncodedForcing OracleJump ArithmeticHierarchy PersistentRestrictions
open ConePersistence (Cone)
open TwoConePresentation

noncomputable section

/-- Persistence is symmetric: inverse agreement follows from forward agreement. -/
theorem persistent_symm {a b : Degree} {I : CountableIdeal}
    {ρ : Cone I a ≃o Cone I b} (hp : TwoConePersistence.Persistent I ρ) :
    TwoConePersistence.Persistent I ρ.symm := by
  intro x
  obtain ⟨J, hIJ, σ, hx, he⟩ := hp x
  exact ⟨J, hIJ, σ.symm, hx, fun y => TwoConePersistence.extends_inverse he y⟩

theorem persistent_symm_iff {a b : Degree} {I : CountableIdeal}
    (ρ : Cone I a ≃o Cone I b) :
    TwoConePersistence.Persistent I ρ.symm ↔ TwoConePersistence.Persistent I ρ := by
  constructor
  · intro h
    simpa only [OrderIso.symm_symm] using persistent_symm h
  · exact persistent_symm

/-- Failure of persistence has a single degree witnessing the obstruction. -/
theorem nonpersistent_witness {a b : Degree} {J : CountableIdeal}
    {σ : Cone J a ≃o Cone J b} (h : ¬ TwoConePersistence.Persistent J σ) :
    ∃ x, ∀ (K : CountableIdeal) (hJK : J.carrier ⊆ K.carrier)
      (τ : Cone K a ≃o Cone K b),
      x ∈ K.carrier → ¬ TwoConePersistence.Extends hJK σ τ := by
  classical
  simpa only [TwoConePersistence.Persistent, not_forall, not_exists, not_and] using h

/-- A persistent partial map extends persistently on exactly the prescribed
jump ideal. No global isomorphism or regular representative is assumed. -/
theorem persistent_extension {a b : Degree} (I J : CountableIdeal)
    (ρ : Cone I a ≃o Cone I b) (hp : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    (hIJ : I.carrier ⊆ J.carrier)
    (hjump : IdealLocality.JumpClosed (PersistentLocality.ideal J)) :
    ∃ σ : Cone J a ≃o Cone J b,
      TwoConePersistence.Extends hIJ ρ σ ∧ TwoConePersistence.Persistent J σ := by
  classical
  by_contra hn
  have hnot (σ : Cone J a ≃o Cone J b) (he : TwoConePersistence.Extends hIJ ρ σ) :
      ¬ TwoConePersistence.Persistent J σ := fun hpσ => hn ⟨σ, he, hpσ⟩
  obtain ⟨H, hpres⟩ := ConePresentation.presentation_exists J
  have haJ : a ∈ J.carrier := hIJ (I.lower (degree_le_jump a) hza)
  let S : Set (Cone J a ≃o Cone J b) :=
    {σ | RecursivePred (iterate H 11) (TwoConePresentation.Graph σ hpres haJ)}
  have hS : S.Countable := recursive_maps_countable hpres haJ _
  have : Countable S := hS.to_subtype
  have hwitness (σ : S) : ∃ x, TwoConePersistence.Extends hIJ ρ σ.val →
      ∀ (K : CountableIdeal) (hJK : J.carrier ⊆ K.carrier)
        (τ : Cone K a ≃o Cone K b),
        x ∈ K.carrier → ¬ TwoConePersistence.Extends hJK σ.val τ := by
    by_cases he : TwoConePersistence.Extends hIJ ρ σ.val
    · obtain ⟨x, hx⟩ := nonpersistent_witness (hnot σ.val he)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨⊥, fun h => (he h).elim⟩
  choose w hw using hwitness
  obtain ⟨c, hc⟩ := CountableBound.countable_bounded
    (Set.range w ∪ Set.Iic (degree (jump H)))
    ((Set.countable_range w).union (countable_principal_lower _))
  obtain ⟨K, hIK, τ, hcK, he⟩ := hp c
  have hHK : degree (jump H) ∈ K.carrier :=
    K.lower (hc _ (Or.inr (Set.mem_Iic.mpr le_rfl))) hcK
  have hJK : J.carrier ⊆ K.carrier := fun x hx =>
    K.lower ((ConePresentation.presentation_bound hpres hx).trans (reduces_jump H)) hHK
  obtain ⟨σ, hρ, hτ, hr⟩ := arithmetic_restriction ρ τ hIK he hza hzb
    hIJ hJK hjump hpres haJ hHK
  let s : S := ⟨σ, hr⟩
  have hwK : w s ∈ K.carrier := K.lower (hc (w s) (Or.inl ⟨s, rfl⟩)) hcK
  exact hw s hρ K hJK τ hwK hτ

/-- For a jump-closed starting ideal, membership of the two bases suffices.
Base membership is explicit because both cone intersections could be empty. -/
theorem persistent_extension_of_jump_closed {a b : Degree} (I J : CountableIdeal)
    (ρ : Cone I a ≃o Cone I b) (hp : TwoConePersistence.Persistent I ρ)
    (ha : a ∈ I.carrier) (hb : b ∈ I.carrier)
    (hjumpI : IdealLocality.JumpClosed (PersistentLocality.ideal I))
    (hIJ : I.carrier ⊆ J.carrier)
    (hjumpJ : IdealLocality.JumpClosed (PersistentLocality.ideal J)) :
    ∃ σ : Cone J a ≃o Cone J b,
      TwoConePersistence.Extends hIJ ρ σ ∧ TwoConePersistence.Persistent J σ :=
  persistent_extension I J ρ hp (hjumpI a ha) (hjumpI b hb) hIJ hjumpJ

/-- The same extension can have both indexed graph directions bounded by
H^(11). No new jump is needed when the bases are exchanged. -/
theorem persistent_arithmetic_extension {a b : Degree} (I J : CountableIdeal)
    (ρ : Cone I a ≃o Cone I b) (hp : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    (hIJ : I.carrier ⊆ J.carrier)
    (hjump : IdealLocality.JumpClosed (PersistentLocality.ideal J))
    {H : Oracle} (hpres : ConePresentation.Presented J H) :
    ∃ σ : Cone J a ≃o Cone J b,
      TwoConePersistence.Extends hIJ ρ σ ∧ TwoConePersistence.Persistent J σ ∧
      RecursivePred (iterate H 11) (RawGraph σ H) ∧
      RecursivePred (iterate H 11) (RawGraph σ.symm H) := by
  obtain ⟨σ, he, hpσ⟩ := persistent_extension I J ρ hp hza hzb hIJ hjump
  exact ⟨σ, he, hpσ,
    (raw_graph_arithmetic_of_persistent σ hpσ hpres (hIJ hza) (hIJ hzb)).2,
    (raw_graph_arithmetic_of_persistent σ.symm (persistent_symm hpσ) hpres
      (hIJ hzb) (hIJ hza)).2⟩

/-- Arbitrary persistent partial maps have persistent jump-closed extensions
containing any countable seed, not only restrictions of a global map. -/
theorem persistent_countable_jump_extension {a b : Degree} (I : CountableIdeal)
    (ρ : Cone I a ≃o Cone I b) (hp : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    (S : Set Degree) (hS : S.Countable) :
    ∃ (J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier) (σ : Cone J a ≃o Cone J b),
      S ⊆ J.carrier ∧ IdealLocality.JumpClosed (PersistentLocality.ideal J) ∧
      TwoConePersistence.Extends hIJ ρ σ ∧ TwoConePersistence.Persistent J σ := by
  obtain ⟨c, hc⟩ := CountableBound.countable_bounded (I.carrier ∪ S) (I.countable.union hS)
  let J := JumpIdeal.generated c
  let hIJ : I.carrier ⊆ J.carrier := fun x hx =>
    J.lower (hc x (Or.inl hx)) (JumpIdeal.includes c)
  obtain ⟨σ, he, hpσ⟩ := persistent_extension I J ρ hp hza hzb hIJ (JumpIdeal.closed c)
  exact ⟨J, hIJ, σ, fun x hx => J.lower (hc x (Or.inr hx)) (JumpIdeal.includes c),
    JumpIdeal.closed c, he, hpσ⟩

/-- A semantic condition using conventional partial graphs. Removing the
existential over maps requires a separate real-code reconstruction argument. -/
def ArithmeticExtensions {a b : Degree} (I : CountableIdeal)
    (ρ : Cone I a ≃o Cone I b) : Prop :=
  ∀ (J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier),
    IdealLocality.JumpClosed (PersistentLocality.ideal J) →
    ∀ (H : Oracle), ConePresentation.Presented J H →
      ∃ σ : Cone J a ≃o Cone J b, TwoConePersistence.Extends hIJ ρ σ ∧
        RecursivePred (iterate H 11) (RawGraph σ H)

/-- Persistence is equivalent to arithmetic extensions on all presented
countable jump ideals. This is not yet a coded Pi-1-1 statement. -/
theorem persistent_iff_arithmetic_extensions {a b : Degree} (I : CountableIdeal)
    (ρ : Cone I a ≃o Cone I b)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier) :
    TwoConePersistence.Persistent I ρ ↔ ArithmeticExtensions I ρ := by
  constructor
  · intro hp J hIJ hjump H hpres
    obtain ⟨σ, he, _, hgraph, _⟩ :=
      persistent_arithmetic_extension I J ρ hp hza hzb hIJ hjump hpres
    exact ⟨σ, he, hgraph⟩
  · intro h x
    obtain ⟨c, hc⟩ := CountableBound.countable_bounded (insert x I.carrier) (I.countable.insert x)
    let J := JumpIdeal.generated c
    let hIJ : I.carrier ⊆ J.carrier := fun y hy =>
      J.lower (hc y (Or.inr hy)) (JumpIdeal.includes c)
    obtain ⟨H, hpres⟩ := ConePresentation.presentation_exists J
    obtain ⟨σ, he, _⟩ := h J hIJ (JumpIdeal.closed c) H hpres
    exact ⟨J, hIJ, σ, J.lower (hc x (Or.inl rfl)) (JumpIdeal.includes c), he⟩

end
end OAI.TuringRigidity.TwoConePersistentExtension
