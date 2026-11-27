/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Theory.Classification
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Counting isomorphism classes as orbits

Two lawful cycle sets on `IntegralAtom (Fin s) (Fin n)` have isomorphic complex algebras exactly
when they lie in the same orbit of `IntegralAtom.Aut s n`. Hence the number of isomorphism classes
of finite integral relation algebras with `s` symmetric diversity atoms and `n` pairs of
nonsymmetric atoms is the number of orbits, which Burnside's lemma expresses through counts of
fixed points.
-/

@[expose] public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra

namespace IntegralAtom

variable {s n : ℕ}

/-- Two lawful cycle sets have isomorphic complex algebras exactly when they are related by an
element of `Aut s n`. -/
theorem nonempty_equiv_iff (T T' : {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T}) :
    Nonempty (RelationAlgebraEquiv (ComplexAlgebra (structOf T.val))
      (ComplexAlgebra (structOf T'.val))) ↔ ∃ σ : Aut s n, σ • T = T' := by
  constructor
  · rintro ⟨f⟩
    obtain ⟨e, -, hconv, hid, hcyc⟩ := ComplexAlgebra.exists_equiv_of_relationAlgebraEquiv f
    exact ⟨⟨e, mem_aut_iff.mpr ⟨(hid one).mpr rfl, hconv⟩⟩, smul_eq_iff.mpr hcyc⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨ComplexAlgebra.congr σ.val (Aut.apply_conv σ) fun _ _ _ => apply_mem_smul_iff.symm⟩

/-- The lawful cycle sets fixed by `σ`, as a plain subtype of cycle sets. -/
def fixedByEquiv (σ : Aut s n) :
    MulAction.fixedBy {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T} σ ≃
      {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T ∧
        ∀ a b c, (σ.val a, σ.val b, σ.val c) ∈ T ↔ (a, b, c) ∈ T} where
  toFun T := ⟨T.val.val, T.val.property, smul_eq_self_iff.mp T.property⟩
  invFun T := ⟨⟨T.val, T.property.1⟩, smul_eq_self_iff.mpr T.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full cycle set of a lawful `ofCycles` structure. -/
def cyclesOf (g : {g : Set (Cycle (Fin s) (Fin n)) // LawfulAtomStructure (ofCycles g)}) :
    {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T} :=
  ⟨{c | CycleClosure g.val c}, isLawfulCycles_cycleClosure g.val⟩

namespace IsoClass

/-- The orbit of lawful cycle sets belonging to an isomorphism class. -/
def toOrbit (s n : ℕ) : ofSymmNsymm s n →
    MulAction.orbitRel.Quotient (Aut s n) {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T} :=
  Quotient.lift (fun g => (⟦cyclesOf g⟧ : MulAction.orbitRel.Quotient (Aut s n) _))
    fun g g' ⟨e⟩ => by
      obtain ⟨σ, hσ⟩ := (nonempty_equiv_iff (cyclesOf g') (cyclesOf g)).mp ⟨e.symm⟩
      exact Quotient.sound (MulAction.orbitRel_apply.mpr ⟨σ, hσ⟩)

theorem toOrbit_injective (s n : ℕ) : Function.Injective (toOrbit s n) := by
  intro x y h
  induction x using Quotient.inductionOn with | _ g
  induction y using Quotient.inductionOn with | _ g'
  obtain ⟨σ, hσ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
  obtain ⟨e⟩ := (nonempty_equiv_iff (cyclesOf g') (cyclesOf g)).mpr ⟨σ, hσ⟩
  exact Quotient.sound ⟨e.symm⟩

theorem toOrbit_surjective (s n : ℕ) : Function.Surjective (toOrbit s n) := by
  intro x
  induction x using Quotient.inductionOn with | _ T
  obtain ⟨hlawful, -⟩ := exists_lawful_ofCycles_equiv T
  refine ⟨⟦⟨_, hlawful⟩⟧, congrArg _ (Subtype.ext (Set.ext fun ⟨_, _, _⟩ => ?_))⟩
  exact T.property.cycleClosure_diversity_iff

/-- The number of isomorphism classes of finite integral relation algebras with `s` symmetric
diversity atoms and `n` pairs of nonsymmetric atoms is the number of orbits of `Aut s n` on lawful
cycle sets. -/
theorem card_ofSymmNsymm_eq_card_orbits (s n : ℕ) :
    Nat.card (ofSymmNsymm s n) =
      Nat.card (MulAction.orbitRel.Quotient (IntegralAtom.Aut s n)
        {T : Set (IntegralAtom.Cycle (Fin s) (Fin n)) // IntegralAtom.IsLawfulCycles T}) :=
  Nat.card_congr (Equiv.ofBijective (toOrbit s n) ⟨toOrbit_injective s n, toOrbit_surjective s n⟩)

/-- Burnside's lemma for the action of `Aut s n` on lawful cycle sets. -/
theorem sum_card_fixed_eq_card_orbits_mul_card_aut (s n : ℕ) [Fintype (Aut s n)] :
    ∑ σ : IntegralAtom.Aut s n,
        Nat.card {T : Set (IntegralAtom.Cycle (Fin s) (Fin n)) // IntegralAtom.IsLawfulCycles T ∧
          ∀ a b c, (σ.val a, σ.val b, σ.val c) ∈ T ↔ (a, b, c) ∈ T} =
      Nat.card (MulAction.orbitRel.Quotient (IntegralAtom.Aut s n)
        {T : Set (IntegralAtom.Cycle (Fin s) (Fin n)) // IntegralAtom.IsLawfulCycles T}) *
        Nat.card (IntegralAtom.Aut s n) := by
  classical
  let _ : Fintype (MulAction.orbitRel.Quotient (Aut s n)
    {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T}) := Fintype.ofFinite _
  let _ : ∀ σ : Aut s n,
      Fintype (MulAction.fixedBy {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T} σ) :=
    fun _ => Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (fixedByEquiv σ)]

theorem card_aut_pos (s n : ℕ) : 0 < Nat.card (Aut s n) := Nat.card_pos

/-- Burnside form of the count, with the sum over any `Fintype` structure on `Aut s n`. -/
theorem card_ofSymmNsymm_eq_of_sum' (s n N : ℕ) [Fintype (Aut s n)]
    (h : ∑ σ : IntegralAtom.Aut s n,
        Nat.card {T : Set (IntegralAtom.Cycle (Fin s) (Fin n)) // IntegralAtom.IsLawfulCycles T ∧
          ∀ a b c, (σ.val a, σ.val b, σ.val c) ∈ T ↔ (a, b, c) ∈ T} =
      N * Nat.card (IntegralAtom.Aut s n)) :
    Nat.card (ofSymmNsymm s n) = N := by
  rw [sum_card_fixed_eq_card_orbits_mul_card_aut] at h
  rw [card_ofSymmNsymm_eq_card_orbits, Nat.eq_of_mul_eq_mul_right (card_aut_pos s n) h]

/-- Burnside form of the count: if the numbers of lawful cycle sets fixed by the elements of
`Aut s n` sum to `N * |Aut s n|`, then there are `N` isomorphism classes. -/
theorem card_ofSymmNsymm_eq_of_sum (s n N : ℕ)
    (h : ∑ᶠ σ : IntegralAtom.Aut s n,
        Nat.card {T : Set (IntegralAtom.Cycle (Fin s) (Fin n)) // IntegralAtom.IsLawfulCycles T ∧
          ∀ a b c, (σ.val a, σ.val b, σ.val c) ∈ T ↔ (a, b, c) ∈ T} =
      N * Nat.card (IntegralAtom.Aut s n)) :
    Nat.card (ofSymmNsymm s n) = N := by
  classical
  let _ : Fintype (Aut s n) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype] at h
  exact card_ofSymmNsymm_eq_of_sum' s n N h

end IsoClass

end IntegralAtom

end FiniteIntegralRelationAlgebras.RelationAlgebra
