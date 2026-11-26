/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Theory.Aut
public import LeanPool.FiniteIntegralRelationAlgebras.Theory.ComplexAlgebra
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Classification of finite integral relation algebras by lawful cycle sets

Every finite integral relation algebra with `s` symmetric diversity atoms and `n` pairs of
nonsymmetric atoms is isomorphic to the complex algebra of a lawful cycle set on
`IntegralAtom (Fin s) (Fin n)`. In particular this proves `exists_ofCycles_of_mem_ofSymmNsymm`.
-/

@[expose] public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra

/-- A fixed-point-free involution on a finite type with `2 * n` elements can be straightened to
the swap of the Boolean coordinate of `Fin n × Bool`. -/
theorem exists_equiv_fin_prod_bool {X : Type*} [Finite X] (τ : X → X) (hτ : ∀ x, τ (τ x) = x)
    (hne : ∀ x, τ x ≠ x) {n : ℕ} (hcard : Nat.card X = 2 * n) :
    ∃ e : Fin n × Bool ≃ X, ∀ i b, e (i, !b) = τ (e (i, b)) := by
  classical
  -- order the elements of `X`, and take as representatives the smaller element of each pair
  let f : X → ℕ := fun x => (Finite.equivFin X x).val
  have hf : Function.Injective f := fun x y h => (Finite.equivFin X).injective (Fin.ext h)
  have hlt : ∀ x, ¬ f x < f (τ x) → f (τ x) < f (τ (τ x)) := fun x hx => by
    rw [hτ]
    exact lt_of_le_of_ne (not_lt.mp hx) fun h => hne x (hf h)
  let g : {x : X // f x < f (τ x)} × Bool ≃ X :=
    { toFun := fun p => bif p.2 then τ p.1.val else p.1.val
      invFun := fun x => if h : f x < f (τ x) then (⟨x, h⟩, false) else (⟨τ x, hlt x h⟩, true)
      left_inv := by
        rintro ⟨⟨r, hr⟩, b⟩
        cases b
        · simp [hr]
        · have : ¬ f (τ r) < f r := not_lt.mpr hr.le
          simp [this, hτ]
      right_inv := by
        intro x
        by_cases h : f x < f (τ x)
        · simp [h]
        · simp [h, hτ] }
  have hcardR : Nat.card {x : X // f x < f (τ x)} = n := by
    have h := Nat.card_congr g
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, hcard,
      mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left two_pos h
  let k : Fin n ≃ {x : X // f x < f (τ x)} := ((Finite.equivFin _).trans (finCongr hcardR)).symm
  refine ⟨(Equiv.prodCongr k (Equiv.refl Bool)).trans g, fun i b => ?_⟩
  cases b
  · rfl
  · exact (hτ _).symm

namespace IntegralAtom

variable {s n : ℕ}

/-- The non-dependent eliminator of `IntegralAtom`. -/
def elim {γ : Sort*} (x : γ) (f : Fin s → γ) (g : Fin n → Bool → γ) :
    IntegralAtom (Fin s) (Fin n) → γ
  | one => x
  | symm i => f i
  | nsymm i b => g i b

@[simp]
theorem elim_one {γ : Sort*} (x : γ) (f : Fin s → γ) (g : Fin n → Bool → γ) :
    elim x f g one = x := rfl

@[simp]
theorem elim_symm {γ : Sort*} (x : γ) (f : Fin s → γ) (g : Fin n → Bool → γ) (i : Fin s) :
    elim x f g (symm i) = f i := rfl

@[simp]
theorem elim_nsymm {γ : Sort*} (x : γ) (f : Fin s → γ) (g : Fin n → Bool → γ) (i : Fin n)
    (b : Bool) : elim x f g (nsymm i b) = g i b := rfl

/-- The lawful atom structure of a lawful cycle set, as an instance. -/
instance instLawfulAtomStructureStructOf
    (T : {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T}) :
    LawfulAtomStructure (structOf T.val) := T.property

/-- The complex algebra of a lawful cycle set is integral. -/
theorem isIntegral_structOf (T : {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T}) :
    IsIntegral (ComplexAlgebra (structOf T.val)) :=
  (ComplexAlgebra.isIntegral_iff _).mpr ⟨one, rfl⟩

section Finite

variable {α : Type*} [RelationAlgebra α] [Finite α]

/-- The atoms of a finite integral relation algebra with `s` symmetric diversity atoms and `2 * n`
nonsymmetric atoms can be labelled by `IntegralAtom (Fin s) (Fin n)`, compatibly with identity and
converse. -/
theorem exists_equiv_isAtom (h1 : IsIntegral α) (hs : (symmetricDiversityAtoms α).ncard = s)
    (hn : (nonsymmetricDiversityAtoms α).ncard = 2 * n) :
    ∃ e : IntegralAtom (Fin s) (Fin n) ≃ {a : α // IsAtom a},
      (e one).val = 1 ∧ ∀ a, (e (conv a)).val = star (e a).val := by
  obtain ⟨es⟩ : Nonempty (Fin s ≃ symmetricDiversityAtoms α) :=
    ⟨((Finite.equivFin _).trans (finCongr (by rw [Nat.card_coe_set_eq, hs]))).symm⟩
  obtain ⟨en, hen⟩ := exists_equiv_fin_prod_bool (X := nonsymmetricDiversityAtoms α)
    (fun x => ⟨star x.val, isAtom_star_iff.mpr x.property.1,
      fun h => x.property.2 (star_injective h)⟩)
    (fun x => Subtype.ext (star_star x.val)) (fun x h => x.property.2 (congrArg Subtype.val h))
    (by rw [Nat.card_coe_set_eq, hn])
  classical
  let labels : IntegralAtom (Fin s) (Fin n) ≃ (PUnit.{1} ⊕ Fin s) ⊕ (Fin n × Bool) :=
    { toFun := fun
        | one => .inl (.inl PUnit.unit)
        | symm i => .inl (.inr i)
        | nsymm i b => .inr (i, b)
      invFun := fun
        | .inl (.inl _) => one
        | .inl (.inr i) => symm i
        | .inr (i, b) => nsymm i b
      left_inv := by rintro (_ | _ | ⟨_, _⟩) <;> rfl
      right_inv := by rintro ((⟨⟩ | _) | ⟨_, _⟩) <;> rfl }
  have hpartition : ({a : α | IsAtom a} : Set α) =
      {1} ∪ symmetricDiversityAtoms α ∪ nonsymmetricDiversityAtoms α := by
    rw [setOf_isAtom_eq, identityAtoms_eq_of_isIntegral h1]
  have hsymm : Disjoint ({1} : Set α) (symmetricDiversityAtoms α) := by
    rw [← identityAtoms_eq_of_isIntegral h1]
    exact disjoint_identityAtoms_symmetricDiversityAtoms
  have hnsymm : Disjoint ({1} ∪ symmetricDiversityAtoms α) (nonsymmetricDiversityAtoms α) := by
    rw [← identityAtoms_eq_of_isIntegral h1, Set.disjoint_union_left]
    exact ⟨disjoint_identityAtoms_nonsymmetricDiversityAtoms,
      disjoint_symmetricDiversityAtoms_nonsymmetricDiversityAtoms⟩
  let singleton : PUnit.{1} ≃ ({1} : Set α) := (Equiv.Set.singleton (1 : α)).symm
  let pieces := Equiv.sumCongr (Equiv.sumCongr singleton es) en
  let paired := Equiv.sumCongr (Equiv.Set.union hsymm).symm
    (Equiv.refl (nonsymmetricDiversityAtoms α))
  let atoms := Equiv.subtypeEquivRight (Set.ext_iff.mp hpartition.symm)
  let e := labels.trans (pieces.trans (paired.trans ((Equiv.Set.union hnsymm).symm.trans atoms)))
  refine ⟨e, rfl, ?_⟩
  rintro (_ | i | ⟨i, b⟩)
  · exact (star_one α).symm
  · exact (es i).property.2.2.symm
  · exact congrArg Subtype.val (hen i b)

/-- A finite integral relation algebra with `s` symmetric diversity atoms and `2 * n` nonsymmetric
atoms is isomorphic to the complex algebra of a lawful cycle set on
`IntegralAtom (Fin s) (Fin n)`. -/
theorem exists_isLawfulCycles_relationAlgebraEquiv (h1 : IsIntegral α)
    (hs : (symmetricDiversityAtoms α).ncard = s)
    (hn : (nonsymmetricDiversityAtoms α).ncard = 2 * n) :
    ∃ T : {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T},
      Nonempty (RelationAlgebraEquiv (ComplexAlgebra (structOf T.val)) α) := by
  obtain ⟨e, he1, heconv⟩ := exists_equiv_isAtom (s := s) (n := n) h1 hs hn
  let T : Set (Cycle (Fin s) (Fin n)) := {c | (e c.1, e c.2.1, e c.2.2) ∈ (atomStructure α).cycles}
  have hconv : ∀ a, e ((structOf T).conv a) = (atomStructure α).conv (e a) :=
    fun a => Subtype.ext (heconv a)
  have hcyc : ∀ a b c,
      (a, b, c) ∈ (structOf T).cycles ↔ (e a, e b, e c) ∈ (atomStructure α).cycles :=
    fun _ _ _ => Iff.rfl
  have hid : ∀ a, a ∈ (structOf T).id ↔ e a ∈ (atomStructure α).id := fun a => by
    change a = one ↔ (e a).val ≤ 1
    rw [IsAtom.le_iff_eq h1 (e a).property.ne_bot, ← he1, ← Subtype.ext_iff,
      e.apply_eq_iff_eq]
  have hT : IsLawfulCycles T := LawfulAtomStructure.of_equiv e hconv hid hcyc
  have := hT.lawfulAtomStructure
  exact ⟨⟨T, hT⟩,
    ⟨(ComplexAlgebra.congr e hconv hcyc).trans (complexAlgebraEquivOfFinite α).symm⟩⟩

end Finite

end IntegralAtom

namespace IntegralAtom

variable {s n : ℕ}

/-- A lawful cycle set has the same complex algebra as the `ofCycles` structure generated by its
diversity cycles. -/
theorem exists_lawful_ofCycles_equiv
    (T : {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T}) :
    ∃ _ : LawfulAtomStructure (ofCycles {c ∈ T.val | c.IsDiversity}),
      Nonempty (RelationAlgebraEquiv (ComplexAlgebra (ofCycles {c ∈ T.val | c.IsDiversity}))
        (ComplexAlgebra (structOf T.val))) := by
  have hlawful : LawfulAtomStructure (ofCycles {c ∈ T.val | c.IsDiversity}) :=
    T.property.ofCycles_diversity ▸ T.property.lawfulAtomStructure
  exact ⟨hlawful, ⟨ComplexAlgebra.congr (Equiv.refl _) (fun _ => rfl)
    fun _ _ _ => T.property.cycleClosure_diversity_iff⟩⟩

/-- Every finite integral relation algebra with `s` symmetric diversity atoms and `n` pairs of
nonsymmetric atoms is isomorphic to the complex algebra of an `ofCycles` structure. This is the
`theorem_wanted` of the same name in Cslib. -/
theorem exists_ofCycles_of_isIntegral {A : Type*} [RelationAlgebra A] [Finite A]
    (hA : IsIntegral A) (hs : (symmetricDiversityAtoms A).ncard = s)
    (hn : (nonsymmetricDiversityAtoms A).ncard = 2 * n) :
    ∃ (g : Set (Cycle (Fin s) (Fin n))) (_ : LawfulAtomStructure (ofCycles g)),
      Nonempty (RelationAlgebraEquiv A (ComplexAlgebra (ofCycles g))) := by
  obtain ⟨T, ⟨e⟩⟩ := exists_isLawfulCycles_relationAlgebraEquiv (s := s) (n := n) hA hs hn
  obtain ⟨hlawful, ⟨f⟩⟩ := exists_lawful_ofCycles_equiv T
  exact ⟨_, hlawful, ⟨e.symm.trans f.symm⟩⟩

end IntegralAtom

end FiniteIntegralRelationAlgebras.RelationAlgebra
