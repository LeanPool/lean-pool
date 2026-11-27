/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Foundations.RelationAlgebra.AtomStructure
public import Mathlib.Data.Set.Card.Arithmetic

/-!
# Integral atom structures

This module abstractly defines the atoms of an integral relation algebra, along with a
characterization of its identity and non-identity cycles that form an atom structure when
shown to be associative.

## References

* [Steven Givant, *Introduction to Relation Algebras*][Givant2017a], Section 4.2
* [Steven Givant, *Advanced Topics in Relation Algebras*][Givant2017b], Section 19.3
* [Peter Jipsen, *Small relation algebras*](https://www1.chapman.edu/~jipsen/gap/ramaddux.html)

-/

@[expose] public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra

/--
The atoms of an integral atom structure: the identity atom, a type `α` of symmetric diversity atoms,
and a type `β` of pairs of nonsymmetric atoms.
-/
inductive IntegralAtom (α β : Type*) where
  /-- The identity atom. -/
  | one
  /-- A symmetric diversity atom. -/
  | symm (a : α)
  /-- A nonsymmetric atom. `nsymm b true` is the converse of `nsymm b false`. -/
  | nsymm (b : β) (conv : Bool)
  deriving DecidableEq

namespace IntegralAtom

variable {α β : Type*}

/-- `IntegralAtom α β` as a sum. -/
def equivOptionSum : IntegralAtom α β ≃ Option (α ⊕ β × Bool) where
  toFun
    | one => none
    | symm a => some (.inl a)
    | nsymm b d => some (.inr (b, d))
  invFun
    | none => one
    | some (.inl a) => symm a
    | some (.inr (b, d)) => nsymm b d
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | ⟨_, _⟩) <;> rfl

instance [Fintype α] [Fintype β] : Fintype (IntegralAtom α β) := .ofEquiv _ equivOptionSum.symm

/-- The converse of an atom, where just nonsymmetric atoms are flipped. -/
def conv : IntegralAtom α β → IntegralAtom α β
  | one => one
  | symm a => symm a
  | nsymm b d => nsymm b (!d)

/-- An integral cycle is a triple of integral atoms. -/
abbrev Cycle (α β : Type*) := IntegralAtom α β × IntegralAtom α β × IntegralAtom α β

/-- The left cycle transformation: `t ≤ r * u` implies `u ≤ conv r * t` -/
def Cycle.left : Cycle α β → Cycle α β
  | (r, u, t) => (conv r, t, u)

/-- The right cycle transformation: `t ≤ r * u` implies `r ≤ t * conv u` -/
def Cycle.right : Cycle α β → Cycle α β
  | (r, u, t) => (t, conv u, r)

/-- A cycle without identity. -/
abbrev Cycle.IsDiversity : Cycle α β → Prop
  | (r, u, t) => r ≠ one ∧ u ≠ one ∧ t ≠ one

/-- The union of the Peircean orbits of the generators and all identity cycles. -/
inductive CycleClosure (g : Set (Cycle α β)) : Cycle α β → Prop
  | of {c : Cycle α β} : c ∈ g → CycleClosure g c
  | id (x : IntegralAtom α β) : CycleClosure g (x, one, x)
  | left {c : Cycle α β} : CycleClosure g c → CycleClosure g c.left
  | right {c : Cycle α β} : CycleClosure g c → CycleClosure g c.right

@[simp, grind =]
theorem conv_one : conv (one : IntegralAtom α β) = one := rfl

@[simp, grind =]
theorem conv_symm (a : α) : conv (symm a : IntegralAtom α β) = symm a := rfl

@[simp, grind =]
theorem conv_nsymm (b : β) (d : Bool) : conv (nsymm b d : IntegralAtom α β) = nsymm b !d := rfl

@[simp, grind =]
theorem conv_conv (x : IntegralAtom α β) : conv (conv x) = x := by
  cases x <;> simp

private theorem CycleClosure.id_cycle_aux {g : Set (Cycle α β)} (hg : ∀ c ∈ g, c.IsDiversity)
    {r u t : IntegralAtom α β} (h : CycleClosure g (r, u, t)) :
    (r = one → t = u) ∧ (u = one → t = r) ∧ (t = one → u = conv r) := by
  generalize hc : (r, u, t) = c at h
  induction h generalizing r u t <;> grind [Cycle.left, Cycle.right, conv_conv]

theorem CycleClosure.id_cycle_left {g : Set (Cycle α β)} (hg : ∀ c ∈ g, c.IsDiversity)
    {u t : IntegralAtom α β} (h : CycleClosure g (one, u, t)) : t = u :=
  (h.id_cycle_aux hg).1 rfl

theorem CycleClosure.id_cycle_right {g : Set (Cycle α β)} (hg : ∀ c ∈ g, c.IsDiversity)
    {r t : IntegralAtom α β} (h : CycleClosure g (r, one, t)) : t = r :=
  (h.id_cycle_aux hg).2.1 rfl

theorem CycleClosure.id_cycle_conv {g : Set (Cycle α β)} (hg : ∀ c ∈ g, c.IsDiversity)
    {r u : IntegralAtom α β} (h : CycleClosure g (r, u, one)) : u = conv r :=
  (h.id_cycle_aux hg).2.2 rfl

theorem cycleClosure_one_iff {g : Set (Cycle α β)} (hg : ∀ c ∈ g, c.IsDiversity)
    {r p : IntegralAtom α β} : CycleClosure g (r, one, p) ↔ p = r :=
  ⟨fun h => h.id_cycle_right hg, fun h => h ▸ .id p⟩

/-- Construct an `AtomStructure` from diversity cycle generators. -/
def ofCycles (g : Set (Cycle α β)) : AtomStructure (IntegralAtom α β) where
  conv := conv
  id := {one}
  cycles := {c | CycleClosure g c}

@[simp]
theorem ofCycles_conv (g : Set (Cycle α β)) (x : IntegralAtom α β) :
    (ofCycles g).conv x = conv x := rfl

@[simp]
theorem mem_ofCycles_id {g : Set (Cycle α β)} {x : IntegralAtom α β} :
    x ∈ (ofCycles g).id ↔ x = one := .rfl

@[simp]
theorem mem_ofCycles_cycles {g : Set (Cycle α β)} {c : Cycle α β} :
    c ∈ (ofCycles g).cycles ↔ CycleClosure g c := .rfl

theorem lawfulAtomStructure_ofCycles (g : Set (Cycle α β))
    (hassoc : ∀ {r q p u t}, CycleClosure g (r, q, p) → CycleClosure g (u, t, q) →
      ∃ q', CycleClosure g (q', t, p) ∧ CycleClosure g (r, u, q'))
    (hg : ∀ c ∈ g, c.IsDiversity) :
    LawfulAtomStructure (ofCycles g) where
  assoc := hassoc
  id_cycle_right hs h := (cycleClosure_one_iff hg).mp (hs ▸ h)
  exists_id_cycle_right r := ⟨one, rfl, .id r⟩
  cycle_left := .left

/-- The complex algebra constructed from diversity cycles is integral. -/
@[simp]
theorem isIntegral_ofCycles (g : Set (Cycle α β)) [LawfulAtomStructure (ofCycles g)] :
    IsIntegral (ComplexAlgebra (ofCycles g)) :=
  (ComplexAlgebra.isIntegral_iff _).mpr ⟨one, rfl⟩

theorem preimage_singleton_symmetricDiversityAtoms (g : Set (Cycle α β))
    [LawfulAtomStructure (ofCycles g)] :
    singleton ⁻¹' symmetricDiversityAtoms (ComplexAlgebra (ofCycles g)) = Set.range symm := by
  ext x
  cases x <;> simp

theorem preimage_singleton_nonsymmetricDiversityAtoms (g : Set (Cycle α β))
    [LawfulAtomStructure (ofCycles g)] :
    singleton ⁻¹' nonsymmetricDiversityAtoms (ComplexAlgebra (ofCycles g)) =
      Set.range (Function.uncurry nsymm) := by
  ext x
  cases x <;> simp

theorem ncard_symmetricDiversityAtoms_ofCycles (g : Set (Cycle α β))
    [LawfulAtomStructure (ofCycles g)] :
    (symmetricDiversityAtoms (ComplexAlgebra (ofCycles g))).ncard = Nat.card α := by
  rw [← ComplexAlgebra.ncard_preimage_singleton fun _ => And.left,
    preimage_singleton_symmetricDiversityAtoms,
    Set.ncard_range_of_injective fun _ _ => symm.inj]

theorem ncard_nonsymmetricDiversityAtoms_ofCycles (g : Set (Cycle α β))
    [LawfulAtomStructure (ofCycles g)] :
    (nonsymmetricDiversityAtoms (ComplexAlgebra (ofCycles g))).ncard = 2 * Nat.card β := by
  rw [← ComplexAlgebra.ncard_preimage_singleton fun _ => And.left,
    preimage_singleton_nonsymmetricDiversityAtoms,
    Set.ncard_range_of_injective (by simp [Function.Injective])]
  simp [mul_comm]

instance (g : {g : Set (Cycle α β) // LawfulAtomStructure (ofCycles g)}) :
    LawfulAtomStructure (ofCycles g.val) := g.property

instance setoid (α β : Type*) :
    Setoid {g : Set (Cycle α β) // LawfulAtomStructure (ofCycles g)} where
  r g₁ g₂ := Nonempty (RelationAlgebraEquiv (ComplexAlgebra (ofCycles g₁.val))
    (ComplexAlgebra (ofCycles g₂.val)))
  iseqv := ⟨fun _ => ⟨.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

namespace IsoClass

/-- The set of isomorphism classes with `s` symmetric diversity atoms and `n` pairs of nonsymmetric
atoms. This is an abbrev for the convenience of matching the usual convention without making proofs
more complicated. -/
abbrev ofSymmNsymm (s n : ℕ) : Type := Quotient (setoid (Fin s) (Fin n))

/-- The set of isomorphism classes with `k` atoms. -/
abbrev ofAtoms (k : ℕ) : Type := Σ s, Σ n : {n // 1 + s + 2 * n = k}, ofSymmNsymm s n

theorem isEmpty_ofAtoms_zero : IsEmpty (ofAtoms 0) :=
  ⟨fun ⟨_, n, _⟩ => by lia⟩

theorem card_ofAtoms_succ_eq_sum_ofSymmNsymm (k : ℕ) :
    Nat.card (ofAtoms (k + 1)) =
      ∑ n ∈ Finset.range (k / 2 + 1), Nat.card (ofSymmNsymm (k - 2 * n) n) := by
  rw [← Finset.sum_coe_sort, ← Nat.card_sigma, eq_comm]
  apply Nat.card_eq_of_bijective (fun ⟨n, q⟩ => ⟨k - 2 * n, ⟨n, by grind⟩, q⟩)
  constructor
  · rintro ⟨n, q⟩ ⟨n', q'⟩ h
    obtain rfl : n = n' := by grind
    grind
  · rintro ⟨s, ⟨n, h⟩, q⟩
    obtain rfl : s = k - 2 * n := by lia
    exact ⟨⟨⟨n, by grind⟩, q⟩, rfl⟩

end IsoClass

end IntegralAtom

end FiniteIntegralRelationAlgebras.RelationAlgebra
