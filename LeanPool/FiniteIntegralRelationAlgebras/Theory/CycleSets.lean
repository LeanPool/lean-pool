/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Foundations.RelationAlgebra.IntegralAtomStructure

/-!
# Lawful cycle sets

An integral atom structure on `IntegralAtom (Fin s) (Fin n)` is determined by its full set of
cycles. This file defines the atom structure `IntegralAtom.structOf T` of a cycle set `T`, the
predicate `IntegralAtom.IsLawfulCycles T` saying it is lawful, gives an elementary characterization
of that predicate, and relates these to `IntegralAtom.ofCycles`.
-/

@[expose] public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra

namespace IntegralAtom

variable {s n : ℕ}

/-- The atom structure on `IntegralAtom (Fin s) (Fin n)` with cycle set `T`. -/
def structOf (T : Set (Cycle (Fin s) (Fin n))) : AtomStructure (IntegralAtom (Fin s) (Fin n)) :=
  ⟨conv, {one}, T⟩

@[simp]
theorem structOf_conv (T : Set (Cycle (Fin s) (Fin n))) (a : IntegralAtom (Fin s) (Fin n)) :
    (structOf T).conv a = conv a := rfl

@[simp]
theorem structOf_id (T : Set (Cycle (Fin s) (Fin n))) : (structOf T).id = {one} := rfl

@[simp]
theorem mem_structOf_id {T : Set (Cycle (Fin s) (Fin n))} {a : IntegralAtom (Fin s) (Fin n)} :
    a ∈ (structOf T).id ↔ a = one := .rfl

@[simp]
theorem structOf_cycles (T : Set (Cycle (Fin s) (Fin n))) : (structOf T).cycles = T := rfl

theorem ofCycles_eq_structOf (g : Set (Cycle (Fin s) (Fin n))) :
    ofCycles g = structOf {c | CycleClosure g c} := rfl

/-- `T` is the full cycle set of a lawful integral atom structure. -/
def IsLawfulCycles (T : Set (Cycle (Fin s) (Fin n))) : Prop := LawfulAtomStructure (structOf T)

theorem IsLawfulCycles.lawfulAtomStructure {T : Set (Cycle (Fin s) (Fin n))}
    (h : IsLawfulCycles T) :
    LawfulAtomStructure (structOf T) := h

/-- An elementary characterization of lawful cycle sets. -/
theorem isLawfulCycles_iff (T : Set (Cycle (Fin s) (Fin n))) : IsLawfulCycles T ↔
    (∀ r p, (r, one, p) ∈ T ↔ p = r) ∧
    (∀ r u t, (r, u, t) ∈ T → (conv r, t, u) ∈ T) ∧
    (∀ r q p u t, (r, q, p) ∈ T → (u, t, q) ∈ T → ∃ q', (q', t, p) ∈ T ∧ (r, u, q') ∈ T) := by
  constructor
  · intro h
    have := h.lawfulAtomStructure
    refine ⟨fun r p => ⟨fun hrp => (structOf T).id_cycle_right rfl hrp, ?_⟩,
      fun r u t hc => (structOf T).cycle_left hc,
      fun r q p u t h₁ h₂ => (structOf T).assoc h₁ h₂⟩
    rintro rfl
    obtain ⟨e, he, hc⟩ := (structOf T).exists_id_cycle_right p
    obtain rfl : e = one := he
    exact hc
  · rintro ⟨hid, hleft, hassoc⟩
    exact
      { assoc := fun h₁ h₂ => hassoc _ _ _ _ _ h₁ h₂
        id_cycle_right := fun hs hc => by
          obtain rfl : _ = one := hs
          exact (hid _ _).mp hc
        exists_id_cycle_right := fun r => ⟨one, rfl, (hid r r).mpr rfl⟩
        cycle_left := fun hc => hleft _ _ _ hc }

namespace IsLawfulCycles

variable {T : Set (Cycle (Fin s) (Fin n))} {r u t p : IntegralAtom (Fin s) (Fin n)}

theorem one_right_iff (h : IsLawfulCycles T) : (r, one, p) ∈ T ↔ p = r :=
  ((isLawfulCycles_iff T).mp h).1 r p

theorem id_mem (h : IsLawfulCycles T) (r : IntegralAtom (Fin s) (Fin n)) : (r, one, r) ∈ T :=
  h.one_right_iff.mpr rfl

theorem left_mem (h : IsLawfulCycles T) (hc : (r, u, t) ∈ T) : (conv r, t, u) ∈ T :=
  ((isLawfulCycles_iff T).mp h).2.1 r u t hc

theorem assoc (h : IsLawfulCycles T) {q u' t' : IntegralAtom (Fin s) (Fin n)} (h₁ : (r, q, p) ∈ T)
    (h₂ : (u', t', q) ∈ T) : ∃ q', (q', t', p) ∈ T ∧ (r, u', q') ∈ T :=
  ((isLawfulCycles_iff T).mp h).2.2 r q p u' t' h₁ h₂

/-- For a lawful cycle set, the left cycle transformation is an equivalence. -/
theorem left_mem_iff (h : IsLawfulCycles T) : (conv r, t, u) ∈ T ↔ (r, u, t) ∈ T :=
  ⟨fun hc => by simpa using h.left_mem hc, h.left_mem⟩

theorem conv_mem (h : IsLawfulCycles T) (hc : (r, u, t) ∈ T) : (conv u, conv r, conv t) ∈ T :=
  have := h.lawfulAtomStructure
  (structOf T).conv_cycles hc

theorem conv_mem_iff (h : IsLawfulCycles T) : (conv u, conv r, conv t) ∈ T ↔ (r, u, t) ∈ T :=
  ⟨fun hc => by simpa using h.conv_mem hc, h.conv_mem⟩

theorem right_mem (h : IsLawfulCycles T) (hc : (r, u, t) ∈ T) : (t, conv u, r) ∈ T := by
  have h₁ := h.left_mem (h.conv_mem hc)
  rw [conv_conv] at h₁
  simpa using h.conv_mem h₁

theorem right_mem_iff (h : IsLawfulCycles T) : (t, conv u, r) ∈ T ↔ (r, u, t) ∈ T :=
  ⟨fun hc => by simpa using h.right_mem hc, h.right_mem⟩

theorem cycleLeft_mem (h : IsLawfulCycles T) {c : Cycle (Fin s) (Fin n)} (hc : c ∈ T) :
    c.left ∈ T :=
  h.left_mem hc

theorem cycleRight_mem (h : IsLawfulCycles T) {c : Cycle (Fin s) (Fin n)} (hc : c ∈ T) :
    c.right ∈ T :=
  h.right_mem hc

theorem one_left_iff (h : IsLawfulCycles T) : (one, r, p) ∈ T ↔ p = r := by
  have := h.lawfulAtomStructure
  refine ⟨fun hc => (structOf T).id_cycle_left rfl hc, ?_⟩
  rintro rfl
  simpa using h.conv_mem (h.id_mem (conv p))

theorem one_out_iff (h : IsLawfulCycles T) : (r, u, one) ∈ T ↔ u = conv r := by
  rw [← h.left_mem_iff, h.one_right_iff]

/-- The cycle closure of the diversity cycles of a lawful cycle set is the cycle set itself. -/
theorem cycleClosure_diversity_iff (h : IsLawfulCycles T) {c : Cycle (Fin s) (Fin n)} :
    CycleClosure {c ∈ T | c.IsDiversity} c ↔ c ∈ T := by
  constructor
  · intro hc
    induction hc with
    | of hc => exact hc.1
    | id a => exact h.id_mem a
    | left _ ih => exact h.cycleLeft_mem ih
    | right _ ih => exact h.cycleRight_mem ih
  · obtain ⟨r, u, t⟩ := c
    intro hc
    by_cases hu : u = one
    · subst hu
      obtain rfl := h.one_right_iff.mp hc
      exact .id _
    by_cases hr : r = one
    · subst hr
      obtain rfl := h.one_left_iff.mp hc
      simpa [Cycle.left, Cycle.right] using
        (CycleClosure.id (g := {c ∈ T | c.IsDiversity}) (conv t)).left.right
    by_cases ht : t = one
    · subst ht
      obtain rfl := h.one_out_iff.mp hc
      simpa [Cycle.left] using (CycleClosure.id (g := {c ∈ T | c.IsDiversity}) (conv r)).left
    exact .of ⟨hc, hr, hu, ht⟩

/-- A lawful cycle set is generated, in the sense of `ofCycles`, by its diversity cycles. -/
theorem ofCycles_diversity (h : IsLawfulCycles T) :
    ofCycles {c ∈ T | c.IsDiversity} = structOf T := by
  rw [ofCycles_eq_structOf]
  congr 1
  ext c
  exact h.cycleClosure_diversity_iff

end IsLawfulCycles

/-- The full cycle set of a lawful `ofCycles` structure is a lawful cycle set. -/
theorem isLawfulCycles_cycleClosure (g : Set (Cycle (Fin s) (Fin n)))
    [h : LawfulAtomStructure (ofCycles g)] :
    IsLawfulCycles {c | CycleClosure g c} := h

theorem isLawfulCycles_cycleClosure_iff (g : Set (Cycle (Fin s) (Fin n))) :
    IsLawfulCycles {c | CycleClosure g c} ↔ LawfulAtomStructure (ofCycles g) := .rfl

end IntegralAtom

end FiniteIntegralRelationAlgebras.RelationAlgebra
