/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/CodingForcing.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.Introreducible

/-!
# Coding Forcing
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CodingForcing

structure Condition where
  left : List Bool
  right : List Bool
  sameLength : left.length = right.length
  active : ℕ

def CodingLocation (A : ℕ → Oracle) (p : Condition) (m : ℕ) : Prop :=
  p.left.length ≤ m ∧ (Nat.unpair m).1 < p.active ∧
    A (Nat.unpair m).1 (Nat.unpair m).2 = true

def Extends (A : ℕ → Oracle) (p q : Condition) : Prop :=
  p.left <+: q.left ∧ p.right <+: q.right ∧ p.active ≤ q.active ∧
    ∀ m, CodingLocation A p m → m < q.left.length →
      q.left.getD m false = q.right.getD m false

theorem extends_refl (A : ℕ → Oracle) (p : Condition) : Extends A p p := by
  refine ⟨List.prefix_rfl, List.prefix_rfl, le_rfl, ?_⟩
  intro m hm hlt
  exact False.elim (Nat.not_lt_of_ge hm.1 hlt)

theorem getD_of_prefix {s t : List Bool} (h : s <+: t) {m : ℕ}
    (hm : m < s.length) : t.getD m false = s.getD m false := by
  obtain ⟨u, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, hm]

theorem extends_trans {A : ℕ → Oracle} {p q r : Condition}
    (hpq : Extends A p q) (hqr : Extends A q r) : Extends A p r := by
  refine ⟨hpq.1.trans hqr.1, hpq.2.1.trans hqr.2.1,
    hpq.2.2.1.trans hqr.2.2.1, ?_⟩
  intro m hm hmr
  by_cases hmq : m < q.left.length
  · rw [getD_of_prefix hqr.1 hmq,
      getD_of_prefix hqr.2.1 (by simpa [← q.sameLength] using hmq)]
    exact hpq.2.2.2 m hm hmq
  · exact hqr.2.2.2 m ⟨Nat.le_of_not_gt hmq, hm.2.1.trans_le hpq.2.2.1, hm.2.2⟩ hmr

theorem extends_antisymm {A : ℕ → Oracle} {p q : Condition}
    (hpq : Extends A p q) (hqp : Extends A q p) : p = q := by
  have hl := hpq.1.eq_of_length (Nat.le_antisymm hpq.1.length_le hqp.1.length_le)
  have hr := hpq.2.1.eq_of_length (Nat.le_antisymm hpq.2.1.length_le hqp.2.1.length_le)
  have ha := Nat.le_antisymm hpq.2.2.1 hqp.2.2.1
  cases p
  cases q
  simp_all

def activate (p : Condition) (k : ℕ) : Condition :=
  ⟨p.left, p.right, p.sameLength, max p.active k⟩

theorem activate_extends (A : ℕ → Oracle) (p : Condition) (k : ℕ) :
    Extends A p (activate p k) := by
  refine ⟨List.prefix_rfl, List.prefix_rfl, Nat.le_max_left _ _, ?_⟩
  intro m hm hlt
  exact False.elim (Nat.not_lt_of_ge hm.1 hlt)

theorem active_dense (A : ℕ → Oracle) (p : Condition) (k : ℕ) :
    ∃ q, Extends A p q ∧ k < q.active :=
  ⟨activate p (k+1), activate_extends A p (k+1),
    Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_right _ _)⟩

def append (p : Condition) (s : List Bool) : Condition where
  left := p.left ++ s
  right := p.right ++ s
  sameLength := by simp [p.sameLength]
  active := p.active

theorem append_extends (A : ℕ → Oracle) (p : Condition) (s : List Bool) :
    Extends A p (append p s) := by
  refine ⟨List.prefix_append _ _, List.prefix_append _ _, le_rfl, ?_⟩
  intro m hm _
  simp only [append, List.getD_eq_getElem?_getD, List.getElem?_append]
  rw [ite_eq_right (Nat.not_lt.mpr hm.1),
    ite_eq_right (by simpa [← p.sameLength] using Nat.not_lt.mpr hm.1), p.sameLength]

theorem arbitrary_left_extension (A : ℕ → Oracle) (p : Condition)
    (s : List Bool) (hs : p.left <+: s) :
    ∃ q, Extends A p q ∧ q.left = s := by
  obtain ⟨u, rfl⟩ := hs
  exact ⟨append p u, append_extends A p u, rfl⟩

theorem length_dense (A : ℕ → Oracle) (p : Condition) (n : ℕ) :
    ∃ q, Extends A p q ∧ n ≤ q.left.length := by
  refine ⟨append p (List.replicate n false), append_extends A p _, ?_⟩
  simp [append]

theorem codingLocation_unbounded (A : ℕ → Oracle) (p : Condition) (k : ℕ)
    (hk : k < p.active) (hinf : {a | A k a = true}.Infinite) (n : ℕ) :
    ∃ a, A k a = true ∧ max n p.left.length ≤ Nat.pair k a ∧
      CodingLocation A p (Nat.pair k a) := by
  have hi : (Nat.pair k '' {a | A k a = true}).Infinite :=
    hinf.image (fun a _ b _ h => (Nat.pair_eq_pair.mp h).2)
  have hex : ∃ m ∈ Nat.pair k '' {a | A k a = true}, max n p.left.length < m := by
    by_contra h
    apply hi
    apply (Set.finite_le_nat (max n p.left.length)).subset
    intro m hm
    exact Nat.le_of_not_gt (fun hgt => h ⟨m, hm, hgt⟩)
  obtain ⟨m, ⟨a, ha, rfl⟩, hm⟩ := hex
  refine ⟨a, ha, Nat.le_of_lt hm, ?_⟩
  simp only [CodingLocation, Nat.unpair_pair]
  exact ⟨le_trans (Nat.le_max_right _ _) (Nat.le_of_lt hm), hk, ha⟩

end TuringRigidity.CodingForcing

end OAI
