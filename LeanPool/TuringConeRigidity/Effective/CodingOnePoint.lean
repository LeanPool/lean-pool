/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/CodingOnePoint.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.CodingAgreement

/-!
# Coding One Point
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CodingOnePoint
open CodingForcing CodingAgreement

theorem prefix_set_of_le {s t : List Bool} (h : s <+: t) (m : ℕ)
    (hm : s.length ≤ m) (b : Bool) : s <+: t.set m b := by
  obtain ⟨u, rfl⟩ := h
  rw [List.set_append_right _ _ hm]
  exact List.prefix_append _ _

theorem set_prefix_set {s t : List Bool} (h : s <+: t) (m : ℕ)
    (hm : m < s.length) (b : Bool) : s.set m b <+: t.set m b := by
  obtain ⟨u, rfl⟩ := h
  rw [List.set_append_left _ _ hm]
  exact List.prefix_append _ _

/-- Change one position of the left word while preserving its length and the right word. -/
def changeLeft (q : Condition) (m : ℕ) (b : Bool) : Condition where
  left := q.left.set m b
  right := q.right
  sameLength := by simpa using q.sameLength
  active := q.active

theorem changeLeft_extends {A : ℕ → Oracle} {p q : Condition} (hpq : Extends A p q)
    (m : ℕ) (hm : p.left.length ≤ m) (hnc : ¬ CodingLocation A p m) (b : Bool) :
    Extends A p (changeLeft q m b) := by
  refine ⟨prefix_set_of_le hpq.1 m hm b, hpq.2.1, hpq.2.2.1, ?_⟩
  intro j hj hjlen
  have hne : m ≠ j := by
    intro h
    subst j
    exact hnc hj
  have heq := hpq.2.2.2 j hj (by simpa [changeLeft] using hjlen)
  simpa [changeLeft, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne] using heq

theorem split_coding_or_divergence {A : ℕ → Oracle} {Y : Oracle} {e₀ e₁ : OracleCode}
    {p r : Condition} (hn : NoDisagreement A Y e₀ e₁ p) (hpr : Extends A p r)
    (m : ℕ) (hm : p.left.length ≤ m) (hmr : m < r.left.length) (b : Bool)
    (n v w : ℕ) (hvw : v ≠ w)
    (hv : v ∈ CommonIdeal.run Y e₀ r.left n)
    (hw : w ∈ CommonIdeal.run Y e₀ (r.left.set m b) n) :
    CodingLocation A p m ∨
      ∀ q, Extends A r q → ∀ c, c ∉ CommonIdeal.run Y e₁ q.right n := by
  by_cases hc : CodingLocation A p m
  · exact Or.inl hc
  · right
    intro q hrq c hvc
    have hpq := extends_trans hpr hrq
    have hpc := changeLeft_extends hpq m hm hc b
    have hvq := CommonIdeal.run_mono hrq.1 n v hv
    have hwq := CommonIdeal.run_mono (set_prefix_set hrq.1 m hmr b) n w hw
    have hveq : v = c := by
      by_contra hne
      exact hn q hpq ⟨n, v, c, hne, hvq, hvc⟩
    have hweq : w = c := by
      by_contra hne
      exact hn (changeLeft q m b) hpc ⟨n, w, c, hne, hwq, hvc⟩
    exact hvw (hveq.trans hweq.symm)

end TuringRigidity.CodingOnePoint

end OAI
