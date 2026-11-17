/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/QuotientDense.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.ForcingProjection
public import Mathlib.Basic.Countable.Defs

/-!
# Quotient Dense
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.QuotientDense
open Set CountableForcing ForcingProjection
universe u v
variable {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]

/-- Projected conditions either incompatible with the given image or below an image of a
stronger condition in `D`. -/
def requirement (π : Projection P Q) (D : Set P) (p : P) : Set Q :=
  {a | (¬ ∃ b, b ≤ a ∧ b ≤ π.map p) ∨
    ∃ r, r ≤ p ∧ r ∈ D ∧ a ≤ π.map r}

theorem requirement_dense (π : Projection P Q) (D : Set P) (hD : Dense D)
    (p : P) : Dense (requirement π D p) := by
  classical
  intro a
  by_cases h : ∃ b, b ≤ a ∧ b ≤ π.map p
  · obtain ⟨b,hba,hbp⟩ := h
    obtain ⟨r,hrp,hrb⟩ := π.lift p b hbp
    obtain ⟨s,hsr,hsD⟩ := hD r
    exact ⟨π.map s,((π.mono hsr).trans hrb).trans hba,
      Or.inr ⟨s,hsr.trans hrp,hsD,le_rfl⟩⟩
  · exact ⟨a,le_rfl,Or.inl h⟩

/-- Restrict a family of conditions to the quotient poset over `H`. -/
def restriction (π : Projection P Q) (H : GenericFilter Q) (D : Set P) :
    Set (QuotientConditions π H) := {p | p.val ∈ D}

theorem restriction_dense (π : Projection P Q) (H : GenericFilter Q) (D : Set P)
    (hH : ∀ p, ∃ a ∈ H.carrier, a ∈ requirement π D p) :
    Dense (restriction π H D) := by
  intro p
  obtain ⟨a,ha,hreq⟩ := hH p.val
  rcases hreq with hno | ⟨r,hrp,hrD,har⟩
  · obtain ⟨b,_,hba,hbp⟩ := H.directed ha p.property
    exact False.elim (hno ⟨b,hba,hbp⟩)
  · exact ⟨⟨r,H.upper har ha⟩,hrp,hrD⟩

theorem lift_meets (π : Projection P Q) (H : GenericFilter Q)
    (K : GenericFilter (QuotientConditions π H)) (D : Set P)
    (hK : ∃ p ∈ K.carrier, p ∈ restriction π H D) :
    ∃ p ∈ (liftFilter π H K).carrier, p ∈ D := by
  obtain ⟨p,hp,hpD⟩ := hK
  exact ⟨p.val,⟨p,hp,le_rfl⟩,hpD⟩

theorem lift_generic (π : Projection P Q) (H : GenericFilter Q)
    (K : GenericFilter (QuotientConditions π H)) (D : ℕ → Set P)
    (hK : GenericFor (fun n => restriction π H (D n)) K) :
    GenericFor D (liftFilter π H K) := fun n => lift_meets π H K (D n) (hK n)

theorem quotient_generic_iff (π : Projection P Q) (G : GenericFilter P)
    (D : ℕ → Set P) :
    GenericFor (fun n => restriction π (imageFilter π G) (D n)) (quotientFilter π G) ↔
      GenericFor D G := by
  constructor
  · intro h n
    obtain ⟨p,hp,hpD⟩ := h n
    exact ⟨p.val,hp,hpD⟩
  · intro h n
    obtain ⟨p,hp,hpD⟩ := h n
    exact ⟨⟨p,p,hp,le_rfl⟩,hp,hpD⟩

theorem quotient_countable [Countable P] (π : Projection P Q) (H : GenericFilter Q) :
    Countable (QuotientConditions π H) := inferInstanceAs (Countable {p // π.map p ∈ H.carrier})

end TuringRigidity.QuotientDense

end OAI
