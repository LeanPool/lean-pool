/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PosetHomotopy.FiniteSpace.Fence
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Beat points and strong deformation retracts (roadmap 1.3)

A beat point of a preorder (`IsBeatPoint`) is an element `x` such that the elements strictly
below `x` have a largest element, or the elements strictly above `x` have a smallest one
(J. A. Barmak, *Algebraic Topology of Finite Topological Spaces and Applications*, Lecture Notes
in Math. 2032, Springer, 2011, Definition 1.3.3). Removing a beat point of a finite `T₀` space
leaves a strong deformation retract (`exists_retraction_of_isBeatPoint`, Barmak 2011,
Proposition 1.3.4).

Strong deformation retracts are handled as sets `Y ⊆ X` with a self-map `r` of `X` landing in `Y`,
fixing `Y`, and homotopic to the identity relative to `Y` (`IsStrongDeformationRetract`); a step
`IsStrongDeformationRetract.diff` removes from such a `Y` a set `O` through a map comparable with
the identity on `Y`, so that such steps compose.
-/

@[expose] public section

open Topology

namespace LeanPool.PosetHomotopy

/-- **Roadmap 1.3.** A beat point of a preorder: either the elements strictly below `x` have a
largest element (a down beat point) or the elements strictly above `x` have a smallest one (an up
beat point). -/
def IsBeatPoint {P : Type*} [Preorder P] (x : P) : Prop :=
  (∃ y, y < x ∧ ∀ z, z < x → z ≤ y) ∨ (∃ y, x < y ∧ ∀ z, x < z → y ≤ z)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem homotopicRel_mono {f g : C(X, Y)} {S S' : Set X}
    (h : f.HomotopicRel g S) (hS : S' ⊆ S) : f.HomotopicRel g S' := by
  obtain ⟨F⟩ := h
  exact ⟨{ toHomotopy := F.toHomotopy, prop' := fun t x hx => F.prop t x (hS hx) }⟩

/-- `Y` is a strong deformation retract of `X`: a self-map of `X` lands in `Y`, fixes `Y`, and is
homotopic to the identity relative to `Y`. -/
def IsStrongDeformationRetract (Y : Set X) : Prop :=
  ∃ r : C(X, X), (∀ z, r z ∈ Y) ∧ (∀ y ∈ Y, r y = y) ∧ r.HomotopicRel (ContinuousMap.id X) Y

theorem isStrongDeformationRetract_univ : IsStrongDeformationRetract (Set.univ : Set X) :=
  ⟨ContinuousMap.id X, fun _ => trivial, fun _ _ => rfl, ContinuousMap.HomotopicRel.refl _⟩

/-- Removing a set `O` from a strong deformation retract `Y`, through a map `ρ` sending `Y` to
`Y \ O`, fixing `Y \ O`, preserving specialization on `Y` and comparable with the identity on `Y`,
leaves a strong deformation retract. -/
theorem IsStrongDeformationRetract.diff [AlexandrovDiscrete X] {Y O : Set X}
    (hY : IsStrongDeformationRetract Y) (ρ : X → X) (hρY : ∀ z ∈ Y, ρ z ∈ Y \ O)
    (hρfix : ∀ z ∈ Y \ O, ρ z = z) (hρmono : ∀ a ∈ Y, ∀ b ∈ Y, a ⤳ b → ρ a ⤳ ρ b)
    (hcomp : (∀ z ∈ Y, z ⤳ ρ z) ∨ ∀ z ∈ Y, ρ z ⤳ z) : IsStrongDeformationRetract (Y \ O) := by
  obtain ⟨r, hrY, hrfix, hr⟩ := hY
  let R : C(X, X) := ⟨ρ ∘ r, continuous_of_specializes fun a b hab =>
    hρmono _ (hrY a) _ (hrY b) (hab.map r.continuous)⟩
  have hRfix : ∀ y ∈ Y \ O, R y = y := fun y hy => by
    change ρ (r y) = y
    rw [hrfix y hy.1, hρfix y hy]
  have hRr : R.HomotopicRel r (Y \ O) := by
    have heq : Set.EqOn R r (Y \ O) := fun y hy => by rw [hRfix y hy, hrfix y hy.1]
    rcases hcomp with h | h
    · exact (homotopicRel_of_specializes_of_eqOn r R (fun z => h _ (hrY z)) heq.symm).symm
    · exact homotopicRel_of_specializes_of_eqOn R r (fun z => h _ (hrY z)) heq
  exact ⟨R, fun z => hρY _ (hrY z), hRfix, hRr.trans (homotopicRel_mono hr Set.sdiff_subset)⟩

/-- A strong deformation retract, read as a retraction onto the subspace. -/
theorem IsStrongDeformationRetract.exists_retraction {Y : Set X}
    (hY : IsStrongDeformationRetract Y) :
    ∃ r : C(X, Y), (∀ y : Y, r y = y) ∧
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(Y, X)).comp r).HomotopicRel
        (ContinuousMap.id X) Y := by
  obtain ⟨r, hrY, hrfix, hr⟩ := hY
  exact ⟨⟨fun z => ⟨r z, hrY z⟩, r.continuous.subtype_mk _⟩, fun y => Subtype.ext (hrfix y y.2), hr⟩

/-- Specialization, read in the order of `Specialization X`. -/
theorem specializes_iff_toEquiv_le {a b : X} :
    a ⤳ b ↔ Specialization.toEquiv b ≤ Specialization.toEquiv a := Iff.rfl

section Order

variable [T0Space X]

/-- The retraction collapsing a beat point `x` onto `y₀`. -/
theorem isStrongDeformationRetract_diff_singleton [AlexandrovDiscrete X] {Y : Set X}
    (hY : IsStrongDeformationRetract Y) {x y₀ : X} (hx : x ∈ Y) (hy₀ : y₀ ∈ Y) (hne : y₀ ≠ x)
    (hbeat : (Specialization.toEquiv y₀ < Specialization.toEquiv x ∧
        ∀ z ∈ Y, Specialization.toEquiv z < Specialization.toEquiv x →
          Specialization.toEquiv z ≤ Specialization.toEquiv y₀) ∨
      (Specialization.toEquiv x < Specialization.toEquiv y₀ ∧
        ∀ z ∈ Y, Specialization.toEquiv x < Specialization.toEquiv z →
          Specialization.toEquiv y₀ ≤ Specialization.toEquiv z)) :
    IsStrongDeformationRetract (Y \ {x}) := by
  classical
  let ρ : X → X := fun z => if z = x then y₀ else z
  have hρx : ρ x = y₀ := by simp [ρ]
  have hρz : ∀ z, z ≠ x → ρ z = z := fun z hz => by simp [ρ, hz]
  refine hY.diff ρ (fun z hz => ?_) (fun z hz => hρz z hz.2) (fun a ha b hb hab => ?_) ?_
  · by_cases h : z = x
    · subst h; rw [hρx]; exact ⟨hy₀, hne⟩
    · rw [hρz z h]; exact ⟨hz, h⟩
  · rw [specializes_iff_toEquiv_le] at hab ⊢
    by_cases ha' : a = x <;> by_cases hb' : b = x
    · subst ha' hb'; exact le_rfl
    · subst ha'
      rw [hρx, hρz b hb']
      rcases hbeat with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact h₂ b hb (lt_of_le_of_ne hab fun h => hb' (Specialization.toEquiv.injective h))
      · exact hab.trans h₁.le
    · subst hb'
      rw [hρx, hρz a ha']
      rcases hbeat with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact h₁.le.trans hab
      · exact h₂ a ha (lt_of_le_of_ne hab fun h => ha' (Specialization.toEquiv.injective h).symm)
    · rw [hρz a ha', hρz b hb']; exact hab
  · rcases hbeat with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · refine Or.inl fun z _ => ?_
      by_cases h : z = x
      · subst h; rw [hρx]; exact h₁.le
      · rw [hρz z h]
    · refine Or.inr fun z _ => ?_
      by_cases h : z = x
      · subst h; rw [hρx]; exact h₁.le
      · rw [hρz z h]

/-- **Roadmap 1.3.** Removing a beat point of a finite `T₀` space leaves a strong deformation
retract: a retraction onto the complement of the point whose composite with the inclusion is
homotopic to the identity relative to that complement. -/
theorem exists_retraction_of_isBeatPoint [Finite X] (x : X)
    (hx : IsBeatPoint (Specialization.toEquiv x)) :
    ∃ r : C(X, {y : X // y ≠ x}), (∀ y : {y : X // y ≠ x}, r y = y) ∧
      ((⟨Subtype.val, continuous_subtype_val⟩ : C({y : X // y ≠ x}, X)).comp r).HomotopicRel
        (ContinuousMap.id X) {y | y ≠ x} := by
  have h : IsStrongDeformationRetract ({y | y ≠ x} : Set X) := by
    have hset : ({y | y ≠ x} : Set X) = Set.univ \ {x} := by ext; simp
    rw [hset]
    rcases hx with ⟨y, hy, hy'⟩ | ⟨y, hy, hy'⟩
    · exact isStrongDeformationRetract_diff_singleton isStrongDeformationRetract_univ trivial
        trivial (fun h => hy.ne h) (Or.inl ⟨hy, fun z _ hz => hy' _ hz⟩)
    · exact isStrongDeformationRetract_diff_singleton isStrongDeformationRetract_univ trivial
        trivial (fun h => hy.ne' h) (Or.inr ⟨hy, fun z _ hz => hy' _ hz⟩)
  exact h.exists_retraction

end Order

end LeanPool.PosetHomotopy
