/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/Assembly.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.NumberTheory.Real.Irrational

public import LeanPool.TuringConeRigidity.Computability.Cuts
public import LeanPool.TuringConeRigidity.Computability.Joins
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Assembly
-/


@[expose] public section

namespace OAI

open Set Filter Topology
namespace TuringRigidity

/-- Every degree automorphism has a measurable lift on Boolean oracle representatives. -/
def BorelRepresentation : Prop :=
  ∀ π : Degree ≃o Degree, ∃ F : Oracle → Oracle,
    Measurable F ∧ ∀ A, degree (F A) = π (degree A)

/-- Turing-degree bounds for real-cut addition, subtraction, rational scaling, and rational
translation. -/
structure CutArithmetic : Prop where
  add : ∀ x y : ℝ, realDegree (x+y) ≤ realDegree x ⊔ realDegree y
  sub : ∀ x y : ℝ, realDegree (x-y) ≤ realDegree x ⊔ realDegree y
  smul : ∀ (q : ℚ) (x : ℝ), realDegree ((q : ℝ)*x) ≤ realDegree x
  translate : ∀ (x : ℝ) (q : ℚ), realDegree (x+(q : ℝ)) ≤ realDegree x

/-- Every nonzero Turing degree is the cut degree of an irrational real strictly between zero
and one. -/
def IrrationalDegreeCoverage : Prop := ∀ a : Degree, a ≠ ⊥ →
  ∃ t : ℝ, Irrational t ∧ 0 < t ∧ t < 1 ∧ realDegree t = a

/-- If `Y` is not reducible to `A`, pairs whose joined cuts with `A` compute `Y` form a meagre
set. -/
def CategoryAvoidance : Prop := ∀ A Y : Oracle, ¬ Reduces Y A →
  IsMeagre {p : ℝ × ℝ | Reduces Y (join (join A (cut p.1)) (cut p.2))}

/-- Join four values of `F` at the translated points used by the recovery construction. -/
noncomputable def fourTuple (F : ℝ → Oracle) (t u v : ℝ) (δ : ℚ) : Oracle :=
  join (join (join (F u) (F (u-v))) (F (v-u+(δ : ℝ)*t)))
    (F (v-u+(δ : ℝ)*(t-1)))

/-- A measurable countable-fiber map satisfying an additive reducibility bound recovers each
irrational cut from four values on a residual set. -/
def FourValueRecovery : Prop := ∀ F : ℝ → Oracle,
  Measurable F → (∀ B, {x | F x = B}.Countable) →
  (∀ x y, Reduces (F (x+y)) (join (F x) (F y))) →
  ∀ t : ℝ, Irrational t → 0 < t → t < 1 →
  ∃ G : Set (ℝ × ℝ), G ∈ residual (ℝ × ℝ) ∧
    ∀ p ∈ G, ∃ δ : ℚ, 0 < δ ∧ δ < 1 ∧ Reduces (cut t) (fourTuple F t p.1 p.2 δ)

theorem lift_of_representation (hrep : BorelRepresentation) (harith : CutArithmetic)
    (π : Degree ≃o Degree) :
    ∃ F : ℝ → Oracle, Measurable F ∧
      (∀ B, {x | F x = B}.Countable) ∧
      (∀ x, degree (F x) = π (realDegree x)) ∧
      (∀ x y, Reduces (F (x+y)) (join (F x) (F y))) := by
  obtain ⟨F₀, hmeas, hF₀⟩ := hrep π
  let F : ℝ → Oracle := fun x => F₀ (cut x)
  have hF : ∀ x, degree (F x) = π (realDegree x) := fun x => hF₀ (cut x)
  refine ⟨F, hmeas.comp cut_measurable, represented_real_map_countable_fibers π F hF, hF, ?_⟩
  intro x y
  change degree (F (x+y)) ≤ degree (F x) ⊔ degree (F y)
  rw [hF, hF, hF, ← π.map_sup]
  exact π.monotone (harith.add x y)

theorem fourTuple_bound (harith : CutArithmetic) (π : Degree ≃o Degree)
    (F : ℝ → Oracle) (hF : ∀ x, degree (F x) = π (realDegree x))
    (t u v : ℝ) (δ : ℚ) :
    degree (fourTuple F t u v δ) ≤ π (realDegree t ⊔ realDegree u ⊔ realDegree v) := by
  let b := realDegree t ⊔ realDegree u ⊔ realDegree v
  have ht : realDegree t ≤ b := le_trans le_sup_left le_sup_left
  have hu : realDegree u ≤ b := le_trans le_sup_right le_sup_left
  have hv : realDegree v ≤ b := le_sup_right
  have huv : realDegree (u-v) ≤ b := (harith.sub u v).trans (sup_le hu hv)
  have hvu : realDegree (v-u) ≤ b := (harith.sub v u).trans (sup_le hv hu)
  have hδt : realDegree ((δ : ℝ)*t) ≤ b := (harith.smul δ t).trans ht
  have ht1 : realDegree (t-1) ≤ realDegree t := by
    simpa [sub_eq_add_neg] using harith.translate t (-1)
  have hδt1 : realDegree ((δ : ℝ)*(t-1)) ≤ b :=
    (harith.smul δ (t-1)).trans (ht1.trans ht)
  have h3 : realDegree (v-u+(δ : ℝ)*t) ≤ b :=
    (harith.add _ _).trans (sup_le hvu hδt)
  have h4 : realDegree (v-u+(δ : ℝ)*(t-1)) ≤ b :=
    (harith.add _ _).trans (sup_le hvu hδt1)
  have hvalue : ∀ x : ℝ, realDegree x ≤ b → degree (F x) ≤ π b := by
    intro x hx
    rw [hF]
    exact π.monotone hx
  change ((degree (F u) ⊔ degree (F (u-v))) ⊔ degree (F (v-u+(δ : ℝ)*t))) ⊔
    degree (F (v-u+(δ : ℝ)*(t-1))) ≤ π b
  exact sup_le (sup_le (sup_le (hvalue _ hu) (hvalue _ huv)) (hvalue _ h3)) (hvalue _ h4)

theorem inverse_le_realDegree_of_obligations
    (hrep : BorelRepresentation) (harith : CutArithmetic)
    (hrec : FourValueRecovery) (havoid : CategoryAvoidance)
    (π : Degree ≃o Degree) (t : ℝ) (ht : Irrational t) (ht0 : 0 < t) (ht1 : t < 1) :
    π.symm (realDegree t) ≤ realDegree t := by
  obtain ⟨F, hmeas, hfiber, hF, hadd⟩ := lift_of_representation hrep harith π
  obtain ⟨G, hG, hrecovery⟩ := hrec F hmeas hfiber hadd t ht ht0 ht1
  have hgeneric : ∀ p ∈ G,
      π.symm (realDegree t) ≤ realDegree t ⊔ realDegree p.1 ⊔ realDegree p.2 := by
    intro p hp
    obtain ⟨δ, _, _, hδ⟩ := hrecovery p hp
    have hle : realDegree t ≤ π (realDegree t ⊔ realDegree p.1 ⊔ realDegree p.2) :=
      le_trans hδ (fourTuple_bound harith π F hF t p.1 p.2 δ)
    simpa using π.symm.monotone hle
  by_contra hnle
  obtain ⟨Y, hY⟩ := degree_surjective (π.symm (realDegree t))
  have hnred : ¬ Reduces Y (cut t) := by
    intro h
    apply hnle
    rw [← hY]
    exact h
  have hmeager := havoid (cut t) Y hnred
  have hp : ∃ p : ℝ × ℝ, p ∈ G ∧
      ¬ Reduces Y (join (join (cut t) (cut p.1)) (cut p.2)) :=
    (dense_of_mem_residual (inter_mem hG hmeager)).nonempty
  obtain ⟨p, hpG, hpnot⟩ := hp
  apply hpnot
  change degree Y ≤ realDegree t ⊔ realDegree p.1 ⊔ realDegree p.2
  rw [hY]
  exact hgeneric p hpG

theorem main_of_obligations (hrep : BorelRepresentation) (harith : CutArithmetic)
    (hcover : IrrationalDegreeCoverage) (hrec : FourValueRecovery)
    (havoid : CategoryAvoidance) : MainTheorem := by
  apply order_rigidity_of_inverse_le
  intro π a
  by_cases ha : a = ⊥
  · subst a
    simp
  · obtain ⟨t, ht, ht0, ht1, rfl⟩ := hcover a ha
    exact inverse_le_realDegree_of_obligations hrep harith hrec havoid π t ht ht0 ht1

end TuringRigidity

end OAI
