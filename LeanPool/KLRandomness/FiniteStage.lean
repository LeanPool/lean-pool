/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineObservation
public import LeanPool.KLRandomness.FiniteMeasure
public import LeanPool.KLRandomness.ScanMeasure
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Logic.Function.DependsOn

/-!
# Finite-stage affine identities for adaptive transcripts

Fix finitely many distinct input coordinates. The old constraints and the
specified transcript depend on an observed part of those coordinates. If the
new constraint's map on the complementary unread coordinates is surjective,
each syndrome cuts the probability of every observed event by exactly `2⁻ʳ`.

The conditional version uses Mathlib's actual conditional measure. Its
intersection identity also holds for zero-probability transcript events; it
does not divide by the probability of a transcript.
-/

@[expose] public section

namespace Klr.FiniteStage

open MeasureTheory ProbabilityTheory
open AffineObservation FiniteMeasure
open scoped ENNReal

variable {ι : Type*} {r : ℕ}

/-- An event specified by a condition on some of the finite input coordinates. -/
def observedEvent (e : ι → ℕ) (O : Set ι) (P : (O → ZMod 2) → Prop) : Set Cantor :=
  {X | P (observedPart O (coordinateValues e X))}

/-- The event that a finite system of parity equations has the specified syndrome. -/
def affineEvent (e : ι → ℕ)
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (y : Fin r → ZMod 2) : Set Cantor :=
  {X | D (coordinateValues e X) = y}

theorem measurableSet_observedEvent [Finite ι] (e : ι → ℕ) (O : Set ι)
    (P : (O → ZMod 2) → Prop) : MeasurableSet (observedEvent e O P) :=
  measurableSet_coordinate_event_f2 e (background O P)

theorem measurableSet_affineEvent [Finite ι] (e : ι → ℕ)
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (y : Fin r → ZMod 2) : MeasurableSet (affineEvent e D y) :=
  measurableSet_coordinate_event_f2 e {x | D x = y}

/-- Any event depending only on the observed input positions has an observed-value predicate.
This converts a support condition into the representation used by the counting theorem. -/
theorem exists_observedEvent_of_dependsOn (e : ι → ℕ) (O : Set ι) (A : Set Cantor)
    (hA : DependsOn (fun X : Cantor => X ∈ A) (e '' O)) :
    ∃ P : (O → ZMod 2) → Prop, A = observedEvent e O P := by
  have hf : Function.FactorsThrough (fun X : Cantor => X ∈ A)
      (fun X => observedPart O (coordinateValues e X)) := by
    intro X Y h
    apply hA
    rintro n ⟨i, hi, rfl⟩
    exact boolEquivF2.injective (congrFun h ⟨i, hi⟩)
  obtain ⟨P, hP⟩ := (Function.factorsThrough_iff _).mp hf
  refine ⟨P, ?_⟩
  ext X
  exact iff_of_eq (congrFun hP X)

/-- Events depending on disjoint finite sets of input positions are independent. -/
theorem fairCoin_inter_of_disjoint_support (A B : Set Cantor) (H I : Finset ℕ)
    (hA : DependsOn (fun X : Cantor => X ∈ A) (H : Set ℕ))
    (hB : DependsOn (fun X : Cantor => X ∈ B) (I : Set ℕ))
    (hdis : Disjoint H I) : fairCoin (A ∩ B) = fairCoin A * fairCoin B := by
  obtain ⟨P, hP⟩ := dependsOn_iff_exists_comp.mp hA
  obtain ⟨Q, hQ⟩ := dependsOn_iff_exists_comp.mp hB
  have heA : A = {X | coordinateBits (fun i : H => i.val) X ∈ {o | P o}} := by
    ext X
    exact iff_of_eq (congrFun hP X)
  have heB : B = {X | coordinateBits (fun i : I => i.val) X ∈ {o | Q o}} := by
    ext X
    exact iff_of_eq (congrFun hQ X)
  rw [heA, heB]
  apply fairCoin_coordinate_events_disjoint _ Subtype.val_injective _ Subtype.val_injective
  intro i j h
  apply Finset.disjoint_left.mp hdis i.property
  simpa only [h] using j.property

@[simp] theorem observedEvent_and (e : ι → ℕ) (O : Set ι)
    (P Q : (O → ZMod 2) → Prop) :
    observedEvent e O (fun o => P o ∧ Q o) =
      observedEvent e O P ∩ observedEvent e O Q := rfl

/-- Full unread rank gives an exact syndrome factor for any observed background. -/
theorem fairCoin_observed_inter_affine [Finite ι] (e : ι → ℕ)
    (he : Function.Injective e)
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (P : (O → ZMod 2) → Prop)
    (y : Fin r → ZMod 2) (hD : Function.Surjective (unreadMap D O)) :
    fairCoin (observedEvent e O P ∩ affineEvent e D y) =
      (1 / 2 : ℝ≥0∞) ^ r * fairCoin (observedEvent e O P) := by
  let _ := Fintype.ofFinite ι
  exact fairCoin_coordinate_factor_of_card e he (joint D O P y) (background O P) r
    (card_joint_mul_pow_eq_card_background D O P y hD)

/-- The exact factor persists after conditioning on any earlier observed-coordinate event.
No positive-probability assumption on the transcript event `Q` is needed. -/
theorem cond_observed_inter_affine [Finite ι] (e : ι → ℕ)
    (he : Function.Injective e)
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (P Q : (O → ZMod 2) → Prop)
    (y : Fin r → ZMod 2) (hD : Function.Surjective (unreadMap D O)) :
    (cond fairCoin (observedEvent e O P))
        (observedEvent e O Q ∩ affineEvent e D y) =
      (1 / 2 : ℝ≥0∞) ^ r *
        (cond fairCoin (observedEvent e O P)) (observedEvent e O Q) := by
  rw [cond_apply (measurableSet_observedEvent e O P),
    cond_apply (measurableSet_observedEvent e O P), ← Set.inter_assoc,
    ← observedEvent_and,
    fairCoin_observed_inter_affine e he D O (fun o => P o ∧ Q o) y hD]
  rw [observedEvent_and]
  ac_rfl

/-- Under a nonnull earlier background, every syndrome still has probability `2⁻ʳ`. -/
theorem cond_affine [Finite ι] (e : ι → ℕ) (he : Function.Injective e)
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (P : (O → ZMod 2) → Prop)
    (y : Fin r → ZMod 2) (hD : Function.Surjective (unreadMap D O))
    (hP : fairCoin (observedEvent e O P) ≠ 0) :
    (cond fairCoin (observedEvent e O P)) (affineEvent e D y) =
      (1 / 2 : ℝ≥0∞) ^ r := by
  rw [cond_apply (measurableSet_observedEvent e O P),
    fairCoin_observed_inter_affine e he D O P y hD, mul_left_comm,
    ENNReal.inv_mul_cancel hP (measure_ne_top _ _), mul_one]

/-- The fixed transcript's requirements, written as a predicate on observed coordinates. -/
def transcriptPredicate (v : List Bool) {O : Set ι} (q : Fin v.length → O)
    (o : O → ZMod 2) : Prop :=
  ∀ i, o (q i) = boolEquivF2 (v.getD i.val false)

/-- Once a finite adaptive transcript is fixed, its queries are fixed coordinates. -/
theorem transcriptEvent_eq_observedEvent (e : ι → ℕ) (O : Set ι)
    (π : ScanRule) (v : List Bool) (q : Fin v.length → O)
    (hq : ∀ i, e (q i).val = π.query (v.take i.val)) :
    {X | π.transcript X v.length = v} =
      observedEvent e O (transcriptPredicate v q) := by
  ext X
  rw [Set.mem_ofPred_eq, π.transcript_eq_iff]
  change (∀ i < v.length, X (π.query (v.take i)) = v.getD i false) ↔
    ∀ i : Fin v.length,
      boolEquivF2 (X (e (q i).val)) = boolEquivF2 (v.getD i.val false)
  simp only [hq, Equiv.apply_eq_iff_eq]
  exact ⟨fun h i => h i.val i.isLt, fun h i hi => h ⟨i, hi⟩⟩

/-- The paper's finite-stage intersection identity. Earlier constraints are encoded by `P`;
their coordinates and the transcript's queries lie in `O`. The unread columns of the new
constraint are required to have full row rank, expressed by surjectivity. -/
theorem cond_transcript_inter_affine [Finite ι] (e : ι → ℕ)
    (he : Function.Injective e)
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (P : (O → ZMod 2) → Prop)
    (π : ScanRule) (v : List Bool) (q : Fin v.length → O)
    (hq : ∀ i, e (q i).val = π.query (v.take i.val))
    (y : Fin r → ZMod 2) (hD : Function.Surjective (unreadMap D O)) :
    (cond fairCoin (observedEvent e O P))
        ({X | π.transcript X v.length = v} ∩ affineEvent e D y) =
      (1 / 2 : ℝ≥0∞) ^ r *
        (cond fairCoin (observedEvent e O P)) {X | π.transcript X v.length = v} := by
  rw [transcriptEvent_eq_observedEvent e O π v q hq]
  exact cond_observed_inter_affine e he D O P (transcriptPredicate v q) y hD

end Klr.FiniteStage
