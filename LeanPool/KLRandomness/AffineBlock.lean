/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.FiniteStage
import Mathlib.Tactic.NormNum

/-!
# Disjoint affine blocks and finite-stage laws

This module instantiates the finite-coordinate identity with actual finite sets
of input positions. The ambient coordinates, the old-event representation and
the transcript's coordinate witnesses are constructed in the proof, rather
than left as hypotheses of the block theorem.
-/

@[expose] public section

namespace Klr

open MeasureTheory ProbabilityTheory
open AffineObservation FiniteMeasure FiniteStage
open scoped ENNReal

namespace ScanRule

/-- The input positions queried along a prescribed finite transcript. -/
def queriedPositions (π : ScanRule) (v : List Bool) : Finset ℕ :=
  Finset.univ.image (fun i : Fin v.length => π.query (v.take i.val))

theorem query_mem_queriedPositions (π : ScanRule) (v : List Bool) (i : Fin v.length) :
    π.query (v.take i.val) ∈ π.queriedPositions v := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

@[simp] theorem queriedPositions_nil (π : ScanRule) : π.queriedPositions [] = ∅ := by
  simp [queriedPositions]

end ScanRule

/-- A finite full-row-rank system of parity equations and its chosen syndrome. -/
structure AffineBlock where
  /-- Coordinates constrained by the affine equations. -/
  support : Finset ℕ
  /-- Number of independent parity equations. -/
  rank : ℕ
  /-- Surjective linear map defining the parity equations on the support. -/
  matrix : (support → ZMod 2) →ₗ[ZMod 2] (Fin rank → ZMod 2)
  fullRank : Function.Surjective matrix
  /-- Right-hand side of the parity equations. -/
  syndrome : Fin rank → ZMod 2

namespace AffineBlock

/-- The input event satisfying a block's parity equations. -/
def event (B : AffineBlock) : Set Cantor :=
  affineEvent (fun i : B.support => i.val) B.matrix B.syndrome

theorem measurableSet_event (B : AffineBlock) : MeasurableSet B.event :=
  measurableSet_affineEvent _ _ _

theorem dependsOn_event (B : AffineBlock) :
    DependsOn (fun X : Cantor => X ∈ B.event) (B.support : Set ℕ) := by
  intro X Y h
  have hv : coordinateValues (fun i : B.support => i.val) X =
      coordinateValues (fun i : B.support => i.val) Y := by
    funext i
    rw [coordinateValues_apply, coordinateValues_apply, h i.val i.property]
  change (B.matrix (coordinateValues _ X) = B.syndrome) =
    (B.matrix (coordinateValues _ Y) = B.syndrome)
  rw [hv]

/-- The columns already read along the fixed transcript. -/
def observed (B : AffineBlock) (π : ScanRule) (v : List Bool) : Set B.support :=
  {i | i.val ∈ π.queriedPositions v}

instance (B : AffineBlock) (π : ScanRule) (v : List Bool) :
    DecidablePred (· ∈ B.observed π v) :=
  fun i => inferInstanceAs (Decidable (i.val ∈ π.queriedPositions v))

/-- Full row rank of the columns still unread after this transcript. -/
def UnreadFullRank (B : AffineBlock) (π : ScanRule) (v : List Bool) : Prop :=
  Function.Surjective (unreadMap B.matrix (B.observed π v))

theorem unreadFullRank_nil (B : AffineBlock) (π : ScanRule) :
    B.UnreadFullRank π [] := by
  intro y
  obtain ⟨x, hx⟩ := B.fullRank y
  refine ⟨fun i => x i.val, ?_⟩
  change B.matrix (extendUnread (B.observed π []) (fun i => x i.val)) = y
  have he : extendUnread (B.observed π []) (fun i => x i.val) = x := by
    funext i
    change (if h : i ∈ B.observed π [] then 0 else x i) = x i
    simp [observed]
  rw [he, hx]

/-- Restriction from a larger finite ambient set to a block's coordinates. -/
def restrictCoordinates {S G : Finset ℕ} (h : S ⊆ G) :
    (G → ZMod 2) →ₗ[ZMod 2] (S → ZMod 2) where
  toFun x i := x ⟨i.val, h i.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extend a finite assignment by zero outside its support. -/
def extendCoordinates {S : Finset ℕ} (G : Finset ℕ) (x : S → ZMod 2) :
    G → ZMod 2 := fun i => if h : i.val ∈ S then x ⟨i.val, h⟩ else 0

@[simp] theorem restrict_extendCoordinates {S G : Finset ℕ} (h : S ⊆ G)
    (x : S → ZMod 2) : restrictCoordinates h (extendCoordinates G x) = x := by
  funext i
  simp [restrictCoordinates, extendCoordinates, i.property]

/-- An arbitrary earlier event on disjoint finite support satisfies the exact stage identity.
The full-rank hypothesis is solely about the new block's unread columns. -/
theorem finiteStage_identity_of_dependsOn (B : AffineBlock) (A : Set Cantor)
    (H : Finset ℕ) (hA : DependsOn (fun X : Cantor => X ∈ A) (H : Set ℕ))
    (hdis : Disjoint H B.support) (π : ScanRule) (v : List Bool)
    (hfull : B.UnreadFullRank π v) :
    (cond fairCoin A) ({X | π.transcript X v.length = v} ∩ B.event) =
      (1 / 2 : ℝ≥0∞) ^ B.rank *
        (cond fairCoin A) {X | π.transcript X v.length = v} := by
  classical
  let G := H ∪ B.support ∪ π.queriedPositions v
  have hH : H ⊆ G := by intro n hn; simp [G, hn]
  have hS : B.support ⊆ G := by intro n hn; simp [G, hn]
  have hQ : π.queriedPositions v ⊆ G := by intro n hn; simp [G, hn]
  let e : G → ℕ := Subtype.val
  let O : Set G := {i | i.val ∉ B.support ∨ i.val ∈ π.queriedPositions v}
  let D := B.matrix.comp (restrictCoordinates hS)
  let L (u : {i : B.support // i ∉ B.observed π v} → ZMod 2) : G → ZMod 2 :=
    extendCoordinates G (extendUnread (B.observed π v) u)
  have hzero : ∀ u, observedPart O (L u) = 0 := by
    intro u
    funext i
    rcases i.property with hi | hi
    · simp [observedPart, L, extendCoordinates, hi]
    · by_cases hs : i.val.val ∈ B.support
      · simp only [observedPart, L, extendCoordinates, dite_eq_left hs]
        change (if h : i.val.val ∈ π.queriedPositions v then 0
          else u ⟨⟨i.val.val, hs⟩, h⟩) = 0
        rw [dite_eq_left hi]
      · simp [observedPart, L, extendCoordinates, hs]
  have hsurj : Function.Surjective (fun u => D (L u)) := by
    intro y
    obtain ⟨u, hu⟩ := hfull y
    refine ⟨u, ?_⟩
    simpa [D, L, unreadMap, LinearMap.comp_apply] using hu
  have hD := unreadMap_surjective_of_supported_lift D O L hzero hsurj
  have hdep : DependsOn (fun X : Cantor => X ∈ A) (e '' O) := by
    apply hA.mono
    intro n hn
    exact ⟨⟨n, hH hn⟩, Or.inl (Finset.disjoint_left.mp hdis hn), rfl⟩
  obtain ⟨P, hP⟩ := exists_observedEvent_of_dependsOn e O A hdep
  let q : Fin v.length → O := fun i =>
    ⟨⟨π.query (v.take i.val), hQ (π.query_mem_queriedPositions v i)⟩,
      Or.inr (π.query_mem_queriedPositions v i)⟩
  have hq : ∀ i, e (q i).val = π.query (v.take i.val) := fun _ => rfl
  have h := cond_transcript_inter_affine e Subtype.val_injective D O P π v q hq
    B.syndrome hD
  rw [← hP] at h
  exact h

/-- The common support of finitely many earlier blocks. -/
def familySupport {κ : Type*} [Fintype κ] (B : κ → AffineBlock) : Finset ℕ :=
  Finset.univ.biUnion (fun k => (B k).support)

/-- The conjunction of all earlier block constraints. -/
def familyEvent {κ : Type*} (B : κ → AffineBlock) : Set Cantor :=
  {X | ∀ k, X ∈ (B k).event}

theorem measurableSet_familyEvent {κ : Type*} [Countable κ] (B : κ → AffineBlock) :
    MeasurableSet (familyEvent B) := by
  have he : familyEvent B = ⋂ k, (B k).event := by
    ext X
    simp [familyEvent]
  rw [he]
  exact MeasurableSet.iInter (fun k => (B k).measurableSet_event)

theorem familyEvent_dependsOn {κ : Type*} [Fintype κ] (B : κ → AffineBlock) :
    DependsOn (fun X : Cantor => X ∈ familyEvent B) (familySupport B : Set ℕ) := by
  intro X Y h
  apply propext
  change (∀ k, X ∈ (B k).event) ↔ (∀ k, Y ∈ (B k).event)
  have he (k : κ) : (X ∈ (B k).event) = (Y ∈ (B k).event) := by
    apply (B k).dependsOn_event
    intro n hn
    apply h n
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hn⟩
  simp_rw [he]

/-- The actual finite-stage law, obtained by conditioning fair coin on the earlier blocks. -/
noncomputable def finiteStageLaw {κ : Type*} (B : κ → AffineBlock) : Measure Cantor :=
  cond fairCoin (familyEvent B)

/-- The paper's stage identity for an explicit finite family of old constraints and a new
disjoint block. It includes null transcript events without an extra case assumption. -/
theorem finiteStage_identity {κ : Type*} [Finite κ] (old : κ → AffineBlock)
    (B : AffineBlock) (hdis : ∀ k, Disjoint (old k).support B.support)
    (π : ScanRule) (v : List Bool) (hfull : B.UnreadFullRank π v) :
    (finiteStageLaw old) ({X | π.transcript X v.length = v} ∩ B.event) =
      (1 / 2 : ℝ≥0∞) ^ B.rank *
        (finiteStageLaw old) {X | π.transcript X v.length = v} := by
  let _ := Fintype.ofFinite κ
  apply B.finiteStage_identity_of_dependsOn (familyEvent old) (familySupport old)
    (familyEvent_dependsOn old) _ π v hfull
  rw [Finset.disjoint_left]
  intro n hn hb
  obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hn
  exact Finset.disjoint_left.mp (hdis k) hk hb

/-- A nonnull earlier background makes the finite-stage law a probability measure. -/
theorem finiteStageLaw_isProbabilityMeasure {κ : Type*} (old : κ → AffineBlock)
    (h : fairCoin (familyEvent old) ≠ 0) : IsProbabilityMeasure (finiteStageLaw old) :=
  cond_isProbabilityMeasure h

/-- Before any new bit is read, each syndrome of a disjoint new block has its uniform mass. -/
theorem finiteStageLaw_event {κ : Type*} [Finite κ] (old : κ → AffineBlock)
    (B : AffineBlock) (hdis : ∀ k, Disjoint (old k).support B.support)
    (hold : fairCoin (familyEvent old) ≠ 0) :
    (finiteStageLaw old) B.event = (1 / 2 : ℝ≥0∞) ^ B.rank := by
  let _ := finiteStageLaw_isProbabilityMeasure old hold
  simpa using finiteStage_identity old B hdis ScanRule.monotone []
    (B.unreadFullRank_nil ScanRule.monotone)

/-- A full-row-rank block has exactly the expected fair-coin probability. -/
theorem fairCoin_event (B : AffineBlock) :
    fairCoin B.event = (1 / 2 : ℝ≥0∞) ^ B.rank := by
  have h := B.finiteStage_identity_of_dependsOn Set.univ ∅ (by
    intro X Y _
    rfl) (by simp) ScanRule.monotone [] (B.unreadFullRank_nil ScanRule.monotone)
  simpa using h

theorem fairCoin_event_ne_zero (B : AffineBlock) : fairCoin B.event ≠ 0 := by
  rw [fairCoin_event]
  exact pow_ne_zero _ (by norm_num)

end AffineBlock
end Klr
