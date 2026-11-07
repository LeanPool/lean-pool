/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.Activation

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-! Executable activation testing (`lem:activation-test`). Each round processes
all currently enabled operations. This uses finite-set operations, not a chosen
ordering or a classical selection function. The proof stays independent of grammar syntax.
-/
namespace Parikh

namespace ActivationOrder
variable {N C : Type*} {required : C → N} {added : C → Set N}

/-- More available labels preserve every enabled operation order. -/
theorem mono {U V : Set N} {cs : List C} (h : ActivationOrder required added U cs)
    (hUV : U ⊆ V) : ActivationOrder required added V cs := by
  induction cs generalizing U V with
  | nil => trivial
  | cons c cs ih =>
    refine ⟨hUV h.1, ih h.2 ?_⟩
    exact Set.union_subset_union_left _ hUV
end ActivationOrder

namespace Activatable
variable {N C : Type*} [DecidableEq C]

/-- Any currently enabled operation may be processed first, without changing
whether all operations can be activated (`lem:activation-test`). -/
theorem erase_iff_of_enabled (required : C → N) (added : C → Set N) (U : Set N)
    (D : Finset C) (c : C) (hc : c ∈ D) (henabled : required c ∈ U) :
    Activatable required added U D ↔ Activatable required added (U ∪ added c) (D.erase c) := by
  constructor
  · rintro ⟨order, hnodup, hmem, horder⟩
    -- Pay for `c` first, then omit it from the old order: its support is already available.
    have hmore := horder.mono (V := U ∪ added c) Set.subset_union_left
    have hfiltered := hmore.filter_of_covered (fun d => decide (d ≠ c)) (by
      intro d _ hp
      have : d = c := by simpa using hp
      subst d
      exact Set.subset_union_right)
    refine ⟨order.filter (fun d => decide (d ≠ c)), hnodup.filter _, ?_, hfiltered⟩
    intro d
    simp only [List.mem_filter, decide_eq_true_eq, hmem, Finset.mem_erase]
    tauto
  · rintro ⟨order, hnodup, hmem, horder⟩
    -- Conversely, prepend the enabled operation to an order for the remaining set.
    refine ⟨c :: order, List.nodup_cons.mpr ⟨?_, hnodup⟩, ?_, henabled, horder⟩
    · simpa using (hmem c).mp
    · intro d
      simp only [List.mem_cons, hmem, Finset.mem_erase]
      by_cases hd : d = c
      · subst d; simp [hc]
      · tauto

/-- A whole subset enabled at the start can be processed together. Each member
still occurs exactly once; its added labels are accumulated by finite union. -/
theorem batch_iff_of_enabled [DecidableEq N] (required : C → N) (added : C → Finset N)
    (U : Finset N) (D E : Finset C) (hED : E ⊆ D)
    (henabled : ∀ c ∈ E, required c ∈ U) :
    Activatable required (fun c => (added c : Set N)) (U : Set N) D ↔
      Activatable required (fun c => (added c : Set N))
        ((U ∪ E.biUnion added : Finset N) : Set N) (D \ E) := by
  induction E using Finset.induction_on generalizing U D with
  | empty => simp
  | @insert c E hc ih =>
    have hcD : c ∈ D := hED (Finset.mem_insert_self _ _)
    have hroot : required c ∈ U := henabled c (Finset.mem_insert_self _ _)
    have hED' : E ⊆ D.erase c := by
      intro d hd
      exact Finset.mem_erase.mpr ⟨by intro h; subst d; exact hc hd,
        hED (Finset.mem_insert_of_mem hd)⟩
    have hroot' : ∀ d ∈ E, required d ∈ U ∪ added c := by
      intro d hd
      exact Finset.mem_union_left _ (henabled d (Finset.mem_insert_of_mem hd))
    have hrem : D.erase c \ E = D \ insert c E := by
      ext d
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto
    -- Process one enabled member, then apply the induction hypothesis to the rest of the batch.
    calc
      _ ↔ Activatable required (fun d => (added d : Set N))
          ((U ∪ added c : Finset N) : Set N) (D.erase c) := by
        simpa only [Finset.coe_union] using
          erase_iff_of_enabled required (fun d => (added d : Set N)) U D c hcD hroot
      _ ↔ Activatable required (fun d => (added d : Set N))
          (((U ∪ added c) ∪ E.biUnion added : Finset N) : Set N) (D.erase c \ E) :=
        ih _ _ hED' hroot'
      _ ↔ _ := by rw [Finset.biUnion_insert, ← Finset.union_assoc, hrem]
end Activatable

variable {N C : Type*} [DecidableEq N] [DecidableEq C]

/-- Run at most `fuel` rounds. Reject if unprocessed operations remain with none
enabled. No operation is processed more than once; neither type must be finite. -/
@[expose] def activationRounds (required : C → N) (added : C → Finset N) (fuel : ℕ) :
    Finset N → Finset C → Bool :=
  Nat.rec (motive := fun _ => Finset N → Finset C → Bool)
    (fun _ D => decide (D = ∅))
    (fun _ next U D =>
      if D = ∅ then true else
        let enabled := D.filter (fun c => required c ∈ U)
        if enabled = ∅ then false else
          next (U ∪ enabled.biUnion added) (D \ enabled)) fuel

/-- Sufficient fuel gives an exact decision of the accepted activation predicate,
without assuming an operation adds its own required label (`lem:activation-test`). -/
theorem activationRounds_correct (required : C → N) (added : C → Finset N)
    (fuel : ℕ) (U : Finset N) (D : Finset C) (hfuel : D.card ≤ fuel) :
    activationRounds required added fuel U D = true ↔
      Activatable required (fun c => (added c : Set N)) (U : Set N) D := by
  have hempty (V : Finset N) :
      Activatable required (fun c => (added c : Set N)) (V : Set N) ∅ :=
    ⟨[], by simp, by simp, trivial⟩
  induction fuel generalizing U D with
  | zero =>
    have hD : D = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hfuel)
    subst D
    exact ⟨fun _ => hempty U, fun _ => rfl⟩
  | succ fuel ih =>
    by_cases hD : D = ∅
    · subst D
      simp only [activationRounds, ↓reduceIte, true_iff]
      exact hempty U
    · let enabled := D.filter (fun c => required c ∈ U)
      have hsub : enabled ⊆ D := Finset.filter_subset _ _
      have hroot : ∀ c ∈ enabled, required c ∈ U :=
        fun _ hc => (Finset.mem_filter.mp hc).2
      by_cases hE : enabled = ∅
      · have hnot : ¬ Activatable required (fun c => (added c : Set N)) (U : Set N) D := by
          -- A nonempty successful order would have an enabled first operation.
          rintro ⟨order, _, hmem, horder⟩
          cases order with
          | nil =>
            apply hD
            ext c
            simpa using (hmem c).symm
          | cons c cs =>
            have hc : c ∈ enabled := Finset.mem_filter.mpr
              ⟨(hmem c).mp (by simp), horder.1⟩
            simp [hE] at hc
        simp only [activationRounds, hD, ↓reduceIte]
        change (if enabled = ∅ then false else _) = true ↔ _
        simp [hE, hnot]
      · have hprogress : 0 < enabled.card := Finset.card_pos.mpr
          (Finset.nonempty_iff_ne_empty.mpr hE)
        have hcard := Finset.card_sdiff_of_subset hsub
        -- A nonempty batch removes at least one operation, preserving the fuel invariant.
        have hremaining : (D \ enabled).card ≤ fuel := by omega
        simp only [activationRounds, hD, ↓reduceIte]
        change (if enabled = ∅ then false else _) = true ↔ _
        simp only [hE, ↓reduceIte]
        exact (ih (U ∪ enabled.biUnion added) (D \ enabled) hremaining).trans
          (Activatable.batch_iff_of_enabled required added U D enabled hsub hroot).symm

/-- An executable value of the accepted interface. Its correctness
field is proved above; its runtime uses only equality, finite sets and recursion. -/
@[expose] def activationTest (N C : Type*) [DecidableEq N] [DecidableEq C] :
    ActivationTest N C where
  run required added U D := activationRounds required added D.card U D
  correct required added U D := activationRounds_correct required added D.card U D le_rfl

end Parikh
