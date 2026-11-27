/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.Betting
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.FunProp

/-!
# Fair-coin law of adaptive transcripts

For a fixed finite transcript, all of its query positions are already determined.
Freshness makes those positions distinct. The input event producing that transcript
is therefore a finite assignment of independent fair bits, even though the scan
rule chooses positions adaptively on other transcripts.
-/

@[expose] public section

namespace Klr.ScanRule

open MeasureTheory
open scoped ENNReal

/-- Distinct prefixes of a fixed transcript query different input positions. -/
theorem query_take_ne (π : ScanRule) (v : List Bool) {m n : ℕ}
    (hmn : m < n) (hn : n ≤ v.length) :
    π.query (v.take m) ≠ π.query (v.take n) := by
  have hlen : (v.take n).length = n := by simp [List.length_take, hn]
  have h := π.fresh (v.take n) m (by rw [hlen]; exact hmn)
  simpa [List.take_take, Nat.min_eq_left hmn.le] using h

/-- The fixed coordinates specified by a finite transcript form an injection. -/
theorem query_take_injective (π : ScanRule) (v : List Bool) :
    Function.Injective (fun i : Fin v.length => π.query (v.take i.val)) := by
  intro i j h
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · exact False.elim (π.query_take_ne v hij j.isLt.le h)
  · exact hij
  · exact False.elim (π.query_take_ne v hij i.isLt.le h.symm)

/-- The bit at transcript index `i` is the answer to the query chosen after `i` steps. -/
theorem getD_transcript (π : ScanRule) (X : Cantor) {n i : ℕ} (hi : i < n) :
    (π.transcript X n).getD i false = X (π.query (π.transcript X i)) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
    · rw [transcript_succ, List.getD_append _ _ _ _ (by simpa using hlt)]
      exact ih hlt
    · rw [transcript_succ, List.getD_append_right _ _ _ _ (by simp)]
      simp

/-- Agreement with the finite assignment encoded by a transcript reconstructs every prefix. -/
theorem transcript_eq_take_of_agrees (π : ScanRule) (X : Cantor) (v : List Bool)
    (hX : ∀ i < v.length, X (π.query (v.take i)) = v.getD i false)
    {n : ℕ} (hn : n ≤ v.length) : π.transcript X n = v.take n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : n < v.length := lt_of_lt_of_le (Nat.lt_succ_self n) hn
    rw [transcript_succ, ih (Nat.le_of_succ_le hn), hX n hlt,
      List.getD_eq_getElem _ _ hlt]
    exact List.take_concat_get' v n hlt

/-- Adaptive transcript preimages are exactly finite assignments to the queried coordinates. -/
theorem transcript_eq_iff (π : ScanRule) (X : Cantor) (v : List Bool) :
    π.transcript X v.length = v ↔
      ∀ i < v.length, X (π.query (v.take i)) = v.getD i false := by
  constructor
  · intro h i hi
    have ht : π.transcript X i = v.take i := by
      rw [← h, π.transcript_take X hi.le]
    rw [← ht, ← π.getD_transcript X hi, h]
  · intro h
    simpa using π.transcript_eq_take_of_agrees X v h le_rfl

/-- The transcript event is the preimage of one fixed finite assignment. -/
theorem transcript_event_eq_preimage (π : ScanRule) (v : List Bool) :
    {X : Cantor | π.transcript X v.length = v} =
      (fun X : Cantor => fun i : Fin v.length => X (π.query (v.take i.val))) ⁻¹'
        {fun i : Fin v.length => v.getD i.val false} := by
  ext X
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
  rw [transcript_eq_iff]
  exact ⟨fun h i => h i.val i.isLt, fun h i hi => h ⟨i, hi⟩⟩

/-- The event of observing a prescribed finite transcript is measurable. -/
theorem measurableSet_transcript (π : ScanRule) (v : List Bool) :
    MeasurableSet {X | π.transcript X v.length = v} := by
  rw [transcript_event_eq_preimage]
  exact (by fun_prop : Measurable (fun X : Cantor => fun i : Fin v.length =>
    X (π.query (v.take i.val)))) (measurableSet_singleton _)

/-- A finite transcript has exactly the same probability as a fair bit string. -/
theorem fairCoin_transcript (π : ScanRule) (v : List Bool) :
    fairCoin {X | π.transcript X v.length = v} = (1 / 2 : ℝ≥0∞) ^ v.length := by
  rw [transcript_event_eq_preimage]
  let f : Cantor → (Fin v.length → Bool) := fun X i => X (π.query (v.take i.val))
  let bits : Fin v.length → Bool := fun i => v.getD i.val false
  change fairCoin (f ⁻¹' {bits}) = _
  have hf : Measurable f := by fun_prop
  rw [← Measure.map_apply hf (measurableSet_singleton bits)]
  change (Measure.infinitePi (fun _ : ℕ => fairBit)).map f {bits} = _
  rw [Measure.map_infinitePi_infinitePi_of_inj (π.query_take_injective v)]
  rw [Measure.infinitePi_eq_pi, Measure.pi_singleton]
  simp

end Klr.ScanRule
