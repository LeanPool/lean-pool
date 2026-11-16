/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Readers.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Interval.Finset.Nat

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Deleting positions from a word

Both shortening arguments of the small-hole theorem delete a finite set `D` of positions from
each word of a tuple. This module defines the operation and its effect on cuts, letters and
runs.

The edited word `deletePositions w D` keeps the letters of `w` at the positions outside `D`.
The *cut map* `retainedCount D` sends a cut `p` of `w` to the number of retained positions
below `p`, a cut of the edited word. It is monotone, increases by one exactly at retained
positions, and is constant on every interval of deleted positions. A cut `a` of the edited word
therefore has an interval of preimages, whose greatest element `greatestPreimage D a` is a retained
position; `p ≤ greatestPreimage D a ↔ retainedCount D p ≤ a`. A *junction* is the image of a deleted
position, that is, a cut of the edited word where an interval was removed.

If the two end cuts of every maximal interval of deleted positions carry the same state, the
edited word passes through the states of the original word at corresponding cuts
(`runFrom_deletePositions_take`, `runFrom_take_deletePositions`). Between two consecutive
junctions the edited word is a factor of the original word (`take_drop_deletePositions`).

## Main declarations

- `deletePositions`, `retainedCount`: the edited word and the cut map.
- `greatestPreimage`, `le_greatestPreimage_iff`: the greatest preimage of a cut of the edited word.
- `runFrom_deletePositions_take`, `runFrom_take_deletePositions`: deleting loops of a run
  preserves the states at retained cuts.
- `firstRejection_deletePositions`: the first rejected cut of an eligible run follows the cut
  map.
- `getElem?_deletePositions_eq`: the letters of the edited word.
- `not_mem_of_no_junction`, `take_drop_deletePositions`: a stretch of the edited word without
  junctions is a stretch of the original word.
- `deletePositions_union_Ico`, `retainedCount_union_Ico_of_le`,
  `retainedCount_union_Ico_of_ge`: deleting one more interval to the right of `D`.
-/

@[expose] public section


namespace DeciSigma1.Words

open DeciSigma1.Readers

variable {α S : Type} {k : ℕ}

/-! ## The edited word and the cut map -/

/-- Delete the positions in `D` from `w`. -/
def deletePositions (w : List α) (D : Finset ℕ) : List α :=
  (w.zipIdx.filter (fun p => p.2 ∉ D)).map Prod.fst

/-- The number of retained positions below the cut `a`: the cut map of the deletion. -/
def retainedCount (D : Finset ℕ) (a : ℕ) : ℕ := ((Finset.range a).filter (· ∉ D)).card

variable {D : Finset ℕ}

@[simp] theorem retainedCount_zero : retainedCount D 0 = 0 := by simp [retainedCount]

theorem retainedCount_succ (a : ℕ) :
    retainedCount D (a + 1) = retainedCount D a + if a ∈ D then 0 else 1 := by
  unfold retainedCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : a ∈ D
  · simp [h]
  · simp [h, Finset.card_insert_of_notMem]

theorem retainedCount_succ_of_not_mem {a : ℕ} (h : a ∉ D) :
    retainedCount D (a + 1) = retainedCount D a + 1 := by
  rw [retainedCount_succ, ite_eq_right h]

theorem retainedCount_succ_of_mem {a : ℕ} (h : a ∈ D) :
    retainedCount D (a + 1) = retainedCount D a := by
  rw [retainedCount_succ, ite_eq_left h, Nat.add_zero]

theorem retainedCount_mono {a b : ℕ} (h : a ≤ b) : retainedCount D a ≤ retainedCount D b :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

theorem retainedCount_add_of_not_mem {a n : ℕ} (h : ∀ i < n, a + i ∉ D) :
    retainedCount D (a + n) = retainedCount D a + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, retainedCount_succ_of_not_mem (h n (by omega)),
        ih (fun i hi => h i (by omega))]
    ring

theorem retainedCount_add_of_mem {a n : ℕ} (h : ∀ i < n, a + i ∈ D) :
    retainedCount D (a + n) = retainedCount D a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, retainedCount_succ_of_mem (h n (by omega)),
        ih (fun i hi => h i (by omega))]

theorem retainedCount_lt_of_not_mem {a b : ℕ} (h : a ∉ D) (hab : a < b) :
    retainedCount D a < retainedCount D b := by
  have := retainedCount_succ_of_not_mem h
  have := retainedCount_mono (D := D) (show a + 1 ≤ b by omega)
  omega

/-- The cut map increases by at most one at each position. -/
theorem retainedCount_add_le (a n : ℕ) : retainedCount D (a + n) ≤ retainedCount D a + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, retainedCount_succ]
    split_ifs <;> omega

theorem retainedCount_le (a : ℕ) : retainedCount D a ≤ a := by
  simpa using retainedCount_add_le (D := D) 0 a

theorem retainedCount_lt_of_mem {p a : ℕ} (hp : p ∈ D) (hpa : p < a) : retainedCount D a < a := by
  have h1 := retainedCount_succ_of_mem hp
  have h2 := retainedCount_le (D := D) p
  have h3 := retainedCount_add_le (D := D) (p + 1) (a - (p + 1))
  rw [show p + 1 + (a - (p + 1)) = a by omega] at h3
  omega

theorem retainedCount_congr {D' : Finset ℕ} {a : ℕ} (h : ∀ p < a, p ∈ D ↔ p ∈ D') :
    retainedCount D a = retainedCount D' a := by
  unfold retainedCount
  congr 1
  exact Finset.filter_congr fun p hp => not_congr (h p (Finset.mem_range.mp hp))

@[simp] theorem retainedCount_empty (a : ℕ) : retainedCount ∅ a = a := by simp [retainedCount]

/-- Two cuts with the same image, neither of which ends a deleted interval, are equal. -/
theorem eq_of_retainedCount_eq {p q : ℕ} (h : retainedCount D p = retainedCount D q)
    (hp : p = 0 ∨ p - 1 ∉ D) (hq : q = 0 ∨ q - 1 ∉ D) : p = q := by
  rcases lt_trichotomy p q with hlt | heq | hlt
  · have := retainedCount_lt_of_not_mem (hq.resolve_left (by omega)) (show q - 1 < q by omega)
    have := retainedCount_mono (D := D) (show p ≤ q - 1 by omega)
    omega
  · exact heq
  · have := retainedCount_lt_of_not_mem (hp.resolve_left (by omega)) (show p - 1 < p by omega)
    have := retainedCount_mono (D := D) (show q ≤ p - 1 by omega)
    omega

/-- At most `|D|` positions are deleted below any cut. -/
theorem le_retainedCount_add_card (a : ℕ) : a ≤ retainedCount D a + D.card := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range a) (· ∈ D)
  have hD : ((Finset.range a).filter (· ∈ D)).card ≤ D.card :=
    Finset.card_le_card fun p hp => (Finset.mem_filter.mp hp).2
  rw [Finset.card_range] at h
  unfold retainedCount
  omega

theorem deletePositions_append (xs ys : List α) :
    deletePositions (xs ++ ys) D = deletePositions xs D ++
      ((ys.zipIdx xs.length).filter (fun p => p.2 ∉ D)).map Prod.fst := by
  unfold deletePositions
  rw [List.zipIdx_append, List.filter_append, List.map_append, Nat.zero_add]

theorem deletePositions_snoc (w : List α) (c : α) :
    deletePositions (w ++ [c]) D = deletePositions w D ++ if w.length ∈ D then [] else [c] := by
  rw [deletePositions_append]
  congr 1
  simp only [List.zipIdx_singleton]
  split_ifs with h <;> simp [h]

@[simp] theorem deletePositions_nil : deletePositions ([] : List α) D = [] := rfl

theorem deletePositions_take_succ (w : List α) (c : ℕ) :
    deletePositions (w.take (c + 1)) D = deletePositions (w.take c) D ++ if c ∈
        D then [] else (w[c]?).toList := by
  rw [List.take_add_one]
  rcases Nat.lt_or_ge c w.length with hc | hc
  · rw [List.getElem?_eq_getElem hc, Option.toList_some, deletePositions_snoc, List.length_take,
      min_eq_left hc.le]
  · rw [List.getElem?_eq_none hc, Option.toList_none, List.append_nil]
    split_ifs <;> simp

theorem length_deletePositions_take (w : List α) {c : ℕ} (hc : c ≤ w.length) :
    (deletePositions (w.take c) D).length = retainedCount D c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [deletePositions_take_succ, List.length_append, ih (by omega), retainedCount_succ,
      List.getElem?_eq_getElem (by omega)]
    split_ifs <;> simp

theorem length_deletePositions (w : List α) :
    (deletePositions w D).length = retainedCount D w.length := by
  have := length_deletePositions_take (D := D) w (le_refl w.length)
  rwa [List.take_length] at this

theorem deletePositions_take (w : List α) {a : ℕ} (ha : a ≤ w.length) :
    (deletePositions w D).take (retainedCount D a) = deletePositions (w.take a) D := by
  conv_lhs => rw [← List.take_append_drop a w, deletePositions_append]
  rw [List.take_left' (by rw [length_deletePositions, List.length_take, min_eq_left ha])]

/-- A retained letter of `w` is the letter of the edited word at the image of its position. -/
theorem getElem?_deletePositions (w : List α) {a : ℕ} (hD : a ∉ D) (ha : a < w.length) :
    (deletePositions w D)[retainedCount D a]? = w[a]? := by
  have h1 := deletePositions_take w (D := D) (show a + 1 ≤ w.length by omega)
  rw [deletePositions_take_succ, ite_eq_right hD, List.getElem?_eq_getElem ha, Option.toList_some,
    retainedCount_succ_of_not_mem hD] at h1
  have h2 : (deletePositions (w.take a) D).length = retainedCount D a := by
    rw [length_deletePositions, List.length_take, min_eq_left ha.le]
  have := congrArg (fun u : List α => u[retainedCount D a]?) h1
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_append_right (by omega), h2,
    Nat.sub_self] at this
  rw [this, List.getElem?_eq_getElem ha]
  rfl

theorem deletePositions_take_of_mem (w : List α) {j c : ℕ} (hjc : j ≤ c)
    (h : ∀ p, j ≤ p → p < c → p ∈ D) : deletePositions (w.take c) D =
        deletePositions (w.take j) D := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjc
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, deletePositions_take_succ, ite_eq_left (h _ (by omega) (by omega)),
        List.append_nil,
      ih (by omega) (fun p hp hpc => h p hp (by omega))]

/-! ## The greatest preimage of a cut -/

/-- The greatest cut of the original word whose image is the cut `a` of the edited word. -/
def greatestPreimage (D : Finset ℕ) (a : ℕ) : ℕ :=
  Nat.findGreatest (fun p => retainedCount D p ≤ a) (a + D.card)

/-- `greatestPreimage D` is the upper adjoint of the cut map. -/
theorem le_greatestPreimage_iff {p a : ℕ} : p ≤ greatestPreimage D a ↔ retainedCount D p ≤ a := by
  constructor
  · intro h
    have h0 : retainedCount D (greatestPreimage D a) ≤ a :=
      Nat.findGreatest_spec (P := fun p => retainedCount D p ≤ a) (Nat.zero_le _) (by simp)
    exact (retainedCount_mono h).trans h0
  · intro h
    have := le_retainedCount_add_card (D := D) p
    exact Nat.le_findGreatest (by omega) h

@[simp] theorem retainedCount_greatestPreimage (a : ℕ) :
    retainedCount D (greatestPreimage D a) = a := by
  have h1 := le_greatestPreimage_iff.mp (le_refl (greatestPreimage D a))
  have h2 :=
      mt (le_greatestPreimage_iff (D := D) (p := greatestPreimage D a + 1) (a := a)).mpr (by omega)
  have := retainedCount_add_le (D := D) (greatestPreimage D a) 1
  omega

/-- The greatest preimage of a cut is a retained position. -/
theorem greatestPreimage_not_mem (a : ℕ) : greatestPreimage D a ∉ D := by
  intro h
  have := le_greatestPreimage_iff.mpr (retainedCount_succ_of_mem h).le
  rw [retainedCount_greatestPreimage] at this
  omega

theorem greatestPreimage_retainedCount {p : ℕ} (h : p ∉ D) :
    greatestPreimage D (retainedCount D p) = p := by
  refine le_antisymm (Nat.le_of_not_lt fun hlt => ?_) (le_greatestPreimage_iff.mpr le_rfl)
  have := retainedCount_lt_of_not_mem h hlt
  rw [retainedCount_greatestPreimage] at this
  omega

theorem greatestPreimage_mono {a b : ℕ} (h : a ≤ b) : greatestPreimage D a ≤ greatestPreimage D b :=
  le_greatestPreimage_iff.mpr (by rw [retainedCount_greatestPreimage]; exact h)

@[simp] theorem greatestPreimage_empty (a : ℕ) : greatestPreimage ∅ a = a := by
  simpa using greatestPreimage_retainedCount (D := ∅) (p := a) (by simp)

/-- The letter of the edited word at a cut is the letter of the original word at the greatest
preimage of the cut. -/
theorem getElem?_deletePositions_eq (w : List α) (a : ℕ) :
    (deletePositions w D)[a]? = w[greatestPreimage D a]? := by
  rcases Nat.lt_or_ge (greatestPreimage D a) w.length with h | h
  · rw [← getElem?_deletePositions w (greatestPreimage_not_mem a) h, retainedCount_greatestPreimage]
  · rw [List.getElem?_eq_none h, List.getElem?_eq_none]
    rw [length_deletePositions]
    exact le_greatestPreimage_iff.mp h

@[simp] theorem deletePositions_empty (w : List α) : deletePositions w ∅ = w := by
  apply List.ext_getElem?
  intro a
  rw [getElem?_deletePositions_eq, greatestPreimage_empty]

theorem greatestPreimage_lt_length (w : List α) {a : ℕ} (ha : a < (deletePositions w D).length) :
    greatestPreimage D a < w.length := by
  by_contra h
  have := le_greatestPreimage_iff.mp (Nat.le_of_not_lt h)
  rw [length_deletePositions] at ha
  omega

/-- If the end of `w` is not deleted, it is the greatest preimage of the end of the edited
word. -/
theorem greatestPreimage_length (w : List α) (hD : w.length ∉ D) :
    greatestPreimage D (deletePositions w D).length = w.length := by
  rw [length_deletePositions, greatestPreimage_retainedCount hD]

theorem greatestPreimage_le_length (w : List α) (hD : w.length ∉ D) {a : ℕ}
    (ha : a ≤ (deletePositions w D).length) : greatestPreimage D a ≤ w.length :=
  (greatestPreimage_mono ha).trans (greatestPreimage_length w hD).le

/-! ## Runs -/

/-- Deleting maximal intervals whose two end cuts carry the same state preserves the state at
every cut that is not interior to a deleted interval. -/
theorem runFrom_deletePositions_take (T : Table α S k) (q : S) (w : List α)
    (hblock : ∀ j c, j < c → c ≤ w.length → (∀ p, j ≤ p → p < c → p ∈ D) →
      (j = 0 ∨ j - 1 ∉ D) → c ∉ D → runFrom T.step q (w.take j) = runFrom T.step q (w.take c))
    (c : ℕ) (hc : c ≤ w.length) (hint : c = 0 ∨ c ∉ D ∨ c - 1 ∉ D) :
    runFrom T.step q (deletePositions (w.take c) D) = runFrom T.step q (w.take c) := by
  classical
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases c with _ | c₀
    · simp
    by_cases hc₀ : c₀ ∈ D
    · have hcD : c₀ + 1 ∉ D := by
        rcases hint with h | h | h
        · omega
        · exact h
        · exact absurd hc₀ (by simpa using h)
      have hex : ∃ j, j ≤ c₀ ∧ ∀ p, j ≤ p → p < c₀ + 1 → p ∈ D :=
        ⟨c₀, le_rfl, fun p hp hpc => by rwa [show p = c₀ by omega]⟩
      obtain ⟨hjc, hjD⟩ := Nat.find_spec hex
      set j := Nat.find hex
      have hjmin : j = 0 ∨ j - 1 ∉ D := by
        by_contra hcon
        push Not at hcon
        have := Nat.find_min' hex (m := j - 1) ⟨by omega, fun p hp hpc => by
          rcases Nat.eq_or_lt_of_le hp with h | h
          · rw [← h]; exact hcon.2
          · exact hjD p (by omega) hpc⟩
        omega
      rw [deletePositions_take_of_mem w (show j ≤ c₀ + 1 by omega) hjD,
        ih j (by omega) (by omega) (by rcases hjmin with h | h; · left; exact h
                                       · right; right; exact h),
        hblock j (c₀ + 1) (by omega) hc hjD hjmin hcD]
    · rw [deletePositions_take_succ, ite_eq_right hc₀, List.take_add_one, runFrom_append,
        runFrom_append, ih c₀ (by omega) (by omega) (Or.inr (Or.inl hc₀))]

/-- Under the hypothesis of `runFrom_deletePositions_take`, the state of the edited word at a
cut is the state of the original word at the greatest preimage of the cut. -/
theorem runFrom_take_deletePositions (T : Table α S k) (q : S) (w : List α)
    (hblock : ∀ j c, j < c → c ≤ w.length → (∀ p, j ≤ p → p < c → p ∈ D) →
      (j = 0 ∨ j - 1 ∉ D) → c ∉ D → runFrom T.step q (w.take j) = runFrom T.step q (w.take c))
    (hD : w.length ∉ D) (a : ℕ) :
    runFrom T.step q ((deletePositions w D).take a) =
        runFrom T.step q (w.take (greatestPreimage D a)) := by
  have key : ∀ a ≤ (deletePositions w D).length,
      runFrom T.step q ((deletePositions w D).take a) =
        runFrom T.step q (w.take (greatestPreimage D a)) := by
    intro a ha
    have hle := greatestPreimage_le_length w hD ha
    rw [← runFrom_deletePositions_take T q w hblock _ hle (Or.inr (Or.inl
        (greatestPreimage_not_mem a))),
      ← deletePositions_take w hle, retainedCount_greatestPreimage]
  rcases Nat.le_total a (deletePositions w D).length with ha | ha
  · exact key a ha
  · have hw : w.length ≤ greatestPreimage D a :=
      (greatestPreimage_length w hD).ge.trans (greatestPreimage_mono ha)
    have h := key _ le_rfl
    rw [greatestPreimage_length w hD, List.take_length, List.take_length] at h
    rw [List.take_of_length_le ha, List.take_of_length_le hw, h]

/-- Deleting loops of the run of an eligible coordinate moves its first rejected cut to the
image of that cut: rejection is monotone along an eligible run, so no assumption on the deleted
positions other than the states of the edited run is needed. -/
theorem firstRejection_deletePositions (M : StructuralReader α S k) {W U : Fin k → List α}
    {i : Fin k} (hW : M.Eligible W i) (hU : U i = deletePositions (W i) D)
    (hD : (W i).length ∉ D)
    (hrun : ∀ a, M.runPrefix U i a = M.runPrefix W i (greatestPreimage D a)) :
    M.firstRejection U i = retainedCount D (M.firstRejection W i) := by
  have hend : greatestPreimage D (U i).length =
      (W i).length := by rw [hU]; exact greatestPreimage_length _ hD
  have hlen : (U i).length = retainedCount D (W i).length := by rw [hU, length_deletePositions]
  have hUe : M.Eligible U i := by
    refine ⟨fun a _ => by rw [hrun]; exact hW.runPrefix_ne _, ?_⟩
    have h2 := hW.2
    unfold Table.endState at h2 ⊢
    rwa [hrun, hend]
  have hJ := StructuralReader.firstRejection_spec hW
  have hJ' := StructuralReader.firstRejection_spec hUe
  have hle : retainedCount D (M.firstRejection W i) ≤ (U i).length :=
    hlen ▸ retainedCount_mono hJ.1
  apply le_antisymm
  · refine (StructuralReader.rejected_iff_firstRejection_le hUe hle).mp ?_
    rw [hrun]
    exact StructuralReader.rejected_of_firstRejection_le hW (le_greatestPreimage_iff.mpr le_rfl)
      (hend ▸ greatestPreimage_mono hle)
  · have hr : M.rejected (M.runPrefix W i (greatestPreimage D (M.firstRejection U i))) = true := by
      rw [← hrun]; exact hJ'.2.1
    exact le_greatestPreimage_iff.mp ((StructuralReader.rejected_iff_firstRejection_le hW
      (hend ▸ greatestPreimage_mono hJ'.1)).mp hr)

/-! ## Stretches without junctions -/

/-- If no junction lies strictly between the cuts `a` and `a + n` of the edited word, the `n`
positions from the greatest preimage of `a` are retained. -/
theorem not_mem_of_no_junction {a n : ℕ}
    (hJ : ∀ p ∈ D, ¬ (a < retainedCount D p ∧ retainedCount D p < a + n)) :
    ∀ i < n, greatestPreimage D a + i ∉ D := by
  intro i hi hm
  have h0 : i ≠ 0 := fun h => greatestPreimage_not_mem a (by simpa [h] using hm)
  have h1 := retainedCount_add_le (D := D) (greatestPreimage D a) i
  have h2 := retainedCount_lt_of_not_mem (greatestPreimage_not_mem (D := D) a)
    (show greatestPreimage D a < greatestPreimage D a + i by omega)
  rw [retainedCount_greatestPreimage] at h1 h2
  exact hJ _ hm ⟨h2, by omega⟩

/-- Along a stretch of retained positions that starts at the greatest preimage of `a`, the cut
map is a shift. -/
theorem retainedCount_greatestPreimage_add {a n : ℕ} (h : ∀ i < n, greatestPreimage D a + i ∉ D) :
    retainedCount D (greatestPreimage D a + n) = a + n := by
  rw [retainedCount_add_of_not_mem h, retainedCount_greatestPreimage]

/-- If no junction lies strictly between the cuts `a` and `a + n` of the edited word, the `n`
letters of the edited word read from `a` are the `n` letters of the original word read from the
greatest preimage of `a`. -/
theorem take_drop_deletePositions (w : List α) {a n : ℕ}
    (hJ : ∀ p ∈ D, ¬ (a < retainedCount D p ∧ retainedCount D p < a + n)) :
    ((deletePositions w D).drop a).take n = (w.drop (greatestPreimage D a)).take n := by
  have hret := not_mem_of_no_junction hJ
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_take]
  split_ifs with hi
  · rw [List.getElem?_drop, List.getElem?_drop, getElem?_deletePositions_eq,
      ← retainedCount_greatestPreimage_add (fun j hj => hret j (by omega)),
      greatestPreimage_retainedCount (hret i hi)]
  · rfl

/-! ## Deleting one more interval

If all positions of `D` lie below `c`, deleting `D ∪ [c, c + δ)` amounts to removing the factor
`[c, c + δ)` first and deleting `D` from the result. This gives proofs by induction on the
deleted intervals, from right to left. -/

section Interval

variable {c δ : ℕ}

theorem retainedCount_union_Ico_of_le {p : ℕ} (hp : p ≤ c) :
    retainedCount (D ∪ Finset.Ico c (c + δ)) p = retainedCount D p :=
  retainedCount_congr fun i hi => by
    rw [Finset.mem_union, Finset.mem_Ico]
    exact ⟨fun h => h.elim id fun h => by omega, Or.inl⟩

theorem retainedCount_union_Ico_of_ge (hD : ∀ p ∈ D, p < c) {p : ℕ} (hp : c + δ ≤ p) :
    retainedCount (D ∪ Finset.Ico c (c + δ)) p = retainedCount D (p - δ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hp
  have hin : ∀ i < δ, c + i ∈ D ∪ Finset.Ico c (c + δ) := fun i hi =>
    Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  have hout : ∀ i < n, c + δ + i ∉ D ∪ Finset.Ico c (c + δ) := fun i _ h => by
    rcases Finset.mem_union.mp h with h | h
    · have := hD _ h; omega
    · have := (Finset.mem_Ico.mp h).2; omega
  have hout' : ∀ i < n, c + i ∉ D := fun i _ h => by have := hD _ h; omega
  rw [retainedCount_add_of_not_mem hout, retainedCount_add_of_mem hin,
    retainedCount_union_Ico_of_le le_rfl, show c + δ + n - δ = c + n by omega,
    retainedCount_add_of_not_mem hout']

theorem greatestPreimage_union_Ico (hD : ∀ p ∈ D, p < c) (a : ℕ) :
    greatestPreimage (D ∪ Finset.Ico c (c + δ)) a =
      if greatestPreimage D a < c then greatestPreimage D a else greatestPreimage D a + δ := by
  have key : ∀ q, q ∉ D ∪ Finset.Ico c (c + δ) →
      retainedCount (D ∪ Finset.Ico c (c + δ)) q = a →
      greatestPreimage (D ∪ Finset.Ico c (c + δ)) a = q :=
          fun q hq h => h ▸ greatestPreimage_retainedCount hq
  split_ifs with h
  · refine key _ (fun hm => ?_) ?_
    · rcases Finset.mem_union.mp hm with h' | h'
      · exact greatestPreimage_not_mem a h'
      · have := (Finset.mem_Ico.mp h').1; omega
    · rw [retainedCount_union_Ico_of_le h.le, retainedCount_greatestPreimage]
  · refine key _ (fun hm => ?_) ?_
    · rcases Finset.mem_union.mp hm with h' | h'
      · have := hD _ h'; omega
      · have := (Finset.mem_Ico.mp h').2; omega
    · rw [retainedCount_union_Ico_of_ge hD (by omega), Nat.add_sub_cancel,
        retainedCount_greatestPreimage]

theorem deletePositions_union_Ico (w : List α) (hD : ∀ p ∈ D, p < c) (hc : c ≤ w.length) :
    deletePositions w (D ∪ Finset.Ico c (c + δ)) =
      deletePositions (w.take c ++ w.drop (c + δ)) D := by
  apply List.ext_getElem?
  intro a
  rw [getElem?_deletePositions_eq, getElem?_deletePositions_eq, greatestPreimage_union_Ico hD]
  have hl : (w.take c).length = c := by rw [List.length_take, min_eq_left hc]
  split_ifs with h
  · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop, hl]
    congr 1
    omega

end Interval

end DeciSigma1.Words
