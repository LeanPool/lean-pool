/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler B. Hughes
-/

module

public import Mathlib.Data.Fin.VecNotation
public import LeanPool.PatternPosetNotSperner.Defs

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto

/-!
# The Seven-Entry Counterexample `[213, 2574613]` to McNamara–Steingrímsson Question 9.5

Disproves McNamara–Steingrímsson (2015) Question 9.5 ("Are all intervals in the
classical permutation pattern poset Sperner?") via the explicit 7-entry interval
`[σ₇, τ₇] = [213, 2574613]`:
- `sigma7_le_tau7 : σ₇ ≤ τ₇`
- `interval7_card : (Interval σ₇ τ₇).card = 19` (genuinely proved equal to the 19-member set
  from the true definition `Interval σ₇ τ₇`, checking all `2^7 = 128` subsequences in-kernel)
- `interval7_rank_sizes`: exact rank sizes `1, 3, 7, 7, 1` for ranks `3, 4, 5, 6, 7`
  and `0` elsewhere, giving `interval7_largestRank : largestRank (Interval σ₇ τ₇) = 7`
- `interval7_width : width (Interval σ₇ τ₇) = 8` via the explicit 8-element antichain
  `{13524, 14352, 24351, 35241, 43512, 246513, 256413, 264513}` and an explicit 8-chain cover
- `not_sperner_interval7 : ¬ IsSperner (Interval σ₇ τ₇)`
- `mcnamara_steingrimsson_Q9_5_false` :
  `∃ σ τ : Perm, σ ≤ τ ∧ ¬ IsSperner (Interval σ τ)`
-/

@[expose] public section

namespace PatternPoset

/-! ### Bitmask Standardization Bridge (100% In-Kernel, Zero `native_decide`) -/

/-- Computable inverse on `Fin n` by linear search. -/
def invFin {n : ℕ} (f : Fin n → Fin n) (y : Fin n) : Fin n :=
  match (List.finRange n).find? (fun x => decide (f x = y)) with
  | some x => x
  | none => y

/-- Construct a `Perm` from a concrete function `Fin n → Fin n` verified bijective in-kernel. -/
def mkPerm {n : ℕ} (f : Fin n → Fin n)
    (hl : ∀ x : Fin n, invFin f (f x) = x := by decide)
    (hr : ∀ y : Fin n, f (invFin f y) = y := by decide) : Perm :=
  ⟨n, ⟨f, invFin f, hl, hr⟩⟩

/-- Values of `τ` selected by a boolean mask `b : Fin τ.len → Bool`. -/
def maskVals (τ : Perm) (b : Fin τ.len → Bool) : List ℕ :=
  ((List.finRange τ.len).filter b).map (fun i => (τ.perm i).val)

/-- Decode a `Fin (2 ^ n)` bitmask into a boolean predicate on `Fin n`. -/
def bitMask (n : ℕ) (m : Fin (2 ^ n)) (i : Fin n) : Bool :=
  m.val.testBit i.val

/-- Encode a boolean predicate `b : Fin n → Bool` as a `Fin (2 ^ n)` bitmask. -/
def encodeMask : ∀ {n : ℕ}, (Fin n → Bool) → Fin (2 ^ n)
  | 0, _ => ⟨0, by simp⟩
  | n + 1, b =>
    let r := encodeMask (fun i : Fin n => b i.succ)
    ⟨2 * r.val + if b 0 then 1 else 0, by
      have hr := r.isLt
      rw [pow_succ']
      split_ifs <;> omega⟩

theorem bitMask_encodeMask : ∀ {n : ℕ} (b : Fin n → Bool) (i : Fin n),
    bitMask n (encodeMask b) i = b i
  | 0, _, i => Fin.elim0 i
  | n + 1, b, i => by
    refine Fin.cases ?_ ?_ i
    · simp only [bitMask, encodeMask, Fin.val_zero]
      cases hb : b 0 <;> simp [Nat.testBit_zero]
    · intro j
      simp only [bitMask, encodeMask, Fin.val_succ]
      rw [Nat.testBit_succ]
      have hdiv : (2 * (encodeMask fun k : Fin n => b k.succ).val +
          if b 0 = true then 1 else 0) / 2 =
          (encodeMask fun k : Fin n => b k.succ).val := by
        split_ifs <;> omega
      rw [hdiv]
      exact bitMask_encodeMask (fun k : Fin n => b k.succ) j

private theorem list_eq_of_pairwise_lt {α : Type*} [LinearOrder α] :
    ∀ {l₁ l₂ : List α}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
      (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp (by simp)) (by simp)
  | a :: t₁, b :: t₂, hp₁, hp₂, h => by
    rw [List.pairwise_cons] at hp₁ hp₂
    have hab : a = b := by
      rcases lt_trichotomy a b with hlt | heq | hgt
      · exfalso
        rcases List.mem_cons.mp ((h a).mp (by simp)) with rfl | hmem
        · exact lt_irrefl _ hlt
        · exact lt_asymm hlt (hp₂.1 a hmem)
      · exact heq
      · exfalso
        rcases List.mem_cons.mp ((h b).mpr (by simp)) with rfl | hmem
        · exact lt_irrefl _ hgt
        · exact lt_asymm hgt (hp₁.1 b hmem)
    subst hab
    congr 1
    apply list_eq_of_pairwise_lt hp₁.2 hp₂.2
    intro x
    constructor
    · intro hx
      rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with rfl | hmem
      · exact absurd (hp₁.1 _ hx) (lt_irrefl _)
      · exact hmem
    · intro hx
      rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with rfl | hmem
      · exact absurd (hp₂.1 _ hx) (lt_irrefl _)
      · exact hmem

private theorem pairwise_lt_finRange (n : ℕ) : (List.finRange n).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simpa using hij

/-- The standardized list of `subseqPerm τ S` for a boolean mask `b` equals
`standardizeList (maskVals τ b)`. -/
theorem toList_subseqPerm_eq_standardizeList (τ : Perm) (b : Fin τ.len → Bool) :
    (subseqPerm τ (Finset.univ.filter (fun i : Fin τ.len => b i = true))).toList =
    standardizeList (maskVals τ b) := by
  set S : Finset (Fin τ.len) := Finset.univ.filter (fun i => b i = true)
  let ePos : Fin S.card ≃o S := S.orderIsoOfFin rfl
  let f : Fin S.card ↪o Fin τ.len := ePos.toOrderEmbedding.trans (OrderEmbedding.subtype _)
  have hle_f : ∀ i j : Fin S.card,
      (subseqPerm τ S).perm i < (subseqPerm τ S).perm j ↔ τ.perm (f i) < τ.perm (f j) := by
    intro i j
    let V : Finset (Fin τ.len) := S.image τ.perm
    have hV : V.card = S.card := Finset.card_image_of_injective S τ.perm.injective
    let eVal : Fin S.card ≃o V := V.orderIsoOfFin hV
    change (eVal.symm ⟨τ.perm (ePos i).1, _⟩) < (eVal.symm ⟨τ.perm (ePos j).1, _⟩) ↔
      τ.perm (ePos i).1 < τ.perm (ePos j).1
    exact eVal.symm.lt_iff_lt
  have htoList := toList_eq_standardizeList_of_le (σ := subseqPerm τ S) (τ := τ) f hle_f
  rw [htoList]
  congr 1
  have hpos_list : List.ofFn f = (List.finRange τ.len).filter b := by
    apply list_eq_of_pairwise_lt
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [List.getElem_ofFn]
      exact f.strictMono hij
    · exact (pairwise_lt_finRange τ.len).filter b
    · intro x
      rw [List.mem_ofFn, List.mem_filter]
      constructor
      · rintro ⟨idx, rfl⟩
        have hmem : (ePos idx).1 ∈ S := (ePos idx).2
        rw [Finset.mem_filter] at hmem
        exact ⟨List.mem_finRange _, hmem.2⟩
      · rintro ⟨_, hbx⟩
        have hmem : x ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbx⟩
        refine ⟨ePos.symm ⟨x, hmem⟩, ?_⟩
        change (ePos (ePos.symm ⟨x, hmem⟩)).1 = x
        simp
  unfold maskVals
  rw [← hpos_list, List.map_ofFn]
  rfl

/-- Exact bitmask characterization of pattern containment `σ ≤ τ`. -/
theorem le_iff_exists_bitmask {σ τ : Perm} :
    σ ≤ τ ↔ ∃ m : Fin (2 ^ τ.len),
      σ.toList = standardizeList (maskVals τ (bitMask τ.len m)) := by
  constructor
  · intro hle
    rcases le_iff_contains.mp hle with ⟨f, hf⟩
    let b : Fin τ.len → Bool := fun x => decide (x ∈ Finset.univ.image f)
    refine ⟨encodeMask b, ?_⟩
    have hS : Finset.univ.filter (fun x : Fin τ.len => bitMask τ.len (encodeMask b) x = true) =
        Finset.univ.image f := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, bitMask_encodeMask, b,
        decide_eq_true_eq]
    have hsub : σ = subseqPerm τ (Finset.univ.image f) := eq_subseqPerm_of_le f hf
    rw [hsub, ← hS]
    exact toList_subseqPerm_eq_standardizeList τ (bitMask τ.len (encodeMask b))
  · rintro ⟨m, hm⟩
    set S := Finset.univ.filter (fun i : Fin τ.len => bitMask τ.len m i = true)
    have hlist : σ.toList = (subseqPerm τ S).toList := by
      rw [hm, toList_subseqPerm_eq_standardizeList]
    have heq : σ = subseqPerm τ S := Perm.toList_injective hlist
    rw [heq]
    exact subseqPerm_le τ S

/-- Helper test checking whether a list contains entries `b < a < c` in order. -/
def hasPairAfter (a : ℕ) : List ℕ → Bool
  | [] => false
  | b :: rest => (decide (b < a) && rest.any (fun c => decide (a < c))) || hasPairAfter a rest

/-- Computable test for the `213` pattern on a list of natural numbers. -/
def has213List : List ℕ → Bool
  | [] => false
  | a :: rest => hasPairAfter a rest || has213List rest

private theorem hasPairAfter_true_of_getElem {a : ℕ} :
    ∀ {l : List ℕ} {j k : ℕ} (hj : j < l.length) (hk : k < l.length),
      j < k → l[j] < a → a < l[k] → hasPairAfter a l = true
  | [], _, _, hj, _, _, _, _ => absurd hj (Nat.not_lt_zero _)
  | b :: rest, 0, k + 1, _, hk, _, hba, hak => by
    simp only [List.getElem_cons_zero] at hba
    simp only [List.getElem_cons_succ] at hak
    simp only [hasPairAfter, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.any_eq_true]
    left
    exact ⟨hba, rest[k]'(Nat.lt_of_succ_lt_succ hk), List.getElem_mem _, hak⟩
  | _ :: rest, j + 1, k + 1, hj, hk, hjk, hba, hak => by
    simp only [List.getElem_cons_succ] at hba hak
    simp only [hasPairAfter, Bool.or_eq_true]
    right
    exact hasPairAfter_true_of_getElem (Nat.lt_of_succ_lt_succ hj) (Nat.lt_of_succ_lt_succ hk)
      (Nat.lt_of_succ_lt_succ hjk) hba hak

private theorem has213List_true_of_getElem :
    ∀ {l : List ℕ} {i j k : ℕ} (hi : i < l.length) (hj : j < l.length) (hk : k < l.length),
      i < j → j < k → l[j] < l[i] → l[i] < l[k] → has213List l = true
  | [], _, _, _, hi, _, _, _, _, _, _ => absurd hi (Nat.not_lt_zero _)
  | a :: rest, 0, j + 1, k + 1, _, hj, hk, _, hjk, hji, hik => by
    simp only [List.getElem_cons_zero] at hji hik
    simp only [List.getElem_cons_succ] at hji hik
    simp only [has213List, Bool.or_eq_true]
    left
    exact hasPairAfter_true_of_getElem (Nat.lt_of_succ_lt_succ hj) (Nat.lt_of_succ_lt_succ hk)
      (Nat.lt_of_succ_lt_succ hjk) hji hik
  | _ :: rest, i + 1, j + 1, k + 1, hi, hj, hk, hij, hjk, hji, hik => by
    simp only [List.getElem_cons_succ] at hji hik
    simp only [has213List, Bool.or_eq_true]
    right
    exact has213List_true_of_getElem (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)
      (Nat.lt_of_succ_lt_succ hk) (Nat.lt_of_succ_lt_succ hij) (Nat.lt_of_succ_lt_succ hjk)
      hji hik

/-! ### The 19 Permutations of `[213, 2574613]` -/

/-- `σ₇ = 213` (0-indexed: `[1, 0, 2]`). -/
def σ₇ : Perm := mkPerm (n := 3) ![1, 0, 2]

/-- `τ₇ = 2574613` (0-indexed: `[1, 4, 6, 3, 5, 0, 2]`). -/
def τ₇ : Perm := mkPerm (n := 7) ![1, 4, 6, 3, 5, 0, 2]

/-- Rank-4 member `1324` of `[213, 2574613]`. -/
def p1324 : Perm := mkPerm (n := 4) ![0, 2, 1, 3]
/-- Rank-4 member `2413` of `[213, 2574613]`. -/
def p2413 : Perm := mkPerm (n := 4) ![1, 3, 0, 2]
/-- Rank-4 member `3241` of `[213, 2574613]`. -/
def p3241 : Perm := mkPerm (n := 4) ![2, 1, 3, 0]

/-- Rank-5 member `13524` of `[213, 2574613]`. -/
def p13524 : Perm := mkPerm (n := 5) ![0, 2, 4, 1, 3]
/-- Rank-5 member `14352` of `[213, 2574613]`. -/
def p14352 : Perm := mkPerm (n := 5) ![0, 3, 2, 4, 1]
/-- Rank-5 member `24351` of `[213, 2574613]`. -/
def p24351 : Perm := mkPerm (n := 5) ![1, 3, 2, 4, 0]
/-- Rank-5 member `24513` of `[213, 2574613]`. -/
def p24513 : Perm := mkPerm (n := 5) ![1, 3, 4, 0, 2]
/-- Rank-5 member `25413` of `[213, 2574613]`. -/
def p25413 : Perm := mkPerm (n := 5) ![1, 4, 3, 0, 2]
/-- Rank-5 member `35241` of `[213, 2574613]`. -/
def p35241 : Perm := mkPerm (n := 5) ![2, 4, 1, 3, 0]
/-- Rank-5 member `43512` of `[213, 2574613]`. -/
def p43512 : Perm := mkPerm (n := 5) ![3, 2, 4, 0, 1]

/-- Rank-6 member `146352` of `[213, 2574613]`. -/
def p146352 : Perm := mkPerm (n := 6) ![0, 3, 5, 2, 4, 1]
/-- Rank-6 member `246351` of `[213, 2574613]`. -/
def p246351 : Perm := mkPerm (n := 6) ![1, 3, 5, 2, 4, 0]
/-- Rank-6 member `246513` of `[213, 2574613]`. -/
def p246513 : Perm := mkPerm (n := 6) ![1, 3, 5, 4, 0, 2]
/-- Rank-6 member `254613` of `[213, 2574613]`. -/
def p254613 : Perm := mkPerm (n := 6) ![1, 4, 3, 5, 0, 2]
/-- Rank-6 member `256413` of `[213, 2574613]`. -/
def p256413 : Perm := mkPerm (n := 6) ![1, 4, 5, 3, 0, 2]
/-- Rank-6 member `264513` of `[213, 2574613]`. -/
def p264513 : Perm := mkPerm (n := 6) ![1, 5, 3, 4, 0, 2]
/-- Rank-6 member `463512` of `[213, 2574613]`. -/
def p463512 : Perm := mkPerm (n := 6) ![3, 5, 2, 4, 0, 1]

/-- List of all 19 members of `[213, 2574613]`. -/
def interval7List : List Perm :=
  [σ₇,
   p1324, p2413, p3241,
   p13524, p14352, p24351, p24513, p25413, p35241, p43512,
   p146352, p246351, p246513, p254613, p256413, p264513, p463512,
   τ₇]

/-- Explicit 19-member `Finset` that we prove equals the genuine `Interval σ₇ τ₇`. -/
def interval7Explicit : Finset Perm := interval7List.toFinset

/-- Soundness of `has213List` for containment of `σ₇ = 213`. -/
theorem has213List_of_sigma7_le {π : Perm} (h : σ₇ ≤ π) : has213List π.toList = true := by
  rcases le_iff_contains.mp h with ⟨f, hf⟩
  have hlen : π.toList.length = π.len := Perm.toList_length π
  let i0 : Fin σ₇.len := ⟨0, by decide⟩
  let i1 : Fin σ₇.len := ⟨1, by decide⟩
  let i2 : Fin σ₇.len := ⟨2, by decide⟩
  have h10 : σ₇.perm i1 < σ₇.perm i0 := by decide
  have h02 : σ₇.perm i0 < σ₇.perm i2 := by decide
  have hji : (π.perm (f i1)).val < (π.perm (f i0)).val := (hf i1 i0).mp h10
  have hik : (π.perm (f i0)).val < (π.perm (f i2)).val := (hf i0 i2).mp h02
  have h01 : (f i0).val < (f i1).val := f.strictMono (by decide : i0 < i1)
  have h12 : (f i1).val < (f i2).val := f.strictMono (by decide : i1 < i2)
  apply has213List_true_of_getElem (i := (f i0).val) (j := (f i1).val) (k := (f i2).val)
    (hlen.symm ▸ (f i0).isLt) (hlen.symm ▸ (f i1).isLt) (hlen.symm ▸ (f i2).isLt) h01 h12
  · simp [Perm.toList, hji]
  · simp [Perm.toList, hik]

private theorem le_of_bitmask {σ τ : Perm} (m : Fin (2 ^ τ.len))
    (h : σ.toList = standardizeList (maskVals τ (bitMask τ.len m)) := by decide) :
    σ ≤ τ :=
  le_iff_exists_bitmask.mpr ⟨m, h⟩

private theorem all_128_masks_classified :
    ∀ m : Fin (2 ^ 7),
      has213List (standardizeList (maskVals τ₇ (bitMask 7 m))) = true →
      standardizeList (maskVals τ₇ (bitMask 7 m)) ∈ interval7List.map Perm.toList := by
  decide

private theorem all_19_in_interval : ∀ p ∈ interval7List, σ₇ ≤ p ∧ p ≤ τ₇ := by
  intro p hp
  simp only [interval7List, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨le_of_bitmask ⟨7, by decide⟩, le_of_bitmask ⟨26, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨14, by decide⟩, le_of_bitmask ⟨27, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨13, by decide⟩, le_of_bitmask ⟨30, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨7, by decide⟩, le_of_bitmask ⟨58, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨26, by decide⟩, le_of_bitmask ⟨31, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨14, by decide⟩, le_of_bitmask ⟨91, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨14, by decide⟩, le_of_bitmask ⟨59, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨25, by decide⟩, le_of_bitmask ⟨103, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨25, by decide⟩, le_of_bitmask ⟨107, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨13, by decide⟩, le_of_bitmask ⟨62, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨7, by decide⟩, le_of_bitmask ⟨122, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨26, by decide⟩, le_of_bitmask ⟨95, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨26, by decide⟩, le_of_bitmask ⟨63, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨49, by decide⟩, le_of_bitmask ⟨119, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨14, by decide⟩, le_of_bitmask ⟨123, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨49, by decide⟩, le_of_bitmask ⟨111, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨49, by decide⟩, le_of_bitmask ⟨125, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨13, by decide⟩, le_of_bitmask ⟨126, by decide⟩⟩
  · exact ⟨le_of_bitmask ⟨26, by decide⟩, le_of_bitmask ⟨127, by decide⟩⟩

/-- `213 ≤ 2574613`. -/
theorem sigma7_le_tau7 : σ₇ ≤ τ₇ :=
  (all_19_in_interval σ₇ (by simp [interval7List])).2

/-- Exact equality between the genuine interval `Interval σ₇ τ₇` and the 19 explicit
permutations. -/
theorem interval7_eq : Interval σ₇ τ₇ = interval7Explicit := by
  ext π
  rw [mem_interval_iff, interval7Explicit, List.mem_toFinset]
  constructor
  · rintro ⟨hlow, hhigh⟩
    have h213 : has213List π.toList = true := has213List_of_sigma7_le hlow
    rcases le_iff_exists_bitmask.mp hhigh with ⟨m, hm⟩
    have hmem_list : π.toList ∈ interval7List.map Perm.toList := by
      rw [hm]
      exact all_128_masks_classified m (hm ▸ h213)
    rcases List.mem_map.mp hmem_list with ⟨q, hq, hqeq⟩
    rw [← Perm.toList_injective hqeq]
    exact hq
  · exact all_19_in_interval π

private theorem interval7List_toList_nodup : (interval7List.map Perm.toList).Nodup := by
  decide

private theorem interval7List_nodup : interval7List.Nodup :=
  List.Nodup.of_map Perm.toList interval7List_toList_nodup

/-- The interval `[213, 2574613]` has exact cardinality 19. -/
theorem interval7_card : (Interval σ₇ τ₇).card = 19 := by
  rw [interval7_eq, interval7Explicit, List.toFinset_card_of_nodup interval7List_nodup]
  rfl

private theorem rankLevel_card_eq_filter_len (r : ℕ) :
    (RankLevel (Interval σ₇ τ₇) r).card =
    (interval7List.filter (fun π => decide (π.len = r))).length := by
  rw [interval7_eq, RankLevel, interval7Explicit]
  have heq : interval7List.toFinset.filter (fun π => π.len = r) =
      (interval7List.filter (fun π => decide (π.len = r))).toFinset := by
    ext π
    simp
  rw [heq, List.toFinset_card_of_nodup (interval7List_nodup.filter _)]

/-- Exact rank sizes of `[213, 2574613]`: `1, 3, 7, 7, 1` for ranks `3, 4, 5, 6, 7`,
and `0` for every other rank. -/
theorem interval7_rank_sizes :
    (RankLevel (Interval σ₇ τ₇) 3).card = 1 ∧
    (RankLevel (Interval σ₇ τ₇) 4).card = 3 ∧
    (RankLevel (Interval σ₇ τ₇) 5).card = 7 ∧
    (RankLevel (Interval σ₇ τ₇) 6).card = 7 ∧
    (RankLevel (Interval σ₇ τ₇) 7).card = 1 ∧
    ∀ r : ℕ, r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 →
      (RankLevel (Interval σ₇ τ₇) r).card = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rankLevel_card_eq_filter_len]; decide
  · rw [rankLevel_card_eq_filter_len]; decide
  · rw [rankLevel_card_eq_filter_len]; decide
  · rw [rankLevel_card_eq_filter_len]; decide
  · rw [rankLevel_card_eq_filter_len]; decide
  · intro r h3 h4 h5 h6 h7
    rw [rankLevel_card_eq_filter_len, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro π hπ
    have hlen : π.len ∈ ([3, 4, 5, 6, 7] : List ℕ) := by
      revert π hπ
      decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    simp only [decide_eq_true_eq]
    rcases hlen with h | h | h | h | h <;> omega

/-- The largest rank size of `[213, 2574613]` is `7`. -/
theorem interval7_largestRank : largestRank (Interval σ₇ τ₇) = 7 := by
  have hr := interval7_rank_sizes
  apply largestRank_eq_of_bounds (r := 5)
  · intro r
    by_cases h3 : r = 3
    · rw [h3, hr.1]; omega
    by_cases h4 : r = 4
    · rw [h4, hr.2.1]; omega
    by_cases h5 : r = 5
    · rw [h5, hr.2.2.1]
    by_cases h6 : r = 6
    · rw [h6, hr.2.2.2.1]
    by_cases h7 : r = 7
    · rw [h7, hr.2.2.2.2.1]; omega
    rw [hr.2.2.2.2.2 r h3 h4 h5 h6 h7]
    exact Nat.zero_le _
  · exact le_of_eq hr.2.2.1.symm

/-! ### Explicit 8-Element Antichain and 8-Chain Cover of `[213, 2574613]` -/

/-- The 8-element antichain inside `[213, 2574613]`:
5 members of length 5 and 3 members of length 6. -/
def anti7List : List Perm :=
  [p13524, p14352, p24351, p35241, p43512, p246513, p256413, p264513]

/-- The 8-element antichain inside `[213, 2574613]` as a `Finset`. -/
def anti7 : Finset Perm := anti7List.toFinset

private theorem anti7List_toList_nodup : (anti7List.map Perm.toList).Nodup := by decide

private theorem anti7List_nodup : anti7List.Nodup :=
  List.Nodup.of_map Perm.toList anti7List_toList_nodup

theorem anti7_card : anti7.card = 8 := by
  rw [anti7, List.toFinset_card_of_nodup anti7List_nodup]
  rfl

theorem anti7_subset : anti7 ⊆ Interval σ₇ τ₇ := by
  rw [interval7_eq, anti7, interval7Explicit]
  intro π hπ
  rw [List.mem_toFinset] at hπ ⊢
  simp only [anti7List, interval7List, List.mem_cons, List.not_mem_nil, or_false] at hπ ⊢
  rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tauto

private theorem anti7_no_5_le_6 :
    ∀ x ∈ ([p13524, p14352, p24351, p35241, p43512] : List Perm),
    ∀ y ∈ ([p246513, p256413, p264513] : List Perm),
    ∀ m : Fin (2 ^ y.len),
      x.toList ≠ standardizeList (maskVals y (bitMask y.len m)) := by
  decide

theorem anti7_isAntichain : IsAntichain anti7 := by
  intro x hx y hy hxy
  rw [anti7, List.mem_toFinset] at hx hy
  have hlen_le := le_len_le hxy
  by_cases heq : x.len = y.len
  · exact eq_of_le_of_len_eq hxy heq
  · exfalso
    have hx_split : x ∈ ([p13524, p14352, p24351, p35241, p43512] : List Perm) ∨
        x ∈ ([p246513, p256413, p264513] : List Perm) := by
      simp only [anti7List, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tauto
    have hy_split : y ∈ ([p13524, p14352, p24351, p35241, p43512] : List Perm) ∨
        y ∈ ([p246513, p256413, p264513] : List Perm) := by
      simp only [anti7List, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tauto
    have hlen5 : ∀ z ∈ ([p13524, p14352, p24351, p35241, p43512] : List Perm), z.len = 5 := by
      decide
    have hlen6 : ∀ z ∈ ([p246513, p256413, p264513] : List Perm), z.len = 6 := by
      decide
    rcases hx_split with hx5 | hx6 <;> rcases hy_split with hy5 | hy6
    · exact heq ((hlen5 x hx5).trans (hlen5 y hy5).symm)
    · rcases le_iff_exists_bitmask.mp hxy with ⟨m, hm⟩
      exact anti7_no_5_le_6 x hx5 y hy6 m hm
    · have := hlen6 x hx6; have := hlen5 y hy5; omega
    · exact heq ((hlen6 x hx6).trans (hlen6 y hy6).symm)

/-- Explicit 8-chain cover of `[213, 2574613]`. -/
def chain7List : Fin 8 → List Perm
  | ⟨0, _⟩ => [p2413, p13524]
  | ⟨1, _⟩ => [p3241, p14352, p146352]
  | ⟨2, _⟩ => [p35241, p246351]
  | ⟨3, _⟩ => [p25413, p246513]
  | ⟨4, _⟩ => [σ₇, p1324, p24351, p254613]
  | ⟨5, _⟩ => [p24513, p256413]
  | ⟨6, _⟩ => [p264513]
  | ⟨7, _⟩ => [p43512, p463512, τ₇]

/-- The 8 chains covering `[213, 2574613]` as `Finset`s. -/
def chains7 (i : Fin 8) : Finset Perm := (chain7List i).toFinset

private theorem isChain_list1 {a : Perm} : IsChain ([a].toFinset) := by
  intro x hx y hy
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  subst hx; subst hy; exact Or.inl le_rfl

private theorem isChain_list2 {a b : Perm} (h : a ≤ b) : IsChain ([a, b].toFinset) := by
  intro x hx y hy
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact Or.inl le_rfl
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl le_rfl

private theorem isChain_list3 {a b c : Perm} (h1 : a ≤ b) (h2 : b ≤ c) :
    IsChain ([a, b, c].toFinset) := by
  intro x hx y hy
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact Or.inl le_rfl
  · exact Or.inl h1
  · exact Or.inl (h1.trans h2)
  · exact Or.inr h1
  · exact Or.inl le_rfl
  · exact Or.inl h2
  · exact Or.inr (h1.trans h2)
  · exact Or.inr h2
  · exact Or.inl le_rfl

private theorem isChain_list4 {a b c d : Perm} (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) :
    IsChain ([a, b, c, d].toFinset) := by
  intro x hx y hy
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
  · exact Or.inl le_rfl
  · exact Or.inl h1
  · exact Or.inl (h1.trans h2)
  · exact Or.inl ((h1.trans h2).trans h3)
  · exact Or.inr h1
  · exact Or.inl le_rfl
  · exact Or.inl h2
  · exact Or.inl (h2.trans h3)
  · exact Or.inr (h1.trans h2)
  · exact Or.inr h2
  · exact Or.inl le_rfl
  · exact Or.inl h3
  · exact Or.inr ((h1.trans h2).trans h3)
  · exact Or.inr (h2.trans h3)
  · exact Or.inr h3
  · exact Or.inl le_rfl

theorem chains7_isChain (i : Fin 8) : IsChain (chains7 i) := by
  fin_cases i
  · exact isChain_list2 (le_of_bitmask ⟨30, by decide⟩)
  · exact isChain_list3 (le_of_bitmask ⟨30, by decide⟩) (le_of_bitmask ⟨59, by decide⟩)
  · exact isChain_list2 (le_of_bitmask ⟨62, by decide⟩)
  · exact isChain_list2 (le_of_bitmask ⟨61, by decide⟩)
  · exact isChain_list4 (le_of_bitmask ⟨14, by decide⟩) (le_of_bitmask ⟨15, by decide⟩)
      (le_of_bitmask ⟨31, by decide⟩)
  · exact isChain_list2 (le_of_bitmask ⟨55, by decide⟩)
  · exact isChain_list1
  · exact isChain_list3 (le_of_bitmask ⟨61, by decide⟩) (le_of_bitmask ⟨126, by decide⟩)

theorem chains7_covers : ∀ π ∈ Interval σ₇ τ₇, ∃ i : Fin 8, π ∈ chains7 i := by
  intro π hπ
  rw [interval7_eq, interval7Explicit, List.mem_toFinset] at hπ
  simp only [interval7List, List.mem_cons, List.not_mem_nil, or_false] at hπ
  rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨4, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨4, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨0, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨1, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨0, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨1, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨4, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨5, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨3, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨2, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨7, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨1, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨2, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨3, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨4, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨5, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨6, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨7, by decide⟩, by simp [chains7, chain7List]⟩
  · exact ⟨⟨7, by decide⟩, by simp [chains7, chain7List]⟩

/-- The width of `[213, 2574613]` is `8`. -/
theorem interval7_width : width (Interval σ₇ τ₇) = 8 := by
  apply le_antisymm
  · calc
      width (Interval σ₇ τ₇) ≤ (Finset.univ : Finset (Fin 8)).card :=
        width_le_of_indexed_chain_cover (fun i _ => chains7_isChain i)
          (fun π hπ => by
            rcases chains7_covers π hπ with ⟨i, hi⟩
            exact ⟨i, Finset.mem_univ i, hi⟩)
      _ = 8 := by simp
  · calc
      8 = anti7.card := anti7_card.symm
      _ ≤ width (Interval σ₇ τ₇) :=
        card_le_width_of_antichain anti7_subset anti7_isAntichain

/-- `[213, 2574613]` is NOT Sperner (`width = 8 ≠ 7 = largestRank`). -/
theorem not_sperner_interval7 : ¬ IsSperner (Interval σ₇ τ₇) := by
  unfold IsSperner
  rw [interval7_width, interval7_largestRank]
  omega

/-- **Refutation of McNamara–Steingrímsson (2015) Question 9.5**:
Not every interval in the classical permutation pattern poset is Sperner. -/
theorem mcnamara_steingrimsson_Q9_5_false :
    ∃ σ τ : Perm, σ ≤ τ ∧ ¬ IsSperner (Interval σ τ) :=
  ⟨σ₇, τ₇, sigma7_le_tau7, not_sperner_interval7⟩

end PatternPoset
