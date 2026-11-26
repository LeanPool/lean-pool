/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# The finite Erdős–Szekeres theorem

XVI (8.1), Claim (4), page 72, selects paths whose ends have the same
order on two circles, after possibly reversing one orientation. The
finite sequence theorem needed there follows by labeling each term
with the lengths of the longest increasing and decreasing subsequences
ending at that term. These pairs of lengths are all distinct.
-/

public section
namespace GraphMinor.GM16
open Set Finset

private noncomputable def endingChains {ι α : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder α]
    (f : ι → α) (i : ι) : Finset (Finset ι) := by
  classical
  exact univ.powerset.filter (fun s => i ∈ s ∧ (∀ j ∈ s, j ≤ i) ∧ StrictMonoOn f (s : Set ι))

private theorem singleton_mem_endingChains {ι α : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder α]
    (f : ι → α) (i : ι) : {i} ∈ endingChains f i := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
    Finset.mem_singleton_self i, fun j hj => (Finset.mem_singleton.mp hj).le, ?_⟩
  intro a ha b hb hab
  exact False.elim ((ne_of_lt hab) ((Finset.mem_singleton.mp ha).trans
    (Finset.mem_singleton.mp hb).symm))

private noncomputable def endingLength {ι α : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder α]
    (f : ι → α) (i : ι) : ℕ := (endingChains f i).sup Finset.card

private theorem endingLength_witness {ι α : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder α]
    (f : ι → α) (i : ι) : ∃ s : Finset ι,
      i ∈ s ∧ (∀ j ∈ s, j ≤ i) ∧ StrictMonoOn f (s : Set ι) ∧ s.card = endingLength f i := by
  classical
  obtain ⟨s, hs, hcard⟩ := exists_mem_eq_sup (endingChains f i)
    ⟨{i}, singleton_mem_endingChains f i⟩ Finset.card
  have hs' := (mem_filter.mp hs).2
  exact ⟨s, hs'.1, hs'.2.1, hs'.2.2, hcard.symm⟩

private theorem endingLength_pos {ι α : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder α]
    (f : ι → α) (i : ι) : 1 ≤ endingLength f i := by
  classical
  have h := le_sup (f := Finset.card) (singleton_mem_endingChains f i)
  change 1 ≤ (endingChains f i).sup Finset.card
  simpa only [card_singleton] using h

private theorem endingLength_lt_of_lt {ι α : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder α]
    (f : ι → α) {i j : ι} (hij : i < j) (hfij : f i < f j) :
    endingLength f i < endingLength f j := by
  classical
  obtain ⟨s, his, hle, hmono, hcard⟩ := endingLength_witness f i
  have hjs : j ∉ s := fun hj => (not_le_of_gt hij) (hle j hj)
  have hmem : insert j s ∈ endingChains f j := by
    refine mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), mem_insert_self _ _, ?_,
      ?_⟩
    · intro k hk
      rcases mem_insert.mp hk with rfl | hk
      · exact le_rfl
      · exact (hle k hk).trans (le_of_lt hij)
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with haJ | haS
      · have hbLe : b ≤ j := (Finset.mem_insert.mp hb).elim (fun h => h.le)
          (fun h => (hle b h).trans (le_of_lt hij))
        exact False.elim ((not_lt_of_ge hbLe) (haJ ▸ hab))
      · rcases Finset.mem_insert.mp hb with hbJ | hbS
        · have hfai : f a ≤ f i := by
            by_cases hai : a = i
            · exact le_of_eq (congrArg f hai)
            · exact le_of_lt (hmono haS his (lt_of_le_of_ne (hle a haS) hai))
          rw [hbJ]
          exact lt_of_le_of_lt hfai hfij
        · exact hmono haS hbS hab
  have hb := le_sup (f := Finset.card) hmem
  rw [card_insert_of_notMem hjs, hcard] at hb
  exact Nat.lt_of_succ_le hb

/-- The finite Erdős–Szekeres theorem used in Graph Minors XVI (8.1),
Claim (4), page 72. An injective sequence of `m²` terms in a linear order
has an increasing or decreasing subsequence with at least `m` terms. -/
theorem erdos_szekeres {α : Type*} [LinearOrder α] (m : ℕ) (hm : 1 ≤ m)
    (f : Fin (m ^ 2) → α) (hf : Function.Injective f) :
    ∃ s : Finset (Fin (m ^ 2)), m ≤ s.card ∧
      (StrictMonoOn f (s : Set (Fin (m ^ 2))) ∨ StrictAntiOn f (s : Set (Fin (m ^ 2)))) := by
  classical
  by_contra hn
  have hInc : ∀ i, endingLength f i < m := by
    intro i
    obtain ⟨s, _, _, hMono, hcard⟩ := endingLength_witness f i
    by_contra hlarge
    exact hn ⟨s, hcard ▸ (Nat.le_of_not_gt hlarge), Or.inl hMono⟩
  let fRev : Fin (m ^ 2) → OrderDual α := f
  have hDec : ∀ i, endingLength fRev i < m := by
    intro i
    obtain ⟨s, _, _, hMono, hcard⟩ := endingLength_witness fRev i
    by_contra hlarge
    exact hn ⟨s, hcard ▸ (Nat.le_of_not_gt hlarge), Or.inr hMono⟩
  let label : Fin (m ^ 2) → Fin (m - 1) × Fin (m - 1) := fun i =>
    (⟨endingLength f i - 1, by have := endingLength_pos f i; have := hInc i; omega⟩,
      ⟨endingLength fRev i - 1, by have := endingLength_pos fRev i; have := hDec i; omega⟩)
  have hLabel : Function.Injective label := by
    intro i j heq
    by_contra hij
    have hneq : f i ≠ f j := fun he => hij (hf he)
    have hLabels : endingLength f i = endingLength f j ∧
        endingLength fRev i = endingLength fRev j := by
      have h₁ := congrArg (fun p => p.1.val) heq
      have h₂ := congrArg (fun p => p.2.val) heq
      have hi := endingLength_pos f i
      have hj := endingLength_pos f j
      have hi' := endingLength_pos fRev i
      have hj' := endingLength_pos fRev j
      dsimp only [label] at h₁ h₂
      omega
    rcases lt_or_gt_of_ne hij with hij | hji
    · rcases lt_or_gt_of_ne hneq with hlt | hgt
      · exact (ne_of_lt (endingLength_lt_of_lt f hij hlt)) hLabels.1
      · exact (ne_of_lt (endingLength_lt_of_lt fRev hij hgt)) hLabels.2
    · rcases lt_or_gt_of_ne hneq with hlt | hgt
      · exact (ne_of_lt (endingLength_lt_of_lt fRev hji hlt)) hLabels.2.symm
      · exact (ne_of_lt (endingLength_lt_of_lt f hji hgt)) hLabels.1.symm
  have hc := Fintype.card_le_of_injective label hLabel
  simp only [Fintype.card_fin, Fintype.card_prod] at hc
  have hmEq : m - 1 + 1 = m := by omega
  nlinarith

/-- The sequence form of the selection in XVI (8.1), Claim (4):
retain exactly `m` indices, in their original order. -/
theorem erdos_szekeres_subsequence {α : Type*} [LinearOrder α] (m : ℕ) (hm : 1 ≤ m)
    (f : Fin (m ^ 2) → α) (hf : Function.Injective f) :
    ∃ g : Fin m → Fin (m ^ 2), StrictMono g ∧
      (StrictMono (f ∘ g) ∨ StrictAnti (f ∘ g)) := by
  classical
  obtain ⟨s, hsize, hOrder⟩ := erdos_szekeres m hm f hf
  let g : Fin m → Fin (m ^ 2) := fun i =>
    s.orderEmbOfFin rfl ⟨i.val, lt_of_lt_of_le i.isLt hsize⟩
  have hg : StrictMono g := by
    intro i j hij
    exact (s.orderEmbOfFin rfl).strictMono (show (⟨i.val, lt_of_lt_of_le i.isLt hsize⟩ : Fin
      s.card) <
      ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ from hij)
  have hgs : ∀ i, g i ∈ (s : Set (Fin (m ^ 2))) := fun i => s.orderEmbOfFin_mem rfl _
  refine ⟨g, hg, ?_⟩
  rcases hOrder with hMono | hAnti
  · exact Or.inl (fun i j hij => hMono (hgs i) (hgs j) (hg hij))
  · exact Or.inr (fun i j hij => hAnti (hgs i) (hgs j) (hg hij))

end GraphMinor.GM16
