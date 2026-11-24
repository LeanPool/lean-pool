/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs2

/-!
# Rado's theorem on independent transversals

R. Rado, *A theorem on independence relations*, Quart. J. Math. Oxford 13 (1942), 83–89. Quickly
excluding a planar graph
uses this in the proof of (2.10), page 329. We prove it for a rank function on a finite set, by the
usual reduction: a set
`Y i` with two elements can lose one of them.
-/

@[expose] public section

namespace GraphMinor.RST94

open Set GM10

variable {α ι : Type*} [Fintype ι]

/-- The union of the sets `Y i`, `i ∈ I`. -/
def unionOver (Y : ι → Set α) (I : Finset ι) : Set α := ⋃ i ∈ I, Y i

omit [Fintype ι] in
theorem unionOver_subset {E : Set α} {Y : ι → Set α} (hY : ∀ i, Y i ⊆ E)
  (I : Finset ι) : unionOver Y I ⊆ E :=
  iUnion₂_subset fun i _ => hY i

/-- **Rado's theorem**, for a rank function `r` on a finite set `E`: if each `I` has `|I| ≤ r(⋃_{i ∈
I} Y i)`, then there
are `y i ∈ Y i`, all different, whose set has rank `|ι|`. -/
theorem rado {E : Set α} (hE : E.Finite) {r : Set α → ℕ} (hr : IsMatroidRankOn E r) (Y : ι → Set α)
    (hY : ∀ i, Y i ⊆ E) (h : ∀ I : Finset ι, I.card ≤ r (unionOver Y I)) :
    ∃ y : ι → α, (∀ i, y i ∈ Y i) ∧ Function.Injective y ∧ r (range y) = Fintype.card ι := by
  classical
  induction hn : ∑ i, (Y i).ncard using Nat.strong_induction_on generalizing Y with
  | _ n ih =>
  have hfin : ∀ i, (Y i).Finite := fun i => hE.subset (hY i)
  by_cases hall : ∀ i, (Y i).Subsingleton
  · -- Every set has one element.
    have hne : ∀ i, (Y i).Nonempty := fun i => by
      have h₁ := h {i}
      have h₂ := hr.le_ncard (unionOver_subset hY {i})
      simp only [unionOver, Finset.card_singleton, Finset.mem_singleton, iUnion_iUnion_eq_left]
        at h₁ h₂
      exact (ncard_pos (hfin i)).1 (by omega)
    choose y hy using hne
    have hun : unionOver Y Finset.univ = range y := by
      ext x
      simp only [unionOver, Finset.mem_univ, iUnion_true, mem_iUnion, mem_range]
      exact exists_congr fun i => ⟨fun hx => (hall i) (hy i) hx, fun hx => hx ▸ hy i⟩
    have hsub : range y ⊆ E := fun x ⟨i, hi⟩ => hi ▸ hY i (hy i)
    have h₁ := h Finset.univ
    rw [hun, Finset.card_univ] at h₁
    have h₂ := hr.le_ncard hsub
    have hcard : (range y).ncard ≤ Fintype.card ι := by
      rw [← image_univ, ← Finset.coe_univ, ← Finset.coe_image, ncard_coe_finset]
      exact Finset.card_image_le
    refine ⟨y, hy, ?_, by omega⟩
    have : (Finset.univ.image y).card = (Finset.univ : Finset ι).card := by
      have h₃ : (range y).ncard = (Finset.univ.image y).card := by
        rw [← image_univ, ← Finset.coe_univ, ← Finset.coe_image, ncard_coe_finset]
      rw [← h₃, Finset.card_univ]
      omega
    exact fun a b e => (Finset.card_image_iff.1 this) (by simp) (by simp) e
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    obtain ⟨x, hx, x', hx', hne⟩ := hi
    -- The set `Y` with `a` removed from `Y i`.
    let Yo : α → ι → Set α := fun a => Function.update Y i (Y i \ {a})
    have hYo : ∀ a j, Yo a j ⊆ E := fun a j => by
      by_cases hj : j = i
      · subst hj
        simp only [Yo, Function.update_self]
        exact sdiff_subset.trans (hY j)
      · simpa [Yo, hj] using hY j
    have hYoY : ∀ a j, Yo a j ⊆ Y j := fun a j => by
      by_cases hj : j = i
      · subst hj
        simp [Yo, sdiff_subset]
      · simp [Yo, hj]
    have hsum : ∀ a ∈ Y i, ∑ j, (Yo a j).ncard < n := fun a ha => by
      rw [← hn]
      refine Finset.sum_lt_sum (fun j _ => ncard_le_ncard (hYoY a j) (hfin j)) ⟨i, Finset.mem_univ
        _, ?_⟩
      simp only [Yo, Function.update_self]
      exact ncard_sdiff_singleton_lt_of_mem ha (hfin i)
    by_cases h₁ : ∀ I : Finset ι, I.card ≤ r (unionOver (Yo x) I)
    · obtain ⟨y, hy, hinj, hrk⟩ := ih _ (hsum x hx) (Yo x) (hYo x) h₁ rfl
      exact ⟨y, fun j => hYoY x j (hy j), hinj, hrk⟩
    by_cases h₂ : ∀ I : Finset ι, I.card ≤ r (unionOver (Yo x') I)
    · obtain ⟨y, hy, hinj, hrk⟩ := ih _ (hsum x' hx') (Yo x') (hYo x') h₂ rfl
      exact ⟨y, fun j => hYoY x' j (hy j), hinj, hrk⟩
    exfalso
    push Not at h₁ h₂
    obtain ⟨I₁, hI₁⟩ := h₁
    obtain ⟨I₂, hI₂⟩ := h₂
    -- The sets that fail both contain `i`.
    have hmem : ∀ a (I : Finset ι), r (unionOver (Yo a) I) < I.card → i ∈ I := fun a I hI => by
      by_contra hn'
      have : unionOver (Yo a) I = unionOver Y I := by
        refine iUnion₂_congr fun j hj => ?_
        have : j ≠ i := fun e => hn' (e ▸ hj)
        simp [Yo, this]
      rw [this] at hI
      exact absurd (h I) (by omega)
    have hi₁ := hmem x I₁ hI₁
    have hi₂ := hmem x' I₂ hI₂
    let A₁ := unionOver (Yo x) I₁
    let A₂ := unionOver (Yo x') I₂
    have hA₁ : A₁ ⊆ E := unionOver_subset (hYo x) I₁
    have hA₂ : A₂ ⊆ E := unionOver_subset (hYo x') I₂
    have hsm := hr.submodular hA₁ hA₂
    have hI₁' : r A₁ < I₁.card := hI₁
    have hI₂' : r A₂ < I₂.card := hI₂
    have hU : unionOver Y (I₁ ∪ I₂) ⊆ A₁ ∪ A₂ := by
      refine iUnion₂_subset fun j hj z hz => ?_
      by_cases hji : j = i
      · subst hji
        by_cases hzx : z = x
        · refine Or.inr (mem_iUnion₂.2 ⟨j, hi₂, ?_⟩)
          simp only [Yo, Function.update_self]
          exact ⟨hzx ▸ hx, by simpa [hzx] using hne⟩
        · refine Or.inl (mem_iUnion₂.2 ⟨j, hi₁, ?_⟩)
          simp only [Yo, Function.update_self]
          exact ⟨hz, by simpa using hzx⟩
      · rcases Finset.mem_union.1 hj with hj | hj
        · exact Or.inl (mem_iUnion₂.2 ⟨j, hj, by simpa [Yo, hji] using hz⟩)
        · exact Or.inr (mem_iUnion₂.2 ⟨j, hj, by simpa [Yo, hji] using hz⟩)
    have hI : unionOver Y ((I₁ ∩ I₂).erase i) ⊆ A₁ ∩ A₂ := by
      refine iUnion₂_subset fun j hj z hz => ?_
      obtain ⟨hji, hj⟩ := Finset.mem_erase.1 hj
      obtain ⟨hj₁, hj₂⟩ := Finset.mem_inter.1 hj
      exact ⟨mem_iUnion₂.2 ⟨j, hj₁, by simpa [Yo, hji] using hz⟩, mem_iUnion₂.2 ⟨j, hj₂, by simpa
        [Yo, hji] using hz⟩⟩
    have h₃ := (h (I₁ ∪ I₂)).trans (hr.mono hU (union_subset hA₁ hA₂))
    have h₄ := (h ((I₁ ∩ I₂).erase i)).trans (hr.mono hI (inter_subset_left.trans hA₁))
    have hcard := Finset.card_union_add_card_inter I₁ I₂
    rw [Finset.card_erase_of_mem (Finset.mem_inter.2 ⟨hi₁, hi₂⟩)] at h₄
    have hpos : 0 < (I₁ ∩ I₂).card := Finset.card_pos.2 ⟨i, Finset.mem_inter.2 ⟨hi₁, hi₂⟩⟩
    omega

end GraphMinor.RST94
