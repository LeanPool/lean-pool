/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Order.Antichain
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
/-!

Imported from [jtraverso/konig-edge-colouring](https://github.com/jtraverso/konig-edge-colouring/blob/7c60f7efb69c1747aaf39e5dfa7a89d907cd84ef/Konig/Dilworth.lean), registered as PALOMAR-2026-10-15-000019. The original proof is retained; module paths and imports are adapted for this collection.

# Dilworth's and Mirsky's theorems

For a finite partially ordered set:

* `dilworth`: **Dilworth (1950).** There are an antichain `A` and a partition of the poset into
  `|A|` chains; hence the maximum size of an antichain equals the minimum number of chains
  covering the poset.
* `mirsky`: **Mirsky (1971).** There are a chain `C` and a partition of the poset into `|C|`
  antichains; hence the maximum size of a chain equals the minimum number of antichains covering
  the poset.

A partition into `m` parts is a map to `Fin m`, whose fibres are the parts (some may be empty).
-/

@[expose] public section

namespace Konig.Poset

open Classical in
/-- The width of a finite set: the maximum size of an antichain contained in it. -/
noncomputable def antichainWidth {α : Type*} [PartialOrder α] (S : Finset α) : ℕ :=
  (S.powerset.filter (fun A : Finset α => IsAntichain (· ≤ ·) (A : Set α))).sup Finset.card

section
variable {α : Type*} [PartialOrder α]

lemma card_le_antichainWidth {S A : Finset α} (hAS : A ⊆ S)
    (hA : IsAntichain (· ≤ ·) (A : Set α)) : A.card ≤ antichainWidth S := by
  classical
  unfold antichainWidth
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hAS, hA⟩)

lemma exists_card_eq_antichainWidth (S : Finset α) :
    ∃ A ⊆ S, IsAntichain (· ≤ ·) (A : Set α) ∧ A.card = antichainWidth S := by
  classical
  obtain ⟨A, hA, hAeq⟩ := Finset.exists_mem_eq_sup
    (S.powerset.filter (fun A : Finset α => IsAntichain (· ≤ ·) (A : Set α)))
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset S, by simp⟩⟩ Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  refine ⟨A, hA.1, hA.2, ?_⟩
  unfold antichainWidth
  convert hAeq.symm

lemma antichainWidth_mono {S T : Finset α} (h : S ⊆ T) :
    antichainWidth S ≤ antichainWidth T := by
  obtain ⟨A, hAS, hA, hAc⟩ := exists_card_eq_antichainWidth S
  exact hAc ▸ card_le_antichainWidth (hAS.trans h) hA

/-- An antichain of size `k` meets every one of `k` chains covering the set. -/
lemma exists_mem_label {S : Finset α} {c : α → ℕ} {k : ℕ} (hc : ∀ x ∈ S, c x < k)
    (hch : ∀ i, IsChain (· ≤ ·) {x | x ∈ S ∧ c x = i}) {A : Finset α} (hAS : A ⊆ S)
    (hA : IsAntichain (· ≤ ·) (A : Set α)) (hAk : A.card = k) :
    ∀ i < k, ∃ y ∈ A, c y = i := by
  classical
  have hinj : Set.InjOn c A := by
    intro x hx y hy hxy
    by_contra hne
    rcases hch (c x) ⟨hAS hx, rfl⟩ ⟨hAS hy, hxy.symm⟩ hne with h | h
    · exact hA hx hy hne h
    · exact hA hy hx (Ne.symm hne) h
  have himg : A.image c = Finset.range k := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact Finset.mem_range.2 (hc x (hAS hx))
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range, hAk]
  intro i hi
  have : i ∈ A.image c := himg ▸ Finset.mem_range.2 hi
  simpa using this

/-- Dilworth's theorem for a finite set `S`, in labelling form (Galvin's proof): `S` is covered by
`antichainWidth S` chains, the `i`-th chain being the elements of `S` labelled `i`. -/
theorem dilworth_finset (S : Finset α) : ∃ c : α → ℕ, (∀ x ∈ S, c x < antichainWidth S) ∧
    ∀ i, IsChain (· ≤ ·) {x | x ∈ S ∧ c x = i} := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ => 0, by simp, fun i => ?_⟩
    simp [IsChain]
  obtain ⟨a, haS, hamax⟩ := Finset.exists_maximal hne
  have hamax' : ∀ x ∈ S, a ≤ x → x = a := fun x hx hax => le_antisymm (hamax hx hax) hax
  have : Nonempty α := ⟨a⟩
  set S' := S.erase a with hS'
  have hS'S : S' ⊆ S := Finset.erase_subset a S
  obtain ⟨c', hc'lt, hc'ch⟩ := ih S' (Finset.erase_ssubset haS)
  set k := antichainWidth S' with hk
  have hD : ∀ i < k, ∃ x, (x ∈ S' ∧ c' x = i ∧ ∃ A ⊆ S', IsAntichain (· ≤ ·) (A : Set α) ∧
      A.card = k ∧ x ∈ A) ∧ ∀ y, (y ∈ S' ∧ c' y = i ∧ ∃ A ⊆ S',
        IsAntichain (· ≤ ·) (A : Set α) ∧ A.card = k ∧ y ∈ A) → y ≤ x := by
    intro i hi
    set D := S'.filter (fun y => c' y = i ∧ ∃ A ⊆ S', IsAntichain (· ≤ ·) (A : Set α) ∧
      A.card = k ∧ y ∈ A) with hD
    have hDne : D.Nonempty := by
      obtain ⟨A, hAS, hA, hAk⟩ := exists_card_eq_antichainWidth S'
      obtain ⟨y, hyA, hy⟩ := exists_mem_label hc'lt hc'ch hAS hA hAk i hi
      exact ⟨y, Finset.mem_filter.2 ⟨hAS hyA, hy, A, hAS, hA, hAk, hyA⟩⟩
    obtain ⟨x, hxD, hxmax⟩ := Finset.exists_maximal hDne
    have hx := Finset.mem_filter.1 hxD
    refine ⟨x, ⟨hx.1, hx.2⟩, fun y hy => ?_⟩
    by_cases hxy : y = x
    · exact le_of_eq hxy
    rcases hc'ch i ⟨hy.1, hy.2.1⟩ ⟨hx.1, hx.2.1⟩ hxy with h | h
    · exact h
    · exact absurd (le_antisymm (hxmax (Finset.mem_filter.2 ⟨hy.1, hy.2⟩) h) h) hxy
  choose! x hxD hxmax using hD
  have hxinc : ∀ i < k, ∀ j < k, i ≠ j → ¬ x i ≤ x j := by
    intro i hi j hj hij hle
    obtain ⟨A, hAS, hA, hAk, hxjA⟩ := (hxD j hj).2.2
    obtain ⟨y, hyA, hyi⟩ := exists_mem_label hc'lt hc'ch hAS hA hAk i hi
    have hyx : y ≤ x i := hxmax i hi y ⟨hAS hyA, hyi, A, hAS, hA, hAk, hyA⟩
    have hyne : y ≠ x j := by
      intro h
      apply hij
      rw [← hyi, h, (hxD j hj).2.1]
    exact hA hyA hxjA hyne (hyx.trans hle)
  have hwS : k ≤ antichainWidth S := antichainWidth_mono hS'S
  by_cases hcase : ∃ i < k, x i ≤ a
  · obtain ⟨i, hi, hxa⟩ := hcase
    set K := insert a (S'.filter (fun z => c' z = i ∧ z ≤ x i)) with hK
    set T := S \ K with hT
    have hTS' : T ⊆ S' := by
      intro z hz
      rw [hT, Finset.mem_sdiff, hK, Finset.mem_insert, not_or] at hz
      exact Finset.mem_erase.2 ⟨hz.2.1, hz.1⟩
    obtain ⟨c'', hc''lt, hc''ch⟩ := ih T (lt_of_le_of_lt hTS' (Finset.erase_ssubset haS))
    have hwT : antichainWidth T < k := by
      obtain ⟨B, hBT, hB, hBw⟩ := exists_card_eq_antichainWidth T
      by_contra hge
      push Not at hge
      have hBS' : B ⊆ S' := hBT.trans hTS'
      have hBk : B.card = k := le_antisymm (card_le_antichainWidth hBS' hB) (hBw ▸ hge)
      obtain ⟨y, hyB, hyi⟩ := exists_mem_label hc'lt hc'ch hBS' hB hBk i hi
      have hyx : y ≤ x i := hxmax i hi y ⟨hBS' hyB, hyi, B, hBS', hB, hBk, hyB⟩
      have hyK : y ∈ K := Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hBS' hyB, hyi, hyx⟩)
      exact (Finset.mem_sdiff.1 (hBT hyB)).2 hyK
    have hKch : ∀ z ∈ K, ∀ w ∈ K, z ≤ w ∨ w ≤ z := by
      have hfil : ∀ z ∈ S'.filter (fun z => c' z = i ∧ z ≤ x i), z ≤ a := fun z hz =>
        (Finset.mem_filter.1 hz).2.2.trans hxa
      intro z hz w hw
      rw [hK, Finset.mem_insert] at hz hw
      rcases hz with rfl | hz <;> rcases hw with rfl | hw
      · exact Or.inl le_rfl
      · exact Or.inr (hfil w hw)
      · exact Or.inl (hfil z hz)
      · by_cases hzw : z = w
        · exact Or.inl (le_of_eq hzw)
        have hz' := Finset.mem_filter.1 hz
        have hw' := Finset.mem_filter.1 hw
        exact hc'ch i ⟨hz'.1, hz'.2.1⟩ ⟨hw'.1, hw'.2.1⟩ hzw
    refine ⟨fun z => if z ∈ K then k - 1 else c'' z, ?_, ?_⟩
    · intro z hz
      by_cases hzK : z ∈ K
      · simp only [hzK, ite_true]
        omega
      · simp only [hzK, ite_false]
        have := hc''lt z (Finset.mem_sdiff.2 ⟨hz, hzK⟩)
        omega
    · intro j z hz w hw hne
      simp only [Set.mem_ofPred_eq] at hz hw
      by_cases hzK : z ∈ K <;> by_cases hwK : w ∈ K
      · exact hKch z hzK w hwK
      · simp only [hzK, hwK, ite_true, ite_false] at hz hw
        have := hc''lt w (Finset.mem_sdiff.2 ⟨hw.1, hwK⟩)
        omega
      · simp only [hzK, hwK, ite_true, ite_false] at hz hw
        have := hc''lt z (Finset.mem_sdiff.2 ⟨hz.1, hzK⟩)
        omega
      · simp only [hzK, hwK, ite_false] at hz hw
        exact hc''ch j ⟨Finset.mem_sdiff.2 ⟨hz.1, hzK⟩, hz.2⟩
          ⟨Finset.mem_sdiff.2 ⟨hw.1, hwK⟩, hw.2⟩ hne
  · push Not at hcase
    have hxS' : ∀ i < k, x i ∈ S' := fun i hi => (hxD i hi).1
    set A := insert a ((Finset.range k).image x) with hA
    have hinj : Set.InjOn x (Finset.range k) := by
      intro i hi j hj hij
      have hi' := Finset.mem_range.1 hi
      have hj' := Finset.mem_range.1 hj
      rw [← (hxD i hi').2.1, ← (hxD j hj').2.1, hij]
    have haimg : a ∉ (Finset.range k).image x := by
      intro h
      rw [Finset.mem_image] at h
      obtain ⟨i, hi, hia⟩ := h
      have := hxS' i (Finset.mem_range.1 hi)
      rw [hia, hS'] at this
      simp at this
    have hAcard : A.card = k + 1 := by
      rw [hA, Finset.card_insert_of_notMem haimg, Finset.card_image_of_injOn hinj,
        Finset.card_range]
    have hAS : A ⊆ S := by
      intro z hz
      rw [hA, Finset.mem_insert, Finset.mem_image] at hz
      rcases hz with rfl | ⟨i, hi, rfl⟩
      · exact haS
      · exact hS'S (hxS' i (Finset.mem_range.1 hi))
    have hAanti : IsAntichain (· ≤ ·) (A : Set α) := by
      rw [hA, Finset.coe_insert]
      refine IsAntichain.insert ?_ ?_ ?_
      · intro z hz w hw hne
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hz hw
        obtain ⟨i, hi, rfl⟩ := hz
        obtain ⟨j, hj, rfl⟩ := hw
        exact hxinc i hi j hj (fun h => hne (h ▸ rfl))
      · intro z hz _
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hz
        obtain ⟨i, hi, rfl⟩ := hz
        exact hcase i hi
      · intro z hz hne hle
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hz
        obtain ⟨i, hi, rfl⟩ := hz
        exact hne (hamax' _ (hS'S (hxS' i hi)) hle).symm
    have hwA : k + 1 ≤ antichainWidth S := hAcard ▸ card_le_antichainWidth hAS hAanti
    refine ⟨fun z => if z = a then k else c' z, ?_, ?_⟩
    · intro z hz
      by_cases hza : z = a
      · simp only [hza, ite_true]
        omega
      · simp only [hza, ite_false]
        have := hc'lt z (Finset.mem_erase.2 ⟨hza, hz⟩)
        omega
    · intro j z hz w hw hne
      simp only [Set.mem_ofPred_eq] at hz hw
      by_cases hza : z = a <;> by_cases hwa : w = a
      · exact absurd (hza.trans hwa.symm) hne
      · simp only [hza, hwa, ite_true, ite_false] at hz hw
        have := hc'lt w (Finset.mem_erase.2 ⟨hwa, hw.1⟩)
        omega
      · simp only [hza, hwa, ite_true, ite_false] at hz hw
        have := hc'lt z (Finset.mem_erase.2 ⟨hza, hz.1⟩)
        omega
      · simp only [hza, hwa, ite_false] at hz hw
        exact hc'ch j ⟨Finset.mem_erase.2 ⟨hza, hz.1⟩, hz.2⟩
          ⟨Finset.mem_erase.2 ⟨hwa, hw.1⟩, hw.2⟩ hne

end

/-- **Dilworth's theorem (1950).** A finite poset has an antichain `A` and a partition into `|A|`
chains. -/
theorem dilworth {α : Type*} [PartialOrder α] [Finite α] :
    ∃ A : Finset α, IsAntichain (· ≤ ·) (A : Set α) ∧
      ∃ c : α → Fin A.card, ∀ i, IsChain (· ≤ ·) {x | c x = i} := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨c, hclt, hcch⟩ := dilworth_finset (Finset.univ : Finset α)
  obtain ⟨A, -, hA, hAc⟩ := exists_card_eq_antichainWidth (Finset.univ : Finset α)
  refine ⟨A, hA, fun x => ⟨c x, hAc ▸ hclt x (Finset.mem_univ x)⟩, fun i => ?_⟩
  refine (hcch i).mono ?_
  intro x hx
  simp only [Set.mem_ofPred_eq, Fin.ext_iff] at hx ⊢
  exact ⟨Finset.mem_univ x, hx⟩

/-- **Mirsky's theorem (1971).** A finite poset has a chain `C` and a partition into `|C|`
antichains. -/
theorem mirsky {α : Type*} [PartialOrder α] [Finite α] :
    ∃ C : Finset α, IsChain (· ≤ ·) (C : Set α) ∧
      ∃ c : α → Fin C.card, ∀ i, IsAntichain (· ≤ ·) {x | c x = i} := by
  classical
  have := Fintype.ofFinite α
  set chains : Finset (Finset α) :=
    Finset.univ.filter (fun C : Finset α => IsChain (· ≤ ·) (C : Set α)) with hchains
  obtain ⟨C₀, hC₀, hmax⟩ := chains.exists_max_image Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp⟩⟩
  set top : α → Finset (Finset α) :=
    fun x => chains.filter (fun C => x ∈ C ∧ ∀ y ∈ C, y ≤ x) with htop
  set h : α → ℕ := fun x => (top x).sup Finset.card with hh
  have hsing : ∀ x, {x} ∈ top x := fun x => by
    simp [htop, hchains]
  have h_ge : ∀ x, 1 ≤ h x := fun x => by
    have := Finset.le_sup (f := Finset.card) (hsing x)
    rw [Finset.card_singleton] at this
    exact this
  have h_le : ∀ x, h x ≤ C₀.card := fun x =>
    Finset.sup_le fun C hC => hmax C (Finset.mem_filter.1 hC).1
  have h_mono : ∀ x y, x < y → h x < h y := by
    intro x y hxy
    obtain ⟨C, hC, hCc⟩ := Finset.exists_mem_eq_sup (top x) ⟨{x}, hsing x⟩ Finset.card
    have hC' := Finset.mem_filter.1 hC
    have hCch : IsChain (· ≤ ·) (C : Set α) := (Finset.mem_filter.1 hC'.1).2
    have hyC : y ∉ C := fun hy => (hC'.2.2 y hy).not_gt hxy
    have hmem : insert y C ∈ top y := by
      refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩,
        Finset.mem_insert_self y C, ?_⟩
      · rw [Finset.coe_insert]
        exact hCch.insert fun b hb _ => Or.inr ((hC'.2.2 b hb).trans hxy.le)
      · intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact le_rfl
        · exact (hC'.2.2 z hz).trans hxy.le
    have := Finset.le_sup (f := Finset.card) hmem
    rw [Finset.card_insert_of_notMem hyC] at this
    change (top x).sup Finset.card < (top y).sup Finset.card
    omega
  refine ⟨C₀, (Finset.mem_filter.1 hC₀).2,
    fun x => ⟨h x - 1, by have := h_ge x; have := h_le x; omega⟩, fun i => ?_⟩
  intro x hx y hy hne hle
  simp only [Set.mem_ofPred_eq, Fin.ext_iff] at hx hy
  have := h_mono x y (lt_of_le_of_ne hle hne)
  have := h_ge x
  have := h_ge y
  omega

end Konig.Poset
