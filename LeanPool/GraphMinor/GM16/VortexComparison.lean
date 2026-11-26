/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2a
import LeanPool.GraphMinor.GM09.Section2d

/-!
# Comparing the vortex definitions in XV and XVI

For XVI (7.2), page 62, we use the segregations constructed in XV.
A half-open interval and its complement form a fence of the cyclic order.
Thus disjoint paths across the partition in XVI form a transaction in XV,
with the same cardinality bound.
-/

public section
namespace GraphMinor.GM16
open Set Function Graph GraphMinor.GM09 GraphMinor.GM15
universe u v

/-- The two half-open intervals between distinct boundary vertices form
 a fence of the cyclic order. -/
theorem isFence_half_open_intervals {α : Type u} (Ω : CyclicPerm α)
    {x y : α} (hx : x ∈ Ω.bar) (hy : y ∈ Ω.bar) (hxy : x ≠ y) :
    Ω.IsFence (Ω.interval x y ∪ {x}) (Ω.interval y x ∪ {y}) := by
  have hclosed := Ω.isFence_interval_compl hx hy hxy
  have hA : Ω.interval x y ∪ {x} ⊆ {x, y} ∪ Ω.interval x y := by
    rintro z (hz | rfl)
    · exact Or.inr hz
    · exact Or.inl (Or.inl rfl)
  have hd : Disjoint (Ω.interval x y ∪ {x}) (Ω.interval y x ∪ {y}) := by
    refine disjoint_left.mpr ?_
    rintro z (hz | rfl) (hz' | rfl)
    · exact disjoint_left.mp (Ω.disjoint_interval_swap x y) hz hz'
    · exact hz.1.2 (by simp)
    · exact hz'.1.2 (by simp)
    · exact hxy rfl
  refine ⟨fun z hz => hclosed.1 (hA hz), ?_, hd, ?_, ?_⟩
  · rintro z (hz | rfl)
    · exact hz.1.1
    · exact hy
  · convert hclosed.2.2.2.1 using 1
    ext z
    simp only [mem_union, mem_insert_iff, mem_singleton_iff]
    tauto
  · intro a₁ ha₁ a₂ ha₂ ha12 b₁ hb₁ b₂ hb₂ hb12 hc
    rcases hb₁ with hb₁ | rfl <;> rcases hb₂ with hb₂ | rfl
    · exact hclosed.2.2.2.2 _ (hA ha₁) _ (hA ha₂) ha12 _ hb₁ _ hb₂ hb12 hc
    · have hc' := (Ω.crosses_iff_interval).mp hc.symm
      rcases hc' with ⟨_, ha₂'⟩ | ⟨_, ha₁'⟩
      · exact disjoint_left.mp hd ha₂ (Or.inl (Ω.interval_subset_interval_left hb₁ ha₂'))
      · exact disjoint_left.mp hd ha₁ (Or.inl (Ω.interval_subset_interval_left hb₁ ha₁'))
    · have hc' := (Ω.crosses_iff_interval).mp hc.symm
      rcases hc' with ⟨ha₁', _⟩ | ⟨ha₂', _⟩
      · exact disjoint_left.mp hd ha₁ (Or.inl (Ω.interval_subset_interval_left hb₂ ha₁'))
      · exact disjoint_left.mp hd ha₂ (Or.inl (Ω.interval_subset_interval_left hb₂ ha₂'))
    · exact hb12 rfl

/-- The transaction bound of XV implies the vortex condition of XVI,
with the same bound. This supplies the change of wording in XVI (7.2). -/
theorem isRhoVortex_of_isPVortex {α : Type u} {β : Type v}
    {S : Society α β} {ρ : ℕ} (h : S.IsPVortex ρ) : IsRhoVortex S ρ := by
  classical
  intro u hu v hv huv
  rintro ⟨P, hdisj, hpaths⟩
  choose a ha b hb hP using hpaths
  have hfence := isFence_half_open_intervals S.Ω hu hv huv
  have hne : ∀ i, a i ≠ b i := fun i heq =>
    disjoint_left.mp hfence.2.2.1 (ha i) (heq ▸ hb i)
  have hΩ : ∀ i, S.IsOmegaPathWithEnds (P i) (a i) (b i) :=
    fun i => ⟨hP i, hne i, hfence.1 (ha i), hfence.2.1 (hb i)⟩
  have hinj : Injective P := by
    intro i j hij
    by_contra hneij
    exact disjoint_left.mp (hdisj hneij) (hP i).left_mem (hij ▸ (hP i).left_mem)
  have hTrans : S.IsTransaction (range P) := by
    refine ⟨_, _, ⟨?_, ?_⟩, hfence, ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨a i, b i, hΩ i⟩
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hneij
      exact hdisj (fun heq => hneij (congrArg P heq))
    · rintro _ ⟨i, rfl⟩
      exact ⟨a i, ha i, b i, hb i, hΩ i⟩
  have hcount := h hTrans
  rw [ncard_range_of_injective hinj] at hcount
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hcount
  exact Nat.not_succ_le_self ρ hcount

/-- The societies of a segregation from XV satisfy the vortex condition
used by XVI, without changing the two bounds. -/
theorem isSegregationOfType_of_gm15 {α : Type u} {β : Type v}
    {G : Graph α β} {ρ κ : ℕ} {𝒮 : Set (Society α β)}
    (h : GM15.IsSegregationOfType G ρ κ 𝒮) : IsSegregationOfType G ρ κ 𝒮 :=
  ⟨h.isSegregation, h.vortex_count_le,
    fun _ hA hlarge => isRhoVortex_of_isPVortex (h.is_p_vortex hA hlarge)⟩

end GraphMinor.GM16
