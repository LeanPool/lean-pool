/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CircleLoops
import Mathlib.Tactic.FinCases

/-!
# A short curve through two circles joined by a line

The construction for XII (3.1)(ii), used on page 246 in (3.2),
traverses the first circle, the joining line, the second circle,
and the joining line backwards. Each image point is visited at
most twice. At the first joining point the first circle receives
the second visit label, since the forward joining line starts there.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM07

/-- The short normal curve used for condition (3.1)(ii) in the
proof of XII (3.2), page 246. -/
theorem exists_short_curve_covering_joined_circles
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {A B P : Set S} {u v : S}
    (hA : IsOArc A) (hB : IsOArc B) (hP : IsLineWithEnds P u v)
    (hAB : Disjoint A B) (hu : u ∈ A) (hv : v ∈ B)
    (hPA : P ∩ A = {u}) (hPB : P ∩ B = {v})
    (hn : Γ.IsNormal (A ∪ B ∪ P)) :
    ∃ φ : C(Circle, S), IsNormalCurve Γ φ ∧ range φ = A ∪ B ∪ P ∧
      curveLength Γ φ ≤ 2 * (Γ.V ∩ (A ∪ B ∪ P)).ncard := by
  classical
  obtain ⟨α, hα0, hα1, hαr, hαi⟩ := exists_circle_loop_based_at hA hu
  obtain ⟨β, hβ0, hβ1, hβr, hβi⟩ := exists_circle_loop_based_at hB hv
  obtain ⟨H, hH0, hH1⟩ := hP
  let q : C(unitInterval, S) := ⟨fun t => (H t).val, by fun_prop⟩
  let q' : C(unitInterval, S) := ⟨fun t => q (unitInterval.symm t), by fun_prop⟩
  have hq0 : q 0 = u := hH0
  have hq1 : q 1 = v := hH1
  have hqi : Function.Injective q := fun s t h => H.injective (Subtype.ext h)
  have hqr : range q = P := by
    ext x
    exact ⟨fun ⟨t, ht⟩ => ht ▸ (H t).property,
      fun hx => ⟨H.symm ⟨x, hx⟩, congrArg Subtype.val (H.apply_symm_apply _)⟩⟩
  have haq : ∀ s t : unitInterval, s.val < 1 → α s = q t → s = 0 ∧ t = 0 := by
    intro s t hs heq
    have hp : q t = u := hPA.subset ⟨hqr.subset (mem_range_self t),
      heq ▸ hαr.subset (mem_range_self s)⟩
    exact ⟨hαi ⟨s.property.1, hs⟩ (by simp) (heq.trans (hp.trans hα0.symm)),
      hqi (hp.trans hq0.symm)⟩
  have hbq : ∀ s t : unitInterval, s.val < 1 → β s = q t → s = 0 ∧ t = 1 := by
    intro s t hs heq
    have hp : q t = v := hPB.subset ⟨hqr.subset (mem_range_self t),
      heq ▸ hβr.subset (mem_range_self s)⟩
    exact ⟨hβi ⟨s.property.1, hs⟩ (by simp) (heq.trans (hp.trans hβ0.symm)),
      hqi (hp.trans hq1.symm)⟩
  have hab : ∀ s t : unitInterval, α s ≠ β t := by
    intro s t heq
    exact Set.disjoint_left.mp hAB (hαr.subset (mem_range_self s))
      (heq.symm ▸ hβr.subset (mem_range_self t))
  let γ : Fin 4 → C(unitInterval, S) := ![α, q, β, q']
  let L : Fin 4 → unitInterval → Fin 2 := fun i t =>
    if i = 0 then (if t = 0 then 1 else 0) else if i = 3 then 1 else 0
  have hmatch : ∀ i, γ i 1 = γ (finNext (by decide : 0 < 4) i) 0 := by
    intro i
    fin_cases i <;> simp [γ, q', finNext, hα0, hα1, hβ0, hβ1, hq0, hq1]
  have hsep : ∀ (i j : Fin 4) (s t : unitInterval), s.val < 1 → t.val < 1 →
      γ i s = γ j t → L i s = L j t → i = j ∧ s = t := by
    intro i j s t hs ht heq hl
    have hs1 : s ≠ 1 := fun h => by subst s; exact (lt_irrefl (1 : ℝ)) hs
    have ht1 : t ≠ 1 := fun h => by subst t; exact (lt_irrefl (1 : ℝ)) ht
    fin_cases i <;> fin_cases j
    · exact ⟨rfl, hαi ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ heq⟩
    · obtain ⟨rfl, rfl⟩ := haq s t hs heq
      simp [L] at hl
    · exact False.elim (hab s t heq)
    · have h := (haq s (unitInterval.symm t) hs heq).2
      have ht0 := congrArg unitInterval.symm h
      simp only [unitInterval.symm_symm, unitInterval.symm_zero] at ht0
      exact False.elim (ht1 ht0)
    · obtain ⟨rfl, rfl⟩ := haq t s ht heq.symm
      simp [L] at hl
    · exact ⟨rfl, hqi heq⟩
    · exact False.elim (hs1 (hbq t s ht heq.symm).2)
    · simp [L] at hl
    · exact False.elim (hab t s heq.symm)
    · exact False.elim (ht1 (hbq s t hs heq).2)
    · exact ⟨rfl, hβi ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ heq⟩
    · simp [L] at hl
    · have h := (haq t (unitInterval.symm s) ht heq.symm).2
      have hs0 := congrArg unitInterval.symm h
      simp only [unitInterval.symm_symm, unitInterval.symm_zero] at hs0
      exact False.elim (hs1 hs0)
    · simp [L] at hl
    · simp [L] at hl
    · refine ⟨rfl, ?_⟩
      have h := congrArg unitInterval.symm (hqi heq)
      simpa only [unitInterval.symm_symm] using h
  have hγX : ∀ i, range (γ i) ⊆ A ∪ B ∪ P := by
    intro i
    fin_cases i
    · exact hαr.subset.trans (subset_union_left.trans subset_union_left)
    · exact hqr.subset.trans subset_union_right
    · exact hβr.subset.trans (subset_union_right.trans subset_union_left)
    · intro x hx
      obtain ⟨t, rfl⟩ := hx
      exact Or.inr (hqr.subset (mem_range_self (unitInterval.symm t)))
  obtain ⟨hφ, hlen⟩ := concatLoop_length_le_of_piece_labels hn (by decide : 0 < 4) γ hmatch hγX L
    hsep
  have hrange : range (concatLoop (by decide : 0 < 4) γ hmatch) = A ∪ B ∪ P := by
    rw [range_concatLoop]
    apply Subset.antisymm (iUnion_subset hγX)
    rintro x ((hx | hx) | hx)
    · exact mem_iUnion.mpr ⟨0, hαr.symm.subset hx⟩
    · exact mem_iUnion.mpr ⟨2, hβr.symm.subset hx⟩
    · exact mem_iUnion.mpr ⟨1, hqr.symm.subset hx⟩
  exact ⟨_, hφ, hrange, by simpa only [inter_comm] using hlen⟩

end GraphMinor.GM12
