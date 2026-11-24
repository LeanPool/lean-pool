/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4EndPartition
import Mathlib.Tactic.FinCases

/-!
# Endpoint classes and the four marks at each crossing

In XII (4.5), page 253, the edge-pair bijection identifies all
source edge ends with the four marks at each crossing. The
opposite-pair equations prove that these ends cover exactly
the union of the marked quadruples. Two noncrossing incident
edges at a vertex belong to different crossings, so that
vertex's endpoint class meets two distinct crossing discs.
-/

public section

namespace GraphMinor.GM12

open Set

/-- The opposite-pair equations and the edge-pair bijection
identify the full end set with all four crossing marks. This
is the endpoint cover in XII (4.5), claim (1), page 253. -/
theorem range_ends_eq_crossing_marks {S T E : Type*} (σ : T × Bool ≃ E)
    (ends : E × Bool → S) (m : T → Fin 4 → S)
    (h0 : ∀ i, ({ends (σ (i, false), false), ends (σ (i, false), true)} : Set S) = {m i 0, m i 2})
    (h1 : ∀ i, ({ends (σ (i, true), false), ends (σ (i, true), true)} : Set S) = {m i 1, m i 3}) :
    range ends = ⋃ i, range (m i) := by
  apply Subset.antisymm
  · rintro z ⟨⟨e, b⟩, rfl⟩
    obtain ⟨⟨i, c⟩, rfl⟩ := σ.surjective e
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hpair : ends (σ (i, c), b) ∈
        ({ends (σ (i, c), false), ends (σ (i, c), true)} : Set S) := by cases b <;> simp
    cases c
    · rw [h0 i] at hpair
      rcases hpair with heq | heq
      · exact ⟨0, heq.symm⟩
      · exact ⟨2, (mem_singleton_iff.mp heq).symm⟩
    · rw [h1 i] at hpair
      rcases hpair with heq | heq
      · exact ⟨1, heq.symm⟩
      · exact ⟨3, (mem_singleton_iff.mp heq).symm⟩
  · intro z hz
    obtain ⟨i, j, rfl⟩ := mem_iUnion.mp hz
    have hp0 : ({m i 0, m i 2} : Set S) ⊆ range ends := by
      rw [← h0 i]
      rintro z (rfl | rfl) <;> exact mem_range_self _
    have hp1 : ({m i 1, m i 3} : Set S) ⊆ range ends := by
      rw [← h1 i]
      rintro z (rfl | rfl) <;> exact mem_range_self _
    fin_cases j
    · exact hp0 (Or.inl rfl)
    · exact hp1 (Or.inl rfl)
    · exact hp0 (Or.inr rfl)
    · exact hp1 (Or.inr rfl)

/-- Noncrossing incident edges give contacts at different
crossings. This is the two-region witness for each branch in
XII (4.5)'s final small-side bound, page 253. -/
theorem two_crossing_classes_of_noncrossing_pairs {S V E T : Type*}
    (v : V → S) (P : E → Set S) (κ : E × Bool → V) (x : T → S)
    (σ : T × Bool ≃ E) (hxV : ∀ i, x i ∉ range v)
    (hpair : ∀ i, x i ∈ P (σ (i, false)) ∩ P (σ (i, true)))
    (hPV : ∀ e w, v w ∈ P e → w = κ (e, false) ∨ w = κ (e, true))
    (htwo : ∀ w, ∃ e f, P e ∩ P f = {v w}) :
    ∀ w, ∃ i j, i ≠ j ∧ ∃ b c d e : Bool,
      κ (σ (i, b), c) = w ∧ κ (σ (j, d), e) = w := by
  intro w
  obtain ⟨e, f, hef⟩ := htwo w
  obtain ⟨⟨i, b⟩, hei⟩ := σ.surjective e
  obtain ⟨⟨j, d⟩, hfj⟩ := σ.surjective f
  have hxi : x i ∈ P e := by
    rw [← hei]
    cases b
    · exact (hpair i).1
    · exact (hpair i).2
  have hxj : x j ∈ P f := by
    rw [← hfj]
    cases d
    · exact (hpair j).1
    · exact (hpair j).2
  have hij : i ≠ j := by
    intro h
    have hxboth : x i ∈ P e ∩ P f := ⟨hxi, h.symm ▸ hxj⟩
    have hxw : x i = v w := mem_singleton_iff.mp (hef.subset hxboth)
    exact hxV i ⟨w, hxw.symm⟩
  have hw : v w ∈ P e ∩ P f := hef.symm.subset (mem_singleton _)
  obtain ⟨c, hc⟩ : ∃ c : Bool, κ (e, c) = w := by
    rcases hPV e w hw.1 with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩
  obtain ⟨a, ha⟩ : ∃ a : Bool, κ (f, a) = w := by
    rcases hPV f w hw.2 with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩
  exact ⟨i, j, hij, b, c, d, a, hei ▸ hc, hfj ▸ ha⟩

end GraphMinor.GM12
