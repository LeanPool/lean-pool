/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4OneMeetingSubdivision
public import LeanPool.GraphMinor.GM12.Section4CrossingCount
public import Mathlib.Data.Fintype.Sigma

/-!
# Subdividing the full source edge family

For XII (4.5), pages 252--253, take on each original edge its
finite nonempty set of meetings away from vertices. Apply the
one-meeting subdivision to each edge. The sum of the new edge
counts is twice the meeting count, because each meeting lies on
exactly two original edges.
-/

public section

namespace GraphMinor.GM12

open Set Surface
open scoped BigOperators

/-- Subdivide every source edge into simple pieces with one
meeting each, retaining all local cut incidences and the exact
edge count. This is the full family subdivision step in XII (4.5),
pages 252--253, before identifying shared original endpoints. -/
theorem exists_family_one_meeting_subdivision {m n : ℕ}
    (V : Fin m → ℂ) (κ : Fin n × Bool → Fin m) (E : Fin n → Set ℂ)
    (hline : ∀ e, IsLineWithEnds (E e) (V (κ (e, false))) (V (κ (e, true))))
    (hfinite : ∀ i j, i ≠ j → (E i ∩ E j).Finite)
    (htriple : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → E i ∩ E j ∩ E k ⊆ range V)
    (hcross : ∀ i, ∃ j, j ≠ i ∧ ∃ x : ℂ, x ∈ E i ∩ E j ∧ x ∉ range V) :
    ∃ k : Fin n → ℕ, (∀ e, 0 < k e) ∧
    ∃ (w : ∀ e, Fin (k e + 1) → ℂ) (P : ∀ e, Fin (k e) → Set ℂ),
      (∀ e, Function.Injective (w e)) ∧
      (∀ e, w e 0 = V (κ (e, false))) ∧
      (∀ e, w e (Fin.last (k e)) = V (κ (e, true))) ∧
      (∀ e i, IsLineWithEnds (P e i) (w e i.castSucc) (w e i.succ)) ∧
      (∀ e, (⋃ i, P e i) = E e) ∧
      (∀ e i, ∃ x ∈ E e ∩ edgeMeetingPoints V E, P e i ∩ (E e ∩ edgeMeetingPoints V E) = {x}) ∧
      (∀ e i, w e i ∉ E e ∩ edgeMeetingPoints V E) ∧
      (∀ e i j, i ≠ j → P e i ∩ P e j ⊆ range (w e)) ∧
      (∀ e i, P e i ∩ range (w e) = {w e i.castSucc, w e i.succ}) ∧
      (∀ e, (E e ∩ edgeMeetingPoints V E).ncard = k e) ∧
      Fintype.card (Σ e : Fin n, Fin (k e)) = 2 * (edgeMeetingPoints V E).ncard := by
  classical
  have hM := finite_edgeMeetingPoints V E hfinite
  have hnot : ∀ v, V v ∉ edgeMeetingPoints V E := by
    rintro v ⟨i, j, hij, hx, hxV⟩
    exact hxV ⟨v, rfl⟩
  have hper : ∀ e, ∃ k : ℕ, 0 < k ∧ ∃ (w : Fin (k + 1) → ℂ) (P : Fin k → Set ℂ),
      Function.Injective w ∧ w 0 = V (κ (e, false)) ∧ w (Fin.last k) = V (κ (e, true)) ∧
      (∀ i, IsLineWithEnds (P i) (w i.castSucc) (w i.succ)) ∧
      (⋃ i, P i) = E e ∧
      (∀ i, ∃ x ∈ E e ∩ edgeMeetingPoints V E, P i ∩ (E e ∩ edgeMeetingPoints V E) = {x}) ∧
      (∀ i, w i ∉ E e ∩ edgeMeetingPoints V E) ∧
      (∀ i j, i ≠ j → P i ∩ P j ⊆ range w) ∧
      (∀ i, P i ∩ range w = {w i.castSucc, w i.succ}) ∧
      (E e ∩ edgeMeetingPoints V E).ncard = k := by
    intro e
    have hne : (E e ∩ edgeMeetingPoints V E).Nonempty := by
      obtain ⟨j, hje, x, hx, hxV⟩ := hcross e
      exact ⟨x, hx.1, e, j, hje.symm, hx, hxV⟩
    exact exists_one_meeting_arc_subdivision (hline e) (Set.Finite.subset hM inter_subset_right) hne
      inter_subset_left (fun h => hnot _ h.2) (fun h => hnot _ h.2)
  choose k hk w P hwinj hw0 hwlast hPline hPcover hPmeeting hwavoid hPinter hPvertices hcount using
    hper
  refine ⟨k, hk, w, P, hwinj, hw0, hwlast, hPline, hPcover, hPmeeting, hwavoid,
    hPinter, hPvertices, hcount, ?_⟩
  calc
    Fintype.card (Σ e : Fin n, Fin (k e)) = ∑ e, k e := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
    _ = ∑ e, (E e ∩ edgeMeetingPoints V E).ncard :=
      Finset.sum_congr rfl fun e _ => (hcount e).symm
    _ = 2 * (edgeMeetingPoints V E).ncard := sum_edge_meeting_counts V E hfinite htriple

end GraphMinor.GM12
