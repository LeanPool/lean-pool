/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.FreeLift
public import LeanPool.GraphMinor.GM11.PaintingCells
public import LeanPool.GraphMinor.Surface.RemoveDiscs

/-!
# A painting from closed discs

A finite family of closed discs that meet only in a finite set `N` of points on their boundaries is
a painting (`exists_painting_of_discs`). Its cells
are the discs minus `N`. This is the form in which the painting of XVII (13.1) is built.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {T : Type} [TopologicalSpace T] [T2Space T] {ι : Type*} [Finite ι]

/-- **A painting from closed discs.** -/
theorem exists_painting_of_discs {D : ι → Set T} {N : Set T} (hD : ∀ i, IsClosedDisc (D i))
  (hN : N.Finite) (hNb : ∀ i, N ∩ D i ⊆ discBd (D i))
    (hdis : ∀ i j, i ≠ j → D i ∩ D j ⊆ N) (hNU : N ⊆ ⋃ i, D i) (h3 : ∀ i, (N ∩ D i).ncard ≤ 3)
      (hbd : bd T ⊆ ⋃ i, D i)
    (hb : ∀ i, ((D i \ N) ∩ bd T).Nonempty → (N ∩ D i).ncard = 2 ∧ IsLine (D i ∩ bd T) ∧ lineEnds
      (D i ∩ bd T) = N ∩ D i) :
    ∃ Γ : Painting T, Γ.U = (⋃ i, D i) ∧ Γ.N = N ∧ Γ.C = range (fun i => D i \ N) ∧
      ∀ i, closure (D i \ N) = D i ∧ tilde (D i \ N) = N ∩ D i := by
  have hcl : ∀ i, closure (D i \ N) = D i := fun i => (disc_diff_finite (hD i) (hNb i)).1
  have htl : ∀ i, tilde (D i \ N) = N ∩ D i := fun i => by
    rw [tilde, hcl]
    ext x
    simp only [mem_sdiff, mem_inter_iff, not_and, not_not]
    exact ⟨fun h => ⟨h.2 h.1, h.1⟩, fun h => ⟨h.2, fun _ => h.1⟩⟩
  have hne : ∀ i, (D i \ N).Nonempty := fun i => by
    by_contra hn
    rw [not_nonempty_iff_eq_empty] at hn
    have h1 := hcl i
    rw [hn, closure_empty] at h1
    obtain ⟨x, hx⟩ := (IsOArc.isConnected' (hD i).isOArc_discBd).nonempty
    have := discBd_subset _ hx
    rw [← h1] at this
    exact this
  have hdc : ∀ i, IsClosed (D i) := fun i => (hD i).isClosed
  have hC : arcComponentsIn ((⋃ i, D i) \ N) = range (fun i => D i \ N) := by
    refine arcComponentsIn_eq_of_finite_cover (Set.finite_range _) ?_ ?_ ?_ ?_ ?_
    · ext x
      simp
    · rintro _ ⟨i, rfl⟩
      exact hne i
    · rintro _ ⟨i, rfl⟩
      exact GM11.isPathConnected_disc_sdiff (hD i) (hNb i)
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
      have hij' : i ≠ j := fun h => hij (h ▸ rfl)
      exact Set.disjoint_left.mpr fun x hx hx' => hx.2 (hdis i j hij' ⟨hx.1, hx'.1⟩)
    · rintro _ ⟨i, rfl⟩
      rw [show closure (D i \ N) = D i from hcl i]
      ext x
      constructor
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, mem_iUnion.2 ⟨i, h1⟩, h2⟩
  refine ⟨{ U := ⋃ i, D i, N := N, isClosed_U := isClosed_iUnion_of_finite hdc, N_subset
    := hNU, finite_N := hN, finite_cells := ?_, cell_disc := ?_, bd_subset := hbd, border_cell
      := ?_ }, rfl, rfl, hC, fun i => ⟨hcl i, htl i⟩⟩
  · rw [hC]
    exact Set.finite_range _
  · rw [hC]
    rintro _ ⟨i, rfl⟩
    rw [hcl]
    refine ⟨hD i, ?_, ?_, ?_⟩
    · rw [htl]
      exact hNb i
    · rw [htl]
      exact hN.subset inter_subset_left
    · rw [htl]
      exact h3 i
  · rw [hC]
    rintro _ ⟨i, rfl⟩ h
    obtain ⟨h1, h2, h4⟩ := hb i h
    rw [hcl, htl]
    exact ⟨h1, hN.subset inter_subset_left, h2, h4⟩

end GraphMinor.GM17
