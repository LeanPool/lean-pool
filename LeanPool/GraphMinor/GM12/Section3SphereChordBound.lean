/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SphereSideDisc
public import LeanPool.GraphMinor.GM12.Section3SphereSeparatorCount
import LeanPool.GraphMinor.GM11.Section6

/-!
# The normal-chord bound for the one-disc sphere case

For XII (3.2), pages 247--248, a chord outside the prescribed disc
and the two boundary arcs form a theta graph. Choose the side disc
opposite each boundary arc. These two discs, together with the
prescribed disc, cover the sphere. Since the drawing meets the
prescribed disc only at its boundary, the two new discs already
cover the drawing. The unselected-side count gives the chord bound
needed for VI (3.6).
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The complete normal-line inequality in the last case of XII
(3.2), pages 247--248, with the two boundary arcs displayed. -/
theorem normal_chord_vertex_count_ge_min
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hs : IsSphere S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T) {Δ A B P : Set S} {a b : S}
    (hΔ : IsClosedDisc Δ) (hbΔ : discBd Δ = A ∪ B)
    (havoid : Γ.U ∩ Δ = Γ.V ∩ discBd Δ)
    (hfree : GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd Δ))
    (hA : IsLineWithEnds A a b) (hB : IsLineWithEnds B a b) (hP : IsLineWithEnds P a b)
    (hAB : A ∩ B = {a, b}) (hAP : A ∩ P = {a, b}) (hBP : B ∩ P = {a, b})
    (hPΔ : P ∩ Δ = {a, b}) (hnP : Γ.IsNormal P) :
    min (Γ.V ∩ A).ncard (Γ.V ∩ B).ncard ≤ (Γ.V ∩ P).ncard := by
  obtain ⟨D, hD, hbD, _, hnA, houtD⟩ := exists_sphere_theta_side_disc hS hs hA hB hP hAB hAP hBP
  obtain ⟨E, hE, hbE, _, hnB, houtE⟩ := exists_sphere_theta_side_disc hS hs hB hA hP
    ((inter_comm B A).trans hAB) hBP hAP
  have hnPΔ : ¬ P ⊆ Δ := by
    intro hsub
    obtain ⟨x, hxP, hxne⟩ := line_sdiff_ends_nonempty hP
    exact hxne (hPΔ.subset ⟨hxP, hsub hxP⟩)
  have hcov := GM11.theta_cover hS hP hA hB
    ((inter_comm P A).trans hAP) hAB hBP hΔ hD hE
    ((IsClosedDisc.frontier_eq_discBd hS hΔ).trans hbΔ)
    ((IsClosedDisc.frontier_eq_discBd hS hD).trans hbD)
    ((IsClosedDisc.frontier_eq_discBd hS hE).trans (hbE.trans (union_comm A P))) hnPΔ hnA hnB
  have hΓcov : Γ.U ⊆ D ∪ E := by
    intro x hx
    have hxcover : x ∈ Δ ∪ D ∪ E := hcov.symm.subset (mem_univ x)
    rcases hxcover with (hxΔ | hxD) | hxE
    · have hxBd := (havoid.subset ⟨hx, hxΔ⟩).2
      rw [hbΔ] at hxBd
      rcases hxBd with hxA | hxB
      · exact Or.inr (Surface.discBd_subset E (hbE.symm.subset (Or.inl hxA)))
      · exact Or.inl (Surface.discBd_subset D (hbD.symm.subset (Or.inl hxB)))
    · exact Or.inl hxD
    · exact Or.inr hxE
  have hn : Γ.IsNormal (A ∪ B ∪ P) := by
    intro x hx
    rcases hx.1 with hxAB | hxP
    · have hxBd : x ∈ discBd Δ := hbΔ.symm.subset hxAB
      exact (havoid.subset ⟨hx.2, Surface.discBd_subset Δ hxBd⟩).1
    · exact hnP ⟨hxP, hx.2⟩
  apply sphere_separator_vertex_count_ge_min hS hT (hbΔ ▸ hfree) hAB hAP hBP hn hD hE
    hbD hbE hΓcov (fun _ hx => houtD hx.2)
  intro x hx
  exact houtE (hx.2.elim Or.inr Or.inl)

end GraphMinor.GM12
