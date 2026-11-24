/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ThetaSchismatic
public import LeanPool.GraphMinor.GM12.Section3CircleSchismatic
import LeanPool.GraphMinor.GM12.Section3PuncturedCuffs
import LeanPool.GraphMinor.GM11.RadialChord

/-!
# A chord either gives a schism or stays planar in the same cap

In the extraction used by XII (3.1), page 245, fix a circle surrounding
a prescribed cuff and add a chord whose interior misses the circle.
The union has three branches. If a pair of branches is not near-planar,
that pair is schismatic. If all pairs are near-planar but the whole
union is not, the union is schismatic. In the remaining case, its cap
must be the original circle's cuff, by uniqueness of that cuff.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Adding one chord to a surrounding circle either supplies a
schismatic subset or gives a set planar after filling the same cuff. -/
theorem schismatic_or_planarInCappedCuff_of_chord
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {i : ι} {F L : Set (discComplement Δ)} {u v : discComplement Δ}
    (hF : IsOArc F) (hL : IsLineWithEnds L u v) (huv : u ≠ v)
    (hLF : L ∩ F = {u, v})
    (hsF : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ i))) :
    (∃ Y, Y ⊆ F ∪ L ∧ GM07.IsSchismatic Y) ∨
      GM07.IsPlanarInCappedCuff (Subtype.val ⁻¹' discBd (Δ i)) (F ∪ L) := by
  classical
  by_cases hnear : GM07.IsNearPlanar (F ∪ L)
  · right
    rcases hnear with hp | ⟨C, hC, hpC⟩
    · exact (hsF.2.2 (isPlanar_mono subset_union_left hp)).elim
    · have hC' := hC
      rw [discComplement_cuffs_eq hS Δ hΔ hdisj] at hC'
      obtain ⟨k, rfl⟩ := hC'
      have hsFk : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ k)) :=
        ⟨hC, isPlanarInCappedCuff_mono subset_union_left hpC, hsF.2.2⟩
      have hik := surrounding_cuff_index_unique hS Δ hΔ hdisj hcase hF hsF hsFk
      exact hik.symm ▸ hpC
  · left
    have huF : u ∈ F := (hLF.symm ▸ (show u ∈ ({u, v} : Set (discComplement Δ)) by simp)).2
    have hvF : v ∈ F := (hLF.symm ▸ (show v ∈ ({u, v} : Set (discComplement Δ)) by simp)).2
    obtain ⟨p, q, hpq, hp0, hp1, hpqF⟩ := hF.exists_arcs huF hvF huv
    have hP : IsLineWithEnds (range p) u v := by
      have h := isLine_range hpq.arc_left.1 hpq.arc_left.2
      rwa [hp0, hp1] at h
    have hQ : IsLineWithEnds (range q) u v := by
      have h := isLine_range hpq.arc_right.1 hpq.arc_right.2
      rwa [hpq.zero, hpq.one, hp0, hp1] at h
    have hPQ : range p ∩ range q = {u, v} := by
      simpa only [hp0, hp1] using hpq.inter
    have hPF : range p ⊆ F := hpqF ▸ subset_union_left
    have hQF : range q ⊆ F := hpqF ▸ subset_union_right
    have hcap : ∀ B, IsLineWithEnds B u v → B ⊆ F → L ∩ B = {u, v} := by
      intro B hB hBF
      apply Subset.antisymm
      · intro x hx
        exact hLF ▸ (show x ∈ L ∩ F from ⟨hx.1, hBF hx.2⟩)
      · rintro x (rfl | rfl)
        · exact ⟨hL.left_mem, hB.left_mem⟩
        · exact ⟨hL.right_mem, hB.right_mem⟩
    have hLP := hcap (range p) hP hPF
    have hLQ := hcap (range q) hQ hQF
    have hsubP : L ∪ range p ⊆ F ∪ L := union_subset subset_union_right
      (hPF.trans subset_union_left)
    have hsubQ : L ∪ range q ⊆ F ∪ L := union_subset subset_union_right
      (hQF.trans subset_union_left)
    by_cases hnLP : GM07.IsNearPlanar (L ∪ range p)
    · by_cases hnLQ : GM07.IsNearPlanar (L ∪ range q)
      · have hun : L ∪ range p ∪ range q = F ∪ L := by
          rw [union_assoc, hpqF, union_comm]
        refine ⟨F ∪ L, subset_rfl, ?_⟩
        rw [← hun]
        apply isSchismatic_x3_of_nearPlanar_pairs huv hL hP hQ hLP hLQ hPQ hnLP hnLQ
        · exact hpqF.symm ▸ (Or.inr ⟨_, hsF.1, hsF.2.1⟩)
        · exact hun.symm ▸ hnear
      · exact ⟨_, hsubQ, isSchismatic_oArc
          (isOArc_union_of_lines_inter_eq_ends hL hQ hLQ) hnLQ⟩
    · exact ⟨_, hsubP, isSchismatic_oArc
        (isOArc_union_of_lines_inter_eq_ends hL hP hLP) hnLP⟩

end GraphMinor.GM12
