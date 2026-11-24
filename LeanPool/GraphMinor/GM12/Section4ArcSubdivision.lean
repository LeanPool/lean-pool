/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4ArcSubintervals
public import LeanPool.GraphMinor.GM12.Section4SubdivisionCover

/-!
# Subdividing an arc into pieces with one marked meeting each

For XII (4.5), page 252, use the midpoint cuts between the ordered
meeting parameters. The cut images give the subdivision vertices,
and the intervening arc portions give the new edges. Each portion
is a simple arc containing exactly its assigned meeting.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- A subdivision vertex at a midpoint cut, in XII (4.5), page 252. -/
@[expose] noncomputable def arcSubdivisionVertex {S : Type u}
    {k : ℕ} (g : unitInterval → S) (t : Fin k → unitInterval) (i : Fin (k + 1)) : S :=
  extI g (subdivisionCut (fun j => (t j : ℝ)) i)

/-- An arc portion between consecutive midpoint cuts, in the
subdivision of XII (4.5), page 252. -/
@[expose] noncomputable def arcSubdivisionPiece {S : Type u}
    {k : ℕ} (g : unitInterval → S) (t : Fin k → unitInterval) (i : Fin k) : Set S :=
  range (pieceA g (subdivisionCut (fun j => (t j : ℝ)) i.castSucc)
    (subdivisionCut (fun j => (t j : ℝ)) i.succ))

/-- Each new edge is a simple arc with its two cut images as ends. -/
theorem arcSubdivisionPiece_isLine {S : Type u} [TopologicalSpace S] [T2Space S]
    {k : ℕ} (hk : 0 < k) {g : unitInterval → S} (hg : IsArcMap g)
    (t : Fin k → unitInterval) (ht : StrictMono t)
    (ht01 : ∀ i, 0 < (t i : ℝ) ∧ (t i : ℝ) < 1) (i : Fin k) :
    IsLineWithEnds (arcSubdivisionPiece g t i)
      (arcSubdivisionVertex g t i.castSucc) (arcSubdivisionVertex g t i.succ) := by
  exact isLineWithEnds_pieceA hg
    (subdivisionCut_mem_Icc hk (fun j => (t j : ℝ)) ht ht01 i.castSucc).1
    ((subdivisionCut_strictMono (fun j => (t j : ℝ)) ht ht01) Fin.castSucc_lt_succ)
    (subdivisionCut_mem_Icc hk (fun j => (t j : ℝ)) ht ht01 i.succ).2

/-- A marked meeting lies on exactly its assigned subdivision
piece, as required by XII (4.5), page 252. -/
theorem marked_mem_arcSubdivisionPiece_iff {S : Type u}
    {k : ℕ} (hk : 0 < k) {g : unitInterval → S} (hg : Function.Injective g)
    (t : Fin k → unitInterval) (ht : StrictMono t)
    (ht01 : ∀ i, 0 < (t i : ℝ) ∧ (t i : ℝ) < 1) (i j : Fin k) :
    g (t j) ∈ arcSubdivisionPiece g t i ↔ j = i := by
  rw [arcSubdivisionPiece, mem_range_pieceA_iff hg
    (subdivisionCut_mem_Icc hk (fun j => (t j : ℝ)) ht ht01 i.castSucc).1
    ((subdivisionCut_strictMono (fun j => (t j : ℝ)) ht ht01) Fin.castSucc_lt_succ).le
    (subdivisionCut_mem_Icc hk (fun j => (t j : ℝ)) ht ht01 i.succ).2]
  exact crossing_mem_subdivisionInterval_iff (fun j => (t j : ℝ)) ht ht01 j i

/-- Each subdivision piece meets the marked set in exactly one
point. This is the geometric one-meeting-per-edge assertion in
XII (4.5), page 252. -/
theorem arcSubdivisionPiece_inter_marked {S : Type u}
    {k : ℕ} (hk : 0 < k) {g : unitInterval → S} (hg : Function.Injective g)
    (t : Fin k → unitInterval) (ht : StrictMono t)
    (ht01 : ∀ i, 0 < (t i : ℝ) ∧ (t i : ℝ) < 1) (i : Fin k) :
    arcSubdivisionPiece g t i ∩ range (fun j => g (t j)) = {g (t i)} := by
  ext x
  constructor
  · rintro ⟨hx, j, rfl⟩
    have hji := (marked_mem_arcSubdivisionPiece_iff hk hg t ht ht01 i j).mp hx
    subst j
    rfl
  · rintro rfl
    exact ⟨(marked_mem_arcSubdivisionPiece_iff hk hg t ht ht01 i i).mpr rfl, ⟨i, rfl⟩⟩

/-- Distinct cuts give distinct subdivision vertices. -/
theorem arcSubdivisionVertex_injective {S : Type u}
    {k : ℕ} (hk : 0 < k) {g : unitInterval → S} (hg : Function.Injective g)
    (t : Fin k → unitInterval) (ht : StrictMono t)
    (ht01 : ∀ i, 0 < (t i : ℝ) ∧ (t i : ℝ) < 1) :
    Function.Injective (arcSubdivisionVertex g t) := by
  intro i j hij
  apply (subdivisionCut_strictMono (fun j => (t j : ℝ)) ht ht01).injective
  exact extI_injOn hg (subdivisionCut_mem_Icc hk (fun j => (t j : ℝ)) ht ht01 i)
    (subdivisionCut_mem_Icc hk (fun j => (t j : ℝ)) ht ht01 j) hij

/-- No subdivision vertex is one of the marked meetings. -/
theorem arcSubdivisionVertex_not_mem_marked {S : Type u}
    {k : ℕ} (hk : 0 < k) {g : unitInterval → S} (hg : Function.Injective g)
    (t : Fin k → unitInterval) (ht : StrictMono t)
    (ht01 : ∀ i, 0 < (t i : ℝ) ∧ (t i : ℝ) < 1) (i : Fin (k + 1)) :
    arcSubdivisionVertex g t i ∉ range (fun j => g (t j)) := by
  rintro ⟨j, hj⟩
  have heq : subdivisionCut (fun j => (t j : ℝ)) i = (t j : ℝ) :=
    extI_injOn hg (subdivisionCut_mem_Icc hk (fun j => (t j : ℝ)) ht ht01 i)
      (t j).property (hj.symm.trans (extI_coe g (t j)).symm)
  exact subdivisionCut_ne_crossing (fun j => (t j : ℝ)) ht ht01 i j heq

/-- The first subdivision vertex is the original first endpoint. -/
theorem arcSubdivisionVertex_zero {S : Type u}
    {k : ℕ} (g : unitInterval → S) (t : Fin k → unitInterval) :
    arcSubdivisionVertex g t 0 = g 0 := by
  rw [arcSubdivisionVertex, subdivisionCut_zero]
  exact extI_coe g 0

/-- The last subdivision vertex is the original last endpoint. -/
theorem arcSubdivisionVertex_last {S : Type u}
    {k : ℕ} (hk : 0 < k) (g : unitInterval → S) (t : Fin k → unitInterval) :
    arcSubdivisionVertex g t (Fin.last k) = g 1 := by
  rw [arcSubdivisionVertex, subdivisionCut_last hk]
  exact extI_coe g 1

/-- The subdivision pieces cover the whole original arc. -/
theorem iUnion_arcSubdivisionPieces {S : Type u}
    {k : ℕ} (hk : 0 < k) {g : unitInterval → S} (hg : Function.Injective g)
    (t : Fin k → unitInterval) (ht : StrictMono t)
    (ht01 : ∀ i, 0 < (t i : ℝ) ∧ (t i : ℝ) < 1) :
    (⋃ i, arcSubdivisionPiece g t i) = range g := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact range_pieceA_subset_range g _ _ hi
  · rintro x ⟨u, rfl⟩
    obtain ⟨i, hi⟩ := exists_subdivisionInterval_of_mem_Icc hk (fun j =>
      (t j : ℝ)) ht ht01 u.property
    refine mem_iUnion.mpr ⟨i, ?_⟩
    exact (mem_range_pieceA_iff hg
      (subdivisionCut_mem_Icc hk (fun j => (t j : ℝ)) ht ht01 i.castSucc).1
      ((subdivisionCut_strictMono (fun j => (t j : ℝ)) ht ht01) Fin.castSucc_lt_succ).le
      (subdivisionCut_mem_Icc hk (fun j => (t j : ℝ)) ht ht01 i.succ).2 u).mpr hi

/-- Two different subdivision pieces can meet only at a cut
vertex. This gives the edge-incidence condition for the subdivision
in XII (4.5), page 252. -/
theorem arcSubdivisionPieces_inter_subset_vertices {S : Type u}
    {k : ℕ} (hk : 0 < k) {g : unitInterval → S} (hg : Function.Injective g)
    (t : Fin k → unitInterval) (ht : StrictMono t)
    (ht01 : ∀ i, 0 < (t i : ℝ) ∧ (t i : ℝ) < 1)
    {i j : Fin k} (hij : i ≠ j) :
    arcSubdivisionPiece g t i ∩ arcSubdivisionPiece g t j ⊆ range (arcSubdivisionVertex g t) := by
  intro x hx
  obtain ⟨u, rfl⟩ := range_pieceA_subset_range g _ _ hx.1
  have hmem : ∀ l, g u ∈ arcSubdivisionPiece g t l →
      (u : ℝ) ∈ Icc (subdivisionCut (fun j => (t j : ℝ)) l.castSucc)
        (subdivisionCut (fun j => (t j : ℝ)) l.succ) := by
    intro l hl
    exact (mem_range_pieceA_iff hg
      (subdivisionCut_mem_Icc hk (fun j => (t j : ℝ)) ht ht01 l.castSucc).1
      ((subdivisionCut_strictMono (fun j => (t j : ℝ)) ht ht01) Fin.castSucc_lt_succ).le
      (subdivisionCut_mem_Icc hk (fun j => (t j : ℝ)) ht ht01 l.succ).2 u).mp hl
  have hmi := hmem i hx.1
  have hmj := hmem j hx.2
  have hmono := (subdivisionCut_strictMono (fun j => (t j : ℝ)) ht ht01).monotone
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hsep := hmono (show i.succ ≤ j.castSucc by change i.val + 1 ≤ j.val; omega)
    have hueq := le_antisymm hmi.2 (hsep.trans hmj.1)
    refine ⟨i.succ, ?_⟩
    change extI g (subdivisionCut (fun j => (t j : ℝ)) i.succ) = g u
    rw [← hueq]
    exact extI_coe g u
  · have hsep := hmono (show j.succ ≤ i.castSucc by change j.val + 1 ≤ i.val; omega)
    have hueq := le_antisymm hmj.2 (hsep.trans hmi.1)
    refine ⟨j.succ, ?_⟩
    change extI g (subdivisionCut (fun j => (t j : ℝ)) j.succ) = g u
    rw [← hueq]
    exact extI_coe g u

/-- A subdivision piece contains exactly its two endpoint cuts
from the full cut set. This gives the exact vertex incidence in
XII (4.5)'s subdivision, page 252. -/
theorem cut_mem_arcSubdivisionPiece_iff {S : Type u}
    {k : ℕ} (hk : 0 < k) {g : unitInterval → S} (hg : Function.Injective g)
    (t : Fin k → unitInterval) (ht : StrictMono t)
    (ht01 : ∀ i, 0 < (t i : ℝ) ∧ (t i : ℝ) < 1)
    (i : Fin k) (j : Fin (k + 1)) :
    arcSubdivisionVertex g t j ∈ arcSubdivisionPiece g t i ↔ j = i.castSucc ∨ j = i.succ := by
  have hcuts := subdivisionCut_strictMono (fun j => (t j : ℝ)) ht ht01
  have hbound := subdivisionCut_mem_Icc hk (fun j => (t j : ℝ)) ht ht01
  rw [arcSubdivisionVertex, extI_of_mem g (hbound j), arcSubdivisionPiece,
    mem_range_pieceA_iff hg (hbound i.castSucc).1
      (hcuts Fin.castSucc_lt_succ).le (hbound i.succ).2]
  constructor
  · intro hmem
    have hlo : i.castSucc ≤ j := le_of_not_gt fun h => (not_le_of_gt (hcuts h)) hmem.1
    have hhi : j ≤ i.succ := le_of_not_gt fun h => (not_le_of_gt (hcuts h)) hmem.2
    have hcases : j.val = i.val ∨ j.val = i.val + 1 := by
      change i.val ≤ j.val at hlo
      change j.val ≤ i.val + 1 at hhi
      omega
    exact hcases.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
  · rintro (rfl | rfl)
    · exact ⟨le_rfl, (hcuts Fin.castSucc_lt_succ).le⟩
    · exact ⟨(hcuts Fin.castSucc_lt_succ).le, le_rfl⟩

/-- The marked vertex set of each new edge is exactly its two
consecutive cuts. -/
theorem arcSubdivisionPiece_inter_vertices {S : Type u}
    {k : ℕ} (hk : 0 < k) {g : unitInterval → S} (hg : Function.Injective g)
    (t : Fin k → unitInterval) (ht : StrictMono t)
    (ht01 : ∀ i, 0 < (t i : ℝ) ∧ (t i : ℝ) < 1) (i : Fin k) :
    arcSubdivisionPiece g t i ∩ range (arcSubdivisionVertex g t) =
      {arcSubdivisionVertex g t i.castSucc, arcSubdivisionVertex g t i.succ} := by
  ext x
  constructor
  · rintro ⟨hx, j, rfl⟩
    rcases (cut_mem_arcSubdivisionPiece_iff hk hg t ht ht01 i j).mp hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨(cut_mem_arcSubdivisionPiece_iff hk hg t ht ht01 i i.castSucc).mpr (Or.inl rfl),
        ⟨i.castSucc, rfl⟩⟩
    · exact ⟨(cut_mem_arcSubdivisionPiece_iff hk hg t ht ht01 i i.succ).mpr (Or.inr rfl),
        ⟨i.succ, rfl⟩⟩

end GraphMinor.GM12
