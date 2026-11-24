/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.RegionTools

/-!
# Sides of cells

A side of a cell of a painting is a line of the boundary of the closure of the cell between two
consecutive nodes, off the boundary of the surface. Here we prove the plain
facts about sides: a point of the boundary of a cell off the nodes and off the boundary of the
surface lies on a side (`exists_side`), two sides with a common point off the
nodes are equal (`IsGap.unique`), and there are finitely many sides (`finite_gaps`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

namespace Painting

/-- A line of the boundary of a cell between two consecutive nodes. -/
def IsGap (Γ : Painting S) (c L : Set S) (u v : S) : Prop :=
  c ∈ Γ.C ∧ IsLineWithEnds L u v ∧ L ⊆ discBd (closure c) ∧ L ∩ Γ.N = {u, v}

/-- A side of a cell: a line of its boundary between two consecutive nodes that meets the boundary
of the surface at most in its ends. -/
def IsSide (Γ : Painting S) (c L : Set S) (u v : S) : Prop :=
  Γ.IsGap c L u v ∧ Disjoint (L \ {u, v}) (bd S)

variable {Γ : Painting S} [T2Space S]

omit [T2Space S] in
theorem IsGap.symm {c L : Set S} {u v : S} (h : Γ.IsGap c L u v) : Γ.IsGap c L v u :=
  ⟨h.1, h.2.1.symm, h.2.2.1, by rw [pair_comm]; exact h.2.2.2⟩

omit [T2Space S] in
theorem IsSide.symm {c L : Set S} {u v : S} (h : Γ.IsSide c L u v) : Γ.IsSide c L v u :=
  ⟨h.1.symm, by rw [pair_comm]; exact h.2⟩

omit [T2Space S] in
theorem IsGap.subset_closure {c L : Set S} {u v : S} (h : Γ.IsGap c L u v) : L ⊆ closure c :=
  h.2.2.1.trans (discBd_subset _)

omit [T2Space S] in
theorem IsGap.subset_U {c L : Set S} {u v : S} (h : Γ.IsGap c L u v) : L ⊆ Γ.U := by
  refine h.subset_closure.trans (closure_minimal (Γ.cell_subset_U h.1) Γ.isClosed_U)

omit [T2Space S] in
theorem IsGap.left_mem_N {c L : Set S} {u v : S} (h : Γ.IsGap c L u v) : u ∈ Γ.N :=
  (h.2.2.2.ge (mem_insert _ _)).2

omit [T2Space S] in
theorem IsGap.right_mem_N {c L : Set S} {u v : S} (h : Γ.IsGap c L u v) : v ∈ Γ.N :=
  (h.2.2.2.ge (mem_insert_of_mem _ rfl)).2

omit [T2Space S] in
theorem IsGap.not_mem_N {c L : Set S} {u v x : S} (h : Γ.IsGap c L u v) (hx : x ∈ L) (hu : x ≠ u)
  (hv : x ≠ v) : x ∉ Γ.N := fun hN => by
  rcases (h.2.2.2.le ⟨hx, hN⟩ : x ∈ ({u, v} : Set S)) with h1 | h1
  · exact hu h1
  · exact hv h1

omit [T2Space S] in
theorem IsGap.mem_cell {c L : Set S} {u v x : S} (h : Γ.IsGap c L u v) (hx : x ∈ L) (hu : x ≠ u)
  (hv : x ≠ v) : x ∈ c :=
  closure_eq_cell h.1 (h.subset_closure hx) (h.not_mem_N hx hu hv)

/-- A gap is determined by a point on it off the nodes. -/
theorem IsGap.subset_of_mem {c d L L' : Set S} {u v u' v' z : S} (h : Γ.IsGap c L u v)
  (h' : Γ.IsGap d L' u' v') (hz : z ∈ L) (hz' : z ∈ L') (hzN : z ∉ Γ.N) : L' ⊆ L := by
  obtain rfl : d = c := by
    by_contra hne
    exact hzN (closure_inter_closure h'.1 h.1 hne ⟨h'.subset_closure hz', h.subset_closure hz⟩)
  obtain ⟨B, hB, hun, hin⟩ := oarc_split (Γ.isClosedDisc_closure_cell h.1).isOArc_discBd h.2.1
    h.2.2.1
  have hne : ∀ {x}, x ∈ L' \ {u', v'} → x ∉ ({u, v} : Set S) := fun {x} hx hm => by
    have h1 : x ∈ Γ.N := by
      rcases hm with rfl | rfl
      · exact h.left_mem_N
      · exact h.right_mem_N
    exact h'.not_mem_N hx.1 (fun e => hx.2 (.inl e)) (fun e => hx.2 (.inr e)) h1
  have hcov : L' \ {u', v'} ⊆ L ∪ B := fun x hx => hun ▸ h'.2.2.1 hx.1
  have hzi : z ∈ L' \ {u', v'} := ⟨hz', by
    rintro (rfl | rfl)
    · exact hzN h'.left_mem_N
    · exact hzN h'.right_mem_N⟩
  have hsub : L' \ {u', v'} ⊆ L := by
    have hcl := isPreconnected_closed_iff.mp h'.2.1.isPreconnected_diff L B
      h.2.1.isCompact.isClosed hB.isCompact.isClosed hcov
    intro x hx
    by_contra hxL
    have hxB : x ∈ B := (hcov hx).resolve_left hxL
    obtain ⟨y, hy, hy1, hy2⟩ := hcl ⟨z, hzi, hz⟩ ⟨x, hx, hxB⟩
    exact hne hy (hin ▸ ⟨hy1, hy2⟩)
  exact h'.2.1.subset_closure_diff.trans (closure_minimal hsub h.2.1.isCompact.isClosed)

/-- Two gaps with a common point off the nodes are equal. -/
theorem IsGap.unique {c d L L' : Set S} {u v u' v' z : S} (h : Γ.IsGap c L u v)
  (h' : Γ.IsGap d L' u' v') (hz : z ∈ L) (hz' : z ∈ L') (hzN : z ∉ Γ.N) : c = d ∧ L = L' := by
  refine ⟨?_, subset_antisymm (h'.subset_of_mem h hz' hz hzN) (h.subset_of_mem h' hz hz' hzN)⟩
  by_contra hne
  exact hzN (closure_inter_closure h.1 h'.1 hne ⟨h.subset_closure hz, h'.subset_closure hz'⟩)

/-- The gaps of a cell with two nodes cover the boundary of the cell, and there are finitely many.
-/
theorem exists_gaps {c : Set S} {x y : S} (hc : c ∈ Γ.C) (hx : x ∈ tilde c) (hy : y ∈ tilde c)
  (hxy : x ≠ y) :
    ∃ 𝓕 : Set (Set S), 𝓕.Finite ∧ (∀ F ∈ 𝓕, ∃ u v, Γ.IsGap c F u v) ∧ ⋃₀ 𝓕 = discBd (closure c)
      := by
  obtain ⟨𝓕, hf, h, hu⟩ := exists_gaps_oarc (Γ.isClosedDisc_closure_cell hc).isOArc_discBd
    (Γ.finite_tilde_cell hc) (Γ.tilde_subset_discBd hc) hx hy hxy
  refine ⟨𝓕, hf, fun F hF => ?_, hu⟩
  obtain ⟨a, -, b, -, h1, h2, h3⟩ := h F hF
  refine ⟨a, b, hc, h1, h2, ?_⟩
  rw [← h3, ← Γ.closure_cell_inter_N hc]
  ext z
  exact ⟨fun h => ⟨h.1, discBd_subset _ (h2 h.1), h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

omit [T2Space S] in
theorem exists_inner {L : Set S} {u v : S} (hL : IsLineWithEnds L u v) {A : Set S}
  (hA : A.Finite) : ∃ z ∈ L, z ≠ u ∧ z ≠ v ∧ z ∉ A := by
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := hL.exists_arc
  have hinf : (Ioo (0 : ℝ) 1).Infinite := Set.Ioo_infinite zero_lt_one
  have hinj : InjOn (fun t : ℝ => a (Set.projIcc 0 1 zero_le_one t)) (Ioo 0 1) := fun s hs t ht he
    => by
    have h1 := ha.2 he
    have h2 := congrArg Subtype.val h1
    rwa [Set.projIcc_of_mem _ (Ioo_subset_Icc_self hs), Set.projIcc_of_mem _
      (Ioo_subset_Icc_self ht)] at h2
  have h3 := (hinf.image hinj).sdiff (hA.union (toFinite {a 0, a 1}))
  obtain ⟨_, ⟨t, ht, rfl⟩, hn⟩ := h3.nonempty
  exact ⟨_, mem_range_self _, fun h => hn (.inr (.inl h)), fun h => hn (.inr (.inr h)),
    fun h => hn (.inl h)⟩

/-- There are finitely many gaps of all cells. -/
theorem finite_gaps : {L | ∃ c u v, Γ.IsGap c L u v}.Finite := by
  classical
  have h1 : ∀ c ∈ Γ.C, {L | ∃ u v, Γ.IsGap c L u v}.Finite := fun c hc => by
    by_cases hne : ∃ x ∈ tilde c, ∃ y ∈ tilde c, x ≠ y
    · obtain ⟨x, hx, y, hy, hxy⟩ := hne
      obtain ⟨𝓕, hf, h, hu⟩ := exists_gaps hc hx hy hxy
      refine hf.subset ?_
      rintro L ⟨u, v, hL⟩
      obtain ⟨z, hz, hzu, hzv, hzN⟩ := exists_inner hL.2.1 Γ.finite_N
      obtain ⟨F, hF, hzF⟩ := (hu ▸ hL.2.2.1 hz : z ∈ ⋃₀ 𝓕)
      obtain ⟨u', v', hF'⟩ := h F hF
      obtain ⟨-, rfl⟩ := hL.unique hF' hz hzF hzN
      exact hF
    · apply Set.Finite.subset finite_empty
      rintro L ⟨u, v, hL⟩
      have hu : u ∈ tilde c := by
        rw [← Γ.closure_cell_inter_N hc]
        exact ⟨hL.subset_closure hL.2.1.left_mem, hL.left_mem_N⟩
      have hv : v ∈ tilde c := by
        rw [← Γ.closure_cell_inter_N hc]
        exact ⟨hL.subset_closure hL.2.1.right_mem, hL.right_mem_N⟩
      exact (hne ⟨u, hu, v, hv, hL.2.1.ne'⟩).elim
  refine (Γ.finite_cells.biUnion h1).subset ?_
  rintro L ⟨c, u, v, hL⟩
  exact mem_iUnion₂.mpr ⟨c, hL.1, u, v, hL⟩

/-- A point of the boundary of a cell off the nodes and off the boundary of the surface lies on a
side, if the cell has two nodes. -/
theorem exists_side (hS : IsSurface S) {c : Set S} {y : S} (hc : c ∈ Γ.C)
    (h2 : ∃ a ∈ tilde c, ∃ b ∈ tilde c, a ≠ b) (hy : y ∈ discBd (closure c))
    (hyN : y ∉ Γ.N) (hyb : y ∉ bd S) :
    ∃ L u v, Γ.IsSide c L u v ∧ y ∈ L ∧ y ≠ u ∧ y ≠ v := by
  by_cases hbd : (c ∩ bd S).Nonempty
  · obtain ⟨u, v, -, ht, hB, -, -, -⟩ := Γ.border_cell_exists_ends hc hbd
    have hdisc := Γ.isClosedDisc_closure_cell hc
    have hBs : closure c ∩ bd S ⊆ discBd (closure c) := fun x hx => by
      by_contra hn
      exact hx.2 (isInteriorPoint_of_mem_discInt hS.2.2 hdisc ⟨hx.1, hn⟩)
    obtain ⟨B', hB', hun, hin⟩ := oarc_split hdisc.isOArc_discBd hB hBs
    have hyB' : y ∈ B' := (hun ▸ hy : y ∈ _ ∪ B').resolve_left fun (h : y ∈ closure c ∩ bd S)
      => hyb h.2
    have hB'c : B' ⊆ closure c := (hun ▸ subset_union_right : B' ⊆ _).trans (discBd_subset _)
    refine ⟨B', u, v, ⟨⟨hc, hB', hun ▸ subset_union_right, ?_⟩, ?_⟩, hyB', ?_, ?_⟩
    · rw [← ht, ← Γ.closure_cell_inter_N hc]
      apply subset_antisymm
      · exact fun z hz => ⟨hB'c hz.1, hz.2⟩
      · intro z hz
        have h1 : z ∈ tilde c := by
          rw [← Γ.closure_cell_inter_N hc]
          exact hz
        rw [ht] at h1
        rcases h1 with rfl | rfl
        · exact ⟨hB'.left_mem, hz.2⟩
        · exact ⟨hB'.right_mem, hz.2⟩
    · refine disjoint_left.mpr fun x hx hxb => hx.2 ?_
      have h1 : x ∈ (closure c ∩ bd S) ∩ B' := ⟨⟨hB'c hx.1, hxb⟩, hx.1⟩
      rwa [hin] at h1
    · rintro rfl
      exact hyN (Γ.tilde_subset_N hc (ht ▸ .inl rfl))
    · rintro rfl
      exact hyN (Γ.tilde_subset_N hc (ht ▸ .inr rfl))
  · obtain ⟨a, ha, b, hb, hab⟩ := h2
    obtain ⟨𝓕, -, h, hu⟩ := exists_gaps hc ha hb hab
    obtain ⟨F, hF, hyF⟩ := (hu ▸ hy : y ∈ ⋃₀ 𝓕)
    obtain ⟨u, v, hF'⟩ := h F hF
    refine ⟨F, u, v, ⟨hF', disjoint_left.mpr fun x hx hxb => ?_⟩, hyF, ?_, ?_⟩
    · exact hbd ⟨x, hF'.mem_cell hx.1 (fun e => hx.2 (.inl e)) (fun e => hx.2 (.inr e)), hxb⟩
    · rintro rfl
      exact hyN hF'.left_mem_N
    · rintro rfl
      exact hyN hF'.right_mem_N

end Painting

end GraphMinor.GM17
