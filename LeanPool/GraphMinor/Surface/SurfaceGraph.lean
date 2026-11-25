/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ArcTools

/-!
# Finite graphs in a space

`IsGraph V E` says that `E` is a finite set of arcs with ends in the finite set `V`, that meet only
in `V`. We add
points (`IsGraph.add_point`), arcs and whole curves (`IsGraph.add_curve`), as long as the new curve
meets the old graph
in a finite way. An `O`-arc in the graph contains or misses the open part of each edge
(`IsGraph.edge_or`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

universe u

local notation "𝕀" => unitInterval

variable {X : Type u} [TopologicalSpace X]

theorem IsLineWithEnds.left_mem {L : Set X} {u v : X} (h : IsLineWithEnds L u v) : u ∈ L := by
  obtain ⟨f, h0, -⟩ := h
  exact h0 ▸ (f 0).2

theorem IsLineWithEnds.right_mem {L : Set X} {u v : X} (h : IsLineWithEnds L u v) : v ∈ L := by
  obtain ⟨f, -, h1⟩ := h
  exact h1 ▸ (f 1).2

theorem IsLineWithEnds.isCompact {L : Set X} {u v : X} (h : IsLineWithEnds L u v) : IsCompact L
  := by
  obtain ⟨f, -, -⟩ := h
  have : L = range fun t => (f t).1 := by
    ext x
    constructor
    · intro hx
      exact ⟨f.symm ⟨x, hx⟩, by simp⟩
    · rintro ⟨t, rfl⟩
      exact (f t).2
  rw [this]
  exact isCompact_range (continuous_subtype_val.comp f.continuous)

/-- The carrier of a graph. -/
def gr (V : Set X) (E : Set (Set X)) : Set X := V ∪ ⋃₀ E

/-- `E` is a finite set of arcs with ends in the finite set `V`, that meet only in `V`. -/
structure IsGraph (V : Set X) (E : Set (Set X)) : Prop where
  fin : V.Finite
  fine : E.Finite
  edge : ∀ e ∈ E, ∃ u v, u ≠ v ∧ IsLineWithEnds e u v ∧ e ∩ V = {u, v}
  disj : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → e ∩ f ⊆ V

theorem isGraph_empty : IsGraph (∅ : Set X) ∅ := ⟨finite_empty, finite_empty, by simp, by simp⟩

theorem IsGraph.isClosed_gr [T2Space X] {V : Set X} {E : Set (Set X)} (h : IsGraph V E) : IsClosed
  (gr V E) := by
  refine h.fin.isClosed.union (h.fine.isClosed_sUnion fun e he => ?_)
  obtain ⟨u, v, -, hl, -⟩ := h.edge e he
  exact hl.isCompact.isClosed

/-- Insert a vertex, subdividing at most one edge. Each resulting edge lies in an old edge. -/
theorem IsGraph.add_point_counted [T2Space X] {V : Set X} {E : Set (Set X)} (h : IsGraph V E)
  (x : X) :
    ∃ E', IsGraph (insert x V) E' ∧ gr (insert x V) E' = insert x (gr V E) ∧ ⋃₀ E ⊆ ⋃₀ E'
      ∧ E'.ncard ≤ E.ncard + 1 ∧
      ∀ f ∈ E', ∃ e ∈ E, f ⊆ e := by
  classical
  by_cases hV : x ∈ V
  · refine ⟨E, by rwa [insert_eq_of_mem hV], ?_, subset_rfl, by omega, fun f hf ↦ ⟨f, hf,
      subset_rfl⟩⟩
    rw [insert_eq_of_mem hV, insert_eq_of_mem (Or.inl hV : x ∈ gr V E)]
  by_cases hE : ∃ e ∈ E, x ∈ e
  · obtain ⟨e, he, hx⟩ := hE
    obtain ⟨u, v, huv, hl, hi⟩ := h.edge e he
    have hu : u ∈ V := (hi.symm ▸ mem_insert u {v} : u ∈ e ∩ V).2
    have hv : v ∈ V := (hi.symm ▸ mem_insert_of_mem u rfl : v ∈ e ∩ V).2
    have hxu : x ≠ u := fun he' => hV (he' ▸ hu)
    have hxv : x ≠ v := fun he' => hV (he' ▸ hv)
    obtain ⟨L₁, L₂, h₁, h₂, hun, hin⟩ := hl.split hx hxu hxv
    have hs1 : L₁ ⊆ e := hun ▸ subset_union_left
    have hs2 : L₂ ⊆ e := hun ▸ subset_union_right
    have hof : ∀ f ∈ E, f ≠ e → x ∉ f := fun f hf hne hxf => hV (h.disj e he f hf hne.symm ⟨hx,
      hxf⟩)
    have hvL : v ∉ L₁ := fun hc => hxv (mem_singleton_iff.mp (hin ▸ (⟨hc, h₂.right_mem⟩ : v ∈ L₁ ∩
      L₂))).symm
    have huL : u ∉ L₂ := fun hc => hxu (mem_singleton_iff.mp (hin ▸ (⟨h₁.left_mem, hc⟩ : u ∈ L₁ ∩
      L₂))).symm
    refine ⟨insert L₁ (insert L₂ (E \ {e})), ⟨h.fin.insert x, ((h.fine.sdiff).insert _).insert _,
      ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rintro f (rfl | rfl | ⟨hf, hne⟩)
      · refine ⟨u, x, hxu.symm, h₁, ?_⟩
        ext y
        constructor
        · rintro ⟨hy, rfl | hy'⟩
          · simp
          · have : y ∈ e ∩ V := ⟨hs1 hy, hy'⟩
            rw [hi] at this
            rcases this with rfl | rfl
            · simp
            · exact absurd hy hvL
        · rintro (rfl | rfl)
          · exact ⟨h₁.left_mem, .inr hu⟩
          · exact ⟨h₁.right_mem, .inl rfl⟩
      · refine ⟨x, v, hxv, h₂, ?_⟩
        ext y
        constructor
        · rintro ⟨hy, rfl | hy'⟩
          · simp
          · have : y ∈ e ∩ V := ⟨hs2 hy, hy'⟩
            rw [hi] at this
            rcases this with rfl | rfl
            · exact absurd hy huL
            · simp
        · rintro (rfl | rfl)
          · exact ⟨h₂.left_mem, .inl rfl⟩
          · exact ⟨h₂.right_mem, .inr hv⟩
      · obtain ⟨a, b, hab, hl', hi'⟩ := h.edge f hf
        refine ⟨a, b, hab, hl', ?_⟩
        rw [inter_insert_of_notMem (hof f hf hne), hi']
    · have hL1 : ∀ g ∈ E \ {e}, L₁ ∩ g ⊆ insert x V := fun g hg y hy =>
        .inr (h.disj e he g hg.1 (Ne.symm hg.2) ⟨hs1 hy.1, hy.2⟩)
      have hL2 : ∀ g ∈ E \ {e}, L₂ ∩ g ⊆ insert x V := fun g hg y hy =>
        .inr (h.disj e he g hg.1 (Ne.symm hg.2) ⟨hs2 hy.1, hy.2⟩)
      have h12 : L₁ ∩ L₂ ⊆ insert x V := by
        rw [hin]
        exact singleton_subset_iff.mpr (mem_insert _ _)
      rintro f (rfl | rfl | hf) g (rfl | rfl | hg) hne
      · exact absurd rfl hne
      · exact h12
      · exact hL1 g hg
      · exact (inter_comm _ _).subset.trans h12
      · exact absurd rfl hne
      · exact hL2 g hg
      · exact (inter_comm _ _).subset.trans (hL1 f hf)
      · exact (inter_comm _ _).subset.trans (hL2 f hf)
      · exact (h.disj f hf.1 g hg.1 hne).trans (subset_insert _ _)
    · ext y
      simp only [gr, mem_union, mem_insert_iff, mem_sUnion, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ((rfl | hy) | ⟨f, (rfl | rfl | ⟨hf, -⟩), hy⟩)
        · exact .inl rfl
        · exact .inr (.inl hy)
        · exact .inr (.inr ⟨e, he, hs1 hy⟩)
        · exact .inr (.inr ⟨e, he, hs2 hy⟩)
        · exact .inr (.inr ⟨f, hf, hy⟩)
      · rintro (rfl | hy | ⟨f, hf, hy⟩)
        · exact .inl (.inl rfl)
        · exact .inl (.inr hy)
        · by_cases hfe : f = e
          · subst hfe
            rw [← hun] at hy
            rcases hy with hy | hy
            · exact .inr ⟨L₁, .inl rfl, hy⟩
            · exact .inr ⟨L₂, .inr (.inl rfl), hy⟩
          · exact .inr ⟨f, .inr (.inr ⟨hf, hfe⟩), hy⟩
    · rintro y ⟨f, hf, hy⟩
      by_cases hfe : f = e
      · subst hfe
        rw [← hun] at hy
        rcases hy with hy | hy
        · exact ⟨L₁, .inl rfl, hy⟩
        · exact ⟨L₂, .inr (.inl rfl), hy⟩
      · exact ⟨f, .inr (.inr ⟨hf, hfe⟩), hy⟩
    · have h1 : (insert L₁ (insert L₂ (E \ {e}))).ncard ≤ (insert L₂ (E \ {e})).ncard + 1
      := ncard_insert_le _ _
      have h2 : (insert L₂ (E \ {e})).ncard ≤ (E \ {e}).ncard + 1 := ncard_insert_le _ _
      have h3 : (E \ {e}).ncard + 1 = E.ncard := ncard_sdiff_singleton_add_one he h.fine
      omega
    · rintro f (rfl | rfl | ⟨hf, -⟩)
      · exact ⟨e, he, hs1⟩
      · exact ⟨e, he, hs2⟩
      · exact ⟨f, hf, subset_rfl⟩
  · push Not at hE
    refine ⟨E, ⟨h.fin.insert x, h.fine, fun e he => ?_, fun e he f hf hne =>
      (h.disj e he f hf hne).trans (subset_insert _ _)⟩, ?_, subset_rfl, by omega, fun f hf ↦ ⟨f,
        hf, subset_rfl⟩⟩
    · obtain ⟨a, b, hab, hl', hi'⟩ := h.edge e he
      refine ⟨a, b, hab, hl', ?_⟩
      rw [inter_insert_of_notMem (hE e he), hi']
    · simp only [gr, insert_union]

theorem IsGraph.add_point [T2Space X] {V : Set X} {E : Set (Set X)} (h : IsGraph V E) (x : X) :
    ∃ E', IsGraph (insert x V) E' ∧ gr (insert x V) E' = insert x (gr V E) ∧ ⋃₀ E ⊆ ⋃₀ E' := by
  obtain ⟨E', hGraph, hPointSet, hCover, _, _⟩ := h.add_point_counted x
  exact ⟨E', hGraph, hPointSet, hCover⟩

/-- Adding an arc whose ends are vertices and which misses the rest of the graph. -/
theorem IsGraph.add_arc {V : Set X} {E : Set (Set X)} (h : IsGraph V E) {A : Set X} {p q : X}
  (hpq : p ≠ q)
    (hl : IsLineWithEnds A p q) (hp : p ∈ V) (hq : q ∈ V) (hA : A ∩ gr V E = {p, q}) :
    IsGraph V (insert A E) ∧ gr V (insert A E) = gr V E ∪ A := by
  have hsub : ∀ f ∈ E, A ∩ f ⊆ V := fun f hf y hy => by
    have : y ∈ A ∩ gr V E := ⟨hy.1, .inr ⟨f, hf, hy.2⟩⟩
    rw [hA] at this
    rcases this with rfl | rfl
    · exact hp
    · exact hq
  refine ⟨⟨h.fin, h.fine.insert _, ?_, ?_⟩, ?_⟩
  · rintro f (rfl | hf)
    · refine ⟨p, q, hpq, hl, ?_⟩
      ext y
      constructor
      · rintro ⟨h1, h2⟩
        rw [← hA]
        exact ⟨h1, .inl h2⟩
      · rintro (rfl | rfl)
        · exact ⟨hl.left_mem, hp⟩
        · exact ⟨hl.right_mem, hq⟩
    · exact h.edge f hf
  · rintro f (rfl | hf) g (rfl | hg) hne
    · exact absurd rfl hne
    · exact hsub g hg
    · exact (inter_comm _ _).subset.trans (hsub f hf)
    · exact h.disj f hf g hg hne
  · ext y
    simp only [gr, mem_union, mem_sUnion, mem_insert_iff]
    constructor
    · rintro (hy | ⟨f, rfl | hf, hy⟩)
      · exact .inl (.inl hy)
      · exact .inr hy
      · exact .inl (.inr ⟨f, hf, hy⟩)
    · rintro ((hy | ⟨f, hf, hy⟩) | hy)
      · exact .inl hy
      · exact .inr ⟨f, .inr hf, hy⟩
      · exact .inr ⟨A, .inl rfl, hy⟩

/-- Adding an arc with ends in the graph which meets the graph in a finite way. -/
theorem IsGraph.add_path [T2Space X] {a : 𝕀 → X} (ha : IsArcMap a) (n : ℕ) :
    ∀ (V : Set X) (E : Set (Set X)) (F : Set (Set X)), IsGraph V E → a 0 ∈ gr V E → a 1 ∈ gr V E
      → F.Finite →
      F.ncard = n → (∀ J ∈ F, IsPreconnected J) → ⋃₀ F = range a \ gr V E →
      ∃ V' E', V ⊆ V' ∧ IsGraph V' E' ∧ gr V' E' = gr V E ∪ range a ∧ (V ⊆ ⋃₀ E → V' ⊆ ⋃₀ E') := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V E F h h0 h1 hF hn hJ hU
  by_cases hW : range a ⊆ gr V E
  · exact ⟨V, E, subset_rfl, h, by rw [union_eq_left.mpr hW], id⟩
  obtain ⟨_, ⟨t0, rfl⟩, ht0⟩ := not_subset.mp hW
  have hcl : IsClosed (a ⁻¹' gr V E) := h.isClosed_gr.preimage ha.1
  have hc1 : IsCompact (a ⁻¹' gr V E ∩ Iic t0) := (hcl.inter isClosed_Iic).isCompact
  have hc2 : IsCompact (a ⁻¹' gr V E ∩ Ici t0) := (hcl.inter isClosed_Ici).isCompact
  obtain ⟨s, ⟨hs1, hs2⟩, hsg⟩ := hc1.exists_isGreatest ⟨0, h0, unitInterval.nonneg t0⟩
  obtain ⟨r, ⟨hr1, hr2⟩, hrl⟩ := hc2.exists_isLeast ⟨1, h1, unitInterval.le_one t0⟩
  have hst : s < t0 := lt_of_le_of_ne hs2 fun he => ht0 (he ▸ hs1)
  have htr : t0 < r := lt_of_le_of_ne hr2 fun he => ht0 (he ▸ hr1)
  have hsr : s < r := hst.trans htr
  have hsrR : (s : ℝ) < r := hsr
  set A : Set X := a '' Icc s r with hAdef
  have hline : IsLineWithEnds A (a s) (a r) := by
    have := (IsArcMap.sub ha hsr.ne).isLineWithEnds
    rw [range_subArc a hsr.le, subArc_zero, subArc_one] at this
    exact this
  have hne : a s ≠ a r := fun he => hsr.ne (ha.2 he)
  have hAi : A ∩ gr V E = {a s, a r} := by
    ext y
    constructor
    · rintro ⟨⟨t, ⟨h3, h4⟩, rfl⟩, hy⟩
      rcases le_total t t0 with h5 | h5
      · have : t ≤ s := hsg ⟨hy, h5⟩
        exact .inl (congrArg a (le_antisymm this h3))
      · have : r ≤ t := hrl ⟨hy, h5⟩
        exact .inr (congrArg a (le_antisymm h4 this))
    · rintro (rfl | rfl)
      · exact ⟨⟨s, ⟨le_rfl, hsr.le⟩, rfl⟩, hs1⟩
      · exact ⟨⟨r, ⟨hsr.le, le_rfl⟩, rfl⟩, hr1⟩
  obtain ⟨E1, hG1, hg1, hu1⟩ := h.add_point (a s)
  obtain ⟨E2, hG2, hg2, hu2⟩ := hG1.add_point (a r)
  have hgr : gr (insert (a r) (insert (a s) V)) E2 = gr V E := by
    rw [hg2, hg1, insert_eq_of_mem (show a s ∈ gr V E from hs1),
      insert_eq_of_mem (show a r ∈ gr V E from hr1)]
  obtain ⟨hG3, hg3⟩ := hG2.add_arc hne hline (.inr (.inl rfl)) (.inl rfl) (by rw [hgr, hAi])
  rw [hgr] at hg3
  have hsame : ∀ J ∈ F, (J ∩ A).Nonempty → J ⊆ A := by
    rintro J hJF ⟨_, hy, ⟨t, ht, rfl⟩⟩ y' hy'
    have hJW : J ⊆ range a \ gr V E := hU ▸ subset_sUnion_of_mem hJF
    obtain ⟨t', rfl⟩ := (hJW hy').1
    have hemb : IsEmbedding a := (ha.1.isClosedEmbedding ha.2).isEmbedding
    have hpc : IsPreconnected (a ⁻¹' J) := by
      refine hemb.isInducing.isPreconnected_image.mp ?_
      rw [image_preimage_eq_inter_range, inter_eq_left.mpr fun z hz => (hJW hz).1]
      exact hJ J hJF
    have hord := hpc.ordConnected
    by_contra hcon
    have ht' : t' < s ∨ r < t' := by
      by_contra hc
      push Not at hc
      exact hcon ⟨t', ⟨hc.1, hc.2⟩, rfl⟩
    have hbad : ∀ w ∈ a ⁻¹' J, w ∉ a ⁻¹' gr V E := fun w hw => (hJW hw).2
    rcases ht' with h3 | h3
    · exact hbad s (hord.out hy' hy ⟨h3.le, ht.1⟩) hs1
    · exact hbad r (hord.out hy hy' ⟨ht.2, h3.le⟩) hr1
  let F' : Set (Set X) := {J ∈ F | Disjoint J A}
  obtain ⟨J0, hJ0, hx0⟩ : ∃ J ∈ F, a t0 ∈ J := by
    have : a t0 ∈ ⋃₀ F := hU ▸ ⟨⟨t0, rfl⟩, ht0⟩
    exact this
  have hA0 : a t0 ∈ A := ⟨t0, ⟨hst.le, htr.le⟩, rfl⟩
  have hlt : F'.ncard < n := by
    rw [← hn]
    refine ncard_lt_ncard ?_ hF
    refine ⟨fun J hJ => hJ.1, fun hc => ?_⟩
    exact Set.disjoint_left.mp (hc hJ0).2 hx0 hA0
  obtain ⟨V', E', hVV, hG', hg', hno⟩ := ih _ hlt _ _ F' hG3 (by rw [hg3]; exact .inl h0)
    (by rw [hg3]; exact .inl h1)
    (hF.subset fun J hJ => hJ.1) rfl (fun J hJ' => hJ J hJ'.1) (by
      rw [hg3]
      ext y
      constructor
      · rintro ⟨J, ⟨hJF, hd⟩, hy⟩
        have : y ∈ range a \ gr V E := hU ▸ mem_sUnion_of_mem hy hJF
        exact ⟨this.1, fun hc => hc.elim this.2 (Set.disjoint_left.mp hd hy)⟩
      · rintro ⟨hy1, hy2⟩
        have hy3 : y ∈ ⋃₀ F := hU ▸ ⟨hy1, fun hc => hy2 (.inl hc)⟩
        obtain ⟨J, hJF, hyJ⟩ := hy3
        refine ⟨J, ⟨hJF, ?_⟩, hyJ⟩
        rw [Set.disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
        intro hne'
        exact hy2 (.inr (hsame J hJF hne' hyJ)))
  refine ⟨V', E', (subset_insert _ _).trans ((subset_insert _ _).trans hVV), hG', ?_, fun hVE
    => hno ?_⟩
  · rw [hg', hg3, union_assoc, union_eq_right.mpr (image_subset_range a _)]
  · rintro y (rfl | rfl | hy)
    · exact ⟨A, .inl rfl, hline.right_mem⟩
    · exact ⟨A, .inl rfl, hline.left_mem⟩
    · obtain ⟨f, hf, hyf⟩ := hu2 (hu1 (hVE hy))
      exact ⟨f, .inr hf, hyf⟩

theorem IsOArc.exists_ne {P : Set X} (hP : IsOArc P) (x : X) : ∃ y ∈ P, y ≠ x := by
  obtain ⟨φ⟩ := id hP
  by_cases h3 : (φ 1).1 = x
  · refine ⟨(φ (Circle.exp Real.pi)).1, (φ _).2, fun h4 => ?_⟩
    have h5 := φ.injective (Subtype.ext (h4.trans h3.symm))
    have h6 := congrArg (fun w : Circle => (w : ℂ)) h5
    simp at h6
    norm_num at h6
  · exact ⟨_, (φ 1).2, h3⟩

theorem IsTwoArcs.inter {a b : 𝕀 → X} (h : IsTwoArcs a b) : range a ∩ range b = {a 0, a 1} := by
  ext y
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩
    rcases h.meet s t ht.symm with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact .inl rfl
    · exact .inr rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨0, rfl⟩, ⟨0, h.zero⟩⟩
    · exact ⟨⟨1, rfl⟩, ⟨1, h.one⟩⟩

/-- Adding a curve which meets the graph in a finite way. -/
theorem IsGraph.add_curve [T2Space X] {V : Set X} {E : Set (Set X)} (h : IsGraph V E) {P : Set X}
  (hP : IsOArc P)
    (hF : FinConn (P \ gr V E)) :
    ∃ V' E', V ⊆ V' ∧ IsGraph V' E' ∧ gr V' E' = gr V E ∪ P ∧ (V ⊆ ⋃₀ E → V' ⊆ ⋃₀ E') := by
  classical
  by_cases h2 : ∃ x y, x ∈ P ∧ y ∈ P ∧ x ∈ gr V E ∧ y ∈ gr V E ∧ x ≠ y
  · obtain ⟨x, y, hxP, hyP, hxG, hyG, hxy⟩ := h2
    obtain ⟨a, b, hab, rfl, rfl, rfl⟩ := hP.exists_arcs hxP hyP hxy
    obtain ⟨F, hFf, hFc, hFu⟩ := hF
    have hi := hab.inter
    have hca : IsClosed (range a) := (isCompact_range hab.1.1).isClosed
    have hcb : IsClosed (range b) := (isCompact_range hab.2.1).isClosed
    have hside : ∀ J ∈ F, J ⊆ range a ∨ J ⊆ range b := fun J hJ => by
      have h3 : J ⊆ (range a ∪ range b) \ gr V E := hFu ▸ subset_sUnion_of_mem hJ
      by_contra hcon
      push Not at hcon
      obtain ⟨h4, h5⟩ := hcon
      obtain ⟨z, hz, hz'⟩ := not_subset.mp h4
      obtain ⟨z', hw, hw'⟩ := not_subset.mp h5
      have hzb : z ∈ range b := ((h3 hz).1).resolve_left hz'
      have hwa : z' ∈ range a := ((h3 hw).1).resolve_right hw'
      obtain ⟨v, hv, hv'⟩ := isPreconnected_closed_iff.mp (hFc J hJ) _ _ hca hcb
        (fun w hw => (h3 hw).1) ⟨z', hw, hwa⟩ ⟨z, hz, hzb⟩
      rw [hi] at hv'
      rcases hv' with rfl | rfl
      · exact (h3 hv).2 hxG
      · exact (h3 hv).2 hyG
    let Fa : Set (Set X) := {J ∈ F | J ⊆ range a}
    let Fb : Set (Set X) := {J ∈ F | J ⊆ range b}
    obtain ⟨V1, E1, hV1, hG1, hg1, hno1⟩ := IsGraph.add_path hab.1 _ V E Fa h hxG hyG
      (hFf.subset fun J hJ => hJ.1) rfl
      (fun J hJ => hFc J hJ.1) (by
        ext z
        constructor
        · rintro ⟨J, hJ, hz⟩
          have h3 : z ∈ (range a ∪ range b) \ gr V E := hFu ▸ mem_sUnion_of_mem hz hJ.1
          exact ⟨hJ.2 hz, h3.2⟩
        · rintro ⟨hz, hz'⟩
          have h3 : z ∈ ⋃₀ F := hFu ▸ ⟨.inl hz, hz'⟩
          obtain ⟨J, hJ, hzJ⟩ := h3
          rcases hside J hJ with h4 | h4
          · exact ⟨J, ⟨hJ, h4⟩, hzJ⟩
          · have h5 : z ∈ range a ∩ range b := ⟨hz, h4 hzJ⟩
            rw [hi] at h5
            rcases h5 with rfl | rfl
            · exact absurd hxG hz'
            · exact absurd hyG hz')
    have h0b : b 0 ∈ gr V1 E1 := by rw [hg1, hab.zero]; exact .inl hxG
    have h1b : b 1 ∈ gr V1 E1 := by rw [hg1, hab.one]; exact .inl hyG
    obtain ⟨V2, E2, hV2, hG2, hg2, hno2⟩ := IsGraph.add_path hab.2 _ V1 E1 Fb hG1 h0b h1b
      (hFf.subset fun J hJ => hJ.1) rfl
      (fun J hJ => hFc J hJ.1) (by
        rw [hg1]
        ext z
        constructor
        · rintro ⟨J, hJ, hz⟩
          have h3 : z ∈ (range a ∪ range b) \ gr V E := hFu ▸ mem_sUnion_of_mem hz hJ.1
          refine ⟨hJ.2 hz, ?_⟩
          rintro (h4 | h4)
          · exact h3.2 h4
          · have h5 : z ∈ range a ∩ range b := ⟨h4, hJ.2 hz⟩
            rw [hi] at h5
            rcases h5 with rfl | rfl
            · exact h3.2 hxG
            · exact h3.2 hyG
        · rintro ⟨hz, hz'⟩
          have h3 : z ∈ ⋃₀ F := hFu ▸ ⟨.inr hz, fun h4 => hz' (.inl h4)⟩
          obtain ⟨J, hJ, hzJ⟩ := h3
          rcases hside J hJ with h4 | h4
          · exact absurd (.inr (h4 hzJ)) hz'
          · exact ⟨J, ⟨hJ, h4⟩, hzJ⟩)
    exact ⟨V2, E2, hV1.trans hV2, hG2, by rw [hg2, hg1, union_assoc], hno2 ∘ hno1⟩
  · push Not at h2
    obtain ⟨x, hxP, hx1⟩ : ∃ x ∈ P, ∀ z ∈ P, z ∈ gr V E → z = x := by
      by_cases h3 : ∃ x ∈ P, x ∈ gr V E
      · obtain ⟨x, hxP, hxG⟩ := h3
        exact ⟨x, hxP, fun z hz hzG => h2 z x hz hxP hzG hxG⟩
      · push Not at h3
        obtain ⟨x, hxP, -⟩ := hP.exists_ne (Classical.choice (by
          obtain ⟨φ⟩ := hP
          exact ⟨(φ 1).1⟩))
        exact ⟨x, hxP, fun z hz hzG => absurd hzG (h3 z hz)⟩
    obtain ⟨y, hyP, hyx⟩ := hP.exists_ne x
    obtain ⟨a, b, hab, ha0, ha1, hu⟩ := hP.exists_arcs hxP hyP (Ne.symm hyx)
    obtain ⟨E1, hG1, hg1, hu1⟩ := h.add_point x
    obtain ⟨E2, hG2, hg2, hu2⟩ := hG1.add_point y
    have hi := hab.inter
    rw [ha0, ha1] at hi
    have hg3 : gr (insert y (insert x V)) E2 = insert y (insert x (gr V E)) := by rw [hg2, hg1]
    have hra : range a ⊆ P := hu ▸ subset_union_left
    have hrb : range b ⊆ P := hu ▸ subset_union_right
    obtain ⟨hG3, hg4⟩ := hG2.add_arc (Ne.symm hyx) (by
      have := hab.1.isLineWithEnds
      rwa [ha0, ha1] at this) (.inr (.inl rfl)) (.inl rfl) (by
      rw [hg3]
      ext z
      constructor
      · rintro ⟨hz, rfl | rfl | hz'⟩
        · exact .inr rfl
        · exact .inl rfl
        · exact .inl (hx1 z (hra hz) hz')
      · rintro (rfl | rfl)
        · exact ⟨⟨0, ha0⟩, .inr (.inl rfl)⟩
        · exact ⟨⟨1, ha1⟩, .inl rfl⟩)
    obtain ⟨hG4, hg5⟩ := hG3.add_arc (Ne.symm hyx) (by
      have := hab.2.isLineWithEnds
      rwa [hab.zero, hab.one, ha0, ha1] at this) (.inr (.inl rfl)) (.inl rfl) (by
      rw [hg4, hg3]
      ext z
      constructor
      · rintro ⟨hz, (rfl | rfl | hz') | hz'⟩
        · exact .inr rfl
        · exact .inl rfl
        · exact .inl (hx1 z (hrb hz) hz')
        · rw [← hi]
          exact ⟨hz', hz⟩
      · rintro (rfl | rfl)
        · exact ⟨⟨0, by rw [hab.zero, ha0]⟩, .inl (.inr (.inl rfl))⟩
        · exact ⟨⟨1, by rw [hab.one, ha1]⟩, .inl (.inl rfl)⟩)
    refine ⟨_, _, (subset_insert _ _).trans (subset_insert _ _), hG4, ?_, fun hVE => ?_⟩
    swap
    · rintro z (rfl | rfl | hz)
      · exact ⟨range a, .inr (.inl rfl), ⟨1, ha1⟩⟩
      · exact ⟨range a, .inr (.inl rfl), ⟨0, ha0⟩⟩
      · obtain ⟨f, hf, hzf⟩ := hu2 (hu1 (hVE hz))
        exact ⟨f, .inr (.inr hf), hzf⟩
    rw [hg5, hg4, hg3, ← hu]
    ext z
    simp only [mem_union, mem_insert_iff]
    constructor
    · rintro (((rfl | rfl | hz) | hz) | hz)
      · exact .inr (.inl ⟨1, ha1⟩)
      · exact .inr (.inl ⟨0, ha0⟩)
      · exact .inl hz
      · exact .inr (.inl hz)
      · exact .inr (.inr hz)
    · rintro (hz | hz | hz)
      · exact .inl (.inl (.inr (.inr hz)))
      · exact .inl (.inr hz)
      · exact .inr hz

/-- `G` stays connected when one point is removed. -/
def TwoConn (G : Set X) : Prop := ∀ p, IsPreconnected (G \ {p})

theorem TwoConn.union {A B : Set X} (hA : TwoConn A) (hB : TwoConn B) {x y : X} (hx : x ∈ A ∩ B)
  (hy : y ∈ A ∩ B)
    (hxy : x ≠ y) : TwoConn (A ∪ B) := by
  intro p
  rw [union_sdiff_distrib]
  by_cases hp : x = p
  · refine (hA p).union y ⟨hy.1, ?_⟩ ⟨hy.2, ?_⟩ (hB p)
    all_goals exact fun h => hxy (hp.trans (mem_singleton_iff.mp h).symm)
  · exact (hA p).union x ⟨hx.1, hp⟩ ⟨hx.2, hp⟩ (hB p)

/-- An `O`-arc is still connected when one point is removed. -/
theorem IsOArc.twoConn {P : Set X} (hP : IsOArc P) : TwoConn P := by
  intro p
  obtain ⟨φ⟩ := id hP
  by_cases hp : p ∈ P
  · obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, Circle.exp θ = φ.symm ⟨p, hp⟩ := ⟨Complex.arg _, Circle.exp_arg _⟩
    have hc : Continuous fun t : ℝ => (φ (Circle.exp t)).1 :=
      continuous_subtype_val.comp (φ.continuous.comp Circle.exp.continuous)
    have heq : P \ {p} = (fun t : ℝ => (φ (Circle.exp t)).1) '' Ioo θ (θ + 2 * Real.pi) := by
      ext z
      constructor
      · rintro ⟨hz, hzp⟩
        obtain ⟨t, ht, e⟩ := exists_circle_angle (Circle.exp θ) (φ.symm ⟨z, hz⟩)
        rw [← Circle.exp_add] at e
        have ht0 : 0 < t := by
          refine lt_of_le_of_ne ht.1 fun h0 => hzp ?_
          rw [← h0, add_zero, hθ] at e
          have := φ.symm.injective e
          exact congrArg Subtype.val this
        refine ⟨θ + t, ⟨by linarith, by linarith [ht.2]⟩, ?_⟩
        simp only
        rw [← e]
        simp
      · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
        refine ⟨(φ _).2, fun he => ?_⟩
        have e : φ (Circle.exp t) = φ (Circle.exp θ) := Subtype.ext (by rw [hθ]; simpa using he)
        obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (φ.injective e)
        have hpi := Real.pi_pos
        rcases le_or_gt m 0 with h3 | h3
        · have h4 : (m : ℝ) ≤ 0 := by exact_mod_cast h3
          nlinarith
        · have h4 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
          nlinarith
    rw [heq]
    exact isPreconnected_Ioo.image _ hc.continuousOn
  · rw [sdiff_singleton_eq_self hp]
    exact hP.isPreconnected

/-- An `O`-arc in a graph contains or misses the open part of each edge. -/
theorem IsGraph.edge_or [T2Space X] {V : Set X} {E : Set (Set X)} (h : IsGraph V E) {P : Set X}
  (hP : IsOArc P)
    (hPG : P ⊆ gr V E) {e : Set X} (he : e ∈ E) : e ⊆ P ∨ Disjoint (e \ V) P := by
  classical
  obtain ⟨u, v, huv, hl, hi⟩ := h.edge e he
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := hl.exists_arc
  have hP0 : IsClosed P := hP.isCompact.isClosed
  obtain ⟨k, -, hk⟩ := exists_inv_of_compactOn isCompact_univ ha.1.continuousOn ha.2.injOn
  have hk' : ∀ x ∈ range a, a (k x) = x := by
    rintro _ ⟨s, rfl⟩
    rw [hk (mem_univ s)]
  have hkc : ContinuousOn k (range a) := by
    obtain ⟨k', hk1, hk2⟩ := exists_inv_of_compactOn isCompact_univ ha.1.continuousOn ha.2.injOn
    rw [← image_univ]
    refine hk1.congr fun x hx => ?_
    obtain ⟨s, -, rfl⟩ := hx
    rw [hk (mem_univ s), hk2 (mem_univ s)]
  have hc := continuous_extI ha.1
  have hint : ∀ t ∈ Ioo (0 : ℝ) 1, extI a t ∉ V := fun t ht hV => by
    have h1 : extI a t ∈ range a ∩ V := ⟨by rw [extI_of_mem a ⟨ht.1.le, ht.2.le⟩]; exact ⟨_, rfl⟩,
      hV⟩
    rw [hi, extI_of_mem a ⟨ht.1.le, ht.2.le⟩] at h1
    rcases h1 with h2 | h2
    · have := congrArg Subtype.val (ha.2 h2)
      exact ht.1.ne' this
    · have := congrArg Subtype.val (ha.2 h2)
      exact ht.2.ne this
  have hmem : ∀ t ∈ Ioo (0 : ℝ) 1, extI a t ∈ range a := fun t ht => by
    rw [extI_of_mem a ⟨ht.1.le, ht.2.le⟩]
    exact ⟨_, rfl⟩
  let T : Set ℝ := {t | t ∈ Ioo (0 : ℝ) 1 ∧ extI a t ∈ P}
  have hTo : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    rintro t ⟨ht, htP⟩
    obtain ⟨φ⟩ := id hP
    let ψ : ℝ → X := fun θ => (φ (Circle.exp θ)).1
    have hψ : Continuous ψ := continuous_subtype_val.comp (φ.continuous.comp Circle.exp.continuous)
    obtain ⟨θ0, hθ0⟩ : ∃ θ : ℝ, ψ θ = extI a t := by
      refine ⟨Complex.arg (φ.symm ⟨_, htP⟩), ?_⟩
      simp [ψ, Circle.exp_arg]
    have hOc : IsClosed (V ∪ ⋃₀ (E \ {range a})) := by
      refine h.fin.isClosed.union ((h.fine.subset sdiff_subset).isClosed_sUnion fun f hf => ?_)
      obtain ⟨u, v, -, hl', -⟩ := h.edge f hf.1
      exact hl'.isCompact.isClosed
    have hyO : extI a t ∉ V ∪ ⋃₀ (E \ {range a}) := by
      rintro (hV | ⟨f, hf, hyf⟩)
      · exact hint t ht hV
      · exact hint t ht (h.disj _ he f hf.1 (Ne.symm hf.2) ⟨hmem t ht, hyf⟩)
    have hO : ψ ⁻¹' (V ∪ ⋃₀ (E \ {range a}))ᶜ ∈ 𝓝 θ0 :=
      hOc.isOpen_compl.preimage hψ |>.mem_nhds (by rw [mem_preimage, hθ0]; exact hyO)
    obtain ⟨δ', hδ', hball⟩ := Metric.mem_nhds_iff.mp hO
    let δ := min (δ' / 2) 1
    have hδ0 : 0 < δ := lt_min (by positivity) one_pos
    have hδ1 : δ < δ' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ2 : δ ≤ 1 := min_le_right _ _
    let I : Set ℝ := Icc (θ0 - δ) (θ0 + δ)
    have hIO : ∀ θ ∈ I, ψ θ ∈ range a ∧ ψ θ ∉ V := fun θ hθ => by
      have h1 : θ ∈ Metric.ball θ0 δ' := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      have h2 := hball h1
      have h3 : ψ θ ∈ gr V E := hPG (φ _).2
      refine ⟨?_, fun hV => h2 (.inl hV)⟩
      rcases h3 with h3 | ⟨f, hf, h3⟩
      · exact absurd (.inl h3) h2
      · by_cases hfe : f = range a
        · exact hfe ▸ h3
        · exact absurd (.inr ⟨f, ⟨hf, hfe⟩, h3⟩) h2
    have hinjψ : InjOn ψ I := fun x hx y hy he => by
      have e1 := φ.injective (Subtype.ext he)
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp e1
      have hpi := Real.pi_gt_three
      have h5 : |(m : ℝ) * (2 * Real.pi)| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
      rcases eq_or_ne m 0 with rfl | hm0
      · simpa using hm
      · exfalso
        have h6 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
        rw [abs_mul, abs_of_pos (show 0 < 2 * Real.pi by positivity)] at h5
        nlinarith
    let q : ℝ → ℝ := fun θ => k (ψ θ)
    have hqc : ContinuousOn q I := by
      refine continuous_subtype_val.comp_continuousOn (hkc.comp hψ.continuousOn fun θ hθ =>
        (hIO θ hθ).1)
    have hqi : InjOn q I := fun x hx y hy he => by
      have h1 : k (ψ x) = k (ψ y) := Subtype.ext he
      refine hinjψ hx hy ?_
      rw [← hk' _ (hIO x hx).1, ← hk' _ (hIO y hy).1, h1]
    have hqa : ∀ θ ∈ I, a (k (ψ θ)) = ψ θ := fun θ hθ => hk' _ (hIO θ hθ).1
    have hq01 : ∀ θ ∈ I, q θ ∈ Ioo (0 : ℝ) 1 := fun θ hθ => by
      have h1 := hIO θ hθ
      have hu0 : a 0 ∈ V := by
        have : a 0 ∈ range a ∩ V := hi ▸ mem_insert _ _
        exact this.2
      have hu1 : a 1 ∈ V := by
        have : a 1 ∈ range a ∩ V := hi ▸ mem_insert_of_mem _ rfl
        exact this.2
      refine ⟨lt_of_le_of_ne (k (ψ θ)).2.1 fun h0 => ?_, lt_of_le_of_ne (k (ψ θ)).2.2 fun h0 => ?_⟩
      · have : k (ψ θ) = 0 := Subtype.ext h0.symm
        apply h1.2
        rw [← hqa θ hθ, this]
        exact hu0
      · have : k (ψ θ) = 1 := Subtype.ext h0
        apply h1.2
        rw [← hqa θ hθ, this]
        exact hu1
    have hθI : θ0 ∈ I := ⟨by linarith, by linarith⟩
    have hq0 : q θ0 = t := by
      have h1 : a (k (ψ θ0)) = a ⟨t, ht.1.le, ht.2.le⟩ := by
        rw [hqa θ0 hθI, hθ0, extI_of_mem a ⟨ht.1.le, ht.2.le⟩]
      exact congrArg Subtype.val (ha.2 h1)
    have hle : θ0 - δ ≤ θ0 + δ := by linarith
    have hlI : θ0 - δ ∈ I := ⟨le_rfl, hle⟩
    have hrI : θ0 + δ ∈ I := ⟨hle, le_rfl⟩
    have hbetween : min (q (θ0 - δ)) (q (θ0 + δ)) < t ∧ t < max (q (θ0 - δ)) (q (θ0 + δ)) := by
      rcases hqc.strictMonoOn_of_injOn_Icc' hle hqi with hm | hm
      · have h1 := hm hlI hθI (by linarith)
        have h2 := hm hθI hrI (by linarith)
        rw [hq0] at h1 h2
        exact ⟨min_lt_iff.mpr (.inl h1), lt_max_iff.mpr (.inr h2)⟩
      · have h1 := hm hlI hθI (by linarith)
        have h2 := hm hθI hrI (by linarith)
        rw [hq0] at h1 h2
        exact ⟨min_lt_iff.mpr (.inr h2), lt_max_iff.mpr (.inl h1)⟩
    refine Filter.mem_of_superset (Ioo_mem_nhds hbetween.1 hbetween.2) fun s hs => ?_
    have hiv := intermediate_value_uIcc (a := θ0 - δ) (b := θ0 + δ) (f := q)
      (by rw [uIcc_of_le hle]; exact hqc)
    have hsu : s ∈ uIcc (q (θ0 - δ)) (q (θ0 + δ)) := Ioo_subset_Icc_self hs
    obtain ⟨θ, hθ, rfl⟩ := hiv hsu
    rw [uIcc_of_le hle] at hθ
    have hmemI := hq01 θ hθ
    refine ⟨hmemI, ?_⟩
    rw [extI_coe]
    show a (k (ψ θ)) ∈ P
    rw [hqa θ hθ]
    exact (φ _).2
  by_cases hemp : T.Nonempty
  · left
    have hall : Ioo (0 : ℝ) 1 ⊆ extI a ⁻¹' P := by
      intro t ht
      by_contra hcon
      obtain ⟨z, -, hz⟩ := isPreconnected_Ioo _ _ hTo (hP0.isOpen_compl.preimage hc)
        (fun w hw => by
          by_cases h1 : extI a w ∈ P
          · exact .inl ⟨hw, h1⟩
          · exact .inr h1) (by
            obtain ⟨w, hw⟩ := hemp
            exact ⟨w, hw.1, hw⟩) ⟨t, ht, hcon⟩
      exact hz.2 hz.1.2
    have hcl : Icc (0 : ℝ) 1 ⊆ extI a ⁻¹' P := by
      rw [← closure_Ioo (zero_ne_one' ℝ)]
      exact closure_minimal hall (hP0.preimage hc)
    rintro _ ⟨t, rfl⟩
    have := hcl t.2
    rwa [mem_preimage, extI_coe] at this
  · right
    rw [Set.disjoint_left]
    rintro _ ⟨⟨t, rfl⟩, htV⟩ htP
    apply hemp
    have h0 : (t : ℝ) ≠ 0 := fun h0 => htV (by
      have : t = 0 := Subtype.ext h0
      rw [this]
      have : a 0 ∈ range a ∩ V := hi ▸ mem_insert _ _
      exact this.2)
    have h1 : (t : ℝ) ≠ 1 := fun h0 => htV (by
      have : t = 1 := Subtype.ext h0
      rw [this]
      have : a 1 ∈ range a ∩ V := hi ▸ mem_insert_of_mem _ rfl
      exact this.2)
    refine ⟨t, ⟨lt_of_le_of_ne t.2.1 (Ne.symm h0), lt_of_le_of_ne t.2.2 h1⟩, ?_⟩
    rwa [extI_coe]

end GraphMinor.Surface
