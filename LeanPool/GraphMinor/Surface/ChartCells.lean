/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Skeleton

/-!
# Cutting a chart disc along a graph

Let `G` be a graph in a surface that stays connected when a point is removed, and let `B` be a
closed disc whose
boundary lies in `G`. Starting from `B` we add the edges of `G` inside `B` along arcs with two
different ends on what we
have so far (`exists_ear`). Each such arc cuts one closed disc in two (`IsCells.split`). So `B` is
cut into closed discs
whose interiors miss `G` (`exists_cells`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

universe u

local notation "𝕀" => unitInterval

variable {X : Type u} [TopologicalSpace X]

theorem IsLineWithEnds.diff_eq {L : Set X} {u v : X} {a : 𝕀 → X} (ha : IsArcMap a)
  (hr : range a = L)
    (h0 : a 0 = u) (h1 : a 1 = v) : L \ {u, v} = extI a '' Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨hx, hne⟩
    obtain ⟨t, rfl⟩ := hr.symm.subset hx
    have ht0 : (t : ℝ) ≠ 0 := fun he => hne (.inl (by rw [← h0]; exact congrArg a (Subtype.ext he)))
    have ht1 : (t : ℝ) ≠ 1 := fun he => hne (.inr (by rw [← h1]; exact congrArg a (Subtype.ext he)))
    exact ⟨t, ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0), lt_of_le_of_ne t.2.2 ht1⟩, extI_coe a t⟩
  · rintro ⟨t, ht, rfl⟩
    have hm : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    rw [extI_of_mem a hm]
    refine ⟨hr ▸ ⟨_, rfl⟩, ?_⟩
    rintro (he | he)
    · have := congrArg Subtype.val (ha.2 (he.trans h0.symm))
      exact ht.1.ne' this
    · have := congrArg Subtype.val (ha.2 (he.trans h1.symm))
      exact ht.2.ne this

theorem IsLineWithEnds.isPreconnected_diff {L : Set X} {u v : X}
  (h : IsLineWithEnds L u v) :
    IsPreconnected (L \ {u, v}) := by
  obtain ⟨a, ha, hr, h0, h1⟩ := h.exists_arc
  rw [IsLineWithEnds.diff_eq ha hr h0 h1]
  exact isPreconnected_Ioo.image _ (continuous_extI ha.1).continuousOn

theorem IsLineWithEnds.subset_closure_diff {L : Set X} {u v : X}
  (h : IsLineWithEnds L u v) :
    L ⊆ closure (L \ {u, v}) := by
  obtain ⟨a, ha, hr, h0, h1⟩ := h.exists_arc
  rw [IsLineWithEnds.diff_eq ha hr h0 h1]
  refine subset_trans ?_ (image_closure_subset_closure_image (continuous_extI ha.1))
  rw [closure_Ioo (zero_ne_one' ℝ), ← hr]
  rintro _ ⟨t, rfl⟩
  exact ⟨t, t.2, extI_coe a t⟩

variable {V : Set X} {E : Set (Set X)}

theorem IsGraph.diff_edge (_hg : IsGraph V E) {e : Set X} {u v : X} (hi : e ∩ V
  = {u, v}) : e \ {u, v} = e \ V := by
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h3 => h2 (hi ▸ ⟨h1, h3⟩)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h3 => h2 (by
      have : x ∈ e ∩ V := hi ▸ h3
      exact this.2)⟩

theorem IsGraph.isPreconnected_open (hg : IsGraph V E) {e : Set X}
  (he : e ∈ E) : IsPreconnected (e \ V) := by
  obtain ⟨u, v, -, hl, hi⟩ := hg.edge e he
  rw [← hg.diff_edge hi]
  exact hl.isPreconnected_diff

theorem IsGraph.subset_closure_open (hg : IsGraph V E) {e : Set X}
  (he : e ∈ E) : e ⊆ closure (e \ V) := by
  obtain ⟨u, v, -, hl, hi⟩ := hg.edge e he
  rw [← hg.diff_edge hi]
  exact hl.subset_closure_diff

/-- The edges inside the disc `B`. -/
def innerEdges (E : Set (Set X)) (B : Set X) : Set (Set X) := {e ∈ E | e ⊆ B ∧ ¬ e ⊆ discBd B}

/-- What we have so far: the boundary of `B` and the edges in `M`. -/
def partG (B : Set X) (M : Set (Set X)) : Set X := discBd B ∪ ⋃₀ M

section

variable [T2Space X] {B : Set X}

theorem innerEdges_open (hg : IsGraph V E) (hB : IsClosedDisc B) (hbd : discBd B ⊆ gr V E) {e : Set
  X}
    (he : e ∈ innerEdges E B) : e \ V ⊆ discInt B := by
  rcases hg.edge_or hB.isOArc_discBd hbd he.1 with h | h
  · exact absurd h he.2.2
  · exact fun x hx => ⟨he.2.1 hx.1, Set.disjoint_left.mp h hx⟩

theorem mem_innerEdges (hman : ∀ x : X, IsManifoldPoint x) (hg : IsGraph V E) (hB : IsClosedDisc B)
    (hbd : discBd B ⊆ gr V E) {e : Set X} (he : e ∈ E) {x : X} (hx : x ∈ e) (hxB : x ∈ discInt B) :
    e ∈ innerEdges E B := by
  have hnot : ¬ e ⊆ discBd B := fun h => hxB.2 (h hx)
  refine ⟨he, ?_, hnot⟩
  have hdisj := (hg.edge_or hB.isOArc_discBd hbd he).resolve_left hnot
  rcases hB.side hman (hg.isPreconnected_open he) hdisj with h | h
  · exact (hg.subset_closure_open he).trans (closure_minimal (h.trans
    (discInt_subset B)) hB.isClosed)
  · exfalso
    have hxc := hg.subset_closure_open he hx
    obtain ⟨z, hz, hz'⟩ := mem_closure_iff.mp hxc _ (hB.isOpen_discInt hman) hxB
    exact Set.disjoint_left.mp h hz' hz.1

theorem inter_partG_subset (hg : IsGraph V E) (hB : IsClosedDisc B) (hbd : discBd B ⊆ gr V E)
    {M : Set (Set X)} (hM : M ⊆ innerEdges E B) {e : Set X} (he : e ∈ innerEdges E B)
      (heM : e ∉ M) :
    e ∩ partG B M ⊆ V := by
  rintro z ⟨hz, hz' | ⟨f, hf, hzf⟩⟩
  · by_contra hzV
    exact (innerEdges_open hg hB hbd he ⟨hz, hzV⟩).2 hz'
  · exact hg.disj e he.1 f (hM hf).1 (fun h => heM (h ▸ hf)) ⟨hz, hzf⟩

omit [T2Space X] in
/-- A set that stays connected when a point is removed has no separation at a point. -/
theorem TwoConn.no_cut {G : Set X} (hG : TwoConn G) {A C : Set X} (hA : IsClosed A)
  (hC : IsClosed C)
    (hu : G ⊆ A ∪ C) (hAG : A ⊆ G) (hCG : C ⊆ G) {p : X} (hi : A ∩ C ⊆ {p}) {x y : X} (hx : x ∈ A)
      (hxp : x ≠ p)
    (hy : y ∈ C) (hyp : y ≠ p) : False := by
  obtain ⟨z, hz, hz'⟩ := isPreconnected_closed_iff.mp (hG p) A C hA hC (fun w hw => hu hw.1)
    ⟨x, ⟨hAG hx, hxp⟩, hx⟩ ⟨y, ⟨hCG hy, hyp⟩, hy⟩
  exact hz.2 (hi hz')

end

/-- A path of edges from `p`, off the set `H`. -/
inductive EarPath (p : X) (W : Set (Set X)) (H V : Set X) : Set (Set X) → X → Prop
  | one {e : Set X} {w : X} : e ∈ W → e ∩ V = {p, w} → IsLineWithEnds e p w → w ≠ p → w ∉ H
    → EarPath p W H V {e} w
  | step {A : Set (Set X)} {w w' : X} {f : Set X} : EarPath p W H V A w → f ∈ W → f ∩ V = {w, w'} →
      IsLineWithEnds f w w' → w' ≠ w → w' ∉ H → w' ∉ ⋃₀ A → EarPath p W H V (insert f A) w'

section

variable [T2Space X] {p : X} {W : Set (Set X)} {H : Set X}

theorem EarPath.facts (hWE : W ⊆ E) (hg : IsGraph V E) (hp : p ∈ H) (hW : ∀ e ∈ W, e ∩ H ⊆ V) {A :
  Set (Set X)} {w : X}
    (h : EarPath p W H V A w) :
    A ⊆ W ∧ A.Nonempty ∧ w ∈ V ∧ w ≠ p ∧ w ∉ H ∧ IsLineWithEnds (⋃₀ A) p w ∧ (⋃₀ A) ∩ H = {p} := by
  induction h with
  | @one e w he hi hl hne hn =>
    refine ⟨singleton_subset_iff.mpr he, singleton_nonempty _, ?_, hne, hn, by simpa using hl, ?_⟩
    · have : w ∈ e ∩ V := hi ▸ mem_insert_of_mem _ rfl
      exact this.2
    · rw [sUnion_singleton]
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        have : z ∈ e ∩ V := ⟨h1, hW _ he ⟨h1, h2⟩⟩
        rw [hi] at this
        rcases this with rfl | rfl
        · rfl
        · exact absurd h2 hn
      · rintro rfl
        exact ⟨hl.left_mem, hp⟩
  | @step A w w' f hA hf hi hl hne hn hnew ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih
    have hw'V : w' ∈ V := by
      have : w' ∈ f ∩ V := hi ▸ mem_insert_of_mem _ rfl
      exact this.2
    have hsU : ⋃₀ (insert f A) = ⋃₀ A ∪ f := by rw [sUnion_insert, union_comm]
    refine ⟨insert_subset hf h1, insert_nonempty _ _, hw'V, ?_, hn, ?_, ?_⟩
    · rintro rfl
      exact hnew h6.left_mem
    · rw [hsU]
      refine h6.union hl ?_
      ext z
      constructor
      · rintro ⟨⟨g, hgA, hzg⟩, hzf⟩
        have hgf : g ≠ f := fun he => hnew ⟨g, hgA, he ▸ hl.right_mem⟩
        have hzV := hg.disj g (hWE (h1 hgA)) f (hWE hf) hgf ⟨hzg, hzf⟩
        have : z ∈ f ∩ V := ⟨hzf, hzV⟩
        rw [hi] at this
        rcases this with rfl | rfl
        · rfl
        · exact absurd ⟨g, hgA, hzg⟩ hnew
      · rintro rfl
        exact ⟨h6.right_mem, hl.left_mem⟩
    · rw [hsU]
      ext z
      constructor
      · rintro ⟨h8 | h8, h9⟩
        · rw [← h7]
          exact ⟨h8, h9⟩
        · have : z ∈ f ∩ V := ⟨h8, hW f hf ⟨h8, h9⟩⟩
          rw [hi] at this
          rcases this with rfl | rfl
          · exact absurd h9 h5
          · exact absurd h9 hn
      · rintro rfl
        exact ⟨.inl h6.left_mem, hp⟩

omit [T2Space X] in
theorem EarPath.reach {A : Set (Set X)} {w : X} (h : EarPath p W H V A w) {x : X} (hxV : x ∈ V)
  (hxA : x ∈ ⋃₀ A)
    (hxp : x ≠ p) : ∃ A', EarPath p W H V A' x := by
  induction h with
  | @one e w he hi hl hne hn =>
    have h1 : x ∈ e ∩ V := ⟨by simpa using hxA, hxV⟩
    rw [hi] at h1
    rcases h1 with rfl | rfl
    · exact absurd rfl hxp
    · exact ⟨_, .one he hi hl hne hn⟩
  | @step A w w' f hA hf hi hl hne hn hnew ih =>
    rw [sUnion_insert] at hxA
    rcases hxA with h1 | h1
    · have h2 : x ∈ f ∩ V := ⟨h1, hxV⟩
      rw [hi] at h2
      rcases h2 with rfl | rfl
      · exact ⟨_, hA⟩
      · exact ⟨_, .step hA hf hi hl hne hn hnew⟩
    · exact ih h1

/-- An arc made of edges inside `B` that are not yet used, with two different ends on what we have
so far. -/
theorem exists_ear (hman : ∀ x : X, IsManifoldPoint x) (hg : IsGraph V E) (hG : TwoConn
  (⋃₀ E)) {B : Set X}
    (hB : IsClosedDisc B) (hbd : discBd B ⊆ ⋃₀ E) (hbd' : discBd B ⊆ gr V E) {M : Set (Set X)}
      (hM : M ⊆ innerEdges E B)
    (hne : ¬ innerEdges E B ⊆ M) :
    ∃ (W : Set (Set X)) (a b : X), W ⊆ innerEdges E B \ M ∧ W.Nonempty ∧ a ≠ b ∧ a ∈ V ∧ b ∈ V ∧
      IsLineWithEnds (⋃₀ W) a b ∧ (⋃₀ W) ∩ partG B M = {a, b} := by
  classical
  set W0 := innerEdges E B \ M with hW0
  set H := partG B M with hH
  have hWE : W0 ⊆ E := fun e he => he.1.1
  have hsubH : H ⊆ ⋃₀ E := union_subset hbd (sUnion_subset_sUnion fun e he => (hM he).1)
  have hW : ∀ e ∈ W0, e ∩ H ⊆ V := fun e he => inter_partG_subset hg hB hbd' hM he.1 he.2
  have hint : ∀ {e z}, e ∈ W0 → z ∈ e → z ∉ H → z ∈ discInt B := fun he hz hzH =>
    ⟨he.1.2.1 hz, fun h => hzH (.inl h)⟩
  have hclosedE : ∀ D : Set (Set X), D ⊆ E → IsClosed (⋃₀ D) := fun D hD =>
    (hg.fine.subset hD).isClosed_sUnion fun e he => by
      obtain ⟨u, v, -, hl, -⟩ := hg.edge e (hD he)
      exact hl.isCompact.isClosed
  have hHcl : IsClosed H := hB.isOArc_discBd.isCompact.isClosed.union (hclosedE M fun e he =>
    (hM he).1)
  obtain ⟨c, hc, -⟩ : ∃ c ∈ discBd B, True := by
    obtain ⟨φ⟩ := id hB.isOArc_discBd
    exact ⟨_, (φ 1).2, trivial⟩
  have hin : ∀ {e z}, e ∈ W0 → z ∈ e → z ∉ H → ∀ f ∈ E, z ∈ f → f ∈ W0 := fun he hz hzH f hf hzf =>
    ⟨mem_innerEdges hman hg hB hbd' hf hzf (hint he hz hzH), fun h => hzH (.inr ⟨f, h, hzf⟩)⟩
  -- an edge that touches what we have
  have hstart : ∃ e ∈ W0, (e ∩ H).Nonempty := by
    by_contra hcon
    push Not at hcon
    obtain ⟨e0, he0⟩ : W0.Nonempty := by
      obtain ⟨e, he, he'⟩ := not_subset.mp hne
      exact ⟨e, he, he'⟩
    obtain ⟨u, v, -, hl, -⟩ := hg.edge e0 (hWE he0)
    obtain ⟨c', hc', hcc⟩ := hB.isOArc_discBd.exists_ne c
    refine hG.no_cut (A := ⋃₀ W0) (C := H ∪ ⋃₀ (E \ W0)) (p := c) (hclosedE _ hWE)
      (hHcl.union (hclosedE _ sdiff_subset)) ?_ (sUnion_subset_sUnion hWE)
      (union_subset hsubH (sUnion_subset_sUnion sdiff_subset)) ?_ (x := u) ⟨e0, he0, hl.left_mem⟩ ?_
      (y := c') (.inl (.inl hc')) hcc
    · rintro z ⟨f, hf, hz⟩
      by_cases hfW : f ∈ W0
      · exact .inl ⟨f, hfW, hz⟩
      · exact .inr (.inr ⟨f, ⟨hf, hfW⟩, hz⟩)
    · rintro z ⟨⟨e, he, hz⟩, hz' | ⟨f, hf, hzf⟩⟩
      · exact absurd hz' (Set.eq_empty_iff_forall_notMem.mp (hcon e he) z |> fun h h' => h ⟨hz, h'⟩)
      · have hzH : z ∉ H := fun h' => Set.eq_empty_iff_forall_notMem.mp (hcon e he) z ⟨hz, h'⟩
        exact absurd (hin he hz hzH f hf.1 hzf) hf.2
    · rintro rfl
      exact Set.eq_empty_iff_forall_notMem.mp (hcon e0 he0) u ⟨hl.left_mem, .inl hc⟩
  have hat : ∀ f ∈ E, ∀ x ∈ f, x ∈ V → ∃ o, o ≠ x ∧ f ∩ V = {x, o} ∧ IsLineWithEnds f x o
    := fun f hf x hxf hxV => by
    obtain ⟨u, v, huv, hl, hi⟩ := hg.edge f hf
    have h1 : x ∈ f ∩ V := ⟨hxf, hxV⟩
    rw [hi] at h1
    rcases h1 with rfl | rfl
    · exact ⟨v, huv.symm, hi, hl⟩
    · exact ⟨u, huv, by rw [hi, pair_comm], hl.symm⟩
  obtain ⟨e0, he0, p, hpe, hpH⟩ := hstart
  have hpV : p ∈ V := hW e0 he0 ⟨hpe, hpH⟩
  obtain ⟨w, hwp, hi0, hl0⟩ := hat e0 (hWE he0) p hpe hpV
  have hwV : w ∈ V := by
    have : w ∈ e0 ∩ V := hi0 ▸ mem_insert_of_mem _ rfl
    exact this.2
  by_cases hwH : w ∈ H
  · refine ⟨{e0}, p, w, singleton_subset_iff.mpr he0, singleton_nonempty _, hwp.symm, hpV, hwV,
      by simpa using hl0, ?_⟩
    rw [sUnion_singleton]
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : z ∈ e0 ∩ V := ⟨h1, hW e0 he0 ⟨h1, h2⟩⟩
      rwa [hi0] at h3
    · rintro (rfl | rfl)
      · exact ⟨hpe, hpH⟩
      · exact ⟨hl0.right_mem, hwH⟩
  have hp0 : EarPath p W0 H V {e0} w := .one he0 hi0 hl0 hwp hwH
  by_cases hear : ∃ (A : Set (Set X)) (x : X) (f : Set X) (y : X), EarPath p W0 H V A x ∧ f ∈ W0
    ∧ f ∩ V = {x, y} ∧
      IsLineWithEnds f x y ∧ y ≠ x ∧ y ∈ H ∧ y ≠ p
  · obtain ⟨A, x, f, y, hA, hf, hi, hl, hne', hyH, hyp⟩ := hear
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hA.facts hWE hg hpH hW
    have hyV : y ∈ V := by
      have : y ∈ f ∩ V := hi ▸ mem_insert_of_mem _ rfl
      exact this.2
    have hyA : y ∉ ⋃₀ A := fun hc' => hyp (by
      have : y ∈ (⋃₀ A) ∩ H := ⟨hc', hyH⟩
      rwa [h7] at this)
    have hfA : f ∉ A := fun hc' => hyA ⟨f, hc', hl.right_mem⟩
    have hsU : ⋃₀ (insert f A) = ⋃₀ A ∪ f := by rw [sUnion_insert, union_comm]
    refine ⟨insert f A, p, y, insert_subset hf h1, insert_nonempty _ _, hyp.symm, hpV, hyV, ?_, ?_⟩
    · rw [hsU]
      refine h6.union hl ?_
      ext z
      constructor
      · rintro ⟨⟨g, hgA, hzg⟩, hzf⟩
        have hgf : g ≠ f := fun he => hfA (he ▸ hgA)
        have hzV := hg.disj g (hWE (h1 hgA)) f (hWE hf) hgf ⟨hzg, hzf⟩
        have : z ∈ f ∩ V := ⟨hzf, hzV⟩
        rw [hi] at this
        rcases this with rfl | rfl
        · rfl
        · exact absurd ⟨g, hgA, hzg⟩ hyA
      · rintro rfl
        exact ⟨h6.right_mem, hl.left_mem⟩
    · rw [hsU]
      ext z
      constructor
      · rintro ⟨h8 | h8, h9⟩
        · have : z ∈ (⋃₀ A) ∩ H := ⟨h8, h9⟩
          rw [h7] at this
          exact .inl this
        · have : z ∈ f ∩ V := ⟨h8, hW f hf ⟨h8, h9⟩⟩
          rw [hi] at this
          rcases this with rfl | rfl
          · exact absurd h9 h5
          · exact .inr rfl
      · rintro (rfl | rfl)
        · exact ⟨.inl h6.left_mem, hpH⟩
        · exact ⟨.inr hl.right_mem, hyH⟩
  push Not at hear
  exfalso
  have hstep : ∀ x f o A, EarPath p W0 H V A x → f ∈ W0 → f ∩ V = {x, o} → IsLineWithEnds f x o
    → o ≠ x →
      o = p ∨ ∃ A', EarPath p W0 H V A' o := by
    intro x f o A hA hf hi hl hox
    have hoV : o ∈ V := by
      have : o ∈ f ∩ V := hi ▸ mem_insert_of_mem _ rfl
      exact this.2
    by_cases hoH : o ∈ H
    · exact .inl (hear A x f o hA hf hi hl hox hoH)
    · have hop : o ≠ p := fun he => hoH (he ▸ hpH)
      by_cases hoA : o ∈ ⋃₀ A
      · exact .inr (hA.reach hoV hoA hop)
      · exact .inr ⟨_, .step hA hf hi hl hox hoH hoA⟩
  let WR : Set (Set X) := {f ∈ W0 | ∃ x ∈ f, ∃ A, EarPath p W0 H V A x}
  have hWRE : WR ⊆ E := fun f hf => hWE hf.1
  obtain ⟨c', hc', hcc⟩ := hB.isOArc_discBd.exists_ne p
  refine hG.no_cut (A := ⋃₀ WR) (C := H ∪ ⋃₀ (E \ WR)) (p := p) (hclosedE _ hWRE)
    (hHcl.union (hclosedE _ sdiff_subset)) ?_ (sUnion_subset_sUnion hWRE)
    (union_subset hsubH (sUnion_subset_sUnion sdiff_subset)) ?_ (x := w)
    ⟨e0, ⟨he0, w, hl0.right_mem, _, hp0⟩, hl0.right_mem⟩ hwp (y := c') (.inl (.inl hc')) hcc
  · rintro z ⟨f, hf, hz⟩
    by_cases hfW : f ∈ WR
    · exact .inl ⟨f, hfW, hz⟩
    · exact .inr (.inr ⟨f, ⟨hf, hfW⟩, hz⟩)
  · rintro z ⟨⟨e, ⟨heW, x, hxe, A, hA⟩, hz⟩, hz'⟩
    obtain ⟨-, -, hxV, -, hxH, -, -⟩ := hA.facts hWE hg hpH hW
    obtain ⟨o, hox, hi, hl⟩ := hat e (hWE heW) x hxe hxV
    have hor := hstep x e o A hA heW hi hl hox
    have hzcase : ∀ y, y ∈ e → (∃ A', EarPath p W0 H V A' y) → y = z → y ∈ ({p} : Set X) := by
      rintro y hye ⟨A', hA'⟩ rfl
      obtain ⟨-, -, -, -, hyH, -, -⟩ := hA'.facts hWE hg hpH hW
      exfalso
      rcases hz' with h1 | ⟨f, hf, hzf⟩
      · exact hyH h1
      · exact hf.2 ⟨hin heW hye hyH f hf.1 hzf, y, hzf, _, hA'⟩
    have hzV : z ∈ V := by
      rcases hz' with h1 | ⟨f, hf, hzf⟩
      · exact hW e heW ⟨hz, h1⟩
      · exact hg.disj e (hWE heW) f hf.1 (fun he => hf.2 (he ▸ ⟨heW, x, hxe, A, hA⟩)) ⟨hz, hzf⟩
    have h1 : z ∈ e ∩ V := ⟨hz, hzV⟩
    rw [hi] at h1
    rcases h1 with rfl | rfl
    · exact hzcase _ hz ⟨A, hA⟩ rfl
    · rcases hor with rfl | h2
      · rfl
      · exact hzcase _ hz h2 rfl

/-- `𝓒` cuts the disc `B` into closed discs along `H`. -/
structure IsCells (V B H : Set X) (𝓒 : Set (Set X)) : Prop where
  fin : 𝓒.Finite
  disc : ∀ Φ ∈ 𝓒, IsClosedDisc Φ
  sub : ∀ Φ ∈ 𝓒, Φ ⊆ B
  bd : ∀ Φ ∈ 𝓒, discBd Φ ⊆ H
  int : ∀ Φ ∈ 𝓒, Disjoint (discInt Φ) H
  cover : ⋃₀ 𝓒 = B
  disj : ∀ Φ ∈ 𝓒, ∀ Φ' ∈ 𝓒, Φ ≠ Φ' → Disjoint (discInt Φ) Φ'
  count : ∀ x ∉ V, {Φ ∈ 𝓒 | x ∈ Φ}.encard ≤ 2

theorem IsCells.split (hman : ∀ x : X, IsManifoldPoint x) {B H : Set X} {𝓒 : Set (Set X)}
  (h : IsCells V B H 𝓒)
    {A : Set X} {p q : X} (hpq : p ≠ q) (hl : IsLineWithEnds A p q) (hp : p ∈ V) (hq : q ∈ V)
      (hAB : A ⊆ B)
    (hA : A ∩ H = {p, q}) : ∃ 𝓒', IsCells V B (H ∪ A) 𝓒' := by
  classical
  have hpA : p ∈ A := hl.left_mem
  have hqA : q ∈ A := hl.right_mem
  have hA0 : (A \ {p, q}) ∩ H = ∅ := by
    ext z
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact absurd (hA ▸ (⟨h1, h3⟩ : z ∈ A ∩ H)) h2
    · simp
  have hdj : Disjoint (A \ {p, q}) H := Set.disjoint_iff_inter_eq_empty.mpr hA0
  have hne : (A \ {p, q}).Nonempty := by
    by_contra hc
    rw [not_nonempty_iff_eq_empty] at hc
    have h1 := hl.subset_closure_diff
    rw [hc, closure_empty] at h1
    exact h1 hpA
  obtain ⟨z, hz⟩ := hne
  have hzB : z ∈ ⋃₀ 𝓒 := h.cover ▸ hAB hz.1
  obtain ⟨Φ, hΦ, hzΦ⟩ := hzB
  have hdΦ := h.disc Φ hΦ
  have hside : A \ {p, q} ⊆ discInt Φ := by
    rcases hdΦ.side hman hl.isPreconnected_diff (hdj.mono_right (h.bd Φ hΦ)) with h1 | h1
    · exact h1
    · exact absurd hzΦ (Set.disjoint_left.mp h1 hz)
  have hAΦ : A ⊆ Φ := hl.subset_closure_diff.trans
    (closure_minimal (hside.trans (discInt_subset Φ)) hdΦ.isClosed)
  have hH : ∀ {y}, y ∈ A ∩ H → y ∈ discBd Φ := fun {y} hy => by
    by_contra hc
    exact Set.disjoint_left.mp (h.int Φ hΦ) (⟨hAΦ hy.1, hc⟩ : y ∈ discInt Φ) hy.2
  have hmemp : p ∈ A ∩ H := hA ▸ mem_insert _ _
  have hmemq : q ∈ A ∩ H := hA ▸ mem_insert_of_mem _ rfl
  have hAbd : A ∩ discBd Φ = {p, q} := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hc
      exact (hside ⟨h1, hc⟩).2 h2
    · rintro (rfl | rfl)
      · exact ⟨hpA, hH hmemp⟩
      · exact ⟨hqA, hH hmemq⟩
  obtain ⟨A₁, A₂, Δ₁, Δ₂, -, hc, hd1, hd2, hun, hin, hb1, hb2, -⟩ := disc_iArc.{u} Φ A p q hdΦ hAΦ
    hpq hl hAbd
  have hA1 : A₁ ⊆ discBd Φ := by
    have : A₁ ∈ componentsIn (discBd Φ \ {p, q}) := hc ▸ mem_insert _ _
    obtain ⟨y, hy, rfl⟩ := this
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  have hA2 : A₂ ⊆ discBd Φ := by
    have : A₂ ∈ componentsIn (discBd Φ \ {p, q}) := hc ▸ mem_insert_of_mem _ rfl
    obtain ⟨y, hy, rfl⟩ := this
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  have h1Φ : Δ₁ ⊆ Φ := hun ▸ subset_union_left
  have h2Φ : Δ₂ ⊆ Φ := hun ▸ subset_union_right
  have hi1 : discInt Δ₁ ⊆ discInt Φ := discInt_mono hman hd1 h1Φ
  have hi2 : discInt Δ₂ ⊆ discInt Φ := discInt_mono hman hd2 h2Φ
  have hI1 : Disjoint (discInt Δ₁) A := Set.disjoint_left.mpr fun y hy hy' => hy.2 (hb1 ▸ .inr hy')
  have hI2 : Disjoint (discInt Δ₂) A := Set.disjoint_left.mpr fun y hy hy' => hy.2 (hb2 ▸ .inr hy')
  have hHΦ : discBd Φ ⊆ H := h.bd Φ hΦ
  have hIH : Disjoint (discInt Φ) H := h.int Φ hΦ
  have holdne : ∀ Ψ ∈ 𝓒 \ {Φ}, Φ ≠ Ψ := fun Ψ hΨ he => hΨ.2 he.symm
  refine ⟨insert Δ₁ (insert Δ₂ (𝓒 \ {Φ})), ⟨((h.fin.sdiff).insert _).insert _, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩⟩
  · rintro Ψ (rfl | rfl | hΨ)
    · exact hd1
    · exact hd2
    · exact h.disc Ψ hΨ.1
  · rintro Ψ (rfl | rfl | hΨ)
    · exact h1Φ.trans (h.sub Φ hΦ)
    · exact h2Φ.trans (h.sub Φ hΦ)
    · exact h.sub Ψ hΨ.1
  · rintro Ψ (rfl | rfl | hΨ)
    · rw [hb1]
      exact union_subset_union_left _ (hA1.trans hHΦ)
    · rw [hb2]
      exact union_subset_union_left _ (hA2.trans hHΦ)
    · exact (h.bd Ψ hΨ.1).trans subset_union_left
  · rintro Ψ (rfl | rfl | hΨ)
    · exact Set.disjoint_union_right.mpr ⟨hIH.mono_left hi1, hI1⟩
    · exact Set.disjoint_union_right.mpr ⟨hIH.mono_left hi2, hI2⟩
    · exact Set.disjoint_union_right.mpr ⟨h.int Ψ hΨ.1,
        (h.disj Ψ hΨ.1 Φ hΦ (holdne Ψ hΨ).symm).mono_right hAΦ⟩
  · ext y
    constructor
    · rintro ⟨Ψ, rfl | rfl | hΨ, hy⟩
      · exact h.cover ▸ ⟨Φ, hΦ, h1Φ hy⟩
      · exact h.cover ▸ ⟨Φ, hΦ, h2Φ hy⟩
      · exact h.cover ▸ ⟨Ψ, hΨ.1, hy⟩
    · intro hy
      rw [← h.cover] at hy
      obtain ⟨Ψ, hΨ, hyΨ⟩ := hy
      by_cases hΨΦ : Ψ = Φ
      · subst hΨΦ
        rw [← hun] at hyΨ
        rcases hyΨ with h3 | h3
        · exact ⟨Δ₁, .inl rfl, h3⟩
        · exact ⟨Δ₂, .inr (.inl rfl), h3⟩
      · exact ⟨Ψ, .inr (.inr ⟨hΨ, hΨΦ⟩), hyΨ⟩
  · have h12 : Disjoint (discInt Δ₁) Δ₂ := Set.disjoint_left.mpr fun y hy hy' =>
      Set.disjoint_left.mp hI1 hy (hin ▸ (⟨hy.1, hy'⟩ : y ∈ Δ₁ ∩ Δ₂))
    have h21 : Disjoint (discInt Δ₂) Δ₁ := Set.disjoint_left.mpr fun y hy hy' =>
      Set.disjoint_left.mp hI2 hy (hin ▸ (⟨hy', hy.1⟩ : y ∈ Δ₁ ∩ Δ₂))
    rintro Ψ (rfl | rfl | hΨ) Ψ' (rfl | rfl | hΨ') hne
    · exact absurd rfl hne
    · exact h12
    · exact (h.disj Φ hΦ Ψ' hΨ'.1 (holdne Ψ' hΨ')).mono_left hi1
    · exact h21
    · exact absurd rfl hne
    · exact (h.disj Φ hΦ Ψ' hΨ'.1 (holdne Ψ' hΨ')).mono_left hi2
    · exact (h.disj Ψ hΨ.1 Φ hΦ (holdne Ψ hΨ).symm).mono_right h1Φ
    · exact (h.disj Ψ hΨ.1 Φ hΦ (holdne Ψ hΨ).symm).mono_right h2Φ
    · exact h.disj Ψ hΨ.1 Ψ' hΨ'.1 hne
  · intro x hxV
    by_cases hxA : x ∈ A
    · have hxi : x ∈ discInt Φ := hside ⟨hxA, by
        rintro (rfl | rfl)
        · exact hxV hp
        · exact hxV hq⟩
      have hsub : {Ψ ∈ insert Δ₁ (insert Δ₂ (𝓒 \ {Φ})) | x ∈ Ψ} ⊆ {Δ₁, Δ₂} := by
        rintro Ψ ⟨rfl | rfl | hΨ, hx⟩
        · exact .inl rfl
        · exact .inr rfl
        · exact absurd hx (Set.disjoint_left.mp (h.disj Φ hΦ Ψ hΨ.1 (holdne Ψ hΨ)) hxi)
      refine (encard_le_encard hsub).trans ((encard_insert_le _ _).trans ?_)
      rw [encard_singleton]
      norm_num
    · let σ : Set X → Set X := fun Ψ => if Ψ = Φ then (if x ∈ Δ₁ then Δ₁ else Δ₂) else Ψ
      have hsub : {Ψ ∈ insert Δ₁ (insert Δ₂ (𝓒 \ {Φ})) | x ∈ Ψ} ⊆ σ '' {Ψ ∈ 𝓒 | x ∈ Ψ} := by
        rintro Ψ ⟨hm, hx⟩
        rcases hm with e | e | hΨ
        · rw [e] at hx ⊢
          exact ⟨Φ, ⟨hΦ, h1Φ hx⟩, by simp [σ, hx]⟩
        · rw [e] at hx ⊢
          have hn1 : x ∉ Δ₁ := fun h3 => hxA (hin ▸ (⟨h3, hx⟩ : x ∈ Δ₁ ∩ Δ₂))
          exact ⟨Φ, ⟨hΦ, h2Φ hx⟩, by simp [σ, hn1]⟩
        · have hne' : Ψ ≠ Φ := hΨ.2
          exact ⟨Ψ, ⟨hΨ.1, hx⟩, by simp [σ, hne']⟩
      exact (encard_le_encard hsub).trans (encard_image_le _ _ |>.trans (h.count x hxV))

theorem exists_cells_aux (hman : ∀ x : X, IsManifoldPoint x) (hg : IsGraph V E) (hG : TwoConn
  (⋃₀ E)) {B : Set X}
    (hB : IsClosedDisc B) (hbd : discBd B ⊆ ⋃₀ E) (hbd' : discBd B ⊆ gr V E) (n : ℕ) :
    ∀ (M : Set (Set X)) (𝓒 : Set (Set X)), M ⊆ innerEdges E B → (innerEdges E B \ M).ncard = n →
      IsCells V B (partG B M) 𝓒 → ∃ 𝓒', IsCells V B (partG B (innerEdges E B)) 𝓒' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M 𝓒 hM hn hc
  by_cases hne : innerEdges E B ⊆ M
  · have e := subset_antisymm hne hM
    rw [← e] at hc
    exact ⟨𝓒, hc⟩
  obtain ⟨W, a, b, hW, hWne, hab, ha, hb, hl, hi⟩ := exists_ear hman hg hG hB hbd hbd' hM hne
  have hfin : (innerEdges E B).Finite := hg.fine.subset fun e he => he.1
  have hWB : ⋃₀ W ⊆ B := sUnion_subset fun e he => (hW he).1.2.1
  obtain ⟨𝓒', hc'⟩ := hc.split hman hab hl ha hb hWB hi
  have hpart : partG B M ∪ ⋃₀ W = partG B (M ∪ W) := by
    simp only [partG, sUnion_union, union_assoc]
  rw [hpart] at hc'
  refine ih _ ?_ (M ∪ W) 𝓒' (union_subset hM fun e he => (hW he).1) rfl hc'
  rw [← hn]
  refine ncard_lt_ncard ?_ (hfin.subset sdiff_subset)
  obtain ⟨e, he⟩ := hWne
  refine ⟨fun f hf => ⟨hf.1, fun h3 => hf.2 (.inl h3)⟩, fun hc2 => ?_⟩
  have := hc2 (hW he)
  exact this.2 (.inr he)

/-- A chart disc is cut into closed discs along a graph that stays connected when a point is
removed. -/
theorem exists_cells (hman : ∀ x : X, IsManifoldPoint x) (hg : IsGraph V E) (hG : TwoConn
  (⋃₀ E)) {B : Set X}
    (hB : IsClosedDisc B) (hbd : discBd B ⊆ ⋃₀ E) (hbd' : discBd B ⊆ gr V E) :
    ∃ 𝓒, IsCells V B (⋃₀ E) 𝓒 := by
  have hpe : partG B (∅ : Set (Set X)) = discBd B := by simp [partG]
  have hstart : IsCells V B (partG B ∅) {B} := by
    rw [hpe]
    refine ⟨finite_singleton _, ?_, ?_, ?_, ?_, sUnion_singleton _, ?_, fun x _ => ?_⟩
    · rintro _ rfl
      exact hB
    · rintro _ rfl
      exact subset_rfl
    · rintro _ rfl
      exact subset_rfl
    · rintro _ rfl
      exact Set.disjoint_left.mpr fun y hy => hy.2
    · rintro _ rfl _ rfl hne
      exact absurd rfl hne
    · refine (encard_le_encard (sep_subset _ _)).trans ?_
      rw [encard_singleton]
      norm_num
  obtain ⟨𝓒, hc⟩ := exists_cells_aux hman hg hG hB hbd hbd' _ ∅ {B} (empty_subset _) rfl hstart
  refine ⟨𝓒, hc.fin, hc.disc, hc.sub, fun Φ hΦ => (hc.bd Φ hΦ).trans
    (union_subset hbd (sUnion_subset_sUnion fun e he => he.1)), fun Φ hΦ
      => ?_, hc.cover, hc.disj, hc.count⟩
  rw [Set.disjoint_left]
  rintro z hz ⟨e, he, hze⟩
  have hzB : z ∈ B := hc.sub Φ hΦ hz.1
  have hnH : z ∉ partG B (innerEdges E B) := Set.disjoint_left.mp (hc.int Φ hΦ) hz
  have hzi : z ∈ discInt B := ⟨hzB, fun h3 => hnH (.inl h3)⟩
  exact hnH (.inr ⟨e, mem_innerEdges hman hg hB hbd' he hze hzi, hze⟩)

end

end GraphMinor.Surface
