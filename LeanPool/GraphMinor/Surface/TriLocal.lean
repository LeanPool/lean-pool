/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Triangulate
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Local structure of a triangulation

We read off the combinatorics of a triangulation of a connected closed surface (`IsTriang`): each
edge lies in exactly two faces, each face has three edges, two vertices of a face are joined by an
edge of the face, the graph is connected, faces are connected through common edges, and the faces at
a vertex are connected through common edges at the vertex. The topological inputs are that a
connected open set of a surface stays connected when a point is removed, and that a surface has no
boundary point.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

local notation "𝕀" => unitInterval

variable {X : Type} [TopologicalSpace X]

theorem punctured_unit_ball : IsPreconnected (ball (0 : ℂ) 1 \ {0}) := by
  have hs : IsPreconnected (sphere (0 : ℂ) 1) := isPreconnected_sphere (by
    rw [Complex.rank_real_complex]
    norm_num) 0 1
  have h1 : IsPreconnected (Ioo (0 : ℝ) 1 ×ˢ sphere (0 : ℂ) 1) := isPreconnected_Ioo.prod hs
  have h2 := h1.image (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) (by fun_prop)
  convert h2 using 1
  ext x
  constructor
  · rintro ⟨h3, h4⟩
    have h5 : x ≠ 0 := h4
    have h6 : 0 < ‖x‖ := norm_pos_iff.mpr h5
    refine ⟨(‖x‖, x / ‖x‖), ⟨⟨h6, by simpa using h3⟩, ?_⟩, ?_⟩
    · simp [h6.ne']
    · have : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast h6.ne'
      simp only
      field_simp
  · rintro ⟨⟨r, z⟩, ⟨h3, h4⟩, rfl⟩
    have h5 : ‖z‖ = 1 := by simpa using h4
    have h6 : (r : ℂ) ≠ 0 := by exact_mod_cast h3.1.ne'
    have h7 : z ≠ 0 := fun h => by simp [h] at h5
    constructor
    · simp [h5, abs_of_pos h3.1, h3.2]
    · simp [h6, h7]

theorem BallChart.isPreconnected_punctured {U : Set X} {h : X → ℂ} {g : ℂ → X}
  (c : BallChart 1 U h g) :
    IsPreconnected (U \ {g 0}) := by
  have h1 := punctured_unit_ball.image g (c.gc.mono sdiff_subset)
  convert h1 using 1
  ext x
  constructor
  · rintro ⟨h2, h3⟩
    refine ⟨h x, ⟨c.hm h2, fun h4 => h3 ?_⟩, c.gh h2⟩
    rw [← c.gh h2, show h x = 0 from h4]
    rfl
  · rintro ⟨y, ⟨h2, h3⟩, rfl⟩
    refine ⟨c.gm h2, fun h4 => h3 ?_⟩
    have h5 := c.hg h2
    rw [show g y = g 0 from h4, c.hg (by simp)] at h5
    exact h5.symm

/-- A boundary point of a closed disc in a closed surface is a limit of points outside the disc. -/
theorem not_nhds_of_mem_discBd {Φ W : Set X} {x : X} (hi : IsInteriorPoint x) (hx : x ∈ discBd Φ)
  (hW : IsOpen W)
    (hxW : x ∈ W) (hWΦ : W ⊆ Φ) : False := by
  obtain ⟨⟨y, hxΦ⟩, hb, rfl⟩ := hx
  apply hb
  obtain ⟨U, hU, hyU, hsub, ⟨f⟩⟩ := hi.exists_subset hW hxW
  refine ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hyU, ⟨?_⟩⟩
  refine Homeomorph.trans ?_ f
  exact
    { toFun := fun z => ⟨z.1.1, z.2⟩
      invFun := fun z => ⟨⟨z.1, hWΦ (hsub z.2)⟩, z.2⟩
      left_inv := fun z => rfl
      right_inv := fun z => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

variable [T2Space X]

/-- Removing a point from a connected open set of a closed surface leaves a connected set. -/
theorem IsPreconnected.diff_point (hT : IsClosedSurface X) {U : Set X} (hU : IsPreconnected U)
  (hUo : IsOpen U) (p : X) :
    IsPreconnected (U \ {p}) := by
  by_cases hp : p ∈ U
  swap
  · rwa [sdiff_singleton_eq_self hp]
  obtain ⟨B, h, g, c, hBU, hg0⟩ := (hT.2.2 p).exists_ballChart hUo hp (R := 1) one_pos
  have hpc := c.isPreconnected_punctured
  rw [hg0] at hpc
  have hpB : p ∈ B := hg0 ▸ c.gm (by simp)
  rw [isPreconnected_iff_subset_of_disjoint] at hU ⊢
  intro A A' hA hA' hcov hd
  have hopen : IsOpen (U \ {p}) := hUo.sdiff isClosed_singleton
  have hAo := hA.inter hopen
  have hAo' := hA'.inter hopen
  have hcase : B \ {p} ⊆ A ∨ B \ {p} ⊆ A' := by
    refine isPreconnected_iff_subset_of_disjoint.mp hpc A A' hA hA' ((sdiff_subset_sdiff_left
      hBU).trans hcov) ?_
    refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
    have : y ∈ (U \ {p}) ∩ (A ∩ A') := ⟨⟨hBU hy.1.1, hy.1.2⟩, hy.2⟩
    rw [hd] at this
    exact this
  have main : ∀ {A A' : Set X}, IsOpen A → IsOpen A' → U \ {p} ⊆ A ∪ A' → (U \ {p}) ∩ (A ∩ A') = ∅
    → B \ {p} ⊆ A →
      U \ {p} ⊆ A ∨ U \ {p} ⊆ A' := by
    intro A A' hA hA' hcov hd hB
    have h1 := hU ((A ∩ (U \ {p})) ∪ B) (A' ∩ (U \ {p})) ((hA.inter hopen).union c.isOpen)
      (hA'.inter hopen) (fun y hy => by
      by_cases hyp : y = p
      · exact .inl (.inr (hyp ▸ hpB))
      · rcases hcov ⟨hy, hyp⟩ with h2 | h2
        · exact .inl (.inl ⟨h2, hy, hyp⟩)
        · exact .inr ⟨h2, hy, hyp⟩) (by
      refine Set.eq_empty_iff_forall_notMem.mpr ?_
      rintro y ⟨-, h2 | h2, ⟨h3, h4⟩⟩
      · have : y ∈ (U \ {p}) ∩ (A ∩ A') := ⟨h4, h2.1, h3⟩
        rw [hd] at this
        exact this
      · have h5 : y ∈ A := hB ⟨h2, h4.2⟩
        have : y ∈ (U \ {p}) ∩ (A ∩ A') := ⟨h4, h5, h3⟩
        rw [hd] at this
        exact this)
    rcases h1 with h1 | h1
    · left
      intro y hy
      rcases h1 hy.1 with h2 | h2
      · exact h2.1
      · exact hB ⟨h2, hy.2⟩
    · right
      intro y hy
      exact (h1 hy.1).1
  rcases hcase with h1 | h1
  · exact main hA hA' hcov hd h1
  · rcases main hA' hA (by rwa [union_comm]) (by rwa [inter_comm A']) h1 with h2 | h2
    · exact .inr h2
    · exact .inl h2

/-- A connected closed surface stays connected when finitely many points are removed. -/
theorem isPreconnected_compl_finite (hT : IsClosedSurface X) [ConnectedSpace X] {P : Set X}
  (hP : P.Finite) :
    IsPreconnected Pᶜ := by
  induction P, hP using Set.Finite.induction_on with
  | empty => simpa using isPreconnected_univ
  | @insert a s _ hs ih =>
    have h1 := IsPreconnected.diff_point hT ih hs.isClosed.isOpen_compl a
    convert h1 using 1
    ext y
    simp only [mem_compl_iff, mem_insert_iff, not_or, mem_sdiff, mem_singleton_iff]
    tauto

namespace IsTriang

variable {V : Set X} {E 𝓕 : Set (Set X)}

omit [T2Space X] in
theorem mem_bd (h : IsTriang V E 𝓕) {Φ : Set X} (hΦ : Φ ∈ 𝓕) {y : X} (hy : y ∈ Φ)
  (hyE : y ∈ ⋃₀ E) : y ∈ discBd Φ := by
  by_contra hn
  exact Set.disjoint_left.mp (h.dis.int Φ hΦ) ⟨hy, hn⟩ hyE

omit [T2Space X] in
theorem mem_bd_of_ne (h : IsTriang V E 𝓕) {Φ Φ' : Set X} (hΦ : Φ ∈ 𝓕) (hΦ' : Φ' ∈ 𝓕)
  (hne : Φ ≠ Φ') {y : X} (hy : y ∈ Φ)
    (hy' : y ∈ Φ') : y ∈ discBd Φ := by
  by_contra hn
  exact Set.disjoint_left.mp (h.dis.disj Φ hΦ Φ' hΦ' hne) ⟨hy, hn⟩ hy'

/-- A face that contains an inner point of an edge has this edge on its boundary. -/
theorem edge_sub (h : IsTriang V E 𝓕) {e Φ : Set X} (he : e ∈ E) (hΦ : Φ ∈ 𝓕) {x : X} (hxe : x ∈ e)
  (hxV : x ∉ V) (hxΦ : x ∈ Φ) :
    e ⊆ discBd Φ := by
  have hb := h.mem_bd hΦ hxΦ ⟨e, he, hxe⟩
  have hO := (h.dis.disc Φ hΦ).isOArc_discBd
  rcases h.dis.graph.edge_or hO ((h.dis.bd Φ hΦ).trans subset_union_right) he with h1 | h1
  · exact h1
  · exact absurd hb (Set.disjoint_left.mp h1 ⟨hxe, hxV⟩)

omit [T2Space X] in
theorem exists_inner (h : IsTriang V E 𝓕) {e : Set X} (he : e ∈ E) : ∃ x ∈ e, x ∉ V := by
  obtain ⟨u, v, huv, hl, hi⟩ := h.dis.graph.edge e he
  have h2 := hl.subset_closure_diff
  have hne : (e \ {u, v}).Nonempty := by
    by_contra hc
    rw [not_nonempty_iff_eq_empty] at hc
    rw [hc, closure_empty] at h2
    exact h2 hl.left_mem
  obtain ⟨x, hx, hn⟩ := hne
  exact ⟨x, hx, fun hV => hn (hi ▸ ⟨hx, hV⟩)⟩

omit [T2Space X] in
theorem ends_ncard (h : IsTriang V E 𝓕) {e : Set X} (he : e ∈ E) : (e ∩ V).ncard = 2 := by
  obtain ⟨u, v, huv, -, hi⟩ := h.dis.graph.edge e he
  rw [hi, ncard_pair huv]

/-- Two vertices of a face are joined by an edge on the boundary of the face. -/
theorem face_pair (h : IsTriang V E 𝓕) {Φ : Set X} (hΦ : Φ ∈ 𝓕) {a b : X} (ha : a ∈ Φ ∩ V)
  (hb : b ∈ Φ ∩ V) (hab : a ≠ b) :
    ∃ e ∈ E, e ⊆ discBd Φ ∧ e ∩ V = {a, b} := by
  classical
  have hfinV := h.dis.graph.fin
  have hVb : ∀ y ∈ Φ ∩ V, y ∈ discBd Φ := fun y hy => h.mem_bd hΦ hy.1 (h.cov hy.2)
  have h3 := h.three Φ hΦ
  have hsub : ({a, b} : Set X) ⊆ Φ ∩ V := insert_subset ha (singleton_subset_iff.mpr hb)
  have hc1 : ((Φ ∩ V) \ {a, b}).ncard = 1 := by
    rw [ncard_sdiff hsub (Set.toFinite _), h3, ncard_pair hab]
  obtain ⟨c, hc⟩ := ncard_eq_one.mp hc1
  have hcm : c ∈ (Φ ∩ V) \ {a, b} := hc ▸ rfl
  have hall : ∀ y ∈ Φ ∩ V, y = a ∨ y = b ∨ y = c := fun y hy => by
    by_cases h1 : y = a ∨ y = b
    · rcases h1 with h1 | h1
      · exact .inl h1
      · exact .inr (.inl h1)
    · have : y ∈ (Φ ∩ V) \ {a, b} := ⟨hy, h1⟩
      rw [hc] at this
      exact .inr (.inr this)
  obtain ⟨a₁, a₂, hTwo, h0, h1, hu⟩ := (h.dis.disc Φ hΦ).isOArc_discBd.exists_arcs (hVb a ha)
    (hVb b hb) hab
  have hl₁ : IsLineWithEnds (range a₁) a b := by
    have := hTwo.arc_left.isLineWithEnds
    rwa [h0, h1] at this
  have hl₂ : IsLineWithEnds (range a₂) a b := by
    have := hTwo.arc_right.isLineWithEnds
    rwa [hTwo.zero, hTwo.one, h0, h1] at this
  have hinter : range a₁ ∩ range a₂ = {a, b} := by
    rw [hTwo.inter, h0, h1]
  have main : ∀ {L L' : Set X}, IsLineWithEnds L a b → L ∪ L' = discBd Φ → L ∩ L' = {a, b}
    → IsClosed L' → c ∉ L →
      ∃ e ∈ E, e ⊆ discBd Φ ∧ e ∩ V = {a, b} := by
    intro L L' hL hLu hLi hL' hcL
    have hne : (L \ {a, b}).Nonempty := by
      by_contra hc'
      rw [not_nonempty_iff_eq_empty] at hc'
      have h2 := hL.subset_closure_diff
      rw [hc', closure_empty] at h2
      exact h2 hL.left_mem
    obtain ⟨x, hx, hxn⟩ := hne
    have hxb : x ∈ discBd Φ := hLu ▸ .inl hx
    have hxV : x ∉ V := fun hV => by
      rcases hall x ⟨discBd_subset Φ hxb, hV⟩ with h2 | h2 | h2
      · exact hxn (.inl h2)
      · exact hxn (.inr h2)
      · exact hcL (h2 ▸ hx)
    obtain ⟨e, he, hxe⟩ := h.dis.bd Φ hΦ hxb
    have hes := h.edge_sub he hΦ hxe hxV (discBd_subset Φ hxb)
    obtain ⟨u, v, huv, hl, hi⟩ := h.dis.graph.edge e he
    have hdiff : e \ {u, v} ⊆ L := by
      have hp : IsPreconnected (e \ {u, v}) := hl.isPreconnected_diff
      by_contra hns
      obtain ⟨y, hy, hyL⟩ := not_subset.mp hns
      have hxe' : x ∈ e \ {u, v} := ⟨hxe, fun h2 => hxV (hi ▸ h2 |> fun h3 : x ∈ e ∩ V => h3.2)⟩
      have hyL' : y ∈ L' := by
        have : y ∈ L ∪ L' := hLu ▸ hes hy.1
        exact this.resolve_left hyL
      obtain ⟨z, hz, hz1, hz2⟩ := isPreconnected_closed_iff.mp hp L L' hL.isCompact.isClosed hL'
        (fun w hw => by
        have : w ∈ discBd Φ := hes hw.1
        rwa [← hLu] at this) ⟨x, hxe', hx⟩ ⟨y, hy, hyL'⟩
      have hzab : z ∈ L ∩ L' := ⟨hz1, hz2⟩
      rw [hLi] at hzab
      have hzV : z ∈ V := by
        rcases hzab with rfl | rfl
        · exact ha.2
        · exact hb.2
      exact hz.2 (hi ▸ (⟨hz.1, hzV⟩ : z ∈ e ∩ V))
    have hesL : e ⊆ L := hl.subset_closure_diff.trans (closure_minimal hdiff hL.isCompact.isClosed)
    refine ⟨e, he, hes, ?_⟩
    have hs : e ∩ V ⊆ {a, b} := by
      rintro y ⟨h2, h3⟩
      rcases hall y ⟨discBd_subset Φ (hes h2), h3⟩ with h4 | h4 | h4
      · exact .inl h4
      · exact .inr h4
      · exact absurd (h4 ▸ hesL h2) hcL
    exact eq_of_subset_of_ncard_le hs (by rw [ncard_pair hab, h.ends_ncard he]) (by simp)
  by_cases hcl : c ∈ range a₁
  · have hcl₂ : c ∉ range a₂ := fun h2 => hcm.2 (hinter ▸ ⟨hcl, h2⟩)
    exact main hl₂ (by rw [union_comm, hu]) (by rw [inter_comm, hinter]) hl₁.isCompact.isClosed hcl₂
  · exact main hl₁ hu hinter hl₂.isCompact.isClosed hcl

/-- An edge lies in a face as soon as its two ends do. -/
theorem sub_iff (h : IsTriang V E 𝓕) {e Φ : Set X} (he : e ∈ E) (hΦ : Φ ∈ 𝓕) : e ⊆ Φ ↔ e ∩ V ⊆ Φ
  := by
  refine ⟨fun h1 => inter_subset_left.trans h1, fun h1 => ?_⟩
  obtain ⟨u, v, huv, -, hi⟩ := h.dis.graph.edge e he
  have hu : u ∈ e ∩ V := hi ▸ .inl rfl
  have hv : v ∈ e ∩ V := hi ▸ .inr rfl
  obtain ⟨f, hf, h2, h3⟩ := h.face_pair hΦ ⟨h1 hu, hu.2⟩ ⟨h1 hv, hv.2⟩ huv
  rw [h.simple e he f hf (hi.trans h3.symm)]
  exact h2.trans (discBd_subset Φ)

/-- Each edge lies in exactly two faces. The second face exists because a surface has no boundary
point. -/
theorem two_faces (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) {e : Set X}
  (he : e ∈ E) : {Φ ∈ 𝓕 | e ⊆ Φ}.ncard = 2 := by
  classical
  obtain ⟨x, hxe, hxV⟩ := h.exists_inner he
  have hcov : ∀ y : X, ∃ Φ ∈ 𝓕, y ∈ Φ := fun y => by
    have : y ∈ ⋃₀ 𝓕 := h.dis.cover ▸ mem_univ y
    exact this
  have hle : {Φ ∈ 𝓕 | e ⊆ Φ}.encard ≤ 2 := by
    have hs : {Φ ∈ 𝓕 | e ⊆ Φ} ⊆ {Φ ∈ 𝓕 | x ∈ Φ} := fun Φ hΦ => ⟨hΦ.1, hΦ.2 hxe⟩
    exact (encard_le_encard hs).trans (h.dis.count x hxV)
  obtain ⟨Φ₁, h1, hx1⟩ := hcov x
  have hb := h.mem_bd h1 hx1 ⟨e, he, hxe⟩
  have hs1 := (h.edge_sub he h1 hxe hxV hx1).trans (discBd_subset Φ₁)
  obtain ⟨Φ₂, h2, hx2, hne⟩ : ∃ Φ₂ ∈ 𝓕, x ∈ Φ₂ ∧ Φ₂ ≠ Φ₁ := by
    by_contra hc
    push Not at hc
    let W : Set X := (⋃₀ (𝓕 \ {Φ₁}))ᶜ
    have hWo : IsOpen W := by
      have h5 : IsClosed (⋃₀ (𝓕 \ {Φ₁})) :=
        (h.dis.fin.subset sdiff_subset).isClosed_sUnion fun Φ hΦ => (h.dis.disc Φ hΦ.1).isClosed
      exact h5.isOpen_compl
    have hxW : x ∈ W := by
      rintro ⟨Φ, hΦ, h3⟩
      exact hΦ.2 (hc Φ hΦ.1 h3)
    have hWs : W ⊆ Φ₁ := fun y hy => by
      obtain ⟨Φ, hΦ, h3⟩ := hcov y
      by_cases h4 : Φ = Φ₁
      · exact h4 ▸ h3
      · exact absurd ⟨Φ, ⟨hΦ, h4⟩, h3⟩ hy
    exact not_nhds_of_mem_discBd (hT.2.2 x) hb hWo hxW hWs
  have hs2 := (h.edge_sub he h2 hxe hxV hx2).trans (discBd_subset Φ₂)
  have hsub : ({Φ₁, Φ₂} : Set (Set X)) ⊆ {Φ ∈ 𝓕 | e ⊆ Φ} := by
    rintro Φ (rfl | rfl)
    · exact ⟨h1, hs1⟩
    · exact ⟨h2, hs2⟩
  have hf : {Φ ∈ 𝓕 | e ⊆ Φ}.Finite := h.dis.fin.subset fun Φ hΦ => hΦ.1
  have h3 : (2 : ℕ∞) ≤ {Φ ∈ 𝓕 | e ⊆ Φ}.encard := by
    have := encard_le_encard hsub
    rwa [encard_pair (Ne.symm hne)] at this
  have h4 : {Φ ∈ 𝓕 | e ⊆ Φ}.encard = 2 := le_antisymm hle h3
  rw [← hf.cast_ncard_eq] at h4
  exact_mod_cast h4

/-- The graph of a triangulation of a connected surface is connected. -/
theorem graph_conn (h : IsTriang V E 𝓕) [ConnectedSpace X] {S : Set X}
  (hS : ∀ e ∈ E, ∀ a ∈ e ∩ V, ∀ b ∈ e ∩ V, a ∈ S → b ∈ S)
    (hne : (S ∩ V).Nonempty) : V ⊆ S := by
  classical
  have hcov : ∀ y : X, ∃ Φ ∈ 𝓕, y ∈ Φ := fun y => by
    have : y ∈ ⋃₀ 𝓕 := h.dis.cover ▸ mem_univ y
    exact this
  have hsame : ∀ Φ ∈ 𝓕, ∀ a ∈ Φ ∩ V, ∀ b ∈ Φ ∩ V, a ∈ S → b ∈ S := fun Φ hΦ a ha b hb has => by
    by_cases hab : a = b
    · exact hab ▸ has
    obtain ⟨e, he, -, hi⟩ := h.face_pair hΦ ha hb hab
    exact hS e he a (hi ▸ .inl rfl) b (hi ▸ .inr rfl) has
  let 𝓐 : Set (Set X) := {Φ ∈ 𝓕 | ∃ a ∈ Φ ∩ V, a ∈ S}
  let 𝓑 : Set (Set X) := 𝓕 \ 𝓐
  have hdis : Disjoint (⋃₀ 𝓐) (⋃₀ 𝓑) := Set.disjoint_left.mpr fun x ⟨Φ, hΦ, hx⟩ ⟨Φ', hΦ', hx'⟩ => by
    have hne : Φ ≠ Φ' := fun h1 => hΦ'.2 (h1 ▸ hΦ)
    obtain ⟨a, ha, has⟩ := hΦ.2
    have hb := h.mem_bd_of_ne hΦ.1 hΦ'.1 hne hx hx'
    obtain ⟨e, he, hxe⟩ := h.dis.bd Φ hΦ.1 hb
    by_cases hxV : x ∈ V
    · exact hΦ'.2 ⟨hΦ'.1, x, ⟨hx', hxV⟩, hsame Φ hΦ.1 a ha x ⟨hx, hxV⟩ has⟩
    · have h1 := (h.edge_sub he hΦ.1 hxe hxV hx).trans (discBd_subset Φ)
      have h2 := (h.edge_sub he hΦ'.1 hxe hxV hx').trans (discBd_subset Φ')
      obtain ⟨u, v, -, hl, hi⟩ := h.dis.graph.edge e he
      have hu : u ∈ e ∩ V := hi ▸ .inl rfl
      exact hΦ'.2 ⟨hΦ'.1, u, ⟨h2 hu.1, hu.2⟩, hsame Φ hΦ.1 a ha u ⟨h1 hu.1, hu.2⟩ has⟩
  have hA : IsClosed (⋃₀ 𝓐) :=
    (h.dis.fin.subset (show 𝓐 ⊆ 𝓕 from fun _ hΦ => hΦ.1)).isClosed_sUnion
      fun Φ hΦ => (h.dis.disc Φ hΦ.1).isClosed
  have hB : IsClosed (⋃₀ 𝓑) :=
    (h.dis.fin.subset (show 𝓑 ⊆ 𝓕 from fun _ hΦ => hΦ.1)).isClosed_sUnion
      fun Φ hΦ => (h.dis.disc Φ hΦ.1).isClosed
  have hU : ⋃₀ 𝓐 ∪ ⋃₀ 𝓑 = univ := by
    rw [eq_univ_iff_forall]
    intro y
    obtain ⟨Φ, hΦ, hy⟩ := hcov y
    by_cases h1 : Φ ∈ 𝓐
    · exact .inl ⟨Φ, h1, hy⟩
    · exact .inr ⟨Φ, ⟨hΦ, h1⟩, hy⟩
  have hclopen : IsClopen (⋃₀ 𝓐) := ⟨hA, by
    have : (⋃₀ 𝓐)ᶜ = ⋃₀ 𝓑 := by
      ext y
      constructor
      · intro hy
        have h2 : y ∈ ⋃₀ 𝓐 ∪ ⋃₀ 𝓑 := hU ▸ mem_univ y
        exact h2.resolve_left hy
      · exact fun hy h1 => Set.disjoint_left.mp hdis h1 hy
    rw [← isClosed_compl_iff, this]
    exact hB⟩
  obtain ⟨v₀, hv₀, hv₀V⟩ := hne
  obtain ⟨Φ₀, hΦ₀, hv₀Φ⟩ := hcov v₀
  have hall : ⋃₀ 𝓐 = univ := (isClopen_iff.mp hclopen).resolve_left (nonempty_iff_ne_empty.mp
    ⟨v₀, Φ₀, ⟨hΦ₀, v₀, ⟨hv₀Φ, hv₀V⟩, hv₀⟩, hv₀Φ⟩)
  intro v hv
  obtain ⟨Φ, hΦ, hvΦ⟩ : v ∈ ⋃₀ 𝓐 := hall ▸ mem_univ v
  obtain ⟨a, ha, has⟩ := hΦ.2
  exact hsame Φ hΦ.1 a ha v ⟨hvΦ, hv⟩ has

omit [T2Space X] in
theorem discInt_disj_V (h : IsTriang V E 𝓕) {Φ : Set X} (hΦ : Φ ∈ 𝓕) {y : X}
  (hy : y ∈ discInt Φ) : y ∉ V := fun hV =>
  Set.disjoint_left.mp (h.dis.int Φ hΦ) hy (h.cov hV)

/-- Faces of a triangulation of a connected surface are connected through common edges. -/
theorem dual_conn (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] {𝓐 : Set
  (Set X)} (hs : 𝓐 ⊆ 𝓕)
    (hcl : ∀ e ∈ E, ∀ Φ ∈ 𝓐, ∀ Φ' ∈ 𝓕, e ⊆ Φ → e ⊆ Φ' → Φ' ∈ 𝓐) (hne : 𝓐.Nonempty) : 𝓐 = 𝓕 := by
  classical
  refine Subset.antisymm hs fun Φ' hΦ' => ?_
  by_contra hn
  obtain ⟨Φ, hΦ⟩ := hne
  obtain ⟨y, hy⟩ := (h.dis.disc Φ (hs hΦ)).discInt_nonempty
  obtain ⟨y', hy'⟩ := (h.dis.disc Φ' hΦ').discInt_nonempty
  have hA : IsClosed (⋃₀ 𝓐) := (h.dis.fin.subset hs).isClosed_sUnion fun Φ hΦ => (h.dis.disc Φ
    (hs hΦ)).isClosed
  have hB : IsClosed (⋃₀ (𝓕 \ 𝓐)) :=
    (h.dis.fin.subset sdiff_subset).isClosed_sUnion fun Φ hΦ => (h.dis.disc Φ hΦ.1).isClosed
  obtain ⟨z, hz, ⟨Ψ, hΨ, hzΨ⟩, ⟨Ψ', hΨ', hzΨ'⟩⟩ := isPreconnected_closed_iff.mp
    (isPreconnected_compl_finite hT h.dis.graph.fin)
    _ _ hA hB (fun x _ => by
      have : x ∈ ⋃₀ 𝓕 := h.dis.cover ▸ mem_univ x
      obtain ⟨Ψ, hΨ, hx⟩ := this
      by_cases h1 : Ψ ∈ 𝓐
      · exact .inl ⟨Ψ, h1, hx⟩
      · exact .inr ⟨Ψ, ⟨hΨ, h1⟩, hx⟩) ⟨y, h.discInt_disj_V (hs hΦ) hy, Φ, hΦ, hy.1⟩
    ⟨y', h.discInt_disj_V hΦ' hy', Φ', ⟨hΦ', hn⟩, hy'.1⟩
  have hne' : Ψ ≠ Ψ' := fun h1 => hΨ'.2 (h1 ▸ hΨ)
  have hb := h.mem_bd_of_ne (hs hΨ) hΨ'.1 hne' hzΨ hzΨ'
  obtain ⟨e, he, hze⟩ := h.dis.bd Ψ (hs hΨ) hb
  have h1 := (h.edge_sub he (hs hΨ) hze hz hzΨ).trans (discBd_subset Ψ)
  have h2 := (h.edge_sub he hΨ'.1 hze hz hzΨ').trans (discBd_subset Ψ')
  exact hΨ'.2 (hcl e he Ψ hΨ Ψ' hΨ'.1 h1 h2)

/-- The faces at a vertex are connected through common edges at the vertex. -/
theorem link_conn (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) {w : X} (hw : w ∈ V) {𝓐 : Set
  (Set X)} (hs : 𝓐 ⊆ 𝓕)
    (hsw : ∀ Φ ∈ 𝓐, w ∈ Φ) (hcl : ∀ e ∈ E, w ∈ e → ∀ Φ ∈ 𝓐, ∀ Φ' ∈ 𝓕, e ⊆ Φ → e ⊆ Φ' → Φ' ∈ 𝓐)
      (hne : 𝓐.Nonempty)
    {Φ' : Set X} (hΦ' : Φ' ∈ 𝓕) (hwΦ' : w ∈ Φ') : Φ' ∈ 𝓐 := by
  classical
  by_contra hn
  obtain ⟨Φ, hΦ⟩ := hne
  let C : Set X := ⋃₀ {Ψ ∈ 𝓕 | w ∉ Ψ} ∪ (V \ {w}) ∪ ⋃₀ {e ∈ E | w ∉ e}
  have hC : IsClosed C := by
    refine (IsClosed.union ?_ ?_).union ?_
    · exact (h.dis.fin.subset (show {Ψ ∈ 𝓕 | w ∉ Ψ} ⊆ 𝓕 from fun _ hΨ => hΨ.1)).isClosed_sUnion
        fun Ψ hΨ => (h.dis.disc Ψ hΨ.1).isClosed
    · exact (h.dis.graph.fin.subset sdiff_subset).isClosed
    · refine (h.dis.graph.fine.subset (show {e ∈ E | w ∉ e} ⊆ E from fun _ he
      => he.1)).isClosed_sUnion
        fun e he => ?_
      obtain ⟨u, v, -, hl, -⟩ := h.dis.graph.edge e he.1
      exact hl.isCompact.isClosed
  have hwC : w ∉ C := by
    rintro ((⟨Ψ, hΨ, h1⟩ | h1) | ⟨e, he, h1⟩)
    · exact hΨ.2 h1
    · exact h1.2 rfl
    · exact he.2 h1
  obtain ⟨B, k, g, c, hBC, hg0⟩ := (hT.2.2 w).exists_ballChart hC.isOpen_compl hwC (R := 1) one_pos
  have hpc := c.isPreconnected_punctured
  rw [hg0] at hpc
  have hwB : w ∈ B := hg0 ▸ c.gm (by simp)
  let 𝓑 : Set (Set X) := {Ψ ∈ 𝓕 | w ∈ Ψ} \ 𝓐
  have hA : IsClosed (⋃₀ 𝓐) := (h.dis.fin.subset hs).isClosed_sUnion fun Φ hΦ => (h.dis.disc Φ
    (hs hΦ)).isClosed
  have hB : IsClosed (⋃₀ 𝓑) :=
    (h.dis.fin.subset (show 𝓑 ⊆ 𝓕 from fun _ hΨ => hΨ.1.1)).isClosed_sUnion
      fun Ψ hΨ => (h.dis.disc Ψ hΨ.1.1).isClosed
  have hmeet : ∀ Ψ ∈ 𝓕, w ∈ Ψ → ∃ y ∈ B \ {w}, y ∈ Ψ := fun Ψ hΨ hwΨ => by
    have h1 : w ∈ closure (discInt Ψ) := (h.dis.disc Ψ hΨ).subset_closure_discInt hwΨ
    obtain ⟨y, hy, hyi⟩ := mem_closure_iff.mp h1 B c.isOpen hwB
    refine ⟨y, ⟨hy, fun h2 => ?_⟩, hyi.1⟩
    have h3 : y = w := h2
    exact hyi.2 (h3 ▸ h.mem_bd hΨ hwΨ (h.cov hw))
  obtain ⟨y₁, hy₁, hy₁Φ⟩ := hmeet Φ (hs hΦ) (hsw Φ hΦ)
  obtain ⟨y₂, hy₂, hy₂Φ⟩ := hmeet Φ' hΦ' hwΦ'
  obtain ⟨z, hz, ⟨Ψ, hΨ, hzΨ⟩, ⟨Ψ', hΨ', hzΨ'⟩⟩ := isPreconnected_closed_iff.mp hpc _ _ hA hB
    (fun x hx => by
      have : x ∈ ⋃₀ 𝓕 := h.dis.cover ▸ mem_univ x
      obtain ⟨Ψ, hΨ, hxΨ⟩ := this
      have hwΨ : w ∈ Ψ := by
        by_contra h1
        exact hBC hx.1 (.inl (.inl ⟨Ψ, ⟨hΨ, h1⟩, hxΨ⟩))
      by_cases h1 : Ψ ∈ 𝓐
      · exact .inl ⟨Ψ, h1, hxΨ⟩
      · exact .inr ⟨Ψ, ⟨⟨hΨ, hwΨ⟩, h1⟩, hxΨ⟩) ⟨y₁, hy₁, Φ, hΦ, hy₁Φ⟩ ⟨y₂, hy₂, Φ', ⟨⟨hΦ', hwΦ'⟩,
          hn⟩, hy₂Φ⟩
  have hne' : Ψ ≠ Ψ' := fun h1 => hΨ'.2 (h1 ▸ hΨ)
  have hb := h.mem_bd_of_ne (hs hΨ) hΨ'.1.1 hne' hzΨ hzΨ'
  obtain ⟨e, he, hze⟩ := h.dis.bd Ψ (hs hΨ) hb
  have hzV : z ∉ V := fun h1 => hBC hz.1 (.inl (.inr ⟨h1, hz.2⟩))
  have hwe : w ∈ e := by
    by_contra h1
    exact hBC hz.1 (.inr ⟨e, ⟨he, h1⟩, hze⟩)
  have h1 := (h.edge_sub he (hs hΨ) hze hzV hzΨ).trans (discBd_subset Ψ)
  have h2 := (h.edge_sub he hΨ'.1.1 hze hzV hzΨ').trans (discBd_subset Ψ')
  exact hΨ'.2 (hcl e he hwe Ψ hΨ Ψ' hΨ'.1.1 h1 h2)

end IsTriang

end GraphMinor.Surface
