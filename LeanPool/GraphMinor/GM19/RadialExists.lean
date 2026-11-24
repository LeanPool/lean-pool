/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Defs2
public import LeanPool.GraphMinor.GM11.RadialExists
public import LeanPool.GraphMinor.GM11.ArcDrawings
public import LeanPool.GraphMinor.Surface.DiscMerge
public import LeanPool.GraphMinor.Surface.Disc
public import LeanPool.GraphMinor.Surface.OpenDisc
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Radial drawings of paintings of Graph Minors XIX

Graph Minors XIX, Section 5 (page 337), uses a radial drawing of a 2-cell painting `Γ` in `Σ̂`, and
Graph Minors XI, Section 3 (page 75), says that it exists. A painting of XIX may have both line
edges
and disc edges, so it is neither a painting nor a drawing of XI, and `GM11.exists_radialDrawing`
does
not apply to it. Here we reduce to the drawing `sk(Γ)` of XI.

The regions of `sk(Γ)` in `Σ̂` are the regions of `Γ` and the insides of the discs of the edges of
size 3. A drawing that satisfies conditions (i)–(iv) for `Γ`, with one more isolated vertex inside
each
such disc, satisfies them for `sk(Γ)`. So `GM11.ncard_spokes_le` bounds its number of edges, and a
drawing with the most edges is a radial drawing of `Γ` (`Painting.exists_radialDrawing`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface unitInterval

universe u

section Arc

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

instance : PathConnectedSpace I :=
  isPathConnected_iff_pathConnectedSpace.1 ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)

theorem exists_arcComp_superset {F C : Set X} (hC : IsPathConnected C) (hCF : C ⊆ F) :
    ∃ c ∈ arcComponentsIn F, C ⊆ c := by
  obtain ⟨x, hx⟩ := hC.nonempty
  have hc : IsPathConnected (pathComponentIn F x) := isPathConnected_pathComponentIn (hCF hx)
  refine ⟨_, ⟨⟨x, mem_pathComponentIn_self (hCF hx)⟩, pathComponentIn_subset, hc,
    fun D hDF hD hcD ↦ ?_⟩, fun y hy ↦ (hC.joinedIn x hx y hy).mono hCF⟩
  refine Subset.antisymm (fun y hy ↦ ?_) hcD
  exact (hD.joinedIn x (hcD (mem_pathComponentIn_self (hCF hx))) y hy).mono hDF

theorem arcComp_eq_of_mem {F a b : Set X} (ha : a ∈ arcComponentsIn F) (hb : b ∈ arcComponentsIn F)
    {x : X} (hxa : x ∈ a) (hxb : x ∈ b) : a = b := by
  have hu : IsPathConnected (a ∪ b) := ha.2.2.1.union hb.2.2.1 ⟨x, hxa, hxb⟩
  have h₁ := ha.2.2.2 (a ∪ b) (union_subset ha.2.1 hb.2.1) hu subset_union_left
  have h₂ := hb.2.2.2 (a ∪ b) (union_subset ha.2.1 hb.2.1) hu subset_union_right
  rw [← h₁, h₂]

theorem mem_arcComp_of_path {F e : Set X} (he : e ∈ arcComponentsIn F) {φ : I → X}
    (hφ : Continuous φ) (hF : ∀ t, φ t ∈ F) (h1 : φ 1 ∈ e) : φ 0 ∈ e := by
  have hK : IsPathConnected (φ '' univ) := isPathConnected_univ.image hφ
  have hu := he.2.2.1.union hK ⟨φ 1, h1, mem_image_of_mem _ (mem_univ _)⟩
  have h := he.2.2.2 _ (union_subset he.2.1 (by rintro _ ⟨t, -, rfl⟩; exact hF t)) hu
    subset_union_left
  rw [← h]
  exact Or.inr (mem_image_of_mem _ (mem_univ _))

theorem arcComponentsIn_image {ι : X → Y} (hι : IsEmbedding ι) {F : Set X} {C : Set Y}
    (hC : C ∈ arcComponentsIn (ι '' F)) : ∃ c ∈ arcComponentsIn F, ι '' c = C := by
  have hCr : ι '' (ι ⁻¹' C) = C := image_preimage_eq_of_subset (hC.2.1.trans
    (image_subset_range _ _))
  have hpc : IsPathConnected (ι ⁻¹' C) := by
    rw [hι.isInducing.isPathConnected_iff, hCr]
    exact hC.2.2.1
  have hsub : ι ⁻¹' C ⊆ F := fun x hx ↦ by
    obtain ⟨y, hy, hyx⟩ := hC.2.1 hx
    exact hι.injective hyx ▸ hy
  refine ⟨ι ⁻¹' C, ⟨hpc.nonempty, hsub, hpc, fun D hDF hD hCD ↦ ?_⟩, hCr⟩
  have h := hC.2.2.2 (ι '' D) (image_mono hDF) (hD.image hι.continuous)
    (by rw [← hCr]; exact image_mono hCD)
  rw [← h, preimage_image_eq _ hι.injective]

theorem connectedComponentIn_union_left {A B : Set X} (hA : IsOpen A) (hB : IsOpen B)
    (hd : Disjoint A B) {x : X} (hx : x ∈ A) :
    connectedComponentIn (A ∪ B) x = connectedComponentIn A x := by
  refine Subset.antisymm ?_ (connectedComponentIn_mono _ subset_union_left)
  have hc : IsPreconnected (connectedComponentIn (A ∪ B) x) := isPreconnected_connectedComponentIn
  have hxc : x ∈ connectedComponentIn (A ∪ B) x := mem_connectedComponentIn (Or.inl hx)
  have hs : connectedComponentIn (A ∪ B) x ⊆ A :=
    hc.subset_left_of_subset_union hA hB hd (connectedComponentIn_subset _ _) ⟨x, hxc, hx⟩
  exact hc.subset_connectedComponentIn hxc hs

end Arc

variable {S : Type u} [TopologicalSpace S]

namespace Painting

theorem isDisc_of_three (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) (h3 : (tilde e).ncard = 3) :
    IsClosedDisc (closure e) ∧ tilde e ⊆ discBd (closure e) ∧ (tilde e).Finite := by
  rcases Γ.edge_shape e he with h | h
  · have := h.1
    omega
  · exact ⟨h.2.2.1, h.2.2.2, h.2.1⟩

theorem size_cases (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) :
    (tilde e).ncard = 2 ∨ (tilde e).ncard = 3 := by
  rcases Γ.edge_shape e he with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem closure_subset_U (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) : closure e ⊆ Γ.U :=
  closure_minimal (he.2.1.trans sdiff_subset) Γ.isClosed_U

theorem disjoint_V (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) {x : S} (hx : x ∈ e) : x ∉ Γ.V :=
  (he.2.1 hx).2

/-- A line edge, with its ends written out. -/
theorem exists_line (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) (h2 : (tilde e).ncard = 2) :
    ∃ (f : I ≃ₜ closure e), (f 0).1 ≠ (f 1).1 ∧ tilde e = {(f 0).1, (f 1).1} := by
  rcases Γ.edge_shape e he with h | h
  · obtain ⟨-, hfin, ⟨f⟩, hends⟩ := h
    have hne : (f 0).1 ≠ (f 1).1 := fun h ↦ by
      have := f.injective (Subtype.ext h)
      exact zero_ne_one this
    have h0 : (f 0).1 ∈ tilde e := hends ▸ ⟨(f 1).1, f, rfl, rfl⟩
    have h1 : (f 1).1 ∈ tilde e := by
      rw [← hends]
      refine ⟨(f 0).1, (unitInterval.symmHomeomorph.trans f), ?_, ?_⟩ <;> simp
    refine ⟨f, hne, ?_⟩
    have hsub : ({(f 0).1, (f 1).1} : Set S) ⊆ tilde e := by
      rintro x (rfl | rfl)
      · exact h0
      · exact h1
    refine (eq_of_subset_of_ncard_le hsub ?_ hfin).symm
    rw [ncard_pair hne, h2]
  · have := h.1
    omega

/-- The set `eTilde` consists of vertices of `Γ`. -/
theorem tilde_subset_V (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) : tilde e ⊆ Γ.V := by
  intro x hx
  by_contra hxV
  have hxU : x ∈ Γ.U := Γ.closure_subset_U he hx.1
  have hmem : ∀ y, y ∈ e ∨ y = x → y ∈ Γ.U \ Γ.V := by
    rintro y (hy | rfl)
    · exact he.2.1 hy
    · exact ⟨hxU, hxV⟩
  rcases Γ.size_cases he with h2 | h3
  · obtain ⟨f, hne, hset⟩ := Γ.exists_line he h2
    have hsame : ∀ t : I, t ≠ 0 → t ≠ 1 → (f t).1 ∈ e := by
      intro t h0 h1
      by_contra hn
      have : (f t).1 ∈ tilde e := ⟨(f t).2, hn⟩
      rw [hset] at this
      rcases this with h | h
      · exact h0 (f.injective (Subtype.ext h))
      · exact h1 (f.injective (Subtype.ext h))
    let half : I := ⟨1 / 2, by norm_num, by norm_num⟩
    have hhalf : (f half).1 ∈ e := hsame half
      (fun h ↦ by have := congrArg Subtype.val h; norm_num [half] at this)
      (fun h ↦ by have := congrArg Subtype.val h; norm_num [half] at this)
    have hx' : x = (f 0).1 ∨ x = (f 1).1 := by
      rw [hset] at hx
      exact hx
    rcases hx' with rfl | rfl
    · let φ : I → S := fun t ↦ (f ⟨t.1 / 2, by have := t.2.1; positivity, by
        have := t.2.2; linarith⟩).1
      have hφ : Continuous φ := by
        refine continuous_subtype_val.comp (f.continuous.comp (Continuous.subtype_mk ?_ _))
        exact continuous_subtype_val.div_const 2
      have h0 : φ 0 = (f 0).1 := by
        simp only [φ]
        congr 2
        exact Subtype.ext (by simp)
      have h1 : φ 1 = (f half).1 := by
        simp only [φ]
        congr 2
      refine hx.2 (h0 ▸ mem_arcComp_of_path he hφ (fun t ↦ hmem _ ?_) (h1 ▸ hhalf))
      by_cases ht : t = 0
      · exact Or.inr (by rw [ht]; exact h0)
      · refine Or.inl (hsame _ (fun h ↦ ht (Subtype.ext ?_)) (fun h ↦ ?_))
        · have := congrArg Subtype.val h
          simp only [Icc.coe_zero] at this
          simpa using (by linarith : t.1 = 0)
        · have := congrArg Subtype.val h
          have ht1 := t.2.2
          simp only [Icc.coe_one] at this
          linarith
    · let φ : I → S := fun t ↦ (f ⟨1 - t.1 / 2, by have := t.2.2; linarith, by
        have := t.2.1; linarith⟩).1
      have hφ : Continuous φ := by
        refine continuous_subtype_val.comp (f.continuous.comp (Continuous.subtype_mk ?_ _))
        exact continuous_const.sub (continuous_subtype_val.div_const 2)
      have h0 : φ 0 = (f 1).1 := by
        simp only [φ]
        congr 2
        exact Subtype.ext (by simp)
      have h1 : φ 1 = (f half).1 := by
        simp only [φ]
        congr 2
        exact Subtype.ext (by simp [half]; norm_num)
      refine hx.2 (h0 ▸ mem_arcComp_of_path he hφ (fun t ↦ hmem _ ?_) (h1 ▸ hhalf))
      by_cases ht : t = 0
      · exact Or.inr (by rw [ht]; exact h0)
      · refine Or.inl (hsame _ (fun h ↦ ?_) (fun h ↦ ht (Subtype.ext ?_)))
        · have := congrArg Subtype.val h
          have ht1 := t.2.2
          simp only [Icc.coe_zero] at this
          linarith
        · have := congrArg Subtype.val h
          simp only [Icc.coe_one] at this
          simpa using (by linarith : t.1 = 0)
  · obtain ⟨hD, hbd, -⟩ := Γ.isDisc_of_three he h3
    obtain ⟨h, g, c⟩ := hD.exists_isChart
    have hxb := hbd hx
    have hp : h x ∈ Metric.sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hxb
    have hnorm : ‖h x‖ = 1 := by simpa using hp
    have hball : ∀ t : I, (1 - t.1 : ℝ) • h x ∈ Metric.closedBall (0 : ℂ) 1 := fun t ↦ by
      have h1 := t.2.1
      have h2 := t.2.2
      rw [mem_closedBall_zero_iff, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.2 h2)]
      linarith
    have hint : ∀ z ∈ Metric.ball (0 : ℂ) 1, g z ∈ e := by
      intro z hz
      have hz' : g z ∈ discInt (closure e) := by
        rw [c.discInt_eq]
        exact mem_image_of_mem g hz
      by_contra hn
      exact hz'.2 (hbd ⟨hz'.1, hn⟩)
    let φ : I → S := fun t ↦ g ((1 - t.1 : ℝ) • h x)
    have hφ : Continuous φ := by
      refine c.gc.comp_continuous ?_ hball
      exact (continuous_const.sub continuous_subtype_val).smul continuous_const
    have h0 : φ 0 = x := by
      simp only [φ, Icc.coe_zero, sub_zero, one_smul]
      exact c.gh (discBd_subset _ hxb)
    have hnear : ∀ t : I, t ≠ 0 → φ t ∈ e := fun t ht ↦ by
      refine hint _ ?_
      have h1 : 0 < t.1 := lt_of_le_of_ne t.2.1 (fun h ↦ ht (Subtype.ext h.symm))
      have h2 := t.2.2
      simp only [Metric.mem_ball, dist_zero_right, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.2 h2)]
      linarith
    have := mem_arcComp_of_path he hφ (fun t ↦ hmem _ (by
      by_cases ht : t = 0
      · exact Or.inr (by rw [ht]; exact h0)
      · exact Or.inl (hnear t ht))) (hnear 1 one_ne_zero)
    exact hx.2 (h0 ▸ this)

theorem closure_inter_V (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) :
    closure e ∩ Γ.V = tilde e := by
  ext x
  exact ⟨fun h ↦ ⟨h.1, fun hx ↦ Γ.disjoint_V he hx h.2⟩, fun h ↦ ⟨h.1, Γ.tilde_subset_V he h⟩⟩

theorem closure_subset (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) : closure e ⊆ e ∪ Γ.V := by
  intro x hx
  by_cases h : x ∈ e
  · exact Or.inl h
  · exact Or.inr (Γ.tilde_subset_V he ⟨hx, h⟩)

theorem skU_subset (Γ : Painting S) : Γ.skU ⊆ Γ.U := by
  rintro x ((hx | hx) | hx)
  · exact Γ.V_subset hx
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.1 hx
    exact (he.1.2.1 hxe).1
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.1 hx
    exact Γ.closure_subset_U he.1 (discBd_subset _ hxe)

/-- A point of an edge of size 3 that lies in `U(sk(Γ))` lies on the boundary of the disc. -/
theorem mem_discBd_of_skU (Γ : Painting S) {c : Set S} (hc : c ∈ Γ.E) (h3 : (tilde c).ncard = 3)
    {x : S} (hxc : x ∈ c) (hx : x ∈ Γ.skU) : x ∈ discBd (closure c) := by
  rcases hx with (hx | hx) | hx
  · exact absurd hx (Γ.disjoint_V hc hxc)
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.1 hx
    have := arcComp_eq_of_mem he.1 hc hxe hxc
    rw [this] at he
    have := he.2
    omega
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.1 hx
    rcases Γ.closure_subset he.1 (discBd_subset _ hxe) with h | h
    · rw [← arcComp_eq_of_mem he.1 hc h hxc]
      exact hxe
    · exact absurd h (Γ.disjoint_V hc hxc)

/-- `sk(Γ)` is a drawing of Graph Minors XI (Graph Minors XIX, Section 2, page 327). -/
theorem exists_skDrawing [T2Space S] (Γ : Painting S) :
    ∃ D : Drawing S, D.U = Γ.skU ∧ D.V = Γ.V := by
  classical
  have hDc : ∀ c, ∃ D : Drawing S, c ∈ Γ.E → (tilde c).ncard = 3 →
      D.U = discBd (closure c) ∧ D.V = tilde c := by
    intro c
    by_cases h : c ∈ Γ.E ∧ (tilde c).ncard = 3
    · obtain ⟨hD, hbd, hfin⟩ := Γ.isDisc_of_three h.1 h.2
      have hne : (tilde c).Nonempty := by
        rw [← ncard_pos hfin, h.2]
        norm_num
      obtain ⟨D, h₁, h₂⟩ := GM11.exists_drawing_on_oArc hD.isOArc_discBd hfin hne hbd
      exact ⟨D, fun _ _ ↦ ⟨h₁, h₂⟩⟩
    · exact ⟨GM11.pointsDrawing (finite_empty (α := S)), fun h₁ h₂ ↦ absurd ⟨h₁, h₂⟩ h⟩
  choose Dc hDc using hDc
  set Z2 : Set (Set S) := {e ∈ Γ.E | (tilde e).ncard = 2} with hZ2
  set Z3 : Set (Set S) := {e ∈ Γ.E | (tilde e).ncard = 3} with hZ3
  have hfin2 : Z2.Finite := Γ.finite_edges.subset fun _ h ↦ h.1
  have hfin3 : Z3.Finite := Γ.finite_edges.subset fun _ h ↦ h.1
  have hclosed : IsClosed Γ.skU := by
    have hset : Γ.skU = Γ.V ∪ (⋃ e ∈ Z2, closure e) ∪
        (⋃ e ∈ Z3, discBd (closure e)) := by
      apply Subset.antisymm
      · refine union_subset_union_left _ (union_subset_union_right _ ?_)
        exact iUnion₂_mono fun e _ ↦ subset_closure
      · refine union_subset (union_subset (fun x hx ↦ Or.inl (Or.inl hx)) ?_) fun x hx ↦ Or.inr hx
        refine iUnion₂_subset fun e he ↦ fun x hx ↦ ?_
        rcases Γ.closure_subset he.1 hx with h | h
        · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨e, he, h⟩))
        · exact Or.inl (Or.inl h)
    rw [hset]
    refine ((Γ.finite_V.isClosed).union ?_).union ?_
    · exact hfin2.isClosed_biUnion fun _ _ ↦ isClosed_closure
    · refine hfin3.isClosed_biUnion fun e he ↦ ?_
      exact (IsOArc.isCompact (Γ.isDisc_of_three he.1 he.2).1.isOArc_discBd).isClosed
  have hAsub : Γ.skU \ Γ.V ⊆ Γ.U \ Γ.V := sdiff_subset_sdiff_left Γ.skU_subset
  have hcomp : ∀ C ∈ arcComponentsIn (Γ.skU \ Γ.V), C ∈ Z2 ∨ ∃ c ∈ Z3, C ∈ (Dc c).E := by
    intro C hC
    obtain ⟨c, hc, hCc⟩ := exists_arcComp_superset hC.2.2.1 (hC.2.1.trans hAsub)
    rcases Γ.size_cases hc with h2 | h3
    · left
      have hsub : c ⊆ Γ.skU \ Γ.V := fun x hx ↦
        ⟨Or.inl (Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h2⟩, hx⟩)), Γ.disjoint_V hc hx⟩
      rw [← hC.2.2.2 c hsub hc.2.2.1 hCc]
      exact ⟨hc, h2⟩
    · right
      refine ⟨c, ⟨hc, h3⟩, ?_⟩
      obtain ⟨hU, hV⟩ := hDc c hc h3
      change C ∈ arcComponentsIn ((Dc c).U \ (Dc c).V)
      rw [hU, hV]
      refine ⟨hC.1, fun x hx ↦ ?_, hC.2.2.1, fun D hD hpc hCD ↦ ?_⟩
      · exact ⟨Γ.mem_discBd_of_skU hc h3 (hCc hx) (hC.2.1 hx).1, fun h ↦ h.2 (hCc hx)⟩
      · refine hC.2.2.2 D (fun x hx ↦ ⟨Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h3⟩, (hD hx).1⟩),
          fun hV ↦ ?_⟩)
          hpc hCD
        have hxc := discBd_subset _ (hD hx).1
        rw [← Γ.closure_inter_V hc] at hD
        exact (hD hx).2 ⟨hxc, hV⟩
  refine ⟨{ U := Γ.skU, V := Γ.V, V_subset_U := fun x hx ↦ Or.inl (Or.inl hx),
            isClosed_U := hclosed, finite_V := Γ.finite_V, finite_edges := ?_,
            edge_cond := ?_ }, rfl, rfl⟩
  · refine (hfin2.union (hfin3.biUnion fun c _ ↦ (Dc c).finite_edges)).subset fun C hC ↦ ?_
    rcases hcomp C hC with h | ⟨c, hc, h⟩
    · exact Or.inl h
    · exact Or.inr (mem_iUnion₂.2 ⟨c, hc, h⟩)
  · intro e he
    rcases hcomp e he with h | ⟨c, hc, h⟩
    · obtain ⟨f, hne, hset⟩ := Γ.exists_line h.1 h.2
      left
      refine ⟨_, _, hne, ?_, f, rfl, rfl⟩
      rw [Γ.closure_inter_V h.1, hset]
    · obtain ⟨hU, hV⟩ := hDc c hc.1 hc.2
      have hsub : closure e ⊆ closure c := by
        have h₁ : closure e ⊆ (Dc c).U :=
          closure_minimal (h.2.1.trans sdiff_subset) (Dc c).isClosed_U
        exact h₁.trans (hU ▸ discBd_subset _)
      have hset : closure e ∩ Γ.V = closure e ∩ (Dc c).V := by
        rw [hV, ← Γ.closure_inter_V hc.1]
        ext x
        exact ⟨fun hx ↦ ⟨hx.1, hsub hx.1, hx.2⟩, fun hx ↦ ⟨hx.1, hx.2.2⟩⟩
      rw [hset]
      exact (Dc c).edge_cond e h

end Painting

section Hat

variable {T : Type u} [TopologicalSpace T]

/-- The image of a drawing under a closed embedding is a drawing. -/
theorem exists_drawing_image (D : Drawing S) {ι : S → T} (hι : IsClosedEmbedding ι) :
    ∃ D' : Drawing T, D'.U = ι '' D.U ∧ D'.V = ι '' D.V := by
  have hset : ι '' D.U \ ι '' D.V = ι '' (D.U \ D.V) := (image_sdiff hι.injective _ _).symm
  refine ⟨{ U := ι '' D.U, V := ι '' D.V, V_subset_U := image_mono D.V_subset_U,
            isClosed_U := hι.isClosedMap _ D.isClosed_U, finite_V := D.finite_V.image _,
            finite_edges := ?_, edge_cond := ?_ }, rfl, rfl⟩
  · rw [hset]
    refine (D.finite_edges.image fun c ↦ ι '' c).subset fun C hC ↦ ?_
    obtain ⟨c, hc, rfl⟩ := arcComponentsIn_image hι.isEmbedding hC
    exact mem_image_of_mem _ hc
  · intro C hC
    rw [hset] at hC
    obtain ⟨c, hc, rfl⟩ := arcComponentsIn_image hι.isEmbedding hC
    rw [hι.closure_image_eq, ← image_inter hι.injective]
    let e := hι.isEmbedding.homeomorphImage (closure c)
    rcases D.edge_cond c hc with ⟨u, v, huv, hset', f, hf0, hf1⟩ | ⟨u, hset', ⟨f⟩⟩
    · refine Or.inl ⟨ι u, ι v, hι.injective.ne huv, ?_, f.trans e, ?_, ?_⟩
      · rw [hset', image_pair]
      · change ι (f 0).1 = ι u
        rw [hf0]
      · change ι (f 1).1 = ι v
        rw [hf1]
    · exact Or.inr ⟨ι u, by rw [hset', image_singleton], ⟨f.trans e⟩⟩

/-- A drawing with some isolated vertices added. -/
theorem exists_addPoints [T1Space T] (G : Drawing T) {W : Set T} (hW : W.Finite)
    (hd : Disjoint W G.U) : ∃ G' : Drawing T, G'.U = G.U ∪ W ∧ G'.V = G.V ∪ W ∧ G'.E = G.E := by
  have hset : (G.U ∪ W) \ (G.V ∪ W) = G.U \ G.V := by
    ext x
    constructor
    · rintro ⟨hx | hx, hn⟩
      · exact ⟨hx, fun h ↦ hn (Or.inl h)⟩
      · exact absurd (Or.inr hx) hn
    · rintro ⟨hx, hn⟩
      exact ⟨Or.inl hx, fun h ↦ h.elim hn fun h' ↦ disjoint_left.1 hd h' hx⟩
  refine ⟨{ U := G.U ∪ W, V := G.V ∪ W, V_subset_U := union_subset_union_left _ G.V_subset_U,
            isClosed_U := G.isClosed_U.union hW.isClosed, finite_V := G.finite_V.union hW,
            finite_edges := by rw [hset]; exact G.finite_edges, edge_cond := ?_ }, rfl, rfl, ?_⟩
  · intro e he
    rw [hset] at he
    have hcl : closure e ⊆ G.U := closure_minimal (he.2.1.trans sdiff_subset) G.isClosed_U
    have heq : closure e ∩ (G.V ∪ W) = closure e ∩ G.V := by
      ext x
      constructor
      · rintro ⟨hx, h | h⟩
        · exact ⟨hx, h⟩
        · exact absurd (hcl hx) (disjoint_left.1 hd h)
      · exact fun h ↦ ⟨h.1, Or.inl h.2⟩
    rw [heq]
    exact G.edge_cond e he
  · change arcComponentsIn ((G.U ∪ W) \ (G.V ∪ W)) = arcComponentsIn (G.U \ G.V)
    rw [hset]

/-- Conditions (i)–(iv) have a solution with no edges: the vertices and one point in each region. -/
theorem exists_preRadial_points [T2Space T] [Nonempty T] {U V : Set T} (hVU : V ⊆ U) (hV : V.Finite)
    (hR : (componentsIn Uᶜ).Finite) : ∃ G : Drawing T, IsPreRadial U V G := by
  classical
  have hne : ∀ r ∈ componentsIn Uᶜ, r.Nonempty := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, mem_connectedComponentIn hy⟩
  have hout : ∀ r ∈ componentsIn Uᶜ, ∀ x ∈ r, x ∉ U := by
    rintro _ ⟨y, hy, rfl⟩ x hx
    exact connectedComponentIn_subset _ _ hx
  have hsame : ∀ r₁ ∈ componentsIn Uᶜ, ∀ r₂ ∈ componentsIn Uᶜ, ∀ x, x ∈ r₁ → x ∈ r₂ → r₁ = r₂ := by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ x ha hb
    rw [connectedComponentIn_eq ha, connectedComponentIn_eq hb]
  choose! hub hhub using hne
  have hA : (V ∪ hub '' componentsIn Uᶜ).Finite := hV.union (hR.image _)
  have hE := GM11.pointsDrawing_E hA
  have hUV : (GM11.pointsDrawing hA).U = V ∪ hub '' componentsIn Uᶜ := rfl
  have hVV : (GM11.pointsDrawing hA).V = V ∪ hub '' componentsIn Uᶜ := rfl
  refine ⟨GM11.pointsDrawing hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hUV]
    ext x
    constructor
    · rintro ⟨hxU, hx | ⟨r, hr, rfl⟩⟩
      · exact hx
      · exact absurd hxU (hout r hr _ (hhub r hr))
    · exact fun hx ↦ ⟨hVU hx, Or.inl hx⟩
  · rw [hVV]
    exact subset_union_left
  · intro r hr
    refine ⟨hub r, ⟨hhub r hr, Or.inr ⟨r, hr, rfl⟩⟩, ?_⟩
    rintro w ⟨hwr, hw | ⟨r', hr', rfl⟩⟩
    · exact absurd (hVU hw) (hout r hr _ hwr)
    · rw [hsame r hr r' hr' _ hwr (hhub r' hr')]
  · rintro w ⟨hw | ⟨r, hr, rfl⟩, hn⟩
    · exact absurd hw hn
    · exact ⟨r, hr, hhub r hr⟩
  · intro e he
    rw [hE] at he
    exact absurd he (notMem_empty _)
  · intro e he
    rw [hE] at he
    exact absurd he (notMem_empty _)

/-- The inside of a closed disc in a manifold is an open disc. -/
theorem isOpenDisc_discInt (hman : ∀ x : T, IsManifoldPoint x) {D : Set T} (hD : IsClosedDisc D) :
    IsOpenDisc (discInt D) := by
  refine ⟨hD.isOpen_discInt hman, ?_⟩
  obtain ⟨φ⟩ := hD
  have hsub : ∀ x : OpenUnitDisc, x.1 ∈ ClosedUnitDisc := fun x ↦
    Metric.ball_subset_closedBall x.2
  let j : OpenUnitDisc → T := fun x ↦ (φ ⟨x.1, hsub x⟩).1
  have hj : IsEmbedding j := by
    refine IsEmbedding.subtypeVal.comp (φ.isEmbedding.comp ?_)
    exact IsEmbedding.inclusion (fun x hx ↦ Metric.ball_subset_closedBall hx)
  have hr : range j = discInt D := by
    have hbd := disc_boundary.{u} D φ
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(φ _).2, fun hy ↦ ?_⟩
      rw [hbd] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have hz' : z = ⟨x.1, hsub x⟩ := φ.injective (Subtype.ext hzy)
      have h₁ : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.1 hz
      have h₂ : ‖x.1‖ < 1 := mem_ball_zero_iff.1 x.2
      rw [hz'] at h₁
      exact absurd h₁ h₂.ne
    · rintro ⟨hyD, hn⟩
      let z := φ.symm ⟨y, hyD⟩
      have hzφ : (φ z).1 = y := by simp [z]
      have h₁ : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.1 z.2
      have h₂ : ‖z.1‖ ≠ 1 := fun h ↦ hn (by
        rw [hbd]
        exact ⟨z, mem_sphere_zero_iff_norm.2 h, hzφ⟩)
      exact ⟨⟨z.1, mem_ball_zero_iff.2 (lt_of_le_of_ne h₁ h₂)⟩, hzφ⟩
  exact ⟨hj.toHomeomorph.trans (Homeomorph.setCongr hr)⟩

/-- The image of a closed disc under a closed embedding, with its boundary. -/
theorem isClosedDisc_image {Δ : Set S} (hΔ : IsClosedDisc Δ) {ι : S → T} (hι : IsEmbedding ι) :
    IsClosedDisc (ι '' Δ) ∧ discBd (ι '' Δ) = ι '' discBd Δ := by
  obtain ⟨φ⟩ := hΔ
  let e := hι.homeomorphImage Δ
  refine ⟨⟨φ.trans e⟩, ?_⟩
  rw [disc_boundary.{u} (ι '' Δ) (φ.trans e), disc_boundary.{u} Δ φ, image_image]
  rfl

end Hat

section Main

variable {Shat : Type u} [TopologicalSpace Shat]

omit [TopologicalSpace S] in
private theorem components_of_disjoint_open_discs
    {A U : Set Shat} {cells : Set (Set S)} {B : Set S → Set Shat}
    (hcompl : Uᶜ = A ∪ ⋃ c ∈ cells, B c)
    (hAopen : IsOpen A) (hBopen : ∀ c ∈ cells, IsOpen (B c))
    (hBconn : ∀ c ∈ cells, IsPreconnected (B c))
    (hBne : ∀ c ∈ cells, (B c).Nonempty)
    (hBU : ∀ c ∈ cells, Disjoint (B c) A)
    (hBdisj : ∀ c ∈ cells, ∀ c' ∈ cells, c ≠ c' → Disjoint (B c) (B c')) :
    componentsIn A ⊆ componentsIn (univ \ U) ∧
      (∀ c ∈ cells, B c ∈ componentsIn (univ \ U)) ∧
      ∀ r ∈ componentsIn (univ \ U), r ∈ componentsIn A ∨ ∃ c ∈ cells, r = B c := by
  have hBs : IsOpen (⋃ c ∈ cells, B c) := isOpen_biUnion fun c hc ↦ hBopen c hc
  have hABd : Disjoint A (⋃ c ∈ cells, B c) := by
    refine disjoint_left.2 fun w hw hb ↦ ?_
    obtain ⟨c, hc, hwc⟩ := mem_iUnion₂.1 hb
    exact disjoint_left.1 (hBU c hc) hwc hw
  have hRhat : componentsIn A ⊆ componentsIn (univ \ U) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, ?_, ?_⟩
    · rw [← compl_eq_univ_sdiff, hcompl]
      exact Or.inl hx
    · rw [← compl_eq_univ_sdiff, hcompl, connectedComponentIn_union_left hAopen hBs hABd hx]
  have hRB : ∀ c ∈ cells, B c ∈ componentsIn (univ \ U) := by
    intro c hc
    obtain ⟨x, hx⟩ := hBne c hc
    refine ⟨x, ?_, ?_⟩
    · rw [← compl_eq_univ_sdiff, hcompl]
      exact Or.inr (mem_iUnion₂.2 ⟨c, hc, hx⟩)
    · have hsplit : Uᶜ = B c ∪ (A ∪ ⋃ c' ∈ cells \ {c}, B c') := by
        rw [hcompl]
        ext w
        simp only [mem_union, mem_iUnion₂, mem_sdiff, mem_singleton_iff]
        constructor
        · rintro (h | ⟨c', hc', hw⟩)
          · exact Or.inr (Or.inl h)
          · by_cases he : c' = c
            · exact Or.inl (he ▸ hw)
            · exact Or.inr (Or.inr ⟨c', ⟨hc', he⟩, hw⟩)
        · rintro (h | h | ⟨c', ⟨hc', -⟩, hw⟩)
          · exact Or.inr ⟨c, hc, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨c', hc', hw⟩
      have hopen : IsOpen (A ∪ ⋃ c' ∈ cells \ {c}, B c') :=
        hAopen.union (isOpen_biUnion fun c' hc' ↦ hBopen c' hc'.1)
      have hd : Disjoint (B c) (A ∪ ⋃ c' ∈ cells \ {c}, B c') := by
        refine disjoint_union_right.2 ⟨hBU c hc, disjoint_iUnion₂_right.2 fun c' hc' ↦ ?_⟩
        exact hBdisj c hc c' hc'.1 (Ne.symm hc'.2)
      rw [← compl_eq_univ_sdiff, hsplit,
        connectedComponentIn_union_left (hBopen c hc) hopen hd hx,
        (hBconn c hc).connectedComponentIn hx]
  have hRcases : ∀ r ∈ componentsIn (univ \ U), r ∈ componentsIn A ∨ ∃ c ∈ cells, r = B c := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← compl_eq_univ_sdiff, hcompl] at hx ⊢
    rcases hx with hx | hx
    · left
      rw [connectedComponentIn_union_left hAopen hBs hABd hx]
      exact ⟨x, hx, rfl⟩
    · right
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 hx
      refine ⟨c, hc, ?_⟩
      have := hRB c hc
      obtain ⟨y, hy, hyc⟩ := this
      rw [← compl_eq_univ_sdiff, hcompl] at hy hyc
      have hxy : x ∈ connectedComponentIn (A ∪ ⋃ c ∈ cells, B c) y := by
        rw [hyc]
        exact hxc
      rw [← connectedComponentIn_eq hxy, hyc]
  exact ⟨hRhat, hRB, hRcases⟩

/-- `sk(Γ)` in `Σ̂` is a 2-cell drawing. A drawing that satisfies conditions (i)–(iv) for `Γ`, with
one
more isolated vertex inside each disc of an edge of size 3, satisfies them for `sk(Γ)`. -/
theorem Painting.exists_hubDrawing (hS : IsSurface S) (cap : IsCappedSurface S Shat)
    (Γ : Painting S) (h2 : ∀ r ∈ Γ.hatRegions cap, IsOpenDisc r) :
    ∃ (D : Drawing Shat) (W : Set Shat), D.U = cap.emb '' Γ.skU ∧ D.V = cap.emb '' Γ.V ∧
      (GM11.PaintingOrDrawing.drawing D).IsTwoCell ∧ (Γ.hatRegions cap).Finite ∧
      ∀ G : Drawing Shat, IsPreRadial (Γ.hatU cap) (Γ.hatV cap) G → ∃ G' : Drawing Shat,
        (GM11.PaintingOrDrawing.drawing D).IsPreRadialDrawing G' ∧ G'.U = G.U ∪ W ∧
        G'.V = G.V ∪ W ∧ G'.E = G.E := by
  classical
  obtain ⟨hcomp, hT2, -⟩ := hS
  have hsurf := cap.isSurface
  have hclosedS : IsClosedSurface Shat := by
    refine ⟨hsurf.1, hsurf.2.1, fun x ↦ ?_⟩
    by_contra hx
    have : x ∈ bd Shat := hx
    rw [cap.bd_empty] at this
    exact this
  have : CompactSpace Shat := hsurf.1
  have : T2Space Shat := hsurf.2.1
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := hsurf.2.2
  set ι := cap.emb with hιdef
  have hιc : IsClosedEmbedding ι :=
    IsClosedEmbedding.of_continuous_injective_isClosedMap cap.isEmbedding.continuous
      cap.isEmbedding.injective cap.isEmbedding.continuous.isClosedMap
  obtain ⟨D₀, hD₀U, hD₀V⟩ := Γ.exists_skDrawing
  obtain ⟨D, hDU, hDV⟩ := exists_drawing_image D₀ hιc
  rw [hD₀U] at hDU
  rw [hD₀V] at hDV
  have hDV' : D.V = Γ.hatV cap := hDV
  have hUc : IsClosed (Γ.hatU cap) := hιc.isClosedMap _ Γ.isClosed_U
  set Z3 : Set (Set S) := {c ∈ Γ.E | (tilde c).ncard = 3} with hZ3
  have hZfin : Z3.Finite := Γ.finite_edges.subset fun _ h ↦ h.1
  let B : Set S → Set Shat := fun c ↦ discInt (ι '' closure c)
  have hdisc : ∀ c ∈ Z3, IsClosedDisc (ι '' closure c) ∧
      discBd (ι '' closure c) = ι '' discBd (closure c) := fun c hc ↦
    isClosedDisc_image (Γ.isDisc_of_three hc.1 hc.2).1 cap.isEmbedding
  have hBmem : ∀ c ∈ Z3, ∀ w ∈ B c, ∃ y ∈ c, ι y = w ∧ y ∉ discBd (closure c) := by
    rintro c hc w ⟨⟨y, hy, rfl⟩, hn⟩
    rw [(hdisc c hc).2] at hn
    have hnb : y ∉ discBd (closure c) := fun h ↦ hn (mem_image_of_mem _ h)
    refine ⟨y, ?_, rfl, hnb⟩
    by_contra hyc
    exact hnb ((Γ.isDisc_of_three hc.1 hc.2).2.1 ⟨hy, hyc⟩)
  have hBopen : ∀ c ∈ Z3, IsOpenDisc (B c) := fun c hc ↦ isOpenDisc_discInt hman (hdisc c hc).1
  have hBconn : ∀ c ∈ Z3, IsPreconnected (B c) := fun c hc ↦
    (hdisc c hc).1.isPreconnected_discInt
  have hBne : ∀ c ∈ Z3, (B c).Nonempty := fun c hc ↦ (hdisc c hc).1.nonempty_discInt
  have hBU : ∀ c ∈ Z3, Disjoint (B c) (Γ.hatU cap)ᶜ := fun c hc ↦ by
    refine disjoint_left.2 fun w hw hn ↦ ?_
    obtain ⟨y, hy, rfl, -⟩ := hBmem c hc w hw
    exact hn (mem_image_of_mem _ (hc.1.2.1 hy).1)
  have hBV : ∀ c ∈ Z3, ∀ w ∈ B c, w ∉ Γ.hatV cap := fun c hc w hw ⟨v, hv, hvw⟩ ↦ by
    obtain ⟨y, hy, rfl, -⟩ := hBmem c hc w hw
    exact Γ.disjoint_V hc.1 hy (hιc.injective hvw ▸ hv)
  have hBdisj : ∀ c ∈ Z3, ∀ c' ∈ Z3, c ≠ c' → Disjoint (B c) (B c') := fun c hc c' hc' hne ↦ by
    refine disjoint_left.2 fun w hw hw' ↦ ?_
    obtain ⟨y, hy, rfl, -⟩ := hBmem c hc w hw
    obtain ⟨y', hy', hyy, -⟩ := hBmem c' hc' _ hw'
    exact hne (arcComp_eq_of_mem hc.1 hc'.1 hy (hιc.injective hyy ▸ hy'))
  have hcompl : D.Uᶜ = (Γ.hatU cap)ᶜ ∪ ⋃ c ∈ Z3, B c := by
    rw [hDU]
    ext w
    constructor
    · intro hw
      by_cases hwU : w ∈ Γ.hatU cap
      · obtain ⟨y, hy, rfl⟩ := hwU
        have hyS : y ∉ Γ.skU := fun h ↦ hw (mem_image_of_mem _ h)
        have hyV : y ∉ Γ.V := fun h ↦ hyS (Or.inl (Or.inl h))
        obtain ⟨c, hc, hyc⟩ := exists_arcComp_superset (F := Γ.U \ Γ.V)
          (isPathConnected_singleton y) (singleton_subset_iff.2 ⟨hy, hyV⟩)
        have hyc' : y ∈ c := hyc rfl
        rcases Γ.size_cases hc with h | h
        · exact absurd (Or.inl (Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h⟩, hyc'⟩))) hyS
        · refine Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h⟩, mem_image_of_mem _ (subset_closure hyc'), ?_⟩)
          rw [(hdisc c ⟨hc, h⟩).2]
          rintro ⟨z, hz, hzy⟩
          exact hyS (Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h⟩, hιc.injective hzy ▸ hz⟩))
      · exact Or.inl hwU
    · rintro (hw | hw) ⟨y, hy, rfl⟩
      · exact hw (mem_image_of_mem _ (Γ.skU_subset hy))
      · obtain ⟨c, hc, hyB⟩ := mem_iUnion₂.1 hw
        obtain ⟨z, hz, hzy, hn⟩ := hBmem c hc _ hyB
        obtain rfl := hιc.injective hzy
        exact hn (Γ.mem_discBd_of_skU hc.1 hc.2 hz hy)
  have hAopen : IsOpen (Γ.hatU cap)ᶜ := hUc.isOpen_compl
  obtain ⟨hRhat, hRB, hRcases⟩ :=
    components_of_disjoint_open_discs hcompl hAopen
      (fun c hc => (hBopen c hc).1) hBconn hBne hBU hBdisj
  have hD2 : (GM11.PaintingOrDrawing.drawing D).IsTwoCell := by
    refine ⟨inferInstance, fun r hr ↦ ?_⟩
    rcases hRcases r hr with h | ⟨c, hc, rfl⟩
    · exact h2 r h
    · exact hBopen c hc
  have hRfin : (Γ.hatRegions cap).Finite :=
    (GM11.finite_R hclosedS D).subset hRhat
  have hVU : Γ.hatV cap ⊆ Γ.hatU cap := image_mono Γ.V_subset
  have hVfin : (Γ.hatV cap).Finite := Γ.finite_V.image _
  obtain ⟨hub, hhub⟩ : ∃ hub : Set S → Shat, ∀ c ∈ Z3, hub c ∈ B c := by
    choose! f hf using hBne
    exact ⟨f, hf⟩
  refine ⟨D, hub '' Z3, hDU, hDV, hD2, hRfin, fun G hG ↦ ?_⟩
  · obtain ⟨h1, h2', h3, h4, h5, h6⟩ := hG
    have hBG : ∀ c ∈ Z3, ∀ w ∈ B c, w ∉ G.U := fun c hc w hw hwG ↦ by
      have hwU : w ∈ Γ.hatU cap := by
        by_contra hn
        exact disjoint_left.1 (hBU c hc) hw hn
      exact hBV c hc w hw (h1 ▸ ⟨hwU, hwG⟩)
    have hWfin : (hub '' Z3).Finite := hZfin.image _
    have hWd : Disjoint (hub '' Z3) G.U := by
      refine disjoint_left.2 ?_
      rintro _ ⟨c, hc, rfl⟩
      exact hBG c hc _ (hhub c hc)
    obtain ⟨G', hU', hV', hE'⟩ := exists_addPoints G hWfin hWd
    have hcl : ∀ e ∈ G.E, closure e ⊆ G.U := fun e he ↦
      closure_minimal (he.2.1.trans sdiff_subset) G.isClosed_U
    have hcle : ∀ e ∈ G.E, closure e ∩ G'.V = closure e ∩ G.V := fun e he ↦ by
      rw [hV']
      ext x
      constructor
      · rintro ⟨hx, h | h⟩
        · exact ⟨hx, h⟩
        · exact absurd (hcl e he hx) (disjoint_left.1 hWd h)
      · exact fun h ↦ ⟨h.1, Or.inl h.2⟩
    have hout : ∀ r ∈ Γ.hatRegions cap, ∀ x ∈ r, x ∉ Γ.hatU cap := by
      rintro _ ⟨y, hy, rfl⟩ x hx
      exact connectedComponentIn_subset _ _ hx
    have hpre : (GM11.PaintingOrDrawing.drawing D).IsPreRadialDrawing G' := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · change D.U ∩ G'.U = D.V
        rw [hDU, hDV, hU']
        ext x
        constructor
        · rintro ⟨⟨y, hy, rfl⟩, h | ⟨c, hc, hcy⟩⟩
          · rw [← Painting.hatV, ← h1]
            exact ⟨mem_image_of_mem _ (Γ.skU_subset hy), h⟩
          · have hin : hub c ∈ D.Uᶜ := by
              rw [hcompl]
              exact Or.inr (mem_iUnion₂.2 ⟨c, hc, hhub c hc⟩)
            exact absurd (show hub c ∈ D.U by
              rw [hDU, hcy]
              exact mem_image_of_mem _ hy) hin
        · rintro ⟨v, hv, rfl⟩
          exact ⟨mem_image_of_mem _ (Or.inl (Or.inl hv)), Or.inl (G.V_subset_U (h2' ⟨v, hv, rfl⟩))⟩
      · change D.V ⊆ G'.V
        rw [hDV, hV']
        exact h2'.trans subset_union_left
      · intro r hr
        change r ∈ componentsIn (univ \ D.U) at hr
        rcases hRcases r hr with h | ⟨c, hc, rfl⟩
        · obtain ⟨w, ⟨hwr, hwV⟩, huniq⟩ := h3 r h
          refine ⟨w, ⟨hwr, hV' ▸ Or.inl hwV⟩, ?_⟩
          rintro w' ⟨hw'r, hw'⟩
          rw [hV'] at hw'
          rcases hw' with hw' | ⟨c, hc, rfl⟩
          · exact huniq w' ⟨hw'r, hw'⟩
          · exact absurd (hout r h _ hw'r) (fun hn ↦ hn (by
              by_contra hn'
              exact disjoint_left.1 (hBU c hc) (hhub c hc) hn'))
        · refine ⟨hub c, ⟨hhub c hc, hV' ▸ Or.inr ⟨c, hc, rfl⟩⟩, ?_⟩
          rintro w' ⟨hw'r, hw'⟩
          rw [hV'] at hw'
          rcases hw' with hw' | ⟨c', hc', rfl⟩
          · exact absurd (G.V_subset_U hw') (hBG c hc _ hw'r)
          · by_cases he : c = c'
            · rw [he]
            · exact absurd (hhub c' hc') (disjoint_left.1 (hBdisj c hc c' hc' he) hw'r)
      · rintro w ⟨hw, hn⟩
        change w ∈ G'.V at hw
        change w ∉ D.V at hn
        rw [hV'] at hw
        rcases hw with hw | ⟨c, hc, rfl⟩
        · obtain ⟨r, hr, hwr⟩ := h4 w ⟨hw, fun h ↦ hn (by rw [hDV']; exact h)⟩
          exact ⟨r, hRhat hr, hwr⟩
        · exact ⟨B c, hRB c hc, hhub c hc⟩
      · intro e he
        rw [hE'] at he
        obtain ⟨v, hv, w, ⟨hw, hwn⟩, hset⟩ := h5 e he
        refine ⟨v, (by change v ∈ D.V; rw [hDV']; exact hv), w, ⟨hV' ▸ Or.inl hw, fun h ↦ hwn (by
          rw [← hDV']; exact h)⟩, ?_⟩
        rw [hcle e he, hset]
      · intro e he f hf hne v hv r hr w hw h₁ h₂
        rw [hE'] at he hf
        rw [hcle e he] at h₁
        rw [hcle f hf] at h₂
        have hwG : w ∈ G.V := by
          have : w ∈ closure e ∩ G.V := by
            rw [h₁]
            exact Or.inr rfl
          exact this.2
        change r ∈ componentsIn (univ \ D.U) at hr
        change v ∈ D.V at hv
        rcases hRcases r hr with h | ⟨c, hc, rfl⟩
        · exact h6 e he f hf hne v (hDV' ▸ hv) r h w ⟨hw.1, hwG⟩ h₁ h₂
        · exact absurd (G.V_subset_U hwG) (hBG c hc _ hw.1)
    exact ⟨G', hpre, hU', hV', hE'⟩

/-- **A 2-cell painting of Graph Minors XIX has a radial drawing** (Graph Minors XIX, Section 5,
page 337, and Graph Minors XI, Section 3, page 75). -/
theorem Painting.exists_radialDrawing (hS : IsSurface S) (cap : IsCappedSurface S Shat)
    (Γ : Painting S) (h2 : ∀ r ∈ Γ.hatRegions cap, IsOpenDisc r) :
    Nonempty (RadialDrawing cap Γ) := by
  classical
  have hsurf := cap.isSurface
  have hclosedS : IsClosedSurface Shat := by
    refine ⟨hsurf.1, hsurf.2.1, fun x ↦ ?_⟩
    by_contra hx
    have : x ∈ bd Shat := hx
    rw [cap.bd_empty] at this
    exact this
  have : CompactSpace Shat := hsurf.1
  have : T2Space Shat := hsurf.2.1
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨D, W, -, -, hD2, hRfin, hG'⟩ := Γ.exists_hubDrawing hS cap h2
  have hVU : Γ.hatV cap ⊆ Γ.hatU cap := image_mono Γ.V_subset
  have hVfin : (Γ.hatV cap).Finite := Γ.finite_V.image _
  have hbound : ∀ G : Drawing Shat, IsPreRadial (Γ.hatU cap) (Γ.hatV cap) G →
      G.E.ncard ≤ D.V.ncard + 2 * D.E.ncard := by
    intro G hG
    obtain ⟨G', hpre, -, -, hE'⟩ := hG' G hG
    have := GM11.ncard_spokes_le (Γ := D) (Γ' := G') ⟨hD2, hpre⟩ hclosedS
    rwa [hE'] at this
  have hAne : {n | ∃ G : Drawing Shat, IsPreRadial (Γ.hatU cap) (Γ.hatV cap) G ∧ G.E.ncard
    = n}.Nonempty := by
    obtain ⟨G, hG⟩ := exists_preRadial_points hVU hVfin hRfin
    exact ⟨_, G, hG, rfl⟩
  have hbdd : BddAbove {n | ∃ G : Drawing Shat, IsPreRadial (Γ.hatU cap) (Γ.hatV cap) G ∧ G.E.ncard
    = n} :=
    ⟨_, by rintro _ ⟨G, h, rfl⟩; exact hbound G h⟩
  obtain ⟨G, hpre, hc⟩ := Nat.sSup_mem hAne hbdd
  refine ⟨⟨G, hpre, fun G' hG' hsub ↦ ⟨fun w hw ↦ ?_, ?_⟩⟩⟩
  · by_cases hwV : w ∈ Γ.hatV cap
    · exact hpre.2.1 hwV
    obtain ⟨r, hr, hwr⟩ := hG'.2.2.2.1 w ⟨hw, hwV⟩
    obtain ⟨w', ⟨hw'r, hw'⟩, -⟩ := hpre.2.2.1 r hr
    rw [(hG'.2.2.1 r hr).unique ⟨hwr, hw⟩ ⟨hw'r, hsub.1 hw'⟩]
    exact hw'
  · have hle : G'.E.ncard ≤ G.E.ncard := by
      rw [hc]
      exact le_csSup hbdd ⟨G', hG', rfl⟩
    exact (eq_of_subset_of_ncard_le hsub.2 hle G'.finite_edges).ge

/-- Each interior point is inside a closed disc. -/
theorem exists_disc_around {y : S} (hy : IsInteriorPoint y) :
    ∃ E : Set S, IsClosedDisc E ∧ y ∈ discInt E := by
  obtain ⟨U, h, g, c, -, hg0⟩ := hy.exists_ballChart isOpen_univ (mem_univ _) (R := 2) two_pos
  obtain ⟨hZ, hbd⟩ := isClosedDisc_closedBall
  have hsub : Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball 0 2 :=
    Metric.closedBall_subset_ball (by norm_num)
  obtain ⟨hE, hEb⟩ := c.image_disc hZ hsub
  refine ⟨_, hE, ⟨0, by simp, hg0⟩, fun hy' ↦ ?_⟩
  rw [hEb, hbd] at hy'
  obtain ⟨z, hz, hzy⟩ := hy'
  have hz' : ‖z‖ = 1 := by simpa using hz
  have h₁ : z = 0 := by
    have ha := c.hg (show z ∈ Metric.ball (0 : ℂ) 2 from hsub (Metric.sphere_subset_closedBall hz))
    have hb := c.hg (show (0 : ℂ) ∈ Metric.ball (0 : ℂ) 2 by simp)
    rw [← ha, hzy, ← hg0, hb]
  rw [h₁] at hz'
  simp at hz'

/-- The pasted open disc of a cuff is the inside of its closure. -/
theorem IsCappedSurface.cuffDisc_eq_discInt (_hS : IsSurface S) (cap : IsCappedSurface S Shat)
    {Θ : Set S} (hΘ : Θ ∈ cuffs S) : cap.cuffDisc Θ = discInt (closure (cap.cuffDisc Θ)) := by
  have hsurf := cap.isSurface
  have : T2Space Shat := hsurf.2.1
  have hcomp : ∀ Θ' ∈ cuffs S, cap.cuffDisc Θ' ⊆ (range cap.emb)ᶜ := fun Θ' hΘ' x hx ↦ by
    rw [cap.compl_eq]
    exact mem_iUnion₂.2 ⟨Θ', hΘ', hx⟩
  apply Subset.antisymm
  · intro x hx
    refine ⟨subset_closure hx, fun hb ↦ ?_⟩
    rw [cap.cuffDisc_bd Θ hΘ] at hb
    obtain ⟨y, -, rfl⟩ := hb
    exact hcomp Θ hΘ hx (mem_range_self y)
  · rintro x ⟨hxD, hxb⟩
    by_contra hxc
    by_cases hxr : x ∈ range cap.emb
    · obtain ⟨y, rfl⟩ := hxr
      rw [cap.cuffDisc_bd Θ hΘ] at hxb
      have hyΘ : y ∉ Θ := fun h ↦ hxb (mem_image_of_mem _ h)
      by_cases hy : y ∈ bd S
      · have hΘ' : connectedComponentIn (bd S) y ∈ cuffs S := ⟨y, hy, rfl⟩
        have hne : connectedComponentIn (bd S) y ≠ Θ := fun h ↦
          hyΘ (h ▸ mem_connectedComponentIn hy)
        have hin : cap.emb y ∈ closure (cap.cuffDisc (connectedComponentIn (bd S) y)) := by
          apply discBd_subset
          rw [cap.cuffDisc_bd _ hΘ']
          exact mem_image_of_mem _ (mem_connectedComponentIn hy)
        exact disjoint_left.1 (cap.cuffDisc_disjoint _ hΘ' _ hΘ hne) hin hxD
      · have hyI : IsInteriorPoint y := by
          by_contra hn
          exact hy hn
        obtain ⟨E, hE, hyE⟩ := exists_disc_around hyI
        obtain ⟨hE', hEb⟩ := isClosedDisc_image hE cap.isEmbedding
        have hopen : IsOpen (discInt (cap.emb '' E)) := hE'.isOpen_discInt hsurf.2.2
        have hmem : cap.emb y ∈ discInt (cap.emb '' E) := by
          refine ⟨mem_image_of_mem _ hyE.1, fun h ↦ ?_⟩
          rw [hEb] at h
          obtain ⟨z, hz, hzy⟩ := h
          exact hyE.2 (cap.isEmbedding.injective hzy ▸ hz)
        obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.1 hxD _ hopen hmem
        obtain ⟨z, -, rfl⟩ := discInt_subset _ hw₁
        exact hcomp Θ hΘ hw₂ (mem_range_self z)
    · have hmem : x ∈ ⋃ Θ' ∈ cuffs S, cap.cuffDisc Θ' := by
        rw [← cap.compl_eq]
        exact hxr
      obtain ⟨Θ', hΘ', hx'⟩ := mem_iUnion₂.1 hmem
      by_cases he : Θ' = Θ
      · exact hxc (he ▸ hx')
      · exact disjoint_left.1 (cap.cuffDisc_disjoint _ hΘ' _ hΘ he) (subset_closure hx') hxD

theorem IsCappedSurface.closure_cuffDisc (hS : IsSurface S) (cap : IsCappedSurface S Shat)
    {Θ : Set S} (hΘ : Θ ∈ cuffs S) :
    closure (cap.cuffDisc Θ) = cap.cuffDisc Θ ∪ cap.emb '' Θ := by
  rw [← cap.cuffDisc_bd Θ hΘ]
  ext x
  constructor
  · intro hx
    by_cases hb : x ∈ discBd (closure (cap.cuffDisc Θ))
    · exact Or.inr hb
    · left
      rw [cap.cuffDisc_eq_discInt hS hΘ]
      exact ⟨hx, hb⟩
  · rintro (hx | hx)
    · exact subset_closure hx
    · exact discBd_subset _ hx

/-- **Every internally 3-connected painting is 2-cell** (Graph Minors XIX, Section 5, page 337), for
its regions in `Σ̂`. A region inside a pasted disc is that disc. For any other region `r`, an
`O`-arc
`F` in `r` misses `V(Γ)` and `bd(Σ)`, so by internal 3-connectivity it bounds a disc in `Σ` with no
vertex. This disc has no point of `U(Γ)`, because the ends of an edge inside it would be vertices in
it, so the disc lies in `r`. Then Graph Minors VII, (4.2), says `r` is an open disc. -/
theorem Painting.IsInternallyThreeConnected.hatRegions_isOpenDisc {Γ : Painting S}
    (h3 : Γ.IsInternallyThreeConnected) (hS : IsSurface S) (cap : IsCappedSurface S Shat) :
    ∀ r ∈ Γ.hatRegions cap, IsOpenDisc r := by
  classical
  have hS' := hS
  obtain ⟨hcomp, hT2, hmanS⟩ := hS
  have hsurf := cap.isSurface
  have hclosedS : IsClosedSurface Shat := by
    refine ⟨hsurf.1, hsurf.2.1, fun x ↦ ?_⟩
    by_contra hx
    have : x ∈ bd Shat := hx
    rw [cap.bd_empty] at this
    exact this
  have : CompactSpace Shat := hsurf.1
  have : T2Space Shat := hsurf.2.1
  have : ConnectedSpace Shat := cap.connected
  have : LocallyConnectedSpace Shat := GM11.IsClosedSurface.locallyConnectedSpace hclosedS
  have hman : ∀ x : Shat, IsManifoldPoint x := hsurf.2.2
  set ι := cap.emb with hιdef
  have hιc : IsClosedEmbedding ι :=
    IsClosedEmbedding.of_continuous_injective_isClosedMap cap.isEmbedding.continuous
      cap.isEmbedding.injective cap.isEmbedding.continuous.isClosedMap
  have hUc : IsClosed (Γ.hatU cap) := hιc.isClosedMap _ Γ.isClosed_U
  obtain ⟨-, hcfin, -⟩ := cuff_statement.{u} S hS'
  have hcapopen : ∀ Θ ∈ cuffs S, IsOpen (cap.cuffDisc Θ) := fun Θ hΘ ↦ by
    rw [cap.cuffDisc_eq_discInt hS' hΘ]
    exact (cap.cuffDisc_closedDisc Θ hΘ).isOpen_discInt hman
  have hcaprange : ∀ Θ ∈ cuffs S, ∀ x ∈ cap.cuffDisc Θ, x ∉ range ι := fun Θ hΘ x hx hr ↦ by
    have : x ∈ (range cap.emb)ᶜ := by
      rw [cap.compl_eq]
      exact mem_iUnion₂.2 ⟨Θ, hΘ, hx⟩
    exact this hr
  have hbdsub : ∀ y ∈ bd S, ι y ∈ ⋃ Θ ∈ cuffs S, closure (cap.cuffDisc Θ) := fun y hy ↦ by
    have hΘ : connectedComponentIn (bd S) y ∈ cuffs S := ⟨y, hy, rfl⟩
    refine mem_iUnion₂.2 ⟨_, hΘ, ?_⟩
    rw [cap.closure_cuffDisc hS' hΘ]
    exact Or.inr (mem_image_of_mem _ (mem_connectedComponentIn hy))
  let Y₀ : Set Shat := (⋃ Θ ∈ cuffs S, closure (cap.cuffDisc Θ))ᶜ
  have hY₀ : IsOpen Y₀ := (hcfin.isClosed_biUnion fun _ _ ↦ isClosed_closure).isOpen_compl
  have hY₀sub : ∀ w ∈ Y₀, w ∈ range ι := fun w hw ↦ by
    by_contra hn
    have hmem : w ∈ ⋃ Θ ∈ cuffs S, cap.cuffDisc Θ := by
      rw [← cap.compl_eq]
      exact hn
    obtain ⟨Θ, hΘ, hwΘ⟩ := mem_iUnion₂.1 hmem
    exact hw (mem_iUnion₂.2 ⟨Θ, hΘ, subset_closure hwΘ⟩)
  have hbdU : ∀ y ∈ bd S, ι y ∈ Γ.hatU cap := fun y hy ↦ mem_image_of_mem _ (Γ.bd_subset hy)
  rintro _ ⟨x, hx, rfl⟩
  set r := connectedComponentIn (Γ.hatU cap)ᶜ x with hr
  have hrpre : IsPreconnected r := isPreconnected_connectedComponentIn
  have hrU : r ⊆ (Γ.hatU cap)ᶜ := connectedComponentIn_subset _ _
  have hrx : x ∈ r := mem_connectedComponentIn hx
  by_cases hxcap : ∃ Θ ∈ cuffs S, x ∈ cap.cuffDisc Θ
  · obtain ⟨Θ, hΘ, hxΘ⟩ := hxcap
    have hcapU : cap.cuffDisc Θ ⊆ (Γ.hatU cap)ᶜ := fun w hw ⟨y, _, hy⟩ ↦
      hcaprange Θ hΘ w hw ⟨y, hy⟩
    have hconn : IsPreconnected (cap.cuffDisc Θ) := by
      rw [cap.cuffDisc_eq_discInt hS' hΘ]
      exact (cap.cuffDisc_closedDisc Θ hΘ).isPreconnected_discInt
    have h₁ : cap.cuffDisc Θ ⊆ r := hconn.subset_connectedComponentIn hxΘ hcapU
    have h₂ : r ⊆ cap.cuffDisc Θ := by
      refine hrpre.subset_left_of_subset_union (hcapopen Θ hΘ)
        (isClosed_closure (s := cap.cuffDisc Θ)).isOpen_compl ?_ (fun w hw ↦ ?_) ⟨x, hrx, hxΘ⟩
      · exact disjoint_left.2 fun w hw hn ↦ hn (subset_closure hw)
      · by_cases hwc : w ∈ cap.cuffDisc Θ
        · exact Or.inl hwc
        · refine Or.inr fun hcl ↦ ?_
          rw [cap.closure_cuffDisc hS' hΘ] at hcl
          rcases hcl with h | ⟨y, hy, rfl⟩
          · exact hwc h
          · have hyb : y ∈ bd S := by
              obtain ⟨z, hz, rfl⟩ := hΘ
              exact connectedComponentIn_subset _ _ hy
            exact hrU hw (hbdU y hyb)
    rw [Subset.antisymm h₂ h₁, cap.cuffDisc_eq_discInt hS' hΘ]
    exact isOpenDisc_discInt hman (cap.cuffDisc_closedDisc Θ hΘ)
  · have hxr : ∃ y, ι y = x := by
      by_contra hn
      have hmem : x ∈ ⋃ Θ ∈ cuffs S, cap.cuffDisc Θ := by
        rw [← cap.compl_eq]
        exact hn
      obtain ⟨Θ, hΘ, hxΘ⟩ := mem_iUnion₂.1 hmem
      exact hxcap ⟨Θ, hΘ, hxΘ⟩
    have hxY : x ∈ Y₀ := by
      intro hmem
      obtain ⟨Θ, hΘ, hcl⟩ := mem_iUnion₂.1 hmem
      rw [cap.closure_cuffDisc hS' hΘ] at hcl
      rcases hcl with h | ⟨y, hy, rfl⟩
      · exact hxcap ⟨Θ, hΘ, h⟩
      · have hyb : y ∈ bd S := by
          obtain ⟨z, hz, rfl⟩ := hΘ
          exact connectedComponentIn_subset _ _ hy
        exact hx (hbdU y hyb)
    have hrY : r ⊆ Y₀ := by
      refine hrpre.subset_left_of_subset_union hY₀
        (isOpen_biUnion fun Θ hΘ ↦ hcapopen Θ hΘ) ?_ (fun w hw ↦ ?_) ⟨x, hrx, hxY⟩
      · refine disjoint_left.2 fun w hw hn ↦ ?_
        obtain ⟨Θ, hΘ, hwΘ⟩ := mem_iUnion₂.1 hn
        exact hw (mem_iUnion₂.2 ⟨Θ, hΘ, subset_closure hwΘ⟩)
      · by_cases hwc : w ∈ ⋃ Θ ∈ cuffs S, cap.cuffDisc Θ
        · exact Or.inr hwc
        · left
          intro hmem
          obtain ⟨Θ, hΘ, hcl⟩ := mem_iUnion₂.1 hmem
          rw [cap.closure_cuffDisc hS' hΘ] at hcl
          rcases hcl with h | ⟨y, hy, rfl⟩
          · exact hwc (mem_iUnion₂.2 ⟨Θ, hΘ, h⟩)
          · have hyb : y ∈ bd S := by
              obtain ⟨z, hz, rfl⟩ := hΘ
              exact connectedComponentIn_subset _ _ hy
            exact hrU hw (hbdU y hyb)
    have hrO : IsOpen r := hUc.isOpen_compl.connectedComponentIn
    have hmain : ∀ F : Set Shat, F ⊆ r → IsOArc F →
        ∃ Δ : Set Shat, Δ ⊆ r ∧ IsClosedDisc Δ ∧ discBd Δ = F := by
      intro F hFr hF
      have hFrange : F ⊆ range ι := fun w hw ↦ hY₀sub w (hrY (hFr hw))
      have hFimg : ι '' (ι ⁻¹' F) = F := image_preimage_eq_of_subset hFrange
      set F₀ : Set S := ι ⁻¹' F with hF₀
      have hF₀O : IsOArc F₀ := by
        obtain ⟨φ⟩ := hF
        exact ⟨φ.trans ((Homeomorph.setCongr hFimg).symm.trans
          (cap.isEmbedding.homeomorphImage F₀).symm)⟩
      have hF₀U : ∀ y ∈ F₀, y ∉ Γ.U := fun y hy hyU ↦
        hrU (hFr hy) (mem_image_of_mem _ hyU)
      have hF₀b : F₀ ∩ bd S = ∅ := by
        refine eq_empty_of_forall_notMem fun y hy ↦ hF₀U y hy.1 (Γ.bd_subset hy.2)
      have hF₀V : F₀ ∩ Γ.V = ∅ := by
        refine eq_empty_of_forall_notMem fun y hy ↦ hF₀U y hy.1 (Γ.V_subset hy.2)
      obtain ⟨Δ₀, hΔ₀, hbΔ₀, hVΔ₀⟩ := h3.2 F₀ hF₀O
        (fun y hy ↦ absurd hy.2 (hF₀U y hy.1)) (by rw [hF₀b]; exact finite_empty)
        (by rw [hF₀b, hF₀V]; simp)
      have hΔV : ∀ y ∈ Δ₀, y ∉ Γ.V := fun y hy hyV ↦ by
        have := hVΔ₀ ⟨hy, hyV⟩
        exact hF₀U y this (Γ.V_subset hyV)
      have hΔU : ∀ y ∈ Δ₀, y ∉ Γ.U := by
        intro y hy hyU
        obtain ⟨c, hc, hyc⟩ := exists_arcComp_superset (F := Γ.U \ Γ.V)
          (isPathConnected_singleton y) (singleton_subset_iff.2 ⟨hyU, hΔV y hy⟩)
        have hyc' : y ∈ c := hyc rfl
        have hyint : y ∈ discInt Δ₀ := ⟨hy, fun h ↦ by
          rw [hbΔ₀] at h
          exact hF₀U y h hyU⟩
        have hcsub : c ⊆ discInt Δ₀ := by
          refine hc.2.2.1.isConnected.isPreconnected.subset_left_of_subset_union
            (hΔ₀.isOpen_discInt hmanS) (hΔ₀.isClosed.isOpen_compl) ?_
              (fun w hw ↦ ?_) ⟨y, hyc', hyint⟩
          · exact disjoint_left.2 fun w hw hn ↦ hn hw.1
          · by_cases hwΔ : w ∈ Δ₀
            · refine Or.inl ⟨hwΔ, fun h ↦ ?_⟩
              rw [hbΔ₀] at h
              exact hF₀U w h (hc.2.1 hw).1
            · exact Or.inr hwΔ
        have hcl : closure c ⊆ Δ₀ := closure_minimal (hcsub.trans (discInt_subset _)) hΔ₀.isClosed
        have hne : (tilde c).Nonempty := by
          rcases Γ.size_cases hc with h | h <;>
          · by_contra hn
            rw [not_nonempty_iff_eq_empty.1 hn] at h
            simp at h
        obtain ⟨v, hv⟩ := hne
        exact hΔV v (hcl hv.1) (Γ.tilde_subset_V hc hv)
      obtain ⟨hD, hDb⟩ := isClosedDisc_image hΔ₀ cap.isEmbedding
      refine ⟨ι '' Δ₀, ?_, hD, by rw [hDb, hbΔ₀, hFimg]⟩
      obtain ⟨φ⟩ := hF
      have hFne : (F : Set Shat).Nonempty := ⟨_, (φ 1).2⟩
      obtain ⟨p, hp⟩ := hFne
      have hpr : connectedComponentIn (Γ.hatU cap)ᶜ x = connectedComponentIn (Γ.hatU cap)ᶜ p :=
        connectedComponentIn_eq (hFr hp)
      rw [hr, hpr]
      have hpre : IsPreconnected (ι '' Δ₀) :=
        ((IsClosedDisc.isPathConnected hΔ₀).image
          cap.isEmbedding.continuous).isConnected.isPreconnected
      refine hpre.subset_connectedComponentIn ?_ ?_
      · rw [← hFimg] at hp
        obtain ⟨y, hy, rfl⟩ := hp
        refine ⟨y, ?_, rfl⟩
        have : y ∈ discBd Δ₀ := by
          rw [hbΔ₀]
          exact hy
        exact discBd_subset _ this
      · rintro _ ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
        exact hΔU y hy (hιc.injective hzy ▸ hz)
    rcases open_disc.{u} Shat r hclosedS inferInstance ⟨⟨x, hrx⟩, hrpre⟩ hrO hmain with h | h
    · obtain ⟨c, hc⟩ := h3.1
      obtain ⟨y, hy⟩ := hc.1
      have hmem : ι y ∈ r := by
        rw [h.2]
        exact mem_univ _
      exact absurd (mem_image_of_mem ι (hc.2.1 hy).1) (hrU hmem)
    · exact h

/-- An internally 3-connected painting has a radial drawing. This is the case used in the paper. -/
theorem Painting.IsInternallyThreeConnected.nonempty_radialDrawing {Γ : Painting S}
    (h3 : Γ.IsInternallyThreeConnected) (hS : IsSurface S) (cap : IsCappedSurface S Shat) :
    Nonempty (RadialDrawing cap Γ) :=
  Γ.exists_radialDrawing hS cap (h3.hatRegions_isOpenDisc hS cap)

end Main

end GraphMinor.GM19
