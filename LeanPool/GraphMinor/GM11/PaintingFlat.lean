/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section64b
public import LeanPool.GraphMinor.GM11.PaintingTwoCell

/-!
# Claim (2) of (6.4) of Graph Minors XI, for paintings

`exists_flat_painting` is `exists_flat_regions` for a painting. It runs on the drawing of the
boundaries of the cells, and
the drawing made from `Γ'` by adding stars in the cells. Only the regions of the painting enter the
cover, so only edges of
`Γ'` are used.

`exists_oArc_of_null_painting` is claim (2) of (6.4). The closed set is the union of closed discs in
the cells that miss
the vertices of `A ∩ B` (`exists_disc_cut`).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Metric Filter Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- A closed disc has a closed sub-disc that misses a given finite part of its boundary, and that
includes all of
the disc outside an open set around that part. The sub-disc is the disc cut by a half-plane at each
point. -/
theorem exists_disc_cut {Δ P O : Set S} (hΔ : IsClosedDisc Δ) (hP : P.Finite) (hPb : P ⊆ discBd Δ)
  (hO : IsOpen O)
    (hPO : P ⊆ O) : ∃ E, IsClosedDisc E ∧ E ⊆ Δ ∧ Disjoint E P ∧ Δ \ O ⊆ E := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  have hP' : (h '' P).Finite := hP.image h
  -- Near each point of `P`, the chart stays in `O`.
  have hnear : ∀ p ∈ h '' P, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ closedBall (0 : ℂ) 1, ‖z - p‖ ^ 2 ≤ 2 * ε
    → g z ∈ O := by
    rintro _ ⟨x, hx, rfl⟩
    have hxΔ : x ∈ Δ := discBd_subset _ (hPb hx)
    have hhx : h x ∈ closedBall (0 : ℂ) 1 := c.hm hxΔ
    have hcont := c.gc (h x) hhx
    have hmem : O ∈ 𝓝 (g (h x)) := hO.mem_nhds (by rw [c.gh hxΔ]; exact hPO hx)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp (hcont hmem)
    have hpos : 0 < δ ^ 2 / 4 := by positivity
    filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε z hz hle
    refine hball ⟨?_, hz⟩
    have h₁ : ‖z - h x‖ ^ 2 < δ ^ 2 := by nlinarith [hε.2]
    have h₂ : ‖z - h x‖ < δ := lt_of_pow_lt_pow_left₀ 2 hδ.le h₁
    rwa [mem_ball, dist_eq_norm]
  have hall := (Set.Finite.eventually_all hP').mpr hnear
  obtain ⟨ε, hε, hεlt⟩ := (hall.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num))).exists
  have hε₀ : 0 < ε := hεlt.1
  have hε₁ : ε < 1 / 2 := hεlt.2
  let K : Set ℂ := closedBall 0 1 ∩ ⋂ p ∈ h '' P, {z | (z * (starRingEnd ℂ) p).re ≤ 1 - ε}
  have hpn : ∀ p ∈ h '' P, ‖p‖ = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have : h x ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h (hPb hx)
    simpa using this
  have hre : ∀ z p : ℂ, ‖z - p‖ ^ 2 = ‖z‖ ^ 2 + ‖p‖ ^ 2 - 2 * (z * (starRingEnd ℂ) p).re := by
    intro z p
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub]
  have hKcv : Convex ℝ K := by
    refine (convex_closedBall _ _).inter (convex_iInter₂ fun p _ => ?_)
    intro x hx y hy a b ha hb hab
    simp only [mem_ofPred_eq, Complex.real_smul] at hx hy ⊢
    have e : ((a : ℂ) * x + (b : ℂ) * y) * (starRingEnd ℂ) p = (a : ℂ) * (x * (starRingEnd ℂ) p) +
        (b : ℂ) * (y * (starRingEnd ℂ) p) := by ring
    rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    nlinarith
  have hKcl : IsClosed K := by
    refine isClosed_closedBall.inter (isClosed_biInter fun p _ => ?_)
    exact isClosed_le (by fun_prop) continuous_const
  have hKb : Bornology.IsBounded K := isBounded_closedBall.subset inter_subset_left
  have hball : ball (0 : ℂ) (1 / 2) ⊆ K := fun z hz => by
    have hz' : ‖z‖ < 1 / 2 := by simpa using hz
    refine ⟨?_, mem_iInter₂.mpr fun p hp => ?_⟩
    · simp only [mem_closedBall, dist_zero_right]
      linarith
    have h₁ : (z * (starRingEnd ℂ) p).re ≤ ‖z * (starRingEnd ℂ) p‖ := Complex.re_le_norm _
    rw [norm_mul, RCLike.norm_conj, hpn p hp, mul_one] at h₁
    change _ ≤ _
    linarith
  have hKint : (interior K).Nonempty := ⟨0, mem_interior.mpr ⟨_, hball, isOpen_ball, by simp⟩⟩
  obtain ⟨hKd, -⟩ := isClosedDisc_of_convex hKcv hKint hKb hKcl
  refine ⟨g '' K, (c.disc_g inter_subset_left hKd).1, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact c.gm hz.1
  · refine disjoint_left.mpr ?_
    rintro _ ⟨z, hz, rfl⟩ hzP
    have hpm : h (g z) ∈ h '' P := mem_image_of_mem h hzP
    rw [c.hg hz.1] at hpm
    have h₁ := mem_iInter₂.mp hz.2 z hpm
    have h₂ := hre z z
    rw [sub_self, norm_zero, hpn z hpm] at h₂
    change _ ≤ _ at h₁
    nlinarith
  · rintro x ⟨hxΔ, hxO⟩
    refine ⟨h x, ⟨c.hm hxΔ, mem_iInter₂.mpr fun p hp => ?_⟩, c.gh hxΔ⟩
    change _ ≤ _
    by_contra hlt
    have hn : ‖h x‖ ≤ 1 := by simpa using c.hm hxΔ
    have h₁ := hre (h x) p
    rw [hpn p hp] at h₁
    refine hxO ?_
    have hsq : ‖h x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (h x)]
    rw [one_pow] at h₁
    have h₂ := hε p hp (h x) (c.hm hxΔ) (by push Not at hlt; linarith)
    rwa [c.gh hxΔ] at h₂


/-- A drawing whose point set is a finite family of `O`-arcs that meet only in a finite set `V₀`. -/
theorem exists_drawing_on_oArcs (_hS : IsClosedSurface S) {ι : Type*} {I₀ : Set ι}
  (hI : I₀.Finite) {F : ι → Set S}
    {V₀ : Set S} (hfin : V₀.Finite) (hF : ∀ i ∈ I₀, IsOArc (F i)) (hne : ∀ i ∈ I₀,
      (V₀ ∩ F i).Nonempty)
    (hmeet : ∀ i ∈ I₀, ∀ j ∈ I₀, i ≠ j → F i ∩ F j ⊆ V₀) :
    ∃ D : Drawing S, D.U = V₀ ∪ ⋃ i ∈ I₀, F i ∧ D.V = V₀ := by
  classical
  have key : ∀ T : Finset ι, (∀ e ∈ T, e ∈ I₀) →
      ∃ D : Drawing S, D.U = V₀ ∪ ⋃ e ∈ T, F e ∧ D.V = V₀ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨pointsDrawing hfin, by simp [pointsDrawing], rfl⟩
    | insert e T he ih =>
      intro hT
      obtain ⟨D, hU', hV'⟩ := ih fun f hf => hT f (Finset.mem_insert_of_mem hf)
      have hee := hT e (Finset.mem_insert_self _ _)
      obtain ⟨C, hCU, hCV⟩ := exists_drawing_on_oArc (hF e hee) (hfin.inter_of_left _)
        (hne e hee) inter_subset_right
      have hmeet' : D.U ∩ C.U ⊆ D.V ∩ C.V := by
        rw [hU', hV', hCU, hCV]
        rintro x ⟨hx | hx, hxb⟩
        · exact ⟨hx, hx, hxb⟩
        · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
          have hfe : e ≠ f := fun h => he (h ▸ hf)
          have hxV := hmeet e hee f (hT f (Finset.mem_insert_of_mem hf)) hfe ⟨hxb, hxf⟩
          exact ⟨hxV, hxV, hxb⟩
      refine ⟨D.glue C hmeet', ?_, ?_⟩
      · change D.U ∪ C.U = _
        rw [hU', hCU]
        ext x
        simp only [mem_union, mem_iUnion, Finset.mem_insert, exists_prop]
        constructor
        · rintro ((h | ⟨f, hf, h⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨f, Or.inr hf, h⟩
          · exact Or.inr ⟨e, Or.inl rfl, h⟩
        · rintro (h | ⟨f, rfl | hf, h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
          · exact Or.inl (Or.inr ⟨f, hf, h⟩)
      · change D.V ∪ C.V = V₀
        rw [hV', hCV]
        exact union_eq_left.mpr inter_subset_left
  obtain ⟨D, hD, hV⟩ := key hI.toFinset fun e he => hI.mem_toFinset.mp he
  refine ⟨D, ?_, hV⟩
  rw [hD]
  simp only [hI.mem_toFinset]

variable [ConnectedSpace S] {Γ : Painting S} {Γ' : Drawing S} {θ : ℕ}
  {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}

/-- A 2-cell painting with a cell that has no vertex is in a sphere. -/
theorem sphere_of_free_cell (hS : IsClosedSurface S)
    (hrad : PreRad (PaintingOrDrawing.painting Γ) Γ') {e : Set S} (he : e ∈ Γ.E)
    (hfree : closure e ∩ Γ.V = ∅) : IsSphere S :=
  (free_cell_disc_cover hS hrad he hfree).1

/-- A cell of a 2-cell painting in a surface other than a sphere has a vertex. -/
theorem cell_has_vertex (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    (hrad : PreRad (PaintingOrDrawing.painting Γ) Γ') {e : Set S} (he : e ∈ Γ.E) :
      (closure e ∩ Γ.V).Nonempty := by
  by_contra h
  exact hns (sphere_of_free_cell hS hrad he (not_nonempty_iff_eq_empty.mp h))

/-- The drawing `D` of the boundaries of the cells of a painting, and the radial drawing `G` of `D`
made from `Γ'` by
adding stars in the cells. -/
theorem exists_cell_drawings (hS : IsClosedSurface S) (hrad : (PaintingOrDrawing.painting
  Γ).IsRadialDrawing Γ')
    (hE : Γ.E.Nonempty) (hv : ∀ e ∈ Γ.E, (closure e ∩ Γ.V).Nonempty) :
    ∃ D G : Drawing S, D.U = Γ.V ∪ (⋃ e ∈ Γ.E, discBd (closure e)) ∧ D.V = Γ.V ∧ D.R
      = Γ.R ∪ cellInt '' Γ.E ∧
      (PaintingOrDrawing.drawing D).IsRadialDrawing G ∧ D.E.Nonempty ∧ Γ'.IsSubdrawing G ∧
      G.U ⊆ Γ'.U ∪ Γ.U ∧ (∀ h ∈ G.E, ∀ r ∈ Γ.R, h ⊆ r → h ∈ Γ'.E) ∧ ∀ x ∈ G.V, x ∉ Γ.U → x ∈ Γ'.V
        := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hpre : PreRad (PaintingOrDrawing.painting Γ) Γ' := ⟨hrad.1, hrad.2.1⟩
  have hmax : RadMax (PaintingOrDrawing.painting Γ) Γ' := hrad.2.2
  obtain ⟨e₀, he₀⟩ := hE
  obtain ⟨y₀, -⟩ := he₀.1
  have hneS : Nonempty S := ⟨y₀⟩
  have hU : IsClosed Γ.U := cell_isClosed_U hpre
  obtain ⟨c, K, hst⟩ := exists_cellStars (Γ := Γ)
  obtain ⟨G, hG⟩ := exists_star_drawing hpre hst hS
  have hbd : ∀ e ∈ Γ.E, Γ.V ∩ closure e ⊆ discBd (closure e) := fun e he x hx =>
    Cell.closure_inter_V_subset hS he ⟨hx.2, hx.1⟩
  obtain ⟨D, hDU, hDV⟩ := exists_boundary_drawing hS hU Γ.finite_V Subset.rfl fun e he => by
    obtain ⟨x, hx, hxV⟩ := hv e he
    exact ⟨x, hxV, hbd e he ⟨hxV, hx⟩⟩
  have hDR : D.R = Γ.R ∪ cellInt '' Γ.E :=
    boundary_R hS hrad.1.2 Subset.rfl Γ.V_subset_U hbd hDU
  have hGrad := radial_of_stars hpre hst hS hG hDU hDV hv hmax hDR
  have hedge : ∀ x ∈ D.U, x ∉ D.V → ∃ a ∈ D.E, x ∈ a := fun x hx hn =>
    exists_mem_arcComponent ⟨hx, hn⟩
  have hDE : D.E.Nonempty := by
    have hinf := infinite_of_isOArc (Cell.isClosedDisc_closure he₀).isOArc_discBd
    obtain ⟨x, hx, hn⟩ := hinf.exists_notMem_finite Γ.finite_V
    have hxD : x ∈ D.U := by
      rw [hDU]
      exact Or.inr (mem_iUnion₂.mpr ⟨e₀, he₀, hx⟩)
    obtain ⟨a, ha, -⟩ := hedge x hxD (hDV ▸ hn)
    exact ⟨a, ha⟩
  have hoff : ∀ {a x}, a ∈ Γ.R → x ∈ a → x ∉ Γ.U := by
    rintro a x ⟨y, -, rfl⟩ hx
    exact (connectedComponentIn_subset _ _ hx).2
  have hsub : Γ'.IsSubdrawing G := ⟨fun x hx => hG.V ▸ Or.inl hx, fun e he => by
    have : e ∈ G.E := hG.E ▸ Or.inl he
    exact this⟩
  have hstarU : G.U ⊆ Γ'.U ∪ Γ.U := by
    rw [hG.U]
    refine union_subset_union_right _ (iUnion₂_subset fun t ht => ?_)
    have hb := Cell.closure_inter_V_subset hS ht.1 ⟨ht.2.2, ht.2.1⟩
    exact (star_subset_closure hst ht.1 hb).trans (closure_subset_cell_U hpre ht.1)
  refine ⟨D, G, hDU, hDV, hDR, hGrad, hDE, hsub, hstarU, ?_, ?_⟩
  · intro h hh r hr hhr
    have hh' : h ∈ G.E := hh
    rw [hG.E] at hh'
    rcases hh' with h₁ | ⟨t, ht, rfl⟩
    · exact h₁
    · exfalso
      obtain ⟨y, hy⟩ := (show _ ∈ G.E from hh).1
      have hb := Cell.closure_inter_V_subset hS ht.1 ⟨ht.2.2, ht.2.1⟩
      exact hoff hr (hhr hy) (closure_subset_cell_U hpre ht.1 (star_subset_closure hst ht.1 hb
        hy.1))
  · intro x hxV hxU
    have hxV' : x ∈ G.V := hxV
    rw [hG.V] at hxV'
    rcases hxV' with h₁ | ⟨t, ht, rfl⟩
    · exact h₁
    · exact absurd (closure_subset_cell_U hpre ht.1 (hst.hub t.1 ht.1).1) hxU

/-- `exists_flat_regions` for a painting. -/
theorem exists_flat_painting (hS : IsClosedSurface S) (hrad : (PaintingOrDrawing.painting
  Γ).IsRadialDrawing Γ')
    (hE : Γ.E.Nonempty) (hv : ∀ e ∈ Γ.E, (closure e ∩ Γ.V).Nonempty) (hθ : 1 ≤ θ)
    (hnull : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ
      → IsNullHomotopicOArc C.U)
    {S₀ : Set S} (hS₀V : S₀ ⊆ Γ.V) (hS₀f : S₀.Finite) (hord : S₀.ncard < θ) :
    ∃ D : S → Set S, (∀ s ∈ S₀, IsOpen (D s)) ∧ (∀ s ∈ S₀, s ∈ D s) ∧
      Flat ((⋃ r ∈ Γ.R, r) ∪ ⋃ s ∈ S₀, D s) := by
  obtain ⟨D, G, -, hDV, hDR, hGrad, hDE, hsub, -, hh₁, hh₂⟩ := exists_cell_drawings hS hrad hE hv
  have hoff : ∀ {a x}, a ∈ Γ.R → x ∈ a → x ∉ Γ.U := by
    rintro a x ⟨y, -, rfl⟩ hx
    exact (connectedComponentIn_subset _ _ hx).2
  exact exists_flat_regions_of_sub (Γ := D) (Γ' := G) hS hDE hGrad hθ hsub
    (hDR ▸ subset_union_left) hh₁
    (fun r hr x hx hxV => hh₂ x hxV (hoff hr hx)) hnull (hDV ▸ hS₀V) (hS₀V.trans hrad.2.1.2.1) hS₀f
      hord

omit [ConnectedSpace S] in
/-- A painting with a cell does not fill the surface. -/
theorem exists_notMem_painting_U (hS : IsClosedSurface S) (hrad : PreRad
  (PaintingOrDrawing.painting Γ) Γ')
    (hE : Γ.E.Nonempty) : ∃ y, y ∉ Γ.U := by
  classical
  have hU : IsClosed Γ.U := cell_isClosed_U hrad
  obtain ⟨e, he⟩ := hE
  have hd := Cell.isClosedDisc_closure he
  obtain ⟨b, hb, hbV⟩ := (infinite_of_isOArc hd.isOArc_discBd).exists_notMem_finite Γ.finite_V
  have hfe : Γ.E.Finite := Γ.finite_edges
  let W : Set S := (Γ.V ∪ ⋃ f ∈ Γ.E \ {e}, closure f)ᶜ
  have hW : IsOpen W := (Γ.finite_V.isClosed.union ((hfe.subset sdiff_subset).isClosed_biUnion
    fun _ _ => isClosed_closure)).isOpen_compl
  have hbW : b ∈ W := by
    rintro (h | h)
    · exact hbV h
    · obtain ⟨f, hf, hbf⟩ := mem_iUnion₂.mp h
      exact hbV (Cell.closure_inter_subset_V hS hU he hf.1 (Ne.symm hf.2) ⟨discBd_subset _ hb, hbf⟩)
  have hbf : b ∈ closure (closure e)ᶜ := by
    have : b ∈ frontier (closure e) := by
      rw [IsClosedDisc.frontier_eq_discBd hS hd]
      exact hb
    exact (frontier_eq_closure_inter_closure.subset this).2
  obtain ⟨y, hyW, hye⟩ := mem_closure_iff.mp hbf W hW hbW
  refine ⟨y, fun hyU => ?_⟩
  rcases Cell.mem_V_or_cell Γ hyU with h | ⟨f, hf, hyf⟩
  · exact hyW (Or.inl h)
  · by_cases hfe' : f = e
    · exact hye (subset_closure (hfe' ▸ hyf))
    · exact hyW (Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfe'⟩, subset_closure hyf⟩))

/-- **Claim (2) of (6.4)** (pages 90–91), for a painting. -/
theorem exists_oArc_of_null_painting (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
  (hE : Γ.E.Nonempty)
    (hrad : (PaintingOrDrawing.painting Γ).IsRadialDrawing Γ') (hθ : 1 ≤ θ)
    (hd : IsDerivedSlope (PaintingOrDrawing.painting Γ) Γ' θ T ins) {A B : Hypergraph S (Set S)}
    (hsep : Γ.toHypergraph.IsSeparation A B) (hord : separationOrder A B < θ)
    (hA : ∀ F : Set S, F ⊆ PaintingOrDrawing.underlying A → IsOArc F → IsNullHomotopicOArc F) :
    ∃ F : Set S, IsOArc F ∧ F ⊆ PaintingOrDrawing.underlying B \ PaintingOrDrawing.underlying A ∧
      ¬ IsNullHomotopicOArc F := by
  classical
  by_contra hno
  push Not at hno
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hpre : PreRad (PaintingOrDrawing.painting Γ) Γ' := ⟨hrad.1, hrad.2.1⟩
  have hU : IsClosed Γ.U := cell_isClosed_U hpre
  have hnull : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ
    → IsNullHomotopicOArc C.U :=
    fun C hC hCs hl => null_of_short hd hC hCs hl
  have hS₀V : (A ∩ B).vertexSet ⊆ Γ.V := fun x hx => hsep.left_le.vertexSet_subset hx.1
  have hS₀f := (A ∩ B).vertexSet_finite
  obtain ⟨D, hDo, hsD, hfl⟩ := exists_flat_painting hS hrad hE (fun e he
    => cell_has_vertex hS hns hpre he) hθ hnull
    hS₀V hS₀f hord
  set S₀ : Set S := (A ∩ B).vertexSet with hS₀
  let O : Set S := ⋃ s ∈ S₀, D s
  have hOo : IsOpen O := isOpen_biUnion hDo
  have hex : ∀ e ∈ Γ.E, ∃ E, IsClosedDisc E ∧ E ⊆ closure e ∧ Disjoint E (S₀ ∩ closure e)
    ∧ closure e \ O ⊆ E :=
    fun e he => exists_disc_cut (Cell.isClosedDisc_closure he) (hS₀f.inter_of_left _)
      (fun x hx => Cell.closure_inter_V_subset hS he ⟨hx.2, hS₀V hx.1⟩) hOo
      (fun x hx => mem_iUnion₂.mpr ⟨x, hx.1, hsD x hx.1⟩)
  choose! E hEd hEs hEdis hEcov using hex
  have hfe : Γ.E.Finite := Γ.finite_edges
  have hEc : ∀ e ∈ Γ.E, IsClosed (E e) := fun e he => (IsClosedDisc.isCompact (hEd e he)).isClosed
  have hbne : ∀ e ∈ Γ.E, (discBd (E e)).Nonempty := fun e he => (infinite_of_isOArc
    (hEd e he).isOArc_discBd).nonempty
  choose! b hb using hbne
  let V₀ : Set S := (Γ.V \ S₀) ∪ b '' Γ.E
  let Q : Set S := V₀ ∪ ⋃ e ∈ Γ.E, E e
  have hV₀f : V₀.Finite := (Γ.finite_V.subset sdiff_subset).union (hfe.image b)
  have hQc : IsClosed Q := hV₀f.isClosed.union (hfe.isClosed_biUnion hEc)
  have hVoff : ∀ e ∈ Γ.E, ∀ x ∈ E e, x ∉ S₀ := fun e he x hx hxS =>
    disjoint_left.mp (hEdis e he) hx ⟨hxS, hEs e he hx⟩
  have hQU : Q ⊆ Γ.U \ S₀ := by
    rintro x ((hx | ⟨e, he, rfl⟩) | hx)
    · exact ⟨Γ.V_subset_U hx.1, hx.2⟩
    · have h₁ := discBd_subset _ (hb e he)
      exact ⟨closure_subset_cell_U hpre he (hEs e he h₁), hVoff e he _ h₁⟩
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact ⟨closure_subset_cell_U hpre he (hEs e he hxe), hVoff e he _ hxe⟩
  have hUQ : Γ.U \ Q ⊆ O := by
    rintro x ⟨hxU, hxQ⟩
    rcases Cell.mem_V_or_cell Γ hxU with h | ⟨e, he, hxe⟩
    · have hxS : x ∈ S₀ := by
        by_contra hn
        exact hxQ (Or.inl (Or.inl ⟨h, hn⟩))
      exact mem_iUnion₂.mpr ⟨x, hxS, hsD x hxS⟩
    · by_contra hxO
      exact hxQ (Or.inr (mem_iUnion₂.mpr ⟨e, he, hEcov e he ⟨subset_closure hxe, hxO⟩⟩))
  -- `Q` is nice.
  obtain ⟨N, hNU, hNV⟩ := exists_drawing_on_oArcs hS hfe hV₀f (F := fun e => discBd (E e))
    (fun e he => (hEd e he).isOArc_discBd)
    (fun e he => ⟨b e, Or.inr (mem_image_of_mem b he), hb e he⟩) (fun e he f hf hef x hx => by
      have hxV := Cell.closure_inter_subset_V hS hU he hf hef
        ⟨hEs e he (discBd_subset _ hx.1), hEs f hf (discBd_subset _ hx.2)⟩
      exact Or.inl ⟨hxV, hVoff e he x (discBd_subset _ hx.1)⟩)
  have hQn : IsNice Q := by
    refine ⟨N, isGammaNice_of_frontier (Drawing.IsSubdrawing.refl N) ?_ ?_⟩
    · rw [hNU]
      refine union_subset subset_union_left (iUnion₂_subset fun e he => ?_)
      exact (discBd_subset _).trans ((subset_biUnion_of_mem (u := E) he).trans subset_union_right)
    · intro x hx
      have hxQ : x ∈ Q := hQc.frontier_subset hx
      rw [hNU]
      rcases hxQ with h | h
      · exact Or.inl h
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp h
        by_cases hxb : x ∈ discBd (E e)
        · exact Or.inr (mem_iUnion₂.mpr ⟨e, he, hxb⟩)
        · exfalso
          have hxi : x ∈ interior (E e) := by
            rw [interior_eq_sdiff_discBd hS (hEd e he)]
            exact ⟨hxe, hxb⟩
          exact hx.2 (interior_mono ((subset_biUnion_of_mem (u := E) he).trans subset_union_right)
            hxi)
  have hu : Q ≠ univ := fun h => by
    obtain ⟨y, hy⟩ := exists_notMem_painting_U hS hpre hE
    exact hy (hQU (h ▸ mem_univ y)).1
  have hcl : ∀ e ∈ (PaintingOrDrawing.painting Γ).E, closure e \ (PaintingOrDrawing.painting Γ).V ⊆
    e := fun e he =>
    (Cell.closure_sdiff_V hS hU he).subset
  have hAc := isClosed_underlying (Γ := PaintingOrDrawing.painting Γ) hcl hsep.left_le
  have hBc := isClosed_underlying (Γ := PaintingOrDrawing.painting Γ) hcl hsep.right_le
  have hcov := U_subset_underlying (Γ := PaintingOrDrawing.painting Γ) (fun x hx hxV =>
    (Cell.mem_V_or_cell Γ hx).resolve_left hxV) hsep
  have hint := underlying_inter (Γ := PaintingOrDrawing.painting Γ)
    (fun e he f hf x hxe hxf => arcComponent_eq he hf hxe hxf) (fun e he x hx => (he.2.1 hx).2) hsep
  obtain ⟨Δ, hΔ, -, hQΔ⟩ := theorem_7_5_proof hS hQc hQn hu finite_empty
    (disjoint_empty _) fun F hFQ hF => by
    rw [sdiff_empty]
    have hFA : F ⊆ PaintingOrDrawing.underlying A ∪ PaintingOrDrawing.underlying B := fun x hx =>
      hcov (hQU (hFQ hx)).1
    by_cases hFa : F ⊆ PaintingOrDrawing.underlying A
    · exact hA F hFa hF
    · refine hno F hF fun x hx => ?_
      have hFB : F ⊆ PaintingOrDrawing.underlying B := by
        obtain ⟨a, ha, haA⟩ := not_subset.mp hFa
        by_contra hFb
        obtain ⟨c, hc, hcB⟩ := not_subset.mp hFb
        obtain ⟨z, hzF, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hF.isPreconnected _ _ hAc hBc hFA
          ⟨c, hc, (hFA hc).resolve_right hcB⟩ ⟨a, ha, (hFA ha).resolve_left haA⟩
        exact (hQU (hFQ hzF)).2 (hint ⟨hz₁, hz₂⟩)
      refine ⟨hFB hx, fun hxA => ?_⟩
      exact (hQU (hFQ hx)).2 (hint ⟨hxA, hFB hx⟩)
  refine not_flat_compl_disc hS hns hΔ (fun x hx => ?_) hfl
  have hxQ : x ∉ Q := fun h => hx (hQΔ h)
  by_cases hxU : x ∈ Γ.U
  · exact Or.inr (hUQ ⟨hxU, hxQ⟩)
  · exact Or.inl (mem_iUnion₂.mpr ⟨_, ⟨x, ⟨trivial, hxU⟩, rfl⟩, mem_connectedComponentIn ⟨trivial,
      hxU⟩⟩)

section Any

variable {Γ : PaintingOrDrawing S}

omit [T2Space S] [ConnectedSpace S] in
/-- A point off `U(Γ)` lies in a region of `Γ`. -/
theorem exists_mem_region {x : S} (hx : x ∉ Γ.U) : ∃ r ∈ Γ.R, x ∈ r := by
  cases Γ with
  | painting Γ => exact ⟨_, ⟨x, ⟨trivial, hx⟩, rfl⟩, mem_connectedComponentIn ⟨trivial, hx⟩⟩
  | drawing Γ => exact exists_region_of_notMem hx

/-- `exists_flat_regions`, for a painting or drawing in a surface other than a sphere. -/
theorem exists_flat_of_not_sphere (hS : IsClosedSurface S) (hns : ¬ IsSphere S) (hE : Γ.E.Nonempty)
    (hrad : Γ.IsRadialDrawing Γ') (hθ : 1 ≤ θ)
    (hnull : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ
      → IsNullHomotopicOArc C.U)
    {S₀ : Set S} (hS₀V : S₀ ⊆ Γ.V) (hS₀f : S₀.Finite) (hord : S₀.ncard < θ) :
    ∃ D : S → Set S, (∀ s ∈ S₀, IsOpen (D s)) ∧ (∀ s ∈ S₀, s ∈ D s) ∧
      Flat ((⋃ r ∈ Γ.R, r) ∪ ⋃ s ∈ S₀, D s) := by
  cases Γ with
  | painting Γ =>
    exact exists_flat_painting hS hrad hE (fun e he => cell_has_vertex hS hns ⟨hrad.1,
      hrad.2.1⟩ he) hθ hnull hS₀V hS₀f
      hord
  | drawing Γ => exact exists_flat_regions hS hE hrad hθ hnull hS₀V hS₀f hord

/-- **Claim (2) of (6.4)** (pages 90–91), for a painting or drawing. -/
theorem exists_oArc_of_null_any (hS : IsClosedSurface S) (hns : ¬ IsSphere S) (hE : Γ.E.Nonempty)
    (hrad : Γ.IsRadialDrawing Γ') (hθ : 1 ≤ θ) (hd : IsDerivedSlope Γ Γ' θ T ins) {A B : Hypergraph
      S (Set S)}
    (hsep : Γ.toHypergraph.IsSeparation A B) (hord : separationOrder A B < θ)
    (hA : ∀ F : Set S, F ⊆ PaintingOrDrawing.underlying A → IsOArc F → IsNullHomotopicOArc F) :
    ∃ F : Set S, IsOArc F ∧ F ⊆ PaintingOrDrawing.underlying B \ PaintingOrDrawing.underlying A ∧
      ¬ IsNullHomotopicOArc F := by
  cases Γ with
  | painting Γ => exact exists_oArc_of_null_painting hS hns hE hrad hθ hd hsep hord hA
  | drawing Γ => exact exists_oArc_of_null hS hns hE hrad hθ hd hsep hord hA

end Any

end GraphMinor.GM11
