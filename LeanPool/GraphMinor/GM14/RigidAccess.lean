/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.RigidClaims
public import LeanPool.GraphMinor.GM14.RigidFinger
public import LeanPool.GraphMinor.GM14.RigidSphere
import LeanPool.GraphMinor.GM11.ForestRegions
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM12.Section4ParallelLine
import LeanPool.GraphMinor.GM14.WhitneyFaces
import LeanPool.GraphMinor.GM14.RigidThread
import LeanPool.GraphMinor.Surface.ArcInPath
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# A disc around a part of a rigid drawing

Let `H` be a rigid drawing in a closed disc `D₁` of a sphere, and let `Γ` be a subdrawing of `H`.
Let `X` be a
set of at most three vertices of `Γ`, such that all the other vertices of `Γ` are off `bd(D₁)` and
have all
their edges in `Γ`. We find a closed disc that holds `Γ`, with `X` as the points of `Γ` on its
boundary
(`exists_disc_of_part`). This is how we use Claim (2) of Graph Minors XIV, (6.5), that `Γ` with a
new vertex
joined to `X` is planar.

By `exists_disc_around`, we need a line from a fixed point `a` to each `x ∈ X`, meeting `U(Γ)` only
in `x`.
Take `a` to be the hub of a wheel outside `D₁`. The wheel with `H` has the graph of the paper's
proof of
Claim (2), `H` with a new vertex joined to `V(H) ∩ bd(D₁)`, up to the rim.

If `Γ` has a circuit, then Claim (1) gives three disjoint paths to `bd(D₁)`. By `tail_off`, each `x`
starts a
path off `Γ`, and this path with a spoke of the wheel is the line. If `Γ` has no circuit, then the
paper says
that the planarity is clear, and here is the reason. The complement of `U(Γ)` is connected, and each
`x`
is an end of a line whose other points are off `U(Γ)`: an edge of `H` or of the wheel at `x` off
`Γ`, or a
parallel copy of an edge of `Γ` at `x`.
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology Graph GraphMinor.GM09 GraphMinor.Surface GraphMinor.GM11

universe u

variable {T : Type u} [TopologicalSpace T]

/-- A closed surface is locally path connected. -/
theorem locPath (hS : IsClosedSurface T) : LocallyPathConnectedSpace T := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x u hu hx
  obtain ⟨V, hV, hxV, ⟨h⟩⟩ := hS.2.2 x
  have hball : IsOpen (OpenUnitDisc : Set EuclideanPlane) := Metric.isOpen_ball
  have : LocallyPathConnectedSpace OpenUnitDisc := hball.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace V := h.isOpenEmbedding.locallyPathConnectedSpace
  let x' : V := ⟨x, hxV⟩
  have hu' : IsOpen (Subtype.val ⁻¹' u : Set V) := hu.preimage continuous_subtype_val
  have hm := (locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mp ‹_›) x' _ hu' hx
  have hm₂ : Subtype.val '' pathComponentIn (Subtype.val ⁻¹' u : Set V) x' ∈ 𝓝 x := by
    have := hV.isOpenEmbedding_subtypeVal.map_nhds_eq x'
    rw [← this]
    exact Filter.image_mem_map hm
  refine Filter.mem_of_superset hm₂ ?_
  rintro _ ⟨y, hy, rfl⟩
  have hj : JoinedIn (Subtype.val ⁻¹' u : Set V) x' y := hy
  have h₂ := hj.map continuous_subtype_val.continuousOn
  exact h₂.mono (image_preimage_subset _ _)

/-- A line to `x` from a point of a path connected set `C` that holds the rest of a line at `x`. -/
theorem exists_line_to [T2Space T] {C L : Set T} {a x y : T} (hC : IsPathConnected C) (ha : a ∈ C)
    (hL : IsLineWithEnds L x y) (hsub : L \ {x, y} ⊆ C) (hax : a ≠ x) :
    ∃ ℓ, IsLineWithEnds ℓ a x ∧ ℓ ⊆ insert x C := by
  obtain ⟨f, h0, h1⟩ := id hL
  let m : unitInterval → unitInterval := fun t => ⟨(1 - t.1) / 2, by
    have := t.2.1
    have := t.2.2
    constructor <;> linarith⟩
  have hm : Continuous m := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  let q : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hq : m 0 = q := Subtype.ext (by simp [m, q])
  have h₀ : m 1 = 0 := Subtype.ext (by simp [m])
  have hinn : ∀ t : unitInterval, t ≠ 1 → ((f (m t)).1 : T) ∈ L \ {x, y} := by
    intro t ht
    refine ⟨(f (m t)).2, ?_⟩
    have hne0 : m t ≠ 0 := fun h => ht (by
      have h₁ : (1 - t.1) / 2 = 0 := congrArg Subtype.val h
      exact Subtype.ext (by simp only [Set.Icc.coe_one]; linarith))
    have hne1 : m t ≠ 1 := fun h => by
      have h₁ : (1 - t.1) / 2 = 1 := congrArg Subtype.val h
      have := t.2.1
      linarith
    rintro (h | h)
    · exact hne0 (f.injective (Subtype.ext (h.trans h0.symm)))
    · exact hne1 (f.injective (Subtype.ext (h.trans h1.symm)))
  let γ : Path ((f q).1 : T) x :=
    { toFun := fun t => (f (m t)).1
      continuous_toFun := continuous_subtype_val.comp (f.continuous.comp hm)
      source' := by simp [hq]
      target' := by simp only [h₀]; exact h0 }
  have hqC : ((f q).1 : T) ∈ C := by
    have := hinn 0 zero_ne_one
    rw [hq] at this
    exact hsub this
  obtain ⟨p, hp⟩ := hC.joinedIn a ha _ hqC
  let P := p.trans γ
  obtain ⟨e, he, hi, he0, he1, her⟩ := exists_arc_of_path (γ := P) P.continuous
    (by simpa [P] using hax)
  have hline : IsLineWithEnds (range e) (e 0) (e 1) := IsArcMap.isLineWithEnds ⟨he, hi⟩
  rw [he0, he1] at hline
  refine ⟨range e, by simpa [P] using hline, her.trans ?_⟩
  rw [show range ⇑P = range ⇑p ∪ range ⇑γ from Path.trans_range p γ]
  refine union_subset (range_subset_iff.mpr fun t => Or.inr (hp t)) ?_
  rintro _ ⟨t, rfl⟩
  by_cases ht : t = 1
  · subst ht
    exact Or.inl γ.target
  · exact Or.inr (hsub (hinn t ht))

/-- Each vertex of a subdivision of a 3-connected graph has an edge. -/
theorem SubData.exists_edge {α β : Type*} {G G₀ : Graph α β} {P : β → Graph α β}
  (h : SubData G G₀ P)
    {v : α} (hv : v ∈ V(G)) : ∃ g ∈ E(G), G.Inc g v := by
  have hE : ∀ {e g}, e ∈ E(G₀) → g ∈ E(P e) → g ∈ E(G) := fun {e g} he hg => by
    rw [h.eunion]
    exact mem_iUnion₂.mpr ⟨e, he, hg⟩
  rw [h.vunion] at hv
  rcases hv with hv | hv
  · obtain ⟨e, -, -, ⟨w, hw⟩, -⟩ := IsSimpleThreeConnected.exists_two_edges h.simple hv
    obtain ⟨g, hg, hi⟩ := (h.exists_edge_at_ends hw).1
    exact ⟨g, hE hw.edge_mem hg, hi⟩
  · obtain ⟨e, he, hv⟩ := mem_iUnion₂.mp hv
    obtain ⟨u, w, hl, ⟨hle, W, hs, hVe, hEe⟩, -, -⟩ := h.path e he
    by_cases hvu : v = u
    · obtain ⟨g, hg, hi⟩ := (h.exists_edge_at_ends hl).1
      exact ⟨g, hE he hg, hvu ▸ hi⟩
    by_cases hvw : v = w
    · obtain ⟨g, hg, hi⟩ := (h.exists_edge_at_ends hl).2
      exact ⟨g, hE he hg, hvw ▸ hi⟩
    rw [hVe] at hv
    obtain ⟨g, hg, -, -, -, ⟨y, hy⟩, -⟩ := exists_two_edges_at_inner W hs hv hvu hvw
    have hgE : g ∈ E(P e) := by rw [hEe]; exact hg
    exact ⟨g, hE he hgE, y, hy.mono hle⟩

private theorem exists_access_line_to_vertex_of_forest
    {T : Type u}
    [TopologicalSpace T]
    [T2Space T]
    [ConnectedSpace T]
    (hS : IsClosedSurface T)
    {Γ : Drawing T}
    {X : Set T}
    (a : T)
    (G₀ : Graph T (Set T))
    (Q₀ : Set T → Graph T (Set T))
    (J : Drawing T)
    (hgood : Good J.toGraph)
    (hsd : SubData J.toGraph G₀ Q₀)
    (hΓJ : Γ.IsSubdrawing J)
    (haK : a ∉ Γ.U)
    (hoff : ∀ g ∈ J.E, g ∉ Γ.E → ∀ z ∈ g, z ∉ Γ.U)
    (hclo : ∀ {g : Set T} {v : T}, J.toGraph.Inc g v → v ∈ closure g)
    (hXJ : ∀ {x : T}, x ∈ X → x ∈ J.V)
    (hax : ∀ {x : T}, x ∈ X → a ≠ x) :
    (¬∃ R : Drawing T, R.IsCircuit ∧ R.IsSubdrawing Γ) →
      ∀ x ∈ X, ∃ ℓ, IsLineWithEnds ℓ a x ∧ ℓ ∩ Γ.U ⊆ {x} := by
  intro hno x₀ hx₀
  have hpre : IsPreconnected Γ.Uᶜ :=
    isPreconnected_compl_of_noCircuit hS Γ fun R h₁ h₂ => hno ⟨R, h₁, h₂⟩
  have hO : IsOpen Γ.Uᶜ := Γ.isClosed_U.isOpen_compl
  have := locPath hS
  have hCp : IsPathConnected Γ.Uᶜ := by
    refine hO.isConnected_iff_isPathConnected.mp ⟨⟨a, haK⟩, hpre⟩
  have hfin : ∀ L y, IsLineWithEnds L x₀ y → L \ {x₀, y} ⊆ Γ.Uᶜ →
      ∃ ℓ, IsLineWithEnds ℓ a x₀ ∧ ℓ ∩ Γ.U ⊆ {x₀} := by
    intro L y hL hsub
    obtain ⟨ℓ, hℓ, hsubℓ⟩ := exists_line_to hCp haK hL hsub (hax hx₀)
    refine ⟨ℓ, hℓ, ?_⟩
    rintro z ⟨hz, hzU⟩
    exact (hsubℓ hz).resolve_right fun h => h hzU
  obtain ⟨g₀, hg₀, hi₀⟩ := hsd.exists_edge (v := x₀) (hXJ hx₀)
  have hg₀' : g₀ ∈ J.E := hg₀
  obtain ⟨w, hxw, hc, hL⟩ : ∃ w, x₀ ≠ w ∧ closure g₀ ∩ J.V = {x₀, w} ∧
      IsLineWithEnds (closure g₀) x₀ w := by
    rcases J.edge_cond g₀ hg₀' with ⟨u, v, huv, hc, hL⟩ | ⟨u, hc, -⟩
    · have h₁ : x₀ ∈ ({u, v} : Set T) := hc ▸ ⟨hclo hi₀, hXJ hx₀⟩
      rcases h₁ with rfl | h₁
      · exact ⟨v, huv, hc, hL⟩
      · have h₂ : x₀ = v := h₁
        subst h₂
        exact ⟨u, huv.symm, hc.trans (pair_comm _ _), IsLineWithEnds.symm hL⟩
    · have huV : u ∈ J.V := by
        have h₁ : u ∈ closure g₀ ∩ J.V := hc ▸ rfl
        exact h₁.2
      exact absurd ⟨hg₀', huV, huV, hc.trans (pair_eq_singleton u).symm⟩ (hgood.no_loop g₀ u)
  by_cases hg₀Γ : g₀ ∈ Γ.E
  · let Z : Set T := (Γ.span Γ.V (Γ.E \ {g₀})).U
    have hZc : IsClosed Z := (Γ.span Γ.V (Γ.E \ {g₀})).isClosed_U
    have hKZ : Γ.U ⊆ Z ∪ closure g₀ := by
      intro z hz
      rw [Γ.U_eq] at hz
      rcases hz with hz | hz
      · exact Or.inl (Or.inl (Or.inl ⟨hz, hz⟩))
      · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hz
        by_cases heg : e = g₀
        · exact Or.inr (heg ▸ hze)
        · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e, ⟨⟨he, heg⟩, he⟩, hze⟩))
    have hLZ : closure g₀ ∩ Z ⊆ {x₀, w} := by
      rintro z ⟨hz, hzZ⟩
      by_contra hzn
      have hzV : z ∉ J.V := fun h => hzn (hc ▸ ⟨hz, h⟩)
      have hzg : z ∈ g₀ := by
        rw [← J.closure_diff_V hg₀']
        exact ⟨hz, hzV⟩
      rcases hzZ with hzs | hzc
      · exact hzV (hΓJ.1 (Γ.spanV_subset _ _ hzs))
      · obtain ⟨e, ⟨⟨he, hne⟩, -⟩, hze⟩ := mem_iUnion₂.mp hzc
        have hzeJ : z ∈ e := by
          rw [← J.closure_diff_V (hΓJ.2 he)]
          exact ⟨hze, hzV⟩
        exact hne (J.edge_eq_of_mem (hΓJ.2 he) hg₀' hzeJ hzg)
    obtain ⟨P', hP', hP'Z, hP'L⟩ := GM12.exists_parallel_line hS hL hxw hZc hLZ
    refine hfin P' w hP' ?_
    rintro z ⟨hz, hzn⟩ hzU
    rcases hKZ hzU with h₁ | h₁
    · exact hzn (hP'Z ⟨hz, h₁⟩)
    · exact hzn (hP'L ▸ ⟨hz, h₁⟩)
  · refine hfin _ w hL ?_
    rintro z ⟨hz, hzn⟩
    refine hoff g₀ hg₀' hg₀Γ z ?_
    rw [← J.closure_diff_V hg₀']
    exact ⟨hz, fun hzV => hzn (hc ▸ ⟨hz, hzV⟩)⟩

/-- **A disc around a part.** See the module docstring. -/
theorem exists_disc_of_part [T2Space T] [ConnectedSpace T] (hS : IsClosedSurface T)
  (hsph : IsSphere T)
    {D₁ D₂ B : Set T} (hd₁ : IsClosedDisc D₁) (hd₂ : IsClosedDisc D₂) (hb₁ : discBd D₁ = B)
    (hb₂ : discBd D₂ = B) (hcov : D₁ ∪ D₂ = univ) (hcap : D₁ ∩ D₂ = B) {H Γ : Drawing T}
    (hU : H.U ⊆ D₁) (hn : H.U ∩ B ⊆ H.V) (hr : IsRigidIn H D₁) (hΓ : Γ.IsSubdrawing H) {X : Set T}
    (hXV : X ⊆ Γ.V) (hX : X.ncard ≤ 3)
    (hout : ∀ v ∈ Γ.V, v ∉ X → v ∉ B ∧ ∀ e ∈ H.E, v ∈ closure e → e ∈ Γ.E) :
    ∃ E : Set T, IsClosedDisc E ∧ Γ.U ⊆ E ∧ discBd E ∩ Γ.U = X := by
  classical
  have hcomp : CompactSpace T := hS.1
  obtain ⟨W, a, Γ', hm, hw, hf, hrr, -, -, haD₁, -, hhub⟩ :=
    exists_frame hS hsph hd₁ hd₂ hb₁ hb₂ hcov hcap hU hn hr
  have hu : IsUnion H W (H.glue W hm) := isUnion_glue hm
  have hsb : subBd D₁ = B := (IsClosedDisc.subBd_eq_discBd hS hd₁).trans hb₁
  have hgood := good_of_wheel hf hrr hw hu
    (fun v hv hvW => ⟨hv, by
      have : v ∈ D₁ ∩ D₂ := ⟨hU (H.V_subset_U hv), hw.Usub (W.V_subset_U hvW)⟩
      rwa [hcap] at this⟩) hm hS hsph
  obtain ⟨G₀, Q₀, hsd⟩ := exists_subData (good_sub hgood)
  generalize hJ : H.glue W hm = J at hu hf hrr hgood hsd
  have hHJ : H.IsSubdrawing J := ⟨hf.Vsub, hf.Esub⟩
  have hWJ : W.IsSubdrawing J := ⟨hu.hV ▸ subset_union_right, hu.hE ▸ subset_union_right⟩
  have hΓJ : Γ.IsSubdrawing J := hΓ.trans hHJ
  have hKH : Γ.U ⊆ H.U := hΓ.U_subset
  have haK : a ∉ Γ.U := fun h => haD₁ (hU (hKH h))
  -- Edges of `J` off `Γ` miss `U(Γ)`.
  have hoff : ∀ g ∈ J.E, g ∉ Γ.E → ∀ z ∈ g, z ∉ Γ.U := by
    intro g hg hgΓ z hz hzU
    by_cases hzV : z ∈ Γ.V
    · exact edge_notMem_V hg hz (hΓJ.1 hzV)
    · obtain ⟨e, he, hze⟩ := Γ.exists_edge_of_mem hzU hzV
      exact hgΓ (J.edge_eq_of_mem hg (hΓJ.2 he) hz hze ▸ he)
  have hclo : ∀ {g v}, J.toGraph.Inc g v → v ∈ closure g := by
    rintro g v ⟨y, hl⟩
    have h₁ : v ∈ closure g ∩ J.V := hl.2.2.2 ▸ mem_insert _ _
    exact h₁.1
  have hXJ : ∀ {x}, x ∈ X → x ∈ J.V := fun hx => hΓJ.1 (hXV hx)
  have hXf : X.Finite := Γ.finite_V.subset hXV
  have hax : ∀ {x}, x ∈ X → a ≠ x := fun hx h => haK (h ▸ Γ.V_subset_U (hXV hx))
  have hUV : ∀ {z}, z ∈ Γ.U → z ∈ J.V → z ∈ Γ.V := fun {z} hz hzJ => by
    by_contra hn
    obtain ⟨e, he, hze⟩ := Γ.exists_edge_of_mem hz hn
    exact edge_notMem_V (hΓJ.2 he) hze hzJ
  -- The case of a circuit: Claims (1) and (2).
  have hcirc : (∃ R : Drawing T, R.IsCircuit ∧ R.IsSubdrawing Γ) →
      ∀ x ∈ X, ∃ ℓ, IsLineWithEnds ℓ a x ∧ ℓ ∩ Γ.U ⊆ {x} := by
    rintro ⟨R, hR, hRs⟩ x₀ hx₀
    have hB' : ∀ v ∈ H.V, ∀ g ∈ J.E, g ∉ H.E → v ∈ closure g → v ∈ subBd D₁ := by
      intro v hv g hg hgH hvg
      have hgW : g ∈ W.E := (show g ∈ H.E ∪ W.E from hu.hE ▸ hg).resolve_left hgH
      have h₂ : v ∈ closure g ∩ J.V := ⟨hvg, hf.Vsub hv⟩
      rw [← hWJ.closure_inter_V hgW] at h₂
      rw [hsb]
      exact hcap ▸ ⟨hU (H.V_subset_U hv), hw.Usub (W.V_subset_U h₂.2)⟩
    obtain ⟨Q, hdis, hQ⟩ := claim_1_three_paths hf hrr hS hsph hsd hB' hR (hRs.trans hΓ)
    have hyB : ∀ {y}, y ∈ H.V ∩ subBd D₁ → y ∈ B := fun hy => hsb ▸ hy.2
    have hhit : ∀ i, ∃ x ∈ V(Q i), x ∈ X := by
      intro i
      obtain ⟨u, y, ⟨hle, W', -, hV, -⟩, hu', hy⟩ := hQ i
      have huR : u ∈ V(Q i) ∩ R.V := hu' ▸ rfl
      have hyB' : y ∈ V(Q i) ∩ (H.V ∩ subBd D₁) := hy ▸ rfl
      obtain ⟨x, hx, hxX⟩ := walk_hits hΓ hout hle W' (hRs.1 huR.2) (hyB hyB'.2)
      exact ⟨x, hV ▸ hx, hxX⟩
    choose c hc hcX using hhit
    have hinj : Function.Injective c := by
      intro i j hij
      by_contra hne
      exact disjoint_left.mp (hdis hne) (hc i) (hij ▸ hc j)
    have hrange : range c = X := by
      refine eq_of_subset_of_ncard_le (range_subset_iff.mpr hcX) ?_ hXf
      rw [← image_univ, ncard_image_of_injective _ hinj, ncard_univ]
      simpa using hX
    obtain ⟨i, rfl⟩ : x₀ ∈ range c := hrange ▸ hx₀
    have huniq : ∀ z ∈ V(Q i), z ∈ X → z = c i := by
      intro z hz hzX
      rw [← hrange] at hzX
      obtain ⟨j, rfl⟩ := hzX
      by_cases hij : i = j
      · rw [hij]
      · exact absurd (hc j) (disjoint_left.mp (hdis hij) hz)
    obtain ⟨u, y, ⟨hle, W', hs, hV, -⟩, -, hy⟩ := hQ i
    have hyH : y ∈ H.V ∩ subBd D₁ := (show y ∈ V(Q i) ∩ (H.V ∩ subBd D₁) from hy ▸ rfl).2
    have hci : c i ∈ W'.support := by
      have := hc i
      rw [hV] at this
      exact this
    obtain ⟨T, hTs, hT₁, -⟩ := walk_tail W' hci hs
    have hmem : ∀ {z}, z ∈ T.support → z ∈ V(Q i) := fun {z} hz => by
      rw [hV]
      exact hT₁ z hz
    have hTH : ∀ {z}, z ∈ T.support → z ∈ H.V := fun hz => hle.vertexSet_mono (hmem hz)
    have htail := fun {z} (hz : z ∈ T.support) (hne : z ≠ c i) =>
      tail_off hΓ hout hle T hTs (hyB hyH) (fun w hw hwX => huniq w (hmem hw) hwX) hz hne
    have hay : y ≠ a := fun h => haD₁ (h ▸ hU (H.V_subset_U hyH.1))
    obtain ⟨g, hg⟩ := hhub y (hw.BV ⟨hyH.1, hyB hyH⟩) hay
    have hgJ : J.toGraph.IsLink g a y := (hWJ.isLink_iff hg.1).mp hg
    obtain ⟨T', hs', he'⟩ := T.exists_transfer (G' := J.toGraph)
      (fun e p q _ hl => (hHJ.isLink_iff (hl.mono hle).1).mp (hl.mono hle))
      (fun z hz => hf.Vsub (hTH hz))
    have hT's : T'.IsSimple := by
      unfold GraphWalk.IsSimple
      rw [hs']
      exact hTs
    have hsupp : ∀ {z}, z ∈ (GraphWalk.cons hgJ T'.reverse).support → z = a ∨ z ∈ T.support := by
      intro z hz
      simp only [GraphWalk.support, List.mem_cons, GraphWalk.support_reverse,
        List.mem_reverse] at hz
      rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (hs' ▸ hz)
    have hAs : (GraphWalk.cons hgJ T'.reverse).IsSimple := by
      refine List.nodup_cons.mpr ⟨fun h => ?_, hT's.reverse⟩
      rw [GraphWalk.support_reverse, List.mem_reverse, hs'] at h
      exact haD₁ (hU (H.V_subset_U (hTH h)))
    have hVoff : ∀ z ∈ (GraphWalk.cons hgJ T'.reverse).support, z ≠ c i → z ∉ Γ.U := by
      intro z hz hne hzU
      rcases hsupp hz with rfl | hz'
      · exact haK hzU
      · exact htail hz' hne (hUV hzU (hf.Vsub (hTH hz')))
    have hEoff : ∀ e ∈ (GraphWalk.cons hgJ T'.reverse).edges, e ∉ Γ.E := by
      intro e he heΓ
      obtain ⟨p, q, hl, hp, hq⟩ := walk_edge_ends _ he
      have hend : ∀ {w}, w ∈ closure e ∩ J.V → w ∈ (GraphWalk.cons hgJ T'.reverse).support → w
        = c i := by
        intro w hw hws
        by_contra hne
        rw [← hΓJ.closure_inter_V heΓ] at hw
        exact hVoff w hws hne (Γ.V_subset_U hw.2)
      have hpc : p ∈ closure e ∩ J.V := hl.2.2.2 ▸ mem_insert _ _
      have hqc : q ∈ closure e ∩ J.V := hl.2.2.2 ▸ mem_insert_of_mem _ rfl
      have hpq : p = q := (hend hpc hp).trans (hend hqc hq).symm
      subst hpq
      exact hgood.no_loop e p hl
    refine ⟨_, walk_isLine J _ hAs (hax (hcX i)), ?_⟩
    rintro z ⟨hz | hz, hzU⟩
    · by_contra hne
      exact hVoff z hz hne hzU
    · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hz
      obtain ⟨p, q, hl, hp, hq⟩ := walk_edge_ends _ he
      by_cases hzV : z ∈ J.V
      · by_contra hne
        have h₁ : z ∈ closure e ∩ J.V := ⟨hze, hzV⟩
        rw [hl.2.2.2] at h₁
        rcases h₁ with rfl | h₁
        · exact hVoff z hp hne hzU
        · have h₂ : z = q := h₁
          exact hVoff z (h₂ ▸ hq) hne hzU
      · have hze' : z ∈ e := by
          rw [← J.closure_diff_V hl.1]
          exact ⟨hze, hzV⟩
        exact absurd hzU (hoff e hl.1 (hEoff e he) z hze')
  -- The case of no circuit.
  have hforest : (¬ ∃ R : Drawing T, R.IsCircuit ∧ R.IsSubdrawing Γ) →
      ∀ x ∈ X, ∃ ℓ, IsLineWithEnds ℓ a x ∧ ℓ ∩ Γ.U ⊆ {x} := by
    exact exists_access_line_to_vertex_of_forest (T := T) hS (Γ := Γ) (X := X) a G₀ Q₀ J hgood hsd
      hΓJ haK hoff hclo hXJ hax
  have hlines : ∀ x ∈ X, ∃ ℓ, IsLineWithEnds ℓ a x ∧ ℓ ∩ Γ.U ⊆ {x} := by
    by_cases hc : ∃ R : Drawing T, R.IsCircuit ∧ R.IsSubdrawing Γ
    · exact hcirc hc
    · exact hforest hc
  obtain ⟨E, hE, hKE, -, hb⟩ := exists_disc_around hS hsph Γ.isClosed_U.isCompact haK hXf
    (hXV.trans Γ.V_subset_U) hlines
  exact ⟨E, hE, hKE, hb⟩

end GraphMinor.GM14.Whitney
