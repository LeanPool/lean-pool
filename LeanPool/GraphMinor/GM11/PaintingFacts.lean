/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PaintingRadial
public import LeanPool.GraphMinor.GM11.RadialFacts

/-!
# Each region of a radial drawing of a painting contains a unique cell

`regionFacts_of_painting` is the statement of Graph Minors XI (Section 3, page 75) for a 2-cell
painting
with a cell.

If a cell has no vertex, this is `regionFacts_of_free_cell`. Otherwise let `D` be the drawing of the
boundaries of the cells, and `G` a radial drawing of `D` made from `Γ'` by adding stars in the
cells. By
`regionFacts_of_radial`, each region of `G` contains a unique edge of `D`. Each region of `Γ'` is
then
the union of one cell `e` with the regions of `G` that contain an edge of `D` in `e`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- An `O`-arc is infinite. -/
theorem infinite_of_isOArc {F : Set S} (hF : IsOArc F) : F.Infinite := by
  obtain ⟨f⟩ := id hF
  obtain ⟨p, -, -, -, hper, himg, -⟩ := exists_oArc_par hF (f 1).2
  have hpos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hinj : InjOn p (Ico 0 (2 * Real.pi)) := by
    intro s hs t ht h
    obtain ⟨m, hm⟩ := hper s t h
    have h₁ : (m : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith [hs.2, ht.1]
    have h₂ : -(2 * Real.pi) < (m : ℝ) * (2 * Real.pi) := by linarith [hs.1, ht.2]
    have h₃ : (m : ℝ) < 1 := by nlinarith
    have h₄ : (-1 : ℝ) < m := by nlinarith
    have h₅ : m < 1 := by exact_mod_cast h₃
    have h₆ : -1 < m := by exact_mod_cast h₄
    have h₇ : m = 0 := by omega
    rw [hm, h₇]
    simp
  rw [← himg]
  exact (Ico_infinite hpos).image hinj

variable [T2Space S] [ConnectedSpace S] {Γ : Painting S} {Γ' : Drawing S}

/-- **Every region of a radial drawing of a 2-cell painting contains a unique cell.** Graph Minors
XI,
Section 3 (page 75). -/
theorem regionFacts_of_painting (hrad : PreRad (PaintingOrDrawing.painting Γ) Γ')
    (hmax : RadMax (PaintingOrDrawing.painting Γ) Γ') (hS : IsClosedSurface S) (hE :
      (PaintingOrDrawing.painting Γ).E.Nonempty) :
    RegionFacts (PaintingOrDrawing.painting Γ) Γ' := by
  classical
  by_cases hfree : ∃ e ∈ Γ.E, closure e ∩ Γ.V = ∅
  · obtain ⟨e, he, hf⟩ := hfree
    exact regionFacts_of_free_cell hS hrad he hf
  have hv : ∀ e ∈ Γ.E, (closure e ∩ Γ.V).Nonempty := fun e he => by
    by_contra h
    exact hfree ⟨e, he, not_nonempty_iff_eq_empty.mp h⟩
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨e₀, he₀⟩ := hE
  obtain ⟨y₀, -⟩ := he₀.1
  have hneS : Nonempty S := ⟨y₀⟩
  have hU : IsClosed Γ.U := cell_isClosed_U hrad
  obtain ⟨c, K, hst⟩ := exists_cellStars (Γ := Γ)
  obtain ⟨G, hG⟩ := exists_star_drawing hrad hst hS
  have hbd : ∀ e ∈ Γ.E, Γ.V ∩ closure e ⊆ discBd (closure e) := fun e he x hx =>
    Cell.closure_inter_V_subset hS he ⟨hx.2, hx.1⟩
  obtain ⟨D, hDU, hDV⟩ := exists_boundary_drawing hS hU Γ.finite_V Subset.rfl fun e he => by
    obtain ⟨x, hx, hxV⟩ := hv e he
    exact ⟨x, hxV, hbd e he ⟨hxV, hx⟩⟩
  have hDR : D.R = Γ.R ∪ cellInt '' Γ.E :=
    boundary_R hS hrad.1.2 Subset.rfl Γ.V_subset_U hbd hDU
  have hGrad := radial_of_stars hrad hst hS hG hDU hDV hv hmax hDR
  -- Each point of `D` that is not a vertex lies in an edge of `D`.
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
  obtain ⟨hf₁, hf₂, hf₃⟩ := regionFacts_of_radial ⟨hGrad.1, hGrad.2.1⟩ hS hGrad.2.2 hDE
  have hf₁' : ∀ s ∈ G.R, ∃ a ∈ D.E, a ⊆ s := hf₁
  have hf₂' : ∀ s ∈ G.R, ∀ a ∈ D.E, ∀ b ∈ D.E, a ⊆ s → b ⊆ s → a = b := hf₂
  have hf₃' : ∀ s ∈ G.R, ∀ a ∈ D.E, a ⊆ s → ∀ v ∈ D.V, v ∈ closure s → v ∈ closure a := hf₃
  have hDUsub : D.U ⊆ Γ.U := D_U_subset hrad hDU
  have hUU' : Γ.U ∩ Γ'.U = Γ.V := hrad.2.1
  have hcellV : ∀ e ∈ Γ.E, Disjoint e Γ.V := fun e he =>
    disjoint_left.mpr fun x hx h => (he.2.1 hx).2 h
  -- Each edge of `D` lies in a cell.
  have hcell : ∀ a ∈ D.E, ∃ e ∈ Γ.E, a ⊆ e := by
    intro a ha
    have hsub : a ⊆ Γ.U \ Γ.V := fun x hx => by
      have h := ha.2.1 hx
      exact ⟨hDUsub h.1, fun hV => h.2 (hDV.symm.subset hV)⟩
    obtain ⟨x, hx⟩ := ha.1
    obtain ⟨e, he, hxe⟩ := exists_mem_arcComponent (hsub hx)
    refine ⟨e, he, ?_⟩
    have hu : IsPathConnected (e ∪ a) := he.2.2.1.union ha.2.2.1 ⟨x, hxe, hx⟩
    have := he.2.2.2 _ (union_subset he.2.1 hsub) hu subset_union_left
    exact this ▸ subset_union_right
  have hG_U : Γ'.U ⊆ G.U := fun x hx => hG.U ▸ Or.inl hx
  have hVG : Γ.V ⊆ G.U := fun x hx => hG_U (Γ'.V_subset_U (hrad.2.2.1 hx))
  have hadis : ∀ a ∈ D.E, Disjoint a G.U := fun a ha =>
    edge_disjoint ⟨hGrad.1, hGrad.2.1⟩ ha
  have hcellU' : ∀ e ∈ Γ.E, Disjoint e Γ'.U := fun e he =>
    disjoint_left.mpr fun x hx h => disjoint_left.mp (hcellV e he) hx
      (hUU'.subset ⟨(he.2.1 hx).1, h⟩)
  -- A region of `G` with an edge in the cell `e` misses the other cells.
  have hcross : ∀ p ∈ G.R, ∀ a ∈ D.E, a ⊆ p → ∀ e ∈ Γ.E, a ⊆ e → ∀ f ∈ Γ.E, f ≠ e →
      Disjoint f p := by
    intro p hp a ha hap e he hae f hf hfe
    refine disjoint_left.mpr fun x hxf hxp => ?_
    obtain ⟨z, hz⟩ := ha.1
    have hd := Cell.isClosedDisc_closure hf
    have hsep : Disjoint a (closure f) := by
      refine disjoint_left.mpr fun y hya hyf => ?_
      have hyV : y ∉ Γ.V := disjoint_left.mp (hcellV e he) (hae hya)
      have hyf' : y ∈ f := Cell.closure_sdiff_V hS hU hf ▸ (⟨hyf, hyV⟩ : y ∈ closure f \ Γ.V)
      exact hfe (arcComponent_eq hf he hyf' (hae hya))
    -- `p` meets the boundary of `f`.
    have hmeet : ∃ y ∈ p, y ∈ discBd (closure f) := by
      by_contra hno
      push Not at hno
      have hxint : x ∈ cellInt f := ⟨subset_closure hxf, hno x hxp⟩
      have hsub : p ⊆ cellInt f ∪ (closure f)ᶜ := fun y hy => by
        by_cases hyf : y ∈ closure f
        · exact Or.inl ⟨hyf, hno y hy⟩
        · exact Or.inr hyf
      have hin := (region_isPreconnected hp).subset_left_of_subset_union
        (isOpenDisc_interior hS hd).1 isClosed_closure.isOpen_compl
        (disjoint_left.mpr fun y hy h => h hy.1) hsub ⟨x, hxp, hxint⟩
      exact disjoint_left.mp hsep hz (hin (hap hz)).1
    obtain ⟨y, hyp, hyb⟩ := hmeet
    have hyU : y ∉ G.U := region_subset hp hyp
    have hyV : y ∉ Γ.V := fun h => hyU (hVG h)
    have hyD : y ∈ D.U := by
      rw [hDU]
      exact Or.inr (mem_iUnion₂.mpr ⟨f, hf, hyb⟩)
    obtain ⟨b, hb, hyb'⟩ := hedge y hyD (hDV ▸ hyV)
    have hbp : b ⊆ p := subset_region hp hb.2.2.1.isConnected.isPreconnected (hadis b hb) hyb' hyp
    obtain rfl : a = b := hf₂' p hp a ha b hb hap hbp
    have hyf : y ∈ f := Cell.closure_sdiff_V hS hU hf ▸
      (⟨discBd_subset _ hyb, hyV⟩ : y ∈ closure f \ Γ.V)
    exact disjoint_left.mp hsep hyb' (subset_closure hyf)
  -- The part of a region `s` of `Γ'` around the cell `e`.
  let Y : Set S → Set S → Set S := fun s e =>
    e ∪ ⋃ p ∈ {p ∈ G.R | p ⊆ s ∧ ∃ a ∈ D.E, a ⊆ p ∧ a ⊆ e}, p
  have hregsub : ∀ s ∈ Γ'.R, ∀ p ∈ G.R, ∀ x ∈ p, x ∈ s → p ⊆ s := fun s hs p hp x hxp hxs =>
    subset_region hs (region_isPreconnected hp)
      (disjoint_left.mpr fun y hy h => region_subset hp hy (hG_U h)) hxp hxs
  have hopen : ∀ s ∈ Γ'.R, ∀ e ∈ Γ.E, e ⊆ s → IsOpen (Y s e) := by
    intro s hs e he hes
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro y (hy | hy)
    · by_cases hyb : y ∈ discBd (closure e)
      · have hyV : y ∉ Γ.V := disjoint_left.mp (hcellV e he) hy
        have hyD : y ∈ D.U := by
          rw [hDU]
          exact Or.inr (mem_iUnion₂.mpr ⟨e, he, hyb⟩)
        obtain ⟨b, hb, hyb'⟩ := hedge y hyD (hDV ▸ hyV)
        obtain ⟨p, hp, hyp⟩ := exists_region_of_notMem (disjoint_left.mp (hadis b hb) hyb')
        have hbp : b ⊆ p :=
          subset_region hp hb.2.2.1.isConnected.isPreconnected (hadis b hb) hyb' hyp
        obtain ⟨e', he', hbe'⟩ := hcell b hb
        obtain rfl : e' = e := arcComponent_eq he' he (hbe' hyb') hy
        refine Filter.mem_of_superset ((region_isOpen hp).mem_nhds hyp) fun z hz => ?_
        exact Or.inr (mem_iUnion₂.mpr ⟨p, ⟨hp, hregsub s hs p hp y hyp (hes hy), b, hb, hbp,
          hbe'⟩, hz⟩)
      · have hO := (isOpenDisc_interior hS (Cell.isClosedDisc_closure he)).1
        refine Filter.mem_of_superset (hO.mem_nhds ⟨subset_closure hy, hyb⟩) fun z hz => ?_
        have hzV : z ∉ Γ.V := disjoint_left.mp (cellInt_disjoint_V hS he) hz
        exact Or.inl (Cell.closure_sdiff_V hS hU he ▸ (⟨hz.1, hzV⟩ : z ∈ closure e \ Γ.V))
    · obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hy
      exact Filter.mem_of_superset ((region_isOpen hp.1).mem_nhds hyp) fun z hz =>
        Or.inr (mem_iUnion₂.mpr ⟨p, hp, hz⟩)
  have hdisj : ∀ s, ∀ e ∈ Γ.E, ∀ f ∈ Γ.E, f ≠ e → Disjoint (Y s f) (Y s e) := by
    intro s e he f hf hfe
    refine disjoint_left.mpr ?_
    rintro x (hx | hx) (hy | hy)
    · exact hfe (arcComponent_eq hf he hx hy)
    · obtain ⟨p, ⟨hp, -, a, ha, hap, hae⟩, hxp⟩ := mem_iUnion₂.mp hy
      exact disjoint_left.mp (hcross p hp a ha hap e he hae f hf hfe) hx hxp
    · obtain ⟨p, ⟨hp, -, a, ha, hap, haf⟩, hxp⟩ := mem_iUnion₂.mp hx
      exact disjoint_left.mp (hcross p hp a ha hap f hf haf e he hfe.symm) hy hxp
    · obtain ⟨p, ⟨hp, -, a, ha, hap, haf⟩, hxp⟩ := mem_iUnion₂.mp hx
      obtain ⟨q, ⟨hq, -, b, hb, hbq, hbe⟩, hxq⟩ := mem_iUnion₂.mp hy
      obtain rfl : p = q := region_eq_of_mem hp hq hxp hxq
      obtain rfl := hf₂' p hp a ha b hb hap hbq
      obtain ⟨z, hz⟩ := ha.1
      exact hfe (arcComponent_eq hf he (haf hz) (hbe hz))
  have hstarU : G.U ⊆ Γ'.U ∪ Γ.U := by
    rw [hG.U]
    refine union_subset_union_right _ (iUnion₂_subset fun t ht => ?_)
    have hb := Cell.closure_inter_V_subset hS ht.1 ⟨ht.2.2, ht.2.1⟩
    exact (star_subset_closure hst ht.1 hb).trans (closure_subset_cell_U hrad ht.1)
  have hcover : ∀ s ∈ Γ'.R, ∀ x ∈ s, ∃ e ∈ Γ.E, e ⊆ s ∧ x ∈ Y s e := by
    intro s hs x hx
    have hxU' : x ∉ Γ'.U := region_subset hs hx
    by_cases hxU : x ∈ Γ.U
    · rcases Cell.mem_V_or_cell Γ hxU with h | ⟨e, he, hxe⟩
      · exact (hxU' (Γ'.V_subset_U (hrad.2.2.1 h))).elim
      · exact ⟨e, he, subset_region hs he.2.2.1.isConnected.isPreconnected (hcellU' e he) hxe hx,
          Or.inl hxe⟩
    · have hxG : x ∉ G.U := fun h => (hstarU h).elim hxU' hxU
      obtain ⟨p, hp, hxp⟩ := exists_region_of_notMem hxG
      have hps := hregsub s hs p hp x hxp hx
      obtain ⟨a, ha, hap⟩ := hf₁' p hp
      obtain ⟨e, he, hae⟩ := hcell a ha
      obtain ⟨z, hz⟩ := ha.1
      refine ⟨e, he, subset_region hs he.2.2.1.isConnected.isPreconnected (hcellU' e he) (hae hz)
        (hps (hap hz)), Or.inr (mem_iUnion₂.mpr ⟨p, ⟨hp, hps, a, ha, hap, hae⟩, hxp⟩)⟩
  have hfill : ∀ s ∈ Γ'.R, ∀ e ∈ Γ.E, e ⊆ s → s ⊆ Y s e := by
    intro s hs e he hes
    let Rest : Set S := ⋃ f ∈ {f ∈ Γ.E | f ⊆ s ∧ f ≠ e}, Y s f
    have hRest : IsOpen Rest := isOpen_biUnion fun f hf => hopen s hs f hf.1 hf.2.1
    have hcov : s ⊆ Y s e ∪ Rest := by
      intro x hx
      obtain ⟨f, hf, hfs, hxf⟩ := hcover s hs x hx
      by_cases hfe : f = e
      · exact Or.inl (hfe ▸ hxf)
      · exact Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfs, hfe⟩, hxf⟩)
    have hd : Disjoint (Y s e) Rest := by
      refine disjoint_left.mpr fun x hx hx' => ?_
      obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx'
      exact disjoint_left.mp (hdisj s e he f hf.1 hf.2.2) hxf hx
    obtain ⟨y, hy⟩ := he.1
    exact (region_isPreconnected hs).subset_left_of_subset_union (hopen s hs e he hes) hRest hd hcov
      ⟨y, hes hy, Or.inl hy⟩
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨x, hx⟩ := region_nonempty hs
    obtain ⟨e, he, hes, -⟩ := hcover s hs x hx
    exact ⟨e, he, hes⟩
  · intro s hs e he f hf hes hfs
    by_contra hef
    obtain ⟨y, hy⟩ := (show f ∈ Γ.E from hf).1
    exact disjoint_left.mp (hdisj s e he f hf (Ne.symm hef)) (Or.inl hy)
      (hfill s hs e he hes (hfs hy))
  · intro s hs e he hes v hvV hvs
    have hfin := finite_R hS G
    have hcl := closure_mono (hfill s hs e he hes) hvs
    change v ∈ closure (e ∪ ⋃ p ∈ {p ∈ G.R | p ⊆ s ∧ ∃ a ∈ D.E, a ⊆ p ∧ a ⊆ e}, p) at hcl
    have hpfin : {p ∈ G.R | p ⊆ s ∧ ∃ a ∈ D.E, a ⊆ p ∧ a ⊆ e}.Finite :=
      hfin.subset fun _ h => h.1
    rw [closure_union, hpfin.closure_biUnion _] at hcl
    rcases hcl with h | h
    · exact h
    · obtain ⟨p, ⟨hp, -, a, ha, hap, hae⟩, hvp⟩ := mem_iUnion₂.mp h
      exact closure_mono hae (hf₃' p hp a ha hap v (hDV.symm.subset hvV) hvp)

end GraphMinor.GM11
