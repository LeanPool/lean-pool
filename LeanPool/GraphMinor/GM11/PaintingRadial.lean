/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PaintingStars

/-!
# A radial drawing of the boundary drawing of a painting

Let `Γ` be a 2-cell painting in which each cell has a vertex, with radial drawing `Γ'`, and let `G`
be
`Γ'` with stars in the cells. Then `G` is a radial drawing of the drawing `D` of the boundaries of
the
cells (`radial_of_stars`).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]
  {Γ : Painting S} {Γ' G D : Drawing S} {c : Set S → S} {K : Set S → S → Set S}
  (hrad : PreRad (PaintingOrDrawing.painting Γ) Γ') (hst : CellStars Γ c K)
  (hS : IsClosedSurface S) (hG : IsStarDrawing Γ Γ' c K G)
  (hDU : D.U = Γ.V ∪ ⋃ e ∈ Γ.E, discBd (closure e))
  (hDV : D.V = Γ.V) (hv : ∀ e ∈ Γ.E, (closure e ∩ Γ.V).Nonempty)

omit [T2Space S] in
/-- The drawing `D` of the boundaries of the cells is 2-cell. -/
theorem boundary_twoCell (hS : IsClosedSurface S) (hP : ∀ r ∈ Γ.R, IsOpenDisc r) [ConnectedSpace S]
    (hDR : D.R = Γ.R ∪ cellInt '' Γ.E) : (PaintingOrDrawing.drawing D).IsTwoCell := by
  refine ⟨inferInstance, ?_⟩
  intro r hr
  have hr' : r ∈ D.R := hr
  rw [hDR] at hr'
  rcases hr' with h | ⟨e, he, rfl⟩
  · exact hP r h
  · exact isOpenDisc_interior hS (Cell.isClosedDisc_closure he)

include hrad hst hS hG

omit hG [T2Space S] in
theorem hub_notMem_U' {e : Set S} (he : e ∈ Γ.E) : c e ∉ Γ'.U := fun h =>
  hub_notMem_V hst hS he ((show Γ.U ∩ Γ'.U = Γ.V from hrad.2.1) ▸
    ⟨cellInt_subset_U hrad he (hst.hub e he), h⟩)

omit hS hrad hst [T2Space S] in
theorem G_V_cases {x : S} (hx : x ∈ G.V) : x ∈ Γ'.V ∨ ∃ e ∈ Γ.E, x = c e := by
  rw [hG.V] at hx
  rcases hx with h | ⟨t, ht, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨t.1, ht.1, rfl⟩

omit hrad hG in
theorem star_closure {t : Set S × S} (ht : t ∈ cellPairs Γ) :
    closure (K t.1 t.2 \ {c t.1, t.2}) = K t.1 t.2 :=
  closure_sdiff_pair (hst.line _ ht.1 _ (Cell.closure_inter_V_subset hS ht.1 ⟨ht.2.2, ht.2.1⟩))

omit [T2Space S] in
/-- A line of a star meets the vertices of `G` in its ends. -/
theorem star_inter_V {t : Set S × S} (ht : t ∈ cellPairs Γ) :
    K t.1 t.2 ∩ G.V = {t.2, c t.1} := by
  have hb : t.2 ∈ discBd (closure t.1) := Cell.closure_inter_V_subset hS ht.1 ⟨ht.2.2, ht.2.1⟩
  obtain ⟨f, h0, h1⟩ := hst.line t.1 ht.1 t.2 hb
  apply subset_antisymm
  · rintro x ⟨hx, hxG⟩
    by_cases hxb : x = t.2
    · exact Or.inl hxb
    refine Or.inr ?_
    have hxint := hst.sub _ ht.1 _ hb ⟨hx, hxb⟩
    rcases G_V_cases hG hxG with h | ⟨e, he, rfl⟩
    · exact (hxb (star_inter_U hrad hst hS ht hx (Γ'.V_subset_U h))).elim
    · by_cases hee : e = t.1
      · rw [hee]
        rfl
      · exact (disjoint_left.mp (cellInt_disjoint hrad hS he ht.1 hee) (hst.hub e he) hxint.1).elim
  · rintro x (rfl | rfl)
    · refine ⟨by have := (f 1).2; rwa [h1] at this, ?_⟩
      rw [hG.V]
      exact Or.inl (hrad.2.2.1 ht.2.1)
    · refine ⟨by have := (f 0).2; rwa [h0] at this, ?_⟩
      rw [hG.V]
      exact Or.inr ⟨t, ht, rfl⟩

omit [T2Space S] in
/-- An edge of `Γ'` has the same vertices in `G` as in `Γ'`. -/
theorem closure_inter_G_V {e : Set S} (he : e ∈ Γ'.E) : closure e ∩ G.V = closure e ∩ Γ'.V := by
  apply subset_antisymm
  · rintro x ⟨hx, hxG⟩
    rcases G_V_cases hG hxG with h | ⟨f, hf, rfl⟩
    · exact ⟨hx, h⟩
    · exact (hub_notMem_U' hrad hst hS hf (Γ'.closure_subset_U he hx)).elim
  · rintro x ⟨hx, hxG⟩
    refine ⟨hx, ?_⟩
    rw [hG.V]
    exact Or.inl hxG

include hDU in
omit hst hG hS [T2Space S] in
theorem D_U_subset : D.U ⊆ Γ.U := by
  rw [hDU]
  refine union_subset Γ.V_subset_U (iUnion₂_subset fun e he => ?_)
  exact (discBd_subset _).trans (closure_subset_cell_U hrad he)

include hDU in
omit hst hG [T2Space S] in
theorem cellInt_disjoint_D {e : Set S} (he : e ∈ Γ.E) : Disjoint (cellInt e) D.U := by
  rw [hDU]
  refine disjoint_left.mpr fun x hx h => ?_
  rcases h with h | h
  · exact disjoint_left.mp (cellInt_disjoint_V hS he) hx h
  · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp h
    by_cases hef : e = f
    · subst hef
      exact hx.2 hxf
    · exact disjoint_left.mp (cellInt_disjoint hrad hS he hf hef) hx (discBd_subset _ hxf)

include hDU hDV in
omit [T2Space S] in
/-- Condition (i) of a radial drawing. -/
theorem star_cond_one : D.U ∩ G.U = D.V := by
  have hUU' : Γ.U ∩ Γ'.U = Γ.V := hrad.2.1
  rw [hDV]
  apply subset_antisymm
  · rintro x ⟨hx, hxG⟩
    rw [hG.U] at hxG
    rcases hxG with h | h
    · exact hUU' ▸ ⟨D_U_subset hrad hDU hx, h⟩
    · obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp h
      by_cases hxb : x = t.2
      · exact hxb ▸ ht.2.1
      · have hb := Cell.closure_inter_V_subset hS ht.1 ⟨ht.2.2, ht.2.1⟩
        exact (disjoint_left.mp (cellInt_disjoint_D hrad hS hDU ht.1)
          (hst.sub _ ht.1 _ hb ⟨hxt, hxb⟩) hx).elim
  · intro x hx
    refine ⟨?_, ?_⟩
    · rw [hDU]
      exact Or.inl hx
    · rw [hG.U]
      exact Or.inl (Γ'.V_subset_U (hrad.2.2.1 hx))

include hv in
omit hrad hst hS [T2Space S] in
theorem hub_mem_G {e : Set S} (he : e ∈ Γ.E) : c e ∈ G.V := by
  obtain ⟨b, hb, hbV⟩ := hv e he
  rw [hG.V]
  exact Or.inr ⟨(e, b), ⟨he, hbV, hb⟩, rfl⟩

include hv in
omit [T2Space S] in
/-- A region of `Γ` or the interior of a cell has exactly one vertex of `G`. -/
theorem star_cond_two {r : Set S} (hr : r ∈ Γ.R ∪ cellInt '' Γ.E) : ∃! w, w ∈ r ∧ w ∈ G.V := by
  have hUU' : Γ.U ∩ Γ'.U = Γ.V := hrad.2.1
  have hoff : ∀ {a x}, a ∈ Γ.R → x ∈ a → x ∉ Γ.U := by
    rintro a x ⟨y, -, rfl⟩ hx
    exact (connectedComponentIn_subset _ _ hx).2
  rcases hr with hr | ⟨e, he, rfl⟩
  · obtain ⟨w, ⟨hwr, hwV⟩, huniq⟩ := hrad.2.2.2.1 r hr
    refine ⟨w, ⟨hwr, ?_⟩, ?_⟩
    · rw [hG.V]
      exact Or.inl hwV
    · rintro y ⟨hyr, hyG⟩
      rcases G_V_cases hG hyG with h | ⟨f, hf, rfl⟩
      · exact huniq y ⟨hyr, h⟩
      · exact (hoff hr hyr (cellInt_subset_U hrad hf (hst.hub f hf))).elim
  · refine ⟨c e, ⟨hst.hub e he, hub_mem_G hG hv he⟩, ?_⟩
    rintro y ⟨hyr, hyG⟩
    rcases G_V_cases hG hyG with h | ⟨f, hf, rfl⟩
    · by_cases hyV : y ∈ Γ.V
      · exact (disjoint_left.mp (cellInt_disjoint_V hS he) hyr hyV).elim
      · obtain ⟨a, ha, hya⟩ := hrad.2.2.2.2.1 y ⟨h, hyV⟩
        exact (hoff ha hya (cellInt_subset_U hrad he hyr)).elim
    · by_cases hfe : f = e
      · rw [hfe]
      · exact (disjoint_left.mp (cellInt_disjoint hrad hS hf he hfe) (hst.hub f hf) hyr.1).elim

include hDV in
omit hS [T2Space S] in
/-- Each vertex of `G` not in `D` lies in a region of `Γ` or the interior of a cell. -/
theorem star_cond_three {w : S} (hw : w ∈ G.V \ D.V) : ∃ r ∈ Γ.R ∪ cellInt '' Γ.E, w ∈ r := by
  rw [hDV] at hw
  rcases G_V_cases hG hw.1 with h | ⟨e, he, rfl⟩
  · obtain ⟨a, ha, hwa⟩ := hrad.2.2.2.2.1 w ⟨h, hw.2⟩
    exact ⟨a, Or.inl ha, hwa⟩
  · exact ⟨cellInt e, Or.inr ⟨e, he, rfl⟩, hst.hub e he⟩

include hDV in
/-- Each edge of `G` has one end in `D` and one other. -/
theorem star_cond_four {e : Set S} (he : e ∈ G.E) :
    ∃ v ∈ D.V, ∃ w ∈ G.V \ D.V, closure e ∩ G.V = {v, w} := by
  rw [hDV]
  rw [hG.E] at he
  rcases he with he | ⟨t, ht, rfl⟩
  · obtain ⟨v, hv', w, ⟨hwV, hwn⟩, hcap⟩ := hrad.2.2.2.2.2.1 e he
    refine ⟨v, hv', w, ⟨?_, hwn⟩, ?_⟩
    · rw [hG.V]
      exact Or.inl hwV
    · rw [closure_inter_G_V hrad hst hS hG he]
      exact hcap
  · have hcG := star_inter_V hrad hst hS hG ht
    refine ⟨t.2, ht.2.1, c t.1, ⟨?_, hub_notMem_V hst hS ht.1⟩, ?_⟩
    · have : c t.1 ∈ K t.1 t.2 ∩ G.V := by rw [hcG]; simp
      exact this.2
    · rw [star_closure hst hS ht, hcG]

include hDV hv in
/-- Condition (iv) of a radial drawing. -/
theorem star_cond_five {e f : Set S} (he : e ∈ G.E) (hf : f ∈ G.E) (hef : e ≠ f) {v : S}
    (hvD : v ∈ D.V) {r : Set S} (hr : r ∈ Γ.R ∪ cellInt '' Γ.E) {w : S} (hw : w ∈ r ∩ G.V)
    (he' : closure e ∩ G.V = {v, w}) (hf' : closure f ∩ G.V = {v, w}) :
    ¬ ∃ Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ r ∪ {v} ∧ subBd Δ = closure e ∪ closure f := by
  have hoff : ∀ {a x}, a ∈ Γ.R → x ∈ a → x ∉ Γ.U := by
    rintro a x ⟨y, -, rfl⟩ hx
    exact (connectedComponentIn_subset _ _ hx).2
  rw [hDV] at hvD
  have hwcap : ∀ {g : Set S}, closure g ∩ G.V = {v, w} → w ∈ closure g := by
    intro g h
    have : w ∈ closure g ∩ G.V := by rw [h]; simp
    exact this.1
  rcases hr with hr | ⟨g, hg, rfl⟩
  · -- Both edges are edges of `Γ'`, as the lines of the stars stay in the cells.
    have hin : ∀ {g : Set S}, g ∈ G.E → closure g ∩ G.V = {v, w} → g ∈ Γ'.E := by
      intro g hg hc
      rw [hG.E] at hg
      rcases hg with h | ⟨t, ht, rfl⟩
      · exact h
      · exfalso
        have hb := Cell.closure_inter_V_subset hS ht.1 ⟨ht.2.2, ht.2.1⟩
        have hwK := hwcap hc
        rw [star_closure hst hS ht] at hwK
        exact hoff hr hw.1 (closure_subset_cell_U hrad ht.1 (star_subset_closure hst ht.1 hb hwK))
    have he₁ := hin he he'
    have hf₁ := hin hf hf'
    have hw' : w ∈ Γ'.V := by
      rcases G_V_cases hG hw.2 with h | ⟨g, hg, rfl⟩
      · exact h
      · exact (hoff hr hw.1 (cellInt_subset_U hrad hg (hst.hub g hg))).elim
    rw [closure_inter_G_V hrad hst hS hG he₁] at he'
    rw [closure_inter_G_V hrad hst hS hG hf₁] at hf'
    exact hrad.2.2.2.2.2.2 e he₁ f hf₁ hef v hvD r hr w ⟨hw.1, hw'⟩ he' hf'
  · exfalso
    have hwc : w = c g := (star_cond_two hrad hst hS hG hv (Or.inr ⟨g, hg, rfl⟩)).unique
      hw ⟨hst.hub g hg, hub_mem_G hG hv hg⟩
    subst hwc
    have hne : v ≠ c g := fun h => hub_notMem_V hst hS hg (h ▸ hvD)
    have hin : ∀ {x : Set S}, x ∈ G.E → closure x ∩ G.V = {v, c g} →
        x = K g v \ {c g, v} := by
      intro x hx hc
      rw [hG.E] at hx
      rcases hx with h | ⟨t, ht, rfl⟩
      · exact (hub_notMem_U' hrad hst hS hg (Γ'.closure_subset_U h (hwcap hc))).elim
      · rw [star_closure hst hS ht, star_inter_V hrad hst hS hG ht] at hc
        have h₁ : c g ∈ ({t.2, c t.1} : Set S) := hc ▸ (Or.inr rfl)
        have h₂ : v ∈ ({t.2, c t.1} : Set S) := hc ▸ (Or.inl rfl)
        have hcc : c g = c t.1 := by
          rcases h₁ with h | h
          · exact (hub_notMem_V hst hS hg (h ▸ ht.2.1)).elim
          · exact h
        have htg : t.1 = g := by
          by_contra hn
          exact disjoint_left.mp (cellInt_disjoint hrad hS hg ht.1 (Ne.symm hn)) (hst.hub g hg)
            (hcc ▸ (hst.hub t.1 ht.1).1)
        have hv2 : v = t.2 := by
          rcases h₂ with h | h
          · exact h
          · exact (hne (h.trans hcc.symm)).elim
        change K t.1 t.2 \ {c t.1, t.2} = _
        rw [htg, ← hv2]
    exact hef ((hin he he').trans (hin hf hf').symm)

include hDU hDV hv in
/-- **`G` is a pre-radial drawing of `D`.** -/
theorem star_preRadial (hDR : D.R = Γ.R ∪ cellInt '' Γ.E) :
    (PaintingOrDrawing.drawing D).IsPreRadialDrawing G := by
  refine ⟨star_cond_one hrad hst hS hG hDU hDV, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ Γ.V := hDV ▸ hx
    change x ∈ G.V
    rw [hG.V]
    exact Or.inl (hrad.2.2.1 hx')
  · intro r hr
    have hr' : r ∈ D.R := hr
    rw [hDR] at hr'
    exact star_cond_two hrad hst hS hG hv hr'
  · intro w hw
    obtain ⟨r, hr, hwr⟩ := star_cond_three hrad hst hG hDV hw
    refine ⟨r, ?_, hwr⟩
    change r ∈ D.R
    rw [hDR]
    exact hr
  · intro e he
    exact star_cond_four hrad hst hS hG hDV he
  · intro e he f hf hef v hvD r hr w hw he' hf'
    have hr' : r ∈ D.R := hr
    rw [hDR] at hr'
    exact star_cond_five hrad hst hS hG hDV hv he hf hef hvD hr' hw he' hf'

include hDU hDV hv in
/-- **`G` is maximal: it is a radial drawing of `D`.** -/
theorem radial_of_stars (hmax : RadMax (PaintingOrDrawing.painting Γ) Γ')
    (hDR : D.R = Γ.R ∪ cellInt '' Γ.E) [ConnectedSpace S] :
    (PaintingOrDrawing.drawing D).IsRadialDrawing G := by
  have hpre := star_preRadial hrad hst hS hG hDU hDV hv hDR
  have hoff : ∀ {a x}, a ∈ Γ.R → x ∈ a → x ∉ Γ.U := by
    rintro a x ⟨y, -, rfl⟩ hx
    exact (connectedComponentIn_subset _ _ hx).2
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  refine ⟨boundary_twoCell hS hrad.1.2 hDR, hpre, ?_⟩
  rintro G₁ hp ⟨hVs, hEs⟩
  have hVG : G₁.V ⊆ G.V := by
    intro x hx
    by_cases hxD : x ∈ D.V
    · exact hpre.2.1 hxD
    · obtain ⟨r, hr, hxr⟩ := hp.2.2.2.1 x ⟨hx, hxD⟩
      obtain ⟨w, ⟨hwr, hwG⟩, -⟩ := hpre.2.2.1 r hr
      have : x = w := (hp.2.2.1 r hr).unique ⟨hxr, hx⟩ ⟨hwr, hVs hwG⟩
      exact this ▸ hwG
  have hVeq : G₁.V = G.V := subset_antisymm hVG hVs
  refine ⟨hVG, fun g hg => ?_⟩
  obtain ⟨v, hvD, w, ⟨hwV, hwn⟩, hcap⟩ := hp.2.2.2.2.1 g hg
  obtain ⟨r, hr, hwr⟩ := hp.2.2.2.1 w ⟨hwV, hwn⟩
  have hr' : r ∈ D.R := hr
  have hvΓ : v ∈ Γ.V := hDV ▸ hvD
  have hgD : Disjoint g D.U := by
    refine disjoint_left.mpr fun x hx hxD => ?_
    have h₁ : x ∈ D.U ∩ G₁.U := ⟨hxD, G₁.closure_subset_U hg (subset_closure hx)⟩
    have h₂ : x ∈ D.V := (show D.U ∩ G₁.U = D.V from hp.1) ▸ h₁
    exact edge_notMem_V hg hx (hp.2.1 h₂)
  have hwg : w ∈ closure g := by
    have : w ∈ closure g ∩ G₁.V := by rw [hcap]; simp
    exact this.1
  have hvg : v ∈ closure g := by
    have : v ∈ closure g ∩ G₁.V := by rw [hcap]; simp
    exact this.1
  have hvV : v ∈ G₁.V := by
    have : v ∈ closure g ∩ G₁.V := by rw [hcap]; simp
    exact this.2
  obtain ⟨y, hyr, hyg⟩ := mem_closure_iff.mp hwg r (region_isOpen hr') hwr
  have hgr : g ⊆ r := subset_region hr' hg.2.2.1.isConnected.isPreconnected hgD hyg hyr
  have hgcl : ∀ x ∈ closure g, x = v ∨ x = w ∨ x ∈ g := by
    intro x hx
    by_cases hxV : x ∈ G₁.V
    · have : x ∈ closure g ∩ G₁.V := ⟨hx, hxV⟩
      rw [hcap] at this
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ((G₁.closure_diff_V hg).subset ⟨hx, hxV⟩))
  rw [hDR] at hr'
  rcases hr' with hrΓ | ⟨e, he, rfl⟩
  · -- `g` lies in a region of `Γ`, so that adding it to `Γ'` contradicts the maximality of `Γ'`.
    have hwΓ' : w ∈ Γ'.V := by
      rcases G_V_cases hG (hVG hwV) with h | ⟨f, hf, rfl⟩
      · exact h
      · exact (hoff hrΓ hwr (cellInt_subset_U hrad hf (hst.hub f hf))).elim
    have hvΓ' : v ∈ Γ'.V := hrad.2.2.1 hvΓ
    have hV'G₁ : Γ'.V ⊆ G₁.V := fun x hx => hVs (by rw [hG.V]; exact Or.inl hx)
    have hE'G₁ : Γ'.E ⊆ G₁.E := fun x hx => hEs (by rw [hG.E]; exact Or.inl hx)
    let G₂ : Drawing S := G₁.span Γ'.V (insert g Γ'.E)
    have hsame : ∀ e ∈ insert g Γ'.E, closure e ∩ G₁.V = closure e ∩ Γ'.V := by
      rintro e (rfl | he)
      · apply subset_antisymm
        · rintro x ⟨hx, hxV⟩
          have : x ∈ closure e ∩ G₁.V := ⟨hx, hxV⟩
          rw [hcap] at this
          refine ⟨hx, ?_⟩
          rcases this with h | h
          · exact h ▸ hvΓ'
          · exact h ▸ hwΓ'
        · exact fun x hx => ⟨hx.1, hV'G₁ hx.2⟩
      · rw [hVeq]
        exact closure_inter_G_V hrad hst hS hG he
    have hG₂V : G₂.V = Γ'.V := by
      apply subset_antisymm
      · rintro x (⟨hx, -⟩ | hx)
        · exact hx
        · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
          rw [hsame e he.1] at hxe
          exact hxe.2
      · exact fun x hx => Or.inl ⟨hx, hV'G₁ hx⟩
    have hG₂E : G₂.E = insert g Γ'.E := by
      exact (G₁.span_E _ _).trans (inter_eq_left.mpr (insert_subset hg hE'G₁))
    have hG₂U : G₂.U ⊆ Γ'.U ∪ closure g := by
      rintro x (hx | hx)
      · have hx' : x ∈ G₂.V := hx
        rw [hG₂V] at hx'
        exact Or.inl (Γ'.V_subset_U hx')
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
        rcases he.1 with rfl | h
        · exact Or.inr hxe
        · exact Or.inl (Γ'.closure_subset_U h hxe)
    have hUU' : Γ.U ∩ Γ'.U = Γ.V := hrad.2.1
    have hpre₂ : (PaintingOrDrawing.painting Γ).IsPreRadialDrawing G₂ := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply subset_antisymm
        · rintro x ⟨hxU, hxG⟩
          rcases hG₂U hxG with h | h
          · exact hUU'.subset ⟨hxU, h⟩
          · rcases hgcl x h with h' | h' | h'
            · exact h' ▸ hvΓ
            · exact (hoff hrΓ (h' ▸ hwr) hxU).elim
            · exact (hoff hrΓ (hgr h') hxU).elim
        · intro x hx
          have hx' : x ∈ Γ'.V := hrad.2.2.1 hx
          exact ⟨Γ.V_subset_U hx, Or.inl (show x ∈ _ from by
            have : x ∈ G₂.V := hG₂V ▸ hx'
            exact this)⟩
      · change Γ.V ⊆ G₂.V
        rw [hG₂V]
        exact hrad.2.2.1
      · change ∀ r ∈ Γ.R, ∃! w, w ∈ r ∧ w ∈ G₂.V
        rw [hG₂V]
        exact hrad.2.2.2.1
      · change ∀ w ∈ G₂.V \ Γ.V, ∃ r ∈ Γ.R, w ∈ r
        rw [hG₂V]
        exact hrad.2.2.2.2.1
      · change ∀ e ∈ G₂.E, ∃ v ∈ Γ.V, ∃ w ∈ G₂.V \ Γ.V, closure e ∩ G₂.V = {v, w}
        rw [hG₂V, hG₂E]
        rintro e (rfl | he)
        · refine ⟨v, hvΓ, w, ⟨hwΓ', fun h => hwn (hDV.symm.subset h)⟩, ?_⟩
          rw [← hsame e (mem_insert _ _), hcap]
        · exact hrad.2.2.2.2.2.1 e he
      · change ∀ e ∈ G₂.E, ∀ f ∈ G₂.E, e ≠ f → ∀ v ∈ Γ.V, ∀ r ∈ Γ.R, ∀ w ∈ r ∩ G₂.V,
          closure e ∩ G₂.V = {v, w} → closure f ∩ G₂.V = {v, w} →
          ¬ ∃ Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ r ∪ {v} ∧ subBd Δ = closure e ∪ closure f
        rw [hG₂V, hG₂E]
        intro e he f hf hef x hx a ha z hz hez hfz
        have he₁ : e ∈ G₁.E := insert_subset hg hE'G₁ he
        have hf₁ : f ∈ G₁.E := insert_subset hg hE'G₁ hf
        have ha' : a ∈ (PaintingOrDrawing.drawing D).R := by
          change a ∈ D.R
          rw [hDR]
          exact Or.inl ha
        refine hp.2.2.2.2.2 e he₁ f hf₁ hef x (hDV.symm.subset hx) a ha' z ⟨hz.1, hV'G₁ hz.2⟩ ?_ ?_
        · rw [hsame e he, hez]
        · rw [hsame f hf, hfz]
    have hsub := (hmax G₂ hpre₂ ⟨hG₂V.ge, by rw [hG₂E]; exact subset_insert _ _⟩).2
    have hgE : g ∈ Γ'.E := hsub (by rw [hG₂E]; exact mem_insert _ _)
    rw [hG.E]
    exact Or.inl hgE
  · -- `g` lies in the interior of a cell, where it is parallel to a line of the star.
    have hwc : w = c e := (hpre.2.2.1 (cellInt e) hr).unique ⟨hwr, hVG hwV⟩
      ⟨hst.hub e he, hub_mem_G hG hv he⟩
    subst hwc
    have hd := Cell.isClosedDisc_closure he
    have hcl : closure (cellInt e) ⊆ closure e :=
      closure_minimal sdiff_subset isClosed_closure
    have hve : v ∈ closure e := hcl (closure_mono hgr hvg)
    have ht : (e, v) ∈ cellPairs Γ := ⟨he, hvΓ, hve⟩
    have hb : v ∈ discBd (closure e) := Cell.closure_inter_V_subset hS he ⟨hve, hvΓ⟩
    let s : Set S := K e v \ {c e, v}
    have hsG : s ∈ G.E := by
      rw [hG.E]
      exact Or.inr ⟨(e, v), ht, rfl⟩
    by_cases hgs : g = s
    · exact hgs ▸ hsG
    exfalso
    have hs₁ : s ∈ G₁.E := hEs hsG
    have hscl : closure s = K e v := star_closure hst hS ht
    have hne : v ≠ c e := fun h => hub_notMem_V hst hS he (h ▸ hvΓ)
    have hcaps : closure s ∩ G₁.V = {v, c e} := by
      rw [hVeq, hscl]
      exact star_inter_V hrad hst hS hG ht
    have hJ := isOArc_spokes hg hs₁ hgs hne hcap hcaps
    have hJsub : closure g ∪ closure s ⊆ cellInt e ∪ {v} := by
      rintro x (hx | hx)
      · rcases hgcl x hx with h | h | h
        · exact Or.inr h
        · exact Or.inl (h ▸ hst.hub e he)
        · exact Or.inl (hgr h)
      · rw [hscl] at hx
        by_cases hxv : x = v
        · exact Or.inr hxv
        · exact Or.inl (hst.sub e he v hb ⟨hx, hxv⟩)
    have hJD : closure g ∪ closure s ⊆ closure e := fun x hx => by
      rcases hJsub hx with h | h
      · exact h.1
      · exact mem_singleton_iff.mp h ▸ hve
    obtain ⟨Δ, ⟨hΔsub, hΔ, hΔbd, -, hΔdis, -⟩, -⟩ := disc_oArc _ _ hd hJD hJ
    refine hp.2.2.2.2.2 g hg s hs₁ hgs v hvD _ hr (c e) ⟨hwr, hwV⟩ hcap hcaps
      ⟨Δ, hΔ, fun x hx => ?_, ?_⟩
    · by_cases hxJ : x ∈ closure g ∪ closure s
      · exact hJsub hxJ
      · exact Or.inl ⟨hΔsub hx, disjoint_left.mp hΔdis ⟨hx, hxJ⟩⟩
    · rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hΔ, hΔbd]

end GraphMinor.GM11
