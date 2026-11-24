/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section6Pretangle
public import LeanPool.GraphMinor.GM11.Section7
public import LeanPool.GraphMinor.GM11.Section3
public import LeanPool.GraphMinor.GM11.Section4c
public import LeanPool.GraphMinor.GM11.Forest
public import LeanPool.GraphMinor.GM11.Fan
public import LeanPool.GraphMinor.GM11.PlaneFacts
public import LeanPool.GraphMinor.Surface.DiscsInSurface
public import LeanPool.GraphMinor.Surface.DiscUnion
public import LeanPool.GraphMinor.Surface.SphereDisc
public import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# Slopes from Pretangles and Closed Discs

This file provides two slope constructions used across Graph Minors XIV:

1. `isSlope_of_derived`: the derived inside function `ins` of a respectful pretangle `T` of order
   `θ ≥ 1` in a 2-cell drawing `Γ` is a slope of order `2θ` in a radial drawing `Γ'`
   (Graph Minors XI, (6.6), used in Sections 7 and 9 of Graph Minors XIV).
2. `isSlope_discIns`: for any drawing `Γ'` with `U(Γ') ⊆ Δ` inside a closed disc `Δ` in a connected
   closed surface `S`, the function `discIns Δ` mapping each circuit `C` of `Γ'` to the unique
   closed disc in `Δ` bounded by `U(C)` is a slope of any order `k ≥ 2` on `Γ'` (used in Section 5
   of Graph Minors XIV).
3. `IsClosedDisc.isOpenDisc_diff_subBd`: for any closed disc `D` in a closed surface `S`,
   `D \ subBd D` is an open disc with closure `D` and boundary `subBd D`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Topology GraphMinor.Surface GraphMinor.GM11 Metric Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Boundary and Interior of Closed Discs in a Closed Surface -/

/-- The manifold boundary of a closed disc in a closed surface is its frontier. This is invariance
of domain, in a chart of the surface. -/
theorem IsClosedDisc.frontier_eq_discBd (hS : IsClosedSurface S) {D : Set S} (hD : IsClosedDisc D) :
    frontier D = discBd D := by
  have : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := (IsClosedSurface.isSurface hS).2.2
  have hcl : IsClosed D := hD.isCompact.isClosed
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  obtain ⟨u1, -⟩ := c.union_ball
  have hO := c.isOpen_image_ball hman
  have hsub : g '' ball 0 1 ⊆ D := fun x hx => u1 ▸ Or.inl hx
  apply subset_antisymm
  · intro x hx
    have hxD : x ∈ D := hcl.frontier_subset hx
    rw [← u1] at hxD
    rcases hxD with h' | h'
    · exact absurd (interior_maximal hsub hO h') hx.2
    · exact h'
  · intro x hx
    have hxD : x ∈ D := Surface.discBd_subset _ hx
    refine ⟨subset_closure hxD, fun hint => ?_⟩
    obtain ⟨U, hU, hxU, ⟨f⟩⟩ := hS.2.2 x
    classical
    let G : ℂ → S := fun w =>
      if hw : complexPlane w ∈ OpenUnitDisc then (f.symm ⟨_, hw⟩).1 else x
    let M : Set ℂ := complexPlane ⁻¹' OpenUnitDisc
    have hMo : IsOpen M := by
      have : IsOpen OpenUnitDisc := by
        have := Metric.isOpen_ball (x := (0 : EuclideanPlane)) (ε := 1)
        convert this using 1
        ext y
        simp [OpenUnitDisc]
      exact this.preimage complexPlane.continuous
    have hG : ∀ w (hw : w ∈ M), G w = (f.symm ⟨_, hw⟩).1 := fun w hw => by
      have hw' : complexPlane w ∈ OpenUnitDisc := hw
      simp only [G, hw', dite_true]
    have hGc : ContinuousOn G M := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : M.domRestrict G = fun w : M => (f.symm ⟨complexPlane w.1, w.2⟩).1 := by
        ext w
        exact hG w.1 w.2
      rw [this]
      refine continuous_subtype_val.comp (f.symm.continuous.comp ?_)
      exact Continuous.subtype_mk (complexPlane.continuous.comp continuous_subtype_val) _
    have hGi : InjOn G M := by
      intro a ha b hb hab
      rw [hG a ha, hG b hb] at hab
      have h₁ := f.symm.injective (Subtype.ext hab)
      exact complexPlane.injective (congrArg Subtype.val h₁)
    let B : Set ℂ := M ∩ G ⁻¹' interior D
    have hBo : IsOpen B := hGc.isOpen_inter_preimage hMo isOpen_interior
    have hBD : MapsTo G B D := fun w hw => interior_subset hw.2
    have hHc : ContinuousOn (h ∘ G) B := c.hc.comp (hGc.mono inter_subset_left) hBD
    have hHi : InjOn (h ∘ G) B := by
      intro a ha b hb hab
      apply hGi ha.1 hb.1
      have := congrArg g hab
      simpa [c.gh (hBD ha), c.gh (hBD hb)] using this
    have hOpen := isOpen_image_of_injOn hBo hHc hHi
    set w₀ : ℂ := complexPlane.symm (f ⟨x, hxU⟩).1 with hw₀
    have hw₀M : w₀ ∈ M := by
      change complexPlane w₀ ∈ OpenUnitDisc
      rw [hw₀, LinearIsometryEquiv.apply_symm_apply]
      exact (f ⟨x, hxU⟩).2
    have hGw : G w₀ = x := by
      rw [hG w₀ hw₀M]
      have : (⟨complexPlane w₀, hw₀M⟩ : OpenUnitDisc) = f ⟨x, hxU⟩ := by
        apply Subtype.ext
        change complexPlane w₀ = _
        rw [hw₀, LinearIsometryEquiv.apply_symm_apply]
      rw [this, f.symm_apply_apply]
    have hw₀B : w₀ ∈ B := ⟨hw₀M, show G w₀ ∈ interior D from hGw ▸ hint⟩
    have hball : h x ∈ interior (closedBall (0 : ℂ) 1) := by
      refine mem_interior.mpr ⟨_, ?_, hOpen, ⟨w₀, hw₀B, by simp [hGw]⟩⟩
      rintro _ ⟨w, hw, rfl⟩
      exact c.hm (hBD hw)
    rw [interior_closedBall _ one_ne_zero] at hball
    have hsph : h x ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hx
    rw [mem_ball, mem_sphere.mp hsph] at hball
    exact lt_irrefl _ hball

theorem IsClosedDisc.subBd_eq_discBd (hS : IsClosedSurface S) {D : Set S} (hD : IsClosedDisc D) :
    subBd D = discBd D := by
  rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hD]

/-- A closed disc in a closed surface is the closure of its interior. -/
theorem IsClosedDisc.subset_closure_diff_frontier (hS : IsClosedSurface S) {D : Set S}
    (hD : IsClosedDisc D) : D ⊆ closure (D \ frontier D) := by
  have : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := (IsClosedSurface.isSurface hS).2.2
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  obtain ⟨u1, -⟩ := c.union_ball
  have hO := c.isOpen_image_ball hman
  have hsub : g '' ball 0 1 ⊆ D := fun x hx => u1 ▸ Or.inl hx
  have hin : g '' ball 0 1 ⊆ D \ frontier D := fun x hx =>
    ⟨hsub hx, fun hfr => hfr.2 (interior_maximal hsub hO hx)⟩
  intro y hy
  refine closure_mono hin ?_
  have hz := c.hm hy
  have hzc : h y ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact hz
  have hwithin : ContinuousWithinAt g (ball 0 1) (h y) :=
    (c.gc (h y) hz).mono ball_subset_closedBall
  have := hwithin.mem_closure_image hzc
  rwa [c.gh hy] at this

/-- For a closed disc `D` in a closed surface `S`, `D \ subBd D` is an open disc with closure `D`
and boundary `subBd D`. -/
theorem IsClosedDisc.isOpenDisc_diff_subBd (hS : IsClosedSurface S) {D : Set S}
    (hD : IsClosedDisc D) :
    IsOpenDisc (D \ subBd D) ∧ closure (D \ subBd D) = D ∧ subBd (D \ subBd D) = subBd D := by
  have : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := (IsClosedSurface.isSurface hS).2.2
  have hcl : IsClosed D := hD.isCompact.isClosed
  have hbd : subBd D = discBd D := IsClosedDisc.subBd_eq_discBd hS hD
  have hfr : frontier D = subBd D := (subBd_eq_frontier D).symm
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  obtain ⟨u1, d1⟩ := c.union_ball
  have hEq : D \ subBd D = g '' ball 0 1 := by
    rw [hbd]
    ext x
    constructor
    · rintro ⟨hxD, hxn⟩
      rw [← u1] at hxD
      rcases hxD with hx | hx
      · exact hx
      · exact absurd hx hxn
    · intro hx
      exact ⟨u1 ▸ Or.inl hx, disjoint_left.mp d1 hx⟩
  have hOpen : IsOpen (D \ subBd D) := by
    rw [hEq]
    exact c.isOpen_image_ball hman
  have hHomeo : Nonempty (OpenUnitDisc ≃ₜ (D \ subBd D : Set S)) := by
    -- `g ∘ complexPlane.symm` maps `OpenUnitDisc` onto `g '' ball 0 1 = D \ subBd D` with inverse
    -- `complexPlane ∘ h`.
    have hball : ∀ x : OpenUnitDisc, complexPlane.symm x.1 ∈ ball (0 : ℂ) 1 := by
      intro x
      have hx : ‖x.1‖ < 1 := by simpa [OpenUnitDisc] using x.2
      simpa [mem_ball_zero_iff] using hx
    have hmemD : ∀ x : OpenUnitDisc, g (complexPlane.symm x.1) ∈ D \ subBd D := by
      intro x
      rw [hEq]
      exact mem_image_of_mem g (hball x)
    have hinvM : ∀ y : (D \ subBd D : Set S), complexPlane (h y.1) ∈ OpenUnitDisc := by
      intro y
      have hy : y.1 ∈ g '' ball 0 1 := hEq ▸ y.2
      obtain ⟨z, hz, hzy⟩ := hy
      rw [← hzy, c.hg (ball_subset_closedBall hz)]
      have hzn : ‖complexPlane z‖ < 1 := by
        rw [LinearIsometryEquiv.norm_map]
        simpa [mem_ball_zero_iff] using hz
      simpa [OpenUnitDisc] using hzn
    refine ⟨{
      toFun := fun x => ⟨g (complexPlane.symm x.1), hmemD x⟩
      invFun := fun y => ⟨complexPlane (h y.1), hinvM y⟩
      left_inv := fun x => by
        apply Subtype.ext
        change complexPlane (h (g (complexPlane.symm x.1))) = x.1
        rw [c.hg (ball_subset_closedBall (hball x)), LinearIsometryEquiv.apply_symm_apply]
      right_inv := fun y => by
        apply Subtype.ext
        change g (complexPlane.symm (complexPlane (h y.1))) = y.1
        rw [LinearIsometryEquiv.symm_apply_apply, c.gh y.2.1]
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        have hc : ContinuousOn g (ball 0 1) := c.gc.mono ball_subset_closedBall
        exact hc.comp_continuous (complexPlane.symm.continuous.comp continuous_subtype_val) hball
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        refine complexPlane.continuous.comp ?_
        exact c.hc.comp_continuous continuous_subtype_val fun y => y.2.1
    }⟩
  have hclEq : closure (D \ subBd D) = D := by
    apply subset_antisymm (hcl.closure_subset_iff.mpr sdiff_subset)
    rw [← hfr]
    exact IsClosedDisc.subset_closure_diff_frontier hS hD
  have hsubBdEq : subBd (D \ subBd D) = subBd D := by
    have hsubD : subBd D ⊆ D := by
      rw [← hfr]
      exact hcl.frontier_subset
    rw [subBd_eq_frontier, frontier_eq_closure_inter_closure, hclEq,
      hOpen.isClosed_compl.closure_eq]
    ext x
    constructor
    · rintro ⟨hxD, hxnot⟩
      by_contra hnbd
      exact hxnot ⟨hxD, hnbd⟩
    · intro hxbd
      exact ⟨hsubD hxbd, fun h => h.2 hxbd⟩
  exact ⟨⟨hOpen, hHomeo⟩, hclEq, hsubBdEq⟩

/-- The interior of a closed disc in a closed surface is preconnected. -/
theorem IsClosedDisc.isPreconnected_diff_frontier (hS : IsClosedSurface S) {D : Set S}
    (hD : IsClosedDisc D) : IsPreconnected (D \ frontier D) := by
  obtain ⟨hOpenDisc, -, -⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hD
  obtain ⟨e⟩ := hOpenDisc.2
  have hc : IsPreconnected OpenUnitDisc := by
    have : OpenUnitDisc = ball (0 : EuclideanPlane) 1 := by
      ext x; simp [OpenUnitDisc]
    rw [this]
    exact (convex_ball (0 : EuclideanPlane) 1).isPreconnected
  have : PreconnectedSpace OpenUnitDisc := isPreconnected_iff_preconnectedSpace.mp hc
  have hEq : D \ frontier D = D \ subBd D := by rw [subBd_eq_frontier]
  rw [hEq]
  have himg : Subtype.val '' (range e) = D \ subBd D := by
    rw [e.surjective.range_eq]
    simp
    rfl
  rw [← himg, ← range_comp]
  rw [← image_univ]
  exact isPreconnected_univ.image _ (continuous_subtype_val.comp e.continuous).continuousOn

/-- A preconnected set disjoint from the frontier of a closed set `X` is either contained in `X`
or disjoint from `X`. -/
theorem subset_or_disjoint_of_frontier {X F : Set S} (hX : IsClosed X) (hF : IsPreconnected F)
    (hd : Disjoint F (frontier X)) : F ⊆ X ∨ Disjoint F X := by
  have hcov : F ⊆ interior X ∪ Xᶜ := by
    intro x hx
    by_cases hxX : x ∈ X
    · refine Or.inl ?_
      by_contra hxi
      exact disjoint_left.mp hd hx ⟨subset_closure hxX, hxi⟩
    · exact Or.inr hxX
  have hdisj : Disjoint (interior X) Xᶜ :=
    disjoint_left.mpr fun x hx hx' => hx' (interior_subset hx)
  by_cases hmeet : (F ∩ X).Nonempty
  · obtain ⟨x, hxF, hxX⟩ := hmeet
    have hxi : x ∈ interior X := by
      rcases hcov hxF with h | h
      · exact h
      · exact absurd hxX h
    exact Or.inl ((hF.subset_left_of_subset_union isOpen_interior hX.isOpen_compl hdisj hcov
      ⟨x, hxF, hxi⟩).trans interior_subset)
  · exact Or.inr (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet))

/-! ## 2. Two Lines with Common Ends and Circuits as `O`-Arcs -/

/-- Two different closed discs of a connected closed surface with the same boundary cover the
surface. -/
theorem cover_of_discBd_eq [ConnectedSpace S] (hS : IsClosedSurface S) {Δ₁ Δ₂ : Set S}
    (h₁ : IsClosedDisc Δ₁) (h₂ : IsClosedDisc Δ₂) (hb : discBd Δ₁ = discBd Δ₂) (hne : Δ₁ ≠ Δ₂) :
    Δ₁ ∪ Δ₂ = univ := by
  by_cases hsph : IsSphere S
  · obtain ⟨a, b, -, -, -, -, -, hcov, -, -, hall⟩ := sphere_disc S hsph _ h₁.isOArc_discBd
    rcases hall Δ₁ h₁ rfl with e₁ | e₁ <;> rcases hall Δ₂ h₂ hb.symm with e₂ | e₂
    · exact absurd (e₁.trans e₂.symm) hne
    · rw [e₁, e₂, hcov]
    · rw [e₁, e₂, union_comm, hcov]
    · exact absurd (e₁.trans e₂.symm) hne
  · exact absurd (eq_of_discBd_eq (IsClosedSurface.isSurface hS) hsph h₁ h₂ hb) hne

/-- The part of a line between its ends is connected. -/
theorem IsLineWithEnds.isPreconnected_sdiff_pair {L : Set S} {a b : S} (h : IsLineWithEnds L a b) :
    IsPreconnected (L \ {a, b}) := by
  obtain ⟨f, hf0, hf1⟩ := h
  have hEq : L \ {a, b} = (fun t => (f t).1) '' Ioo (0 : unitInterval) 1 := by
    ext x
    constructor
    · rintro ⟨hxL, hx⟩
      obtain ⟨t, ht⟩ := f.surjective ⟨x, hxL⟩
      have hx' : (f t).1 = x := by rw [ht]
      refine ⟨t, ⟨lt_of_le_of_ne unitInterval.nonneg' ?_, lt_of_le_of_ne unitInterval.le_one' ?_⟩,
        hx'⟩
      · rintro rfl
        exact hx (Or.inl (hx'.symm.trans hf0))
      · rintro rfl
        exact hx (Or.inr (hx'.symm.trans hf1))
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
      refine ⟨(f t).2, ?_⟩
      rintro (h' | h')
      · have := f.injective (Subtype.ext (h'.trans hf0.symm))
        exact h0.ne this.symm
      · have := f.injective (Subtype.ext (h'.trans hf1.symm))
        exact h1.ne this
  rw [hEq]
  exact isPreconnected_Ioo.image _ (by fun_prop)

/-- Let `A₀, A₁, A₂` be lines with common ends and otherwise disjoint, and let `Δ_i` be a closed
disc
with boundary the union of the other two lines. If `A_i ⊄ Δ_i` for each `i`, then `Δ₀ ∪ Δ₁` is a
closed disc distinct from `Δ₂` with the same boundary as `Δ₂`. -/
theorem theta_disc_union (hS : IsClosedSurface S) {A₀ A₁ A₂ Δ₀ Δ₁ Δ₂ : Set S} {a b : S}
    (l₀ : IsLineWithEnds A₀ a b) (l₁ : IsLineWithEnds A₁ a b) (l₂ : IsLineWithEnds A₂ a b)
    (i₀₁ : A₀ ∩ A₁ = {a, b}) (i₁₂ : A₁ ∩ A₂ = {a, b}) (i₂₀ : A₂ ∩ A₀ = {a, b})
    (d₀ : IsClosedDisc Δ₀) (d₁ : IsClosedDisc Δ₁) (d₂ : IsClosedDisc Δ₂)
    (f₀ : frontier Δ₀ = A₁ ∪ A₂) (f₁ : frontier Δ₁ = A₂ ∪ A₀) (f₂ : frontier Δ₂ = A₀ ∪ A₁)
    (h₀ : ¬ A₀ ⊆ Δ₀) (h₁ : ¬ A₁ ⊆ Δ₁) (h₂ : ¬ A₂ ⊆ Δ₂) :
    IsClosedDisc (Δ₀ ∪ Δ₁) ∧ discBd (Δ₀ ∪ Δ₁) = discBd Δ₂ ∧ Δ₀ ∪ Δ₁ ≠ Δ₂ := by
  have : T2Space S := hS.2.1
  have c₀ : IsClosed Δ₀ := d₀.isCompact.isClosed
  have c₁ : IsClosed Δ₁ := d₁.isCompact.isClosed
  have sub₀ : A₁ ∪ A₂ ⊆ Δ₀ := f₀ ▸ c₀.frontier_subset
  have sub₁ : A₂ ∪ A₀ ⊆ Δ₁ := f₁ ▸ d₁.isCompact.isClosed.frontier_subset
  have m₂ : ∀ x, x ∈ A₂ → x ∈ A₀ → x = a ∨ x = b := fun x h h' => by
    have : x ∈ A₂ ∩ A₀ := ⟨h, h'⟩
    rwa [i₂₀] at this
  have m₁ : ∀ x, x ∈ A₁ → x ∈ A₂ → x = a ∨ x = b := fun x h h' => by
    have : x ∈ A₁ ∩ A₂ := ⟨h, h'⟩
    rwa [i₁₂] at this
  have m₀ : ∀ x, x ∈ A₀ → x ∈ A₁ → x = a ∨ x = b := fun x h h' => by
    have : x ∈ A₀ ∩ A₁ := ⟨h, h'⟩
    rwa [i₀₁] at this
  have ha : a ∈ A₀ ∩ A₁ := by rw [i₀₁]; simp
  have hb : b ∈ A₀ ∩ A₁ := by rw [i₀₁]; simp
  have ha₂ : a ∈ A₁ ∩ A₂ := by rw [i₁₂]; simp
  have hb₂ : b ∈ A₁ ∩ A₂ := by rw [i₁₂]; simp
  have out₀ : Disjoint (A₀ \ {a, b}) Δ₀ := by
    have hdis : Disjoint (A₀ \ {a, b}) (frontier Δ₀) := by
      rw [f₀, disjoint_left]
      rintro x ⟨hx, hxn⟩ (h' | h')
      · exact hxn (m₀ x hx h')
      · exact hxn (m₂ x h' hx)
    refine (subset_or_disjoint_of_frontier c₀ (IsLineWithEnds.isPreconnected_sdiff_pair l₀)
      hdis).resolve_left ?_
    intro hsub
    refine h₀ fun x hx => ?_
    by_cases hxab : x ∈ ({a, b} : Set S)
    · rcases hxab with rfl | rfl
      · exact sub₀ (Or.inl ha.2)
      · exact sub₀ (Or.inl hb.2)
    · exact hsub ⟨hx, hxab⟩
  have out₁ : Disjoint (A₁ \ {a, b}) Δ₁ := by
    have hdis : Disjoint (A₁ \ {a, b}) (frontier Δ₁) := by
      rw [f₁, disjoint_left]
      rintro x ⟨hx, hxn⟩ (h' | h')
      · exact hxn (m₁ x hx h')
      · exact hxn (m₀ x h' hx)
    refine (subset_or_disjoint_of_frontier c₁ (IsLineWithEnds.isPreconnected_sdiff_pair l₁)
      hdis).resolve_left ?_
    intro hsub
    refine h₁ fun x hx => ?_
    by_cases hxab : x ∈ ({a, b} : Set S)
    · rcases hxab with rfl | rfl
      · exact sub₁ (Or.inl ha₂.2)
      · exact sub₁ (Or.inl hb₂.2)
    · exact hsub ⟨hx, hxab⟩
  have hint : Disjoint (Δ₁ \ frontier Δ₁) Δ₀ := by
    have hdis : Disjoint (Δ₁ \ frontier Δ₁) (frontier Δ₀) := by
      rw [f₀, disjoint_left]
      rintro x ⟨hxD, hxf⟩ (h' | h')
      · by_cases hxab : x ∈ ({a, b} : Set S)
        · apply hxf
          rw [f₁]
          rcases hxab with rfl | rfl
          · exact Or.inl ha₂.2
          · exact Or.inl hb₂.2
        · exact disjoint_left.mp out₁ ⟨h', hxab⟩ hxD
      · exact hxf (f₁ ▸ Or.inl h')
    refine (subset_or_disjoint_of_frontier c₀ (IsClosedDisc.isPreconnected_diff_frontier hS d₁)
      hdis).resolve_left ?_
    intro hsub
    refine h₀ fun x hx => ?_
    have hxD : x ∈ Δ₁ := sub₁ (Or.inr hx)
    exact c₀.closure_subset_iff.mpr hsub (IsClosedDisc.subset_closure_diff_frontier hS d₁ hxD)
  have hcap : Δ₀ ∩ Δ₁ = A₂ := by
    apply subset_antisymm
    · rintro x ⟨hx₀, hx₁⟩
      have hxf : x ∈ frontier Δ₁ := by
        by_contra hn
        exact disjoint_left.mp hint ⟨hx₁, hn⟩ hx₀
      rw [f₁] at hxf
      rcases hxf with h' | h'
      · exact h'
      · by_cases hxab : x ∈ ({a, b} : Set S)
        · rcases hxab with rfl | rfl
          · exact ha₂.2
          · exact hb₂.2
        · exact absurd hx₀ (disjoint_left.mp out₀ ⟨h', hxab⟩)
    · exact fun x hx => ⟨sub₀ (Or.inr hx), sub₁ (Or.inl hx)⟩
  have e₀ := IsClosedDisc.frontier_eq_discBd hS d₀
  have e₁ := IsClosedDisc.frontier_eq_discBd hS d₁
  have e₂ := IsClosedDisc.frontier_eq_discBd hS d₂
  obtain ⟨dU, hU⟩ := disc_union Δ₀ Δ₁ A₂ a b d₀ d₁ l₂ hcap
    (by rw [← e₀, f₀]; exact subset_union_right) (by rw [← e₁, f₁]; exact subset_union_left)
  have hbd : discBd (Δ₀ ∪ Δ₁) = discBd Δ₂ := by
    rw [hU, ← e₀, ← e₁, ← e₂, f₀, f₁, f₂]
    ext x
    constructor
    · rintro ⟨(h' | h') | h' | h', hn⟩
      · exact Or.inr h'
      · have hab : x ∈ ({a, b} : Set S) := by
          by_contra hab
          exact hn ⟨h', hab⟩
        rcases hab with rfl | rfl
        · exact Or.inr ha.2
        · exact Or.inr hb.2
      · have hab : x ∈ ({a, b} : Set S) := by
          by_contra hab
          exact hn ⟨h', hab⟩
        rcases hab with rfl | rfl
        · exact Or.inr ha.2
        · exact Or.inr hb.2
      · exact Or.inl h'
    · rintro (h' | h')
      · refine ⟨Or.inr (Or.inr h'), fun hx => hx.2 (m₂ x hx.1 h')⟩
      · refine ⟨Or.inl (Or.inl h'), fun hx => hx.2 (m₁ x h' hx.1)⟩
  have hne : Δ₀ ∪ Δ₁ ≠ Δ₂ := fun heq => h₂ fun x hx => heq ▸ Or.inl (sub₀ (Or.inr hx))
  exact ⟨dU, hbd, hne⟩

theorem theta_cover [ConnectedSpace S] (hS : IsClosedSurface S) {A₀ A₁ A₂ Δ₀ Δ₁ Δ₂ : Set S} {a b :
  S}
    (l₀ : IsLineWithEnds A₀ a b) (l₁ : IsLineWithEnds A₁ a b) (l₂ : IsLineWithEnds A₂ a b)
    (i₀₁ : A₀ ∩ A₁ = {a, b}) (i₁₂ : A₁ ∩ A₂ = {a, b}) (i₂₀ : A₂ ∩ A₀ = {a, b})
    (d₀ : IsClosedDisc Δ₀) (d₁ : IsClosedDisc Δ₁) (d₂ : IsClosedDisc Δ₂)
    (f₀ : frontier Δ₀ = A₁ ∪ A₂) (f₁ : frontier Δ₁ = A₂ ∪ A₀) (f₂ : frontier Δ₂ = A₀ ∪ A₁)
    (h₀ : ¬ A₀ ⊆ Δ₀) (h₁ : ¬ A₁ ⊆ Δ₁) (h₂ : ¬ A₂ ⊆ Δ₂) : Δ₀ ∪ Δ₁ ∪ Δ₂ = univ := by
  obtain ⟨dU, hbd, hne⟩ :=
    theta_disc_union hS l₀ l₁ l₂ i₀₁ i₁₂ i₂₀ d₀ d₁ d₂ f₀ f₁ f₂ h₀ h₁ h₂
  exact cover_of_discBd_eq hS dU d₂ hbd hne

section Paths

variable [T2Space S]

omit [T2Space S] in
theorem mem_V_of_mem_support {Γ : Drawing S} {a b : S} (W : GraphWalk Γ.toGraph a b) {x : S}
    (hx : x ∈ W.support) : x ∈ Γ.V := by
  induction W with
  | nil h =>
    rcases List.mem_singleton.mp hx with rfl
    exact h
  | @cons a y b e hl r ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hl.2.1
    · exact ih hx

omit [T2Space S] in
theorem mem_E_of_mem_edges {Γ : Drawing S} {a b : S} (W : GraphWalk Γ.toGraph a b) {f : Set S}
    (hf : f ∈ W.edges) : f ∈ Γ.E := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at hf
  | @cons a y b e hl r ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hl.1
    · exact ih hf

omit [T2Space S] in
/-- A vertex in the closure of an edge of a walk is on the walk. -/
theorem mem_support_of_mem_edges {Γ : Drawing S} {a b : S} (W : GraphWalk Γ.toGraph a b) {f : Set S}
    (hf : f ∈ W.edges) {x : S} (hxf : x ∈ closure f) (hxV : x ∈ Γ.V) : x ∈ W.support := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at hf
  | @cons a y b e hl r ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · have : x ∈ closure f ∩ Γ.V := ⟨hxf, hxV⟩
      rw [hl.2.2.2] at this
      rcases this with rfl | rfl
      · exact (GraphWalk.cons hl r).start_mem_support
      · exact List.mem_cons_of_mem _ r.start_mem_support
    · exact List.mem_cons_of_mem _ (ih hf)

/-- The union of the vertices and edges of a path with distinct ends is a line between them. -/
theorem walk_isLine (Γ : Drawing S) {a b : S} (W : GraphWalk Γ.toGraph a b) (hW : W.IsSimple)
    (hab : a ≠ b) : IsLineWithEnds ({x | x ∈ W.support} ∪ ⋃ e ∈ {e | e ∈ W.edges}, closure e) a b
      := by
  induction W with
  | nil _ => exact absurd rfl hab
  | @cons a y b e hl r ih =>
    have hnd : a ∉ r.support ∧ r.IsSimple := by
      have := List.nodup_cons.mp hW
      exact ⟨this.1, this.2⟩
    have hay : a ≠ y := fun h => hnd.1 (h ▸ r.start_mem_support)
    have hline : IsLineWithEnds (closure e) y a := by
      rcases Γ.edge_cond e hl.1 with ⟨u, v, -, hcap, hL⟩ | ⟨u, hcap, -⟩
      · have heq : ({u, v} : Set S) = {a, y} := hcap.symm.trans hl.2.2.2
        have hu : u ∈ ({a, y} : Set S) := heq ▸ mem_insert u _
        have hv : v ∈ ({a, y} : Set S) := heq ▸ mem_insert_of_mem u rfl
        have ha : a ∈ ({u, v} : Set S) := heq ▸ mem_insert a _
        have hy : y ∈ ({u, v} : Set S) := heq ▸ mem_insert_of_mem a rfl
        rcases hu with rfl | rfl
        · rcases hy with rfl | rfl
          · exact absurd rfl hay
          · exact GraphMinor.GM11.IsLineWithEnds.symm hL
        · rcases ha with rfl | rfl
          · exact absurd rfl hay
          · exact hL
      · exfalso
        have heq : ({u} : Set S) = {a, y} := hcap.symm.trans hl.2.2.2
        have h₁ : a ∈ ({u} : Set S) := heq ▸ mem_insert a _
        have h₂ : y ∈ ({u} : Set S) := heq ▸ mem_insert_of_mem a rfl
        exact hay (h₁.trans h₂.symm)
    have hae : a ∈ closure e := by
      have : a ∈ closure e ∩ Γ.V := by rw [hl.2.2.2]; exact mem_insert a _
      exact this.1
    have hye : y ∈ closure e := by
      have : y ∈ closure e ∩ Γ.V := by rw [hl.2.2.2]; exact mem_insert_of_mem a rfl
      exact this.1
    have hcons : ({x | x ∈ (GraphWalk.cons hl r).support} ∪
        ⋃ f ∈ {f | f ∈ (GraphWalk.cons hl r).edges}, closure f) =
        closure e ∪ ({x | x ∈ r.support} ∪ ⋃ f ∈ {f | f ∈ r.edges}, closure f) := by
      ext x
      constructor
      · rintro (hx | hx)
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inl hae
          · exact Or.inr (Or.inl hx)
        · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
          rcases List.mem_cons.mp hf with rfl | hf
          · exact Or.inl hxf
          · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨f, hf, hxf⟩))
      · rintro (hx | hx | hx)
        · exact Or.inr (mem_iUnion₂.mpr ⟨e, List.mem_cons_self .., hx⟩)
        · exact Or.inl (List.mem_cons_of_mem _ hx)
        · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
          exact Or.inr (mem_iUnion₂.mpr ⟨f, List.mem_cons_of_mem _ hf, hxf⟩)
    rw [hcons]
    have hcap : closure e ∩ ({x | x ∈ r.support} ∪ ⋃ f ∈ {f | f ∈ r.edges}, closure f) = {y} := by
      apply subset_antisymm
      · rintro x ⟨hxe, hx⟩
        have hV : x ∈ Γ.V → x = y := fun hxV => by
          have h₁ : x ∈ closure e ∩ Γ.V := ⟨hxe, hxV⟩
          rw [hl.2.2.2] at h₁
          rcases h₁ with rfl | h₁
          · exfalso
            rcases hx with hx | hx
            · exact hnd.1 hx
            · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
              exact hnd.1 (mem_support_of_mem_edges r hf hxf hxV)
          · exact h₁
        by_cases hxV : x ∈ Γ.V
        · exact hV hxV
        · exfalso
          rcases hx with hx | hx
          · exact hxV (mem_V_of_mem_support r hx)
          · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
            have hfE : f ∈ Γ.E := mem_E_of_mem_edges r hf
            have h₁ : x ∈ e := by
              rw [← Γ.closure_diff_V hl.1]
              exact ⟨hxe, hxV⟩
            have h₂ : x ∈ f := by
              rw [← Γ.closure_diff_V hfE]
              exact ⟨hxf, hxV⟩
            have := Γ.edge_eq_of_mem hl.1 hfE h₁ h₂
            subst this
            exact hnd.1 (mem_support_of_mem_edges r hf hae hl.2.1)
      · rintro x rfl
        exact ⟨hye, Or.inl r.start_mem_support⟩
    by_cases hyb : y = b
    · subst hyb
      cases r with
      | nil h =>
        have : closure e ∪ ({x | x ∈ (GraphWalk.nil h).support} ∪
            ⋃ f ∈ {f | f ∈ (GraphWalk.nil h : GraphWalk Γ.toGraph y y).edges}, closure f) =
            closure e := by
          refine union_eq_left.mpr (union_subset ?_ ?_)
          · intro x hx
            rcases List.mem_singleton.mp hx with rfl
            exact hye
          · intro x hx
            obtain ⟨f, hf, -⟩ := mem_iUnion₂.mp hx
            exact absurd hf (List.not_mem_nil)
        rw [this]
        exact GraphMinor.GM11.IsLineWithEnds.symm hline
      | cons h r' =>
        exfalso
        have := (List.nodup_cons.mp hnd.2).1
        exact this r'.end_mem_support
    · exact IsLineWithEnds.union hline (ih hnd.2 hyb) hcap

omit [T2Space S] in
/-- A path of positive length has distinct ends. -/
theorem ne_of_isPathBetween {P : Drawing S} {a b : S} (hP : P.IsPathBetween a b)
    (hl : 0 < P.length) : a ≠ b := by
  rintro rfl
  obtain ⟨W, hW, -, hE⟩ := hP
  cases W with
  | nil _ =>
    rw [Drawing.length, hE] at hl
    simp [GraphWalk.edges] at hl
  | cons h r =>
    exact (List.nodup_cons.mp hW).1 r.end_mem_support

/-- A path of positive length is a line between its ends. -/
theorem isLine_of_isPathBetween {P : Drawing S} {a b : S} (hP : P.IsPathBetween a b)
    (hab : a ≠ b) : IsLineWithEnds P.U a b := by
  obtain ⟨W, hW, hV, hE⟩ := hP
  have := walk_isLine P W hW hab
  rwa [← hV, ← hE, ← Drawing.U_eq] at this

omit [T2Space S] in
/-- Two subdrawings of a drawing without common edges meet only in common vertices. -/
theorem U_inter_of_disjoint {Γ C D : Drawing S} (hC : C.IsSubdrawing Γ) (hD : D.IsSubdrawing Γ)
    (hE : Disjoint C.E D.E) : C.U ∩ D.U = C.V ∩ D.V := by
  apply subset_antisymm
  · rintro x ⟨hxC, hxD⟩
    have key : ∀ {C D : Drawing S}, C.IsSubdrawing Γ → D.IsSubdrawing Γ → x ∈ C.U → x ∈ D.U →
        x ∉ C.V → ∃ f ∈ C.E, x ∈ f ∧ x ∉ D.V := by
      intro C D hC hD hxC hxD hn
      obtain ⟨f, hf, hxf⟩ := C.exists_edge_of_mem hxC hn
      exact ⟨f, hf, hxf, fun h => ((hC.2 hf).2.1 hxf).2 (hD.1 h)⟩
    by_cases h₁ : x ∈ C.V
    · by_cases h₂ : x ∈ D.V
      · exact ⟨h₁, h₂⟩
      · obtain ⟨g, hg, hxg, -⟩ := key hD hC hxD hxC h₂
        exact absurd (hC.1 h₁) ((hD.2 hg).2.1 hxg).2
    · obtain ⟨f, hf, hxf, hn⟩ := key hC hD hxC hxD h₁
      obtain ⟨g, hg, hxg⟩ := D.exists_edge_of_mem hxD hn
      have := Γ.edge_eq_of_mem (hC.2 hf) (hD.2 hg) hxf hxg
      exact absurd (this ▸ hg) (disjoint_left.mp hE hf)
  · exact fun x hx => ⟨C.V_subset_U hx.1, D.V_subset_U hx.2⟩

/-- Two lines with the same two ends and nothing else in common form an `O`-arc. -/
theorem isOArc_union {L₁ L₂ : Set S} {a b : S} (h₁ : IsLineWithEnds L₁ a b)
    (h₂ : IsLineWithEnds L₂ a b) (hcap : L₁ ∩ L₂ ⊆ {a, b}) : IsOArc (L₁ ∪ L₂) := by
  obtain ⟨f₁, a₁, b₁⟩ := h₁
  obtain ⟨f₂, a₂, b₂⟩ := h₂
  let I := unitInterval
  let up : I → I := fun t => Set.projIcc 0 1 zero_le_one (2 * t.1)
  let dn : I → I := fun t => Set.projIcc 0 1 zero_le_one (2 - 2 * t.1)
  let γ : I → S := fun t => if t.1 ≤ 1 / 2 then (f₁ (up t)).1 else (f₂ (dn t)).1
  have hup : ∀ t : I, t.1 ≤ 1 / 2 → (up t).1 = 2 * t.1 := fun t ht => by
    simp only [up]
    rw [Set.projIcc_of_mem zero_le_one ⟨by have := t.2.1; positivity, by linarith⟩]
  have hdn : ∀ t : I, 1 / 2 ≤ t.1 → (dn t).1 = 2 - 2 * t.1 := fun t ht => by
    simp only [dn]
    rw [Set.projIcc_of_mem zero_le_one ⟨by have := t.2.2; linarith, by linarith⟩]
  have hγ : Continuous γ := by
    refine Continuous.if_le ?_ ?_ continuous_subtype_val continuous_const ?_
    · exact continuous_subtype_val.comp (f₁.continuous.comp (by fun_prop))
    · exact continuous_subtype_val.comp (f₂.continuous.comp (by fun_prop))
    · intro t ht
      have e₁ : up t = 1 := Subtype.ext (by rw [hup t ht.le]; rw [ht]; norm_num)
      have e₂ : dn t = 1 := Subtype.ext (by rw [hdn t ht.ge]; rw [ht]; norm_num)
      rw [e₁, e₂, b₁, b₂]
  have hγ₀ : ∀ t : I, t.1 ≤ 1 / 2 → γ t = (f₁ (up t)).1 := fun t ht => by simp only [γ, ht,
    ite_true]
  have hγ₁ : ∀ t : I, ¬ t.1 ≤ 1 / 2 → γ t = (f₂ (dn t)).1 := fun t ht => by
    simp only [γ, ht, ite_false]
  have hup0 : ∀ t : I, t.1 ≤ 1 / 2 → up t = 0 → t = 0 := fun t ht h => by
    have := congrArg Subtype.val h
    rw [hup t ht] at this
    exact Subtype.ext (by simpa using this)
  have hup1 : ∀ t : I, t.1 ≤ 1 / 2 → up t = 1 → t.1 = 1 / 2 := fun t ht h => by
    have := congrArg Subtype.val h
    rw [hup t ht] at this
    have h' : 2 * t.1 = 1 := this
    linarith
  have hdn0 : ∀ t : I, ¬ t.1 ≤ 1 / 2 → dn t = 0 → t = 1 := fun t ht h => by
    have := congrArg Subtype.val h
    rw [hdn t (le_of_not_ge ht)] at this
    have h' : 2 - 2 * t.1 = 0 := this
    exact Subtype.ext (by change t.1 = 1; linarith)
  have hdn1 : ∀ t : I, ¬ t.1 ≤ 1 / 2 → dn t ≠ 1 := fun t ht h => by
    have := congrArg Subtype.val h
    rw [hdn t (le_of_not_ge ht)] at this
    have h' : 2 - 2 * t.1 = 1 := this
    exact ht (by linarith)
  have cross : ∀ s t : I, s.1 ≤ 1 / 2 → ¬ t.1 ≤ 1 / 2 → γ s = γ t → s = 0 ∧ t = 1 := by
    intro s t hs ht h
    rw [hγ₀ s hs, hγ₁ t ht] at h
    have hmem : (f₁ (up s)).1 ∈ L₁ ∩ L₂ := ⟨(f₁ _).2, h ▸ (f₂ _).2⟩
    rcases hcap hmem with h' | h'
    · have e₁ : up s = 0 := f₁.injective (Subtype.ext (h'.trans a₁.symm))
      have e₂ : dn t = 0 := f₂.injective (Subtype.ext ((h.symm.trans h').trans a₂.symm))
      exact ⟨hup0 s hs e₁, hdn0 t ht e₂⟩
    · have e₂ : dn t = 1 := f₂.injective (Subtype.ext ((h.symm.trans h').trans b₂.symm))
      exact absurd e₂ (hdn1 t ht)
  have hinj : ∀ s t : I, γ s = γ t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    intro s t h
    by_cases hs : s.1 ≤ 1 / 2 <;> by_cases ht : t.1 ≤ 1 / 2
    · rw [hγ₀ s hs, hγ₀ t ht] at h
      have e : up s = up t := f₁.injective (Subtype.ext h)
      have := congrArg Subtype.val e
      rw [hup s hs, hup t ht] at this
      exact Or.inl (Subtype.ext (by linarith))
    · exact Or.inr (Or.inl (cross s t hs ht h))
    · obtain ⟨e₁, e₂⟩ := cross t s ht hs h.symm
      exact Or.inr (Or.inr ⟨e₂, e₁⟩)
    · rw [hγ₁ s hs, hγ₁ t ht] at h
      have e : dn s = dn t := f₂.injective (Subtype.ext h)
      have := congrArg Subtype.val e
      rw [hdn s (le_of_not_ge hs), hdn t (le_of_not_ge ht)] at this
      exact Or.inl (Subtype.ext (by linarith))
  have hγ01 : γ 0 = γ 1 := by
    have e₀ : up 0 = 0 := Subtype.ext (by rw [hup 0 (by norm_num)]; simp)
    have e₁ : dn 1 = 0 := Subtype.ext (by rw [hdn 1 (by norm_num)]; norm_num)
    rw [hγ₀ 0 (by norm_num), hγ₁ 1 (by norm_num), e₀, e₁, a₁, a₂]
  let q : I → Circle := arcParam 1
  have hq : Continuous q := (arcParam 1).continuous
  have hqs : Function.Surjective q := arcParam_surjective 1
  have hqq : Topology.IsQuotientMap q := hq.isClosedMap.isQuotientMap hq hqs
  let G : Circle → S := fun z => γ (Function.surjInv hqs z)
  have hGq : G ∘ q = γ := by
    funext t
    have hsi : q (Function.surjInv hqs (q t)) = q t := Function.surjInv_eq hqs _
    change γ (Function.surjInv hqs (q t)) = γ t
    rcases arcParam_eq_iff 1 hsi with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h]
    · rw [h₁, h₂, hγ01]
    · rw [h₁, h₂, hγ01]
  have hG : Continuous G := hqq.continuous_iff.mpr (hGq ▸ hγ)
  have hGi : Function.Injective G := by
    intro z w h
    rw [← Function.surjInv_eq hqs z, ← Function.surjInv_eq hqs w]
    rcases hinj _ _ h with h' | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h']
    · rw [h₁, h₂]
      change arcParam 1 0 = arcParam 1 1
      simp
    · rw [h₁, h₂]
      change arcParam 1 1 = arcParam 1 0
      simp
  have hrange : range G = L₁ ∪ L₂ := by
    have hγr : range γ = L₁ ∪ L₂ := by
      apply subset_antisymm
      · rintro _ ⟨t, rfl⟩
        by_cases ht : t.1 ≤ 1 / 2
        · rw [hγ₀ t ht]
          exact Or.inl (f₁ _).2
        · rw [hγ₁ t ht]
          exact Or.inr (f₂ _).2
      · rintro x (hx | hx)
        · obtain ⟨u, hu⟩ := f₁.surjective ⟨x, hx⟩
          let t : I := ⟨u.1 / 2, by have := u.2.1; positivity, by have := u.2.2; linarith⟩
          have ht : t.1 ≤ 1 / 2 := by
            change u.1 / 2 ≤ 1 / 2
            have := u.2.2
            linarith
          have e : up t = u := Subtype.ext (by
            rw [hup t ht]
            change 2 * (u.1 / 2) = u.1
            ring)
          exact ⟨t, by rw [hγ₀ t ht, e, hu]⟩
        · obtain ⟨u, hu⟩ := f₂.surjective ⟨x, hx⟩
          by_cases hu1 : u = 1
          · subst hu1
            have hxb : x = b := by
              have := congrArg Subtype.val hu
              exact this.symm.trans b₂
            let t : I := ⟨1 / 2, by norm_num, by norm_num⟩
            have ht : t.1 ≤ 1 / 2 := le_rfl
            have e : up t = 1 := Subtype.ext (by
              rw [hup t ht]
              change (2 : ℝ) * (1 / 2) = 1
              norm_num)
            exact ⟨t, by rw [hγ₀ t ht, e, b₁, hxb]⟩
          · have hu' : u.1 < 1 := lt_of_le_of_ne u.2.2 fun h => hu1 (Subtype.ext h)
            let t : I := ⟨1 - u.1 / 2, by have := u.2.2; linarith, by have := u.2.1; linarith⟩
            have ht : ¬ t.1 ≤ 1 / 2 := by
              change ¬ 1 - u.1 / 2 ≤ 1 / 2
              linarith
            have e : dn t = u := Subtype.ext (by
              rw [hdn t (le_of_not_ge ht)]
              change 2 - 2 * (1 - u.1 / 2) = u.1
              ring)
            exact ⟨t, by rw [hγ₁ t ht, e, hu]⟩
    rw [← hγr, ← hGq, range_comp, hqs.range_eq, image_univ]
  have hemb := hG.isClosedEmbedding hGi
  rw [← hrange]
  exact ⟨hemb.isEmbedding.toHomeomorph⟩

/-- The point set `U(C)` of any circuit `C` in a Hausdorff space is an `O`-arc. -/
theorem isOArc_of_isCircuit {C : Drawing S} (hC : C.IsCircuit) : IsOArc C.U := by
  obtain ⟨e, he⟩ := IsCircuit.E_nonempty hC
  rcases C.edge_cond e he with ⟨a, b, hab, hcap, hL⟩ | ⟨u, hcap, hO⟩
  · have ha : a ∈ C.V := by
      have : a ∈ closure e ∩ C.V := by rw [hcap]; simp
      exact this.2
    have hb : b ∈ C.V := by
      have : b ∈ closure e ∩ C.V := by rw [hcap]; simp
      exact this.2
    obtain ⟨P, Q, hP, hQ, hPs, hQs, -, -, hV, hE, hsup⟩ := hC.exists_two_paths ha hb hab
    have hU : C.U = P.U ∪ Q.U := by
      rw [← hsup, Drawing.U_eq, Drawing.sup_V hPs hQs, Drawing.sup_E hPs hQs, P.U_eq, Q.U_eq,
        biUnion_union]
      ext x
      simp only [mem_union]
      tauto
    rw [hU]
    exact isOArc_union (isLine_of_isPathBetween hP hab) (isLine_of_isPathBetween hQ hab)
      (by rw [U_inter_of_disjoint hPs hQs hE, hV])
  · have hE : C.E = {e} := IsCircuit.E_eq_of_loop hC he hcap
    have hU : C.U = closure e := by
      rw [C.U_eq, hE]
      refine subset_antisymm (union_subset ?_ (iUnion₂_subset fun f hf => ?_))
        (subset_union_of_subset_right (subset_biUnion_of_mem (mem_singleton e)) _)
      · intro v hv
        obtain ⟨W, -, hpos, -, -⟩ := exists_walk_at hC hv
        cases W with
        | nil _ => simp at hpos
        | @cons _ w _ f h r =>
          have hfe : f = e := mem_singleton_iff.mp (hE ▸ h.1)
          have : v ∈ closure f ∩ C.V := by rw [h.2.2.2]; simp
          exact hfe ▸ this.1
      · rw [mem_singleton_iff.mp hf]
    rwa [hU]

end Paths

/-! ## 3. Derived Slope of a Pretangle -/

section Tangle

variable [T1Space S] {Γ : PaintingOrDrawing S} {Γ' : Drawing S} {θ : ℕ}
  {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}

omit [T1Space S] in
theorem PaintingOrDrawing.toHypergraph_inc {Γ : PaintingOrDrawing S} {e : Set S} {v : S} :
    Γ.toHypergraph.Inc e v ↔ e ∈ Γ.E ∧ v ∈ Γ.V ∧ v ∈ closure e := by
  cases Γ <;> rfl

omit [T1Space S] in
theorem PaintingOrDrawing.edge_props {Γ : PaintingOrDrawing S} {e : Set S} (he : e ∈ Γ.E) :
    IsPreconnected e ∧ Disjoint e Γ.V ∧ e ⊆ Γ.U ∧ e.Nonempty := by
  cases Γ with
  | painting Γ =>
    exact ⟨he.2.2.1.isConnected.isPreconnected, disjoint_left.mpr fun x hx => (he.2.1 hx).2,
      fun x hx => (he.2.1 hx).1, he.1⟩
  | drawing Γ =>
    exact ⟨he.2.2.1.isConnected.isPreconnected, disjoint_left.mpr fun x hx => (he.2.1 hx).2,
      fun x hx => (he.2.1 hx).1, he.1⟩

omit [T1Space S] in
theorem edge_subset_or_disjoint_of_radial (hrad : Γ.U ∩ Γ'.U = Γ.V) {Δ : Set S} (hΔ : IsClosed Δ)
    (hb : frontier Δ ⊆ Γ'.U) {e : Set S} (he : e ∈ Γ.E) : e ⊆ Δ ∨ Disjoint e Δ := by
  obtain ⟨hp, hd, hU, -⟩ := PaintingOrDrawing.edge_props he
  refine subset_or_disjoint_of_frontier hΔ hp (disjoint_left.mpr fun x hx hf => ?_)
  have : x ∈ Γ.U ∩ Γ'.U := ⟨hU hx, hb hf⟩
  rw [hrad] at this
  exact disjoint_left.mp hd hx this

omit [T1Space S] in
theorem not_cover (hT : IsPretangle Γ.toHypergraph θ T) (hrad : Γ.U ∩ Γ'.U = Γ.V)
    {Δ₁ Δ₂ Δ₃ : Set S} (c₁ : IsClosed Δ₁) (c₂ : IsClosed Δ₂) (c₃ : IsClosed Δ₃)
    (b₁ : frontier Δ₁ ⊆ Γ'.U) (b₂ : frontier Δ₂ ⊆ Γ'.U) (b₃ : frontier Δ₃ ⊆ Γ'.U)
    (m₁ : (Γ.inter Δ₁, Γ.interOutside Δ₁) ∈ T) (m₂ : (Γ.inter Δ₂, Γ.interOutside Δ₂) ∈ T)
    (m₃ : (Γ.inter Δ₃, Γ.interOutside Δ₃) ∈ T) (hcov : Δ₁ ∪ Δ₂ ∪ Δ₃ = univ) : False := by
  have hedge : ∀ e ∈ Γ.E, e ⊆ Δ₁ ∨ e ⊆ Δ₂ ∨ e ⊆ Δ₃ := by
    intro e he
    obtain ⟨x, hx⟩ := (PaintingOrDrawing.edge_props he).2.2.2
    have hxc : x ∈ Δ₁ ∪ Δ₂ ∪ Δ₃ := hcov ▸ mem_univ x
    have side : ∀ {Δ : Set S}, IsClosed Δ → frontier Δ ⊆ Γ'.U → x ∈ Δ → e ⊆ Δ := fun c b h =>
      (edge_subset_or_disjoint_of_radial hrad c b he).resolve_right
        fun hd => disjoint_left.mp hd hx h
    rcases hxc with (h | h) | h
    · exact Or.inl (side c₁ b₁ h)
    · exact Or.inr (Or.inl (side c₂ b₂ h))
    · exact Or.inr (Or.inr (side c₃ b₃ h))
  refine hT.axiom2 m₁ m₂ m₃ (Hypergraph.ext ?_ ?_ ?_)
  · ext v
    simp only [PaintingOrDrawing.toHypergraph_vertexSet]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hv
      have hvc : v ∈ Δ₁ ∪ Δ₂ ∪ Δ₃ := hcov ▸ mem_univ v
      rcases hvc with (h | h) | h
      · exact Or.inl (Or.inl ⟨hv, h⟩)
      · exact Or.inl (Or.inr ⟨hv, h⟩)
      · exact Or.inr ⟨hv, h⟩
  · ext e
    simp only [PaintingOrDrawing.toHypergraph_edgeSet]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro he
      rcases hedge e he with h | h | h
      · exact Or.inl (Or.inl ⟨he, h⟩)
      · exact Or.inl (Or.inr ⟨he, h⟩)
      · exact Or.inr ⟨he, h⟩
  · funext e v
    apply propext
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hi
      have hcl : ∀ {Δ : Set S}, IsClosed Δ → e ⊆ Δ → v ∈ Δ := fun c h =>
        c.closure_subset_iff.mpr h (PaintingOrDrawing.toHypergraph_inc.mp hi).2.2
      rcases hedge e (PaintingOrDrawing.toHypergraph_inc.mp hi).1 with h | h | h
      · exact Or.inl (Or.inl ⟨hi, h, hcl c₁ h⟩)
      · exact Or.inl (Or.inr ⟨hi, h, hcl c₂ h⟩)
      · exact Or.inr ⟨hi, h, hcl c₃ h⟩

/-- The derived slope of a respectful pretangle is a slope (Graph Minors XI, (6.6)). -/
theorem isSlope_of_derived [ConnectedSpace S] (hS : IsClosedSurface S)
    (hT : IsPretangle Γ.toHypergraph θ T) (hrad : Γ.U ∩ Γ'.U = Γ.V)
    (hd : IsDerivedSlope Γ Γ' θ T ins) : IsSlope Γ' (2 * θ) ins := by
  have : T2Space S := hS.2.1
  have hfr : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ →
      IsClosedDisc (ins C) ∧ frontier (ins C) = C.U ∧ IsClosed (ins C) ∧
      frontier (ins C) ⊆ Γ'.U ∧ (Γ.inter (ins C), Γ.interOutside (ins C)) ∈ T := by
    intro C h s l
    obtain ⟨d, b, m⟩ := hd C h s l
    rw [subBd_eq_frontier] at b
    exact ⟨d, b, d.isCompact.isClosed, b ▸ s.U_subset, m⟩
  have hmono : ∀ C₁ C₂ : Drawing S, C₁.IsCircuit → C₁.IsSubdrawing Γ' → C₁.length < 2 * θ →
      C₂.IsCircuit → C₂.IsSubdrawing Γ' → C₂.length < 2 * θ → C₁.U ⊆ ins C₂ →
      ins C₁ ⊆ ins C₂ := by
    intro C₁ C₂ h₁ s₁ l₁ h₂ s₂ l₂ hsub
    obtain ⟨d₁, f₁, c₁, b₁, m₁⟩ := hfr C₁ h₁ s₁ l₁
    obtain ⟨d₂, f₂, c₂, b₂, m₂⟩ := hfr C₂ h₂ s₂ l₂
    obtain ⟨Δ, ⟨hΔD, dΔ, bΔ, -⟩, -⟩ := disc_oArc (ins C₂) (discBd (ins C₁)) d₂
      (by rw [← IsClosedDisc.frontier_eq_discBd hS d₁, f₁]; exact hsub) (d₁.isOArc_discBd)
    by_cases heq : ins C₁ = Δ
    · exact heq ▸ hΔD
    · exfalso
      have hcov := cover_of_discBd_eq hS d₁ dΔ bΔ.symm heq
      refine not_cover hT hrad c₁ c₂ c₂ b₁ b₂ b₂ m₁ m₂ m₂ (eq_univ_of_univ_subset ?_)
      rw [← hcov]
      exact fun x hx => hx.elim (fun h => Or.inl (Or.inl h)) fun h => Or.inr (hΔD h)
  refine ⟨by have := hT.one_le; omega, fun C h s l => (hd C h s l).1,
    fun C h s l => (hd C h s l).2.1, hmono, ?_⟩
  intro P₀ P₁ P₂ a b hP₀ hP₁ hP₂ s₀ s₁ s₂ p₀ p₁ p₂ v₀₁ v₁₂ v₂₀ e₀₁ e₁₂ e₂₀ l₀ l₁ l₂
  have hab := ne_of_isPathBetween hP₀ p₀
  have supU : ∀ {P Q : Drawing S}, P.IsSubdrawing Γ' → Q.IsSubdrawing Γ' →
      (Γ'.sup P Q).U = P.U ∪ Q.U := by
    intro P Q hP hQ
    rw [Drawing.U_eq, Drawing.sup_V hP hQ, Drawing.sup_E hP hQ, P.U_eq, Q.U_eq, biUnion_union]
    ext x
    simp only [mem_union]
    tauto
  have circ : ∀ {P Q : Drawing S}, P.IsPathBetween a b → Q.IsPathBetween a b →
      P.IsSubdrawing Γ' → Q.IsSubdrawing Γ' → P.V ∩ Q.V = {a, b} → Disjoint P.E Q.E →
      (Γ'.sup P Q).IsCircuit ∧ (Γ'.sup P Q).IsSubdrawing Γ' := fun hP hQ sP sQ v e =>
    ⟨Drawing.isCircuit_sup hP hQ sP sQ hab v e, Drawing.sup_isSubdrawing Γ' _ _⟩
  obtain ⟨c₀, ss₀⟩ := circ hP₁ hP₂ s₁ s₂ v₁₂ e₁₂
  obtain ⟨c₁, ss₁⟩ := circ hP₂ hP₀ s₂ s₀ v₂₀ e₂₀
  obtain ⟨c₂, ss₂⟩ := circ hP₀ hP₁ s₀ s₁ v₀₁ e₀₁
  obtain ⟨d₀, f₀, cl₀, b₀, m₀⟩ := hfr _ c₀ ss₀ l₀
  obtain ⟨d₁, f₁, cl₁, b₁, m₁⟩ := hfr _ c₁ ss₁ l₁
  obtain ⟨d₂, f₂, cl₂, b₂, m₂⟩ := hfr _ c₂ ss₂ l₂
  rw [supU s₁ s₂] at f₀
  rw [supU s₂ s₀] at f₁
  rw [supU s₀ s₁] at f₂
  have sub : ∀ {Δ F : Set S}, IsClosed Δ → frontier Δ = F → F ⊆ Δ := fun c h
    => h ▸ c.frontier_subset
  have sb₀ := sub cl₀ f₀
  have sb₁ := sub cl₁ f₁
  have sb₂ := sub cl₂ f₂
  by_cases h₀ : P₀.U ⊆ ins (Γ'.sup P₁ P₂)
  · refine Or.inl ⟨hmono _ _ c₁ ss₁ l₁ c₀ ss₀ l₀ ?_, hmono _ _ c₂ ss₂ l₂ c₀ ss₀ l₀ ?_⟩
    · rw [supU s₂ s₀]
      exact union_subset (subset_union_right.trans sb₀) h₀
    · rw [supU s₀ s₁]
      exact union_subset h₀ (subset_union_left.trans sb₀)
  by_cases h₁ : P₁.U ⊆ ins (Γ'.sup P₂ P₀)
  · refine Or.inr (Or.inl ⟨hmono _ _ c₀ ss₀ l₀ c₁ ss₁ l₁ ?_, hmono _ _ c₂ ss₂ l₂ c₁ ss₁ l₁ ?_⟩)
    · rw [supU s₁ s₂]
      exact union_subset h₁ (subset_union_left.trans sb₁)
    · rw [supU s₀ s₁]
      exact union_subset (subset_union_right.trans sb₁) h₁
  by_cases h₂ : P₂.U ⊆ ins (Γ'.sup P₀ P₁)
  · refine Or.inr (Or.inr ⟨hmono _ _ c₀ ss₀ l₀ c₂ ss₂ l₂ ?_, hmono _ _ c₁ ss₁ l₁ c₂ ss₂ l₂ ?_⟩)
    · rw [supU s₁ s₂]
      exact union_subset (subset_union_right.trans sb₂) h₂
    · rw [supU s₂ s₀]
      exact union_subset h₂ (subset_union_left.trans sb₂)
  exfalso
  have hcov := theta_cover hS (isLine_of_isPathBetween hP₀ hab) (isLine_of_isPathBetween hP₁ hab)
    (isLine_of_isPathBetween hP₂ hab) (by rw [U_inter_of_disjoint s₀ s₁ e₀₁, v₀₁])
    (by rw [U_inter_of_disjoint s₁ s₂ e₁₂, v₁₂]) (by rw [U_inter_of_disjoint s₂ s₀ e₂₀, v₂₀])
    d₀ d₁ d₂ f₀ f₁ f₂ h₀ h₁ h₂
  exact not_cover hT hrad cl₀ cl₁ cl₂ b₀ b₁ b₂ m₀ m₁ m₂ hcov

end Tangle

/-! ## 4. Slope of a Drawing in a Closed Disc -/

/-- For a closed disc `Δ` and a drawing `C`, `discIns Δ C` is the unique closed disc in `Δ` bounded
by `U(C)` when `Δ` is a closed disc and `U(C) ⊆ Δ` is an `O`-arc, and `∅` otherwise. -/
noncomputable def discIns (Δ : Set S) (C : Drawing S) : Set S :=
  open Classical in
  if h : IsClosedDisc Δ ∧ C.U ⊆ Δ ∧ IsOArc C.U then
    (disc_oArc Δ C.U h.1 h.2.1 h.2.2).choose
  else ∅

theorem discIns_spec [T2Space S] {Δ : Set S} (hΔ : IsClosedDisc Δ) {C : Drawing S}
    (hC : C.IsCircuit) (hCU : C.U ⊆ Δ) :
    (discIns Δ C ⊆ Δ ∧ IsClosedDisc (discIns Δ C) ∧ discBd (discIns Δ C) = C.U) ∧
      ∀ Δ' : Set S, Δ' ⊆ Δ → IsClosedDisc Δ' → discBd Δ' = C.U → Δ' = discIns Δ C := by
  have hO : IsOArc C.U := isOArc_of_isCircuit hC
  have hdisc : discIns Δ C = (disc_oArc Δ C.U hΔ hCU hO).choose := by
    simp only [discIns, hΔ, hCU, hO, and_self, dite_true]
  rw [hdisc]
  obtain ⟨⟨h1, h2, h3, -⟩, huniq⟩ := (disc_oArc Δ C.U hΔ hCU hO).choose_spec
  exact ⟨⟨h1, h2, h3⟩, huniq⟩

/-- Any drawing `Γ'` with `U(Γ') ⊆ Δ` inside a closed disc `Δ` in a closed surface `S` has
`discIns Δ` as a slope of any order `k ≥ 2`. -/
theorem isSlope_discIns [T2Space S] (hS : IsClosedSurface S) {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {Γ' : Drawing S} (hU : Γ'.U ⊆ Δ) {k : ℕ} (hk : 2 ≤ k) :
    IsSlope Γ' k (discIns Δ) := by
  have hspec : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' →
      discIns Δ C ⊆ Δ ∧ IsClosedDisc (discIns Δ C) ∧ discBd (discIns Δ C) = C.U ∧
        frontier (discIns Δ C) = C.U ∧ subBd (discIns Δ C) = C.U ∧
        (∀ Δ' : Set S, Δ' ⊆ Δ → IsClosedDisc Δ' → discBd Δ' = C.U → Δ' = discIns Δ C) := by
    intro C hC hCs
    obtain ⟨⟨h1, h2, h3⟩, huniq⟩ := discIns_spec hΔ hC (hCs.U_subset.trans hU)
    have hfr : frontier (discIns Δ C) = C.U := by
      rw [IsClosedDisc.frontier_eq_discBd hS h2, h3]
    exact ⟨h1, h2, h3, hfr, by rw [subBd_eq_frontier, hfr], huniq⟩
  have hmono : ∀ C₁ C₂ : Drawing S, C₁.IsCircuit → C₁.IsSubdrawing Γ' → C₁.length < k →
      C₂.IsCircuit → C₂.IsSubdrawing Γ' → C₂.length < k → C₁.U ⊆ discIns Δ C₂ →
      discIns Δ C₁ ⊆ discIns Δ C₂ := by
    intro C₁ C₂ h₁ s₁ _ h₂ s₂ _ hsub
    obtain ⟨sub₁, d₁, b₁, -, -, uniq₁⟩ := hspec C₁ h₁ s₁
    obtain ⟨sub₂, d₂, b₂, -, -, -⟩ := hspec C₂ h₂ s₂
    obtain ⟨D, ⟨hD₂, dD, bD, -⟩, -⟩ := disc_oArc (discIns Δ C₂) C₁.U d₂ hsub
      (isOArc_of_isCircuit h₁)
    have huniq : D = discIns Δ C₁ := uniq₁ D (hD₂.trans sub₂) dD bD
    exact huniq ▸ hD₂
  refine ⟨hk, fun C hC hCs _ => (hspec C hC hCs).2.1,
    fun C hC hCs _ => (hspec C hC hCs).2.2.2.2.1, hmono, ?_⟩
  intro P₀ P₁ P₂ a b hP₀ hP₁ hP₂ s₀ s₁ s₂ p₀ p₁ p₂ v₀₁ v₁₂ v₂₀ e₀₁ e₁₂ e₂₀ l₀ l₁ l₂
  have hab := ne_of_isPathBetween hP₀ p₀
  have supU : ∀ {P Q : Drawing S}, P.IsSubdrawing Γ' → Q.IsSubdrawing Γ' →
      (Γ'.sup P Q).U = P.U ∪ Q.U := by
    intro P Q hP hQ
    rw [Drawing.U_eq, Drawing.sup_V hP hQ, Drawing.sup_E hP hQ, P.U_eq, Q.U_eq, biUnion_union]
    ext x
    simp only [mem_union]
    tauto
  have circ : ∀ {P Q : Drawing S}, P.IsPathBetween a b → Q.IsPathBetween a b →
      P.IsSubdrawing Γ' → Q.IsSubdrawing Γ' → P.V ∩ Q.V = {a, b} → Disjoint P.E Q.E →
      (Γ'.sup P Q).IsCircuit ∧ (Γ'.sup P Q).IsSubdrawing Γ' := fun hP hQ sP sQ v e =>
    ⟨Drawing.isCircuit_sup hP hQ sP sQ hab v e, Drawing.sup_isSubdrawing Γ' _ _⟩
  obtain ⟨c₀, ss₀⟩ := circ hP₁ hP₂ s₁ s₂ v₁₂ e₁₂
  obtain ⟨c₁, ss₁⟩ := circ hP₂ hP₀ s₂ s₀ v₂₀ e₂₀
  obtain ⟨c₂, ss₂⟩ := circ hP₀ hP₁ s₀ s₁ v₀₁ e₀₁
  obtain ⟨sub₀, d₀, b₀, f₀, -, -⟩ := hspec _ c₀ ss₀
  obtain ⟨sub₁, d₁, b₁, f₁, -, -⟩ := hspec _ c₁ ss₁
  obtain ⟨sub₂, d₂, b₂, f₂, -, uniq₂⟩ := hspec _ c₂ ss₂
  rw [supU s₁ s₂] at f₀
  rw [supU s₂ s₀] at f₁
  rw [supU s₀ s₁] at f₂
  have sb₀ : P₁.U ∪ P₂.U ⊆ discIns Δ (Γ'.sup P₁ P₂) := f₀ ▸ d₀.isCompact.isClosed.frontier_subset
  have sb₁ : P₂.U ∪ P₀.U ⊆ discIns Δ (Γ'.sup P₂ P₀) := f₁ ▸ d₁.isCompact.isClosed.frontier_subset
  have sb₂ : P₀.U ∪ P₁.U ⊆ discIns Δ (Γ'.sup P₀ P₁) := f₂ ▸ d₂.isCompact.isClosed.frontier_subset
  by_cases h₀ : P₀.U ⊆ discIns Δ (Γ'.sup P₁ P₂)
  · refine Or.inl ⟨hmono _ _ c₁ ss₁ l₁ c₀ ss₀ l₀ ?_, hmono _ _ c₂ ss₂ l₂ c₀ ss₀ l₀ ?_⟩
    · rw [supU s₂ s₀]; exact union_subset (subset_union_right.trans sb₀) h₀
    · rw [supU s₀ s₁]; exact union_subset h₀ (subset_union_left.trans sb₀)
  by_cases h₁ : P₁.U ⊆ discIns Δ (Γ'.sup P₂ P₀)
  · refine Or.inr (Or.inl ⟨hmono _ _ c₀ ss₀ l₀ c₁ ss₁ l₁ ?_, hmono _ _ c₂ ss₂ l₂ c₁ ss₁ l₁ ?_⟩)
    · rw [supU s₁ s₂]; exact union_subset h₁ (subset_union_left.trans sb₁)
    · rw [supU s₀ s₁]; exact union_subset (subset_union_right.trans sb₁) h₁
  by_cases h₂ : P₂.U ⊆ discIns Δ (Γ'.sup P₀ P₁)
  · refine Or.inr (Or.inr ⟨hmono _ _ c₀ ss₀ l₀ c₂ ss₂ l₂ ?_, hmono _ _ c₁ ss₁ l₁ c₂ ss₂ l₂ ?_⟩)
    · rw [supU s₁ s₂]; exact union_subset (subset_union_right.trans sb₂) h₂
    · rw [supU s₂ s₀]; exact union_subset h₂ (subset_union_left.trans sb₂)
  exfalso
  obtain ⟨dU, hbd, hne⟩ :=
    theta_disc_union hS (isLine_of_isPathBetween hP₀ hab) (isLine_of_isPathBetween hP₁ hab)
      (isLine_of_isPathBetween hP₂ hab) (by rw [U_inter_of_disjoint s₀ s₁ e₀₁, v₀₁])
      (by rw [U_inter_of_disjoint s₁ s₂ e₁₂, v₁₂]) (by rw [U_inter_of_disjoint s₂ s₀ e₂₀, v₂₀])
      d₀ d₁ d₂ f₀ f₁ f₂ h₀ h₁ h₂
  have hUsub : discIns Δ (Γ'.sup P₁ P₂) ∪ discIns Δ (Γ'.sup P₂ P₀) ⊆ Δ :=
    union_subset sub₀ sub₁
  have hbd₂ : discBd (discIns Δ (Γ'.sup P₁ P₂) ∪ discIns Δ (Γ'.sup P₂ P₀)) =
      (Γ'.sup P₀ P₁).U := hbd.trans b₂
  have heq := uniq₂ _ hUsub dU hbd₂
  exact hne heq

end GraphMinor.GM14
