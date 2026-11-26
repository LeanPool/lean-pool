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
import LeanPool.GraphMinor.GM11.DrawingTopology
import LeanPool.GraphMinor.GM11.NormalNoncover
import LeanPool.GraphMinor.GM11.Section6

/-!
# Slopes from Pretangles and Closed Discs

This file provides two slope constructions used across Graph Minors XIV:

1. `isSlope_of_derived`: the inside function derived from a respectful pretangle of order `θ`
   gives a slope of order `θ` in the radial drawing, as described before (6.1) in Graph Minors XI,
   page 87. Lean uses the circuit-length cutoff `2 * θ`. Graph Minors XIV uses this construction
   in Sections 7 and 9.
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
    frontier D = discBd D :=
  GM11.IsClosedDisc.frontier_eq_discBd hS hD

theorem IsClosedDisc.subBd_eq_discBd (hS : IsClosedSurface S) {D : Set S} (hD : IsClosedDisc D) :
    subBd D = discBd D := by
  rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hD]

/-- A closed disc in a closed surface is the closure of its interior. -/
theorem IsClosedDisc.subset_closure_diff_frontier (hS : IsClosedSurface S) {D : Set S}
    (hD : IsClosedDisc D) : D ⊆ closure (D \ frontier D) :=
  GM11.IsClosedDisc.subset_closure_diff_frontier hS hD

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
    (hD : IsClosedDisc D) : IsPreconnected (D \ frontier D) :=
  GM11.IsClosedDisc.isPreconnected_diff_frontier hS hD

/-- A preconnected set disjoint from the frontier of a closed set `X` is either contained in `X`
or disjoint from `X`. -/
theorem subset_or_disjoint_of_frontier {X F : Set S} (hX : IsClosed X) (hF : IsPreconnected F)
    (hd : Disjoint F (frontier X)) : F ⊆ X ∨ Disjoint F X :=
  GM11.subset_or_disjoint_of_frontier hX hF hd

/-! ## 2. Two Lines with Common Ends and Circuits as `O`-Arcs -/

/-- Two different closed discs of a connected closed surface with the same boundary cover the
surface. -/
theorem cover_of_discBd_eq [ConnectedSpace S] (hS : IsClosedSurface S) {Δ₁ Δ₂ : Set S}
    (h₁ : IsClosedDisc Δ₁) (h₂ : IsClosedDisc Δ₂) (hb : discBd Δ₁ = discBd Δ₂) (hne : Δ₁ ≠ Δ₂) :
    Δ₁ ∪ Δ₂ = univ :=
  GM11.cover_of_discBd_eq hS h₁ h₂ hb hne

/-- The part of a line between its ends is connected. -/
theorem IsLineWithEnds.isPreconnected_sdiff_pair {L : Set S} {a b : S} (h : IsLineWithEnds L a b) :
    IsPreconnected (L \ {a, b}) :=
  GM11.IsLineWithEnds.isPreconnected_sdiff_pair h

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
    IsClosedDisc (Δ₀ ∪ Δ₁) ∧ discBd (Δ₀ ∪ Δ₁) = discBd Δ₂ ∧ Δ₀ ∪ Δ₁ ≠ Δ₂ :=
  GM11.theta_union hS l₀ l₁ l₂ i₀₁ i₁₂ i₂₀ d₀ d₁ d₂ f₀ f₁ f₂ h₀ h₁ h₂

theorem theta_cover [ConnectedSpace S] (hS : IsClosedSurface S) {A₀ A₁ A₂ Δ₀ Δ₁ Δ₂ : Set S} {a b :
  S}
    (l₀ : IsLineWithEnds A₀ a b) (l₁ : IsLineWithEnds A₁ a b) (l₂ : IsLineWithEnds A₂ a b)
    (i₀₁ : A₀ ∩ A₁ = {a, b}) (i₁₂ : A₁ ∩ A₂ = {a, b}) (i₂₀ : A₂ ∩ A₀ = {a, b})
    (d₀ : IsClosedDisc Δ₀) (d₁ : IsClosedDisc Δ₁) (d₂ : IsClosedDisc Δ₂)
    (f₀ : frontier Δ₀ = A₁ ∪ A₂) (f₁ : frontier Δ₁ = A₂ ∪ A₀) (f₂ : frontier Δ₂ = A₀ ∪ A₁)
    (h₀ : ¬ A₀ ⊆ Δ₀) (h₁ : ¬ A₁ ⊆ Δ₁) (h₂ : ¬ A₂ ⊆ Δ₂) : Δ₀ ∪ Δ₁ ∪ Δ₂ = univ :=
  GM11.theta_cover hS l₀ l₁ l₂ i₀₁ i₁₂ i₂₀ d₀ d₁ d₂ f₀ f₁ f₂ h₀ h₁ h₂

section Paths

variable [T2Space S]

omit [T2Space S] in
theorem mem_V_of_mem_support {Γ : Drawing S} {a b : S} (W : GraphWalk Γ.toGraph a b) {x : S}
    (hx : x ∈ W.support) : x ∈ Γ.V :=
  GM11.mem_V_of_mem_support W hx

omit [T2Space S] in
theorem mem_E_of_mem_edges {Γ : Drawing S} {a b : S} (W : GraphWalk Γ.toGraph a b) {f : Set S}
    (hf : f ∈ W.edges) : f ∈ Γ.E :=
  GM11.mem_E_of_mem_edges W hf

omit [T2Space S] in
/-- A vertex in the closure of an edge of a walk is on the walk. -/
theorem mem_support_of_mem_edges {Γ : Drawing S} {a b : S} (W : GraphWalk Γ.toGraph a b) {f : Set S}
    (hf : f ∈ W.edges) {x : S} (hxf : x ∈ closure f) (hxV : x ∈ Γ.V) : x ∈ W.support :=
  GM11.mem_support_of_mem_edges W hf hxf hxV

/-- The union of the vertices and edges of a path with distinct ends is a line between them. -/
theorem walk_isLine (Γ : Drawing S) {a b : S} (W : GraphWalk Γ.toGraph a b) (hW : W.IsSimple)
    (hab : a ≠ b) : IsLineWithEnds ({x | x ∈ W.support} ∪ ⋃ e ∈ {e | e ∈ W.edges}, closure e) a b :=
  GM11.walk_isLine Γ W hW hab

omit [T2Space S] in
/-- A path of positive length has distinct ends. -/
theorem ne_of_isPathBetween {P : Drawing S} {a b : S} (hP : P.IsPathBetween a b)
    (hl : 0 < P.length) : a ≠ b :=
  GM11.ne_of_isPathBetween hP hl

/-- A path of positive length is a line between its ends. -/
theorem isLine_of_isPathBetween {P : Drawing S} {a b : S} (hP : P.IsPathBetween a b)
    (hab : a ≠ b) : IsLineWithEnds P.U a b :=
  GM11.isLine_of_isPathBetween hP hab

omit [T2Space S] in
/-- Two subdrawings of a drawing without common edges meet only in common vertices. -/
theorem U_inter_of_disjoint {Γ C D : Drawing S} (hC : C.IsSubdrawing Γ) (hD : D.IsSubdrawing Γ)
    (hE : Disjoint C.E D.E) : C.U ∩ D.U = C.V ∩ D.V :=
  GM11.U_inter_of_disjoint hC hD hE

/-- Two lines with the same two ends and nothing else in common form an `O`-arc. -/
theorem isOArc_union {L₁ L₂ : Set S} {a b : S} (h₁ : IsLineWithEnds L₁ a b)
    (h₂ : IsLineWithEnds L₂ a b) (hcap : L₁ ∩ L₂ ⊆ {a, b}) : IsOArc (L₁ ∪ L₂) :=
  GM11.isOArc_union h₁ h₂ hcap

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
    Γ.toHypergraph.Inc e v ↔ e ∈ Γ.E ∧ v ∈ Γ.V ∧ v ∈ closure e :=
  GM11.PaintingOrDrawing.toHypergraph_inc

omit [T1Space S] in
theorem PaintingOrDrawing.edge_props {Γ : PaintingOrDrawing S} {e : Set S} (he : e ∈ Γ.E) :
    IsPreconnected e ∧ Disjoint e Γ.V ∧ e ⊆ Γ.U ∧ e.Nonempty :=
  GM11.PaintingOrDrawing.edge_props he

omit [T1Space S] in
theorem edge_subset_or_disjoint_of_radial (hrad : Γ.U ∩ Γ'.U = Γ.V) {Δ : Set S} (hΔ : IsClosed Δ)
    (hb : frontier Δ ⊆ Γ'.U) {e : Set S} (he : e ∈ Γ.E) : e ⊆ Δ ∨ Disjoint e Δ :=
  GM11.edge_subset_or_disjoint_of_radial hrad hΔ hb he

omit [T1Space S] in
theorem not_cover (hT : IsPretangle Γ.toHypergraph θ T) (hrad : Γ.U ∩ Γ'.U = Γ.V)
    {Δ₁ Δ₂ Δ₃ : Set S} (c₁ : IsClosed Δ₁) (c₂ : IsClosed Δ₂) (c₃ : IsClosed Δ₃)
    (b₁ : frontier Δ₁ ⊆ Γ'.U) (b₂ : frontier Δ₂ ⊆ Γ'.U) (b₃ : frontier Δ₃ ⊆ Γ'.U)
    (m₁ : (Γ.inter Δ₁, Γ.interOutside Δ₁) ∈ T) (m₂ : (Γ.inter Δ₂, Γ.interOutside Δ₂) ∈ T)
    (m₃ : (Γ.inter Δ₃, Γ.interOutside Δ₃) ∈ T) (hcov : Δ₁ ∪ Δ₂ ∪ Δ₃ = univ) : False :=
  GM11.not_cover_of_radial_frontiers hT hrad c₁ c₂ c₃ b₁ b₂ b₃ m₁ m₂ m₃ hcov

/-- A derived inside function is a slope with circuit-length cutoff `2 * θ`.
This is the cutoff for a slope of order `θ` in Graph Minors XI, page 87, before (6.1). -/
theorem isSlope_of_derived [ConnectedSpace S] (hS : IsClosedSurface S)
    (hT : IsPretangle Γ.toHypergraph θ T) (hrad : Γ.U ∩ Γ'.U = Γ.V)
    (hd : IsDerivedSlope Γ Γ' θ T ins) : IsSlope Γ' (2 * θ) ins :=
  GM11.isSlope_of_derived hS hT hrad hd

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
