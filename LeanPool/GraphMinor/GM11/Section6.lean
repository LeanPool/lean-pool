/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section8
public import LeanPool.GraphMinor.GM11.Section7
public import LeanPool.GraphMinor.GM11.Section6Pretangle
public import LeanPool.GraphMinor.GM11.Fan
public import LeanPool.GraphMinor.GM11.PlaneFacts
public import LeanPool.GraphMinor.Surface.DiscsInSurface
public import LeanPool.GraphMinor.Surface.DiscUnion
public import LeanPool.GraphMinor.Surface.SphereDisc
public import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XI, Section 6: the slope derived from a tangle

Graph Minors XI calls `ins` "the derived slope" of a respectful pretangle, without proof that it is
a
slope. This file proves it (`isSlope_of_derived`). Both axioms come from the same remark. If closed
discs `Δ₁, Δ₂, Δ₃` bounded by circuits of `Γ'` cover `Σ`, then `Γ ∩ Δ₁`, `Γ ∩ Δ₂`, `Γ ∩ Δ₃` cover
`Γ`,
which the second tangle axiom forbids (`not_cover`). This uses that an edge of `Γ` misses `U(Γ')`.

For the first slope axiom, let `U(C₁) ⊆ ins(C₂)`. Then `U(C₁)` bounds a closed disc in `ins(C₂)`. It
is
`ins(C₁)`, or else `ins(C₁)` and `ins(C₂)` cover `Σ`. For the second slope axiom, suppose that each
of
the three paths leaves the disc bounded by the other two. Two of the discs meet in a path, so that
their union is a closed disc, and it covers `Σ` together with the third (`theta_cover`).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface Metric Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S]

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
    have hxD : x ∈ D := discBd_subset _ hx
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

/-- Two different closed discs of a connected closed surface with the same boundary cover the
surface. If the surface is not a sphere there are no such discs (`eq_of_discBd_eq`), and in a sphere
the two discs that an `O`-arc bounds cover it. -/
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
closed disc, other
than `Δ₂`, with the same boundary as `Δ₂`. -/
theorem theta_union (hS : IsClosedSurface S) {A₀ A₁ A₂ Δ₀ Δ₁ Δ₂ : Set S} {a b :
  S}
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
  -- The inner parts of `A₀` and `A₁` lie outside `Δ₀` and `Δ₁`.
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
  -- So the interior of `Δ₁` misses `Δ₀`.
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
  exact ⟨dU, hbd, fun heq => h₂ fun x hx => heq ▸ Or.inl (sub₀ (Or.inr hx))⟩

/-- Under the hypotheses of `theta_union`, the three discs cover `Σ`. -/
theorem theta_cover [ConnectedSpace S] (hS : IsClosedSurface S) {A₀ A₁ A₂ Δ₀ Δ₁ Δ₂ : Set S} {a b :
  S}
    (l₀ : IsLineWithEnds A₀ a b) (l₁ : IsLineWithEnds A₁ a b) (l₂ : IsLineWithEnds A₂ a b)
    (i₀₁ : A₀ ∩ A₁ = {a, b}) (i₁₂ : A₁ ∩ A₂ = {a, b}) (i₂₀ : A₂ ∩ A₀ = {a, b})
    (d₀ : IsClosedDisc Δ₀) (d₁ : IsClosedDisc Δ₁) (d₂ : IsClosedDisc Δ₂)
    (f₀ : frontier Δ₀ = A₁ ∪ A₂) (f₁ : frontier Δ₁ = A₂ ∪ A₀) (f₂ : frontier Δ₂ = A₀ ∪ A₁)
    (h₀ : ¬ A₀ ⊆ Δ₀) (h₁ : ¬ A₁ ⊆ Δ₁) (h₂ : ¬ A₂ ⊆ Δ₂) : Δ₀ ∪ Δ₁ ∪ Δ₂ = univ := by
  obtain ⟨dU, hbd, hne⟩ := theta_union hS l₀ l₁ l₂ i₀₁ i₁₂ i₂₀ d₀ d₁ d₂ f₀ f₁ f₂ h₀ h₁ h₂
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

end Paths

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
/-- An edge of `Γ` misses `U(Γ')`, so it lies inside or outside a closed set with frontier in
`U(Γ')`. -/
theorem edge_subset_or_disjoint_of_radial (hrad : Γ.U ∩ Γ'.U = Γ.V) {Δ : Set S} (hΔ : IsClosed Δ)
    (hb : frontier Δ ⊆ Γ'.U) {e : Set S} (he : e ∈ Γ.E) : e ⊆ Δ ∨ Disjoint e Δ := by
  obtain ⟨hp, hd, hU, -⟩ := Γ.edge_props he
  refine subset_or_disjoint_of_frontier hΔ hp (disjoint_left.mpr fun x hx hf => ?_)
  have : x ∈ Γ.U ∩ Γ'.U := ⟨hU hx, hb hf⟩
  rw [hrad] at this
  exact disjoint_left.mp hd hx this

omit [T1Space S] in
/-- Three sets `Γ ∩ Δ_i` cover `Γ` if the sets `Δ_i` are closed, cover `Σ`, and each has frontier in
`U(Γ')`. By the second tangle axiom they are not all first parts of members of `T`. -/
theorem not_cover (hT : IsPretangle Γ.toHypergraph θ T) (hrad : Γ.U ∩ Γ'.U = Γ.V)
    {Δ₁ Δ₂ Δ₃ : Set S} (c₁ : IsClosed Δ₁) (c₂ : IsClosed Δ₂) (c₃ : IsClosed Δ₃)
    (b₁ : frontier Δ₁ ⊆ Γ'.U) (b₂ : frontier Δ₂ ⊆ Γ'.U) (b₃ : frontier Δ₃ ⊆ Γ'.U)
    (m₁ : (Γ.inter Δ₁, Γ.interOutside Δ₁) ∈ T) (m₂ : (Γ.inter Δ₂, Γ.interOutside Δ₂) ∈ T)
    (m₃ : (Γ.inter Δ₃, Γ.interOutside Δ₃) ∈ T) (hcov : Δ₁ ∪ Δ₂ ∪ Δ₃ = univ) : False := by
  have hedge : ∀ e ∈ Γ.E, e ⊆ Δ₁ ∨ e ⊆ Δ₂ ∨ e ⊆ Δ₃ := by
    intro e he
    obtain ⟨x, hx⟩ := (Γ.edge_props he).2.2.2
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

/-- The discs of short circuits of `Γ'` form a slope, if they are monotone and, in a sphere, three
of them do not
cover the surface. -/
theorem isSlope_of_mono [ConnectedSpace S] {Γ' : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
  (hS : IsClosedSurface S)
    (hk : 2 ≤ k)
    (hd : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < k → IsClosedDisc (ins C)
      ∧ subBd (ins C) = C.U)
    (hmono : ∀ C₁ C₂ : Drawing S, C₁.IsCircuit → C₁.IsSubdrawing Γ' → C₁.length < k →
      C₂.IsCircuit → C₂.IsSubdrawing Γ' → C₂.length < k → C₁.U ⊆ ins C₂ → ins C₁ ⊆ ins C₂)
    (htheta : IsSphere S → ∀ C₀, C₀.IsCircuit → C₀.IsSubdrawing Γ' → C₀.length < k →
      ∀ C₁, C₁.IsCircuit → C₁.IsSubdrawing Γ' → C₁.length < k →
      ∀ C₂, C₂.IsCircuit → C₂.IsSubdrawing Γ' → C₂.length < k → ins C₀ ∪ ins C₁ ∪ ins C₂ ≠ univ) :
    IsSlope Γ' k ins := by
  have : T2Space S := hS.2.1
  have hfr : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < k →
      IsClosedDisc (ins C) ∧ frontier (ins C) = C.U ∧ IsClosed (ins C) := by
    intro C h s l
    obtain ⟨d, b⟩ := hd C h s l
    rw [subBd_eq_frontier] at b
    exact ⟨d, b, d.isCompact.isClosed⟩
  refine ⟨hk, fun C h s l => (hd C h s l).1, fun C h s l => (hd C h s l).2, hmono, ?_⟩
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
  obtain ⟨d₀, f₀, cl₀⟩ := hfr _ c₀ ss₀ l₀
  obtain ⟨d₁, f₁, cl₁⟩ := hfr _ c₁ ss₁ l₁
  obtain ⟨d₂, f₂, cl₂⟩ := hfr _ c₂ ss₂ l₂
  have f₀' := f₀
  have f₁' := f₁
  have f₂' := f₂
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
  obtain ⟨dU, hbd, hne⟩ := theta_union hS (isLine_of_isPathBetween hP₀ hab)
    (isLine_of_isPathBetween hP₁ hab)
    (isLine_of_isPathBetween hP₂ hab) (by rw [U_inter_of_disjoint s₀ s₁ e₀₁, v₀₁])
    (by rw [U_inter_of_disjoint s₁ s₂ e₁₂, v₁₂]) (by rw [U_inter_of_disjoint s₂ s₀ e₂₀, v₂₀])
    d₀ d₁ d₂ f₀ f₁ f₂ h₀ h₁ h₂
  by_cases hsph : IsSphere S
  · refine htheta hsph _ c₀ ss₀ l₀ _ c₁ ss₁ l₁ _ c₂ ss₂ l₂ ?_
    rw [cover_of_discBd_eq hS dU d₂ hbd hne]
  · exact hne (eq_of_discBd_eq (IsClosedSurface.isSurface hS) hsph dU d₂ hbd)

/-- `ins` is a slope in `Γ'`: the slope "derived" from `T` (Graph Minors XI, Section 6, page 87). -/
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
  refine isSlope_of_mono hS (by have := hT.one_le; omega) (fun C h s l => ⟨(hd C h s l).1,
    (hd C h s l).2.1⟩) hmono ?_
  rintro - C₀ h₀ s₀ l₀ C₁ h₁ s₁ l₁ C₂ h₂ s₂ l₂ hcov
  obtain ⟨-, -, cl₀, b₀, m₀⟩ := hfr C₀ h₀ s₀ l₀
  obtain ⟨-, -, cl₁, b₁, m₁⟩ := hfr C₁ h₁ s₁ l₁
  obtain ⟨-, -, cl₂, b₂, m₂⟩ := hfr C₂ h₂ s₂ l₂
  exact not_cover hT hrad cl₀ cl₁ cl₂ b₀ b₁ b₂ m₀ m₁ m₂ hcov

omit [T1Space S] in
/-- A vertex common to `Γ ∩ Δ` and `Γ ∩ closure (Σ − Δ)` is a vertex of the circuit `C` that bounds
`Δ`, since edges of `Γ'` contain no vertex of `Γ`. -/
theorem inter_outside_vertex (hV : Γ.V ⊆ Γ'.V) {C : Drawing S} (hCs : C.IsSubdrawing Γ')
    {Δ : Set S} (hb : frontier Δ = C.U) {x : S}
    (hx : x ∈ (Γ.inter Δ ∩ Γ.interOutside Δ).vertexSet) : x ∈ C.V ∩ Γ.V := by
  obtain ⟨⟨hxV, hxΔ⟩, -, hxc⟩ := hx
  have hxf : x ∈ C.U := by
    rw [← hb, frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hxΔ, by rwa [compl_eq_univ_sdiff]⟩
  have hxV' : x ∈ Γ.V := Γ.toHypergraph_vertexSet ▸ hxV
  by_contra hn
  have hxC : x ∉ C.V := fun h => hn ⟨h, hxV'⟩
  obtain ⟨f, hf, hxef⟩ := C.exists_edge_of_mem hxf hxC
  exact ((hCs.2 hf).2.1 hxef).2 (hV hxV')

omit [T1Space S] in
/-- (ii) implies (i) in (6.3) of Graph Minors XI (page 89). The hypothesis `hiso` says that `Γ` has
no
isolated vertices. -/
theorem mem_of_circuits [T2Space S] (hT : IsPretangle Γ.toHypergraph θ T) (hVs : Γ.V ⊆ Γ'.V)
    (hd : IsDerivedSlope Γ Γ' θ T ins) (hiso : ∀ v ∈ Γ.V, ∃ e ∈ Γ.E, v ∈ closure e)
    {A B : Hypergraph S (Set S)} (hsep : Γ.toHypergraph.IsSeparation A B)
    (hord : separationOrder A B < θ) {k : ℕ} {C : Fin k → Drawing S}
    (hC : ∀ i, (C i).IsCircuit ∧ (C i).IsSubdrawing Γ' ∧ (C i).length < 2 * θ ∧
      (C i).V ∩ Γ.V ⊆ (A ∩ B).vertexSet)
    (hin : ∀ e ∈ A.edgeSet, ∃ i, e ⊆ ins (C i)) : (A, B) ∈ T := by
  rcases hT.axiom1 hsep hord with h | hBA
  · exact h
  exfalso
  -- The pair `(A ∩ B, Γ)` is in `T`.
  have hinf : (A ∩ B) ≤ Γ.toHypergraph := by
    refine le_trans ?_ hsep.left_le
    refine ⟨inter_subset_left, inter_subset_left, fun e he => ?_⟩
    have h₀ : (A ∩ B).edgeSet = ∅ := hsep.edgeSet_inter_eq
    rw [h₀] at he
    exact absurd he (notMem_empty e)
  have hE₀ : (A ∩ B).edgeSet = ∅ := hsep.edgeSet_inter_eq
  have hsep₀ : Γ.toHypergraph.IsSeparation (A ∩ B) Γ.toHypergraph := by
    refine ⟨hinf, le_rfl, ?_, ?_⟩
    · exact le_antisymm (by
        refine ⟨union_subset hinf.vertexSet_subset subset_rfl,
          union_subset hinf.edgeSet_subset subset_rfl, fun e he => ?_⟩
        rcases he with he | he
        · rw [hE₀] at he
          exact absurd he (notMem_empty e)
        · ext v
          constructor
          · exact fun h => Or.inr h
          · rintro (h | h)
            · exact absurd ((A ∩ B).edge_mem_of_inc h) (by rw [hE₀]; exact notMem_empty e)
            · exact h)
        (Hypergraph.IsSubhypergraph.mk subset_union_right subset_union_right fun e he => by
          ext v
          constructor
          · rintro (h | h)
            · exact absurd ((A ∩ B).edge_mem_of_inc h) (by rw [hE₀]; exact notMem_empty e)
            · exact h
          · exact fun h => Or.inr h)
    · have : ((A ∩ B) ∩ Γ.toHypergraph).edgeSet ⊆ ∅ := fun e he => hE₀ ▸ he.1
      exact subset_empty_iff.mp this
  have hord₀ : separationOrder (A ∩ B) Γ.toHypergraph < θ := by
    refine lt_of_le_of_lt (ncard_le_ncard inter_subset_left (A ∩ B).vertexSet_finite) hord
  have hm₀ : (A ∩ B, Γ.toHypergraph) ∈ T := by
    rcases hT.axiom1 hsep₀ hord₀ with h | h
    · exact h
    · have heq : Γ.toHypergraph ∪ Γ.toHypergraph ∪ Γ.toHypergraph = Γ.toHypergraph := by
        rw [GM10.union_self, GM10.union_self]
      exact absurd heq (hT.axiom2 h h h)
  classical
  let L : List (Hypergraph S (Set S) × Hypergraph S (Set S)) :=
    (A ∩ B, Γ.toHypergraph) ::
      (List.finRange k).map fun i => (Γ.inter (ins (C i)), Γ.interOutside (ins (C i)))
  have hcirc : ∀ i, IsClosed (ins (C i)) ∧ frontier (ins (C i)) = (C i).U ∧
      (Γ.inter (ins (C i)), Γ.interOutside (ins (C i))) ∈ T := fun i => by
    obtain ⟨c, s, l, -⟩ := hC i
    obtain ⟨d, b, m⟩ := hd _ c s l
    exact ⟨d.isCompact.isClosed, by rwa [subBd_eq_frontier] at b, m⟩
  have hmem : ∀ i, (Γ.inter (ins (C i)), Γ.interOutside (ins (C i))) ∈ L := fun i =>
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  refine theorem_6_2_proof hT hBA L ?_ ?_ ?_ ?_
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hm₀
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      exact (hcirc i).2.2
  · intro p hp x hx
    rw [GM10.inter_comm B A]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hx.1
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      exact (hC i).2.2.2 (inter_outside_vertex hVs (hC i).2.1 (hcirc i).2.1 hx)
  · intro v hv
    by_cases hvB : v ∈ B.vertexSet
    · exact ⟨_, List.mem_cons_self .., ⟨hv, hvB⟩⟩
    have hvΓ : v ∈ Γ.V := Γ.toHypergraph_vertexSet ▸ hsep.left_le.vertexSet_subset hv
    obtain ⟨e, he, hve⟩ := hiso v hvΓ
    have hinc : Γ.toHypergraph.Inc e v := PaintingOrDrawing.toHypergraph_inc.mpr ⟨he, hvΓ, hve⟩
    rw [← hsep.union_eq] at hinc
    rcases hinc with hinc | hinc
    · obtain ⟨i, hi⟩ := hin e (A.edge_mem_of_inc hinc)
      exact ⟨_, hmem i, hvΓ, (hcirc i).1.closure_subset_iff.mpr hi hve⟩
    · exact absurd (B.vertex_mem_of_inc hinc) hvB
  · intro e he
    obtain ⟨i, hi⟩ := hin e he
    refine ⟨_, hmem i, ?_, hi⟩
    have : e ∈ Γ.toHypergraph.edgeSet := hsep.left_le.edgeSet_subset he
    exact Γ.toHypergraph_edgeSet ▸ this

omit [T1Space S] in
/-- In a bipartite walk, about half of the vertices lie in one side `X`. -/
theorem two_mul_count_le {G : Drawing S} (X : Set S) [DecidablePred (· ∈ X)]
    (hb : ∀ e x y, G.toGraph.IsLink e x y → (x ∈ X ↔ y ∉ X)) {u v : S}
    (W : GraphWalk G.toGraph u v) :
    W.length + (if v ∈ X then 1 else 0) ≤
      2 * (W.support.tail.countP (· ∈ X)) + (if u ∈ X then 1 else 0) := by
  induction W with
  | nil _ => simp [GraphWalk.length, GraphWalk.edges, GraphWalk.support]
  | @cons a y b e hl r ih =>
    have h₁ := hb e a y hl
    have hsup : (GraphWalk.cons hl r).support.tail = r.support := rfl
    have hsup₂ : r.support = y :: r.support.tail := by
      cases r <;> rfl
    have hlen : (GraphWalk.cons hl r).length = r.length + 1 := rfl
    rw [hsup, hlen]
    rw [hsup₂, List.countP_cons]
    by_cases hy : y ∈ X
    · have ha : a ∉ X := fun h => (h₁.mp h) hy
      simp only [hy, ha, ite_true, ite_false, decide_true] at ih ⊢
      omega
    · have ha : a ∈ X := h₁.mpr hy
      simp only [hy, ha, ite_true, ite_false, decide_false] at ih ⊢
      omega

omit [T1Space S] in
/-- Half the length of a circuit of a radial drawing is the number of its vertices in `Γ`. So
`(V(Γ), θ)` is a weighting of `Γ'` for the slope order `2θ`. -/
theorem isWeighting_radial (hθ : 1 ≤ θ) (hV : Γ.V ⊆ Γ'.V)
    (hbip : ∀ e x y, Γ'.toGraph.IsLink e x y → (x ∈ Γ.V ↔ y ∉ Γ.V)) :
    IsWeighting Γ' (2 * θ) Γ.V θ := by
  classical
  refine ⟨hV, hθ, fun C hC hCs hl => ?_⟩
  obtain ⟨u, W, ⟨hnd, hed⟩, -, hCV, hCE⟩ := hC
  have hlen : C.length = W.length := by
    rw [Drawing.length, hCE]
    have h : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by
      ext x
      simp
    rw [h, ncard_coe_finset, List.toFinset_card_of_nodup hed]
    rfl
  have hb' : ∀ e x y, C.toGraph.IsLink e x y → (x ∈ Γ.V ↔ y ∉ Γ.V) := by
    intro e x y hl'
    refine hbip e x y ⟨hCs.2 hl'.1, hCs.1 hl'.2.1, hCs.1 hl'.2.2.1, ?_⟩
    rw [← hCs.closure_inter_V hl'.1]
    exact hl'.2.2.2
  have hc := two_mul_count_le Γ.V hb' W
  have hcard : W.support.tail.countP (· ∈ Γ.V) ≤ (Γ.V ∩ C.V).ncard := by
    have hf : (W.support.tail.filter (· ∈ Γ.V)).Nodup := hnd.filter _
    have hsub : ((W.support.tail.filter (· ∈ Γ.V)).toFinset : Set S) ⊆ Γ.V ∩ C.V := by
      intro x hx
      have hx' : x ∈ W.support.tail ∧ x ∈ Γ.V := by simpa using hx
      refine ⟨hx'.2, ?_⟩
      rw [hCV]
      exact List.mem_of_mem_tail hx'.1
    have := ncard_le_ncard hsub (C.finite_V.subset fun x hx => hx.2)
    rw [ncard_coe_finset, List.toFinset_card_of_nodup hf] at this
    rwa [List.countP_eq_length_filter]
  omega

/-- What Graph Minors XI (Section 3, page 75) says of a radial drawing without proof: "every region
of $\Gamma'$ includes a unique edge of $\Gamma$", and, as its proof of (6.5) (page 91) uses, the
vertices of `Γ` on
the closure of a region of `Γ'` are the ends of that edge. -/
def RegionFacts (Γ : PaintingOrDrawing S) (Γ' : Drawing S) : Prop :=
  (∀ s ∈ Γ'.R, ∃ e ∈ Γ.E, e ⊆ s) ∧ (∀ s ∈ Γ'.R, ∀ e ∈ Γ.E, ∀ f ∈ Γ.E, e ⊆ s → f ⊆ s → e = f) ∧
    ∀ s ∈ Γ'.R, ∀ e ∈ Γ.E, e ⊆ s → ∀ v ∈ Γ.V, v ∈ closure s → v ∈ closure e

omit [T1Space S] in
/-- A radial drawing is bipartite, by condition (iii) of its definition. -/
theorem bipartite_of_preRadial (hrad : Γ.IsPreRadialDrawing Γ') :
    ∀ e x y, Γ'.toGraph.IsLink e x y → (x ∈ Γ.V ↔ y ∉ Γ.V) := by
  intro e x y hl
  obtain ⟨v, hv, w, ⟨-, hw⟩, hcap⟩ := hrad.2.2.2.2.1 e hl.1
  have heq : ({x, y} : Set S) = {v, w} := hl.2.2.2.symm.trans hcap
  have hx : x ∈ ({v, w} : Set S) := heq ▸ mem_insert x _
  have hy : y ∈ ({v, w} : Set S) := heq ▸ mem_insert_of_mem x rfl
  have hv' : v ∈ ({x, y} : Set S) := heq ▸ mem_insert v _
  have hw' : w ∈ ({x, y} : Set S) := heq ▸ mem_insert_of_mem v rfl
  rcases hx with rfl | rfl
  · rcases hw' with rfl | rfl
    · exact absurd hv hw
    · exact ⟨fun _ => hw, fun _ => hv⟩
  · rcases hy with rfl | rfl
    · exact ⟨fun h => absurd h hw, fun h => absurd hv h⟩
    · rcases hv' with rfl | rfl <;> exact absurd hv hw

omit [T1Space S] in
/-- A vertex of `Γ` lies in the closure of a region of `Γ'`, so it is not isolated, by
`RegionFacts`. -/
theorem exists_edge_of_regionFacts [ConnectedSpace S] (hS : IsClosedSurface S)
    (hf : RegionFacts Γ Γ') {v : S} (hv : v ∈ Γ.V) : ∃ e ∈ Γ.E, v ∈ closure e := by
  have : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hfin := finite_R hS Γ'
  have hdense : v ∈ closure (⋃₀ Γ'.R) := by
    refine mem_closure_iff.mpr fun O hO hvO => ?_
    obtain ⟨y, hyO, hyU⟩ := exists_notMem_U (Γ := Γ') hS hO ⟨v, hvO⟩
    obtain ⟨s, hs, hys⟩ := exists_region_of_notMem hyU
    exact ⟨y, hyO, s, hs, hys⟩
  rw [hfin.closure_sUnion] at hdense
  obtain ⟨s, hs, hvs⟩ := mem_iUnion₂.mp hdense
  obtain ⟨e, he, hes⟩ := hf.1 s hs
  exact ⟨e, he, hf.2.2 s hs e he hes v hv hvs⟩

section Sep

variable {A B : Hypergraph S (Set S)}

omit [T1Space S] in
/-- With `RegionFacts`, each region of `Γ'` includes an edge of exactly one side of a separation. -/
theorem compl_regions (hf : RegionFacts Γ Γ') (hsep : Γ.toHypergraph.IsSeparation A B) :
    Γ'.R \ PaintingOrDrawing.regionsIncludingEdge Γ' A =
      PaintingOrDrawing.regionsIncludingEdge Γ' B := by
  have hE : (A ∩ B).edgeSet = ∅ := hsep.edgeSet_inter_eq
  have hA : ∀ {e}, e ∈ A.edgeSet → e ∈ Γ.E := fun h =>
    Γ.toHypergraph_edgeSet ▸ hsep.left_le.edgeSet_subset h
  have hB : ∀ {e}, e ∈ B.edgeSet → e ∈ Γ.E := fun h =>
    Γ.toHypergraph_edgeSet ▸ hsep.right_le.edgeSet_subset h
  ext s
  constructor
  · rintro ⟨hs, hn⟩
    obtain ⟨e, he, hes⟩ := hf.1 s hs
    have he' : e ∈ (A ∪ B).edgeSet := by
      rw [hsep.union_eq]
      exact Γ.toHypergraph_edgeSet ▸ he
    rcases he' with h | h
    · exact absurd ⟨hs, e, h, hes⟩ hn
    · exact ⟨hs, e, h, hes⟩
  · rintro ⟨hs, e, he, hes⟩
    refine ⟨hs, ?_⟩
    rintro ⟨-, f, hfa, hfs⟩
    have := hf.2.1 s hs f (hA hfa) e (hB he) hfs hes
    subst this
    have : f ∈ (A ∩ B).edgeSet := ⟨hfa, he⟩
    rw [hE] at this
    exact notMem_empty _ this

omit [T1Space S] in
/-- With `RegionFacts`, a vertex of `Γ` in the closure of a region with an edge of `A` lies in `A`.
-/
theorem mem_side (hf : RegionFacts Γ Γ') (hsep : Γ.toHypergraph.IsSeparation A B) {v : S}
    (hv : v ∈ Γ.V) {s : Set S} (hs : s ∈ PaintingOrDrawing.regionsIncludingEdge Γ' A)
    (hvs : v ∈ closure s) : v ∈ A.vertexSet := by
  obtain ⟨hR, e, he, hes⟩ := hs
  have heΓ : e ∈ Γ.E := Γ.toHypergraph_edgeSet ▸ hsep.left_le.edgeSet_subset he
  have hinc : Γ.toHypergraph.Inc e v :=
    PaintingOrDrawing.toHypergraph_inc.mpr ⟨heΓ, hv, hf.2.2 s hR e heΓ hes v hv hvs⟩
  rw [← hsep.union_eq] at hinc
  rcases hinc with hinc | hinc
  · exact A.vertex_mem_of_inc hinc
  · have : e ∈ (A ∩ B).edgeSet := ⟨he, B.edge_mem_of_inc hinc⟩
    rw [show (A ∩ B).edgeSet = ∅ from hsep.edgeSet_inter_eq] at this
    exact absurd this (notMem_empty _)

/-- With `RegionFacts`, the vertices of `Γ` in `N(Z(A))` lie in `A ∩ B`. -/
theorem boundary_vertex (hS : IsClosedSurface S) (hf : RegionFacts Γ Γ')
    (hsep : Γ.toHypergraph.IsSeparation A B) {v : S} (hv : v ∈ Γ.V)
    (hN : v ∈ (boundaryDrawing Γ' (PaintingOrDrawing.regionsIncludingEdge Γ' A)).V) :
    v ∈ (A ∩ B).vertexSet := by
  have : T2Space S := hS.2.1
  obtain ⟨⟨r, hr, hir⟩, s, hs, his⟩ := (mem_boundaryDrawing_V hS).mp hN
  rw [compl_regions hf hsep] at hs
  exact ⟨mem_side hf hsep hv hr hir.2.2, mem_side hf hsep.symm hv hs his.2.2⟩

/-- If `Z(A)` is small then (ii) of (6.3) holds. -/
theorem circuits_of_small (hS : IsClosedSurface S) (hf : RegionFacts Γ Γ')
    (hrad : Γ.U ∩ Γ'.U = Γ.V) (hsep : Γ.toHypergraph.IsSeparation A B)
    (hsm : IsSmall Γ' ins (2 * θ) Γ.V θ (PaintingOrDrawing.regionsIncludingEdge Γ' A)) :
    ∃ (k : ℕ) (C : Fin k → Drawing S),
      (∀ i : Fin k, (C i).IsCircuit ∧ (C i).IsSubdrawing Γ' ∧ (C i).length < 2 * θ ∧
        (C i).V ∩ Γ.V ⊆ (A ∩ B).vertexSet) ∧
      ∀ e ∈ A.edgeSet, ∃ i : Fin k, e ⊆ ins (C i) := by
  have : T2Space S := hS.2.1
  set N := boundaryDrawing Γ' (PaintingOrDrawing.regionsIncludingEdge Γ' A) with hN
  have hNs : N.IsSubdrawing Γ' := Drawing.span_isSubdrawing Γ' _ _
  have hex : ∀ e : A.edgeSet, ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing N ∧
      C.length < 2 * θ ∧ e.1 ⊆ ins C := by
    intro e
    have heΓ : e.1 ∈ Γ.E := Γ.toHypergraph_edgeSet ▸ hsep.left_le.edgeSet_subset e.2
    obtain ⟨hp, hd, hU, x, hx⟩ := Γ.edge_props heΓ
    have hoff : ∀ y ∈ e.1, y ∉ Γ'.U := fun y hy hyU => by
      have : y ∈ Γ.U ∩ Γ'.U := ⟨hU hy, hyU⟩
      rw [hrad] at this
      exact disjoint_left.mp hd hy this
    have hr : connectedComponentIn (univ \ Γ'.U) x ∈ Γ'.R :=
      (mem_R_iff Γ').mpr ⟨x, hoff x hx, rfl⟩
    have hsub : e.1 ⊆ connectedComponentIn (univ \ Γ'.U) x :=
      hp.subset_connectedComponentIn hx fun y hy => ⟨mem_univ y, hoff y hy⟩
    obtain ⟨C, hC, hCs, hl, hin⟩ := hsm.2 _ ⟨hr, e.1, e.2, hsub⟩
    exact ⟨C, hC, hCs, hl, hsub.trans hin⟩
  choose C' hC' using hex
  have : Fintype A.edgeSet := A.edgeSet_finite.fintype
  refine ⟨Fintype.card A.edgeSet, fun i => C' ((Fintype.equivFin _).symm i), fun i => ?_, ?_⟩
  · obtain ⟨c, s, l, -⟩ := hC' ((Fintype.equivFin _).symm i)
    refine ⟨c, s.trans hNs, l, fun x hx => ?_⟩
    exact boundary_vertex hS hf hsep hx.2 (s.1 hx.1)
  · intro e he
    refine ⟨Fintype.equivFin _ ⟨e, he⟩, ?_⟩
    have := (hC' ⟨e, he⟩).2.2.2
    simpa using this

/-- Exactly one of `Z(A)`, `Z(B)` is small, by (5.2), for a separation of order `< θ`. -/
theorem small_or_small (hS : IsClosedSurface S) [ConnectedSpace S] (hf : RegionFacts Γ Γ')
    (hsl : IsSlope Γ' (2 * θ) ins) (hw : IsWeighting Γ' (2 * θ) Γ.V θ)
    (hsep : Γ.toHypergraph.IsSeparation A B) (hord : separationOrder A B < θ) :
    (IsSmall Γ' ins (2 * θ) Γ.V θ (PaintingOrDrawing.regionsIncludingEdge Γ' A) ∨
      IsSmall Γ' ins (2 * θ) Γ.V θ (PaintingOrDrawing.regionsIncludingEdge Γ' B)) ∧
    ¬ (IsSmall Γ' ins (2 * θ) Γ.V θ (PaintingOrDrawing.regionsIncludingEdge Γ' A) ∧
      IsSmall Γ' ins (2 * θ) Γ.V θ (PaintingOrDrawing.regionsIncludingEdge Γ' B)) := by
  have : T2Space S := hS.2.1
  have hsub : Γ.V ∩ (boundaryDrawing Γ' (PaintingOrDrawing.regionsIncludingEdge Γ' A)).V ⊆
      (A ∩ B).vertexSet := fun x hx => boundary_vertex hS hf hsep hx.1 hx.2
  have hlt := lt_of_le_of_lt (ncard_le_ncard hsub (A ∩ B).vertexSet_finite) hord
  have hregions : PaintingOrDrawing.regionsIncludingEdge Γ' A ⊆ Γ'.R := fun _ hr => hr.1
  have := theorem_5_2_proof hS hsl hw hregions hlt
  rwa [compl_regions hf hsep] at this

end Sep

/-- (6.3) of Graph Minors XI (page 89), from `RegionFacts`. -/
theorem theorem_6_3_of_regionFacts [ConnectedSpace S] (hS : IsClosedSurface S)
    (hT : IsPretangle Γ.toHypergraph θ T) (hrad : Γ.IsPreRadialDrawing Γ')
    (hd : IsDerivedSlope Γ Γ' θ T ins) (hf : RegionFacts Γ Γ') :
    (∀ A B : Hypergraph S (Set S), Γ.toHypergraph.IsSeparation A B → separationOrder A B < θ →
      ((A, B) ∈ T ↔
        ∃ (k : ℕ) (C : Fin k → Drawing S),
          (∀ i : Fin k, (C i).IsCircuit ∧ (C i).IsSubdrawing Γ' ∧ (C i).length < 2 * θ ∧
            (C i).V ∩ Γ.V ⊆ (A ∩ B).vertexSet) ∧
          ∀ e ∈ A.edgeSet, ∃ i : Fin k, e ⊆ ins (C i))) ∧
    T = inducedPretangle Γ Γ' θ ins := by
  have : T2Space S := hS.2.1
  have hr₁ : Γ.U ∩ Γ'.U = Γ.V := hrad.1
  have hVs : Γ.V ⊆ Γ'.V := hrad.2.1
  have hsl := isSlope_of_derived hS hT hr₁ hd
  have hw : IsWeighting Γ' (2 * θ) Γ.V θ :=
    isWeighting_radial hT.one_le hVs (bipartite_of_preRadial hrad)
  have hiso : ∀ v ∈ Γ.V, ∃ e ∈ Γ.E, v ∈ closure e := fun v hv =>
    exists_edge_of_regionFacts hS hf hv
  -- If `Z(A)` is small then `(A, B) ∈ T`.
  have hsmall : ∀ {A B : Hypergraph S (Set S)}, Γ.toHypergraph.IsSeparation A B →
      separationOrder A B < θ →
      IsSmall Γ' ins (2 * θ) Γ.V θ (PaintingOrDrawing.regionsIncludingEdge Γ' A) → (A, B) ∈ T := by
    intro A B hsep hord hsm
    obtain ⟨k, C, hC, hin⟩ := circuits_of_small hS hf hr₁ hsep hsm
    exact mem_of_circuits hT hVs hd hiso hsep hord hC hin
  -- If `(A, B) ∈ T` then `Z(A)` is small.
  have hmem : ∀ {A B : Hypergraph S (Set S)}, Γ.toHypergraph.IsSeparation A B →
      separationOrder A B < θ → (A, B) ∈ T →
      IsSmall Γ' ins (2 * θ) Γ.V θ (PaintingOrDrawing.regionsIncludingEdge Γ' A) := by
    intro A B hsep hord hAB
    refine (small_or_small hS hf hsl hw hsep hord).1.resolve_right fun hsm => ?_
    have hBA := hsmall hsep.symm (by rwa [GM10.separationOrder_comm]) hsm
    refine hT.axiom2 hAB hBA hBA ?_
    rw [GM10.union_assoc, GM10.union_self, hsep.union_eq]
  refine ⟨fun A B hsep hord => ⟨fun h => ?_, ?_⟩, ?_⟩
  · exact circuits_of_small hS hf hr₁ hsep (hmem hsep hord h)
  · rintro ⟨k, C, hC, hin⟩
    exact mem_of_circuits hT hVs hd hiso hsep hord hC hin
  · ext p
    constructor
    · intro hp
      have hs := hT.isSeparation (A := p.1) (B := p.2) hp
      have ho := hT.order_lt (A := p.1) (B := p.2) hp
      exact ⟨hs, ho, hmem hs ho hp⟩
    · rintro ⟨hs, ho, hsm⟩
      exact hsmall hs ho hsm

end Tangle

end GraphMinor.GM11
