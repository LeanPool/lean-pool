/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section7
public import LeanPool.GraphMinor.GM11.Walks
public import LeanPool.GraphMinor.Surface.DiscsInSurface
public import LeanPool.GraphMinor.Surface.DiscUnion
public import LeanPool.GraphMinor.Surface.SphereDisc
import LeanPool.GraphMinor.GM11.PlaneFacts
import LeanPool.GraphMinor.GM11.Section3
import LeanPool.GraphMinor.GM11.Fan
import LeanPool.GraphMinor.GM11.Forest

/-!
# Topology of drawings and their bounding discs

The shared disc-frontier, theta-curve and drawing-walk lemmas used by the slope constructions
in Graph Minors XI and XIV. Two arcs that meet only at their common ends give a simple loop.
-/

public section

namespace GraphMinor.GM11

open Set Topology Surface Metric Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The image of the open disc under coordinates on a closed disc is open: this is invariance of
domain, in a chart of the surface around each point. -/
private theorem isOpen_image_ball (hS : IsClosedSurface S) {g : ℂ → S}
    (hg : ContinuousOn g (ball 0 1)) (hinj : InjOn g (ball 0 1)) : IsOpen (g '' ball 0 1) := by
  have : T2Space S := hS.2.1
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨U, hU, hxU, ⟨f⟩⟩ := hS.2.2 (g z)
  classical
  let F : S → ℂ := fun y => if hy : y ∈ U then complexPlane.symm (f ⟨y, hy⟩).1 else 0
  have hF : ∀ y (hy : y ∈ U), F y = complexPlane.symm (f ⟨y, hy⟩).1 := fun y hy => by
    simp only [F, hy, dite_true]
  have hFc : ContinuousOn F U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : U.domRestrict F = fun y : U => complexPlane.symm (f y).1 := by
      ext y
      exact hF y.1 y.2
    rw [this]
    exact complexPlane.symm.continuous.comp (continuous_subtype_val.comp f.continuous)
  have hFi : InjOn F U := by
    intro a ha b hb hab
    rw [hF a ha, hF b hb] at hab
    have h₁ := complexPlane.symm.injective hab
    have h₂ := f.injective (Subtype.ext h₁)
    exact congrArg Subtype.val h₂
  let B : Set ℂ := ball 0 1 ∩ g ⁻¹' U
  have hBo : IsOpen B := hg.isOpen_inter_preimage isOpen_ball hU
  have hzB : z ∈ B := ⟨hz, hxU⟩
  have hGc : ContinuousOn (F ∘ g) B :=
    hFc.comp (hg.mono inter_subset_left) fun w hw => hw.2
  have hGi : InjOn (F ∘ g) B := fun a ha b hb hab =>
    hinj ha.1 hb.1 (hFi ha.2 hb.2 hab)
  have hOpen := isOpen_image_of_injOn hBo hGc hGi
  have hO' : IsOpen (U ∩ F ⁻¹' ((F ∘ g) '' B)) := hFc.isOpen_inter_preimage hU hOpen
  refine Filter.mem_of_superset (hO'.mem_nhds ⟨hxU, z, hzB, rfl⟩) ?_
  rintro y ⟨hyU, w, hw, hwy⟩
  exact ⟨w, hw.1, hFi hw.2 hyU hwy⟩

/-- The interior of a closed disc in a closed surface is connected. -/
theorem IsClosedDisc.isPreconnected_diff_frontier (hS : IsClosedSurface S) {D : Set S}
    (hD : IsClosedDisc D) : IsPreconnected (D \ frontier D) := by
  obtain ⟨h, g, -, hg, hhD, hgD, hl, hr, -⟩ := IsClosedDisc.exists_chart hD
  have hgb : ContinuousOn g (ball 0 1) := hg.mono ball_subset_closedBall
  have hinj : InjOn g (ball 0 1) := by
    intro a ha b hb hab
    have ha' := hr (ball_subset_closedBall ha)
    have hb' := hr (ball_subset_closedBall hb)
    rw [← ha', ← hb']
    exact congrArg h hab
  have hO := isOpen_image_ball hS hgb hinj
  have hsub : g '' ball 0 1 ⊆ D := by
    rintro _ ⟨z, hz, rfl⟩
    exact hgD (ball_subset_closedBall hz)
  have hpre : IsPreconnected (g '' ball 0 1) :=
    (convex_ball (0 : ℂ) 1).isPreconnected.image g hgb
  refine hpre.subset_closure ?_ ?_
  · intro y hy
    refine ⟨hsub hy, fun hfr => hfr.2 ?_⟩
    exact interior_maximal hsub hO hy
  · rintro y ⟨hy, -⟩
    have hz := hhD hy
    have hzc : h y ∈ closure (ball (0 : ℂ) 1) := by
      rw [closure_ball (0 : ℂ) one_ne_zero]
      exact hz
    have hwithin : ContinuousWithinAt g (ball 0 1) (h y) :=
      (hg (h y) hz).mono ball_subset_closedBall
    have := hwithin.mem_closure_image hzc
    rwa [hl hy] at this

/-- A connected set that misses the frontier of a closed set lies in it or misses it. -/
theorem subset_or_disjoint_of_frontier {X A : Set S} (hX : IsClosed X) (hA : IsPreconnected A)
    (hdis : Disjoint A (frontier X)) : A ⊆ X ∨ Disjoint A X := by
  have hcov : A ⊆ interior X ∪ Xᶜ := by
    intro y hy
    by_cases hyX : y ∈ X
    · refine Or.inl ?_
      by_contra hi
      exact disjoint_left.mp hdis hy ⟨subset_closure hyX, hi⟩
    · exact Or.inr hyX
  by_cases hm : (A ∩ X).Nonempty
  · left
    obtain ⟨x, hxA, hxX⟩ := hm
    have hxi : x ∈ interior X := (hcov hxA).resolve_right fun h => h hxX
    intro y hy
    by_contra hyX
    obtain ⟨z, -, hz₁, hz₂⟩ := hA _ _ isOpen_interior hX.isOpen_compl hcov ⟨x, hxA, hxi⟩ ⟨y, hy,
      hyX⟩
    exact hz₂ (interior_subset hz₁)
  · exact Or.inr (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hm))

/-- The edges of a walk of a drawing are edges of the drawing. -/
theorem mem_E_of_mem_edges {N : Drawing S} {u v : S} (W : GraphWalk N.toGraph u v) {e : Set S}
    (he : e ∈ W.edges) : e ∈ N.E := by
  induction W with
  | nil => exact absurd he List.not_mem_nil
  | cons h r ih =>
    rcases List.mem_cons.mp he with rfl | h'
    · exact h.1
    · exact ih h'

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
    · exact GraphMinor.GM11.IsLineWithEnds.union hline (ih hnd.2 hyb) hcap

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

/-- Two lines with the same two ends and nothing else in common form an `O`-arc. -/
theorem isOArc_union [T2Space S] {L₁ L₂ : Set S} {a b : S} (h₁ : IsLineWithEnds L₁ a b)
    (h₂ : IsLineWithEnds L₂ a b) (hcap : L₁ ∩ L₂ ⊆ {a, b}) : IsOArc (L₁ ∪ L₂) := by
  obtain ⟨f₁, a₁, b₁⟩ := h₁
  obtain ⟨f₂, a₂, b₂⟩ := h₂
  let I := unitInterval
  -- The loop that runs along `L₁` and back along `L₂`.
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

end GraphMinor.GM11
