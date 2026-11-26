/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.LocalCone
public import LeanPool.GraphMinor.Surface.EdgeLens
public import LeanPool.GraphMinor.Surface.Fan

/-!
# Star-shaped discs around a vertex

Near a point of a closed surface a drawing is a finite set of rays. For this we use the polar charts
of
Graph Minors XI (`GM11.IsPolar`), which that paper builds at a vertex with at least two half-edges
and at
a point of an edge. We add the vertices with fewer half-edges (`exists_isPolar_of_vertex`), so that
every
vertex has a polar chart.

A round disc of a polar chart is a *star disc* (`IsStarDisc`): each closed union of atoms of the
drawing
that meets the disc in a point `y` holds a connected set from `y` to the centre, which stays inside
the
disc after it leaves `y`. This is all that we use. From it we read how lines and `O`-arcs of the
drawing
cross the disc (`exists_ray`, `exists_chord`). They are used for Graph Minors VII, (3.4), claim (1)
(page 220), which thickens a forest to a family of discs.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 unitInterval



variable {S : Type} [TopologicalSpace S]

/-- A strip chart around an arc of a closed surface. -/
theorem exists_stripChart_of_arc (hS : IsClosedSurface S) {a : I → S} (ha : IsArcMap a) :
    ∃ (O : Set ℂ) (K : ℂ → S) (θ : I → ℝ), StripChart O K ∧ Continuous θ ∧ StrictMono θ ∧
      ∀ t, (θ t : ℂ) ∈ O ∧ K (θ t) = a t := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have : T2Space S := hS.2.1
  obtain ⟨D₀, hD₀, hs⟩ := exists_disc_of_arc hS ha
  obtain ⟨h, g, cc⟩ := hD₀.exists_isChart
  have hbc : BallChart 1 (g '' ball 0 1) h g := by
    refine ⟨cc.isOpen_image_ball hman, cc.hc.mono ?_, cc.gc.mono ball_subset_closedBall, ?_, ?_,
      ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact cc.gm (ball_subset_closedBall hz)
    · rintro _ ⟨z, hz, rfl⟩
      rwa [cc.hg (ball_subset_closedBall hz)]
    · exact fun z hz => ⟨z, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      rw [cc.hg (ball_subset_closedBall hz)]
    · exact fun z hz => cc.hg (ball_subset_closedBall hz)
  have hU : range a ⊆ g '' ball 0 1 := by
    rw [← cc.discInt_eq]
    exact hs
  exact exists_stripChart hman hbc ha hU

/-- The plane of the closed disc, read as the complex numbers. -/
noncomputable def toC (x : ClosedUnitDisc) : ℂ := planeOf.symm x.1

theorem continuous_toC : Continuous toC :=
  planeOf.symm.continuous.comp continuous_subtype_val

theorem norm_toC (x : ClosedUnitDisc) : ‖toC x‖ ≤ 1 := by
  rw [toC, LinearIsometryEquiv.norm_map]
  exact mem_closedBall_zero_iff.mp x.2

theorem toC_injective : Function.Injective toC := fun _x _y h =>
  Subtype.ext (planeOf.symm.injective h)

theorem toC_discScale (c : I) (x : ClosedUnitDisc) : toC (discScale c x) = (c.1 : ℂ) * toC x := by
  simp [toC, discScale, map_smul]

theorem toC_centre : toC polarCentre = 0 := by simp [toC, polarCentre]

theorem exists_toC_eq {z : ℂ} (hz : ‖z‖ ≤ 1) : ∃ x, toC x = z :=
  ⟨⟨planeOf z, by simpa [ClosedUnitDisc] using hz⟩, by simp [toC]⟩

/-- A round disc of a chart in which the drawing is empty, except for a part of one atom on the
segment
to the left of the centre. -/
theorem exists_polar_of_chart (Γ : Drawing S) {O : Set ℂ} {K : ℂ → S}
  (hK : StripChart O K) {x₀ : ℝ} {ε : ℝ}
    (hε : 0 < ε) (hO : closedBall (x₀ : ℂ) ε ⊆ O) {a : Set S} (ha : a ∈ Γ.A)
    (hleft : ∀ s : ℝ, -ε ≤ s → s < 0 → K ((x₀ + s : ℝ) : ℂ) ∈ a)
    (hoff : ∀ z ∈ closedBall (x₀ : ℂ) ε, ¬ (z.im = 0 ∧ z.re ≤ x₀) → K z ∉ Γ.U) : ∃ Φ, IsPolar Γ
      (K x₀) Φ := by
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  let f : ClosedUnitDisc → ℂ := fun x => (x₀ : ℂ) + ε * toC x
  have hf : Continuous f := by
    have := continuous_toC
    fun_prop
  have hfm : ∀ x, f x ∈ closedBall (x₀ : ℂ) ε := fun x => by
    rw [mem_closedBall, dist_eq_norm]
    simp only [f, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith [norm_toC x]
  have hfi : Function.Injective f := fun x y h =>
    toC_injective (mul_left_cancel₀ hεc (add_left_cancel h))
  have hΦc : Continuous fun x => K (f x) := hK.hc.comp_continuous hf fun x => hO (hfm x)
  refine ⟨⟨fun x => K (f x), hΦc⟩, fun x y h => hfi (hK.hi (hO (hfm x)) (hO (hfm y)) h), ?_, ?_, ?_⟩
  · simp [f, toC_centre]
  · have hsub : K '' ball (x₀ : ℂ) ε ⊆ range fun x => K (f x) := by
      rintro _ ⟨z, hz, rfl⟩
      have h1 : ‖(z - x₀) / ε‖ ≤ 1 := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, div_le_one hε]
        rw [← dist_eq_norm]
        exact (mem_ball.mp hz).le
      obtain ⟨x, hx⟩ := exists_toC_eq h1
      refine ⟨x, ?_⟩
      simp only [f, hx]
      congr 1
      field_simp
      ring
    exact interior_maximal hsub (hK.ho _ isOpen_ball (ball_subset_closedBall.trans hO)) ⟨x₀,
      mem_ball_self hε, rfl⟩
  · intro x hx c hc
    have hne : toC x ≠ 0 := fun h => hx (toC_injective (h.trans toC_centre.symm))
    have hsc : f (discScale c x) = (x₀ : ℂ) + ε * ((c.1 : ℂ) * toC x) := by
      simp only [f, toC_discScale]
    change ∃ a ∈ Γ.A, K (f x) ∈ a ∧ K (f (discScale c x)) ∈ a
    by_cases hl : (toC x).im = 0 ∧ (toC x).re < 0
    · -- Both points lie on the left segment.
      have hre : toC x = (((toC x).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hl.1])
      have hn : -1 ≤ (toC x).re := by
        have := (Complex.abs_re_le_norm (toC x)).trans (norm_toC x)
        exact (abs_le.mp this).1
      have hc1 := c.2.2
      have hc0 : (0 : ℝ) < c.1 := hc
      have h1 : f x = ((x₀ + ε * (toC x).re : ℝ) : ℂ) := by
        simp only [f]
        rw [hre]
        push_cast
        simp
      have h2 : f (discScale c x) = ((x₀ + ε * (c.1 * (toC x).re) : ℝ) : ℂ) := by
        rw [hsc, hre]
        push_cast
        simp
      have hcr : (toC x).re ≤ c.1 * (toC x).re := by nlinarith [hl.2]
      have hcn : c.1 * (toC x).re < 0 := mul_neg_of_pos_of_neg hc0 hl.2
      have hn1 : -ε ≤ ε * (toC x).re := by nlinarith
      refine ⟨a, ha, ?_, ?_⟩
      · rw [h1]
        exact hleft _ hn1 (mul_neg_of_pos_of_neg hε hl.2)
      · rw [h2]
        exact hleft _ (by nlinarith) (mul_neg_of_pos_of_neg hε hcn)
    · -- Both points lie on a segment that misses the drawing.
      let seg : ℝ → ℂ := fun u => (x₀ : ℂ) + ε * ((u : ℂ) * toC x)
      have hsc' : Continuous seg := by fun_prop
      have hc0 : (0 : ℝ) < c.1 := hc
      have hsm : ∀ u ∈ Icc c.1 1, seg u ∈ closedBall (x₀ : ℂ) ε := fun u hu => by
        rw [mem_closedBall, dist_eq_norm]
        simp only [seg, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hε]
        have hu0 : 0 ≤ u := hc0.le.trans hu.1
        rw [abs_of_nonneg hu0]
        have := norm_toC x
        have h4 : u * ‖toC x‖ ≤ 1 := by nlinarith [hu.2, norm_nonneg (toC x)]
        nlinarith
      have hsoff : ∀ u ∈ Icc c.1 1, K (seg u) ∉ Γ.U := fun u hu => by
        refine hoff _ (hsm u hu) fun hz => ?_
        have hu0 : 0 < u := hc0.trans_le hu.1
        have him : (seg u).im = ε * (u * (toC x).im) := by simp [seg]
        have hre : (seg u).re = x₀ + ε * (u * (toC x).re) := by simp [seg]
        have h1 : (toC x).im = 0 := by
          have := hz.1
          rw [him] at this
          have h2 := mul_ne_zero hε.ne' hu0.ne'
          by_contra h3
          exact mul_ne_zero h2 h3 (by rw [mul_assoc]; exact this)
        have h2 : (toC x).re ≤ 0 := by
          have := hz.2
          rw [hre] at this
          by_contra h3
          have := mul_pos hε (mul_pos hu0 (not_le.mp h3))
          linarith
        rcases h2.lt_or_eq with h3 | h3
        · exact hl ⟨h1, h3⟩
        · exact hne (Complex.ext (by simpa using h3) (by simpa using h1))
      have hcont : ContinuousOn (fun u => K (seg u)) (Icc c.1 1) :=
        hK.hc.comp hsc'.continuousOn fun u hu => hO (hsm u hu)
      have hpre : IsPreconnected ((fun u => K (seg u)) '' Icc c.1 1) := isPreconnected_Icc.image _
        hcont
      have h1m : (1 : ℝ) ∈ Icc c.1 1 := ⟨c.2.2, le_rfl⟩
      have hcm : c.1 ∈ Icc c.1 1 := ⟨le_rfl, c.2.2⟩
      have e1 : K (seg 1) = K (f x) := by simp [seg, f]
      have e2 : K (seg c.1) = K (f (discScale c x)) := by rw [hsc]
      obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (Γ := Γ) (hsoff 1 h1m)
      have hsub := subset_region hr hpre
        (disjoint_left.mpr fun _ ⟨u, hu, e⟩ => e ▸ hsoff u hu) (mem_image_of_mem _ h1m) hxr
      refine ⟨r, Or.inr hr, ?_, ?_⟩
      · rw [← e1]
        exact hxr
      · rw [← e2]
        exact hsub (mem_image_of_mem _ hcm)

/-- A polar chart at a vertex with no half-edges or one half-edge. -/
theorem exists_isPolar_of_few (hS : IsClosedSurface S) {Γ : Drawing S} {γ : Set S → I → S}
  (hγ : EdgePar Γ γ) {v : S}
    (hv : v ∈ Γ.V) (h2 : ¬ 2 ≤ Nat.card (halfEdges Γ γ v)) : ∃ Φ, IsPolar Γ v Φ := by
  classical
  have : T2Space S := hS.2.1
  have hfinH : Finite (halfEdges Γ γ v) := (finite_halfEdges Γ γ v).to_subtype
  have hss : Subsingleton (halfEdges Γ γ v) := Finite.card_le_one_iff_subsingleton.mp (by omega)
  rcases isEmpty_or_nonempty (halfEdges Γ γ v) with h0 | ⟨⟨k⟩⟩
  · -- No half-edges: a small round disc misses the rest of the drawing.
    have hno : ∀ g ∈ Γ.E, v ∉ closure g := by
      intro g hg hzg
      obtain ⟨b, hb⟩ := exists_end_eq hγ hg hv hzg
      exact h0.false ⟨(g, b), hg, hb⟩
    let P : Set S := (Γ.V \ {v}) ∪ ⋃ g ∈ Γ.E, closure g
    have hP : IsClosed P := (Γ.finite_V.subset sdiff_subset).isClosed.union
      (Γ.finite_edges.isClosed_biUnion fun _ _ => isClosed_closure)
    have hvP : v ∉ P := by
      rintro (h | h)
      · exact h.2 rfl
      · obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp h
        exact hno g hg hzg
    have hUP : Γ.U ⊆ P ∪ {v} := by
      intro x hx
      rw [Γ.U_eq] at hx
      rcases hx with h | h
      · by_cases hxv : x = v
        · exact Or.inr hxv
        · exact Or.inl (Or.inl ⟨h, hxv⟩)
      · exact Or.inl (Or.inr h)
    obtain ⟨U, h, g, c, hUsub, hy⟩ := (hS.2.2 v).exists_ballChart hP.isOpen_compl hvP (R := 2)
      (by norm_num)
    have hK : StripChart (ball 0 2) g := ⟨isOpen_ball, c.gc, fun x hx y hy e => by
      rw [← c.hg hx, ← c.hg hy, e], fun W hW hsub => c.isOpen_image hW hsub⟩
    have hsub : closedBall ((0 : ℝ) : ℂ) 1 ⊆ ball 0 2 := by
      simpa using closedBall_subset_ball (x := (0 : ℂ)) (by norm_num : (1 : ℝ) < 2)
    have hoff : ∀ z ∈ closedBall ((0 : ℝ) : ℂ) 1, z ≠ 0 → g z ∉ Γ.U := fun z hz hz0 hU => by
      rcases hUP hU with h1 | h1
      · exact hUsub (c.gm (hsub hz)) h1
      · have h3 : g z = g 0 := h1.trans hy.symm
        exact hz0 (hK.hi (hsub hz) (by simp) h3)
    have hmem : ∀ s : ℝ, -1 ≤ s → s < 0 → ((((0 : ℝ) + s : ℝ) : ℂ)) ∈ closedBall ((0 : ℝ) : ℂ) 1 ∧
        ((((0 : ℝ) + s : ℝ) : ℂ)) ≠ 0 := fun s h1 h3 => by
      refine ⟨?_, ?_⟩
      · simp [abs_le]
        constructor <;> linarith
      · simpa using h3.ne
    have hcont : ContinuousOn (fun s : ℝ => g (((0 : ℝ) + s : ℝ) : ℂ)) (Ico (-1) 0) :=
      hK.hc.comp (by fun_prop) fun s hs => hsub (hmem s hs.1 hs.2).1
    have hpre : IsPreconnected ((fun s : ℝ => g (((0 : ℝ) + s : ℝ) : ℂ)) '' Ico (-1) 0) :=
      isPreconnected_Ico.image _ hcont
    have hm1 : (-1 : ℝ) ∈ Ico (-1 : ℝ) 0 := ⟨le_rfl, by norm_num⟩
    obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (Γ := Γ) (hoff _ (hmem (-1) le_rfl
      (by norm_num)).1 (hmem (-1) le_rfl (by norm_num)).2)
    have hsr := subset_region hr hpre (disjoint_left.mpr fun _ ⟨s, hs, e⟩ =>
      e ▸ hoff _ (hmem s hs.1 hs.2).1 (hmem s hs.1 hs.2).2) (mem_image_of_mem _ hm1) hxr
    obtain ⟨Φ, hΦ⟩ := exists_polar_of_chart Γ hK one_pos hsub (a := r) (Or.inr hr)
      (fun s h1 h3 => hsr (mem_image_of_mem _ ⟨h1, h3⟩)) (fun z hz hn => hoff z hz fun e => hn
        (by simp [e]))
    refine ⟨Φ, ?_⟩
    have e : g ((0 : ℝ) : ℂ) = v := by simpa using hy
    rwa [e] at hΦ
  · -- One half-edge: straighten the edge and take a round disc at its end.
    obtain ⟨⟨e, b⟩, he, hb⟩ := k
    have hbe : e ∈ Γ.E := he
    have hother : γ e (endOf (!b)) ≠ v := fun h => by
      have := congrArg (fun k : halfEdges Γ γ v => k.1.2) (hss.elim ⟨(e, !b), hbe, h⟩ ⟨(e, b), hbe,
        hb⟩)
      cases b <;> simp at this
    let P : Set S := (Γ.V \ {v}) ∪ ⋃ g ∈ Γ.E \ {e}, closure g
    have hP : IsClosed P := (Γ.finite_V.subset sdiff_subset).isClosed.union
      ((Γ.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)
    have hvP : v ∉ P := by
      rintro (h | h)
      · exact h.2 rfl
      · obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp h
        obtain ⟨b', hb'⟩ := exists_end_eq hγ hg.1 hv hzg
        have := congrArg (fun k : halfEdges Γ γ v => k.1.1) (hss.elim ⟨(g, b'), hg.1, hb'⟩ ⟨(e, b),
          hbe, hb⟩)
        exact hg.2 this
    let f : I → I := fun t => if b then t else σ t
    have hfc : Continuous f := by
      cases b
      · have e1 : f = σ := by funext t; simp [f]
        rw [e1]
        exact continuous_symm
      · have e1 : f = id := by funext t; simp [f]
        rw [e1]
        exact continuous_id
    have hfi : Function.Injective f := by
      cases b
      · have e1 : f = σ := by funext t; simp [f]
        rw [e1]
        exact symm_bijective.injective
      · have e1 : f = id := by funext t; simp [f]
        rw [e1]
        exact Function.injective_id
    have hf1 : f 1 = endOf b := by cases b <;> simp [f, endOf]
    have hf0 : f 0 = endOf (!b) := by cases b <;> simp [f, endOf]
    have hfI : ∀ t ∈ Ioo (0 : I) 1, f t ∈ Ioo (0 : I) 1 := fun t ht => by
      cases b
      · have e1 : f t = σ t := by simp [f]
        rw [e1]
        have h1 : (t : ℝ) < 1 := ht.2
        have h0 : (0 : ℝ) < t := ht.1
        exact ⟨Subtype.coe_lt_coe.mp (show (0 : ℝ) < 1 - t by linarith),
          Subtype.coe_lt_coe.mp (show (1 : ℝ) - t < 1 by linarith)⟩
      · simpa [f] using ht
    let a : I → S := fun t => γ e (f t)
    have hac : Continuous a := (hγ.cont e hbe).comp hfc
    have ha1 : a 1 = v := by simp only [a, hf1, hb]
    have ha0 : a 0 ≠ v := by simp only [a, hf0]; exact hother
    have hmid : ∀ t ∈ Ioo (0 : I) 1, a t ∈ e := fun t ht => by
      have := mem_image_of_mem (γ e) (hfI t ht)
      rwa [hγ.image e hbe] at this
    have hendV : ∀ t : I, t = 0 ∨ t = 1 → a t ∈ Γ.V := by
      rintro t (rfl | rfl)
      · simp only [a, hf0]
        cases !b
        · exact hγ.zero e hbe
        · exact hγ.one e hbe
      · rw [ha1]
        exact hv
    have hcases : ∀ t : I, t = 0 ∨ t = 1 ∨ t ∈ Ioo (0 : I) 1 := fun t => by
      by_cases h0 : t = 0
      · exact .inl h0
      by_cases h1 : t = 1
      · exact .inr (.inl h1)
      · exact .inr (.inr ⟨unitInterval.pos_iff_ne_zero.mpr h0, unitInterval.lt_one_iff_ne_one.mpr
          h1⟩)
    have hnotV : ∀ t ∈ Ioo (0 : I) 1, a t ∉ Γ.V := fun t ht => (he.2.1 (hmid t ht)).2
    have hai : IsArcMap a := by
      refine ⟨hac, fun s t hst => ?_⟩
      rcases hcases s with rfl | rfl | hs <;> rcases hcases t with rfl | rfl | ht
      · rfl
      · rw [ha1] at hst
        exact (ha0 hst).elim
      · exact (hnotV t ht (hst ▸ hendV 0 (.inl rfl))).elim
      · rw [ha1] at hst
        exact (ha0 hst.symm).elim
      · rfl
      · exact (hnotV t ht (hst ▸ hendV 1 (.inr rfl))).elim
      · exact (hnotV s hs (hst.symm ▸ hendV 0 (.inl rfl))).elim
      · exact (hnotV s hs (hst.symm ▸ hendV 1 (.inr rfl))).elim
      · exact hfi ((hγ.inj e hbe) (hfI s hs) (hfI t ht) hst)
    have hUP : Γ.U ⊆ P ∪ range a := by
      have hcl : closure e ⊆ range a := by
        refine closure_minimal (fun x hx => ?_) (isCompact_range hac).isClosed
        rw [← hγ.image e hbe] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        have hft : f (f t) = t := by
          cases b <;> simp [f]
        exact ⟨f t, by simp only [a, hft]⟩
      intro x hx
      rw [Γ.U_eq] at hx
      rcases hx with h | h
      · by_cases hxv : x = v
        · exact Or.inr ⟨1, ha1.trans hxv.symm⟩
        · exact Or.inl (Or.inl ⟨h, hxv⟩)
      · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h
        by_cases hge : g = e
        · exact Or.inr (hcl (hge ▸ hxg))
        · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨g, ⟨hg, hge⟩, hxg⟩))
    obtain ⟨O, K, θ, hK, hθc, hθm, hθ⟩ := exists_stripChart_of_arc hS hai
    have hN : IsOpen (O ∩ K ⁻¹' Pᶜ) := hK.hc.isOpen_inter_preimage hK.isOpen hP.isOpen_compl
    have hx₀ : ((θ 1 : ℝ) : ℂ) ∈ O ∩ K ⁻¹' Pᶜ := ⟨(hθ 1).1, by
      change K _ ∉ P
      rw [(hθ 1).2, ha1]
      exact hvP⟩
    obtain ⟨ε₀, hε₀, hb₀⟩ := Metric.isOpen_iff.mp hN _ hx₀
    have hlt : θ 0 < θ 1 := hθm (by simp)
    set ε : ℝ := min (ε₀ / 2) ((θ 1 - θ 0) / 2) with hεd
    have hε : 0 < ε := lt_min (by linarith) (by linarith)
    have hε1 : ε ≤ ε₀ / 2 := min_le_left _ _
    have hε2 : ε ≤ (θ 1 - θ 0) / 2 := min_le_right _ _
    have hsub : closedBall ((θ 1 : ℝ) : ℂ) ε ⊆ O ∩ K ⁻¹' Pᶜ :=
      (closedBall_subset_ball (by linarith)).trans hb₀
    obtain ⟨Φ, hΦ⟩ := exists_polar_of_chart Γ hK hε (x₀ := θ 1) (fun z hz => (hsub hz).1) (a := e)
      (Or.inl (Or.inr hbe))
      (fun s h1 h3 => by
        obtain ⟨t, ht⟩ : θ 1 + s ∈ range θ :=
          mem_range_of_exists_le_of_exists_ge hθc ⟨0, by linarith⟩ ⟨1, by linarith⟩
        rw [← ht, (hθ t).2]
        refine hmid t ⟨?_, ?_⟩
        · exact hθm.lt_iff_lt.mp (by rw [ht]; linarith)
        · exact hθm.lt_iff_lt.mp (by rw [ht]; linarith))
      (fun z hz hn hU => by
        rcases hUP hU with h1 | ⟨t, ht⟩
        · exact (hsub hz).2 h1
        · rw [← (hθ t).2] at ht
          have hzt : z = (θ t : ℂ) := hK.hi (hsub hz).1 (hθ t).1 ht.symm
          refine hn ⟨by simp [hzt], ?_⟩
          rw [hzt, Complex.ofReal_re]
          exact hθm.monotone (le_one t))
    refine ⟨Φ, ?_⟩
    rwa [(hθ 1).2, ha1] at hΦ

/-- Every vertex of a drawing in a closed surface has a polar chart. -/
theorem exists_isPolar_of_vertex (hS : IsClosedSurface S) (Γ : Drawing S) {v : S} (hv : v ∈ Γ.V) :
    ∃ Φ, IsPolar Γ v Φ := by
  have : T2Space S := hS.2.1
  have hne : Nonempty S := ⟨v⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  by_cases h2 : 2 ≤ Nat.card (halfEdges Γ γ v)
  · exact exists_isPolar_of_sectors hS hγ hv h2
  · exact exists_isPolar_of_few hS hγ hv h2

/-- A closed disc `R` around `v` in which each closed union of atoms of `Γ` is a star at `v`. -/
structure IsStarDisc (Γ : Drawing S) (v : S) (R : Set S) : Prop where
  disc : IsClosedDisc R
  mem : v ∈ discInt R
  star : ∀ X, IsClosed X → IsGammaNice Γ X → ∀ y ∈ R ∩ X, ∃ C, IsPreconnected C ∧ C ⊆ X ∧ y ∈ C
    ∧ v ∈ C ∧
    C \ {y} ⊆ discInt R

/-- Each vertex has a star disc in each of its neighbourhoods. -/
theorem exists_starDisc (hS : IsClosedSurface S) (Γ : Drawing S) {v : S} (hv : v ∈ Γ.V) {W : Set S}
  (hW : IsOpen W)
    (hvW : v ∈ W) : ∃ R, IsStarDisc Γ v R ∧ R ⊆ W := by
  have : T2Space S := hS.2.1
  obtain ⟨Φ, hΦ⟩ := exists_isPolar_of_vertex hS Γ hv
  have hN : IsOpen (Φ ⁻¹' W) := hW.preimage Φ.continuous
  have h0 : polarCentre ∈ Φ ⁻¹' W := by
    change Φ _ ∈ W
    rw [hΦ.centre]
    exact hvW
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hN _ h0
  set r : ℝ := min (ε / 2) (1 / 2) with hrd
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hr1 : r ≤ 1 / 2 := min_le_right _ _
  have hr2 : r ≤ ε / 2 := min_le_left _ _
  let c : I := ⟨r, hr.le, by linarith⟩
  have hc0 : (c.1 : ℝ) ≠ 0 := hr.ne'
  let ψ : ClosedUnitDisc → S := fun x => Φ (discScale c x)
  have hψc : Continuous ψ := Φ.continuous.comp (continuous_discScale.comp
    (continuous_const.prodMk continuous_id))
  have hψi : Function.Injective ψ := fun x y h => by
    have h1 := hΦ.inj h
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext (smul_right_injective _ hc0 h2)
  have hemb : IsEmbedding ψ := (hψc.isClosedEmbedding hψi).isEmbedding
  let e : ClosedUnitDisc ≃ₜ range ψ := hemb.toHomeomorph
  have hD : IsClosedDisc (range ψ) := ⟨e⟩
  have hbd : discBd (range ψ) = (fun x : ClosedUnitDisc => (e x).1) '' {x | ‖x.1‖ = 1} := by
    have h := disc_boundary (range ψ) e
    rw [h]
    have hu : ∀ x : ClosedUnitDisc, x.1 ∈ UnitCircle ↔ ‖x.1‖ = 1 := fun x => by simp [UnitCircle]
    ext z
    simp only [mem_image, mem_ofPred_eq, hu]
  have hint : ∀ x : ClosedUnitDisc, ‖x.1‖ < 1 → ψ x ∈ discInt (range ψ) := fun x hx => by
    refine ⟨⟨x, rfl⟩, ?_⟩
    rw [hbd]
    rintro ⟨y, hy, hxy⟩
    have : y = x := e.injective (Subtype.ext hxy)
    rw [this] at hy
    exact hx.ne hy
  have hnorm : ∀ (d : I) (x : ClosedUnitDisc), d < 1 → ‖(discScale d x).1‖ < 1 := fun d x hd => by
    have hx : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
    have hd0 := d.2.1
    have hd1 : (d.1 : ℝ) < 1 := hd
    simp only [discScale, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd0]
    nlinarith [norm_nonneg x.1]
  have hmul : ∀ (d : I) (x : ClosedUnitDisc), discScale c (discScale d x) = discScale d
    (discScale c x) := fun d x =>
    Subtype.ext (smul_comm _ _ _)
  refine ⟨range ψ, ⟨hD, ?_, ?_⟩, ?_⟩
  · have e0 : ψ polarCentre = v := by
      have : discScale c polarCentre = polarCentre := Subtype.ext (by simp [discScale, polarCentre])
      simp only [ψ, this, hΦ.centre]
    rw [← e0]
    exact hint _ (by simp [polarCentre])
  · rintro X hXc hXn y ⟨⟨x, rfl⟩, hyX⟩
    let C : Set S := (fun d : I => ψ (discScale d x)) '' univ
    have hcont : Continuous fun d : I => ψ (discScale d x) :=
      hψc.comp (continuous_discScale.comp (continuous_id.prodMk continuous_const))
    refine ⟨C, isPreconnected_univ.image _ hcont.continuousOn, ?_, ⟨1, mem_univ _, ?_⟩, ⟨0,
      mem_univ _, ?_⟩, ?_⟩
    · rintro _ ⟨d, -, rfl⟩
      change Φ _ ∈ X
      rw [hmul]
      exact hΦ.star hXc hXn hyX d
    · simp only [discScale_one]
    · simp only [discScale_zero, ψ]
      have : discScale c polarCentre = polarCentre := Subtype.ext (by simp [discScale, polarCentre])
      rw [this, hΦ.centre]
    · rintro _ ⟨⟨d, -, rfl⟩, hne⟩
      refine hint _ (hnorm d x ?_)
      refine lt_of_le_of_ne (le_one d) fun hd => hne ?_
      simp only [hd, discScale_one, mem_singleton_iff]
  · rintro _ ⟨x, rfl⟩
    refine hb ?_
    rw [mem_ball, Subtype.dist_eq, dist_eq_norm]
    have hx : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
    have : ‖((discScale c x).1 - polarCentre.1)‖ = r * ‖x.1‖ := by
      simp [discScale, polarCentre, norm_smul, abs_of_pos hr, c]
    change ‖((discScale c x).1 - polarCentre.1)‖ < ε
    rw [this]
    nlinarith [norm_nonneg x.1]

/-- Near a point other than `0`, an open set of the interval has smaller points. -/
theorem exists_lt_of_isOpen {O : Set I} (hO : IsOpen O) {t : I} (ht : t ∈ O)
  (h0 : 0 < t) : ∃ u, u < t ∧ u ∈ O := by
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hO t ht
  have h0' : (0 : ℝ) < t := h0
  set d : ℝ := min (ε / 2) t with hd
  have hd0 : 0 < d := lt_min (by linarith) h0'
  have hd1 : d ≤ ε / 2 := min_le_left _ _
  have hd2 : d ≤ t := min_le_right _ _
  refine ⟨⟨t - d, by linarith, by linarith [t.2.2]⟩, Subtype.coe_lt_coe.mp (by simpa using hd0),
    hb ?_⟩
  rw [mem_ball, Subtype.dist_eq, Real.dist_eq]
  simp only [sub_sub_cancel_left, abs_neg, abs_of_pos hd0]
  linarith

/-- A line split at a point, read off a parametrization. -/
theorem split_at [T2Space S] {a : I → S} (ha : IsArcMap a) {t : I} (h0 : 0 < t) (h1 : t < 1) :
    IsLineWithEnds (a '' Iic t) (a 0) (a t) ∧ IsLineWithEnds (a '' Ici t) (a t) (a 1) := by
  have h0' : (0 : ℝ) < t := h0
  have h1' : (t : ℝ) < 1 := h1
  have a1 := isArcMap_pieceA ha le_rfl h0' h1'.le
  have a2 := isArcMap_pieceA ha h0'.le h1' le_rfl
  have e1 : extI a 0 = a 0 := extI_coe a 0
  have e2 : extI a 1 = a 1 := extI_coe a 1
  have e3 : extI a t = a t := extI_coe a t
  have r1 : range (pieceA a 0 t) = a '' Iic t := by
    rw [range_pieceA a le_rfl h0'.le h1'.le]
    ext y
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr.1, hr.2.trans h1'.le⟩, hr.2, (extI_of_mem a ⟨hr.1, hr.2.trans h1'.le⟩).symm⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, ⟨r.2.1, hr⟩, extI_coe a r⟩
  have r2 : range (pieceA a t 1) = a '' Ici t := by
    rw [range_pieceA a h0'.le h1'.le le_rfl]
    ext y
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, h0'.le.trans hr.1, hr.2⟩, hr.1, (extI_of_mem a ⟨h0'.le.trans hr.1, hr.2⟩).symm⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, ⟨hr, r.2.2⟩, extI_coe a r⟩
  constructor
  · have := a1.isLineWithEnds
    rwa [pieceA_zero, pieceA_one, e1, e3, r1] at this
  · have := a2.isLineWithEnds
    rwa [pieceA_zero, pieceA_one, e2, e3, r2] at this

/-- **A line from outside to the centre of a star disc.** It enters the disc once. Here `Y` is the
rest of
a closed union of atoms `X` of the drawing, which may hold the connected sets to the centre. -/
theorem exists_ray_param (hS : IsClosedSurface S) {Γ : Drawing S} {R : Set S} {b : I → S}
  (h : IsStarDisc Γ (b 1) R) {X Y : Set S}
    (hb : IsArcMap b) (hw : b 0 ∉ R) (hXc : IsClosed X) (hXn : IsGammaNice Γ X) (hX : X
      = range b ∪ Y)
    (hY : IsClosed Y) (hLY : range b ∩ Y ⊆ {b 0, b 1}) :
    ∃ τ : I, 0 < τ ∧ τ < 1 ∧ (∀ t, b t ∈ R ↔ τ ≤ t) ∧ b τ ∈ discBd R ∧ ∀ t, τ < t → b t ∈ discInt R
      := by
  have ht2 : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hint : IsOpen (discInt R) := h.disc.isOpen_discInt hman
  have hRc : IsClosed R := h.disc.isClosed
  let T : Set I := b ⁻¹' R
  have hTc : IsClosed T := hRc.preimage hb.1
  have h1T : (1 : I) ∈ T := h.mem.1
  have hne : T.Nonempty := ⟨1, h1T⟩
  have hτ : sInf T ∈ T := hTc.csInf_mem hne (OrderBot.bddBelow T)
  set τ : I := sInf T with hτd
  have h0T : (0 : I) ∉ T := hw
  have hτ0 : 0 < τ := unitInterval.pos_iff_ne_zero.mpr fun e => h0T (e ▸ hτ)
  -- A point of the line in the disc: everything after it lies inside.
  have hafter : ∀ t ∈ T, ∀ u, t < u → b u ∈ discInt R := by
    intro t ht u htu
    by_cases hu1 : u = 1
    · rw [hu1]
      exact h.mem
    have hu1' : u < 1 := unitInterval.lt_one_iff_ne_one.mpr hu1
    have ht0 : 0 < t := unitInterval.pos_iff_ne_zero.mpr fun e => h0T (e ▸ ht)
    have hyX : b t ∈ X := hX ▸ Or.inl ⟨t, rfl⟩
    obtain ⟨C, hC, hCX, hyC, hvC, hCint⟩ := h.star X hXc hXn (b t) ⟨ht, hyX⟩
    have hCR : C ⊆ R := fun z hz => by
      by_cases hzy : z = b t
      · rw [hzy]
        exact ht
      · exact (hCint ⟨hz, hzy⟩).1
    suffices hbu : b u ∈ C from hCint ⟨hbu, fun e => htu.ne (hb.2 e.symm)⟩
    by_contra hbu
    have c1 : IsClosed (b '' Iic u) := (isClosed_Iic.isCompact.image hb.1).isClosed
    have c2 : IsClosed (b '' Ici u ∪ Y) := (isClosed_Ici.isCompact.image hb.1).isClosed.union hY
    have hcov : C ⊆ b '' Iic u ∪ (b '' Ici u ∪ Y) := fun z hz => by
      have hzX := hCX hz
      rw [hX] at hzX
      rcases hzX with ⟨r, rfl⟩ | hzY
      · rcases le_total r u with hr | hr
        · exact .inl ⟨r, hr, rfl⟩
        · exact .inr (.inl ⟨r, hr, rfl⟩)
      · exact .inr (.inr hzY)
    obtain ⟨z, hzC, hz1, hz2⟩ := isPreconnected_closed_iff.mp hC _ _ c1 c2 hcov ⟨_, hyC, ⟨t,
      htu.le, rfl⟩⟩
      ⟨_, hvC, .inl ⟨1, le_one u, rfl⟩⟩
    obtain ⟨r, hr, rfl⟩ := hz1
    rcases hz2 with ⟨r', hr', e⟩ | hzY
    · have e1 := hb.2 e
      rw [e1] at hr'
      have e2 : r = u := le_antisymm hr hr'
      rw [e2] at hzC
      exact hbu hzC
    · have hmem : b r ∈ ({b 0, b 1} : Set S) := hLY ⟨⟨r, rfl⟩, hzY⟩
      rcases hmem with e | e
      · have := hCR hzC
        rw [e] at this
        exact hw this
      · have e' : r = 1 := hb.2 e
        rw [e'] at hr
        exact absurd (lt_of_le_of_lt hr hu1') (lt_irrefl _)
  have hOo : IsOpen (b ⁻¹' discInt R) := hint.preimage hb.1
  have hτ1 : τ < 1 := by
    obtain ⟨u, hu, huO⟩ := exists_lt_of_isOpen hOo (t := 1) h.mem one_pos
    exact lt_of_le_of_lt (csInf_le (OrderBot.bddBelow T) (show b u ∈ R from huO.1)) hu
  have hT : ∀ t, b t ∈ R ↔ τ ≤ t := fun t => by
    constructor
    · exact fun ht => csInf_le (OrderBot.bddBelow T) ht
    · intro ht
      rcases ht.eq_or_lt with e | e
      · rw [← e]
        exact hτ
      · exact (hafter τ hτ t e).1
  have hp : b τ ∈ discBd R := by
    by_contra hn
    obtain ⟨u, hu, huO⟩ := exists_lt_of_isOpen hOo (t := τ) (show b τ ∈ discInt R from ⟨hτ, hn⟩) hτ0
    exact absurd ((hT u).mp huO.1) (not_le.mpr hu)
  exact ⟨τ, hτ0, hτ1, hT, hp, hafter τ hτ⟩

/-- The set form of `exists_ray_param`. -/
theorem exists_ray (hS : IsClosedSurface S) {Γ : Drawing S} {v : S} {R : Set S}
  (h : IsStarDisc Γ v R) {X Y L : Set S} {w : S}
    (hL : IsLineWithEnds L w v) (hw : w ∉ R) (hXc : IsClosed X) (hXn : IsGammaNice Γ X) (hX : X
      = L ∪ Y)
    (hY : IsClosed Y) (hLY : L ∩ Y ⊆ {w, v}) :
    ∃ p L₁ L₂, IsLineWithEnds L₁ w p ∧ IsLineWithEnds L₂ p v ∧ L₁ ∪ L₂ = L ∧ L₁ ∩ L₂ = {p} ∧ L₂
      = L ∩ R ∧
      p ∈ discBd R ∧ L₂ \ {p} ⊆ discInt R ∧ p ≠ w ∧ p ≠ v := by
  have ht2 : T2Space S := hS.2.1
  obtain ⟨b, hb, rfl, rfl, rfl⟩ := hL.exists_arc
  obtain ⟨τ, hτ0, hτ1, hT, hp, hafter⟩ := exists_ray_param hS h hb hw hXc hXn hX hY hLY
  obtain ⟨l1, l2⟩ := split_at hb hτ0 hτ1
  refine ⟨b τ, _, _, l1, l2, ?_, ?_, ?_, hp, ?_, fun e => hτ0.ne (hb.2 e).symm,
    fun e => hτ1.ne (hb.2 e)⟩
  · ext y
    constructor
    · rintro (⟨r, -, rfl⟩ | ⟨r, -, rfl⟩) <;> exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      rcases le_total r τ with hr | hr
      · exact .inl ⟨r, hr, rfl⟩
      · exact .inr ⟨r, hr, rfl⟩
  · ext y
    constructor
    · rintro ⟨⟨r, hr, rfl⟩, ⟨r', hr', e⟩⟩
      have e1 := hb.2 e
      rw [e1] at hr'
      have e2 : r = τ := le_antisymm hr hr'
      rw [e2]
      rfl
    · rintro rfl
      exact ⟨⟨τ, le_refl τ, rfl⟩, ⟨τ, le_refl τ, rfl⟩⟩
  · ext y
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, rfl⟩, (hT r).mpr hr⟩
    · rintro ⟨⟨r, rfl⟩, hr⟩
      exact ⟨r, (hT r).mp hr, rfl⟩
  · rintro _ ⟨⟨r, hr, rfl⟩, hne⟩
    rcases (show τ ≤ r from hr).eq_or_lt with e | e
    · exact (hne (by rw [e]; rfl)).elim
    · exact hafter r e

/-- **Two lines from outside to the centre of a star disc.** Two lines from `w` to `v` that make up
an
`O`-arc `F` of the drawing, with `w` outside the disc. Then `F` crosses the disc in one chord
through `v`. -/
theorem exists_chord (hS : IsClosedSurface S) {Γ : Drawing S} {v : S} {R : Set S}
  (h : IsStarDisc Γ v R) {F A₁ A₂ : Set S} {w : S}
    (h₁ : IsLineWithEnds A₁ w v) (h₂ : IsLineWithEnds A₂ w v) (hF : F = A₁ ∪ A₂) (hm : A₁ ∩ A₂
      = {w, v}) (hw : w ∉ R)
    (hFc : IsClosed F) (hFn : IsGammaNice Γ F) :
    ∃ s t ρ₁ ρ₂ B₁ B₂, IsLineWithEnds ρ₁ s v ∧ IsLineWithEnds ρ₂ t v ∧ IsLineWithEnds B₁ w s
      ∧ IsLineWithEnds B₂ w t ∧
      B₁ ∪ ρ₁ = A₁ ∧ B₂ ∪ ρ₂ = A₂ ∧ IsLineWithEnds (ρ₁ ∪ ρ₂) s t ∧ s ≠ t ∧ ρ₁ ∪ ρ₂ = F ∩ R ∧
      (ρ₁ ∪ ρ₂) ∩ discBd R = {s, t} := by
  have ht2 : T2Space S := hS.2.1
  have hc₁ : IsClosed A₁ := h₁.isCompact.isClosed
  have hc₂ : IsClosed A₂ := h₂.isCompact.isClosed
  obtain ⟨s, B₁, ρ₁, l₁, r₁, u₁, m₁, e₁, hsb, hi₁, hsw, hsv⟩ :=
    exists_ray hS h h₁ hw hFc hFn hF hc₂ (by rw [hm])
  obtain ⟨t, B₂, ρ₂, l₂, r₂, u₂, m₂, e₂, htb, hi₂, htw, htv⟩ :=
    exists_ray hS h h₂ hw hFc hFn (by rw [hF, union_comm]) hc₁ (by rw [inter_comm, hm])
  have hρ : ρ₁ ∩ ρ₂ = {v} := by
    ext y
    constructor
    · rintro ⟨h3, h4⟩
      have h5 : y ∈ A₁ ∩ A₂ := ⟨(e₁ ▸ h3 : y ∈ A₁ ∩ R).1, (e₂ ▸ h4 : y ∈ A₂ ∩ R).1⟩
      rw [hm] at h5
      rcases h5 with e | e
      · exact (hw (by rw [← e]; exact (e₁ ▸ h3 : y ∈ A₁ ∩ R).2)).elim
      · exact e
    · rintro rfl
      exact ⟨r₁.right_mem, r₂.right_mem⟩
  have hst : s ≠ t := fun e => by
    have : s ∈ ρ₁ ∩ ρ₂ := ⟨r₁.left_mem, e ▸ r₂.left_mem⟩
    rw [hρ] at this
    exact hsv this
  refine ⟨s, t, ρ₁, ρ₂, B₁, B₂, r₁, r₂, l₁, l₂, u₁, u₂, IsLineWithEnds.union r₁ r₂.symm hρ, hst,
    ?_, ?_⟩
  · rw [e₁, e₂, hF, union_inter_distrib_right]
  · ext y
    constructor
    · rintro ⟨h3 | h3, h4⟩
      · by_cases e : y = s
        · exact .inl e
        · exact ((disjoint_left.mp (show Disjoint (discInt R) (discBd R) from disjoint_sdiff_left)
            (hi₁ ⟨h3, e⟩)) h4).elim
      · by_cases e : y = t
        · exact .inr e
        · exact ((disjoint_left.mp (show Disjoint (discInt R) (discBd R) from disjoint_sdiff_left)
            (hi₂ ⟨h3, e⟩)) h4).elim
    · rintro (rfl | rfl)
      · exact ⟨.inl r₁.left_mem, hsb⟩
      · exact ⟨.inr r₂.left_mem, htb⟩

/-- A chord splits a closed disc, with the two arcs of the boundary as lines. -/
theorem disc_split [T2Space S] {D F : Set S} {s t : S} (hD : IsClosedDisc D) (hFD : F ⊆ D)
  (hst : s ≠ t)
    (hF : IsLineWithEnds F s t) (hb : F ∩ discBd D = {s, t}) :
    ∃ Δ₁ Δ₂ A₁ A₂, IsLineWithEnds A₁ s t ∧ IsLineWithEnds A₂ s t ∧ A₁ ∪ A₂ = discBd D ∧ A₁ ∩ A₂
      = {s, t} ∧
      IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧ Δ₁ ∪ Δ₂ = D ∧ Δ₁ ∩ Δ₂ = F ∧ discBd Δ₁ = A₁ ∪ F
        ∧ discBd Δ₂ = A₂ ∪ F ∧
      IsPreconnected (Δ₁ \ F) ∧ IsPreconnected (Δ₂ \ F) := by
  obtain ⟨c₁, c₂, Δ₁, Δ₂, hne, hc, d₁, d₂, hu, hi, b₁, b₂, hcc⟩ := disc_iArc D F s t hD hFD hst hF
    hb
  have hs : s ∈ discBd D := (hb ▸ (mem_insert s {t}) : s ∈ F ∩ discBd D).2
  have ht : t ∈ discBd D := (hb ▸ (Or.inr rfl : t ∈ ({s, t} : Set S)) : t ∈ F ∩ discBd D).2
  obtain ⟨a, b, hab, ha0, ha1, hr⟩ := hD.isOArc_discBd.exists_arcs hs ht hst
  have la : IsLineWithEnds (range a) s t := ha0 ▸ ha1 ▸ hab.arc_left.isLineWithEnds
  have lb : IsLineWithEnds (range b) s t := by
    have := hab.arc_right.isLineWithEnds
    rwa [hab.zero, hab.one, ha0, ha1] at this
  have hne' : ∀ {c : I → S}, IsArcMap c → c 0 = s → c 1 = t → (range c \ {s, t}).Nonempty
    := fun {c} hc h0 h1 =>
    ⟨c ⟨1 / 2, by norm_num, by norm_num⟩, ⟨_, rfl⟩, by
      rintro (e | e)
      · have := hc.2 (e.trans h0.symm)
        simpa using congrArg Subtype.val this
      · have := hc.2 (e.trans h1.symm)
        simpa using congrArg Subtype.val this⟩
  have hY : discBd D \ {s, t} = (range a \ {s, t}) ∪ (range b \ {s, t}) := by
    rw [← hr, union_sdiff_distrib]
  have hdis : Disjoint (range a \ {s, t}) (range b \ {s, t}) := disjoint_left.mpr fun y hy hy' => by
    obtain ⟨⟨r, rfl⟩, hn⟩ := hy
    obtain ⟨⟨r', e⟩, -⟩ := hy'
    rcases hab.meet r r' e.symm with ⟨h0, -⟩ | ⟨h1, -⟩
    · exact hn (.inl (by rw [h0, ha0]))
    · exact hn (.inr (by rw [h1, ha1]; rfl))
  have hPre : ∀ X ∈ componentsIn (D \ F), IsPreconnected X := fun X hX => by
    obtain ⟨x, -, rfl⟩ := hX
    exact isPreconnected_connectedComponentIn
  have hp₁ := hPre (Δ₁ \ F) (hcc ▸ Or.inl rfl)
  have hp₂ := hPre (Δ₂ \ F) (hcc ▸ Or.inr rfl)
  have hsF : s ∈ F := hF.left_mem
  have htF : t ∈ F := hF.right_mem
  have hadd : ∀ {L : Set S}, s ∈ L → t ∈ L → (L \ {s, t}) ∪ F = L ∪ F := fun {L} h1 h2 => by
    ext y
    constructor
    · rintro (⟨h3, -⟩ | h3)
      · exact .inl h3
      · exact .inr h3
    · rintro (h3 | h3)
      · by_cases hy : y ∈ ({s, t} : Set S)
        · rcases hy with rfl | rfl
          · exact .inr hsF
          · exact .inr htF
        · exact .inl ⟨h3, hy⟩
      · exact .inr h3
  have hmeet : range a ∩ range b = {s, t} := by
    ext y
    constructor
    · rintro ⟨⟨r, rfl⟩, ⟨r', e⟩⟩
      rcases hab.meet r r' e.symm with ⟨h0, -⟩ | ⟨h1, -⟩
      · exact .inl (by rw [h0, ha0])
      · exact .inr (by rw [h1, ha1]; rfl)
    · rintro (rfl | rfl)
      · exact ⟨la.left_mem, lb.left_mem⟩
      · exact ⟨la.right_mem, lb.right_mem⟩
  rcases comps_two hne hc hY hdis la.isPreconnected_diff lb.isPreconnected_diff
    (hne' hab.arc_left ha0 ha1)
    (hne' hab.arc_right (hab.zero.trans ha0) (hab.one.trans ha1)) with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine ⟨Δ₁, Δ₂, range a, range b, la, lb, hr, hmeet, d₁, d₂, hu, hi, ?_, ?_, hp₁, hp₂⟩
    · rw [b₁, e1, hadd la.left_mem la.right_mem]
    · rw [b₂, e2, hadd lb.left_mem lb.right_mem]
  · refine ⟨Δ₁, Δ₂, range b, range a, lb, la, by rw [union_comm, hr], by rw [inter_comm, hmeet],
      d₁, d₂, hu, hi, ?_, ?_, hp₁, hp₂⟩
    · rw [b₁, e1, hadd lb.left_mem lb.right_mem]
    · rw [b₂, e2, hadd la.left_mem la.right_mem]

/-- A connected set off the frontier of a closed set lies inside it or outside it. -/
theorem inside_or_outside {X B : Set S} (hX : IsPreconnected X) (hB : IsClosed B) (hf : Disjoint X
  (frontier B)) :
    X ⊆ interior B ∨ X ⊆ Bᶜ := by
  have hcov : X ⊆ interior B ∪ Bᶜ := fun x hx => by
    by_cases h1 : x ∈ B
    · refine .inl ?_
      by_contra h2
      exact disjoint_left.mp hf hx ⟨hB.closure_eq.symm ▸ h1, h2⟩
    · exact .inr h1
  have hdj : Disjoint (interior B) Bᶜ := disjoint_left.mpr fun x h1 h2 => h2 (interior_subset h1)
  exact hX.subset_or_subset isOpen_interior hB.isOpen_compl hdj hcov

/-- **The two sides of a chord.** Let the frontier of the closed set `B` meet the disc `D` exactly
in the
chord `F`, with `B` on both sides near a point of `F`. Then one side of `F` lies in `B`, and the
other misses
`B` off `F`. -/
theorem side_of_frontier (hS : IsClosedSurface S) {D F Δ₁ Δ₂ B : Set S} {p : S}
  (hD : IsClosedDisc D)
    (hu : Δ₁ ∪ Δ₂ = D) (_hi : Δ₁ ∩ Δ₂ = F) (hp₁ : IsPreconnected (Δ₁ \ F)) (hp₂ : IsPreconnected
      (Δ₂ \ F))
    (hB : IsClosed B) (hf : frontier B ∩ D = F) (_hpF : p ∈ F) (hpi : p ∈ discInt D)
      (hin : p ∈ closure (interior B))
    (hout : p ∈ closure Bᶜ) : (Δ₁ ⊆ B ∧ Disjoint (Δ₂ \ F) B) ∨ (Δ₂ ⊆ B ∧ Disjoint (Δ₁ \ F) B) := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hint : IsOpen (discInt D) := hD.isOpen_discInt hman
  have hFf : F ⊆ frontier B := fun x hx => (hf ▸ hx : x ∈ frontier B ∩ D).1
  have hFB : F ⊆ B := hFf.trans hB.frontier_subset
  have hoff : ∀ {X}, X ⊆ D \ F → Disjoint X (frontier B) := fun {X} hX
    => disjoint_left.mpr fun x hx hxf =>
    (hX hx).2 (hf ▸ ⟨hxf, (hX hx).1⟩)
  have h1 : Δ₁ \ F ⊆ D \ F := fun x hx => ⟨hu ▸ Or.inl hx.1, hx.2⟩
  have h2 : Δ₂ \ F ⊆ D \ F := fun x hx => ⟨hu ▸ Or.inr hx.1, hx.2⟩
  obtain ⟨z, hzD, hzB⟩ := mem_closure_iff.mp hin _ hint hpi
  obtain ⟨z', hz'D, hz'B⟩ := mem_closure_iff.mp hout _ hint hpi
  have hzF : z ∉ F := fun h => (hFf h).2 hzB
  have hz'F : z' ∉ F := fun h => hz'B (hFB h)
  have hclose : ∀ {Δ : Set S}, Δ \ F ⊆ interior B → Δ ⊆ B := fun {Δ} h x hx => by
    by_cases hxF : x ∈ F
    · exact hFB hxF
    · exact interior_subset (h ⟨hx, hxF⟩)
  have hdj : ∀ {Δ : Set S}, Δ \ F ⊆ Bᶜ → Disjoint (Δ \ F) B := fun h => disjoint_left.mpr fun x hx
    hxB => h hx hxB
  have hzm : z ∈ Δ₁ ∪ Δ₂ := hu ▸ hzD.1
  have hz'm : z' ∈ Δ₁ ∪ Δ₂ := hu ▸ hz'D.1
  rcases inside_or_outside hp₁ hB (hoff h1) with a | a <;> rcases inside_or_outside hp₂ hB
    (hoff h2) with b | b
  · rcases hz'm with h3 | h3
    · exact (hz'B (interior_subset (a ⟨h3, hz'F⟩))).elim
    · exact (hz'B (interior_subset (b ⟨h3, hz'F⟩))).elim
  · exact .inl ⟨hclose a, hdj b⟩
  · exact .inr ⟨hclose b, hdj a⟩
  · rcases hzm with h3 | h3
    · exact (a ⟨h3, hzF⟩ (interior_subset hzB)).elim
    · exact (b ⟨h3, hzF⟩ (interior_subset hzB)).elim

/-- A closed subset `X` of `U(Γ)` is a union of atoms, if the rest of `U(Γ)` lies in a closed set
that meets `X`
only in vertices. -/
theorem nice_of_cover {Γ : Drawing S} {X Y : Set S} (hX : IsClosed X) (hY : IsClosed Y)
  (hU : Γ.U ⊆ X ∪ Y) (hXU : X ⊆ Γ.U)
    (hV : X ∩ Y ⊆ Γ.V) : IsGammaNice Γ X := by
  refine ⟨(singleton '' (X ∩ Γ.V)) ∪ {e ∈ Γ.E | (e ∩ X).Nonempty}, ?_, ?_⟩
  · rintro a (⟨v, hv, rfl⟩ | ⟨he, -⟩)
    · exact Or.inl (Or.inl ⟨v, hv.2, rfl⟩)
    · exact Or.inl (Or.inr he)
  · ext x
    constructor
    · intro hx
      by_cases hxV : x ∈ Γ.V
      · exact ⟨{x}, .inl ⟨x, ⟨hx, hxV⟩, rfl⟩, rfl⟩
      · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem (hXU hx) hxV
        exact ⟨e, .inr ⟨he, x, hxe, hx⟩, hxe⟩
    · rintro ⟨a, (⟨v, hv, rfl⟩ | ⟨he, y, hye, hyX⟩), hxa⟩
      · rw [mem_singleton_iff.mp hxa]
        exact hv.1
      · have hpre : IsPreconnected a := he.2.2.1.isConnected.isPreconnected
        have hcov : a ⊆ X ∪ Y := fun z hz => hU (he.2.1 hz).1
        by_contra hxX
        have hxY : x ∈ Y := (hcov hxa).resolve_left hxX
        obtain ⟨z, hza, hz1, hz2⟩ := isPreconnected_closed_iff.mp hpre _ _ hX hY hcov ⟨y, hye, hyX⟩
          ⟨x, hxa, hxY⟩
        exact (he.2.1 hza).2 (hV ⟨hz1, hz2⟩)

/-- **The sides of a boundary in a star disc.** Let `v` be a point of the boundary of a closed disc
`A`, with
`w ∈ bd(A)` outside the star disc `R`. Then `bd(A)` is a chord of `R`, one side of it lies in `A`,
and the other
misses `A` off the chord. -/
theorem exists_disc_sides (hS : IsClosedSurface S) {Γ : Drawing S} {v : S} {R A : Set S}
  (h : IsStarDisc Γ v R) (hA : IsClosedDisc A)
    (hv : v ∈ discBd A) {w : S} (hwA : w ∈ discBd A) (hw : w ∉ R) (hn : IsGammaNice Γ (discBd A)) :
    ∃ ℓ s t Δ E c c', IsLineWithEnds ℓ s t ∧ s ≠ t ∧ ℓ = discBd A ∩ R ∧ IsClosedDisc Δ
      ∧ IsClosedDisc E ∧ Δ ∪ E = R ∧
      Δ ∩ E = ℓ ∧ IsLineWithEnds c s t ∧ IsLineWithEnds c' s t ∧ c ∪ c' = discBd R ∧ c ∩ c'
        = {s, t} ∧
      discBd Δ = c ∪ ℓ ∧ discBd E = c' ∪ ℓ ∧ ℓ ∩ discBd R = {s, t} ∧ v ∈ ℓ ∧ Δ ⊆ A ∧ Disjoint
        (E \ ℓ) A := by
  have ht2 : T2Space S := hS.2.1
  have hne : w ≠ v := fun e => hw (e ▸ h.mem.1)
  have hbc : IsClosed (discBd A) := hA.isOArc_discBd.isCompact.isClosed
  obtain ⟨a, b, hab, ha0, ha1, hr⟩ := hA.isOArc_discBd.exists_arcs hwA hv hne
  have la : IsLineWithEnds (range a) w v := ha0 ▸ ha1 ▸ hab.arc_left.isLineWithEnds
  have lb : IsLineWithEnds (range b) w v := by
    have := hab.arc_right.isLineWithEnds
    rwa [hab.zero, hab.one, ha0, ha1] at this
  have hmeet : range a ∩ range b = {w, v} := by
    ext y
    constructor
    · rintro ⟨⟨r, rfl⟩, ⟨r', e⟩⟩
      rcases hab.meet r r' e.symm with ⟨h0, -⟩ | ⟨h1, -⟩
      · exact .inl (by rw [h0, ha0])
      · exact .inr (by rw [h1, ha1]; rfl)
    · rintro (rfl | rfl)
      · exact ⟨la.left_mem, lb.left_mem⟩
      · exact ⟨la.right_mem, lb.right_mem⟩
  obtain ⟨s, t, ρ₁, ρ₂, -, -, r₁, r₂, -, -, -, -, hl, hst, hF, hbd⟩ := exists_chord hS h la lb
    hr.symm hmeet hw hbc hn
  have hvℓ : v ∈ ρ₁ ∪ ρ₂ := .inl r₁.right_mem
  have hsub : ρ₁ ∪ ρ₂ ⊆ R := by rw [hF]; exact inter_subset_right
  obtain ⟨Δ₁, Δ₂, c₁, c₂, l₁, l₂, hu, hi, d₁, d₂, hU, hI, b₁, b₂, p₁, p₂⟩
    := disc_split h.disc hsub hst hl hbd
  have hfr : frontier A ∩ R = ρ₁ ∪ ρ₂ := by rw [IsClosedDisc.frontier_eq_discBd hS hA, hF]
  have hin : v ∈ closure (interior A) := by
    rw [interior_eq_sdiff_discBd hS hA]
    exact hA.subset_closure_discInt (GM11.discBd_subset A hv)
  have hout : v ∈ closure Aᶜ := by
    rw [closure_compl, interior_eq_sdiff_discBd hS hA]
    exact fun h3 => h3.2 hv
  rcases side_of_frontier hS h.disc hU hI p₁ p₂ hA.isClosed hfr hvℓ h.mem hin hout with ⟨h3, h4⟩ |
    ⟨h3, h4⟩
  · exact ⟨_, s, t, Δ₁, Δ₂, c₁, c₂, hl, hst, hF.symm ▸ rfl, d₁, d₂, hU, hI, l₁, l₂, hu, hi, b₁,
      b₂, hbd, hvℓ, h3, h4⟩
  · exact ⟨_, s, t, Δ₂, Δ₁, c₂, c₁, hl, hst, hF.symm ▸ rfl, d₂, d₁, by rw [union_comm, hU],
      by rw [inter_comm, hI], l₂, l₁,
      by rw [union_comm, hu], by rw [inter_comm, hi], b₂, b₁, hbd, hvℓ, h3, h4⟩

end GraphMinor.GM07
