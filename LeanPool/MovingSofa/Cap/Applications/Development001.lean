/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Bounds.Foundations.Development005
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Geometry.Foundations.Development004

/-!
# Moving sofa: related mathematical developments

* `Cap.PolylineBoundary`.
* `Cap.PolylineDefinition`.
* `Cap.Polyline`.
* `Cap.UpperBoundary.Polygon`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Polyline Boundary
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The slope and intercept of the inner B-wall line at angle `t`. -/
def capBAffine {Θ : AngleSet} (K : PolygonCapSpace Θ) (t : ℝ) : ℝ × ℝ :=
  (-Real.cos t / Real.sin t,
    (supportValue K.val.val (t : Real.Angle) - 1) / Real.sin t)

/-- The slope and intercept of the inner D-wall line at angle `t`. -/
def capDAffine {Θ : AngleSet} (K : PolygonCapSpace Θ) (t : ℝ) : ℝ × ℝ :=
  (Real.sin t / Real.cos t,
    (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) / Real.cos t)

/-- The slope and zero intercept of the slanted fan boundary. -/
def fanAffine (ω : ℝ) : ℝ × ℝ :=
  (-Real.cos ω / Real.sin ω, 0)

private def capAffinePieces {Θ : AngleSet} (K : PolygonCapSpace Θ) : Finset (ℝ × ℝ) :=
  {(0, 0), fanAffine Θ.angle} ∪
    Θ.directions.biUnion fun t ↦ {capBAffine K t, capDAffine K t}

/-- The lower boundary height of a polygon cap after removing its niche. -/
def capBoundaryHeight {Θ : AngleSet} (K : PolygonCapSpace Θ) (x : ℝ) : ℝ :=
  max 0 (max (affineValue (fanAffine Θ.angle) x)
    (Θ.directions.sup' Θ.nonempty fun t ↦
      min (affineValue (capBAffine K t) x) (affineValue (capDAffine K t) x)))

private theorem continuous_capBoundaryHeight {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    Continuous (capBoundaryHeight K) := by
  unfold capBoundaryHeight
  apply Continuous.max continuous_const
  apply Continuous.max (continuous_affineValue _)
  apply Continuous.finset_sup'_apply Θ.nonempty
  intro t ht
  exact (continuous_affineValue _).min (continuous_affineValue _)

private theorem capBoundaryHeight_eq_affineValue {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (x : ℝ) :
    ∃ c ∈ capAffinePieces K, capBoundaryHeight K x = affineValue c x := by
  obtain hzero | hrest := max_choice 0
    (max (affineValue (fanAffine Θ.angle) x)
      (Θ.directions.sup' Θ.nonempty fun t ↦
        min (affineValue (capBAffine K t) x) (affineValue (capDAffine K t) x)))
  · refine ⟨(0, 0), by simp [capAffinePieces], ?_⟩
    simpa [capBoundaryHeight, affineValue] using hzero
  · obtain hfan | hsup := max_choice (affineValue (fanAffine Θ.angle) x)
      (Θ.directions.sup' Θ.nonempty fun t ↦
        min (affineValue (capBAffine K t) x) (affineValue (capDAffine K t) x))
    · refine ⟨fanAffine Θ.angle, by simp [capAffinePieces], ?_⟩
      rw [capBoundaryHeight, hrest, hfan]
    · obtain ⟨t, ht, htEq⟩ := Finset.exists_mem_eq_sup' Θ.nonempty
        (fun t ↦ min (affineValue (capBAffine K t) x)
          (affineValue (capDAffine K t) x))
      obtain hB | hD := min_choice (affineValue (capBAffine K t) x)
        (affineValue (capDAffine K t) x)
      · refine ⟨capBAffine K t, ?_, ?_⟩
        · apply Finset.mem_union.mpr
          right
          exact Finset.mem_biUnion.mpr ⟨t, ht, by simp⟩
        · rw [capBoundaryHeight, hrest, hsup, htEq, hB]
      · refine ⟨capDAffine K t, ?_, ?_⟩
        · apply Finset.mem_union.mpr
          right
          exact Finset.mem_biUnion.mpr ⟨t, ht, by simp⟩
        · rw [capBoundaryHeight, hrest, hsup, htEq, hD]

private theorem capAffinePieces_has_normal {Θ : AngleSet} (K : PolygonCapSpace Θ)
    {c : ℝ × ℝ} (hc : c ∈ capAffinePieces K) :
    ∃ t ∈ angleDomain Θ, Real.cos t + c.1 * Real.sin t = 0 := by
  rw [capAffinePieces, Finset.mem_union] at hc
  rcases hc with hc | hc
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · refine ⟨Real.pi / 2, ?_, ?_⟩
      · simp [angleDomain]
      · simp
    · refine ⟨Θ.angle, ?_, ?_⟩
      · simp [angleDomain]
      · simp only [fanAffine]
        have hs : Real.sin Θ.angle ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
          (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))).ne'
        field_simp
        ring
  · obtain ⟨t, ht, hc⟩ := Finset.mem_biUnion.mp hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · refine ⟨t, by simp [angleDomain, ht], ?_⟩
      simp only [capBAffine]
      have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi
        (Θ.interior t ht).1
        ((Θ.interior t ht).2.trans_le Θ.angle_le |>.trans
          (by linarith [Real.pi_pos]))).ne'
      field_simp
      ring
    · refine ⟨t + Real.pi / 2, ?_, ?_⟩
      · simp [angleDomain, ht]
      · simp only [capDAffine, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
        have hc : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [Real.pi_pos, (Θ.interior t ht).1],
            (Θ.interior t ht).2.trans_le Θ.angle_le⟩).ne'
        field_simp
        ring

private theorem mem_innerQuadrant_iff_lt_min_affine {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) (p : Point) :
    p ∈ innerQuadrant K.val.val t ↔
      p 1 < min (affineValue (capBAffine K t) (p 0))
        (affineValue (capDAffine K t) (p 0)) := by
  have htt := Θ.interior t ht
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htt.1
    ((htt.2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos]))
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, htt.1], htt.2.trans_le Θ.angle_le⟩
  simp only [innerQuadrant, normalHalfPlane, Set.mem_inter_iff,
    Bool.false_eq_true, ite_false, ite_true]
  simp [normalVector, frame, PiLp.inner_apply, Real.sin_add, Real.cos_add,
    -Real.Angle.coe_add]
  change
    (Real.cos t * p 0 + Real.sin t * p 1 <
        supportValue K.val.val (t : Real.Angle) - 1 ∧
      Real.cos t * p 1 < Real.sin t * p 0 +
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)) ↔ _
  simp only [affineValue, capBAffine, capDAffine]
  have heqB : -Real.cos t / Real.sin t * p 0 +
      (supportValue K.val.val (t : Real.Angle) - 1) / Real.sin t =
      (supportValue K.val.val (t : Real.Angle) - 1 - Real.cos t * p 0) /
        Real.sin t := by
    field_simp
    ring
  have heqD : Real.sin t / Real.cos t * p 0 +
      (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
        Real.cos t =
      (Real.sin t * p 0 +
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)) /
        Real.cos t := by
    field_simp
  rw [heqB, heqD]
  constructor
  · rintro ⟨hB, hD⟩
    constructor
    · apply (lt_div_iff₀ hs).2
      nlinarith
    · apply (lt_div_iff₀ hc).2
      nlinarith
  · rintro ⟨hB, hD⟩
    constructor
    · apply (lt_div_iff₀ hs).mp at hB
      nlinarith
    · apply (lt_div_iff₀ hc).mp at hD
      nlinarith

private theorem mem_capFan_iff_max_affine_le {Θ : AngleSet}
    (p : Point) :
    p ∈ capFan Θ.angle ↔
      max 0 (affineValue (fanAffine Θ.angle) (p 0)) ≤ p 1 := by
  have hs : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
    (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))
  simp [capFan, normalHalfPlane, normalVector, frame, PiLp.inner_apply,
    affineValue, fanAffine]
  have heq : -Real.cos Θ.angle / Real.sin Θ.angle * p 0 =
      (-Real.cos Θ.angle * p 0) / Real.sin Θ.angle := by ring
  rw [heq]
  constructor
  · rintro ⟨hfan, hy⟩
    exact ⟨hy, (div_le_iff₀ hs).2 (by nlinarith)⟩
  · rintro ⟨hy, hfan⟩
    apply (div_le_iff₀ hs).mp at hfan
    exact ⟨by nlinarith, hy⟩

/-- The fan outside the polygon niche is the epigraph of its boundary height. -/
theorem capFan_sdiff_polygonNiche_eq_epigraph {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    capFan Θ.angle \ polygonNiche Θ K.val =
      {p | capBoundaryHeight K (p 0) ≤ p 1} := by
  ext p
  constructor
  · rintro ⟨hfan, hniche⟩
    have hnotUnion : p ∉ ⋃ t ∈ Θ.directions, innerQuadrant K.val.val t := by
      intro hp
      exact hniche ⟨hfan, hp⟩
    have hfan' := (mem_capFan_iff_max_affine_le (Θ := Θ) p).mp hfan
    change capBoundaryHeight K (p 0) ≤ p 1
    unfold capBoundaryHeight
    apply max_le
    · exact (le_max_left _ _).trans hfan'
    · apply max_le
      · exact (le_max_right _ _).trans hfan'
      · apply (Finset.sup'_le_iff Θ.nonempty _).2
        intro t ht
        apply le_of_not_gt
        intro hlt
        apply hnotUnion
        exact Set.mem_iUnion₂.mpr
          ⟨t, ht, (mem_innerQuadrant_iff_lt_min_affine K ht p).mpr hlt⟩
  · intro hp
    change capBoundaryHeight K (p 0) ≤ p 1 at hp
    unfold capBoundaryHeight at hp
    have hzero : 0 ≤ p 1 := by
      exact (le_max_left 0 _).trans hp
    have hfanLine : affineValue (fanAffine Θ.angle) (p 0) ≤ p 1 := by
      exact (le_max_left _ _).trans <|
        (le_max_right 0 _).trans hp
    have hsup : (Θ.directions.sup' Θ.nonempty fun t ↦
        min (affineValue (capBAffine K t) (p 0))
          (affineValue (capDAffine K t) (p 0))) ≤ p 1 := by
      exact (le_max_right _ _).trans <|
        (le_max_right 0 _).trans hp
    have hfan : p ∈ capFan Θ.angle :=
      (mem_capFan_iff_max_affine_le (Θ := Θ) p).mpr (max_le hzero hfanLine)
    refine ⟨hfan, ?_⟩
    rintro ⟨-, hunion⟩
    obtain ⟨t, ht, hquad⟩ := Set.mem_iUnion₂.mp hunion
    have hlt := (mem_innerQuadrant_iff_lt_min_affine K ht p).mp hquad
    have hle := ((Finset.sup'_le_iff Θ.nonempty _).1 hsup) t ht
    exact (not_lt_of_ge hle) hlt

/-- The cap outside its polygon niche is closed, with frontier the boundary graph. -/
theorem capFan_sdiff_polygonNiche_closed_frontier {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) ∧
    frontier (capFan Θ.angle \ polygonNiche Θ K.val) =
      Set.range (pointOnGraph (capBoundaryHeight K)) := by
  rw [capFan_sdiff_polygonNiche_eq_epigraph K]
  exact ⟨isClosed_verticalEpigraph (continuous_capBoundaryHeight K),
    frontier_verticalEpigraph (continuous_capBoundaryHeight K)⟩

/-- Every compact interval of the polygon-cap boundary graph is a finite polyline. -/
theorem exists_capBoundary_graphPolyline {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {a b : ℝ} (hab : a < b) :
    ∃ p : XMonotonePolylineData,
      0 < p.edges ∧
      p.vertices 0 = pointOnGraph (capBoundaryHeight K) a ∧
      p.vertices (Fin.last p.edges) = pointOnGraph (capBoundaryHeight K) b ∧
      p.carrier = pointOnGraph (capBoundaryHeight K) '' Set.Icc a b ∧
      (∀ i : Fin p.edges, ∃ t ∈ angleDomain Θ,
        inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0) := by
  obtain ⟨p, hp, hp0, hp1, hpcarrier, hgraph, hpieces⟩ :=
    exists_graphPolyline_of_finite_affine_selector hab (capAffinePieces K)
      (continuous_capBoundaryHeight K).continuousOn
      (fun x _ ↦ capBoundaryHeight_eq_affineValue K x)
  refine ⟨p, hp, hp0, hp1, hpcarrier, ?_⟩
  intro i
  obtain ⟨c, hcL, hc⟩ := hpieces i
  obtain ⟨t, ht, horth⟩ := capAffinePieces_has_normal K hcL
  refine ⟨t, ht, ?_⟩
  have hab' : p.vertices i.castSucc 0 ≤ p.vertices i.succ 0 :=
    (p.increasing i.castSucc_lt_succ).le
  rw [hgraph i.succ, hgraph i.castSucc]
  change Set.EqOn (capBoundaryHeight K) (fun x ↦ c.1 * x + c.2)
    (Set.Icc (p.vertices i.castSucc 0) (p.vertices i.succ 0)) at hc
  exact inner_pointOnGraph_sub_normalVector_eq_zero
    (m := c.1) (c := c.2) (t := t)
    hc hab' horth

/-- The lower endpoint of the zero-angle cap face lies on the horizontal axis. -/
theorem capVertices_zero_snd_eq {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    (capVertices K.val 0).1.2 =
      supportValue K.val.val (0 : Real.Angle) • normalVector (0 : Real.Angle) := by
  let A := supportValue K.val.val (0 : Real.Angle) • normalVector (0 : Real.Angle)
  have hAK : A ∈ (K.val.val : Set Point) :=
    supportValue_zero_smul_normalVector_mem K.val
  have hAedge : A ∈ exposedEdge K.val.val (0 : Real.Angle) := by
    refine ⟨hAK, ?_⟩
    change inner ℝ A (normalVector (0 : Real.Angle)) =
      supportValue K.val.val (0 : Real.Angle)
    dsimp [A]
    simp [normalVector, frame, PiLp.inner_apply]
  change (edgeVertices K.val.val (0 : Real.Angle)).2 = A
  apply edgeVertices_snd_eq_of_tangent_isLeast K.val.val _ hAedge
  intro q hq
  have hqFan := K.val.subset_capFan hq.1
  have hqy : 0 ≤ q 1 := by
    have h := hqFan.2
    change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at h
    simpa [normalVector, frame, PiLp.inner_apply] using h
  simp [A, tangentVector, normalVector, frame, PiLp.inner_apply]
  exact hqy

/-- The terminal positive cap contact lies on the lower fan ray. -/
theorem capVertices_angle_fst_eq {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    (capVertices K.val Θ.angle).2.1 =
      supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
        tangentVector (Θ.angle : Real.Angle) := by
  let L := supportValue K.val.val
    ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
  let C := L • tangentVector (Θ.angle : Real.Angle)
  have hCK : C ∈ (K.val.val : Set Point) := by
    by_cases hω : Θ.angle = Real.pi / 2
    · have hmem := supportValue_pi_smul_normalVector_mem_of_eq K.val hω
      simpa [C, L, hω, tangentVector, normalVector, frame, PiLp.inner_apply] using hmem
    · exact supportValue_add_pi_div_two_smul_tangentVector_mem_of_lt K.val
        (Θ.angle_le.lt_of_ne hω)
  have hCedge : C ∈ exposedEdge K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hCK, ?_⟩
    change inner ℝ C
      (normalVector ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)) = L
    rw [show ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) =
        (Θ.angle : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
      normalVector_add_pi_div_two, real_inner_smul_left,
      inner_tangentVector_self]
    ring
  change (edgeVertices K.val.val
    ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).1 = C
  apply edgeVertices_fst_eq_of_tangent_isGreatest K.val.val _ hCedge
  intro q hq
  have hqFan := K.val.subset_capFan hq.1
  have hqu : 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) := hqFan.1
  rw [tangentVector_add_pi_div_two]
  simp only [inner_neg_right]
  have hCzero : inner ℝ C (normalVector (Θ.angle : Real.Angle)) = 0 := by
    dsimp [C]
    rw [real_inner_smul_left, real_inner_comm,
      inner_normalVector_tangentVector]
    simp
  rw [hCzero]
  simpa using neg_nonpos.mpr hqu

/-- The terminal cap contacts occur in strictly increasing horizontal order. -/
theorem polygonCap_left_x_lt_right_x {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    ((capVertices K.val Θ.angle).2.1) 0 < ((capVertices K.val 0).1.2) 0 := by
  let C := (capVertices K.val Θ.angle).2.1
  let A := (capVertices K.val 0).1.2
  have hq_le_A : ∀ q ∈ (K.val.val : Set Point), q 0 ≤ A 0 := by
    intro q hq
    have hq' := inner_le_supportValue K.val.val hq (0 : Real.Angle)
    have hA := (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).2
    change inner ℝ A (normalVector (0 : Real.Angle)) =
      supportValue K.val.val (0 : Real.Angle) at hA
    calc
      q 0 = inner ℝ q (normalVector (0 : Real.Angle)) := by
        simp [normalVector, frame, PiLp.inner_apply]
      _ ≤ supportValue K.val.val (0 : Real.Angle) := hq'
      _ = inner ℝ A (normalVector (0 : Real.Angle)) := hA.symm
      _ = A 0 := by simp [normalVector, frame, PiLp.inner_apply]
  by_cases hω : Θ.angle = Real.pi / 2
  · have hC_le_q : ∀ q ∈ (K.val.val : Set Point), C 0 ≤ q 0 := by
      intro q hq
      have hq' := inner_le_supportValue K.val.val hq (Real.pi : Real.Angle)
      have hC := (edgeVertices_fst_mem K.val.val
        ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).2
      change inner ℝ C
        (normalVector ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)) =
          supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) at hC
      have hang : ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) =
          (Real.pi : Real.Angle) := by
        congr 1
        rw [hω]
        ring
      rw [hang] at hC
      have hqcoord : -q 0 ≤ supportValue K.val.val (Real.pi : Real.Angle) := by
        simpa [normalVector, frame, PiLp.inner_apply] using hq'
      have hCcoord : -C 0 = supportValue K.val.val (Real.pi : Real.Angle) := by
        simpa [normalVector, frame, PiLp.inner_apply] using hC
      linarith
    by_contra hnot
    have hAC : A 0 = C 0 := by
      apply le_antisymm (le_of_not_gt hnot)
      exact hC_le_q A (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).1
    have hx : ∀ q ∈ (K.val.val : Set Point), q 0 = A 0 := by
      intro q hq
      exact le_antisymm (hq_le_A q hq) (hAC.trans_le (hC_le_q q hq))
    obtain ⟨u, huK, hu⟩ := exists_mem_inner_eq_supportValue K.val.val
      ((Real.pi / 2 : ℝ) : Real.Angle)
    obtain ⟨l, hlK, hl⟩ := exists_mem_inner_eq_supportValue K.val.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    have huy : u 1 = 1 := by
      rw [K.val.property.2.2.2.1] at hu
      simpa [normalVector, frame, PiLp.inner_apply] using hu
    have hly : l 1 = 0 := by
      rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hl
      linarith
    let m : Point := (2 : ℝ)⁻¹ • (u + l)
    let N : Set Real.Angle :=
      ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle
    let U : Set Point := ⋂ t ∈ N,
      {p | inner ℝ p (normalVector t) < supportValue K.val.val t}
    have hdomain_finite : (angleDomain Θ).Finite := by
      unfold angleDomain
      exact (Θ.directions.finite_toSet.union
        (Θ.directions.finite_toSet.image (fun t ↦ t + Real.pi / 2))).union
          (Set.toFinite _)
    have hlower_finite : (capLowerNormals Θ.angle).Finite := by
      simp [capLowerNormals]
    have hNfinite : N.Finite := by
      dsimp [N]
      exact (hdomain_finite.image fun t : ℝ ↦ (t : Real.Angle)).union hlower_finite
    have hUopen : IsOpen U := by
      dsimp [U]
      apply hNfinite.isOpen_biInter
      intro t ht
      exact isOpen_lt (by fun_prop) continuous_const
    have hmU : m ∈ U := by
      dsimp [U]
      simp only [Set.mem_iInter]
      intro t htN
      rcases htN with ⟨r, hr, rfl⟩ | htLower
      · have hrI : r ∈ Set.Ioo 0 Real.pi := by
          rcases hr with (hr | ⟨s, hs, rfl⟩) | hr
          · exact ⟨(Θ.interior r hr).1,
              by linarith [(Θ.interior r hr).2, Θ.angle_le, Real.pi_pos]⟩
          · exact ⟨by linarith [(Θ.interior s hs).1, Real.pi_pos],
              by linarith [(Θ.interior s hs).2, hω, Real.pi_pos]⟩
          · rcases hr with rfl | hr
            · rw [hω]
              constructor <;> linarith [Real.pi_pos]
            · have hr : r = Real.pi / 2 := hr
              rw [hr]
              constructor <;> linarith [Real.pi_pos]
        have hsin : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hrI.1 hrI.2
        have htop : inner ℝ m (normalVector (r : Real.Angle)) <
            inner ℝ u (normalVector (r : Real.Angle)) := by
          have hux : u 0 = l 0 := (hx u huK).trans (hx l hlK).symm
          simp [m, normalVector, frame, PiLp.inner_apply, huy, hly]
          rw [hux]
          norm_num
          nlinarith
        exact htop.trans_le (inner_le_supportValue K.val.val huK _)
      · simp only [capLowerNormals, Set.mem_insert_iff, Set.mem_singleton_iff] at htLower
        rcases htLower with rfl | rfl
        · rw [K.val.property.2.2.2.2.1]
          norm_num [m, hω, normalVector, frame, PiLp.inner_apply, huy, hly]
        · rw [K.val.property.2.2.2.2.2.1]
          change inner ℝ m
            (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) < 0
          rw [inner_normalVector_three_pi_div_two]
          simp [m, huy, hly]
    obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hUopen) m hmU
    let q : Point := m + (ε / 2) • normalVector (0 : Real.Angle)
    have hqm : q ∈ Metric.ball m ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [q, add_sub_cancel_left, norm_smul]
      rw [Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      have hn : ‖normalVector (0 : Real.Angle)‖ = 1 := by
        simpa only [Real.Angle.coe_zero] using norm_normalVector_real 0
      rw [hn, mul_one]
      linarith
    have hqU : q ∈ U := hball hqm
    have hqK : q ∈ (K.val.val : Set Point) := by
      rw [K.property.eq_iInter_supportValue]
      simp only [Set.mem_iInter]
      intro t ht
      have hqt := Set.mem_iInter.mp (Set.mem_iInter.mp hqU t) ht
      change inner ℝ q (normalVector t) < supportValue K.val.val t at hqt
      exact hqt.le
    have hq0 : q 0 = A 0 + ε / 2 := by
      simp [q, m, normalVector, frame, hx u huK, hx l hlK]
      ring
    have := hq_le_A q hqK
    rw [hq0] at this
    linarith
  · have hωlt : Θ.angle < Real.pi / 2 := Θ.angle_le.lt_of_ne hω
    rw [capVertices_zero_snd_eq K, capVertices_angle_fst_eq K]
    have hA0 : 0 < supportValue K.val.val (0 : Real.Angle) := by
      obtain ⟨p, hpK, hp⟩ := exists_mem_inner_eq_supportValue K.val.val
        (Θ.angle : Real.Angle)
      have hpy : p 1 ≤ 1 := by
        have hpy' := inner_le_supportValue K.val.val hpK
          ((Real.pi / 2 : ℝ) : Real.Angle)
        rw [K.val.property.2.2.2.1] at hpy'
        simpa [normalVector, frame, PiLp.inner_apply] using hpy'
      rw [K.val.property.2.2.1] at hp
      have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hωlt⟩
      have hsin_lt : Real.sin Θ.angle < 1 := by
        nlinarith only [Real.sin_sq_add_cos_sq Θ.angle, sq_pos_of_pos hcos]
      have hpx : 0 < p 0 := by
        simp [normalVector, frame, PiLp.inner_apply] at hp
        have hsin : 0 ≤ Real.sin Θ.angle :=
          (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
            (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))).le
        have hmul := mul_le_mul_of_nonneg_left hpy hsin
        nlinarith
      exact hpx.trans_le (by
        have := inner_le_supportValue K.val.val hpK (0 : Real.Angle)
        simpa [normalVector, frame, PiLp.inner_apply] using this)
    have hL0 : 0 ≤ supportValue K.val.val
        ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) :=
      supportValue_nonneg_of_mem_capUpperAngles K.val hωlt
        (Or.inr ⟨by linarith [Θ.angle_pos, Real.pi_pos], le_rfl⟩)
    have hs : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
      (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))
    have hprod : 0 ≤ supportValue K.val.val
        ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) * Real.sin Θ.angle :=
      mul_nonneg hL0 hs.le
    have hprod' : 0 ≤ supportValue K.val.val
        ((Θ.angle : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) *
          Real.sin Θ.angle := by
      simpa only [Real.Angle.coe_add] using hprod
    simp [normalVector, tangentVector, frame]
    nlinarith

private theorem capBoundaryHeight_eq_zero_of_right {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {x : ℝ}
    (hx : ((capVertices K.val 0).1.2) 0 ≤ x) :
    capBoundaryHeight K x = 0 := by
  let A := (capVertices K.val 0).1.2
  have hAeq := capVertices_zero_snd_eq K
  have hsinω : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
    (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))
  have hcosω : 0 ≤ Real.cos Θ.angle := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], Θ.angle_le⟩
  have hAfan := K.val.subset_capFan (edgeVertices_snd_mem K.val.val
    (0 : Real.Angle)).1
  have hfanA : affineValue (fanAffine Θ.angle) (A 0) ≤ 0 := by
    change A = supportValue K.val.val (0 : Real.Angle) •
      normalVector (0 : Real.Angle) at hAeq
    change A ∈ capFan Θ.angle at hAfan
    have h := hAfan.1
    change 0 ≤ inner ℝ A (normalVector (Θ.angle : Real.Angle)) at h
    rw [hAeq] at h
    simp [normalVector, frame, PiLp.inner_apply] at h
    have hAcoord : A 0 = supportValue K.val.val (0 : Real.Angle) := by
      rw [hAeq]
      simp [normalVector, frame]
    rw [hAcoord]
    simp only [affineValue, fanAffine, add_zero]
    have heq : -Real.cos Θ.angle / Real.sin Θ.angle *
        supportValue K.val.val (0 : Real.Angle) =
        (-Real.cos Θ.angle * supportValue K.val.val (0 : Real.Angle)) /
          Real.sin Θ.angle := by ring
    rw [heq]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [h]
    · exact hsinω.le
  have hfan : affineValue (fanAffine Θ.angle) x ≤ 0 := by
    simp only [affineValue, fanAffine, add_zero] at hfanA ⊢
    have hslope : -Real.cos Θ.angle / Real.sin Θ.angle ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcosω) hsinω.le
    exact (mul_le_mul_of_nonpos_left hx hslope).trans hfanA
  have hpieces : (Θ.directions.sup' Θ.nonempty fun t ↦
      min (affineValue (capBAffine K t) x)
        (affineValue (capDAffine K t) x)) ≤ 0 := by
    apply (Finset.sup'_le_iff Θ.nonempty _).2
    intro t ht
    apply (min_le_left _ _).trans
    have htt := Θ.interior t ht
    have hsint : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htt.1
      ((htt.2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos]))
    have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [htt.1, Real.pi_pos], htt.2.trans_le Θ.angle_le⟩
    have hgapBounds := wedgeGaps_positive_lower_bound K.val t htt
    have hgap : 0 < (wedgeGaps K.val t).1 :=
      hgapBounds.2.1.trans_le hgapBounds.1
    rw [wedgeGaps_fst_eq_supportValue] at hgap
    have hAcoord : A 0 = supportValue K.val.val (0 : Real.Angle) := by
      change A = supportValue K.val.val (0 : Real.Angle) •
        normalVector (0 : Real.Angle) at hAeq
      rw [hAeq]
      simp [normalVector, frame]
    have hnum : supportValue K.val.val (t : Real.Angle) - 1 - Real.cos t * x < 0 := by
      have hdiv := (sub_pos.mp hgap)
      have hmul := (div_lt_iff₀ hcost).mp hdiv
      rw [hAcoord] at hx
      nlinarith
    simp only [affineValue, capBAffine]
    have heq : -Real.cos t / Real.sin t * x +
        (supportValue K.val.val (t : Real.Angle) - 1) / Real.sin t =
        (supportValue K.val.val (t : Real.Angle) - 1 - Real.cos t * x) /
          Real.sin t := by
      field_simp
      ring
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg hnum.le hsint.le
  unfold capBoundaryHeight
  rw [max_eq_left (max_le hfan hpieces)]

private theorem capBoundaryHeight_eq_fanAffine_of_left {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {x : ℝ}
    (hx : x ≤ ((capVertices K.val Θ.angle).2.1) 0) :
    capBoundaryHeight K x = affineValue (fanAffine Θ.angle) x := by
  let C := (capVertices K.val Θ.angle).2.1
  let L := supportValue K.val.val
    ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
  have hCeq := capVertices_angle_fst_eq K
  have hsinω : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
    (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))
  have hcosω : 0 ≤ Real.cos Θ.angle := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], Θ.angle_le⟩
  have hfan_nonneg : 0 ≤ affineValue (fanAffine Θ.angle) x := by
    by_cases hω : Θ.angle = Real.pi / 2
    · simp [affineValue, fanAffine, hω]
    · have hωlt : Θ.angle < Real.pi / 2 := Θ.angle_le.lt_of_ne hω
      have hL : 0 ≤ L := supportValue_nonneg_of_mem_capUpperAngles K.val hωlt
        (Or.inr ⟨by linarith [Θ.angle_pos, Real.pi_pos], le_rfl⟩)
      have hCx : C 0 = -L * Real.sin Θ.angle := by
        change C = L • tangentVector (Θ.angle : Real.Angle) at hCeq
        rw [hCeq]
        simp [tangentVector, frame]
      have hx0 : x ≤ 0 := by
        rw [hCx] at hx
        nlinarith [mul_nonneg hL hsinω.le]
      simp only [affineValue, fanAffine, add_zero]
      exact mul_nonneg_of_nonpos_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcosω) hsinω.le) hx0
  have hpieces : (Θ.directions.sup' Θ.nonempty fun t ↦
      min (affineValue (capBAffine K t) x)
        (affineValue (capDAffine K t) x)) ≤
      affineValue (fanAffine Θ.angle) x := by
    apply (Finset.sup'_le_iff Θ.nonempty _).2
    intro t ht
    apply (min_le_right _ _).trans
    have htt := Θ.interior t ht
    have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [htt.1, Real.pi_pos], htt.2.trans_le Θ.angle_le⟩
    have hcosδ : 0 < Real.cos (Θ.angle - t) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [htt.2, Real.pi_pos], by linarith [htt.1, Θ.angle_le]⟩
    have hgapBounds := wedgeGaps_positive_lower_bound K.val t htt
    have hgap : 0 < (wedgeGaps K.val t).2 :=
      hgapBounds.2.2.2.trans_le hgapBounds.2.2.1
    rw [wedgeGaps_snd_eq_supportValue] at hgap
    have hCx : C 0 = -L * Real.sin Θ.angle := by
      change C = L • tangentVector (Θ.angle : Real.Angle) at hCeq
      rw [hCeq]
      simp [tangentVector, frame]
    have hsupport :
        supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 <
          L * Real.cos (Θ.angle - t) := by
      have hdiv := sub_pos.mp hgap
      exact (div_lt_iff₀ hcosδ).mp hdiv
    have hnum : Real.cos (Θ.angle - t) / Real.sin Θ.angle * x +
        supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 < 0 := by
      have hcoef : 0 < Real.cos (Θ.angle - t) / Real.sin Θ.angle :=
        div_pos hcosδ hsinω
      have hxC : x ≤ C 0 := by simpa [C] using hx
      have hx' : x ≤ -L * Real.sin Θ.angle := hCx ▸ hxC
      have hmul := mul_le_mul_of_nonneg_left hx' hcoef.le
      have hrhs : Real.cos (Θ.angle - t) / Real.sin Θ.angle *
          (-L * Real.sin Θ.angle) = -L * Real.cos (Θ.angle - t) := by
        field_simp [hsinω.ne']
      rw [hrhs] at hmul
      nlinarith
    have hdiff : affineValue (capDAffine K t) x -
        affineValue (fanAffine Θ.angle) x =
        (Real.cos (Θ.angle - t) / Real.sin Θ.angle * x +
          supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos t := by
      simp only [affineValue, capDAffine, fanAffine]
      rw [Real.cos_sub]
      field_simp [hcost.ne', hsinω.ne']
      ring
    rw [sub_eq_iff_eq_add] at hdiff
    rw [hdiff]
    have hdiv := div_nonpos_of_nonpos_of_nonneg hnum.le hcost.le
    linarith
  unfold capBoundaryHeight
  rw [max_eq_left hpieces, max_eq_right hfan_nonneg]

/-- The right cap contact lies on the boundary graph. -/
theorem pointOnGraph_capBoundaryHeight_rightEndpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    pointOnGraph (capBoundaryHeight K) (((capVertices K.val 0).1.2) 0) =
      (capVertices K.val 0).1.2 := by
  have hAeq := capVertices_zero_snd_eq K
  have hh := capBoundaryHeight_eq_zero_of_right K
    (x := ((capVertices K.val 0).1.2) 0) le_rfl
  ext i
  fin_cases i
  · rfl
  · change capBoundaryHeight K (((capVertices K.val 0).1.2) 0) =
      ((capVertices K.val 0).1.2) 1
    rw [hh, hAeq]
    simp [normalVector, frame]

/-- The left cap contact lies on the boundary graph. -/
theorem pointOnGraph_capBoundaryHeight_leftEndpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    pointOnGraph (capBoundaryHeight K) (((capVertices K.val Θ.angle).2.1) 0) =
      (capVertices K.val Θ.angle).2.1 := by
  let C := (capVertices K.val Θ.angle).2.1
  let L := supportValue K.val.val
    ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
  have hCeq := capVertices_angle_fst_eq K
  have hh := capBoundaryHeight_eq_fanAffine_of_left K
    (x := ((capVertices K.val Θ.angle).2.1) 0) le_rfl
  change C = L • tangentVector (Θ.angle : Real.Angle) at hCeq
  ext i
  fin_cases i
  · rfl
  · change capBoundaryHeight K (C 0) = C 1
    change capBoundaryHeight K (((capVertices K.val Θ.angle).2.1) 0) = C 1
    rw [hh]
    have hCxy : C 0 = -L * Real.sin Θ.angle ∧
        C 1 = L * Real.cos Θ.angle := by
      rw [hCeq]
      simp [tangentVector, frame]
    rw [hCxy.1, hCxy.2]
    simp [affineValue, fanAffine]
    field_simp [(Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
      (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))).ne']

/-- The open ray to the right of a polygon-cap boundary is the right graph tail. -/
theorem capRightOpenRay_eq_graph_image {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    {q | ∃ s : ℝ, 0 < s ∧
      q = (capVertices K.val 0).1.2 + s • normalVector 0} =
      pointOnGraph (capBoundaryHeight K) ''
        Set.Ioi (((capVertices K.val 0).1.2) 0) := by
  let A := (capVertices K.val 0).1.2
  have hAeq := capVertices_zero_snd_eq K
  have hAy : A 1 = 0 := by
    change A = supportValue K.val.val (0 : Real.Angle) •
      normalVector (0 : Real.Angle) at hAeq
    rw [hAeq]
    simp [normalVector, frame]
  ext q
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨A 0 + s, ?_, ?_⟩
    · change ((capVertices K.val 0).1.2) 0 < A 0 + s
      simpa [A] using (show A 0 < A 0 + s by linarith)
    · have hh := capBoundaryHeight_eq_zero_of_right K
        (x := A 0 + s) (by simpa [A] using (show A 0 ≤ A 0 + s by linarith))
      ext i
      fin_cases i <;> simp [pointOnGraph, hh, A, hAy, normalVector, frame]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x - A 0, ?_, ?_⟩
    · exact sub_pos.mpr (by simpa [A] using hx)
    · have hh := capBoundaryHeight_eq_zero_of_right K
        (x := x) (by simpa [A] using hx.le)
      ext i
      fin_cases i <;> simp [pointOnGraph, hh, A, hAy, normalVector, frame]

/-- The open ray to the left of a polygon-cap boundary is the left graph tail. -/
theorem capLeftOpenRay_eq_graph_image {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    {q | ∃ s : ℝ, 0 < s ∧ q = (capVertices K.val Θ.angle).2.1 +
      s • tangentVector (Θ.angle : Real.Angle)} =
      pointOnGraph (capBoundaryHeight K) ''
        Set.Iio (((capVertices K.val Θ.angle).2.1) 0) := by
  let C := (capVertices K.val Θ.angle).2.1
  let L := supportValue K.val.val
    ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
  have hCeq := capVertices_angle_fst_eq K
  have hs : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
    (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))
  have hCxy : C 0 = -L * Real.sin Θ.angle ∧ C 1 = L * Real.cos Θ.angle := by
    change C = L • tangentVector (Θ.angle : Real.Angle) at hCeq
    rw [hCeq]
    simp [tangentVector, frame]
  ext q
  constructor
  · rintro ⟨s, hspos, rfl⟩
    let x := C 0 - s * Real.sin Θ.angle
    have hx : x < C 0 := by dsimp [x]; nlinarith
    refine ⟨x, by simpa [C] using hx, ?_⟩
    have hh := capBoundaryHeight_eq_fanAffine_of_left K
      (x := x) (by simpa [C] using hx.le)
    ext i
    fin_cases i
    · change x = C 0 + s * (-Real.sin Θ.angle)
      dsimp [x]
      ring
    · change capBoundaryHeight K x = C 1 + s * Real.cos Θ.angle
      rw [hh, hCxy.2]
      simp only [affineValue, fanAffine, add_zero]
      dsimp [x]
      rw [hCxy.1]
      field_simp [hs.ne']
      ring
  · rintro ⟨x, hx, rfl⟩
    let s := (C 0 - x) / Real.sin Θ.angle
    have hspos : 0 < s := div_pos (sub_pos.mpr (by simpa [C] using hx)) hs
    refine ⟨s, hspos, ?_⟩
    have hh := capBoundaryHeight_eq_fanAffine_of_left K
      (x := x) (by simpa [C] using hx.le)
    ext i
    fin_cases i
    · change x = C 0 + s * (-Real.sin Θ.angle)
      dsimp [s]
      field_simp [hs.ne']
      ring
    · change capBoundaryHeight K x = C 1 + s * Real.cos Θ.angle
      rw [hh, hCxy.2]
      simp only [affineValue, fanAffine, add_zero]
      dsimp [s]
      rw [hCxy.1]
      field_simp [hs.ne']
      ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Polyline Definition
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The open ray starting at `p` in direction `v`, excluding its initial point. -/
def openRay (p v : Point) : Set Point :=
  {q | ∃ s : ℝ, 0 < s ∧ q = p + s • v}

/-- The polyline and two disjoint endpoint rays describe the fan-minus-niche frontier. -/
def IsCapPolyline {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (p : XMonotonePolylineData) : Prop :=
  0 < p.edges ∧
  p.vertices 0 = (capVertices K.val Θ.angle).2.1 ∧
  p.vertices (Fin.last p.edges) = (capVertices K.val 0).1.2 ∧
  (∀ i : Fin p.edges, ∃ t : angleDomain Θ,
    inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t.val : Real.Angle)) = 0) ∧
  IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) ∧
  frontier (capFan Θ.angle \ polygonNiche Θ K.val) =
    openRay ((capVertices K.val Θ.angle).2.1) (tangentVector (Θ.angle : Real.Angle)) ∪
      p.carrier ∪ openRay ((capVertices K.val 0).1.2) (normalVector 0) ∧
  Disjoint (openRay ((capVertices K.val Θ.angle).2.1)
    (tangentVector (Θ.angle : Real.Angle))) p.carrier ∧
  Disjoint p.carrier (openRay ((capVertices K.val 0).1.2) (normalVector 0)) ∧
  Disjoint (openRay ((capVertices K.val Θ.angle).2.1)
    (tangentVector (Θ.angle : Real.Angle)))
    (openRay ((capVertices K.val 0).1.2) (normalVector 0))

theorem polygonCap_polyline {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    ∃ p : XMonotonePolylineData, IsCapPolyline K p := by
  let C := (capVertices K.val Θ.angle).2.1
  let A := (capVertices K.val 0).1.2
  have hCA : C 0 < A 0 := polygonCap_left_x_lt_right_x K
  obtain ⟨p, hpedge, hpC, hpA, hcarrier, hedge⟩ :=
    exists_capBoundary_graphPolyline K hCA
  refine ⟨p, hpedge, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpC]
    exact pointOnGraph_capBoundaryHeight_leftEndpoint K
  · rw [hpA]
    exact pointOnGraph_capBoundaryHeight_rightEndpoint K
  · intro i
    obtain ⟨t, ht, hi⟩ := hedge i
    exact ⟨⟨t, ht⟩, hi⟩
  · exact (capFan_sdiff_polygonNiche_closed_frontier K).1
  · rw [(capFan_sdiff_polygonNiche_closed_frontier K).2,
      show openRay ((capVertices K.val Θ.angle).2.1)
        (tangentVector (Θ.angle : Real.Angle)) = _ by
          simpa [openRay] using capLeftOpenRay_eq_graph_image K,
      show openRay ((capVertices K.val 0).1.2) (normalVector 0) = _ by
          simpa [openRay] using capRightOpenRay_eq_graph_image K, hcarrier]
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      rcases lt_or_ge x (C 0) with hx | hx
      · apply Or.inl
        apply Or.inl
        exact ⟨x, by simpa [C] using hx, rfl⟩
      · rcases le_or_gt x (A 0) with hxA | hxA
        · apply Or.inl
          apply Or.inr
          exact ⟨x, ⟨hx, hxA⟩, rfl⟩
        · apply Or.inr
          exact ⟨x, by simpa [A] using hxA, rfl⟩
    · rintro ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) <;>
        exact ⟨x, rfl⟩
  · rw [show openRay ((capVertices K.val Θ.angle).2.1)
      (tangentVector (Θ.angle : Real.Angle)) = _ by
        simpa [openRay] using capLeftOpenRay_eq_graph_image K, hcarrier]
    apply pointOnGraph_image_disjoint
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' : x < C 0 := by simpa [C] using hx
    exact (not_lt_of_ge hy.1) hx'
  · rw [hcarrier, show openRay ((capVertices K.val 0).1.2) (normalVector 0) = _ by
      simpa [openRay] using capRightOpenRay_eq_graph_image K]
    apply pointOnGraph_image_disjoint
    rw [Set.disjoint_left]
    intro x hx hy
    have hy' : A 0 < x := by simpa [A] using hy
    exact (not_lt_of_ge hx.2) hy'
  · rw [show openRay ((capVertices K.val Θ.angle).2.1)
      (tangentVector (Θ.angle : Real.Angle)) = _ by
        simpa [openRay] using capLeftOpenRay_eq_graph_image K,
    show openRay ((capVertices K.val 0).1.2) (normalVector 0) = _ by
      simpa [openRay] using capRightOpenRay_eq_graph_image K]
    apply pointOnGraph_image_disjoint
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' : x < C 0 := by simpa [C] using hx
    have hy' : A 0 < x := by simpa [A] using hy
    linarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Polyline
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A chosen monotone polyline describing the polygonal cap’s niche boundary. -/
def polygonCapPolyline {Θ : AngleSet} (K : PolygonCapSpace Θ) : XMonotonePolylineData :=
  (polygonCap_polyline K).choose

/-- Sum the lengths of polyline edges perpendicular to a prescribed wall direction. -/
def polygonCapPolylineLength {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) : ℝ := by
  classical
  let p := polygonCapPolyline K
  exact ∑ i : Fin p.edges,
    if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t.val : Real.Angle)) = 0 then
      dist (p.vertices i.castSucc) (p.vertices i.succ) else 0

/-- The cap’s surface measure at each wall direction equals the corresponding polyline length. -/
def IsBalancedPolygonCap {Θ : AngleSet} (K : PolygonCapSpace Θ) : Prop :=
  ∀ t : angleDomain Θ, surfaceAreaMeasure K.val.val {(t.val : Real.Angle)} =
    ENNReal.ofReal (polygonCapPolylineLength K t)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Upper Boundary / Polygon
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory

private lemma PolygonCapSpace.eq_of_mem_of_fst_eq_of_fst_extremal {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {a b : Point}
    (ha : a ∈ (K.val.val : Set Point)) (hb : b ∈ (K.val.val : Set Point))
    (hab : a 0 = b 0)
    (hext : (∀ q ∈ (K.val.val : Set Point), q 0 ≤ a 0) ∨
      (∀ q ∈ (K.val.val : Set Point), a 0 ≤ q 0)) : a = b := by
  apply ConvexBody.eq_of_mem_of_fst_eq_of_fst_extremal K.val.val
    (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle)
    _ K.property _ ha hb hab hext
  · have hfinite : (angleDomain Θ).Finite := by
      unfold angleDomain
      exact (Θ.directions.finite_toSet.union
        (Θ.directions.finite_toSet.image (fun t ↦ t + Real.pi / 2))).union
          (Set.toFinite _)
    exact (hfinite.image _).union (by simp [capLowerNormals])
  · intro t ht
    rcases ht with ⟨r, hr, rfl⟩ | ht
    · exact (Real.sin_pos_of_pos_of_lt_pi
        (angleDomain_subset_Ioo Θ hr).1 (angleDomain_subset_Ioo Θ hr).2).ne'
    · simp only [capLowerNormals, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · change Real.sin (Θ.angle + Real.pi) ≠ 0
        rw [Real.sin_add_pi]
        exact neg_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
          (by linarith [Θ.angle_le, Real.pi_pos])).ne'
      · change Real.sin (3 * Real.pi / 2) ≠ 0
        norm_num [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
          Real.sin_add]

private def upperSupportAffine (K : ConvexBody Point) (t : ℝ) : ℝ × ℝ :=
  (-Real.cos t / Real.sin t, supportValue K (t : Real.Angle) / Real.sin t)

private def upperSupportHeight (K : ConvexBody Point) (D : Finset ℝ)
    (hne : D.Nonempty) (x : ℝ) : ℝ :=
  D.inf' hne (fun t ↦ affineValue (upperSupportAffine K t) x)

private lemma continuous_upperSupportHeight (K : ConvexBody Point) (D : Finset ℝ)
    (hne : D.Nonempty) : Continuous (upperSupportHeight K D hne) := by
  apply Continuous.finset_inf'_apply hne
  intro t ht
  exact continuous_affineValue _

private lemma upperSupportHeight_eq_affineValue (K : ConvexBody Point) (D : Finset ℝ)
    (hne : D.Nonempty) (x : ℝ) :
    ∃ c ∈ D.image (upperSupportAffine K),
      upperSupportHeight K D hne x = affineValue c x := by
  obtain ⟨t, ht, heq⟩ := Finset.exists_mem_eq_inf' hne
    (fun t ↦ affineValue (upperSupportAffine K t) x)
  exact ⟨upperSupportAffine K t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, heq⟩

private lemma inner_le_support_iff_snd_le_affine (K : ConvexBody Point)
    {t : ℝ} (ht : 0 < Real.sin t) (q : Point) :
    inner ℝ q (normalVector (t : Real.Angle)) ≤ supportValue K (t : Real.Angle) ↔
      q 1 ≤ affineValue (upperSupportAffine K t) (q 0) := by
  have hformula : affineValue (upperSupportAffine K t) (q 0) =
      (supportValue K (t : Real.Angle) - q 0 * Real.cos t) / Real.sin t := by
    simp only [affineValue, upperSupportAffine]
    ring
  rw [hformula, le_div_iff₀ ht]
  simp only [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  simp
  constructor <;> intro h <;> nlinarith

private lemma snd_le_upperSupportHeight_iff (K : ConvexBody Point)
    (D : Finset ℝ) (hne : D.Nonempty) (hD : ∀ t ∈ D, 0 < Real.sin t) (q : Point) :
    q 1 ≤ upperSupportHeight K D hne (q 0) ↔
      ∀ t ∈ D, inner ℝ q (normalVector (t : Real.Angle)) ≤
        supportValue K (t : Real.Angle) := by
  rw [upperSupportHeight, Finset.le_inf'_iff]
  exact forall_congr' fun t ↦ forall_congr' fun ht ↦
    (inner_le_support_iff_snd_le_affine K (hD t ht) q).symm

private lemma PolygonCapSpace.mem_iff_mem_capFan_and_support_le {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (p : Point) :
    p ∈ (K.val.val : Set Point) ↔ p ∈ capFan Θ.angle ∧
      ∀ t ∈ angleDomain Θ,
        inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue K.val.val (t : Real.Angle) := by
  constructor
  · intro hp
    exact ⟨K.val.subset_capFan hp, fun t _ ↦ inner_le_supportValue K.val.val hp _⟩
  · rintro ⟨hp, hupper⟩
    rw [K.property.eq_iInter_supportValue]
    simp only [Set.mem_iInter]
    intro a ha
    rcases ha with ⟨t, ht, rfl⟩ | ha
    · exact hupper t ht
    rcases ha with rfl | rfl
    · change inner ℝ p (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) ≤ _
      rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right]
      exact neg_nonpos.mpr hp.1
    · have hang : ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
          (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) := by congr 1; ring
      change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ _
      rw [K.val.property.2.2.2.2.2.1, hang, normalVector_add_pi, inner_neg_right]
      exact neg_nonpos.mpr hp.2

private lemma mem_capFan_of_fst_eq_of_snd_le {ω : ℝ} (hω : 0 ≤ Real.sin ω)
    {p q : Point} (hp : p ∈ capFan ω) (hx : p 0 = q 0) (hy : p 1 ≤ q 1) :
    q ∈ capFan ω := by
  change 0 ≤ inner ℝ q (normalVector (ω : Real.Angle)) ∧
    0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
  change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) ∧
    0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hp
  simp [normalVector, frame, PiLp.inner_apply] at hp ⊢
  rw [hx] at hp
  constructor
  · nlinarith [hp.1, mul_nonneg hω (sub_nonneg.mpr hy)]
  · exact hp.2.trans hy

private lemma pointOnGraph_upperSupportHeight_mem {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (D : Finset ℝ) (hne : D.Nonempty) (hD : (D : Set ℝ) = angleDomain Θ)
    (hsin : ∀ t ∈ D, 0 < Real.sin t) {x : ℝ}
    (hx : ∃ q ∈ (K.val.val : Set Point), q 0 = x) :
    pointOnGraph (upperSupportHeight K.val.val D hne) x ∈ (K.val.val : Set Point) := by
  obtain ⟨q, hq, hqx⟩ := hx
  have hqle : q 1 ≤ upperSupportHeight K.val.val D hne x := by
    rw [← hqx, snd_le_upperSupportHeight_iff K.val.val D hne hsin]
    exact fun t _ ↦ inner_le_supportValue K.val.val hq _
  apply (K.mem_iff_mem_capFan_and_support_le _).mpr
  constructor
  · apply mem_capFan_of_fst_eq_of_snd_le
      (Real.sin_nonneg_of_nonneg_of_le_pi Θ.angle_pos.le
        (Θ.angle_le.trans (by linarith [Real.pi_pos]))) (K.val.subset_capFan hq)
    · exact hqx
    · exact hqle
  · intro t ht
    have htD : t ∈ D := by change t ∈ (D : Set ℝ); rwa [hD]
    apply (inner_le_support_iff_snd_le_affine K.val.val (hsin t htD) _).mpr
    change upperSupportHeight K.val.val D hne x ≤
      affineValue (upperSupportAffine K.val.val t) x
    exact Finset.inf'_le _ htD

private lemma exists_upperSupportHeight_polyline {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (D : Finset ℝ) (hne : D.Nonempty) (hD : (D : Set ℝ) = angleDomain Θ)
    (hsin : ∀ t ∈ D, 0 < Real.sin t) {a b : ℝ} (hab : a < b)
    (hfeasible : ∀ x ∈ Set.Icc a b, ∃ q ∈ (K.val.val : Set Point), q 0 = x) :
    ∃ p : XMonotonePolylineData,
      0 < p.edges ∧
      p.vertices 0 = pointOnGraph (upperSupportHeight K.val.val D hne) a ∧
      p.vertices (Fin.last p.edges) = pointOnGraph (upperSupportHeight K.val.val D hne) b ∧
      p.carrier = pointOnGraph (upperSupportHeight K.val.val D hne) '' Set.Icc a b ∧
      p.carrier ⊆ (K.val.val : Set Point) ∧
      ∀ i : Fin p.edges, ∃ t ∈ D,
        inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 ∧
        inner ℝ (p.vertices i.castSucc) (normalVector (t : Real.Angle)) =
          supportValue K.val.val (t : Real.Angle) := by
  obtain ⟨p, hp, hpa, hpb, hcarrier, hvertices, hpieces⟩ :=
    exists_graphPolyline_of_finite_affine_selector hab (D.image (upperSupportAffine K.val.val))
      (continuous_upperSupportHeight K.val.val D hne).continuousOn
      (fun x _ ↦ upperSupportHeight_eq_affineValue K.val.val D hne x)
  refine ⟨p, hp, hpa, hpb, hcarrier, ?_, ?_⟩
  · rw [hcarrier]
    rintro q ⟨x, hx, rfl⟩
    exact pointOnGraph_upperSupportHeight_mem K D hne hD hsin (hfeasible x hx)
  · intro i
    obtain ⟨c, hc, heq⟩ := hpieces i
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
    refine ⟨t, ht, ?_, ?_⟩
    · rw [hvertices i.succ, hvertices i.castSucc]
      apply inner_pointOnGraph_sub_normalVector_eq_zero heq
        (p.increasing i.castSucc_lt_succ).le
      dsimp [upperSupportAffine]
      field_simp [(hsin t ht).ne']
      ring
    · have hstart := heq ⟨le_rfl, (p.increasing i.castSucc_lt_succ).le⟩
      rw [hvertices i.castSucc]
      simp only [pointOnGraph, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
      simp only [Real.Angle.cos_coe, Real.Angle.sin_coe]
      change Real.cos t * (p.vertices i.castSucc) 0 +
        Real.sin t * upperSupportHeight K.val.val D hne ((p.vertices i.castSucc) 0) = _
      rw [hstart]
      dsimp [upperSupportAffine, affineValue]
      field_simp [(hsin t ht).ne']
      ring

private lemma exists_upperSupportHeight_polyline_with_endpoints {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (D : Finset ℝ) (hne : D.Nonempty)
    (hD : (D : Set ℝ) = angleDomain Θ) {a b : Point}
    (ha : a ∈ (K.val.val : Set Point)) (hb : b ∈ (K.val.val : Set Point))
    (hab : a 0 < b 0)
    (hmin : ∀ q ∈ (K.val.val : Set Point), a 0 ≤ q 0)
    (hmax : ∀ q ∈ (K.val.val : Set Point), q 0 ≤ b 0) :
    ∃ p : XMonotonePolylineData, 0 < p.edges ∧ p.vertices 0 = a ∧
      p.vertices (Fin.last p.edges) = b ∧
      p.carrier = pointOnGraph (upperSupportHeight K.val.val D hne) '' Set.Icc (a 0) (b 0) ∧
      p.carrier ⊆ (K.val.val : Set Point) ∧
      ∀ i : Fin p.edges, ∃ t ∈ D,
        inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 ∧
        inner ℝ (p.vertices i.castSucc) (normalVector (t : Real.Angle)) =
          supportValue K.val.val (t : Real.Angle) := by
  have hsin : ∀ t ∈ D, 0 < Real.sin t := by
    intro t ht
    have ht' : t ∈ angleDomain Θ := hD ▸ ht
    exact Real.sin_pos_of_pos_of_lt_pi (angleDomain_subset_Ioo Θ ht').1
      (angleDomain_subset_Ioo Θ ht').2
  obtain ⟨p, hp, hpa, hpb, hc, hK, hn⟩ :=
    exists_upperSupportHeight_polyline K D hne hD hsin hab
      (fun _ hx ↦ ConvexBody.exists_mem_fst_eq_of_mem_Icc K.val.val ha hb hab hx)
  refine ⟨p, hp, ?_, ?_, hc, hK, hn⟩
  · rw [hpa]
    apply K.eq_of_mem_of_fst_eq_of_fst_extremal
      (pointOnGraph_upperSupportHeight_mem K D hne hD hsin ⟨a, ha, rfl⟩) ha rfl
    exact Or.inr hmin
  · rw [hpb]
    apply K.eq_of_mem_of_fst_eq_of_fst_extremal
      (pointOnGraph_upperSupportHeight_mem K D hne hD hsin ⟨b, hb, rfl⟩) hb rfl
    exact Or.inl hmax

/-- The terminal cap contacts bound every horizontal coordinate of a polygon cap. -/
lemma PolygonCapSpace.capVertices_fst_bounds {Θ : AngleSet} (K : PolygonCapSpace Θ)
    {q : Point} (hq : q ∈ (K.val.val : Set Point)) :
    ((capVertices K.val Θ.angle).2.1) 0 ≤ q 0 ∧
      q 0 ≤ ((capVertices K.val 0).1.2) 0 := by
  constructor
  · rw [capVertices_angle_fst_eq]
    have hu := (K.val.subset_capFan hq).1
    have hv := inner_le_supportValue K.val.val hq
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
    have hs : 0 ≤ Real.sin Θ.angle := (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
      (by linarith [Θ.angle_le, Real.pi_pos])).le
    have hc : 0 ≤ Real.cos Θ.angle := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], Θ.angle_le⟩
    change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at hu
    simp [normalVector, tangentVector, frame, PiLp.inner_apply,
      Real.Angle.cos_add_pi_div_two, Real.Angle.sin_add_pi_div_two] at hu hv ⊢
    nlinarith [congrArg (fun z : ℝ ↦ z * q 0) (Real.sin_sq_add_cos_sq Θ.angle),
      mul_nonneg hu hc, mul_le_mul_of_nonneg_right hv hs,
      sq_nonneg (Real.sin Θ.angle), sq_nonneg (Real.cos Θ.angle)]
  · have hq' := inner_le_supportValue K.val.val hq (0 : Real.Angle)
    have hA := (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).2
    change inner ℝ ((capVertices K.val 0).1.2) (normalVector (0 : Real.Angle)) =
      supportValue K.val.val (0 : Real.Angle) at hA
    simp [normalVector, frame, PiLp.inner_apply] at hq' hA
    linarith

private lemma PolygonCapSpace.exists_upperBoundary_polyline {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (D : Finset ℝ) (hne : D.Nonempty)
    (hD : (D : Set ℝ) = angleDomain Θ) :
    ∃ p : XMonotonePolylineData, 0 < p.edges ∧
      p.vertices 0 = (capVertices K.val Θ.angle).2.1 ∧
      p.vertices (Fin.last p.edges) = (capVertices K.val 0).1.2 ∧
      p.carrier = pointOnGraph (upperSupportHeight K.val.val D hne) ''
        Set.Icc (((capVertices K.val Θ.angle).2.1) 0)
          (((capVertices K.val 0).1.2) 0) ∧
      p.carrier ⊆ (K.val.val : Set Point) ∧
      ∀ i : Fin p.edges, ∃ t ∈ D,
        inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 ∧
        inner ℝ (p.vertices i.castSucc) (normalVector (t : Real.Angle)) =
          supportValue K.val.val (t : Real.Angle) := by
  apply exists_upperSupportHeight_polyline_with_endpoints K D hne hD
    (edgeVertices_fst_mem K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).1
    (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).1
    (polygonCap_left_x_lt_right_x K)
  · exact fun q hq ↦ (K.capVertices_fst_bounds hq).1
  · exact fun q hq ↦ (K.capVertices_fst_bounds hq).2

private lemma PolygonCapSpace.exposedEdge_eq_upperSupportGraph_inter {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (D : Finset ℝ) (hne : D.Nonempty)
    (hD : (D : Set ℝ) = angleDomain Θ) {t : ℝ} (ht : t ∈ D) :
    exposedEdge K.val.val (t : Real.Angle) =
      (pointOnGraph (upperSupportHeight K.val.val D hne) ''
        Set.Icc (((capVertices K.val Θ.angle).2.1) 0)
          (((capVertices K.val 0).1.2) 0)) ∩
      {q | inner ℝ q (normalVector (t : Real.Angle)) =
        supportValue K.val.val (t : Real.Angle)} := by
  have hsin : ∀ r ∈ D, 0 < Real.sin r := by
    intro r hr
    have hr' : r ∈ angleDomain Θ := hD ▸ hr
    exact Real.sin_pos_of_pos_of_lt_pi (angleDomain_subset_Ioo Θ hr').1
      (angleDomain_subset_Ioo Θ hr').2
  ext q
  constructor
  · rintro ⟨hq, heq⟩
    refine ⟨⟨q 0, K.capVertices_fst_bounds hq, ?_⟩, heq⟩
    have hle : q 1 ≤ upperSupportHeight K.val.val D hne (q 0) :=
      (snd_le_upperSupportHeight_iff K.val.val D hne hsin q).mpr
        (fun r _ ↦ inner_le_supportValue K.val.val hq _)
    have hge := Finset.inf'_le (fun r ↦ affineValue (upperSupportAffine K.val.val r) (q 0)) ht
    have haff : affineValue (upperSupportAffine K.val.val t) (q 0) = q 1 := by
      change inner ℝ q (normalVector (t : Real.Angle)) =
        supportValue K.val.val (t : Real.Angle) at heq
      simp [normalVector, frame, PiLp.inner_apply] at heq
      dsimp [affineValue, upperSupportAffine]
      field_simp [(hsin t ht).ne']
      nlinarith [heq]
    have hy : upperSupportHeight K.val.val D hne (q 0) = q 1 :=
      le_antisymm (haff ▸ hge) hle
    ext i
    fin_cases i
    · rfl
    · exact hy
  · rintro ⟨⟨x, hx, rfl⟩, heq⟩
    refine ⟨pointOnGraph_upperSupportHeight_mem K D hne hD hsin ?_, heq⟩
    exact ConvexBody.exists_mem_fst_eq_of_mem_Icc K.val.val
      (edgeVertices_fst_mem K.val.val
        ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).1
      (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).1
      (polygonCap_left_x_lt_right_x K) hx

/-- The sine-weighted exposed-face lengths equal the horizontal separation of cap contacts. -/
lemma PolygonCapSpace.sum_hausdorffMeasure_exposedEdge_mul_sin {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (D : Finset ℝ) (hne : D.Nonempty)
    (hD : (D : Set ℝ) = angleDomain Θ) :
    ∑ t ∈ D, (Measure.hausdorffMeasure 1 (exposedEdge K.val.val (t : Real.Angle))).toReal *
      Real.sin t = ((capVertices K.val 0).1.2) 0 - ((capVertices K.val Θ.angle).2.1) 0 := by
  classical
  obtain ⟨p, hp, hpa, hpb, hc, hK, hn⟩ := K.exists_upperBoundary_polyline D hne hD
  have hangle : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi := by
    intro t ht
    exact angleDomain_subset_Ioo Θ (hD ▸ ht)
  have hface (t : ℝ) (ht : t ∈ D) :
      (Measure.hausdorffMeasure 1 (exposedEdge K.val.val (t : Real.Angle))).toReal =
        ∑ i : Fin p.edges,
          if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
            (normalVector (t : Real.Angle)) = 0 then
            dist (p.vertices i.castSucc) (p.vertices i.succ) else 0 := by
    rw [K.exposedEdge_eq_upperSupportGraph_inter D hne hD ht, ← hc]
    apply p.toReal_hausdorffMeasure_carrier_inter_hyperplane
    intro i hi
    obtain ⟨r, hr, horth, hstart⟩ := hn i
    have hrt := eq_of_inner_sub_normalVector_eq_zero (hangle r hr) (hangle t ht)
      (p.increasing i.castSucc_lt_succ) horth hi
    subst r
    intro q hq
    rw [segment_eq_image'] at hq
    obtain ⟨c, hcoef, rfl⟩ := hq
    change inner ℝ (p.vertices i.castSucc + c •
      (p.vertices i.succ - p.vertices i.castSucc)) (normalVector (t : Real.Angle)) = _
    rw [inner_add_left, real_inner_smul_left, hi, mul_zero, add_zero, hstart]
  calc
    _ = ∑ t ∈ D, (∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * Real.sin t := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hface t ht]
    _ = _ := by
      rw [p.sum_normal_lengths_mul_sin D hangle
        (fun i ↦ by obtain ⟨t, ht, ho, _⟩ := hn i; exact ⟨t, ht, ho⟩), hpa, hpb]

end MovingSofa

end

end

end
