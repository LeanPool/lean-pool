/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Infrastructure.Analysis.Foundations.Development002
public import LeanPool.MovingSofa.Analysis.Foundations.Development004
public import LeanPool.MovingSofa.Analysis.Foundations.Development003
public import LeanPool.MovingSofa.Cap.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001

public import LeanPool.MovingSofa.Geometry.Foundations.Development005
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
/-!
# Moving sofa: related mathematical developments

* `Analysis.Stieltjes.ConvexBoundary`.
* `Analysis.SurfaceMeasure.Polygon`.
* `Analysis.SurfaceMeasure.BoundaryLimit`.
* `Analysis.SurfaceMeasure.DiscreteBounds`.
* `Analysis.SurfaceMeasure.Integrals`.
* `Analysis.SurfaceMeasure.VertexBoundary`.
* `Analysis.SurfaceMeasure.AngularDensity`.
* `Analysis.SurfaceMeasure.FrameProducts`.
* `Analysis.SurfaceMeasure.Boundary`.
* `Analysis.SurfaceMeasure.Linearity`.
* `Analysis.SurfaceMeasure.OppositeDensity`.
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
# Analysis / Stieltjes / Convex Boundary
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace MovingSofa

/-- Each coordinate of the positive vertex is right-continuous and has bounded
variation on its closed interval domain. -/
theorem exists_positiveVertex_intervalBV (K : ConvexBody Point) {a b : ℝ} (hab : a ≤ b) :
    ∃ f : Fin 2 → RightContinuousIntervalBV a b,
      ∀ i t, (f i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i := by
  have hv : BoundedVariationOn
      (fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) Set.univ := by
    exact ne_top_of_le_ne_top (positiveVertex_boundedVariation K a b hab)
      (eVariationOn.comp_le_of_monotoneOn
        (fun t : ℝ ↦ (edgeVertices K (t : Real.Angle)).1)
        (s := Set.Icc a b) (t := Set.univ) (fun t : Set.Icc a b ↦ (t : ℝ))
        (fun _ _ _ _ h ↦ h) (fun t _ ↦ t.property))
  have hc (i : Fin 2) : IsIntervalBoundedVariation a b
      (fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1 i) := by
    change BoundedVariationOn ((fun p : Point ↦ p i) ∘
      fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) Set.univ
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).lipschitzWith.comp_boundedVariationOn
      (g := fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) hv
  have hr (i : Fin 2) (t : Set.Icc a b) : ContinuousWithinAt
      (fun s : Set.Icc a b ↦ (edgeVertices K ((s : ℝ) : Real.Angle)).1 i)
      (Set.Ici t) t := by
    have h : ContinuousWithinAt (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).1)
        (Set.Ici (t : ℝ)) (t : ℝ) :=
      continuousWithinAt_Ioi_iff_Ici.mp (contact_oneSided_limits K (t : ℝ)).1
    have hcomp : ContinuousWithinAt
        (fun s : Set.Icc a b ↦ (edgeVertices K ((s : ℝ) : Real.Angle)).1)
        (Set.Ici t) t := h.comp
      (show ContinuousWithinAt (fun s : Set.Icc a b ↦ (s : ℝ)) (Set.Ici t) t from
        continuous_subtype_val.continuousWithinAt) (fun _ hy ↦ hy)
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).continuous.continuousAt
      |>.comp_continuousWithinAt hcomp
  exact ⟨fun i ↦ ⟨_, hc i, hr i⟩, fun _ _ ↦ rfl⟩

/-- Each coordinate of the positive vertex is measurable on the closed parameter interval,
being the difference of two monotone functions by bounded variation. -/
theorem measurable_positiveVertex_coordinate (K : ConvexBody Point) {a b : ℝ}
    (hab : a ≤ b) (i : Fin 2) :
    Measurable fun t : Set.Icc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).1 i := by
  obtain ⟨f, hf⟩ := exists_positiveVertex_intervalBV K hab
  have hfun : (fun t : Set.Icc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).1 i) =
      (f i).toFun := by
    funext t
    exact (hf i t).symm
  have hbv : LocallyBoundedVariationOn (f i).toFun (Set.univ : Set (Set.Icc a b)) :=
    (f i).boundedVariation.locallyBoundedVariationOn
  obtain ⟨p, q, hp, hq, hpq⟩ := hbv.exists_monotoneOn_sub_monotoneOn
  rw [hfun, hpq]
  exact (monotoneOn_univ.mp hp).measurable.sub (monotoneOn_univ.mp hq).measurable

/-- Each coordinate of the positive vertex is measurable on the half-open parameter
interval. -/
theorem measurable_positiveVertex_coordinate_Ioc (K : ConvexBody Point) {a b : ℝ}
    (hab : a ≤ b) (i : Fin 2) :
    Measurable fun t : Set.Ioc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).1 i := by
  have hpos := measurable_positiveVertex_coordinate K hab i
  have hmem (t : Set.Ioc a b) : (t : ℝ) ∈ Set.Icc a b := ⟨t.property.1.le, t.property.2⟩
  have hcont : Continuous fun t : Set.Ioc a b ↦ (⟨(t : ℝ), hmem t⟩ : Set.Icc a b) :=
    Continuous.subtype_mk continuous_subtype_val hmem
  have hcomp : Measurable
      ((fun s : Set.Icc a b ↦ (edgeVertices K (((s : ℝ) : Real.Angle))).1 i) ∘
        fun t : Set.Ioc a b ↦ (⟨(t : ℝ), hmem t⟩ : Set.Icc a b)) :=
    hpos.comp hcont.measurable
  have hfun : ((fun s : Set.Icc a b ↦ (edgeVertices K (((s : ℝ) : Real.Angle))).1 i) ∘
      fun t : Set.Ioc a b ↦ (⟨(t : ℝ), hmem t⟩ : Set.Icc a b)) =
      fun t : Set.Ioc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).1 i := by
    funext t
    rfl
  rwa [hfun] at hcomp

/-- Each coordinate of the negative vertex is measurable on the half-open parameter interval,
being the pointwise left limit of the positive vertex. -/
theorem measurable_negativeVertex_coordinate (K : ConvexBody Point) {a b : ℝ}
    (hab : a ≤ b) (i : Fin 2) :
    Measurable fun t : Set.Ioc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).2 i := by
  have hpos := measurable_positiveVertex_coordinate K hab i
  have hmem (n : ℕ) (t : Set.Ioc a b) :
      max a ((t : ℝ) - 1 / (n + 1 : ℝ)) ∈ Set.Icc a b := by
    refine ⟨le_max_left _ _, max_le hab ?_⟩
    have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith [t.property.2]
  set g : ℕ → Set.Ioc a b → ℝ := fun n t ↦
    (edgeVertices K ((max a ((t : ℝ) - 1 / (n + 1 : ℝ)) : ℝ) : Real.Angle)).1 i
  have hgmeas (n : ℕ) : Measurable (g n) := by
    have hcont : Continuous fun t : Set.Ioc a b ↦ (⟨max a ((t : ℝ) - 1 / (n + 1 : ℝ)),
        hmem n t⟩ : Set.Icc a b) :=
      Continuous.subtype_mk
        (continuous_const.max (continuous_subtype_val.sub continuous_const)) (hmem n)
    have hcomp : Measurable
        ((fun s : Set.Icc a b ↦ (edgeVertices K (((s : ℝ) : Real.Angle))).1 i) ∘
          fun t : Set.Ioc a b ↦ (⟨max a ((t : ℝ) - 1 / (n + 1 : ℝ)),
            hmem n t⟩ : Set.Icc a b)) :=
      hpos.comp hcont.measurable
    have hfun :
        ((fun s : Set.Icc a b ↦ (edgeVertices K (((s : ℝ) : Real.Angle))).1 i) ∘
          fun t : Set.Ioc a b ↦ (⟨max a ((t : ℝ) - 1 / (n + 1 : ℝ)),
            hmem n t⟩ : Set.Icc a b)) = g n := by
      funext t
      rfl
    rwa [hfun] at hcomp
  refine measurable_of_tendsto_metrizable hgmeas (tendsto_pi_nhds.2 fun t ↦ ?_)
  have hta : a < (t : ℝ) := t.property.1
  have hlim := (contact_oneSided_limits K (t : ℝ)).2.2.2.1
  have hlimi : Filter.Tendsto (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).1 i)
      (𝓝[<] (t : ℝ)) (𝓝 ((edgeVertices K ((t : ℝ) : Real.Angle)).2 i)) :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).continuous.tendsto _).comp hlim
  refine hlimi.comp ?_
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h0 : Filter.Tendsto (fun n : ℕ ↦ (t : ℝ) - 1 / (n + 1 : ℝ))
        Filter.atTop (𝓝 (t : ℝ)) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_sub ((t : ℝ))
    have hconst : Filter.Tendsto (fun _ : ℕ ↦ a) Filter.atTop (𝓝 a) := tendsto_const_nhds
    have h1 := hconst.max h0
    rwa [max_eq_right hta.le] at h1
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / ((t : ℝ) - a))
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hpos : (0 : ℝ) < (t : ℝ) - a := by linarith
    have hNle : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    have hlt : 1 / (n + 1 : ℝ) < (t : ℝ) - a := by
      have h1 : 1 / ((t : ℝ) - a) < (n + 1 : ℝ) := by linarith
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℝ))]
      rw [div_lt_iff₀ hpos] at h1
      linarith
    have hmaxeq : max a ((t : ℝ) - 1 / (n + 1 : ℝ)) = (t : ℝ) - 1 / (n + 1 : ℝ) :=
      max_eq_right (by linarith)
    rw [Set.mem_Iio, hmaxeq]
    have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
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
# Analysis / Surface Measure / Polygon
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

private def quarterTurn (p : Point) : Point := !₂[-p 1, p 0]

private theorem quarterTurn_ne_zero {p : Point} (hp : p ≠ 0) : quarterTurn p ≠ 0 := by
  intro h
  apply hp
  ext i
  fin_cases i
  · exact congrFun (congrArg WithLp.ofLp h) 1
  · simpa [quarterTurn] using congrFun (congrArg WithLp.ofLp h) 0

private theorem inner_quarterTurn (p : Point) : inner ℝ p (quarterTurn p) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [quarterTurn, dotProduct, Fin.sum_univ_two]
  ring

private theorem inner_normalVector_vectorNormalAngle_quarterTurn {p : Point} (hp : p ≠ 0) :
    inner ℝ p (normalVector (vectorNormalAngle (quarterTurn p))) = 0 := by
  rw [normalVector_vectorNormalAngle (quarterTurn_ne_zero hp), inner_smul_right,
    inner_quarterTurn, mul_zero]

/-- A nonzero planar direction has only finitely many perpendicular angular normals. -/
theorem finite_orthogonalNormal_angles {p : Point} (hp : p ≠ 0) :
    Set.Finite {t : Real.Angle | inner ℝ p (normalVector t) = 0} := by
  let t₀ := vectorNormalAngle (quarterTurn p)
  apply Set.Finite.subset
    ((Set.finite_singleton (t₀ + (Real.pi : Real.Angle))).insert t₀)
  intro t ht
  have h := normalVector_eq_or_eq_add_pi_of_orthogonal hp ht
    (inner_normalVector_vectorNormalAngle_quarterTurn hp)
  rcases h with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl h)
  · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h))

/-- The possible normals perpendicular to differences of points in a finite set are finite. -/
theorem finite_pairDifferenceNormal_angles (V : Finset Point) :
    Set.Finite {t : Real.Angle | ∃ p ∈ V, ∃ q ∈ V,
      p ≠ q ∧ inner ℝ (p - q) (normalVector t) = 0} := by
  classical
  let N : Point → Point → Set Real.Angle := fun p q ↦
    if h : p = q then ∅ else {t | inner ℝ (p - q) (normalVector t) = 0}
  have hN (p q : Point) : Set.Finite (N p q) := by
    by_cases h : p = q
    · simp [N, h]
    · simpa [N, h] using finite_orthogonalNormal_angles (sub_ne_zero.mpr h)
  apply Set.Finite.subset (V.finite_toSet.biUnion fun p _ ↦
    V.finite_toSet.biUnion fun q _ ↦ hN p q)
  rintro t ⟨p, hp, q, hq, hpq, ht⟩
  apply Set.mem_iUnion₂.mpr
  refine ⟨p, hp, Set.mem_iUnion₂.mpr ⟨q, hq, ?_⟩⟩
  simp [N, hpq, ht]

private theorem isExposed_exposedEdge (K : ConvexBody Point) (t : Real.Angle) :
    IsExposed ℝ (K : Set Point) (exposedEdge K t) := by
  intro _
  refine ⟨innerSL ℝ (normalVector t), ?_⟩
  ext p
  simp only [Set.mem_ofPred_eq, innerSL_apply_apply, real_inner_comm]
  constructor
  · intro hp
    refine ⟨hp.1, fun q hq ↦ ?_⟩
    rw [hp.2]
    exact inner_le_supportValue K hq t
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, le_antisymm (inner_le_supportValue K hp t) ?_⟩
    apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    exact hmax q hq

private theorem isExposed_singleton_edgeVertices_fst (K : ConvexBody Point)
    (t : Real.Angle) :
    IsExposed ℝ (exposedEdge K t) {(edgeVertices K t).1} := by
  intro _
  refine ⟨innerSL ℝ (tangentVector t), ?_⟩
  ext p
  simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, innerSL_apply_apply,
    real_inner_comm]
  constructor
  · rintro rfl
    refine ⟨edgeVertices_fst_mem K t, fun q hq ↦ ?_⟩
    rw [inner_edgeVertices_fst_tangent]
    exact le_csSup ((isCompact_exposedEdge K t).image
      (continuous_id.inner continuous_const)).bddAbove ⟨q, hq, rfl⟩
  · rintro ⟨hp, hmax⟩
    have htangent : inner ℝ p (tangentVector t) =
        inner ℝ (edgeVertices K t).1 (tangentVector t) := by
      apply le_antisymm
      · rw [inner_edgeVertices_fst_tangent]
        exact le_csSup ((isCompact_exposedEdge K t).image
          (continuous_id.inner continuous_const)).bddAbove ⟨p, hp, rfl⟩
      · exact hmax _ (edgeVertices_fst_mem K t)
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul p t,
      ← inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K t).1 t,
      hp.2, (edgeVertices_fst_mem K t).2, htangent]

private theorem isExposed_singleton_edgeVertices_snd (K : ConvexBody Point)
    (t : Real.Angle) :
    IsExposed ℝ (exposedEdge K t) {(edgeVertices K t).2} := by
  intro _
  refine ⟨innerSL ℝ (-tangentVector t), ?_⟩
  ext p
  simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, innerSL_apply_apply,
    real_inner_comm, inner_neg_left]
  constructor
  · rintro rfl
    refine ⟨edgeVertices_snd_mem K t, fun q hq ↦ neg_le_neg ?_⟩
    rw [inner_edgeVertices_snd_tangent]
    exact csInf_le ((isCompact_exposedEdge K t).image
      (continuous_id.inner continuous_const)).bddBelow ⟨q, hq, rfl⟩
  · rintro ⟨hp, hmax⟩
    have htangent : inner ℝ p (tangentVector t) =
        inner ℝ (edgeVertices K t).2 (tangentVector t) := by
      apply le_antisymm
      · exact neg_le_neg_iff.mp (hmax _ (edgeVertices_snd_mem K t))
      · rw [inner_edgeVertices_snd_tangent]
        exact csInf_le ((isCompact_exposedEdge K t).image
          (continuous_id.inner continuous_const)).bddBelow ⟨p, hp, rfl⟩
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul p t,
      ← inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K t).2 t,
      hp.2, (edgeVertices_snd_mem K t).2, htangent]

/-- Both endpoints of a polygon's exposed edge belong to its finite generating set. -/
theorem edgeVertices_mem_of_eq_convexHull (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) (t : Real.Angle) :
    (edgeVertices K t).1 ∈ V ∧ (edgeVertices K t).2 ∈ V := by
  have hedge := (isExposed_exposedEdge K t).isExtreme
  constructor
  · have hext : (edgeVertices K t).1 ∈ Set.extremePoints ℝ (K : Set Point) :=
      (hedge.trans (isExposed_singleton_edgeVertices_fst K t).isExtreme).mem_extremePoints
    rw [hKV] at hext
    exact Finset.mem_coe.mp (extremePoints_convexHull_subset hext)
  · have hext : (edgeVertices K t).2 ∈ Set.extremePoints ℝ (K : Set Point) :=
      (hedge.trans (isExposed_singleton_edgeVertices_snd K t).isExtreme).mem_extremePoints
    rw [hKV] at hext
    exact Finset.mem_coe.mp (extremePoints_convexHull_subset hext)

/-- Every proper edge normal of a finite convex hull is one of finitely many pair normals. -/
theorem finite_properEdgeNormal_angles (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) :
    Set.Finite {t : Real.Angle | (edgeVertices K t).1 ≠ (edgeVertices K t).2} := by
  apply (finite_pairDifferenceNormal_angles V).subset
  intro t ht
  refine ⟨(edgeVertices K t).1, (edgeVertices_mem_of_eq_convexHull K V hKV t).1,
    (edgeVertices K t).2, (edgeVertices_mem_of_eq_convexHull K V hKV t).2, ht, ?_⟩
  rw [inner_sub_left, (edgeVertices_fst_mem K t).2, (edgeVertices_snd_mem K t).2,
    sub_self]

private theorem continuousAt_positiveVertex_of_eq_negativeVertex (K : ConvexBody Point)
    (t : ℝ) (ht : (edgeVertices K (t : Real.Angle)).1 =
      (edgeVertices K (t : Real.Angle)).2) :
    ContinuousAt (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).1) t := by
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · show Tendsto _ (𝓝[<] t) _
    simpa only [ht] using (contact_oneSided_limits K t).2.2.2.1
  · show Tendsto _ (𝓝[>] t) _
    exact (contact_oneSided_limits K t).1

/-- Away from a proper-edge normal, the positive vertex of a finite convex hull is locally
constant. -/
theorem eventuallyEq_positiveVertex_of_eq_convexHull (K : ConvexBody Point)
    (V : Finset Point) (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (t : ℝ) (ht : (edgeVertices K (t : Real.Angle)).1 =
      (edgeVertices K (t : Real.Angle)).2) :
    ∀ᶠ s : ℝ in 𝓝 t, (edgeVertices K (s : Real.Angle)).1 =
      (edgeVertices K (t : Real.Angle)).1 := by
  classical
  let v := (edgeVertices K (t : Real.Angle)).1
  let W : Set Point := (↑(V.erase v) : Set Point)
  have hvV : v ∈ V := (edgeVertices_mem_of_eq_convexHull K V hKV _).1
  have hvW : v ∈ Wᶜ := by simp [W, hvV]
  have hopen : IsOpen Wᶜ := (V.erase v).finite_toSet.isClosed.isOpen_compl
  have hnhds : Wᶜ ∈ 𝓝 v := hopen.mem_nhds hvW
  have htend :=
    (continuousAt_positiveVertex_of_eq_negativeVertex K t ht).eventually hnhds
  exact htend.mono (by
    intro s hs
    have hsV : (edgeVertices K (s : Real.Angle)).1 ∈ V :=
      (edgeVertices_mem_of_eq_convexHull K V hKV _).1
    by_contra hne
    have hnev : (edgeVertices K (s : Real.Angle)).1 ≠ v := by simpa [v] using hne
    exact hs (by simp [W, hsV, hnev]))

/-- For a two-dimensional finite convex hull, surface measure is supported on its finite set of
proper-edge normals. -/
theorem surfaceAreaMeasure_compl_properEdgeNormals_eq_zero
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (hint : (interior (K : Set Point)).Nonempty) :
    surfaceAreaMeasure K {t | (edgeVertices K t).1 = (edgeVertices K t).2} = 0 := by
  let N : Set Real.Angle := {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}
  have hNfinite : N.Finite := finite_properEdgeNormal_angles K V hKV
  have hmeas : MeasurableSet Nᶜ := hNfinite.measurableSet.compl
  have hface := (surfaceAreaMeasure_face_union K).2.2.2.2 Nᶜ hmeas (Or.inl hint)
  have hunion : (⋃ t ∈ Nᶜ, exposedEdge K t) ⊆ (V : Set Point) := by
    intro p hp
    obtain ⟨t, htN, hpt⟩ := Set.mem_iUnion₂.mp hp
    have ht : (edgeVertices K t).1 = (edgeVertices K t).2 := by
      simpa only [N, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using htN
    have hp' : p = (edgeVertices K t).1 := by
      rw [exposedEdge_eq_segment_edgeVertices, ← ht] at hpt
      simpa using hpt
    rw [hp']
    exact (edgeVertices_mem_of_eq_convexHull K V hKV t).1
  rw [show {t | (edgeVertices K t).1 = (edgeVertices K t).2} = Nᶜ by
    ext t
    simp [N], hface]
  let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact measure_mono_null hunion
    (V.finite_toSet.measure_zero (Measure.hausdorffMeasure 1))

/-- Surface measure of any finite convex hull, including a point or segment, is supported on its
finite set of proper-edge normals. -/
theorem surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_eq_convexHull
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) :
    surfaceAreaMeasure K {t | (edgeVertices K t).1 = (edgeVertices K t).2} = 0 := by
  by_cases hsub : (K : Set Point).Subsingleton
  · rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hsub]
    simp
  by_cases hint : (interior (K : Set Point)).Nonempty
  · exact surfaceAreaMeasure_compl_properEdgeNormals_eq_zero K V hKV hint
  obtain ⟨d, hd⟩ := exists_segmentPresentation_of_interior_empty K hsub
    (Set.not_nonempty_iff_eq_empty.mp hint)
  have hproper (u : Real.Angle)
      (hu : inner ℝ (d.2.1 - d.1) (normalVector u) = 0) :
      (edgeVertices K u).1 ≠ (edgeVertices K u).2 := by
    intro heq
    have hedge := exposedEdge_eq_segment_of_orthogonal K d hd u hu
    have hsingle : (K : Set Point).Subsingleton := by
      rw [← hedge, exposedEdge_eq_segment_edgeVertices, heq]
      simp
    exact hsub hsingle
  have hpi : inner ℝ (d.2.1 - d.1)
      (normalVector (d.2.2 + (Real.pi : Real.Angle))) = 0 := by
    have hn : normalVector (d.2.2 + (Real.pi : Real.Angle)) =
        -normalVector d.2.2 := by
      induction d.2.2 using Real.Angle.induction_on with
      | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
    rw [hn, inner_neg_right, hd.2.2, neg_zero]
  rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
  simp [hproper d.2.2 hd.2.2, hproper _ hpi]

/-- Surface measure is carried by the proper edge normals as soon as these are finitely many
and the degenerate faces lie in a one-dimensional null set. -/
theorem surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_finite_carrier
    (K : ConvexBody Point)
    (hN : {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}.Finite)
    (V : Set Point) (hV : Measure.hausdorffMeasure 1 V = 0)
    (hcarrier : (⋃ t ∈ {t | (edgeVertices K t).1 = (edgeVertices K t).2},
      exposedEdge K t) ⊆ V) :
    surfaceAreaMeasure K {t | (edgeVertices K t).1 = (edgeVertices K t).2} = 0 := by
  let N : Set Real.Angle := {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}
  have hset : {t | (edgeVertices K t).1 = (edgeVertices K t).2} = Nᶜ := by
    ext t
    simp [N]
  by_cases hsub : (K : Set Point).Subsingleton
  · rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hsub]
    simp
  by_cases hint : (interior (K : Set Point)).Nonempty
  · rw [hset, (surfaceAreaMeasure_face_union K).2.2.2.2 Nᶜ
      hN.measurableSet.compl (Or.inl hint)]
    exact measure_mono_null (by simpa only [hset] using hcarrier) hV
  obtain ⟨d, hd⟩ := exists_segmentPresentation_of_interior_empty K hsub
    (Set.not_nonempty_iff_eq_empty.mp hint)
  have hproper (u : Real.Angle)
      (hu : inner ℝ (d.2.1 - d.1) (normalVector u) = 0) :
      (edgeVertices K u).1 ≠ (edgeVertices K u).2 := by
    intro heq
    have hedge := exposedEdge_eq_segment_of_orthogonal K d hd u hu
    have hsingle : (K : Set Point).Subsingleton := by
      rw [← hedge, exposedEdge_eq_segment_edgeVertices, heq]
      simp
    exact hsub hsingle
  have hpi : inner ℝ (d.2.1 - d.1)
      (normalVector (d.2.2 + (Real.pi : Real.Angle))) = 0 := by
    rw [normalVector_add_pi_angle, inner_neg_right, hd.2.2, neg_zero]
  rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
  simp [hproper d.2.2 hd.2.2, hproper _ hpi]

/-- The surface integral of an arbitrary integrand over a finite convex hull is the sum of its
proper-edge atoms, including the point and segment cases. No regularity of the integrand is
needed: the measure is carried by a finite set. -/
theorem integral_surfaceAreaMeasure_eq_sum_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (φ : Real.Angle → ℝ) (E : Set Real.Angle) (hE : MeasurableSet E) :
    ∫ t in E, φ t ∂surfaceAreaMeasure K =
      Finset.sum ((finite_properEdgeNormal_angles K V hKV).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K).real {t} * φ t) := by
  classical
  let N : Set Real.Angle := {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}
  have hNfinite : N.Finite := finite_properEdgeNormal_angles K V hKV
  have hae : ∀ᵐ t ∂surfaceAreaMeasure K, t ∈ N := by
    rw [ae_iff]
    simpa only [N, Set.mem_ofPred_eq, not_ne_iff] using
      surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_eq_convexHull K V hKV
  have hrestrict : (surfaceAreaMeasure K).restrict N = surfaceAreaMeasure K :=
    Measure.restrict_eq_self_of_ae_mem hae
  let _ := (surfaceAreaMeasure_face_union K).1
  have hEN : E ∩ N = ↑(hNfinite.inter_of_left E).toFinset := by
    ext t
    simp [N, and_comm]
  calc
    ∫ t in E, φ t ∂surfaceAreaMeasure K =
        ∫ t in E, φ t ∂(surfaceAreaMeasure K).restrict N := by rw [hrestrict]
    _ = ∫ t in E ∩ N, φ t ∂surfaceAreaMeasure K := by
      rw [Measure.restrict_restrict hE]
    _ = _ := by
      rw [hEN]
      exact MeasureTheory.setIntegral_finset _
        (μ := surfaceAreaMeasure K) (f := φ) IntegrableOn.finset

/-- The coordinate tangent integral of a finite convex hull is the sum of its proper-edge atoms,
including the point and segment cases. -/
theorem integral_tangentCoordinate_surfaceAreaMeasure_eq_sum_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (i : Fin 2) (E : Set Real.Angle) (hE : MeasurableSet E) :
    ∫ t in E, tangentVector t i ∂surfaceAreaMeasure K =
      Finset.sum ((finite_properEdgeNormal_angles K V hKV).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K).real {t} * tangentVector t i) :=
  integral_surfaceAreaMeasure_eq_sum_properEdgeNormals K V hKV
    (fun t ↦ tangentVector t i) E hE

/-- On a real interval, the coordinate Stieltjes measure of a polygon's positive vertex is
supported at proper-edge normals (apart from the excluded left endpoint). -/
theorem intervalStieltjesMeasure_variation_eq_zero_off_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hab : a < b) (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i) (i : Fin 2) :
    (intervalStieltjesMeasure (f i)).variation
      {t | a < (t : ℝ) ∧ (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 =
        (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).2} = 0 := by
  let T : Set (Set.Icc a b) :=
    {t | a < (t : ℝ) ∧ (edgeVertices K ((t : ℝ) : Real.Angle)).1 =
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  change (f i).boundedVariation.vectorMeasure.variation T = 0
  apply measure_null_of_locally_null T
  intro x hx
  have hconst := eventuallyEq_positiveVertex_of_eq_convexHull K V hKV (x : ℝ) hx.2
  have hconst' : (f i).toFun =ᶠ[𝓝 x] fun _ ↦ (f i).toFun x := by
    filter_upwards [continuousAt_subtype_val.eventually hconst] with y hy
    rw [hf i y, hf i x, hy]
  obtain ⟨U, hU, hUzero⟩ :=
    BoundedVariationOn.exists_nhds_variation_vectorMeasure_eq_zero_of_eventuallyEq_const
    hab (f i).boundedVariation (f i).right_continuous x hx.1 hconst'
  exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, hUzero⟩

/-- The left limit of a positive-vertex coordinate at a noninitial parameter is the corresponding
coordinate of the negative vertex. -/
theorem leftLim_positiveVertex_coordinate
    (K : ConvexBody Point) {a b : ℝ} (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (i : Fin 2) (t : Set.Icc a b) (ht : a < (t : ℝ)) :
    Function.leftLim (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).2 i := by
  have hab : a < b := ht.trans_le t.property.2
  let _ : Fact (a ≤ b) := ⟨hab.le⟩
  let _ : Nontrivial (Set.Icc a b) :=
    ⟨⟨⟨a, le_rfl, hab.le⟩, ⟨b, hab.le, le_rfl⟩, fun h ↦
      hab.ne (congrArg Subtype.val h)⟩⟩
  have hcoe : Tendsto (fun s : Set.Icc a b ↦ (s : ℝ)) (𝓝[<] t) (𝓝[<] (t : ℝ)) := by
    rw [nhdsWithin_subtype, Set.image_subtype_val_Icc_Iio,
      nhdsWithin_Ico_eq_nhdsLT ht]
    exact tendsto_comap
  have hcontact := ((contact_oneSided_limits K (t : ℝ)).2.2.2.1).comp hcoe
  have hcoord := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).continuous.continuousAt
    |>.tendsto.comp hcontact
  have hfleft := (f i).boundedVariation.tendsto_leftLim t
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨⊥, ht⟩
  apply tendsto_nhds_unique hfleft
  apply hcoord.congr
  intro s
  simpa [Function.comp_apply] using (hf i s).symm

/-- Each noninitial Stieltjes atom of a positive-vertex coordinate is the corresponding
coordinate of the tangent-weighted surface-measure atom. -/
theorem intervalStieltjesMeasure_singleton_positiveVertex
    (K : ConvexBody Point) {a b : ℝ} (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (i : Fin 2) (t : Set.Icc a b) (ht : a < (t : ℝ)) :
    intervalStieltjesMeasure (f i) {t} =
      (surfaceAreaMeasure K {((t : ℝ) : Real.Angle)}).toReal *
        tangentVector ((t : ℝ) : Real.Angle) i := by
  rw [intervalStieltjesMeasure, (f i).boundedVariation.vectorMeasure_singleton,
    (f i).right_continuous t |>.rightLim_eq,
    leftLim_positiveVertex_coordinate K f hf i t ht, hf]
  have h := congrArg (fun p : Point ↦ p i)
    (surfaceAreaMeasure_atom_length K ((t : ℝ) : Real.Angle)).2.2
  simpa [PiLp.smul_apply] using congrArg (fun z : ℝ ↦
    z - (edgeVertices K ((t : ℝ) : Real.Angle)).2 i) h

/-- A proper-edge normal has only finitely many lifts in a half-open interval of length at most one
full turn. -/
theorem finite_properEdgeNormal_lifts (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi) :
    Set.Finite {t : Set.Icc a b | a < (t : ℝ) ∧
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 ≠
        (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).2} := by
  let S : Set (Set.Icc a b) := {t | a < (t : ℝ) ∧
    (edgeVertices K ((t : ℝ) : Real.Angle)).1 ≠
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  let N : Set Real.Angle :=
    {u | (edgeVertices K u).1 ≠ (edgeVertices K u).2}
  let c : Set.Icc a b → Real.Angle := fun t ↦ ((t : ℝ) : Real.Angle)
  let _ : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  change S.Finite
  apply Set.Finite.of_finite_image
  · apply (finite_properEdgeNormal_angles K V hKV).subset
    rintro _ ⟨t, ht, rfl⟩
    exact ht.2
  · intro x hx y hy hxy
    apply Subtype.ext
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ioc
      (p := 2 * Real.pi) ⟨hx.1, x.property.2.trans hturn⟩
      ⟨hy.1, y.property.2.trans hturn⟩).mp
    change ((x : ℝ) : Real.Angle) = ((y : ℝ) : Real.Angle)
    simpa [c] using hxy

/-- On a polygon, every measurable noninitial set has Stieltjes mass equal to the finite sum of
its proper-edge atoms. -/
theorem intervalStieltjesMeasure_eq_sum_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (i : Fin 2) (E : Set (Set.Icc a b)) (hE : MeasurableSet E)
    (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    intervalStieltjesMeasure (f i) E =
      Finset.sum ((finite_properEdgeNormal_lifts K V hKV hturn).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K
          {(((t : Set.Icc a b) : ℝ) : Real.Angle)}).toReal *
            tangentVector (((t : Set.Icc a b) : ℝ) : Real.Angle) i) := by
  classical
  let S : Set (Set.Icc a b) := {t | a < (t : ℝ) ∧
    (edgeVertices K ((t : ℝ) : Real.Angle)).1 ≠
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  let T : Set (Set.Icc a b) := {t | a < (t : ℝ) ∧
    (edgeVertices K ((t : ℝ) : Real.Angle)).1 =
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  let μ := intervalStieltjesMeasure (f i)
  change μ E = _
  have hSfinite : S.Finite := finite_properEdgeNormal_lifts K V hKV hturn
  have hTzero : μ.variation T = 0 :=
    intervalStieltjesMeasure_variation_eq_zero_off_properEdgeNormals K V hKV hab f hf i
  have hdiffsub : E \ S ⊆ T := by
    intro t ht
    exact ⟨hEa t ht.1, not_ne_iff.mp (fun hne ↦ ht.2 ⟨hEa t ht.1, hne⟩)⟩
  have hdiffzero : μ (E \ S) = 0 := by
    rw [← enorm_eq_zero, ← le_zero_iff]
    exact (μ.enorm_measure_le_variation (E \ S)).trans
      (by rw [measure_mono_null hdiffsub hTzero])
  have hsplit : E = S ∩ E ∪ (E \ S) := by
    ext t
    constructor
    · intro ht
      by_cases htS : t ∈ S
      · exact Or.inl ⟨htS, ht⟩
      · exact Or.inr ⟨ht, htS⟩
    · rintro (ht | ht)
      · exact ht.2
      · exact ht.1
  have hfinite : S ∩ E =
      ↑((hSfinite.inter_of_left E).toFinset) := by
    exact (hSfinite.inter_of_left E).coe_toFinset.symm
  have hES : MeasurableSet (S ∩ E) := hSfinite.measurableSet.inter hE
  have hEdiff : MeasurableSet (E \ S) := hE.diff hSfinite.measurableSet
  have hdisj : Disjoint (S ∩ E) (E \ S) :=
    Set.disjoint_of_subset_left Set.inter_subset_left Set.disjoint_sdiff_right
  have hreduce : μ E = μ (S ∩ E) := calc
    μ E = μ (S ∩ E ∪ (E \ S)) := congrArg μ hsplit
    _ = μ (S ∩ E) + μ (E \ S) := μ.of_union hdisj hES hEdiff
    _ = μ (S ∩ E) := by rw [hdiffzero, add_zero]
  rw [hreduce]
  conv_lhs => rw [hfinite]
  let F := (hSfinite.inter_of_left E).toFinset
  have hU : (↑F : Set (Set.Icc a b)) = ⋃ t ∈ F, {t} := by
    ext t
    simp only [Finset.mem_coe, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro ht
      exact ⟨t, ht, rfl⟩
    · rintro ⟨u, hu, _, rfl⟩
      exact hu
  rw [hU, μ.of_biUnion_finset (by
    intro x hx y hy hxy
    simpa [Set.disjoint_singleton] using hxy) (by simp)]
  calc
    Finset.sum F (fun t ↦ μ {t}) =
        Finset.sum F (fun t ↦
          (surfaceAreaMeasure K {((t : ℝ) : Real.Angle)}).toReal *
            tangentVector ((t : ℝ) : Real.Angle) i) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' : t ∈ S ∩ E := by simpa [F] using ht
      exact intervalStieltjesMeasure_singleton_positiveVertex K f hf i t
        (by simpa [S] using ht'.1.1)
    _ = _ := by
      exact congrArg (fun G : Finset (Set.Icc a b) ↦
        Finset.sum G (fun t ↦
          (surfaceAreaMeasure K {((t : ℝ) : Real.Angle)}).toReal *
            tangentVector ((t : ℝ) : Real.Angle) i)) (by
              apply Finset.ext
              intro t
              simp [F, S])

/-- The surface integral of an arbitrary integrand over the angular image of a measurable
interval set, as a finite sum indexed by the angular lifts carrying a proper edge. The left
endpoint `a` is excluded from `E` so that each angle has at most one lift in `E`. -/
theorem integral_surfaceAreaMeasure_image_eq_sum_properEdgeNormal_lifts
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi) (φ : Real.Angle → ℝ)
    (E : Set (Set.Icc a b)) (hE : MeasurableSet E)
    (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
      φ u ∂surfaceAreaMeasure K) =
      Finset.sum ((finite_properEdgeNormal_lifts K V hKV hturn).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K).real {((t : ℝ) : Real.Angle)} *
          φ ((t : ℝ) : Real.Angle)) := by
  classical
  let c : Set.Icc a b → Real.Angle := fun t ↦ ((t : ℝ) : Real.Angle)
  let S : Set (Set.Icc a b) := {t | a < (t : ℝ) ∧
    (edgeVertices K ((t : ℝ) : Real.Angle)).1 ≠
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  have hinj : Set.InjOn c E := by
    intro x hx y hy hxy
    apply Subtype.ext
    let _ : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ioc
      (p := 2 * Real.pi) ⟨hEa x hx, x.property.2.trans hturn⟩
      ⟨hEa y hy, y.property.2.trans hturn⟩).mp
    change c x = c y
    exact hxy
  have hAmeas : MeasurableSet (c '' E) :=
    hE.image_of_continuousOn_injOn
      ((Real.Angle.continuous_coe : Continuous fun x : ℝ ↦ (x : Real.Angle)).comp
        continuous_subtype_val).continuousOn hinj
  rw [integral_surfaceAreaMeasure_eq_sum_properEdgeNormals K V hKV φ (c '' E) hAmeas]
  let F := ((finite_properEdgeNormal_lifts K V hKV hturn).inter_of_left E).toFinset
  let G := ((finite_properEdgeNormal_angles K V hKV).inter_of_left (c '' E)).toFinset
  have hG : G = F.image c := by
    ext u
    simp only [G, F, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_image,
      Finset.mem_image]
    constructor
    · rintro ⟨huN, t, htE, rfl⟩
      exact ⟨t, ⟨⟨hEa t htE, huN⟩, htE⟩, rfl⟩
    · rintro ⟨t, ⟨⟨hta, htN⟩, htE⟩, rfl⟩
      exact ⟨htN, t, htE, rfl⟩
  change Finset.sum G (fun u ↦ (surfaceAreaMeasure K).real {u} * φ u) = _
  rw [hG, Finset.sum_image]
  · intro x hx y hy hxy
    have hx' : x ∈ S ∩ E := by
      change (a < (x : ℝ) ∧ (edgeVertices K ((x : ℝ) : Real.Angle)).1 ≠
        (edgeVertices K ((x : ℝ) : Real.Angle)).2) ∧ x ∈ E
      simpa [F] using hx
    have hy' : y ∈ S ∩ E := by
      change (a < (y : ℝ) ∧ (edgeVertices K ((y : ℝ) : Real.Angle)).1 ≠
        (edgeVertices K ((y : ℝ) : Real.Angle)).2) ∧ y ∈ E
      simpa [F] using hy
    exact hinj hx'.2 hy'.2 hxy

/-- The tangent-coordinate surface integral over the angular image of a measurable interval set is
the same finite proper-edge sum as the positive-vertex Stieltjes measure. -/
theorem integral_tangentCoordinate_image_eq_sum_properEdgeNormal_lifts
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi) (i : Fin 2)
    (E : Set (Set.Icc a b)) (hE : MeasurableSet E)
    (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
      tangentVector u i ∂surfaceAreaMeasure K) =
      Finset.sum ((finite_properEdgeNormal_lifts K V hKV hturn).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K {((t : ℝ) : Real.Angle)}).toReal *
          tangentVector ((t : ℝ) : Real.Angle) i) :=
  integral_surfaceAreaMeasure_image_eq_sum_properEdgeNormal_lifts K V hKV hturn
    (fun u ↦ tangentVector u i) E hE hEa

/-- Polygon case of the positive-vertex Stieltjes/surface-measure identity, including degenerate
point and segment convex hulls. -/
theorem positiveVertex_stieltjes_surface_of_eq_convexHull
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (a b : ℝ) (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    ∃ f : Fin 2 → RightContinuousIntervalBV a b,
      (∀ i t, (f i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i) ∧
      ∀ (i : Fin 2) (E : Set (Set.Icc a b)), MeasurableSet E →
        (∀ t ∈ E, a < (t : ℝ)) →
        intervalStieltjesMeasure (f i) E =
          ∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
            tangentVector u i ∂surfaceAreaMeasure K := by
  obtain ⟨f, hf⟩ := exists_positiveVertex_intervalBV K hab.le
  refine ⟨f, hf, fun i E hE hEa ↦ ?_⟩
  rw [intervalStieltjesMeasure_eq_sum_properEdgeNormals K V hKV hab hturn f hf i E hE hEa,
    integral_tangentCoordinate_image_eq_sum_properEdgeNormal_lifts
      K V hKV hturn i E hE hEa]

/-- The positive vertex increment of a polygon is the tangent-coordinate surface integral over
the corresponding angular interval. -/
theorem positiveVertex_sub_eq_integral_of_eq_convexHull
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (i : Fin 2) :
    (edgeVertices K (b : Real.Angle)).1 i -
        (edgeVertices K (a : Real.Angle)).1 i =
      ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc a b,
        tangentVector u i ∂surfaceAreaMeasure K := by
  obtain ⟨f, hf, hmeasure⟩ :=
    positiveVertex_stieltjes_surface_of_eq_convexHull K V hKV a b hab hturn
  let aa : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let bb : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  have hangularImage :
      (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' Set.Ioc aa bb =
        (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc a b := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ⟨ht.1, ht.2⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht.1.le, ht.2⟩, ⟨ht.1, ht.2⟩, rfl⟩
  have hstieltjes := hmeasure i (Set.Ioc aa bb) measurableSet_Ioc
    (fun t ht ↦ ht.1)
  rw [intervalStieltjesMeasure_Ioc (f i) aa bb hab.le] at hstieltjes
  rw [hf i bb, hf i aa, hangularImage] at hstieltjes
  exact hstieltjes

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
# Analysis / Surface Measure / Boundary Limit
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace MovingSofa

/-- Face-preserving polygon approximation transfers the boundary increment identity. -/
private theorem positiveVertex_sub_eq_integral_of_polygon_identity
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (hpoly : ∀ (P : ConvexBody Point) (V : Finset Point),
      (P : Set Point) = convexHull ℝ (V : Set Point) → ∀ i : Fin 2,
      (edgeVertices P (b : Real.Angle)).1 i - (edgeVertices P (a : Real.Angle)).1 i =
        ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
          tangentVector u i ∂surfaceAreaMeasure P) (i : Fin 2) :
    (edgeVertices K (b : Real.Angle)).1 i - (edgeVertices K (a : Real.Angle)).1 i =
      ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
        tangentVector u i ∂surfaceAreaMeasure K := by
  classical
  obtain ⟨V, P, hP, hdist⟩ := exists_facePreserving_polygonApproximation K
    {(a : Real.Angle), (b : Real.Angle)}
  have ha (n : ℕ) : exposedEdge (P n) (a : Real.Angle) = exposedEdge K (a : Real.Angle) :=
    (hP n).2.2.2 _ (by simp)
  have hb (n : ℕ) : exposedEdge (P n) (b : Real.Angle) = exposedEdge K (b : Real.Angle) :=
    (hP n).2.2.2 _ (by simp)
  have hlim : Tendsto (fun n ↦ Metric.hausdorffDist (P n : Set Point) (K : Set Point))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ Metric.hausdorffDist_nonneg)
      (Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hdist n hn⟩)
    exact tendsto_one_div_atTop_nhds_zero_nat
  have hcontinuous : Continuous (fun u : Real.Angle ↦ tangentVector u i) := by
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hint := tendsto_integral_surfaceAreaMeasure_Ioc_of_preserves_faces
    P K hlim hab hturn ha hb (fun u ↦ tangentVector u i) hcontinuous
  have hvalue (n : ℕ) :
      (∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
        tangentVector u i ∂surfaceAreaMeasure (P n)) =
      (edgeVertices K (b : Real.Angle)).1 i - (edgeVertices K (a : Real.Angle)).1 i := by
    rw [← hpoly (P n) (V n) (hP n).2.1 i,
      edgeVertices_eq_of_exposedEdge_eq (P n) K _ (ha n),
      edgeVertices_eq_of_exposedEdge_eq (P n) K _ (hb n)]
  simp only [hvalue] at hint
  exact tendsto_nhds_unique tendsto_const_nhds hint

/-- The positive vertex increment is the tangent-coordinate surface integral over
the corresponding half-open angular interval. -/
theorem positiveVertex_sub_eq_integral
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (i : Fin 2) :
    (edgeVertices K (b : Real.Angle)).1 i - (edgeVertices K (a : Real.Angle)).1 i =
      ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
        tangentVector u i ∂surfaceAreaMeasure K := by
  exact positiveVertex_sub_eq_integral_of_polygon_identity K hab hturn
    (fun P V hPV i ↦ positiveVertex_sub_eq_integral_of_eq_convexHull P V hPV hab hturn i) i

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
# Analysis / Surface Measure / Discrete Bounds
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The integral of tangent vectors gives the increment of the positive supporting vertex. -/
theorem integral_tangentVector_surfaceAreaMeasure (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    (∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc a b,
      tangentVector u ∂surfaceAreaMeasure K) =
      (edgeVertices K (b : Real.Angle)).1 - (edgeVertices K (a : Real.Angle)).1 := by
  let A := (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc a b
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hu : Integrable (fun u : Real.Angle ↦ tangentVector u)
      ((surfaceAreaMeasure K).restrict A) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  ext i
  have hi := ContinuousLinearMap.integral_comp_comm
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i) hu
  change (∫ u in A, tangentVector u i ∂surfaceAreaMeasure K) =
    (∫ u in A, tangentVector u ∂surfaceAreaMeasure K) i at hi
  rw [← hi]
  exact (positiveVertex_sub_eq_integral K hab hturn i).symm

/-- The projected boundary integral computes the support value relative to the initial vertex. -/
theorem integral_inner_tangentVector_eq_support_sub (K : ConvexBody Point)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 Real.pi) :
    (∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc 0 s,
      inner ℝ (normalVector (s : Real.Angle)) (tangentVector u) ∂surfaceAreaMeasure K) =
      supportValue K (s : Real.Angle) -
        inner ℝ (normalVector (s : Real.Angle)) (edgeVertices K 0).1 := by
  let A := (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc 0 s
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hu : Integrable (fun u : Real.Angle ↦ tangentVector u)
      ((surfaceAreaMeasure K).restrict A) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hi := ContinuousLinearMap.integral_comp_comm
    (innerSL ℝ (normalVector (s : Real.Angle))) hu
  change (∫ u in A, inner ℝ (normalVector (s : Real.Angle)) (tangentVector u)
    ∂surfaceAreaMeasure K) = inner ℝ (normalVector (s : Real.Angle))
      (∫ u in A, tangentVector u ∂surfaceAreaMeasure K) at hi
  rw [show (∫ u in A, tangentVector u ∂surfaceAreaMeasure K) =
      (edgeVertices K (s : Real.Angle)).1 - (edgeVertices K 0).1 from
        integral_tangentVector_surfaceAreaMeasure K hs.1 (by linarith [hs.2, Real.pi_pos]),
    inner_sub_right,
    real_inner_comm (edgeVertices K (s : Real.Angle)).1 (normalVector (s : Real.Angle)),
    (edgeVertices_fst_mem K (s : Real.Angle)).2] at hi
  exact hi

/-- Positive atomic sine contributions are bounded by the corresponding support increment. -/
theorem sum_surfaceAreaMeasure_mul_pos_sin_le (K : ConvexBody Point)
    (D : Finset ℝ) (hD : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 Real.pi) :
    ∑ t ∈ D, (surfaceAreaMeasure K {(t : Real.Angle)}).toReal *
      max (Real.sin (s - t)) 0 ≤ supportValue K (s : Real.Angle) -
        inner ℝ (normalVector (s : Real.Angle)) (edgeVertices K 0).1 := by
  classical
  let F := D.filter (fun t ↦ t ≤ s)
  let E := (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc 0 s
  let g : Real.Angle → ℝ :=
    fun u ↦ inner ℝ (normalVector (s : Real.Angle)) (tangentVector u)
  have hcoe : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) (Set.Ioc 0 s) :=
    Real.Angle.injOn_coe_Ioc (by linarith [hs.2, Real.pi_pos])
  have hE : MeasurableSet E := measurableSet_Ioc.image_of_continuousOn_injOn
    Real.Angle.continuous_coe.continuousOn hcoe
  have hF (t : ℝ) (ht : t ∈ F) : t ∈ Set.Ioc 0 s :=
    ⟨(hD t (Finset.mem_filter.mp ht).1).1, (Finset.mem_filter.mp ht).2⟩
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hgcont : Continuous g := by
    apply Continuous.inner continuous_const
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hg : IntegrableOn g E (surfaceAreaMeasure K) :=
    by
    have hall : Integrable g (surfaceAreaMeasure K) := by
      rw [← integrableOn_univ]
      exact hgcont.continuousOn.integrableOn_compact isCompact_univ
    exact hall.integrableOn
  have hgnonneg : ∀ u ∈ E, 0 ≤ g u := by
    rintro u ⟨t, ht, rfl⟩
    change 0 ≤ inner ℝ (normalVector (s : Real.Angle)) (tangentVector (t : Real.Angle))
    rw [real_inner_comm (tangentVector (t : Real.Angle)), inner_tangentVector_normalVector_real]
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [ht.2], by linarith [ht.1, hs.2]⟩
  have hb := sum_measureReal_mul_le_setIntegral (surfaceAreaMeasure K)
    (F.image fun t : ℝ ↦ (t : Real.Angle)) hE
    (by rintro u hu; obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu; exact ⟨t, hF t ht, rfl⟩)
    hg hgnonneg
  rw [Finset.sum_image (fun x hx y hy hxy ↦ hcoe (hF x hx) (hF y hy) hxy)] at hb
  have heval (t : ℝ) : g (t : Real.Angle) = Real.sin (s - t) := by
    dsimp [g]
    rw [real_inner_comm (tangentVector (t : Real.Angle)), inner_tangentVector_normalVector_real]
  simp_rw [heval] at hb
  change (∑ t ∈ F, (surfaceAreaMeasure K {(t : Real.Angle)}).toReal *
    Real.sin (s - t)) ≤ _ at hb
  have hsum : (∑ t ∈ D, (surfaceAreaMeasure K {(t : Real.Angle)}).toReal *
      max (Real.sin (s - t)) 0) =
      ∑ t ∈ F, (surfaceAreaMeasure K {(t : Real.Angle)}).toReal * Real.sin (s - t) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hts : t ≤ s
    · rw [ite_eq_left hts, max_eq_left (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith, by linarith [(hD t ht).1, hs.2]⟩)]
    · have hsin : Real.sin (s - t) ≤ 0 := by
        have h := Real.sin_nonneg_of_mem_Icc
          (show t - s ∈ Set.Icc 0 Real.pi from
            ⟨by linarith, by linarith [(hD t ht).2, hs.1]⟩)
        rw [show s - t = -(t - s) by ring, Real.sin_neg]
        linarith
      rw [ite_eq_right hts, max_eq_right hsin, mul_zero]
  rw [hsum]
  exact hb.trans_eq (integral_inner_tangentVector_eq_support_sub K hs)

/-- For upper normals, the negative zero-angle vertex projects below the positive vertex. -/
theorem inner_negativeVertex_zero_le_positiveVertex (K : ConvexBody Point)
    {s : ℝ} (hs : s ∈ Set.Icc 0 Real.pi) :
    inner ℝ (normalVector (s : Real.Angle)) (edgeVertices K 0).2 ≤
      inner ℝ (normalVector (s : Real.Angle)) (edgeVertices K 0).1 := by
  have hy : inner ℝ (edgeVertices K 0).2 (tangentVector 0) ≤
      inner ℝ (edgeVertices K 0).1 (tangentVector 0) := by
    rw [inner_edgeVertices_snd_tangent]
    exact csInf_le ((isCompact_exposedEdge K 0).image
      (continuous_id.inner continuous_const)).bddBelow
      ⟨(edgeVertices K 0).1, edgeVertices_fst_mem K 0, rfl⟩
  have hx := (edgeVertices_fst_mem K 0).2.trans (edgeVertices_snd_mem K 0).2.symm
  simp [tangentVector, normalVector, frame, PiLp.inner_apply] at hx hy ⊢
  have hsin := Real.sin_nonneg_of_mem_Icc hs
  rw [hx]
  linarith [mul_le_mul_of_nonneg_right hy hsin]

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
# Analysis / Surface Measure / Integrals
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

/-- A sine convolution of tangent directions is the negative normal projection of their
Bochner integral. -/
private theorem integral_sin_sub_eq_neg_inner_integral_tangentVector
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (u : α → Real.Angle) (t : Real.Angle)
    (hu : Integrable (fun x ↦ tangentVector (u x)) (μ.restrict s)) :
    (∫ x in s, (u x - t).sin ∂μ) =
      -inner ℝ (normalVector t) (∫ x in s, tangentVector (u x) ∂μ) := by
  let L : Point →L[ℝ] ℝ := innerSL ℝ (normalVector t)
  calc
    (∫ x in s, (u x - t).sin ∂μ) =
        ∫ x in s, -L (tangentVector (u x)) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact sin_sub_eq_neg_inner_normalVector_tangentVector t (u x)
    _ = -(∫ x in s, L (tangentVector (u x)) ∂μ) := integral_neg _
    _ = -L (∫ x in s, tangentVector (u x) ∂μ) := by
      rw [ContinuousLinearMap.integral_comp_comm L hu]
    _ = -inner ℝ (normalVector t) (∫ x in s, tangentVector (u x) ∂μ) := rfl

theorem tangentArm_convolution (K : RightAngleCapSpace) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (tangentArmLengths K t).2.1 =
      ∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc t (t + Real.pi / 2),
        (u - (t : Real.Angle)).sin ∂surfaceAreaMeasure K.val := by
  let A := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc t (t + Real.pi / 2)
  let _ : IsFiniteMeasure (surfaceAreaMeasure K.val) :=
    (surfaceAreaMeasure_face_union K.val).1
  have hu : Integrable (fun u : Real.Angle ↦ tangentVector u)
      ((surfaceAreaMeasure K.val).restrict A) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hvec : (∫ u in A, tangentVector u ∂surfaceAreaMeasure K.val) =
      (edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1 -
        (edgeVertices K.val (t : Real.Angle)).1 := by
    ext i
    have hi := ContinuousLinearMap.integral_comp_comm
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i) hu
    change (∫ u in A, tangentVector u i ∂surfaceAreaMeasure K.val) =
      (∫ u in A, tangentVector u ∂surfaceAreaMeasure K.val) i at hi
    rw [← hi]
    symm
    simpa [A] using positiveVertex_sub_eq_integral K.val (a := t)
      (b := t + Real.pi / 2) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) i
  have harm : (tangentArmLengths K t).2.1 =
      -inner ℝ (normalVector (t : Real.Angle))
        ((edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1 -
          (edgeVertices K.val (t : Real.Angle)).1) := by
    obtain ⟨hA, _, hC, _⟩ := capTangentArm_identities K t ht
    have hnt : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (t : Real.Angle)) = 0 := by
      rw [real_inner_comm]
      exact inner_normalVector_tangentVector t
    have hnn : inner ℝ (normalVector (t : Real.Angle))
        (normalVector (t : Real.Angle)) = 1 := inner_normalVector_self t
    rw [hA] at hC
    have hproj := congrArg (fun p : Point ↦ inner ℝ p (normalVector (t : Real.Angle))) hC
    simp only [inner_add_left, real_inner_smul_left, hnt, hnn, mul_zero, add_zero,
      mul_one] at hproj
    simp only [capVertices] at hproj
    rw [inner_sub_right]
    rw [real_inner_comm
      (edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
      (normalVector (t : Real.Angle)),
      real_inner_comm (edgeVertices K.val (t : Real.Angle)).1
        (normalVector (t : Real.Angle))]
    linarith
  have hkernel := integral_sin_sub_eq_neg_inner_integral_tangentVector
    (surfaceAreaMeasure K.val) A id (t : Real.Angle) hu
  simp only [id_eq] at hkernel
  rw [show (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc t (t + Real.pi / 2) = A from rfl,
    hkernel, hvec, harm]

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
# Analysis / Surface Measure / Vertex Boundary
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

theorem positiveVertex_stieltjes_surface (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    ∃ f : Fin 2 → RightContinuousIntervalBV a b,
      (∀ i t, (f i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i) ∧
      ∀ (i : Fin 2) (E : Set (Set.Icc a b)), MeasurableSet E →
        (∀ t ∈ E, a < (t : ℝ)) →
        intervalStieltjesMeasure (f i) E =
          ∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
            tangentVector u i ∂surfaceAreaMeasure K := by
  obtain ⟨f, hf⟩ := exists_positiveVertex_intervalBV K hab.le
  refine ⟨f, hf, ?_⟩
  apply intervalStieltjesMeasure_eq_surfaceIntegral_of_increment K hab hturn f hf
  intro c d hcd i
  have hcdturn : (d : ℝ) ≤ (c : ℝ) + 2 * Real.pi :=
    d.property.2.trans (hturn.trans (by linarith [c.property.1]))
  exact positiveVertex_sub_eq_integral K hcd hcdturn i

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
# Angular densities of the surface-area measure

On an angular window of at most one turn the positive vertex of a convex body is a function of
bounded variation whose Stieltjes measure, paired with the moving tangent, is the surface-area
measure (`sum_intervalStieltjesIntegral_positiveVertex_tangent`).  If on such a window the
positive vertex happens to be a differentiable curve with derivative `g s • tangentVector s`,
this identifies the surface-area measure with the Lebesgue density `g`.

This file records that identification (`surfaceAreaMeasure_angleImage_eq_setLIntegral`,
`surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt`), and the bookkeeping that glues
finitely many or countably many such windows together (`measure_angleImage_eq_of_union`,
`measure_angleImage_eq_of_iUnion`) and turns the resulting set-level identities into the
`Measure.restrict = Measure.map (Measure.withDensity …)` form used by cap-density statements
(`measure_restrict_eq_map_withDensity`, `surfaceAreaMeasure_restrict_eq_map_withDensity`,
`surfaceAreaMeasure_restrict_eq_map_add_withDensity`).

The gluing lemmas are stated for an arbitrary pair of measures on `Real.Angle` and on `ℝ`,
since they only use additivity and the injectivity of the angular projection on a window of at
most one turn.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MovingSofa

/-- Pairing the frame tangent with a multiple of itself, in coordinates. -/
private theorem sum_mul_tangentVector_sq (c s : ℝ) :
    tangentVector (s : Real.Angle) 0 * (c * tangentVector (s : Real.Angle) 0) +
      tangentVector (s : Real.Angle) 1 * (c * tangentVector (s : Real.Angle) 1) = c := by
  have h : tangentVector (s : Real.Angle) 0 ^ 2 + tangentVector (s : Real.Angle) 1 ^ 2 = 1 := by
    have h := inner_tangentVector_self s
    rw [PiLp.inner_apply] at h
    simpa [Fin.sum_univ_two] using h
  linear_combination c * h

/-! ### The surface measure of an arc with a differentiable positive vertex -/

/-- Suppose that on the angular window `Ioc a b`, of at most one turn, the positive vertex of `K`
is traced by a curve `F` with derivative `g s • tangentVector s`, where `g` is continuous and
nonnegative.  Then the surface-area measure of the angular image of a measurable
`S ⊆ Ioc a b` is the Lebesgue integral of `g` over `S`. -/
theorem surfaceAreaMeasure_angleImage_eq_setLIntegral (K : ConvexBody Point) {a b : ℝ}
    (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point) (g : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (g s • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hgnn : ∀ s ∈ Ioc a b, 0 ≤ g s)
    (hvertex : ∀ s ∈ Icc a b, (edgeVertices K (s : Real.Angle)).1 = F s)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Ioc a b) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      ∫⁻ s in S, ENNReal.ofReal (g s) := by
  have hfin : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hSIcc : S ⊆ Icc a b := hSsub.trans Ioc_subset_Icc_self
  obtain ⟨f, hftoFun, hfmeas⟩ := positiveVertex_stieltjes_surface K a b hab hturn
  have hcontT : ∀ i : Fin 2, Continuous fun s : ℝ ↦ tangentVector (s : Real.Angle) i :=
    fun i ↦ (continuous_tangentVector_coordinate i).comp Real.Angle.continuous_coe
  -- the coordinate functions of the differentiable vertex curve and their derivatives
  set φ : Fin 2 → ℝ → ℝ := fun i s ↦ F s i with hφ
  set ψ : Fin 2 → ℝ → ℝ := fun i s ↦ g s * tangentVector (s : Real.Angle) i with hψ
  have hderiv : ∀ (i : Fin 2) (s : ℝ), HasDerivAt (φ i) (ψ i s) s := by
    intro i s
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt s (hF s)
    simpa [φ, ψ, Function.comp_def] using h
  have hcontψ : ∀ i : Fin 2, Continuous (ψ i) := fun i ↦ hg.mul (hcontT i)
  -- the Stieltjes density of each vertex coordinate
  have hdens : ∀ i : Fin 2, HasIntervalStieltjesDensity (f i) (ψ i) := by
    intro i
    obtain ⟨G, hGfun, hGdens⟩ :=
      exists_intervalBV_of_hasDerivAt hab.le (φ i) (ψ i) (hderiv i) (hcontψ i)
    have hfe : f i = G := by
      refine RightContinuousIntervalBV.toFun_injective (funext fun t ↦ ?_)
      rw [hftoFun i t, hGfun t, hvertex (t : ℝ) t.2]
    rw [hfe]
    exact hGdens
  -- the sum over the two coordinates of the Stieltjes integrals
  set E : Set (Icc a b) := {x : Icc a b | (x : ℝ) ∈ S} with hE
  have hEmeas : MeasurableSet E := hS.preimage measurable_subtype_coe
  have hEa : ∀ t ∈ E, a < (t : ℝ) := fun t ht ↦ (hSsub ht).1
  have himage : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E =
      (fun s : ℝ ↦ (s : Real.Angle)) '' S := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(t : ℝ), ht, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hSIcc hs⟩, hs, rfl⟩
  have hsum := sum_intervalStieltjesIntegral_positiveVertex_tangent K hab hturn f hfmeas
    E hEmeas hEa
  rw [himage] at hsum
  -- each Stieltjes integral is an ordinary set integral
  have hstep : ∀ i : Fin 2,
      intervalStieltjesIntegral (f i) (fun t ↦ tangentVector ((t : ℝ) : Real.Angle) i) E =
        ∫ s in S, tangentVector (s : Real.Angle) i * ψ i s := by
    intro i
    have hq : Continuous fun t : Icc a b ↦ tangentVector ((t : ℝ) : Real.Angle) i :=
      (hcontT i).comp continuous_subtype_val
    rw [intervalStieltjesIntegral_eq_integral_mul_of_density (f i) (hdens i) hq E hEmeas]
    rw [MeasureTheory.integral_subtype_preimage measurableSet_Icc hS
      (fun s ↦ tangentVector (s : Real.Angle) i * ψ i s)]
    rw [Measure.restrict_restrict_of_subset hSIcc]
  simp only [hstep] at hsum
  -- integrability of the two summands and of the density
  have hintegrand : ∀ i : Fin 2,
      IntegrableOn (fun s : ℝ ↦ tangentVector (s : Real.Angle) i * ψ i s) S volume := by
    intro i
    refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set hSIcc
    exact ((hcontT i).mul (hcontψ i)).continuousOn
  have hgint : IntegrableOn g S volume :=
    (ContinuousOn.integrableOn_compact isCompact_Icc hg.continuousOn).mono_set hSIcc
  have hsum2 : (surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S)).toReal =
      ∫ s in S, g s := by
    rw [← hsum, Fin.sum_univ_two, ← integral_add (hintegrand 0) (hintegrand 1)]
    refine setIntegral_congr_fun hS fun s _ ↦ ?_
    exact sum_mul_tangentVector_sq (g s) s
  rw [← ENNReal.ofReal_toReal (measure_ne_top (surfaceAreaMeasure K) _), hsum2]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint]
  filter_upwards [ae_restrict_mem hS] with s hs
  exact hgnn s (hSsub hs)

/-- The same identification as `surfaceAreaMeasure_angleImage_eq_setLIntegral`, phrased as
agreement with a `Measure.withDensity` for any nonnegative weight `w` that agrees with the
derivative factor `g` on the window. -/
theorem surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point) (g w : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (g s • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hvertex : ∀ s ∈ Icc a b, (edgeVertices K (s : Real.Angle)).1 = F s)
    (hw : ∀ s ∈ Ioc a b, w s = g s) (hwnn : ∀ s ∈ Ioc a b, 0 ≤ w s)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Ioc a b) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (w s)) S := by
  have hgnn : ∀ s ∈ Ioc a b, 0 ≤ g s := fun s hs ↦ (hw s hs) ▸ hwnn s hs
  rw [withDensity_apply _ hS, surfaceAreaMeasure_angleImage_eq_setLIntegral K hab hturn F g hF hg
    hgnn hvertex hS hSsub]
  exact setLIntegral_congr_fun hS fun s hs ↦ by rw [hw s (hSsub hs)]

/-! ### Gluing angular density identities -/

/-- Two measures that read one another through the angular projection on each of two disjoint
measurable subsets of a window of at most one turn do so on their union. -/
theorem measure_angleImage_eq_of_union {μ : Measure Real.Angle} {ν : Measure ℝ} {c d : ℝ}
    (hturn : d ≤ c + 2 * Real.pi) {I J : Set ℝ}
    (hI : I ⊆ Ioc c d) (hJ : J ⊆ Ioc c d)
    (hImeas : MeasurableSet I) (hJmeas : MeasurableSet J) (hdisj : Disjoint I J)
    (hA : ∀ S, MeasurableSet S → S ⊆ I → μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S)
    (hB : ∀ S, MeasurableSet S → S ⊆ J → μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ I ∪ J) :
    μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S := by
  have hsplit : S = S ∩ I ∪ S ∩ J := by
    rw [← Set.inter_union_distrib_left, Set.inter_eq_left.2 hSsub]
  have hSI : MeasurableSet (S ∩ I) := hS.inter hImeas
  have hSJ : MeasurableSet (S ∩ J) := hS.inter hJmeas
  have hdisj' : Disjoint (S ∩ I) (S ∩ J) :=
    hdisj.mono Set.inter_subset_right Set.inter_subset_right
  have hinj := Real.Angle.injOn_coe_Ioc hturn
  have himdisj : Disjoint ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ I))
      ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J)) := by
    rw [Set.disjoint_left]
    rintro u ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hyx : y = x := hinj (hJ hy.2) (hI hx.2) hxy
    exact (Set.disjoint_left.1 hdisj' hx) (hyx ▸ hy)
  have himmeas : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J)) :=
    Real.Angle.measurableSet_image_of_subset_Ioc hturn hSJ (Set.inter_subset_right.trans hJ)
  calc μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S)
      = μ ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ I) ∪
          (fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J)) := by
        rw [← Set.image_union, ← hsplit]
    _ = μ ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ I)) +
          μ ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J)) := measure_union himdisj himmeas
    _ = ν (S ∩ I) + ν (S ∩ J) := by
        rw [hA _ hSI Set.inter_subset_right, hB _ hSJ Set.inter_subset_right]
    _ = ν S := by rw [← measure_union hdisj' hSJ, ← hsplit]

/-- Two measures that read one another through the angular projection on each member of a
monotone sequence of measurable sets do so on the union of that sequence. -/
theorem measure_angleImage_eq_of_iUnion {μ : Measure Real.Angle} {ν : Measure ℝ}
    {J : ℕ → Set ℝ} (hmono : Monotone J) (hJmeas : ∀ n, MeasurableSet (J n))
    (hA : ∀ (n : ℕ) (S : Set ℝ), MeasurableSet S → S ⊆ J n →
      μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ ⋃ n, J n) :
    μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S := by
  have hSeq : S = ⋃ n, S ∩ J n := by
    rw [← Set.inter_iUnion, Set.inter_eq_left.2 hSsub]
  have hmono' : Monotone fun n ↦ S ∩ J n := fun m n h ↦
    Set.inter_subset_inter_right _ (hmono h)
  have hmonoimg : Monotone fun n ↦ (fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J n) :=
    fun m n h ↦ Set.image_mono (hmono' h)
  calc μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S)
      = μ (⋃ n, (fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J n)) := by
        rw [← Set.image_iUnion, ← hSeq]
    _ = ⨆ n, μ ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J n)) := hmonoimg.measure_iUnion
    _ = ⨆ n, ν (S ∩ J n) :=
        iSup_congr fun n ↦ hA n _ (hS.inter (hJmeas n)) Set.inter_subset_right
    _ = ν S := by rw [← hmono'.measure_iUnion, ← hSeq]

/-! ### From set-level identities to restricted measures -/

/-- A set-level angular density identity on a measurable parameter set `I` says exactly that the
measure restricted to the angular image of `I` is the pushforward of the weighted Lebesgue
measure on `I`. -/
theorem measure_restrict_eq_map_withDensity {μ : Measure Real.Angle} {I : Set ℝ}
    {w : ℝ → ℝ≥0∞} (hImeas : MeasurableSet I)
    (hagree : ∀ S, MeasurableSet S → S ⊆ I →
      μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = volume.withDensity w S) :
    μ.restrict ((fun s : ℝ ↦ (s : Real.Angle)) '' I) =
      Measure.map (fun s : ℝ ↦ (s : Real.Angle)) ((volume.restrict I).withDensity w) := by
  have hmeas : Measurable fun s : ℝ ↦ (s : Real.Angle) := Real.Angle.continuous_coe.measurable
  ext B hB
  have hpre : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B) := hB.preimage hmeas
  have hset : B ∩ (fun s : ℝ ↦ (s : Real.Angle)) '' I =
      (fun s : ℝ ↦ (s : Real.Angle)) '' ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B ∩ I) := by
    ext u
    constructor
    · rintro ⟨hu, s, hs, rfl⟩
      exact ⟨s, ⟨hu, hs⟩, rfl⟩
    · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
      exact ⟨hs1, s, hs2, rfl⟩
  rw [Measure.restrict_apply hB, hset, hagree _ (hpre.inter hImeas) Set.inter_subset_right,
    Measure.map_apply hmeas hB, withDensity_apply _ hpre,
    withDensity_apply _ (hpre.inter hImeas), Measure.restrict_restrict hpre]

/-- The surface-area measure instance of `measure_restrict_eq_map_withDensity`. -/
theorem surfaceAreaMeasure_restrict_eq_map_withDensity {K : ConvexBody Point}
    {I : Set ℝ} {w : ℝ → ℝ≥0∞} (hImeas : MeasurableSet I)
    (hagree : ∀ S, MeasurableSet S → S ⊆ I →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = volume.withDensity w S) :
    (surfaceAreaMeasure K).restrict ((fun s : ℝ ↦ (s : Real.Angle)) '' I) =
      Measure.map (fun s : ℝ ↦ (s : Real.Angle)) ((volume.restrict I).withDensity w) :=
  measure_restrict_eq_map_withDensity hImeas hagree

/-- The shifted form of `surfaceAreaMeasure_restrict_eq_map_withDensity`: an angular density
identity on the translated window `Ioc c (c + T)` with the translated weight `u ↦ w (u - c)`
says that the surface-area measure restricted to that angular arc is the pushforward of the
`w`-weighted Lebesgue measure on `Ioc 0 T` along `t ↦ ↑(t + c)`. -/
theorem surfaceAreaMeasure_restrict_eq_map_add_withDensity {K : ConvexBody Point}
    {c T : ℝ} {w : ℝ → ℝ≥0∞}
    (hagree : ∀ S, MeasurableSet S → S ⊆ Ioc c (c + T) →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity (fun u ↦ w (u - c)) S) :
    (surfaceAreaMeasure K).restrict ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioc c (c + T)) =
      Measure.map (fun t : ℝ ↦ ((t + c : ℝ) : Real.Angle))
        ((volume.restrict (Ioc 0 T)).withDensity w) := by
  have hmeas : Measurable fun s : ℝ ↦ (s : Real.Angle) := Real.Angle.continuous_coe.measurable
  have hmeas' : Measurable fun t : ℝ ↦ ((t + c : ℝ) : Real.Angle) :=
    Real.Angle.continuous_coe.measurable.comp (measurable_id.add_const c)
  ext B hB
  have hpre : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B) := hB.preimage hmeas
  have hpre' : MeasurableSet ((fun t : ℝ ↦ ((t + c : ℝ) : Real.Angle)) ⁻¹' B) :=
    hB.preimage hmeas'
  have hset : B ∩ (fun s : ℝ ↦ (s : Real.Angle)) '' Ioc c (c + T) =
      (fun s : ℝ ↦ (s : Real.Angle)) ''
        ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B ∩ Ioc c (c + T)) := by
    ext u
    constructor
    · rintro ⟨hu, s, hs, rfl⟩
      exact ⟨s, ⟨hu, hs⟩, rfl⟩
    · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
      exact ⟨hs1, s, hs2, rfl⟩
  have hpreimage : (fun t : ℝ ↦ t + c) ⁻¹'
      ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B ∩ Ioc c (c + T)) =
      (fun t : ℝ ↦ ((t + c : ℝ) : Real.Angle)) ⁻¹' B ∩ Ioc 0 T := by
    ext t
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
  rw [Measure.restrict_apply hB, hset,
    hagree _ (hpre.inter measurableSet_Ioc) Set.inter_subset_right,
    withDensity_apply _ (hpre.inter measurableSet_Ioc), setLIntegral_comp_sub_right, hpreimage,
    Measure.map_apply hmeas' hB, withDensity_apply _ hpre',
    Measure.restrict_restrict hpre']

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
# Analysis / Surface Measure / Frame Products
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- The normal and tangent projections of the positive vertex, with their Stieltjes measures. -/
theorem exists_positiveVertex_frame_products
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    ∃ H P : RightContinuousIntervalBV a b,
      (∀ t, H.toFun t = inner ℝ (edgeVertices K (((t : ℝ) : Real.Angle))).1
        (normalVector (((t : ℝ) : Real.Angle)))) ∧
      (∀ t, P.toFun t = inner ℝ (edgeVertices K (((t : ℝ) : Real.Angle))).1
        (tangentVector (((t : ℝ) : Real.Angle)))) ∧
      ∀ E : Set (Icc a b), MeasurableSet E → (∀ t ∈ E, a < (t : ℝ)) →
        intervalStieltjesMeasure H E =
          ∫ t in (Subtype.val : Icc a b → ℝ) '' E,
            inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) ∧
        intervalStieltjesMeasure P E =
          (surfaceAreaMeasure K
              ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal -
            ∫ t in (Subtype.val : Icc a b → ℝ) '' E,
              inner ℝ (edgeVertices K (t : Real.Angle)).1 (normalVector (t : Real.Angle)) := by
  obtain ⟨v, hv, hvm⟩ := positiveVertex_stieltjes_surface K a b hab hturn
  choose n hn hnd using fun i : Fin 2 ↦ exists_normalVector_coordinate_intervalBV hab.le i
  choose τ hτ hτd using fun i : Fin 2 ↦ exists_tangentVector_coordinate_intervalBV hab.le i
  have hnc (i : Fin 2) : Continuous (n i).toFun := by
    convert ((by
      fin_cases i
      · exact Real.Angle.continuous_cos
      · exact Real.Angle.continuous_sin :
          Continuous (fun u : Real.Angle ↦ normalVector u i))).comp
          (Real.Angle.continuous_coe.comp continuous_subtype_val) using 1
    funext t
    exact hn i t
  have hτc (i : Fin 2) : Continuous (τ i).toFun := by
    convert ((by
      fin_cases i
      · exact Real.Angle.continuous_sin.neg
      · exact Real.Angle.continuous_cos :
          Continuous (fun u : Real.Angle ↦ tangentVector u i))).comp
          (Real.Angle.continuous_coe.comp continuous_subtype_val) using 1
    funext t
    exact hτ i t
  obtain ⟨H, hH, hHm⟩ := intervalStieltjes_inner_fin_two v n hnc
  obtain ⟨P, hP, hPm⟩ := intervalStieltjes_inner_fin_two v τ hτc
  refine ⟨H, P, ?_, ?_, ?_⟩
  · intro t
    rw [hH]
    simp_rw [hv, hn]
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
  · intro t
    rw [hP]
    simp_rw [hv, hτ]
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
  · intro E hE hEa
    have hnormal := sum_intervalStieltjesIntegral_positiveVertex_normal
      K hab hturn v hvm E hE hEa
    have htangent := sum_intervalStieltjesIntegral_positiveVertex_tangent
      K hab hturn v hvm E hE hEa
    have hnfun (i : Fin 2) : (n i).toFun =
        fun t : Icc a b ↦ normalVector (((t : ℝ) : Real.Angle)) i :=
      funext (hn i)
    have hτfun (i : Fin 2) : (τ i).toFun =
        fun t : Icc a b ↦ tangentVector (((t : ℝ) : Real.Angle)) i :=
      funext (hτ i)
    have hnormal' :
        (∑ i : Fin 2, intervalStieltjesIntegral (v i) (n i).toFun E) = 0 := by
      simpa only [hnfun] using hnormal
    have htangent' :
        (∑ i : Fin 2, intervalStieltjesIntegral (v i) (τ i).toFun E) =
          (surfaceAreaMeasure K
            ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal := by
      simpa only [hτfun] using htangent
    have hfinite : IsFiniteMeasure (volume.comap (Subtype.val : Icc a b → ℝ)) :=
      ⟨by
        rw [comap_subtype_coe_apply measurableSet_Icc]
        simp only [image_univ, Subtype.range_val]
        exact measure_Icc_lt_top⟩
    let _ := hfinite
    have hsmoothN (i : Fin 2) :
        intervalStieltjesIntegral (n i) (v i).toFun E =
          ∫ t in E, (v i).toFun t * tangentVector (((t : ℝ) : Real.Angle)) i
            ∂volume.comap (Subtype.val : Icc a b → ℝ) :=
      intervalStieltjesIntegral_eq_integral_mul_of_density_bv hab.le (n i) (hnd i)
        (v i).boundedVariation E hE
    have hsmoothT (i : Fin 2) :
        intervalStieltjesIntegral (τ i) (v i).toFun E =
          ∫ t in E, (v i).toFun t * -normalVector (((t : ℝ) : Real.Angle)) i
            ∂volume.comap (Subtype.val : Icc a b → ℝ) :=
      intervalStieltjesIntegral_eq_integral_mul_of_density_bv hab.le (τ i) (hτd i)
        (v i).boundedVariation E hE
    have hintN (i : Fin 2) : Integrable
        (fun t : Icc a b ↦ (v i).toFun t * tangentVector (((t : ℝ) : Real.Angle)) i)
        (volume.comap (Subtype.val : Icc a b → ℝ)) := by
      apply (v i).boundedVariation.integrable.mul_bdd
      · exact ((by
          fin_cases i
          · exact Real.Angle.continuous_sin.neg
          · exact Real.Angle.continuous_cos :
              Continuous (fun u : Real.Angle ↦ tangentVector u i))).comp
              (Real.Angle.continuous_coe.comp continuous_subtype_val) |>.aestronglyMeasurable
      · filter_upwards with t
        fin_cases i
        · simpa [tangentVector, frame] using Real.abs_sin_le_one (t : ℝ)
        · simpa [tangentVector, frame] using Real.abs_cos_le_one (t : ℝ)
    have hintT (i : Fin 2) : Integrable
        (fun t : Icc a b ↦ (v i).toFun t * -normalVector (((t : ℝ) : Real.Angle)) i)
        (volume.comap (Subtype.val : Icc a b → ℝ)) := by
      apply (v i).boundedVariation.integrable.mul_bdd
      · exact ((by
          fin_cases i
          · exact Real.Angle.continuous_cos.neg
          · exact Real.Angle.continuous_sin.neg :
              Continuous (fun u : Real.Angle ↦ -normalVector u i))).comp
              (Real.Angle.continuous_coe.comp continuous_subtype_val) |>.aestronglyMeasurable
      · filter_upwards with t
        fin_cases i
        · simpa [normalVector, frame] using Real.abs_cos_le_one (t : ℝ)
        · simpa [normalVector, frame] using Real.abs_sin_le_one (t : ℝ)
    let R := (Subtype.val : Icc a b → ℝ) '' E
    have hR : MeasurableSet R :=
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hE
    have hRsub : R ⊆ Icc a b := by
      rintro x ⟨t, -, rfl⟩
      exact t.property
    have hpre : {t : Icc a b | (t : ℝ) ∈ R} = E :=
      Set.preimage_image_eq E Subtype.val_injective
    have hsubN :
        (∑ i : Fin 2, ∫ t in E,
          (v i).toFun t * tangentVector (((t : ℝ) : Real.Angle)) i
            ∂volume.comap (Subtype.val : Icc a b → ℝ)) =
          ∫ t in R, inner ℝ (edgeVertices K (t : Real.Angle)).1
            (tangentVector (t : Real.Angle)) := by
      rw [Fin.sum_univ_two, ← integral_add (hintN 0).integrableOn (hintN 1).integrableOn]
      have hsubtype := integral_subtype_preimage (μ := volume) (s := Icc a b) (t := R)
        measurableSet_Icc hR
        (fun t : ℝ ↦ inner ℝ (edgeVertices K (t : Real.Angle)).1
          (tangentVector (t : Real.Angle)))
      rw [hpre, Measure.restrict_restrict_of_subset hRsub] at hsubtype
      rw [← hsubtype]
      apply integral_congr_ae
      filter_upwards with t
      rw [hv 0 t, hv 1 t]
      simp [PiLp.inner_apply, Fin.sum_univ_two]
      ring
    have hsubT :
        (∑ i : Fin 2, ∫ t in E,
          (v i).toFun t * -normalVector (((t : ℝ) : Real.Angle)) i
            ∂volume.comap (Subtype.val : Icc a b → ℝ)) =
          -(∫ t in R, inner ℝ (edgeVertices K (t : Real.Angle)).1
            (normalVector (t : Real.Angle))) := by
      rw [Fin.sum_univ_two, ← integral_add (hintT 0).integrableOn (hintT 1).integrableOn]
      have hsubtype := integral_subtype_preimage (μ := volume) (s := Icc a b) (t := R)
        measurableSet_Icc hR
        (fun t : ℝ ↦ inner ℝ (edgeVertices K (t : Real.Angle)).1
          (normalVector (t : Real.Angle)))
      rw [hpre, Measure.restrict_restrict_of_subset hRsub] at hsubtype
      rw [← hsubtype, ← integral_neg]
      apply integral_congr_ae
      filter_upwards with t
      rw [hv 0 t, hv 1 t]
      simp [PiLp.inner_apply, Fin.sum_univ_two]
      ring
    constructor
    · rw [hHm E hE, Finset.sum_add_distrib, hnormal']
      simp only [zero_add]
      simpa only [hsmoothN] using hsubN
    · rw [hPm E hE, Finset.sum_add_distrib, htangent']
      rw [show (∑ i : Fin 2, intervalStieltjesIntegral (τ i) (v i).toFun E) =
          -(∫ t in R, inner ℝ (edgeVertices K (t : Real.Angle)).1
            (normalVector (t : Real.Angle))) by simpa only [hsmoothT] using hsubT]
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
# Analysis / Surface Measure / Boundary
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

theorem positiveArm_stieltjes_surface (K : RightAngleCapSpace) :
    ∃ f : RightContinuousIntervalBV 0 (Real.pi / 2),
      (∀ t, f.toFun t = (tangentArmLengths K t).1.1) ∧
      ∀ E : Set (Set.Icc (0 : ℝ) (Real.pi / 2)), MeasurableSet E →
        (∀ t ∈ E, 0 < (t : ℝ)) →
        intervalStieltjesMeasure f E =
          (∫ t in (fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ (s : ℝ)) '' E,
            (tangentArmLengths K t).2.1) -
          (surfaceAreaMeasure K.val
            ((fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ ((s : ℝ) : Real.Angle)) '' E)).toReal := by
  have hT : 0 < (Real.pi / 2) := by positivity
  obtain ⟨HA, PA, hHA, hPA, hmA⟩ := exists_positiveVertex_frame_products K.val hT
    (by linarith [Real.pi_pos])
  obtain ⟨HC, PC, hHC, hPC, hmC⟩ := exists_positiveVertex_frame_products K.val
    (a := 0 + (Real.pi / 2)) (b := (Real.pi / 2) + (Real.pi / 2)) (by linarith)
    (by linarith [Real.pi_pos])
  have hHC_support (t : Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2))) :
      HC.toFun t = supportValue K.val (((t : ℝ) : Real.Angle)) := by
    rw [hHC, (edgeVertices_fst_mem K.val (((t : ℝ) : Real.Angle))).2]
  have hHCc : Continuous HC.toFun := by
    convert (continuous_supportValue_real K.val).comp continuous_subtype_val using 1
    funext t
    exact hHC_support t
  obtain ⟨Hs, hHs, hHsm⟩ := exists_intervalBV_shift_from_zero hT.le HC hHCc
  obtain ⟨f, hf, hfm⟩ := intervalStieltjes_linear_combination 0 (Real.pi / 2) Hs PA 1 (-1)
  refine ⟨f, ?_, ?_⟩
  · intro t
    rw [hf, hHs, hHC_support, hPA, (tangentArmLengths_positive_frame K t).1]
    simp only [one_mul, neg_mul, one_mul]
    ring
  · intro E hE hE0
    change Set (Icc 0 (Real.pi / 2)) at E
    let φ : Icc 0 (Real.pi / 2) →
        Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2)) := fun t ↦
      ⟨(t : ℝ) + (Real.pi / 2), by constructor <;> linarith [t.property.1, t.property.2]⟩
    let R := (Subtype.val : Icc 0 (Real.pi / 2) → ℝ) '' E
    have hR : MeasurableSet R :=
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hE
    have hφE : MeasurableSet (φ '' E) := by
      let ψ : Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2)) →
          Icc 0 (Real.pi / 2) := fun t ↦
        ⟨(t : ℝ) - (Real.pi / 2), by
          constructor
          · linarith [t.property.1]
          · linarith [t.property.2]⟩
      let e : Icc 0 (Real.pi / 2) ≃ₜ
          Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2)) :=
        { toFun := φ
          invFun := ψ
          left_inv := fun x ↦ by apply Subtype.ext; simp [φ, ψ]
          right_inv := fun x ↦ by apply Subtype.ext; simp [φ, ψ]
          continuous_toFun := (continuous_subtype_val.add_const (Real.pi / 2)).subtype_mk _
          continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _ }
      exact e.measurableEmbedding.measurableSet_image' hE
    have hφleft : ∀ t ∈ φ '' E, 0 + (Real.pi / 2) < (t : ℝ) := by
      rintro t ⟨s, hs, rfl⟩
      dsimp [φ]
      linarith [hE0 s hs]
    have hreal : (Subtype.val :
        Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2)) → ℝ) '' (φ '' E) =
        (fun x : ℝ ↦ x + (Real.pi / 2)) '' R := by
      ext x
      constructor
      · rintro ⟨-, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨s, ⟨s, hs, rfl⟩, rfl⟩
      · rintro ⟨-, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨φ s, ⟨s, hs, rfl⟩, rfl⟩
    have hHs_measure : intervalStieltjesMeasure Hs E =
        ∫ t in R, inner ℝ
          (edgeVertices K.val (((t + (Real.pi / 2) : ℝ) : Real.Angle))).1
          (tangentVector (((t + (Real.pi / 2) : ℝ) : Real.Angle))) := by
      rw [hHsm E hE, (hmC (φ '' E) hφE hφleft).1, hreal,
        integral_image_add_right_eq (Real.pi / 2) R hR]
    have hPA_measure := (hmA E hE hE0).2
    have hlin : intervalStieltjesMeasure f E =
        intervalStieltjesMeasure Hs E - intervalStieltjesMeasure PA E := by
      have := congrArg (fun m : SignedMeasure (Icc 0 (Real.pi / 2)) ↦ m E) hfm
      rw [add_apply, _root_.smul_apply, _root_.smul_apply] at this
      simpa only [smul_eq_mul, one_mul, neg_one_mul, sub_eq_add_neg] using this
    change intervalStieltjesMeasure f E = _
    rw [hlin, hHs_measure, hPA_measure]
    have hAint : IntegrableOn
        (fun t : ℝ ↦ inner ℝ (edgeVertices K.val (t : Real.Angle)).1
          (normalVector (t : Real.Angle))) R := by
      have hAIcc := HA.integrableOn_Icc_of_eq
        (fun t : ℝ ↦ inner ℝ (edgeVertices K.val (t : Real.Angle)).1
          (normalVector (t : Real.Angle))) (fun t ↦ (hHA t).symm)
      apply hAIcc.mono_set
      rintro x ⟨t, -, rfl⟩
      exact t.property
    have hCint : IntegrableOn
        (fun t : ℝ ↦ inner ℝ
          (edgeVertices K.val (((t + (Real.pi / 2) : ℝ) : Real.Angle))).1
          (tangentVector (((t + (Real.pi / 2) : ℝ) : Real.Angle)))) R := by
      let q : ℝ → ℝ := fun s ↦ inner ℝ (edgeVertices K.val (s : Real.Angle)).1
        (tangentVector (s : Real.Angle))
      have hqIcc := PC.integrableOn_Icc_of_eq q (fun t ↦ (hPC t).symm)
      have hqshift : IntegrableOn q
          ((fun x : ℝ ↦ x + Real.pi / 2) '' R) := by
        apply hqIcc.mono_set
        rintro x ⟨-, ⟨t, -, rfl⟩, rfl⟩
        constructor <;> linarith [t.property.1, t.property.2]
      exact (integrableOn_comp_add_right_iff (Real.pi / 2) R hR q).2 hqshift
    rw [show (∫ t in R, inner ℝ
          (edgeVertices K.val (((t + Real.pi / 2 : ℝ) : Real.Angle))).1
          (tangentVector (((t + Real.pi / 2 : ℝ) : Real.Angle)))) -
        ((surfaceAreaMeasure K.val
          ((fun t : Icc 0 (Real.pi / 2) ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal -
          ∫ t in R, inner ℝ (edgeVertices K.val (t : Real.Angle)).1
            (normalVector (t : Real.Angle))) =
        ((∫ t in R, inner ℝ
            (edgeVertices K.val (((t + Real.pi / 2 : ℝ) : Real.Angle))).1
            (tangentVector (((t + Real.pi / 2 : ℝ) : Real.Angle)))) +
          ∫ t in R, inner ℝ (edgeVertices K.val (t : Real.Angle)).1
            (normalVector (t : Real.Angle))) -
        (surfaceAreaMeasure K.val
          ((fun t : Icc 0 (Real.pi / 2) ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal by ring]
    rw [← integral_add hCint hAint]
    apply congrArg (fun z : ℝ ↦ z -
      (surfaceAreaMeasure K.val
        ((fun s : Icc (0 : ℝ) (Real.pi / 2) ↦ ((s : ℝ) : Real.Angle)) '' E)).toReal)
    apply integral_congr_ae
    filter_upwards with t
    rw [(tangentArmLengths_positive_frame K t).2]
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
# Analysis / Surface Measure / Linearity
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped unitInterval

namespace MovingSofa

private theorem intervalStieltjesMeasure_congr {a b : ℝ}
    (f g : RightContinuousIntervalBV a b) (h : ∀ x, f.toFun x = g.toFun x) :
    intervalStieltjesMeasure f = intervalStieltjesMeasure g := by
  have hfun : f.toFun = g.toFun := funext h
  cases f with
  | mk ff hfb hfr =>
    cases g with
    | mk gf hgb hgr =>
      simp only at hfun ⊢
      subst gf
      rfl

/-- Planar surface area measures commute with convex combinations. -/
theorem surfaceAreaMeasure_convexBodyCombination (t : I)
    (K L : ConvexBody Point) :
    surfaceAreaMeasure (convexBodyCombination t K L) =
      ENNReal.ofReal (1 - (t : ℝ)) • surfaceAreaMeasure K +
        ENNReal.ofReal (t : ℝ) • surfaceAreaMeasure L := by
  let r : ℝ := 1 - (t : ℝ)
  let s : ℝ := t
  let M := convexBodyCombination t K L
  have hvertex (u : Real.Angle) :
      (edgeVertices M u).1 = r • (edgeVertices K u).1 + s • (edgeVertices L u).1 :=
    (edgeVertices_convexBodyCombination t K L u).1
  have hab : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hturn : 2 * Real.pi ≤ (0 : ℝ) + 2 * Real.pi := by simp
  obtain ⟨fM, hfM, hmM⟩ := positiveVertex_stieltjes_surface M 0 (2 * Real.pi) hab hturn
  obtain ⟨fK, hfK, hmK⟩ := positiveVertex_stieltjes_surface K 0 (2 * Real.pi) hab hturn
  obtain ⟨fL, hfL, hmL⟩ := positiveVertex_stieltjes_surface L 0 (2 * Real.pi) hab hturn
  have hmeasure (i : Fin 2) : intervalStieltjesMeasure (fM i) =
      r • intervalStieltjesMeasure (fK i) + s • intervalStieltjesMeasure (fL i) := by
    obtain ⟨f, hfun, hfm⟩ := intervalStieltjes_linear_combination
      0 (2 * Real.pi) (fK i) (fL i) r s
    have heq : intervalStieltjesMeasure f = intervalStieltjesMeasure (fM i) := by
      apply intervalStieltjesMeasure_congr
      intro x
      rw [hfun, hfK, hfL, hfM]
      have hv := congrArg (fun p : Point ↦ p i)
        (hvertex (((x : Set.Icc (0 : ℝ) (2 * Real.pi)) : ℝ) : Real.Angle))
      simpa [r, s] using hv.symm
    rwa [← heq]
  ext A hA
  let E : Set (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    {x | 0 < (x : ℝ) ∧ (((x : ℝ) : Real.Angle)) ∈ A}
  have hE : MeasurableSet E := by
    exact (measurableSet_Ioi.preimage measurable_subtype_coe).inter
      (hA.preimage (Real.Angle.continuous_coe.comp continuous_subtype_val).measurable)
  have hEa : ∀ x ∈ E, 0 < (x : ℝ) := fun _ hx ↦ hx.1
  have himage : (fun x : Set.Icc (0 : ℝ) (2 * Real.pi) ↦
      (((x : ℝ) : Real.Angle))) '' E = A := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hu
      let _ : Fact (0 < 2 * Real.pi) := ⟨hab⟩
      let x := AddCircle.equivIoc (2 * Real.pi) 0 u
      have hx : (x : ℝ) ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by simpa using x.property
      let y : Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨x, hx.1.le, hx.2⟩
      have hxu : (((x : ℝ) : Real.Angle)) = u := AddCircle.coe_equivIoc
      refine ⟨y, ⟨hx.1, ?_⟩, ?_⟩
      · simpa [y, hxu] using hu
      · simpa [y] using hxu
  have hmassM := sum_intervalStieltjesIntegral_positiveVertex_tangent
    M hab hturn fM hmM E hE hEa
  have hmassK := sum_intervalStieltjesIntegral_positiveVertex_tangent
    K hab hturn fK hmK E hE hEa
  have hmassL := sum_intervalStieltjesIntegral_positiveVertex_tangent
    L hab hturn fL hmL E hE hEa
  rw [himage] at hmassM hmassK hmassL
  have hstieltjes (i : Fin 2) :
      intervalStieltjesIntegral (fM i)
          (fun x ↦ tangentVector ((((x : Set.Icc (0 : ℝ) (2 * Real.pi)) : ℝ) :
            Real.Angle)) i) E =
        r * intervalStieltjesIntegral (fK i)
            (fun x ↦ tangentVector ((((x : Set.Icc (0 : ℝ) (2 * Real.pi)) : ℝ) :
              Real.Angle)) i) E +
          s * intervalStieltjesIntegral (fL i)
            (fun x ↦ tangentVector ((((x : Set.Icc (0 : ℝ) (2 * Real.pi)) : ℝ) :
              Real.Angle)) i) E := by
    have hq : Continuous (fun x : Set.Icc (0 : ℝ) (2 * Real.pi) ↦
        tangentVector (((x : ℝ) : Real.Angle)) i) := by
      have hi : Continuous (fun u : Real.Angle ↦ tangentVector u i) := by
        fin_cases i
        · exact Real.Angle.continuous_sin.neg
        · exact Real.Angle.continuous_cos
      exact hi.comp (Real.Angle.continuous_coe.comp continuous_subtype_val)
    have hrint : (r • VectorMeasure.restrict (intervalStieltjesMeasure (fK i)) E).Integrable
        (fun x ↦ tangentVector (((x : ℝ) : Real.Angle)) i) :=
      ((fK i).integrable_of_continuous hq).integrableOn.smul_vectorMeasure r
    have hsint : (s • VectorMeasure.restrict (intervalStieltjesMeasure (fL i)) E).Integrable
        (fun x ↦ tangentVector (((x : ℝ) : Real.Angle)) i) :=
      ((fL i).integrable_of_continuous hq).integrableOn.smul_vectorMeasure s
    unfold intervalStieltjesIntegral
    rw [hmeasure i, VectorMeasure.restrict_add, VectorMeasure.restrict_smul,
      VectorMeasure.restrict_smul, VectorMeasure.integral_add_vectorMeasure hrint hsint,
      VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure]
    rfl
  have hreal : (surfaceAreaMeasure M A).toReal =
      r * (surfaceAreaMeasure K A).toReal + s * (surfaceAreaMeasure L A).toReal := by
    rw [← hmassM, ← hmassK, ← hmassL, Fin.sum_univ_two]
    rw [hstieltjes 0, hstieltjes 1]
    simp only [Fin.sum_univ_two]
    ring
  let _ : IsFiniteMeasure (surfaceAreaMeasure M) := (surfaceAreaMeasure_face_union M).1
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  let _ : IsFiniteMeasure (surfaceAreaMeasure L) := (surfaceAreaMeasure_face_union L).1
  have hKtop : surfaceAreaMeasure K A ≠ ⊤ := measure_ne_top _ A
  have hLtop : surfaceAreaMeasure L A ≠ ⊤ := measure_ne_top _ A
  have hright :
      (ENNReal.ofReal (1 - (t : ℝ)) • surfaceAreaMeasure K +
        ENNReal.ofReal (t : ℝ) • surfaceAreaMeasure L) A ≠ ⊤ := by
    rw [Measure.add_apply]
    simp only [Measure.smul_apply]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLtop⟩
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ A) hright).mp
  rw [show convexBodyCombination t K L = M from rfl, hreal]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLtop),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr t.2.2), ENNReal.toReal_ofReal t.2.1]

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
# Angular densities of the opposite surface measure

The opposite surface measure `(oppositeSurfaceData K).1` is the surface-area measure of `K`
translated by `π`, so it reads the *negative* vertex data of `K` at the angle `s` as the positive
vertex data at `π + s`.  Transporting `surfaceAreaMeasure_angleImage_eq_setLIntegral` along that
translation identifies it with a Lebesgue density whenever the positive vertex of `K` at normal
`π + s` is traced by a differentiable curve `F` with derivative `-(g s) • tangentVector s`
(`oppositeSurfaceData_angleImage_eq_withDensity`); the extra minus sign is exactly
`tangentVector_add_pi`.

The two variants `oppositeSurfaceData_angleImage_eq_withDensity_of_openLeft` and
`…_of_openRight` drop the vertex information at one endpoint of the window by exhausting the
window from the other side with `measure_angleImage_eq_of_iUnion`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- An Archimedean step used to exhaust an open interval endpoint. -/
private theorem exists_nat_div_add_two_lt {d e : ℝ} (he : 0 < e) :
    ∃ n : ℕ, d / (n + 2) < e := by
  obtain ⟨n, hn⟩ := exists_nat_gt (d / e)
  refine ⟨n, ?_⟩
  have hpos : (0 : ℝ) < n + 2 := by positivity
  rw [div_lt_iff₀ hpos]
  have h : d / e < n + 2 := by linarith
  rw [div_lt_iff₀ he] at h
  linarith

/-- The angular projection reads the opposite surface measure through the `π`-shifted window. -/
theorem oppositeSurfaceData_angleImage (K : ConvexBody Point) {S : Set ℝ}
    (hS : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' S)) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      surfaceAreaMeasure K
        ((fun s : ℝ ↦ (s : Real.Angle)) '' ((fun s : ℝ ↦ s + Real.pi) '' S)) := by
  have hm : Measurable fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle) :=
    (continuous_id.sub continuous_const).measurable
  have hpre : (fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle)) ⁻¹'
      ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      (fun s : ℝ ↦ (s : Real.Angle)) '' ((fun s : ℝ ↦ s + Real.pi) '' S) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨s, hs, hsx⟩
      refine ⟨s + Real.pi, ⟨s, hs, rfl⟩, ?_⟩
      rw [Real.Angle.coe_add, hsx]
      abel
    · rintro ⟨r, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨s, hs, ?_⟩
      rw [Real.Angle.coe_add]
      abel
  show Measure.map (fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle))
    (surfaceAreaMeasure K) _ = _
  rw [Measure.map_apply hm hS, hpre]

/-- Suppose that on the angular window `(π + a, π + b]`, of at most one turn, the positive vertex
of `K` at normal `π + s` is traced by a curve `F` with derivative `-(g s) • v_s`, where `g` is
continuous and nonnegative.  Then the opposite surface measure of the angular image of a
measurable `S ⊆ (a, b]` is the weighted Lebesgue measure of `S` for any weight `f` agreeing with
`g` on the open window. -/
theorem oppositeSurfaceData_angleImage_eq_withDensity (K : ConvexBody Point) {a b : ℝ}
    (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point) (f g : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (-(g s) • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hgnn : ∀ s ∈ Set.Ioc a b, 0 ≤ g s) (hfg : ∀ s ∈ Set.Ioo a b, f s = g s)
    (hvertex : ∀ s ∈ Set.Icc a b, (edgeVertices K ((Real.pi + s : ℝ) : Real.Angle)).1 = F s)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc a b) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (f s)) S := by
  have hemb : MeasurableEmbedding fun s : ℝ ↦ s + Real.pi :=
    (MeasurableEquiv.addRight Real.pi).measurableEmbedding
  have himg : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' S) :=
    Real.Angle.measurableSet_image_of_subset_Ioc hturn hS hSsub
  have hSmeas : MeasurableSet ((fun s : ℝ ↦ s + Real.pi) '' S) := hemb.measurableSet_image' hS
  have hSsub' : (fun s : ℝ ↦ s + Real.pi) '' S ⊆ Set.Ioc (a + Real.pi) (b + Real.pi) := by
    rintro r ⟨s, hs, rfl⟩
    exact ⟨by linarith [(hSsub hs).1], by linarith [(hSsub hs).2]⟩
  -- the vertex curve of the shifted window and its derivative
  have hshift : ∀ r : ℝ, tangentVector ((r - Real.pi : ℝ) : Real.Angle) =
      -tangentVector (r : Real.Angle) := by
    intro r
    have h := tangentVector_add_pi (r - Real.pi)
    rw [show r - Real.pi + Real.pi = r from by ring] at h
    rw [h, neg_neg]
  have hF' : ∀ r : ℝ, HasDerivAt (fun r : ℝ ↦ F (r - Real.pi))
      (g (r - Real.pi) • tangentVector (r : Real.Angle)) r := by
    intro r
    have h := (hF (r - Real.pi)).scomp r ((hasDerivAt_id r).sub_const Real.pi)
    rw [hshift r] at h
    refine h.congr_deriv ?_
    module
  have hvertex' : ∀ r ∈ Set.Icc (a + Real.pi) (b + Real.pi),
      (edgeVertices K (r : Real.Angle)).1 = F (r - Real.pi) := by
    intro r hr
    have h := hvertex (r - Real.pi) ⟨by linarith [hr.1], by linarith [hr.2]⟩
    rw [show Real.pi + (r - Real.pi) = r from by ring] at h
    exact h
  have hmain := surfaceAreaMeasure_angleImage_eq_setLIntegral K (a := a + Real.pi)
    (b := b + Real.pi) (by linarith) (by linarith) (fun r ↦ F (r - Real.pi))
    (fun r ↦ g (r - Real.pi)) hF' (hg.comp (continuous_id.sub continuous_const))
    (fun r hr ↦ hgnn (r - Real.pi) ⟨by linarith [hr.1], by linarith [hr.2]⟩) hvertex'
    hSmeas hSsub'
  -- change variables back to the unshifted window
  rw [oppositeSurfaceData_angleImage K himg, hmain,
    setLIntegral_comp_sub_right (fun s ↦ ENNReal.ofReal (g s)) Real.pi,
    hemb.injective.preimage_image, withDensity_apply _ hS]
  -- the two densities agree off the right endpoint
  refine (lintegral_congr_ae ?_).symm
  have hne : ∀ᵐ s ∂volume.restrict S, s ∈ Set.Ioo a b := by
    refine ae_restrict_mem_of_countable_diff hS (Set.countable_singleton b) ?_
    rintro s ⟨hs, hsA⟩
    have h := hSsub hs
    rcases eq_or_lt_of_le h.2 with heq | hlt
    · exact heq
    · exact absurd (Set.mem_Ioo.2 ⟨h.1, hlt⟩) hsA
  filter_upwards [hne] with s hs
  rw [hfg s hs]

/-- The variant of `oppositeSurfaceData_angleImage_eq_withDensity` whose left endpoint carries no
vertex information: the window is exhausted from the right. -/
theorem oppositeSurfaceData_angleImage_eq_withDensity_of_openLeft (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point)
    (f g : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (-(g s) • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hgnn : ∀ s ∈ Set.Ioc a b, 0 ≤ g s) (hfg : ∀ s ∈ Set.Ioo a b, f s = g s)
    (hvertex : ∀ s ∈ Set.Ioc a b, (edgeVertices K ((Real.pi + s : ℝ) : Real.Angle)).1 = F s)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc a b) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (f s)) S := by
  have hba : 0 < b - a := by linarith
  have hpos : ∀ n : ℕ, 0 < (b - a) / (n + 2) := fun n ↦ by positivity
  have hlt : ∀ n : ℕ, a + (b - a) / (n + 2) < b := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / 2 := by gcongr; linarith
    linarith
  refine measure_angleImage_eq_of_iUnion (μ := (oppositeSurfaceData K).1)
    (J := fun n : ℕ ↦ Set.Ioc (a + (b - a) / (n + 2)) b)
    (ν := volume.withDensity (fun s ↦ ENNReal.ofReal (f s))) ?_ (fun n ↦ measurableSet_Ioc) ?_
    S hS ?_
  · intro m n hmn
    refine Set.Ioc_subset_Ioc ?_ le_rfl
    have hmn' : ((m : ℝ)) ≤ n := Nat.cast_le.2 hmn
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / ((m : ℝ) + 2) := by gcongr
    linarith
  · intro n T hT hTsub
    refine oppositeSurfaceData_angleImage_eq_withDensity K (hlt n) (by linarith [hpos n])
      F f g hF hg (fun s hs ↦ hgnn s ⟨by linarith [hs.1, hpos n], hs.2⟩)
      (fun s hs ↦ hfg s ⟨by linarith [hs.1, hpos n], hs.2⟩)
      (fun s hs ↦ hvertex s ⟨by linarith [hs.1, hpos n], hs.2⟩) hT hTsub
  · intro s hs
    obtain ⟨n, hn⟩ := exists_nat_div_add_two_lt (d := b - a) (e := s - a)
      (by linarith [(hSsub hs).1])
    exact Set.mem_iUnion.2 ⟨n, ⟨by linarith, (hSsub hs).2⟩⟩

/-- The variant of `oppositeSurfaceData_angleImage_eq_withDensity` whose right endpoint carries no
vertex information: the window is exhausted from the left. -/
theorem oppositeSurfaceData_angleImage_eq_withDensity_of_openRight (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point)
    (f g : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (-(g s) • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hgnn : ∀ s ∈ Set.Ioo a b, 0 ≤ g s) (hfg : ∀ s ∈ Set.Ioo a b, f s = g s)
    (hvertex : ∀ s ∈ Set.Ico a b, (edgeVertices K ((Real.pi + s : ℝ) : Real.Angle)).1 = F s)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioo a b) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (f s)) S := by
  have hba : 0 < b - a := by linarith
  have hpos : ∀ n : ℕ, 0 < (b - a) / (n + 2) := fun n ↦ by positivity
  have hlt : ∀ n : ℕ, a < b - (b - a) / (n + 2) := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / 2 := by gcongr; linarith
    linarith
  refine measure_angleImage_eq_of_iUnion (μ := (oppositeSurfaceData K).1)
    (J := fun n : ℕ ↦ Set.Ioc a (b - (b - a) / (n + 2)))
    (ν := volume.withDensity (fun s ↦ ENNReal.ofReal (f s))) ?_ (fun n ↦ measurableSet_Ioc) ?_
    S hS ?_
  · intro m n hmn
    refine Set.Ioc_subset_Ioc le_rfl ?_
    have hmn' : ((m : ℝ)) ≤ n := Nat.cast_le.2 hmn
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / ((m : ℝ) + 2) := by gcongr
    linarith
  · intro n T hT hTsub
    refine oppositeSurfaceData_angleImage_eq_withDensity K (hlt n) (by linarith [hpos n])
      F f g hF hg (fun s hs ↦ hgnn s ⟨hs.1, by linarith [hs.2, hpos n]⟩)
      (fun s hs ↦ hfg s ⟨hs.1, by linarith [hs.2, hpos n]⟩)
      (fun s hs ↦ hvertex s ⟨hs.1, by linarith [hs.2, hpos n]⟩) hT hTsub
  · intro s hs
    obtain ⟨n, hn⟩ := exists_nat_div_add_two_lt (d := b - a) (e := b - s)
      (by linarith [(hSsub hs).2])
    exact Set.mem_iUnion.2 ⟨n, ⟨(hSsub hs).1, by linarith⟩⟩

end MovingSofa

end

end

end
