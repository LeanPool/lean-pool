/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Analysis.Foundations.Development002

public import LeanPool.MovingSofa.Analysis.Foundations.Development005
public import LeanPool.MovingSofa.Analysis.Foundations.Development003

public import LeanPool.MovingSofa.Curve.Foundations.Development001

public import LeanPool.MovingSofa.ForMathlib.Algebra.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.Analysis.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.MeasureTheory.Foundations.Development001
/-!
# Moving sofa: related mathematical developments

* `Convex.SupportArea`.
* `Convex.Linearity`.
* `Convex.MixedArea`.
* `Convex.TangentLinePath`.
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
# The area of a convex body as a support-function surface integral

The planar area of a nonempty compact convex set is one half of the integral of its support
function against its surface area measure. The identity is proved for finite convex hulls by
fanning the polygon into triangles over an interior base point, and then transported to an
arbitrary body by polygon approximation and weak convergence of surface measures. The same
integral, taken with the two bodies decoupled, is convex-bilinear.
-/

@[expose] public section

noncomputable section

open scoped unitInterval Pointwise Topology
open MeasureTheory Filter

namespace MovingSofa

private theorem one_lt_finrank_point : 1 < Module.finrank ℝ Point := by
  simp [Point]

private theorem normalVector_ne_zero (t : Real.Angle) : normalVector t ≠ 0 := by
  intro h
  have hone := norm_normalVector t
  rw [h, norm_zero] at hone
  exact zero_ne_one hone

/-- The ordered endpoints of an exposed edge differ by its length in the positive tangent
direction. -/
theorem edgeVertices_fst_sub_snd_eq_dist_smul_tangentVector
    (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).1 - (edgeVertices K t).2 =
      dist (edgeVertices K t).1 (edgeVertices K t).2 • tangentVector t := by
  let a := (edgeVertices K t).1
  let b := (edgeVertices K t).2
  let r := inner ℝ (a - b) (tangentVector t)
  have hnormal : inner ℝ (a - b) (normalVector t) = 0 := by
    dsimp only [a, b]
    rw [inner_sub_left]
    rw [(edgeVertices_fst_mem K t).2, (edgeVertices_snd_mem K t).2, sub_self]
  have hdecomp := inner_normalVector_smul_add_inner_tangentVector_smul (a - b) t
  have hvec : r • tangentVector t = a - b := by
    simpa only [r, hnormal, zero_smul, zero_add] using hdecomp
  have hr : 0 ≤ r := by
    let S : Set ℝ :=
      (fun p ↦ inner ℝ p (tangentVector t)) '' exposedEdge K t
    simp only [r, inner_sub_left, a, b, inner_edgeVertices_fst_tangent,
      inner_edgeVertices_snd_tangent]
    have hcompact : IsCompact S :=
      (isCompact_exposedEdge K t).image (continuous_id.inner continuous_const)
    apply sub_nonneg.mpr
    simpa only [S] using
      (csInf_le_csSup (s := S) ((exposedEdge_nonempty K t).image _)
        (hb := hcompact.bddBelow) (ha := hcompact.bddAbove))
  have htangent : ‖tangentVector t‖ = 1 := by
    induction t using Real.Angle.induction_on with
    | _ t =>
      rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
      rw [EuclideanSpace.norm_sq_eq]
      simp [tangentVector, frame, Fin.sum_univ_two]
  have hnorm := congrArg norm hvec
  have hre : r = dist a b := by
    simpa only [norm_smul, htangent, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hr, dist_eq_norm] using hnorm
  simpa only [a, b, ← hre] using hvec.symm

/-- The half support integral is convex-bilinear in the two body arguments. -/
theorem supportIntegral_bilinear :
    IsConvexBilinear convexBodyCombination convexBodyCombination realCombination
      (fun K L : ConvexBody Point ↦ (1 / 2 : ℝ) * ∫ t,
          supportValue K t ∂surfaceAreaMeasure L) := by
  have hcont (K : ConvexBody Point) : Continuous (fun u : Real.Angle ↦ supportValue K u) :=
    (compactSet_support_continuity K K K.nonempty K.isCompact K.nonempty K.isCompact).2.2.1
  have hint (K L : ConvexBody Point) :
      Integrable (fun u : Real.Angle ↦ supportValue K u) (surfaceAreaMeasure L) := by
    let _ : IsFiniteMeasure (surfaceAreaMeasure L) := (surfaceAreaMeasure_face_union L).1
    exact (hcont K).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  constructor
  · intro K t L M
    have hmeasure := surfaceAreaMeasure_convexBodyCombination t L M
    change (1 / 2 : ℝ) * (∫ u, supportValue K u ∂surfaceAreaMeasure
        (convexBodyCombination t L M)) = _
    simp only [realCombination]
    rw [hmeasure, integral_add_measure ((hint K L).smul_measure _) ((hint K M).smul_measure _)]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal,
      sub_nonneg.mpr (show (t : ℝ) ≤ 1 from t.property.2), t.property.1]
    ring
    all_goals exact ENNReal.ofReal_ne_top
  · intro L t K M
    change (1 / 2 : ℝ) * (∫ u, supportValue (convexBodyCombination t K M) u
      ∂surfaceAreaMeasure L) = _
    simp only [realCombination]
    have hfun : (fun u : Real.Angle ↦ supportValue (convexBodyCombination t K M) u) =
        fun u ↦ (1 - (t : ℝ)) * supportValue K u + (t : ℝ) * supportValue M u := by
      funext u
      exact supportValue_convexBodyCombination t K M u
    rw [hfun, integral_add ((hint K L).const_mul _) ((hint M L).const_mul _),
      integral_const_mul, integral_const_mul]
    ring

/-- The mixed support integral is Hausdorff continuous in the two bodies simultaneously. -/
theorem tendsto_integral_supportValue_of_hausdorff_pair
    (P Q : ℕ → ConvexBody Point) (K L : ConvexBody Point)
    (hPK : Tendsto (fun n ↦ Metric.hausdorffDist (P n : Set Point) (K : Set Point))
      atTop (𝓝 0))
    (hQL : Tendsto (fun n ↦ Metric.hausdorffDist (Q n : Set Point) (L : Set Point))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ u, supportValue (P n) u ∂surfaceAreaMeasure (Q n)) atTop
      (𝓝 (∫ u, supportValue K u ∂surfaceAreaMeasure L)) := by
  have hcont (M : ConvexBody Point) : Continuous (supportValue M) :=
    (compactSet_support_continuity M M M.nonempty M.isCompact M.nonempty M.isCompact).2.2.1
  have hint (M N : ConvexBody Point) : Integrable (supportValue M) (surfaceAreaMeasure N) := by
    let _ : IsFiniteMeasure (surfaceAreaMeasure N) := (surfaceAreaMeasure_face_union N).1
    exact (hcont M).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hmass : Tendsto (fun n ↦ (surfaceAreaMeasure (Q n)).real Set.univ) atTop
      (𝓝 ((surfaceAreaMeasure L).real Set.univ)) := by
    simpa using surfaceAreaMeasure_weak_continuity Q L hQL (fun _ ↦ (1 : ℝ)) continuous_const
  have hbound (n : ℕ) :
      ‖∫ u, supportValue (P n) u - supportValue K u ∂surfaceAreaMeasure (Q n)‖ ≤
        Metric.hausdorffDist (P n : Set Point) (K : Set Point) *
          (surfaceAreaMeasure (Q n)).real Set.univ := by
    let _ : IsFiniteMeasure (surfaceAreaMeasure (Q n)) :=
      (surfaceAreaMeasure_face_union (Q n)).1
    apply norm_integral_le_of_norm_le_const
    filter_upwards [] with u
    simpa only [Real.norm_eq_abs, vectorSupport, supportValue] using
      (compactSet_support_continuity (P n) K (P n).nonempty
        (P n).isCompact K.nonempty K.isCompact).2.1 (normalVector u) (norm_normalVector u)
  have herror : Tendsto
      (fun n ↦ ∫ u, supportValue (P n) u - supportValue K u ∂surfaceAreaMeasure (Q n))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hbound (by simpa using hPK.mul hmass)
  have hfixed := surfaceAreaMeasure_weak_continuity Q L hQL (supportValue K) (hcont K)
  have hsum := herror.add hfixed
  simp only [zero_add] at hsum
  convert hsum using 1
  funext n
  rw [integral_sub (hint (P n) (Q n)) (hint K (Q n)), sub_add_cancel]

/-- The support integral of a body against its own surface measure is Hausdorff continuous. -/
theorem tendsto_integral_supportValue_of_hausdorff
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ u, supportValue (K n) u ∂surfaceAreaMeasure (K n)) atTop
      (𝓝 (∫ u, supportValue L u ∂surfaceAreaMeasure L)) :=
  tendsto_integral_supportValue_of_hausdorff_pair K K L L hlim hlim

/-- For a finite convex hull, the support integral is the finite sum over its proper edges. -/
private theorem integral_supportValue_surfaceAreaMeasure_eq_sum_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) :
    ∫ t, supportValue K t ∂surfaceAreaMeasure K =
      Finset.sum (finite_properEdgeNormal_angles K V hKV).toFinset
        (fun t ↦ (surfaceAreaMeasure K).real {t} * supportValue K t) := by
  classical
  let N : Set Real.Angle := {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}
  have hNfinite : N.Finite := finite_properEdgeNormal_angles K V hKV
  have hae : ∀ᵐ t ∂surfaceAreaMeasure K, t ∈ N := by
    rw [ae_iff]
    simpa only [N, Set.mem_ofPred_eq, not_ne_iff] using
      surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_eq_convexHull K V hKV
  have hrestrict : (surfaceAreaMeasure K).restrict N = surfaceAreaMeasure K :=
    Measure.restrict_eq_self_of_ae_mem hae
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  calc
    ∫ t, supportValue K t ∂surfaceAreaMeasure K =
        ∫ t in N, supportValue K t ∂surfaceAreaMeasure K := by
          rw [hrestrict]
    _ = _ := by
      rw [show N = ↑hNfinite.toFinset by ext t; simp [N]]
      exact MeasureTheory.setIntegral_finset _
        (μ := surfaceAreaMeasure K) (f := supportValue K) IntegrableOn.finset

/-- On a finite convex hull, each coefficient in the support sum is the corresponding edge
length. -/
theorem integral_supportValue_surfaceAreaMeasure_eq_sum_edgeLength
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) :
    ∫ t, supportValue K t ∂surfaceAreaMeasure K =
      Finset.sum (finite_properEdgeNormal_angles K V hKV).toFinset
        (fun t ↦ dist (edgeVertices K t).1 (edgeVertices K t).2 * supportValue K t) := by
  rw [integral_supportValue_surfaceAreaMeasure_eq_sum_properEdgeNormals K V hKV]
  apply Finset.sum_congr rfl
  intro t _
  change (surfaceAreaMeasure K {t}).toReal * supportValue K t = _
  rw [(surfaceAreaMeasure_atom_length K t).2.1, ENNReal.toReal_ofReal dist_nonneg]

/-- The total tangent vector of the surface-area measure vanishes. -/
theorem integral_tangentVector_surfaceAreaMeasure_eq_zero (K : ConvexBody Point) :
    ∫ t, tangentVector t ∂surfaceAreaMeasure K = 0 := by
  have himage :
      (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc 0 (2 * Real.pi) = Set.univ := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioc, Set.mem_univ, iff_true]
    let _ : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
    let s := AddCircle.equivIoc (2 * Real.pi) 0 u
    have hs : (s : ℝ) ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
      simpa using s.property
    exact ⟨s, hs, AddCircle.coe_equivIoc⟩
  rw [← setIntegral_univ, ← himage,
    integral_tangentVector_surfaceAreaMeasure K Real.two_pi_pos (by simp)]
  simp

/-- Every non-generating boundary point of a two-dimensional finite convex hull lies on a
proper exposed edge. -/
theorem exists_mem_properExposedEdge_of_mem_frontier
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (hK : (interior (K : Set Point)).Nonempty) {p : Point}
    (hp : p ∈ frontier (K : Set Point)) (hpV : p ∉ V) :
    ∃ t : Real.Angle,
      (edgeVertices K t).1 ≠ (edgeVertices K t).2 ∧ p ∈ exposedEdge K t := by
  obtain ⟨t, hpt⟩ := exists_mem_exposedEdge_of_mem_frontier K hK hp
  refine ⟨t, ?_, hpt⟩
  intro heq
  rw [exposedEdge_eq_segment_edgeVertices, heq, segment_same] at hpt
  apply hpV
  simpa only [Set.mem_singleton_iff] using
    hpt.symm ▸ (edgeVertices_mem_of_eq_convexHull K V hKV t).2

/-- The support-area identity holds for a singleton convex body. -/
theorem convexBody_area_support_integral_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) :
    ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K := by
  obtain ⟨p, hp⟩ := K.nonempty
  have hsingleton : (K : Set Point) = {p} := hK.eq_singleton_of_mem hp
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hK, integral_zero_measure, mul_zero]
  simp [ClassicalResults.area, hsingleton]

/-- The support-area identity holds for a nondegenerate segment presentation. -/
theorem convexBody_area_support_integral_of_segmentPresentation
    (K : ConvexBody Point) (d : Point × Point × Real.Angle)
    (hd : IsSegmentPresentation K d) :
    ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K := by
  have hline : (K : Set Point) ⊆
      {p | inner ℝ p (normalVector d.2.2) = inner ℝ d.1 (normalVector d.2.2)} := by
    intro p hp
    rw [hd.2.1, segment_eq_image'] at hp
    obtain ⟨s, _, rfl⟩ := hp
    change inner ℝ (d.1 + s • (d.2.1 - d.1)) (normalVector d.2.2) = _
    rw [inner_add_left, inner_smul_left, hd.2.2, mul_zero, add_zero]
  have hvolume : volume (K : Set Point) = 0 :=
    measure_mono_null hline
      (volume.addHaar_setOf_real_inner_eq (normalVector_ne_zero d.2.2) _)
  have hnormalPi : normalVector (d.2.2 + (Real.pi : Real.Angle)) =
      -normalVector d.2.2 := by
    induction d.2.2 using Real.Angle.induction_on with
    | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
  have hdmem : d.1 ∈ exposedEdge K d.2.2 := by
    rw [exposedEdge_eq_segment_of_orthogonal K d hd d.2.2 hd.2.2, hd.2.1]
    exact left_mem_segment ℝ _ _
  have hpimem : d.1 ∈ exposedEdge K (d.2.2 + (Real.pi : Real.Angle)) := by
    rw [exposedEdge_eq_segment_of_orthogonal K d hd _ (by
      rw [hnormalPi, inner_neg_right, hd.2.2, neg_zero]), hd.2.1]
    exact left_mem_segment ℝ _ _
  have hsupport : supportValue K d.2.2 +
      supportValue K (d.2.2 + (Real.pi : Real.Angle)) = 0 := by
    rw [← hdmem.2, ← hpimem.2, hnormalPi, inner_neg_right, add_neg_cancel]
  have hint₁ : Integrable (supportValue K) (Measure.dirac d.2.2) :=
    integrable_dirac (by simp)
  have hint₂ : Integrable (supportValue K)
      (Measure.dirac (d.2.2 + (Real.pi : Real.Angle))) := integrable_dirac (by simp)
  rw [show ClassicalResults.area (K : Set Point) = 0 by
    simp [ClassicalResults.area, hvolume],
    surfaceAreaMeasure_eq_segmentPresentation K d hd]
  rw [integral_smul_measure, integral_add_measure hint₁ hint₂]
  simp [hsupport]

/-- The support-area identity for finite convex hulls extends to every convex body. -/
theorem convexBody_area_support_integral_of_finiteHull
    (hpolygon : ∀ (P : ConvexBody Point) (V : Finset Point), V.Nonempty →
      (P : Set Point) = convexHull ℝ (V : Set Point) →
      ClassicalResults.area (P : Set Point) =
        (1 / 2 : ℝ) * ∫ t, supportValue P t ∂surfaceAreaMeasure P) :
    ∀ K : ConvexBody Point, ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K := by
  intro K
  obtain ⟨V, P, hP, hdist⟩ := exists_facePreserving_polygonApproximation K ∅
  have hlim : Tendsto (fun n ↦ Metric.hausdorffDist (P n : Set Point) (K : Set Point))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ Metric.hausdorffDist_nonneg)
      (Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hdist n hn⟩)
    exact tendsto_one_div_atTop_nhds_zero_nat
  have harea := convexArea_hausdorff_continuity P K hlim
  have hintegral := (tendsto_integral_supportValue_of_hausdorff P K hlim).const_mul (1 / 2)
  have heq (n : ℕ) : ClassicalResults.area (P n : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue (P n) t ∂surfaceAreaMeasure (P n) :=
    hpolygon (P n) (V n) (hP n).1 (hP n).2.1
  exact tendsto_nhds_unique harea
    (hintegral.congr' (Filter.Eventually.of_forall fun n ↦ (heq n).symm))

/-- The area identity and the explicit support integral's bilinearity give quadraticity. -/
theorem convexBody_area_support_integral_of_area_identity
    (harea : ∀ K : ConvexBody Point, ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K) :
    (∀ K : ConvexBody Point, ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K) ∧
    IsConvexBilinear convexBodyCombination convexBodyCombination realCombination
      (fun K L : ConvexBody Point ↦
        (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure L) ∧
    IsQuadraticFunctional convexBodyCombination
      (fun K : ConvexBody Point ↦ ClassicalResults.area (K : Set Point)) := by
  refine ⟨harea, supportIntegral_bilinear, ?_⟩
  exact ⟨_, supportIntegral_bilinear, harea⟩

/-- An exposed-edge point realizes the support value. -/
theorem inner_eq_supportValue_of_mem_exposedEdge (K : ConvexBody Point) (t : Real.Angle)
    {p : Point} (hp : p ∈ exposedEdge K t) :
    inner ℝ p (normalVector t) = supportValue K t := hp.2

/-- An interior base point lies strictly inside every supporting line. -/
theorem inner_lt_supportValue_of_mem_interior (K : ConvexBody Point) {o : Point}
    (ho : o ∈ interior (K : Set Point)) (t : Real.Angle) :
    inner ℝ o (normalVector t) < supportValue K t := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior o ho
  have hnorm : inner ℝ (normalVector t) (normalVector t) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_normalVector]
    norm_num
  have hpball : o + (ε / 2) • normalVector t ∈ Metric.ball o ε := by
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      norm_normalVector, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hle := inner_le_supportValue K (interior_subset (hball hpball)) t
  rw [inner_add_left, real_inner_smul_left, hnorm, mul_one] at hle
  linarith

/-- The oriented determinant of a triangle with one side in the positive tangent direction. -/
private theorem planeCrossProduct_add_smul_tangentVector (w : Point) (d : ℝ)
    (t : Real.Angle) :
    planeCrossProduct w (w + d • tangentVector t) = d * inner ℝ w (normalVector t) := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    simp [planeCrossProduct, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.inner_apply, Fin.sum_univ_two, normalVector, tangentVector, frame,
      Real.Angle.cos_coe, Real.Angle.sin_coe]
    ring

/-- Each exposed-edge summand is the oriented determinant of its triangle over the base
point. -/
theorem edgeLength_mul_supportValue_sub_eq_planeCrossProduct
    (K : ConvexBody Point) (o : Point) (t : Real.Angle) :
    dist (edgeVertices K t).1 (edgeVertices K t).2 *
        (supportValue K t - inner ℝ o (normalVector t)) =
      planeCrossProduct ((edgeVertices K t).2 - o) ((edgeVertices K t).1 - o) := by
  have hedge := edgeVertices_fst_sub_snd_eq_dist_smul_tangentVector K t
  have ha : (edgeVertices K t).1 - o =
      ((edgeVertices K t).2 - o) +
        dist (edgeVertices K t).1 (edgeVertices K t).2 • tangentVector t := by
    rw [← hedge]
    abel
  rw [ha, planeCrossProduct_add_smul_tangentVector, inner_sub_left,
    inner_eq_supportValue_of_mem_exposedEdge K t (edgeVertices_snd_mem K t)]

/-- The fan triangle over an exposed edge, based at a chosen interior point. -/
private def edgeTriangle (K : ConvexBody Point) (o : Point) (t : Real.Angle) : Set Point :=
  convexHull ℝ ({o, (edgeVertices K t).2, (edgeVertices K t).1} : Set Point)

/-- The finitely many rays from a base point through the generating vertices. -/
private def vertexRayUnion (o : Point) (V : Finset Point) : Set Point :=
  ⋃ v : ↥V, (o +ᵥ (ℝ ∙ ((v : Point) - o) : Set Point))

/-- The vertex rays through a base point have planar area zero. -/
private theorem volume_vertexRayUnion (o : Point) (V : Finset Point) :
    volume (vertexRayUnion o V) = 0 := by
  exact volume.addHaar_iUnion_vadd_span_singleton one_lt_finrank_point o _

/-- Away from the finitely many vertex rays, every polygon point lies in a proper-edge fan
triangle over the base point. -/
private theorem exists_mem_edgeTriangle_of_notMem_vertexRayUnion
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {o : Point} (ho : o ∈ interior (K : Set Point)) {x : Point}
    (hx : x ∈ (K : Set Point)) (hxline : x ∉ vertexRayUnion o V) :
    ∃ t : Real.Angle,
      (edgeVertices K t).1 ≠ (edgeVertices K t).2 ∧ x ∈ edgeTriangle K o t := by
  obtain ⟨p, hpfront, hxp⟩ := K.convex.exists_mem_frontier_mem_segment K.isCompact ho hx
  have hpV : p ∉ V := by
    intro hpV
    apply hxline
    refine Set.mem_iUnion.2 ⟨⟨p, hpV⟩, ?_⟩
    rw [segment_eq_image'] at hxp
    obtain ⟨c, _, hc⟩ := hxp
    have hc' : o + c • (p - o) = x := hc
    refine ⟨x - o, ?_, by simp only [vadd_eq_add]; abel⟩
    exact Submodule.mem_span_singleton.2 ⟨c, by rw [← hc']; abel⟩
  obtain ⟨t, htproper, hpt⟩ :=
    exists_mem_properExposedEdge_of_mem_frontier K V hKV ⟨o, ho⟩ hpfront hpV
  refine ⟨t, htproper, ?_⟩
  have hpT : p ∈ edgeTriangle K o t := by
    rw [exposedEdge_eq_segment_edgeVertices] at hpt
    exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) hpt
  exact (convex_convexHull ℝ _).segment_subset
    (subset_convexHull ℝ _ (by simp)) hpT hxp

/-- Two unit normals annihilating a common nonzero vector have vanishing angular sine. -/
private theorem sin_sub_eq_zero_of_inner_normalVector_eq_zero {u : Point} (hu : u ≠ 0)
    {s t : Real.Angle} (h1 : inner ℝ u (normalVector s) = 0)
    (h2 : inner ℝ u (normalVector t) = 0) : (t - s).sin = 0 := by
  induction s using Real.Angle.induction_on with
  | _ s =>
    induction t using Real.Angle.induction_on with
    | _ t =>
      have hu' : ¬(u 0 = 0 ∧ u 1 = 0) := by
        rintro ⟨ha, hb⟩
        refine hu ?_
        ext i
        fin_cases i <;> simpa
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
        normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
        Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
      rw [← Real.Angle.coe_sub, Real.Angle.sin_coe, Real.sin_sub]
      have hd0 : (Real.sin t * Real.cos s - Real.cos t * Real.sin s) * u 0 = 0 := by
        linear_combination Real.sin t * h1 - Real.sin s * h2
      have hd1 : (Real.sin t * Real.cos s - Real.cos t * Real.sin s) * u 1 = 0 := by
        linear_combination (-Real.cos t) * h1 + Real.cos s * h2
      rcases mul_eq_zero.mp hd0 with hD | hu0
      · exact hD
      rcases mul_eq_zero.mp hd1 with hD | hu1
      · exact hD
      exact absurd ⟨hu0, hu1⟩ hu'

/-- Distinct normal directions share at most one exposed-edge point. -/
theorem subsingleton_exposedEdge_inter (K : ConvexBody Point) {o : Point}
    (ho : o ∈ interior (K : Set Point)) {s t : Real.Angle} (hst : s ≠ t) :
    (exposedEdge K s ∩ exposedEdge K t).Subsingleton := by
  intro z hz w hw
  by_contra hzw
  have h1 : inner ℝ (z - w) (normalVector s) = 0 := by
    rw [inner_sub_left, inner_eq_supportValue_of_mem_exposedEdge K s hz.1,
      inner_eq_supportValue_of_mem_exposedEdge K s hw.1, sub_self]
  have h2 : inner ℝ (z - w) (normalVector t) = 0 := by
    rw [inner_sub_left, inner_eq_supportValue_of_mem_exposedEdge K t hz.2,
      inner_eq_supportValue_of_mem_exposedEdge K t hw.2, sub_self]
  have hsin := sin_sub_eq_zero_of_inner_normalVector_eq_zero (sub_ne_zero.mpr hzw) h1 h2
  rcases Real.Angle.sin_eq_zero_iff.mp hsin with hz0 | hpi
  · exact hst (by linear_combination (norm := abel) -hz0)
  · have ht : t = s + ((Real.pi : ℝ) : Real.Angle) := by
      linear_combination (norm := abel) hpi
    have hopp : normalVector t = -normalVector s := by
      rw [ht, normalVector_add_pi_angle]
    have hsum : supportValue K s + supportValue K t = 0 := by
      rw [← inner_eq_supportValue_of_mem_exposedEdge K s hz.1,
        ← inner_eq_supportValue_of_mem_exposedEdge K t hz.2, hopp, inner_neg_right,
        add_neg_cancel]
    have hs' := inner_lt_supportValue_of_mem_interior K ho s
    have ht' := inner_lt_supportValue_of_mem_interior K ho t
    rw [hopp, inner_neg_right] at ht'
    linarith

/-- A fan triangle is the union of the segments from the base point to its exposed edge. -/
private theorem edgeTriangle_eq_iUnion_segment (K : ConvexBody Point) (o : Point)
    (t : Real.Angle) :
    edgeTriangle K o t = ⋃ z ∈ exposedEdge K t, segment ℝ o z := by
  rw [edgeTriangle, exposedEdge_eq_segment_edgeVertices,
    show ({o, (edgeVertices K t).2, (edgeVertices K t).1} : Set Point) =
      insert o {(edgeVertices K t).2, (edgeVertices K t).1} from rfl,
    convexHull_insert ⟨(edgeVertices K t).2, by simp⟩, convexHull_pair,
    convexJoin_singleton_left]

/-- Fan triangles over distinct proper edges meet in a planar null set. -/
private theorem volume_edgeTriangle_inter_eq_zero (K : ConvexBody Point) {o : Point}
    (ho : o ∈ interior (K : Set Point)) {s t : Real.Angle} (hst : s ≠ t) :
    volume (edgeTriangle K o s ∩ edgeTriangle K o t) = 0 := by
  classical
  have hsub : ∀ x ∈ edgeTriangle K o s ∩ edgeTriangle K o t,
      x = o ∨ ∃ z ∈ exposedEdge K s ∩ exposedEdge K t, x ∈ segment ℝ o z := by
    rintro x ⟨hxs, hxt⟩
    rw [edgeTriangle_eq_iUnion_segment] at hxs hxt
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hxs
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hxt
    by_cases hxo : x = o
    · exact Or.inl hxo
    have hzw : z = w := K.convex.eq_of_mem_frontier_of_mem_segment K.isClosed ho hxo
      (exposedEdge_subset_frontier K s hz)
      (exposedEdge_subset_frontier K t hw) hxz hxw
    exact Or.inr ⟨z, ⟨hz, hzw ▸ hw⟩, hxz⟩
  by_cases hne : (exposedEdge K s ∩ exposedEdge K t).Nonempty
  · obtain ⟨q, hq⟩ := hne
    refine measure_mono_null (t := (o +ᵥ (ℝ ∙ (q - o) : Set Point))) ?_ ?_
    · intro x hx
      rcases hsub x hx with hxo | ⟨z, hzq, hxz⟩
      · exact ⟨0, Submodule.zero_mem _, by simp only [vadd_eq_add, hxo]; abel⟩
      · have hzeq : z = q := subsingleton_exposedEdge_inter K ho hst hzq hq
        subst hzeq
        rw [segment_eq_image'] at hxz
        obtain ⟨c, _, hc⟩ := hxz
        have hc' : o + c • (z - o) = x := hc
        exact ⟨x - o, Submodule.mem_span_singleton.2 ⟨c, by rw [← hc']; abel⟩,
          by simp only [vadd_eq_add]; abel⟩
    · exact volume.addHaar_vadd_span_singleton one_lt_finrank_point o (q - o)
  · refine measure_mono_null (t := ({o} : Set Point)) ?_ (measure_singleton o)
    intro x hx
    rcases hsub x hx with hxo | ⟨z, hz, _⟩
    · exact hxo
    · exact absurd ⟨z, hz⟩ hne

/-- The coordinate tangent integral of a surface measure vanishes. -/
theorem integral_tangentCoordinate_surfaceAreaMeasure_eq_zero (K : ConvexBody Point)
    (i : Fin 2) : ∫ t, tangentVector t i ∂surfaceAreaMeasure K = 0 := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hcont : Continuous (fun u : Real.Angle ↦ tangentVector u) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro j
    fin_cases j
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hu : Integrable (fun u : Real.Angle ↦ tangentVector u) (surfaceAreaMeasure K) :=
    hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hi := ContinuousLinearMap.integral_comp_comm
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i) hu
  change (∫ u, tangentVector u i ∂surfaceAreaMeasure K) =
    (∫ u, tangentVector u ∂surfaceAreaMeasure K) i at hi
  rw [hi, integral_tangentVector_surfaceAreaMeasure_eq_zero K]
  simp

/-- Atomic surface mass is the corresponding edge length. -/
private theorem surfaceAreaMeasure_real_singleton (K : ConvexBody Point) (t : Real.Angle) :
    (surfaceAreaMeasure K).real {t} = dist (edgeVertices K t).1 (edgeVertices K t).2 := by
  change (surfaceAreaMeasure K {t}).toReal = _
  rw [(surfaceAreaMeasure_atom_length K t).2.1, ENNReal.toReal_ofReal dist_nonneg]

/-- The proper-edge lengths of a polygon weight its tangent coordinates to zero. -/
theorem sum_edgeLength_mul_tangentCoordinate_eq_zero (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) (i : Fin 2) :
    ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
      dist (edgeVertices K t).1 (edgeVertices K t).2 * tangentVector t i = 0 := by
  classical
  have h := integral_tangentCoordinate_surfaceAreaMeasure_eq_sum_properEdgeNormals K V hKV i
    Set.univ MeasurableSet.univ
  rw [setIntegral_univ, integral_tangentCoordinate_surfaceAreaMeasure_eq_zero K i] at h
  rw [show (finite_properEdgeNormal_angles K V hKV).toFinset =
      ((finite_properEdgeNormal_angles K V hKV).inter_of_left Set.univ).toFinset from by
    ext u
    simp]
  refine Eq.trans (Finset.sum_congr rfl fun u _ ↦ ?_) h.symm
  rw [surfaceAreaMeasure_real_singleton]

/-- The proper-edge lengths of a polygon weight its normal directions to zero. -/
theorem sum_edgeLength_mul_inner_normalVector_eq_zero (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) (o : Point) :
    ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
      dist (edgeVertices K t).1 (edgeVertices K t).2 * inner ℝ o (normalVector t) = 0 := by
  have hkey : ∀ t : Real.Angle, inner ℝ o (normalVector t) =
      o 0 * tangentVector t 1 - o 1 * tangentVector t 0 := by
    intro t
    induction t using Real.Angle.induction_on with
    | _ t =>
      simp [PiLp.inner_apply, Fin.sum_univ_two, normalVector, tangentVector, frame,
        Real.Angle.cos_coe, Real.Angle.sin_coe]
      ring
  have h0 := sum_edgeLength_mul_tangentCoordinate_eq_zero K V hKV 0
  have h1 := sum_edgeLength_mul_tangentCoordinate_eq_zero K V hKV 1
  calc ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
        dist (edgeVertices K t).1 (edgeVertices K t).2 * inner ℝ o (normalVector t)
      = o 0 * ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
            dist (edgeVertices K t).1 (edgeVertices K t).2 * tangentVector t 1 -
          o 1 * ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
            dist (edgeVertices K t).1 (edgeVertices K t).2 * tangentVector t 0 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [hkey t]
        ring
    _ = 0 := by rw [h0, h1]; ring

/-- The support-area identity for a polygon with interior, by fan triangulation. -/
theorem convexBody_area_support_integral_of_convexHull_interior
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (hint : (interior (K : Set Point)).Nonempty) :
    ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K := by
  classical
  obtain ⟨o, ho⟩ := hint
  have hmemF : ∀ t : Real.Angle,
      t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset ↔
        (edgeVertices K t).1 ≠ (edgeVertices K t).2 := by
    intro t
    simp
  have hpos : ∀ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
      0 < dist (edgeVertices K t).1 (edgeVertices K t).2 *
        (supportValue K t - inner ℝ o (normalVector t)) := by
    intro t htF
    exact mul_pos (dist_pos.mpr ((hmemF t).1 htF))
      (sub_pos.mpr (inner_lt_supportValue_of_mem_interior K ho t))
  have hTvol : ∀ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
      volume (edgeTriangle K o t) = ENNReal.ofReal
        (dist (edgeVertices K t).1 (edgeVertices K t).2 *
          (supportValue K t - inner ℝ o (normalVector t)) / 2) := by
    intro t htF
    rw [edgeTriangle, EuclideanSpace.volume_convexHull_triple]
    congr 1
    rw [show ((edgeVertices K t).2 - o) 0 * ((edgeVertices K t).1 - o) 1 -
          ((edgeVertices K t).1 - o) 0 * ((edgeVertices K t).2 - o) 1 =
        planeCrossProduct ((edgeVertices K t).2 - o) ((edgeVertices K t).1 - o) from by
      simp only [planeCrossProduct]
      ring, ← edgeLength_mul_supportValue_sub_eq_planeCrossProduct K o t,
      abs_of_pos (hpos t htF)]
  have hTsubK : ∀ t : Real.Angle, edgeTriangle K o t ⊆ (K : Set Point) := by
    intro t
    rw [edgeTriangle]
    refine convexHull_min ?_ K.convex
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact interior_subset ho
    · exact (edgeVertices_snd_mem K t).1
    · exact (edgeVertices_fst_mem K t).1
  have hvolK : volume (K : Set Point) =
      ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
        volume (edgeTriangle K o t) := by
    have hcover : (K : Set Point) ⊆
        (⋃ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset, edgeTriangle K o t) ∪
          vertexRayUnion o V := by
      intro x hx
      by_cases hxline : x ∈ vertexRayUnion o V
      · exact Or.inr hxline
      obtain ⟨t, htproper, hxt⟩ :=
        exists_mem_edgeTriangle_of_notMem_vertexRayUnion K V hKV ho hx hxline
      exact Or.inl (Set.mem_biUnion ((hmemF t).2 htproper) hxt)
    have hle : volume (K : Set Point) ≤
        volume (⋃ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
          edgeTriangle K o t) := by
      calc volume (K : Set Point)
          ≤ volume ((⋃ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
              edgeTriangle K o t) ∪ vertexRayUnion o V) := measure_mono hcover
        _ ≤ volume (⋃ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
              edgeTriangle K o t) + volume (vertexRayUnion o V) := measure_union_le _ _
        _ = volume (⋃ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
              edgeTriangle K o t) := by rw [volume_vertexRayUnion, add_zero]
    have hge : volume (⋃ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
        edgeTriangle K o t) ≤ volume (K : Set Point) :=
      measure_mono (Set.iUnion₂_subset fun t _ ↦ hTsubK t)
    rw [le_antisymm hle hge]
    refine measure_biUnion_finset₀ ?_ ?_
    · intro s _ t _ hst
      exact volume_edgeTriangle_inter_eq_zero K ho hst
    · intro t _
      exact ((Set.toFinite ({o, (edgeVertices K t).2, (edgeVertices K t).1} :
        Set Point)).isCompact_convexHull ℝ).isClosed.measurableSet.nullMeasurableSet
  have hnonneg : ∀ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
      0 ≤ dist (edgeVertices K t).1 (edgeVertices K t).2 *
        (supportValue K t - inner ℝ o (normalVector t)) / 2 := by
    intro t htF
    linarith [hpos t htF]
  have harea : ClassicalResults.area (K : Set Point) =
      ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
        dist (edgeVertices K t).1 (edgeVertices K t).2 *
          (supportValue K t - inner ℝ o (normalVector t)) / 2 := by
    simp only [ClassicalResults.area]
    rw [hvolK, Finset.sum_congr rfl hTvol, ← ENNReal.ofReal_sum_of_nonneg hnonneg,
      ENNReal.toReal_ofReal (Finset.sum_nonneg hnonneg)]
  have hsplit : ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
        dist (edgeVertices K t).1 (edgeVertices K t).2 *
          (supportValue K t - inner ℝ o (normalVector t)) / 2 =
      (1 / 2 : ℝ) * ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
          dist (edgeVertices K t).1 (edgeVertices K t).2 * supportValue K t -
        (1 / 2 : ℝ) * ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
          dist (edgeVertices K t).1 (edgeVertices K t).2 * inner ℝ o (normalVector t) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    ring
  rw [harea, hsplit, sum_edgeLength_mul_inner_normalVector_eq_zero K V hKV o, mul_zero,
    sub_zero, integral_supportValue_surfaceAreaMeasure_eq_sum_edgeLength K V hKV]

/-- The support-area identity for every finite convex hull. -/
theorem convexBody_area_support_integral_of_convexHull
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) :
    ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K := by
  by_cases hsub : (K : Set Point).Subsingleton
  · exact convexBody_area_support_integral_of_subsingleton K hsub
  by_cases hint : (interior (K : Set Point)).Nonempty
  · exact convexBody_area_support_integral_of_convexHull_interior K V hKV hint
  obtain ⟨d, hd⟩ := exists_segmentPresentation_of_interior_empty K hsub
    (Set.not_nonempty_iff_eq_empty.mp hint)
  exact convexBody_area_support_integral_of_segmentPresentation K d hd

/-! ### Symmetry of the mixed support integral

The mixed integral `∫ h_P dσ_Q` of two finite convex hulls is computed by lifting the circle to
`(0, 2π]` and indexing by the finite set `F` of lifts carrying a proper edge of `P` or of `Q`.
The positive-vertex increment formula turns `h_P` into a partial sum along `F`, so the integral
becomes a lower-triangular double sum `∑_{t ∈ F} ∑_{u ≤ t} α_u β_t sin (t - u)`, whose symmetry
in `(α, β)` is `Finset.sum_filter_le_add_sum_filter_le_swap` together with the vanishing of the
first trigonometric moments of the edge lengths. Polygon approximation transfers the identity to
arbitrary convex bodies. -/

/-- The first tangent coordinate at a real angle lift. -/
private theorem tangentVector_coe_zero (s : ℝ) :
    tangentVector ((s : ℝ) : Real.Angle) 0 = -Real.sin s := by
  simp [tangentVector, frame, Real.Angle.sin_coe]

/-- The second tangent coordinate at a real angle lift. -/
private theorem tangentVector_coe_one (s : ℝ) :
    tangentVector ((s : ℝ) : Real.Angle) 1 = Real.cos s := by
  simp [tangentVector, frame, Real.Angle.cos_coe]

/-- A finite set of angular lifts in `(0, 2π]` covering all proper-edge normals of a polygon.
Excluding `0` makes the lift of each angle unique, so no edge atom is counted twice. -/
private def IsProperEdgeLiftIndex (K : ConvexBody Point)
    (F : Finset (Set.Icc (0 : ℝ) (2 * Real.pi))) : Prop :=
  (∀ u ∈ F, 0 < (u : ℝ)) ∧
    ∀ u : Set.Icc (0 : ℝ) (2 * Real.pi), 0 < (u : ℝ) →
      (edgeVertices K ((u : ℝ) : Real.Angle)).1 ≠
        (edgeVertices K ((u : ℝ) : Real.Angle)).2 → u ∈ F

/-- The surface integral over an initial angular arc is the finite sum of its edge atoms. -/
private theorem integral_surfaceAreaMeasure_image_Ioc_eq_sum_lifts
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (F : Finset (Set.Icc (0 : ℝ) (2 * Real.pi))) (hF : IsProperEdgeLiftIndex K F)
    (φ : Real.Angle → ℝ) (t : Set.Icc (0 : ℝ) (2 * Real.pi)) :
    (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc 0 (t : ℝ),
        φ u ∂surfaceAreaMeasure K) =
      ∑ u ∈ F.filter (fun u ↦ u ≤ t),
        dist (edgeVertices K ((u : ℝ) : Real.Angle)).1
            (edgeVertices K ((u : ℝ) : Real.Angle)).2 * φ ((u : ℝ) : Real.Angle) := by
  classical
  have hturn : 2 * Real.pi ≤ 0 + 2 * Real.pi := le_of_eq (by ring)
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  let a' : Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨0, le_rfl, hpi⟩
  have himg : (fun s : Set.Icc (0 : ℝ) (2 * Real.pi) ↦ ((s : ℝ) : Real.Angle)) ''
      Set.Ioc a' t = (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc 0 (t : ℝ) := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(s : ℝ), ⟨hs.1, hs.2⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs.1.le, hs.2.trans t.property.2⟩, ⟨hs.1, hs.2⟩, rfl⟩
  rw [← himg, integral_surfaceAreaMeasure_image_eq_sum_properEdgeNormal_lifts K V hKV hturn φ
    (Set.Ioc a' t) measurableSet_Ioc (fun u hu ↦ hu.1)]
  have hatom : ∀ u : Set.Icc (0 : ℝ) (2 * Real.pi),
      (surfaceAreaMeasure K).real {((u : ℝ) : Real.Angle)} =
        dist (edgeVertices K ((u : ℝ) : Real.Angle)).1
          (edgeVertices K ((u : ℝ) : Real.Angle)).2 := by
    intro u
    change (surfaceAreaMeasure K {((u : ℝ) : Real.Angle)}).toReal = _
    rw [(surfaceAreaMeasure_atom_length K ((u : ℝ) : Real.Angle)).2.1,
      ENNReal.toReal_ofReal dist_nonneg]
  simp only [hatom]
  refine Finset.sum_subset ?_ ?_
  · intro u hu
    simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff] at hu
    exact Finset.mem_filter.2 ⟨hF.2 u hu.1.1 hu.1.2, hu.2.2⟩
  · intro u hu hnot
    simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, not_and] at hnot
    obtain ⟨huF, hut⟩ := Finset.mem_filter.1 hu
    have hu0 : 0 < (u : ℝ) := hF.1 u huF
    have hdeg : ¬((edgeVertices K ((u : ℝ) : Real.Angle)).1 ≠
        (edgeVertices K ((u : ℝ) : Real.Angle)).2) := fun hne ↦
      (hnot ⟨hu0, hne⟩) ⟨hu0, hut⟩
    rw [not_not.mp hdeg, dist_self, zero_mul]

/-- The total surface integral is the finite sum of the edge atoms of a polygon. -/
private theorem integral_surfaceAreaMeasure_eq_sum_lifts
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (F : Finset (Set.Icc (0 : ℝ) (2 * Real.pi))) (hF : IsProperEdgeLiftIndex K F)
    (φ : Real.Angle → ℝ) :
    (∫ u, φ u ∂surfaceAreaMeasure K) =
      ∑ u ∈ F,
        dist (edgeVertices K ((u : ℝ) : Real.Angle)).1
            (edgeVertices K ((u : ℝ) : Real.Angle)).2 * φ ((u : ℝ) : Real.Angle) := by
  classical
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  let b' : Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨2 * Real.pi, hpi, le_rfl⟩
  have hfull : (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc 0 ((b' : ℝ)) = Set.univ := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioc, Set.mem_univ, iff_true]
    let _ : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
    refine ⟨(AddCircle.equivIoc (2 * Real.pi) 0 u : ℝ), ?_, AddCircle.coe_equivIoc⟩
    simpa using (AddCircle.equivIoc (2 * Real.pi) 0 u).property
  have hfilter : F.filter (fun u ↦ u ≤ b') = F := by
    refine Finset.filter_true_of_mem fun u _ ↦ ?_
    exact u.property.2
  have := integral_surfaceAreaMeasure_image_Ioc_eq_sum_lifts K V hKV F hF φ b'
  rw [hfull, setIntegral_univ, hfilter] at this
  exact this

/-- The edge lengths of a polygon weight the cosines and sines of its normal directions to
zero. -/
private theorem sum_edgeLength_lift_cos_sin_eq_zero
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (F : Finset (Set.Icc (0 : ℝ) (2 * Real.pi))) (hF : IsProperEdgeLiftIndex K F) :
    (∑ u ∈ F, dist (edgeVertices K ((u : ℝ) : Real.Angle)).1
            (edgeVertices K ((u : ℝ) : Real.Angle)).2 * Real.cos (u : ℝ) = 0) ∧
      ∑ u ∈ F, dist (edgeVertices K ((u : ℝ) : Real.Angle)).1
            (edgeVertices K ((u : ℝ) : Real.Angle)).2 * Real.sin (u : ℝ) = 0 := by
  have hzero : ∀ i : Fin 2, ∑ u ∈ F,
      dist (edgeVertices K ((u : ℝ) : Real.Angle)).1
          (edgeVertices K ((u : ℝ) : Real.Angle)).2 *
        tangentVector ((u : ℝ) : Real.Angle) i = 0 := by
    intro i
    rw [← integral_surfaceAreaMeasure_eq_sum_lifts K V hKV F hF (fun v ↦ tangentVector v i)]
    exact integral_tangentCoordinate_surfaceAreaMeasure_eq_zero K i
  refine ⟨by simpa only [tangentVector_coe_one] using hzero 1, ?_⟩
  have h := hzero 0
  simp only [tangentVector_coe_zero, mul_neg, Finset.sum_neg_distrib] at h
  linarith

/-- The mixed support integral of two polygons, as a lower-triangular double sum over a common
index set of angular lifts. -/
private theorem integral_supportValue_eq_sum_sum_lifts
    (P Q : ConvexBody Point) (VP VQ : Finset Point)
    (hP : (P : Set Point) = convexHull ℝ (VP : Set Point))
    (hQ : (Q : Set Point) = convexHull ℝ (VQ : Set Point))
    (F : Finset (Set.Icc (0 : ℝ) (2 * Real.pi)))
    (hidxP : IsProperEdgeLiftIndex P F) (hidxQ : IsProperEdgeLiftIndex Q F) :
    (∫ t, supportValue P t ∂surfaceAreaMeasure Q) =
      ∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t),
        dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
              (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
            dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
              (edgeVertices Q ((t : ℝ) : Real.Angle)).2 *
          Real.sin ((t : ℝ) - (u : ℝ)) := by
  classical
  have hcosQ : ∑ u ∈ F, dist (edgeVertices Q ((u : ℝ) : Real.Angle)).1
      (edgeVertices Q ((u : ℝ) : Real.Angle)).2 * Real.cos (u : ℝ) = 0 :=
    (sum_edgeLength_lift_cos_sin_eq_zero Q VQ hQ F hidxQ).1
  have hsinQ : ∑ u ∈ F, dist (edgeVertices Q ((u : ℝ) : Real.Angle)).1
      (edgeVertices Q ((u : ℝ) : Real.Angle)).2 * Real.sin (u : ℝ) = 0 :=
    (sum_edgeLength_lift_cos_sin_eq_zero Q VQ hQ F hidxQ).2
  have hincP : ∀ (i : Fin 2) (t : Set.Icc (0 : ℝ) (2 * Real.pi)), 0 < (t : ℝ) →
      (edgeVertices P ((t : ℝ) : Real.Angle)).1 i =
        (edgeVertices P ((0 : ℝ) : Real.Angle)).1 i +
          ∑ u ∈ F.filter (fun u ↦ u ≤ t),
            dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
              tangentVector ((u : ℝ) : Real.Angle) i := by
    intro i t ht
    have h1 := positiveVertex_sub_eq_integral_of_eq_convexHull P VP hP (a := 0)
      (b := (t : ℝ)) ht (by simpa using t.property.2) i
    rw [integral_surfaceAreaMeasure_image_Ioc_eq_sum_lifts P VP hP F hidxP
      (fun v ↦ tangentVector v i) t] at h1
    linarith
  have hsupp : ∀ t : Set.Icc (0 : ℝ) (2 * Real.pi), 0 < (t : ℝ) →
      supportValue P ((t : ℝ) : Real.Angle) =
        (edgeVertices P ((0 : ℝ) : Real.Angle)).1 0 * Real.cos (t : ℝ) +
            (edgeVertices P ((0 : ℝ) : Real.Angle)).1 1 * Real.sin (t : ℝ) +
          ∑ u ∈ F.filter (fun u ↦ u ≤ t),
            dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
              Real.sin ((t : ℝ) - (u : ℝ)) := by
    intro t ht
    rw [← (edgeVertices_fst_mem P ((t : ℝ) : Real.Angle)).2, inner_normalVector_real,
      hincP 0 t ht, hincP 1 t ht]
    have hsplit :
        (∑ u ∈ F.filter (fun u ↦ u ≤ t),
              dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                  (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
                tangentVector ((u : ℝ) : Real.Angle) 0) * Real.cos (t : ℝ) +
            (∑ u ∈ F.filter (fun u ↦ u ≤ t),
              dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                  (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
                tangentVector ((u : ℝ) : Real.Angle) 1) * Real.sin (t : ℝ) =
          ∑ u ∈ F.filter (fun u ↦ u ≤ t),
            dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
              Real.sin ((t : ℝ) - (u : ℝ)) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [tangentVector_coe_zero, tangentVector_coe_one, Real.sin_sub]
      ring
    linarith
  rw [integral_surfaceAreaMeasure_eq_sum_lifts Q VQ hQ F hidxQ (fun v ↦ supportValue P v)]
  have step1 : ∑ t ∈ F, dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
          (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * supportValue P ((t : ℝ) : Real.Angle) =
      ∑ t ∈ F, ((edgeVertices P ((0 : ℝ) : Real.Angle)).1 0 *
            (dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
              (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * Real.cos (t : ℝ)) +
          (edgeVertices P ((0 : ℝ) : Real.Angle)).1 1 *
            (dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
              (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * Real.sin (t : ℝ)) +
          ∑ u ∈ F.filter (fun u ↦ u ≤ t),
            dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                  (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
                dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
                  (edgeVertices Q ((t : ℝ) : Real.Angle)).2 *
              Real.sin ((t : ℝ) - (u : ℝ))) := by
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have hms : dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
          (edgeVertices Q ((t : ℝ) : Real.Angle)).2 *
        (∑ u ∈ F.filter (fun u ↦ u ≤ t), dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
          (edgeVertices P ((u : ℝ) : Real.Angle)).2 * Real.sin ((t : ℝ) - (u : ℝ))) =
          ∑ u ∈ F.filter (fun u ↦ u ≤ t),
            dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                  (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
                dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
                  (edgeVertices Q ((t : ℝ) : Real.Angle)).2 *
              Real.sin ((t : ℝ) - (u : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ ↦ by ring
    rw [hsupp t (hidxQ.1 t ht)]
    linear_combination hms
  have step2 : ∑ t ∈ F, ((edgeVertices P ((0 : ℝ) : Real.Angle)).1 0 *
          (dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
            (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * Real.cos (t : ℝ)) +
        (edgeVertices P ((0 : ℝ) : Real.Angle)).1 1 *
          (dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
            (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * Real.sin (t : ℝ)) +
        ∑ u ∈ F.filter (fun u ↦ u ≤ t),
          dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
              dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
                (edgeVertices Q ((t : ℝ) : Real.Angle)).2 *
            Real.sin ((t : ℝ) - (u : ℝ))) =
      (edgeVertices P ((0 : ℝ) : Real.Angle)).1 0 *
          (∑ t ∈ F, dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
            (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * Real.cos (t : ℝ)) +
        (edgeVertices P ((0 : ℝ) : Real.Angle)).1 1 *
          (∑ t ∈ F, dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
            (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * Real.sin (t : ℝ)) +
        ∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t),
          dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
              dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
                (edgeVertices Q ((t : ℝ) : Real.Angle)).2 *
            Real.sin ((t : ℝ) - (u : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [step1, step2, hcosQ, hsinQ]
  ring

/-- The lower-triangular sine double sum is symmetric under swapping the two weight families,
provided the second family has vanishing first trigonometric moments. -/
private theorem sum_filter_le_sin_sub_comm
    {ι : Type*} [LinearOrder ι] (F : Finset ι) (θ : ι → ℝ) (α β : ι → ℝ)
    (hβ0 : ∑ u ∈ F, β u * Real.cos (θ u) = 0)
    (hβ1 : ∑ u ∈ F, β u * Real.sin (θ u) = 0) :
    (∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t), α u * β t * Real.sin (θ t - θ u)) =
      ∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t), β u * α t * Real.sin (θ t - θ u) := by
  set f : ι → ι → ℝ := fun x y ↦ α x * β y * Real.sin (θ y - θ x) with hf
  have hdiag : ∀ x, f x x = 0 := by
    intro x
    simp [hf]
  have hfull : (∑ x ∈ F, ∑ y ∈ F, f x y) = 0 := by
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    have hinner : (∑ y ∈ F, f x y) =
        (α x * Real.cos (θ x)) * (∑ y ∈ F, β y * Real.sin (θ y)) -
          (α x * Real.sin (θ x)) * (∑ y ∈ F, β y * Real.cos (θ y)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      simp only [hf, Real.sin_sub]
      ring
    rw [hinner, hβ0, hβ1]
    ring
  have htrans : (∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t), f u t) +
      ∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t), f t u = 0 := by
    rw [Finset.sum_filter_le_add_sum_filter_le_swap F f hdiag, hfull]
  have hright : (∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t), β u * α t * Real.sin (θ t - θ u)) =
      -∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t), f t u := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    simp only [hf]
    rw [show θ u - θ t = -(θ t - θ u) by ring, Real.sin_neg]
    ring
  rw [hright]
  linarith [htrans]

/-- Symmetry of the mixed support integral for finite convex hulls, including the degenerate
point and segment cases. -/
theorem supportIntegral_symm_of_convexHull (P Q : ConvexBody Point) (VP VQ : Finset Point)
    (hP : (P : Set Point) = convexHull ℝ (VP : Set Point))
    (hQ : (Q : Set Point) = convexHull ℝ (VQ : Set Point)) :
    (∫ t, supportValue P t ∂surfaceAreaMeasure Q) =
      ∫ t, supportValue Q t ∂surfaceAreaMeasure P := by
  classical
  have hturn : 2 * Real.pi ≤ 0 + 2 * Real.pi := le_of_eq (by ring)
  have hSP := finite_properEdgeNormal_lifts P VP hP (a := 0) (b := 2 * Real.pi) hturn
  have hSQ := finite_properEdgeNormal_lifts Q VQ hQ (a := 0) (b := 2 * Real.pi) hturn
  set F : Finset (Set.Icc (0 : ℝ) (2 * Real.pi)) := hSP.toFinset ∪ hSQ.toFinset with hFdef
  have hidxP : IsProperEdgeLiftIndex P F := by
    refine ⟨fun u hu ↦ ?_, fun u h0 hne ↦ ?_⟩
    · rcases Finset.mem_union.mp hu with h | h
      · exact (hSP.mem_toFinset.mp h).1
      · exact (hSQ.mem_toFinset.mp h).1
    · exact Finset.mem_union_left _ (hSP.mem_toFinset.mpr ⟨h0, hne⟩)
  have hidxQ : IsProperEdgeLiftIndex Q F := by
    refine ⟨fun u hu ↦ ?_, fun u h0 hne ↦ ?_⟩
    · rcases Finset.mem_union.mp hu with h | h
      · exact (hSP.mem_toFinset.mp h).1
      · exact (hSQ.mem_toFinset.mp h).1
    · exact Finset.mem_union_right _ (hSQ.mem_toFinset.mpr ⟨h0, hne⟩)
  rw [integral_supportValue_eq_sum_sum_lifts P Q VP VQ hP hQ F hidxP hidxQ,
    integral_supportValue_eq_sum_sum_lifts Q P VQ VP hQ hP F hidxQ hidxP]
  exact sum_filter_le_sin_sub_comm F (fun u ↦ (u : ℝ))
    (fun u ↦ dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
      (edgeVertices P ((u : ℝ) : Real.Angle)).2)
    (fun u ↦ dist (edgeVertices Q ((u : ℝ) : Real.Angle)).1
      (edgeVertices Q ((u : ℝ) : Real.Angle)).2)
    (sum_edgeLength_lift_cos_sin_eq_zero Q VQ hQ F hidxQ).1
    (sum_edgeLength_lift_cos_sin_eq_zero Q VQ hQ F hidxQ).2

/-- Symmetry of the mixed support integral for arbitrary planar convex bodies:
`∫ h_K dσ_L = ∫ h_L dσ_K`. -/
theorem supportIntegral_symm (K L : ConvexBody Point) :
    (∫ t, supportValue K t ∂surfaceAreaMeasure L) =
      ∫ t, supportValue L t ∂surfaceAreaMeasure K := by
  obtain ⟨VP, P, hPspec, hPdist⟩ := exists_facePreserving_polygonApproximation K ∅
  obtain ⟨VQ, Q, hQspec, hQdist⟩ := exists_facePreserving_polygonApproximation L ∅
  have hlimP : Tendsto (fun n ↦ Metric.hausdorffDist (P n : Set Point) (K : Set Point))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ Metric.hausdorffDist_nonneg)
      (Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hPdist n hn⟩)
    exact tendsto_one_div_atTop_nhds_zero_nat
  have hlimQ : Tendsto (fun n ↦ Metric.hausdorffDist (Q n : Set Point) (L : Set Point))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ Metric.hausdorffDist_nonneg)
      (Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hQdist n hn⟩)
    exact tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_nhds_unique
    (tendsto_integral_supportValue_of_hausdorff_pair P Q K L hlimP hlimQ)
    (Filter.Tendsto.congr (fun n ↦ ?_)
      (tendsto_integral_supportValue_of_hausdorff_pair Q P L K hlimQ hlimP))
  exact supportIntegral_symm_of_convexHull (Q n) (P n) (VQ n) (VP n)
    (hQspec n).2.1 (hPspec n).2.1

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
# Convex / Linearity
-/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

theorem convexBody_maps_linear (t : I) (K L : ConvexBody Point) :
    (∀ a : Real.Angle,
      supportValue (convexBodyCombination t K L) a =
        (1 - (t : ℝ)) * supportValue K a + (t : ℝ) * supportValue L a) ∧
    (∀ a : Real.Angle,
      (edgeVertices (convexBodyCombination t K L) a).1 =
        (1 - (t : ℝ)) • (edgeVertices K a).1 + (t : ℝ) • (edgeVertices L a).1 ∧
      (edgeVertices (convexBodyCombination t K L) a).2 =
        (1 - (t : ℝ)) • (edgeVertices K a).2 + (t : ℝ) • (edgeVertices L a).2) ∧
    (∀ a b : ℝ, a < b → b < a + Real.pi →
      supportingIntersection (convexBodyCombination t K L) a b =
        (1 - (t : ℝ)) • supportingIntersection K a b +
          (t : ℝ) • supportingIntersection L a b) ∧
    surfaceAreaMeasure (convexBodyCombination t K L) =
      ENNReal.ofReal (1 - (t : ℝ)) • surfaceAreaMeasure K +
        ENNReal.ofReal (t : ℝ) • surfaceAreaMeasure L := by
  refine ⟨supportValue_convexBodyCombination t K L, ?_, ?_,
    surfaceAreaMeasure_convexBodyCombination t K L⟩
  · exact edgeVertices_convexBodyCombination t K L
  · intro a b _hab _hba
    simp only [supportingIntersection, supportValue_convexBodyCombination]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring

theorem convexBody_area_support_integral :
    (∀ K : ConvexBody Point, ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ a : Real.Angle, supportValue K a ∂surfaceAreaMeasure K) ∧
    IsConvexBilinear convexBodyCombination convexBodyCombination realCombination
      (fun K L : ConvexBody Point ↦
        (1 / 2 : ℝ) * ∫ a : Real.Angle, supportValue K a ∂surfaceAreaMeasure L) ∧
    IsQuadraticFunctional convexBodyCombination
      (fun K : ConvexBody Point ↦ ClassicalResults.area (K : Set Point)) :=
  convexBody_area_support_integral_of_area_identity
    (convexBody_area_support_integral_of_finiteHull
      (fun P W _hW hPW ↦ convexBody_area_support_integral_of_convexHull P W hPW))

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
# The mixed area of two planar convex bodies

The mixed support integral `∫ h_K dσ_L` is symmetric in the two bodies, and the area of the
Minkowski segment `λ ↦ |(1 - λ) K + λ L|` is therefore the quadratic
`(1 - λ)² |K| + λ (1 - λ) ∫ h_L dσ_K + λ² |L|`, whose right derivative at `λ = 0` is
`∫ (h_L - h_K) dσ_K`.

The symmetry itself is `MovingSofa.supportIntegral_symm` in `MovingSofa.Convex.SupportArea`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Symmetry of the mixed support integral, together with the right derivative at `0` of the
area along the Minkowski segment from `K` to `L`. -/
theorem supportMeasure_mixedArea_symmetry (K L : ConvexBody Point) :
    (∫ t : Real.Angle, supportValue K t ∂surfaceAreaMeasure L) =
      (∫ t : Real.Angle, supportValue L t ∂surfaceAreaMeasure K) ∧
    HasDerivWithinAt
      (segmentFunctional convexBodyCombination
        (fun M : ConvexBody Point ↦ ClassicalResults.area (M : Set Point)) K L)
      (∫ t : Real.Angle, supportValue L t - supportValue K t ∂surfaceAreaMeasure K)
      (Set.Icc (0 : ℝ) 1) 0 := by
  classical
  have hsymm := supportIntegral_symm K L
  refine ⟨hsymm, ?_⟩
  obtain ⟨harea, hbil, -⟩ := convexBody_area_support_integral
  have hcont (M : ConvexBody Point) : Continuous (supportValue M) :=
    (compactSet_support_continuity M M M.nonempty M.isCompact M.nonempty M.isCompact).2.2.1
  have hint : ∀ M N : ConvexBody Point, Integrable (supportValue M) (surfaceAreaMeasure N) := by
    intro M N
    let _ : IsFiniteMeasure (surfaceAreaMeasure N) := (surfaceAreaMeasure_face_union N).1
    exact (hcont M).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  rw [integral_sub (hint L K) (hint K K)]
  have hfun : ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      segmentFunctional convexBodyCombination
          (fun M : ConvexBody Point ↦ ClassicalResults.area (M : Set Point)) K L lam =
        1 / 2 * (∫ t, supportValue K t ∂surfaceAreaMeasure K) +
          ((∫ t, supportValue L t ∂surfaceAreaMeasure K) -
            ∫ t, supportValue K t ∂surfaceAreaMeasure K) * lam +
          (1 / 2 * (∫ t, supportValue K t ∂surfaceAreaMeasure K) -
            (∫ t, supportValue L t ∂surfaceAreaMeasure K) +
            1 / 2 * ∫ t, supportValue L t ∂surfaceAreaMeasure L) * lam ^ 2 := by
    intro lam hlam
    have hseg : segmentFunctional convexBodyCombination
        (fun M : ConvexBody Point ↦ ClassicalResults.area (M : Set Point)) K L lam =
        ClassicalResults.area
          ((convexBodyCombination ⟨lam, hlam⟩ K L : ConvexBody Point) : Set Point) :=
      dite_eq_left hlam
    have h2 := hbil.2 (convexBodyCombination ⟨lam, hlam⟩ K L) ⟨lam, hlam⟩ K L
    have h3 := hbil.1 K ⟨lam, hlam⟩ K L
    have h4 := hbil.1 L ⟨lam, hlam⟩ K L
    simp only [realCombination] at h2 h3 h4
    rw [hseg, harea (convexBodyCombination ⟨lam, hlam⟩ K L), h2, h3, h4, hsymm]
    ring
  have hpoly : ∀ A B C : ℝ, HasDerivAt (fun lam : ℝ ↦ A + B * lam + C * lam ^ 2) B 0 := by
    intro A B C
    have h : HasDerivAt (fun lam : ℝ ↦ A + B * lam + C * lam ^ 2)
        (0 + B * 1 + C * (2 * 0 ^ 1)) 0 :=
      HasDerivAt.add (HasDerivAt.add (hasDerivAt_const _ _)
        ((hasDerivAt_id _).const_mul _)) ((hasDerivAt_pow _ _).const_mul _)
    simpa using h
  exact HasDerivWithinAt.congr (hpoly _ _ _).hasDerivWithinAt hfun
    (hfun 0 ⟨le_rfl, zero_le_one⟩)

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
# Convex / Tangent Line Path
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace MovingSofa

/-- Trace intersections with a fixed supporting line, ending at its exposed-edge endpoint. -/
def tangentLinePath (K : ConvexBody Point) (t : ℝ) (s : Set.Ioc (t - Real.pi) t) : Point :=
  if s.val < t then supportingIntersection K (s.val : Real.Angle) (t : Real.Angle)
  else (edgeVertices K (t : Real.Angle)).2

/-- Restrict the tangent-line path to a closed interval of supporting directions. -/
def tangentLineRestriction (K : ConvexBody Point) (t a b : ℝ)
    (ha : a ∈ Set.Ioc (t - Real.pi) t) (hb : b ∈ Set.Ioc (t - Real.pi) t)
    (s : Set.Icc a b) : Point :=
  tangentLinePath K t ⟨s.val, lt_of_lt_of_le ha.1 s.property.1,
    le_trans s.property.2 hb.2⟩

private def tangentLineCoordinate (K : ConvexBody Point) (t s : ℝ) : ℝ :=
  (supportValue K (s : Real.Angle) - supportValue K (t : Real.Angle) * Real.cos (s - t)) /
    Real.sin (s - t)

private theorem tangentLineCoordinate_le (K : ConvexBody Point) {t s : ℝ}
    (hs : s ∈ Ioo (t - Real.pi) t) {p : Point} (hp : p ∈ K) :
    tangentLineCoordinate K t s ≤ inner ℝ p (tangentVector (t : Real.Angle)) +
      (inner ℝ p (normalVector (t : Real.Angle)) - supportValue K (t : Real.Angle)) *
        (Real.cos (s - t) / Real.sin (s - t)) := by
  have hsin : Real.sin (s - t) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hs.2]) (by linarith [hs.1])
  have hbound := inner_le_supportValue K hp (s : Real.Angle)
  have hn : normalVector (s : Real.Angle) =
      Real.cos (s - t) • normalVector (t : Real.Angle) +
        Real.sin (s - t) • tangentVector (t : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real t (s - t)
  rw [hn, inner_add_right, inner_smul_right, inner_smul_right] at hbound
  dsimp [tangentLineCoordinate]
  apply (div_le_iff_of_neg hsin).mpr
  have hc : (inner ℝ p (tangentVector (t : Real.Angle)) +
      (inner ℝ p (normalVector (t : Real.Angle)) - supportValue K (t : Real.Angle)) *
        (Real.cos (s - t) / Real.sin (s - t))) * Real.sin (s - t) =
      inner ℝ p (tangentVector (t : Real.Angle)) * Real.sin (s - t) +
      (inner ℝ p (normalVector (t : Real.Angle)) - supportValue K (t : Real.Angle)) *
        Real.cos (s - t) := by
    field_simp [hsin.ne]
  rw [hc]
  nlinarith

private theorem tangentLineCoordinate_eq_of_mem_support (K : ConvexBody Point) {t s : ℝ}
    (hs : s ∈ Ioo (t - Real.pi) t) {p : Point}
    (hp : inner ℝ p (normalVector (s : Real.Angle)) = supportValue K (s : Real.Angle)) :
    tangentLineCoordinate K t s = inner ℝ p (tangentVector (t : Real.Angle)) +
      (inner ℝ p (normalVector (t : Real.Angle)) - supportValue K (t : Real.Angle)) *
        (Real.cos (s - t) / Real.sin (s - t)) := by
  have hsin : Real.sin (s - t) ≠ 0 :=
    (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hs.2]) (by linarith [hs.1])).ne
  have hn : normalVector (s : Real.Angle) =
      Real.cos (s - t) • normalVector (t : Real.Angle) +
        Real.sin (s - t) • tangentVector (t : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real t (s - t)
  dsimp [tangentLineCoordinate]
  rw [← hp, hn, inner_add_right, inner_smul_right, inner_smul_right]
  field_simp
  ring

private theorem monotoneOn_tangentLineCoordinate (K : ConvexBody Point) (t : ℝ) :
    MonotoneOn (tangentLineCoordinate K t) (Ioo (t - Real.pi) t) := by
  intro x hx y hy hxy
  obtain ⟨p, hp, hmax⟩ := exists_mem_inner_eq_supportValue K (y : Real.Angle)
  rw [tangentLineCoordinate_eq_of_mem_support K hy hmax]
  apply (tangentLineCoordinate_le K hx hp).trans
  apply add_le_add_right
  exact mul_le_mul_of_nonpos_left
    (Real.antitoneOn_cos_div_sin_Ioo_neg_pi_zero ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith))
    (sub_nonpos.mpr (inner_le_supportValue K hp (t : Real.Angle)))

private theorem supportingIntersection_eq_tangentLineCoordinate (K : ConvexBody Point)
    {t s : ℝ} (hs : s ∈ Ioo (t - Real.pi) t) :
    supportingIntersection K (s : Real.Angle) (t : Real.Angle) =
      supportValue K (t : Real.Angle) • normalVector (t : Real.Angle) +
        tangentLineCoordinate K t s • tangentVector (t : Real.Angle) := by
  rw [supportingIntersection_comm K s t
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.2]) (by linarith [hs.1])).ne']
  simp only [supportingIntersection, tangentLineCoordinate, ← Real.Angle.coe_sub,
    Real.Angle.cos_coe, Real.Angle.sin_coe]

private theorem continuousAt_tangentLineCoordinate (K : ConvexBody Point) {t s : ℝ}
    (hs : s ∈ Ioo (t - Real.pi) t) : ContinuousAt (tangentLineCoordinate K t) s := by
  have hsin : Real.sin (s - t) ≠ 0 :=
    (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hs.2]) (by linarith [hs.1])).ne
  exact ((continuous_supportValue_real K).continuousAt.sub
    (continuousAt_const.mul (Real.continuous_cos.continuousAt.comp
      (continuousAt_id.sub continuousAt_const)))).div
    (Real.continuous_sin.continuousAt.comp (continuousAt_id.sub continuousAt_const)) hsin

private theorem tendsto_tangentLineCoordinate_left (K : ConvexBody Point) (t : ℝ) :
    Tendsto (tangentLineCoordinate K t) (𝓝[<] t)
      (𝓝 (inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)))) := by
  have h := (contact_oneSided_limits K t).2.2.2.2.2.inner
    (𝕜 := ℝ) (tendsto_const_nhds (x := tangentVector (t : Real.Angle)))
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : t - Real.pi < t)] with s hs
  rw [supportingIntersection_eq_tangentLineCoordinate K hs]
  simp only [inner_add_left, real_inner_smul_left, inner_normalVector_tangentVector,
    inner_tangentVector_self, mul_zero, mul_one, zero_add]

private def closedTangentLineCoordinate (K : ConvexBody Point) (t s : ℝ) : ℝ :=
  if s = t then inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle))
  else tangentLineCoordinate K t s

private theorem continuousOn_closedTangentLineCoordinate (K : ConvexBody Point) {t a : ℝ}
    (ha : a ∈ Ioo (t - Real.pi) t) :
    ContinuousOn (closedTangentLineCoordinate K t) (Icc a t) := by
  exact continuousOn_replace_right_endpoint ha.2 _ _
    (fun s hs ↦
      (continuousAt_tangentLineCoordinate K ⟨ha.1.trans_le hs.1, hs.2⟩).tendsto.mono_left
      nhdsWithin_le_nhds)
    (fun s hs ↦
      (continuousAt_tangentLineCoordinate K ⟨ha.1.trans hs.1, hs.2⟩).tendsto.mono_left
      nhdsWithin_le_nhds)
    (tendsto_tangentLineCoordinate_left K t)

private theorem monotoneOn_closedTangentLineCoordinate (K : ConvexBody Point) (t : ℝ) :
    MonotoneOn (closedTangentLineCoordinate K t) (Ioc (t - Real.pi) t) := by
  intro x hx y hy hxy
  by_cases hyEq : y = t
  · subst y
    by_cases hxEq : x = t
    · subst x
      rfl
    · have hxt : x < t := lt_of_le_of_ne hx.2 hxEq
      change (if x = t then _ else _) ≤ (if t = t then _ else _)
      simp only [ite_eq_right hxEq, ite_true]
      apply ge_of_tendsto (tendsto_tangentLineCoordinate_left K t)
      filter_upwards [Ioo_mem_nhdsLT hxt] with u hu
      exact monotoneOn_tangentLineCoordinate K t ⟨hx.1, hxt⟩
        ⟨hx.1.trans hu.1, hu.2⟩ hu.1.le
  · have hyt : y < t := lt_of_le_of_ne hy.2 hyEq
    have hxt : x < t := hxy.trans_lt hyt
    simp only [closedTangentLineCoordinate, ite_eq_right hxt.ne, ite_eq_right hyEq]
    exact monotoneOn_tangentLineCoordinate K t ⟨hx.1, hxt⟩ ⟨hy.1, hyt⟩ hxy

private theorem tangentLinePath_eq_coordinate (K : ConvexBody Point) (t : ℝ)
    (s : Ioc (t - Real.pi) t) :
    tangentLinePath K t s = supportValue K (t : Real.Angle) • normalVector (t : Real.Angle) +
      closedTangentLineCoordinate K t s • tangentVector (t : Real.Angle) := by
  dsimp [tangentLinePath]
  split_ifs with hs
  · rw [supportingIntersection_eq_tangentLineCoordinate K ⟨s.property.1, hs⟩]
    simp only [closedTangentLineCoordinate, ite_eq_right hs.ne]
  · have heq : (s : ℝ) = t := le_antisymm s.property.2 (le_of_not_gt hs)
    simp only [closedTangentLineCoordinate, heq]
    have hp := (edgeVertices_snd_mem K (t : Real.Angle)).2
    change inner ℝ (edgeVertices K (t : Real.Angle)).2 (normalVector (t : Real.Angle)) =
      supportValue K (t : Real.Angle) at hp
    rw [← hp]
    exact (inner_normalVector_smul_add_inner_tangentVector_smul _ _).symm

/-- Every value of a tangent-line path lies on the supporting line at its own path parameter. -/
theorem tangentLinePath_mem_supportingLine (K : ConvexBody Point) (t : ℝ)
    (s : Set.Ioc (t - Real.pi) t) :
    tangentLinePath K t s ∈
      (supportingLineHalfPlane (K : Set Point) ((s : ℝ) : Real.Angle)).1 := by
  unfold tangentLinePath
  split_ifs with hs
  · exact supportingIntersection_inner_left K (s : ℝ) t
  · have hst : (s : ℝ) = t := le_antisymm s.property.2 (le_of_not_gt hs)
    rw [hst]
    exact (edgeVertices_snd_mem K (t : Real.Angle)).2

theorem tangentLinePath_segment_area (K : ConvexBody Point) (t a b : ℝ)
    (ha : a ∈ Set.Ioc (t - Real.pi) t) (hb : b ∈ Set.Ioc (t - Real.pi) t)
    (hab : a ≤ b) :
    ∃ γ : ContinuousBVPaths a b,
      γ.val = tangentLineRestriction K t a b ha hb ∧
      Set.range γ.val = segment ℝ (tangentLinePath K t ⟨a, ha⟩)
        (tangentLinePath K t ⟨b, hb⟩) ∧
      Set.range γ.val ⊆ (supportingLineHalfPlane (K : Set Point) (t : Real.Angle)).1 ∧
      curveAreaFunctional γ =
        segmentArea (tangentLinePath K t ⟨a, ha⟩) (tangentLinePath K t ⟨b, hb⟩) := by
  let Q : Set.Icc a b → ℝ := fun s ↦ closedTangentLineCoordinate K t s
  have hQmono : Monotone Q := by
    intro x y hxy
    exact monotoneOn_closedTangentLineCoordinate K t
      ⟨ha.1.trans_le x.property.1, x.property.2.trans hb.2⟩
      ⟨ha.1.trans_le y.property.1, y.property.2.trans hb.2⟩ hxy
  have hQcont : Continuous Q := by
    change Continuous (Set.domRestrict (Set.Icc a b) (closedTangentLineCoordinate K t))
    by_cases hat : a < t
    · exact continuousOn_iff_continuous_domRestrict.mp
        ((continuousOn_closedTangentLineCoordinate K ⟨ha.1, hat⟩).mono
          (Icc_subset_Icc_right hb.2))
    · have heq : a = b := le_antisymm hab (hb.2.trans (le_of_not_gt hat))
      have hc : ContinuousOn (closedTangentLineCoordinate K t) ({a} : Set ℝ) :=
        (show ({a} : Set ℝ).Subsingleton from Set.subsingleton_singleton).continuousOn _
      exact continuousOn_iff_continuous_domRestrict.mp (hc.mono (by simp [heq]))
  have hQbv : BoundedVariationOn Q Set.univ := by
    apply MonotoneOn.boundedVariationOn (f := Q) (s := Set.univ)
      (fun _ _ _ _ hxy ↦ hQmono hxy)
      (C := |Q ⟨a, le_rfl, hab⟩| + |Q ⟨b, hab, le_rfl⟩|)
    intro s _
    have hlo := hQmono (show (⟨a, le_rfl, hab⟩ : Set.Icc a b) ≤ s from s.property.1)
    have hhi := hQmono (show s ≤ (⟨b, hab, le_rfl⟩ : Set.Icc a b) from s.property.2)
    exact abs_le.mpr ⟨by
      linarith [neg_abs_le (Q ⟨a, le_rfl, hab⟩), abs_nonneg (Q ⟨b, hab, le_rfl⟩)], by
      linarith [le_abs_self (Q ⟨b, hab, le_rfl⟩), abs_nonneg (Q ⟨a, le_rfl, hab⟩)]⟩
  let h := supportValue K (t : Real.Angle)
  let γ : ContinuousBVPaths a b := {
    val := fun s ↦ h • normalVector (t : Real.Angle) + Q s • tangentVector (t : Real.Angle)
    property := ⟨continuous_const.add (hQcont.smul continuous_const), fun i ↦ by
      let C : NNReal := ⟨|tangentVector (t : Real.Angle) i|, abs_nonneg _⟩
      have hLip : LipschitzWith C (fun r : ℝ ↦
          h * normalVector (t : Real.Angle) i + r * tangentVector (t : Real.Angle) i) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        simp only [Real.dist_eq]
        rw [show (h * normalVector (t : Real.Angle) i + x * tangentVector (t : Real.Angle) i) -
          (h * normalVector (t : Real.Angle) i + y * tangentVector (t : Real.Angle) i) =
            (x - y) * tangentVector (t : Real.Angle) i by ring, abs_mul, mul_comm]
        rfl
      have hcomp := hLip.comp_boundedVariationOn hQbv
      change BoundedVariationOn (fun t_1 ↦
        h * normalVector (t : Real.Angle) i + Q t_1 * tangentVector (t : Real.Angle) i) Set.univ
      exact hcomp⟩ }
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · funext s
    unfold tangentLineRestriction
    exact (tangentLinePath_eq_coordinate K t
      ⟨s, lt_of_lt_of_le ha.1 s.property.1, s.property.2.trans hb.2⟩).symm
  · rw [show γ.val = fun s ↦ h • normalVector (t : Real.Angle) +
        Q s • tangentVector (t : Real.Angle) from rfl]
    let A := Q ⟨a, le_rfl, hab⟩
    let B := Q ⟨b, hab, le_rfl⟩
    have hAB : A ≤ B := hQmono hab
    have hQrange : Set.range Q = Set.Icc (Q ⟨a, le_rfl, hab⟩) (Q ⟨b, hab, le_rfl⟩) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨s, rfl⟩
        exact ⟨hQmono s.property.1, hQmono s.property.2⟩
      · intro y hy
        let _ : PreconnectedSpace (Set.Icc a b) :=
          Subtype.preconnectedSpace isPreconnected_Icc
        exact intermediate_value_univ ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩ hQcont hy
    have haeq := tangentLinePath_eq_coordinate K t ⟨a, ha⟩
    have hbeq := tangentLinePath_eq_coordinate K t ⟨b, hb⟩
    have hAa : closedTangentLineCoordinate K t a = A := rfl
    have hBb : closedTangentLineCoordinate K t b = B := rfl
    change Set.range (fun s ↦ h • normalVector (t : Real.Angle) +
      Q s • tangentVector (t : Real.Angle)) = _
    rw [haeq, hbeq]
    rw [hAa, hBb]
    rw [segment_eq_image_lineMap]
    ext p
    constructor
    · rintro ⟨s, rfl⟩
      have hs : Q s ∈ Set.Icc A B := by
        exact ⟨hQmono s.property.1, hQmono s.property.2⟩
      by_cases hABeq : A = B
      · refine ⟨0, by simp, ?_⟩
        have : Q s = A := le_antisymm (hs.2.trans_eq hABeq.symm) hs.1
        ext i
        simp [h, hABeq, this]
      · let u := (Q s - A) / (B - A)
        have hpos : 0 < B - A := sub_pos.mpr (lt_of_le_of_ne hAB hABeq)
        refine ⟨u, ⟨div_nonneg (sub_nonneg.mpr hs.1) hpos.le,
          (div_le_one hpos).2 (by linarith [hs.2])⟩, ?_⟩
        ext i
        simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply,
          smul_eq_mul]
        dsimp [u]
        field_simp [hpos.ne']
        ring
    · rintro ⟨u, hu, rfl⟩
      let r := A + u * (B - A)
      have hr : r ∈ Set.Icc A B := by
        dsimp [r]
        constructor
        · exact le_add_of_nonneg_right (mul_nonneg hu.1 (sub_nonneg.mpr hAB))
        · nlinarith [mul_le_mul_of_nonneg_right hu.2 (sub_nonneg.mpr hAB)]
      have hrange : r ∈ Set.range Q := by simpa [A, B, hQrange] using hr
      obtain ⟨s, hs⟩ := hrange
      refine ⟨s, ?_⟩
      ext i
      simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul]
      rw [hs]
      ring
  · intro p hp
    obtain ⟨s, rfl⟩ := hp
    change inner ℝ (γ.val s) (normalVector (t : Real.Angle)) = supportValue K _
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_normalVector_self, real_inner_comm, inner_normalVector_tangentVector]
    simp [h]
  · let Qbv : RightContinuousIntervalBV a b := {
      toFun := Q
      boundedVariation := hQbv
      right_continuous := fun s ↦ hQcont.continuousAt.continuousWithinAt }
    have hcoord (i : Fin 2) (s : Set.Icc a b) :
        (continuousBVCoordinate γ i).toFun s =
          h * normalVector (t : Real.Angle) i +
            tangentVector (t : Real.Angle) i * Qbv.toFun s := by
      change (h • normalVector (t : Real.Angle) + Q s • tangentVector (t : Real.Angle)) i = _
      simp [Qbv, mul_comm]
    unfold curveAreaFunctional
    change (intervalStieltjesIntegral (continuousBVCoordinate γ 1)
        (continuousBVCoordinate γ 0).toFun Set.univ -
      intervalStieltjesIntegral (continuousBVCoordinate γ 0)
        (continuousBVCoordinate γ 1).toFun Set.univ) / 2 = _
    rw [intervalStieltjesIntegral_affine_driver_cross hab Qbv
      (continuousBVCoordinate γ 0) (continuousBVCoordinate γ 1) hQcont
      (h * normalVector (t : Real.Angle) 0) (tangentVector (t : Real.Angle) 0)
      (h * normalVector (t : Real.Angle) 1) (tangentVector (t : Real.Angle) 1)
      (hcoord 0) (hcoord 1)]
    have haeq := tangentLinePath_eq_coordinate K t ⟨a, ha⟩
    have hbeq := tangentLinePath_eq_coordinate K t ⟨b, hb⟩
    rw [haeq, hbeq]
    simp only [Qbv]
    simp [segmentArea, planeCrossProduct, normalVector, tangentVector, frame, h]
    simp only [Q]
    ring

theorem tangentLinePath_convexLinear (t a b : ℝ)
    (ha : a ∈ Set.Ioc (t - Real.pi) t) (hb : b ∈ Set.Ioc (t - Real.pi) t)
    (hab : a ≤ b) :
    ∃ F : ConvexBody Point → ContinuousBVPaths a b,
      (∀ K, (F K).val = tangentLineRestriction K t a b ha hb) ∧
      IsConvexLinear convexBodyCombination
        (fun r x y ↦ (1 - (r : ℝ)) • x + (r : ℝ) • y) F := by
  let F : ConvexBody Point → ContinuousBVPaths a b := fun K ↦
    (tangentLinePath_segment_area K t a b ha hb hab).choose
  have hF (K : ConvexBody Point) :
      (F K).val = tangentLineRestriction K t a b ha hb :=
    (tangentLinePath_segment_area K t a b ha hb hab).choose_spec.1
  refine ⟨F, hF, ?_⟩
  intro r K L
  apply Subtype.ext
  funext s
  change (F (convexBodyCombination r K L)).val s =
    ((1 - (r : ℝ)) • (F K).val + (r : ℝ) • (F L).val) s
  rw [hF, hF, hF]
  unfold tangentLineRestriction tangentLinePath
  by_cases hs : (s : ℝ) < t
  · simp only [hs, ↓reduceIte, Pi.add_apply, Pi.smul_apply]
    exact (convexBody_maps_linear r K L).2.2.1 (s : ℝ) t hs
      (by linarith [ha.1, s.property.1])
  · have hst : (s : ℝ) = t := by
      apply le_antisymm
      · exact le_trans s.property.2 hb.2
      · exact le_of_not_gt hs
    simp only [hs, ↓reduceIte, Pi.add_apply, Pi.smul_apply]
    simpa [hst] using (convexBody_maps_linear r K L).2.1 (t : Real.Angle) |>.2

end MovingSofa

end

end

end
