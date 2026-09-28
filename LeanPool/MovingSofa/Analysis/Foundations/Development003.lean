/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Infrastructure.Analysis.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001



public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Geometry.Foundations.Development003
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
/-!
# Moving sofa: related mathematical developments

* `Analysis.SurfaceMeasure.UpperGraph`.
* `Analysis.SurfaceMeasure.ExposedFrontier`.
* `Analysis.SurfaceMeasure.RegularBoundaryHelpers`.
* `Analysis.SurfaceMeasure.GraphIntegral`.
* `Analysis.SurfaceMeasure.Construction`.
* `Analysis.SurfaceMeasure.GraphConvergence`.
* `Analysis.SurfaceMeasure.Properties`.
* `Analysis.SurfaceMeasure.BoundaryExtension`.
* `Analysis.SurfaceMeasure.Opposite`.
* `Analysis.SurfaceMeasure.WeakConvergence`.
* `Analysis.SurfaceMeasure.AtomLimits`.
* `Analysis.SurfaceMeasure.WeightedBoundary`.
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
# Analysis / Surface Measure / Upper Graph
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace MovingSofa

private def negCoordinates (e : Point ≃ₗᵢ[ℝ] Point) : Point ≃ₗᵢ[ℝ] Point :=
  e.trans (LinearIsometryEquiv.neg ℝ)

private def swapCoordinates (e : Point ≃ₗᵢ[ℝ] Point) : Point ≃ₗᵢ[ℝ] Point :=
  e.trans coordinateSwap

@[simp] private theorem negCoordinates_apply (e : Point ≃ₗᵢ[ℝ] Point) (p : Point) (i : Fin 2) :
    negCoordinates e p i = -e p i := by
  simp [negCoordinates]

@[simp] private theorem swapCoordinates_apply_zero (e : Point ≃ₗᵢ[ℝ] Point)
    (p : Point) : swapCoordinates e p 0 = e p 1 := by
  simp [swapCoordinates, coordinateSwap]

@[simp] private theorem swapCoordinates_apply_one (e : Point ≃ₗᵢ[ℝ] Point)
    (p : Point) : swapCoordinates e p 1 = e p 0 := by
  simp [swapCoordinates, coordinateSwap]

/-- The upper graph height is the greatest vertical coordinate in its fiber. -/
theorem upperGraphHeight_isGreatest (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ} (hx : x ∈ horizontalProjection K o e) :
    IsGreatest {y : ℝ | o + e.symm !₂[x, y] ∈ (K : Set Point)}
      (upperGraphHeight K o e x) := by
  let F : Set ℝ := {y | o + e.symm !₂[x, y] ∈ (K : Set Point)}
  let Y : Set ℝ := (fun p : Point ↦ e (p - o) 1) '' (K : Set Point)
  have hY : IsCompact Y := K.isCompact.image (by fun_prop)
  have hFc : IsClosed F := K.isClosed.preimage (by fun_prop)
  have hFY : F ⊆ Y := by
    intro y hy
    refine ⟨o + e.symm !₂[x, y], hy, ?_⟩
    simp
  have hF : IsCompact F := hY.of_isClosed_subset hFc hFY
  have hFne : F.Nonempty := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨e (p - o) 1, ?_⟩
    dsimp [F]
    convert hp using 1
    apply sub_eq_zero.mp
    apply e.injective
    ext i
    fin_cases i
    · simp only [map_sub, PiLp.sub_apply] at hpx
      simp
      linarith
    · simp
  change IsGreatest F (sSup F)
  exact hF.isGreatest_sSup hFne

/-- An attained upper graph point belongs to the convex body. -/
theorem upperGraphHeight_mem (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ} (hx : x ∈ horizontalProjection K o e) :
    o + e.symm !₂[x, upperGraphHeight K o e x] ∈ (K : Set Point) :=
  (upperGraphHeight_isGreatest K o e hx).1

private theorem upperGraphHeight_eq_coordinate_of_isExteriorNormal_of_pos
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    {a : Real.Angle} (ha : IsExteriorNormal K p a) (hpos : 0 < e (normalVector a) 1) :
    upperGraphHeight K o e (e (p - o) 0) = e (p - o) 1 := by
  have hx : e (p - o) 0 ∈ horizontalProjection K o e := ⟨p, hp, rfl⟩
  apply le_antisymm
  · apply le_of_not_gt
    intro hgt
    have hmem := upperGraphHeight_mem K o e hx
    have hs := ha (o + e.symm !₂[e (p - o) 0,
      upperGraphHeight K o e (e (p - o) 0)]) hmem
    rw [← e.inner_map_map] at hs
    simp only [map_sub, map_add, LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, PiLp.sub_apply, PiLp.add_apply] at hs
    have hzero : e (p - o) 0 = e p 0 - e o 0 := by simp
    have hone : e (p - o) 1 = e p 1 - e o 1 := by simp
    ring_nf at hs
    rw [hzero, hone] at hgt
    rw [show -(e o 0) + e p 0 = e p 0 - e o 0 by ring] at hs
    have hnonpos : e (normalVector a) 1 *
        (upperGraphHeight K o e (e p 0 - e o 0) - (e p 1 - e o 1)) ≤ 0 := by
      nlinarith [hs]
    exact (not_lt_of_ge hnonpos) (mul_pos hpos (sub_pos.mpr hgt))
  · exact (upperGraphHeight_isGreatest K o e hx).2 (by
      change o + e.symm !₂[e (p - o) 0, e (p - o) 1] ∈ (K : Set Point)
      rw [show o + e.symm !₂[e (p - o) 0, e (p - o) 1] = p by
        apply e.injective
        ext i
        fin_cases i <;> simp [map_sub]]
      exact hp)

/-- A boundary point whose exterior normal has positive vertical coordinate lies
on the upper coordinate graph. -/
theorem eq_upperCoordinateGraph_of_isExteriorNormal_of_pos
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    {a : Real.Angle} (ha : IsExteriorNormal K p a) (hpos : 0 < e (normalVector a) 1) :
    p = o + e.symm !₂[e (p - o) 0, upperGraphHeight K o e (e (p - o) 0)] := by
  rw [upperGraphHeight_eq_coordinate_of_isExteriorNormal_of_pos K o e hp ha hpos]
  apply e.injective
  ext i
  fin_cases i <;> simp [map_sub]

private theorem eq_upperCoordinateGraph_of_maximal_verticalCoordinate
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    (hmax : ∀ q ∈ K, e (q - o) 1 ≤ e (p - o) 1) :
    p = o + e.symm !₂[e (p - o) 0, upperGraphHeight K o e (e (p - o) 0)] := by
  have hx : e (p - o) 0 ∈ horizontalProjection K o e := ⟨p, hp, rfl⟩
  have hpGreatest : IsGreatest
      {y : ℝ | o + e.symm !₂[e (p - o) 0, y] ∈ (K : Set Point)} (e (p - o) 1) := by
    constructor
    · change o + e.symm !₂[e (p - o) 0, e (p - o) 1] ∈ (K : Set Point)
      rw [show o + e.symm !₂[e (p - o) 0, e (p - o) 1] = p by
        apply e.injective
        ext i
        fin_cases i <;> simp [map_sub]]
      exact hp
    · intro y hy
      have := hmax (o + e.symm !₂[e (p - o) 0, y]) hy
      simpa using this
  have heq := (upperGraphHeight_isGreatest K o e hx).unique hpGreatest
  rw [heq]
  apply e.injective
  ext i
  fin_cases i <;> simp [map_sub]

private theorem horizontalCoordinate_le_rightBound (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K) :
    e (p - o) 0 ≤ (horizontalBounds K o e).2 := by
  exact (K.isCompact.image (by fun_prop)).isGreatest_sSup (K.nonempty.image _)
    |>.2 ⟨p, hp, rfl⟩

private theorem horizontalProjection_negCoordinates (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    horizontalProjection K o (negCoordinates e) = -(horizontalProjection K o e) := by
  ext x
  simp only [horizontalProjection, negCoordinates, LinearIsometryEquiv.trans_apply, map_sub,
    LinearIsometryEquiv.coe_neg, Fin.isValue, PiLp.sub_apply, PiLp.neg_apply, Set.mem_image,
    SetLike.mem_coe, Set.mem_neg]
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, by linarith⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, by linarith⟩

private theorem horizontalBounds_negCoordinates (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    horizontalBounds K o (negCoordinates e) =
      (-(horizontalBounds K o e).2, -(horizontalBounds K o e).1) := by
  simp only [horizontalBounds, horizontalProjection_negCoordinates, Real.sInf_neg,
    Real.sSup_neg]

private theorem leftBound_le_horizontalCoordinate (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K) :
    (horizontalBounds K o e).1 ≤ e (p - o) 0 := by
  exact (K.isCompact.image (by fun_prop)).isLeast_sInf (K.nonempty.image _)
    |>.2 ⟨p, hp, rfl⟩

private theorem eq_swapUpperGraph_of_horizontalCoordinate_eq_rightBound
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    (hpr : e (p - o) 0 = (horizontalBounds K o e).2) :
    p = o + (swapCoordinates e).symm
      !₂[swapCoordinates e (p - o) 0,
        upperGraphHeight K o (swapCoordinates e) (swapCoordinates e (p - o) 0)] := by
  apply eq_upperCoordinateGraph_of_maximal_verticalCoordinate K o (swapCoordinates e) hp
  intro q hq
  have hqle := horizontalCoordinate_le_rightBound K o e hq
  simp only [swapCoordinates_apply_one]
  simp only [map_sub, PiLp.sub_apply] at hpr hqle ⊢
  linarith

private theorem eq_negSwapUpperGraph_of_horizontalCoordinate_eq_leftBound
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    (hpl : e (p - o) 0 = (horizontalBounds K o e).1) :
    p = o + (negCoordinates (swapCoordinates e)).symm
      !₂[negCoordinates (swapCoordinates e) (p - o) 0,
        upperGraphHeight K o (negCoordinates (swapCoordinates e))
          (negCoordinates (swapCoordinates e) (p - o) 0)] := by
  apply eq_upperCoordinateGraph_of_maximal_verticalCoordinate K o
    (negCoordinates (swapCoordinates e)) hp
  intro q hq
  have hle := leftBound_le_horizontalCoordinate K o e hq
  simp only [negCoordinates_apply, swapCoordinates_apply_one]
  simp only [map_sub, PiLp.sub_apply] at hpl hle ⊢
  linarith

private def coordinateCornerSet (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : Set Point :=
  {p | e (p - o) 0 ∈ ({(horizontalBounds K o e).1,
      (horizontalBounds K o e).2} : Set ℝ) ∧
    e (p - o) 1 ∈ ({(horizontalBounds K o (swapCoordinates e)).1,
      (horizontalBounds K o (swapCoordinates e)).2} : Set ℝ)}

private theorem coordinateCornerSet_finite (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : (coordinateCornerSet K o e).Finite := by
  let coords : Point → ℝ × ℝ := fun p ↦ (e (p - o) 0, e (p - o) 1)
  let xs : Set ℝ := {(horizontalBounds K o e).1, (horizontalBounds K o e).2}
  let ys : Set ℝ := {(horizontalBounds K o (swapCoordinates e)).1,
    (horizontalBounds K o (swapCoordinates e)).2}
  have hcoords : Function.Injective coords := by
    intro p q hpq
    apply sub_left_injective (b := o)
    apply e.injective
    ext i
    fin_cases i
    · exact congrArg Prod.fst hpq
    · exact congrArg Prod.snd hpq
  have hfinite : (xs ×ˢ ys).Finite := Set.toFinite xs |>.prod (Set.toFinite ys)
  have hpre : (coords ⁻¹' (xs ×ˢ ys)).Finite := hfinite.preimage hcoords.injOn
  have heq : coordinateCornerSet K o e = coords ⁻¹' (xs ×ˢ ys) := by
    ext p
    simp only [coordinateCornerSet, coords, xs, ys, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_prod, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [heq]
  exact hpre

private theorem hausdorffMeasure_coordinateCornerSet_eq_zero (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    Measure.hausdorffMeasure 1 (coordinateCornerSet K o e) = 0 := by
  let _ := MeasureTheory.Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact (coordinateCornerSet_finite K o e).measure_zero _

/-- The upper height function of a convex body is concave on its projection. -/
theorem concaveOn_upperGraphHeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    ConcaveOn ℝ (horizontalProjection K o e) (upperGraphHeight K o e) := by
  have hproj : Convex ℝ (horizontalProjection K o e) := by
    intro x hx y hy a b ha hb hab
    obtain ⟨p, hp, hpx⟩ := hx
    obtain ⟨q, hq, hqx⟩ := hy
    refine ⟨a • p + b • q, K.convex hp hq ha hb hab, ?_⟩
    simp only [map_sub, map_add, map_smul, PiLp.sub_apply, PiLp.add_apply,
      PiLp.smul_apply] at hpx hqx ⊢
    linear_combination a * hpx + b * hqx + e o 0 * hab
  refine ⟨hproj, ?_⟩
  · intro x hx y hy a b ha hb hab
    apply (upperGraphHeight_isGreatest K o e (by
      exact hproj hx hy ha hb hab)).2
    have hpx := upperGraphHeight_mem K o e hx
    have hpy := upperGraphHeight_mem K o e hy
    have hconv := K.convex hpx hpy ha hb hab
    change o + e.symm !₂[a • x + b • y,
      a • upperGraphHeight K o e x + b • upperGraphHeight K o e y] ∈ (K : Set Point)
    rw [show o + e.symm !₂[a • x + b • y,
        a • upperGraphHeight K o e x + b • upperGraphHeight K o e y] =
        a • (o + e.symm !₂[x, upperGraphHeight K o e x]) +
          b • (o + e.symm !₂[y, upperGraphHeight K o e y]) by
      apply e.injective
      ext i
      fin_cases i <;> simp [map_add, map_smul] <;>
        linear_combination -(e o _) * hab]
    exact hconv

/-- The horizontal projection is the interval between its compact extrema. -/
theorem horizontalProjection_eq_Icc (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    horizontalProjection K o e =
      Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2 := by
  let s := horizontalProjection K o e
  have hscompact : IsCompact s := K.isCompact.image (by fun_prop)
  have hsne : s.Nonempty := K.nonempty.image _
  have hsconv : Convex ℝ s := (concaveOn_upperGraphHeight K o e).1
  change s = Set.Icc (sInf s) (sSup s)
  apply Set.Subset.antisymm
  · exact hscompact.isBounded.subset_Icc_sInf_sSup
  · have hle := (hscompact.isLeast_sInf hsne).2 (hscompact.sSup_mem hsne)
    rw [← Set.uIcc_of_le hle, ← segment_eq_uIcc]
    exact hsconv.segment_subset (hscompact.sInf_mem hsne) (hscompact.sSup_mem hsne)

/-- The upper boundary height is locally Lipschitz inside its projection interval. -/
theorem locallyLipschitzOn_upperGraphHeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    LocallyLipschitzOn
      (Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
      (upperGraphHeight K o e) := by
  have hlip := (concaveOn_upperGraphHeight K o e).locallyLipschitzOn_interior
  rw [horizontalProjection_eq_Icc K o e, interior_Icc] at hlip
  exact hlip

/-- The upward normal determined by the derivative of an upper graph is exterior. -/
theorem upperGraph_deriv_isExteriorNormal (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ}
    (hx : x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
    (hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x) :
    IsExteriorNormal K (o + e.symm !₂[x, upperGraphHeight K o e x])
      (vectorNormalAngle (e.symm !₂[-deriv (upperGraphHeight K o e) x, 1])) := by
  let g := upperGraphHeight K o e
  let q : Point := e.symm !₂[-deriv g x, 1]
  have hq : q ≠ 0 := by
    intro hzero
    have := congrFun (congrArg WithLp.ofLp (congrArg e hzero)) 1
    simp [q] at this
  change IsExteriorNormal K (o + e.symm !₂[x, g x]) (vectorNormalAngle q)
  rw [IsExteriorNormal]
  rw [normalVector_vectorNormalAngle hq]
  intro p hp
  have hxp : e (p - o) 0 ∈ horizontalProjection K o e := ⟨p, hp, rfl⟩
  have hxproj : x ∈ horizontalProjection K o e := by
    rw [horizontalProjection_eq_Icc K o e]
    exact ⟨hx.1.le, hx.2.le⟩
  have hvertical : e (p - o) 1 ≤ g (e (p - o) 0) :=
    (upperGraphHeight_isGreatest K o e hxp).2 (by
      change o + e.symm !₂[e (p - o) 0, e (p - o) 1] ∈ (K : Set Point)
      rw [show o + e.symm !₂[e (p - o) 0, e (p - o) 1] = p by
        apply e.injective
        ext i
        fin_cases i <;> simp [map_sub]]
      exact hp)
  have htangent := ConcaveOn.le_add_deriv_mul_sub
    (concaveOn_upperGraphHeight K o e) hxproj hdiff hxp
  have hvertical' : e p 1 - e o 1 ≤ g (e p 0 - e o 0) := by
    simpa only [map_sub, PiLp.sub_apply] using hvertical
  have htangent' : g (e p 0 - e o 0) ≤
      g x + deriv g x * ((e p 0 - e o 0) - x) := by
    simpa only [map_sub, PiLp.sub_apply] using htangent
  rw [inner_smul_right]
  apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg q))
  rw [← e.inner_map_map]
  simp only [map_sub, map_add, LinearIsometryEquiv.apply_symm_apply, q, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, PiLp.sub_apply, PiLp.add_apply]
  dsimp only [g] at hvertical' htangent' ⊢
  nlinarith [hvertical', htangent']

/-- Angular normal vectors have norm one. -/
theorem norm_normalVector (a : Real.Angle) : ‖normalVector a‖ = 1 := by
  induction a using Real.Angle.induction_on with
  | _ a =>
    rw [EuclideanSpace.norm_eq]
    simp [normalVector, frame, Fin.sum_univ_two]

private theorem horizontalCoordinate_eq_endpoint_of_isExteriorNormal_of_vertical_eq_zero
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    {a : Real.Angle} (ha : IsExteriorNormal K p a)
    (hzero : e (normalVector a) 1 = 0) :
    e (p - o) 0 = (horizontalBounds K o e).1 ∨
      e (p - o) 0 = (horizontalBounds K o e).2 := by
  have hxne : e (normalVector a) 0 ≠ 0 := by
    intro hx
    have he : e (normalVector a) = 0 := by
      ext i
      fin_cases i <;> simp [hx, hzero]
    have hn : ‖e (normalVector a)‖ = 1 := by rw [e.norm_map, norm_normalVector]
    simp [he] at hn
  rcases lt_or_gt_of_ne hxne with hneg | hpos
  · left
    have hleast : IsLeast (horizontalProjection K o e) (e (p - o) 0) := by
      refine ⟨⟨p, hp, rfl⟩, ?_⟩
      rintro x ⟨q, hq, rfl⟩
      have hs := ha q hq
      rw [← e.inner_map_map] at hs
      simp only [map_sub, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        Fin.sum_univ_two, PiLp.sub_apply, hzero] at hs
      have hxcoord : e (q - o) 0 - e (p - o) 0 = e q 0 - e p 0 := by simp
      nlinarith
    exact hleast.unique ((K.isCompact.image (by fun_prop)).isLeast_sInf (K.nonempty.image _))
  · right
    have hgreatest : IsGreatest (horizontalProjection K o e) (e (p - o) 0) := by
      refine ⟨⟨p, hp, rfl⟩, ?_⟩
      rintro x ⟨q, hq, rfl⟩
      have hs := ha q hq
      rw [← e.inner_map_map] at hs
      simp only [map_sub, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        Fin.sum_univ_two, PiLp.sub_apply, hzero] at hs
      have hxcoord : e (q - o) 0 - e (p - o) 0 = e q 0 - e p 0 := by simp
      nlinarith
    exact hgreatest.unique ((K.isCompact.image (by fun_prop)).isGreatest_sSup
      (K.nonempty.image _))

/-- A point of a convex body admitting an exterior unit normal belongs to its frontier. -/
theorem mem_frontier_of_mem_of_isExteriorNormal (K : ConvexBody Point)
    {p : Point} (hp : p ∈ K) {a : Real.Angle} (ha : IsExteriorNormal K p a) :
    p ∈ frontier (K : Set Point) := by
  rw [mem_frontier_iff_notMem_interior hp]
  intro hpint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hpint
  let q := p + (ε / 2) • normalVector a
  have hqp : q ∈ K := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show q - p = (ε / 2) • normalVector a by simp [q], norm_smul,
      norm_normalVector]
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hε (by norm_num))]
    linarith))
  have := ha q hqp
  rw [show q - p = (ε / 2) • normalVector a by simp [q], inner_smul_left,
    real_inner_self_eq_norm_sq, norm_normalVector a] at this
  have hnonpos : ε / 2 ≤ 0 := by simpa using this
  linarith

private theorem upperGraph_tangent_orthogonal_of_isExteriorNormal
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ}
    (hx : x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
    (hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x) {a : Real.Angle}
    (ha : IsExteriorNormal K
      (o + e.symm !₂[x, upperGraphHeight K o e x]) a) :
    inner ℝ (e.symm !₂[1, deriv (upperGraphHeight K o e) x]) (normalVector a) = 0 := by
  let g := upperGraphHeight K o e
  let n := e (normalVector a)
  let f : ℝ → ℝ := fun y ↦ (y - x) * n 0 + (g y - g x) * n 1
  have hlocal : IsLocalMax f x := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have hyproj : y ∈ horizontalProjection K o e := by
      rw [horizontalProjection_eq_Icc K o e]
      exact ⟨hy.1.le, hy.2.le⟩
    have hmem := upperGraphHeight_mem K o e hyproj
    have hsupport := ha (o + e.symm !₂[y, g y]) hmem
    rw [← e.inner_map_map] at hsupport
    simp only [map_sub, map_add, LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, PiLp.sub_apply, PiLp.add_apply] at hsupport
    dsimp only [f, g, n]
    dsimp only [g] at hsupport
    nlinarith [hsupport]
  have hfderiv : HasDerivAt f (n 0 + deriv g x * n 1) x := by
    convert (((hasDerivAt_id x).sub_const x).mul_const (n 0)).add
      ((hdiff.hasDerivAt.sub_const (g x)).mul_const (n 1)) using 1
    · funext y
      rfl
    · simp [g]
  have hzero := hlocal.hasDerivAt_eq_zero hfderiv
  rw [← e.inner_map_map]
  simp only [LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  dsimp only [g, n] at hzero ⊢
  nlinarith [hzero]

private theorem normalVector_injective : Function.Injective normalVector := by
  intro a b hab
  induction a using Real.Angle.induction_on with
  | _ a =>
    induction b using Real.Angle.induction_on with
    | _ b =>
      apply Real.Angle.cos_sin_inj
      · exact congrFun (congrArg WithLp.ofLp hab) 0
      · exact congrFun (congrArg WithLp.ofLp hab) 1

private theorem exteriorNormal_eq_of_orthogonal_of_interior_nonempty
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    {p v : Point} (hv : v ≠ 0) {a b : Real.Angle}
    (ha : IsExteriorNormal K p a) (hb : IsExteriorNormal K p b)
    (hva : inner ℝ v (normalVector a) = 0)
    (hvb : inner ℝ v (normalVector b) = 0) : a = b := by
  let orientation : Orientation ℝ Point (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  rcases EuclideanGeometry.eq_or_eq_neg_of_unit_orthogonal orientation hv (norm_normalVector a)
      (norm_normalVector b) hva hvb with hab | hab
  · exact normalVector_injective hab
  · exfalso
    obtain ⟨z, hz⟩ := hK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    let q := z + (ε / 2) • normalVector a
    have hq : q ∈ K := interior_subset (hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [show q - z = (ε / 2) • normalVector a by simp [q], norm_smul,
        norm_normalVector, Real.norm_eq_abs, abs_of_pos (div_pos hε (by norm_num))]
      norm_num
      linarith))
    have haz := ha z (interior_subset hz)
    have hbz := hb z (interior_subset hz)
    have hba : normalVector b = -normalVector a := by rw [hab]; simp
    rw [hba, inner_neg_right] at hbz
    have heq : inner ℝ (z - p) (normalVector a) = 0 := by linarith
    have haq := ha q hq
    have hqp : q - p = (z - p) + (ε / 2) • normalVector a := by
      dsimp only [q]
      module
    rw [hqp,
      inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
      norm_normalVector a, heq, zero_add] at haq
    have : ε / 2 ≤ 0 := by simpa using haq
    linarith

/-- A differentiable interior point of an upper boundary graph is regular. -/
theorem upperGraph_mem_regularBoundary (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {x : ℝ} (hx : x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
    (hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x) :
    o + e.symm !₂[x, upperGraphHeight K o e x] ∈ regularBoundary K := by
  let p := o + e.symm !₂[x, upperGraphHeight K o e x]
  let a := vectorNormalAngle
    (e.symm !₂[-deriv (upperGraphHeight K o e) x, 1])
  have hxproj : x ∈ horizontalProjection K o e := by
    rw [horizontalProjection_eq_Icc K o e]
    exact ⟨hx.1.le, hx.2.le⟩
  have hp : p ∈ K := upperGraphHeight_mem K o e hxproj
  have ha : IsExteriorNormal K p a := upperGraph_deriv_isExteriorNormal K o e hx hdiff
  refine ⟨mem_frontier_of_mem_of_isExteriorNormal K hp ha, a, ha, ?_⟩
  intro b hb
  symm
  apply exteriorNormal_eq_of_orthogonal_of_interior_nonempty K hK
    (v := e.symm !₂[1, deriv (upperGraphHeight K o e) x])
  · intro hv
    have := congrFun (congrArg WithLp.ofLp (congrArg e hv)) 0
    simp at this
  · exact ha
  · exact hb
  · rw [normalVector_vectorNormalAngle]
    · rw [← e.inner_map_map]
      simp [PiLp.inner_apply, Fin.sum_univ_two]
    · intro hv
      have := congrFun (congrArg WithLp.ofLp (congrArg e hv)) 1
      simp at this
  · exact upperGraph_tangent_orthogonal_of_isExteriorNormal K o e hx hdiff (a := b) hb

/-- Points of an upper graph lying above nondifferentiability parameters. -/
def irregularUpperGraph (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : Set Point :=
  (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x]) ''
    {x | x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2 ∧
      ¬ DifferentiableAt ℝ (upperGraphHeight K o e) x}

/-- An irregular upper graph has zero one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_irregularUpperGraph_eq_zero (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    Measure.hausdorffMeasure 1 (irregularUpperGraph K o e) = 0 := by
  exact MeasureTheory.hausdorffMeasure_coordinateGraph_nondifferentiable_eq_zero
    (locallyLipschitzOn_upperGraphHeight K o e) o e

private theorem eq_left_or_eq_right_or_mem_Ioo {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    x = a ∨ x = b ∨ x ∈ Set.Ioo a b := by
  rcases hx.1.eq_or_lt with h | h
  · exact Or.inl h.symm
  rcases hx.2.eq_or_lt with h' | h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr ⟨h, h'⟩)

private theorem irregularBoundary_subset_graphs_union_corners (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    frontier (K : Set Point) \ regularBoundary K ⊆
      irregularUpperGraph K o e ∪ (irregularUpperGraph K o (negCoordinates e) ∪
      (irregularUpperGraph K o (swapCoordinates e) ∪
      (irregularUpperGraph K o (negCoordinates (swapCoordinates e)) ∪
      coordinateCornerSet K o e))) := by
  intro p hp
  have hpK : p ∈ K := by
    change p ∈ (K : Set Point)
    rw [← K.isClosed.closure_eq]
    exact frontier_subset_closure hp.1
  let x := e (p - o) 0
  let y := e (p - o) 1
  have hxIcc : x ∈ Set.Icc (horizontalBounds K o e).1
      (horizontalBounds K o e).2 := by
    rw [← horizontalProjection_eq_Icc K o e]
    exact ⟨p, hpK, rfl⟩
  have hyIcc : y ∈ Set.Icc (horizontalBounds K o (swapCoordinates e)).1
      (horizontalBounds K o (swapCoordinates e)).2 := by
    rw [← horizontalProjection_eq_Icc K o (swapCoordinates e)]
    refine ⟨p, hpK, ?_⟩
    simp [y, swapCoordinates_apply_zero]
  rcases eq_left_or_eq_right_or_mem_Ioo hxIcc with hxleft | hxright | hxint
  · rcases eq_left_or_eq_right_or_mem_Ioo hyIcc with hyleft | hyright | hyint
    · right; right; right; right
      exact ⟨Or.inl (by simpa [x] using hxleft), Or.inl (by simpa [y] using hyleft)⟩
    · right; right; right; right
      exact ⟨Or.inl (by simpa [x] using hxleft), Or.inr (by simpa [y] using hyright)⟩
    · right; right; right; left
      let e' := negCoordinates (swapCoordinates e)
      let z := e' (p - o) 0
      have hzint : z ∈ Set.Ioo (horizontalBounds K o e').1
          (horizontalBounds K o e').2 := by
        rw [horizontalBounds_negCoordinates]
        change -y ∈ Set.Ioo (-(horizontalBounds K o (swapCoordinates e)).2)
          (-(horizontalBounds K o (swapCoordinates e)).1)
        exact ⟨neg_lt_neg hyint.2, neg_lt_neg hyint.1⟩
      have hgraph := eq_negSwapUpperGraph_of_horizontalCoordinate_eq_leftBound
        K o e hpK (by simpa [x] using hxleft)
      refine ⟨z, ⟨hzint, ?_⟩, hgraph.symm⟩
      intro hdiff
      apply hp.2
      rw [hgraph]
      exact upperGraph_mem_regularBoundary K hK o e' hzint hdiff
  · rcases eq_left_or_eq_right_or_mem_Ioo hyIcc with hyleft | hyright | hyint
    · right; right; right; right
      exact ⟨Or.inr (by simpa [x] using hxright), Or.inl (by simpa [y] using hyleft)⟩
    · right; right; right; right
      exact ⟨Or.inr (by simpa [x] using hxright), Or.inr (by simpa [y] using hyright)⟩
    · right; right; left
      let e' := swapCoordinates e
      let z := e' (p - o) 0
      have hzint : z ∈ Set.Ioo (horizontalBounds K o e').1
          (horizontalBounds K o e').2 := by simpa [e', z, y] using hyint
      have hgraph := eq_swapUpperGraph_of_horizontalCoordinate_eq_rightBound
        K o e hpK (by simpa [x] using hxright)
      refine ⟨z, ⟨hzint, ?_⟩, hgraph.symm⟩
      intro hdiff
      apply hp.2
      rw [hgraph]
      exact upperGraph_mem_regularBoundary K hK o e' hzint hdiff
  · obtain ⟨a, ha⟩ := exists_isExteriorNormal_of_mem_frontier K hK hp.1
    have hvertical : e (normalVector a) 1 ≠ 0 := by
      intro hzero
      rcases horizontalCoordinate_eq_endpoint_of_isExteriorNormal_of_vertical_eq_zero
        K o e hpK ha hzero with hleft | hright
      · exact hxint.1.ne' (by simpa [x] using hleft)
      · exact hxint.2.ne (by simpa [x] using hright)
    rcases lt_or_gt_of_ne hvertical with hneg | hpos
    · right; left
      let e' := negCoordinates e
      let z := e' (p - o) 0
      have hzint : z ∈ Set.Ioo (horizontalBounds K o e').1
          (horizontalBounds K o e').2 := by
        rw [horizontalBounds_negCoordinates]
        change -x ∈ Set.Ioo (-(horizontalBounds K o e).2)
          (-(horizontalBounds K o e).1)
        exact ⟨neg_lt_neg hxint.2, neg_lt_neg hxint.1⟩
      have hgraph := eq_upperCoordinateGraph_of_isExteriorNormal_of_pos K o e'
        hpK ha (by simpa [e'] using neg_pos.mpr hneg)
      refine ⟨z, ⟨hzint, ?_⟩, hgraph.symm⟩
      intro hdiff
      apply hp.2
      rw [hgraph]
      exact upperGraph_mem_regularBoundary K hK o e' hzint hdiff
    · left
      have hgraph := eq_upperCoordinateGraph_of_isExteriorNormal_of_pos K o e hpK ha hpos
      refine ⟨x, ⟨hxint, ?_⟩, ?_⟩
      · intro hdiff
        apply hp.2
        rw [hgraph]
        exact upperGraph_mem_regularBoundary K hK o e hxint hdiff
      · simpa [x] using hgraph.symm

/-- The irregular boundary of a planar convex body with nonempty interior has
zero one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_irregularBoundary_eq_zero (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) :
    Measure.hausdorffMeasure 1
      (frontier (K : Set Point) \ regularBoundary K) = 0 := by
  let e : Point ≃ₗᵢ[ℝ] Point := LinearIsometryEquiv.refl ℝ Point
  let o : Point := 0
  apply measure_mono_null
    (irregularBoundary_subset_graphs_union_corners K hK o e)
  exact MeasureTheory.measure_union_null
    (hausdorffMeasure_irregularUpperGraph_eq_zero K o e)
    (MeasureTheory.measure_union_null
      (hausdorffMeasure_irregularUpperGraph_eq_zero K o (negCoordinates e))
      (MeasureTheory.measure_union_null
        (hausdorffMeasure_irregularUpperGraph_eq_zero K o (swapCoordinates e))
        (MeasureTheory.measure_union_null
          (hausdorffMeasure_irregularUpperGraph_eq_zero K o
            (negCoordinates (swapCoordinates e)))
          (hausdorffMeasure_coordinateCornerSet_eq_zero K o e))))

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
# Exposed faces and the boundary of a convex body

The exposed faces of a convex body are exactly the sets of boundary points realizing a support
value: each exposed face lies on the boundary, and, when the body has interior, every boundary
point lies on some exposed face.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Every boundary point of a convex body with nonempty interior lies on a supporting
exposed face. -/
theorem exists_mem_exposedEdge_of_mem_frontier
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    {p : Point} (hp : p ∈ frontier (K : Set Point)) :
    ∃ a : Real.Angle, p ∈ exposedEdge K a := by
  have hpK : p ∈ K := by
    change p ∈ (K : Set Point)
    rw [← K.isClosed.closure_eq]
    exact frontier_subset_closure hp
  obtain ⟨a, ha⟩ := exists_isExteriorNormal_of_mem_frontier K hK hp
  refine ⟨a, hpK, ?_⟩
  change inner ℝ p (normalVector a) = supportValue K a
  apply le_antisymm
  · exact inner_le_supportValue K hpK a
  · obtain ⟨q, hq, hqeq⟩ := exists_mem_inner_eq_supportValue K a
    rw [← hqeq]
    have := ha q hq
    rw [inner_sub_left] at this
    linarith

/-- Every exposed face of a convex body lies on its boundary. -/
theorem exposedEdge_subset_frontier
    (K : ConvexBody Point) (a : Real.Angle) :
    exposedEdge K a ⊆ frontier (K : Set Point) := by
  intro p hp
  rw [mem_frontier_iff_notMem_interior hp.1]
  intro hpint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hpint
  let z := p + (ε / 2) • normalVector a
  have hzball : z ∈ Metric.ball p ε := by
    simp only [Metric.mem_ball, dist_eq_norm, z, add_sub_cancel_left, norm_smul,
      norm_normalVector, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hzK : z ∈ K := interior_subset (hball hzball)
  have hzle := inner_le_supportValue K hzK a
  have hpEq := hp.2
  change inner ℝ p (normalVector a) = supportValue K a at hpEq
  have hnorm : inner ℝ (normalVector a) (normalVector a) = 1 := by
    induction a using Real.Angle.induction_on with
    | _ a => exact inner_normalVector_self a
  rw [show z = p + (ε / 2) • normalVector a from rfl, inner_add_left,
    real_inner_smul_left, hnorm, hpEq] at hzle
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
# Analysis / Surface Measure / Regular Boundary Helpers
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- A planar convex body with nonempty interior has no segment presentation. -/
theorem not_exists_segmentPresentation_of_interior_nonempty (K : ConvexBody Point)
    (hint : (interior (K : Set Point)).Nonempty) : ¬ ∃ d, IsSegmentPresentation K d := by
  rintro ⟨d, hd⟩
  have htop : affineSpan ℝ (K : Set Point) = ⊤ :=
    K.convex.interior_nonempty_iff_affineSpan_eq_top.mp hint
  have hle : affineSpan ℝ (K : Set Point) ≤ affineSpan ℝ ({d.1, d.2.1} : Set Point) := by
    rw [hd.2.1]
    apply affineSpan_le.2
    exact (affineSpan ℝ ({d.1, d.2.1} : Set Point)).convex.segment_subset
      (subset_affineSpan ℝ _ (by simp)) (subset_affineSpan ℝ _ (by simp))
  rw [htop] at hle
  have heq : affineSpan ℝ ({d.1, d.2.1} : Set Point) = ⊤ := top_unique hle
  have hfin := (collinear_iff_finrank_le_one.mp (collinear_pair ℝ d.1 d.2.1))
  rw [← direction_affineSpan, heq] at hfin
  rw [AffineSubspace.direction_top ℝ Point Point, finrank_top] at hfin
  norm_num [Point, finrank_euclideanSpace_fin] at hfin

/-- A convex body with nonempty interior is not a singleton. -/
theorem not_subsingleton_of_interior_nonempty (K : ConvexBody Point)
    (hint : (interior (K : Set Point)).Nonempty) : ¬ (K : Set Point).Subsingleton := by
  intro hsub
  obtain ⟨p, hp⟩ := K.nonempty
  have hK : (K : Set Point) = {p} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun x hx ↦ hsub hx hp⟩
  rw [hK, interior_singleton] at hint
  exact hint.ne_empty rfl

private theorem surfaceAreaMeasure_eq_map_of_interior_nonempty (K : ConvexBody Point)
    (hint : (interior (K : Set Point)).Nonempty) :
    surfaceAreaMeasure K = Measure.map (exteriorNormalAngle K)
      ((Measure.hausdorffMeasure 1).restrict (regularBoundary K)) := by
  have hsub := not_subsingleton_of_interior_nonempty K hint
  have hseg := not_exists_segmentPresentation_of_interior_nonempty K hint
  simp [surfaceAreaMeasure, hsub, hseg]

/-- Surface area measure is finite when the convex body has nonempty interior. -/
theorem isFiniteMeasure_surfaceAreaMeasure_of_interior_nonempty (K : ConvexBody Point)
    (hint : (interior (K : Set Point)).Nonempty) : IsFiniteMeasure (surfaceAreaMeasure K) := by
  rw [surfaceAreaMeasure_eq_map_of_interior_nonempty K hint]
  let μ := (Measure.hausdorffMeasure 1).restrict (regularBoundary K)
  have hμ : μ Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono fun p hp ↦ hp.1)
      (K.hausdorffMeasure_frontier_lt_top hint)
  let _ : IsFiniteMeasure μ := ⟨hμ⟩
  exact Measure.isFiniteMeasure_map μ (exteriorNormalAngle K)

/-- Any extension of the exterior-normal angle from the regular boundary gives
the surface area measure as a pushforward of frontier length. -/
theorem surfaceAreaMeasure_eq_map_frontier_of_eq_on_regularBoundary
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    (ν : Point → Real.Angle)
    (hν : ∀ p ∈ regularBoundary K, ν p = exteriorNormalAngle K p) :
    surfaceAreaMeasure K = Measure.map ν
      ((Measure.hausdorffMeasure 1).restrict (frontier (K : Set Point))) := by
  let μ : Measure Point := Measure.hausdorffMeasure 1
  have hregular : regularBoundary K ⊆ frontier (K : Set Point) := fun _ hp ↦ hp.1
  have hae : frontier (K : Set Point) =ᵐ[μ] regularBoundary K := by
    rw [ae_eq_set]
    exact ⟨hausdorffMeasure_irregularBoundary_eq_zero K hK,
      measure_mono_null (fun _ hp ↦ (hp.2 (hregular hp.1)).elim) measure_empty⟩
  have hrestrict : μ.restrict (frontier (K : Set Point)) =
      μ.restrict (regularBoundary K) := Measure.restrict_congr_set hae
  rw [surfaceAreaMeasure_eq_map_of_interior_nonempty K hK, hrestrict]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (measurableSet_regularBoundary K)] with p hp
  exact (hν p hp).symm

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
# Analysis / Surface Measure / Graph Integral
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

private theorem exteriorNormalAngle_upperGraph_eq (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {x : ℝ} (hx : x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
    (hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x) :
    exteriorNormalAngle K (o + e.symm !₂[x, upperGraphHeight K o e x]) =
      vectorNormalAngle (e.symm !₂[-deriv (upperGraphHeight K o e) x, 1]) := by
  have hp := upperGraph_mem_regularBoundary K hK o e hx hdiff
  have hu := hp.2
  have hn : IsExteriorNormal K (o + e.symm !₂[x, upperGraphHeight K o e x])
      (exteriorNormalAngle K (o + e.symm !₂[x, upperGraphHeight K o e x])) := by
    unfold exteriorNormalAngle
    rw [dite_eq_left hu]
    exact hu.exists.choose_spec
  exact hu.unique hn (upperGraph_deriv_isExteriorNormal K o e hx hdiff)

private theorem coordinate_normalVector_vectorNormalAngle_second
    (e : Point ≃ₗᵢ[ℝ] Point) (m : ℝ) :
    e (normalVector (vectorNormalAngle (e.symm !₂[-m, 1]))) 1 =
      (Real.sqrt (1 + m ^ 2))⁻¹ := by
  let q : Point := e.symm !₂[-m, 1]
  have hq : q ≠ 0 := by
    intro h
    have h1 := congrFun (congrArg WithLp.ofLp (congrArg e h)) 1
    simp [q] at h1
  rw [normalVector_vectorNormalAngle hq, map_smul, PiLp.smul_apply]
  have hnorm : ‖q‖ = Real.sqrt (1 + m ^ 2) := by
    rw [← e.norm_map q, LinearIsometryEquiv.apply_symm_apply, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_two, Real.norm_eq_abs, pow_two]
    ring
  rw [hnorm]
  simp [q]

private theorem upperGraphSurfaceIntegrand_eq_zero_of_speed_gt
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) {x : ℝ}
    (hx : ε⁻¹ < Real.sqrt (1 + (deriv (upperGraphHeight K o e) x) ^ 2)) :
    upperGraphSurfaceIntegrand K o e ψ x = 0 := by
  rw [upperGraphSurfaceIntegrand, hsupport, zero_mul]
  rw [coordinate_normalVector_vectorNormalAngle_second]
  exact (inv_lt_comm₀ (Real.sqrt_pos.2 (by positivity)) hε).2 hx

private theorem measurable_vectorNormalAngle : Measurable vectorNormalAngle := by
  unfold vectorNormalAngle
  apply Real.Angle.continuous_coe.measurable.comp
  apply Complex.measurable_arg.comp
  have hp0 : Measurable (fun p : Point ↦ p 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.measurable
  have hp1 : Measurable (fun p : Point ↦ p 1) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 1).continuous.measurable
  have h0 : Measurable (fun p : Point ↦ (p 0 : ℂ)) :=
    Complex.measurable_ofReal.comp hp0
  have h1 : Measurable (fun p : Point ↦ (p 1 : ℂ)) :=
    Complex.measurable_ofReal.comp hp1
  convert h0.add (h1.mul_const Complex.I) using 1
  funext p
  apply Complex.ext <;> simp

private theorem measurable_upperGraphSurfaceIntegrand (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) :
    Measurable (upperGraphSurfaceIntegrand K o e ψ) := by
  unfold upperGraphSurfaceIntegrand
  have hd : Measurable (deriv (upperGraphHeight K o e)) := measurable_deriv _
  have hv : Measurable (fun x ↦ e.symm !₂[-deriv (upperGraphHeight K o e) x, 1]) := by
    fun_prop
  apply (hψ.measurable.comp (measurable_vectorNormalAngle.comp ?_)).mul
    ((measurable_const.add (hd.pow_const 2)).sqrt)
  exact hv

/-- A normal support cutoff gives a uniform bound on the weighted graph density. -/
theorem norm_upperGraphSurfaceIntegrand_le
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) {ε M : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0)
    (hM : ∀ t, ‖ψ t‖ ≤ M) (x : ℝ) :
    ‖upperGraphSurfaceIntegrand K o e ψ x‖ ≤ M * ε⁻¹ := by
  have hM0 : 0 ≤ M := (norm_nonneg (ψ 0)).trans (hM 0)
  let s := Real.sqrt (1 + (deriv (upperGraphHeight K o e) x) ^ 2)
  by_cases hs : s ≤ ε⁻¹
  · rw [upperGraphSurfaceIntegrand, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul (hM _) hs (Real.sqrt_nonneg _) hM0
  · rw [upperGraphSurfaceIntegrand_eq_zero_of_speed_gt K o e ψ hε hsupport
      (lt_of_not_ge hs), norm_zero]
    exact mul_nonneg hM0 (le_of_lt (inv_pos.mpr hε))

/-- The weighted surface integrand of an upper graph is integrable on its
horizontal projection interval. -/
theorem integrable_upperGraphSurfaceIntegrand (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (hψ : Continuous ψ)
    {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) (a b : ℝ) :
    Integrable (upperGraphSurfaceIntegrand K o e ψ) (volume.restrict (Set.Icc a b)) := by
  obtain ⟨t, -, ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hψ.norm.continuousOn
  let M := ‖ψ t‖
  have hM (u : Real.Angle) : ‖ψ u‖ ≤ M := ht trivial
  apply (integrable_const (μ := volume.restrict (Set.Icc a b))
    (c := M * ε⁻¹)).mono'
    (measurable_upperGraphSurfaceIntegrand K o e ψ hψ).aestronglyMeasurable
  exact Eventually.of_forall fun x ↦
    norm_upperGraphSurfaceIntegrand_le K o e ψ hε hsupport hM x

private theorem upperCoordinateGraph_mem_frontier (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ}
    (hx : x ∈ Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2) :
    o + e.symm !₂[x, upperGraphHeight K o e x] ∈ frontier (K : Set Point) := by
  have hxproj : x ∈ horizontalProjection K o e := by
    rw [horizontalProjection_eq_Icc]
    exact hx
  let p := o + e.symm !₂[x, upperGraphHeight K o e x]
  have hpK : p ∈ K := upperGraphHeight_mem K o e hxproj
  rw [mem_frontier_iff_notMem_interior hpK]
  intro hpint
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hpint
  let q := p + (r / 2) • e.symm !₂[0, 1]
  have hqp : q ∈ K := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show q - p = (r / 2) • e.symm !₂[0, 1] by simp [q], norm_smul,
      e.symm.norm_map, EuclideanSpace.norm_eq]
    simp only [norm_div, Real.norm_eq_abs, sq_abs, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow, zero_add, Real.sqrt_one, mul_one]
    rw [abs_of_pos hr]
    linarith))
  have hqfiber : o + e.symm !₂[x, upperGraphHeight K o e x + r / 2] ∈ K := by
    convert hqp using 1
    apply e.injective
    ext i
    fin_cases i
    · simp [p, q, map_add, map_smul]
    · simp [p, q, map_add, map_smul]
      ring
  have hle := (upperGraphHeight_isGreatest K o e hxproj).2 hqfiber
  linarith

/-- Evaluate an angular weight at the upper graph’s normal direction above a point’s abscissa. -/
def upperGraphWeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (p : Point) : ℝ :=
  ψ (vectorNormalAngle (e.symm !₂[
    -deriv (upperGraphHeight K o e) (e (p - o) 0), 1]))

private theorem measurable_upperGraphWeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) :
    Measurable (upperGraphWeight K o e ψ) := by
  unfold upperGraphWeight
  apply hψ.measurable.comp (measurable_vectorNormalAngle.comp ?_)
  have hx : Measurable (fun p : Point ↦ e (p - o) 0) := by fun_prop
  have hd : Measurable (fun p : Point ↦
      deriv (upperGraphHeight K o e) (e (p - o) 0)) :=
    (measurable_deriv _).comp hx
  fun_prop

private theorem integral_restrict_upperCoordinateGraph_eq_integral
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) {a b : ℝ}
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆
      Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2) :
    (∫ p, upperGraphWeight K o e ψ p ∂(Measure.hausdorffMeasure 1).restrict
      ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc a b)) =
      ∫ x in a..b, upperGraphSurfaceIntegrand K o e ψ x := by
  have hlocal : LocallyLipschitzOn (Set.Icc a b) (upperGraphHeight K o e) :=
    (locallyLipschitzOn_upperGraphHeight K o e).mono hsub
  obtain ⟨C, hC⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc hlocal
  rw [MeasureTheory.integral_restrict_coordinateGraph_eq_integral_sqrt_mul hab hC o e
    (measurable_upperGraphWeight K o e ψ hψ)]
  apply intervalIntegral.integral_congr
  intro x _
  unfold upperGraphWeight upperGraphSurfaceIntegrand
  simp only [add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply, Fin.isValue,
    Matrix.cons_val_zero]
  apply mul_comm

private theorem integral_restrict_upperCoordinateGraph_eq_setIntegral
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) {a b : ℝ}
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆
      Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2) :
    (∫ p, upperGraphWeight K o e ψ p ∂(Measure.hausdorffMeasure 1).restrict
      ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc a b)) =
      ∫ x in Set.Icc a b, upperGraphSurfaceIntegrand K o e ψ x := by
  rw [integral_restrict_upperCoordinateGraph_eq_integral K o e ψ hψ hab hsub,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]

private theorem upperCoordinateGraph_image_subset_frontier (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {s : Set ℝ}
    (hs : s ⊆ Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2) :
    (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) '' s ⊆
      frontier (K : Set Point) := by
  rintro _ ⟨x, hx, rfl⟩
  exact upperCoordinateGraph_mem_frontier K o e (hs hx)

private theorem hausdorffMeasure_upperGraph_endpoints_eq_zero (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        ({(horizontalBounds K o e).1, (horizontalBounds K o e).2} : Set ℝ)) = 0 := by
  let _ := MeasureTheory.Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  apply Set.Finite.measure_zero
  exact (Set.toFinite _).image _

private theorem eventually_innerIcc_nonempty {a b : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      a + 1 / ((n : ℝ) + 1) ≤ b - 1 / ((n : ℝ) + 1) := by
  have hevent := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (Iio_mem_nhds (half_pos (sub_pos.mpr hab)))
  exact hevent.mono fun n hn ↦ by linarith

/-- Integrals over the inner upper graph equal integrals over its coordinate interval. -/
theorem eventually_integral_innerUpperGraph_eq_innerIcc
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (hψ : Continuous ψ)
    (hwidth : (horizontalBounds K o e).1 < (horizontalBounds K o e).2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (∫ p, upperGraphWeight K o e ψ p ∂(Measure.hausdorffMeasure 1).restrict
        ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
          Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
            ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)))) =
        ∫ x in Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
          ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)),
          upperGraphSurfaceIntegrand K o e ψ x := by
  filter_upwards [eventually_innerIcc_nonempty hwidth] with n hn
  exact integral_restrict_upperCoordinateGraph_eq_setIntegral K o e ψ hψ hn
    (innerIcc_subset_Ioo _ _ n)

private theorem measurableSet_innerUpperGraph (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (n : ℕ) :
    MeasurableSet
      ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
          ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))) := by
  let s := Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
    ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))
  have hs : s ⊆ Set.Ioo (horizontalBounds K o e).1
      (horizontalBounds K o e).2 := innerIcc_subset_Ioo _ _ n
  have hcont : ContinuousOn (upperGraphHeight K o e) s :=
    ((locallyLipschitzOn_upperGraphHeight K o e).mono hs).continuousOn
  exact (isCompact_Icc.image_of_continuousOn (by fun_prop)).measurableSet

private theorem tendsto_innerUpperGraph_indicator_at_regularPoint
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) {p : Point}
    (hp : p ∈ regularBoundary K)
    (hpend : p ∉ (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
      ({(horizontalBounds K o e).1, (horizontalBounds K o e).2} : Set ℝ))
    (hpirr : p ∉ irregularUpperGraph K o e) :
    Filter.Tendsto (fun n : ℕ ↦
      (((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
          ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))).indicator
            (upperGraphWeight K o e ψ) p)) Filter.atTop
      (nhds (ψ (exteriorNormalAngle K p))) := by
  let a := exteriorNormalAngle K p
  have ha : IsExteriorNormal K p a := by
    dsimp only [a]
    unfold exteriorNormalAngle
    rw [dite_eq_left hp.2]
    exact hp.2.exists.choose_spec
  have hpK : p ∈ K := by
    change p ∈ (K : Set Point)
    rw [← K.isClosed.closure_eq]
    exact frontier_subset_closure hp.1
  by_cases hψa : ψ a = 0
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    by_cases hpn : p ∈ (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
          ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))
    · obtain ⟨x, hx, rfl⟩ := hpn
      have hxint := innerIcc_subset_Ioo (horizontalBounds K o e).1
        (horizontalBounds K o e).2 n hx
      have hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x := by
        by_contra hndiff
        exact hpirr ⟨x, ⟨hxint, hndiff⟩, rfl⟩
      have hmem : (o + e.symm !₂[x, upperGraphHeight K o e x]) ∈
          (fun y ↦ o + e.symm !₂[y, upperGraphHeight K o e y] : ℝ → Point) ''
            Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
              ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)) := ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hmem]
      unfold upperGraphWeight
      simp only [add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply, Fin.isValue,
        Matrix.cons_val_zero]
      rw [← exteriorNormalAngle_upperGraph_eq K hK o e hxint hdiff]
    · change ψ a = _
      rw [Set.indicator]
      simp only [hpn, ↓reduceIte]
      exact hψa
  · have hcoord : ε ≤ e (normalVector a) 1 := by
      apply le_of_not_gt
      exact fun h ↦ hψa (hsupport a h)
    have hpos : 0 < e (normalVector a) 1 := hε.trans_le hcoord
    have hgraph := eq_upperCoordinateGraph_of_isExteriorNormal_of_pos K o e hpK ha hpos
    let x := e (p - o) 0
    have hxproj : x ∈ horizontalProjection K o e := ⟨p, hpK, rfl⟩
    have hxIcc : x ∈ Set.Icc (horizontalBounds K o e).1
        (horizontalBounds K o e).2 := by
      rw [← horizontalProjection_eq_Icc]
      exact hxproj
    have hxneleft : x ≠ (horizontalBounds K o e).1 := by
      intro hx
      apply hpend
      refine ⟨x, by simp [hx], ?_⟩
      exact hgraph.symm
    have hxneright : x ≠ (horizontalBounds K o e).2 := by
      intro hx
      apply hpend
      refine ⟨x, by simp [hx], ?_⟩
      exact hgraph.symm
    have hxint : x ∈ Set.Ioo (horizontalBounds K o e).1
        (horizontalBounds K o e).2 :=
      ⟨lt_of_le_of_ne hxIcc.1 (Ne.symm hxneleft), lt_of_le_of_ne hxIcc.2 hxneright⟩
    have hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x := by
      by_contra hndiff
      apply hpirr
      refine ⟨x, ⟨hxint, hndiff⟩, ?_⟩
      exact hgraph.symm
    have hweight : upperGraphWeight K o e ψ p = ψ a := by
      unfold upperGraphWeight
      dsimp only [x]
      have haeq : a = vectorNormalAngle
          (e.symm !₂[-deriv (upperGraphHeight K o e) (e (p - o) 0), 1]) := by
        have he := exteriorNormalAngle_upperGraph_eq K hK o e hxint hdiff
        dsimp only [x] at he
        calc
          a = exteriorNormalAngle K p := rfl
          _ = exteriorNormalAngle K
              (o + e.symm !₂[e (p - o) 0, upperGraphHeight K o e (e (p - o) 0)]) :=
            congrArg (exteriorNormalAngle K) hgraph
          _ = _ := he
      rw [haeq]
    have hev := eventually_mem_innerIcc_of_mem_Ioo hxint
    apply tendsto_const_nhds.congr'
    exact hev.mono fun n hn ↦ by
      have hmem : p ∈ (fun y ↦ o + e.symm !₂[y, upperGraphHeight K o e y] : ℝ → Point) ''
          Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
            ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)) := ⟨x, hn, hgraph.symm⟩
      change ψ (exteriorNormalAngle K p) = _
      simp only [Set.indicator, hmem, ↓reduceIte, hweight]
      rfl

/-- Weighted integrals over compact inner upper graphs converge to the weighted
integral over the full frontier. -/
theorem tendsto_integral_innerUpperGraph
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (hψ : Continuous ψ)
    {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) :
    Filter.Tendsto (fun n : ℕ ↦
      ∫ p, upperGraphWeight K o e ψ p ∂(Measure.hausdorffMeasure 1).restrict
        ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
          Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
            ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)))) Filter.atTop
      (nhds (∫ p in frontier (K : Set Point), ψ (exteriorNormalAngle K p)
        ∂Measure.hausdorffMeasure 1)) := by
  let μ : Measure Point := Measure.hausdorffMeasure 1
  let t := frontier (K : Set Point)
  let g : ℕ → Set Point := fun n ↦
    (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
      Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
        ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))
  obtain ⟨u, -, hu⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hψ.norm.continuousOn
  let M := ‖ψ u‖
  have hM (v : Real.Angle) : ‖ψ v‖ ≤ M := hu trivial
  have hM0 : 0 ≤ M := norm_nonneg _
  have hgt (n : ℕ) : g n ⊆ t :=
    upperCoordinateGraph_image_subset_frontier K o e
      ((innerIcc_subset_Ioo _ _ n).trans Set.Ioo_subset_Icc_self)
  have hgmeas (n : ℕ) : MeasurableSet (g n) := measurableSet_innerUpperGraph K o e n
  have hFmeas (n : ℕ) : AEStronglyMeasurable
      ((g n).indicator (upperGraphWeight K o e ψ)) μ :=
    (measurable_upperGraphWeight K o e ψ hψ).aestronglyMeasurable.indicator (hgmeas n)
  have hbound (n : ℕ) : ∀ᵐ p ∂μ,
      ‖(g n).indicator (upperGraphWeight K o e ψ) p‖ ≤ t.indicator (fun _ ↦ M) p :=
    Filter.Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ g n
      · have hpt := hgt n hp
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hpt]
        exact hM _
      · rw [Set.indicator]
        simp only [hp, ↓reduceIte, norm_zero]
        by_cases hpt : p ∈ t <;> simp [hpt, hM0]
  have hboundInt : Integrable (t.indicator fun _ ↦ M) μ := by
    apply MeasureTheory.IntegrableOn.integrable_indicator
    · exact MeasureTheory.integrableOn_const
        (lt_top_iff_ne_top.mp (K.hausdorffMeasure_frontier_lt_top hK))
    · exact measurableSet_frontier
  have hae : t =ᵐ[μ] regularBoundary K := by
    rw [ae_eq_set]
    exact ⟨hausdorffMeasure_irregularBoundary_eq_zero K hK,
      measure_mono_null (fun _ hp ↦ (hp.2 hp.1.1).elim) measure_empty⟩
  have hpreg : ∀ᵐ p ∂μ, p ∈ t → p ∈ regularBoundary K := by
    filter_upwards [hae] with p hp
    exact fun hpt ↦ hp.mp hpt
  have hpend : ∀ᵐ p ∂μ, p ∉
      (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        ({(horizontalBounds K o e).1, (horizontalBounds K o e).2} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp (hausdorffMeasure_upperGraph_endpoints_eq_zero K o e)
  have hpirr : ∀ᵐ p ∂μ, p ∉ irregularUpperGraph K o e :=
    measure_eq_zero_iff_ae_notMem.mp (hausdorffMeasure_irregularUpperGraph_eq_zero K o e)
  have hlim : ∀ᵐ p ∂μ, Filter.Tendsto
      (fun n ↦ (g n).indicator (upperGraphWeight K o e ψ) p) Filter.atTop
      (nhds (t.indicator (fun p ↦ ψ (exteriorNormalAngle K p)) p)) := by
    filter_upwards [hpreg, hpend, hpirr] with p hpreg hpend hpirr
    by_cases hpt : p ∈ t
    · rw [Set.indicator_of_mem hpt]
      exact tendsto_innerUpperGraph_indicator_at_regularPoint K hK o e ψ hε hsupport
        (hpreg hpt) hpend hpirr
    · simp only [Set.indicator, hpt, ↓reduceIte]
      apply tendsto_const_nhds.congr'
      filter_upwards [] with n
      have hpgn : p ∉ g n := fun h ↦ hpt (hgt n h)
      simp [hpgn]
  have ht := MeasureTheory.tendsto_integral_of_dominated_convergence (μ := μ)
    (t.indicator fun _ ↦ M) hFmeas hboundInt hbound hlim
  have htarget : (∫ p, t.indicator (fun p ↦ ψ (exteriorNormalAngle K p)) p ∂μ) =
      ∫ p in t, ψ (exteriorNormalAngle K p) ∂μ := by
    rw [MeasureTheory.integral_indicator measurableSet_frontier]
  rw [← htarget]
  simpa only [μ, g, MeasureTheory.integral_indicator, hgmeas] using ht

/-- A planar convex body with nonempty interior has distinct horizontal bounds
in every isometric coordinate frame. -/
theorem horizontalBounds_lt_of_interior_nonempty (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    (horizontalBounds K o e).1 < (horizontalBounds K o e).2 := by
  obtain ⟨z, hz⟩ := hK
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  let v := e.symm (normalVector 0)
  let q := z + (ε / 2) • v
  have hq : q ∈ K := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show q - z = (ε / 2) • v by simp [q], norm_smul]
    simp only [v, e.symm.norm_map, norm_normalVector, mul_one, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith))
  have hzI : e (z - o) 0 ∈ Set.Icc (horizontalBounds K o e).1
      (horizontalBounds K o e).2 := by
    rw [← horizontalProjection_eq_Icc]
    exact ⟨z, interior_subset hz, rfl⟩
  have hqI : e (q - o) 0 ∈ Set.Icc (horizontalBounds K o e).1
      (horizontalBounds K o e).2 := by
    rw [← horizontalProjection_eq_Icc]
    exact ⟨q, hq, rfl⟩
  have hcoord : e (q - o) 0 = e (z - o) 0 + ε / 2 := by
    rw [show q - o = (z - o) + (ε / 2) • v by simp [q]; module]
    simp [v, normalVector, frame]
  linarith [hzI.1, hqI.2]

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
# Analysis / Surface Measure / Construction
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem surfaceAreaMeasure_construction (K : ConvexBody Point) :
    IsFiniteMeasure (surfaceAreaMeasure K) ∧
    ((K : Set Point).Subsingleton → surfaceAreaMeasure K = 0) ∧
    (∀ d, IsSegmentPresentation K d → surfaceAreaMeasure K =
      ENNReal.ofReal (dist d.1 d.2.1) •
        (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + ((Real.pi : ℝ) : Real.Angle)))) ∧
    ((interior (K : Set Point)).Nonempty →
      Measure.hausdorffMeasure 1 (frontier (K : Set Point)) < ⊤ ∧
      Measure.hausdorffMeasure 1 (frontier (K : Set Point) \ regularBoundary K) = 0 ∧
      ∀ ν : Point → Real.Angle, (∀ p ∈ regularBoundary K, ν p = exteriorNormalAngle K p) →
        surfaceAreaMeasure K = Measure.map ν
          ((Measure.hausdorffMeasure 1).restrict (frontier (K : Set Point)))) ∧
    (∀ (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ), Continuous ψ →
      ∀ ε : ℝ, 0 < ε → (∀ t, e (normalVector t) 1 < ε → ψ t = 0) →
      ((horizontalBounds K o e).1 < (horizontalBounds K o e).2 →
        Integrable (upperGraphSurfaceIntegrand K o e ψ)
          (volume.restrict (Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2)) ∧
        (∫ t, ψ t ∂surfaceAreaMeasure K) =
          ∫ x in Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2,
            upperGraphSurfaceIntegrand K o e ψ x) ∧
      ((horizontalBounds K o e).1 = (horizontalBounds K o e).2 →
        (∫ t, ψ t ∂surfaceAreaMeasure K) = 0)) := by
  by_cases hsub : (K : Set Point).Subsingleton
  · refine ⟨isFiniteMeasure_surfaceAreaMeasure_of_subsingleton K hsub,
      fun _ ↦ surfaceAreaMeasure_eq_zero_of_subsingleton K hsub, ?_, ?_, ?_⟩
    · intro d hd
      exact (not_subsingleton_of_isSegmentPresentation K hd hsub).elim
    · intro hint
      obtain ⟨p, hp⟩ := K.nonempty
      have hset : (K : Set Point) = {p} :=
        Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun x hx ↦ hsub hx hp⟩
      rw [hset, interior_singleton] at hint
      exact hint.ne_empty rfl |>.elim
    · intro o e ψ _ ε _ _
      have hbounds := horizontalBounds_eq_of_subsingleton K hsub o e
      constructor
      · intro hlt
        exact (hlt.ne hbounds).elim
      · intro _
        exact surfaceAreaMeasure_integral_eq_zero_of_subsingleton K hsub ψ
  · by_cases hint : (interior (K : Set Point)).Nonempty
    · refine ⟨isFiniteMeasure_surfaceAreaMeasure_of_interior_nonempty K hint,
        fun hs ↦ (not_subsingleton_of_interior_nonempty K hint hs).elim, ?_, ?_, ?_⟩
      · intro d hd
        exact (not_exists_segmentPresentation_of_interior_nonempty K hint ⟨d, hd⟩).elim
      · intro _
        refine ⟨K.hausdorffMeasure_frontier_lt_top hint, ?_, ?_⟩
        · exact hausdorffMeasure_irregularBoundary_eq_zero K hint
        · intro ν hν
          exact surfaceAreaMeasure_eq_map_frontier_of_eq_on_regularBoundary K hint ν hν
      · intro o e ψ hψ ε hε hsupport
        constructor
        · intro hwidth
          have hintg := integrable_upperGraphSurfaceIntegrand K o e ψ hψ hε hsupport
            (horizontalBounds K o e).1 (horizontalBounds K o e).2
          refine ⟨hintg, ?_⟩
          rw [surfaceAreaMeasure_eq_map_frontier_of_eq_on_regularBoundary K hint
            (exteriorNormalAngle K) (fun _ _ ↦ rfl)]
          rw [MeasureTheory.integral_map]
          · apply tendsto_nhds_unique
              (tendsto_integral_innerUpperGraph K hint o e ψ hψ hε hsupport)
            apply (tendsto_integral_innerIcc hintg).congr'
            filter_upwards [eventually_integral_innerUpperGraph_eq_innerIcc
              K o e ψ hψ hwidth] with n hn
            exact hn.symm
          · have hae : frontier (K : Set Point) =ᵐ[Measure.hausdorffMeasure 1]
                regularBoundary K := by
              rw [ae_eq_set]
              exact ⟨hausdorffMeasure_irregularBoundary_eq_zero K hint,
                measure_mono_null (fun _ hp ↦ (hp.2 hp.1.1).elim) measure_empty⟩
            have hrestrict : (Measure.hausdorffMeasure 1).restrict
                (frontier (K : Set Point)) =
                (Measure.hausdorffMeasure 1).restrict (regularBoundary K) :=
              Measure.restrict_congr_set hae
            rw [hrestrict]
            exact aemeasurable_exteriorNormalAngle_restrict_regularBoundary K
              (Measure.hausdorffMeasure 1)
          · exact hψ.aestronglyMeasurable
        · intro hwidth
          exact ((horizontalBounds_lt_of_interior_nonempty K hint o e).ne hwidth).elim
    · have hinterior : interior (K : Set Point) = ∅ := Set.not_nonempty_iff_eq_empty.mp hint
      have hseg := exists_segmentPresentation_of_interior_empty K hsub hinterior
      refine ⟨isFiniteMeasure_surfaceAreaMeasure_of_segmentPresentation K hseg.choose_spec,
        fun hs ↦ (hsub hs).elim, ?_, ?_, ?_⟩
      · intro d hd
        exact surfaceAreaMeasure_eq_segmentPresentation K d hd
      · exact fun hi ↦ (hint hi).elim
      · intro o e ψ _ ε hε hsupport
        constructor
        · intro hbounds
          exact segment_graph_formula K o e ψ hε hsupport hseg.choose hseg.choose_spec hbounds
        · intro hbounds
          exact segment_integral_eq_zero_of_horizontalBounds_eq K o e ψ ε hε hsupport
            hseg.choose hseg.choose_spec hbounds

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
# Analysis / Surface Measure / Graph Convergence
-/

@[expose] public section

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

namespace MovingSofa

/-- The angle of a planar vector varies continuously away from zero. -/
theorem continuousAt_vectorNormalAngle {p : Point} (hp : p ≠ 0) :
    ContinuousAt vectorNormalAngle p := by
  have hz : (⟨p 0, p 1⟩ : ℂ) ≠ 0 := by
    intro h
    apply hp
    ext i
    fin_cases i
    · exact congrArg Complex.re h
    · exact congrArg Complex.im h
  have hc : Continuous (fun q : Point ↦ (⟨q 0, q 1⟩ : ℂ)) := by
    have h : Continuous (fun q : Point ↦ (q 0 : ℂ) + (q 1 : ℂ) * Complex.I) := by
      fun_prop
    convert h using 1
    funext q
    apply Complex.ext <;> simp
  exact (Complex.continuousAt_arg_coe_angle hz).comp
    (f := fun q : Point ↦ (⟨q 0, q 1⟩ : ℂ)) hc.continuousAt

/-- The weighted upper-graph surface density is continuous as a function of slope. -/
theorem continuous_surfaceDensity_of_slope (e : Point ≃ₗᵢ[ℝ] Point)
    {ψ : Real.Angle → ℝ} (hψ : Continuous ψ) :
    Continuous (fun r : ℝ ↦ ψ (vectorNormalAngle (e.symm !₂[-r, 1])) *
      Real.sqrt (1 + r ^ 2)) := by
  have hv : Continuous (fun r : ℝ ↦ vectorNormalAngle (e.symm !₂[-r, 1])) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    have hne : e.symm !₂[-r, 1] ≠ 0 := by
      intro h
      have h1 := congrArg (fun p : Point ↦ e p 1) h
      simp at h1
    apply (continuousAt_vectorNormalAngle hne).comp
      (f := fun r : ℝ ↦ e.symm !₂[-r, 1])
    fun_prop
  exact (hψ.comp hv).mul (by fun_prop)

private theorem ae_differentiableAt_upperGraphHeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    ∀ᵐ x : ℝ, x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2 →
      DifferentiableAt ℝ (upperGraphHeight K o e) x := by
  let a := (horizontalBounds K o e).1
  let b := (horizontalBounds K o e).2
  let δ : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have hδpos (m : ℕ) : 0 < δ m := by positivity
  have hcompact (m : ℕ) : IsCompact (Set.Icc (a + δ m) (b - δ m)) := isCompact_Icc
  have hsub (m : ℕ) : Set.Icc (a + δ m) (b - δ m) ⊆ Set.Ioo a b := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_add_of_pos_right a (hδpos m)) hx.1,
      lt_of_le_of_lt hx.2 (sub_lt_self b (hδpos m))⟩
  have hae (m : ℕ) : ∀ᵐ x : ℝ,
      x ∈ Set.Ioo (a + δ m) (b - δ m) →
        DifferentiableAt ℝ (upperGraphHeight K o e) x := by
    obtain ⟨C, hC⟩ :=
      ((locallyLipschitzOn_upperGraphHeight K o e).mono (hsub m)).exists_lipschitzOnWith_of_compact
        (hcompact m)
    filter_upwards [hC.ae_differentiableWithinAt_of_mem_of_real] with x hdiff hx
    exact (hdiff ⟨hx.1.le, hx.2.le⟩).differentiableAt (Icc_mem_nhds hx.1 hx.2)
  have hall : ∀ᵐ x : ℝ, ∀ m, x ∈ Set.Ioo (a + δ m) (b - δ m) →
      DifferentiableAt ℝ (upperGraphHeight K o e) x :=
    MeasureTheory.ae_all_iff.mpr hae
  filter_upwards [hall] with x hxall hx
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hevent : ∀ᶠ m in atTop, δ m < x - a ∧ δ m < b - x :=
    ((hδ.eventually_lt_const (sub_pos.mpr hx.1)).and
      (hδ.eventually_lt_const (sub_pos.mpr hx.2)))
  obtain ⟨m, hm⟩ := hevent.exists
  apply hxall m
  constructor <;> linarith [hm.1, hm.2]

private theorem exists_tendsto_points_of_mem_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) {p : Point} (hp : p ∈ L) :
    ∃ q : ℕ → Point, (∀ n, q n ∈ K n) ∧ Tendsto q atTop (𝓝 p) := by
  have hnear (n : ℕ) : ∃ q ∈ (K n : Set Point),
      dist p q < Metric.hausdorffDist (K n : Set Point) (L : Set Point) +
        1 / ((n : ℝ) + 1) := by
    obtain ⟨q, hq, hd⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt'
      (r := Metric.hausdorffDist (K n : Set Point) (L : Set Point) +
        1 / ((n : ℝ) + 1)) hp
      (by linarith [show 0 < 1 / ((n : ℝ) + 1) by positivity])
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
    exact ⟨q, hq, by simpa [dist_comm] using hd⟩
  choose q hqK hqdist using hnear
  refine ⟨q, hqK, ?_⟩
  have hsum : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point) + 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [add_zero] using hlim.add tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hsum
  intro n
  simpa [dist_comm] using (hqdist n).le

private theorem exists_horizontal_side_points (L : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ}
    (hx : x ∈ Set.Ioo (horizontalBounds L o e).1 (horizontalBounds L o e).2) :
    ∃ l ∈ (L : Set Point), ∃ r ∈ (L : Set Point),
      e (l - o) 0 < x ∧ x < e (r - o) 0 := by
  let a := (horizontalBounds L o e).1
  let b := (horizontalBounds L o e).2
  have hlcoord : (a + x) / 2 ∈ horizontalProjection L o e := by
    rw [horizontalProjection_eq_Icc]
    dsimp [a, b]
    constructor <;> linarith [hx.1, hx.2]
  have hrcoord : (x + b) / 2 ∈ horizontalProjection L o e := by
    rw [horizontalProjection_eq_Icc]
    dsimp [a, b]
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨l, hl, hleq⟩ := hlcoord
  obtain ⟨r, hr, hreq⟩ := hrcoord
  refine ⟨l, hl, r, hr, ?_, ?_⟩
  · change e (l - o) 0 = (a + x) / 2 at hleq
    rw [hleq]
    dsimp [a]
    linarith [hx.1]
  · change e (r - o) 0 = (x + b) / 2 at hreq
    rw [hreq]
    dsimp [b]
    linarith [hx.2]

/-- Points on an interior horizontal fiber can be approximated within the same fibers. -/
theorem exists_tendsto_points_with_horizontal_coordinate
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {p : Point} (hp : p ∈ L)
    (hpint : e (p - o) 0 ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2) :
    ∃ q : ℕ → Point, (∀ n, q n ∈ K n) ∧ Tendsto q atTop (𝓝 p) ∧
      ∀ᶠ n in atTop, e (q n - o) 0 = e (p - o) 0 := by
  let c : Point → ℝ := fun z ↦ e (z - o) 0
  have hc : Continuous c := by
    exact (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp
      (e.continuous.comp (continuous_id.sub continuous_const))
  have hc_lineMap (a b : Point) (t : ℝ) :
      c (AffineMap.lineMap a b t) = (1 - t) * c a + t * c b := by
    dsimp [c]
    rw [AffineMap.lineMap_apply_module]
    simp only [map_sub, map_add, map_smul, PiLp.sub_apply, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
    ring
  obtain ⟨l, hlL, r, hrL, hl, hr⟩ := exists_horizontal_side_points L o e hpint
  obtain ⟨pn, hpnK, hpn⟩ := exists_tendsto_points_of_mem_of_hausdorffDist K L hlim hp
  obtain ⟨ln, hlnK, hln⟩ := exists_tendsto_points_of_mem_of_hausdorffDist K L hlim hlL
  obtain ⟨rn, hrnK, hrn⟩ := exists_tendsto_points_of_mem_of_hausdorffDist K L hlim hrL
  let x := c p
  let tR : ℕ → ℝ := fun n ↦ (x - c (pn n)) / (c (rn n) - c (pn n))
  let tL : ℕ → ℝ := fun n ↦ (c (pn n) - x) / (c (pn n) - c (ln n))
  let qR : ℕ → Point := fun n ↦ AffineMap.lineMap (pn n) (rn n) (tR n)
  let qL : ℕ → Point := fun n ↦ AffineMap.lineMap (pn n) (ln n) (tL n)
  let corrected : ℕ → Point := fun n ↦ if c (pn n) ≤ x then qR n else qL n
  let good : ℕ → Prop := fun n ↦ c (ln n) < x ∧ x < c (rn n)
  let q : ℕ → Point := fun n ↦ if good n then corrected n else pn n
  have hcp : Tendsto (fun n ↦ c (pn n)) atTop (𝓝 (c p)) := (hc.tendsto p).comp hpn
  have hcl : Tendsto (fun n ↦ c (ln n)) atTop (𝓝 (c l)) := (hc.tendsto l).comp hln
  have hcr : Tendsto (fun n ↦ c (rn n)) atTop (𝓝 (c r)) := (hc.tendsto r).comp hrn
  have htR : Tendsto tR atTop (𝓝 0) := by
    have hden : c r - c p ≠ 0 := by
      dsimp [c] at hr
      linarith
    have hxlim : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x) := tendsto_const_nhds
    change Tendsto ((fun n ↦ x - c (pn n)) /
      fun n ↦ c (rn n) - c (pn n)) atTop (𝓝 0)
    simpa [x] using (hxlim.sub hcp).div (hcr.sub hcp) hden
  have htL : Tendsto tL atTop (𝓝 0) := by
    have hden : c p - c l ≠ 0 := by
      dsimp [c] at hl
      linarith
    have hxlim : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x) := tendsto_const_nhds
    change Tendsto ((fun n ↦ c (pn n) - x) /
      fun n ↦ c (pn n) - c (ln n)) atTop (𝓝 0)
    simpa [x] using (hcp.sub hxlim).div (hcp.sub hcl) hden
  have hqR : Tendsto qR atTop (𝓝 p) := by
    simpa [qR] using hpn.lineMap hrn htR
  have hqL : Tendsto qL atTop (𝓝 p) := by
    simpa [qL] using hpn.lineMap hln htL
  have hcorrected : Tendsto corrected atTop (𝓝 p) := by
    exact hqR.if' hqL
  have hq : Tendsto q atTop (𝓝 p) := by
    exact hcorrected.if' hpn
  have hgood : ∀ᶠ n in atTop, good n := by
    filter_upwards [hcl.eventually_lt tendsto_const_nhds hl,
      tendsto_const_nhds.eventually_lt hcr hr] with n hnl hnr
    exact ⟨hnl, hnr⟩
  refine ⟨q, ?_, hq, ?_⟩
  · intro n
    by_cases hgn : good n
    · simp only [q, hgn, ite_true, corrected]
      dsimp [good] at hgn
      by_cases hpnx : c (pn n) ≤ x
      · simp only [hpnx, ite_true, qR]
        apply (K n).convex.lineMap_mem (hpnK n) (hrnK n)
        constructor
        · exact div_nonneg (sub_nonneg.mpr hpnx) (sub_nonneg.mpr (le_trans hpnx hgn.2.le))
        · apply (div_le_one (sub_pos.mpr (lt_of_le_of_lt hpnx hgn.2))).mpr
          linarith
      · simp only [hpnx, ite_false, qL]
        apply (K n).convex.lineMap_mem (hpnK n) (hlnK n)
        constructor
        · exact div_nonneg (sub_nonneg.mpr (le_of_not_ge hpnx))
            (sub_nonneg.mpr (le_trans hgn.1.le (le_of_not_ge hpnx)))
        · apply (div_le_one (sub_pos.mpr (lt_of_lt_of_le hgn.1 (le_of_not_ge hpnx)))).mpr
          linarith
    · simp [q, hgn, hpnK n]
  · filter_upwards [hgood] with n hgn
    simp only [q, hgn, ite_true, corrected]
    dsimp [good] at hgn
    by_cases hpnx : c (pn n) ≤ x
    · simp only [hpnx, ite_true, qR, tR]
      rw [show e (AffineMap.lineMap (pn n) (rn n)
          ((x - c (pn n)) / (c (rn n) - c (pn n))) - o) 0 =
          c (AffineMap.lineMap (pn n) (rn n)
            ((x - c (pn n)) / (c (rn n) - c (pn n)))) by rfl]
      rw [hc_lineMap]
      change _ = x
      field_simp [ne_of_gt (sub_pos.mpr (lt_of_le_of_lt hpnx hgn.2))]
      ring
    · simp only [hpnx, ite_false, qL, tL]
      rw [show e (AffineMap.lineMap (pn n) (ln n)
          ((c (pn n) - x) / (c (pn n) - c (ln n))) - o) 0 =
          c (AffineMap.lineMap (pn n) (ln n)
            ((c (pn n) - x) / (c (pn n) - c (ln n)))) by rfl]
      rw [hc_lineMap]
      change _ = x
      field_simp [ne_of_gt (sub_pos.mpr (lt_of_lt_of_le hgn.1 (le_of_not_ge hpnx)))]
      ring

/-- A varying point of the approximating bodies is asymptotically close to the limit body. -/
private theorem exists_points_in_limit_tendsto_dist_zero
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (p : ℕ → Point) (hp : ∀ n, p n ∈ K n) :
    ∃ q : ℕ → Point, (∀ n, q n ∈ L) ∧
      Tendsto (fun n ↦ dist (p n) (q n)) atTop (𝓝 0) := by
  have hnear (n : ℕ) : ∃ q ∈ (L : Set Point),
      dist (p n) q < Metric.hausdorffDist (K n : Set Point) (L : Set Point) +
        1 / ((n : ℝ) + 1) := by
    obtain ⟨q, hq, hd⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
      (r := Metric.hausdorffDist (K n : Set Point) (L : Set Point) +
        1 / ((n : ℝ) + 1)) (hp n)
      (by linarith [show 0 < 1 / ((n : ℝ) + 1) by positivity])
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
    exact ⟨q, hq, hd⟩
  choose q hqL hqdist using hnear
  refine ⟨q, hqL, ?_⟩
  have hsum : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point) + 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [add_zero] using hlim.add tendsto_one_div_add_atTop_nhds_zero_nat
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hsum
  exact fun n ↦ (hqdist n).le

/-- Upper graph heights converge at every interior point of the limit projection. -/
theorem tendsto_upperGraphHeight_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {x : ℝ} (hx : x ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2) :
    Tendsto (fun n ↦ upperGraphHeight (K n) o e x) atTop
      (𝓝 (upperGraphHeight L o e x)) := by
  classical
  let cx : Point → ℝ := fun p ↦ e (p - o) 0
  let cy : Point → ℝ := fun p ↦ e (p - o) 1
  have reconstruct (p : Point) : o + e.symm !₂[cx p, cy p] = p := by
    dsimp [cx, cy]
    rw [← e.injective.eq_iff]
    ext i
    fin_cases i <;> simp
  have hxproj : x ∈ horizontalProjection L o e := by
    rw [horizontalProjection_eq_Icc]
    exact ⟨hx.1.le, hx.2.le⟩
  let pTop := o + e.symm !₂[x, upperGraphHeight L o e x]
  have hpTop : pTop ∈ L := upperGraphHeight_mem L o e hxproj
  have hcxTop : cx pTop = x := by simp [cx, pTop]
  have hcyTop : cy pTop = upperGraphHeight L o e x := by simp [cy, pTop]
  have hpTopInt : cx pTop ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 := by simpa [hcxTop] using hx
  obtain ⟨q, hqK, hq, hqx⟩ :=
    exists_tendsto_points_with_horizontal_coordinate K L hlim o e hpTop hpTopInt
  have hcyq : Tendsto (fun n ↦ cy (q n)) atTop
      (𝓝 (upperGraphHeight L o e x)) := by
    have hcy : Continuous cy := by
      exact (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp
        (e.continuous.comp (continuous_id.sub continuous_const))
    change Tendsto (cy ∘ q) atTop (𝓝 (upperGraphHeight L o e x))
    simpa [hcyTop] using (hcy.tendsto pTop).comp hq
  have hqcx : ∀ᶠ n in atTop, cx (q n) = x := by
    filter_upwards [hqx] with n hnx
    dsimp [cx]
    rw [hnx]
    exact hcxTop
  have hqproj : ∀ᶠ n in atTop, x ∈ horizontalProjection (K n) o e := by
    filter_upwards [hqcx] with n hnx
    refine ⟨q n, hqK n, ?_⟩
    exact hnx
  let z : ℕ → Point := fun n ↦ if hn : x ∈ horizontalProjection (K n) o e then
    o + e.symm !₂[x, upperGraphHeight (K n) o e x] else q n
  have hzK (n : ℕ) : z n ∈ K n := by
    dsimp [z]
    split_ifs with hn
    · exact upperGraphHeight_mem (K n) o e hn
    · exact hqK n
  have hzeq : z =ᶠ[atTop]
      fun n ↦ o + e.symm !₂[x, upperGraphHeight (K n) o e x] := by
    filter_upwards [hqproj] with n hn
    simp [z, hn]
  obtain ⟨w, hwL, hd⟩ := exists_points_in_limit_tendsto_dist_zero K L hlim z hzK
  have hsub : Tendsto (fun n ↦ z n - w n) atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa [dist_eq_norm] using hd
  have hdx : Tendsto (fun n ↦ cx (z n) - cx (w n)) atTop (𝓝 0) := by
    have heval : Continuous (fun v : Point ↦ e v 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp e.continuous
    rw [show (fun n ↦ cx (z n) - cx (w n)) =
        fun n ↦ e (z n - w n) 0 by
      funext n
      simp [cx]]
    change Tendsto ((fun v : Point ↦ e v 0) ∘ fun n ↦ z n - w n) atTop (𝓝 0)
    simpa only [map_zero, PiLp.zero_apply] using (heval.tendsto 0).comp hsub
  have hdy : Tendsto (fun n ↦ cy (z n) - cy (w n)) atTop (𝓝 0) := by
    have heval : Continuous (fun v : Point ↦ e v 1) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp e.continuous
    rw [show (fun n ↦ cy (z n) - cy (w n)) =
        fun n ↦ e (z n - w n) 1 by
      funext n
      simp [cy]]
    change Tendsto ((fun v : Point ↦ e v 1) ∘ fun n ↦ z n - w n) atTop (𝓝 0)
    simpa only [map_zero, PiLp.zero_apply] using (heval.tendsto 0).comp hsub
  have hcxz : Tendsto (fun n ↦ cx (z n)) atTop (𝓝 x) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hzeq] with n hn
    rw [hn]
    simp [cx]
  have hcxw : Tendsto (fun n ↦ cx (w n)) atTop (𝓝 x) := by
    have h := hcxz.sub hdx
    convert h using 1 <;> simp
  have hgL : Tendsto (fun n ↦ upperGraphHeight L o e (cx (w n))) atTop
      (𝓝 (upperGraphHeight L o e x)) := by
    have hcont : ContinuousAt (upperGraphHeight L o e) x :=
      (locallyLipschitzOn_upperGraphHeight L o e).continuousOn.continuousAt
        (isOpen_Ioo.mem_nhds hx)
    exact hcont.tendsto.comp hcxw
  have hlower : ∀ᶠ n in atTop,
      cy (q n) ≤ upperGraphHeight (K n) o e x := by
    filter_upwards [hqcx] with n hnx
    apply (upperGraphHeight_isGreatest (K n) o e (by
      exact ⟨q n, hqK n, hnx⟩)).2
    change o + e.symm !₂[x, cy (q n)] ∈ K n
    rw [show o + e.symm !₂[x, cy (q n)] = q n by
      calc
        o + e.symm !₂[x, cy (q n)] = o + e.symm !₂[cx (q n), cy (q n)] := by
          rw [hnx]
        _ = q n := reconstruct (q n)]
    exact hqK n
  have hupper : ∀ᶠ n in atTop,
      upperGraphHeight (K n) o e x ≤
        upperGraphHeight L o e (cx (w n)) + (cy (z n) - cy (w n)) := by
    filter_upwards [hzeq] with n hzn
    have hwproj : cx (w n) ∈ horizontalProjection L o e :=
      ⟨w n, hwL n, rfl⟩
    have hwy : cy (w n) ≤ upperGraphHeight L o e (cx (w n)) := by
      apply (upperGraphHeight_isGreatest L o e hwproj).2
      change o + e.symm !₂[cx (w n), cy (w n)] ∈ L
      rw [reconstruct (w n)]
      exact hwL n
    have hzy : cy (z n) = upperGraphHeight (K n) o e x := by
      rw [hzn]
      simp [cy]
    rw [← hzy]
    linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hcyq
    (by simpa using hgL.add hdy) hlower hupper

private theorem eventually_mem_horizontalProjection_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {x : ℝ} (hx : x ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2) :
    ∀ᶠ n in atTop, x ∈ horizontalProjection (K n) o e := by
  have hxproj : x ∈ horizontalProjection L o e := by
    rw [horizontalProjection_eq_Icc]
    exact ⟨hx.1.le, hx.2.le⟩
  let p := o + e.symm !₂[x, upperGraphHeight L o e x]
  have hp : p ∈ L := upperGraphHeight_mem L o e hxproj
  have hpcoord : e (p - o) 0 = x := by simp [p]
  have hpint : e (p - o) 0 ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 := by
    rw [hpcoord]
    exact hx
  obtain ⟨q, hqK, -, hqx⟩ :=
    exists_tendsto_points_with_horizontal_coordinate K L hlim o e hp hpint
  filter_upwards [hqx] with n hn
  exact ⟨q n, hqK n, hn.trans hpcoord⟩

/-- Upper graph surface densities converge almost everywhere on the interior limit projection. -/
theorem ae_tendsto_upperGraphSurfaceIntegrand_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {ψ : Real.Angle → ℝ} (hψ : Continuous ψ) :
    ∀ᵐ x : ℝ, x ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 →
        Tendsto (fun n ↦ upperGraphSurfaceIntegrand (K n) o e ψ x) atTop
          (𝓝 (upperGraphSurfaceIntegrand L o e ψ x)) := by
  have haeK : ∀ᵐ x : ℝ, ∀ n,
      x ∈ Set.Ioo (horizontalBounds (K n) o e).1 (horizontalBounds (K n) o e).2 →
        DifferentiableAt ℝ (upperGraphHeight (K n) o e) x :=
    MeasureTheory.ae_all_iff.mpr fun n ↦ ae_differentiableAt_upperGraphHeight (K n) o e
  have haeL := ae_differentiableAt_upperGraphHeight L o e
  filter_upwards [haeK, haeL] with x hdiffK hdiffL hx
  let left := (horizontalBounds L o e).1
  let right := (horizontalBounds L o e).2
  let a := (left + x) / 2
  let b := (x + right) / 2
  have hax : a < x := by dsimp [a, left]; linarith [hx.1]
  have hxb : x < b := by dsimp [b, right]; linarith [hx.2]
  have haL : a ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 := by
    dsimp [a, left]
    constructor <;> linarith [hx.1, hx.2]
  have hbL : b ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 := by
    dsimp [b, right]
    constructor <;> linarith [hx.1, hx.2]
  have haK := eventually_mem_horizontalProjection_of_hausdorffDist K L hlim o e haL
  have hbK := eventually_mem_horizontalProjection_of_hausdorffDist K L hlim o e hbL
  have hconc : ∀ᶠ n in atTop,
      ConcaveOn ℝ (Set.Ioo a b) (upperGraphHeight (K n) o e) := by
    filter_upwards [haK, hbK] with n han hbn
    apply (concaveOn_upperGraphHeight (K n) o e).subset _ (convex_Ioo a b)
    intro y hy
    rw [horizontalProjection_eq_Icc] at han hbn ⊢
    exact ⟨han.1.trans hy.1.le, hy.2.le.trans hbn.2⟩
  have hdiffEventually : ∀ᶠ n in atTop,
      DifferentiableAt ℝ (upperGraphHeight (K n) o e) x := by
    filter_upwards [haK, hbK] with n han hbn
    apply hdiffK n
    rw [horizontalProjection_eq_Icc] at han hbn
    exact ⟨han.1.trans_lt hax, hxb.trans_le hbn.2⟩
  have hpointwise (y : ℝ) (hy : y ∈ Set.Ioo a b) :
      Tendsto (fun n ↦ upperGraphHeight (K n) o e y) atTop
        (𝓝 (upperGraphHeight L o e y)) := by
    apply tendsto_upperGraphHeight_of_hausdorffDist K L hlim o e
    exact ⟨haL.1.trans hy.1, hy.2.trans hbL.2⟩
  have hderiv : Tendsto (fun n ↦ deriv (upperGraphHeight (K n) o e) x) atTop
      (𝓝 (deriv (upperGraphHeight L o e) x)) :=
    ConcaveOn.tendsto_deriv_of_tendsto_Ioo ⟨hax, hxb⟩ hconc hpointwise hdiffEventually
      (hdiffL hx)
  have hdensity := (continuous_surfaceDensity_of_slope e hψ).continuousAt.tendsto.comp hderiv
  change Tendsto ((fun r : ℝ ↦ ψ (vectorNormalAngle (e.symm !₂[-r, 1])) *
    Real.sqrt (1 + r ^ 2)) ∘ fun n ↦ deriv (upperGraphHeight (K n) o e) x)
      atTop (𝓝 (upperGraphSurfaceIntegrand L o e ψ x))
  simpa only [upperGraphSurfaceIntegrand] using hdensity

private theorem tendsto_vectorSupport_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) {u : Point} (hu : ‖u‖ = 1) :
    Tendsto (fun n ↦ vectorSupport (K n) u) atTop (𝓝 (vectorSupport L u)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hlim
  intro n
  simpa only [Real.dist_eq] using
    (compactSet_support_continuity (K n) L (K n).nonempty
      (K n).isCompact L.nonempty L.isCompact).2.1 u hu

private theorem horizontalBounds_snd_eq_vectorSupport (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    (horizontalBounds K o e).2 =
      vectorSupport K (e.symm !₂[1, 0]) - inner ℝ o (e.symm !₂[1, 0]) := by
  let u : Point := e.symm !₂[1, 0]
  have hu (p : Point) : e (p - o) 0 = inner ℝ p u - inner ℝ o u := by
    rw [← inner_sub_left, ← e.inner_map_map]
    simp [u, PiLp.inner_apply, Fin.sum_univ_two]
  obtain ⟨p, hp, hsup, hge⟩ := K.isCompact.exists_sSup_image_eq_and_ge K.nonempty
    (show Continuous (fun p : Point ↦ inner ℝ p u) from
      continuous_id.inner continuous_const).continuousOn
  change sSup ((fun p : Point ↦ e (p - o) 0) '' (K : Set Point)) = _
  rw [show vectorSupport K u = inner ℝ p u by exact hsup]
  apply le_antisymm
  · apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    change e (q - o) 0 ≤ inner ℝ p u - inner ℝ o u
    rw [hu q]
    exact sub_le_sub_right (hge q hq) _
  · apply le_csSup
    · have hc : Continuous (fun p : Point ↦ e (p - o)) :=
        e.continuous.comp (continuous_id.sub continuous_const)
      exact K.isCompact.bddAbove_image
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp hc).continuousOn
    · exact ⟨p, hp, hu p⟩

private theorem horizontalBounds_fst_eq_vectorSupport (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    (horizontalBounds K o e).1 =
      -vectorSupport K (-(e.symm !₂[1, 0])) - inner ℝ o (e.symm !₂[1, 0]) := by
  let u : Point := e.symm !₂[1, 0]
  have hu (p : Point) : e (p - o) 0 = inner ℝ p u - inner ℝ o u := by
    rw [← inner_sub_left, ← e.inner_map_map]
    simp [u, PiLp.inner_apply, Fin.sum_univ_two]
  obtain ⟨p, hp, hsup, hge⟩ := K.isCompact.exists_sSup_image_eq_and_ge K.nonempty
    (show Continuous (fun p : Point ↦ inner ℝ p (-u)) from
      continuous_id.inner continuous_const).continuousOn
  change sInf ((fun p : Point ↦ e (p - o) 0) '' (K : Set Point)) = _
  rw [show vectorSupport K (-u) = inner ℝ p (-u) by exact hsup]
  apply le_antisymm
  · apply csInf_le
    · have hc : Continuous (fun p : Point ↦ e (p - o)) :=
        e.continuous.comp (continuous_id.sub continuous_const)
      exact K.isCompact.bddBelow_image
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp hc).continuousOn
    · refine ⟨p, hp, ?_⟩
      change e (p - o) 0 = -inner ℝ p (-u) - inner ℝ o u
      rw [hu p]
      simp
  · apply le_csInf (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    change -inner ℝ p (-u) - inner ℝ o u ≤ e (q - o) 0
    rw [hu q]
    have h := hge q hq
    simp only [inner_neg_right] at h ⊢
    linarith

/-- Horizontal projection endpoints converge with their convex bodies. -/
private theorem tendsto_horizontalBounds_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    Tendsto (fun n ↦ horizontalBounds (K n) o e) atTop
      (𝓝 (horizontalBounds L o e)) := by
  let u : Point := e.symm !₂[1, 0]
  have hu : ‖u‖ = 1 := by
    rw [show ‖u‖ = ‖(!₂[1, 0] : Point)‖ by exact e.symm.norm_map _]
    rw [EuclideanSpace.norm_eq]
    norm_num [Fin.sum_univ_two]
  rw [show (fun n ↦ horizontalBounds (K n) o e) =
      fun n ↦ (-vectorSupport (K n) (-u) - inner ℝ o u,
        vectorSupport (K n) u - inner ℝ o u) by
      funext n
      ext <;> simp [horizontalBounds_fst_eq_vectorSupport,
        horizontalBounds_snd_eq_vectorSupport, u]]
  rw [show horizontalBounds L o e =
      (-vectorSupport L (-u) - inner ℝ o u,
        vectorSupport L u - inner ℝ o u) by
      ext <;> simp [horizontalBounds_fst_eq_vectorSupport,
        horizontalBounds_snd_eq_vectorSupport, u]]
  apply Tendsto.prodMk_nhds
  · exact (tendsto_vectorSupport_of_hausdorffDist K L hlim (by simpa using hu)).neg.sub_const _
  · exact (tendsto_vectorSupport_of_hausdorffDist K L hlim hu).sub_const _

private theorem weightedSurfaceIntegral_eq_upperGraphIntegral
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) :
    (∫ t, ψ t ∂surfaceAreaMeasure K) =
      ∫ x in Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2,
        upperGraphSurfaceIntegrand K o e ψ x := by
  have hformula := (surfaceAreaMeasure_construction K).2.2.2.2 o e ψ hψ ε hε hsupport
  have hle : (horizontalBounds K o e).1 ≤ (horizontalBounds K o e).2 := by
    obtain ⟨x, hx⟩ := K.nonempty.image (fun p : Point ↦ e (p - o) 0)
    change x ∈ horizontalProjection K o e at hx
    rw [horizontalProjection_eq_Icc] at hx
    exact hx.1.trans hx.2
  rcases hle.lt_or_eq with hlt | heq
  · exact (hformula.1 hlt).2
  · rw [hformula.2 heq, heq]
    simp

/-- Weighted upper-normal surface integrals are continuous under Hausdorff convergence. -/
theorem tendsto_integral_surfaceAreaMeasure_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {ψ : Real.Angle → ℝ} (hψ : Continuous ψ) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) :
    Tendsto (fun n ↦ ∫ t, ψ t ∂surfaceAreaMeasure (K n)) atTop
      (𝓝 (∫ t, ψ t ∂surfaceAreaMeasure L)) := by
  obtain ⟨t, -, ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hψ.norm.continuousOn
  let M := ‖ψ t‖
  have hM (u : Real.Angle) : ‖ψ u‖ ≤ M := ht trivial
  have hM0 : 0 ≤ M := norm_nonneg _
  have hb := tendsto_horizontalBounds_of_hausdorffDist K L hlim o e
  have ha : Tendsto (fun n ↦ (horizontalBounds (K n) o e).1) atTop
      (𝓝 (horizontalBounds L o e).1) := continuousAt_fst.tendsto.comp hb
  have hb' : Tendsto (fun n ↦ (horizontalBounds (K n) o e).2) atTop
      (𝓝 (horizontalBounds L o e).2) := continuousAt_snd.tendsto.comp hb
  have hgraph := tendsto_integral_Icc_of_tendsto_endpoints_of_bound ha hb'
    (Eventually.of_forall fun n ↦
      (integrable_upperGraphSurfaceIntegrand (K n) o e ψ hψ hε hsupport _ _).1)
    (mul_nonneg hM0 (inv_nonneg.mpr hε.le))
    (Eventually.of_forall fun n ↦ Eventually.of_forall fun x _ ↦
      norm_upperGraphSurfaceIntegrand_le (K n) o e ψ hε hsupport hM x)
    (ae_tendsto_upperGraphSurfaceIntegrand_of_hausdorffDist K L hlim o e hψ)
  rw [weightedSurfaceIntegral_eq_upperGraphIntegral L o e ψ hψ hε hsupport]
  apply hgraph.congr'
  filter_upwards [] with n
  exact (weightedSurfaceIntegral_eq_upperGraphIntegral (K n) o e ψ hψ hε hsupport).symm

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
# Analysis / Surface Measure / Properties
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

private theorem mem_exposedEdge_iff_isExteriorNormal (K : ConvexBody Point)
    {p : Point} (hp : p ∈ K) (t : Real.Angle) :
    p ∈ exposedEdge K t ↔ IsExteriorNormal K p t := by
  constructor
  · intro h q hq
    have he : inner ℝ p (normalVector t) = supportValue K t := h.2
    rw [inner_sub_left, he]
    exact sub_nonpos.mpr (inner_le_supportValue K hq t)
  · intro h
    refine ⟨hp, le_antisymm (inner_le_supportValue K hp t) ?_⟩
    apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    exact sub_nonpos.mp (by simpa only [inner_sub_left] using h q hq)

private theorem mem_exposedEdge_iff_exteriorNormalAngle_eq (K : ConvexBody Point)
    {p : Point} (hp : p ∈ regularBoundary K) (t : Real.Angle) :
    p ∈ exposedEdge K t ↔ exteriorNormalAngle K p = t := by
  have hpK : p ∈ K := by
    change p ∈ (K : Set Point)
    simpa only [K.isCompact.isClosed.closure_eq] using frontier_subset_closure hp.1
  rw [mem_exposedEdge_iff_isExteriorNormal K hpK]
  have hn : IsExteriorNormal K p (exteriorNormalAngle K p) := by
    simp only [exteriorNormalAngle, dite_eq_left hp.2]
    exact hp.2.exists.choose_spec
  exact ⟨fun ht ↦ hp.2.unique hn ht, fun ht ↦ ht ▸ hn⟩

private theorem faceUnion_inter_regularBoundary (K : ConvexBody Point) (E : Set Real.Angle) :
    (⋃ t ∈ E, exposedEdge K t) ∩ regularBoundary K =
      exteriorNormalAngle K ⁻¹' E ∩ regularBoundary K := by
  ext p
  constructor
  · rintro ⟨hp, hreg⟩
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
    refine ⟨?_, hreg⟩
    change exteriorNormalAngle K p ∈ E
    rwa [(mem_exposedEdge_iff_exteriorNormalAngle_eq K hreg t).mp hp]
  · rintro ⟨hp, hreg⟩
    exact ⟨Set.mem_iUnion₂.mpr ⟨exteriorNormalAngle K p, hp,
      (mem_exposedEdge_iff_exteriorNormalAngle_eq K hreg _).mpr rfl⟩, hreg⟩

private theorem surfaceAreaMeasure_face_union_of_interior_nonempty (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty)
    (E : Set Real.Angle) (hE : MeasurableSet E) :
    surfaceAreaMeasure K E = Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t) := by
  simp only [surfaceAreaMeasure,
    ite_eq_right (not_subsingleton_of_interior_nonempty K hK),
    dite_eq_right (not_exists_segmentPresentation_of_interior_nonempty K hK)]
  rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_exteriorNormalAngle_restrict_regularBoundary K _) hE,
    Measure.restrict_apply' (measurableSet_regularBoundary K),
    ← faceUnion_inter_regularBoundary]
  apply measure_congr
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null (fun p hp ↦ (hp.2 hp.1.1).elim) measure_empty
  · apply measure_mono_null ?_ (hausdorffMeasure_irregularBoundary_eq_zero K hK)
    rintro p ⟨hp, hnot⟩
    refine ⟨?_, fun hreg ↦ hnot ⟨hp, hreg⟩⟩
    obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
    exact mem_frontier_of_mem_of_isExteriorNormal K hpt.1
      ((mem_exposedEdge_iff_isExteriorNormal K hpt.1 t).mp hpt)

private theorem surfaceAreaMeasure_face_union_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) (E : Set Real.Angle) :
    surfaceAreaMeasure K E = Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t) := by
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hK]
  change 0 = _
  symm
  let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  obtain ⟨p, hp⟩ := K.nonempty
  apply measure_mono_null (t := {p})
  · intro q hq
    obtain ⟨t, ht, hqt⟩ := Set.mem_iUnion₂.mp hq
    exact hK hqt.1 hp
  · simp

theorem surfaceAreaMeasure_face_union (K : ConvexBody Point) :
    IsFiniteMeasure (surfaceAreaMeasure K) ∧
    ((K : Set Point).Subsingleton → surfaceAreaMeasure K = 0) ∧
    (∀ d, IsSegmentPresentation K d → surfaceAreaMeasure K =
      ENNReal.ofReal (dist d.1 d.2.1) •
        (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + ((Real.pi : ℝ) : Real.Angle)))) ∧
    ((interior (K : Set Point)).Nonempty → surfaceAreaMeasure K =
      Measure.map (exteriorNormalAngle K)
        ((Measure.hausdorffMeasure 1).restrict (regularBoundary K))) ∧
    (∀ E : Set Real.Angle, MeasurableSet E →
      ((interior (K : Set Point)).Nonempty ∨
        ∃ a b : ℝ, a ≤ b ∧ b < a + Real.pi ∧
          E ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc a b) →
      surfaceAreaMeasure K E =
        Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t)) := by
  obtain ⟨hfinite, hpoint, hsegment, _, _⟩ := surfaceAreaMeasure_construction K
  refine ⟨hfinite, hpoint, hsegment, ?_, ?_⟩
  · intro hK
    simp only [surfaceAreaMeasure,
      ite_eq_right (not_subsingleton_of_interior_nonempty K hK),
      dite_eq_right (not_exists_segmentPresentation_of_interior_nonempty K hK)]
  · intro E hE hdomain
    by_cases hsub : (K : Set Point).Subsingleton
    · exact surfaceAreaMeasure_face_union_of_subsingleton K hsub E
    by_cases hint : (interior (K : Set Point)).Nonempty
    · exact surfaceAreaMeasure_face_union_of_interior_nonempty K hint E hE
    obtain ⟨a, b, hab, hwidth, hsubset⟩ := hdomain.resolve_left hint
    have hseg := exists_segmentPresentation_of_interior_empty K hsub
      (Set.not_nonempty_iff_eq_empty.mp hint)
    obtain ⟨d, hd⟩ := hseg
    exact surfaceAreaMeasure_face_union_of_segmentPresentation K d hd E hE hab hwidth hsubset

instance isFiniteMeasure_surfaceAreaMeasure (K : ConvexBody Point) :
    IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1

/-- A measurable set of normal directions lying in an angular interval of width less than `π`,
on which every face of `K` degenerates to one and the same point, is null for the surface area
measure of `K`. -/
theorem surfaceAreaMeasure_null_of_exposedEdge_subset_singleton (K : ConvexBody Point)
    {E : Set Real.Angle} (hE : MeasurableSet E) {a b : ℝ} (hab : a ≤ b) (hba : b < a + Real.pi)
    (hEab : E ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc a b) (p : Point)
    (hsub : ∀ t ∈ E, exposedEdge K t ⊆ {p}) :
    surfaceAreaMeasure K E = 0 := by
  let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  rw [(surfaceAreaMeasure_face_union K).2.2.2.2 E hE (Or.inr ⟨a, b, hab, hba, hEab⟩)]
  refine measure_mono_null (t := {p}) ?_ (by simp)
  intro x hx
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
  exact hsub t ht hxt

/-- The surface measure of a convex body vanishes on the open angular window strictly between two
normal angles less than a half turn apart at which one and the same point attains the support. -/
theorem surfaceAreaMeasure_angleImage_Ioo_eq_zero_of_mem_exposedEdge (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) {p : Point}
    (hpa : p ∈ exposedEdge K (a : Real.Angle))
    (hpb : p ∈ exposedEdge K (b : Real.Angle)) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) = 0 := by
  refine surfaceAreaMeasure_null_of_exposedEdge_subset_singleton K
    (Real.Angle.isOpen_image_Ioo a b).measurableSet hab.le hba
    (Set.image_mono Set.Ioo_subset_Icc_self) p fun t ht ↦ ?_
  obtain ⟨s, hs, rfl⟩ := ht
  exact (exposedEdge_eq_singleton_of_mem_exposedEdge_of_mem_Ioo hba hs hpa hpb).subset

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
# Analysis / Surface Measure / Boundary Extension
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace MovingSofa

/-- Agreement of positive-vertex increments with tangent-coordinate surface integrals extends
from half-open subintervals to every measurable set avoiding the initial endpoint. -/
theorem intervalStieltjesMeasure_eq_surfaceIntegral_of_increment
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (hinc : ∀ (c d : Set.Icc a b), c < d → ∀ i : Fin 2,
      (edgeVertices K (((d : Set.Icc a b) : ℝ) : Real.Angle)).1 i -
          (edgeVertices K (((c : Set.Icc a b) : ℝ) : Real.Angle)).1 i =
        ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc (c : ℝ) d,
          tangentVector u i ∂surfaceAreaMeasure K) :
    ∀ (i : Fin 2) (E : Set (Set.Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K := by
  let A := Set.Ioc a b
  let c : A → Real.Angle := fun t ↦ ((t : ℝ) : Real.Angle)
  let j : A → Set.Icc a b := fun t ↦ ⟨t, t.property.1.le, t.property.2⟩
  have hc : MeasurableEmbedding c := by
    refine ⟨?_, (Real.Angle.continuous_coe.comp continuous_subtype_val).measurable, ?_⟩
    · intro x y hxy
      exact Subtype.ext (Real.Angle.injOn_coe_Ioc hturn x.property y.property hxy)
    · intro s hs
      let S : Set ℝ := Subtype.val '' s
      have hS : MeasurableSet S :=
        (MeasurableEmbedding.subtype_coe measurableSet_Ioc).measurableSet_image' hs
      have hSI : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) S := by
        intro x hx y hy hxy
        obtain ⟨tx, htx, rfl⟩ := hx
        obtain ⟨ty, hty, rfl⟩ := hy
        exact Real.Angle.injOn_coe_Ioc hturn tx.property ty.property hxy
      have hm := hS.image_of_continuousOn_injOn Real.Angle.continuous_coe.continuousOn hSI
      convert hm using 1
      ext u
      simp [S, c]
  have hj : Measurable j := by fun_prop
  intro i E hE hEa
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) :=
    (surfaceAreaMeasure_face_union K).1
  have hgi : Integrable (fun u : Real.Angle ↦ tangentVector u i) (surfaceAreaMeasure K) := by
    rw [← integrableOn_univ]
    exact ContinuousOn.integrableOn_compact isCompact_univ (by
      fin_cases i
      · exact Real.Angle.continuous_sin.neg.continuousOn
      · exact Real.Angle.continuous_cos.continuousOn)
  obtain ⟨ν, hν⟩ :=
    MeasurableEmbedding.exists_vectorMeasure_image_integral hc (surfaceAreaMeasure K)
      (fun u ↦ tangentVector u i) hgi
  have hmeasure : intervalStieltjesMeasure (f i) = ν.map j := by
    apply MeasureTheory.VectorMeasure.ext_of_Ioc
    · intro x y hxy
      have hpre : j ⁻¹' Ioc x y = {t : A | (x : ℝ) < (t : ℝ) ∧ (t : ℝ) ≤ (y : ℝ)} := rfl
      have hpremeas : MeasurableSet (j ⁻¹' Ioc x y) :=
        measurableSet_Ioc.preimage hj
      have himage : c '' (j ⁻¹' Ioc x y) =
          (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc (x : ℝ) y := by
        ext u
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨t, ht, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, x.property.1.trans_lt ht.1, ht.2.trans y.property.2⟩, ht, rfl⟩
      rw [intervalStieltjesMeasure_Ioc (f i) x y hxy.le,
        VectorMeasure.map_apply _ hj measurableSet_Ioc, hν _ hpremeas, himage,
        hf i y, hf i x, hinc x y hxy i]
    · let aa : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
      let bb : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
      have hpre : j ⁻¹' univ = univ := preimage_univ
      have hunivmeas : MeasurableSet (univ : Set A) := MeasurableSet.univ
      have himage : c '' (univ : Set A) =
          (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b := by
        ext u
        simp [c, A]
      have hzero : intervalStieltjesMeasure (f i) {aa} = 0 := by
        rw [intervalStieltjesMeasure, (f i).boundedVariation.vectorMeasure_singleton,
          (f i).right_continuous aa |>.rightLim_eq]
        have hbot : 𝓝[<] aa = ⊥ := by
          have hIio : Iio aa = ∅ := by
            ext t
            simp only [mem_Iio, mem_empty_iff_false, iff_false]
            exact not_lt_of_ge t.property.1
          rw [hIio]
          exact nhdsWithin_empty aa
        rw [leftLim_eq_of_eq_bot _ hbot, sub_self]
      have hsplit : (univ : Set (Set.Icc a b)) = Ioc aa bb ∪ {aa} := by
        ext t
        simp only [mem_univ, true_iff, mem_union, mem_Ioc, mem_singleton_iff]
        by_cases hta : aa = t
        · exact Or.inr hta.symm
        · exact Or.inl ⟨lt_of_le_of_ne t.property.1 hta, t.property.2⟩
      have hlhs : intervalStieltjesMeasure (f i) univ =
          intervalStieltjesMeasure (f i) (Ioc aa bb) := by
        rw [hsplit, VectorMeasure.of_union (disjoint_singleton_right.2 (by simp))
          measurableSet_Ioc (measurableSet_singleton aa),
          hzero, add_zero]
      rw [hlhs, intervalStieltjesMeasure_Ioc (f i) aa bb hab.le,
        VectorMeasure.map_apply _ hj MeasurableSet.univ, hpre, hν _ hunivmeas, himage,
        hf i bb, hf i aa, hinc aa bb hab i]
  have himageE : c '' (j ⁻¹' E) =
      (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨j t, ht, rfl⟩
    · rintro ⟨t, htE, rfl⟩
      exact ⟨⟨t, hEa t htE, t.property.2⟩, htE, rfl⟩
  rw [hmeasure, VectorMeasure.map_apply _ hj hE, hν _ (hE.preimage hj), himageE]

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
# Analysis / Surface Measure / Opposite
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The opposite-angle surface measure and support function. -/
def oppositeSurfaceData (K : ConvexBody Point) :
    Measure Real.Angle × (Real.Angle → ℝ) :=
  (Measure.map (fun t ↦ t - ((Real.pi : ℝ) : Real.Angle)) (surfaceAreaMeasure K),
    fun t ↦ supportValue K (t + ((Real.pi : ℝ) : Real.Angle)))

/-- The opposite surface measure is the half-turn translate of the surface measure. -/
theorem oppositeSurfaceData_fst (K : ConvexBody Point) :
    (oppositeSurfaceData K).1 =
      Measure.map (fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle))
        (surfaceAreaMeasure K) := rfl

instance isFiniteMeasure_oppositeSurfaceData (K : ConvexBody Point) :
    IsFiniteMeasure (oppositeSurfaceData K).1 := by
  rw [oppositeSurfaceData_fst]
  exact Measure.isFiniteMeasure_map _ _

/-- The opposite support function of a convex body is continuous in the normal direction. -/
theorem continuous_oppositeSurfaceData_snd (K : ConvexBody Point) :
    Continuous (oppositeSurfaceData K).2 :=
  (continuous_supportValue K).comp (continuous_id.add continuous_const)

/-- Integrating a `π`-shifted integrand against the opposite surface measure over an open angular
window is integrating the integrand itself against the surface-area measure over the `π`-translated
window.  The endpoints of the translated window are given as hypotheses so that call sites may
normalize them arithmetically. -/
theorem setIntegral_oppositeSurfaceData_angleImage_Ioo (K : ConvexBody Point) {a b a' b' : ℝ}
    (ha : a' = a + Real.pi) (hb : b' = b + Real.pi) {f : Real.Angle → ℝ} (hf : Measurable f) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        f (t + ((Real.pi : ℝ) : Real.Angle)) ∂(oppositeSurfaceData K).1) =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a' b',
        f t ∂surfaceAreaMeasure K := by
  subst ha hb
  have hshift : Measurable fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle) :=
    (continuous_id.sub continuous_const).measurable
  have hfshift : Measurable fun t : Real.Angle ↦ f (t + ((Real.pi : ℝ) : Real.Angle)) :=
    hf.comp (continuous_id.add continuous_const).measurable
  have hE : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) :=
    (Real.Angle.isOpen_image_Ioo a b).measurableSet
  rw [oppositeSurfaceData_fst, setIntegral_map hE hfshift.aestronglyMeasurable hshift.aemeasurable,
    Real.Angle.preimage_sub_pi_image_Ioo]
  simp only [sub_add_cancel]

/-- The opposite surface measure vanishes on an open angular window whose half-turn translate
carries a single support point. -/
theorem oppositeSurfaceData_angleImage_Ioo_eq_zero_of_mem_exposedEdge (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) {p : Point}
    (hpa : p ∈ exposedEdge K ((a + Real.pi : ℝ) : Real.Angle))
    (hpb : p ∈ exposedEdge K ((b + Real.pi : ℝ) : Real.Angle)) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) = 0 := by
  have hshift : Measurable fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle) :=
    (continuous_id.sub continuous_const).measurable
  rw [oppositeSurfaceData_fst,
    Measure.map_apply hshift (Real.Angle.isOpen_image_Ioo a b).measurableSet,
    Real.Angle.preimage_sub_pi_image_Ioo]
  exact surfaceAreaMeasure_angleImage_Ioo_eq_zero_of_mem_exposedEdge K (by linarith) (by linarith)
    hpa hpb

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
# Analysis / Surface Measure / Weak Convergence
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

private def normalCoordinateFrames : Fin 4 → Point ≃ₗᵢ[ℝ] Point :=
  ![LinearIsometryEquiv.refl ℝ Point, LinearIsometryEquiv.neg ℝ,
    coordinateSwap, coordinateSwap.trans (LinearIsometryEquiv.neg ℝ)]

private theorem exists_normalCoordinateFrame (t : Real.Angle) :
    ∃ i, (1 / 2 : ℝ) < normalCoordinateFrames i (normalVector t) 1 := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp [normalCoordinateFrames, coordinateSwap, normalVector, frame] at h0 h1 h2 h3
  have hs : t.sin ^ 2 ≤ 1 / 4 := by nlinarith
  have hc : t.cos ^ 2 ≤ 1 / 4 := by nlinarith
  nlinarith [t.cos_sq_add_sin_sq]

/-- Four coordinate half-circles admit a continuous partition of unity supported
where the upward component of the normal is at least one half. -/
theorem exists_normalCoordinate_partition :
    ∃ (e : Fin 4 → Point ≃ₗᵢ[ℝ] Point) (χ : Fin 4 → Real.Angle → ℝ),
      (∀ i, Continuous (χ i)) ∧ (∀ t, ∑ i, χ i t = 1) ∧
        (∀ i t, e i (normalVector t) 1 < 1 / 2 → χ i t = 0) := by
  let ρ : Fin 4 → Real.Angle → ℝ := fun i t ↦
    max 0 (normalCoordinateFrames i (normalVector t) 1 - 1 / 2)
  have hρ : ∀ i, Continuous (ρ i) := by
    intro i
    dsimp [ρ]
    exact continuous_const.max
      (((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp
        ((normalCoordinateFrames i).continuous.comp continuous_normalVector_angle)).sub
          continuous_const)
  have hpos (t : Real.Angle) : 0 < ∑ i, ρ i t := by
    obtain ⟨i, hi⟩ := exists_normalCoordinateFrame t
    apply Finset.sum_pos' (fun j _ ↦ le_max_left _ _)
    refine ⟨i, Finset.mem_univ _, ?_⟩
    exact (sub_pos.mpr hi).trans_le (le_max_right _ _)
  refine ⟨normalCoordinateFrames, fun i t ↦ ρ i t / ∑ j, ρ j t, ?_, ?_, ?_⟩
  · intro i
    exact (hρ i).div (continuous_finsetSum _ fun j _ ↦ hρ j)
      (fun t ↦ (hpos t).ne')
  · intro t
    rw [← Finset.sum_div]
    exact div_self (hpos t).ne'
  · intro i t ht
    have hz : ρ i t = 0 := max_eq_left (sub_nonpos.mpr ht.le)
    dsimp only
    rw [hz, zero_div]

/-- Convergence for test functions supported in upward normal patches implies
convergence for all continuous test functions. -/
theorem tendsto_surfaceIntegral_of_normal_patches
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hpatch : ∀ (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ), Continuous ψ →
      (∀ t, e (normalVector t) 1 < 1 / 2 → ψ t = 0) →
      Tendsto (fun n ↦ ∫ t, ψ t ∂surfaceAreaMeasure (K n)) atTop
        (𝓝 (∫ t, ψ t ∂surfaceAreaMeasure L)))
    (φ : Real.Angle → ℝ) (hφ : Continuous φ) :
    Tendsto (fun n ↦ ∫ t, φ t ∂surfaceAreaMeasure (K n)) atTop
      (𝓝 (∫ t, φ t ∂surfaceAreaMeasure L)) := by
  obtain ⟨e, χ, hχ, hsum, hsupp⟩ := exists_normalCoordinate_partition
  let ψ : Fin 4 → Real.Angle → ℝ := fun i t ↦ φ t * χ i t
  have hψ (i : Fin 4) : Continuous (ψ i) := hφ.mul (hχ i)
  have hψsum (t : Real.Angle) : ∑ i, ψ i t = φ t := by
    simp only [ψ, ← Finset.mul_sum, hsum, mul_one]
  have hint (C : ConvexBody Point) :
      ∑ i, (∫ t, ψ i t ∂surfaceAreaMeasure C) = ∫ t, φ t ∂surfaceAreaMeasure C := by
    let _ := (surfaceAreaMeasure_construction C).1
    rw [← integral_finsetSum]
    · simp only [hψsum]
    · intro i _
      exact integrableOn_univ.mp ((hψ i).continuousOn.integrableOn_compact isCompact_univ)
  have ht (i : Fin 4) := hpatch (e i) (ψ i) (hψ i) (by
    intro t ht
    simp only [ψ, hsupp i t ht, mul_zero])
  have h := tendsto_finsetSum Finset.univ (fun i _ ↦ ht i)
  simpa only [hint] using h

theorem surfaceAreaMeasure_weak_continuity (K : ℕ → ConvexBody Point)
    (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) (φ : Real.Angle → ℝ) (hφ : Continuous φ) :
    Tendsto (fun n ↦ ∫ u, φ u ∂surfaceAreaMeasure (K n))
      atTop (𝓝 (∫ u, φ u ∂surfaceAreaMeasure L)) := by
  apply tendsto_surfaceIntegral_of_normal_patches K L _ φ hφ
  intro e ψ hψ hsupp
  exact tendsto_integral_surfaceAreaMeasure_of_hausdorffDist K L hlim 0 e hψ
    (by norm_num : (0 : ℝ) < 1 / 2) hsupp

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
# Analysis / Surface Measure / Atom Limits
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- An upper bound by a moving surface atom passes to a Hausdorff limit. -/
theorem le_surfaceAreaMeasure_atom_of_tendsto {K : ℕ → ConvexBody Point}
    {L : ConvexBody Point}
    (hK : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) {u : Real.Angle} {x : ℕ → ℝ} {a : ℝ}
    (hx : Tendsto x atTop (𝓝 a))
    (hle : ∀ n, x n ≤ (surfaceAreaMeasure (K n) {u}).toReal) :
    a ≤ (surfaceAreaMeasure L {u}).toReal := by
  let μs : ℕ → FiniteMeasure Real.Angle := fun n ↦
    ⟨surfaceAreaMeasure (K n), (surfaceAreaMeasure_face_union (K n)).1⟩
  let μ : FiniteMeasure Real.Angle :=
    ⟨surfaceAreaMeasure L, (surfaceAreaMeasure_face_union L).1⟩
  have hμ : Tendsto μs atTop (𝓝 μ) := by
    apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    exact surfaceAreaMeasure_weak_continuity K L hK f f.continuous
  have hclosed :
      Filter.limsup (fun n ↦ surfaceAreaMeasure (K n) {u}) atTop ≤
        surfaceAreaMeasure L {u} := by
    have h := FiniteMeasure.limsup_measure_closed_le_of_tendsto hμ
      (isClosed_singleton : IsClosed {u})
    change Filter.limsup (fun n ↦ surfaceAreaMeasure (K n) {u}) atTop ≤
      surfaceAreaMeasure L {u} at h
    exact h
  have hpoint : ∀ n, ENNReal.ofReal (x n) ≤ surfaceAreaMeasure (K n) {u} := by
    intro n
    exact ENNReal.ofReal_le_of_le_toReal (hle n)
  have hlimsup :
      Filter.limsup (fun n ↦ ENNReal.ofReal (x n)) atTop ≤
        Filter.limsup (fun n ↦ surfaceAreaMeasure (K n) {u}) atTop :=
    Filter.limsup_le_limsup (Eventually.of_forall hpoint)
  have hmain : ENNReal.ofReal a ≤ surfaceAreaMeasure L {u} := by
    calc
      ENNReal.ofReal a = Filter.limsup (fun n ↦ ENNReal.ofReal (x n)) atTop :=
        (ENNReal.tendsto_ofReal hx).limsup_eq.symm
      _ ≤ Filter.limsup (fun n ↦ surfaceAreaMeasure (K n) {u}) atTop := hlimsup
      _ ≤ surfaceAreaMeasure L {u} := hclosed
  let _ : IsFiniteMeasure (surfaceAreaMeasure L) := (surfaceAreaMeasure_face_union L).1
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hmain

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
# Analysis / Surface Measure / Weighted Boundary
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- On a half-open parameter interval of at most one turn, the angular projection is a
measurable embedding. -/
theorem measurableEmbedding_angleCoe_Ioc {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi) :
    MeasurableEmbedding fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle) := by
  refine ⟨?_, (Real.Angle.continuous_coe.comp continuous_subtype_val).measurable, ?_⟩
  · intro x y hxy
    exact Subtype.ext (Real.Angle.injOn_coe_Ioc hturn x.property y.property hxy)
  · intro s hs
    let S : Set ℝ := Subtype.val '' s
    have hS : MeasurableSet S :=
      (MeasurableEmbedding.subtype_coe measurableSet_Ioc).measurableSet_image' hs
    have hSI : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) S := by
      intro x hx y hy hxy
      obtain ⟨tx, htx, rfl⟩ := hx
      obtain ⟨ty, hty, rfl⟩ := hy
      exact Real.Angle.injOn_coe_Ioc hturn tx.property ty.property hxy
    have hm := hS.image_of_continuousOn_injOn Real.Angle.continuous_coe.continuousOn hSI
    convert hm using 1
    ext u
    simp [S]

/-- A bounded measurable function on a half-open parameter interval of at most one full turn
extends to a bounded measurable function of the angle. -/
theorem exists_bounded_measurable_angle_extension {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi)
    (ψ : Ioc a b → ℝ) (hψm : Measurable ψ) (C : ℝ) (hC : 0 ≤ C) (hψb : ∀ t, ‖ψ t‖ ≤ C) :
    ∃ Q : Real.Angle → ℝ, Measurable Q ∧ (∀ u, ‖Q u‖ ≤ C) ∧
      ∀ t : Ioc a b, Q ((t : ℝ) : Real.Angle) = ψ t := by
  have hc : MeasurableEmbedding fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle) :=
    measurableEmbedding_angleCoe_Ioc hturn
  refine ⟨Function.extend (fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle)) ψ (fun _ ↦ 0),
    hc.measurable_extend hψm measurable_const, fun u ↦ ?_,
    fun t ↦ hc.injective.extend_apply ψ _ t⟩
  by_cases hu : ∃ t : Ioc a b, ((t : ℝ) : Real.Angle) = u
  · obtain ⟨t, rfl⟩ := hu
    rw [hc.injective.extend_apply]
    exact hψb t
  · rw [Function.extend_apply' _ _ _ hu]
    simpa using hC

/-- A bounded measurable angular weight may be transported through the positive-vertex
Stieltjes identity, coordinate by coordinate. -/
theorem intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (i : Fin 2) (Q : Real.Angle → ℝ) (C : ℝ)
    (hQm : Measurable fun t : Ioc a b ↦ Q (((t : ℝ) : Real.Angle)))
    (hQb : ∀ u, ‖Q u‖ ≤ C)
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    intervalStieltjesIntegral (f i)
        (fun t ↦ Q (((t : ℝ) : Real.Angle))) E =
      ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
        Q u * tangentVector u i ∂surfaceAreaMeasure K := by
  let A := Ioc a b
  let c : A → Real.Angle := fun t ↦ ((t : ℝ) : Real.Angle)
  let j : A → Icc a b := fun t ↦ ⟨t, t.property.1.le, t.property.2⟩
  have hc : MeasurableEmbedding c := measurableEmbedding_angleCoe_Ioc hturn
  have hj : MeasurableEmbedding j := by
    refine ⟨fun x y h ↦ Subtype.ext (congrArg (fun z : Icc a b ↦ (z : ℝ)) h), ?_, ?_⟩
    · fun_prop
    · intro s hs
      have hsval : MeasurableSet ((Subtype.val : A → ℝ) '' s) :=
        (MeasurableEmbedding.subtype_coe measurableSet_Ioc).measurableSet_image' hs
      have hsj : j '' s = {t : Icc a b | (t : ℝ) ∈ (Subtype.val : A → ℝ) '' s} := by
        ext t
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, hxt⟩
          exact ⟨x, hx, Subtype.ext hxt⟩
      rw [hsj]
      exact hsval.preimage measurable_subtype_coe
  let μA := (surfaceAreaMeasure K).comap c
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  let _ : IsFiniteMeasure μA :=
    ⟨by
      rw [hc.comap_apply]
      exact measure_lt_top _ _⟩
  have htancont : Continuous (fun t : A ↦ tangentVector (c t) i) :=
    (continuous_tangentVector_coordinate i).comp
      (Real.Angle.continuous_coe.comp continuous_subtype_val)
  have htan : Integrable (fun t : A ↦ tangentVector (c t) i) μA :=
    Integrable.of_bound htancont.aestronglyMeasurable 1
      (ae_of_all _ fun t ↦ norm_tangentVector_coordinate_le_one (c t) i)
  let ν : SignedMeasure A := μA.withDensityᵥ (fun t ↦ tangentVector (c t) i)
  have hν (S : Set A) (hS : MeasurableSet S) :
      ν S = ∫ u in c '' S, tangentVector u i ∂surfaceAreaMeasure K := by
    rw [show ν S = ∫ t in S, tangentVector (c t) i ∂μA by
      exact withDensityᵥ_apply htan hS]
    have hm := hc.setIntegral_map (μ := μA) (fun u ↦ tangentVector u i) (c '' S)
    rw [hc.map_comap, hc.injective.preimage_image,
      Measure.restrict_restrict_of_subset (image_subset_range c S)] at hm
    exact hm.symm
  have hmeasure : intervalStieltjesMeasure (f i) = ν.map j := by
    apply MeasureTheory.VectorMeasure.ext_of_Ioc
    · intro x y hxy
      have hpremeas : MeasurableSet (j ⁻¹' Ioc x y) :=
        measurableSet_Ioc.preimage hj.measurable
      have himage : c '' (j ⁻¹' Ioc x y) =
          (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' Ioc x y := by
        ext u
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨j t, ht, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, x.property.1.trans_lt ht.1, t.property.2⟩, ht, rfl⟩
      rw [VectorMeasure.map_apply _ hj.measurable measurableSet_Ioc, hν _ hpremeas,
        himage, hf i (Ioc x y) measurableSet_Ioc]
      intro t ht
      exact x.property.1.trans_lt ht.1
    · let aa : Icc a b := ⟨a, le_rfl, hab.le⟩
      let bb : Icc a b := ⟨b, hab.le, le_rfl⟩
      have hzero : intervalStieltjesMeasure (f i) {aa} = 0 := by
        rw [intervalStieltjesMeasure, (f i).boundedVariation.vectorMeasure_singleton,
          (f i).right_continuous aa |>.rightLim_eq]
        have hbot : 𝓝[<] aa = ⊥ := by
          have hIio : Iio aa = ∅ := by
            ext t
            simp only [mem_Iio, mem_empty_iff_false, iff_false]
            exact not_lt_of_ge t.property.1
          rw [hIio]
          exact nhdsWithin_empty aa
        rw [leftLim_eq_of_eq_bot _ hbot, sub_self]
      have hsplit : (univ : Set (Icc a b)) = Ioc aa bb ∪ {aa} := by
        ext t
        simp only [mem_univ, true_iff, mem_union, mem_Ioc, mem_singleton_iff]
        by_cases hta : aa = t
        · exact Or.inr hta.symm
        · exact Or.inl ⟨lt_of_le_of_ne t.property.1 hta, t.property.2⟩
      have hlhs : intervalStieltjesMeasure (f i) univ =
          intervalStieltjesMeasure (f i) (Ioc aa bb) := by
        rw [hsplit, VectorMeasure.of_union (disjoint_singleton_right.2 (by simp))
          measurableSet_Ioc (measurableSet_singleton aa), hzero, add_zero]
      have himage : c '' (univ : Set A) =
          (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' Ioc aa bb := by
        ext u
        constructor
        · rintro ⟨t, -, rfl⟩
          exact ⟨j t, t.property, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, ht⟩, mem_univ _, rfl⟩
      rw [hlhs, VectorMeasure.map_apply _ hj.measurable MeasurableSet.univ,
        preimage_univ, hν _ MeasurableSet.univ, himage,
        hf i (Ioc aa bb) measurableSet_Ioc]
      intro t ht
      exact ht.1
  unfold intervalStieltjesIntegral
  rw [hmeasure, hj.setIntegral_map_vectorMeasure hE]
  change (∫ᵛ t in j ⁻¹' E, Q (c t)
      ∂[ContinuousLinearMap.mul ℝ ℝ; μA.withDensityᵥ fun t ↦ tangentVector (c t) i]) = _
  rw [VectorMeasure.setIntegral_withDensity_mul_of_bounded (q := fun t : A ↦ Q (c t)) htan
    hQm.aestronglyMeasurable C (fun t ↦ hQb (c t))
    (j ⁻¹' E) (hE.preimage hj.measurable)]
  have hm := hc.setIntegral_map (μ := μA)
    (fun u ↦ Q u * tangentVector u i) (c '' (j ⁻¹' E))
  rw [hc.map_comap, hc.injective.preimage_image,
    Measure.restrict_restrict_of_subset (image_subset_range c (j ⁻¹' E))] at hm
  have himageE : c '' (j ⁻¹' E) =
      (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨j t, ht, rfl⟩
    · rintro ⟨t, htE, rfl⟩
      exact ⟨⟨t, hEa t htE, t.property.2⟩, htE, rfl⟩
  rw [← himageE]
  exact hm.symm

/-- A continuous angular weight may be transported through the positive-vertex Stieltjes
identity, coordinate by coordinate. -/
theorem intervalStieltjesIntegral_positiveVertex_coordinate
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (i : Fin 2) (Q : Real.Angle → ℝ) (hQ : Continuous Q)
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    intervalStieltjesIntegral (f i)
        (fun t ↦ Q (((t : ℝ) : Real.Angle))) E =
      ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
        Q u * tangentVector u i ∂surfaceAreaMeasure K :=
  intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable K hab hturn f hf i Q
    ‖ContinuousMap.equivBoundedOfCompact Real.Angle ℝ ⟨Q, hQ⟩‖
    (hQ.comp (Real.Angle.continuous_coe.comp continuous_subtype_val)).measurable
    (fun u ↦ BoundedContinuousFunction.norm_coe_le_norm
      (ContinuousMap.equivBoundedOfCompact Real.Angle ℝ ⟨Q, hQ⟩) u) E hE hEa

/-- A bounded measurable angular weight times a frame tangent coordinate is integrable against
the surface measure on every measurable set of angles represented in the half-open parameter
interval. -/
theorem integrableOn_mul_tangentVector_of_bounded
    (K : ConvexBody Point) {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi)
    (i : Fin 2) (Q : Real.Angle → ℝ) (C : ℝ)
    (hQm : Measurable fun t : Ioc a b ↦ Q (((t : ℝ) : Real.Angle)))
    (hQb : ∀ u, ‖Q u‖ ≤ C)
    (S : Set Real.Angle) (hS : MeasurableSet S)
    (hSsub : S ⊆ Set.range fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle)) :
    IntegrableOn (fun u ↦ Q u * tangentVector u i) S (surfaceAreaMeasure K) := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hC : 0 ≤ C := le_trans (norm_nonneg (Q 0)) (hQb 0)
  obtain ⟨Q', hQ'meas, hQ'b, hQ'eq⟩ := exists_bounded_measurable_angle_extension hturn
    (fun t : Ioc a b ↦ Q (((t : ℝ) : Real.Angle))) hQm C hC (fun t ↦ hQb _)
  have hglobal : Integrable (fun u ↦ Q' u * tangentVector u i) (surfaceAreaMeasure K) := by
    refine Integrable.of_bound
      (hQ'meas.mul (continuous_tangentVector_coordinate i).measurable).aestronglyMeasurable C
      (ae_of_all _ fun u ↦ ?_)
    calc ‖Q' u * tangentVector u i‖ = ‖Q' u‖ * ‖tangentVector u i‖ := norm_mul _ _
      _ ≤ C * 1 :=
        mul_le_mul (hQ'b u) (norm_tangentVector_coordinate_le_one u i) (norm_nonneg _) hC
      _ = C := mul_one C
  refine hglobal.integrableOn.congr_fun (fun u hu ↦ ?_) hS
  obtain ⟨t, rfl⟩ := hSsub hu
  simp only [hQ'eq t]

/-- Pairing the positive-vertex Stieltjes measures with a bounded measurable planar weight is the
surface integral of the pointwise contraction of that weight with the tangent frame. -/
theorem sum_intervalStieltjesIntegral_positiveVertex_dot
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (φ : Fin 2 → Icc a b → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hφm : ∀ i, Measurable (φ i)) (hφb : ∀ i t, ‖φ i t‖ ≤ C)
    (g : Real.Angle → ℝ)
    (hg : ∀ t : Icc a b, a < (t : ℝ) →
      ∑ i : Fin 2, φ i t * tangentVector (((t : ℝ) : Real.Angle)) i =
        g (((t : ℝ) : Real.Angle)))
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∑ i : Fin 2, intervalStieltjesIntegral (f i) (φ i) E) =
      ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E, g u ∂surfaceAreaMeasure K := by
  set incl : Ioc a b → Icc a b := fun t ↦ ⟨(t : ℝ), t.property.1.le, t.property.2⟩
  have hinclm : Measurable incl := (Continuous.subtype_mk continuous_subtype_val _).measurable
  have himg : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E =
      (fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle)) '' (incl ⁻¹' E) := by
    ext u
    constructor
    · rintro ⟨t, htE, rfl⟩
      exact ⟨⟨(t : ℝ), hEa t htE, t.property.2⟩, htE, rfl⟩
    · rintro ⟨t, htE, rfl⟩
      exact ⟨incl t, htE, rfl⟩
  have hEmeas : MeasurableSet ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E) := by
    rw [himg]
    exact (measurableEmbedding_angleCoe_Ioc hturn).measurableSet_image' (hE.preimage hinclm)
  have hsub : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E ⊆
      Set.range fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle) := by
    rintro u ⟨t, htE, rfl⟩
    exact ⟨⟨(t : ℝ), hEa t htE, t.property.2⟩, rfl⟩
  choose Q hQm hQb hQeq using fun i : Fin 2 ↦ exists_bounded_measurable_angle_extension hturn
    (fun t : Ioc a b ↦ φ i (incl t)) ((hφm i).comp hinclm) C hC fun t ↦ hφb i (incl t)
  have hQmIoc (i : Fin 2) : Measurable fun t : Ioc a b ↦ Q i (((t : ℝ) : Real.Angle)) :=
    (hQm i).comp (Real.Angle.continuous_coe.comp continuous_subtype_val).measurable
  have hQφ (i : Fin 2) (t : Icc a b) (ht : a < (t : ℝ)) :
      Q i (((t : ℝ) : Real.Angle)) = φ i t := hQeq i ⟨(t : ℝ), ht, t.property.2⟩
  have hterm (i : Fin 2) : intervalStieltjesIntegral (f i) (φ i) E =
      ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
        Q i u * tangentVector u i ∂surfaceAreaMeasure K := by
    rw [show intervalStieltjesIntegral (f i) (φ i) E =
        intervalStieltjesIntegral (f i) (fun t ↦ Q i (((t : ℝ) : Real.Angle))) E from
      VectorMeasure.setIntegral_congr_fun fun t htE ↦ (hQφ i t (hEa t htE)).symm]
    exact intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable K hab hturn f hf i
      (Q i) C (hQmIoc i) (hQb i) E hE hEa
  have hint (i : Fin 2) : IntegrableOn (fun u ↦ Q i u * tangentVector u i)
      ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E) (surfaceAreaMeasure K) :=
    integrableOn_mul_tangentVector_of_bounded K hturn i (Q i) C (hQmIoc i) (hQb i) _ hEmeas hsub
  rw [Fin.sum_univ_two, hterm 0, hterm 1, ← integral_add (hint 0) (hint 1)]
  refine setIntegral_congr_fun hEmeas ?_
  rintro u ⟨t, htE, rfl⟩
  have ht := hEa t htE
  simpa only [hQφ 0 t ht, hQφ 1 t ht, Fin.sum_univ_two] using hg t ht

/-- Pairing the positive-vertex Stieltjes measure with the tangent frame gives surface mass. -/
theorem sum_intervalStieltjesIntegral_positiveVertex_tangent
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∑ i : Fin 2, intervalStieltjesIntegral (f i)
      (fun t ↦ tangentVector (((t : ℝ) : Real.Angle)) i) E) =
      (surfaceAreaMeasure K
        ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hcoord (i : Fin 2) :
      intervalStieltjesIntegral (f i)
          (fun t ↦ tangentVector (((t : ℝ) : Real.Angle)) i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i * tangentVector u i ∂surfaceAreaMeasure K := by
    have hQi : Continuous (fun u : Real.Angle ↦ tangentVector u i) := by
      fin_cases i
      · exact Real.Angle.continuous_sin.neg
      · exact Real.Angle.continuous_cos
    exact intervalStieltjesIntegral_positiveVertex_coordinate K hab hturn f hf i
      (fun u ↦ tangentVector u i) hQi E hE hEa
  rw [Fin.sum_univ_two, hcoord 0, hcoord 1]
  have h0 : Integrable (fun u : Real.Angle ↦ tangentVector u 0 * tangentVector u 0)
      (surfaceAreaMeasure K) := by
    apply Continuous.integrable_of_hasCompactSupport
    · convert Real.Angle.continuous_sin.mul Real.Angle.continuous_sin using 1
      funext u
      simp [tangentVector, frame]
    · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  have h1 : Integrable (fun u : Real.Angle ↦ tangentVector u 1 * tangentVector u 1)
      (surfaceAreaMeasure K) := by
    apply Continuous.integrable_of_hasCompactSupport
    · convert Real.Angle.continuous_cos.mul Real.Angle.continuous_cos using 1
      funext u
      simp [tangentVector, frame]
    · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  rw [← integral_add h0.integrableOn h1.integrableOn]
  have hone : (fun u : Real.Angle ↦
      tangentVector u 0 * tangentVector u 0 + tangentVector u 1 * tangentVector u 1) = 1 := by
    funext u
    simpa [tangentVector, frame, pow_two, add_comm] using u.cos_sq_add_sin_sq
  rw [hone]
  let S := (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E
  calc
    integral ((surfaceAreaMeasure K).restrict S) 1 =
        ((surfaceAreaMeasure K).restrict S).real univ := by
          change (∫ _ : Real.Angle, (1 : ℝ) ∂(surfaceAreaMeasure K).restrict S) = _
          rw [integral_const (μ := (surfaceAreaMeasure K).restrict S) (1 : ℝ),
            smul_eq_mul, mul_one]
    _ = (surfaceAreaMeasure K).real S :=
      measureReal_restrict_apply_univ (μ := surfaceAreaMeasure K) S
    _ = (surfaceAreaMeasure K S).toReal := measureReal_def _ _

/-- Pairing the positive-vertex Stieltjes measure with the normal frame vanishes. -/
theorem sum_intervalStieltjesIntegral_positiveVertex_normal
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∑ i : Fin 2, intervalStieltjesIntegral (f i)
      (fun t ↦ normalVector (((t : ℝ) : Real.Angle)) i) E) = 0 := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hcoord (i : Fin 2) :
      intervalStieltjesIntegral (f i)
          (fun t ↦ normalVector (((t : ℝ) : Real.Angle)) i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          normalVector u i * tangentVector u i ∂surfaceAreaMeasure K := by
    have hQi : Continuous (fun u : Real.Angle ↦ normalVector u i) := by
      fin_cases i
      · exact Real.Angle.continuous_cos
      · exact Real.Angle.continuous_sin
    exact intervalStieltjesIntegral_positiveVertex_coordinate K hab hturn f hf i
      (fun u ↦ normalVector u i) hQi E hE hEa
  rw [Fin.sum_univ_two, hcoord 0, hcoord 1]
  have h0 : Integrable (fun u : Real.Angle ↦ normalVector u 0 * tangentVector u 0)
      (surfaceAreaMeasure K) := by
    apply Continuous.integrable_of_hasCompactSupport
    · convert (Real.Angle.continuous_cos.mul Real.Angle.continuous_sin).neg using 1
      funext u
      simp [normalVector, tangentVector, frame]
    · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  have h1 : Integrable (fun u : Real.Angle ↦ normalVector u 1 * tangentVector u 1)
      (surfaceAreaMeasure K) := by
    apply Continuous.integrable_of_hasCompactSupport
    · convert Real.Angle.continuous_sin.mul Real.Angle.continuous_cos using 1
      funext u
      simp [normalVector, tangentVector, frame]
    · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  rw [← integral_add h0.integrableOn h1.integrableOn]
  apply integral_eq_zero_of_ae
  filter_upwards with u
  simp [normalVector, tangentVector, frame]
  ring

end MovingSofa

end

end

end
