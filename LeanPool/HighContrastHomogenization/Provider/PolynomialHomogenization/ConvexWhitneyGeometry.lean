/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryLayer
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyRows

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexWhitneyGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Euclidean Whitney rows in bounded domains

The identity-grid maximal filling gives finite rows of ordinary open triadic
cubes.  Its selected cubes are disjoint, lie inside the target, have escaping
parents below the starting scale, and exhaust every bounded open target up to a
null set.  For convex targets, the escaping-parent property and the inner ball
bound the volume of each row.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal Matrix Pointwise

noncomputable section

variable {d : ℕ}

/-- An aligned cell of the identity grid is exactly the corresponding open
translated triadic cube. -/
theorem adaptedCellAt_one_eq_openCubeSet_translateCube (a : ℤ)
    (w : Fin d → ℤ) :
    adaptedCellAt (1 : Mat d) a w =
      openCubeSet (translateCube w (originCube d a)) := by
  rw [Recurrence.adaptedCellAt_eq_image]
  have h : matVecMul (1 : Mat d) = id := funext fun x => matVecMul_one x
  rw [h, Set.image_id]
  rfl

private theorem standardCell_subset_metricBall_of_mem {a : ℤ}
    {w : Fin d → ℤ} {x : Vec d} (hx : x ∈ standardCell d a w) :
    standardCell d a w ⊆ Metric.ball x ((3 : ℝ) ^ a) := by
  intro y hy
  have hside : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  rw [Metric.mem_ball, dist_pi_lt_iff hside]
  rw [Recurrence.mem_standardCell_iff] at hx hy
  intro i
  rw [Real.dist_eq, abs_lt]
  obtain ⟨hxlo, hxhi⟩ := hx i
  obtain ⟨hylo, hyhi⟩ := hy i
  constructor <;> linarith only [hxlo, hxhi, hylo, hyhi]

private theorem mem_euclideanBallAt_of_mem_same_standardCell
    (hd : 1 ≤ d) {a : ℤ} {w : Fin d → ℤ} {x y : Vec d}
    (hx : x ∈ standardCell d a w) (hy : y ∈ standardCell d a w) :
    y ∈ euclideanBallAt x
      (2 * Real.sqrt d * (3 : ℝ) ^ a) := by
  have hyball := standardCell_subset_metricBall_of_mem hx hy
  have hvec := vecNormSq_sub_le_of_mem_metricBall hyball
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hside : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have hrad : (2 * Real.sqrt d * (3 : ℝ) ^ a) ^ 2 =
      (4 * (d : ℝ)) * ((3 : ℝ) ^ a) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    ring
  rw [mem_euclideanBallAt_iff, hrad]
  refine hvec.trans_lt ?_
  have hfour : (d : ℝ) < 4 * (d : ℝ) := by linarith only [hdpos]
  exact mul_lt_mul_of_pos_right hfour (sq_pos_of_pos hside)

/-- A selected identity-grid cube lies in the target, while below the starting
scale its aligned parent escapes the target. -/
theorem fillingIndex_one_cell_and_parent_escape {U : Set (Vec d)}
    {n a : ℤ} (han : a < n) {w : Fin d → ℤ}
    (hw : w ∈ Transport.fillingIndex (1 : Mat d) n U a) :
    openCubeSet (translateCube w (originCube d a)) ⊆ U ∧
      ¬openCubeSet (translateCube (Transport.gridParent w) (originCube d (a + 1))) ⊆ U := by
  constructor
  · rw [← adaptedCellAt_one_eq_openCubeSet_translateCube]
    exact Transport.adaptedCellAt_subset_of_mem_fillingIndex hw
  · rw [← adaptedCellAt_one_eq_openCubeSet_translateCube]
    exact hw.2.2.resolve_left (ne_of_lt han)

/-- Every identity-grid row below the starting scale lies in a Euclidean inner
boundary layer whose thickness is twice the Euclidean diameter bound for its
escaping parent. -/
theorem iUnion_fillingIndex_one_subset_innerBoundaryLayer
    (hd : 1 ≤ d) {U : Set (Vec d)} {n a : ℤ} (han : a < n) :
    (⋃ w ∈ Transport.fillingIndex (1 : Mat d) n U a,
        openCubeSet (translateCube w (originCube d a))) ⊆
      {x : Vec d | x ∈ U ∧
        ¬euclideanBallAt x (2 * Real.sqrt d * (3 : ℝ) ^ (a + 1)) ⊆ U} := by
  rintro x hx
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
  have hgeom := fillingIndex_one_cell_and_parent_escape han hw
  refine ⟨hgeom.1 hxw, ?_⟩
  obtain ⟨y, hyparent, hyU⟩ := Set.not_subset.mp hgeom.2
  intro hball
  apply hyU
  apply hball
  apply mem_euclideanBallAt_of_mem_same_standardCell hd
  · have hxadapt : x ∈ adaptedCellAt (1 : Mat d) a w := by
      rwa [adaptedCellAt_one_eq_openCubeSet_translateCube]
    have hxparent := Transport.adaptedCellAt_subset_parent (1 : Mat d) a w hxadapt
    rwa [adaptedCellAt_one_eq_openCubeSet_translateCube] at hxparent
  · exact hyparent

/-- A convex Whitney row has the explicit boundary-volume rate
`6 d^(3/2) 3^a / rho`. -/
theorem volume_iUnion_fillingIndex_one_le (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {rho Rad : ℝ} (hsand : HasBallSandwich U rho Rad)
    {n a : ℤ} (han : a < n) :
    volume (⋃ w ∈ Transport.fillingIndex (1 : Mat d) n U a,
        openCubeSet (translateCube w (originCube d a))) ≤
      ENNReal.ofReal
          (6 * (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ a / rho) * volume U := by
  calc
    volume (⋃ w ∈ Transport.fillingIndex (1 : Mat d) n U a,
        openCubeSet (translateCube w (originCube d a))) ≤
        volume {x : Vec d | x ∈ U ∧
          ¬euclideanBallAt x (2 * Real.sqrt d * (3 : ℝ) ^ (a + 1)) ⊆ U} :=
      measure_mono (iUnion_fillingIndex_one_subset_innerBoundaryLayer hd han)
    _ ≤ ENNReal.ofReal
          ((d : ℝ) * (2 * Real.sqrt d * (3 : ℝ) ^ (a + 1)) / rho) * volume U :=
      volume_innerBoundaryLayer_le hd hU hsand (by positivity)
    _ = ENNReal.ofReal
          (6 * (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ a / rho) * volume U := by
      congr 2
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
      ring

private theorem volume_iUnion_identity_gridFaces :
    volume (⋃ a : ℤ, matVecMul (1 : Mat d) '' ⋃ (i : Fin d) (k : ℤ),
      {z : Vec d | z i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ a}) = 0 := by
  exact measure_iUnion_null fun a => Transport.volume_image_gridFaces (1 : Mat d) a

/-- The identity-grid maximal filling exhausts every open target up to a null
set.  Openness supplies a sufficiently fine cube around each point away from
the countable union of grid faces. -/
theorem volume_diff_iUnion_fillingIndex_one {U : Set (Vec d)}
    (hU : IsOpen U) (n : ℤ) :
    volume (U \ ⋃ a ∈ Set.Iic n,
      ⋃ w ∈ Transport.fillingIndex (1 : Mat d) n U a,
        openCubeSet (translateCube w (originCube d a))) = 0 := by
  refine measure_mono_null ?_ volume_iUnion_identity_gridFaces
  rintro x ⟨hxU, hxnot⟩
  by_contra hxfaces
  obtain ⟨eps, heps, hballU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (1 / 3 : ℝ) ^ m < eps :=
    exists_pow_lt_of_lt_one heps (by norm_num)
  let J : ℤ := min (-(m : ℤ)) n
  have hJn : J ≤ n := min_le_right _ _
  have hJm : J ≤ -(m : ℤ) := min_le_left _ _
  have hscale : (3 : ℝ) ^ J < eps := by
    calc
      (3 : ℝ) ^ J ≤ (3 : ℝ) ^ (-(m : ℤ)) :=
        zpow_le_zpow_right₀ (by norm_num) hJm
      _ = (1 / 3 : ℝ) ^ m := by
        rw [zpow_neg, zpow_natCast, one_div, inv_pow]
      _ < eps := hm
  have hxfaceJ : x ∉ matVecMul (1 : Mat d) '' ⋃ (i : Fin d) (k : ℤ),
      {z : Vec d | z i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ J} := by
    intro hx
    exact hxfaces (Set.mem_iUnion.mpr ⟨J, hx⟩)
  obtain ⟨w, hxw⟩ := Transport.exists_mem_adaptedCellAt Matrix.PosDef.one J hxfaceJ
  have hxw' : x ∈ standardCell d J w := by
    rwa [adaptedCellAt_one_eq_openCubeSet_translateCube] at hxw
  have hcellU : adaptedCellAt (1 : Mat d) J w ⊆ U := by
    rw [adaptedCellAt_one_eq_openCubeSet_translateCube]
    exact (standardCell_subset_metricBall_of_mem hxw').trans
      (Metric.ball_subset_ball hscale.le) |>.trans hballU
  obtain ⟨b, hbn, hbmem, hbsub⟩ :=
    Transport.exists_mem_fillingIndex_of_subset hJn hcellU
  apply hxnot
  refine Set.mem_iUnion₂.mpr ⟨J + (b : ℤ), hbn, ?_⟩
  refine Set.mem_iUnion₂.mpr ⟨Transport.gridParent^[b] w, hbmem, ?_⟩
  rw [← adaptedCellAt_one_eq_openCubeSet_translateCube]
  exact hbsub hxw

/-- A bounded open convex domain admits finite identity-grid Whitney rows with
the exact open-triadic carriers, disjointness, parent escape, quantitative row
volume, and almost-everywhere exhaustion. -/
theorem exists_convex_whitney_rows (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {rho Rad : ℝ} (hsand : HasBallSandwich U rho Rad) (n : ℤ) :
    ∃ Z : ℤ → Finset (Fin d → ℤ),
      (∀ a, ↑(Z a) = Transport.fillingIndex (1 : Mat d) n U a) ∧
      (∀ a, ∀ w ∈ Z a,
        openCubeSet (translateCube w (originCube d a)) ⊆ U) ∧
      (∀ a, a < n → ∀ w ∈ Z a,
        ¬openCubeSet (translateCube (Transport.gridParent w) (originCube d (a + 1))) ⊆ U) ∧
      (∀ a b : ℤ, ∀ w ∈ Z a, ∀ v ∈ Z b, (a, w) ≠ (b, v) →
        Disjoint (openCubeSet (translateCube w (originCube d a)))
          (openCubeSet (translateCube v (originCube d b)))) ∧
      (∀ a : ℤ, a < n →
        ∑ w ∈ Z a, volume (openCubeSet (translateCube w (originCube d a))) ≤
          ENNReal.ofReal
            (6 * (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ a / rho) * volume U) ∧
      volume (U \ ⋃ a ∈ Set.Iic n, ⋃ w ∈ (Z a : Set (Fin d → ℤ)),
        openCubeSet (translateCube w (originCube d a))) = 0 := by
  classical
  have hfin : ∀ a : ℤ, (Transport.fillingIndex (1 : Mat d) n U a).Finite := fun a =>
    Transport.finite_fillingIndex Matrix.PosDef.one hU.isBoundedDomain n a
  let Z : ℤ → Finset (Fin d → ℤ) := fun a => (hfin a).toFinset
  have hZ : ∀ a, ↑(Z a) = Transport.fillingIndex (1 : Mat d) n U a := fun a =>
    (hfin a).coe_toFinset
  refine ⟨Z, hZ, ?_, ?_, ?_, ?_, ?_⟩
  · intro a w hw
    rw [← adaptedCellAt_one_eq_openCubeSet_translateCube]
    exact Transport.adaptedCellAt_subset_of_mem_fillingIndex
      ((hfin a).mem_toFinset.mp hw)
  · intro a han w hw
    exact (fillingIndex_one_cell_and_parent_escape han
      ((hfin a).mem_toFinset.mp hw)).2
  · intro a b w hw v hv hne
    rw [← adaptedCellAt_one_eq_openCubeSet_translateCube,
      ← adaptedCellAt_one_eq_openCubeSet_translateCube]
    exact Transport.disjoint_of_mem_fillingIndex Matrix.PosDef.one
      ((hfin a).mem_toFinset.mp hw) ((hfin b).mem_toFinset.mp hv) hne
  · intro a han
    rw [← measure_biUnion_finset ?_ ?_]
    · rw [← Finset.set_biUnion_coe, hZ a]
      exact volume_iUnion_fillingIndex_one_le hd hU hsand han
    · intro w hw v hv hwv
      change Disjoint (openCubeSet (translateCube w (originCube d a)))
        (openCubeSet (translateCube v (originCube d a)))
      rw [← adaptedCellAt_one_eq_openCubeSet_translateCube,
        ← adaptedCellAt_one_eq_openCubeSet_translateCube]
      exact Transport.disjoint_of_mem_fillingIndex Matrix.PosDef.one
        ((hfin a).mem_toFinset.mp hw) ((hfin a).mem_toFinset.mp hv)
        (by simpa using hwv)
    · intro w _
      exact (isOpen_openCubeSet (translateCube w (originCube d a))).measurableSet
  · simp only [hZ]
    exact volume_diff_iUnion_fillingIndex_one hU.isOpen n

end

end HighContrast
end HCPolySupport
