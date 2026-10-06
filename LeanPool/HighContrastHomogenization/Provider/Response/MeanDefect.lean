/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffEnergy

/-!
# High-contrast homogenization: Provider.Response.MeanDefect

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The mean-defect term of the cutoff-energy estimate

The mean-defect term compares the cutoff's childwise means against the childwise
averages of the parent energy density.  Replacing the parent gradient by the
child gradient on each child splits it into two pieces: the cutoff-weighted
child responses, and a cross term built from the gradient difference.

The cross term is quadratic in the gradient difference and linear in the child
gradient, so the Cauchy-Schwarz inequality in the symmetric metric, applied
first on each child and then across the children, bounds it by the geometric
mean of the childwise difference energy and the childwise sum energy.  The sum
energy is at most twice the parent energy plus twice the child responses, which
gives the closed bound recorded below.

Nothing here is an inequality between annealed quantities: the cutoff-weighted
child responses are kept as an explicit term, because they cancel only after
averaging over a stationary law, where the child responses become independent of
the child's position.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open MeasureTheory Book.Ch05.Section53.JUpperBoundWeakNorms

variable {d : ℕ}

/-! ## Elementary facts about descendant averages and cube averages -/

/-- Descendant averages commute with scalar multiples. -/
theorem descendantsAverage_const_mul (Q : TriadicCube d) (j : ℕ) (c : ℝ)
    (F : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => c * F R) =
      c * descendantsAverage Q j F := by
  unfold descendantsAverage
  show ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      (descendantsAtDepth Q j).sum (fun R => c * F R) =
    c * (((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      (descendantsAtDepth Q j).sum F)
  rw [← Finset.mul_sum]
  ring

/-- Descendant averages are monotone. -/
theorem descendantsAverage_mono (Q : TriadicCube d) (j : ℕ)
    {F G : TriadicCube d → ℝ}
    (h : ∀ R ∈ descendantsAtDepth Q j, F R ≤ G R) :
    descendantsAverage Q j F ≤ descendantsAverage Q j G := by
  unfold descendantsAverage
  show ((descendantsAtDepth Q j).card : ℝ)⁻¹ * (descendantsAtDepth Q j).sum F ≤
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ * (descendantsAtDepth Q j).sum G
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) ?_
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- A pointwise two-sided bound passes to the cube average. -/
theorem cubeAverage_le_of_le (R : TriadicCube d) {f : Vec d → ℝ} {B : ℝ}
    (hint : IntegrableOn f (cubeSet R) volume) (hB : ∀ x, f x ≤ B) :
    cubeAverage R f ≤ B := by
  have hconst : IntegrableOn (fun _ : Vec d => B) (cubeSet R) volume :=
    integrableOn_const (μ := volume) (s := cubeSet R) (C := B)
      (volume_cubeSet_lt_top R).ne
  have hmono : ∫ x in cubeSet R, f x ∂volume ≤
      ∫ _x in cubeSet R, B ∂volume :=
    setIntegral_mono_on hint hconst (measurableSet_cubeSet R)
      fun x _hx => hB x
  have hright : ∫ _x in cubeSet R, B ∂volume = cubeVolume R * B := by
    rw [setIntegral_const]
    simp [measureReal_def]
  have hvol : 0 < cubeVolume R := cubeVolume_pos R
  unfold cubeAverage
  calc
    (cubeVolume R)⁻¹ * ∫ x in cubeSet R, f x ∂volume ≤
        (cubeVolume R)⁻¹ * ∫ _x in cubeSet R, B ∂volume :=
      mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hvol.le)
    _ = (cubeVolume R)⁻¹ * (cubeVolume R * B) := by rw [hright]
    _ = B := by
      field_simp

/-- A pointwise lower bound passes to the cube average. -/
theorem le_cubeAverage_of_le (R : TriadicCube d) {f : Vec d → ℝ} {B : ℝ}
    (hint : IntegrableOn f (cubeSet R) volume) (hB : ∀ x, B ≤ f x) :
    B ≤ cubeAverage R f := by
  have hconst : IntegrableOn (fun _ : Vec d => B) (cubeSet R) volume :=
    integrableOn_const (μ := volume) (s := cubeSet R) (C := B)
      (volume_cubeSet_lt_top R).ne
  have hmono : ∫ _x in cubeSet R, B ∂volume ≤
      ∫ x in cubeSet R, f x ∂volume :=
    setIntegral_mono_on hconst hint (measurableSet_cubeSet R)
      fun x _hx => hB x
  have hleft : ∫ _x in cubeSet R, B ∂volume = cubeVolume R * B := by
    rw [setIntegral_const]
    simp [measureReal_def]
  have hvol : 0 < cubeVolume R := cubeVolume_pos R
  unfold cubeAverage
  calc
    B = (cubeVolume R)⁻¹ * (cubeVolume R * B) := by field_simp
    _ = (cubeVolume R)⁻¹ * ∫ _x in cubeSet R, B ∂volume := by rw [hleft]
    _ ≤ (cubeVolume R)⁻¹ * ∫ x in cubeSet R, f x ∂volume :=
      mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hvol.le)

/-- The childwise weights of a cutoff bounded between zero and two are bounded
by one in absolute value. -/
theorem abs_one_sub_cubeAverage_le_one (R : TriadicCube d) {φ : Vec d → ℝ}
    (hint : IntegrableOn φ (cubeSet R) volume)
    (h0 : ∀ x, 0 ≤ φ x) (h2 : ∀ x, φ x ≤ 2) :
    |1 - cubeAverage R φ| ≤ 1 := by
  have hlo : 0 ≤ cubeAverage R φ := le_cubeAverage_of_le R hint h0
  have hhi : cubeAverage R φ ≤ 2 := cubeAverage_le_of_le R hint h2
  rw [abs_le]
  constructor <;> linarith only [hlo, hhi]

/-! ## The split of the mean-defect term -/

/-- **The mean-defect term splits** into the cutoff-weighted child responses and
the additivity cross term. -/
theorem meanDefectTopEnergyTermOnCubeAtDepth_eq_cross_add_cutoffWeightedChild
    [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d) (Q : TriadicCube d) (j : ℕ)
    (φ : Vec d → ℝ) (p r : Vec d)
    (hCoeff : ∀ R ∈ descendantsAtDepth Q j,
      (a.coeffOn Q).toCoeffField = (a.coeffOn R).toCoeffField) :
    meanDefectTopEnergyTermOnCubeAtDepth Q (a.coeffOn Q) j φ p r =
      concreteAdditivityCrossTermOnFamilyAtDepth a Q j φ p r +
        cutoffWeightedChildResponseJOnFamilyAtDepth a Q j φ p r := by
  have hcell : ∀ R ∈ descendantsAtDepth Q j,
      (1 - cubeAverage R φ) *
          cubeAverage R (topHalfEnergyDensityOnCube Q (a.coeffOn Q) p r) =
        (1 - cubeAverage R φ) *
            cubeAverage R
              (childAdditivityCrossDensityOnFamilyOnCube a Q R p r) +
          cutoffChildWeight φ R *
            Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R) p r := by
    intro R hR
    rw [cubeAverage_topHalfEnergyOnFamily_eq_childAdditivityCross_add_responseJOnChild
      a Q R p r (hCoeff R hR)
      (childAdditivityCrossDensityOnFamilyOnCube_integrableOn a Q hR p r)]
    unfold cutoffChildWeight
    ring
  calc
    meanDefectTopEnergyTermOnCubeAtDepth Q (a.coeffOn Q) j φ p r =
        descendantsAverage Q j (fun R =>
          (1 - cubeAverage R φ) *
              cubeAverage R
                (childAdditivityCrossDensityOnFamilyOnCube a Q R p r) +
            cutoffChildWeight φ R *
              Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
                (a.coeffOn R) p r) := by
      unfold meanDefectTopEnergyTermOnCubeAtDepth
      exact descendantsAverage_congr_of_eq_on_descendants Q j hcell
    _ = concreteAdditivityCrossTermOnFamilyAtDepth a Q j φ p r +
        cutoffWeightedChildResponseJOnFamilyAtDepth a Q j φ p r := by
      rw [← descendantsAverage_add]
      rfl

/-! ## The cross-term bound -/

/-- The childwise sum energies average to at most four times the parent
response plus twice the partition defect. -/
theorem descendantsAverage_additivitySumHalfEnergy_le [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (Q : TriadicCube d) (j : ℕ)
    (p r : Vec d)
    (hCoeff : ∀ R ∈ descendantsAtDepth Q j,
      (a.coeffOn Q).toCoeffField = (a.coeffOn R).toCoeffField) :
    (descendantsAverage Q j fun R =>
        cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p r)) ≤
      4 * Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) (a.coeffOn Q) p r +
        2 * responseJPartitionDefectOnFamilyAtDepth a Q j p r := by
  have hcell : ∀ R ∈ descendantsAtDepth Q j,
      cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p r) ≤
        2 * cubeAverage R (topHalfEnergyDensityOnCube Q (a.coeffOn Q) p r) +
          2 * Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
            (a.coeffOn R) p r := by
    intro R hR
    exact
      cubeAverage_additivitySumHalfEnergyDensityOnFamilyOnCube_le_two_topHalfEnergy_add_two_childResponse
        a Q hR p r (hCoeff R hR)
  have hmono := descendantsAverage_mono Q j hcell
  have hsplit :
      (descendantsAverage Q j fun R =>
          2 * cubeAverage R (topHalfEnergyDensityOnCube Q (a.coeffOn Q) p r) +
            2 * Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
              (a.coeffOn R) p r) =
        2 * Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) (a.coeffOn Q) p r +
          2 * childResponseJAverageOnFamilyAtDepth a Q j p r := by
    rw [← descendantsAverage_add, descendantsAverage_const_mul,
      descendantsAverage_const_mul,
      descendantsAverage_cubeAverage_topHalfEnergyOnCube_eq_responseJOnCube
        Q (a.coeffOn Q) j p r]
    rfl
  rw [hsplit] at hmono
  have hdefect : childResponseJAverageOnFamilyAtDepth a Q j p r =
      Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) (a.coeffOn Q) p r +
        responseJPartitionDefectOnFamilyAtDepth a Q j p r := by
    unfold responseJPartitionDefectOnFamilyAtDepth
    ring
  rw [hdefect] at hmono
  linarith only [hmono]

/-- **The cross term is bounded** by the geometric mean of the childwise
difference energy and the closed sum-energy majorant. -/
theorem abs_concreteAdditivityCrossTermOnFamilyAtDepth_le_sqrt_mul_sqrt
    [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d) (Q : TriadicCube d) (j : ℕ)
    (φ : Vec d → ℝ) (p r : Vec d)
    (hCoeff : ∀ R ∈ descendantsAtDepth Q j,
      (a.coeffOn Q).toCoeffField = (a.coeffOn R).toCoeffField)
    (hweight : ∀ R ∈ descendantsAtDepth Q j, |1 - cubeAverage R φ| ≤ 1) :
    |concreteAdditivityCrossTermOnFamilyAtDepth a Q j φ p r| ≤
      Real.sqrt (descendantsAverage Q j fun R =>
          cubeAverage R
            (additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p r)) *
        Real.sqrt
          (4 * Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) (a.coeffOn Q) p r +
            2 * responseJPartitionDefectOnFamilyAtDepth a Q j p r) := by
  have hbase :=
    abs_concreteAdditivityCrossTermOnFamilyAtDepth_le_const_mul_sqrt_descAvg_diffEnergy_mul_sqrt_descAvg_sumEnergy
      a Q j φ p r (C := 1) zero_le_one hweight
  refine hbase.trans ?_
  rw [one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt
    (descendantsAverage_additivitySumHalfEnergy_le a Q j p r hCoeff)

/-! ## The shape of the bound -/

/-- Square roots are subadditive. -/
private theorem sqrt_add_le_sqrt_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hsq : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have hsx := Real.sq_sqrt hx
    have hsy := Real.sq_sqrt hy
    have hcross : 0 ≤ Real.sqrt x * Real.sqrt y :=
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
    linarith only [hsx, hsy, hcross]
  calc
    Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = Real.sqrt x + Real.sqrt y :=
      Real.sqrt_sq (by positivity)

/-- The closed bound in the shape used by the localization argument. -/
theorem sqrt_mul_sqrt_four_add_two_le {X J T : ℝ} (hJ : 0 ≤ J) (hT : 0 ≤ T) :
    Real.sqrt X * Real.sqrt (4 * J + 2 * T) ≤
      2 * (Real.sqrt X * Real.sqrt J) +
        Real.sqrt 2 * (Real.sqrt X * Real.sqrt T) := by
  have h4J : (0 : ℝ) ≤ 4 * J := by linarith only [hJ]
  have h2T : (0 : ℝ) ≤ 2 * T := by linarith only [hT]
  have hsub := sqrt_add_le_sqrt_add_sqrt h4J h2T
  have h4 : Real.sqrt (4 * J) = 2 * Real.sqrt J := by
    rw [show (4 : ℝ) * J = 2 ^ 2 * J by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : Real.sqrt (2 * T) = Real.sqrt 2 * Real.sqrt T :=
    Real.sqrt_mul (by norm_num) T
  rw [h4, h2] at hsub
  calc
    Real.sqrt X * Real.sqrt (4 * J + 2 * T) ≤
        Real.sqrt X * (2 * Real.sqrt J + Real.sqrt 2 * Real.sqrt T) :=
      mul_le_mul_of_nonneg_left hsub (Real.sqrt_nonneg X)
    _ = 2 * (Real.sqrt X * Real.sqrt J) +
        Real.sqrt 2 * (Real.sqrt X * Real.sqrt T) := by ring

/-- The closed bound is at most the coarser shape with the two separated
coefficients. -/
theorem sqrt_mul_sqrt_four_add_two_le_two_mul_add_four_mul {T J : ℝ}
    (hJ : 0 ≤ J) (hT : 0 ≤ T) :
    Real.sqrt T * Real.sqrt (4 * J + 2 * T) ≤
      2 * T + 4 * (Real.sqrt T * Real.sqrt J) := by
  have hstep := sqrt_mul_sqrt_four_add_two_le (X := T) hJ hT
  have hTT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    have h : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [h, h4.le, h4.ge]
  have hprod : 0 ≤ Real.sqrt T * Real.sqrt J :=
    mul_nonneg (Real.sqrt_nonneg T) (Real.sqrt_nonneg J)
  have hsqrt2T : Real.sqrt 2 * T ≤ 2 * T :=
    mul_le_mul_of_nonneg_right hsqrt2 hT
  rw [hTT] at hstep
  linarith only [hstep, hsqrt2T, hprod]

/-! ## The discharged cutoff-energy estimate -/

/-- The pulled-back adapted cutoff is integrable on every triadic cube. -/
theorem integrableOn_adaptedPreYoungCutoff_pullback [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (R : TriadicCube d) :
    IntegrableOn (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y))
      (cubeSet R) volume := by
  have hlinear : ContDiff ℝ (⊤ : ℕ∞) (matVecMul q) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin q)).contDiff
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) := by
    simpa only [Function.comp_def] using
      (adaptedPreYoungCutoff_smooth hq t).comp hlinear
  have hconst : IntegrableOn (fun _ : Vec d => (1 : ℝ)) (cubeSet R) volume :=
    integrableOn_const (μ := volume) (s := cubeSet R) (C := (1 : ℝ))
      (volume_cubeSet_lt_top R).ne
  have hmeas : AEStronglyMeasurable
      (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y))
      (volume.restrict (cubeSet R)) :=
    hsmooth.continuous.aestronglyMeasurable
  have hbdd : ∀ᵐ x ∂(volume.restrict (cubeSet R)),
      ‖adaptedPreYoungCutoff q hq t (matVecMul q x)‖ ≤ 2 :=
    _root_.Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact adaptedPreYoungCutoff_le_two hq t (matVecMul q x)
      · exact adaptedPreYoungCutoff_nonneg hq t (matVecMul q x)
  simpa using! hconst.bdd_mul hmeas hbdd

/-- The adapted cutoff's childwise weights are bounded by one. -/
theorem abs_one_sub_cubeAverage_adaptedPreYoungCutoff_le_one [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (R : TriadicCube d) :
    |1 - cubeAverage R
        (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y))| ≤ 1 :=
  abs_one_sub_cubeAverage_le_one R
    (integrableOn_adaptedPreYoungCutoff_pullback hq t R)
    (fun x => adaptedPreYoungCutoff_nonneg hq t (matVecMul q x))
    (fun x => adaptedPreYoungCutoff_le_two hq t (matVecMul q x))

end

end Response
end HighContrast
end HCPolySupport
