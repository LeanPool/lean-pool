/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderNearIdentityDualAbsorption
public import LeanPool.HighContrastHomogenization.Support.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge.SharpLoss
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.PublicTheorems
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ContinuousInterpolation.OverlapCoordinateBridge
public import LeanPool.HighContrastHomogenization.Support.Besov.Duality.CaccioppoliVectorization
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.NegativeBesovLocalize
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.DualToCircLoss.FiniteLoss

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderIdentityCubeDualRegularity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Identity-coefficient cube dual regularity at the printed order

The identity background is the scalar background at `sigma = 1`.  For a
zero-trace potential field `w` whose sum with an `L²` datum `F` is solenoidal
on a triadic cube, the printed-order dual negative Besov norms of `w` and of
`w + F` are controlled by the same norm of `F`, with a constant depending only
on the dimension and on the printed order.

The proof is the duality argument at the printed order.  A unit full-dual test
in one coordinate is turned into an identity-coefficient Dirichlet datum; the
solution's gradient is a positive Besov test with a budget fixed before the
cube; the Dirichlet pairing identity moves the test from `w` to `F`; and the
genuine dual norm of `F` absorbs it.  The printed order is below the trace
threshold, which is exactly the range in which the coordinate bridge holds.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

private theorem dualConj_two_eq :
    cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
  simpa [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))

private theorem dualConj_two_ne_top :
    cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
  rw [dualConj_two_eq]
  norm_num

private theorem dualConj_two_ne_zero :
    cubeBesovConjExponent (2 : ℝ≥0∞) ≠ 0 := by
  rw [dualConj_two_eq]
  norm_num

/-- A coordinate of a cube mean is dominated by the Euclidean size of the mean
vector. -/
private theorem abs_cubeAverage_component_le_sqrt_vecNormSq
    {d : ℕ} (Q : TriadicCube d) (H : Vec d → Vec d) (i : Fin d) :
    |cubeAverage Q (fun x ↦ H x i)| ≤
      Real.sqrt (vecNormSq (cubeAverageVec Q H)) := by
  have hcomp : cubeAverage Q (fun x ↦ H x i) = cubeAverageVec Q H i := rfl
  have hsq : (cubeAverageVec Q H i) ^ 2 ≤ vecNormSq (cubeAverageVec Q H) := by
    have hterm :
        (cubeAverageVec Q H i) ^ 2 =
          cubeAverageVec Q H i * cubeAverageVec Q H i := by ring
    rw [hterm, vecNormSq, vecDot]
    exact Finset.single_le_sum
      (f := fun j : Fin d ↦ cubeAverageVec Q H j * cubeAverageVec Q H j)
      (fun j _hj ↦ mul_self_nonneg (cubeAverageVec Q H j)) (Finset.mem_univ i)
  rw [hcomp, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq

/-- A budget for the overlapping positive vector norm of a field caps every
finite-depth full-dual test norm of each of its coordinates. -/
private theorem componentDualTestNorm_le_of_overlappingBudget
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (H : Vec d → Vec d) (i : Fin d)
    {B : ℝ}
    (hreg : CubeVectorOverlappingBesovHRegularity Q s H)
    (hB : cubeBesovOverlappingPositiveVectorNormTwo Q s H ≤ B)
    (N : ℕ) :
    cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x ↦ H x i) ≤
      (3 : ℝ) ^ ((d : ℝ) / 2) * (cubeBesovScaleWeight s Q * B) := by
  have hweight : 0 ≤ cubeBesovScaleWeight s Q := cubeBesovScaleWeight_nonneg s Q
  have hsemi :
      cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (fun x ↦ H x i) ≤
        cubeBesovScaleWeight s Q *
          cubeBesovOverlappingPositiveVectorSeminormTwo Q s H :=
    (cubeBesovOverlapPartialSeminorm_two_coordinate_le_vector Q s H i N
        hreg.memLp).trans
      (mul_le_mul_of_nonneg_left (hreg.partialSeminorm_le_seminorm N) hweight)
  have hmean :
      cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x ↦ H x i)‖ ≤
        cubeBesovScaleWeight s Q *
          Real.sqrt (vecNormSq (cubeAverageVec Q H)) := by
    refine mul_le_mul_of_nonneg_left ?_ hweight
    simpa [Real.norm_eq_abs] using
      abs_cubeAverage_component_le_sqrt_vecNormSq Q H i
  have hoverlap :
      cubeBesovOverlapPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (fun x ↦ H x i) ≤
        cubeBesovScaleWeight s Q * B := by
    have hsum :
        cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
              (fun x ↦ H x i) +
            cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x ↦ H x i)‖ ≤
          cubeBesovScaleWeight s Q *
            cubeBesovOverlappingPositiveVectorNormTwo Q s H := by
      have hnorm :
          cubeBesovOverlappingPositiveVectorNormTwo Q s H =
            Real.sqrt (vecNormSq (cubeAverageVec Q H)) +
              cubeBesovOverlappingPositiveVectorSeminormTwo Q s H := rfl
      rw [hnorm, mul_add]
      linarith only [hsemi, hmean]
    exact hsum.trans
      (mul_le_mul_of_nonneg_left hB hweight)
  have hpartial :=
    cubeBesovPartialNorm_le_three_rpow_mul_overlapPartialNorm
      Q s (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) N
      (fun x ↦ H x i)
  have hfactor : (0 : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
    N (fun x ↦ H x i) dualConj_two_ne_top, dualConj_two_eq]
  refine hpartial.trans ?_
  simpa using mul_le_mul_of_nonneg_left hoverlap hfactor

/-- The normalized pairing of an `L²` flux defect against a positive Besov test
field is priced by the genuine dual norms of the defect's coordinates. -/
private theorem abs_cubeAverage_vecDot_le_of_overlappingBudget
    {d : ℕ} {Q : TriadicCube d} {s B : ℝ}
    (hs : 0 < s) (F H : Vec d → Vec d)
    (hF : MemVectorL2 (cubeSet Q) F)
    (hreg : CubeVectorOverlappingBesovHRegularity Q s H)
    (hB : cubeBesovOverlappingPositiveVectorNormTwo Q s H ≤ B) :
    |cubeAverage Q (fun x ↦ vecDot (F x) (H x))| ≤
      ((3 : ℝ) ^ ((d : ℝ) / 2) * (cubeBesovScaleWeight s Q * B)) *
        ∑ j : Fin d,
          cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x ↦ F x j) := by
  have hBnonneg : 0 ≤ B := hreg.norm_nonneg.trans hB
  have hweight : 0 ≤ cubeBesovScaleWeight s Q := cubeBesovScaleWeight_nonneg s Q
  have hfactor : (0 : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hbudget :
      (0 : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) / 2) * (cubeBesovScaleWeight s Q * B) :=
    mul_nonneg hfactor (mul_nonneg hweight hBnonneg)
  have hFmem : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hF
  have hFcomp : ∀ j : Fin d,
      MemLp (fun x ↦ F x j) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    fun j ↦ memLp_component_of_memLp F j hFmem
  have hHcomp : ∀ j : Fin d,
      MemLp (fun x ↦ H x j) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    fun j ↦ memLp_component_of_memLp H j hreg.memLp
  have hInt : ∀ j : Fin d,
      Integrable (fun x ↦ F x j * H x j) (normalizedCubeMeasure Q) :=
    fun j ↦ (hFcomp j).integrable_mul (hHcomp j)
  have hlocal : ∀ j : Fin d,
      CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x ↦ H x j) := by
    intro j
    exact CubeBesovDualLocalMemLpGlobal.of_memLp_parent
      (p := (2 : ℝ≥0∞)) (by simpa [dualConj_two_eq] using hHcomp j)
  calc
    |cubeAverage Q (fun x ↦ vecDot (F x) (H x))| ≤
        ∑ j : Fin d,
          |cubeBesovPairing Q (fun x ↦ F x j) (fun x ↦ H x j)| :=
      abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q F H hInt
    _ ≤ ∑ j : Fin d,
          cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x ↦ F x j) *
            ((3 : ℝ) ^ ((d : ℝ) / 2) *
              (cubeBesovScaleWeight s Q * B)) := by
        refine Finset.sum_le_sum ?_
        intro j _hj
        exact
          Book.Ch01.Legacy.abs_cubeBesovPairing_le_dualFullNorm_mul_bound
            Q s (fun x ↦ F x j) (fun x ↦ H x j) hs (hFcomp j) hbudget
            (fun N ↦
              componentDualTestNorm_le_of_overlappingBudget Q s H j hreg hB N)
            (hlocal j)
    _ = ((3 : ℝ) ^ ((d : ℝ) / 2) * (cubeBesovScaleWeight s Q * B)) *
          ∑ j : Fin d,
            cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
              (fun x ↦ F x j) := by
        rw [← Finset.sum_mul, mul_comm]

/-- A unit full-dual test prices the coordinate pairing by the coordinate's own
genuine dual norm. -/
private theorem abs_cubeBesovPairing_le_dualFullNorm_of_fullTest
    {d : ℕ} (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (u : Vec d → ℝ) {g : Vec d → ℝ}
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u := by
  have h :=
    Book.Ch01.Legacy.abs_cubeBesovPairing_le_dualFullNorm_mul_bound
      Q s u g hs hu zero_le_one hg.1 hg.2
  simpa using h

/-- Identity-coefficient cube dual regularity at the printed order, with a
constant fixed before the cube, the potential field, and the datum. -/
theorem exists_printOrderIdentityCubeDualRegularityWithConstant
    (d : ℕ) [NeZero d] (g : ℝ) (hg : g ∈ Ico (0 : ℝ) 1) :
    ∃ Cid : ℝ, PrintOrderIdentityCubeDualRegularityWithConstant d g Cid := by
  classical
  obtain ⟨Cdir, hdir⟩ :=
    exists_discreteConstantCoefficientDirichletBesovFunctionSpacesUniform d
  have hbridge := unitFullDualCoordinateOverlappingBridgeSharpLoss d
  have hs : 0 < printCertificateOrder g := (printOrder_margins hg).1
  have hhalf : printCertificateOrder g < 1 / 2 := (printOrder_margins hg).2.1
  set s : ℝ := printCertificateOrder g with hs_def
  set K : ℝ := 1 + Real.sqrt (sharpBoundaryKernelLoss d s) with hK_def
  have hK : 0 ≤ K := by
    rw [hK_def]
    positivity
  set beta : ℝ := (3 : ℝ) ^ ((d : ℝ) / 2) * (Cdir * (2 * K)) with hbeta_def
  have hbeta : 0 ≤ beta := by
    rw [hbeta_def]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg hdir.1 (by linarith only [hK]))
  refine ⟨(d : ℝ) * (beta + 1), mul_nonneg (Nat.cast_nonneg d)
    (by linarith only [hbeta]), ?_⟩
  intro Q w F hF hw hsol
  have hsolScalar :
      IsSolenoidalOn (cubeSet Q)
        (fun x ↦ matVecMul (scalarMatrix (d := d) (1 : ℝ)) (w x) + F x) := by
    have hfun :
        (fun x ↦ matVecMul (scalarMatrix (d := d) (1 : ℝ)) (w x) + F x) =
          fun x ↦ w x + F x := by
      funext x
      rw [matVecMul_scalarMatrix, one_smul]
    rw [hfun]
    exact hsol
  have hFmem : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hF
  have hFopen : MemVectorL2 (openCubeSet Q) F := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using hF
  set S : ℝ :=
    ∑ j : Fin d, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
      (fun x ↦ F x j) with hS_def
  have hSnonneg : 0 ≤ S := by
    rw [hS_def]
    exact Finset.sum_nonneg fun j _hj ↦
      cubeBesovDualFullNorm_nonneg Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
        (fun x ↦ F x j) dualConj_two_ne_zero dualConj_two_ne_top
  -- The common per-coordinate step: solve the identity Dirichlet problem for
  -- the coordinate test and price the resulting pairing.
  have hcore : ∀ (i : Fin d) (t : Vec d → ℝ),
      CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) t →
        ∃ v : H10Function (openCubeSet Q),
          CubeDirichletDivergenceProblem Q v (coordinateVectorField i t) ∧
            |cubeAverage Q
              (fun x ↦ vecDot (F x) (v.toH1Function.grad x))| ≤ beta * S := by
    intro i t ht
    obtain ⟨v, hv, hvReg, hvNorm⟩ :=
      exists_coordinateDirichletSolution_overlappingPositiveNorm_le_sharpLoss
        hdir hbridge Q i t hs hhalf ht
    refine ⟨v, hv, ?_⟩
    have hbound :=
      abs_cubeAverage_vecDot_le_of_overlappingBudget (Q := Q) (s := s)
        (B := Cdir * (2 * K * cubeBesovScaleWeight (-s) Q)) hs F
        (fun x ↦ v.toH1Function.grad x) hF hvReg (by
          simpa [hK_def, mul_assoc] using hvNorm)
    have hcoef :
        (3 : ℝ) ^ ((d : ℝ) / 2) *
            (cubeBesovScaleWeight s Q *
              (Cdir * (2 * K * cubeBesovScaleWeight (-s) Q))) = beta := by
      have hmul := cubeBesovScaleWeight_mul_neg_self s Q
      calc
        (3 : ℝ) ^ ((d : ℝ) / 2) *
            (cubeBesovScaleWeight s Q *
              (Cdir * (2 * K * cubeBesovScaleWeight (-s) Q))) =
            (cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q) *
              ((3 : ℝ) ^ ((d : ℝ) / 2) * (Cdir * (2 * K))) := by ring
        _ = 1 * ((3 : ℝ) ^ ((d : ℝ) / 2) * (Cdir * (2 * K))) := by rw [hmul]
        _ = beta := by rw [hbeta_def, one_mul]
    rw [hcoef] at hbound
    exact hbound
  constructor
  · refine le_trans
      (cubeScaleNormalizedDualNegativeBesovVectorNormTwo_le_card_mul
        Q s w (B := beta * S) ?_) ?_
    · intro i t ht
      obtain ⟨v, hv, hvbound⟩ := hcore i t ht
      have hpair :=
        cubeBesovPairing_solutionComparison_component_eq_cubeAverage_fluxDefect_dualGradient
          (Q := Q) (sigma0 := (1 : ℝ)) (w := w) (F := F) (v := v)
          i t hF hv hw hsolScalar
      have hwcomp :
          (fun x ↦ matVecMul (scalarMatrix (d := d) (1 : ℝ)) (w x) i) =
            fun x ↦ w x i := by
        funext x
        rw [matVecMul_scalarMatrix, one_smul]
      rw [hwcomp] at hpair
      rw [hpair]
      exact hvbound
    · have hnorm :
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F =
            cubeBesovScaleWeight s Q * S := rfl
      rw [hnorm, Fintype.card_fin]
      have hweight : 0 ≤ cubeBesovScaleWeight s Q :=
        cubeBesovScaleWeight_nonneg s Q
      have hexpand :
          cubeBesovScaleWeight s Q * ((d : ℝ) * (beta * S)) ≤
            (d : ℝ) * (beta + 1) * (cubeBesovScaleWeight s Q * S) := by
        have hgap :
            (d : ℝ) * (beta + 1) * (cubeBesovScaleWeight s Q * S) -
                cubeBesovScaleWeight s Q * ((d : ℝ) * (beta * S)) =
              (d : ℝ) * (cubeBesovScaleWeight s Q * S) := by ring
        have hrest : 0 ≤ (d : ℝ) * (cubeBesovScaleWeight s Q * S) :=
          mul_nonneg (Nat.cast_nonneg d) (mul_nonneg hweight hSnonneg)
        linarith only [hgap, hrest]
      exact hexpand
  · refine le_trans
      (cubeScaleNormalizedDualNegativeBesovVectorNormTwo_le_card_mul
        Q s (fun x ↦ w x + F x) (B := (beta + 1) * S) ?_) ?_
    · intro i t ht
      obtain ⟨v, hv, hvbound⟩ := hcore i t ht
      have hpair :=
        BesovPairing_fluxComparison_component_eq_fluxDefect_dualGradient
          (Q := Q) (sigma0 := (1 : ℝ)) (s := s) (w := w) (F := F) (v := v)
          i ht hF hv hw hsolScalar
      have hwcomp :
          (fun x ↦ (matVecMul (scalarMatrix (d := d) (1 : ℝ)) (w x) + F x) i) =
            fun x ↦ (w x + F x) i := by
        funext x
        rw [matVecMul_scalarMatrix, one_smul]
      rw [hwcomp] at hpair
      rw [hpair]
      have hcoordLp :
          MemLp (coordinateVectorField i t) (2 : ℝ≥0∞)
            (normalizedCubeMeasure Q) :=
        coordinateVectorField_memLp_of_cubeBesovDualFullTest_two_two ht
      have hcoordOpen : MemVectorL2 (openCubeSet Q) (coordinateVectorField i t) :=
        memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hcoordLp
      have hsplit :=
        abs_cubeAverage_vecDot_add_right_le Q F
          (fun x ↦ v.toH1Function.grad x) (coordinateVectorField i t)
          hFopen v.toH1Function.grad_memVectorL2 hcoordOpen
      have hcoordPair :
          |cubeAverage Q
              (fun x ↦ vecDot (F x) (coordinateVectorField i t x))| ≤ S := by
        have heq :
            cubeBesovPairing Q (fun x ↦ F x i) t =
              cubeAverage Q
                (fun x ↦ vecDot (F x) (coordinateVectorField i t x)) :=
          cubeBesovPairing_component_eq_cubeAverage_vecDot_coordinateVectorField
            Q F i t
        have hle :
            |cubeBesovPairing Q (fun x ↦ F x i) t| ≤
              cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
                (fun x ↦ F x i) :=
          abs_cubeBesovPairing_le_dualFullNorm_of_fullTest Q hs
            (fun x ↦ F x i) (memLp_component_of_memLp F i hFmem) ht
        have hsingle :
            cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
                (fun x ↦ F x i) ≤ S := by
          rw [hS_def]
          exact Finset.single_le_sum
            (f := fun j : Fin d ↦
              cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
                (fun x ↦ F x j))
            (fun j _hj ↦
              cubeBesovDualFullNorm_nonneg Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
                (fun x ↦ F x j) dualConj_two_ne_zero dualConj_two_ne_top)
            (Finset.mem_univ i)
        rw [← heq]
        exact hle.trans hsingle
      have htotal :
          |cubeAverage Q
              (fun x ↦ vecDot (F x)
                (v.toH1Function.grad x + coordinateVectorField i t x))| ≤
            beta * S + S := by
        exact hsplit.trans (add_le_add hvbound hcoordPair)
      calc
        |cubeAverage Q
            (fun x ↦ vecDot (F x)
              (v.toH1Function.grad x + coordinateVectorField i t x))| ≤
            beta * S + S := htotal
        _ = (beta + 1) * S := by ring
    · have hnorm :
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F =
            cubeBesovScaleWeight s Q * S := rfl
      rw [hnorm, Fintype.card_fin]
      exact le_of_eq (by ring)

end

end HighContrast
end HCPolySupport
