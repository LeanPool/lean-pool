/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicSlopeDiagonal
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalCauchy
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSuccessorGradient
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCorrector
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.ABK26.LocalCoarseGrainingOneCube

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorIntrinsicSlopeGoodTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Intrinsic slope from a scalar good tail

This module supplies the analytic input missing from the topology-only
diagonal argument.  Cube averages are controlled through the negative Besov
seminorm and the multiscale lower-ellipticity factor, never through a
pointwise ellipticity constant.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem poincareLowerEllipticityFactor_finite_two_eq_sqrt_inv
    {d : ℕ} (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) {s : ℝ} :
    Book.Ch03.poincareLowerEllipticityFactor Q a s (.finite 2) =
      Real.sqrt ((Book.Ch02.lambdaSq Q s (.finite 2) a)⁻¹) := by
  have hleft :
      Real.sqrt ((Book.Ch02.lambdaSq Q s (.finite 2) a)⁻¹) =
        Real.rpow (Book.Ch02.lambdaSq Q s (.finite 2) a) (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow]
    rw [← Real.rpow_eq_pow]
    ring_nf
  have hexponent : (-1 / 2 : ℝ) = (-(1 / 2 : ℝ)) := by ring
  simpa [Book.Ch03.poincareLowerEllipticityFactor, hexponent] using hleft.symm

private theorem scalarIdentityWeakError_le_one_lowerEllipticity
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s : ℝ} (hs : 0 < s) {k : ℤ}
    (herror : scalarIdentityWeakError a s k ≤ 1) :
    (Book.Ch02.lambdaSq (originCube d k) s (.finite 2) a)⁻¹ ≤
      4 * (d : ℝ) := by
  let E := scalarIdentityWeakError a s k
  have hE_nonneg : 0 ≤ E := scalarIdentityWeakError_nonneg a s k
  have hE_sq : E ^ 2 + 1 ≤ 2 := by
    nlinarith only [hE_nonneg, herror]
  have hlower :=
    Book.Ch02.sigma_mul_lambdaSq_finite_two_inv_le_card_mul_homogenizationError_sq_add_one
      (originCube d k) a hs (by norm_num : (0 : ℝ) < 1)
  have hlower' :
      (Book.Ch02.lambdaSq (originCube d k) s (.finite 2) a)⁻¹ ≤
        2 * (d : ℝ) * (E ^ 2 + 1) := by
    simpa [E, scalarIdentityWeakError, scalarMatrix] using hlower
  calc
    (Book.Ch02.lambdaSq (originCube d k) s (.finite 2) a)⁻¹ ≤
        2 * (d : ℝ) * (E ^ 2 + 1) := hlower'
    _ ≤ 2 * (d : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hE_sq (by positivity)
    _ = 4 * (d : ℝ) := by ring

private theorem cubeBesovNegativeVectorDepthSeminorm_le_partialSeminormTwo
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d)
    (N j : ℕ) (hj : j ∈ Finset.range (N + 1)) :
    cubeBesovNegativeVectorDepthSeminorm Q s F j ≤
      cubeBesovNegativeVectorPartialSeminormTwo Q s N F := by
  have hsq :
      (cubeBesovNegativeVectorDepthSeminorm Q s F j) ^ 2 ≤
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N F) ^ 2 := by
    rw [sq_cubeBesovNegativeVectorPartialSeminormTwo]
    exact Finset.single_le_sum
      (fun k _ => sq_nonneg (cubeBesovNegativeVectorDepthSeminorm Q s F k)) hj
  have hdepth : 0 ≤ cubeBesovNegativeVectorDepthSeminorm Q s F j :=
    cubeBesovNegativeVectorDepthSeminorm_nonneg Q s F j
  have hpartial : 0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N F :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N F
  exact (sq_le_sq₀ hdepth hpartial).mp hsq

/-- A descendant cube average is controlled by the parent negative Besov
seminorm, with the explicit finite-depth loss. -/
theorem norm_cubeAverageVec_le_sqrt_card_mul_rpow_mul_negativeSeminormTwo_of_mem_descendant
    {d : ℕ} (Q R : TriadicCube d) (s : ℝ) (j : ℕ)
    (F : Vec d → Vec d)
    (hR : R ∈ descendantsAtDepth Q j)
    (hs : 0 < s)
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ‖cubeAverageVec R F‖ ≤
      Real.sqrt ((descendantsAtDepth Q j).card : ℝ) *
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          cubeBesovNegativeVectorSeminormTwo Q s F := by
  let D := descendantsAtDepth Q j
  have hDcard : D.card ≠ 0 := by
    exact Finset.card_ne_zero.mpr ⟨R, hR⟩
  have hDcardReal : (D.card : ℝ) ≠ 0 := by
    exact_mod_cast hDcard
  have hsingle : vecNormSq (cubeAverageVec R F) ≤
      ∑ S ∈ D, vecNormSq (cubeAverageVec S F) := by
    exact Finset.single_le_sum
      (fun S _ => vecNormSq_nonneg (cubeAverageVec S F)) hR
  have hvalue : vecNormSq (cubeAverageVec R F) ≤
      (D.card : ℝ) * cubeBesovNegativeVectorDepthAverage Q F j := by
    calc
      vecNormSq (cubeAverageVec R F) ≤
          ∑ S ∈ D, vecNormSq (cubeAverageVec S F) := hsingle
      _ = (D.card : ℝ) * cubeBesovNegativeVectorDepthAverage Q F j := by
        dsimp [cubeBesovNegativeVectorDepthAverage, descendantsAverage, D]
        rw [← mul_assoc, mul_inv_cancel₀ hDcardReal, one_mul]
  have hsqrt : ‖cubeAverageVec R F‖ ≤
      Real.sqrt (D.card : ℝ) *
        Real.sqrt (cubeBesovNegativeVectorDepthAverage Q F j) := by
    calc
      ‖cubeAverageVec R F‖ ≤ Real.sqrt (vecNormSq (cubeAverageVec R F)) :=
        norm_le_sqrt_vecNormSq _
      _ ≤ Real.sqrt ((D.card : ℝ) *
          cubeBesovNegativeVectorDepthAverage Q F j) := Real.sqrt_le_sqrt hvalue
      _ = Real.sqrt (D.card : ℝ) *
          Real.sqrt (cubeBesovNegativeVectorDepthAverage Q F j) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ D.card)]
  have hdepth : cubeBesovNegativeVectorDepthSeminorm Q s F j ≤
      cubeBesovNegativeVectorSeminormTwo Q s F := by
    calc
      cubeBesovNegativeVectorDepthSeminorm Q s F j ≤
          cubeBesovNegativeVectorPartialSeminormTwo Q s j F :=
        cubeBesovNegativeVectorDepthSeminorm_le_partialSeminormTwo
          Q s F j j (by simp)
      _ ≤ cubeBesovNegativeVectorSeminormTwo Q s F :=
        cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
          Q s F
          (cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp
            Q hs F hF) j
  have hscale : Real.sqrt (cubeBesovNegativeVectorDepthAverage Q F j) =
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        cubeBesovNegativeVectorDepthSeminorm Q s F j := by
    have hprod : Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) = 1 := by
      have hexp : s * (j : ℝ) + -s * (j : ℝ) = 0 := by ring
      calc
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) =
            Real.rpow (3 : ℝ) (s * (j : ℝ) + -s * (j : ℝ)) :=
          (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
        _ = 1 := by
          rw [hexp]
          exact Real.rpow_zero (3 : ℝ)
    rw [cubeBesovNegativeVectorDepthSeminorm, ← mul_assoc, hprod, one_mul]
  rw [hscale] at hsqrt
  calc
    ‖cubeAverageVec R F‖ ≤ Real.sqrt (D.card : ℝ) *
        (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          cubeBesovNegativeVectorDepthSeminorm Q s F j) := hsqrt
    _ ≤ Real.sqrt (D.card : ℝ) *
        (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          cubeBesovNegativeVectorSeminormTwo Q s F) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdepth (Real.rpow_nonneg (by norm_num) _))
        (Real.sqrt_nonneg _)
    _ = Real.sqrt ((descendantsAtDepth Q j).card : ℝ) *
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          cubeBesovNegativeVectorSeminormTwo Q s F := by
      simp only [D, mul_assoc]

private theorem homogenizationComparisonFluxSeminorm_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch03.CoeffFamily d) (a0 : Book.Ch03.ConstantCoeffMatrix d)
    (s : ℝ) (hs : 0 < s)
    (u v : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d))) :
    0 ≤ cubeBesovNegativeVectorSeminormTwo Q s
      (Book.Ch03.homogenizationComparisonFluxField Q a a0 u v) := by
  have huGrad : MemVectorL2 (cubeSet Q) u.grad := by
    simpa using (Book.Ch03.publicH1ToCubeSet u).grad_memVectorL2
  have hvGrad : MemVectorL2 (cubeSet Q) v.grad := by
    simpa using (Book.Ch03.publicH1ToCubeSet v).grad_memVectorL2
  have hEll0 :
      IsEllipticFieldOn a0.lam a0.Lam (cubeSet Q)
        (constantCoeffField a0.matrix) :=
    Book.Ch03.constantCoeffMatrix_isEllipticFieldOn_constantCoeffField a0
      (measurableSet_cubeSet Q)
  let Ginternal : Vec d → Vec d :=
    fluxComparison (Book.Ch03.publicCoeffField Q a) a0.matrix u.grad v.grad
  have hfluxA : MemVectorL2 (cubeSet Q)
      (fun x ↦ matVecMul (Book.Ch03.publicCoeffField Q a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_cubeSet Q a) huGrad
  have hflux0 : MemVectorL2 (cubeSet Q)
      (fun x ↦ matVecMul a0.matrix (v.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 hvGrad
  have hGinternal : MemVectorL2 (cubeSet Q) Ginternal := by
    dsimp [Ginternal, fluxComparison]
    exact hfluxA.sub hflux0
  have hae :
      Book.Ch03.homogenizationComparisonFluxField Q a a0 u v
        =ᵐ[volumeMeasureOn (cubeSet Q)] Ginternal :=
    Book.Ch03.homogenizationComparisonFluxField_ae_eq_fluxComparison_publicCoeffField_cubeSet
      (Q := Q) (a := a) (a0 := a0) u v
  have hmem : MemVectorL2 (cubeSet Q)
      (Book.Ch03.homogenizationComparisonFluxField Q a a0 u v) :=
    MemLp.ae_eq hae.symm hGinternal
  have hmemNormalized : MemLp
      (Book.Ch03.homogenizationComparisonFluxField Q a a0 u v)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hmem
  exact cubeBesovNegativeVectorSeminormTwo_nonneg_of_memLp
    Q hs _ hmemNormalized

private theorem finiteAffineCorrection_grad_eq_comparisonGradient
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (e : Vec d) :
    (finiteAffineCorrection a m e).toH1Function.grad =
      Book.Ch03.homogenizationComparisonConstantGradientField
        (identityConstantCoeffMatrix d) (finiteAffineSolution a m e).toH1
        (finiteAffineBoundaryH1 m e) := by
  funext x
  rw [finiteAffineSolution_toH1]
  simp only [Book.Ch03.homogenizationComparisonConstantGradientField,
    identityConstantCoeffMatrix_matrix, HCPolySupport.matVecMul_one,
    H1Function.add_grad, finiteAffineBoundaryH1_grad]
  abel

private theorem originCube_pred_mem_childCubes_originCube
    {d : ℕ} (s : ℤ) :
    originCube d (s - 1) ∈ childCubes (originCube d s) := by
  rw [mem_childCubes_iff]
  refine ⟨fun _ => (1 : Fin 3), ?_⟩
  simp only [originCube]
  apply congrArg₂ TriadicCube.mk
  · rfl
  · funext i
    norm_num

private theorem originCube_depth_two_descendant
    {d q : ℕ} :
    originCube d (q : ℤ) ∈
      descendantsAtDepth (originCube d ((q + 2 : ℕ) : ℤ)) 2 := by
  rw [show 2 = 1 + 1 by omega, descendantsAtDepth_succ,
    descendantsAtDepth_one]
  refine Finset.mem_biUnion.mpr ⟨originCube d ((q + 1 : ℕ) : ℤ), ?_, ?_⟩
  · have hscale : ((q + 2 : ℕ) : ℤ) - 1 = ((q + 1 : ℕ) : ℤ) := by omega
    simpa only [hscale] using
      originCube_pred_mem_childCubes_originCube (d := d) (((q + 2 : ℕ) : ℤ))
  · have hscale : ((q + 1 : ℕ) : ℤ) - 1 = (q : ℤ) := by omega
    simpa only [hscale] using
      originCube_pred_mem_childCubes_originCube (d := d) (((q + 1 : ℕ) : ℤ))

/-- The average gradient of the finite correction two scales inside its
Dirichlet cube is controlled by the corrected scalar weak error. -/
theorem exists_finiteAffineCorrectionDepthTwoGradientAverageEstimateConstant
    (d : ℕ) [NeZero d] (sOut b : ℝ)
    (hb : 0 < b) (h2b : 2 * b < sOut) (hsOut_lt : sOut < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (q : ℕ) (e : Vec d),
        ‖cubeAverageVec (originCube d (q : ℤ))
            (finiteAffineCorrection a ((q + 2 : ℕ) : ℤ) e).toH1Function.grad‖ ≤
          C * scalarIdentityCorrectedWeakError a b
            ((q + 2 : ℕ) : ℤ) * euclideanNorm e := by
  obtain ⟨Cweak, hCweak, hweak⟩ :=
    exists_finiteAffineSolutionNegativeBesovEstimateConstant_at_error_order
      d sOut b hb h2b hsOut_lt
  have hsOut : 0 < sOut :=
    (mul_pos (by norm_num : (0 : ℝ) < 2) hb).trans h2b
  let A : ℝ := Real.sqrt ((descendantsAtDepth
      (originCube d (2 : ℤ)) 2).card : ℝ) *
    Real.rpow (3 : ℝ) (sOut * (2 : ℝ))
  let C : ℝ := A * Cweak
  have hA : 0 < A := by
    have hcard : 0 < ((descendantsAtDepth
        (originCube d (2 : ℤ)) 2).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr
        ⟨originCube d (0 : ℤ), originCube_depth_two_descendant (d := d) (q := 0)⟩
    exact mul_pos (Real.sqrt_pos.2 hcard)
      (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C, mul_pos hA hCweak, ?_⟩
  intro a q e
  let Q : TriadicCube d := originCube d ((q + 2 : ℕ) : ℤ)
  let R : TriadicCube d := originCube d (q : ℤ)
  let F : Vec d → Vec d :=
    (finiteAffineCorrection a ((q + 2 : ℕ) : ℤ) e).toH1Function.grad
  let N : ℝ := cubeBesovNegativeVectorSeminormTwo Q sOut F
  let L : ℝ := Book.Ch03.homogenizationComparisonNegativeBesovLHS Q a
    (identityConstantCoeffMatrix d) sOut
    (finiteAffineSolution a ((q + 2 : ℕ) : ℤ) e).toH1
    (finiteAffineBoundaryH1 ((q + 2 : ℕ) : ℤ) e)
  have hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa only [F, Q] using
      (MemLp.of_eval (fun i : Fin d =>
        (finiteAffineCorrection a ((q + 2 : ℕ) : ℤ) e).toH1Function
          |>.grad_memL2_normalizedCubeMeasure i))
  have hdesc : R ∈ descendantsAtDepth Q 2 := by
    exact originCube_depth_two_descendant
  have havg : ‖cubeAverageVec R F‖ ≤
      Real.sqrt ((descendantsAtDepth Q 2).card : ℝ) *
        Real.rpow (3 : ℝ) (sOut * (2 : ℝ)) * N := by
    exact norm_cubeAverageVec_le_sqrt_card_mul_rpow_mul_negativeSeminormTwo_of_mem_descendant
      Q R sOut 2 F hdesc hsOut hF
  have hflux : 0 ≤ cubeBesovNegativeVectorSeminormTwo Q sOut
      (Book.Ch03.homogenizationComparisonFluxField Q a
        (identityConstantCoeffMatrix d)
        (finiteAffineSolution a ((q + 2 : ℕ) : ℤ) e).toH1
        (finiteAffineBoundaryH1 ((q + 2 : ℕ) : ℤ) e)) :=
    homogenizationComparisonFluxSeminorm_nonneg Q a
      (identityConstantCoeffMatrix d) sOut hsOut _ _
  have hNL : N ≤ L := by
    have hgrad := finiteAffineCorrection_grad_eq_comparisonGradient
      a ((q + 2 : ℕ) : ℤ) e
    dsimp only [N, L, F]
    rw [Book.Ch03.homogenizationComparisonNegativeBesovLHS, hgrad]
    exact le_add_of_nonneg_right hflux
  have hL : L ≤ Cweak * scalarIdentityCorrectedWeakError a b
      ((q + 2 : ℕ) : ℤ) * euclideanNorm e := by
    simpa only [L, Q, scalarIdentityCorrectedWeakError, mul_assoc] using
      hweak a ((q + 2 : ℕ) : ℤ) e
  have hfactor : 0 ≤ Real.sqrt ((descendantsAtDepth Q 2).card : ℝ) *
      Real.rpow (3 : ℝ) (sOut * (2 : ℝ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  calc
    ‖cubeAverageVec (originCube d (q : ℤ))
        (finiteAffineCorrection a ((q + 2 : ℕ) : ℤ) e).toH1Function.grad‖ =
        ‖cubeAverageVec R F‖ := rfl
    _ ≤ Real.sqrt ((descendantsAtDepth Q 2).card : ℝ) *
        Real.rpow (3 : ℝ) (sOut * (2 : ℝ)) * N := havg
    _ ≤ Real.sqrt ((descendantsAtDepth Q 2).card : ℝ) *
        Real.rpow (3 : ℝ) (sOut * (2 : ℝ)) * L :=
      mul_le_mul_of_nonneg_left hNL hfactor
    _ ≤ Real.sqrt ((descendantsAtDepth Q 2).card : ℝ) *
        Real.rpow (3 : ℝ) (sOut * (2 : ℝ)) *
          (Cweak * scalarIdentityCorrectedWeakError a b
            ((q + 2 : ℕ) : ℤ) * euclideanNorm e) :=
      mul_le_mul_of_nonneg_left hL hfactor
    _ = C * scalarIdentityCorrectedWeakError a b
          ((q + 2 : ℕ) : ℤ) * euclideanNorm e := by
      have hcardEq : (descendantsAtDepth Q 2).card =
          (descendantsAtDepth (originCube d (2 : ℤ)) 2).card := by
        rw [descendantsAtDepth_card, descendantsAtDepth_card]
      rw [hcardEq]
      dsimp [C, A]
      ring

private theorem normalizedLocalH1_finiteAffineCorrection_grad
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k : ℕ) :
    (normalizedLocalH1
      (finiteAffineCorrectionLocalSequence a e) q k).grad =
        (finiteAffineCorrectionLocalSequence a e (q + k)).grad := by
  funext x
  change
    (normalizeOnUnitCube
      (finiteAffineCorrectionLocalSequence a e (q + k))).grad x =
        (finiteAffineCorrectionLocalSequence a e (q + k)).grad x
  rw [normalizeOnUnitCube_grad]

private theorem gradToHilbertVectorL2_sub {d : ℕ} {U : Set (Vec d)}
    (u v : H1Function U) :
    (u - v).gradToHilbertVectorL2 =
      u.gradToHilbertVectorL2 - v.gradToHilbertVectorL2 := by
  rw [sub_eq_add_neg, H1Function.gradToHilbertVectorL2_add]
  have hneg := H1Function.gradToHilbertVectorL2_smul (-1 : ℝ) v
  rw [show (-v : H1Function U) = (-1 : ℝ) • v by rfl, hneg]
  simp only [neg_smul, one_smul, sub_eq_add_neg]

private theorem gradToHilbertVectorL2_eq_of_grad_eq {d : ℕ}
    {U : Set (Vec d)} (u v : H1Function U) (hgrad : u.grad = v.grad) :
    u.gradToHilbertVectorL2 = v.gradToHilbertVectorL2 := by
  apply Lp.ext
  filter_upwards
      [u.coeFn_gradToHilbertVectorL2,
        v.coeFn_gradToHilbertVectorL2]
    with x hu hv
  rw [hu, hv, hgrad]

private theorem normalizedFiniteCorrection_successor_gradient_eq
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k r : ℕ) (hqr : q ≤ r)
    (hrm : (r : ℤ) ≤ ((q + k : ℕ) : ℤ)) :
    (normalizedLocalH1
          (finiteAffineCorrectionLocalSequence a e) q
          (k + 1)).gradToHilbertVectorL2 -
        (normalizedLocalH1
          (finiteAffineCorrectionLocalSequence a e) q k).gradToHilbertVectorL2 =
      localGradientRestrict hqr
        (finiteCubeSolutionRestriction a hrm
          (finiteAffineSuccessorDifference a
            ((q + k : ℕ) : ℤ) e)).toH1.gradToHilbertVectorL2 := by
  let w : H1Function (localGradientCube d r) := by
    simp only [localGradientCube]
    exact (finiteCubeSolutionRestriction a hrm
      (finiteAffineSuccessorDifference a ((q + k : ℕ) : ℤ) e)).toH1
  have hcast :
      (finiteCubeSolutionRestriction a hrm
          (finiteAffineSuccessorDifference a
            ((q + k : ℕ) : ℤ) e)).toH1.gradToHilbertVectorL2 =
        w.gradToHilbertVectorL2 := rfl
  rw [hcast, ← gradToHilbertVectorL2_sub,
    localGradientRestrict_gradToHilbertVectorL2_restrictLocalH1]
  apply gradToHilbertVectorL2_eq_of_grad_eq
  funext x
  rw [H1Function.sub_grad,
    normalizedLocalH1_finiteAffineCorrection_grad,
    normalizedLocalH1_finiteAffineCorrection_grad]
  change _ =
    (finiteCubeSolutionRestriction a hrm
      (finiteAffineSuccessorDifference a ((q + k : ℕ) : ℤ) e)).toH1.grad x
  rw [finiteCubeSolutionRestriction_grad,
    finiteAffineSuccessorDifference_grad]
  have hindex : ((q + (k + 1) : ℕ) : ℤ) =
      ((q + k : ℕ) : ℤ) + 1 := by omega
  change
    (finiteAffineCorrection a
          ((q + (k + 1) : ℕ) : ℤ) e).toH1Function.grad x -
        (finiteAffineCorrection a
          ((q + k : ℕ) : ℤ) e).toH1Function.grad x =
      (finiteAffineCubeSolution a
          (((q + k : ℕ) : ℤ) + 1) e).toH1.grad x -
        (finiteAffineCubeSolution a
          ((q + k : ℕ) : ℤ) e).toH1.grad x
  rw [hindex]
  simp only [finiteAffineCubeSolution, finiteAffineSolution_toH1,
    H1Function.add_grad, finiteAffineBoundaryH1_grad]
  abel

private theorem localGradientClassAverage_restrictedH1Gradient
    {d m n : ℕ} (hmn : m ≤ n)
    (u : H1Function (localGradientCube d n)) :
    localGradientClassAverage
        (localGradientRestrict hmn u.gradToHilbertVectorL2) =
      cubeAverageVec (originCube d (m : ℤ)) u.grad := by
  apply localGradientClassAverage_eq_cubeAverageVec_of_ae
  let hmu : volumeMeasureOn (localGradientCube d m) ≤
      volumeMeasureOn (localGradientCube d n) :=
    Measure.restrict_mono_set volume (localGradientCube_mono hmn)
  exact
    (localGradientRestrict_coeFn_ae hmn u.gradToHilbertVectorL2).trans
      (u.coeFn_gradToHilbertVectorL2.filter_mono (ae_mono hmu))

private theorem finiteAffineCorrectionLocalGradientAverage_eq_cubeAverageVec
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k : ℕ) :
    localGradientClassAverage
        (normalizedLocalPair
          (finiteAffineCorrectionLocalSequence a e) q k).2 =
      cubeAverageVec (originCube d (q : ℤ))
        (finiteAffineCorrectionLocalSequence a e (q + k)).grad := by
  rw [normalizedLocalPair_gradient_eq]
  exact localGradientClassAverage_restrictedH1Gradient
    (Nat.le_add_right q k) (finiteAffineCorrectionLocalSequence a e (q + k))

/-- Under a unit scalar weak-error bound, the average gradient of a cube
solution is controlled by its normalized coefficient-energy norm, with a
constant depending only on dimension and the weak-norm order. -/
theorem exists_cubeSolutionGradientAverageEnergyConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (k : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d k) a),
        scalarIdentityWeakError a s k ≤ 1 →
          ‖cubeAverageVec (originCube d k) u.toH1.grad‖ ≤
            C * Book.Ch03.h1EnergyNormOnCube
              (originCube d k) a u.toH1 := by
  let B : ℝ := Book.Ch03.poincareDiscountFactor s (.finite 2)
  let L : ℝ := Real.sqrt (4 * (d : ℝ))
  let C : ℝ := B * L
  have hB : 0 < B := by
    dsimp [B, Book.Ch03.poincareDiscountFactor]
    exact Real.rpow_pos_of_pos
      (HCPolySupport.geometricDiscount_pos (by positivity : 0 < s * (2 : ℝ))) _
  have hL : 0 < L := by
    dsimp [L]
    have hd : (0 : ℝ) < d := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact Real.sqrt_pos.2 (mul_pos (by norm_num) hd)
  refine ⟨C, mul_pos hB hL, ?_⟩
  intro a k u herror
  let Q : TriadicCube d := originCube d k
  let N : ℝ := cubeBesovNegativeVectorSeminormTwo Q s u.toH1.grad
  let D : ℝ := Book.Ch03.h1EnergyNormOnCube Q a u.toH1
  have hmem : MemLp u.toH1.grad (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    by
      simpa only [Q] using
        (MemLp.of_eval (fun i : Fin d =>
          u.toH1.grad_memL2_normalizedCubeMeasure i))
  have hN_nonneg : 0 ≤ N :=
    cubeBesovNegativeVectorSeminormTwo_nonneg_of_memLp Q hs _ hmem
  have havgENN :=
    Book.Ch03.ABK26.ENNReal_ofReal_norm_cubeAverageVec_le_cubeBesovNegativeVectorSeminormTwo
      Q hs u.toH1.grad hmem
  have havg : ‖cubeAverageVec Q u.toH1.grad‖ ≤ N :=
    (ENNReal.ofReal_le_ofReal_iff hN_nonneg).1 havgENN
  have hnegative : N ≤ Book.Ch03.coarsePoincareGradientRHS Q a s (.finite 2) u := by
    simpa only [N,
      Book.Ch03.scaleNegativeBesovVectorNorm_finiteTwo_eq_cubeNegativeSeminorm]
      using! Book.Ch03.coarsePoincareGradient_negativeBesov_le
        Q a u hs (q := .finite 2) (by norm_num)
  have hlower :
      Book.Ch03.poincareLowerEllipticityFactor Q a s (.finite 2) ≤ L := by
    rw [poincareLowerEllipticityFactor_finite_two_eq_sqrt_inv]
    exact Real.sqrt_le_sqrt
      (by simpa only [Q, L] using
        scalarIdentityWeakError_le_one_lowerEllipticity hs herror)
  have hD_nonneg : 0 ≤ D := by
    dsimp [D, Book.Ch03.h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  calc
    ‖cubeAverageVec (originCube d k) u.toH1.grad‖ =
        ‖cubeAverageVec Q u.toH1.grad‖ := rfl
    _ ≤ N := havg
    _ ≤ Book.Ch03.coarsePoincareGradientRHS Q a s (.finite 2) u := hnegative
    _ = B * Book.Ch03.poincareLowerEllipticityFactor Q a s (.finite 2) * D := by
      rfl
    _ ≤ B * L * D := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlower hB.le) hD_nonneg
    _ = C * Book.Ch03.h1EnergyNormOnCube (originCube d k) a u.toH1 := rfl

/-- A finite good tail uniformly controls the average gradient of every
successive finite-corrector difference on an inner centered cube. -/
theorem exists_finiteAffineSuccessorGradientAverageEstimateConstant
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 0 < C ∧ c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ)
        (n m : ℤ) (e : Vec d),
        delta ∈ Set.Ioc (0 : ℝ) c →
        n ≤ m - 2 →
        ScalarIdentityGoodTailOnInterval a s delta n (m + 1) →
          ‖cubeAverageVec (originCube d n)
              (finiteAffineSuccessorDifference a m e).toH1.grad‖ ≤
            C * (scalarIdentityCorrectedWeakError a s m +
              scalarIdentityCorrectedWeakError a s (m + 1)) *
                euclideanNorm e := by
  obtain ⟨Cavg, hCavg, havg⟩ :=
    exists_cubeSolutionGradientAverageEnergyConstant d s hs
  obtain ⟨Cstep, c, hCstep, hc, hstep⟩ :=
    exists_finiteAffineSuccessorWeightedGradientEstimateConstant
      d s hs hs_lt
  let C : ℝ := Cavg * Cstep
  refine ⟨C, c, mul_pos hCavg hCstep, hc, ?_⟩
  intro a delta n m e hdelta hnm hgood
  let u : Book.Ch03.CubeSolution (originCube d n) a :=
    finiteCubeSolutionRestriction a (by omega : n ≤ m)
      (finiteAffineSuccessorDifference a m e)
  let B : ℝ := Cstep *
    (scalarIdentityCorrectedWeakError a s m +
      scalarIdentityCorrectedWeakError a s (m + 1)) * euclideanNorm e
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg hCstep.le
        (add_nonneg
          (scalarIdentityCorrectedWeakError_nonneg a s m)
          (scalarIdentityCorrectedWeakError_nonneg a s (m + 1))))
      (euclideanNorm_nonneg e)
  have hweighted :
      weightedGradNorm (a.coeffOn (originCube d n)).toCoeffField
          (openCubeSet (originCube d n)) u.toH1.grad ≤ ENNReal.ofReal B := by
    simpa only [u, B, finiteCubeSolutionRestriction_grad] using
      hstep a delta n m e hdelta hnm hgood
  have henergy :
      Book.Ch03.h1EnergyNormOnCube (originCube d n) a u.toH1 ≤ B := by
    rw [weightedGradNorm_eq_ofReal_h1EnergyNormOnCube] at hweighted
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 hweighted
  have herror : scalarIdentityWeakError a s n ≤ 1 := by
    have hsingle : scalarIdentityWeakError a s n ≤
        ∑ k ∈ Finset.Icc n (m + 1), scalarIdentityWeakError a s k := by
      exact Finset.single_le_sum
        (fun k _ => scalarIdentityWeakError_nonneg a s k)
        (by simp only [Finset.mem_Icc]; omega)
    exact (hsingle.trans hgood).trans (hdelta.2.trans hc.2.le)
  calc
    ‖cubeAverageVec (originCube d n)
        (finiteAffineSuccessorDifference a m e).toH1.grad‖ =
        ‖cubeAverageVec (originCube d n) u.toH1.grad‖ := by
      congr 2
    _ ≤ Cavg * Book.Ch03.h1EnergyNormOnCube
          (originCube d n) a u.toH1 := havg a n u herror
    _ ≤ Cavg * B := mul_le_mul_of_nonneg_left henergy hCavg.le
    _ = C * (scalarIdentityCorrectedWeakError a s m +
        scalarIdentityCorrectedWeakError a s (m + 1)) *
          euclideanNorm e := by
      dsimp [B, C]
      ring

/-- Every sufficiently small scalar good tail produces the canonical
intrinsically normalized corrector with the prescribed affine slope. -/
theorem exists_scalarIdentityGoodTailIntrinsicSlopeThreshold
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ e : Vec d,
          ∃ hloc : FiniteAffineCorrectionLocalCauchy a,
            HasIntrinsicNormalizedSlope e
              (finiteAffineCorrectionJointLocalLimit a hloc e) := by
  obtain ⟨cCauchy, hcCauchy, hCauchy⟩ :=
    exists_finiteAffineCorrectionLocalCauchyThreshold d s hs hs_lt
  obtain ⟨Cstep, cStep, hCstep, hcStep, hstep⟩ :=
    exists_finiteAffineSuccessorGradientAverageEstimateConstant
      d s hs hs_lt
  obtain ⟨Cinit, hCinit, hinit⟩ :=
    exists_finiteAffineCorrectionDepthTwoGradientAverageEstimateConstant
      d (s + 1 / 2) s hs (by linarith only [hs_lt])
        (by linarith only [hs_lt])
  let c : ℝ := min cCauchy cStep
  have hc : c ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨lt_min hcCauchy.1 hcStep.1,
      (min_le_left cCauchy cStep).trans_lt hcCauchy.2⟩
  refine ⟨c, hc, ?_⟩
  intro a delta n hdelta hgood e
  have hdeltaCauchy : delta ∈ Set.Ioc (0 : ℝ) cCauchy :=
    ⟨hdelta.1, hdelta.2.trans (min_le_left _ _)⟩
  have hdeltaStep : delta ∈ Set.Ioc (0 : ℝ) cStep :=
    ⟨hdelta.1, hdelta.2.trans (min_le_right _ _)⟩
  let hloc : FiniteAffineCorrectionLocalCauchy a :=
    hCauchy a delta n hdeltaCauchy hgood
  refine ⟨hloc, ?_⟩
  let r0 : ℕ := n.toNat
  have hnr0 : n ≤ (r0 : ℤ) := Int.self_le_toNat n
  have hgoodR : ScalarIdentityGoodTail a s delta (r0 : ℤ) :=
    hgood.mono_start hnr0
  let E : ℕ → ℝ := fun j =>
    scalarIdentityCorrectedWeakError a s ((r0 + j : ℕ) : ℤ)
  let epsilon : ℕ → ℝ := fun j => E (j + 2) + E (j + 3)
  have hEsum : Summable E := by
    simpa only [E, Int.natCast_add]
      using hgoodR.summable_corrected_nat_shift
  have hepsilon : Summable epsilon := by
    have htwo : Summable (fun j => E (j + 2)) :=
      (summable_nat_add_iff 2).2 hEsum
    have hthree : Summable (fun j => E (j + 3)) :=
      (summable_nat_add_iff 3).2 hEsum
    simpa only [epsilon] using htwo.add hthree
  let x : ℕ → ℕ → Vec d := fun q k =>
    localGradientClassAverage
      (normalizedLocalPair
        (finiteAffineCorrectionLocalSequence a e) (r0 + q) (k + 2)).2
  let L : ℕ → Vec d := fun q =>
    localGradientClassAverage
      ((finiteAffineCorrectionJointLocalLimit a hloc e).gradientComponent
        (r0 + q))
  have hrow : ∀ q, Filter.Tendsto (x q) Filter.atTop (nhds (L q)) := by
    intro q
    exact (finiteAffineCorrectionLocalGradientAverage_tendsto
      a hloc e (r0 + q)).comp (Filter.tendsto_add_atTop_nat 2)
  have hepsilon_nonneg : ∀ j, 0 ≤ epsilon j := by
    intro j
    exact add_nonneg
      (scalarIdentityCorrectedWeakError_nonneg a s _)
      (scalarIdentityCorrectedWeakError_nonneg a s _)
  have hdiagBound : ∀ q, ‖x q 0‖ ≤ Cinit * epsilon q * euclideanNorm e := by
    intro q
    rw [show x q 0 = localGradientClassAverage
      (normalizedLocalPair
        (finiteAffineCorrectionLocalSequence a e) (r0 + q) 2).2 by rfl]
    rw [finiteAffineCorrectionLocalGradientAverage_eq_cubeAverageVec]
    have hbase := hinit a (r0 + q) e
    have hfirst : scalarIdentityCorrectedWeakError a s
        (((r0 + q) + 2 : ℕ) : ℤ) ≤ epsilon q := by
      exact le_add_of_nonneg_right
        (scalarIdentityCorrectedWeakError_nonneg a s _)
    calc
      ‖cubeAverageVec (originCube d ((r0 + q : ℕ) : ℤ))
          (finiteAffineCorrectionLocalSequence a e (r0 + q + 2)).grad‖ ≤
          Cinit * scalarIdentityCorrectedWeakError a s
            (((r0 + q) + 2 : ℕ) : ℤ) * euclideanNorm e := by
        have heq : (finiteAffineCorrectionLocalSequence a e (r0 + q + 2)).grad =
            (finiteAffineCorrection a (((r0 + q) + 2 : ℕ) : ℤ) e).toH1Function.grad :=
          rfl
        rw [heq]
        exact hbase
      _ ≤ Cinit * epsilon q * euclideanNorm e :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfirst hCinit.le)
          (euclideanNorm_nonneg e)
  have hdiag : Filter.Tendsto (fun q => x q 0) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun q => norm_nonneg (x q 0))
      (Filter.Eventually.of_forall hdiagBound)
    have hepsZero : Filter.Tendsto epsilon Filter.atTop (nhds 0) :=
      hepsilon.tendsto_atTop_zero
    convert (tendsto_const_nhds.mul hepsZero).mul tendsto_const_nhds using 1
    all_goals simp
  have hsuccessive : ∀ q k,
      ‖x q (k + 1) - x q k‖ ≤
        (Cstep * euclideanNorm e) * epsilon (q + k) := by
    intro q k
    let q0 : ℕ := r0 + q
    let m : ℤ := ((q0 + (k + 2) : ℕ) : ℤ)
    let w : Book.Ch03.CubeSolution (originCube d (q0 : ℤ)) a :=
      finiteCubeSolutionRestriction a (by omega : (q0 : ℤ) ≤ m)
        (finiteAffineSuccessorDifference a m e)
    let w' : H1Function (localGradientCube d q0) := by
      simp only [localGradientCube]
      exact w.toH1
    have hwcast : w.toH1.gradToHilbertVectorL2 = w'.gradToHilbertVectorL2 := rfl
    have hwgradcast : w.toH1.grad = w'.grad := rfl
    have hinterval : ScalarIdentityGoodTailOnInterval a s delta
        (q0 : ℤ) (m + 1) :=
      (hgood.interval (by omega)).mono_start (by omega)
    have hclass :
        (normalizedLocalPair
              (finiteAffineCorrectionLocalSequence a e) q0 (k + 3)).2 -
            (normalizedLocalPair
              (finiteAffineCorrectionLocalSequence a e) q0 (k + 2)).2 =
          w.toH1.gradToHilbertVectorL2 := by
      have hraw := normalizedFiniteCorrection_successor_gradient_eq
        a e q0 (k + 2) q0 le_rfl (by omega : (q0 : ℤ) ≤ ((q0 + (k + 2) : ℕ) : ℤ))
      have hrawcast :
          (finiteCubeSolutionRestriction a
              (by omega : (q0 : ℤ) ≤ ((q0 + (k + 2) : ℕ) : ℤ))
              (finiteAffineSuccessorDifference a
                ((q0 + (k + 2) : ℕ) : ℤ) e)).toH1.gradToHilbertVectorL2 =
            w'.gradToHilbertVectorL2 := rfl
      rw [hrawcast, localGradientRestrict_refl, ContinuousLinearMap.id_apply] at hraw
      simpa only [normalizedLocalPair, q0, m, w, hwcast] using hraw
    have havg :
        localGradientClassAverage
          (w.toH1.gradToHilbertVectorL2) =
            cubeAverageVec (originCube d (q0 : ℤ))
              (finiteAffineSuccessorDifference a m e).toH1.grad := by
      calc
        localGradientClassAverage (w.toH1.gradToHilbertVectorL2) =
            cubeAverageVec (originCube d (q0 : ℤ)) w.toH1.grad := by
          rw [hwcast, hwgradcast]
          have hraw := localGradientClassAverage_restrictedH1Gradient
            (le_refl q0) w'
          rwa [localGradientRestrict_refl, ContinuousLinearMap.id_apply] at hraw
        _ = cubeAverageVec (originCube d (q0 : ℤ))
              (finiteAffineSuccessorDifference a m e).toH1.grad := by
          simp only [w, finiteCubeSolutionRestriction_grad]
    rw [← localGradientClassAverage_sub, hclass, havg]
    have hbound := hstep a delta (q0 : ℤ) m e hdeltaStep
      (by omega) hinterval
    dsimp only [epsilon, E]
    have hm0 : m = ((r0 + (q + k + 2) : ℕ) : ℤ) := by
      dsimp [m, q0]
      omega
    have hmSucc : ((r0 + (q + k + 2) : ℕ) : ℤ) + 1 =
        ((r0 + (q + k + 3) : ℕ) : ℤ) := by
      omega
    rw [hm0]
    rw [hm0, hmSucc] at hbound
    convert hbound using 1
    all_goals ring
  have hshift : Filter.Tendsto L Filter.atTop (nhds 0) :=
    tendsto_zero_of_summable_successive_norm_le_of_diagonal_tendsto
      x L epsilon (Cstep * euclideanNorm e) hepsilon hrow hdiag hsuccessive
  apply HasVanishingCorrectorGradientAverage.hasIntrinsicNormalizedSlope
  apply (Filter.tendsto_add_atTop_iff_nat r0).1
  convert hshift using 1
  funext q
  dsimp only [L]
  rw [Nat.add_comm]

end

end HighContrast
end HCPolySupport
