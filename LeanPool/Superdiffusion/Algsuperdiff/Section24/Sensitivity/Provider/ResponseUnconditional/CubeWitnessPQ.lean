/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional.TermARefined
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.CubePotentialDh

/-!
# CubeWitnessPQ

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The zero-trace witness budget at a general loading

Source: ABK26 (`e.split.besov.stuff.begin`), at the **general** loading `(p,
q)` and at an arbitrary triadic cube `R`.

`Provider.BigLambda.CubeWitness` proves the same budget at the pure-potential
loading `q = 0`, where the adjoint response coincides with the primal one and
the loading term `|p|` is controlled by `J(R,p,0)` alone.  At a general loading
two changes occur, and neither is a specialization of the other:

* the adjoint maximizer solves the `(p, -q)` problem for `aᵗ`, and
  `Provider.DhBound.Discharge.responseJ_transpose_neg_right` gives
  `J(R, aᵗ, p, -q) = J(R, a, p, q) + 2 p·q`, i.e. an extra `|p·q|` term under the
  square root;
* the ellipticity chain
  `Provider.DhBound.Discharge.vecNormSq_le_matrixNorm_sigmaStarInvCoarse_mul_two_mul_add`
  keeps its cross term, so `|p| ≲ λ^{-1/2} (J^{1/2} + |p·q|^{1/2})`.

The resulting budget is a clean multiple of
`λ_{3/8,2}^{-1/2}(R) ( J(R,p,q)^{1/2} + |p·q|^{1/2} )`.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.BigLambda
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The ellipticity chain at a general loading -/

/-- **The ellipticity chain at a general triadic cube and a general loading.** -/
theorem vecNormSq_le_lambdaSq_inv_mul_two_mul_add [NeZero d]
    (R : TriadicCube d) (G : Ch02.TriadicCoeffFamily d) (b : CoeffOn (cubeDomain R))
    (hG : CoeffOn.AEEq (G.coeffOn R) b) (p q : Vec d) :
    vecNormSq p ≤ (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ *
      (2 * (responseJ (cubeDomain R) b p q + |vecDot p q|)) := by
  have hchain :=
    vecNormSq_le_matrixNorm_sigmaStarInvCoarse_mul_two_mul_add (cubeDomain R) b p q
  have hmat : Ch02.coarseSigmaStarInvMatrixNorm R G =
      Ch02.matrixNorm (Ch02.sigmaStarInvCoarse (cubeDomain R) b) := by
    unfold Ch02.coarseSigmaStarInvMatrixNorm
    rw [Ch02.sigmaStarInvCoarse_eq_ofAEEq hG]
  have hbound := Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv R G
    (s := (3 / 8 : ℝ)) (q := (2 : ℝ)) (by norm_num) (by norm_num)
  rw [hmat] at hbound
  have hJnn : 0 ≤ responseJ (cubeDomain R) b p q :=
    Ch02.responseJ_nonneg (cubeDomain R) b p q
  have hmnn : (0 : ℝ) ≤ Ch02.matrixNorm (Ch02.sigmaStarInvCoarse (cubeDomain R) b) :=
    Ch02.matrixNorm_nonneg _
  have habs : vecDot p q ≤ |vecDot p q| := le_abs_self _
  have hstep1 : vecNormSq p ≤
      Ch02.matrixNorm (Ch02.sigmaStarInvCoarse (cubeDomain R) b) *
        (2 * (responseJ (cubeDomain R) b p q + |vecDot p q|)) := by
    refine hchain.trans (mul_le_mul_of_nonneg_left ?_ hmnn)
    linarith
  refine hstep1.trans (mul_le_mul_of_nonneg_right hbound ?_)
  have : (0 : ℝ) ≤ |vecDot p q| := abs_nonneg _
  linarith

/-- **The loading budget at a general triadic cube and a general loading.** -/
theorem vecNorm_le_sqrt_two_mul_sqrt_add [NeZero d]
    (R : TriadicCube d) (G : Ch02.TriadicCoeffFamily d) (b : CoeffOn (cubeDomain R))
    (hG : CoeffOn.AEEq (G.coeffOn R) b) (p q : Vec d) :
    vecNorm p ≤ Real.sqrt 2 *
      (Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) *
        (Real.sqrt (responseJ (cubeDomain R) b p q) +
          Real.sqrt |vecDot p q|)) := by
  set L : ℝ := (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ with hL
  set J : ℝ := responseJ (cubeDomain R) b p q with hJ
  set T : ℝ := |vecDot p q| with hT
  have hLnn : 0 ≤ L := lambdaSq_inv_nonneg R G
  have hJnn : 0 ≤ J := Ch02.responseJ_nonneg (cubeDomain R) b p q
  have hTnn : 0 ≤ T := abs_nonneg _
  have hmain := vecNormSq_le_lambdaSq_inv_mul_two_mul_add R G b hG p q
  have hsqL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLnn
  have hsqJ : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJnn
  have hsqT : Real.sqrt T ^ 2 = T := Real.sq_sqrt hTnn
  have hs2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hcross : (0 : ℝ) ≤ 2 * Real.sqrt J * Real.sqrt T :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hrhs : (0 : ℝ) ≤
      Real.sqrt 2 * (Real.sqrt L * (Real.sqrt J + Real.sqrt T)) := by positivity
  have hsq : vecNormSq p ≤
      (Real.sqrt 2 * (Real.sqrt L * (Real.sqrt J + Real.sqrt T))) ^ 2 := by
    have hexp : (Real.sqrt 2 * (Real.sqrt L * (Real.sqrt J + Real.sqrt T))) ^ 2 =
        2 * (L * (J + 2 * Real.sqrt J * Real.sqrt T + T)) := by
      calc (Real.sqrt 2 * (Real.sqrt L * (Real.sqrt J + Real.sqrt T))) ^ 2
          = Real.sqrt 2 ^ 2 * (Real.sqrt L ^ 2 *
              (Real.sqrt J ^ 2 + 2 * Real.sqrt J * Real.sqrt T +
                Real.sqrt T ^ 2)) := by ring
        _ = 2 * (L * (J + 2 * Real.sqrt J * Real.sqrt T + T)) := by
            rw [hs2, hsqL, hsqJ, hsqT]
    rw [hexp]
    have hmain' : vecNormSq p ≤ L * (2 * (J + T)) := hmain
    nlinarith [hmain', mul_nonneg hLnn hcross]
  have hvn : (0 : ℝ) ≤ vecNorm p := Ch02.vecNorm_nonneg p
  nlinarith [Ch02.vecNorm_sq_eq_vecNormSq p, hsq, hrhs, hvn]

/-! ## The adjoint budget at a general loading -/

theorem sqrt_add_two_mul_vecDot_le {J t : ℝ} (hJ : 0 ≤ J) :
    Real.sqrt (J + 2 * t) ≤ Real.sqrt J + Real.sqrt 2 * Real.sqrt |t| := by
  have hTnn : (0 : ℝ) ≤ |t| := abs_nonneg _
  have hrhs : (0 : ℝ) ≤ Real.sqrt J + Real.sqrt 2 * Real.sqrt |t| := by positivity
  have hsqJ : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJ
  have hsqT : Real.sqrt |t| ^ 2 = |t| := Real.sq_sqrt hTnn
  have hs2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hcross : (0 : ℝ) ≤ 2 * Real.sqrt J * (Real.sqrt 2 * Real.sqrt |t|) := by
    positivity
  have hle : t ≤ |t| := le_abs_self t
  have hkey : J + 2 * t ≤ (Real.sqrt J + Real.sqrt 2 * Real.sqrt |t|) ^ 2 := by
    have hexp : (Real.sqrt J + Real.sqrt 2 * Real.sqrt |t|) ^ 2 =
        J + 2 * Real.sqrt J * (Real.sqrt 2 * Real.sqrt |t|) + 2 * |t| := by
      calc (Real.sqrt J + Real.sqrt 2 * Real.sqrt |t|) ^ 2
          = Real.sqrt J ^ 2 + 2 * Real.sqrt J * (Real.sqrt 2 * Real.sqrt |t|) +
              Real.sqrt 2 ^ 2 * Real.sqrt |t| ^ 2 := by ring
        _ = J + 2 * Real.sqrt J * (Real.sqrt 2 * Real.sqrt |t|) + 2 * |t| := by
            rw [hsqJ, hs2, hsqT]
    rw [hexp]
    linarith
  calc Real.sqrt (J + 2 * t)
      ≤ Real.sqrt ((Real.sqrt J + Real.sqrt 2 * Real.sqrt |t|) ^ 2) :=
        Real.sqrt_le_sqrt hkey
    _ = Real.sqrt J + Real.sqrt 2 * Real.sqrt |t| := Real.sqrt_sq hrhs

/-- **The adjoint budget at a general loading.** -/
theorem cubeBesovNegativeVectorSeminormTwo_cubeAdjointGrad_pq_le [NeZero d]
    (Q : TriadicCube d) (F : Ch02.TriadicCoeffFamily d) {p q : Vec d}
    {vAdj : Solution (cubeDomain Q) (F.coeffOn Q).transpose}
    (hvAdj : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q).transpose p (-q) vAdj) :
    cubeBesovNegativeVectorSeminormTwo Q (3 / 8) (fun x => vAdj.toH1.grad x) ≤
      Ch03.poincareDiscountFactor (3 / 8) (.finite 2) *
        Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) *
        (2 * (Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) p q) +
          Real.sqrt 2 * Real.sqrt |vecDot p q|)) := by
  have hbase := cubeBesovNegativeVectorSeminormTwo_cubeMaximizerGrad_le Q
    (transposeCoeffFamily F) (v := vAdj) hvAdj
  rw [lambdaSq_transposeCoeffFamily] at hbase
  have hJ : responseJ (cubeDomain Q) ((transposeCoeffFamily F).coeffOn Q) p (-q) =
      responseJ (cubeDomain Q) (F.coeffOn Q) p q + 2 * vecDot p q := by
    rw [transposeCoeffFamily_coeffOn]
    exact responseJ_transpose_neg_right (cubeDomain Q) (F.coeffOn Q) p q
  rw [hJ] at hbase
  refine hbase.trans ?_
  have hPDnn : (0 : ℝ) ≤ Ch03.poincareDiscountFactor (3 / 8) (.finite 2) :=
    poincareDiscountFactor_sensitivity_pos.le
  have hcoef : (0 : ℝ) ≤ Ch03.poincareDiscountFactor (3 / 8) (.finite 2) *
      Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) := by
    have := Real.sqrt_nonneg ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹)
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hcoef
  have hJnn : (0 : ℝ) ≤ responseJ (cubeDomain Q) (F.coeffOn Q) p q :=
    Ch02.responseJ_nonneg _ _ p q
  have := sqrt_add_two_mul_vecDot_le (J := responseJ (cubeDomain Q) (F.coeffOn Q) p q)
    (t := vecDot p q) hJnn
  linarith

/-! ## The witness budget at a general loading -/

/-- The explicit constant of the general-loading witness-gradient negative Besov
budget. -/
def pqWitnessConst : ℝ :=
  Real.sqrt 2 *
    (2⁻¹ * Real.sqrt 2 *
        (2 * Real.sqrt 2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2) +
          2 * Real.sqrt 2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2)) +
      constantFieldBesovConst (3 / 8) * Real.sqrt 2)

theorem pqWitnessConst_nonneg : 0 ≤ pqWitnessConst := by
  have := poincareDiscountFactor_sensitivity_pos.le
  have := constantFieldBesovConst_nonneg (3 / 8 : ℝ)
  have h2 := Real.sqrt_nonneg (2 : ℝ)
  unfold pqWitnessConst
  positivity

/-- **The general-loading negative Besov budget of the zero-trace witness
gradient at an arbitrary triadic cube.** -/
theorem cubeBesovNegativeVectorSeminormTwo_pqWitnessGrad_le [NeZero d]
    (Q : TriadicCube d) (F : Ch02.TriadicCoeffFamily d) (p q : Vec d)
    {vAdj : Solution (cubeDomain Q) (F.coeffOn Q).transpose}
    {v : Ch03.CubeSolution Q F}
    (hvAdj : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q).transpose p (-q) vAdj)
    (hv : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q) p q v)
    (u : H10Function ((cubeDomain Q : Domain d) : Set (Vec d)))
    (hu : ∀ᵐ x ∂ volumeMeasureOn ((cubeDomain Q : Domain d) : Set (Vec d)),
      u.toH1Function.grad x =
        (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x) + p) :
    cubeBesovNegativeVectorSeminormTwo Q (3 / 8) (fun x => u.toH1Function.grad x) ≤
      pqWitnessConst *
        (Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) *
          (Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) p q) +
            Real.sqrt |vecDot p q|)) := by
  classical
  set PD : ℝ := Ch03.poincareDiscountFactor (3 / 8) (.finite 2) with hPD
  have hPDnn : 0 ≤ PD := poincareDiscountFactor_sensitivity_pos.le
  set SL : ℝ := Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) with hSL
  set SJ : ℝ := Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) p q) with hSJ
  set ST : ℝ := Real.sqrt |vecDot p q| with hST
  have hSLnn : 0 ≤ SL := Real.sqrt_nonneg _
  have hSJnn : 0 ≤ SJ := Real.sqrt_nonneg _
  have hSTnn : 0 ≤ ST := Real.sqrt_nonneg _
  set Z : ℝ := SL * (SJ + ST) with hZ
  have hZnn : 0 ≤ Z := by rw [hZ]; positivity
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2one : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 2 by norm_num)
    simp only [Real.sqrt_one] at h
    exact h
  set A : ℝ := 2 * Real.sqrt 2 * PD with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  -- the adjoint half
  have hbase : (0 : ℝ) ≤ PD * SL := by positivity
  have hAdj : cubeBesovNegativeVectorSeminormTwo Q (3 / 8)
      (fun x => vAdj.toH1.grad x) ≤ A * Z := by
    refine (cubeBesovNegativeVectorSeminormTwo_cubeAdjointGrad_pq_le Q F hvAdj).trans ?_
    have hgap : (0 : ℝ) ≤
        2 * Real.sqrt 2 * (SJ + ST) - 2 * (SJ + Real.sqrt 2 * ST) := by
      nlinarith [hSJnn, hSTnn, hs2one]
    have hprod := mul_nonneg hbase hgap
    show PD * SL * (2 * (SJ + Real.sqrt 2 * ST)) ≤ A * Z
    rw [hA, hZ]
    nlinarith [hprod]
  -- the primal half
  have hPrimal : cubeBesovNegativeVectorSeminormTwo Q (3 / 8)
      (fun x => v.toH1.grad x) ≤ A * Z := by
    refine (cubeBesovNegativeVectorSeminormTwo_cubeMaximizerGrad_le Q F hv).trans ?_
    have hgap : (0 : ℝ) ≤ 2 * Real.sqrt 2 * (SJ + ST) - 2 * SJ := by
      nlinarith [hSJnn, hSTnn, hs2one]
    have hprod := mul_nonneg hbase hgap
    show PD * SL * (2 * SJ) ≤ A * Z
    rw [hA, hZ]
    nlinarith [hprod]
  -- the constant half
  have hConst : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q (3 / 8) N (fun _ => p) ≤
        (constantFieldBesovConst (3 / 8) * Real.sqrt 2) * Z := by
    intro N
    refine (cubeBesovNegativeVectorPartialSeminormTwo_const_le Q
      (by norm_num) N p).trans ?_
    have hp := vecNorm_le_sqrt_two_mul_sqrt_add Q F (F.coeffOn Q)
      (CoeffOn.AEEq.refl _) p q
    have hstep := mul_le_mul_of_nonneg_left hp
      (constantFieldBesovConst_nonneg (3 / 8 : ℝ))
    refine hstep.trans (le_of_eq ?_)
    rw [hZ, hSL, hSJ, hST]; ring
  have hae : (fun x => u.toH1Function.grad x)
      =ᵐ[normalizedCubeMeasure Q]
      fun x => ((2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x)) + (fun _ => p) x := by
    refine ae_cubeDomain_iff_normalizedCubeMeasure Q ?_
    filter_upwards [hu] with x hx using hx
  have hL2Adj : MemVectorL2 (cubeSet Q) (fun x => vAdj.toH1.grad x) :=
    memVectorL2_cubeSet_grad vAdj.toH1
  have hL2v : MemVectorL2 (cubeSet Q) (fun x => v.toH1.grad x) :=
    memVectorL2_cubeSet_grad v.toH1
  have hL2sum : MemVectorL2 (cubeSet Q)
      (fun x => vAdj.toH1.grad x + v.toH1.grad x) := hL2Adj.add hL2v
  have hL2smul : MemVectorL2 (cubeSet Q)
      (fun x => (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x)) :=
    hL2sum.const_smul ((2 : ℝ)⁻¹)
  have hL2const : MemVectorL2 (cubeSet Q) (fun _ : Vec d => p) := by
    let := isFiniteMeasure_volumeMeasureOn_cubeSet Q
    exact memVectorL2_const p
  have hBddAdj := bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad Q vAdj.toH1
  have hBddv := bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad Q v.toH1
  refine cubeBesovNegativeVectorSeminormTwo_le_of_partialBound _ _ _ ?_
  intro N
  rw [cubeBesovNegativeVectorPartialSeminormTwo_congr_ae Q (3 / 8) N hae]
  have hadd := cubeBesovNegativeVectorPartialSeminormTwo_add_le_sqrtTwo_mul_add
    Q (3 / 8) (fun x => (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x))
    (fun _ => p) hL2smul hL2const N
  refine hadd.trans ?_
  have hsmul := cubeBesovNegativeVectorPartialSeminormTwo_const_smul
    Q (3 / 8) N ((2 : ℝ)⁻¹) (fun x => vAdj.toH1.grad x + v.toH1.grad x)
  have habs2 : |((2 : ℝ)⁻¹)| = (2 : ℝ)⁻¹ := by norm_num
  rw [habs2] at hsmul
  have hinner := cubeBesovNegativeVectorPartialSeminormTwo_add_le_sqrtTwo_mul_add
    Q (3 / 8) (fun x => vAdj.toH1.grad x) (fun x => v.toH1.grad x) hL2Adj hL2v N
  have hAdjN : cubeBesovNegativeVectorPartialSeminormTwo Q (3 / 8) N
      (fun x => vAdj.toH1.grad x) ≤ A * Z := by
    refine le_trans ?_ hAdj
    unfold cubeBesovNegativeVectorSeminormTwo
    exact le_csSup hBddAdj ⟨N, rfl⟩
  have hvN : cubeBesovNegativeVectorPartialSeminormTwo Q (3 / 8) N
      (fun x => v.toH1.grad x) ≤ A * Z := by
    refine le_trans ?_ hPrimal
    unfold cubeBesovNegativeVectorSeminormTwo
    exact le_csSup hBddv ⟨N, rfl⟩
  have hleft :
      cubeBesovNegativeVectorPartialSeminormTwo Q (3 / 8) N
          (fun x => (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x)) ≤
        2⁻¹ * Real.sqrt 2 * (A * Z + A * Z) := by
    rw [hsmul]
    have := hinner.trans (mul_le_mul_of_nonneg_left (add_le_add hAdjN hvN) hs2)
    linarith
  have hright := hConst N
  have hgoal :
      Real.sqrt 2 *
          (2⁻¹ * Real.sqrt 2 * (A * Z + A * Z) +
            (constantFieldBesovConst (3 / 8) * Real.sqrt 2) * Z) =
        pqWitnessConst * Z := by
    unfold pqWitnessConst
    rw [hA, hPD]; ring
  calc
    Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo Q (3 / 8) N
            (fun x => (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x)) +
          cubeBesovNegativeVectorPartialSeminormTwo Q (3 / 8) N (fun _ => p))
        ≤ Real.sqrt 2 *
            (2⁻¹ * Real.sqrt 2 * (A * Z + A * Z) +
              (constantFieldBesovConst (3 / 8) * Real.sqrt 2) * Z) :=
          mul_le_mul_of_nonneg_left (add_le_add hleft hright) hs2
    _ = pqWitnessConst * Z := hgoal

end

end Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional
