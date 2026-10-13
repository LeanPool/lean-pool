/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional.CubeWitnessPQ

/-!
# CubeDhPQ

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `D_h` bound at a general loading on a sub-cube, with the scale-damped Term A

Source: ABK26 (`l.Dh.bound`) at the **general** loading `(p, q)` and at an
arbitrary sub-cube `R` of the frozen unit-cube carrier.

This is the general-loading counterpart of
`Provider.BigLambda.CubePotentialDh.abs_dhPotentialForm_cube_le`, with two
changes:

* Term A uses the *scale-damped* budget of
  `Provider.ResponseUnconditional.TermARefined`, so its coefficient is
  `|p| (‖h‖_{L²(R)} + |R| ‖∇h‖_{W^{1,∞}})` rather than `|p| ‖h‖_{W^{1,∞}}`;
* Term BC uses the general-loading witness budget of
  `Provider.ResponseUnconditional.CubeWitnessPQ`, so it carries the extra
  `|p·q|^{1/2}` summand.

Both the splitting identity `Provider.DhBound.Assembly.SplitIdentity` and the
Besov pairing `Provider.DhBound.Assembly.BesovPairing` are already stated at a
general loading, so nothing else has to change.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.BigLambda
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- The `D_h` quadratic form at the general loading `P = (p, -q)`. -/
def dhLoadForm (U : Domain d) (a : CoeffOn U) (h : LInfSkewMatrixFieldOn U)
    (p q : Vec d) : ℝ :=
  blockVecDot (p, -q) (blockMatVecMul (coarseMatrixDerivative U a h.1) (p, -q))

/-! ## The explicit constants -/

/-- The Term A coefficient of the general-loading sub-cube `D_h` bound. -/
def pqCubeConstA (d : ℕ) : ℝ := 2 * fluxPairingConst d * termARefinedConst d

/-- The Term BC coefficient of the general-loading sub-cube `D_h` bound. -/
def pqCubeConstB (d : ℕ) : ℝ  :=
  2 * fluxPairingConst d * fluxTermBCConst d * pqWitnessConst

theorem pqCubeConstA_nonneg (d : ℕ) : 0 ≤ pqCubeConstA d := by
  have h1 := fluxPairingConst_nonneg d
  have h2 := termARefinedConst_nonneg d
  unfold pqCubeConstA
  positivity

theorem pqCubeConstB_nonneg (d : ℕ) : 0 ≤ pqCubeConstB d  := by
  have h1 := fluxPairingConst_nonneg d
  have h2 := fluxTermBCConst_nonneg d
  have h3 := pqWitnessConst_nonneg
  unfold pqCubeConstB
  positivity

/-! ## The sub-cube `D_h` bound at a general loading -/

/-- **The general-loading `D_h` bound on a sub-cube of the frozen carrier, with
the scale-damped Term A budget.** -/
theorem abs_dhLoadForm_cube_le [NeZero d]
    (h : UnitCubeSkewW2Infinity d) {R : TriadicCube d}
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (hL : cubeScaleFactor R ≤ 1) (b : CoeffOn (cubeDomain R))
    (G : Ch02.TriadicCoeffFamily d) (hG : CoeffOn.AEEq (G.coeffOn R) b)
    (p q : Vec d) :
    |dhLoadForm (cubeDomain R) b
        (restrictLInfSkewMatrixFieldOn hsub h.toLInfSkewMatrixFieldOn) p q| ≤
      pqCubeConstA d *
          (vecNorm p * (Real.sqrt (valueBudget h R) +
            cubeScaleFactor R * h.gradientW1Infinity)) *
          (Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) *
            Real.sqrt (responseJ (cubeDomain R) b p q)) +
        pqCubeConstB d * (h.gradientW1Infinity * cubeScaleFactor R) *
          ((Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) *
              Real.sqrt (responseJ (cubeDomain R) b p q)) *
            (Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) *
                Real.sqrt (responseJ (cubeDomain R) b p q) +
              Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) *
                Real.sqrt |vecDot p q|)) := by
  classical
  set g : LInfSkewMatrixFieldOn (cubeDomain R) :=
    restrictLInfSkewMatrixFieldOn hsub h.toLInfSkewMatrixFieldOn with hgdef
  have hgnn : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hLnn : (0 : ℝ) ≤ cubeScaleFactor R := (cubeScaleFactor_pos_cube R).le
  -- canonical maximizers for the primal and adjoint problems
  obtain ⟨vAdj, hvAdj⟩ :
      ∃ z : Solution (cubeDomain R) b.transpose,
        IsResponseMaximizer (cubeDomain R) b.transpose p (-q) z :=
    ⟨_, canonicalMaximizer_isMaximizer
      (responseExistenceTheory (cubeDomain R) b.transpose) p (-q)⟩
  obtain ⟨v, hv⟩ : ∃ z : Solution (cubeDomain R) b,
      IsResponseMaximizer (cubeDomain R) b p q z :=
    ⟨_, canonicalMaximizer_isMaximizer (responseExistenceTheory (cubeDomain R) b) p q⟩
  -- the zero-trace witness
  obtain ⟨u, hu⟩ :=
    Adjoint.exists_h10Function_grad_ae_eq_halfSum_add_const (cubeDomain R) b p q
      vAdj v hvAdj hv
  -- transported maximizers at the family representative
  set v' : Solution (cubeDomain R) (G.coeffOn R) := Solution.ofAEEq hG.symm v with hv'def
  have hv' : IsResponseMaximizer (cubeDomain R) (G.coeffOn R) p q v' := hv.ofAEEq hG.symm
  set vAdj' : Solution (cubeDomain R) (G.coeffOn R).transpose :=
    Solution.ofAEEq (hG.symm.transpose) vAdj with hvAdj'def
  have hvAdj'' : IsResponseMaximizer (cubeDomain R) (G.coeffOn R).transpose p
      (-q) vAdj' := hvAdj.ofAEEq (hG.symm.transpose)
  have hv'grad : v'.toH1 = v.toH1 := Solution.toH1_ofAEEq _ _
  have hvAdj'grad : vAdj'.toH1 = vAdj.toH1 := Solution.toH1_ofAEEq _ _
  have hJeq : responseJ (cubeDomain R) (G.coeffOn R) p q =
      responseJ (cubeDomain R) b p q := responseJ_eq_ofAEEq hG p q
  -- abbreviations
  set L : ℝ := (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ with hLdef
  set J : ℝ := responseJ (cubeDomain R) b p q with hJdef
  set T : ℝ := |vecDot p q| with hTdef
  have hLnn' : 0 ≤ L := lambdaSq_inv_nonneg R G
  have hJnn : 0 ≤ J := Ch02.responseJ_nonneg (cubeDomain R) b p q
  have hTnn : 0 ≤ T := abs_nonneg _
  set X : ℝ := Real.sqrt L * Real.sqrt J with hX
  set Y : ℝ := Real.sqrt L * Real.sqrt T with hY
  have hXnn : 0 ≤ X := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hYnn : 0 ≤ Y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- the bounded-above data for the witness gradient
  have hBdd := bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad R u.toH1Function
  set S : ℝ := cubeBesovNegativeVectorSeminormTwo R (3 / 8)
    (fun x => u.toH1Function.grad x) with hS
  -- the general-loading witness budget
  have hgradeq : ∀ᵐ x ∂ volumeMeasureOn ((cubeDomain R : Domain d) : Set (Vec d)),
      u.toH1Function.grad x =
        (2 : ℝ)⁻¹ • (vAdj'.toH1.grad x + v'.toH1.grad x) + p := by
    rw [hv'grad, hvAdj'grad]; exact hu
  have hwitness : S ≤ pqWitnessConst * (X + Y) := by
    have hmain := cubeBesovNegativeVectorSeminormTwo_pqWitnessGrad_le R G p q
      (vAdj := vAdj') (v := v') hvAdj'' hv' u hgradeq
    rw [hJeq] at hmain
    refine hmain.trans (le_of_eq ?_)
    rw [hX, hY, hLdef, hJdef, hTdef]
    ring
  -- the Term BC budget
  have hBC := scaleNormalizedPositiveBesovVectorNormTwo_fluxTermBCField_le h hsub hL u hBdd
  have hreg := forceBesovRegularity_potTermBCField h hsub u hBdd
  -- the scale-damped Term A budget
  have hregA := forceBesovRegularity_termAField_cube h R hsub hL p
  have hAle := scaleNormalizedPositiveBesovVectorNormTwo_termAField_refined_le h R hsub p
  -- the splitting identity at the general loading
  have hsplit := Assembly.quadForm_coarseMatrixDerivative_eq_split (cubeDomain R) b g
    (Dh := unitCubeDerivData h)
    (fun k i j => memLp_firstDeriv_restrict h hsub k i j)
    (fun k i j => hasWeakPartialDeriv_value_restrict h (cubeDomain R).isOpen hsub k i j)
    p q vAdj v hvAdj hv u hu
  -- Term A as a cube-average pairing against the gradient
  have hTA : vecDot p (Book.Ch02.averageVec (cubeDomain R)
        (fun x => matVecMul (g.1.1 x) (v.toH1.grad x))) =
      cubeAverage R (fun x => vecDot (v.toH1.grad x)
        (matVecMul (matTranspose (h.toLInfSkewMatrixFieldOn.1.1 x)) p)) := by
    rw [← average_vecDot_const_eq_vecDot_averageVec
      (U := cubeDomain R)
      (G := fun x => matVecMul (g.1.1 x) (v.toH1.grad x))
      (fun i => (memScalarL2_matVecMul_grad g v.toH1 i).integrable one_le_two) p]
    rw [← average_cubeDomain_eq_cubeAverage]
    exact average_congr_funext (U := cubeDomain R) fun x =>
      vecDot_matVecMul_eq_vecDot_matTranspose _ _ _
  -- Term BC as a cube-average pairing against the gradient
  have hTBC : Book.Ch02.average (cubeDomain R) (fun x =>
        u.toH1Function.toFun x *
          vecDot (matWeakDiv (unitCubeDerivData h) x) (v.toH1.grad x)) =
      cubeAverage R (fun x => vecDot (v.toH1.grad x) (fluxTermBCField h u x)) := by
    rw [← average_cubeDomain_eq_cubeAverage]
    exact average_congr_funext (U := cubeDomain R) fun x =>
      mul_vecDot_eq_vecDot_smul _ _ _
  -- the two pairing estimates
  have hpairA := abs_cubeAverage_vecDot_grad_le_of_positiveBesov_bound
    (Q := R) (F := G) (v := v') hv' _ hregA hAle
  have hpairBC := abs_cubeAverage_vecDot_grad_le_of_positiveBesov_bound
    (Q := R) (F := G) (v := v') hv' (fluxTermBCField h u) hreg le_rfl
  rw [hv'grad, hJeq] at hpairA hpairBC
  -- assemble
  rw [dhLoadForm, hsplit, hTA, hTBC]
  set K : ℝ := fluxPairingConst d with hK
  have hKnn : 0 ≤ K := fluxPairingConst_nonneg d
  set SA : ℝ := cubeAverage R (fun x => vecDot (v.toH1.grad x)
    (matVecMul (matTranspose (h.toLInfSkewMatrixFieldOn.1.1 x)) p)) with hSA
  set SBC : ℝ := cubeAverage R (fun x => vecDot (v.toH1.grad x)
    (fluxTermBCField h u x)) with hSBC
  have hA : |SA| ≤ K * (termARefinedConst d * vecNorm p *
      (Real.sqrt (valueBudget h R) +
        cubeScaleFactor R * h.gradientW1Infinity)) * X := hpairA
  have hBC' : |SBC| ≤ K *
      (Ch03.scaleNormalizedPositiveBesovVectorNormTwo R (3 / 8)
        (fluxTermBCField h u)) * X := hpairBC
  have hBCbudget : Ch03.scaleNormalizedPositiveBesovVectorNormTwo R (3 / 8)
      (fluxTermBCField h u) ≤
      fluxTermBCConst d * h.gradientW1Infinity *
        (cubeScaleFactor R * (pqWitnessConst * (X + Y))) := by
    refine hBC.trans ?_
    have hcoef : (0 : ℝ) ≤ fluxTermBCConst d * h.gradientW1Infinity :=
      mul_nonneg (fluxTermBCConst_nonneg d) hgnn
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hwitness hLnn) hcoef
  have hBCfinal : |SBC| ≤ K * (fluxTermBCConst d * h.gradientW1Infinity *
      (cubeScaleFactor R * (pqWitnessConst * (X + Y)))) * X := by
    refine hBC'.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hBCbudget hKnn) hXnn
  have htri : |(-2 : ℝ) * SA - 2 * SBC| ≤ 2 * |SA| + 2 * |SBC| := by
    calc
      |(-2 : ℝ) * SA - 2 * SBC| ≤ |(-2 : ℝ) * SA| + |(2 : ℝ) * SBC| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_le ((-2 : ℝ) * SA) (-((2 : ℝ) * SBC))
      _ = 2 * |SA| + 2 * |SBC| := by
        rw [abs_mul, abs_mul]; norm_num
  refine htri.trans ?_
  have hfold : 2 * (K * (termARefinedConst d * vecNorm p *
        (Real.sqrt (valueBudget h R) +
          cubeScaleFactor R * h.gradientW1Infinity)) * X) +
      2 * (K * (fluxTermBCConst d * h.gradientW1Infinity *
        (cubeScaleFactor R * (pqWitnessConst * (X + Y)))) * X) =
      pqCubeConstA d *
          (vecNorm p * (Real.sqrt (valueBudget h R) +
            cubeScaleFactor R * h.gradientW1Infinity)) * X +
        pqCubeConstB d * (h.gradientW1Infinity * cubeScaleFactor R) *
          (X * (X + Y)) := by
    unfold pqCubeConstA pqCubeConstB
    rw [hK]
    ring
  calc 2 * |SA| + 2 * |SBC|
      ≤ 2 * (K * (termARefinedConst d * vecNorm p *
            (Real.sqrt (valueBudget h R) +
              cubeScaleFactor R * h.gradientW1Infinity)) * X) +
          2 * (K * (fluxTermBCConst d * h.gradientW1Infinity *
            (cubeScaleFactor R * (pqWitnessConst * (X + Y)))) * X) := by
        exact add_le_add (by linarith [hA]) (by linarith [hBCfinal])
    _ = _ := hfold

end

end Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional
