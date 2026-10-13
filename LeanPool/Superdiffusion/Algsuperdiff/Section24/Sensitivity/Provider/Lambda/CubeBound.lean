/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CubeTermBC
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.PathGronwall
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly.Skeleton
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Adjoint.H10Witness
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Multiscale.UnitCubeTransfer

/-!
# CubeBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The pure-flux `D_h` bound on a sub-cube of the frozen carrier

Source: ABK26 (`l.Dh.bound`), specialized to the **pure-flux loading** `p = 0`
and stated at an arbitrary sub-cube `R` of the frozen unit-cube carrier.

At `p = 0` the splitting identity degenerates: its Term A is
`-2 p · ⨍_R h ∇v`, which vanishes identically, so only Term BC survives.  The
resulting bound is

```
|D_h(R; b)[(0,-w)]| ≤ C(d) ‖∇h‖_{W^{1,∞}} · cubeScaleFactor R ·
                        λ_{3/8,2}^{-1}(R; G) · J(R, b, 0, w) ,
```

with the *one* factor of `cubeScaleFactor R` produced by the Term BC budget of
`Provider.Lambda.CubeTermBC` and the two half-powers of `λ^{-1} J` produced by
the Besov pairing engine together with the pure-flux witness budget of
`Provider.Lambda.WitnessBudget`.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Lambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Besov regularity of the Term BC field on a sub-cube -/

theorem forceBesovRegularity_fluxTermBCField [NeZero d]
    (h : UnitCubeSkewW2Infinity d) {R : TriadicCube d}
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (u : H10Function ((cubeDomain R : Domain d) : Set (Vec d)))
    (hBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo R (3 / 8) N
        (fun x => u.toH1Function.grad x))) :
    Ch03.ForceBesovRegularity R (3 / 8) (fluxTermBCField h u) where
  memLp := memLp_fluxTermBCField_two h hsub u
  partialSeminorms_bddAbove := by
    classical
    have hg : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
    refine ⟨besovMultConst (3 / 8) *
      (cubeScaleFactor R * ((d : ℝ) ^ 2 * h.gradientW1Infinity) *
          cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x) +
        (d : ℝ) * h.gradientW1Infinity *
          (cubeScaleFactor R * (depthDowngradeConst d *
            cubeBesovNegativeVectorSeminormTwo R (3 / 8)
              (fun x => u.toH1Function.grad x)))), ?_⟩
    rintro _ ⟨N, rfl⟩
    refine (cubeBesovPositiveVectorPartialSeminormTwo_fluxTermBCField_le h hsub u N).trans ?_
    have hmult : (0 : ℝ) ≤ besovMultConst (3 / 8) :=
      (besovMultConst_pos (s := (3 / 8 : ℝ)) (by norm_num)).le
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hmult
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact cubeBesovPositiveScalarPartialSeminormTwo_h1_cube_le R N u.toH1Function hBdd

/-! ## The explicit constants -/

/-- The Besov pairing constant. -/
def fluxPairingConst (d : ℕ) : ℝ :=
  (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
    (2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2))

theorem fluxPairingConst_nonneg (d : ℕ) : 0 ≤ fluxPairingConst d := by
  have h1 : (0 : ℝ) ≤ 1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) := by
    have : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    positivity
  have h2 : (0 : ℝ) ≤ 2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2) := by
    have := poincareDiscountFactor_sensitivity_pos
    linarith
  exact mul_nonneg h1 h2

/-- The explicit constant of the pure-flux sub-cube `D_h` bound. -/
def fluxCubeConst (d : ℕ) [NeZero d] : ℝ :=
  2 * fluxPairingConst d * fluxTermBCConst d * fluxWitnessConst

theorem fluxCubeConst_nonneg (d : ℕ) [NeZero d] : 0 ≤ fluxCubeConst d := by
  have h1 := fluxPairingConst_nonneg d
  have h2 := fluxTermBCConst_nonneg d
  have h3 := fluxWitnessConst_nonneg
  unfold fluxCubeConst
  positivity

/-! ## The sub-cube `D_h` bound at the pure-flux loading -/

/-- **The pure-flux `D_h` bound on a sub-cube of the frozen carrier.**

`b` is an arbitrary coefficient on the sub-cube and `G` any CoarseGraining
family representing it there. -/
theorem abs_dhFluxForm_cube_le [NeZero d]
    (h : UnitCubeSkewW2Infinity d) {R : TriadicCube d}
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (hL : cubeScaleFactor R ≤ 1) (b : CoeffOn (cubeDomain R))
    (G : Ch03.CoeffFamily d) (hG : CoeffOn.AEEq (G.coeffOn R) b) (w : Vec d) :
    |dhFluxForm (cubeDomain R) b
        (restrictLInfSkewMatrixFieldOn hsub h.toLInfSkewMatrixFieldOn) w| ≤
      fluxCubeConst d * h.gradientW1Infinity * cubeScaleFactor R *
        (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ *
        responseJ (cubeDomain R) b 0 w := by
  classical
  set g : LInfSkewMatrixFieldOn (cubeDomain R) :=
    restrictLInfSkewMatrixFieldOn hsub h.toLInfSkewMatrixFieldOn with hgdef
  have hgnn : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hLnn : (0 : ℝ) ≤ cubeScaleFactor R := (cubeScaleFactor_pos_cube R).le
  -- canonical maximizers for the primal and adjoint pure-flux problems
  obtain ⟨vAdj, hvAdj⟩ :
      ∃ z : Solution (cubeDomain R) b.transpose, IsResponseMaximizer (cubeDomain R) b.transpose 0 (-w) z :=
    ⟨_, canonicalMaximizer_isMaximizer (responseExistenceTheory (cubeDomain R) b.transpose) 0 (-w)⟩
  obtain ⟨v, hv⟩ : ∃ z : Solution (cubeDomain R) b, IsResponseMaximizer (cubeDomain R) b 0 w z :=
    ⟨_, canonicalMaximizer_isMaximizer (responseExistenceTheory (cubeDomain R) b) 0 w⟩
  -- the zero-trace witness
  obtain ⟨u, hu⟩ :=
    Adjoint.exists_h10Function_grad_ae_eq_halfSum_add_const (cubeDomain R) b 0 w vAdj v hvAdj hv
  -- transported maximizers at the family representative
  set v' : Solution (cubeDomain R) (G.coeffOn R) := Solution.ofAEEq hG.symm v with hv'def
  have hv' : IsResponseMaximizer (cubeDomain R) (G.coeffOn R) 0 w v' := hv.ofAEEq hG.symm
  set vAdj' : Solution (cubeDomain R) (G.coeffOn R).transpose :=
    Solution.ofAEEq (hG.symm.transpose) vAdj with hvAdj'def
  have hvAdj'' : IsResponseMaximizer (cubeDomain R) (G.coeffOn R).transpose 0 (-w) vAdj' :=
    hvAdj.ofAEEq (hG.symm.transpose)
  have hv'grad : v'.toH1 = v.toH1 := Solution.toH1_ofAEEq _ _
  have hvAdj'grad : vAdj'.toH1 = vAdj.toH1 := Solution.toH1_ofAEEq _ _
  -- the bounded-above data for the witness gradient
  have hBdd := bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad R u.toH1Function
  set S : ℝ := cubeBesovNegativeVectorSeminormTwo R (3 / 8)
    (fun x => u.toH1Function.grad x) with hS
  -- the pure-flux witness budget
  have hwitness : S ≤ fluxWitnessConst *
      (Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) *
        Real.sqrt (responseJ (cubeDomain R) (G.coeffOn R) 0 w)) := by
    refine cubeBesovNegativeVectorSeminormTwo_fluxWitnessGrad_le R G w
      (vAdj := vAdj') (v := v') hvAdj'' hv' u ?_
    rw [hv'grad, hvAdj'grad]
    exact hu
  -- the Term BC budget
  have hBC := scaleNormalizedPositiveBesovVectorNormTwo_fluxTermBCField_le h hsub hL u hBdd
  have hreg := forceBesovRegularity_fluxTermBCField h hsub u hBdd
  -- the splitting identity at the pure-flux loading
  have hsplit := Assembly.quadForm_coarseMatrixDerivative_eq_split (cubeDomain R) b g
    (Dh := unitCubeDerivData h)
    (fun k i j => memLp_firstDeriv_restrict h hsub k i j)
    (fun k i j => hasWeakPartialDeriv_value_restrict h (cubeDomain R).isOpen hsub k i j)
    0 w vAdj v hvAdj hv u hu
  have hzero : vecDot (0 : Vec d)
      (Book.Ch02.averageVec (cubeDomain R) (fun x => matVecMul (g.1.1 x) (v.toH1.grad x))) = 0 := by
    simp [vecDot]
  -- Term BC as a cube-average pairing against the gradient
  have hTBC : Book.Ch02.average (cubeDomain R) (fun x =>
        u.toH1Function.toFun x *
          vecDot (matWeakDiv (unitCubeDerivData h) x) (v.toH1.grad x)) =
      cubeAverage R (fun x => vecDot (v.toH1.grad x) (fluxTermBCField h u x)) := by
    rw [← average_cubeDomain_eq_cubeAverage]
    exact average_congr_funext (U := cubeDomain R) fun x =>
      mul_vecDot_eq_vecDot_smul _ _ _
  have hdh : dhFluxForm (cubeDomain R) b g w =
      -2 * cubeAverage R (fun x => vecDot (v.toH1.grad x) (fluxTermBCField h u x)) := by
    rw [dhFluxForm, hsplit, hzero, hTBC]
    ring
  -- the Besov pairing estimate
  have hpair := abs_cubeAverage_vecDot_grad_le_of_positiveBesov_bound
    (Q := R) (F := G) (v := v') hv' (fluxTermBCField h u) hreg le_rfl
  rw [hv'grad] at hpair
  -- assemble
  set X : ℝ := Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) *
    Real.sqrt (responseJ (cubeDomain R) (G.coeffOn R) 0 w) with hX
  have hXnn : 0 ≤ X := by
    rw [hX]; exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  set B : ℝ := Ch03.scaleNormalizedPositiveBesovVectorNormTwo R (3 / 8)
    (fluxTermBCField h u) with hB
  have hBle : B ≤ fluxTermBCConst d * h.gradientW1Infinity * cubeScaleFactor R *
      (fluxWitnessConst * X) := by
    refine hBC.trans ?_
    have hcoef : (0 : ℝ) ≤ fluxTermBCConst d * h.gradientW1Infinity :=
      mul_nonneg (fluxTermBCConst_nonneg d) hgnn
    have := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hwitness hLnn) hcoef
    refine this.trans (le_of_eq (by ring))
  have hpair' : |cubeAverage R (fun x => vecDot (v.toH1.grad x) (fluxTermBCField h u x))| ≤
      fluxPairingConst d * B * X := by
    refine hpair.trans (le_of_eq ?_)
    rw [fluxPairingConst, hX]
  have habs : |dhFluxForm (cubeDomain R) b g w| =
      2 * |cubeAverage R (fun x => vecDot (v.toH1.grad x) (fluxTermBCField h u x))| := by
    rw [hdh, abs_mul]
    norm_num
  rw [habs]
  have hKnn : (0 : ℝ) ≤ fluxPairingConst d := fluxPairingConst_nonneg d
  have hstep : 2 * |cubeAverage R (fun x => vecDot (v.toH1.grad x) (fluxTermBCField h u x))| ≤
      2 * (fluxPairingConst d * (fluxTermBCConst d * h.gradientW1Infinity *
        cubeScaleFactor R * (fluxWitnessConst * X)) * X) := by
    refine mul_le_mul_of_nonneg_left (hpair'.trans ?_) (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hBle hKnn) hXnn
  refine hstep.trans (le_of_eq ?_)
  -- `X * X = λ⁻¹ J`
  have hJeq : responseJ (cubeDomain R) (G.coeffOn R) 0 w = responseJ (cubeDomain R) b 0 w :=
    responseJ_eq_ofAEEq hG 0 w
  have hlamnn : (0 : ℝ) ≤ (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ :=
    inv_nonneg.mpr (Ch02.lambdaSq_nonneg R G (by norm_num)
      (by simp [Ch02.MultiscaleExponent.IsAdmissible]))
  have hJnn : (0 : ℝ) ≤ responseJ (cubeDomain R) (G.coeffOn R) 0 w := Ch02.responseJ_nonneg _ _ 0 w
  have hXX : X * X = (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ * responseJ (cubeDomain R) b 0 w := by
    rw [hX, ← hJeq]
    rw [show Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) *
        Real.sqrt (responseJ (cubeDomain R) (G.coeffOn R) 0 w) *
        (Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) *
          Real.sqrt (responseJ (cubeDomain R) (G.coeffOn R) 0 w)) =
      (Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) *
        Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹)) *
      (Real.sqrt (responseJ (cubeDomain R) (G.coeffOn R) 0 w) *
        Real.sqrt (responseJ (cubeDomain R) (G.coeffOn R) 0 w)) from by ring]
    rw [Real.mul_self_sqrt hlamnn, Real.mul_self_sqrt hJnn]
  calc 2 * (fluxPairingConst d * (fluxTermBCConst d * h.gradientW1Infinity *
        cubeScaleFactor R * (fluxWitnessConst * X)) * X)
      = (2 * fluxPairingConst d * fluxTermBCConst d * fluxWitnessConst) *
          h.gradientW1Infinity * cubeScaleFactor R * (X * X) := by ring
    _ = fluxCubeConst d * h.gradientW1Infinity * cubeScaleFactor R *
          (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ * responseJ (cubeDomain R) b 0 w := by
          rw [hXX, fluxCubeConst]; ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.Lambda
