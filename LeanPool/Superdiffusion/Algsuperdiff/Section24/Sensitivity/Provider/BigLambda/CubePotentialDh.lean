/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CubeBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.CubeTermA
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.CubeWitness

/-!
# CubePotentialDh

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The pure-potential `D_h` bound on a sub-cube of the frozen carrier

Source: ABK26 (`l.Dh.bound`), specialized to the **pure-potential loading** `q
= 0` and stated at an arbitrary sub-cube `R` of the frozen unit-cube carrier.

Both terms of the splitting identity survive at `q = 0`:

* Term A is `-2 p·⨍_R h ∇v`, controlled by the general-cube Besov budget of
  `BigLambda.CubeTermA` — coefficient `‖h‖_{W^{1,∞}(□₀)} |p|`, no scale factor;
* Term BC is `-2 ⨍_R u (∇·h)·∇v`, controlled by `Provider.Lambda.CubeTermBC`
  together with the pure-potential witness budget of `BigLambda.CubeWitness` —
  coefficient `‖∇h‖_{W^{1,∞}(□₀)}` and exactly *one* factor
  `cubeScaleFactor R`.

The resulting bound is

```
|D_h(R; b)[(p,0)]| ≤ C |p| ‖h‖_{W^{1,∞}} λ_{3/8,2}^{-1/2}(R) J(R,p,0)^{1/2}
                    + C ‖∇h‖_{W^{1,∞}} · cubeScaleFactor R ·
                        λ_{3/8,2}^{-1}(R) J(R,p,0) ,
```

whose second coefficient is exactly the combination `3^k λ^{-1}(R)` that the
descendant scaling of `Provider.Lambda.Closure` converts into the root gauge.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.BigLambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
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

/-- The `D_h` quadratic form at the pure-potential loading `P = (p, -0)`. -/
def dhPotentialForm (U : Domain d) (a : CoeffOn U) (h : LInfSkewMatrixFieldOn U)
    (p : Vec d) : ℝ :=
  blockVecDot (p, -(0 : Vec d))
    (blockMatVecMul (coarseMatrixDerivative U a h.1) (p, -(0 : Vec d)))

/-! ## Besov regularity of the Term BC field at the pure-potential loading -/

theorem forceBesovRegularity_potTermBCField (h : UnitCubeSkewW2Infinity d) {R : TriadicCube d}
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (u : H10Function ((cubeDomain R : Domain d) : Set (Vec d)))
    (hBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo R (3 / 8) N
        (fun x => u.toH1Function.grad x))) :
    Ch03.ForceBesovRegularity R (3 / 8) (fluxTermBCField h u)  :=
  forceBesovRegularity_fluxTermBCField h hsub u hBdd

/-! ## The explicit constants -/

/-- The Term A coefficient of the pure-potential sub-cube `D_h` bound. -/
def potCubeConstA (d : ℕ) : ℝ := 2 * fluxPairingConst d * termABesovConst d

/-- The Term BC coefficient of the pure-potential sub-cube `D_h` bound. -/
def potCubeConstB (d : ℕ) : ℝ  :=
  2 * fluxPairingConst d * fluxTermBCConst d * potWitnessConst

theorem potCubeConstA_nonneg (d : ℕ) : 0 ≤ potCubeConstA d := by
  have h1 := fluxPairingConst_nonneg d
  have h2 := termABesovConst_nonneg d
  unfold potCubeConstA
  positivity

theorem potCubeConstB_nonneg (d : ℕ) : 0 ≤ potCubeConstB d  := by
  have h1 := fluxPairingConst_nonneg d
  have h2 := fluxTermBCConst_nonneg d
  have h3 := potWitnessConst_nonneg
  unfold potCubeConstB
  positivity

/-! ## The sub-cube `D_h` bound at the pure-potential loading -/

/-- **The pure-potential `D_h` bound on a sub-cube of the frozen carrier.** -/
theorem abs_dhPotentialForm_cube_le [NeZero d]
    (h : UnitCubeSkewW2Infinity d) {R : TriadicCube d}
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (hL : cubeScaleFactor R ≤ 1) (b : CoeffOn (cubeDomain R))
    (G : Ch02.TriadicCoeffFamily d) (hG : CoeffOn.AEEq (G.coeffOn R) b)
    (p : Vec d) :
    |dhPotentialForm (cubeDomain R) b
        (restrictLInfSkewMatrixFieldOn hsub h.toLInfSkewMatrixFieldOn) p| ≤
      potCubeConstA d * h.w1Infinity * vecNorm p *
          (Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) *
            Real.sqrt (responseJ (cubeDomain R) b p 0)) +
        potCubeConstB d * h.gradientW1Infinity * cubeScaleFactor R *
          (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ *
          responseJ (cubeDomain R) b p 0 := by
  classical
  set g : LInfSkewMatrixFieldOn (cubeDomain R) :=
    restrictLInfSkewMatrixFieldOn hsub h.toLInfSkewMatrixFieldOn with hgdef
  have hwnn : 0 ≤ h.w1Infinity := w1Infinity_nonneg h
  have hgnn : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hLnn : (0 : ℝ) ≤ cubeScaleFactor R := (cubeScaleFactor_pos_cube R).le
  -- canonical maximizers for the primal and adjoint pure-potential problems
  obtain ⟨vAdj, hvAdj⟩ :
      ∃ z : Solution (cubeDomain R) b.transpose,
        IsResponseMaximizer (cubeDomain R) b.transpose p (-(0 : Vec d)) z :=
    ⟨_, canonicalMaximizer_isMaximizer
      (responseExistenceTheory (cubeDomain R) b.transpose) p (-(0 : Vec d))⟩
  obtain ⟨v, hv⟩ : ∃ z : Solution (cubeDomain R) b,
      IsResponseMaximizer (cubeDomain R) b p 0 z :=
    ⟨_, canonicalMaximizer_isMaximizer (responseExistenceTheory (cubeDomain R) b) p 0⟩
  -- the zero-trace witness
  obtain ⟨u, hu⟩ :=
    Adjoint.exists_h10Function_grad_ae_eq_halfSum_add_const (cubeDomain R) b p 0
      vAdj v hvAdj hv
  -- transported maximizers at the family representative
  set v' : Solution (cubeDomain R) (G.coeffOn R) := Solution.ofAEEq hG.symm v with hv'def
  have hv' : IsResponseMaximizer (cubeDomain R) (G.coeffOn R) p 0 v' := hv.ofAEEq hG.symm
  set vAdj' : Solution (cubeDomain R) (G.coeffOn R).transpose :=
    Solution.ofAEEq (hG.symm.transpose) vAdj with hvAdj'def
  have hvAdj'' : IsResponseMaximizer (cubeDomain R) (G.coeffOn R).transpose p
      (-(0 : Vec d)) vAdj' := hvAdj.ofAEEq (hG.symm.transpose)
  have hv'grad : v'.toH1 = v.toH1 := Solution.toH1_ofAEEq _ _
  have hvAdj'grad : vAdj'.toH1 = vAdj.toH1 := Solution.toH1_ofAEEq _ _
  have hJeq : responseJ (cubeDomain R) (G.coeffOn R) p 0 =
      responseJ (cubeDomain R) b p 0 := responseJ_eq_ofAEEq hG p 0
  -- abbreviations
  set L : ℝ := (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ with hLdef
  set J : ℝ := responseJ (cubeDomain R) b p 0 with hJdef
  have hLnn' : 0 ≤ L := lambdaSq_inv_nonneg R G
  have hJnn : 0 ≤ J := Ch02.responseJ_nonneg (cubeDomain R) b p 0
  set X : ℝ := Real.sqrt L * Real.sqrt J with hX
  have hXnn : 0 ≤ X := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hXX : X * X = L * J := by
    rw [hX]
    calc Real.sqrt L * Real.sqrt J * (Real.sqrt L * Real.sqrt J)
        = (Real.sqrt L * Real.sqrt L) * (Real.sqrt J * Real.sqrt J) := by ring
      _ = L * J := by rw [Real.mul_self_sqrt hLnn', Real.mul_self_sqrt hJnn]
  -- the bounded-above data for the witness gradient
  have hBdd := bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad R u.toH1Function
  set S : ℝ := cubeBesovNegativeVectorSeminormTwo R (3 / 8)
    (fun x => u.toH1Function.grad x) with hS
  -- the pure-potential witness budget
  have hgradeq : ∀ᵐ x ∂ volumeMeasureOn ((cubeDomain R : Domain d) : Set (Vec d)),
      u.toH1Function.grad x =
        (2 : ℝ)⁻¹ • (vAdj'.toH1.grad x + v'.toH1.grad x) + p := by
    rw [hv'grad, hvAdj'grad]; exact hu
  have hwitness : S ≤ potWitnessConst * X := by
    have hmain := cubeBesovNegativeVectorSeminormTwo_potWitnessGrad_le R G p
      (vAdj := vAdj') (v := v') hvAdj'' hv' u hgradeq
    rw [hJeq] at hmain
    exact hmain
  -- the Term BC budget
  have hBC := scaleNormalizedPositiveBesovVectorNormTwo_fluxTermBCField_le h hsub hL u hBdd
  have hreg := forceBesovRegularity_potTermBCField h hsub u hBdd
  -- the Term A budget
  have hregA := forceBesovRegularity_termAField_cube h R hsub hL p
  have hAle := scaleNormalizedPositiveBesovVectorNormTwo_termAField_cube_le h R hsub hL p
  -- the splitting identity at the pure-potential loading
  have hsplit := Assembly.quadForm_coarseMatrixDerivative_eq_split (cubeDomain R) b g
    (Dh := unitCubeDerivData h)
    (fun k i j => memLp_firstDeriv_restrict h hsub k i j)
    (fun k i j => hasWeakPartialDeriv_value_restrict h (cubeDomain R).isOpen hsub k i j)
    p 0 vAdj v hvAdj hv u hu
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
  rw [dhPotentialForm, hsplit, hTA, hTBC]
  set K : ℝ := fluxPairingConst d with hK
  have hKnn : 0 ≤ K := fluxPairingConst_nonneg d
  set SA : ℝ := cubeAverage R (fun x => vecDot (v.toH1.grad x)
    (matVecMul (matTranspose (h.toLInfSkewMatrixFieldOn.1.1 x)) p)) with hSA
  set SBC : ℝ := cubeAverage R (fun x => vecDot (v.toH1.grad x)
    (fluxTermBCField h u x)) with hSBC
  have hA : |SA| ≤ K * (termABesovConst d * vecNorm p * h.w1Infinity) * X := hpairA
  have hBC' : |SBC| ≤ K *
      (Ch03.scaleNormalizedPositiveBesovVectorNormTwo R (3 / 8)
        (fluxTermBCField h u)) * X := hpairBC
  have hBCbudget : Ch03.scaleNormalizedPositiveBesovVectorNormTwo R (3 / 8)
      (fluxTermBCField h u) ≤
      fluxTermBCConst d * h.gradientW1Infinity *
        (cubeScaleFactor R * (potWitnessConst * X)) := by
    refine hBC.trans ?_
    have hcoef : (0 : ℝ) ≤ fluxTermBCConst d * h.gradientW1Infinity :=
      mul_nonneg (fluxTermBCConst_nonneg d) hgnn
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hwitness hLnn) hcoef
  have hBCfinal : |SBC| ≤ K * (fluxTermBCConst d * h.gradientW1Infinity *
      (cubeScaleFactor R * (potWitnessConst * X))) * X := by
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
  have hfold : 2 * (K * (termABesovConst d * vecNorm p * h.w1Infinity) * X) +
      2 * (K * (fluxTermBCConst d * h.gradientW1Infinity *
        (cubeScaleFactor R * (potWitnessConst * X))) * X) =
      potCubeConstA d * h.w1Infinity * vecNorm p * X +
        potCubeConstB d * h.gradientW1Infinity * cubeScaleFactor R * L * J := by
    unfold potCubeConstA potCubeConstB
    rw [hK]
    calc 2 * (fluxPairingConst d * (termABesovConst d * vecNorm p * h.w1Infinity) * X) +
        2 * (fluxPairingConst d * (fluxTermBCConst d * h.gradientW1Infinity *
          (cubeScaleFactor R * (potWitnessConst * X))) * X)
        = 2 * fluxPairingConst d * termABesovConst d * h.w1Infinity * vecNorm p * X +
            2 * fluxPairingConst d * fluxTermBCConst d * potWitnessConst *
              h.gradientW1Infinity * cubeScaleFactor R * (X * X) := by ring
      _ = _ := by rw [hXX]; ring
  calc 2 * |SA| + 2 * |SBC|
      ≤ 2 * (K * (termABesovConst d * vecNorm p * h.w1Infinity) * X) +
          2 * (K * (fluxTermBCConst d * h.gradientW1Infinity *
            (cubeScaleFactor R * (potWitnessConst * X))) * X) := by
        exact add_le_add (by linarith [hA]) (by linarith [hBCfinal])
    _ = _ := hfold

end

end Algsuperdiff.Section24.Sensitivity.Provider.BigLambda
