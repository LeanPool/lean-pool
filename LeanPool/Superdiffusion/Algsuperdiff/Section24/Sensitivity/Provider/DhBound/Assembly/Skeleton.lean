/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly.BesovPairing
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly.SplitIdentity

/-!
# Skeleton

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Assembly skeleton for the frozen `D_h` bound

Source: ABK26 (proof of `l.Dh.bound`).

The proof of the frozen target
`Algsuperdiff.Frozen.Section24.coarseMatrixDerivative_bound` is assembled from

* the splitting identity `quadForm_coarseMatrixDerivative_unitCube_eq_split`
  (`e.sensitivity.basic.split`);
* the Besov pairing engine
  `abs_cubeAverage_vecDot_grad_le_of_positiveBesov_bound`
  (`e.sensitivity.basic.split1`, `e.split.besov.stuff.begin`), which already
  contains the coarse Poincaré inequality `e.w.wstar.to.energy`;
* two **positive Besov budgets**, one for each factor of the split.

This module performs the algebraic assembly of the first two, leaving the two
budgets as explicit premises of an internal helper.

  `B_A`  bounds the positive `B^{3/8}_{2,2}` norm of `x ↦ hᵀ(x) p`,
  `B_BC` bounds the positive `B^{3/8}_{2,2}` norm of
         `x ↦ (w + w* + ℓ_p)(x) (∇·h)(x)`.

The helper is deliberately **internal**: it is never re-exported as a provider
result while its premises are undischarged.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Moving the fixed factor to the second slot of the pairing -/

/-- Adjoint form of the matrix pairing: `x · (M y) = y · (Mᵀ x)`. -/
theorem vecDot_matVecMul_eq_vecDot_matTranspose (M : Mat d) (x y : Vec d) :
    vecDot x (matVecMul M y) = vecDot y (matVecMul (matTranspose M) x) := by
  classical
  unfold vecDot matVecMul matTranspose
  calc
    (∑ i, x i * ∑ j, M i j * y j) = ∑ i, ∑ j, x i * (M i j * y j) :=
      Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    _ = ∑ j, ∑ i, x i * (M i j * y j) := Finset.sum_comm
    _ = ∑ j, y j * ∑ i, (Matrix.transpose M) j i * x i := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [Matrix.transpose_apply]; ring

/-- Scalar multiple form of the pairing: `c (D · g) = g · (c • D)`. -/
theorem mul_vecDot_eq_vecDot_smul (c : ℝ) (D g : Vec d) :
    c * vecDot D g = vecDot g (c • D) := by
  classical
  unfold vecDot
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- Pointwise congruence for the Chapter 2 average. -/
theorem average_congr_funext {U : Domain d} {f g : Vec d → ℝ}
    (hfg : ∀ x, f x = g x) :
    Book.Ch02.average U f = Book.Ch02.average U g := by
  rw [funext hfg]

/-! ## The assembly helper -/

/-- **Internal assembly helper for the frozen `D_h` bound.**

Given the splitting witness `u` and the two positive Besov budgets `B_A`,
`B_BC`, the frozen quadratic form is bounded by

  `4 K(d) (B_A + B_BC) λ_{3/8,2}^{-1/2} J^{1/2}`,
  `K(d) = (1 + d 3^{d+1}) c_{3/8,2}^{-1/2}`. -/
theorem abs_quadForm_coarseMatrixDerivative_le_of_positiveBesov_budgets
    [NeZero d] (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : UnitCubeSkewW2Infinity d) (p q : Vec d)
    (F : Ch03.CoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (vAdj : Solution (cubeDomain (originCube d 0)) a.transpose)
    (v : Solution (cubeDomain (originCube d 0)) a)
    (hvAdj : IsResponseMaximizer (cubeDomain (originCube d 0)) a.transpose p (-q) vAdj)
    (hv : IsResponseMaximizer (cubeDomain (originCube d 0)) a p q v)
    (u : H10Function ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (hu : ∀ᵐ x ∂volumeMeasureOn
        ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      u.toH1Function.grad x =
        (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x) + p)
    {BA BBC : ℝ}
    (hHA : Ch03.ForceBesovRegularity (originCube d 0) (3 / 8)
      (fun x => matVecMul (matTranspose (h.toLInfSkewMatrixFieldOn.1.1 x)) p))
    (hHAle : Ch03.scaleNormalizedPositiveBesovVectorNormTwo (originCube d 0) (3 / 8)
      (fun x => matVecMul (matTranspose (h.toLInfSkewMatrixFieldOn.1.1 x)) p) ≤ BA)
    (hHBC : Ch03.ForceBesovRegularity (originCube d 0) (3 / 8)
      (fun x => u.toH1Function.toFun x • matWeakDiv (unitCubeDerivData h) x))
    (hHBCle : Ch03.scaleNormalizedPositiveBesovVectorNormTwo (originCube d 0) (3 / 8)
      (fun x => u.toH1Function.toFun x • matWeakDiv (unitCubeDerivData h) x) ≤ BBC) :
    |blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative (cubeDomain (originCube d 0)) a
          h.toLInfSkewMatrixFieldOn.1) (p, -q))| ≤
      2 * ((1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
            (2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2))) *
          (BA + BBC) *
        (Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
          Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q)) := by
  classical
  have hvFmax :
      IsResponseMaximizer (cubeDomain (originCube d 0))
        (F.coeffOn (originCube d 0)) p q (Solution.ofAEEq hF.symm v) :=
    hv.ofAEEq hF.symm
  have hgauge : unitCubeLambda (3 / 8) (.finite 2) a =
      Ch02.lambdaSq (originCube d 0) (3 / 8) (.finite 2) F :=
    unitCubeLambda_characterization (3 / 8 : ℝ) (.finite 2) a F hF
  have hJ : responseJ (cubeDomain (originCube d 0))
        (F.coeffOn (originCube d 0)) p q =
      responseJ (cubeDomain (originCube d 0)) a p q := responseJ_eq_ofAEEq hF p q
  have hsplit :=
    quadForm_coarseMatrixDerivative_unitCube_eq_split a h p q vAdj v hvAdj hv u hu
  -- Term A as a cube-average pairing against the gradient
  have hTA : vecDot p (Book.Ch02.averageVec (cubeDomain (originCube d 0))
        (fun x => matVecMul (h.toLInfSkewMatrixFieldOn.1.1 x) (v.toH1.grad x))) =
      cubeAverage (originCube d 0) (fun x => vecDot (v.toH1.grad x)
        (matVecMul (matTranspose (h.toLInfSkewMatrixFieldOn.1.1 x)) p)) := by
    rw [← average_vecDot_const_eq_vecDot_averageVec
      (U := cubeDomain (originCube d 0))
      (G := fun x => matVecMul (h.toLInfSkewMatrixFieldOn.1.1 x) (v.toH1.grad x))
      (fun i => (memScalarL2_matVecMul_grad h.toLInfSkewMatrixFieldOn v.toH1 i).integrable
        one_le_two) p]
    rw [← average_cubeDomain_eq_cubeAverage]
    exact average_congr_funext (U := cubeDomain (originCube d 0)) fun x =>
      vecDot_matVecMul_eq_vecDot_matTranspose _ _ _
  -- Term BC as a cube-average pairing against the gradient
  have hTBC : Book.Ch02.average (cubeDomain (originCube d 0)) (fun x =>
        u.toH1Function.toFun x *
          vecDot (matWeakDiv (unitCubeDerivData h) x) (v.toH1.grad x)) =
      cubeAverage (originCube d 0) (fun x => vecDot (v.toH1.grad x)
        (u.toH1Function.toFun x • matWeakDiv (unitCubeDerivData h) x)) := by
    rw [← average_cubeDomain_eq_cubeAverage]
    exact average_congr_funext (U := cubeDomain (originCube d 0)) fun x =>
      mul_vecDot_eq_vecDot_smul _ _ _
  -- the two pairing estimates
  have hboundA := abs_cubeAverage_vecDot_grad_le_of_positiveBesov_bound
    (Q := originCube d 0) (F := F) (v := Solution.ofAEEq hF.symm v) hvFmax _ hHA hHAle
  have hboundBC := abs_cubeAverage_vecDot_grad_le_of_positiveBesov_bound
    (Q := originCube d 0) (F := F) (v := Solution.ofAEEq hF.symm v) hvFmax _ hHBC hHBCle
  rw [Solution.toH1_ofAEEq, ← hgauge, hJ] at hboundA hboundBC
  rw [hsplit, hTA, hTBC]
  set K : ℝ := (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
    (2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2)) with hK
  set SA : ℝ := cubeAverage (originCube d 0) (fun x => vecDot (v.toH1.grad x)
    (matVecMul (matTranspose (h.toLInfSkewMatrixFieldOn.1.1 x)) p)) with hSA
  set SBC : ℝ := cubeAverage (originCube d 0) (fun x => vecDot (v.toH1.grad x)
    (u.toH1Function.toFun x • matWeakDiv (unitCubeDerivData h) x)) with hSBC
  set L : ℝ := Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
    Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) with hL
  have htri : |(-2 : ℝ) * SA - 2 * SBC| ≤ 2 * |SA| + 2 * |SBC| := by
    calc
      |(-2 : ℝ) * SA - 2 * SBC| ≤ |(-2 : ℝ) * SA| + |(2 : ℝ) * SBC| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_le ((-2 : ℝ) * SA) (-((2 : ℝ) * SBC))
      _ = 2 * |SA| + 2 * |SBC| := by
        rw [abs_mul, abs_mul]; norm_num
  refine htri.trans ?_
  have h1 : |SA| ≤ K * BA * L := hboundA
  have h2 : |SBC| ≤ K * BBC * L := hboundBC
  linarith [h1, h2]

/-! ## The Young/triangle fold into the frozen right-hand side -/

/-- **Arithmetic fold.**  The abstract inequality behind the last two lines of
the source proof: substituting the two budget bounds into
`|X| ≤ 2K(B_A + B_BC) √(λ⁻¹) √J` and expanding
`(P · 𝐀 P)^{1/2} = (2(J + p·q))^{1/2} ≤ √2 (√J + √|p·q|)`
(`e.J.by.means.of.bfA`) produces exactly the frozen right-hand side. -/
theorem abs_le_frozen_shape_of_budget_bounds
    {X K CA CBC np w g sl spq sJ BA BBC : ℝ}
    (hK : 0 ≤ K) (hCA : 0 ≤ CA) (hCBC : 0 ≤ CBC)
    (hnp : 0 ≤ np) (hw : 0 ≤ w) (hg : 0 ≤ g)
    (hsl : 0 ≤ sl) (hspq : 0 ≤ spq) (hsJ : 0 ≤ sJ)
    (hX : |X| ≤ 2 * K * (BA + BBC) * (sl * sJ))
    (hBA : BA ≤ CA * np * w)
    (hBBC : BBC ≤ CBC * g * sl * (sJ + spq)) :
    |X| ≤ 2 * K * (CA + CBC) * (np * w * sl + spq * g * (sl * sl)) * sJ +
      2 * K * (CA + CBC) * g * (sl * sl) * (sJ * sJ) := by
  have hslsJ : 0 ≤ sl * sJ := mul_nonneg hsl hsJ
  have hKnn : (0 : ℝ) ≤ 2 * K := by linarith
  have hsum : BA + BBC ≤ CA * np * w + CBC * g * sl * (sJ + spq) :=
    add_le_add hBA hBBC
  have hstep : 2 * K * (BA + BBC) * (sl * sJ) ≤
      2 * K * (CA * np * w + CBC * g * sl * (sJ + spq)) * (sl * sJ) := by
    have := mul_le_mul_of_nonneg_left hsum hKnn
    exact mul_le_mul_of_nonneg_right this hslsJ
  refine (hX.trans hstep).trans ?_
  -- termwise comparison of the expanded products
  have hCle : 2 * K * CA ≤ 2 * K * (CA + CBC) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hCBC) hKnn
  have hCle' : 2 * K * CBC ≤ 2 * K * (CA + CBC) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hCA) hKnn
  have t1 : 0 ≤ np * w * sl * sJ := by positivity
  have t2 : 0 ≤ g * (sl * sl) * (sJ * sJ) := by positivity
  have t3 : 0 ≤ g * (sl * sl) * (spq * sJ) := by positivity
  have e1 : 2 * K * CA * (np * w * sl * sJ) ≤
      2 * K * (CA + CBC) * (np * w * sl * sJ) :=
    mul_le_mul_of_nonneg_right hCle t1
  have e2 : 2 * K * CBC * (g * (sl * sl) * (sJ * sJ)) ≤
      2 * K * (CA + CBC) * (g * (sl * sl) * (sJ * sJ)) :=
    mul_le_mul_of_nonneg_right hCle' t2
  have e3 : 2 * K * CBC * (g * (sl * sl) * (spq * sJ)) ≤
      2 * K * (CA + CBC) * (g * (sl * sl) * (spq * sJ)) :=
    mul_le_mul_of_nonneg_right hCle' t3
  linarith [e1, e2, e3]

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly
