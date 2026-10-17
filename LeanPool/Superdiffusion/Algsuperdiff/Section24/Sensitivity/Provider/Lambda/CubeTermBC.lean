/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CubeFieldData
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.DepthDowngrade
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov.Product
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.H1Transport
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.PairingConstants

/-!
# CubeTermBC

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The Term BC positive Besov budget at a general triadic cube

Source: ABK26 (`e.split.besov.stuff.begin` through `e.split.besov.stuff`),
stated at an arbitrary sub-cube `R` of the frozen unit-cube carrier.

Everything in the source estimate is scale covariant.  At a cube of scale factor
`L = cubeScaleFactor R` the three ingredients read

```
‖u‖_{L²(R)}                ≤ L · C · [∇u]^-_{B^{-3/8}_{2,2}(R)}   (zero-trace value)
[u]^+_{B^{3/8}_{2,2}(R),N} ≤ L · C · [∇u]^-_{B^{-3/8}_{2,2}(R)}   (function from gradient)
‖u ξ‖^+_{B^{3/8}_{2,2}(R)} ≤ C (L ‖∇ξ‖_∞ ‖u‖_{L²(R)} + ‖ξ‖_∞ [u]^+_{...})
```

so the whole Term BC budget carries exactly one factor `L`.  Since every
descendant of the unit cube has `L ≤ 1`, the surplus factor `L` produced by the
first summand is discarded.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Lambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Scale-weight bookkeeping -/

theorem cubeScaleFactor_pos_cube (R : TriadicCube d) : 0 < cubeScaleFactor R := by
  simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale)

theorem cubeBesovScaleWeight_pos_cube (s : ℝ) (R : TriadicCube d) :
    0 < cubeBesovScaleWeight s R := by
  unfold cubeBesovScaleWeight
  exact Real.rpow_pos_of_pos (cubeScaleFactor_pos_cube R) _

theorem cubeBesovScaleWeight_neg_one_eq (R : TriadicCube d) :
    cubeBesovScaleWeight (-1 : ℝ) R = cubeScaleFactor R := by
  unfold cubeBesovScaleWeight
  rw [neg_neg, Real.rpow_one]

theorem cubeBesovScaleWeight_neg_half_sq (R : TriadicCube d) :
    cubeBesovScaleWeight (-(1 / 2) : ℝ) R * cubeBesovScaleWeight (-(1 / 2) : ℝ) R =
      cubeScaleFactor R := by
  rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
  rw [show (-(1 / 2) : ℝ) + (-(1 / 2)) = -1 by norm_num]
  exact cubeBesovScaleWeight_neg_one_eq R

/-! ## The zero-trace `L²` estimate at a general cube -/

/-- The constant of the zero-trace `L²` estimate at the gauge exponent. -/
def fluxZeroTraceConst (d : ℕ) : ℝ :=
  PairingConstants.zeroTraceValueConst d

theorem fluxZeroTraceConst_nonneg (d : ℕ) : 0 ≤ fluxZeroTraceConst d :=
  PairingConstants.zeroTraceValueConst_nonneg d

/-- **The zero-trace `L²` estimate at an arbitrary triadic cube.**  The scale
factor of the cube appears once. -/
theorem cubeLpNorm_two_h10_cube_le [NeZero d] (R : TriadicCube d)
    (u : H10Function ((cubeDomain R : Domain d) : Set (Vec d))) :
    cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x) ≤
      cubeScaleFactor R * (fluxZeroTraceConst d *
        cubeBesovNegativeVectorSeminormTwo R (3 / 8)
          (fun x => u.toH1Function.grad x)) := by
  have h :=
    Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_h10_le_grad_negativeBesovTwo
      (Q := R) (t := (3 / 16 : ℝ)) (Ch03.publicH10ToCubeSet u)
      (by norm_num) (by norm_num)
  rw [Ch03.publicH10ToCubeSet_toH1Function_toFun,
    Ch03.publicH10ToCubeSet_toH1Function_grad,
    show (2 : ℝ) * (3 / 16) = 3 / 8 by norm_num] at h
  have hW : (0 : ℝ) < cubeBesovScaleWeight (1 : ℝ) R := cubeBesovScaleWeight_pos_cube 1 R
  have hstep := mul_le_mul_of_nonneg_left h (le_of_lt (cubeBesovScaleWeight_pos_cube (-1 : ℝ) R))
  have hcancel : cubeBesovScaleWeight (-1 : ℝ) R * (cubeBesovScaleWeight (1 : ℝ) R *
      cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x)) =
      cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x) := by
    rw [← mul_assoc, cubeBesovScaleWeight_mul_eq_scaleWeight_add]
    rw [show (-1 : ℝ) + 1 = 0 by norm_num]
    simp [cubeBesovScaleWeight]
  rw [hcancel] at hstep
  refine hstep.trans (le_of_eq ?_)
  rw [cubeBesovScaleWeight_neg_one_eq]
  unfold fluxZeroTraceConst PairingConstants.zeroTraceValueConst
  ring

/-! ## The function-from-gradient estimate at a general cube -/

/-- The multiscale Poincaré constant of CoarseGraining does not depend on the cube. -/
theorem fullVectorPoincareConstant_eq_origin (R : TriadicCube d) :
    Ch01.Legacy.fullVectorPoincareConstant R =
      Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) :=
  rfl

/-- **The function-from-gradient estimate at an arbitrary triadic cube**, in the
`ℓ²` form.  The scale factor of the cube appears once. -/
theorem cubeBesovPositiveScalarPartialSeminormTwo_h1_cube_le
    (R : TriadicCube d) (M : ℕ) (u : H1Function (openCubeSet R))
    (hBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo R (3 / 8) N (fun x => u.grad x))) :
    cubeBesovPositiveScalarPartialSeminormTwo R (3 / 8) M (fun x => u x) ≤
      cubeScaleFactor R * (depthDowngradeConst d *
        cubeBesovNegativeVectorSeminormTwo R (3 / 8) (fun x => u.grad x)) := by
  classical
  set S : ℝ := cubeBesovNegativeVectorSeminormTwo R (3 / 8) (fun x => u.grad x) with hS
  set W : ℝ := cubeBesovScaleWeight (-(1 / 2) : ℝ) R with hW
  have hWnn : 0 ≤ W := (cubeBesovScaleWeight_pos_cube _ R).le
  -- Step 1: the `ℓ∞ → ℓ²` downgrade for the fluctuation
  have hdown :=
    cubeBesovPositiveScalarPartialSeminormTwo_le_gap_geometric_mul_partialNormTop
      R (s := (3 / 8 : ℝ)) (t := (1 / 2 : ℝ)) (by norm_num) M
      (cubeFluctuation R (fun x => u x))
  -- Step 2: the fluctuation has the same positive seminorm
  have hmem : ∀ j ∈ Finset.range (M + 1),
      ∀ T ∈ descendantsAtDepth R j,
      MemLp (fun x => u x) (2 : ℝ≥0∞) (normalizedCubeMeasure T) := by
    intro j _ T hT
    exact memLp_on_descendant_of_memLp_generic hT u.memL2_normalizedCubeMeasure
  have hfluct :
      cubeBesovPositiveScalarPartialSeminormTwo R (3 / 8) M
          (cubeFluctuation R (fun x => u x)) =
        cubeBesovPositiveScalarPartialSeminormTwo R (3 / 8) M (fun x => u x) :=
    cubeBesovPositiveScalarPartialSeminormTwo_sub_const R (3 / 8) M
      (fun x => u x) (cubeAverage R (fun x => u x)) hmem
  rw [hfluct] at hdown
  -- Step 3: the multiscale Poincaré estimate at `t = 1/2`
  have hpoincare :=
    Ch01.Legacy.h1_fluctuation_partialNormTop_two_le_sum_grad_circNorm
      R (1 / 2 : ℝ) M u (by norm_num) (by norm_num)
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hhalf] at hpoincare
  -- Step 4: the componentwise circ comparison
  have hcirc : ∀ i : Fin d,
      cubeBesovCircNorm R (1 / 2 : ℝ) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) ≤
        W * (sensitivityGapConst * S) := by
    intro i
    exact cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_gap_geometric_of_bddAbove
      (Q := R) (a := (1 / 2 : ℝ)) (b := (3 / 8 : ℝ)) (by norm_num)
      (fun x => u.grad x) i hBdd
  have hsum :
      (∑ i : Fin d,
          cubeBesovCircNorm R (1 / 2 : ℝ) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i)) ≤
        (d : ℝ) * (W * (sensitivityGapConst * S)) := by
    calc
      (∑ i : Fin d,
          cubeBesovCircNorm R (1 / 2 : ℝ) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i))
          ≤ ∑ _i : Fin d, W * (sensitivityGapConst * S) :=
            Finset.sum_le_sum fun i _ => hcirc i
      _ = (d : ℝ) * (W * (sensitivityGapConst * S)) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hPnn : (0 : ℝ) ≤ Ch01.Legacy.fullVectorPoincareConstant R * (3 : ℝ) ^ ((d : ℝ) + 1) :=
    mul_nonneg (Ch01.Legacy.fullVectorPoincareConstant_nonneg R)
      (Real.rpow_nonneg (by norm_num) _)
  have hstep :
      cubeBesovPartialNormTop R (1 / 2 : ℝ) (2 : ℝ≥0∞) M
          (cubeFluctuation R (fun x => u x)) ≤
        (Ch01.Legacy.fullVectorPoincareConstant R * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((d : ℝ) * (W * (sensitivityGapConst * S))) :=
    hpoincare.trans (mul_le_mul_of_nonneg_left hsum hPnn)
  refine hdown.trans ?_
  have hfinal := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hstep hWnn) sensitivityGapConst_nonneg
  refine hfinal.trans (le_of_eq ?_)
  rw [fullVectorPoincareConstant_eq_origin R]
  unfold depthDowngradeConst
  rw [show sensitivityGapConst *
      (W * (Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) * (3 : ℝ) ^ ((d : ℝ) + 1) *
        ((d : ℝ) * (W * (sensitivityGapConst * S))))) =
      (W * W) * (sensitivityGapConst *
        ((Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((d : ℝ) * sensitivityGapConst))) * S from by ring]
  rw [hW, cubeBesovScaleWeight_neg_half_sq]
  ring

/-- Nonnegativity of the origin-cube function-from-gradient constant. -/
theorem depthDowngradeConst_nonneg' (d : ℕ) :
    0 ≤ depthDowngradeConst d := by
  have hg : (0 : ℝ) ≤ sensitivityGapConst := sensitivityGapConst_nonneg
  have hp : (0 : ℝ) ≤ Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) :=
    Ch01.Legacy.fullVectorPoincareConstant_nonneg _
  have hr : (0 : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) + 1) := Real.rpow_nonneg (by norm_num) _
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold depthDowngradeConst
  positivity

/-! ## Elementary vector bookkeeping -/

theorem sqrt_vecNormSq_le_sqrt_card_mul_norm' (w : Vec d) :
    Real.sqrt (vecNormSq w) ≤ Real.sqrt (d : ℝ) * ‖w‖ := by
  exact PairingConstants.sqrt_vecNormSq_le_sqrt_dimension_mul_norm w

/-! ## The Term BC field at a general cube -/

/-- The Term BC field `x ↦ u(x) (∇·h)(x)` on a sub-cube. -/
def fluxTermBCField (h : UnitCubeSkewW2Infinity d) {R : TriadicCube d}
    (u : H10Function ((cubeDomain R : Domain d) : Set (Vec d))) : Vec d → Vec d :=
  fun x => u.toH1Function.toFun x • matWeakDiv (unitCubeDerivData h) x

theorem memLp_u_two_cube {R : TriadicCube d}
    (u : H10Function ((cubeDomain R : Domain d) : Set (Vec d))) :
    MemLp (fun x => u.toH1Function.toFun x) (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
  H1Function.memL2_normalizedCubeMeasure u.toH1Function

theorem memLp_fluxTermBCField_two (h : UnitCubeSkewW2Infinity d)
    {R : TriadicCube d}
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (u : H10Function ((cubeDomain R : Domain d) : Set (Vec d))) :
    MemLp (fluxTermBCField h u) (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
  MemLp.smul (memLp_u_two_cube u) (memLp_matWeakDiv_cube h R hsub ∞)

/-- The finite-depth Besov product estimate for the Term BC field on a
sub-cube. -/
theorem cubeBesovPositiveVectorPartialSeminormTwo_fluxTermBCField_le
    (h : UnitCubeSkewW2Infinity d) {R : TriadicCube d}
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (u : H10Function ((cubeDomain R : Domain d) : Set (Vec d))) (N : ℕ) :
    cubeBesovPositiveVectorPartialSeminormTwo R (3 / 8) N (fluxTermBCField h u) ≤
      besovMultConst (3 / 8) *
        (cubeScaleFactor R * ((d : ℝ) ^ 2 * h.gradientW1Infinity) *
            cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x) +
          (d : ℝ) * h.gradientW1Infinity *
            cubeBesovPositiveScalarPartialSeminormTwo R (3 / 8) N
              (fun x => u.toH1Function.toFun x)) := by
  classical
  have hg : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hB : (0 : ℝ) ≤ (d : ℝ) ^ 2 * h.gradientW1Infinity := by positivity
  have hmain :=
    cubeBesovPositiveVectorPartialSeminormTwo_scalar_smul_le_besovMult
      R (3 / 8) N (fun x => u.toH1Function.toFun x) (fluxDivRep h)
      hB (by norm_num) (memLp_u_two_cube u) (memLp_fluxDivRep_top_cube h R hsub)
      (fun x _ y _ => fluxDivRep_lipschitz h x y)
  have hcongr :
      cubeBesovPositiveVectorPartialSeminormTwo R (3 / 8) N
          (fun x => u.toH1Function.toFun x • fluxDivRep h x) =
        cubeBesovPositiveVectorPartialSeminormTwo R (3 / 8) N (fluxTermBCField h u) := by
    refine cubeBesovPositiveVectorPartialSeminormTwo_congr_ae R (3 / 8) N ?_
    filter_upwards [fluxDivRep_ae_eq_cube h R hsub] with x hx
    simp [fluxTermBCField, hx]
  rw [hcongr] at hmain
  refine hmain.trans ?_
  have hmult : (0 : ℝ) ≤ besovMultConst (3 / 8) :=
    (besovMultConst_pos (s := (3 / 8 : ℝ)) (by norm_num)).le
  refine mul_le_mul_of_nonneg_left ?_ hmult
  refine add_le_add le_rfl ?_
  refine mul_le_mul_of_nonneg_right (cubeLpNorm_infty_fluxDivRep_le_cube h R hsub) ?_
  exact Real.sqrt_nonneg _

/-! ## The Term BC budget -/

/-- The explicit Term B constant at the pure-flux loading. -/
def fluxTermBCConst (d : ℕ) : ℝ :=
  Real.sqrt (d : ℝ) * (d : ℝ) * fluxZeroTraceConst d +
    besovMultConst (3 / 8) *
      ((d : ℝ) ^ 2 * fluxZeroTraceConst d + (d : ℝ) * depthDowngradeConst d)

theorem fluxTermBCConst_nonneg (d : ℕ) : 0 ≤ fluxTermBCConst d := by
  have h1 : (0 : ℝ) ≤ fluxZeroTraceConst d := fluxZeroTraceConst_nonneg d
  have h2 : (0 : ℝ) ≤ besovMultConst (3 / 8) :=
    (besovMultConst_pos (s := (3 / 8 : ℝ)) (by norm_num)).le
  have h3 : (0 : ℝ) ≤ depthDowngradeConst d := depthDowngradeConst_nonneg' d
  have h5 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have h6 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold fluxTermBCConst
  positivity

/-- **The Term BC positive Besov budget on a sub-cube of the frozen carrier.**

The bound carries exactly one factor of `cubeScaleFactor R`; the surplus factor
produced by the product rule is discarded using `L ≤ 1`. -/
theorem scaleNormalizedPositiveBesovVectorNormTwo_fluxTermBCField_le [NeZero d]
    (h : UnitCubeSkewW2Infinity d) {R : TriadicCube d}
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (hL : cubeScaleFactor R ≤ 1)
    (u : H10Function ((cubeDomain R : Domain d) : Set (Vec d)))
    (hBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo R (3 / 8) N
        (fun x => u.toH1Function.grad x))) :
    Ch03.scaleNormalizedPositiveBesovVectorNormTwo R (3 / 8) (fluxTermBCField h u) ≤
      fluxTermBCConst d * h.gradientW1Infinity *
        (cubeScaleFactor R *
          cubeBesovNegativeVectorSeminormTwo R (3 / 8)
            (fun x => u.toH1Function.grad x)) := by
  classical
  have hg : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  set L : ℝ := cubeScaleFactor R with hLdef
  have hLnn : 0 ≤ L := (cubeScaleFactor_pos_cube R).le
  set S : ℝ := cubeBesovNegativeVectorSeminormTwo R (3 / 8)
    (fun x => u.toH1Function.grad x) with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    refine le_trans (cubeBesovNegativeVectorPartialSeminormTwo_nonneg R (3 / 8) 0
      (fun x => u.toH1Function.grad x)) ?_
    unfold cubeBesovNegativeVectorSeminormTwo
    exact le_csSup hBdd (Set.mem_range_self 0)
  have hztc : (0 : ℝ) ≤ fluxZeroTraceConst d := fluxZeroTraceConst_nonneg d
  have hddc : (0 : ℝ) ≤ depthDowngradeConst d := depthDowngradeConst_nonneg' d
  have hmult : (0 : ℝ) ≤ besovMultConst (3 / 8) :=
    (besovMultConst_pos (s := (3 / 8 : ℝ)) (by norm_num)).le
  -- the two `u`-estimates
  have hL2 : cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x) ≤
      L * (fluxZeroTraceConst d * S) := cubeLpNorm_two_h10_cube_le R u
  have hPos : ∀ N : ℕ,
      cubeBesovPositiveScalarPartialSeminormTwo R (3 / 8) N
        (fun x => u.toH1Function.toFun x) ≤ L * (depthDowngradeConst d * S) := fun N =>
    cubeBesovPositiveScalarPartialSeminormTwo_h1_cube_le R N u.toH1Function hBdd
  -- the mean term
  have hmean : Real.sqrt (vecNormSq (cubeAverageVec R (fluxTermBCField h u))) ≤
      Real.sqrt (d : ℝ) * ((d : ℝ) * h.gradientW1Infinity) *
        (L * (fluxZeroTraceConst d * S)) := by
    refine (sqrt_vecNormSq_le_sqrt_card_mul_norm' _).trans ?_
    have hnorm := norm_cubeAverageVec_scalar_smul_le_cubeLpNorm_infty_mul_cubeLpNorm_two
      R (fun x => u.toH1Function.toFun x) (matWeakDiv (unitCubeDerivData h))
      (memLp_u_two_cube u) (memLp_matWeakDiv_cube h R hsub ∞)
    have hstep : ‖cubeAverageVec R (fluxTermBCField h u)‖ ≤
        ((d : ℝ) * h.gradientW1Infinity) * (L * (fluxZeroTraceConst d * S)) := by
      refine hnorm.trans ?_
      exact mul_le_mul (cubeLpNorm_infty_matWeakDiv_le_cube h R hsub) hL2
        (cubeLpNorm_nonneg _ _ _) (by positivity)
    calc Real.sqrt (d : ℝ) * ‖cubeAverageVec R (fluxTermBCField h u)‖
        ≤ Real.sqrt (d : ℝ) *
            (((d : ℝ) * h.gradientW1Infinity) * (L * (fluxZeroTraceConst d * S))) :=
          mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _)
      _ = Real.sqrt (d : ℝ) * ((d : ℝ) * h.gradientW1Infinity) *
            (L * (fluxZeroTraceConst d * S)) := by ring
  -- the seminorm term
  have hsemi : cubeBesovPositiveVectorSeminormTwo R (3 / 8) (fluxTermBCField h u) ≤
      besovMultConst (3 / 8) *
        (L * ((d : ℝ) ^ 2 * h.gradientW1Infinity) * (L * (fluxZeroTraceConst d * S)) +
          (d : ℝ) * h.gradientW1Infinity * (L * (depthDowngradeConst d * S))) := by
    refine cubeBesovPositiveVectorSeminormTwo_le_of_partialBound _ _ _ fun N => ?_
    refine (cubeBesovPositiveVectorPartialSeminormTwo_fluxTermBCField_le h hsub u N).trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hmult
    · exact mul_le_mul_of_nonneg_left hL2 (by positivity)
    · exact mul_le_mul_of_nonneg_left (hPos N) (by positivity)
  -- assembly
  have hsum :
      Ch03.scaleNormalizedPositiveBesovVectorNormTwo R (3 / 8) (fluxTermBCField h u) ≤
        Real.sqrt (d : ℝ) * ((d : ℝ) * h.gradientW1Infinity) *
            (L * (fluxZeroTraceConst d * S)) +
          besovMultConst (3 / 8) *
            (L * ((d : ℝ) ^ 2 * h.gradientW1Infinity) * (L * (fluxZeroTraceConst d * S)) +
              (d : ℝ) * h.gradientW1Infinity * (L * (depthDowngradeConst d * S))) := by
    unfold Ch03.scaleNormalizedPositiveBesovVectorNormTwo
    exact add_le_add hmean hsemi
  refine hsum.trans ?_
  -- discard the surplus factor `L ≤ 1`
  have hsq : L * ((d : ℝ) ^ 2 * h.gradientW1Infinity) * (L * (fluxZeroTraceConst d * S)) ≤
      (d : ℝ) ^ 2 * h.gradientW1Infinity * (L * (fluxZeroTraceConst d * S)) := by
    have hbase : (0 : ℝ) ≤ (d : ℝ) ^ 2 * h.gradientW1Infinity * (L * (fluxZeroTraceConst d * S))
      := by
      positivity
    nlinarith [hbase, hLnn, hL]
  have hstep2 : besovMultConst (3 / 8) *
      (L * ((d : ℝ) ^ 2 * h.gradientW1Infinity) * (L * (fluxZeroTraceConst d * S)) +
        (d : ℝ) * h.gradientW1Infinity * (L * (depthDowngradeConst d * S))) ≤
      besovMultConst (3 / 8) *
      ((d : ℝ) ^ 2 * h.gradientW1Infinity * (L * (fluxZeroTraceConst d * S)) +
        (d : ℝ) * h.gradientW1Infinity * (L * (depthDowngradeConst d * S))) :=
    mul_le_mul_of_nonneg_left (add_le_add hsq le_rfl) hmult
  refine (add_le_add le_rfl hstep2).trans (le_of_eq ?_)
  unfold fluxTermBCConst
  ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.Lambda
