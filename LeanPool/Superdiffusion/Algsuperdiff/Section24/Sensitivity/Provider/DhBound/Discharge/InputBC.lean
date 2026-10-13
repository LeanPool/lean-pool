/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.GradientSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.DepthDowngrade
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.VectorPerturbation
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.VectorMemLp
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov.Product
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.UnitCubeWeakIBP
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.H1Transport

/-!
# InputBC

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Term BC: the positive Besov budget of `x ↦ (w + w* + ℓ_p)(x) (∇·h)(x)`

Source: ABK26 (`e.split.besov.stuff.begin` through `e.split.besov.stuff`).  The
second factor of the `D_h` split is the product of the zero-trace witness `u`
with the weak divergence `∇·h`.  The source estimate is the Besov product rule
`e.besov.mult`

```
‖u (∇·h)‖_{B^{3/8}_{2,2}} ≤ C ‖∇(∇·h)‖_{L^∞} ‖u‖_{L²} + C ‖∇·h‖_{L^∞} [u]_{B^{3/8}_{2,2}} ,
```

followed by the two `u`-estimates

```
‖u‖_{L²}            ≤ C [∇u]_{B^{-3/8}_{2,2}}      (`e.fractional.Sobolev.embedding.zero.bndr`, `t = 3/16`),
[u]_{B^{3/8}_{2,2}} ≤ C [∇u]_{B^{-3/8}_{2,2}}      (`l.Besov.grad.to.function` in the `ℓ²` form),
```

and the witness-gradient budget of `Discharge.GradientSplit`.  Both `W^{1,∞}`
norms of `∇·h` are dominated by `d` (resp. `d²`) times the frozen
`gradientW1Infinity`, so the whole Term BC budget is proportional to
`h.gradientW1Infinity · λ_{3/8,2}^{-1/2} (J^{1/2} + |p·q|^{1/2})`, which is
exactly the shape consumed by `Assembly.abs_le_frozen_shape_of_budget_bounds`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The `L^∞` half of the frozen gradient norm -/

theorem toReal_eLpNorm_matrixDerivativeNorm_le_gradientW1Infinity
    (h : UnitCubeSkewW2Infinity d) :
    ENNReal.toReal
        (eLpNorm (fun x => matrixDerivativeNorm (h.firstDeriv x)) ∞
          (volumeMeasureOn
            ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))) ≤
      h.gradientW1Infinity := by
  unfold UnitCubeSkewW2Infinity.gradientW1Infinity
  exact le_max_right _ _

theorem ae_abs_firstDeriv_le_gradientW1Infinity (h : UnitCubeSkewW2Infinity d)
    (k i j : Fin d) :
    ∀ᵐ x ∂ volumeMeasureOn
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      |h.firstDeriv x (basisVec k) i j| ≤ h.gradientW1Infinity := by
  filter_upwards [ae_abs_apply_le_toReal_eLpNorm_matrixDerivativeNorm
    (D := h.firstDeriv) (fun k' i' j' => h.firstDeriv_memLp k' i' j') k i j] with x hx
  exact hx.trans (toReal_eLpNorm_matrixDerivativeNorm_le_gradientW1Infinity h)

/-! ## The weak divergence field and its Lipschitz representative -/

/-- The entrywise Lipschitz representative of the frozen first-derivative
field. -/
def derivRep (h : UnitCubeSkewW2Infinity d) (k i j : Fin d) (x : Vec d) : ℝ :=
  (exists_lipschitz_ae_eq_cubeSet_unitCubeSkewW2Infinity_firstDeriv h k i j).choose x

theorem derivRep_lipschitz (h : UnitCubeSkewW2Infinity d) (k i j : Fin d)
    (x y : Vec d) :
    |derivRep h k i j x - derivRep h k i j y| ≤
      (d : ℝ) * h.gradientW1Infinity * ‖x - y‖ := by
  simpa [Real.norm_eq_abs] using!
    (exists_lipschitz_ae_eq_cubeSet_unitCubeSkewW2Infinity_firstDeriv h k i j).choose_spec.1
      x y

theorem derivRep_ae_eq (h : UnitCubeSkewW2Infinity d) (k i j : Fin d) :
    (fun x => derivRep h k i j x)
      =ᵐ[normalizedCubeMeasure (originCube d 0)]
      fun x => h.firstDeriv x (basisVec k) i j :=
  ae_normalizedCubeMeasure_of_ae_cubeMeasure (originCube d 0)
    (exists_lipschitz_ae_eq_cubeSet_unitCubeSkewW2Infinity_firstDeriv h k i j).choose_spec.2

/-- The Lipschitz representative of the weak divergence `∇·h`. -/
def divRep (h : UnitCubeSkewW2Infinity d) : Vec d → Vec d :=
  fun x j => ∑ i : Fin d, derivRep h i i j x

theorem matWeakDiv_unitCubeDerivData_apply (h : UnitCubeSkewW2Infinity d)
    (x : Vec d) (j : Fin d) :
    matWeakDiv (unitCubeDerivData h) x j =
      ∑ i : Fin d, h.firstDeriv x (basisVec i) i j := rfl

theorem divRep_ae_eq (h : UnitCubeSkewW2Infinity d) :
    divRep h =ᵐ[normalizedCubeMeasure (originCube d 0)]
      matWeakDiv (unitCubeDerivData h) := by
  classical
  have hall : ∀ᵐ x ∂ normalizedCubeMeasure (originCube d 0), ∀ k i j : Fin d,
      derivRep h k i j x = h.firstDeriv x (basisVec k) i j := by
    rw [MeasureTheory.ae_all_iff]
    intro k
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact derivRep_ae_eq h k i j
  filter_upwards [hall] with x hx
  funext j
  show (∑ i : Fin d, derivRep h i i j x) = ∑ i : Fin d, h.firstDeriv x (basisVec i) i j
  exact Finset.sum_congr rfl fun i _ => hx i i j

theorem divRep_lipschitz (h : UnitCubeSkewW2Infinity d) (x y : Vec d) :
    ‖divRep h x - divRep h y‖ ≤
      ((d : ℝ) ^ 2 * h.gradientW1Infinity) * ‖x - y‖ := by
  classical
  have hg : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hB : 0 ≤ ((d : ℝ) ^ 2 * h.gradientW1Infinity) * ‖x - y‖ := by positivity
  rw [pi_norm_le_iff_of_nonneg hB]
  intro j
  calc ‖(divRep h x - divRep h y) j‖
      = |∑ i : Fin d, (derivRep h i i j x - derivRep h i i j y)| := by
        rw [Real.norm_eq_abs]
        congr 1
        show (∑ i : Fin d, derivRep h i i j x) - ∑ i : Fin d, derivRep h i i j y =
          ∑ i : Fin d, (derivRep h i i j x - derivRep h i i j y)
        rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin d, |derivRep h i i j x - derivRep h i i j y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (d : ℝ) * h.gradientW1Infinity * ‖x - y‖ :=
        Finset.sum_le_sum fun i _ => derivRep_lipschitz h i i j x y
    _ = ((d : ℝ) ^ 2 * h.gradientW1Infinity) * ‖x - y‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## `L^∞` bounds for the weak divergence -/

theorem memLp_firstDeriv_entry (h : UnitCubeSkewW2Infinity d) (k i j : Fin d)
    (r : ℝ≥0∞) :
    MemLp (fun x => h.firstDeriv x (basisVec k) i j) r
      (normalizedCubeMeasure (originCube d 0)) :=
  (memLp_normalizedCubeMeasure_of_memLp_frozen_carrier
    (q := ∞) (h.firstDeriv_memLp k i j)).mono_exponent le_top

theorem memLp_matWeakDiv_component (h : UnitCubeSkewW2Infinity d) (j : Fin d)
    (r : ℝ≥0∞) :
    MemLp (fun x => matWeakDiv (unitCubeDerivData h) x j) r
      (normalizedCubeMeasure (originCube d 0)) := by
  classical
  have : MemLp (fun x => ∑ i : Fin d, h.firstDeriv x (basisVec i) i j) r
      (normalizedCubeMeasure (originCube d 0)) :=
    memLp_finsetSum (s := Finset.univ)
      (f := fun i => fun x => h.firstDeriv x (basisVec i) i j)
      fun i _ => memLp_firstDeriv_entry h i i j r
  simpa [matWeakDiv_unitCubeDerivData_apply] using this

theorem memLp_matWeakDiv (h : UnitCubeSkewW2Infinity d) (r : ℝ≥0∞) :
    MemLp (matWeakDiv (unitCubeDerivData h)) r
      (normalizedCubeMeasure (originCube d 0)) :=
  memLp_vec_of_components fun j => memLp_matWeakDiv_component h j r

theorem memLp_divRep_top (h : UnitCubeSkewW2Infinity d) :
    MemLp (divRep h) ∞ (normalizedCubeMeasure (originCube d 0)) :=
  (memLp_matWeakDiv h ∞).ae_eq (divRep_ae_eq h).symm

theorem ae_norm_matWeakDiv_le (h : UnitCubeSkewW2Infinity d) :
    ∀ᵐ x ∂ normalizedCubeMeasure (originCube d 0),
      ‖matWeakDiv (unitCubeDerivData h) x‖ ≤ (d : ℝ) * h.gradientW1Infinity := by
  classical
  have hg : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hall : ∀ᵐ x ∂ normalizedCubeMeasure (originCube d 0), ∀ k i j : Fin d,
      |h.firstDeriv x (basisVec k) i j| ≤ h.gradientW1Infinity := by
    rw [MeasureTheory.ae_all_iff]
    intro k
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact ae_normalizedCubeMeasure_of_ae_frozen_carrier
      (ae_abs_firstDeriv_le_gradientW1Infinity h k i j)
  filter_upwards [hall] with x hx
  have hB : (0 : ℝ) ≤ (d : ℝ) * h.gradientW1Infinity := by positivity
  rw [pi_norm_le_iff_of_nonneg hB]
  intro j
  rw [Real.norm_eq_abs, matWeakDiv_unitCubeDerivData_apply]
  calc |∑ i : Fin d, h.firstDeriv x (basisVec i) i j|
      ≤ ∑ i : Fin d, |h.firstDeriv x (basisVec i) i j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, h.gradientW1Infinity :=
        Finset.sum_le_sum fun i _ => hx i i j
    _ = (d : ℝ) * h.gradientW1Infinity := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem cubeLpNorm_infty_matWeakDiv_le (h : UnitCubeSkewW2Infinity d) :
    cubeLpNorm (originCube d 0) ∞ (matWeakDiv (unitCubeDerivData h)) ≤
      (d : ℝ) * h.gradientW1Infinity := by
  have hg : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  exact cubeLpNorm_infty_le_of_ae_bound (originCube d 0) _
    (by positivity) (ae_norm_matWeakDiv_le h)

theorem cubeLpNorm_infty_divRep_le (h : UnitCubeSkewW2Infinity d) :
    cubeLpNorm (originCube d 0) ∞ (divRep h) ≤ (d : ℝ) * h.gradientW1Infinity := by
  rw [cubeLpNorm_congr_ae (originCube d 0) ∞ (divRep_ae_eq h)]
  exact cubeLpNorm_infty_matWeakDiv_le h

/-! ## Elementary vector bookkeeping -/

theorem sqrt_vecNormSq_le_sqrt_card_mul_norm (w : Vec d) :
    Real.sqrt (vecNormSq w) ≤ Real.sqrt (d : ℝ) * ‖w‖ := by
  classical
  have hsum : vecNormSq w ≤ (d : ℝ) * ‖w‖ ^ 2 := by
    have hrw : vecNormSq w = ∑ i : Fin d, (w i) ^ 2 := by
      simp [vecNormSq, vecDot, sq]
    rw [hrw]
    calc (∑ i : Fin d, (w i) ^ 2) ≤ ∑ _i : Fin d, ‖w‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : |w i| ≤ ‖w‖ := by
            simpa [Real.norm_eq_abs] using norm_le_pi_norm w i
          nlinarith [abs_nonneg (w i), sq_abs (w i)]
      _ = (d : ℝ) * ‖w‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (vecNormSq w) ≤ Real.sqrt ((d : ℝ) * ‖w‖ ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * ‖w‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg w)]

/-! ## The two `u`-estimates -/

/-- The constant of the zero-trace `L²` estimate at the gauge exponent. -/
def zeroTraceValueConst (d : ℕ) [NeZero d] : ℝ :=
  (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d * (3 : ℝ) ^ ((d : ℝ) + 1) *
        (d : ℝ)) + 2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
    Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 / 16)))⁻¹)

theorem zeroTraceValueConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ zeroTraceValueConst d := by
  have h1 : (0 : ℝ) ≤ Legacy.cubeNeumannW22CalderonZygmundConstant d :=
    Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) + 1) :=
    Real.rpow_nonneg (by norm_num) _
  have h3 : (0 : ℝ) ≤
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 / 16)))⁻¹) :=
    Real.sqrt_nonneg _
  unfold zeroTraceValueConst
  positivity

/-- The zero-trace `L²` estimate at the gauge exponent `2t = 3/8`. -/
theorem cubeLpNorm_two_h10_originCube_le [NeZero d]
    (u : H10Function ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :
    cubeLpNorm (originCube d 0) (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x) ≤
      zeroTraceValueConst d *
        cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8)
          (fun x => u.toH1Function.grad x) := by
  have h :=
    Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_h10_le_grad_negativeBesovTwo
      (Q := originCube d 0) (t := (3 / 16 : ℝ)) (Ch03.publicH10ToCubeSet u)
      (by norm_num) (by norm_num)
  rw [Ch03.publicH10ToCubeSet_toH1Function_toFun,
    Ch03.publicH10ToCubeSet_toH1Function_grad,
    cubeBesovScaleWeight_originCube_zero, one_mul,
    show (2 : ℝ) * (3 / 16) = 3 / 8 by norm_num] at h
  unfold zeroTraceValueConst
  exact h

/-! ## The Term BC field -/

/-- The Term BC field `x ↦ u(x) (∇·h)(x)`. -/
def termBCField (h : UnitCubeSkewW2Infinity d)
    (u : H10Function ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :
    Vec d → Vec d :=
  fun x => u.toH1Function.toFun x • matWeakDiv (unitCubeDerivData h) x

theorem memLp_u_two [NeZero d]
    (u : H10Function ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :
    MemLp (fun x => u.toH1Function.toFun x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d 0)) :=
  H1Function.memL2_normalizedCubeMeasure u.toH1Function

theorem memLp_termBCField_two [NeZero d] (h : UnitCubeSkewW2Infinity d)
    (u : H10Function ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :
    MemLp (termBCField h u) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d 0)) :=
  MemLp.smul (memLp_u_two u) (memLp_matWeakDiv h ∞)

/-- The finite-depth Besov product estimate for the Term BC field. -/
theorem cubeBesovPositiveVectorPartialSeminormTwo_termBCField_le [NeZero d]
    (h : UnitCubeSkewW2Infinity d)
    (u : H10Function ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (N : ℕ) :
    cubeBesovPositiveVectorPartialSeminormTwo (originCube d 0) (3 / 8) N
        (termBCField h u) ≤
      besovMultConst (3 / 8) *
        ((d : ℝ) ^ 2 * h.gradientW1Infinity *
            cubeLpNorm (originCube d 0) (2 : ℝ≥0∞)
              (fun x => u.toH1Function.toFun x) +
          (d : ℝ) * h.gradientW1Infinity *
            cubeBesovPositiveScalarPartialSeminormTwo (originCube d 0) (3 / 8) N
              (fun x => u.toH1Function.toFun x)) := by
  classical
  have hg : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hB : (0 : ℝ) ≤ (d : ℝ) ^ 2 * h.gradientW1Infinity := by positivity
  have hmain :=
    cubeBesovPositiveVectorPartialSeminormTwo_scalar_smul_le_besovMult
      (originCube d 0) (3 / 8) N (fun x => u.toH1Function.toFun x) (divRep h)
      hB (by norm_num) (memLp_u_two u) (memLp_divRep_top h)
      (fun x _ y _ => divRep_lipschitz h x y)
  have hcongr :
      cubeBesovPositiveVectorPartialSeminormTwo (originCube d 0) (3 / 8) N
          (fun x => u.toH1Function.toFun x • divRep h x) =
        cubeBesovPositiveVectorPartialSeminormTwo (originCube d 0) (3 / 8) N
          (termBCField h u) := by
    refine cubeBesovPositiveVectorPartialSeminormTwo_congr_ae (originCube d 0)
      (3 / 8) N ?_
    filter_upwards [divRep_ae_eq h] with x hx
    simp [termBCField, hx]
  rw [hcongr, cubeScaleFactor_originCube_zero, one_mul] at hmain
  refine hmain.trans ?_
  have hmult : (0 : ℝ) ≤ besovMultConst (3 / 8) :=
    (besovMultConst_pos (s := (3 / 8 : ℝ)) (by norm_num)).le
  refine mul_le_mul_of_nonneg_left ?_ hmult
  refine add_le_add le_rfl ?_
  refine mul_le_mul_of_nonneg_right (cubeLpNorm_infty_divRep_le h) ?_
  exact Real.sqrt_nonneg _

/-! ## The Term BC budget -/

/-- The explicit Term B constant. -/
def termBCBesovConst (d : ℕ) [NeZero d] : ℝ :=
  (Real.sqrt (d : ℝ) * (d : ℝ) * zeroTraceValueConst d +
      besovMultConst (3 / 8) *
        ((d : ℝ) ^ 2 * zeroTraceValueConst d + (d : ℝ) * depthDowngradeConst d)) *
    gradSplitConst

theorem depthDowngradeConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ depthDowngradeConst d := by
  have hg : (0 : ℝ) ≤ sensitivityGapConst := sensitivityGapConst_nonneg
  have hp : (0 : ℝ) ≤ Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) :=
    Ch01.Legacy.fullVectorPoincareConstant_nonneg _
  have hr : (0 : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) + 1) := Real.rpow_nonneg (by norm_num) _
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold depthDowngradeConst
  positivity

theorem termBCBesovConst_nonneg (d : ℕ) [NeZero d] : 0 ≤ termBCBesovConst d := by
  have h1 : (0 : ℝ) ≤ zeroTraceValueConst d := zeroTraceValueConst_nonneg d
  have h2 : (0 : ℝ) ≤ besovMultConst (3 / 8) :=
    (besovMultConst_pos (s := (3 / 8 : ℝ)) (by norm_num)).le
  have h3 : (0 : ℝ) ≤ depthDowngradeConst d := depthDowngradeConst_nonneg d
  have h4 : (0 : ℝ) ≤ gradSplitConst := gradSplitConst_nonneg
  have h5 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have h6 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold termBCBesovConst
  positivity

/-- **The Term BC positive Besov budget.** -/
theorem scaleNormalizedPositiveBesovVectorNormTwo_termBCField_le [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (p q : Vec d)
    {vAdj : Solution (cubeDomain (originCube d 0)) a.transpose}
    {v : Solution (cubeDomain (originCube d 0)) a}
    (hvAdj : IsResponseMaximizer (cubeDomain (originCube d 0)) a.transpose p (-q)
      vAdj)
    (hv : IsResponseMaximizer (cubeDomain (originCube d 0)) a p q v)
    (u : H10Function ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (hu : ∀ᵐ x ∂ volumeMeasureOn
        ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      u.toH1Function.grad x =
        (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x) + p) :
    Ch03.scaleNormalizedPositiveBesovVectorNormTwo (originCube d 0) (3 / 8)
        (termBCField h u) ≤
      termBCBesovConst d * h.gradientW1Infinity *
        (Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
          (Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) +
            Real.sqrt |vecDot p q|)) := by
  classical
  have hg : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  set X : ℝ := Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
    (Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) +
      Real.sqrt |vecDot p q|) with hX
  have hXnn : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  set S : ℝ := cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8)
    (fun x => u.toH1Function.grad x) with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    unfold cubeBesovNegativeVectorSeminormTwo
    refine le_trans (cubeBesovNegativeVectorPartialSeminormTwo_nonneg
      (originCube d 0) (3 / 8) 0 (fun x => u.toH1Function.grad x)) ?_
    exact le_csSup (bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad
      (originCube d 0) u.toH1Function) (Set.mem_range_self 0)
  have hgrad : S ≤ gradSplitConst * X :=
    cubeBesovNegativeVectorSeminormTwo_witnessGrad_le a p q hvAdj hv u hu
  -- the `L²` and positive-seminorm estimates for `u`
  have hL2 : cubeLpNorm (originCube d 0) (2 : ℝ≥0∞)
      (fun x => u.toH1Function.toFun x) ≤ zeroTraceValueConst d * S :=
    cubeLpNorm_two_h10_originCube_le u
  have hBdd := bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad
    (originCube d 0) u.toH1Function
  have hPos : ∀ N : ℕ,
      cubeBesovPositiveScalarPartialSeminormTwo (originCube d 0) (3 / 8) N
        (fun x => u.toH1Function.toFun x) ≤ depthDowngradeConst d * S := fun N =>
    cubeBesovPositiveScalarPartialSeminormTwo_h1_originCube_le N u.toH1Function hBdd
  -- the mean term
  have hmean : Real.sqrt (vecNormSq (cubeAverageVec (originCube d 0)
      (termBCField h u))) ≤
      Real.sqrt (d : ℝ) * ((d : ℝ) * h.gradientW1Infinity) *
        (zeroTraceValueConst d * S) := by
    refine (sqrt_vecNormSq_le_sqrt_card_mul_norm _).trans ?_
    have hnorm := norm_cubeAverageVec_scalar_smul_le_cubeLpNorm_infty_mul_cubeLpNorm_two
      (originCube d 0) (fun x => u.toH1Function.toFun x)
      (matWeakDiv (unitCubeDerivData h)) (memLp_u_two u) (memLp_matWeakDiv h ∞)
    have hstep : ‖cubeAverageVec (originCube d 0) (termBCField h u)‖ ≤
        ((d : ℝ) * h.gradientW1Infinity) * (zeroTraceValueConst d * S) := by
      refine hnorm.trans ?_
      exact mul_le_mul (cubeLpNorm_infty_matWeakDiv_le h) hL2
        (cubeLpNorm_nonneg _ _ _) (by positivity)
    calc Real.sqrt (d : ℝ) * ‖cubeAverageVec (originCube d 0) (termBCField h u)‖
        ≤ Real.sqrt (d : ℝ) *
            (((d : ℝ) * h.gradientW1Infinity) * (zeroTraceValueConst d * S)) :=
          mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _)
      _ = Real.sqrt (d : ℝ) * ((d : ℝ) * h.gradientW1Infinity) *
            (zeroTraceValueConst d * S) := by ring
  -- the seminorm term
  have hmult : (0 : ℝ) ≤ besovMultConst (3 / 8) :=
    (besovMultConst_pos (s := (3 / 8 : ℝ)) (by norm_num)).le
  have hsemi : cubeBesovPositiveVectorSeminormTwo (originCube d 0) (3 / 8)
      (termBCField h u) ≤
      besovMultConst (3 / 8) *
        ((d : ℝ) ^ 2 * h.gradientW1Infinity * (zeroTraceValueConst d * S) +
          (d : ℝ) * h.gradientW1Infinity * (depthDowngradeConst d * S)) := by
    refine cubeBesovPositiveVectorSeminormTwo_le_of_partialBound _ _ _ fun N => ?_
    refine (cubeBesovPositiveVectorPartialSeminormTwo_termBCField_le h u N).trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hmult
    · exact mul_le_mul_of_nonneg_left hL2 (by positivity)
    · exact mul_le_mul_of_nonneg_left (hPos N) (by positivity)
  -- assembly
  have hsum :
      Ch03.scaleNormalizedPositiveBesovVectorNormTwo (originCube d 0) (3 / 8)
          (termBCField h u) ≤
        Real.sqrt (d : ℝ) * ((d : ℝ) * h.gradientW1Infinity) *
            (zeroTraceValueConst d * S) +
          besovMultConst (3 / 8) *
            ((d : ℝ) ^ 2 * h.gradientW1Infinity * (zeroTraceValueConst d * S) +
              (d : ℝ) * h.gradientW1Infinity * (depthDowngradeConst d * S)) := by
    unfold Ch03.scaleNormalizedPositiveBesovVectorNormTwo
    exact add_le_add hmean hsemi
  refine hsum.trans ?_
  have h1 : (0 : ℝ) ≤ zeroTraceValueConst d := zeroTraceValueConst_nonneg d
  have h3 : (0 : ℝ) ≤ depthDowngradeConst d := depthDowngradeConst_nonneg d
  have hcoef : (0 : ℝ) ≤
      Real.sqrt (d : ℝ) * (d : ℝ) * zeroTraceValueConst d +
        besovMultConst (3 / 8) *
          ((d : ℝ) ^ 2 * zeroTraceValueConst d +
            (d : ℝ) * depthDowngradeConst d) := by
    have h4 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have h5 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    positivity
  calc
    Real.sqrt (d : ℝ) * ((d : ℝ) * h.gradientW1Infinity) *
          (zeroTraceValueConst d * S) +
        besovMultConst (3 / 8) *
          ((d : ℝ) ^ 2 * h.gradientW1Infinity * (zeroTraceValueConst d * S) +
            (d : ℝ) * h.gradientW1Infinity * (depthDowngradeConst d * S))
        = (Real.sqrt (d : ℝ) * (d : ℝ) * zeroTraceValueConst d +
              besovMultConst (3 / 8) *
                ((d : ℝ) ^ 2 * zeroTraceValueConst d +
                  (d : ℝ) * depthDowngradeConst d)) *
            h.gradientW1Infinity * S := by ring
    _ ≤ (Real.sqrt (d : ℝ) * (d : ℝ) * zeroTraceValueConst d +
            besovMultConst (3 / 8) *
              ((d : ℝ) ^ 2 * zeroTraceValueConst d +
                (d : ℝ) * depthDowngradeConst d)) *
          h.gradientW1Infinity * (gradSplitConst * X) :=
        mul_le_mul_of_nonneg_left hgrad (mul_nonneg hcoef hg)
    _ = termBCBesovConst d * h.gradientW1Infinity * X := by
        unfold termBCBesovConst; ring

/-- **The Term B regularity package.** -/
theorem forceBesovRegularity_termBCField [NeZero d] (h : UnitCubeSkewW2Infinity d)
    (u : H10Function ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :
    Ch03.ForceBesovRegularity (originCube d 0) (3 / 8) (termBCField h u) where
  memLp := memLp_termBCField_two h u
  partialSeminorms_bddAbove := by
    classical
    have hg : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
    have hBdd := bddAbove_cubeBesovNegativeVectorPartialSeminormTwo_h1Grad
      (originCube d 0) u.toH1Function
    refine ⟨besovMultConst (3 / 8) *
      ((d : ℝ) ^ 2 * h.gradientW1Infinity *
          cubeLpNorm (originCube d 0) (2 : ℝ≥0∞)
            (fun x => u.toH1Function.toFun x) +
        (d : ℝ) * h.gradientW1Infinity *
          (depthDowngradeConst d *
            cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8)
              (fun x => u.toH1Function.grad x))), ?_⟩
    rintro _ ⟨N, rfl⟩
    refine (cubeBesovPositiveVectorPartialSeminormTwo_termBCField_le h u N).trans ?_
    have hmult : (0 : ℝ) ≤ besovMultConst (3 / 8) :=
      (besovMultConst_pos (s := (3 / 8 : ℝ)) (by norm_num)).le
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hmult
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact cubeBesovPositiveScalarPartialSeminormTwo_h1_originCube_le N
      u.toH1Function hBdd

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
