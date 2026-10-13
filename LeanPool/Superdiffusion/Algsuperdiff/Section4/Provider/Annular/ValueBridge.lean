/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional.ValueLipschitz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseCentre
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.GradNormalization
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.LatticeCover
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ResponseTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ErrorAtoms

/-!
# ValueBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `valueL2` slot: the frozen unit-cube `L²` gauge read on `z + cu_n`

ABK26, Section 4.1.  The second term of `e.ugly.estimate.for.J.pre` carries

```
sigmabar_{n-2}^{-2} || k_L - (k_L - k_m)_{cu_m} - k_{n-2} ||^2_{L^2(z + cu_n)} ,
```

while the cited unit-cube lemma `l.J.sensitivity.no.conditions` carries the
frozen `UnitCubeSkewW2Infinity.valueL2` of the perturbation on `cu_0`.  As with
the error, the response and the gradient slots, the change of variables is
performed silently; this module proves the value half.

## The split

`k_L - (k_L - k_m)_{cu_m} - k_{n-2} = (k_m - k_{n-2}) + (k_L - k_m - (k_L -
k_m)_{cu_m})`, and the manuscript bounds the second bracket "by the Poincare
inequality".  Its own display makes the reading unambiguous: the right-hand
side is `3^{2m} || grad (k_L - k_m) ||^2_{L^infinity(cu_m)}`, i.e. the
**mean-value** bound on the big cube `cu_m`, not an `L^2` Poincare inequality
on `z + cu_n` (an `L^2` Poincare on `cu_m` cannot be restricted to `z + cu_n`
without a volume factor `3^{d(m-n)/2}`, which the display does not carry).
What is proved here is that mean-value bound, at the explicit constant `d^3`.

## What is re-derived, and why

`ApproximateRecurrence.PrincipalResponseCentre` proves the same mean-value
estimate, but (i) file-privately and (ii) only at the *same* cube for the
average, the supremum and the gauge.  Here the average is over `cu_m`, the
supremum over `z + cu_n`, and the gauge over `cu_m`, so the statement is a
genuinely different one and the proof is written fresh; the shared elementary
steps (the entrywise/Euclidean norm comparisons, the sup-norm diameter of a
triadic cube, the average-against-a-value bound on the open cube) are
re-derived because they are unreachable.  Its public constant `centeringConst`
is reused unchanged.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open Algsuperdiff.Section24.UnitCubeSkewW2Infinity
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the frozen `L²` carrier is a probability space -/

/-- The frozen `valueL2` carrier is a finite measure. -/
private theorem isFiniteMeasure_unitCubeCarrier (d : ℕ) :
    IsFiniteMeasure
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) := by
  have h : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d 0))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, volume_openCubeSet_eq_volume_cubeSet]
    exact volume_cubeSet_lt_top (originCube d 0)
  exact h

/-- **The frozen `valueL2` carrier is a probability space.**  Hence the frozen
`valueL2` *is* the manuscript's volume-normalized `L^2` norm on `cu_0`. -/
theorem measureReal_univ_unitCubeCarrier (d : ℕ) :
    ((volumeMeasureOn
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) Set.univ).toReal = 1 := by
  show ((volume.restrict (openCubeSet (originCube d 0))) Set.univ).toReal = 1
  rw [Measure.restrict_apply_univ, volume_openCubeSet_eq_volume_cubeSet,
    volume_cubeSet_toReal, cubeVolume_eq_pow_scale]
  show ((3 : ℝ) ^ (0 : ℤ)) ^ d = 1
  rw [zpow_zero, one_pow]

/-- The frozen `L²` value norm is nonnegative: it is an `ENNReal.toReal`. -/
theorem valueL2_nonneg (h : UnitCubeSkewW2Infinity d) : 0 ≤ h.valueL2 :=
  ENNReal.toReal_nonneg

/-- **A uniform bound on the value field bounds the frozen `L²` gauge.**  On a
probability space the `L²` norm is below the `L^infinity` norm; the hypothesis
is the almost-everywhere form, which is what the frozen carrier supports. -/
theorem valueL2_le_of_ae_bound (h : UnitCubeSkewW2Infinity d) {B : ℝ} (hB : 0 ≤ B)
    (hbd : ∀ᵐ x ∂(volumeMeasureOn
        ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))),
      matrixNorm (h.toLInfSkewMatrixFieldOn.1.1 x) ≤ B) :
    h.valueL2 ≤ B := by
  let := isFiniteMeasure_unitCubeCarrier d
  have hsq : h.valueL2 ^ 2 ≤ B ^ 2 := by
    rw [valueL2_sq_eq_integral]
    have hle : ∫ x, matrixNormField h x ^ 2
          ∂(volumeMeasureOn
            ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) ≤
        ∫ _x, B ^ 2
          ∂(volumeMeasureOn
            ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun x => by positivity) (integrable_const _) ?_
      filter_upwards [hbd] with x hx
      exact pow_le_pow_left₀ (matrixNormField_nonneg h x) hx 2
    rw [integral_const, smul_eq_mul, measureReal_def,
      measureReal_univ_unitCubeCarrier d, one_mul] at hle
    exact hle
  by_contra hcon
  push Not at hcon
  have hlt : B ^ 2 < h.valueL2 ^ 2 := by
    have := pow_lt_pow_left₀ hcon hB (n := 2) (by norm_num)
    exact this
  linarith only [hsq, hlt]

/-! ## Part B -- elementary norm comparisons (re-derived; see the header) -/

/-- The ambient entrywise supremum norm of a matrix is below its Euclidean
matrix norm. -/
private theorem norm_mat_le_matrixNorm (A : Mat d) : ‖A‖ ≤ matrixNorm A := by
  rw [Matrix.norm_le_iff (matrixNorm_nonneg A), matrixNorm_eq_matrixOperatorNorm]
  intro i j
  rw [Real.norm_eq_abs]
  exact abs_entry_le_matrixOperatorNorm A i j

/-- The ambient operator norm of a matrix-valued derivative is below `d` times
the exact induced derivative norm. -/
private theorem norm_clm_le_card_mul_matrixDerivativeNorm
    (D : ShellField.MatrixDerivative d) :
    ‖D‖ ≤ (d : ℝ) * ShellField.matrixDerivativeNorm D := by
  refine (norm_le_sum_basisVec_apply D).trans ?_
  have hterm : ∀ k : Fin d,
      ‖D (basisVec k)‖ ≤ ShellField.matrixDerivativeNorm D := by
    intro k
    refine (norm_mat_le_matrixNorm (D (basisVec k))).trans ?_
    rw [matrixNorm_eq_matrixOperatorNorm]
    exact ShellField.matrixOperatorNorm_apply_le_matrixDerivativeNorm D _
      (vecNorm_basisVec_le_one k)
  calc ∑ k : Fin d, ‖D (basisVec k)‖
      ≤ ∑ _k : Fin d, ShellField.matrixDerivativeNorm D :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = (d : ℝ) * ShellField.matrixDerivativeNorm D := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The sup-norm diameter of an open origin cube is its side length. -/
private theorem norm_sub_le_of_mem_openCubeSet_originCube {m : ℤ} {x x' : Vec d}
    (hx : x ∈ openCubeSet (originCube d m))
    (hx' : x' ∈ openCubeSet (originCube d m)) :
    ‖x - x'‖ ≤ (3 : ℝ) ^ m := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  rw [pi_norm_le_iff_of_nonneg h3.le]
  intro i
  have h1 := mem_openCubeSet_originCube_iff.1 hx i
  have h2 := mem_openCubeSet_originCube_iff.1 hx' i
  have hval : (x - x') i = x i - x' i := rfl
  rw [Real.norm_eq_abs, hval, abs_le]
  constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]

/-- The cube average of an integrable scalar stays within a bound that is
assumed on the **open** cube only: the two realizations differ by a null set. -/
private theorem abs_cubeAverage_sub_le_of_openCubeSet (R : TriadicCube d)
    {g : Vec d → ℝ} {c eps : ℝ} (heps : 0 ≤ eps)
    (hg : IntegrableOn g (cubeSet R) volume)
    (hb : ∀ x ∈ openCubeSet R, |g x - c| ≤ eps) :
    |cubeAverage R g - c| ≤ eps := by
  classical
  have hmem : ∀ᵐ x ∂(volume.restrict (cubeSet R)), x ∈ openCubeSet R := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact ae_restrict_mem (measurableSet_openCubeSet R)
  have haeeq : (fun x : Vec d => if x ∈ openCubeSet R then g x else c)
      =ᵐ[volume.restrict (cubeSet R)] g := by
    filter_upwards [hmem] with x hx
    rw [ite_eq_left hx]
  have hint : IntegrableOn (fun x : Vec d => if x ∈ openCubeSet R then g x else c)
      (cubeSet R) volume := hg.congr haeeq.symm
  have havg : cubeAverage R (fun x : Vec d => if x ∈ openCubeSet R then g x else c)
      = cubeAverage R g := cubeAverage_eq_of_ae_eq_on_cubeSet haeeq
  rw [← havg]
  refine Provider.Stream.abs_cubeAverage_sub_le R hint ?_
  intro x _
  by_cases hxo : x ∈ openCubeSet R
  · rw [ite_eq_left hxo]
    exact hb x hxo
  · rw [ite_eq_right hxo, sub_self, abs_zero]
    exact heps

/-- Continuity of the entries of a shell field, and their integrability on a
triadic cube. -/
private theorem integrableOn_cubeSet_shell_entry (R : TriadicCube d)
    (g : ShellField d) (i j : Fin d) :
    IntegrableOn (fun x : Vec d => g x i j) (cubeSet R) volume := by
  have hcont : Continuous fun x : Vec d => g x i j := by
    have hmat : Continuous fun x : Vec d => g x := g.1.1.continuous
    exact (continuous_apply j).comp ((continuous_apply i).comp hmat)
  exact ((hcont.locallyIntegrable).integrableOn_isCompact
      (isCompact_closedBall (cubeCenter R) (cubeRadius R))).mono_set
    (cubeSet_subset_closedBall R)

/-- Subadditivity of the Chapter 2 Euclidean matrix norm. -/
private theorem matrixNorm_add_le (A B : Mat d) :
    matrixNorm (A + B) ≤ matrixNorm A + matrixNorm B := by
  rw [matrixNorm_eq_matrixOperatorNorm, matrixNorm_eq_matrixOperatorNorm,
    matrixNorm_eq_matrixOperatorNorm]
  have h := matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub (A + B) A
  rwa [add_sub_cancel_left] at h

/-! ## Part C -- the mean-value (centering) estimate on the origin cube -/

/-- **The mean-value estimate at the origin cube.**

For a frozen shell field `g` and any point `x` of the open cube `cu_m`,

```
| g(x) - (g)_{cu_m} |  <=  d^3 . 3^{2m} || grad g ||_{W^{1,infinity}(cu_m)} .
```

This is the manuscript's "Poincare inequality" step, in the `L^infinity`
reading its own right-hand side forces.  The supremum point `x` and the
averaging cube are decoupled, which is what the annular chain needs: there the
point runs over the small cube `z + cu_n` while the average is over `cu_m`. -/
theorem matrixNorm_sub_cubeAverageMat_originCube_le [NeZero d] (m : ℤ)
    (g : ShellField d) {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) :
    matrixNorm (g x - cubeAverageMat (originCube d m) fun y => g y) ≤
      centeringConst d *
        ((3 : ℝ) ^ (2 * m) * Support.shellW1InfGradNorm m g) := by
  classical
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hW0 : (0 : ℝ) ≤ Support.shellW1InfGradNorm m g :=
    Support.shellW1InfGradNorm_nonneg m g
  -- the derivative gauge on the cube, converted to the Section 4 normalization
  have hderiv : Provider.Stream.localCubeDerivNorm m g ≤
      (3 : ℝ) ^ m * Support.shellW1InfGradNorm m g := by
    have hleg := Support.three_zpow_mul_localCubeDerivNorm_le_shellW1InfGradNorm m g
    have hmul := mul_le_mul_of_nonneg_left hleg h3.le
    rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), add_neg_cancel,
      zpow_zero, one_mul] at hmul
    exact hmul
  -- the ambient operator bound on the derivative, on the open cube
  have hbound : ∀ w ∈ openCubeSet (originCube d m),
      ‖ShellField.deriv g w‖ ≤
        (d : ℝ) * ((3 : ℝ) ^ m * Support.shellW1InfGradNorm m g) := by
    intro w hw
    refine (norm_clm_le_card_mul_matrixDerivativeNorm (ShellField.deriv g w)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
    exact (Provider.Stream.matrixDerivativeNorm_deriv_le_localCubeDerivNorm m g hw).trans
      hderiv
  -- the mean value inequality on the convex open cube
  have hlip : ∀ y ∈ openCubeSet (originCube d m), ∀ y' ∈ openCubeSet (originCube d m),
      ‖g y - g y'‖ ≤ (d : ℝ) * ((3 : ℝ) ^ (2 * m) * Support.shellW1InfGradNorm m g) := by
    intro y hy y' hy'
    have hC0 : (0 : ℝ) ≤ (d : ℝ) * ((3 : ℝ) ^ m * Support.shellW1InfGradNorm m g) :=
      mul_nonneg (Nat.cast_nonneg d) (mul_nonneg h3.le hW0)
    have hmvt : ‖g y - g y'‖ ≤
        (d : ℝ) * ((3 : ℝ) ^ m * Support.shellW1InfGradNorm m g) * ‖y - y'‖ :=
      (convex_openCubeSet (originCube d m)).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := fun w : Vec d => g w) (f' := fun w => ShellField.deriv g w)
        (fun w _ => (g.hasFDerivAt w).hasFDerivWithinAt) hbound hy' hy
    refine hmvt.trans ?_
    have hdiam := norm_sub_le_of_mem_openCubeSet_originCube hy hy'
    have hstep := mul_le_mul_of_nonneg_left hdiam hC0
    refine hstep.trans (le_of_eq ?_)
    rw [two_mul, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  -- entrywise: the average is within the same bound
  have hentry : ∀ i j : Fin d,
      |g x i j - (cubeAverageMat (originCube d m) fun y => g y) i j| ≤
        (d : ℝ) * ((3 : ℝ) ^ (2 * m) * Support.shellW1InfGradNorm m g) := by
    intro i j
    have hcij : (cubeAverageMat (originCube d m) fun y => g y) i j =
        cubeAverage (originCube d m) fun y : Vec d => g y i j := rfl
    rw [hcij, abs_sub_comm]
    refine abs_cubeAverage_sub_le_of_openCubeSet (originCube d m)
      (mul_nonneg (Nat.cast_nonneg d) (mul_nonneg (by positivity) hW0))
      (integrableOn_cubeSet_shell_entry (originCube d m) g i j) ?_
    intro y hy
    have hstep : |g y i j - g x i j| ≤ ‖g y - g x‖ := by
      have hsup := Matrix.norm_entry_le_entrywise_sup_norm
        (A := g y - g x) (i := i) (j := j)
      rw [Real.norm_eq_abs] at hsup
      exact hsup
    exact hstep.trans (hlip y hy x hx)
  -- the Euclidean norm from the entrywise one
  have helt : ‖g x - cubeAverageMat (originCube d m) fun y => g y‖ ≤
      (d : ℝ) * ((3 : ℝ) ^ (2 * m) * Support.shellW1InfGradNorm m g) := by
    rw [Matrix.norm_le_iff
      (mul_nonneg (Nat.cast_nonneg d) (mul_nonneg (by positivity) hW0))]
    intro i j
    rw [Real.norm_eq_abs]
    exact hentry i j
  calc matrixNorm (g x - cubeAverageMat (originCube d m) fun y => g y)
      ≤ (d : ℝ) ^ 2 * ‖g x - cubeAverageMat (originCube d m) fun y => g y‖ :=
        matrixNorm_le_sq_mul_norm _
    _ ≤ (d : ℝ) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ (2 * m) * Support.shellW1InfGradNorm m g)) :=
        mul_le_mul_of_nonneg_left helt (by positivity)
    _ = centeringConst d *
          ((3 : ℝ) ^ (2 * m) * Support.shellW1InfGradNorm m g) := by
        rw [centeringConst]; ring

/-! ## Part D -- the manuscript's constant is the cube average -/

/-- `(k_L − k_m)_Q` is the cube average of the shell increment `k_L − k_m`. -/
theorem fluxIncrementAverage_eq_cubeAverageMat (M : ABKModel d) {L m : ℤ}
    (hml : m ≤ L) (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    Support.fluxIncrementAverage M L m Q omega =
      cubeAverageMat Q fun x => Provider.Stream.shellIncrement omega.1 m L x := by
  have hvol : (volume (openCubeSet Q)).toReal = cubeVolume Q := by
    rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
  ext i j
  show volumeAverage (openCubeSet Q)
      (fun x => Cutoff.coefficientCutoff M.nu L omega x i j -
        Cutoff.coefficientCutoff M.nu m omega x i j) =
    cubeAverage Q fun x : Vec d => Provider.Stream.shellIncrement omega.1 m L x i j
  have hfun : (fun x : Vec d => Cutoff.coefficientCutoff M.nu L omega x i j -
      Cutoff.coefficientCutoff M.nu m omega x i j) =
      fun x : Vec d => Provider.Stream.shellIncrement omega.1 m L x i j := by
    funext x
    have hx := Support.coefficientCutoff_sub_coefficientCutoff M L m omega x
    have hxij := congrFun (congrFun hx i) j
    rw [Provider.Stream.shellIncrement_apply_eq_cutoff_sub omega hml x]
    exact hxij
  rw [hfun, volumeAverage, cubeAverage, hvol,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]

/-! ## Part E -- the value field of the centered shell, read on `z + cu_n` -/

/-- Translation by the zero vector is the identity on shell fields. -/
theorem shellField_translate_zero (g : ShellField d) :
    ShellField.translate (0 : Vec d) g = g :=
  ShellField.ext fun x => by
    rw [ShellField.translate_apply, add_zero]

/-- **The frozen `L²` value gauge of the centered shell, bounded on `z + cu_n`.**

The shell is `h = k_L - C - k_{n-2}` at the lattice cube `⟨n, v⟩`, and the bound
is the manuscript's own split: the `L^infinity` norm of `k_m - k_{n-2}` on
`z + cu_n` plus the mean-value bound for `k_L - k_m - C` on `cu_m`.

`C` is free here; the instance at the manuscript's `(k_L - k_m)_{cu_m}` is
`valueL2_centeredShellUnitCube_fluxConst_le`. -/
theorem valueL2_centeredShellUnitCube_le [NeZero d] (M : ABKModel d) {n m L : ℤ}
    (hnm : n ≤ m) (hml : m ≤ L) (hle : n - 2 ≤ L) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) (omega : Cutoff.CutoffSample d)
    (hC : matTranspose (cubeAverageMat (originCube d m)
        fun y => Provider.Stream.shellIncrement omega.1 m L y) =
      -cubeAverageMat (originCube d m)
        fun y => Provider.Stream.shellIncrement omega.1 m L y) :
    (centeredShellUnitCube M (⟨n, v⟩ : TriadicCube d) hle omega
        (cubeAverageMat (originCube d m)
          fun y => Provider.Stream.shellIncrement omega.1 m L y) hC).valueL2 ≤
      Cutoff.localCubeControl n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 (n - 2) m))
        + centeringConst d *
          ((3 : ℝ) ^ (2 * m) *
            Support.shellW1InfGradNorm m
              (Provider.Stream.shellIncrement omega.1 m L)) := by
  classical
  set gA : ShellField d := Provider.Stream.shellIncrement omega.1 (n - 2) m with hgA
  set gB : ShellField d := Provider.Stream.shellIncrement omega.1 m L with hgB
  set Cbar : Mat d := cubeAverageMat (originCube d m) fun y => gB y with hCbar
  set z : Vec d := Support.triadicLatticePoint n v with hz
  have hnL : n - 2 ≤ m := by omega
  have hA0 : (0 : ℝ) ≤ Cutoff.localCubeControl n (ShellField.translate z gA) :=
    Cutoff.localCubeControl_nonneg n _
  have hB0 : (0 : ℝ) ≤ centeringConst d *
      ((3 : ℝ) ^ (2 * m) * Support.shellW1InfGradNorm m gB) := by
    have hcc : (0 : ℝ) ≤ centeringConst d := by
      rw [centeringConst]; positivity
    exact mul_nonneg hcc
      (mul_nonneg (by positivity) (Support.shellW1InfGradNorm_nonneg m gB))
  refine valueL2_le_of_ae_bound _ (by linarith only [hA0, hB0]) ?_
  filter_upwards [centeredShellField_toCoeffField_sub_ae_eq M
      (⟨n, v⟩ : TriadicCube d) hle omega Cbar hC,
    ae_restrict_mem (measurableSet_openCubeSet (originCube d 0))] with y hy hyopen
  -- the value field of the centered shell is a.e. the literal centered shell
  have hval : (centeredShellUnitCube M (⟨n, v⟩ : TriadicCube d) hle omega Cbar
      hC).toLInfSkewMatrixFieldOn.1.1 y =
      Provider.Stream.shellIncrement omega.1 (n - 2) L
          (((3 : ℝ) ^ (n : ℤ)) • y + z) - Cbar := by
    have hcb : cubeBasePoint (⟨n, v⟩ : TriadicCube d) = z := Support.cubeBasePoint_mk n v
    have hstep := hy
    rw [centeredShellField_value] at hstep
    rw [hcb] at hstep
    exact hstep
  rw [hval]
  -- the manuscript's split
  set x : Vec d := ((3 : ℝ) ^ (n : ℤ)) • y + z with hxdef
  have hxA : x ∈ openCubeSet (originCube d m) := by
    have hyn : ((3 : ℝ) ^ (n : ℤ)) • y ∈ openCubeSet (originCube d n) := by
      rw [openCubeSet_originCube_eq_smul_originCube_zero (d := d) n, Set.mem_smul_set]
      refine ⟨y, hyopen, ?_⟩
      rw [cubeScaleFactor_originCube]
    exact translate_openCubeSet_originCube_subset hnm hv hyn
  have hsplit : Provider.Stream.shellIncrement omega.1 (n - 2) L x - Cbar =
      gA x + (gB x - Cbar) := by
    rw [Provider.Stream.shellIncrement_apply_eq_cutoff_sub omega (by omega : n - 2 ≤ L),
      hgA, Provider.Stream.shellIncrement_apply_eq_cutoff_sub omega hnL,
      hgB, Provider.Stream.shellIncrement_apply_eq_cutoff_sub omega hml]
    abel
  rw [hsplit]
  refine le_trans (matrixNorm_add_le _ _) (add_le_add ?_ ?_)
  · -- the `L^infinity` leg on `z + cu_n`
    have hyn : ((3 : ℝ) ^ (n : ℤ)) • y ∈ openCubeSet (originCube d n) := by
      rw [openCubeSet_originCube_eq_smul_originCube_zero (d := d) n, Set.mem_smul_set]
      refine ⟨y, hyopen, ?_⟩
      rw [cubeScaleFactor_originCube]
    have hshift : (ShellField.translate z gA) (((3 : ℝ) ^ (n : ℤ)) • y) = gA x := by
      rw [ShellField.translate_apply]
    rw [matrixNorm_eq_matrixOperatorNorm, ← hshift]
    exact matrixOperatorNorm_le_localCubeControl_cubeSet n _
      (openCubeSet_subset_cubeSet (originCube d n) hyn)
  · exact matrixNorm_sub_cubeAverageMat_originCube_le m gB hxA

/-! ## Part F -- the instance at the manuscript's own constant -/

/-- The manuscript's centering constant `(k_L − k_m)_{cu_m}` is antisymmetric, in
the cube-average spelling this module uses. -/
theorem matTranspose_cubeAverageMat_shellIncrement (M : ABKModel d) {L m : ℤ}
    (hml : m ≤ L) (omega : Cutoff.CutoffSample d) :
    matTranspose (cubeAverageMat (originCube d m)
        fun y => Provider.Stream.shellIncrement omega.1 m L y) =
      -cubeAverageMat (originCube d m)
        fun y => Provider.Stream.shellIncrement omega.1 m L y := by
  rw [← fluxIncrementAverage_eq_cubeAverageMat M hml (originCube d m) omega]
  exact matTranspose_fluxIncrementAverage M L m (originCube d m) omega

/-- The frozen centered shell depends on its centering constant only through the
constant's value; the antisymmetry witness is proof-irrelevant. -/
private theorem centeredShellUnitCube_congr_const (M : ABKModel d) (Q : TriadicCube d)
    {lowScale highScale : ℤ} (hle : lowScale ≤ highScale)
    (omega : Cutoff.CutoffSample d) {C₁ C₂ : Mat d}
    (h₁ : matTranspose C₁ = -C₁) (h₂ : matTranspose C₂ = -C₂) (hC : C₁ = C₂) :
    centeredShellUnitCube M Q hle omega C₁ h₁ =
      centeredShellUnitCube M Q hle omega C₂ h₂ := by
  subst hC
  rfl

/-- **The `hH` slot of the ugly chain, at the lattice cube**.

`Ugly.poincareSplit` applied to the two legs of
`valueL2_centeredShellUnitCube_le`: the frozen `L²` gauge squared is at most
twice the squared `L^infinity` content of `k_m - k_{n-2}` on `z + cu_n` plus
twice the squared mean-value bound, at `Cp = d^3`. -/
theorem valueL2_sq_centeredShellUnitCube_le [NeZero d] (M : ABKModel d) {n m L : ℤ}
    (hnm : n ≤ m) (hml : m ≤ L) (hle : n - 2 ≤ L) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) (omega : Cutoff.CutoffSample d) :
    (centeredShellUnitCube M (⟨n, v⟩ : TriadicCube d) hle omega
        (Support.fluxIncrementAverage M L m (originCube d m) omega)
        (matTranspose_fluxIncrementAverage M L m (originCube d m)
          omega)).valueL2 ^ 2 ≤
      2 * (Cutoff.localCubeControl n
            (ShellField.translate (Support.triadicLatticePoint n v)
              (Provider.Stream.shellIncrement omega.1 (n - 2) m))) ^ 2
        + 2 * (centeringConst d *
            ((3 : ℝ) ^ (2 * m) *
              Support.shellW1InfGradNorm m
                (Provider.Stream.shellIncrement omega.1 m L))) ^ 2 := by
  have hCeq := fluxIncrementAverage_eq_cubeAverageMat M hml (originCube d m) omega
  have hkey := valueL2_centeredShellUnitCube_le M hnm hml hle hv omega
    (matTranspose_cubeAverageMat_shellIncrement M hml omega)
  have hBnn : (0 : ℝ) ≤ centeringConst d *
      ((3 : ℝ) ^ (2 * m) *
        Support.shellW1InfGradNorm m (Provider.Stream.shellIncrement omega.1 m L)) := by
    have hcc : (0 : ℝ) ≤ centeringConst d := by
      rw [centeringConst]; positivity
    exact mul_nonneg hcc (mul_nonneg (by positivity)
      (Support.shellW1InfGradNorm_nonneg m _))
  rw [centeredShellUnitCube_congr_const M (⟨n, v⟩ : TriadicCube d) hle omega
    (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)
    (matTranspose_cubeAverageMat_shellIncrement M hml omega) hCeq]
  exact poincareSplit (Cp := centeringConst d)
    (Y := (3 : ℝ) ^ (2 * m) *
      Support.shellW1InfGradNorm m (Provider.Stream.shellIncrement omega.1 m L))
    (valueL2_nonneg _) hBnn hkey le_rfl

end

end Algsuperdiff.Section4.Provider.Annular
