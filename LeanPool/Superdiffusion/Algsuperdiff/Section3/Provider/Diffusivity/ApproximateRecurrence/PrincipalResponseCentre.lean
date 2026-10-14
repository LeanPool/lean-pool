/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchActualShellSize
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementMassRepresentative
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfaces.AECongruence

/-!
# PrincipalResponseCentre

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the centering estimate for the fresh shell on the localization cube

Source displays in ABK26:

* the fresh shell `h := k_m - k_{m-h}` named;
* Step 3 of `l.approximate.recurrence.formula` (label), whose Young remainder
  is absorbed using `||h - (h)_{z+cu_n}||^2 <= Delta^2 shom_{m-h}
  lambda_{3/8,2}`;
* the gauge `3^{2n} ||grad (k_m - k_{m-h})||_{W^{1,infinity}(z+cu_n)}` of
  `e.good.local.events` (label; display), carried in this repository as
  `Provider.BadEvents.incrementOscGauge₂`.

## What this module supplies

`ApproximateRecurrence.PrincipalResponseSwitchActualShellSize` reduces the
shell-size hypothesis of the per-cube switch to the single inequality

```
hcentre :  ||h - (h)_{z+cu_n}||_{W^{1,infinity}}  <=  K . osc ,
```

which it carries as a binder with `K` free.  This module supplies that
inequality, with the explicit `K = d^3` recorded in `centeringConst`, and then
supplies the shell-size hypothesis with that binder discharged.

The estimate is elementary and is not an `L^2` Poincare inequality.  Three
elementary bridges are involved.

1. *Essential supremum from a pointwise bound.*  The frozen
   `UnitCubeSkewW2Infinity.w1Infinity` reads both of its fields through
   `eLpNorm ... ∞` on the literal open unit cube, so a bound holding at every
   point of that cube bounds it; this is `w1Infinity_shellFieldUnitCube_le`.
   Its gradient component is below the manuscript gauge with constant one, by
   the proved normalization `Provider.BadEvents.max_unitCubeDerivNorm_cube`,
   because a constant shift is invisible to `cubeOscGauge`.

2. *Mean value on the localization cube.*  A shell field is `C^2` and carries
   its own derivative, so Mathlib's mean value inequality applies verbatim on
   the convex open cube, whose sup-norm diameter is the side length `3^n`.
   Averaging the resulting bound over the cube against the constant `h(x)`
   gives the centering bound entrywise, and the entrywise bound is converted to
   the Euclidean matrix norm by the proved comparisons of
   `Section24.Sensitivity.Provider.DhBound.Lipschitz.MatrixNorms`.

3. *Rescaling.*  The manuscript's `(h)_{z+cu_n}` is
   `ApproximateRecurrence.freshShellCubeAverage`, an average of the
   **unrescaled** shell over `cubeSet R`, whereas the centered object lives at
   the rescaled unit cube.  The route taken here runs the mean value argument
   at the unrescaled cube `R` and transports the gradient bound through
   `Provider.BadEvents.max_unitCubeDerivNorm_cube` and the chain rule of
   `ShellField.spatialScale`; no change-of-variables formula for the cube
   average is used.

## The constant

`centeringConst d = d^3`.  One factor `d` comes from the comparison between the
ambient sup norm of `Vec d` and the frozen derivative norm
(`norm_le_sum_basisVec_apply` over the `d` coordinate directions), and the
remaining `d^2` from `matrixNorm_le_sq_mul_norm`.  The constant enters the
consumer only through `shellSizeThreshold M Ccg (centeringConst d) lowScale`,
whose comparison with `S` remains a binder about the data of the recurrence.

## Carriers

* the localization cube is a free `TriadicCube d`; no literal buffer constant
  of `e.recurrence.params` occurs;
* the two scales are free integers `lowScale <= highScale`;
* `cstar` does not occur in this module.

## Main definitions

* `centeringConst`: the explicit constant `d^3` of the centering estimate.

## Main results

* `w1Infinity_centeredShellUnitCube_le`: the centering estimate for the shell
  centered at any constant that is its own cube average.
* `w1Infinity_centeredFreshShellUnitCube_le`: the same at the manuscript's own
  constant `(h)_{z+cu_n}`.
* `shell_hypothesis_of_centeringConst_ae`: the shell-size hypothesis the
  per-cube switch consumes, obtained from
  `shell_hypothesis_of_centering_ae` at `K = centeringConst d` with its
  centering binder discharged.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Elementary comparisons between the entrywise and Euclidean matrix norms -/

/-- The ambient entrywise supremum norm of a matrix is below its Euclidean
matrix norm. -/
private theorem norm_mat_le_matrixNorm (A : Mat d) : ‖A‖ ≤ matrixNorm A := by
  rw [Matrix.norm_le_iff (matrixNorm_nonneg A), matrixNorm_eq_matrixOperatorNorm]
  intro i j
  rw [Real.norm_eq_abs]
  exact abs_entry_le_matrixOperatorNorm A i j

/-- The ambient operator norm of a matrix-valued derivative, from the sup norm
of `Vec d` to the entrywise norm of `Mat d`, is below `d` times the exact
induced derivative norm. -/
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

/-! ## The literal open cubes as metric balls -/

private theorem cubeCenter_originCube_eq_zero (m : ℤ) :
    cubeCenter (originCube d m) = (0 : Vec d) := by
  funext i
  simp [cubeCenter, originCube]

private theorem mem_openCubeSet_originCube_iff_norm_lt {m : ℤ} {y : Vec d} :
    y ∈ openCubeSet (originCube d m) ↔ ‖y‖ < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  rw [← ball_cubeCenter_eq_openCubeSet, Metric.mem_ball,
    cubeCenter_originCube_eq_zero, dist_zero_right, cubeRadius,
    cubeScaleFactor_originCube]

private theorem mem_openCubeSet_iff_norm_sub_lt (R : TriadicCube d) {x : Vec d} :
    x ∈ openCubeSet R ↔
      ‖x - cubeBasePoint R‖ < (1 / 2 : ℝ) * (3 : ℝ) ^ R.scale := by
  rw [← ball_cubeCenter_eq_openCubeSet, Metric.mem_ball, dist_eq_norm, cubeRadius]
  exact Iff.rfl

/-- The sup-norm diameter of the open localization cube is its side length. -/
private theorem norm_sub_le_of_mem_openCubeSet {R : TriadicCube d} {x x' : Vec d}
    (hx : x ∈ openCubeSet R) (hx' : x' ∈ openCubeSet R) :
    ‖x - x'‖ ≤ (3 : ℝ) ^ R.scale := by
  rw [mem_openCubeSet_iff_norm_sub_lt] at hx hx'
  have hsub : x - x' = (x - cubeBasePoint R) - (x' - cubeBasePoint R) := by abel
  rw [hsub]
  refine (norm_sub_le _ _).trans ?_
  linarith

/-! ## Averaging against a value taken on the open cube -/

/-- The cube average of an integrable scalar stays within a bound that is
assumed on the *open* cube only: the half-open and open forms of a triadic
cube differ by a null set. -/
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
    simp [hx]
  have hint : IntegrableOn (fun x : Vec d => if x ∈ openCubeSet R then g x else c)
      (cubeSet R) volume := hg.congr haeeq.symm
  have havg : cubeAverage R (fun x : Vec d => if x ∈ openCubeSet R then g x else c)
      = cubeAverage R g := cubeAverage_eq_of_ae_eq_on_cubeSet haeeq
  rw [← havg]
  refine abs_cubeAverage_sub_le R hint ?_
  intro x _
  by_cases hxo : x ∈ openCubeSet R
  · simpa [hxo] using hb x hxo
  · simpa [hxo] using heps

/-! ## Regularity of the entries of a shell field -/

/-- Extract a matrix entry as a continuous linear functional for the recurrence estimate. -/
def matEntryCLM (i j : Fin d) : Mat d →L[ℝ] ℝ :=
  ⟨{ toFun := fun A => A i j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl },
    LinearMap.continuous_of_finiteDimensional
      { toFun := fun A : Mat d => A i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }⟩

private theorem continuous_shell_entry (g : ShellField d) (i j : Fin d) :
    Continuous fun x : Vec d => g x i j :=
  (matEntryCLM i j).continuous.comp g.1.1.continuous

private theorem integrableOn_cubeSet_shell_entry (R : TriadicCube d)
    (g : ShellField d) (i j : Fin d) :
    IntegrableOn (fun x : Vec d => g x i j) (cubeSet R) volume :=
  (((continuous_shell_entry g i j).locallyIntegrable).integrableOn_isCompact
      (isCompact_closedBall (cubeCenter R) (cubeRadius R))).mono_set
    (cubeSet_subset_closedBall R)

/-! ## Bridge (i): a pointwise bound on the open unit cube -/

private theorem toReal_eLpNorm_le_of_bound {f : Vec d → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ openCubeSet (originCube d 0), ‖f x‖ ≤ C) :
    (eLpNorm f ∞
      (volumeMeasureOn
        ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))).toReal ≤ C := by
  exact Algsuperdiff.Section3.Provider.BadEvents.toReal_eLpNorm_unitCube_le hC hbound

/-- **Pointwise bounds on the literal open unit cube bound the frozen
`W^{1,infinity}` gauge.**

Both components of `UnitCubeSkewW2Infinity.w1Infinity` are essential suprema on
the open unit cube, so pointwise bounds on the stored derivative and on the
value transfer.

: this statement holds only under the propositions supplied by its binders
`hA`, `hB`, `hderiv` and `hval`.  It is a provider A, not a source-facing
frozen declaration. -/
private theorem w1Infinity_shellFieldUnitCube_le (g : ShellField d) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hderiv : ∀ y ∈ openCubeSet (originCube d 0),
      ShellField.matrixDerivativeNorm (ShellField.deriv g y) ≤ A)
    (hval : ∀ y ∈ openCubeSet (originCube d 0), matrixNorm (g y) ≤ B) :
    (shellFieldUnitCube g).w1Infinity ≤ max A B := by
  rw [UnitCubeSkewW2Infinity.w1Infinity]
  refine max_le_max ?_ ?_
  · refine toReal_eLpNorm_le_of_bound hA fun y hy => ?_
    have hfrozen : Algsuperdiff.Frozen.Section24.matrixDerivativeNorm
        ((shellFieldUnitCube g).firstDeriv y) =
        ShellField.matrixDerivativeNorm (ShellField.deriv g y) := by
      rw [shellFieldUnitCube_firstDeriv, frozen_matrixDerivativeNorm_eq]
    rw [Real.norm_eq_abs, hfrozen,
      abs_of_nonneg (ShellField.matrixDerivativeNorm_nonneg _)]
    exact hderiv y hy
  · refine toReal_eLpNorm_le_of_bound hB fun y hy => ?_
    rw [Real.norm_eq_abs, shellFieldUnitCube_value,
      abs_of_nonneg (matrixNorm_nonneg _)]
    exact hval y hy

/-! ## The rescaled shell field at a triadic cube -/

/-- The shell field on `z + square_j` transported to the unit cube by the
manuscript's map `y |-> z + 3^j y`. -/
def rescaledField (R : TriadicCube d) (g : ShellField d) : ShellField d :=
  ShellField.spatialScale ((3 : ℝ) ^ R.scale)
    (ShellField.translate (cubeBasePoint R) g)

private theorem cubeUnitCube_eq_shellFieldUnitCube (R : TriadicCube d)
    (g : ShellField d) :
    cubeUnitCube R g = shellFieldUnitCube (rescaledField R g) :=
  rfl

private theorem rescaledField_apply (R : TriadicCube d) (g : ShellField d)
    (y : Vec d) :
    rescaledField R g y = g (((3 : ℝ) ^ R.scale) • y + cubeBasePoint R) :=
  rfl

private theorem rescaledField_deriv (R : TriadicCube d) (g : ShellField d)
    (y : Vec d) :
    ShellField.deriv (rescaledField R g) y =
      ((3 : ℝ) ^ R.scale) •
        ShellField.deriv g (((3 : ℝ) ^ R.scale) • y + cubeBasePoint R) :=
  rfl

/-- The exact normalization of `Provider.BadEvents.max_unitCubeDerivNorm_cube`,
in the one-sided form used below. -/
private theorem unitCubeDerivNorm_rescaledField_le (R : TriadicCube d)
    (g : ShellField d) :
    ShellField.unitCubeDerivNorm (rescaledField R g) ≤ cubeOscGauge R g :=
  (le_max_right (ShellField.unitCubeSecondDerivNorm (rescaledField R g))
    (ShellField.unitCubeDerivNorm (rescaledField R g))).trans_eq
    (max_unitCubeDerivNorm_cube R g)

/-! ## The constant -/

/-- The explicit constant of the centering estimate: `d^3`.  One factor `d`
comes from the comparison between the ambient sup norm of `Vec d` and the exact
induced derivative norm, and the remaining `d^2` from
`matrixNorm_le_sq_mul_norm`. -/
def centeringConst (d : ℕ) : ℝ := (d : ℝ) ^ 3

private theorem centeringConst_nonneg : (0 : ℝ) ≤ centeringConst d := by
  rw [centeringConst]
  positivity

private theorem one_le_centeringConst [NeZero d] : (1 : ℝ) ≤ centeringConst d := by
  have hd : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  rw [centeringConst]
  exact one_le_pow₀ hd

/-! ## Bridges (ii) and (iii): the centering estimate -/

/-- **The centering estimate at the frozen `W^{1,infinity}` carrier.**

If the constant `c` subtracted from the shell field `g` is its own cube average
over the localization cube, then the rescaled centered field obeys

```
||g - c||_{W^{1,infinity}}  <=  d^3 . 3^{2j} ||grad g||_{W^{1,infinity}(z+square_j)} .
```

: this statement holds only under the propositions supplied by its binders --
`hc` (antisymmetry of the constant) and `hcavg` (the identification of the
constant with the cube average).  It is a provider A, not a source-facing
frozen declaration. -/
private theorem w1Infinity_cubeUnitCube_subConstShell_le [NeZero d]
    (R : TriadicCube d) (g : ShellField d) (c : Mat d) (hc : matTranspose c = -c)
    (hcavg : c = cubeAverageMat R fun x => g x) :
    (cubeUnitCube R (subConstShell c hc g)).w1Infinity ≤
      centeringConst d * cubeOscGauge R g := by
  classical
  have hs0 : (0 : ℝ) < (3 : ℝ) ^ R.scale := zpow_pos (by norm_num) _
  have hsne : ((3 : ℝ) ^ R.scale) ≠ 0 := ne_of_gt hs0
  have hosc0 : (0 : ℝ) ≤ cubeOscGauge R g := cubeOscGauge_nonneg R g
  -- the gradient component at the rescaled unit cube
  have hgrad : ∀ y ∈ openCubeSet (originCube d 0),
      ShellField.matrixDerivativeNorm
        (ShellField.deriv (rescaledField R (subConstShell c hc g)) y) ≤
      cubeOscGauge R g := by
    intro y hy
    refine (matrixDerivativeNorm_deriv_le_unitCubeDerivNorm _ hy).trans ?_
    exact (unitCubeDerivNorm_rescaledField_le R (subConstShell c hc g)).trans_eq
      (cubeOscGauge_subConstShell R c hc g)
  -- the gradient bound at the unrescaled cube
  have hgradR : ∀ x ∈ openCubeSet R,
      ShellField.matrixDerivativeNorm (ShellField.deriv g x) ≤
        ((3 : ℝ) ^ R.scale)⁻¹ * cubeOscGauge R g := by
    intro x hx
    have hx' : ‖x - cubeBasePoint R‖ < (1 / 2 : ℝ) * (3 : ℝ) ^ R.scale :=
      (mem_openCubeSet_iff_norm_sub_lt R).1 hx
    have hy : ((3 : ℝ) ^ R.scale)⁻¹ • (x - cubeBasePoint R) ∈
        openCubeSet (originCube d 0) := by
      rw [mem_openCubeSet_originCube_iff_norm_lt, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hs0)]
      calc ((3 : ℝ) ^ R.scale)⁻¹ * ‖x - cubeBasePoint R‖
          < ((3 : ℝ) ^ R.scale)⁻¹ * ((1 / 2 : ℝ) * (3 : ℝ) ^ R.scale) :=
            mul_lt_mul_of_pos_left hx' (inv_pos.2 hs0)
        _ = (1 / 2 : ℝ) * (3 : ℝ) ^ (0 : ℤ) := by
            rw [zpow_zero]
            field_simp
    have hcancel : ((3 : ℝ) ^ R.scale) •
        (((3 : ℝ) ^ R.scale)⁻¹ • (x - cubeBasePoint R)) + cubeBasePoint R = x := by
      rw [smul_smul, mul_inv_cancel₀ hsne, one_smul]
      abel
    have hpt := hgrad _ hy
    rw [rescaledField_deriv, hcancel, subConstShell_deriv,
      matrixDerivativeNorm_smul_of_nonneg hs0.le] at hpt
    rw [le_inv_mul_iff₀ hs0]
    exact hpt
  -- the mean value bound on the convex open cube
  have hlip : ∀ x ∈ openCubeSet R, ∀ x' ∈ openCubeSet R,
      ‖g x - g x'‖ ≤ (d : ℝ) * cubeOscGauge R g := by
    intro x hx x' hx'
    have hbound : ∀ w ∈ openCubeSet R,
        ‖ShellField.deriv g w‖ ≤
          (d : ℝ) * (((3 : ℝ) ^ R.scale)⁻¹ * cubeOscGauge R g) := by
      intro w hw
      refine (norm_clm_le_card_mul_matrixDerivativeNorm (ShellField.deriv g w)).trans ?_
      exact mul_le_mul_of_nonneg_left (hgradR w hw) (Nat.cast_nonneg d)
    have hmvt : ‖g x - g x'‖ ≤
        (d : ℝ) * (((3 : ℝ) ^ R.scale)⁻¹ * cubeOscGauge R g) * ‖x - x'‖ :=
      (convex_openCubeSet R).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := fun w : Vec d => g w) (f' := fun w => ShellField.deriv g w)
        (fun w _ => (g.hasFDerivAt w).hasFDerivWithinAt) hbound hx' hx
    have hC0 : (0 : ℝ) ≤ (d : ℝ) * (((3 : ℝ) ^ R.scale)⁻¹ * cubeOscGauge R g) :=
      mul_nonneg (Nat.cast_nonneg d) (mul_nonneg (inv_nonneg.2 hs0.le) hosc0)
    refine hmvt.trans ?_
    calc (d : ℝ) * (((3 : ℝ) ^ R.scale)⁻¹ * cubeOscGauge R g) * ‖x - x'‖
        ≤ (d : ℝ) * (((3 : ℝ) ^ R.scale)⁻¹ * cubeOscGauge R g) * (3 : ℝ) ^ R.scale :=
          mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_openCubeSet hx hx') hC0
      _ = (d : ℝ) * cubeOscGauge R g := by field_simp
  -- the value component at the rescaled unit cube
  have hvalue : ∀ y ∈ openCubeSet (originCube d 0),
      matrixNorm (rescaledField R (subConstShell c hc g) y) ≤
        centeringConst d * cubeOscGauge R g := by
    intro y hy
    have hy' : ‖y‖ < (1 / 2 : ℝ) := by
      have := mem_openCubeSet_originCube_iff_norm_lt.1 hy
      simpa using this
    have hx₀ : ((3 : ℝ) ^ R.scale) • y + cubeBasePoint R ∈ openCubeSet R := by
      rw [mem_openCubeSet_iff_norm_sub_lt, add_sub_cancel_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hs0]
      calc (3 : ℝ) ^ R.scale * ‖y‖ < (3 : ℝ) ^ R.scale * (1 / 2 : ℝ) :=
            mul_lt_mul_of_pos_left hy' hs0
        _ = (1 / 2 : ℝ) * (3 : ℝ) ^ R.scale := by ring
    have hentry : ∀ i j : Fin d,
        |g (((3 : ℝ) ^ R.scale) • y + cubeBasePoint R) i j - c i j| ≤
          (d : ℝ) * cubeOscGauge R g := by
      intro i j
      have hcij : c i j = cubeAverage R fun x : Vec d => g x i j := by
        rw [hcavg]
        rfl
      rw [hcij, abs_sub_comm]
      refine abs_cubeAverage_sub_le_of_openCubeSet R
        (mul_nonneg (Nat.cast_nonneg d) hosc0)
        (integrableOn_cubeSet_shell_entry R g i j) ?_
      intro x hx
      have hstep : |g x i j - g (((3 : ℝ) ^ R.scale) • y + cubeBasePoint R) i j| ≤
          ‖g x - g (((3 : ℝ) ^ R.scale) • y + cubeBasePoint R)‖ := by
        have hsup := Matrix.norm_entry_le_entrywise_sup_norm
          (A := g x - g (((3 : ℝ) ^ R.scale) • y + cubeBasePoint R)) (i := i) (j := j)
        simpa [Real.norm_eq_abs] using hsup
      exact hstep.trans (hlip x hx _ hx₀)
    have helt : ‖g (((3 : ℝ) ^ R.scale) • y + cubeBasePoint R) - c‖ ≤
        (d : ℝ) * cubeOscGauge R g := by
      rw [Matrix.norm_le_iff (mul_nonneg (Nat.cast_nonneg d) hosc0)]
      intro i j
      simpa [Real.norm_eq_abs] using hentry i j
    have hvaly : rescaledField R (subConstShell c hc g) y =
        g (((3 : ℝ) ^ R.scale) • y + cubeBasePoint R) - c := by
      rw [rescaledField_apply, subConstShell_apply]
    rw [hvaly]
    calc matrixNorm (g (((3 : ℝ) ^ R.scale) • y + cubeBasePoint R) - c)
        ≤ (d : ℝ) ^ 2 * ‖g (((3 : ℝ) ^ R.scale) • y + cubeBasePoint R) - c‖ :=
          matrixNorm_le_sq_mul_norm _
      _ ≤ (d : ℝ) ^ 2 * ((d : ℝ) * cubeOscGauge R g) :=
          mul_le_mul_of_nonneg_left helt (by positivity)
      _ = centeringConst d * cubeOscGauge R g := by
          rw [centeringConst]; ring
  rw [cubeUnitCube_eq_shellFieldUnitCube]
  refine (w1Infinity_shellFieldUnitCube_le (rescaledField R (subConstShell c hc g))
    hosc0 (mul_nonneg centeringConst_nonneg hosc0) hgrad hvalue).trans ?_
  exact max_le (le_mul_of_one_le_left hosc0 one_le_centeringConst) le_rfl

/-- **The centering estimate for the centered rescaled fresh shell.**

: this statement holds only under the propositions supplied by its binders --
`hle`, `hskew`, and `hbaravg`, the identification of the centering constant
with the cube average of the fresh shell.  It is a provider A, not a
source-facing frozen declaration. -/
private theorem w1Infinity_centeredShellUnitCube_le [NeZero d] (M : ABKModel d)
    (R : TriadicCube d) {lowScale highScale : ℤ} (hle : lowScale ≤ highScale)
    (omega : CutoffSample d) (hbar : Mat d) (hskew : matTranspose hbar = -hbar)
    (hbaravg : hbar =
      cubeAverageMat R fun x => shellIncrement omega.1 lowScale highScale x) :
    (centeredShellUnitCube M R hle omega hbar hskew).w1Infinity ≤
      centeringConst d * incrementOscGauge₂ R lowScale highScale omega := by
  rw [centeredShellUnitCube, unitCubeSkewW2InfinityOfAEEq_w1Infinity]
  exact w1Infinity_cubeUnitCube_subConstShell_le R
    (shellIncrement omega.1 lowScale highScale) hbar hskew hbaravg

/-- **The centering estimate at the manuscript's own constant `(h)_{z+cu_n}`.**

This is the binder `hcentre` of
`ApproximateRecurrence.shell_hypothesis_of_centering_ae`, at
`K = centeringConst d`.

: this statement holds only under the proposition supplied by its binder `hle`.
It is a provider A, not a source-facing frozen declaration. -/
private theorem w1Infinity_centeredFreshShellUnitCube_le [NeZero d] (M : ABKModel d)
    (R : TriadicCube d) {lowScale highScale : ℤ} (hle : lowScale ≤ highScale)
    (omega : CutoffSample d) :
    (centeredFreshShellUnitCube M R hle omega).w1Infinity ≤
      centeringConst d * incrementOscGauge₂ R lowScale highScale omega := by
  refine w1Infinity_centeredShellUnitCube_le M R hle omega _ _ ?_
  rw [freshShellCubeAverage_eq_cubeAverageMat_cutoff_sub R omega hle]
  congr 1
  funext x
  exact (shellIncrement_apply_eq_cutoff_sub omega hle x).symm

/-! ## The consumer: the shell-size hypothesis with `hcentre` supplied -/

/-- **The binder `hshell` of the per-cube switch, with the centering estimate
supplied.**

This is `ApproximateRecurrence.shell_hypothesis_of_centering_ae` at
`K = centeringConst d`, with its binder `hcentre` discharged by
`w1Infinity_centeredFreshShellUnitCube_le`.

: this statement holds only under the propositions supplied by its binders --
`hCcg` (`0 < Ccg`), `hle` (`m - h <= m`) and `hS`, the threshold comparison
`shellSizeThreshold M Ccg (centeringConst d) lowScale <= S`, which is a
condition on the data of the recurrence -- together with the membership in the
good event carried inside the almost-sure conclusion.  It is a provider A, not
a source-facing frozen declaration. -/
theorem shell_hypothesis_of_centeringConst_ae [NeZero d] (M : ABKModel d)
    {Ccg : ℝ} (hCcg : 0 < Ccg) (Q : TriadicCube d) (j : ℕ)
    {lowScale highScale : ℤ} (hle : lowScale ≤ highScale) {S : ℝ}
    (hS : shellSizeThreshold M Ccg (centeringConst d) lowScale ≤ S) :
    ∀ R ∈ descendantsAtDepth Q j,
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        omega ∈ goodLocalEvent M Ccg R lowScale →
          (centeredFreshShellUnitCube M R hle omega).w1Infinity ^ 2 ≤
            gridSwitchDiscount Q j lowScale ^ 2 * S *
              Ch02.lambdaSq R (3 / 8) (.finite 2)
                (coefficientCutoffTriadicCoeffFamily M lowScale omega) := by
  intro R hR
  filter_upwards [shell_hypothesis_of_centering_ae M hCcg Q j hle
    (K := centeringConst d) hS R hR] with omega hbound homega
  exact hbound homega (w1Infinity_centeredFreshShellUnitCube_le M R hle omega)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
