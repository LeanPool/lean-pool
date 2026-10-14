/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.CutoffTest
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedSkewAlgebra
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.Basic
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.SkewIdentities

/-!
# LocalizedSkewDivergence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The weak divergence of a `C¹` antisymmetric coefficient field

A `C¹` antisymmetric matrix field `k` acts on a divergence-form equation as a
divergence-free drift: the flux `k grad u` pairs against a zero-trace test
exactly as the drift `u (div k)` does, because the only two terms produced by
one integration by parts are the drift and a contraction of `k` with the
Hessian of the test, and the second vanishes by antisymmetry.

The consequence used by the localized decay estimates is the *quadratic*
identity

```text
  ∫ u ⟨k ∇u, ∇w⟩ = (1 / 2) ∫ u ^ 2 ⟨div k, ∇w⟩ ,
```

valid for a zero-trace `u` and a smooth compactly supported multiplier `w`.
It is what replaces the crude size bound for the smooth part of the skew
coefficient: the left side carries a gradient of the solution and would only
admit a bound by `‖k‖`, while the right side carries no gradient at all and is
bounded by `‖div k‖`.

The identity is obtained without any chain rule for `u ^ 2`, by pairing the
transfer identity twice, once with the test `w u` and once with the factor
`w u`.  Only the divergence-form layer is used, so this module depends on no
model-specific construction.

## Divergence convention

`skewFieldDiv k` contracts the **first** index,

```text
  (div k)_j (x) = ∑_i ∂_i k_{i j}(x) ,
```

the contraction that turns `a ∇u` into `∇ · (a ∇u)` in the divergence-form
equation.  With this convention the quadratic identity carries a plus sign;
with the opposite (row) contraction both sides change sign.

## Main results

- `DivergenceFormProcess.Decay.skewFieldDiv`
- `DivergenceFormProcess.Decay.integral_vecDot_matVecMul_grad_eq_neg`
- `DivergenceFormProcess.Decay.integral_mul_vecDot_matVecMul_eq_half`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open Filter HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open scoped ENNReal

variable {d : ℕ} {U : Set (Vec d)}

/-! ### The divergence of a matrix field -/

/-- The divergence of a matrix field, contracting the first index. -/
def skewFieldDiv (k : Vec d → Mat d) : Vec d → Vec d :=
  fun x j => ∑ i : Fin d, euclideanCoordDeriv i (fun y => k y i j) x

theorem skewFieldDiv_apply (k : Vec d → Mat d) (x : Vec d) (j : Fin d) :
    skewFieldDiv k x j = ∑ i : Fin d, euclideanCoordDeriv i (fun y => k y i j) x :=
  rfl

/-- Each coordinate of the divergence of a `C¹` matrix field is continuous. -/
theorem continuous_skewFieldDiv_apply {k : Vec d → Mat d}
    (hk : ∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q) (j : Fin d) :
    Continuous fun x => skewFieldDiv k x j := by
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((hk i j).continuous_fderiv (by simp)).clm_apply continuous_const

/-! ### `L²` membership on a bounded domain -/

private theorem exists_bound_of_continuousOn {V : Set (Vec d)}
    (hV : IsBoundedDomain V) {f : Vec d → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, ∀ x ∈ V, |f x| ≤ C := by
  have hclos : IsCompact (closure V) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hV.isBounded.closure
  obtain ⟨C, hC⟩ := hclos.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun x hx => by simpa only [Real.norm_eq_abs] using hC x (subset_closure hx)⟩

theorem memScalarL2_of_continuous_bounded (hUm : MeasurableSet U)
    (hU : IsBoundedDomain U) {f : Vec d → ℝ} (hf : Continuous f) :
    MemScalarL2 U f := by
  have := hU.isFiniteMeasure_restrict_volume
  obtain ⟨C, hC⟩ := exists_bound_of_continuousOn hU hf
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem hUm] with x hx
  simpa only [Real.norm_eq_abs] using hC x hx

private theorem memScalarL2_of_continuous_compactSupport {f : Vec d → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) : MemScalarL2 U f := by
  simpa only [MemScalarL2, volumeMeasureOn] using
    (hf.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞)) hfc).restrict U

private theorem integrable_mul_of_memScalarL2 {f g : Vec d → ℝ}
    (hf : MemScalarL2 U f) (hg : MemScalarL2 U g) :
    Integrable (fun x => f x * g x) (volume.restrict U) := by
  simpa only [Pi.mul_apply] using! hf.integrable_mul hg

/-- A `C¹` function on a bounded measurable domain, packaged with its
classical gradient. -/
def contDiffOneH1 (hUm : MeasurableSet U) (hU : IsBoundedDomain U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) : H1Function U where
  toFun := f
  grad := fun x i => (fderiv ℝ f x) (basisVec i)
  memL2 := memScalarL2_of_continuous_bounded hUm hU hf.continuous
  gradMemL2 := fun _ =>
    memScalarL2_of_continuous_bounded hUm hU
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
  hasWeakGradient := HasWeakGradientOn.of_contDiff hf

/-! ### From smooth tests to zero-trace tests -/

private theorem integral_vecDot_eq_sum_coord {F G : Vec d → Vec d}
    (hF : ∀ i : Fin d, MemScalarL2 U fun x => F x i)
    (hG : ∀ i : Fin d, MemScalarL2 U fun x => G x i) :
    ∫ x in U, vecDot (F x) (G x) ∂volume =
      ∑ i : Fin d, ∫ x in U, F x i * G x i ∂volume := by
  rw [show (fun x : Vec d => vecDot (F x) (G x)) =
      fun x : Vec d => ∑ i : Fin d, F x i * G x i from funext fun _ => rfl]
  exact integral_finsetSum Finset.univ fun i _ =>
    integrable_mul_of_memScalarL2 (hF i) (hG i)

private theorem integral_vecDot_congr_of_forall_smooth {P Q : Vec d → Vec d}
    (hP : ∀ i : Fin d, MemScalarL2 U fun x => P x i)
    (hQ : ∀ i : Fin d, MemScalarL2 U fun x => Q x i)
    (hsmooth : ∀ psi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) psi → HasCompactSupport psi →
      tsupport psi ⊆ U →
      ∫ x in U, vecDot (P x) (euclideanGradient psi x) ∂volume =
        ∫ x in U, vecDot (Q x) (euclideanGradient psi x) ∂volume)
    (phi : H10Function U) :
    ∫ x in U, vecDot (P x) (phi.toH1Function.grad x) ∂volume =
      ∫ x in U, vecDot (Q x) (phi.toH1Function.grad x) ∂volume := by
  exact Algsuperdiff.StochasticProcess.Common.DivergenceForm.integral_vecDot_congr_of_forall_smooth
    hP hQ hsmooth phi

/-! ### The transfer identity against smooth tests -/

private theorem integral_vecDot_matVecMul_smooth_eq
    (hUm : MeasurableSet U) (hUb : IsBoundedDomain U)
    {k : Vec d → Mat d} (hk : ∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q)
    (hskew : ∀ x : Vec d, matTranspose (k x) = -k x)
    (phi : H10Function U) {psi : Vec d → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) (hpsic : HasCompactSupport psi) :
    ∫ x in U, vecDot (matVecMul (k x) (euclideanGradient psi x))
        (phi.toH1Function.grad x) ∂volume =
      -∫ x in U, phi.toH1Function.toFun x *
        vecDot (skewFieldDiv k x) (euclideanGradient psi x) ∂volume := by
  classical
  have hDpsi : ∀ j : Fin d, ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv j psi) :=
    fun j => contDiff_euclideanCoordDeriv hpsi j
  have hDpsic : ∀ j : Fin d, HasCompactSupport (euclideanCoordDeriv j psi) :=
    fun j => hasCompactSupport_euclideanCoordDeriv hpsic j
  have hD2c : ∀ i j : Fin d, HasCompactSupport (euclideanCoordSecondDeriv j i psi) :=
    fun i j => hasCompactSupport_euclideanCoordDeriv (hDpsic j) i
  have hD2cont : ∀ i j : Fin d, Continuous (euclideanCoordSecondDeriv j i psi) :=
    fun i j => (contDiff_euclideanCoordDeriv (hDpsi j) i).continuous
  have hDkcont : ∀ i j : Fin d,
      Continuous (euclideanCoordDeriv i fun y => k y i j) :=
    fun i j => ((hk i j).continuous_fderiv (by simp)).clm_apply continuous_const
  set chi : Fin d → Fin d → Vec d → ℝ :=
    fun i j x => k x i j * euclideanCoordDeriv j psi x with hchi_def
  set dA : Fin d → Fin d → Vec d → ℝ :=
    fun i j x => euclideanCoordDeriv i (fun y => k y i j) x *
      euclideanCoordDeriv j psi x with hdA_def
  set dB : Fin d → Fin d → Vec d → ℝ :=
    fun i j x => k x i j * euclideanCoordSecondDeriv j i psi x with hdB_def
  have hchiC1 : ∀ i j : Fin d, ContDiff ℝ 1 (chi i j) := fun i j =>
    (hk i j).mul ((hDpsi j).of_le (by norm_num))
  have hchiL2 : ∀ i j : Fin d, MemScalarL2 U (chi i j) := by
    intro i j
    refine memScalarL2_of_continuous_compactSupport ((hchiC1 i j).continuous) ?_
    simpa only [hchi_def, Pi.mul_apply] using!
      (hDpsic j).mul_left (f := fun x : Vec d => k x i j)
  have hdAL2 : ∀ i j : Fin d, MemScalarL2 U (dA i j) := by
    intro i j
    refine memScalarL2_of_continuous_compactSupport
      ((hDkcont i j).mul ((hDpsi j).continuous)) ?_
    simpa only [hdA_def, Pi.mul_apply] using!
      (hDpsic j).mul_left (f := euclideanCoordDeriv i fun y : Vec d => k y i j)
  have hdBL2 : ∀ i j : Fin d, MemScalarL2 U (dB i j) := by
    intro i j
    refine memScalarL2_of_continuous_compactSupport
      ((hk i j).continuous.mul (hD2cont i j)) ?_
    simpa only [hdB_def, Pi.mul_apply] using!
      (hD2c i j).mul_left (f := fun x : Vec d => k x i j)
  have hchiInt : ∀ i j : Fin d,
      Integrable (fun x => chi i j x * phi.toH1Function.grad x i)
        (volume.restrict U) := fun i j =>
    integrable_mul_of_memScalarL2 (hchiL2 i j) (phi.toH1Function.gradMemL2 i)
  have hdAInt : ∀ i j : Fin d,
      Integrable (fun x => dA i j x * phi.toH1Function.toFun x)
        (volume.restrict U) := fun i j =>
    integrable_mul_of_memScalarL2 (hdAL2 i j) phi.toH1Function.memL2
  have hdBInt : ∀ i j : Fin d,
      Integrable (fun x => dB i j x * phi.toH1Function.toFun x)
        (volume.restrict U) := fun i j =>
    integrable_mul_of_memScalarL2 (hdBL2 i j) phi.toH1Function.memL2
  -- the derivative of the `C¹` factor
  have hderiv : ∀ (i j : Fin d) (x : Vec d),
      (fderiv ℝ (chi i j) x) (basisVec i) = dA i j x + dB i j x := by
    intro i j x
    have hf : HasFDerivAt (fun y : Vec d => k y i j)
        (fderiv ℝ (fun y : Vec d => k y i j) x) x :=
      ((hk i j).differentiable (by norm_num) x).hasFDerivAt
    have hg : HasFDerivAt (euclideanCoordDeriv j psi)
        (fderiv ℝ (euclideanCoordDeriv j psi) x) x :=
      ((hDpsi j).differentiable (by norm_num) x).hasFDerivAt
    have hmul : HasFDerivAt (chi i j)
        (k x i j • fderiv ℝ (euclideanCoordDeriv j psi) x +
          euclideanCoordDeriv j psi x • fderiv ℝ (fun y : Vec d => k y i j) x) x :=
      hf.mul hg
    rw [hmul.fderiv]
    simp only [hdA_def, hdB_def, euclideanCoordDeriv, euclideanCoordSecondDeriv,
      add_apply, smul_apply, smul_eq_mul]
    ring
  -- one integration by parts per index pair
  have key : ∀ i j : Fin d,
      (∫ x in U, chi i j x * phi.toH1Function.grad x i ∂volume) =
        -∫ x in U, (dA i j x + dB i j x) * phi.toH1Function.toFun x ∂volume := by
    intro i j
    have hibp :=
      (contDiffOneH1 hUm hUb (hchiC1 i
        j)).integral_mul_zeroTrace_gradCoord_eq_neg_integral_gradCoord_mul
        phi i
    refine hibp.trans (congrArg Neg.neg (integral_congr_ae ?_))
    filter_upwards with x
    rw [show (contDiffOneH1 hUm hUb (hchiC1 i j)).grad x i =
        (fderiv ℝ (chi i j) x) (basisVec i) from rfl, hderiv i j x]
  -- the left-hand side as a double sum
  have hLHS : (∫ x in U, vecDot (matVecMul (k x) (euclideanGradient psi x))
        (phi.toH1Function.grad x) ∂volume) =
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x in U, chi i j x * phi.toH1Function.grad x i ∂volume := by
    have hpt : ∀ x : Vec d,
        vecDot (matVecMul (k x) (euclideanGradient psi x))
            (phi.toH1Function.grad x) =
          ∑ i : Fin d, ∑ j : Fin d, chi i j x * phi.toH1Function.grad x i := by
      intro x
      rw [vecDot_matVecMul_eq_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [hchi_def, euclideanGradient]
    rw [show (fun x : Vec d => vecDot (matVecMul (k x) (euclideanGradient psi x))
          (phi.toH1Function.grad x)) =
        fun x : Vec d => ∑ i : Fin d, ∑ j : Fin d,
          chi i j x * phi.toH1Function.grad x i from funext hpt,
      integral_finsetSum Finset.univ
        fun i _ => integrable_finsetSum Finset.univ fun j _ => hchiInt i j]
    exact Finset.sum_congr rfl fun i _ =>
      integral_finsetSum Finset.univ fun j _ => hchiInt i j
  -- the drift part of the double sum
  have hsumA : (∑ i : Fin d, ∑ j : Fin d,
        ∫ x in U, dA i j x * phi.toH1Function.toFun x ∂volume) =
      ∫ x in U, phi.toH1Function.toFun x *
        vecDot (skewFieldDiv k x) (euclideanGradient psi x) ∂volume := by
    have hswap : (∑ i : Fin d, ∑ j : Fin d,
        ∫ x in U, dA i j x * phi.toH1Function.toFun x ∂volume) =
        ∫ x in U, ∑ j : Fin d, ∑ i : Fin d,
          dA i j x * phi.toH1Function.toFun x ∂volume := by
      rw [integral_finsetSum Finset.univ
        fun j _ => integrable_finsetSum Finset.univ fun i _ => hdAInt i j]
      rw [show (∑ i : Fin d, ∑ j : Fin d,
            ∫ x in U, dA i j x * phi.toH1Function.toFun x ∂volume) =
          ∑ j : Fin d, ∑ i : Fin d,
            ∫ x in U, dA i j x * phi.toH1Function.toFun x ∂volume from Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ =>
        (integral_finsetSum Finset.univ fun i _ => hdAInt i j).symm
    rw [hswap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [vecDot]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [skewFieldDiv_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hdA_def, euclideanGradient]
    ring
  -- the Hessian part of the double sum vanishes
  have hsumB : (∑ i : Fin d, ∑ j : Fin d,
      ∫ x in U, dB i j x * phi.toH1Function.toFun x ∂volume) = 0 := by
    have hswap : (∑ i : Fin d, ∑ j : Fin d,
        ∫ x in U, dB i j x * phi.toH1Function.toFun x ∂volume) =
        ∫ x in U, ∑ i : Fin d, ∑ j : Fin d,
          dB i j x * phi.toH1Function.toFun x ∂volume := by
      rw [integral_finsetSum Finset.univ
        fun i _ => integrable_finsetSum Finset.univ fun j _ => hdBInt i j]
      exact Finset.sum_congr rfl fun i _ =>
        (integral_finsetSum Finset.univ fun j _ => hdBInt i j).symm
    rw [hswap]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    have hzero : ∑ i : Fin d, ∑ j : Fin d,
        k x i j * euclideanCoordSecondDeriv j i psi x = 0 :=
      sum_sum_mul_eq_zero_of_skew_of_symm
        (fun i j => skew_entry_of_matTranspose (hskew x) i j)
        (fun i j => congrFun (euclideanCoordSecondDeriv_comm_fun hpsi j i) x)
    calc
      ∑ i : Fin d, ∑ j : Fin d, dB i j x * phi.toH1Function.toFun x =
          (∑ i : Fin d, ∑ j : Fin d,
            k x i j * euclideanCoordSecondDeriv j i psi x) *
              phi.toH1Function.toFun x := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Finset.sum_mul]
      _ = 0 := by rw [hzero, zero_mul]
  have hsplit : ∀ i j : Fin d,
      (∫ x in U, (dA i j x + dB i j x) * phi.toH1Function.toFun x ∂volume) =
        (∫ x in U, dA i j x * phi.toH1Function.toFun x ∂volume) +
          ∫ x in U, dB i j x * phi.toH1Function.toFun x ∂volume := by
    intro i j
    rw [← integral_add (hdAInt i j) (hdBInt i j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hLHS]
  have hkey : (∑ i : Fin d, ∑ j : Fin d,
        ∫ x in U, chi i j x * phi.toH1Function.grad x i ∂volume) =
      -((∑ i : Fin d, ∑ j : Fin d,
          ∫ x in U, dA i j x * phi.toH1Function.toFun x ∂volume) +
        ∑ i : Fin d, ∑ j : Fin d,
          ∫ x in U, dB i j x * phi.toH1Function.toFun x ∂volume) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [key i j, hsplit i j]
  rw [hkey, hsumA, hsumB, add_zero]

/-! ### `L²` control of the two flux fields -/

private theorem memScalarL2_mul_of_continuous_left (hUm : MeasurableSet U)
    (hUb : IsBoundedDomain U) {g f : Vec d → ℝ} (hg : Continuous g)
    (hf : MemScalarL2 U f) : MemScalarL2 U fun x => g x * f x := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuousOn hUb hg
  refine MemLp.of_le (hf.const_mul |C|)
    (hg.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem hUm] with x hx
  have h1 : |g x| ≤ |C| := (hC x hx).trans (le_abs_self C)
  simp only [Real.norm_eq_abs, abs_mul, abs_abs]
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

private theorem memScalarL2_mul_of_continuous_right (hUm : MeasurableSet U)
    (hUb : IsBoundedDomain U) {f g : Vec d → ℝ} (hf : MemScalarL2 U f)
    (hg : Continuous g) : MemScalarL2 U fun x => f x * g x := by
  rw [show (fun x => f x * g x) = fun x => g x * f x from funext fun x => mul_comm _ _]
  exact memScalarL2_mul_of_continuous_left hUm hUb hg hf

/-- Each coordinate of the flux of a continuous matrix field against an `L²`
vector field is square integrable on a bounded domain. -/
theorem memScalarL2_matVecMul_coord (hUm : MeasurableSet U)
    (hUb : IsBoundedDomain U) {k : Vec d → Mat d}
    (hk : ∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q) {G : Vec d → Vec d}
    (hG : ∀ j : Fin d, MemScalarL2 U fun x => G x j) (i : Fin d) :
    MemScalarL2 U fun x => matVecMul (k x) (G x) i :=
  memLp_finsetSum Finset.univ fun j _ =>
    memScalarL2_mul_of_continuous_left hUm hUb (hk i j).continuous (hG j)

/-- The drift pairing of a `C¹` matrix field against an `L²` vector field is
square integrable on a bounded domain. -/
theorem memScalarL2_vecDot_skewFieldDiv (hUm : MeasurableSet U)
    (hUb : IsBoundedDomain U) {k : Vec d → Mat d}
    (hk : ∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q) {G : Vec d → Vec d}
    (hG : ∀ j : Fin d, MemScalarL2 U fun x => G x j) :
    MemScalarL2 U fun x => vecDot (skewFieldDiv k x) (G x) :=
  memLp_finsetSum Finset.univ fun j _ =>
    memScalarL2_mul_of_continuous_left hUm hUb
      (continuous_skewFieldDiv_apply hk j) (hG j)

/-! ### The transfer identity -/

/-- **The antisymmetry transfer against zero-trace tests.**  For a `C¹` matrix
field that is antisymmetric at every point, the flux `k grad v` pairs against a
zero-trace test exactly as the drift `-(test) (div k) · grad v` does.  One
integration by parts produces the drift together with a contraction of `k`
against the Hessian of a smooth test, and the second term vanishes because an
antisymmetric array pairs to zero against a symmetric one. -/
theorem integral_vecDot_matVecMul_grad_eq_neg (hUm : MeasurableSet U)
    (hUb : IsBoundedDomain U) {k : Vec d → Mat d}
    (hk : ∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q)
    (hskew : ∀ x : Vec d, matTranspose (k x) = -k x)
    (v phi : H10Function U) :
    ∫ x in U, vecDot (matVecMul (k x) (v.toH1Function.grad x))
        (phi.toH1Function.grad x) ∂volume =
      -∫ x in U, phi.toH1Function.toFun x *
        vecDot (skewFieldDiv k x) (v.toH1Function.grad x) ∂volume := by
  classical
  set P : Vec d → Vec d :=
    fun x j => ∑ i : Fin d, k x i j * phi.toH1Function.grad x i with hP_def
  set Q : Vec d → Vec d :=
    fun x j => -(phi.toH1Function.toFun x * skewFieldDiv k x j) with hQ_def
  have hPmem : ∀ j : Fin d, MemScalarL2 U fun x => P x j := by
    intro j
    exact memLp_finsetSum Finset.univ fun i _ =>
      memScalarL2_mul_of_continuous_left hUm hUb (hk i j).continuous
        (phi.toH1Function.gradMemL2 i)
  have hQmem : ∀ j : Fin d, MemScalarL2 U fun x => Q x j := by
    intro j
    exact (memScalarL2_mul_of_continuous_right hUm hUb phi.toH1Function.memL2
      (continuous_skewFieldDiv_apply hk j)).neg
  have hpairP : ∀ (x : Vec d) (p : Vec d),
      vecDot (matVecMul (k x) p) (phi.toH1Function.grad x) = vecDot (P x) p := by
    intro x p
    rw [vecDot_matVecMul_eq_sum]
    have hswap : (∑ i : Fin d, ∑ j : Fin d,
        k x i j * p j * phi.toH1Function.grad x i) =
        ∑ j : Fin d, ∑ i : Fin d,
          k x i j * p j * phi.toH1Function.grad x i := Finset.sum_comm
    rw [hswap]
    simp only [vecDot, hP_def, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hpairQ : ∀ (x : Vec d) (p : Vec d),
      vecDot (Q x) p = -(phi.toH1Function.toFun x *
        vecDot (skewFieldDiv k x) p) := by
    intro x p
    simp only [vecDot, hQ_def, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmain := integral_vecDot_congr_of_forall_smooth hPmem hQmem ?_ v
  · rw [show (fun x : Vec d => vecDot (matVecMul (k x) (v.toH1Function.grad x))
          (phi.toH1Function.grad x)) =
        fun x : Vec d => vecDot (P x) (v.toH1Function.grad x) from
      funext fun x => hpairP x (v.toH1Function.grad x)]
    rw [hmain, ← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
      hpairQ x (v.toH1Function.grad x))
  · intro psi hpsi hpsic _
    rw [show (fun x : Vec d => vecDot (P x) (euclideanGradient psi x)) =
        fun x : Vec d => vecDot (matVecMul (k x) (euclideanGradient psi x))
          (phi.toH1Function.grad x) from
      funext fun x => (hpairP x (euclideanGradient psi x)).symm]
    rw [integral_vecDot_matVecMul_smooth_eq hUm hUb hk hskew phi hpsi hpsic,
      ← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
      (hpairQ x (euclideanGradient psi x)).symm)

/-! ### The quadratic identity -/

/-- **The antisymmetric flux as a drift.**  For a zero-trace `z` and a smooth
compactly supported multiplier `w`, the drift pairing `w z ⟨div k, grad z⟩` is
the negative of the flux cross term `z ⟨k grad z, grad w⟩`. -/
theorem integral_mul_vecDot_matVecMul_eq_neg (hUm : MeasurableSet U)
    (hUb : IsBoundedDomain U) {k : Vec d → Mat d}
    (hk : ∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q)
    (hskew : ∀ x : Vec d, matTranspose (k x) = -k x)
    (z : H10Function U) {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwc : HasCompactSupport w) :
    (∫ x in U, z.toH1Function.toFun x *
        vecDot (matVecMul (k x) (z.toH1Function.grad x))
          (fun i => (fderiv ℝ w x) (basisVec i)) ∂volume) =
      -∫ x in U, w x * z.toH1Function.toFun x *
        vecDot (skewFieldDiv k x) (z.toH1Function.grad x) ∂volume := by
  classical
  obtain ⟨Y, hYval, hYgrad⟩ := isAdmissibleMultiplier_of_zeroTrace z hw hwc
  set zf : Vec d → ℝ := z.toH1Function.toFun with hzf_def
  set G : Vec d → Vec d := z.toH1Function.grad with hG_def
  set Dw : Vec d → Vec d := fun x i => (fderiv ℝ w x) (basisVec i) with hDw_def
  have halpha := integral_vecDot_matVecMul_grad_eq_neg hUm hUb hk hskew z Y
  have hA : (∫ x in U, vecDot (matVecMul (k x) (G x))
        (Y.toH1Function.grad x) ∂volume) =
      ∫ x in U, zf x * vecDot (matVecMul (k x) (G x)) (Dw x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hYgrad] with x hx
    rw [hx]
    have hzero : vecDot (matVecMul (k x) (G x)) (G x) = 0 :=
      vecDot_matVecMul_self_eq_zero_of_skew (hskew x) (G x)
    simp only [vecDot, Finset.mul_sum] at hzero ⊢
    rw [show (∑ i : Fin d, matVecMul (k x) (G x) i *
          (w x * G x i + zf x * Dw x i)) =
        (∑ i : Fin d, w x * (matVecMul (k x) (G x) i * G x i)) +
          ∑ i : Fin d, zf x * (matVecMul (k x) (G x) i * Dw x i) by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring]
    rw [← Finset.mul_sum, hzero, mul_zero, zero_add, ← Finset.mul_sum]
  have hC : (∫ x in U, Y.toH1Function.toFun x *
        vecDot (skewFieldDiv k x) (G x) ∂volume) =
      ∫ x in U, w x * zf x * vecDot (skewFieldDiv k x) (G x) ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hYval]
  rw [hA, hC] at halpha
  exact halpha

/-- **Integration by parts for the antisymmetric flux against a smooth
multiplier.**  For a zero-trace `z` and a smooth compactly supported `w`, the
cross term `z ⟨k grad z, grad w⟩` carries no gradient of `z` at all: it equals
half of the drift term `z ^ 2 ⟨div k, grad w⟩`.  This is what lets the smooth
part of an antisymmetric coefficient be paid for by `‖div k‖` rather than by
`‖k‖`. -/
theorem integral_mul_vecDot_matVecMul_eq_half (hUm : MeasurableSet U)
    (hUb : IsBoundedDomain U) {k : Vec d → Mat d}
    (hk : ∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q)
    (hskew : ∀ x : Vec d, matTranspose (k x) = -k x)
    (z : H10Function U) {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwc : HasCompactSupport w) :
    (∫ x in U, z.toH1Function.toFun x *
        vecDot (matVecMul (k x) (z.toH1Function.grad x))
          (fun i => (fderiv ℝ w x) (basisVec i)) ∂volume) =
      1 / 2 * ∫ x in U, z.toH1Function.toFun x ^ 2 *
        vecDot (skewFieldDiv k x)
          (fun i => (fderiv ℝ w x) (basisVec i)) ∂volume := by
  classical
  obtain ⟨Y, hYval, hYgrad⟩ := isAdmissibleMultiplier_of_zeroTrace z hw hwc
  set zf : Vec d → ℝ := z.toH1Function.toFun with hzf_def
  set G : Vec d → Vec d := z.toH1Function.grad with hG_def
  set Dw : Vec d → Vec d := fun x i => (fderiv ℝ w x) (basisVec i) with hDw_def
  have hDwCont : ∀ i : Fin d, Continuous fun x => Dw x i := by
    intro i
    exact (hw.continuous_fderiv (by simp)).clm_apply continuous_const
  have hbG : MemScalarL2 U fun x => vecDot (skewFieldDiv k x) (G x) :=
    memScalarL2_vecDot_skewFieldDiv hUm hUb hk z.toH1Function.gradMemL2
  have hbDw : Continuous fun x => vecDot (skewFieldDiv k x) (Dw x) :=
    continuous_finsetSum _ fun i _ =>
      (continuous_skewFieldDiv_apply hk i).mul (hDwCont i)
  have hwzf : MemScalarL2 U fun x => w x * zf x :=
    memScalarL2_mul_of_continuous_left hUm hUb hw.continuous z.toH1Function.memL2
  have hint1 : Integrable
      (fun x => w x * zf x * vecDot (skewFieldDiv k x) (G x))
      (volume.restrict U) := integrable_mul_of_memScalarL2 hwzf hbG
  have hint2 : Integrable
      (fun x => zf x ^ 2 * vecDot (skewFieldDiv k x) (Dw x))
      (volume.restrict U) := by
    refine (integrable_mul_of_memScalarL2 z.toH1Function.memL2
      (memScalarL2_mul_of_continuous_right hUm hUb z.toH1Function.memL2 hbDw)).congr ?_
    filter_upwards with x
    ring
  have halpha :=
    integral_mul_vecDot_matVecMul_eq_neg hUm hUb hk hskew z hw hwc
  have hbeta := integral_vecDot_matVecMul_grad_eq_neg hUm hUb hk hskew Y z
  have hB : (∫ x in U, vecDot (matVecMul (k x) (Y.toH1Function.grad x))
        (G x) ∂volume) =
      -∫ x in U, zf x * vecDot (matVecMul (k x) (G x)) (Dw x) ∂volume := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hYgrad] with x hx
    rw [hx]
    have hsplitK : matVecMul (k x) (fun i => w x * G x i + zf x * Dw x i) =
        fun i => w x * matVecMul (k x) (G x) i +
          zf x * matVecMul (k x) (Dw x) i := by
      funext i
      simp only [matVecMul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsplitK]
    have hzero : vecDot (matVecMul (k x) (G x)) (G x) = 0 :=
      vecDot_matVecMul_self_eq_zero_of_skew (hskew x) (G x)
    have hflip : vecDot (matVecMul (k x) (Dw x)) (G x) =
        -vecDot (matVecMul (k x) (G x)) (Dw x) :=
      vecDot_matVecMul_eq_neg_of_skew (hskew x) (Dw x) (G x)
    have hexpand : vecDot (fun i => w x * matVecMul (k x) (G x) i +
          zf x * matVecMul (k x) (Dw x) i) (G x) =
        w x * vecDot (matVecMul (k x) (G x)) (G x) +
          zf x * vecDot (matVecMul (k x) (Dw x)) (G x) := by
      simp only [vecDot, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexpand, hzero, hflip, mul_zero, zero_add]
    ring
  have hD : (∫ x in U, zf x *
        vecDot (skewFieldDiv k x) (Y.toH1Function.grad x) ∂volume) =
      (∫ x in U, w x * zf x * vecDot (skewFieldDiv k x) (G x) ∂volume) +
        ∫ x in U, zf x ^ 2 * vecDot (skewFieldDiv k x) (Dw x) ∂volume := by
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae ?_
    filter_upwards [hYgrad] with x hx
    rw [hx]
    have hexpand : vecDot (skewFieldDiv k x)
          (fun i => w x * G x i + zf x * Dw x i) =
        w x * vecDot (skewFieldDiv k x) (G x) +
          zf x * vecDot (skewFieldDiv k x) (Dw x) := by
      simp only [vecDot, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexpand]
    ring
  rw [hB, hD] at hbeta
  linarith only [halpha, hbeta]

/-- The drift pairing in terms of the multiplier gradient alone. -/
theorem integral_mul_mul_vecDot_skewFieldDiv_eq (hUm : MeasurableSet U)
    (hUb : IsBoundedDomain U) {k : Vec d → Mat d}
    (hk : ∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q)
    (hskew : ∀ x : Vec d, matTranspose (k x) = -k x)
    (z : H10Function U) {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwc : HasCompactSupport w) :
    (∫ x in U, w x * z.toH1Function.toFun x *
        vecDot (skewFieldDiv k x) (z.toH1Function.grad x) ∂volume) =
      -(1 / 2) * ∫ x in U, z.toH1Function.toFun x ^ 2 *
        vecDot (skewFieldDiv k x)
          (fun i => (fderiv ℝ w x) (basisVec i)) ∂volume := by
  have h1 := integral_mul_vecDot_matVecMul_eq_neg hUm hUb hk hskew z hw hwc
  have h2 := integral_mul_vecDot_matVecMul_eq_half hUm hUb hk hskew z hw hwc
  linarith only [h1, h2]

end DivergenceFormProcess.Decay
