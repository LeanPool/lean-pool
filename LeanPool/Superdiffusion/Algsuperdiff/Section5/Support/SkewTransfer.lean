/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.SolenoidalStream
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.ShellSum
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.Translation
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.Basic
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.Algebra.Membership
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.BasicLemmas
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.SkewIdentities
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.FieldDivergenceTest

/-!
# SkewTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The antisymmetry transfer for a variable skew field

ABK26's iteration scheme for the injection estimate of Section 5.1 solves, at
each step,

```text
  -Δ h_j = -∇ · ( w_j ∇ · (k_m - k_n) )   in □_n ,   h_j = 0 on ∂□_n ,
```

and then rewrites the right side, "using that `k_m - k_n` is anti-symmetric", as

```text
  ∇ · ( w ∇ · k ) = ∇w · (∇ · k) = ∇ · ( k ∇w ) .
```

The manuscript states the display and does not prove it.  This module supplies
the argument, as an identity of the two weak forcings and then as an equivalence
of the two Dirichlet problems.

## The divergence convention

`matFieldDiv k` contracts the **first** index,

```text
  (∇ · k)_j = ∑_i ∂_i k_{i j} ,
```

which is the convention under which the printed display is literally true: it is
the same contraction that turns `a ∇u` into `∇ · a ∇u` in the divergence-form
equation.  With the opposite (row) contraction both sides of the display change
sign, so the convention is not cosmetic; it is the one fixed for the maps
`Vec d → Mat d` of this file.

## The mathematics

Write the difference of the two forcings against a test function `φ` and expand
the product rule inside one integration by parts:

```text
  ∑_{i,j} ∂_i ( k_{i j} · w · ∂_j φ )
    = ∑_{i,j} (∂_i k_{i j}) w ∂_j φ + ∑_{i,j} k_{i j} (∂_i w) ∂_j φ
      + ∑_{i,j} k_{i j} w ∂_i ∂_j φ .
```

The left side integrates to zero (a compactly supported field), the last sum
vanishes pointwise because a skew array pairs to zero against the symmetric
Hessian of a smooth test function, and the first two sums are, after renaming the
summation indices and using skewness once, exactly the two forcings.  Only the
first derivative of `k` is used, so `C¹` with continuous derivative is enough;
the shell increments carry `C²` data.

The single integration by parts is carried out against the test function
`x ↦ ∂_j φ (x) · k_{i j}(x)`, which is `C¹` and compactly supported in the cube
but not smooth.  It is admissible because a smooth compactly supported factor
times an `H¹` factor lies in `H¹₀`, and an `H¹` function integrates by parts
against every `H¹₀` function.  The passage from smooth test functions to `H¹₀`
test functions is the `H¹₀` approximating sequence, exactly as in the constant
skew shift and in the constant-forcing invariance.

## Main definitions

* `matFieldDiv k` — the divergence `(∇ · k)_j = ∑_i ∂_i k_{i j}` of a matrix
  field.

## References

* ABK26, the proof of the injection estimate of Section 5.1 (the antisymmetry
  step of the iteration scheme).
* `Algsuperdiff.Section3.Cutoff.Limit` (`cutoff_skew`),
  `Algsuperdiff.Section3.Cutoff.Finite` (`finiteShellIncrement_skew`) — the
  skewness of the cutoff and of its finite increments.
* `Algsuperdiff.Section3.Provider.Stream.ShellSum` (`shellIncrement`,
  `shellIncrement_apply_eq_cutoff_sub`) — the increment as a shell field with
  honest first and second derivatives.
* `Algsuperdiff.Section4.Provider.ExcessDecay.AntisymmetricShift` — the constant
  skew matrix case, where no derivative of the field appears.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory Filter
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Support
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Shared divergence convention

The generic divergence and analytic support are imported from `FieldDivergenceTest`. -/

/-- Entrywise antisymmetry, read off the matrix identity. -/
private theorem skew_entry_of_matTranspose {A : Mat d} (h : matTranspose A = -A)
    (i j : Fin d) : A j i = -A i j := by
  simpa only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply]
    using congrFun (congrFun h i) j

open Algsuperdiff.Section3.Provider.Corrector in
/-! ## 2. Two elementary reductions -/

private theorem sum_sum_mul_eq_zero_of_skew_of_symm {K : Mat d}
    (hK : ∀ i j : Fin d, K j i = -K i j) {T : Fin d → Fin d → ℝ}
    (hT : ∀ i j : Fin d, T i j = T j i) :
    ∑ i : Fin d, ∑ j : Fin d, K i j * T i j = 0 := by
  exact StochasticProcess.Common.DivergenceForm.sum_sum_mul_eq_zero_of_skew_of_symm
    hK hT

/-! ## 3. `L²` membership on a bounded domain -/

private theorem memH1_of_contDiff_one {U : Set (Vec d)} (hUm : MeasurableSet U)
    (hU : IsBoundedDomain U) {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) : MemH1 U f :=
  ⟨{ toFun := f
     grad := fun x i => (fderiv ℝ f x) (basisVec i)
     memL2 := memScalarL2_of_continuous_of_isBoundedDomain hUm hU hf.continuous
     gradMemL2 := fun i =>
       memScalarL2_of_continuous_of_isBoundedDomain
       (f := fun x => (fderiv ℝ f x) (basisVec i)) hUm hU
       ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
     hasWeakGradient := HasWeakGradientOn.of_contDiff hf }, rfl⟩

/-! ## 4. From smooth tests to zero-trace tests -/

private theorem integral_vecDot_congr_of_forall_smooth {U : Set (Vec d)} {P Q : Vec d → Vec d}
    (hP : ∀ i : Fin d, MemScalarL2 U fun x => P x i)
    (hQ : ∀ i : Fin d, MemScalarL2 U fun x => Q x i)
    (hsmooth : ∀ psi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) psi → HasCompactSupport psi →
      tsupport psi ⊆ U →
      ∫ x in U, vecDot (P x) (euclideanGradient psi x) ∂volume =
        ∫ x in U, vecDot (Q x) (euclideanGradient psi x) ∂volume)
    (phi : H10Function U) :
    ∫ x in U, vecDot (P x) (phi.toH1Function.grad x) ∂volume =
      ∫ x in U, vecDot (Q x) (phi.toH1Function.grad x) ∂volume := by
  exact StochasticProcess.Common.DivergenceForm.integral_vecDot_congr_of_forall_smooth
    hP hQ hsmooth phi

/-! ## 5. The identity against smooth tests -/

private theorem smoothMatrixField_componentIntegrationByParts :
    ∀ {d : ℕ} {U : Set (Vec d)},
      IsOpenBoundedConvexDomain U →
        ∀ {k : Vec d → Mat d},
          (∀ (a b : Fin d), ContDiff ℝ (1 : WithTop ℕ∞) fun (x : Vec d) => k x a b) →
            ∀ (w : H1Function U) {psi : Vec d → ℝ},
              IsFiniteMeasure (volume.restrict U) →
                (∀ (j : Fin d), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (euclideanCoordDeriv j psi)) →
                  (∀ (j : Fin d), HasCompactSupport (euclideanCoordDeriv j psi)) →
                    (∀ (j : Fin d), tsupport (euclideanCoordDeriv j psi) ⊆ U) →
                      (∀ (i j : Fin d),
                          Integrable (fun (x : Vec d) => w.toFun x * (k x i j *
                            euclideanCoordSecondDeriv j i psi x))
                            (volume.restrict U)) →
                        (∀ (i j : Fin d),
                            Integrable
                              (fun (x : Vec d) =>
                                w.toFun x *
                                  (euclideanCoordDeriv j psi x * euclideanCoordDeriv i (fun (y :
                                    Vec d) => k y i j) x))
                              (volume.restrict U)) →
                          ∀ (i j : Fin d),
                            (∫ (x : Vec d) in U, w.toFun x * (k x i j * euclideanCoordSecondDeriv
                              j i psi x)) +
                                ∫ (x : Vec d) in U,
                                  w.toFun x *
                                    (euclideanCoordDeriv j psi x * euclideanCoordDeriv i (fun (y :
                                      Vec d) => k y i j) x) =
                              -∫ (x : Vec d) in U, w.grad x i * (euclideanCoordDeriv j psi x * k x
                                i j) := by
  intro d U hU k hk w psi _ hDpsi_smooth hDpsi_cs hDpsi_sub hP_int hQ_int i j
  have hchi : ContDiff ℝ 1 fun x => euclideanCoordDeriv j psi x * k x i j :=
    ((hDpsi_smooth j).of_le (by norm_num)).mul (hk i j)
  obtain ⟨X, hX⟩ : MemH10 U fun x => euclideanCoordDeriv j psi x * k x i j :=
    memH10_mul_of_contDiff_hasCompactSupport hU (hDpsi_smooth j) (hDpsi_cs j) (hDpsi_sub j)
      (memH1_of_contDiff_one hU.isOpen.measurableSet hU.isBoundedDomain (hk i j))
  have hweakX : HasWeakPartialDerivOn U i (fun x => euclideanCoordDeriv j psi x * k x i j)
      fun x => X.toH1Function.grad x i := by
    rw [← hX]
    exact X.toH1Function.hasWeakGradient i
  have hgrad_ae : (fun x => X.toH1Function.grad x i) =ᵐ[volume.restrict U]
      fun x => euclideanCoordDeriv i (fun y => euclideanCoordDeriv j psi y * k y i j) x :=
    HasWeakPartialDerivOn.ae_eq hU.isOpen
      (MeasureTheory.IntegrableOn.locallyIntegrableOn
        ((X.toH1Function.gradMemL2 i).integrable one_le_two))
      (((hchi.continuous_fderiv (by simp)).clm_apply
        continuous_const).locallyIntegrable.locallyIntegrableOn U)
      hweakX (HasWeakPartialDerivOn.of_contDiff hchi)
  have hprod : ∀ x : Vec d,
      euclideanCoordDeriv i (fun y => euclideanCoordDeriv j psi y * k y i j) x =
        k x i j * euclideanCoordSecondDeriv j i psi x +
          euclideanCoordDeriv j psi x * euclideanCoordDeriv i (fun y => k y i j) x := by
    intro x
    have hf : HasFDerivAt (euclideanCoordDeriv j psi)
        (fderiv ℝ (euclideanCoordDeriv j psi) x) x :=
      ((hDpsi_smooth j).differentiable (by norm_num) x).hasFDerivAt
    have hg : HasFDerivAt (fun y : Vec d => k y i j)
        (fderiv ℝ (fun y : Vec d => k y i j) x) x :=
      ((hk i j).differentiable (by norm_num) x).hasFDerivAt
    change (fderiv ℝ (fun y : Vec d => euclideanCoordDeriv j psi y * k y i j) x) (basisVec i) =
      k x i j * (fderiv ℝ (euclideanCoordDeriv j psi) x) (basisVec i) +
        euclideanCoordDeriv j psi x * (fderiv ℝ (fun y : Vec d => k y i j) x) (basisVec i)
    have hmul : HasFDerivAt (fun y : Vec d => euclideanCoordDeriv j psi y * k y i j)
        (euclideanCoordDeriv j psi x • fderiv ℝ (fun y : Vec d => k y i j) x +
          k x i j • fderiv ℝ (euclideanCoordDeriv j psi) x) x := hf.mul hg
    rw [hmul.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hibp := H1Function.integral_mul_zeroTrace_gradCoord_eq_neg_integral_gradCoord_mul w X i
  have hL : ∫ x in U, w.toFun x * X.toH1Function.grad x i ∂volume =
      (∫ x in U, w.toFun x * (k x i j * euclideanCoordSecondDeriv j i psi x) ∂volume) +
        ∫ x in U, w.toFun x *
          (euclideanCoordDeriv j psi x *
            euclideanCoordDeriv i (fun y => k y i j) x) ∂volume := by
    rw [← integral_add (hP_int i j) (hQ_int i j)]
    refine integral_congr_ae ?_
    filter_upwards [hgrad_ae] with x hx
    rw [hx, hprod x, mul_add]
  rw [hL] at hibp
  rw [hibp]
  simp only [hX]

private theorem integral_smul_matFieldDiv_eq_of_smooth
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {k : Vec d → Mat d} (hk : ∀ a b : Fin d, ContDiff ℝ 1 fun x => k x a b)
    (hskew : ∀ x : Vec d, matTranspose (k x) = -k x)
    (w : H1Function U) {psi : Vec d → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) (hpsic : HasCompactSupport psi)
    (hpsiU : tsupport psi ⊆ U) :
    ∫ x in U, vecDot (w.toFun x • matFieldDiv k x) (euclideanGradient psi x) ∂volume =
      ∫ x in U, vecDot (matVecMul (k x) (w.grad x)) (euclideanGradient psi x) ∂volume := by
  have := hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hDpsi_smooth : ∀ j : Fin d, ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv j psi) :=
    fun j => contDiff_euclideanCoordDeriv hpsi j
  have hDpsi_cs : ∀ j : Fin d, HasCompactSupport (euclideanCoordDeriv j psi) :=
    fun j => hasCompactSupport_euclideanCoordDeriv hpsic j
  have hDpsi_sub : ∀ j : Fin d, tsupport (euclideanCoordDeriv j psi) ⊆ U :=
    fun j => (tsupport_euclideanCoordDeriv_subset_tsupport j psi).trans hpsiU
  have hD2_cs : ∀ i j : Fin d, HasCompactSupport (euclideanCoordSecondDeriv j i psi) :=
    fun i j => hasCompactSupport_euclideanCoordDeriv (hDpsi_cs j) i
  have hD2_cont : ∀ i j : Fin d, Continuous (euclideanCoordSecondDeriv j i psi) :=
    fun i j => (contDiff_euclideanCoordDeriv (hDpsi_smooth j) i).continuous
  have hDk_cont : ∀ i j : Fin d,
      Continuous fun x => euclideanCoordDeriv i (fun y => k y i j) x :=
    fun i j => ((hk i j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hS1 : ∀ i j : Fin d,
      MemScalarL2 U fun x => k x i j * euclideanCoordSecondDeriv j i psi x := fun i j =>
    memScalarL2_of_continuous_hasCompactSupport ((hk i j).continuous.mul (hD2_cont i j))
      (HasCompactSupport.mul_left (hD2_cs i j))
  have hS2 : ∀ i j : Fin d, MemScalarL2 U fun x =>
      euclideanCoordDeriv j psi x * euclideanCoordDeriv i (fun y => k y i j) x := fun i j =>
    memScalarL2_of_continuous_hasCompactSupport
      ((hDpsi_smooth j).continuous.mul (hDk_cont i j))
      (HasCompactSupport.mul_right (hDpsi_cs j))
  have hS3 : ∀ a i j : Fin d,
      MemScalarL2 U fun x => euclideanCoordDeriv a psi x * k x i j := fun a i j =>
    memScalarL2_of_continuous_hasCompactSupport
      ((hDpsi_smooth a).continuous.mul (hk i j).continuous)
      (HasCompactSupport.mul_right (hDpsi_cs a))
  have hP_int : ∀ i j : Fin d, Integrable
      (fun x => w.toFun x * (k x i j * euclideanCoordSecondDeriv j i psi x))
      (volume.restrict U) := fun i j => integrable_mul_of_memScalarL2 w.memL2 (hS1 i j)
  have hQ_int : ∀ i j : Fin d, Integrable
      (fun x => w.toFun x *
        (euclideanCoordDeriv j psi x * euclideanCoordDeriv i (fun y => k y i j) x))
      (volume.restrict U) := fun i j => integrable_mul_of_memScalarL2 w.memL2 (hS2 i j)
  have hR_int : ∀ a i j : Fin d, Integrable
      (fun x => w.grad x a * (euclideanCoordDeriv i psi x * k x i j))
      (volume.restrict U) := fun a i j =>
    integrable_mul_of_memScalarL2 (w.gradMemL2 a) (hS3 i i j)
  -- One integration by parts per pair of indices, against the `C¹` zero-trace test
  -- `x ↦ ∂_j ψ (x) · k_{i j}(x)`.
  have key := @smoothMatrixField_componentIntegrationByParts (d) (U) (hU) (k) (hk) (w) (psi)
    (this) (hDpsi_smooth) (hDpsi_cs) (hDpsi_sub) (hP_int) (hQ_int)
  -- The left-hand side as a double sum of scalar integrals.
  have hLHS : ∫ x in U, vecDot (w.toFun x • matFieldDiv k x) (euclideanGradient psi x) ∂volume =
      ∑ i : Fin d, ∑ j : Fin d, ∫ x in U, w.toFun x *
        (euclideanCoordDeriv j psi x *
          euclideanCoordDeriv i (fun y => k y i j) x) ∂volume := by
    have hpt : ∀ x : Vec d,
        vecDot (w.toFun x • matFieldDiv k x) (euclideanGradient psi x) =
          ∑ j : Fin d, ∑ i : Fin d, w.toFun x *
            (euclideanCoordDeriv j psi x *
              euclideanCoordDeriv i (fun y => k y i j) x) := by
      intro x
      simp only [vecDot, Pi.smul_apply, smul_eq_mul, matFieldDiv, euclideanGradient,
        Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [show (fun x : Vec d => vecDot (w.toFun x • matFieldDiv k x) (euclideanGradient psi x)) =
        fun x : Vec d => ∑ j : Fin d, ∑ i : Fin d, w.toFun x *
          (euclideanCoordDeriv j psi x *
            euclideanCoordDeriv i (fun y => k y i j) x) from funext hpt,
      integral_finsetSum Finset.univ
        fun j _ => integrable_finsetSum Finset.univ fun i _ => hQ_int i j,
      show (∑ j : Fin d, ∫ x in U, ∑ i : Fin d, w.toFun x *
            (euclideanCoordDeriv j psi x *
              euclideanCoordDeriv i (fun y => k y i j) x) ∂volume) =
          ∑ j : Fin d, ∑ i : Fin d, ∫ x in U, w.toFun x *
            (euclideanCoordDeriv j psi x *
              euclideanCoordDeriv i (fun y => k y i j) x) ∂volume from
        Finset.sum_congr rfl fun j _ =>
          integral_finsetSum Finset.univ fun i _ => hQ_int i j]
    exact Finset.sum_comm
  -- The right-hand side as a double sum, after using the skewness of `k` once.
  have hRHS : ∫ x in U, vecDot (matVecMul (k x) (w.grad x)) (euclideanGradient psi x) ∂volume =
      -∑ i : Fin d, ∑ j : Fin d,
        ∫ x in U, w.grad x i * (euclideanCoordDeriv j psi x * k x i j) ∂volume := by
    have hpt : ∀ x : Vec d,
        vecDot (matVecMul (k x) (w.grad x)) (euclideanGradient psi x) =
          ∑ i : Fin d, ∑ j : Fin d,
            w.grad x j * (euclideanCoordDeriv i psi x * k x i j) := by
      intro x
      simp only [vecDot, matVecMul, euclideanGradient, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hstep : ∀ i j : Fin d,
        (∫ x in U, w.grad x j * (euclideanCoordDeriv i psi x * k x i j) ∂volume) =
          -∫ x in U, w.grad x j * (euclideanCoordDeriv i psi x * k x j i) ∂volume := by
      intro i j
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change w.grad x j * (euclideanCoordDeriv i psi x * k x i j) =
        -(w.grad x j * (euclideanCoordDeriv i psi x * k x j i))
      rw [skew_entry_of_matTranspose (hskew x) j i]
      ring
    rw [show (fun x : Vec d => vecDot (matVecMul (k x) (w.grad x)) (euclideanGradient psi x)) =
        fun x : Vec d => ∑ i : Fin d, ∑ j : Fin d,
          w.grad x j * (euclideanCoordDeriv i psi x * k x i j) from funext hpt,
      integral_finsetSum Finset.univ
        fun i _ => integrable_finsetSum Finset.univ fun j _ => hR_int j i j,
      show (∑ i : Fin d, ∫ x in U, ∑ j : Fin d,
            w.grad x j * (euclideanCoordDeriv i psi x * k x i j) ∂volume) =
          ∑ i : Fin d, ∑ j : Fin d,
            ∫ x in U, w.grad x j * (euclideanCoordDeriv i psi x * k x i j) ∂volume from
        Finset.sum_congr rfl fun i _ =>
          integral_finsetSum Finset.univ fun j _ => hR_int j i j]
    calc (∑ i : Fin d, ∑ j : Fin d,
            ∫ x in U, w.grad x j * (euclideanCoordDeriv i psi x * k x i j) ∂volume)
        = ∑ i : Fin d, ∑ j : Fin d,
            -∫ x in U, w.grad x j * (euclideanCoordDeriv i psi x * k x j i) ∂volume :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hstep i j
      _ = -∑ i : Fin d, ∑ j : Fin d,
            ∫ x in U, w.grad x j * (euclideanCoordDeriv i psi x * k x j i) ∂volume := by
          simp only [Finset.sum_neg_distrib]
      _ = -∑ i : Fin d, ∑ j : Fin d,
            ∫ x in U, w.grad x i * (euclideanCoordDeriv j psi x * k x i j) ∂volume :=
          congrArg Neg.neg Finset.sum_comm
  -- The second-derivative sum vanishes pointwise by skewness.
  have hPzero : ∑ i : Fin d, ∑ j : Fin d,
      ∫ x in U, w.toFun x * (k x i j * euclideanCoordSecondDeriv j i psi x) ∂volume = 0 := by
    have hswap : (∑ i : Fin d, ∑ j : Fin d,
        ∫ x in U, w.toFun x * (k x i j * euclideanCoordSecondDeriv j i psi x) ∂volume) =
        ∫ x in U, ∑ i : Fin d, ∑ j : Fin d,
          w.toFun x * (k x i j * euclideanCoordSecondDeriv j i psi x) ∂volume := by
      rw [integral_finsetSum Finset.univ
        fun i _ => integrable_finsetSum Finset.univ fun j _ => hP_int i j]
      exact Finset.sum_congr rfl fun i _ =>
        (integral_finsetSum Finset.univ fun j _ => hP_int i j).symm
    rw [hswap]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    have hzero : ∑ i : Fin d, ∑ j : Fin d,
        k x i j * euclideanCoordSecondDeriv j i psi x = 0 :=
      sum_sum_mul_eq_zero_of_skew_of_symm
        (fun i j => skew_entry_of_matTranspose (hskew x) i j)
        (fun i j => congrFun (euclideanCoordSecondDeriv_comm_fun hpsi j i) x)
    calc ∑ i : Fin d, ∑ j : Fin d,
          w.toFun x * (k x i j * euclideanCoordSecondDeriv j i psi x)
        = w.toFun x * ∑ i : Fin d, ∑ j : Fin d,
            k x i j * euclideanCoordSecondDeriv j i psi x := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
      _ = 0 := by rw [hzero, mul_zero]
  have hsum : (∑ i : Fin d, ∑ j : Fin d,
        ∫ x in U, w.toFun x * (k x i j * euclideanCoordSecondDeriv j i psi x) ∂volume) +
      (∑ i : Fin d, ∑ j : Fin d, ∫ x in U, w.toFun x *
        (euclideanCoordDeriv j psi x *
          euclideanCoordDeriv i (fun y => k y i j) x) ∂volume) =
      -∑ i : Fin d, ∑ j : Fin d,
        ∫ x in U, w.grad x i * (euclideanCoordDeriv j psi x * k x i j) ∂volume := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => key i j
  rw [hLHS, hRHS, ← hsum, hPzero, zero_add]

/-! ## 6. Integral identities for the forcing fields -/

private theorem integral_vecDot_neg_left {U : Set (Vec d)} (F G : Vec d → Vec d) :
    ∫ x in U, vecDot (-F x) (G x) ∂volume = -∫ x in U, vecDot (F x) (G x) ∂volume := by
  simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, integral_neg]

/-! ## 7. The antisymmetry transfer -/

/-- **The antisymmetry transfer.**

For a `C¹` matrix field `k` that is skew at every point, and for `w ∈ H¹(U)` on a
bounded convex open set `U`, the two weak forcings `w (∇ · k)` and `k ∇w` pair
identically against the gradient of every zero-trace test function:

```text
  ∫_U (w (∇ · k)) · ∇φ = ∫_U (k ∇w) · ∇φ ,   φ ∈ H¹₀(U) .
```

Equivalently `∇ · (w (∇ · k)) = ∇ · (k ∇w)` in the sense of distributions.  Both
extra terms of the expansion
`∑_{i,j} ∂_i (k_{i j} ∂_j w) = ∑_{i,j} (∂_i k_{i j}) ∂_j w + ∑_{i,j} k_{i j} ∂_i ∂_j w`
vanish because a skew array pairs to zero against a symmetric one: here the
symmetric array is the second derivative of the smooth test function, which is
where the single integration by parts of the proof places both derivatives. -/
theorem integral_vecDot_smul_matFieldDiv_eq_integral_vecDot_matVecMul
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {k : Vec d → Mat d} (hk : ∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q)
    (hskew : ∀ x : Vec d, matTranspose (k x) = -k x)
    (w : H1Function U) (phi : H10Function U) :
    ∫ x in U, vecDot (w.toFun x • matFieldDiv k x) (phi.toH1Function.grad x) ∂volume =
      ∫ x in U, vecDot (matVecMul (k x) (w.grad x)) (phi.toH1Function.grad x) ∂volume := by
  have hUm : MeasurableSet U := hU.isOpen.measurableSet
  have hUb : IsBoundedDomain U := hU.isBoundedDomain
  refine integral_vecDot_congr_of_forall_smooth ?_ ?_ ?_ phi
  · intro i
    exact memScalarL2_mul_of_continuous_right hUm hUb w.memL2
      (continuous_matFieldDiv_apply hk i)
  · intro i
    exact memLp_finsetSum Finset.univ fun j _ =>
      memScalarL2_mul_of_continuous_left hUm hUb (hk i j).continuous (w.gradMemL2 j)
  · intro psi hpsi hpsic hpsiU
    exact integral_smul_matFieldDiv_eq_of_smooth hU hk hskew w hpsi hpsic hpsiU

/-- **The antisymmetry transfer on the weak equation.**  The divergence-form weak
equation with forcing `-w (∇ · k)` and the one with forcing `-k ∇w` have exactly
the same solutions when `k` is `C¹` and skew. -/
theorem isDivFormWeakSolutionOn_smul_matFieldDiv_iff
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {k : Vec d → Mat d} (hk : ∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q)
    (hskew : ∀ x : Vec d, matTranspose (k x) = -k x)
    {a : CoeffField d} {u : H1Function U} (w : H1Function U) :
    IsDivFormWeakSolutionOn a U u (fun x => -w.toFun x • matFieldDiv k x) ↔
      IsDivFormWeakSolutionOn a U u fun x => -matVecMul (k x) (w.grad x) := by
  have hforcing : ∀ phi : H10Function U,
      (-∫ x in U, vecDot (-w.toFun x • matFieldDiv k x) (phi.toH1Function.grad x) ∂volume) =
        -∫ x in U, vecDot (-matVecMul (k x) (w.grad x)) (phi.toH1Function.grad x) ∂volume := by
    intro phi
    rw [show (fun x : Vec d => vecDot (-w.toFun x • matFieldDiv k x)
          (phi.toH1Function.grad x)) =
        fun x : Vec d => vecDot (-(w.toFun x • matFieldDiv k x)) (phi.toH1Function.grad x) from
      funext fun x => by rw [neg_smul]]
    rw [integral_vecDot_neg_left, integral_vecDot_neg_left,
      integral_vecDot_smul_matFieldDiv_eq_integral_vecDot_matVecMul hU hk hskew w phi]
  constructor
  · intro h phi
    rw [h phi, hforcing phi]
  · intro h phi
    rw [h phi, ← hforcing phi]

/-- **The antisymmetry transfer on the localized Dirichlet problem.**  The boundary
clause of `IsDirichletSolutionAt` does not see the forcing field, so the transfer
moves the whole predicate. -/
theorem isDirichletSolutionAt_smul_matFieldDiv_iff
    {y : Vec d} {n : ℤ} {k : Vec d → Mat d}
    (hk : ∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q)
    (hskew : ∀ x : Vec d, matTranspose (k x) = -k x)
    {a : CoeffField d} {u : H1Function (cubeSetAt y n)} (w : H1Function (cubeSetAt y n)) :
    IsDirichletSolutionAt a y n u (fun x => -w.toFun x • matFieldDiv k x) ↔
      IsDirichletSolutionAt a y n u fun x => -matVecMul (k x) (w.grad x) :=
  and_congr_right fun _ =>
    isDivFormWeakSolutionOn_smul_matFieldDiv_iff (isOpenBoundedConvexDomain_cubeSetAt y n)
      hk hskew w

/-! ## 8. The shell increment of the coefficient cutoff -/

open scoped Matrix.Norms.Elementwise in
/-- Every entry of a shell field is `C¹`; the carrier stores continuous first and
second derivatives, so the field is in fact `C²`. -/
theorem contDiff_one_shellField_entry (j : ShellField d) (p q : Fin d) :
    ContDiff ℝ 1 fun x => j x p q :=
  contDiff_pi.mp (contDiff_pi.mp (j.contDiff_two.of_le (by norm_num)) p) q

end

end Algsuperdiff.Section5.Support
