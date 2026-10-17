/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellL8
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.TranslatedLargeCubeW1Inf

/-!
# StreamForcingDeriv

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Differentiability and derivative size of the fresh-shell forcing

The forcing of the two corrector problems `e.def.w` is `streamForcing sigmaInv
omega n m e = sigmaInv * (k_m - k_n) e` (`FreshShellL8`).  The
nested-recentring display of `OscillationNestedAssembly` consumes a forcing `G`
through exactly two properties:

* `∀ i, Differentiable ℝ (fun y => G y i)`, and
* `∀ x ∈ (the coarse cube), ∀ i, ‖fderiv ℝ (fun y => G y i) x‖ ≤ M`.

This module supplies both at `G = ± streamForcing`, and converts the second one
into the derivative gauges in which ABK26's `e.W.1.inf.bound` is stated.

## Why differentiability is elementary here

Since the passage from the matrix `A` to the real number `sigmaInv * (A e)_i`
is a *continuous linear* map of `A`, the forcing coordinate is a finite sum of
compositions of continuous linear maps with differentiable maps.

## The gauge conversion, with every factor visible

Two conversion factors meet here and neither is absorbed silently.

* The ambient carrier `Vec d = Fin d -> ℝ` is **sup**-normed, so the operator
  norm `‖fderiv ℝ (fun y => G y i) x‖` is measured against `‖v‖_∞`.  The shell
  derivative gauge `ShellField.matrixDerivativeNorm` is measured against the
  **Euclidean** length `Book.Ch02.vecNorm v`.  Converting the input costs the
  factor `sqrt d` (`vecNorm_le_sqrt_dim_mul_norm`); it is written explicitly in
  every statement below.
* Converting the *output* costs nothing: the single coordinate
  `|(A e)_i| ≤ ‖A e‖_∞ ≤ |A e|_2` (`norm_le_vecNorm`), so the factor is `1`.

The net conversion is thus
`M = sigmaInv * sqrt d * |e|_2 * ∑_{k ∈ (n,m]} ‖∇j_k‖_{L∞(z + cu_ell)}`, the
last factor being the bare sum of local cube derivative gauges.  Pricing that
bare sum against the weighted summand `3^k ‖∇j_k‖_{L∞(cu_l)} + 3^{2k}
‖∇²j_k‖_{L∞(cu_l)}` of `e.W.1.inf.bound`
(`Provider.Stream.largeCubeDerivGauge`) costs a further factor `3^{-(n+1)}`,
the reciprocal of the smallest weight in the range; that step belongs to the
consumer and is not taken here.

## Contents

* `differentiable_streamForcing_coord`, `differentiable_neg_streamForcing_coord`
  -- coordinatewise differentiability of the forcing and of its negative.
* `norm_fderiv_streamForcing_coord_le`,
  `norm_fderiv_neg_streamForcing_coord_le` -- the pointwise differential bound
  in the exact induced shell-derivative gauge.
* `matrixDerivativeNorm_sum_deriv_le_sum_localCubeDerivNorm_translate` -- the
  same gauge read on a translated cube `z + cu_ell`.

## References

* ABK26, `e.def.w`.
* ABK26, `e.nablaw.oscillations`, whose forcing term is the eventual consumer.
* ABK26, `e.W.1.inf.bound`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The coordinate functional of the forcing -/

/-- The map `A ↦ sigmaInv * (A e)_i`, which is linear in the matrix `A`. -/
def streamForcingCoordLinear (sigmaInv : ℝ) (e : Vec d) (i : Fin d) :
    Mat d →ₗ[ℝ] ℝ where
  toFun A := sigmaInv * matVecMul A e i
  map_add' A B := by
    simp only [matVecMul, Matrix.add_apply]
    rw [← mul_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  map_smul' c A := by
    simp only [matVecMul, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- The same map as a continuous linear functional.  The bound used to
manufacture continuity is the crude entrywise one; the sharp bound is proved
separately in `norm_fderiv_streamForcing_coord_le`. -/
def streamForcingCoordCLM (sigmaInv : ℝ) (e : Vec d) (i : Fin d) :
    Mat d →L[ℝ] ℝ :=
  LinearMap.mkContinuous (streamForcingCoordLinear sigmaInv e i)
    (|sigmaInv| * ∑ j, |e j|) (by
      intro A
      have hentry : ∀ j : Fin d, |A i j| ≤ ‖A‖ := fun j => by
        simpa [Real.norm_eq_abs] using!
          (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)
      have hstep : |∑ j, A i j * e j| ≤ ∑ j, ‖A‖ * |e j| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hentry j) (abs_nonneg _)
      have hval : ‖streamForcingCoordLinear sigmaInv e i A‖ =
          |sigmaInv| * |∑ j, A i j * e j| := by
        change |sigmaInv * matVecMul A e i| = _
        rw [abs_mul]
        rfl
      rw [hval, ← Finset.mul_sum] at *
      calc |sigmaInv| * |∑ j, A i j * e j|
          ≤ |sigmaInv| * (‖A‖ * ∑ j, |e j|) :=
            mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
        _ = |sigmaInv| * (∑ j, |e j|) * ‖A‖ := by ring)

private theorem streamForcingCoordCLM_apply (sigmaInv : ℝ) (e : Vec d) (i : Fin d)
    (A : Mat d) :
    streamForcingCoordCLM sigmaInv e i A = sigmaInv * matVecMul A e i :=
  rfl

/-- The finite stream increment, written as the plain finite sum of the shell
values it is. -/
private theorem finiteShellIncrement_eq_sum (omega : Cutoff.ShellSeq d) (n m : ℤ)
    (y : Vec d) :
    (Cutoff.finiteShellIncrement omega n m y : Mat d) =
      ∑ k ∈ Finset.Ioc n m, (omega k) y := by
  rw [Cutoff.finiteShellIncrement_apply]
  rfl

/-- The forcing coordinate has, at every point, the differential obtained by
composing the coordinate functional with the summed shell derivatives. -/
private theorem hasFDerivAt_streamForcing_coord (sigmaInv : ℝ)
    (omega : Cutoff.ShellSeq d) (n m : ℤ) (e : Vec d) (i : Fin d) (x : Vec d) :
    HasFDerivAt (fun y => streamForcing sigmaInv omega n m e y i)
      ((streamForcingCoordCLM sigmaInv e i).comp
        (∑ k ∈ Finset.Ioc n m, ShellField.deriv (omega k) x)) x := by
  have hK : HasFDerivAt (fun y : Vec d => ∑ k ∈ Finset.Ioc n m, (omega k) y)
      (∑ k ∈ Finset.Ioc n m, ShellField.deriv (omega k) x) x :=
    HasFDerivAt.fun_sum fun k _ => (omega k).hasFDerivAt x
  have hfun : (fun y => streamForcing sigmaInv omega n m e y i) =
      fun y : Vec d =>
        streamForcingCoordCLM sigmaInv e i (∑ k ∈ Finset.Ioc n m, (omega k) y) := by
    funext y
    rw [streamForcingCoordCLM_apply, ← finiteShellIncrement_eq_sum]
    rfl
  rw [hfun]
  exact (streamForcingCoordCLM sigmaInv e i).hasFDerivAt.comp x hK

/-! ## (1) Coordinatewise differentiability of the forcing -/

/-- **Coordinatewise differentiability of the fresh-shell forcing.**  Each
coordinate of `sigmaInv (k_m - k_n) e` is differentiable on all of `Vec d`. -/
theorem differentiable_streamForcing_coord (sigmaInv : ℝ)
    (omega : Cutoff.ShellSeq d) (n m : ℤ) (e : Vec d) (i : Fin d) :
    Differentiable ℝ fun y => streamForcing sigmaInv omega n m e y i :=
  fun x => (hasFDerivAt_streamForcing_coord sigmaInv omega n m e i x).differentiableAt

/-- The same for the negated forcing, which is the sign convention in which the
CoarseGraining weak-solution predicates state `- Delta w = div f`. -/
theorem differentiable_neg_streamForcing_coord (sigmaInv : ℝ)
    (omega : Cutoff.ShellSeq d) (n m : ℤ) (e : Vec d) (i : Fin d) :
    Differentiable ℝ fun y => (-streamForcing sigmaInv omega n m e y) i := by
  have h := (differentiable_streamForcing_coord sigmaInv omega n m e i).neg
  exact h

/-! ## (2) The differential bound in the exact shell-derivative gauge -/

/-- **The pointwise differential bound.**  At every point, the differential of
each coordinate of the forcing is bounded, in the ambient sup-operator norm, by
`sigmaInv` times `sqrt d` times the Euclidean length of `e` times the exact
induced norm of the summed shell derivatives.  The factor `sqrt d` is the
sup-to-Euclidean conversion on the *input* of the differential; the output
conversion is free. -/
theorem norm_fderiv_streamForcing_coord_le (sigmaInv : ℝ)
    (omega : Cutoff.ShellSeq d) (n m : ℤ) (e : Vec d) (i : Fin d) (x : Vec d) :
    ‖fderiv ℝ (fun y => streamForcing sigmaInv omega n m e y i) x‖ ≤
      |sigmaInv| * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e *
        ShellField.matrixDerivativeNorm
          (∑ k ∈ Finset.Ioc n m, ShellField.deriv (omega k) x) := by
  set D : ShellField.MatrixDerivative d :=
    ∑ k ∈ Finset.Ioc n m, ShellField.deriv (omega k) x with hD
  rw [(hasFDerivAt_streamForcing_coord sigmaInv omega n m e i x).fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      (Book.Ch02.vecNorm_nonneg e)) (ShellField.matrixDerivativeNorm_nonneg D)
  · intro v
    have hcoord : ‖((streamForcingCoordCLM sigmaInv e i).comp D) v‖ =
        |sigmaInv| * |matVecMul (D v) e i| := by
      change |sigmaInv * matVecMul (D v) e i| = _
      rw [abs_mul]
    have h1 : |matVecMul (D v) e i| ≤ Book.Ch02.vecNorm (matVecMul (D v) e) := by
      have hsup := norm_le_pi_norm (matVecMul (D v) e) i
      have heu := norm_le_vecNorm (matVecMul (D v) e)
      rw [Real.norm_eq_abs] at hsup
      linarith
    have h2 : Book.Ch02.vecNorm (matVecMul (D v) e) ≤
        Book.Ch02.matrixOperatorNorm (D v) * Book.Ch02.vecNorm e :=
      Book.Ch02.vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ _
    have h3 : Book.Ch02.matrixOperatorNorm (D v) ≤
        ShellField.matrixDerivativeNorm D * Book.Ch02.vecNorm v :=
      Provider.Stream.matrixOperatorNorm_apply_le_matrixDerivativeNorm_mul_vecNorm D v
    have h4 : Book.Ch02.vecNorm v ≤ Real.sqrt (d : ℝ) * ‖v‖ :=
      vecNorm_le_sqrt_dim_mul_norm v
    have hDnn : (0 : ℝ) ≤ ShellField.matrixDerivativeNorm D :=
      ShellField.matrixDerivativeNorm_nonneg D
    have henn : (0 : ℝ) ≤ Book.Ch02.vecNorm e := Book.Ch02.vecNorm_nonneg e
    have hchain : |matVecMul (D v) e i| ≤
        ShellField.matrixDerivativeNorm D * (Real.sqrt (d : ℝ) * ‖v‖) *
          Book.Ch02.vecNorm e := by
      refine h1.trans (h2.trans ?_)
      exact mul_le_mul_of_nonneg_right
        (h3.trans (mul_le_mul_of_nonneg_left h4 hDnn)) henn
    rw [hcoord]
    calc |sigmaInv| * |matVecMul (D v) e i|
        ≤ |sigmaInv| * (ShellField.matrixDerivativeNorm D *
            (Real.sqrt (d : ℝ) * ‖v‖) * Book.Ch02.vecNorm e) :=
          mul_le_mul_of_nonneg_left hchain (abs_nonneg _)
      _ = |sigmaInv| * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e *
            ShellField.matrixDerivativeNorm D * ‖v‖ := by ring

/-- The same bound for the negated forcing: negation does not change the size of
a differential. -/
theorem norm_fderiv_neg_streamForcing_coord_le (sigmaInv : ℝ)
    (omega : Cutoff.ShellSeq d) (n m : ℤ) (e : Vec d) (i : Fin d) (x : Vec d) :
    ‖fderiv ℝ (fun y => (-streamForcing sigmaInv omega n m e y) i) x‖ ≤
      |sigmaInv| * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e *
        ShellField.matrixDerivativeNorm
          (∑ k ∈ Finset.Ioc n m, ShellField.deriv (omega k) x) := by
  have hfun : (fun y => (-streamForcing sigmaInv omega n m e y) i) =
      fun y => -(streamForcing sigmaInv omega n m e y i) := rfl
  rw [hfun, fderiv_fun_neg, norm_neg]
  exact norm_fderiv_streamForcing_coord_le sigmaInv omega n m e i x

/-! ## The shell-derivative gauge on a translated cube -/

/-- A point of the translated open cube `z + cu_ell` is a translate of a point
of the origin cube `cu_ell`. -/
private theorem sub_mem_openCubeSet_of_mem_openCubeAtScale {z : Vec d} {ell : ℤ}
    {y : Vec d} (hy : y ∈ openCubeAtScale z ell) :
    y - z ∈ openCubeSet (originCube d ell) := by
  rw [← openCubeAtScale_zero_eq_openCubeSet_originCube]
  rw [openCubeAtScale_eq_translateSet z ell] at hy
  rwa [mem_translateSet_iff_sub_mem] at hy

/-- **`‖∇(k_m - k_n)‖_{L∞(z + cu_ell)}` in the exact induced gauge.**  On the
translated cube `z + cu_ell` the derivative of a finite shell sum is dominated
by the sum of the local cube derivative gauges of the *translated* shells, which
is the carrier of ABK26's `e.W.1.inf.bound` at base point `z`. -/
theorem matrixDerivativeNorm_sum_deriv_le_sum_localCubeDerivNorm_translate
    (ell : ℤ) (s : Finset ℤ) (z : Vec d) (omega : Cutoff.ShellSeq d) {y : Vec d}
    (hy : y ∈ openCubeAtScale z ell) :
    ShellField.matrixDerivativeNorm (∑ k ∈ s, ShellField.deriv (omega k) y) ≤
      ∑ k ∈ s, Provider.Stream.localCubeDerivNorm ell
        (ShellField.translate z (omega k)) := by
  have hbase := Provider.Stream.matrixDerivativeNorm_sum_deriv_le_sum_localCubeDerivNorm
    (d := d) ell s (fun k => ShellField.translate z (omega k))
    (sub_mem_openCubeSet_of_mem_openCubeAtScale hy)
  have hderiv : ∀ k : ℤ,
      ShellField.deriv (ShellField.translate z (omega k)) (y - z) =
        ShellField.deriv (omega k) y := by
    intro k
    rw [ShellField.translate_deriv, sub_add_cancel]
  simp only [hderiv] at hbase
  exact hbase

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
