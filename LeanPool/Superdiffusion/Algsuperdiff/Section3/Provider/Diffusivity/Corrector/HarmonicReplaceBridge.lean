/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicWeak
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.BasicLemmas
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2

/-!
# HarmonicReplaceBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# From variational to distributional harmonicity

CoarseGraining carries harmonicity only in the *variational* form: a function
whose weak gradient is `L^2`-orthogonal to the gradients of all `H^1_0`
competitors, i.e. the Euler-Lagrange identity `int_U <grad h, grad psi> = 0`.
`HarmonicWeak` carries the *distributional* form `int_U h (Delta psi) = 0` for
smooth compactly supported `psi`.  Nothing in either repository connects the
two, and the harmonic layer downstream (mean value property, Weyl lemma,
interior gradient decay) is stated exclusively for the distributional
predicate.

This module supplies the missing bridge.  The proof is one integration by parts
*in the weak sense*: the defining identity of the weak partial derivative is
applied with the test function `d_i psi` in the direction `i`, which converts
`int_U h (d_i d_i psi)` into `- int_U (grad h)_i (d_i psi)`; summing over `i`
turns the Green pairing against `Delta psi` into minus the Dirichlet pairing
against `grad psi`, which is the hypothesis.  No regularity of `h` beyond `H^1`
is used, and no boundary term appears because the test function is compactly
supported inside `U`.

The test-class mismatch that this bridge has to absorb is real: the variational
identity quantifies over `H10Function U`, whereas the distributional predicate
quantifies over smooth compactly supported functions.  The two are reconciled
by CoarseGraining's `H10Function.ofContDiff`, whose weak gradient is the
pointwise Euclidean gradient by definitional unfolding.

## Contents

* `integrableOn_mul_of_memL2On_of_continuous_hasCompactSupport` -- the pairing of
  an `L^2` function on `U` with a continuous compactly supported function is
  integrable on `U`.
* `isWeaklyHarmonicOn_of_forall_contDiff_integral_vecDot_grad_eq_zero` -- **the
  bridge**, with the hypothesis quantified over smooth compactly supported test
  functions.
* `isWeaklyHarmonicOn_of_forall_h10Function_integral_vecDot_grad_eq_zero` -- the
  form actually produced by an `H^1_0` solve, quantified over `H10Function U`.

## Portability

This file depends only on **Mathlib**, on **CoarseGraining**
(`Homogenization.*`) and on the harmonic layer of this same directory.  It
mentions no object of the manuscript: no model, no cutoff, no shell, no
corrector, no `sigmaBar`.  It is intended to be portable into CoarseGraining by
a single mechanical namespace rename.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

variable {d : ℕ}

/-- An `L^2(U)` function paired with a continuous compactly supported function is
integrable on `U`: the second factor lies in `L^2(U)` because its square is
bounded and supported in a compact set. -/
theorem integrableOn_mul_of_memL2On_of_continuous_hasCompactSupport {U : Set (Vec d)}
    {u g : Vec d → ℝ} (hu : MemL2On U u) (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    IntegrableOn (fun x => u x * g x) U volume := by
  have hgL2 : MemL2On U g :=
    (hg.memLp_of_hasCompactSupport (μ := (volume : Measure (Vec d))) (p := 2) hgc).restrict U
  exact hu.integrable_mul hgL2

/-- **The variational-to-distributional bridge.**

If the weak gradient of an `H^1(U)` function is `L^2`-orthogonal on `U` to the
Euclidean gradient of every smooth compactly supported test function supported in
`U`, then the function is weakly harmonic on `U` in the distributional sense of
`HarmonicWeak`.

The proof applies the defining identity of the `i`-th weak partial derivative to
the test function `d_i psi`, sums over `i`, and reads off the hypothesis. -/
theorem isWeaklyHarmonicOn_of_forall_contDiff_integral_vecDot_grad_eq_zero
    {U : Set (Vec d)} (h : H1Function U)
    (hzero : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      ∫ x in U, vecDot (h.grad x) (euclideanGradient ψ x) ∂volume = 0) :
    IsWeaklyHarmonicOn U h.toFun := by
  intro ψ hψ hψc hsupp
  have hdψ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i ψ) :=
    fun i => contDiff_euclideanCoordDeriv hψ i
  have hdψc : ∀ i : Fin d, HasCompactSupport (euclideanCoordDeriv i ψ) :=
    fun i => hasCompactSupport_euclideanCoordDeriv hψc i
  have hdψs : ∀ i : Fin d, tsupport (euclideanCoordDeriv i ψ) ⊆ U :=
    fun i => (tsupport_euclideanCoordDeriv_subset_tsupport i ψ).trans hsupp
  have hddψ : ∀ i : Fin d, Continuous (euclideanCoordSecondDeriv i i ψ) := by
    intro i
    exact ((contDiff_euclideanCoordDeriv (hdψ i) i).continuous)
  have hddψc : ∀ i : Fin d, HasCompactSupport (euclideanCoordSecondDeriv i i ψ) :=
    fun i => hasCompactSupport_euclideanCoordDeriv (hdψc i) i
  -- integrability of the two families of scalar pairings
  have hintL : ∀ i : Fin d,
      IntegrableOn (fun x => h.toFun x * euclideanCoordSecondDeriv i i ψ x) U volume :=
    fun i => integrableOn_mul_of_memL2On_of_continuous_hasCompactSupport
      h.memL2 (hddψ i) (hddψc i)
  have hintR : ∀ i : Fin d,
      IntegrableOn (fun x => h.grad x i * euclideanCoordDeriv i ψ x) U volume :=
    fun i => integrableOn_mul_of_memL2On_of_continuous_hasCompactSupport
      (h.grad_memL2 i) (hdψ i).continuous (hdψc i)
  -- the weak integration by parts, one coordinate at a time
  have key : ∀ i : Fin d,
      ∫ x in U, h.toFun x * euclideanCoordSecondDeriv i i ψ x ∂volume =
        -∫ x in U, h.grad x i * euclideanCoordDeriv i ψ x ∂volume := fun i =>
    h.hasWeakGradient i (euclideanCoordDeriv i ψ) (hdψ i) (hdψc i) (hdψs i)
  have hsplitL :
      ∫ x in U, h.toFun x * euclideanCoordLaplacian ψ x ∂volume =
        ∑ i : Fin d, ∫ x in U, h.toFun x * euclideanCoordSecondDeriv i i ψ x ∂volume := by
    have hpt : ∀ x : Vec d, h.toFun x * euclideanCoordLaplacian ψ x =
        ∑ i : Fin d, h.toFun x * euclideanCoordSecondDeriv i i ψ x := by
      intro x
      rw [euclideanCoordLaplacian, Finset.mul_sum]
    simp only [hpt]
    exact integral_finsetSum Finset.univ fun i _ => hintL i
  have hsplitR :
      ∫ x in U, vecDot (h.grad x) (euclideanGradient ψ x) ∂volume =
        ∑ i : Fin d, ∫ x in U, h.grad x i * euclideanCoordDeriv i ψ x ∂volume := by
    have hpt : ∀ x : Vec d, vecDot (h.grad x) (euclideanGradient ψ x) =
        ∑ i : Fin d, h.grad x i * euclideanCoordDeriv i ψ x := fun _ => rfl
    simp only [hpt]
    exact integral_finsetSum Finset.univ fun i _ => hintR i
  calc ∫ x in U, h.toFun x * euclideanCoordLaplacian ψ x ∂volume
      = ∑ i : Fin d, ∫ x in U, h.toFun x * euclideanCoordSecondDeriv i i ψ x ∂volume :=
        hsplitL
    _ = ∑ i : Fin d, -∫ x in U, h.grad x i * euclideanCoordDeriv i ψ x ∂volume :=
        Finset.sum_congr rfl fun i _ => key i
    _ = -∑ i : Fin d, ∫ x in U, h.grad x i * euclideanCoordDeriv i ψ x ∂volume :=
        Finset.sum_neg_distrib _
    _ = -∫ x in U, vecDot (h.grad x) (euclideanGradient ψ x) ∂volume := by rw [hsplitR]
    _ = 0 := by rw [hzero ψ hψ hψc hsupp, neg_zero]

/-- **The bridge in the form produced by an `H^1_0` solve.**

The Euler-Lagrange identity of a Dirichlet problem is stated against
`H10Function U` competitors.  Restricting it to the competitors
`H10Function.ofContDiff` built from smooth compactly supported test functions --
whose weak gradient is the pointwise Euclidean gradient -- gives the hypothesis
of the previous theorem. -/
theorem isWeaklyHarmonicOn_of_forall_h10Function_integral_vecDot_grad_eq_zero
    {U : Set (Vec d)} (hU : IsOpen U) (h : H1Function U)
    (hzero : ∀ φ : H10Function U,
      ∫ x in U, vecDot (h.grad x) (φ.toH1Function.grad x) ∂volume = 0) :
    IsWeaklyHarmonicOn U h.toFun := by
  refine isWeaklyHarmonicOn_of_forall_contDiff_integral_vecDot_grad_eq_zero h ?_
  intro ψ hψ hψc hsupp
  exact hzero (H10Function.ofContDiff hU hψ hψc hsupp)

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
