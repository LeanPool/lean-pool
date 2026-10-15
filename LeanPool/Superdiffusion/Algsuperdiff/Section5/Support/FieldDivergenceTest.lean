/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.BasicLemmas
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2

/-!
# FieldDivergenceTest

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Integrating a `C¹` vector field by parts against a zero-trace Sobolev function

Two of the Section 5.2 computations pair a classical vector field with the
gradient of a Sobolev function of zero trace: the datum `g(x) = x_1 e_1`, whose
divergence is the constant `1`, and the gradient of a smooth barrier, whose
divergence is its Laplacian.  Both are instances of one identity,

```text
  ∫_U F · ∇φ = - ∫_U (∇·F) φ ,   F ∈ C¹ ,  φ ∈ H¹₀(U) ,
```

on a bounded measurable set `U`.  Against a *smooth compactly supported* test
function the identity is the defining property of the weak partial derivatives
of the components of `F`; the passage to a zero-trace Sobolev test function is
the `L²` limit along the approximating sequence carried by `H¹₀`.

## Main definitions

* `matFieldDiv k` — the matrix-field divergence, contracting its first index.
* `vecFieldDiv F` — the divergence `(∇·F)(x) = ∑_i ∂_i F_i(x)` of a vector
  field, contracting the index of the field against the direction of
  differentiation.

## Main results

* `integral_vecDot_h10Grad_eq_neg_integral_vecFieldDiv_mul` — the identity
  above.

## References

* ABK26, the exit-time comparison of Section 5.2.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The divergence of a matrix field**, contracting the *first* index:

```text
  (∇ · k)_j (x) = ∑_i ∂_i k_{i j}(x) .
```

This is the contraction that sends `a ∇u` to `∇ · a ∇u`, and the one under which
the manuscript's antisymmetry display has the printed signs. -/
def matFieldDiv (k : Vec d → Mat d) : Vec d → Vec d :=
  fun x j => ∑ i : Fin d, euclideanCoordDeriv i (fun y => k y i j) x

/-- The defining coordinate formula of `matFieldDiv`. -/
theorem matFieldDiv_apply (k : Vec d → Mat d) (x : Vec d) (j : Fin d) :
    matFieldDiv k x j = ∑ i : Fin d, euclideanCoordDeriv i (fun y => k y i j) x :=
  rfl

/-- Each coordinate of the divergence of a `C¹` matrix field is continuous. -/
theorem continuous_matFieldDiv_apply {k : Vec d → Mat d}
    (hk : ∀ a b : Fin d, ContDiff ℝ 1 fun x => k x a b) (j : Fin d) :
    Continuous fun x => matFieldDiv k x j := by
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((hk i j).continuous_fderiv (by simp)).clm_apply continuous_const

/-- **The divergence of a vector field**, `(∇·F)(x) = ∑_i ∂_i F_i(x)`. -/
def vecFieldDiv (F : Vec d → Vec d) : Vec d → ℝ :=
  fun x => ∑ i : Fin d, (fderiv ℝ (fun z => F z i) x) (basisVec i)

theorem vecFieldDiv_apply (F : Vec d → Vec d) (x : Vec d) :
    vecFieldDiv F x = ∑ i : Fin d, (fderiv ℝ (fun z => F z i) x) (basisVec i) :=
  rfl

/-! ## 1. Square integrability on a bounded set -/

/-- A continuous function is bounded on a bounded domain. -/
theorem exists_bound_of_continuous {U : Set (Vec d)} (hU : IsBoundedDomain U)
    {f : Vec d → ℝ} (hf : Continuous f) : ∃ C : ℝ, ∀ x ∈ U, |f x| ≤ C := by
  have hclos : IsCompact (closure U) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hU.isBounded.closure
  obtain ⟨C, hC⟩ := hclos.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun x hx => by simpa only [Real.norm_eq_abs] using hC x (subset_closure hx)⟩

/-- A continuous function is square integrable on a bounded measurable set. -/
theorem memScalarL2_of_continuous_of_isBoundedDomain {U : Set (Vec d)}
    (hUm : MeasurableSet U) (hU : IsBoundedDomain U) {f : Vec d → ℝ} (hf : Continuous f) :
    MemScalarL2 U f := by
  have := hU.isFiniteMeasure_restrict_volume
  obtain ⟨C, hC⟩ := exists_bound_of_continuous hU hf
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem hUm] with x hx
  simpa only [Real.norm_eq_abs] using hC x hx

/-- A continuous compactly supported function is square integrable on any set. -/
theorem memScalarL2_of_continuous_hasCompactSupport {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) : MemScalarL2 U f := by
  simpa only [MemScalarL2, volumeMeasureOn] using
    (hf.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞)) hfc).restrict U

/-- The product of two square-integrable scalar fields is integrable. -/
theorem integrable_mul_of_memScalarL2 {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemScalarL2 U f) (hg : MemScalarL2 U g) :
    Integrable (fun x => f x * g x) (volume.restrict U) := by
  simpa only [Pi.mul_apply] using! hf.integrable_mul hg

/-- The integral of an L² dot product is the sum of its coordinate integrals. -/
theorem integral_vecDot_eq_sum_coord {U : Set (Vec d)} {P G : Vec d → Vec d}
    (hP : ∀ i : Fin d, MemScalarL2 U fun x => P x i)
    (hG : ∀ i : Fin d, MemScalarL2 U fun x => G x i) :
    ∫ x in U, vecDot (P x) (G x) ∂volume =
      ∑ i : Fin d, ∫ x in U, P x i * G x i ∂volume := by
  rw [show (fun x : Vec d => vecDot (P x) (G x)) =
      fun x : Vec d => ∑ i : Fin d, P x i * G x i from funext fun _ => rfl]
  exact integral_finsetSum Finset.univ fun i _ => integrable_mul_of_memScalarL2 (hP i) (hG i)

/-! ## 2. The integration by parts -/

/-- **A `C¹` vector field integrates by parts against a zero-trace Sobolev
function**: `∫_U F·∇φ = -∫_U (∇·F) φ`. -/
theorem integral_vecDot_h10Grad_eq_neg_integral_vecFieldDiv_mul {U : Set (Vec d)}
    (hUm : MeasurableSet U) (hU : IsBoundedDomain U)
    {F : Vec d → Vec d} (hF : ∀ i : Fin d, ContDiff ℝ 1 fun z => F z i)
    (phi : H10Function U) :
    ∫ x in U, vecDot (F x) (phi.toH1Function.grad x) ∂volume =
      -∫ x in U, vecFieldDiv F x * phi.toH1Function.toFun x ∂volume := by
  classical
  have hFL2 : ∀ i : Fin d, MemScalarL2 U fun x => F x i := fun i =>
    memScalarL2_of_continuous_of_isBoundedDomain hUm hU (hF i).continuous
  have hDcont : ∀ i : Fin d,
      Continuous fun x => (fderiv ℝ (fun z => F z i) x) (basisVec i) := fun i =>
    ((hF i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hDL2 : ∀ i : Fin d,
      MemScalarL2 U fun x => (fderiv ℝ (fun z => F z i) x) (basisVec i) := fun i =>
    memScalarL2_of_continuous_of_isBoundedDomain hUm hU (hDcont i)
  have hdivL2 : MemScalarL2 U (vecFieldDiv F) :=
    memScalarL2_of_continuous_of_isBoundedDomain hUm hU
      (continuous_finsetSum Finset.univ fun i _ => hDcont i)
  set Dn : ℕ → Vec d → Vec d := fun n => euclideanGradient (phi.approx n) with hDn_def
  have hDnL2 : ∀ (n : ℕ) (i : Fin d), MemScalarL2 U fun x => Dn n x i := by
    intro n i
    exact memScalarL2_coord_of_memVectorL2
      (memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport
        (phi.approx_smooth n) (phi.approx_hasCompactSupport n)) i
  have hglim : ∀ i : Fin d, MemScalarL2 U fun x => phi.toH1Function.grad x i := fun i =>
    phi.toH1Function.gradMemL2 i
  have hthetaL2 : ∀ n : ℕ, MemScalarL2 U (phi.approx n) := fun n =>
    memScalarL2_of_continuous_hasCompactSupport (phi.approx_smooth n).continuous
      (phi.approx_hasCompactSupport n)
  -- the identity along the approximating sequence
  have hsmooth : ∀ n : ℕ, (∑ i : Fin d, ∫ x in U, F x i * Dn n x i ∂volume) =
      -∫ x in U, vecFieldDiv F x * phi.approx n x ∂volume := by
    intro n
    have hstep : ∀ i : Fin d, ∫ x in U, F x i * Dn n x i ∂volume =
        -∫ x in U, (fderiv ℝ (fun z => F z i) x) (basisVec i) * phi.approx n x ∂volume := by
      intro i
      exact HasWeakPartialDerivOn.of_contDiff (hF i) (phi.approx n) (phi.approx_smooth n)
        (phi.approx_hasCompactSupport n) (phi.approx_support_subset n)
    have hsum : ∫ x in U, vecFieldDiv F x * phi.approx n x ∂volume =
        ∑ i : Fin d,
          ∫ x in U, (fderiv ℝ (fun z => F z i) x) (basisVec i) * phi.approx n x ∂volume := by
      rw [show (fun x : Vec d => vecFieldDiv F x * phi.approx n x) =
          fun x : Vec d => ∑ i : Fin d,
            (fderiv ℝ (fun z => F z i) x) (basisVec i) * phi.approx n x from
        funext fun x => by rw [vecFieldDiv_apply, Finset.sum_mul]]
      exact integral_finsetSum Finset.univ fun i _ =>
        integrable_mul_of_memScalarL2 (hDL2 i) (hthetaL2 n)
    rw [Finset.sum_congr rfl fun i _ => hstep i, hsum, Finset.sum_neg_distrib]
  -- the two limits
  have hconv : ∀ i : Fin d,
      Filter.Tendsto (fun n => toScalarL2 (hDnL2 n i)) Filter.atTop
        (nhds (toScalarL2 (hglim i))) := by
    intro i
    refine tendsto_toScalarL2_of_tendsto_eLpNorm (fun n => hDnL2 n i) (hglim i) ?_
    simpa only [hDn_def, euclideanGradient, euclideanCoordDeriv, volumeMeasureOn]
      using phi.tendsto_approx_grad i
  have hconv0 : Filter.Tendsto (fun n => toScalarL2 (hthetaL2 n)) Filter.atTop
      (nhds (toScalarL2 phi.toH1Function.memL2)) := by
    refine tendsto_toScalarL2_of_tendsto_eLpNorm hthetaL2 phi.toH1Function.memL2 ?_
    simpa only [volumeMeasureOn] using phi.tendsto_approx
  have hL : Filter.Tendsto (fun n => ∑ i : Fin d, ∫ x in U, F x i * Dn n x i ∂volume)
      Filter.atTop
      (nhds (∑ i : Fin d, ∫ x in U, F x i * phi.toH1Function.grad x i ∂volume)) :=
    tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_integral_mul_of_tendsto_toScalarL2 (hFL2 i) (fun n => hDnL2 n i) (hglim i)
        (hconv i)
  have hR : Filter.Tendsto (fun n => -∫ x in U, vecFieldDiv F x * phi.approx n x ∂volume)
      Filter.atTop
      (nhds (-∫ x in U, vecFieldDiv F x * phi.toH1Function.toFun x ∂volume)) :=
    (tendsto_integral_mul_of_tendsto_toScalarL2 hdivL2 hthetaL2
      phi.toH1Function.memL2 hconv0).neg
  rw [integral_vecDot_eq_sum_coord hFL2 hglim]
  exact tendsto_nhds_unique (hL.congr' (Filter.EventuallyEq.of_eq (funext hsmooth))) hR

end

end Algsuperdiff.Section5.Support
