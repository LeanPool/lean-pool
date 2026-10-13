/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.CoarseGaugeCoeffField
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ

/-!
# CoarseGaugeNullLagrangian

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the constant-skew null Lagrangian, and the shifted harmonic class

The coefficient shift `a |-> a - hbar` of ABK26 is only useful because it does
**not** move the admissible class: for a *constant skew* `hbar` the field `x
|-> hbar grad u (x)` is divergence free in the weak sense, so an `a`-harmonic
function is `(a - hbar)`-harmonic and conversely.  Equivalently,

```
int_U hbar grad u . grad phi = 0   for  u in H^1(U),  phi in H^1_0(U).
```

This is the standard null-Lagrangian cancellation: pairing the constant skew
matrix against the Hessian of a smooth test kills the integrand by the symmetry
of second derivatives, and both sides are `L^2`-continuous in the test.

* `isSolenoidalOn_matVecMul_of_isPotentialOn_of_transpose_eq_neg`, the display
  above, obtained from `Homogenization.IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2`
  by testing against smooth compactly supported functions and integrating by
  parts once in each slot; and
* `isAHarmonicGradient_sub_const_skew`, its consequence for the harmonic class
  of `Homogenization.PDE.Harmonic`.

Only `Homogenization.euclideanCoordSecondDeriv_comm_fun` (symmetry of second
derivatives of a smooth function) and the weak-gradient identity of
`Homogenization.H1Function` are used; no ellipticity enters.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport

variable {d : ℕ}

/-! ## `L²` bookkeeping -/

/-- A constant matrix applied to an `L²` vector field stays in `L²`. -/
theorem memVectorL2_matVecMul_const {U : Set (Vec d)} (H : Mat d)
    {w : Vec d → Vec d} (hw : MemVectorL2 U w) :
    MemVectorL2 U (fun x => matVecMul H (w x)) := by
  refine MeasureTheory.MemLp.of_eval ?_
  intro i
  have hcoord :
      (fun x => matVecMul H (w x) i) = fun x => ∑ j : Fin d, H i j * w x j := rfl
  rw [hcoord]
  exact MeasureTheory.memLp_finsetSum _ fun j _ => (hw.eval j).const_mul (H i j)

/-- An `L²` vector field pairs integrably against every `H^1_0` test gradient. -/
theorem h10FluxIntegrable_of_memVectorL2 {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2 U F) : h10FluxIntegrable U F := by
  intro φ
  have hcoord : ∀ i : Fin d,
      MeasureTheory.IntegrableOn
        (fun x => F x i * φ.toH1Function.grad x i) U := by
    intro i
    simpa [Pi.mul_apply] using!
      (hF.eval i).integrable_mul (φ.toH1Function.gradMemL2 i)
  have hsum :
      (fun x => vecDot (F x) (φ.toH1Function.grad x)) =
        fun x => ∑ i : Fin d, F x i * φ.toH1Function.grad x i := rfl
  rw [hsum]
  exact MeasureTheory.integrable_finsetSum _ fun i _ => hcoord i

/-- Difference of two weakly divergence-free fields with integrable pairings. -/
theorem isSolenoidalOn_sub {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : IsSolenoidalOn U F) (hG : IsSolenoidalOn U G)
    (hFint : h10FluxIntegrable U F) (hGint : h10FluxIntegrable U G) :
    IsSolenoidalOn U (fun x => F x - G x) := by
  intro φ
  have hsplit :
      (fun x => vecDot (F x - G x) (φ.toH1Function.grad x)) =
        fun x => vecDot (F x) (φ.toH1Function.grad x) -
          vecDot (G x) (φ.toH1Function.grad x) := by
    funext x
    rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, sub_eq_add_neg]
  rw [hsplit, MeasureTheory.integral_sub (hFint φ) (hGint φ), hF φ, hG φ, sub_zero]

/-! ## The null Lagrangian -/

/-- Contracting a skew matrix against a symmetric array gives zero. -/
private theorem sum_sum_mul_eq_zero_of_transpose_eq_neg {H : Mat d}
    (hH : matTranspose H = -H) (I : Fin d → Fin d → ℝ)
    (hI : ∀ i j, I i j = I j i) :
    ∑ i : Fin d, ∑ j : Fin d, H i j * I i j = 0 := by
  have hskew : ∀ i j : Fin d, H j i = -H i j := by
    intro i j
    have h := congrFun (congrFun hH i) j
    simpa [matTranspose, Matrix.transpose_apply] using h
  have hswap :
      ∑ i : Fin d, ∑ j : Fin d, H i j * I i j =
        ∑ i : Fin d, ∑ j : Fin d, H j i * I j i :=
    Finset.sum_comm
  have hneg :
      ∑ i : Fin d, ∑ j : Fin d, H j i * I j i =
        -∑ i : Fin d, ∑ j : Fin d, H i j * I i j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hskew i j, hI j i]
    ring
  have hself := hswap.trans hneg
  linarith

/-- The constant-skew null Lagrangian: for constant skew `H` and a potential
field `f = grad u` on `U`, the field `H f` is weakly divergence free on `U`.

This is the exact vanishing that makes the shift `a |-> a - hbar` of ABK26
preserve the admissible class. -/
theorem isSolenoidalOn_matVecMul_of_isPotentialOn_of_transpose_eq_neg
    {U : Set (Vec d)}
    (hU : IsOpen U) {H : Mat d} (hH : matTranspose H = -H)
    {f : Vec d → Vec d} (hf : IsPotentialOn U f) :
    IsSolenoidalOn U (fun x => matVecMul H (f x)) := by
  obtain ⟨u, rfl⟩ := hf
  have hgradL2 : ∀ j : Fin d,
      MeasureTheory.MemLp (fun x => u.grad x j) 2 (volumeMeasureOn U) :=
    fun j => u.gradMemL2 j
  have hmem : MemVectorL2 U (fun x => matVecMul H (u.grad x)) :=
    memVectorL2_matVecMul_const H u.grad_memVectorL2
  refine IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2 hmem hU ?_
  intro ψ hψ hψs hψsub
  have hDcontDiff : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i ψ) :=
    fun i => contDiff_euclideanCoordDeriv hψ i
  have hDsupp : ∀ i : Fin d, HasCompactSupport (euclideanCoordDeriv i ψ) :=
    fun i => hasCompactSupport_euclideanCoordDeriv hψs i
  have hDsub : ∀ i : Fin d, tsupport (euclideanCoordDeriv i ψ) ⊆ U :=
    fun i => (tsupport_euclideanCoordDeriv_subset_tsupport i ψ).trans hψsub
  have hDL2 : ∀ i : Fin d,
      MeasureTheory.MemLp (euclideanCoordDeriv i ψ) 2 (volumeMeasureOn U) :=
    fun i =>
      (((hDcontDiff i).continuous).memLp_of_hasCompactSupport (hDsupp i)).restrict U
  have hInt : ∀ i j : Fin d,
      MeasureTheory.IntegrableOn
        (fun x => u.grad x j * euclideanCoordDeriv i ψ x) U := by
    intro i j
    simpa [Pi.mul_apply] using! (hgradL2 j).integrable_mul (hDL2 i)
  have hpoint : ∀ x : Vec d,
      vecDot (matVecMul H (u.grad x)) (fun i => (fderiv ℝ ψ x) (basisVec i)) =
        ∑ i : Fin d, ∑ j : Fin d,
          H i j * (u.grad x j * euclideanCoordDeriv i ψ x) := by
    intro x
    simp only [vecDot, matVecMul, euclideanCoordDeriv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have hIBP : ∀ i j : Fin d,
      (∫ x in U, u.grad x j * euclideanCoordDeriv i ψ x ∂MeasureTheory.volume) =
        -∫ x in U, u.toFun x * euclideanCoordSecondDeriv i j ψ x
          ∂MeasureTheory.volume := by
    intro i j
    have hweak :
        (∫ x in U, u.toFun x * euclideanCoordSecondDeriv i j ψ x
            ∂MeasureTheory.volume) =
          -∫ x in U, u.grad x j * euclideanCoordDeriv i ψ x
            ∂MeasureTheory.volume :=
      u.hasWeakGradient j (euclideanCoordDeriv i ψ) (hDcontDiff i)
        (hDsupp i) (hDsub i)
    rw [hweak]
    ring
  have hIsymm : ∀ i j : Fin d,
      (∫ x in U, u.grad x j * euclideanCoordDeriv i ψ x ∂MeasureTheory.volume) =
        ∫ x in U, u.grad x i * euclideanCoordDeriv j ψ x ∂MeasureTheory.volume := by
    intro i j
    rw [hIBP i j, hIBP j i, euclideanCoordSecondDeriv_comm_fun hψ i j]
  calc
    (∫ x in U,
        vecDot (matVecMul H (u.grad x)) (fun i => (fderiv ℝ ψ x) (basisVec i))
          ∂MeasureTheory.volume)
        = ∫ x in U,
            (∑ i : Fin d, ∑ j : Fin d,
              H i j * (u.grad x j * euclideanCoordDeriv i ψ x))
              ∂MeasureTheory.volume :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ i : Fin d, ∫ x in U,
            (∑ j : Fin d, H i j * (u.grad x j * euclideanCoordDeriv i ψ x))
              ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_finsetSum _ ?_
          intro i _
          exact MeasureTheory.integrable_finsetSum _
            fun j _ => (hInt i j).const_mul (H i j)
    _ = ∑ i : Fin d, ∑ j : Fin d,
            H i j *
              ∫ x in U, u.grad x j * euclideanCoordDeriv i ψ x
                ∂MeasureTheory.volume := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [MeasureTheory.integral_finsetSum _
            fun j _ => (hInt i j).const_mul (H i j)]
          exact Finset.sum_congr rfl fun j _ =>
            MeasureTheory.integral_const_mul _ _
    _ = 0 :=
        sum_sum_mul_eq_zero_of_transpose_eq_neg hH
          (fun i j => ∫ x in U, u.grad x j * euclideanCoordDeriv i ψ x
            ∂MeasureTheory.volume)
          hIsymm

/-! ## The shifted harmonic class -/

/-- Subtracting a constant skew matrix from the coefficient field does not move
the harmonic class. -/
theorem isAHarmonicGradient_sub_const_skew {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpen U)
    {H : Mat d} (hH : matTranspose H = -H) {c : CoeffField d} {f : Vec d → Vec d}
    (hflux : MemVectorL2 U (fun x => matVecMul (c x) (f x)))
    (hf : IsAHarmonicGradient c U f) :
    IsAHarmonicGradient (fun x => c x - H) U f := by
  obtain ⟨hpot, hsol⟩ := hf
  refine ⟨hpot, ?_⟩
  have hfL2 : MemVectorL2 U f := by
    obtain ⟨u, hu⟩ := hpot
    rw [← hu]
    exact u.grad_memVectorL2
  have hnull : IsSolenoidalOn U (fun x => matVecMul H (f x)) :=
    isSolenoidalOn_matVecMul_of_isPotentialOn_of_transpose_eq_neg hU hH hpot
  have hsub :
      IsSolenoidalOn U (fun x => matVecMul (c x) (f x) - matVecMul H (f x)) :=
    isSolenoidalOn_sub hsol hnull (h10FluxIntegrable_of_memVectorL2 hflux)
      (h10FluxIntegrable_of_memVectorL2 (memVectorL2_matVecMul_const H hfL2))
  have hfun :
      (fun x => matVecMul (c x - H) (f x)) =
        fun x => matVecMul (c x) (f x) - matVecMul H (f x) := by
    funext x
    rw [sub_matVecMul]
  rw [hfun]
  exact hsub

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
