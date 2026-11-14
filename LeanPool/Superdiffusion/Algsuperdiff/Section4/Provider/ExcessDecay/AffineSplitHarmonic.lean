/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AffineSplitLift

/-!
# AffineSplitHarmonic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The affine split `v = v₀ + w + ℓ_h` and the harmonicity of its pieces

The replacement draft's item 2 (`l.comparison.reduction`) defines `w` as the
harmonic function carrying the boundary residual and then *sets*
`v₀ := v - w - ℓ_h`, asserting that `v₀` is harmonic "since `ℓ_h` is affine,
hence harmonic".  In the weak (`H¹`) formulation of this repository that
sentence has real content:

```text
  IsWeaklyHarmonicOn V ℓ   ↔   ∀ φ ∈ H¹₀(V),  ∑_i A_i ∫_V ∂_i φ = 0 ,
```

and `∫_V ∂_i φ = 0` for `φ ∈ H¹₀(V)` is a genuine lemma: it is the weak
divergence theorem for zero-trace functions.  This module proves it (from the
weak-gradient identity of the **constant** `H¹` function, applied to the
approximating sequence bundled in `H10Function`, plus the `L²→L¹` passage on
the finite-measure window), derives the harmonicity of affine functions, and
proves the split.

## Main results

* `integral_grad_coord_h10_eq_zero` — `∫_V (∇φ)_i = 0` for `φ ∈ H¹₀(V)`.
* `isWeaklyHarmonicOn_of_grad_const` — a constant gradient is weakly harmonic;
  in particular `isWeaklyHarmonicOn_affineLiftH1` for `ℓ_h`.
* `isWeaklyHarmonicOn_sub` — harmonicity is stable under differences.
* `exists_affineSplit` — the draft's `v = v₀ + w + ℓ_h` with `v₀` harmonic.

## What is not done here

* The **existence** of the residual corrector `w` (the harmonic function with
  data `h - ℓ_h` on `∂V ∩ ∂□_m` and `0` on `∂V ∩ □_m`) is not constructed: `w`
  enters `exists_affineSplit` as a given weakly harmonic `H¹` function, exactly
  as in the draft's proof, which defines `w` by solving that Dirichlet problem.
  Solvability on the truncated window `V = (x+□_{n-2}) ∩ □_m` is a separate,
  priced obligation.
* The boundary conditions (i) and (ii) of the draft's lemma are *not* rendered
  here; only the algebraic/harmonicity half of the split is.  The `L^∞` bound on
  `w` is `BoundaryLaneMaxPrinciple`.

## References

* ABK26, `l.excess.decay.good.scales`.
* CoarseGraining, `Homogenization/Sobolev/H1/Definitions.lean` (the
  `H10Function` approximation package),
  `Homogenization/Sobolev/Foundations/MeanZero.lean` (`H1Function.const`,
  `H1Function.affineOnIsSobolevRegularDomain`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. The weak divergence theorem for `H¹₀` -/

private theorem integrable_approx_deriv {U : Set (Vec d)} (φ : H10Function U)
    (n : ℕ) (i : Fin d) :
    Integrable (fun y => (fderiv ℝ (φ.approx n) y) (basisVec i))
      (volume.restrict U) := by
  have hcont : Continuous fun y => (fderiv ℝ (φ.approx n) y) (basisVec i) :=
    ((φ.approx_smooth n).continuous_fderiv (by simp)).clm_apply
      continuous_const
  have hcs0 : HasCompactSupport (fderiv ℝ (φ.approx n)) :=
    (φ.approx_hasCompactSupport n).fderiv ℝ
  have hcs : HasCompactSupport fun y => (fderiv ℝ (φ.approx n) y) (basisVec i) := by
    refine HasCompactSupport.intro hcs0 fun y hy => ?_
    rw [image_eq_zero_of_notMem_tsupport hy]
    rfl
  exact (hcont.integrable_of_hasCompactSupport hcs).restrict

/-- **The weak divergence theorem for `H¹₀`.**  Each coordinate of the weak
gradient of a zero-trace function integrates to zero over the domain.

The proof tests the weak-gradient identity of the *constant* `H¹` function
against the smooth compactly supported approximants of `φ`, and passes to the
limit through the `L²` convergence of the approximate gradients (the
`H10Function` package's `tendsto_approx_grad`) on the finite-measure window. -/
theorem integral_grad_coord_h10_eq_zero {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (φ : H10Function U) (i : Fin d) :
    ∫ y in U, φ.toH1Function.grad y i ∂volume = 0 := by
  set f : Vec d → ℝ := fun y => φ.toH1Function.grad y i with hfdef
  set F : ℕ → Vec d → ℝ := fun n y => (fderiv ℝ (φ.approx n) y) (basisVec i) with hFdef
  have hzero : ∀ n, ∫ y in U, F n y ∂volume = 0 := by
    intro n
    have hw := (H1Function.const (U := U) (1 : ℝ)).hasWeakGradient i
      (φ.approx n) (φ.approx_smooth n) (φ.approx_hasCompactSupport n)
      (φ.approx_support_subset n)
    simpa [hFdef] using hw
  have hfi : Integrable f (volume.restrict U) := by
    simpa [hfdef, IntegrableOn, volumeMeasureOn] using
      integrableOn_grad_coord (U := U) φ.toH1Function i
  have hFi : ∀ n, Integrable (F n) (volume.restrict U) := fun n =>
    integrable_approx_deriv φ n i
  have hmeas : ∀ n, AEStronglyMeasurable (fun y => F n y - f y) (volume.restrict U) :=
    fun n => (hFi n).1.sub hfi.1
  set cst : ENNReal :=
    ((volume.restrict U) Set.univ) ^
      (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) with hcstdef
  have huniv : (volume.restrict U) Set.univ ≠ ⊤ := measure_ne_top _ _
  have hcoef : cst ≠ ⊤ := by
    rw [hcstdef]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) huniv
  have hbound : ∀ n, ∫⁻ y, ‖F n y - f y‖ₑ ∂(volume.restrict U) ≤
      eLpNorm (fun y => F n y - f y) 2 (volume.restrict U) * cst := by
    intro n
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (p := (1 : ENNReal)) (q := (2 : ENNReal)) (μ := volume.restrict U)
      (f := fun y => F n y - f y) (by norm_num) (hmeas n)
    rwa [eLpNorm_one_eq_lintegral_enorm (hmeas n)] at h
  have hgrad := φ.tendsto_approx_grad i
  have hmul : Tendsto (fun n =>
      eLpNorm (fun y => F n y - f y) 2 (volume.restrict U) * cst) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const hgrad (Or.inr hcoef)
    rw [zero_mul] at h
    exact h
  have hL1 : Tendsto (fun n => ∫⁻ y, ‖F n y - f y‖ₑ ∂(volume.restrict U)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
      (fun n => zero_le) hbound
  have htend := tendsto_integral_of_L1 (μ := volume.restrict U) f hfi.aestronglyMeasurable
    (Eventually.of_forall hFi) hL1
  have hconst : Tendsto (fun n => ∫ y in U, F n y ∂volume) atTop (𝓝 (0 : ℝ)) := by
    simp only [hzero]
    exact tendsto_const_nhds
  exact (tendsto_nhds_unique hconst htend).symm

/-! ## 2. Affine functions are weakly harmonic -/

/-- An `H¹` function with constant weak gradient is weakly harmonic: the tested
integral is a finite combination of the vanishing gradient integrals of the test
function. -/
theorem isWeaklyHarmonicOn_of_grad_const {V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn V)] {u : H1Function V} {A : Vec d}
    (hgrad : ∀ y, u.grad y = A) : IsWeaklyHarmonicOn V u := by
  intro φ
  have hint : ∀ i : Fin d,
      Integrable (fun y => A i * φ.toH1Function.grad y i) (volume.restrict V) := by
    intro i
    have h : Integrable (fun y => φ.toH1Function.grad y i) (volume.restrict V) := by
      simpa [IntegrableOn, volumeMeasureOn] using
        integrableOn_grad_coord (U := V) φ.toH1Function i
    exact h.const_mul (A i)
  have hrw : ∀ y, vecDot (u.grad y) (φ.toH1Function.grad y) =
      ∑ i : Fin d, A i * φ.toH1Function.grad y i := by
    intro y
    rw [hgrad y, vecDot]
  calc
    ∫ y in V, vecDot (u.grad y) (φ.toH1Function.grad y) ∂volume
        = ∫ y in V, ∑ i : Fin d, A i * φ.toH1Function.grad y i ∂volume := by
          exact integral_congr_ae (Eventually.of_forall fun y => hrw y)
    _ = ∑ i : Fin d, ∫ y in V, A i * φ.toH1Function.grad y i ∂volume :=
          integral_finsetSum _ fun i _ => hint i
    _ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [integral_const_mul, integral_grad_coord_h10_eq_zero φ i, mul_zero]

/-- The affine lift `ℓ_h` is weakly harmonic on the window. -/
theorem isWeaklyHarmonicOn_affineLiftH1 {V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn V)] (hV : IsSobolevRegularDomain V)
    (x : Vec d) (c : ℝ) (A : Vec d) :
    IsWeaklyHarmonicOn V (affineLiftH1 hV x c A) :=
  isWeaklyHarmonicOn_of_grad_const (affineLiftH1_grad hV x c A)

/-! ## 3. Harmonicity under differences -/

/-- The tested integrand of the weak Laplacian is integrable: it is a finite sum
of products of `L²` gradient coordinates. -/
theorem integrableOn_vecDot_grad {V : Set (Vec d)} (u φ : H1Function V) :
    IntegrableOn (fun y => vecDot (u.grad y) (φ.grad y)) V volume := by
  have hsum : (fun y => vecDot (u.grad y) (φ.grad y)) =
      fun y => ∑ i : Fin d, (u.grad y i * φ.grad y i) := by
    funext y
    rw [vecDot]
  rw [IntegrableOn, hsum]
  refine integrable_finsetSum _ fun i _ => ?_
  exact (u.gradMemL2 i).integrable_mul (φ.gradMemL2 i)

theorem isWeaklyHarmonicOn_sub {V : Set (Vec d)} {u v : H1Function V}
    (hu : IsWeaklyHarmonicOn V u) (hv : IsWeaklyHarmonicOn V v) :
    IsWeaklyHarmonicOn V (u - v) := by
  intro φ
  have hrw : ∀ y, vecDot ((u - v).grad y) (φ.toH1Function.grad y) =
      vecDot (u.grad y) (φ.toH1Function.grad y) -
        vecDot (v.grad y) (φ.toH1Function.grad y) := by
    intro y
    rw [H1Function.sub_grad, vecDot, vecDot, vecDot, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.sub_apply]
      ring
  calc
    ∫ y in V, vecDot ((u - v).grad y) (φ.toH1Function.grad y) ∂volume
        = ∫ y in V, (vecDot (u.grad y) (φ.toH1Function.grad y) -
            vecDot (v.grad y) (φ.toH1Function.grad y)) ∂volume := by
          exact integral_congr_ae (Eventually.of_forall fun y => hrw y)
    _ = (∫ y in V, vecDot (u.grad y) (φ.toH1Function.grad y) ∂volume) -
          ∫ y in V, vecDot (v.grad y) (φ.toH1Function.grad y) ∂volume :=
          integral_sub (integrableOn_vecDot_grad u φ.toH1Function)
            (integrableOn_vecDot_grad v φ.toH1Function)
    _ = 0 := by rw [hu φ, hv φ, sub_zero]

/-! ## 4. The affine split -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
