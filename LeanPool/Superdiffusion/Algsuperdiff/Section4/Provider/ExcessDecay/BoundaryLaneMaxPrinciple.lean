/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AffineSplitHarmonic
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.PoincareZeroTrace

/-!
# BoundaryLaneMaxPrinciple

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The weak maximum principle for the Laplacian on the truncated window

The boundary lane's residual corrector `w` (draft item 2(ii)) is controlled by

```text
  ‖w‖_{L^∞(V)} ≤ ‖h - ℓ_h‖_{L^∞(∂V ∩ ∂□_m)} ,
```

which the draft justifies as "the maximum principle for the Laplacian".  This
module proves that step in the weak (`H¹`) formulation:

```text
  v weakly harmonic on V,  (v - M)₊ ∈ H¹₀(V)   ⟹   v ≤ M  a.e. on V ,
```

together with its two-sided form.  The proof is the standard energy argument:
test the harmonicity against the truncation `(v-M)₊`, use the Stampacchia chain
rule `∇(v-M)₊ = 1_{v>M} ∇v` to see that the tested integral is the full Dirichlet
energy of the truncation, conclude that the truncation has vanishing gradient,
and close with the zero-trace Poincaré inequality.

## Why this is the right rendering (and what it costs)

`(v - M)₊ ∈ H¹(V)` with the Stampacchia gradient is **free**: CoarseGraining
proves it for every `H¹` function and every level (`exists_h1_max_sub_const`,
`Homogenization/Sobolev/Truncation/Basic.lean`).  The whole content of the
hypothesis `HasBoundaryUpperBoundOn` is therefore the *zero trace* of the
truncation, which is exactly the weak reading of "`v ≤ M` on `∂V`" — the
standard hypothesis of the weak maximum principle, not a proof step in
disguise.  No pointwise trace operator is used anywhere in this repository, and
none is introduced here.

## What is not done here

The lane still owes:  the *construction* of the corrector `w` with the draft's
boundary data on `∂V ∩ ∂□_m` and `∂V ∩ □_m`, and (b) the verification of
`HasBoundaryUpperBoundOn` for that `w` from the pointwise bound on `h - ℓ_h`
(`AffineSplitLift.abs_sub_affineLift_volumeAverage_le`).

## References

* ABK26, `l.excess.decay.good.scales`.
* CoarseGraining, `Homogenization/Sobolev/Truncation/Basic.lean`
  (`exists_h1_max_sub_const`) and
  `Homogenization/Sobolev/Foundations/PoincareZeroTrace.lean`
  (`H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The weak boundary bound -/

/-- **`u ≤ M` on `∂V`, weakly.**  The positive part `(u - M)₊` lies in `H¹₀(V)`,
carrying CoarseGraining's Stampacchia gradient `1_{u>M} ∇u`.

The `H¹` membership and the gradient formula are unconditional
(`Homogenization.exists_h1_max_sub_const`); the content of this predicate is the
zero trace.  (Given the first component, the second is forced almost everywhere
by uniqueness of weak gradients on an open window; it is bundled so that no
consumer has to rerun that argument, not to strengthen the hypothesis.) -/
def HasBoundaryUpperBoundOn (V : Set (Vec d)) (u : H1Function V) (M : ℝ) : Prop :=
  ∃ ψ : H10Function V,
    ψ.toH1Function.toFun = (fun y => max (u.toFun y - M) 0) ∧
      (∀ᵐ y ∂(volumeMeasureOn V),
        ψ.toH1Function.grad y = {p | M < u.toFun p}.indicator u.grad y)

/-! ## 2. The maximum principle -/

/-- **The weak maximum principle for the Laplacian.**

A weakly harmonic `H¹` function on an open bounded convex window which is `≤ M`
on the boundary (in the zero-trace sense of `HasBoundaryUpperBoundOn`) is `≤ M`
almost everywhere in the window. -/
theorem ae_le_of_isWeaklyHarmonicOn [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {u : H1Function V} {M : ℝ}
    (hu : IsWeaklyHarmonicOn V u) (hM : HasBoundaryUpperBoundOn V u M) :
    ∀ᵐ y ∂(volumeMeasureOn V), u.toFun y ≤ M := by
  obtain ⟨ψ, hψval, hψgrad⟩ := hM
  have hae : ∀ᵐ y ∂(volumeMeasureOn V),
      vecDot (u.grad y) (ψ.toH1Function.grad y) =
        vecNormSq (ψ.toH1Function.grad y) := by
    filter_upwards [hψgrad] with y hy
    by_cases hmem : y ∈ {p | M < u.toFun p}
    · rw [hy, Set.indicator_of_mem hmem, vecNormSq]
    · rw [hy, Set.indicator_of_notMem hmem]
      simp [vecDot, vecNormSq]
  have hzero : ∫ y in V, vecNormSq (ψ.toH1Function.grad y) ∂volume = 0 := by
    rw [← integral_congr_ae hae]
    exact hu ψ
  have hint : Integrable (fun y => vecNormSq (ψ.toH1Function.grad y))
      (volumeMeasureOn V) := by
    have h := integrableOn_vecDot_grad ψ.toH1Function ψ.toH1Function
    simpa [IntegrableOn, volumeMeasureOn, vecNormSq] using h
  have hgz : (fun y => vecNormSq (ψ.toH1Function.grad y)) =ᵐ[volumeMeasureOn V] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun y => vecNormSq_nonneg _) hint).1 hzero
  have hgradzero : ψ.toH1Function.grad =ᵐ[volumeMeasureOn V] 0 := by
    filter_upwards [hgz] with y hy
    refine vecNormSq_eq_zero ?_
    simpa using hy
  have hVL2 : ψ.toH1Function.gradToVectorL2 = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [ψ.toH1Function.coeFn_gradToVectorL2, hgradzero] with y h1 h2
    rw [h1, h2]
  have hS := H10Function.toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant
    (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hV) ψ hVL2
  have hval : ψ.toH1Function.toFun =ᵐ[volumeMeasureOn V] 0 := by
    have hc := ψ.toH1Function.coeFn_toScalarL2
    rw [hS] at hc
    filter_upwards [hc, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volumeMeasureOn V)]
      with y h1 h2
    rw [← h1, h2]
  filter_upwards [hval] with y hy
  have hmax : max (u.toFun y - M) 0 = 0 := by
    rw [← congrFun hψval y]
    simpa using hy
  have hle : u.toFun y - M ≤ 0 := max_eq_right_iff.1 hmax
  linarith only [hle]

/-! ## 3. The two-sided form -/

theorem isWeaklyHarmonicOn_neg {V : Set (Vec d)} {u : H1Function V}
    (hu : IsWeaklyHarmonicOn V u) : IsWeaklyHarmonicOn V (-u) := by
  intro φ
  have hrw : ∀ y, vecDot ((-u).grad y) (φ.toH1Function.grad y) =
      -vecDot (u.grad y) (φ.toH1Function.grad y) := by
    intro y
    simp only [H1Function.neg_grad, vecDot, Pi.neg_apply, neg_mul,
      Finset.sum_neg_distrib]
  calc
    ∫ y in V, vecDot ((-u).grad y) (φ.toH1Function.grad y) ∂volume
        = ∫ y in V, -vecDot (u.grad y) (φ.toH1Function.grad y) ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => hrw y)
    _ = -∫ y in V, vecDot (u.grad y) (φ.toH1Function.grad y) ∂volume := integral_neg _
    _ = 0 := by rw [hu φ, neg_zero]

/-- **The two-sided weak maximum principle.**  This is the display
`‖w‖_{L^∞(V)} ≤ M` of the draft's item 2(ii), with `M` the sup-bound of the
boundary data. -/
theorem ae_abs_le_of_isWeaklyHarmonicOn [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {u : H1Function V} {M : ℝ}
    (hu : IsWeaklyHarmonicOn V u) (hupper : HasBoundaryUpperBoundOn V u M)
    (hlower : HasBoundaryUpperBoundOn V (-u) M) :
    ∀ᵐ y ∂(volumeMeasureOn V), |u.toFun y| ≤ M := by
  have h1 := ae_le_of_isWeaklyHarmonicOn hV hu hupper
  have h2 := ae_le_of_isWeaklyHarmonicOn hV (isWeaklyHarmonicOn_neg hu) hlower
  filter_upwards [h1, h2] with y hy1 hy2
  have hy2' : -u.toFun y ≤ M := by
    simpa using hy2
  exact abs_le.2 ⟨by linarith only [hy2'], hy1⟩

end

end Algsuperdiff.Section4.Provider.ExcessDecay
