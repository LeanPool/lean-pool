/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderLapTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.PoincareMeanZero

/-!
# OneStepSchauderWeyl

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Weyl's lemma by mollification (Weyl, part 2)

The competitor of the Schauder gradient-Hölder estimate is produced as an `H1Function W`
satisfying the variational condition `Support.IsWeaklyHarmonicOn`.  This module
proves that **every CoarseGraining convex smoothing of such a function is
classically harmonic on the interior ball**:

* `isWeaklyHarmonicOn_test_of_contDiff` — instantiate the `H¹₀` quantifier at a
  smooth compactly supported test;
* `isWeaklyHarmonicOn_integral_mul_euclideanCoordLaplacian_eq_zero` — the
  distributional form `∫_U u · Δψ = 0`, obtained by moving the remaining
  derivative off the gradient, one coordinate at a time;
* `euclideanCoordLaplacian_convolution_indicator_eq_zero` — hence the mollified
  function has vanishing coordinate Laplacian wherever the reflected kernel
  support stays inside `U`;
* `contDiff_convexApproxSmoothH1`,
  `euclideanCoordLaplacian_convexApproxSmoothH1_eq_zero`,
  `harmonicOnNhd_convexApproxSmoothH1_of_weaklyHarmonic` — the same for
  CoarseGraining's concrete convex smoothing `H1Function.convexApproxSmoothH1`,
  transported across `toEuc` into Mathlib's `HarmonicOnNhd` **at the full
  radius `r`**.

## Why the radius is not lost

The mollifier kernel `scaledConvexApproxKernel ρ (ε r)` is supported in the
sup-metric ball `closedBall 0 (ε r)`, and the convex smoothing evaluates the
convolution at the contracted point `(1-ε) • y + ε • x₀`, within sup-distance
`(1-ε) r` of `x₀`.  The two contributions add to exactly `r`, so no inner/outer
radius pair is needed; and the Euclidean ball is contained in the sup ball, so
the `HarmonicOnNhd` conclusion holds on `Metric.ball (toEuc x₀) r`.
-/

-- ==== Weyl: the weak Laplacian ====
open MeasureTheory
open HCPolySupport (Vec basisVec vecDot H1Function H10Function euclideanGradient
  euclideanCoordDeriv euclideanCoordSecondDeriv euclideanCoordLaplacian)

open Algsuperdiff.Section4.Support (IsWeaklyHarmonicOn)

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-- **Unpack weak harmonicity at a smooth compactly supported test function.**  The `H¹₀` quantifier
in `IsWeaklyHarmonicOn` is instantiated at `Homogenization.H10Function.ofContDiff φ`. -/
theorem isWeaklyHarmonicOn_test_of_contDiff {U : Set (Vec d)} (hUopen : IsOpen U)
    {u : H1Function U} (hu : IsWeaklyHarmonicOn U u)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U) :
    ∫ x in U, vecDot (u.grad x) (euclideanGradient φ x) ∂volume = 0 := by
  simpa [HCPolySupport.H10Function.ofContDiff, HCPolySupport.H1Function.ofContDiff,
    HCPolySupport.euclideanGradient, HCPolySupport.euclideanCoordDeriv] using!
    hu (HCPolySupport.H10Function.ofContDiff hUopen hφ hφ_supp hφ_sub)

/-- **Weakly harmonic `H¹` functions annihilate compactly supported Laplacian tests.**

`∫_U u · Δψ = 0` for smooth `ψ` with compact support inside `U`.  This is the distributional
(`−Δu = 0`) reading of the variational condition, and it is the form consumed by the convolution
harmonicity argument.

Proof: for each coordinate `i`, the weak derivative identity of `u` applied to the test function
`∂ᵢψ` (still smooth, still compactly supported inside `U`) gives
`∫_U u ∂ᵢ∂ᵢψ = -∫_U (∂ᵢu) (∂ᵢψ)`; summing over `i` turns the right-hand side into
`-∫_U ∇u · ∇ψ`, which vanishes by weak harmonicity. -/
theorem isWeaklyHarmonicOn_integral_mul_euclideanCoordLaplacian_eq_zero {U : Set (Vec d)}
    (hUopen : IsOpen U) {u : H1Function U} (hu : IsWeaklyHarmonicOn U u)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (hψ_sub : tsupport ψ ⊆ U) :
    ∫ x in U, u x * euclideanCoordLaplacian ψ x ∂volume = 0 := by
  classical
  have hgrad_zero :
      ∫ x in U, vecDot (u.grad x) (euclideanGradient ψ x) ∂volume = 0 :=
    isWeaklyHarmonicOn_test_of_contDiff hUopen hu hψ hψ_supp hψ_sub
  -- one integration by parts per coordinate, against the test `∂ᵢψ`
  have hcomp : ∀ i : Fin d,
      ∫ x in U, u x * euclideanCoordSecondDeriv i i ψ x ∂volume =
        -∫ x in U, u.grad x i * euclideanCoordDeriv i ψ x ∂volume := by
    intro i
    have hDψ_sub : tsupport (euclideanCoordDeriv i ψ) ⊆ U :=
      (HCPolySupport.tsupport_euclideanCoordDeriv_subset_tsupport i ψ).trans hψ_sub
    simpa [HCPolySupport.euclideanCoordSecondDeriv, HCPolySupport.euclideanCoordDeriv] using
      u.hasWeakPartialDerivOn i (euclideanCoordDeriv i ψ)
        (HCPolySupport.contDiff_euclideanCoordDeriv hψ i)
        (HCPolySupport.hasCompactSupport_euclideanCoordDeriv hψ_supp i) hDψ_sub
  -- integrability of the two families of products
  have hleftInt : ∀ i : Fin d,
      Integrable (fun x : Vec d => u x * euclideanCoordSecondDeriv i i ψ x)
        (volume.restrict U) := by
    intro i
    have hsecond_mem :
        MemLp (euclideanCoordSecondDeriv i i ψ) 2 (volume.restrict U) :=
      (((HCPolySupport.contDiff_euclideanCoordSecondDeriv hψ i
            i).continuous).memLp_of_hasCompactSupport
        (HCPolySupport.hasCompactSupport_euclideanCoordSecondDeriv hψ_supp i i)).restrict U
    simpa [MeasureTheory.IntegrableOn] using! u.memL2.integrable_mul hsecond_mem
  have hrightInt : ∀ i : Fin d,
      Integrable (fun x : Vec d => u.grad x i * euclideanCoordDeriv i ψ x)
        (volume.restrict U) := by
    intro i
    have hderiv_mem : MemLp (euclideanCoordDeriv i ψ) 2 (volume.restrict U) :=
      (((HCPolySupport.contDiff_euclideanCoordDeriv hψ i).continuous).memLp_of_hasCompactSupport
        (HCPolySupport.hasCompactSupport_euclideanCoordDeriv hψ_supp i)).restrict U
    simpa [MeasureTheory.IntegrableOn] using! (u.grad_memL2 i).integrable_mul hderiv_mem
  calc
    ∫ x in U, u x * euclideanCoordLaplacian ψ x ∂volume
        = ∫ x in U, ∑ i : Fin d, u x * euclideanCoordSecondDeriv i i ψ x ∂volume := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          simp [HCPolySupport.euclideanCoordLaplacian, Finset.mul_sum]
    _ = ∑ i : Fin d, ∫ x in U, u x * euclideanCoordSecondDeriv i i ψ x ∂volume :=
          MeasureTheory.integral_finsetSum Finset.univ fun i _ => hleftInt i
    _ = ∑ i : Fin d, -∫ x in U, u.grad x i * euclideanCoordDeriv i ψ x ∂volume :=
          Finset.sum_congr rfl fun i _ => hcomp i
    _ = -∑ i : Fin d, ∫ x in U, u.grad x i * euclideanCoordDeriv i ψ x ∂volume := by
          rw [Finset.sum_neg_distrib]
    _ = -∫ x in U, ∑ i : Fin d, u.grad x i * euclideanCoordDeriv i ψ x ∂volume := by
          rw [MeasureTheory.integral_finsetSum Finset.univ fun i _ => hrightInt i]
    _ = -∫ x in U, vecDot (u.grad x) (euclideanGradient ψ x) ∂volume := rfl
    _ = 0 := by rw [hgrad_zero, neg_zero]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== Weyl: mollification ====
open scoped Convolution
open MeasureTheory InnerProductSpace
open HCPolySupport (Vec H1Function IsConvexApproxKernel IsOpenBoundedConvexDomain
  scaledConvexApproxKernel convexApproxSmoothRepresentative unitConvexApproxKernel
  unitConvexApproxScale euclideanCoordLaplacian)

open Algsuperdiff.Section4.Support (IsWeaklyHarmonicOn)

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ### Support geometry of the scaled mollifier -/

/-! ### The convolution harmonicity core -/

/-- **The mollified weakly harmonic function has vanishing Laplacian.**  If the *reflected* kernel
`y ↦ K (A - y)` is supported inside `U` and `u` is weakly harmonic on `U`, then the coordinate
Laplacian of the convolution `K ⋆ (𝟙_U u)` vanishes at `A`.

Proof: the Laplacian passes onto the kernel (`euclideanCoordLaplacian_convolution_left`); a change
of variables (`integral_mul_indicator_const_sub_eq_setIntegral`) turns the resulting global integral
into the pairing `∫_U u · Δψ` with `ψ y = K (A - y)`; and the point reflection leaves the Laplacian
invariant (`euclideanCoordLaplacian_comp_const_sub`), so the pairing vanishes by
`IsWeaklyHarmonicOn.integral_mul_euclideanCoordLaplacian_eq_zero`. -/
theorem euclideanCoordLaplacian_convolution_indicator_eq_zero {U : Set (Vec d)}
    (hUopen : IsOpen U) {u : H1Function U} (hu : IsWeaklyHarmonicOn U u)
    {K : Vec d → ℝ} (hK_supp : HasCompactSupport K) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (A : Vec d)
    (hsub : tsupport (fun y : Vec d => K (A - y)) ⊆ U) :
    euclideanCoordLaplacian
        (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Set.indicator U u.toFun) A = 0 := by
  have hUm : MeasurableSet U := hUopen.measurableSet
  have hmem_indicator : MemLp (Set.indicator U u.toFun) 2 volume := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hUm]
    exact u.memL2
  have hloc_indicator : LocallyIntegrable (Set.indicator U u.toFun) volume :=
    hmem_indicator.locallyIntegrable (by norm_num)
  set ψ : Vec d → ℝ := fun y => K (A - y) with hψdef
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hK.comp (contDiff_const.sub contDiff_id)
  have hψ_supp : HasCompactSupport ψ := by
    show HasCompactSupport (K ∘ Homeomorph.subLeft A)
    simpa [ψ, Function.comp_def] using hK_supp.comp_homeomorph (Homeomorph.subLeft A)
  have hweak_zero : ∫ y in U, u y * euclideanCoordLaplacian ψ y ∂volume = 0 :=
    isWeaklyHarmonicOn_integral_mul_euclideanCoordLaplacian_eq_zero hUopen hu hψ hψ_supp hsub
  have hweak_zero' : ∫ y in U, u y * euclideanCoordLaplacian K (A - y) ∂volume = 0 := by
    refine Eq.trans ?_ hweak_zero
    refine MeasureTheory.setIntegral_congr_fun hUm fun y _ => ?_
    congr 1
    exact (euclideanCoordLaplacian_comp_const_sub hK A y).symm
  rw [euclideanCoordLaplacian_convolution_left hK_supp hK hloc_indicator,
    MeasureTheory.convolution_def]
  simpa using
    (integral_mul_indicator_const_sub_eq_setIntegral hUm A (euclideanCoordLaplacian K)
      u.toFun).trans hweak_zero'

/-! ### The CoarseGraining convex smoothing is harmonic on the ball -/

/-! ### The `L²` approximation apex -/

/-! ### `MemLp` bookkeeping for the smooth approximant on a bounded window -/

/-! ### The apex on a supplied measurable window -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

