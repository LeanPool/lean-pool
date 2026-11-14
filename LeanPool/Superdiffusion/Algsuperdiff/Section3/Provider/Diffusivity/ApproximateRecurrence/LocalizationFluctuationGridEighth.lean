/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationEighthMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationEnvelopeMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationGridMoment

/-!
# LocalizationFluctuationGridEighth

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The grid form of the eighth-moment envelope of the oscillation cell

`LocalizationFluctuationEighthMoment.meshOscillationCell_pow_eight_le_volumeAverage`
is the *per-cell* half of the envelope that the boundary remainder consumes
(`LocalizationFluctuationGammaFold.gridFourthMoment_mesoCubeGrid_le_interior_add_of_eighthMoment`,
whose binder `hE` is a bound on the eighth-moment **grid average**).  This
module composes that per-cell bound over the mesh and then over the sample.

## What is proved

* `cubeFamilyAverage_meshOscillationCell_pow_eight_le_cubeAverage` -- the
  **spatial** grid composition, at the tiling constant `1`:
  ```
    avsum_{z in 3^n Zd cap cu_K} osc(z + cu_n)^8  <=  fint_{cu_K} |u|^8 .
  ```
  The mesh tiling identity `LocalizationGrid.cubeAverage_originCube_eq_mesoGridAverage`
  supplies the equality on the right; the per-cell Jensen step supplies the
  inequality on the left.  Nothing is lost: both constants are `1`.
* `cubeAverage_vecNormSq_pow_four_eq_cubeEuclideanLpNorm_eight_pow_eight` --
  the dictionary that turns `fint_{cu_K} |u|^8` into the eighth power of the
  manuscript's own volume-normalized Euclidean `L^8` norm, i.e. into the square
  of the left-hand side of `e.nablaw.in.L.eight`, squared.
* `cubeFamilyAverage_integral_le_of_pointwise` -- the **sample** composition: a
  pointwise (in the sample) bound of a grid average by a single integrable
  observable passes to the grid average of the integrals.
* `cubeFamilyAverage_integral_meshOscillationCell_pow_eight_le` -- the two
  composed: the eighth-moment grid average of the oscillation cells is below the
  expectation of `‖u‖^8_{L8bar(cu_K)}`.
* `integrable_rpow_four_of_isBigOWith_gammaSigma_one` and
  `integral_rpow_four_le_of_isBigOWith_gammaSigma_one` -- the **fourth** moment
  of an `O_{Gamma_1}(A)` variable, `E[T^4] <= (8 e A)^4`, in the exact shape of
  the second-moment pair of `LocalizationEnvelopeMoment`; this is the
  probabilistic input a consumer needs to turn `e.nablaw.in.L.eight`'s pathwise
  `Chead + O_{Gamma_1}(gamma^100)` into a numeric envelope.
* `freshShellEighthEnergyConst` and
  `integral_le_freshShellEighthEnergyConst` -- that numeric envelope,
  `8 Chead^4 + 8 (8 e A)^4`, from a **measurable** dominating fluctuation.

## Binders

The spatial statements carry only the five integrability families on `cu_K`,
all consequences of the `L^8` membership of `|u|` there, and the scale
bookkeeping `n <= K`, which only *names* the mesh.  The sample statements carry
the integrability in the sample of the per-cell eighth powers and of the
dominating observable -- the standing integrability of the very moments being
formed.  No smallness, normalization or moment assumption occurs, and nothing
about the corrector, the coefficient field or the model is assumed.

**Not proved here.** The measurability in the sample of `omega |-> fint_{cu_K}
|u(omega)|^8` -- the octic analogue of `Corrector.CorrectorMeasurableQuartic`
-- is not established, so the dominating observable of
`cubeFamilyAverage_integral_meshOscillationCell_pow_eight_le` is a binder
rather than a construction.  `Corrector.FreshShellL8` produces its fluctuation
`Tfluct` existentially and asserts nothing about its measurability, exactly as
`LocalizationEnvelopeMoment` records; `LocalizationEnvelopeWire` removes that
binder at the *fourth* power by dominating `Tfluct` with a measurable variable
built from the quartic layer, and the same device at the eighth power needs the
octic layer.  That octic layer is available as
`Corrector.CorrectorMeasurableOctic`, and the envelope construction discharging
this binder is `LocalizationFluctuationSplitOscEnvelope`; the binder form below
is retained for generality and is not assumed away.

## Scope

There is no `sorry`.

## References

* ABK26, `e.nablaw.oscillations`, `e.lower.bound.oscillations`,
  `e.nablaw.in.L.eight`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The measure-zero boundary step, on an arbitrary triadic cube -/

/-- **Unconditional.**  The open-cube volume average is the half-open cube
average; the two cube realizations differ by their Lebesgue-null boundary.

`LocalizationFluctuationDuality` states the same identity, but is outside this
importing a whole duality layer for it. -/
theorem volumeAverage_openCubeSet_eq_cubeAverage' (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) f = cubeAverage Q f := by
  unfold volumeAverage cubeAverage
  rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet]

/-! ## The spatial grid composition -/

/-- **The eighth-moment envelope at the mesh, spatially.**  The grid average
over `3^n Zd cap cu_K` of the eighth powers of the oscillation cells of
`e.nablaw.oscillations` is below the single normalized eighth moment of `u` on
`cu_K`.  Both the per-cell constant and the tiling constant are `1`.

Conditional on the scale containment `hn` -- which only *names* the mesh -- and on the five
integrability families on `cu_K`, all consequences of the `L^8` membership of
`|u|` there. -/
theorem cubeFamilyAverage_meshOscillationCell_pow_eight_le_cubeAverage
    (K n : ℤ) (hn : n ≤ K) (u : Vec d → Vec d)
    (hcoord : ∀ k : Fin d,
      IntegrableOn (fun x => u x k) (cubeSet (originCube d K)) volume)
    (hcoordsq : ∀ k : Fin d,
      IntegrableOn (fun x => (u x k) ^ 2) (cubeSet (originCube d K)) volume)
    (hsq : IntegrableOn (fun x => vecNormSq (u x)) (cubeSet (originCube d K)) volume)
    (hfour : IntegrableOn (fun x => vecNormSq (u x) ^ 2) (cubeSet (originCube d K)) volume)
    (height : IntegrableOn (fun x => vecNormSq (u x) ^ (4 : ℕ))
      (cubeSet (originCube d K)) volume) :
    cubeFamilyAverage (mesoCubeGrid d K n)
        (fun R => meshOscillationCell n u R ^ (8 : ℕ)) ≤
      cubeAverage (originCube d K) (fun x => vecNormSq (u x) ^ (4 : ℕ)) := by
  classical
  have hscale : n ≤ (originCube d K).scale := hn
  have hcell : ∀ R ∈ mesoCubeGrid d K n,
      meshOscillationCell n u R ^ (8 : ℕ) ≤
        cubeAverage R (fun x => vecNormSq (u x) ^ (4 : ℕ)) := by
    intro R hR
    have hsub : cubeSet R ⊆ cubeSet (originCube d K) :=
      cubeSet_subset_of_mem_descendantsAtScale hscale hR
    have hres : ∀ f : Vec d → ℝ,
        IntegrableOn f (cubeSet (originCube d K)) volume →
          IntegrableOn f (openCubeSet R) volume := by
      intro f hf
      exact integrableOn_cubeSet_iff_integrableOn_openCubeSet.mp (hf.mono_set hsub)
    have hfour' : IntegrableOn (fun x => (vecNormSq (u x) ^ 2) ^ 2)
        (openCubeSet R) volume := by
      have hcong : (fun x => (vecNormSq (u x) ^ 2) ^ 2) =
          fun x => vecNormSq (u x) ^ (4 : ℕ) := by
        funext x; ring
      rw [hcong]
      exact hres _ height
    have hbound := meshOscillationCell_pow_eight_le_volumeAverage R
      (scale_eq_of_mem_mesoCubeGrid hR) u
      (fun k => hres _ (hcoord k)) (fun k => hres _ (hcoordsq k))
      (hres _ hsq) (hres _ hfour) hfour'
    rwa [volumeAverage_openCubeSet_eq_cubeAverage'] at hbound
  have htile := cubeAverage_originCube_eq_mesoGridAverage hn
    (fun x => vecNormSq (u x) ^ (4 : ℕ)) height
  rw [htile]
  exact cubeFamilyAverage_mono hcell

/-! ## The dictionary to `e.nablaw.in.L.eight` -/

/-- **Unconditional in the cube data, conditional on the `L^8` membership.**
The half-open cube average of `|u|^8` is the eighth power of the manuscript's
volume-normalized Euclidean `L^8` norm.  This is the exact square of the
left-hand side of `e.nablaw.in.L.eight`. -/
theorem cubeAverage_vecNormSq_pow_four_eq_cubeEuclideanLpNorm_eight_pow_eight
    (Q : TriadicCube d) (u : Vec d → Vec d)
    (hu : MemLp (fun x => Book.Ch02.vecNorm (u x)) 8 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => vecNormSq (u x) ^ (4 : ℕ)) =
      Corrector.cubeEuclideanLpNorm Q 8 u ^ (8 : ℕ) := by
  have htoReal : ((8 : ℝ≥0∞)).toReal = (8 : ℝ) := by norm_num
  have hkey := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q 8
    (fun x => Book.Ch02.vecNorm (u x)) (by norm_num) (by norm_num) hu
  rw [htoReal] at hkey
  have hnorm : ∀ x : Vec d,
      ‖Book.Ch02.vecNorm (u x)‖ ^ (8 : ℝ) = vecNormSq (u x) ^ (4 : ℕ) := by
    intro x
    have hnn : (0 : ℝ) ≤ Book.Ch02.vecNorm (u x) := Book.Ch02.vecNorm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn,
      show ((8 : ℝ)) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc Book.Ch02.vecNorm (u x) ^ (8 : ℕ)
        = (Book.Ch02.vecNorm (u x) ^ (2 : ℕ)) ^ (4 : ℕ) := by ring
      _ = vecNormSq (u x) ^ (4 : ℕ) := by rw [Book.Ch02.vecNorm_sq_eq_vecNormSq]
  simp only [hnorm] at hkey
  have hcast : Corrector.cubeEuclideanLpNorm Q 8 u ^ (8 : ℕ) =
      (cubeLpNorm Q 8 (fun x => Book.Ch02.vecNorm (u x))) ^ (8 : ℝ) := by
    rw [Corrector.cubeEuclideanLpNorm,
      ← Real.rpow_natCast (cubeLpNorm Q 8 (fun x => Book.Ch02.vecNorm (u x))) 8]
    norm_num
  rw [hcast]
  exact hkey.symm

/-! ## The sample composition -/

/-- **The sample half of the composition.**  If, at every sample point, the grid
average of a family is below one observable `G`, then the grid average of the
integrals is below the integral of `G`.

Conditional on the integrability of each member of the family and of `G`, and on the
pointwise bound.  This is nothing but linearity of the integral on a finite
average, plus monotonicity. -/
theorem cubeFamilyAverage_integral_le_of_pointwise {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) (I : Finset (TriadicCube d))
    (F : TriadicCube d → Omega → ℝ) (G : Omega → ℝ)
    (hF : ∀ R ∈ I, Integrable (F R) mu) (hG : Integrable G mu)
    (hle : ∀ omega, cubeFamilyAverage I (fun R => F R omega) ≤ G omega) :
    cubeFamilyAverage I (fun R => ∫ omega, F R omega ∂mu) ≤ ∫ omega, G omega ∂mu := by
  classical
  have hswap : cubeFamilyAverage I (fun R => ∫ omega, F R omega ∂mu) =
      ∫ omega, cubeFamilyAverage I (fun R => F R omega) ∂mu := by
    unfold cubeFamilyAverage
    rw [integral_const_mul]
    refine congrArg (fun t : ℝ => ((I.card : ℝ))⁻¹ * t) ?_
    exact (integral_finsetSum I fun R hR => hF R hR).symm
  rw [hswap]
  have hint : Integrable (fun omega => cubeFamilyAverage I (fun R => F R omega)) mu := by
    unfold cubeFamilyAverage
    exact (integrable_finsetSum I fun R hR => hF R hR).const_mul _
  exact integral_mono hint hG hle

/-- **The eighth-moment grid average of the oscillation cells.**  The spatial
composition, integrated: the quantity the boundary remainder consumes is below
the expectation of the eighth power of the normalized Euclidean `L^8` norm of
`u` on `cu_K` -- the square of the quantity `e.nablaw.in.L.eight` controls.

Conditional on the scale bookkeeping `hn`, the five spatial integrability families (per
sample point), the integrability in the sample of the per-cell eighth powers,
and the integrability of the dominating observable `G` together with the
pathwise bound `hpath`.  No smallness or moment assumption occurs. -/
theorem cubeFamilyAverage_integral_meshOscillationCell_pow_eight_le {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) (K n : ℤ) (hn : n ≤ K)
    (u : Omega → Vec d → Vec d) (G : Omega → ℝ)
    (hcoord : ∀ omega, ∀ k : Fin d,
      IntegrableOn (fun x => u omega x k) (cubeSet (originCube d K)) volume)
    (hcoordsq : ∀ omega, ∀ k : Fin d,
      IntegrableOn (fun x => (u omega x k) ^ 2) (cubeSet (originCube d K)) volume)
    (hsq : ∀ omega, IntegrableOn (fun x => vecNormSq (u omega x))
      (cubeSet (originCube d K)) volume)
    (hfour : ∀ omega, IntegrableOn (fun x => vecNormSq (u omega x) ^ 2)
      (cubeSet (originCube d K)) volume)
    (height : ∀ omega, IntegrableOn (fun x => vecNormSq (u omega x) ^ (4 : ℕ))
      (cubeSet (originCube d K)) volume)
    (hcellInt : ∀ R ∈ mesoCubeGrid d K n,
      Integrable (fun omega => meshOscillationCell n (u omega) R ^ (8 : ℕ)) mu)
    (hGint : Integrable G mu)
    (hpath : ∀ omega,
      cubeAverage (originCube d K) (fun x => vecNormSq (u omega x) ^ (4 : ℕ)) ≤ G omega) :
    cubeFamilyAverage (mesoCubeGrid d K n)
        (fun R => ∫ omega, meshOscillationCell n (u omega) R ^ (8 : ℕ) ∂mu) ≤
      ∫ omega, G omega ∂mu := by
  refine cubeFamilyAverage_integral_le_of_pointwise mu (mesoCubeGrid d K n)
    (fun R omega => meshOscillationCell n (u omega) R ^ (8 : ℕ)) G hcellInt hGint
    fun omega => ?_
  exact le_trans
    (cubeFamilyAverage_meshOscillationCell_pow_eight_le_cubeAverage K n hn (u omega)
      (hcoord omega) (hcoordsq omega) (hsq omega) (hfour omega) (height omega))
    (hpath omega)

/-! ## The fourth moment of an `O_{Gamma_1}(A)` variable -/

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The fourth power of an `O_{Gamma_1}(A)` variable is integrable.

: `[IsProbabilityMeasure mu]`, `hA`, `hT0`, `hTm`, `hT`. -/
theorem integrable_rpow_four_of_isBigOWith_gammaSigma_one [IsProbabilityMeasure mu]
    {T : Omega → ℝ} {A : ℝ} (hA : 0 < A) (hT0 : ∀ omega, 0 ≤ T omega)
    (hTm : AEMeasurable T mu)
    (hT : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma 1) T A) :
    Integrable (fun omega => T omega ^ (4 : ℕ)) mu := by
  have h := IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
    (μ := mu) (Y := T) (K := A) (σ := 1) (p := 4) one_pos hA (by norm_num) hT0 hTm hT
  have hfun : (fun omega => T omega ^ (4 : ℝ)) = fun omega => T omega ^ (4 : ℕ) := by
    funext omega
    rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rwa [hfun] at h

/-- **The fourth moment of an `O_{Gamma_1}(A)` variable**: `E[T^4] <= (8 e A)^4`.

The constant is CoarseGraining's `gammaMomentConst 1 * 4^{1} = 2 e * 4 = 8 e`,
raised to the fourth power; nothing below sharpens it.  This is the exact
fourth-power mirror of
`LocalizationEnvelopeMoment.integral_sq_le_of_isBigOWith_gammaSigma_one`.

: `[IsProbabilityMeasure mu]`, `hA`, `hT0`, `hTm`, `hT`. -/
theorem integral_rpow_four_le_of_isBigOWith_gammaSigma_one [IsProbabilityMeasure mu]
    {T : Omega → ℝ} {A : ℝ} (hA : 0 < A) (hT0 : ∀ omega, 0 ≤ T omega)
    (hTm : AEMeasurable T mu)
    (hT : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma 1) T A) :
    ∫ omega, T omega ^ (4 : ℕ) ∂mu ≤ (8 * Real.exp 1 * A) ^ (4 : ℕ) := by
  have h := IndependentSums.integral_rpow_le_of_isBigOWith_gammaSigma
    (μ := mu) (Y := T) (K := A) (σ := 1) (p := 4) one_pos hA (by norm_num) hT0 hTm hT
  have hfun : (fun omega => T omega ^ (4 : ℝ)) = fun omega => T omega ^ (4 : ℕ) := by
    funext omega
    rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hconst : (IndependentSums.gammaMomentConst 1 * (4 : ℝ) ^ ((1 : ℝ))⁻¹ * A) ^ (4 : ℝ)
      = (8 * Real.exp 1 * A) ^ (4 : ℕ) := by
    rw [gammaMomentConst_one, inv_one, Real.rpow_one,
      show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hfun] at h
  rw [← hconst]
  exact h

/-! ## The eighth-energy envelope constant -/

/-- The annealed eighth-energy envelope: `8 Chead^4 + 8 (8 e A)^4`, where
`Chead` is the head constant of `e.nablaw.in.L.eight` and `A` its fluctuation
amplitude.  The two `8`s are the constants of `(a+b)^4 <= 8 a^4 + 8 b^4`. -/
def freshShellEighthEnergyConst (Chead A : ℝ) : ℝ :=
  8 * Chead ^ (4 : ℕ) + 8 * (8 * Real.exp 1 * A) ^ (4 : ℕ)

theorem freshShellEighthEnergyConst_nonneg (Chead A : ℝ) :
    0 ≤ freshShellEighthEnergyConst Chead A := by
  have h : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  unfold freshShellEighthEnergyConst
  positivity

/-- **The numeric envelope, from a measurable dominating fluctuation.**  If
`G <= (Chead + T)^4` pointwise with `T` a nonnegative, a.e.-measurable
`O_{Gamma_1}(A)` variable, then `E[G] <= 8 Chead^4 + 8 (8 e A)^4`.

: `[IsProbabilityMeasure mu]`, `hA`, `hT0`, `hTm`, `hT`, the integrability of
`G` and the pointwise domination `hGle`.  No sign hypothesis on `Chead` is
needed. -/
theorem integral_le_freshShellEighthEnergyConst [IsProbabilityMeasure mu]
    {G T : Omega → ℝ} {Chead A : ℝ} (hA : 0 < A) (hT0 : ∀ omega, 0 ≤ T omega)
    (hTm : AEMeasurable T mu)
    (hT : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma 1) T A)
    (hGint : Integrable G mu)
    (hGle : ∀ omega, G omega ≤ (Chead + T omega) ^ (4 : ℕ)) :
    ∫ omega, G omega ∂mu ≤ freshShellEighthEnergyConst Chead A := by
  have hT4Int : Integrable (fun omega => T omega ^ (4 : ℕ)) mu :=
    integrable_rpow_four_of_isBigOWith_gammaSigma_one hA hT0 hTm hT
  have hmaj : ∀ omega,
      (Chead + T omega) ^ (4 : ℕ) ≤ 8 * Chead ^ (4 : ℕ) + 8 * T omega ^ (4 : ℕ) := by
    intro omega
    have hstep := add_pow_four_le_eight_mul Chead (T omega)
    linarith
  have hRHSInt : Integrable
      (fun omega => 8 * Chead ^ (4 : ℕ) + 8 * T omega ^ (4 : ℕ)) mu :=
    (integrable_const _).add (hT4Int.const_mul 8)
  have hsplit : ∫ omega, (8 * Chead ^ (4 : ℕ) + 8 * T omega ^ (4 : ℕ)) ∂mu =
      8 * Chead ^ (4 : ℕ) + 8 * ∫ omega, T omega ^ (4 : ℕ) ∂mu := by
    rw [integral_add (integrable_const _) (hT4Int.const_mul 8), integral_const,
      integral_const_mul]
    simp
  have hfourth : ∫ omega, T omega ^ (4 : ℕ) ∂mu ≤ (8 * Real.exp 1 * A) ^ (4 : ℕ) :=
    integral_rpow_four_le_of_isBigOWith_gammaSigma_one hA hT0 hTm hT
  calc ∫ omega, G omega ∂mu
      ≤ ∫ omega, (8 * Chead ^ (4 : ℕ) + 8 * T omega ^ (4 : ℕ)) ∂mu :=
        integral_mono hGint hRHSInt fun omega => (hGle omega).trans (hmaj omega)
    _ = 8 * Chead ^ (4 : ℕ) + 8 * ∫ omega, T omega ^ (4 : ℕ) ∂mu := hsplit
    _ ≤ 8 * Chead ^ (4 : ℕ) + 8 * (8 * Real.exp 1 * A) ^ (4 : ℕ) := by linarith
    _ = freshShellEighthEnergyConst Chead A := rfl

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
