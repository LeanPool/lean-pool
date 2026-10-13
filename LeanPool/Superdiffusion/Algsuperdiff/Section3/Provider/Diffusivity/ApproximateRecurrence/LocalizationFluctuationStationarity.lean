/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Symmetry
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationAncestor
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Public
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Translation
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.DoubledMu

/-!
# LocalizationFluctuationStationarity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The stationarity half

1. **geometric** -- state the per-cell bound at the cell's own scale-`m`
   ancestor.  This is `LocalizationFluctuationAncestor`, proved;
2. **probabilistic** -- transport the annealed fourth moment from that ancestor
   back to `cu_m` by stationarity, "which the manuscript uses silently".

This module performs step 2.

## The route

Every scale-`m` triadic cube is an integer translate of `cu_m`
(`eq_translateCube_originCube_of_scale`), and the cutoff-sample law is
invariant under every real translation
(`Cutoff.map_translateCutoffSample_cutoffSampleLaw`,
`Cutoff.coefficientCutoffLaw_stationary_real`).  What is missing between those
two facts is the **per-cube covariance of the coarse matrices** of the *actual*
cutoff family: CoarseGraining's

* `Ch02.LambdaSq_translateCube_of_coarseBMatrixNorm` and
* `Ch02.lambdaSq_translateCube_of_coarseSigmaStarInvMatrixNorm`

reduce the covariance of the two multiscale ellipticity constants to exactly the
per-cube identities

```
  |b(3^n z + R; a_omega)|            = |b(R; a_{tau_v omega})| ,
  |sigma_*^{-1}(3^n z + R; a_omega)| = |sigma_*^{-1}(R; a_{tau_v omega})| ,
```

for every descendant `R` of `cu_m` at depth `n`, where `v = 3^m z` is the
physical shift and `a_omega = coefficientCutoffTriadicCoeffFamily M L omega`.
`coarseBlockMatrix_coefficientCutoff_translateCube` proves both at once, at the
level of the coarse **block** matrix, by the chain

```
  A(cu(3^n z + R); a_omega)  =  A(open(3^n z + R); cutoff_omega)         (Ch02 = CoarseGraining)
                              =  A(v + open(R); cutoff_omega)             (geometry)
                              =  A(open(R); translate_v cutoff_omega)     (translation)
                              =  A(open(R); cutoff_{tau_v omega})         (Cutoff.Symmetry)
                              =  A(cu(R); a_{tau_v omega}) .
```

Note that the physical shift `3^n z * 3^{m-n} = 3^m z` is the **same at every
depth `n`**, which is precisely what the CoarseGraining hypothesis needs.

## What is proved

* `openCubeSet_translateCube_eq_translateSet` -- the geometry step.
* `coarseBlockMatrix_cubeDomain_eq_coarseBlockMatrix_openCubeSet` -- the
  identification of the Chapter-2 coarse block matrix of a cube coefficient
  object with the CoarseGraining coarse block matrix of its underlying field.
  This is
  `coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField`
  with the a.e.-elliptic-field packaging stripped out; the cutoff family is not
  built through that packaging.
* `coarseBlockMatrix_coefficientCutoff_translateCube`, and the two norm
  corollaries `coarseBMatrixNorm_coefficientCutoff_translateCube` and
  `coarseSigmaStarInvMatrixNorm_coefficientCutoff_translateCube` -- **the missing
  link**.
* `gaugedEllipticitySum_translateCube_coefficientCutoff` and
  `gaugedEllipticitySum_scale_eq_originCube` -- the pathwise covariance of the
  gauged ellipticity sum.
* `integral_gaugedEllipticitySum_pow_eq_originCube` and
  `integral_gaugedEllipticitySum_pow_ancestorAtScale_eq_originCube` -- **the
  transport**: the annealed fourth moment of the gauged ellipticity sum at a
  cell's scale-`m` ancestor equals the one at `cu_m`, where the frozen
  `Frozen.Section3.coarse_ellipticity_bounds` lives.

## Binders

Everything through `gaugedEllipticitySum_scale_eq_originCube` is **pathwise and
unconditional** apart from the typing binders and the cube-scale identification
`hT : T.scale = m`; no measure, no model gate and no moment occurs.  The two
transport statements add one binder, `hmeas`, the a.e.-strong measurability in
the sample of the observable being integrated -- the analytic side condition of
the change of variables, on the very object the moment is formed from.  It is
not a smallness, normalization or moment assumption, and it is stated at the
**origin cube**, i.e. at the carrier the frozen theorem already speaks about.

## Scope

There is no `sorry`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2, display and the moment
  average.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Geometry: the open realization of a translated cube -/

/-- **Unconditional.**  The open realization of `translateCube w S` is the
translate of the open realization of `S` by the physical shift
`w * 3^{S.scale}`. -/
theorem openCubeSet_translateCube_eq_translateSet (w : Fin d → ℤ) (S : TriadicCube d) :
    openCubeSet (translateCube w S) =
      translateSet (fun i => ((w i : ℤ) : ℝ) * cubeScaleFactor S) (openCubeSet S) := by
  ext x
  rw [mem_openCubeSet_translateCube_iff, mem_translateSet_iff_sub_mem]

/-- **Unconditional.**  Every scale-`m` triadic cube is the integer translate of
`cu_m` by its own index. -/
theorem eq_translateCube_originCube_of_scale {T : TriadicCube d} {m : ℤ}
    (hT : T.scale = m) : T = translateCube T.index (originCube d m) := by
  cases T with
  | mk scale index =>
      subst hT
      simp [translateCube, originCube]

/-! ## The two coarse block matrices agree -/

/-- **Unconditional.**  The Chapter-2 coarse block matrix of a cube coefficient
object is the CoarseGraining coarse block matrix of its underlying coefficient
field on the open cube.

This is the content of
`coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField`
without its `A packaging: the cutoff family is not built through
`triadicCoeffFamilyOfA, so that statement does not apply to it. -/
theorem coarseBlockMatrix_cubeDomain_eq_coarseBlockMatrix_openCubeSet
    (Q : TriadicCube d) (aQ : Ch02.CoeffOn (Ch02.cubeDomain Q)) :
    Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) aQ =
      coarseBlockMatrix (openCubeSet Q) aQ.toCoeffField := by
  refine eq_coarseBlockMatrix_of_isCoarseBlockMatrix ?_
  refine ⟨Ch02.isSymmetricBlockMat_coarseBlockMatrix (Ch02.cubeDomain Q) aQ, ?_⟩
  intro P
  calc Mu (openCubeSet Q) P aQ.toCoeffField
      = Mu ((Ch02.cubeDomain Q : Ch02.Domain d) : Set (Vec d)) P aQ.toCoeffField := by
        rw [Ch02.cubeDomain_coe]
    _ = Ch02.doubledMu (Ch02.cubeDomain Q) aQ P :=
        (HCPolySupport.Internal.Ch02.BookCh02.book_doubledMu_eq_Mu
          (Ch02.cubeDomain Q) aQ P).symm
    _ = (1 / 2 : ℝ) * blockVecDot P
          (blockMatVecMul (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) aQ) P) :=
        (Ch02.doubledMuTheory (Ch02.cubeDomain Q) aQ).doubledMu_eq_coarseBlockMatrix P

/-! ## The missing link: per-cube covariance of the cutoff coarse matrices -/

/-- **The per-cube covariance of the coarse block matrix of the actual cutoff
family.**  Translating the cube by `w` and translating the sample by the
physical shift `w * 3^{S.scale}` produce the same coarse block matrix.

Unconditional: the only inputs are the geometry step, CoarseGraining's
translation identity for `coarseBlockMatrix` and the exact commutation
`Cutoff.coefficientCutoff_translateCutoffSample`. -/
theorem coarseBlockMatrix_coefficientCutoff_translateCube (M : ABKModel d) (L : ℤ)
    (omega : CutoffSample d) (w : Fin d → ℤ) (S : TriadicCube d) :
    Ch02.coarseBlockMatrix (Ch02.cubeDomain (translateCube w S))
        ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn (translateCube w S)) =
      Ch02.coarseBlockMatrix (Ch02.cubeDomain S)
        ((coefficientCutoffTriadicCoeffFamily M L
          (translateCutoffSample
            (fun i => ((w i : ℤ) : ℝ) * cubeScaleFactor S) omega)).coeffOn S) := by
  set v : Vec d := fun i => ((w i : ℤ) : ℝ) * cubeScaleFactor S with hv
  have hleft :
      Ch02.coarseBlockMatrix (Ch02.cubeDomain (translateCube w S))
          ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn (translateCube w S)) =
        coarseBlockMatrix (openCubeSet (translateCube w S))
          (coefficientCutoff M.nu L omega).toFun :=
    coarseBlockMatrix_cubeDomain_eq_coarseBlockMatrix_openCubeSet _ _
  have hright :
      Ch02.coarseBlockMatrix (Ch02.cubeDomain S)
          ((coefficientCutoffTriadicCoeffFamily M L
            (translateCutoffSample v omega)).coeffOn S) =
        coarseBlockMatrix (openCubeSet S)
          (coefficientCutoff M.nu L (translateCutoffSample v omega)).toFun :=
    coarseBlockMatrix_cubeDomain_eq_coarseBlockMatrix_openCubeSet _ _
  have hfield : (coefficientCutoff M.nu L (translateCutoffSample v omega)).toFun =
      translateCoeffField v (coefficientCutoff M.nu L omega).toFun := by
    rw [coefficientCutoff_translateCutoffSample M.nu L v omega]
    rfl
  rw [hleft, hright, hfield, openCubeSet_translateCube_eq_translateSet w S, ← hv,
    coarseBlockMatrix_translateSet_eq_translateCoeffField]

/-- **The upper per-cube norm is covariant.**  This is the exact hypothesis of
CoarseGraining's `Ch02.LambdaSq_translateCube_of_coarseBMatrixNorm`. -/
theorem coarseBMatrixNorm_coefficientCutoff_translateCube (M : ABKModel d) (L : ℤ)
    (omega : CutoffSample d) (w : Fin d → ℤ) (S : TriadicCube d) :
    Ch02.coarseBMatrixNorm (translateCube w S)
        (coefficientCutoffTriadicCoeffFamily M L omega) =
      Ch02.coarseBMatrixNorm S
        (coefficientCutoffTriadicCoeffFamily M L
          (translateCutoffSample
            (fun i => ((w i : ℤ) : ℝ) * cubeScaleFactor S) omega)) := by
  have h := congrArg (fun A : BlockMat d => Ch02.matrixNorm A.upperLeft)
    (coarseBlockMatrix_coefficientCutoff_translateCube M L omega w S)
  simpa [Ch02.coarseBMatrixNorm] using h

/-- **The lower per-cube norm is covariant.**  This is the exact hypothesis of
CoarseGraining's `Ch02.lambdaSq_translateCube_of_coarseSigmaStarInvMatrixNorm`. -/
theorem coarseSigmaStarInvMatrixNorm_coefficientCutoff_translateCube (M : ABKModel d)
    (L : ℤ) (omega : CutoffSample d) (w : Fin d → ℤ) (S : TriadicCube d) :
    Ch02.coarseSigmaStarInvMatrixNorm (translateCube w S)
        (coefficientCutoffTriadicCoeffFamily M L omega) =
      Ch02.coarseSigmaStarInvMatrixNorm S
        (coefficientCutoffTriadicCoeffFamily M L
          (translateCutoffSample
            (fun i => ((w i : ℤ) : ℝ) * cubeScaleFactor S) omega)) := by
  have h := congrArg (fun A : BlockMat d => Ch02.matrixNorm A.lowerRight)
    (coarseBlockMatrix_coefficientCutoff_translateCube M L omega w S)
  simpa [Ch02.coarseSigmaStarInvMatrixNorm] using h

/-! ## The physical shift does not move with the depth -/

/-- **Unconditional.**  A depth-`n` descendant of a cube of scale `m`, translated
by `descendantTranslationShift n z`, moves by the physical shift `3^m z`, which
does not depend on `n`. -/
theorem descendantTranslationShift_physical (z : Fin d → ℤ) (n : ℕ) (m : ℤ)
    {R : TriadicCube d} (hR : R.scale = m - (n : ℤ)) :
    (fun i => ((descendantTranslationShift n z i : ℤ) : ℝ) * cubeScaleFactor R) =
      (fun i => ((z i : ℤ) : ℝ) * cubeScaleFactor (originCube d m)) := by
  funext i
  have hscale : cubeScaleFactor R = (3 : ℝ) ^ (m - (n : ℤ)) := by
    rw [show cubeScaleFactor R = (3 : ℝ) ^ R.scale from rfl, hR]
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hsplit : (3 : ℝ) ^ (m - (n : ℤ)) = (3 : ℝ) ^ m * ((3 : ℝ) ^ (n : ℤ))⁻¹ := by
    rw [zpow_sub₀ (ne_of_gt h3), div_eq_mul_inv]
  have hn : ((3 : ℝ) ^ (n : ℤ)) = (3 : ℝ) ^ (n : ℕ) := zpow_natCast (3 : ℝ) n
  have hcast : ((descendantTranslationShift n z i : ℤ) : ℝ) =
      (3 : ℝ) ^ (n : ℕ) * ((z i : ℤ) : ℝ) := by
    rw [descendantTranslationShift]
    push_cast
    ring
  have hne : ((3 : ℝ) ^ (n : ℕ)) ≠ 0 := by positivity
  rw [hscale, hsplit, hn, hcast,
    show cubeScaleFactor (originCube d m) = (3 : ℝ) ^ m from rfl]
  field_simp

/-! ## The gauged ellipticity sum is covariant -/

/-- **The pathwise covariance of the gauged ellipticity sum.**  Unconditional. -/
theorem gaugedEllipticitySum_translateCube_coefficientCutoff (M : ABKModel d)
    (L m : ℤ) (omega : CutoffSample d) (z : Fin d → ℤ) (sigmaBar s : ℝ) :
    gaugedEllipticitySum sigmaBar
        (translateCube z (originCube d m)) s
        (coefficientCutoffTriadicCoeffFamily M L omega) =
      gaugedEllipticitySum sigmaBar (originCube d m) s
        (coefficientCutoffTriadicCoeffFamily M L
          (translateCutoffSample
            (fun i => ((z i : ℤ) : ℝ) * cubeScaleFactor (originCube d m)) omega)) := by
  set v : Vec d := fun i => ((z i : ℤ) : ℝ) * cubeScaleFactor (originCube d m) with hv
  have hB : ∀ (n : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) ((originCube d m).scale - (n : ℤ)) →
        Ch02.coarseBMatrixNorm (translateCube (descendantTranslationShift n z) R)
            (coefficientCutoffTriadicCoeffFamily M L omega) =
          Ch02.coarseBMatrixNorm R
            (coefficientCutoffTriadicCoeffFamily M L (translateCutoffSample v omega)) := by
    intro n R hR
    have hk : (originCube d m).scale - (n : ℤ) ≤ (originCube d m).scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hscale : R.scale = m - (n : ℤ) := by
      have := scale_eq_sub_of_mem_descendantsAtScale (Q := originCube d m) hk hR
      simpa [originCube] using this
    have hstep := coarseBMatrixNorm_coefficientCutoff_translateCube M L omega
      (descendantTranslationShift n z) R
    rw [descendantTranslationShift_physical z n m hscale] at hstep
    rw [hstep, hv]
  have hSigma : ∀ (n : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) ((originCube d m).scale - (n : ℤ)) →
        Ch02.coarseSigmaStarInvMatrixNorm
            (translateCube (descendantTranslationShift n z) R)
            (coefficientCutoffTriadicCoeffFamily M L omega) =
          Ch02.coarseSigmaStarInvMatrixNorm R
            (coefficientCutoffTriadicCoeffFamily M L (translateCutoffSample v omega)) := by
    intro n R hR
    have hk : (originCube d m).scale - (n : ℤ) ≤ (originCube d m).scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hscale : R.scale = m - (n : ℤ) := by
      have := scale_eq_sub_of_mem_descendantsAtScale (Q := originCube d m) hk hR
      simpa [originCube] using this
    have hstep := coarseSigmaStarInvMatrixNorm_coefficientCutoff_translateCube M L omega
      (descendantTranslationShift n z) R
    rw [descendantTranslationShift_physical z n m hscale] at hstep
    rw [hstep, hv]
  have hUp := Ch02.LambdaSq_translateCube_of_coarseBMatrixNorm
    (coefficientCutoffTriadicCoeffFamily M L omega)
    (coefficientCutoffTriadicCoeffFamily M L (translateCutoffSample v omega))
    z (originCube d m) s (Ch02.MultiscaleExponent.finite 2) hB
  have hLo := Ch02.lambdaSq_translateCube_of_coarseSigmaStarInvMatrixNorm
    (coefficientCutoffTriadicCoeffFamily M L omega)
    (coefficientCutoffTriadicCoeffFamily M L (translateCutoffSample v omega))
    z (originCube d m) s (Ch02.MultiscaleExponent.finite 2) hSigma
  unfold gaugedEllipticitySum
  rw [hUp, hLo]

/-- **The pathwise covariance, at an arbitrary scale-`m` cube.**  Unconditional
apart from the scale identification `hT`. -/
theorem gaugedEllipticitySum_scale_eq_originCube [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : CutoffSample d) {T : TriadicCube d} (hT : T.scale = m) (sigmaBar s : ℝ) :
    gaugedEllipticitySum sigmaBar T s
        (coefficientCutoffTriadicCoeffFamily M L omega) =
      gaugedEllipticitySum sigmaBar (originCube d m) s
        (coefficientCutoffTriadicCoeffFamily M L
          (translateCutoffSample
            (fun i => ((T.index i : ℤ) : ℝ) * cubeScaleFactor (originCube d m)) omega)) := by
  conv_lhs => rw [eq_translateCube_originCube_of_scale hT]
  exact gaugedEllipticitySum_translateCube_coefficientCutoff M L m omega T.index sigmaBar s

/-! ## The change of variables in the sample -/

/-- **The translation change of variables on the cutoff-sample law.**

Conditional on `hg`, the a.e.-strong measurability of the integrand -- the analytic side
condition of the change of variables. -/
theorem integral_comp_translateCutoffSample (M : ABKModel d) (v : Vec d)
    (g : CutoffSample d → ℝ)
    (hg : AEStronglyMeasurable g (cutoffSampleLaw M).toMeasure) :
    ∫ omega, g (translateCutoffSample v omega) ∂(cutoffSampleLaw M).toMeasure =
      ∫ omega, g omega ∂(cutoffSampleLaw M).toMeasure := by
  have hmap := map_translateCutoffSample_cutoffSampleLaw M v
  have hmeas : AEStronglyMeasurable g
      (Measure.map (translateCutoffSample v) (cutoffSampleLaw M).toMeasure) := by
    rw [hmap]; exact hg
  have h := integral_map (φ := translateCutoffSample (d := d) v)
    (μ := (cutoffSampleLaw M).toMeasure)
    (measurable_translateCutoffSample v).aemeasurable hmeas
  rw [hmap] at h
  exact h.symm

/-! ## The transport -/

/-- **The stationarity half.**  The annealed fourth moment of the gauged
ellipticity sum at any scale-`m` cube equals the one at `cu_m`, where
`Frozen.Section3.coarse_ellipticity_bounds` lives.

Conditional on the scale identification `hT` and on `hmeas`, the a.e.-strong measurability
in the sample of the observable at the **origin cube**.  Nothing about the
model, the gauge or the exponent is assumed. -/
theorem integral_gaugedEllipticitySum_pow_eq_originCube [NeZero d] (M : ABKModel d)
    (L m : ℤ) {T : TriadicCube d} (hT : T.scale = m) (sigmaBar s : ℝ) (k : ℕ)
    (hmeas : AEStronglyMeasurable
      (fun omega : CutoffSample d =>
        gaugedEllipticitySum sigmaBar (originCube d m) s
          (coefficientCutoffTriadicCoeffFamily M L omega) ^ k)
      (cutoffSampleLaw M).toMeasure) :
    ∫ omega : CutoffSample d,
        gaugedEllipticitySum sigmaBar T s
          (coefficientCutoffTriadicCoeffFamily M L omega) ^ k
        ∂(cutoffSampleLaw M).toMeasure =
      ∫ omega : CutoffSample d,
        gaugedEllipticitySum sigmaBar (originCube d m) s
          (coefficientCutoffTriadicCoeffFamily M L omega) ^ k
        ∂(cutoffSampleLaw M).toMeasure := by
  set v : Vec d :=
    fun i => ((T.index i : ℤ) : ℝ) * cubeScaleFactor (originCube d m) with hv
  have hpt : ∀ omega : CutoffSample d,
      gaugedEllipticitySum sigmaBar T s
          (coefficientCutoffTriadicCoeffFamily M L omega) ^ k =
        gaugedEllipticitySum sigmaBar (originCube d m) s
          (coefficientCutoffTriadicCoeffFamily M L (translateCutoffSample v omega)) ^ k :=
    fun omega => congrArg (fun t : ℝ => t ^ k)
      (gaugedEllipticitySum_scale_eq_originCube M L m omega hT sigmaBar s)
  calc ∫ omega : CutoffSample d,
        gaugedEllipticitySum sigmaBar T s
          (coefficientCutoffTriadicCoeffFamily M L omega) ^ k
          ∂(cutoffSampleLaw M).toMeasure
      = ∫ omega : CutoffSample d,
          gaugedEllipticitySum sigmaBar (originCube d m) s
            (coefficientCutoffTriadicCoeffFamily M L
              (translateCutoffSample v omega)) ^ k
          ∂(cutoffSampleLaw M).toMeasure :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ omega : CutoffSample d,
          gaugedEllipticitySum sigmaBar (originCube d m) s
            (coefficientCutoffTriadicCoeffFamily M L omega) ^ k
          ∂(cutoffSampleLaw M).toMeasure :=
        integral_comp_translateCutoffSample M v _ hmeas

/-- **The transport at the ancestor carrier of `LocalizationFluctuationAncestor`.**
The annealed fourth moment of the gauged ellipticity sum at a mesoscopic cell's
own scale-`m` ancestor is the one at `cu_m`.  Together with
`LocalizationFluctuationAncestor.doubledPoincareEllipticityFactor_sq_le_recurrenceAncestor`
this closes the carrier mismatch.

Conditional on `hm : R.scale <= m` (the ancestor exists) and on `hmeas`. -/
theorem integral_gaugedEllipticitySum_pow_ancestorAtScale_eq_originCube [NeZero d]
    (M : ABKModel d) (L m : ℤ) (R : TriadicCube d) (hm : R.scale ≤ m)
    (sigmaBar s : ℝ) (k : ℕ)
    (hmeas : AEStronglyMeasurable
      (fun omega : CutoffSample d =>
        gaugedEllipticitySum sigmaBar (originCube d m) s
          (coefficientCutoffTriadicCoeffFamily M L omega) ^ k)
      (cutoffSampleLaw M).toMeasure) :
    ∫ omega : CutoffSample d,
        gaugedEllipticitySum sigmaBar (ancestorAtScale R m) s
          (coefficientCutoffTriadicCoeffFamily M L omega) ^ k
        ∂(cutoffSampleLaw M).toMeasure =
      ∫ omega : CutoffSample d,
        gaugedEllipticitySum sigmaBar (originCube d m) s
          (coefficientCutoffTriadicCoeffFamily M L omega) ^ k
        ∂(cutoffSampleLaw M).toMeasure :=
  integral_gaugedEllipticitySum_pow_eq_originCube M L m
    (ancestorAtScale_scale R hm) sigmaBar s k hmeas

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
