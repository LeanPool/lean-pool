/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.FluxCorrectedRepresentative
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl

/-!
# LambdaCaps

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The coarse-grained ellipticity ratios of the flux-corrected field

This module renders the two ratios of `e.bound.Lambdas.by.Es.v2` (ABK26) at
the proved Section 4 carriers, and bounds their maximum by the flux-corrected
homogenization error `𝓔_{s,∞,2}`.  It is the `Λ`-side companion of the
good-event caps chain assembled in `GoodEventCaps.lean`.

## What is proved, and what is *not*

The printed Section 2 lemma `l.mathcal.E.to.Lambdas` (display
`e.bound.Lambdas.by.Es`) asserts the **sharp, dimension-free** two-sided
comparison

```
½ 𝓔_{s,∞,q}(□_m; a, σ₀)²
  ≤ max{ σ₀⁻¹ Λ_{s,q}(□_m; a) , σ₀ λ_{s,q}⁻¹(□_m; a) }
  ≤ 1 + 2 𝓔_{s,∞,q}(□_m; a, σ₀)² + 2^{1/2} 𝓔_{s,∞,q}(□_m; a, σ₀) .
```

**Only the upper half is treated here, and only in a `2d`-lossy form**:
`max{…} ≤ 2d (𝓔² + 1)` at `q = 2`.  This is *not* the printed statement and
must never be presented as `l.mathcal.E.to.Lambdas`:

* the printed constants `1, 2, 2^{1/2}` are absolute, ours carries a factor
  `2d`; the printed proof route (the block quadratic identity `e.J.by.f`, the
  matrix inequalities `e.xminusonetimesxminusonesquared.{sstar,b}`, and the
  eigenvalue argument for `f(x) = x⁻¹(x−1)²`) is **not** formalized anywhere in
  this repository or in CoarseGraining;
* the printed lower half `½𝓔² ≤ max{…}` and the `q = 2` refinement
  `e.bound.Lambdas.by.Es.q2` are **not** proved here at all;
* the printed lemma is stated for every `q ∈ [1,∞]`; ours is the `q = 2`
  endpoint only, which is the exponent the consumer display
  `e.bound.Lambdas.by.Es.v2` uses.

The lossy form suffices for the only §4.3 consumption site: the good-event cap
needs a bound by a constant `C(d)`, and `2d(𝓔²+1)` with `𝓔` capped is such a
constant.

## Main definitions

* `fluxCorrectedUpperEllipticity` — `Λ_{s,2}(□_k; a_L − (κ_L−κ_k)_{□_k})`.
* `fluxCorrectedLowerEllipticityInv` — `λ_{s,2}⁻¹(□_k; a_L − (κ_L−κ_k)_{□_k})`.
* `fluxCorrectedEllipticityRatioMax` — the displayed
  `max{σ_k⁻¹Λ_{s,2}, σ_kλ_{s,2}⁻¹}`.

## Main results

* `max_ellipticityRatio_le_homogenizationError` — the `2d`-lossy upper half at
  CoarseGraining's carriers, for an arbitrary positive scalar comparator `σ`.
* `fluxCorrectedEllipticityRatioMax_le` — its pointwise transport to the
  flux-corrected literal error at the comparator `σ_k`.
* `ae_fluxCorrectedEllipticityRatioMax_le` — the almost-everywhere form at
  the *measurable representative*, uniformly in `L ≥ k`.
* `two_mul_dim_mul_sq_add_one_le_of_le` — the monotone folding step that
  turns an `𝓔`-cap into a constant.

## Carrier conventions used (resolution A4)

Every cube is the *origin* cube `originCube d k`; a statement at `z + □_k` is
obtained by translating the **sample**, i.e. by evaluating at
`Cutoff.translateCutoffSample z omega`.  The comparator is `σ_k Id =
isotropicComparatorMatrix (Annealed.sigmaBar M k)`, which is CoarseGraining's
`scalarMatrix (σ_k : ℝ)` on the nose.

## References

* ABK26, `l.mathcal.E.to.Lambdas`.
* ABK26, `e.bound.Lambdas.by.Es.v2`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The two ratio carriers at the flux-corrected field -/

/-- `Λ_{s,2}(□_k; a_L − (κ_L − κ_k)_{□_k})`, as a function of the cutoff
sample.  The value at `z + □_k` is this function at
`Cutoff.translateCutoffSample z omega` (resolution A4). -/
def fluxCorrectedUpperEllipticity (M : ABKModel d) (L k : ℤ) (s : ℝ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  Ch02.LambdaSq (originCube d k) s (.finite 2)
    (Support.fluxCorrectedCoeffFamily M L k (originCube d k) omega)

/-- `λ_{s,2}⁻¹(□_k; a_L − (κ_L − κ_k)_{□_k})`.  The manuscript always writes the
*inverse* lower constant, and so does the proved Section 3 observable
`Observable.cutoffLowerEllipticityInvLiteral`; this is the same reading at the
flux-corrected field. -/
def fluxCorrectedLowerEllipticityInv (M : ABKModel d) (L k : ℤ) (s : ℝ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  (Ch02.lambdaSq (originCube d k) s (.finite 2)
    (Support.fluxCorrectedCoeffFamily M L k (originCube d k) omega))⁻¹

/-- The left-hand side of `e.bound.Lambdas.by.Es.v2`, taken at the *single*
comparator `σ_k` on both legs.

We follow the lemma, i.e. the mathematically supported reading, and take `σ₀ =
σ_k` at the cube `□_k` that carries the functional. -/
def fluxCorrectedEllipticityRatioMax (M : ABKModel d) (L k : ℤ) (s : ℝ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  max ((Annealed.sigmaBar M k : ℝ)⁻¹ * fluxCorrectedUpperEllipticity M L k s omega)
    ((Annealed.sigmaBar M k : ℝ) * fluxCorrectedLowerEllipticityInv M L k s omega)

/-- The unfolded reading of `fluxCorrectedEllipticityRatioMax`. -/
theorem fluxCorrectedEllipticityRatioMax_def (M : ABKModel d) (L k : ℤ) (s : ℝ)
    (omega : Cutoff.CutoffSample d) :
    fluxCorrectedEllipticityRatioMax M L k s omega =
      max ((Annealed.sigmaBar M k : ℝ)⁻¹ *
          Ch02.LambdaSq (originCube d k) s (.finite 2)
            (Support.fluxCorrectedCoeffFamily M L k (originCube d k) omega))
        ((Annealed.sigmaBar M k : ℝ) *
          (Ch02.lambdaSq (originCube d k) s (.finite 2)
            (Support.fluxCorrectedCoeffFamily M L k (originCube d k) omega))⁻¹) :=
  rfl

/-! ## 2. The `2d`-lossy upper half at CoarseGraining's carriers -/

/-- The Section 3 comparator `σ Id` is CoarseGraining's `scalarMatrix σ`. -/
private theorem isotropicComparatorMatrix_eq_scalarMatrix (sigma : PositiveScalar) :
    isotropicComparatorMatrix (d := d) sigma = scalarMatrix (d := d) (sigma : ℝ) :=
  rfl

/-- **The upper half of `e.bound.Lambdas.by.Es`, in its `2d`-lossy `q = 2` form.**
Transport of CoarseGraining's
`Ch02.max_weightedEllipticity_finite_two_le_card_mul_homogenizationError_sq_add_one`
with `Fintype.card (Fin d)` evaluated.

This is **not** the printed lemma: the printed right-hand side is the
dimension-free `1 + 2𝓔² + 2^{1/2}𝓔`.  See the module docstring. -/
theorem max_ellipticityRatio_le_homogenizationError [NeZero d]
    (Q : TriadicCube d) (a : Ch02.TriadicCoeffFamily d) {s sigma : ℝ}
    (hs : 0 < s) (hsigma : 0 < sigma) :
    max (sigma⁻¹ * Ch02.LambdaSq Q s (.finite 2) a)
        (sigma * (Ch02.lambdaSq Q s (.finite 2) a)⁻¹) ≤
      2 * (d : ℝ) *
        (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a
            (scalarMatrix (d := d) sigma) ^ 2 + 1) := by
  have h :=
    Ch02.max_weightedEllipticity_finite_two_le_card_mul_homogenizationError_sq_add_one
      Q a hs hsigma
  rwa [Fintype.card_fin] at h

/-! ## 3. Transport to the flux-corrected sample carrier -/

/-- The paper-wide standing assumption `2 ≤ d`, stored in the model. -/
private theorem neZero_of_model (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- **The ratio maximum at the flux-corrected field, bounded by the literal
flux-corrected error.**  Pointwise in the sample; no probability enters. -/
theorem fluxCorrectedEllipticityRatioMax_le [NeZero d] (M : ABKModel d) (L k : ℤ)
    {s : ℝ} (hs : 0 < s) (omega : Cutoff.CutoffSample d) :
    fluxCorrectedEllipticityRatioMax M L k s omega ≤
      2 * (d : ℝ) * (Support.fluxCorrectedError M L k s omega ^ 2 + 1) := by
  have h := max_ellipticityRatio_le_homogenizationError (d := d) (originCube d k)
    (Support.fluxCorrectedCoeffFamily M L k (originCube d k) omega) hs
    (Annealed.sigmaBar M k).2
  rw [fluxCorrectedEllipticityRatioMax_def,
    Support.fluxCorrectedError_characterization M L k s omega,
    isotropicComparatorMatrix_eq_scalarMatrix]
  exact h

/-- **The almost-everywhere form at the measurable representative**, uniformly
in `L ≥ k`.

The passage from the literal error to
`Support.fluxCorrectedErrorRepresentative` is the proved
`Support.ae_forall_fluxCorrectedError_eq_representative`, which carries all `L
≥ k` on a single probability-one event because the index set is countable. -/
theorem ae_fluxCorrectedEllipticityRatioMax_le (M : ABKModel d) (k : ℤ)
    (s : {s : ℝ // 0 < s}) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ L : ℤ, k ≤ L →
        fluxCorrectedEllipticityRatioMax M L k (s : ℝ) omega ≤
          2 * (d : ℝ) *
            (Support.fluxCorrectedErrorRepresentative M L k s omega ^ 2 + 1) := by
  let : NeZero d := neZero_of_model M
  filter_upwards [Support.ae_forall_fluxCorrectedError_eq_representative M k s]
    with omega hall
  intro L hL
  have heq : Support.fluxCorrectedError M L k (s : ℝ) omega =
      Support.fluxCorrectedErrorRepresentative M L k s omega := hall ⟨L, hL⟩
  have h := fluxCorrectedEllipticityRatioMax_le M L k s.2 omega
  rwa [heq] at h

/-! ## 4. The folding step -/

/-- **The cap-folding step.**  An `𝓔`-bound `𝓔 ≤ t` turns the envelope
`2d(𝓔² + 1)` into the constant `2d(t² + 1)`.  This is the arithmetic the
good-event cap performs after the annular anchor has supplied `t`. -/
theorem two_mul_dim_mul_sq_add_one_le_of_le {E t : ℝ} (hE : 0 ≤ E) (hEt : E ≤ t) :
    2 * (d : ℝ) * (E ^ 2 + 1) ≤ 2 * (d : ℝ) * (t ^ 2 + 1) := by
  have hd : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  have hsq : E ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hE hEt 2
  exact mul_le_mul_of_nonneg_left (by linarith only [hsq]) hd

end

end Algsuperdiff.Section4.Provider.ExcessDecay
