/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.FluxCorrectedTwoScale
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.ABK26.LocalCoarseGrainingResponse

/-!
# FluxCorrectedTwoScaleCarrier

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two-argument carrier identity for the flux-corrected `(∞,2)` error

`FluxCorrectedTwoScale.lean` builds the measurable two-argument observable
`fluxCorrectedTwoScaleErrorObservableSup` and records its a.e. identification
with CoarseGraining's literal object as a named obligation.  This file
discharges that obligation in the exact form the §4.5 chain consumes it: for
a.e. sample, at every admissible `L` and every fractional order,
CoarseGraining's literal `q = 2` truncated parent error of the flux-corrected
coefficient on `□_m` is the extended-real encoding of the proved measurable
two-argument representative.

## The three ingredients

1. Summability of the real series is internal to that theorem (it comes from
   the uniform response bound of the parent `CoeffOn`'s own ellipticity
   constants), so no summability side condition enters here and the real square
   root does not junk to `0`.

2. **The family swap is a.e.-invariance of the response.**  The response value
   set is built from `Ch02.doubledResponseJ`, which depends on the coefficient
   only through its a.e. class (`Ch02.doubledResponseJ_eq_ofAEEq`).  Hence
   `Ch02.normalizedBlockResponseMax` is unchanged when the root pointwise
   family of `fluxCorrectedCoeffOn` is replaced by the proved canonical family
   `fluxCorrectedCoeffFamily`: both are a.e. the same field on every descendant
   cube (`fluxCorrectedRegField_toFun`).

3. **The representative swap is the proved probability-one event**
   `ae_forall_normalizedBlockResponseMax_fluxCorrected_eq_representative`,
   which is indexed by `L` alone — it does not depend on the order `t` — so a
   single countable intersection over `L ≥ m` carries every order at once.

## Units

Carrier bookkeeping only.  `σ_m` occurs solely as the comparator of the two
error functionals, and it is the SAME comparator on both sides
(`isotropicComparatorMatrix (σ_m) = scalarMatrix (σ_m)` definitionally).  No
`ν`-division, no `ν ↔ σ` conversion, no flat elliptic estimate.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Support

open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## 1. The comparator is literally CoarseGraining's scalar matrix -/

/-! ## 2. The response maximum sees the coefficient only through its a.e. class -/

/-- **A.e. invariance of the one-cube response maximum.**  If two triadic
families have a.e. equal representatives on `R`, their normalized block-response
maxima on `R` agree.  The whole content is `Ch02.doubledResponseJ_eq_ofAEEq`:
the response is an infimum/supremum of integrals of the coefficient, so it
factors through the a.e. class. -/
theorem normalizedBlockResponseMax_congr_of_aeeq [NeZero d] (R : TriadicCube d)
    {F G : Ch02.TriadicCoeffFamily d} (a0 : Mat d)
    (h : Ch02.CoeffOn.AEEq (F.coeffOn R) (G.coeffOn R)) :
    Ch02.normalizedBlockResponseMax R F a0 = Ch02.normalizedBlockResponseMax R G a0 := by
  have hset : Ch02.normalizedBlockResponseValueSet R F a0 =
      Ch02.normalizedBlockResponseValueSet R G a0 := by
    ext y
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, Ch02.doubledResponseJ_eq_ofAEEq h _ _⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, Ch02.doubledResponseJ_eq_ofAEEq h.symm _ _⟩
  unfold Ch02.normalizedBlockResponseMax
  rw [hset]

/-- The proved canonical family of the flux-corrected field and CoarseGraining's
root pointwise family of the flux-corrected `CoeffOn` are a.e. equal on every
descendant cube: both representatives are literally the flux-corrected field. -/
theorem fluxCorrectedCoeffFamily_coeffOn_aeeq_rootPointwise [NeZero d]
    (M : ABKModel d) (L m : ℤ) (Q : TriadicCube d) (omega : Cutoff.CutoffSample d)
    {R : TriadicCube d} {k : ℤ} (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) :
    Ch02.CoeffOn.AEEq ((fluxCorrectedCoeffFamily M L m Q omega).coeffOn R)
      ((rootPointwiseCoeffFamily Q (fluxCorrectedCoeffOn M L m Q omega)).coeffOn R) :=
  Filter.EventuallyEq.trans
    (Filter.EventuallyEq.of_eq (fluxCorrectedRegField_toFun M L m Q omega))
    (rootPointwiseCoeffFamily_descendant_aeeq Q
      (fluxCorrectedCoeffOn M L m Q omega) hk hR).symm

/-- The descendant maximum at one physical scale is the same for CoarseGraining's
root pointwise family and for the proved canonical flux-corrected family. -/
theorem maxDescendant_rootPointwise_eq_fluxCorrectedCoeffFamily [NeZero d]
    (M : ABKModel d) (L m : ℤ) (Q : TriadicCube d) (omega : Cutoff.CutoffSample d)
    {k : ℤ} (hk : k ≤ Q.scale) (a0 : Mat d) :
    Ch02.maxDescendantNormalizedBlockResponseAtScale Q k
        (rootPointwiseCoeffFamily Q (fluxCorrectedCoeffOn M L m Q omega)) a0 =
      Ch02.maxDescendantNormalizedBlockResponseAtScale Q k
        (fluxCorrectedCoeffFamily M L m Q omega) a0 :=
  Ch02.finsetSupReal_congr _ fun R hR =>
    (normalizedBlockResponseMax_congr_of_aeeq R a0
      (fluxCorrectedCoeffFamily_coeffOn_aeeq_rootPointwise M L m Q omega hk hR)).symm

/-! ## 3. The carrier identity at one sample of the proved event -/

private theorem twoScale_term_nonneg [NeZero d] (M : ABKModel d) (L m n : ℤ)
    {s : ℝ} (hs : 0 < s) (l : ℕ) (omega : Cutoff.CutoffSample d) :
    0 ≤ Ch02.geometricWeight s 2 l *
      fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L m
        (originCube d m) (n - (l : ℤ))
        (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega := by
  refine mul_nonneg ?_ ?_
  · simpa only [Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg l (by linarith only [hs] : 0 ≤ s * (2 : ℝ))
  · exact fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative_nonneg
      M L m (originCube d m) (n - (l : ℤ))
      (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega

/-- **The two-argument carrier identity, at one sample.**

On the proved probability-one event of
`ae_forall_normalizedBlockResponseMax_fluxCorrected_eq_representative`,
CoarseGraining's literal `q = 2` truncated parent error of the flux-corrected
coefficient `ã_{L,m}` on `□_m`, truncated at any `n ≤ m`, is exactly the
extended-real encoding of the proved measurable two-argument representative at
the same order.  This is an, not a domination. -/
theorem parentTruncatedTwo_fluxCorrected_eq_ofReal_representative [NeZero d]
    (M : ABKModel d) (L m n : ℤ) (hn : n ≤ (originCube d m).scale)
    (t : FractionalOrder) (omega : Cutoff.CutoffSample d)
    (hall : ∀ R : TriadicCube d,
      Ch02.normalizedBlockResponseMax R
          (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) =
        fluxCorrectedNormalizedBlockResponseRepresentative M L m (originCube d m) R
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega) :
    Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m) n hn
        (fluxCorrectedCoeffOn M L m (originCube d m) omega)
        ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2 t =
      ENNReal.ofReal (fluxCorrectedTwoScaleErrorFunctional M L m n t.1 omega) := by
  have hscale : ∀ k : ℤ, k ≤ (originCube d m).scale →
      Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m) k
          (rootPointwiseCoeffFamily (originCube d m)
            (fluxCorrectedCoeffOn M L m (originCube d m) omega))
          (scalarMatrix (d := d) ((Annealed.sigmaBar M m : ℝ))) =
        fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L m
          (originCube d m) k (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega := by
    intro k hk
    rw [maxDescendant_rootPointwise_eq_fluxCorrectedCoeffFamily M L m (originCube d m)
      omega hk (scalarMatrix (d := d) ((Annealed.sigmaBar M m : ℝ)))]
    exact Ch02.finsetSupReal_congr _ fun R _ => hall R
  have hsum :
      (∑' l : ℕ, Ch02.geometricWeight t.1 2 l *
        Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m) (n - (l : ℤ))
          (rootPointwiseCoeffFamily (originCube d m)
            (fluxCorrectedCoeffOn M L m (originCube d m) omega))
          (scalarMatrix (d := d) ((Annealed.sigmaBar M m : ℝ)))) =
      ∑' l : ℕ, Ch02.geometricWeight t.1 2 l *
        fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L m
          (originCube d m) (n - (l : ℤ))
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega :=
    tsum_congr fun l => congrArg (fun x => Ch02.geometricWeight t.1 2 l * x)
      (hscale (n - (l : ℤ)) ((sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn))
  have hnonneg : 0 ≤ ∑' l : ℕ, Ch02.geometricWeight t.1 2 l *
      fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L m
        (originCube d m) (n - (l : ℤ))
        (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega :=
    tsum_nonneg fun l => twoScale_term_nonneg M L m n t.2.1 l omega
  have hleft0 : 0 ≤ Ch02.HomogenizationErrorFinite (originCube d m) n t.1 .infinity 2
      (rootPointwiseCoeffFamily (originCube d m)
        (fluxCorrectedCoeffOn M L m (originCube d m) omega))
      (scalarMatrix (d := d) ((Annealed.sigmaBar M m : ℝ))) := by
    unfold Ch02.HomogenizationErrorFinite
    refine Real.rpow_nonneg (tsum_nonneg fun l => mul_nonneg ?_ ?_) _
    · simpa only [Ch02.geometricWeight_eq_old] using
        HCPolySupport.geometricWeight_nonneg l
          (by linarith only [t.2.1] : 0 ≤ t.1 * (2 : ℝ))
    · exact Real.rpow_nonneg (Ch02.scaleResponseAtScale_infinity_nonneg (originCube d m)
        ((sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn) _ _) _
  have hleftsq : (Ch02.HomogenizationErrorFinite (originCube d m) n t.1 .infinity 2
      (rootPointwiseCoeffFamily (originCube d m)
        (fluxCorrectedCoeffOn M L m (originCube d m) omega))
      (scalarMatrix (d := d) ((Annealed.sigmaBar M m : ℝ)))) ^ 2 =
      ∑' l : ℕ, Ch02.geometricWeight t.1 2 l *
        fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L m
          (originCube d m) (n - (l : ℤ))
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega := by
    rw [Ch02.homogenizationErrorFinite_infinity_two_sq_eq_tsum (originCube d m) hn t.2.1,
      hsum]
  have hrightsq : fluxCorrectedTwoScaleErrorFunctional M L m n t.1 omega ^ 2 =
      ∑' l : ℕ, Ch02.geometricWeight t.1 2 l *
        fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L m
          (originCube d m) (n - (l : ℤ))
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega :=
    Real.sq_sqrt hnonneg
  rw [parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_ofReal]
  congr 1
  calc
    Ch02.HomogenizationErrorFinite (originCube d m) n t.1 .infinity 2
        (rootPointwiseCoeffFamily (originCube d m)
          (fluxCorrectedCoeffOn M L m (originCube d m) omega))
        (scalarMatrix (d := d) ((Annealed.sigmaBar M m : ℝ))) =
        Real.sqrt ((Ch02.HomogenizationErrorFinite (originCube d m) n t.1 .infinity 2
          (rootPointwiseCoeffFamily (originCube d m)
            (fluxCorrectedCoeffOn M L m (originCube d m) omega))
          (scalarMatrix (d := d) ((Annealed.sigmaBar M m : ℝ)))) ^ 2) :=
      (Real.sqrt_sq hleft0).symm
    _ = Real.sqrt (fluxCorrectedTwoScaleErrorFunctional M L m n t.1 omega ^ 2) := by
      rw [hleftsq, hrightsq]
    _ = fluxCorrectedTwoScaleErrorFunctional M L m n t.1 omega :=
      Real.sqrt_sq (fluxCorrectedTwoScaleErrorFunctional_nonneg M L m n t.1 omega)

/-! ## 4. The public carrier, at the `{s // 0 < s}` order and a.e. -/

/-- **The a.e. two-argument carrier identification.**

One probability-one event, one measure: on it, at every `L ≥ m` and every
fractional order,
CoarseGraining's literal `q = 2` truncated parent error of `ã_{L,m}` at the
truncation index `n` equals the encoding of the proved measurable two-argument
representative.  The event is the countable intersection over `L ≥ m` of the
proved per-`L` events; the order plays no role in it. -/
theorem ae_forall_parentTruncatedTwo_fluxCorrected_eq_representative [NeZero d]
    (M : ABKModel d) (m n : ℤ) (hn : n ≤ (originCube d m).scale) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ L : ℤ, m ≤ L → ∀ t : FractionalOrder,
        Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m) n hn
            (fluxCorrectedCoeffOn M L m (originCube d m) omega)
            ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2 t =
          ENNReal.ofReal
            (fluxCorrectedTwoScaleErrorRepresentative M L m n ⟨t.1, t.2.1⟩ omega) := by
  have hall : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ L : {L : ℤ // m ≤ L}, ∀ R : TriadicCube d,
        Ch02.normalizedBlockResponseMax R
            (fluxCorrectedCoeffFamily M L.1 m (originCube d m) omega)
            (isotropicComparatorMatrix (Annealed.sigmaBar M m)) =
          fluxCorrectedNormalizedBlockResponseRepresentative M L.1 m (originCube d m) R
            (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega :=
    MeasureTheory.ae_all_iff.2 fun L =>
      ae_forall_normalizedBlockResponseMax_fluxCorrected_eq_representative M L.1 m
        (originCube d m) (isotropicComparatorMatrix (Annealed.sigmaBar M m))
  filter_upwards [hall] with omega homega L hL t
  exact parentTruncatedTwo_fluxCorrected_eq_ofReal_representative M L m n hn t omega
    (homega ⟨L, hL⟩)

end

end Algsuperdiff.Section4.Support
