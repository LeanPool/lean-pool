/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.FluxCorrectedRepresentative

/-!
# FluxCorrectedTwoScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The two-argument `(m, n)` flux-corrected error

The carrier layer for the frozen `bounds_mathcal_E_aL` anchor: the proved
one-argument construction of `FluxCorrectedRepresentative.lean` with the
truncation index freed — the `(m, n)` form of `d.mathcal.E` at finite `q = 2`
(the manuscript defines the dropped argument as `n := m`, which is the `_self`
reduction below, accepted by `rfl`).

The a.e. identification with CoarseGraining's literal two-argument
`HomogenizationError` at the flux-corrected family is a named provider
obligation of `bounds_mathcal_E_aL` (the matched-index instance is already
proved as `fluxCorrectedError_ae_eq_representative`), not a Support-layer
theorem.

`neZero_of_model` below is a three-line duplicate of the file-private helper in
`FluxCorrectedRepresentative.lean` (and of the public `Section3` Orlicz
sibling).
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Support

open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

theorem neZero_of_model_FluxCorrectedTwoScale (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- The two-argument `(m, n)` flux-corrected `(∞,2)` error functional. -/
noncomputable def fluxCorrectedTwoScaleErrorFunctional [NeZero d] (M : ABKModel d)
    (L m n : ℤ) (s : ℝ) : Cutoff.CutoffSample d → ℝ :=
  fun omega => Real.sqrt (∑' l : ℕ, Ch02.geometricWeight s 2 l *
    fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L m
      (originCube d m) (n - (l : ℤ))
      (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega)

theorem fluxCorrectedTwoScaleErrorFunctional_nonneg [NeZero d] (M : ABKModel d)
    (L m n : ℤ) (s : ℝ) (omega : Cutoff.CutoffSample d) :
    0 ≤ fluxCorrectedTwoScaleErrorFunctional M L m n s omega :=
  Real.sqrt_nonneg _

private theorem fluxCorrectedTwoScaleErrorFunctional_term_nonneg [NeZero d]
    (M : ABKModel d) (L m n : ℤ) {s : ℝ} (hs : 0 < s) (l : ℕ)
    (omega : Cutoff.CutoffSample d) :
    0 ≤ Ch02.geometricWeight s 2 l *
      fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L m
        (originCube d m) (n - (l : ℤ))
        (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega := by
  refine mul_nonneg ?_ ?_
  · simpa only [Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg l (by positivity : 0 ≤ s * (2 : ℝ))
  · exact fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative_nonneg
      M L m (originCube d m) (n - (l : ℤ))
      (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega

theorem measurable_fluxCorrectedTwoScaleErrorFunctional [NeZero d] (M : ABKModel d)
    (L : ℤ) {m n : ℤ} (hnm : n ≤ m) {s : ℝ} (hs : 0 < s) :
    Measurable (fluxCorrectedTwoScaleErrorFunctional M L m n s) := by
  have hterm : ∀ l : ℕ, Measurable
      (fun omega => Ch02.geometricWeight s 2 l *
        fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L m
          (originCube d m) (n - (l : ℤ))
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega) := fun l =>
    (measurable_fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative
      M L m (originCube d m)
      ((sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hnm)
      (isotropicComparatorMatrix (Annealed.sigmaBar M m))).const_mul _
  exact Real.continuous_sqrt.measurable.comp
    (measurable_tsum_of_nonneg _ hterm
      (fluxCorrectedTwoScaleErrorFunctional_term_nonneg M L m n hs))

/-- The two-argument representative at the `{s // 0 < s}` public carrier. -/
noncomputable def fluxCorrectedTwoScaleErrorRepresentative (M : ABKModel d)
    (L m n : ℤ) (s : {s : ℝ // 0 < s}) : Cutoff.CutoffSample d → ℝ := by
  letI : NeZero d := neZero_of_model_FluxCorrectedTwoScale M
  exact fluxCorrectedTwoScaleErrorFunctional M L m n (s : ℝ)

theorem measurable_fluxCorrectedTwoScaleErrorRepresentative (M : ABKModel d)
    (L : ℤ) {m n : ℤ} (hnm : n ≤ m) (s : {s : ℝ // 0 < s}) :
    Measurable (fluxCorrectedTwoScaleErrorRepresentative M L m n s) := by
  let : NeZero d := neZero_of_model_FluxCorrectedTwoScale M
  change Measurable (fluxCorrectedTwoScaleErrorFunctional M L m n (s : ℝ))
  exact measurable_fluxCorrectedTwoScaleErrorFunctional M L hnm s.2

/-- The two-argument `sup_{L ≥ m}` observable, taken in `[0,∞]` so no convergence
side condition enters the statement. -/
noncomputable def fluxCorrectedTwoScaleErrorObservableSup (M : ABKModel d)
    (m n : ℤ) (s : {s : ℝ // 0 < s}) : Cutoff.CutoffSample d → ℝ≥0∞ :=
  fun omega => ⨆ L : {L : ℤ // m ≤ L},
    ENNReal.ofReal (fluxCorrectedTwoScaleErrorRepresentative M L.1 m n s omega)

theorem measurable_fluxCorrectedTwoScaleErrorObservableSup (M : ABKModel d)
    {m n : ℤ} (hnm : n ≤ m) (s : {s : ℝ // 0 < s}) :
    Measurable (fluxCorrectedTwoScaleErrorObservableSup M m n s) :=
  Measurable.iSup fun L =>
    (measurable_fluxCorrectedTwoScaleErrorRepresentative M L.1 hnm s).ennreal_ofReal

theorem le_fluxCorrectedTwoScaleErrorObservableSup (M : ABKModel d) (m n : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) {L : ℤ} (hL : m ≤ L) :
    ENNReal.ofReal (fluxCorrectedTwoScaleErrorRepresentative M L m n s omega) ≤
      fluxCorrectedTwoScaleErrorObservableSup M m n s omega :=
  le_iSup
    (fun L : {L : ℤ // m ≤ L} =>
      ENNReal.ofReal (fluxCorrectedTwoScaleErrorRepresentative M L.1 m n s omega)) ⟨L, hL⟩

end
end Algsuperdiff.Section4.Support
