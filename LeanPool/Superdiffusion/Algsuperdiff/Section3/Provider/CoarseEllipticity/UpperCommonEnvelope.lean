/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperPolyProfile
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.WeakOrlicz

/-!
# UpperCommonEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Finite-`q` upper aggregation from one common random envelope

This file isolates the valid joint-probability input needed after
`UpperPolyProfile.lean`.  Marginal `Gamma_1` certificates for a family
`U n` do not, by themselves, give a `q`-uniform certificate for its weighted
`ell^(q/2)` aggregate: at large finite `q` the aggregate can see the maximum
of many unrelated variables.  The usable input is instead one common
nonnegative envelope `V`, with

```text
U n omega <= upperPolyProfile A gamma n * V omega
```

simultaneously for every depth.  The random factor then leaves the entire
aggregate before any depth summation.  The deterministic theorem
`upperPolyProfile_aggregate_le_of_two_le` supplies the source's cubic budget,
uniformly in finite `q >= 2`, and scaling the single `Gamma_1` certificate for
`V` supplies the joint random lane.

The theorem here is conditional: it does not manufacture the common envelope.
Producing it requires a joint grid-and-depth maximum estimate from the
model-facing upper block bound.  In particular, no family of marginal tail
bounds is accepted as a substitute.

## Source and provenance

* ABK26, for the ordinary upper profile and cubic pole.
* `UpperPolyProfile.lean`, for the deterministic finite-`q` aggregation.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums

noncomputable section

/-- The quadratic upper profile has a summable weighted `q/2` power on the
source window.  This is the summability companion to
`upperPolyProfile_aggregate_le_of_two_le`. -/
theorem summable_geometricWeight_mul_upperPolyProfile_rpow_of_two_le
    {A gamma s q : ℝ} (hA : 0 ≤ A) (hgamma : 0 ≤ gamma)
    (hs : 0 < s) (hs1 : s ≤ 1) (hq : 2 ≤ q)
    (hgap : 0 < 2 * s - gamma) :
    Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s q n * upperPolyProfile A gamma n ^ (q / 2) := by
  let rho : ℝ := 2 * s - gamma
  let C : ℝ := 96 * A * rho⁻¹ ^ 2
  let gamma' : ℝ := gamma + rho / 2
  have hrho : 0 < rho := by simpa [rho] using hgap
  have hrho2 : rho ≤ 2 := by
    dsimp [rho]
    linarith
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hsq : 0 ≤ s * q := mul_nonneg hs.le hq0.le
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hgap' : 0 < 2 * s - gamma' := by
    have hid : 2 * s - gamma' = rho / 2 := by
      dsimp [gamma', rho]
      ring
    rw [hid]
    positivity
  have hprofile : ∀ n : ℕ,
      upperPolyProfile A gamma n ≤ finiteQGeometricProfile C gamma' n := by
    intro n
    simpa [C, gamma'] using
      upperPolyProfile_le_finiteQGeometricProfile hA hrho hrho2 gamma n
  have hright : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s q n *
        finiteQGeometricProfile C gamma' n ^ (q / 2) :=
    summable_geometricWeight_mul_finiteQGeometricProfile_rpow hC hgap' hq0
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (HCPolySupport.geometricWeight_nonneg n hsq)
      (Real.rpow_nonneg (upperPolyProfile_nonneg hA gamma n) _))
    (fun n => ?_) hright
  refine mul_le_mul_of_nonneg_left ?_ (HCPolySupport.geometricWeight_nonneg n hsq)
  exact Real.rpow_le_rpow (upperPolyProfile_nonneg hA gamma n)
    (hprofile n) (by linarith)

/-- A simultaneous pointwise upper-profile envelope factors out of the full
weighted `ell^(q/2)` aggregate.  This is a deterministic statement; its
quantifier `forall n omega` is the essential joint input. -/
theorem upperPolyProfile_aggregate_le_commonEnvelope
    {Omega : Type*} {U : ℕ → Omega → ℝ} {V : Omega → ℝ}
    {A gamma s q : ℝ} (hA : 0 ≤ A) (hgamma : 0 ≤ gamma)
    (hs : 0 < s) (hs1 : s ≤ 1) (hq : 2 ≤ q)
    (hgap : 0 < 2 * s - gamma)
    (hUnonneg : ∀ n omega, 0 ≤ U n omega)
    (hVnonneg : ∀ omega, 0 ≤ V omega)
    (hdom : ∀ n omega, U n omega ≤ upperPolyProfile A gamma n * V omega)
    (omega : Omega) :
    (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        U n omega ^ (q / 2)) ^ (2 / q) ≤
      (384 * A * s * (2 * s - gamma)⁻¹ ^ 3) * V omega := by
  let w : ℕ → ℝ := fun n => Book.Ch02.geometricWeight s q n
  let p : ℕ → ℝ := upperPolyProfile A gamma
  let c : ℝ := V omega
  let S : ℝ := ∑' n : ℕ, w n * p n ^ (q / 2)
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have ht0 : 0 ≤ q / 2 := by positivity
  have hroot0 : 0 ≤ 2 / q := by positivity
  have hsq : 0 ≤ s * q := mul_nonneg hs.le hq0.le
  have hw : ∀ n, 0 ≤ w n := fun n => by
    dsimp [w]
    exact HCPolySupport.geometricWeight_nonneg n hsq
  have hp : ∀ n, 0 ≤ p n := fun n => by
    dsimp [p]
    exact upperPolyProfile_nonneg hA gamma n
  have hc : 0 ≤ c := by simpa [c] using hVnonneg omega
  have hpsum : Summable fun n : ℕ => w n * p n ^ (q / 2) := by
    simpa [w, p] using
      summable_geometricWeight_mul_upperPolyProfile_rpow_of_two_le
        hA hgamma hs hs1 hq hgap
  have hscaledSum : Summable fun n : ℕ =>
      w n * (p n * c) ^ (q / 2) := by
    refine (hpsum.mul_right (c ^ (q / 2))).congr (fun n => ?_)
    rw [Real.mul_rpow (hp n) hc]
    ring
  have hUsum : Summable fun n : ℕ => w n * U n omega ^ (q / 2) := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hUnonneg n omega) _))
      (fun n => ?_) hscaledSum
    refine mul_le_mul_of_nonneg_left ?_ (hw n)
    exact Real.rpow_le_rpow (hUnonneg n omega)
      (by simpa [p, c] using hdom n omega) ht0
  have hsumle :
      (∑' n : ℕ, w n * U n omega ^ (q / 2)) ≤
        ∑' n : ℕ, w n * (p n * c) ^ (q / 2) :=
    hUsum.tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hUnonneg n omega)
          (by simpa [p, c] using hdom n omega) ht0) (hw n))
      hscaledSum
  have hscaledTsum :
      (∑' n : ℕ, w n * (p n * c) ^ (q / 2)) = c ^ (q / 2) * S := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [Real.mul_rpow (hp n) hc]
    ring
  have hS : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hp n) _)
  have hcancel : q / 2 * (2 / q) = 1 := by
    field_simp
  have hscaleRoot :
      (∑' n : ℕ, w n * (p n * c) ^ (q / 2)) ^ (2 / q) =
        c * S ^ (2 / q) := by
    rw [hscaledTsum, Real.mul_rpow (Real.rpow_nonneg hc _) hS,
      ← Real.rpow_mul hc, hcancel, Real.rpow_one]
  have hdet : S ^ (2 / q) ≤
      384 * A * s * (2 * s - gamma)⁻¹ ^ 3 := by
    simpa [S, w, p] using
      upperPolyProfile_aggregate_le_of_two_le hA hgamma hs hs1 hq hgap
  change
    (∑' n : ℕ, w n * U n omega ^ (q / 2)) ^ (2 / q) ≤
      (384 * A * s * (2 * s - gamma)⁻¹ ^ 3) * c
  calc
    (∑' n : ℕ, w n * U n omega ^ (q / 2)) ^ (2 / q) ≤
        (∑' n : ℕ, w n * (p n * c) ^ (q / 2)) ^ (2 / q) :=
      Real.rpow_le_rpow
        (tsum_nonneg fun n => mul_nonneg (hw n)
          (Real.rpow_nonneg (hUnonneg n omega) _)) hsumle hroot0
    _ = c * S ^ (2 / q) := hscaleRoot
    _ ≤ c * (384 * A * s * (2 * s - gamma)⁻¹ ^ 3) :=
      mul_le_mul_of_nonneg_left hdet hc
    _ = (384 * A * s * (2 * s - gamma)⁻¹ ^ 3) * c := by ring


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
