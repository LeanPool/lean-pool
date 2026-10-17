/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.CoarseEllipticityBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.Assembly

/-!
# DimensionFloor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The dimension-floor normalization of the coarse-ellipticity constant

The constant of `p.cg.ellipticity.bounds` may be raised to satisfy `1 ≤ Ccg`.  The
Section 3.4 principal-response consumers need the same constant to clear the dimension
floor `(d : ℝ) ^ 6` as well: the event constant they feed to the sensitivity
gate is `2 * Ccg`, and that gate reads
`2 * (d : ℝ) ^ 6 ≤ 2 * Ccg * sensitivityConstMax d ^ 2`.

An existential cannot expose any lower bound on its own hidden witness, so the
floor is installed by the same monotonicity that installs `1`: every slot of
the statement is weaker at a larger constant, and
`coarse_ellipticity_bounds_body_of_legs` re-derives the `∀`-body at
`max C (max 1 ((d : ℝ) ^ 6))` from the two legs at `C`.  Neither the frozen
statement nor its proof changes.

## The predecessor

`Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds` is applied internally
here, so no premise of that shape survives on the surface below.  It is proved
on this branch, so this module's export is sorry-free.

## References

* ABK26, `p.cg.ellipticity.bounds`, statement.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3

/-- **The floor-normalized constant selection.**  The coarse-ellipticity
statement holds at a constant satisfying `1 ≤ Ccg` *and* `(d : ℝ) ^ 6 ≤ Ccg`,
namely `max C (max 1 ((d : ℝ) ^ 6))` for the constant `C` the frozen statement
provides. -/
theorem coarse_ellipticity_bounds_dim_floor (d : ℕ) :
    ∃ Ccg : ℝ, 1 ≤ Ccg ∧ (d : ℝ) ^ 6 ≤ Ccg ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Ccg / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ q : CoarseEllipticityExponent,
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              Probability.IsLowerIntegerFamilyOrlicz
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma
                    ((1 - sigma) / 2))
                  (fun L : ℤ =>
                    fun omega =>
                      Observable.cutoffLowerEllipticityInv
                          M m L s
                          (by
                            exact
                              (add_pos
                                (div_pos M.shellPrefix.gamma_pos (by norm_num))
                              (Real.exp_pos
                                (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                    M.gamma⁻¹)))).trans_le hsWindow.1)
                          q omega *
                        (Annealed.sigmaBar M (m - 1) : ℝ))
                  (m - 1)
                  (lowerEllipticityProfile Ccg M.gamma s q)
                  (Real.exp
                    (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) ∧
                Probability.IsDeterministicShiftTwoTermOneSidedOrlicz
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma 1)
                  (HCPolySupport.IndependentSums.gammaSigma
                    ((1 - sigma) / 3))
                  (fun omega =>
                    Observable.cutoffUpperEllipticity
                        M m m s
                        (by
                          exact
                            (add_pos
                              (div_pos M.shellPrefix.gamma_pos (by norm_num))
                            (Real.exp_pos
                              (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                  M.gamma⁻¹)))).trans_le hsWindow.1)
                        q omega *
                      (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹)
                  Ccg
                  (Ccg * (Disorder.cstar M)⁻¹ * s * M.gamma *
                    (2 * s - M.gamma)⁻¹ ^ 3)
                  (Real.exp
                    (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  obtain ⟨C, hC, hbody⟩ := Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds d
  refine ⟨max C (max 1 ((d : ℝ) ^ 6)),
    le_trans (le_max_left _ _) (le_max_right _ _),
    le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  exact coarse_ellipticity_bounds_body_of_legs d hC hC (le_max_left _ _)
    (le_max_left _ _)
    (fun M m E hstate sigma hsigma hE1 hE2 q s hsWindow =>
      (hbody M m E hstate sigma hsigma hE1 hE2 q s hsWindow).1)
    (fun M m E hstate sigma hsigma hE1 hE2 q s hsWindow =>
      (hbody M m E hstate sigma hsigma hE1 hE2 q s hsWindow).2)

end Algsuperdiff.Section3.Provider.CoarseEllipticity
