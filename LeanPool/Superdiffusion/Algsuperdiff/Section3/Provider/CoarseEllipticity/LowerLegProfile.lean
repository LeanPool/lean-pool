/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.LowerLeg

/-!
# LowerLegProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The all-`q` unification of the lower leg's deterministic profile

The frozen lower display of `p.cg.ellipticity.bounds` quantifies over **every**
admissible exponent `q in [1, infinity]` and puts its deterministic shift in one
slot, `lowerEllipticityProfile Ccg gamma s q` (`Section3/Exponent.lean`).  That
one symbol is the *union* of three distinct source facts, and this module makes
the union explicit, without touching the frozen shape:

| branch | profile value | source status |
|---|---|---|
| finite `q < 2` | `C (s (2s-gamma)^{-1})^{2/q}` | --- the printed order-one pole is **false** below
`q = 2`; the corrected order is `2/q` |
| finite `2 <= q` | `C s (2s-gamma)^{-1}` | --- the printed pole's shape is confirmed; the payload
remains a conditional input of this module |
| `q = infinity` | `C` | `e.coarse.grained.ellipticity.infty`: no pole |

`coarse_ellipticity_lower_payload_of_branchPayloads` recombines three
branch-indexed payloads into the single all-`q` payload that
`Provider/CoarseEllipticity/LowerLeg.lean`'s reduction consumes.  The
downstream theorem `superposedFlux_coarse_ellipticity_lower_leg` now supplies
all three branches; this module retains the conditional decomposition.

## Where the branch boundary comes from, and what `q < 2` really needs

`lambda_{s,q}^{-1}` is an `ell^{q/2}`-type aggregation of the per-scale grid
maxima.  A linear weighted-series bound --- "the target is at most
`sum_k w_k G_k`" --- is available exactly when `ell^1` norm-embeds in
`ell^{q/2}` (`‖·‖_{ℓ^{q/2}} ≤ ‖·‖_{ℓ¹}`), i.e. exactly when `q/2 >= 1`
(direction corrected).  That is where the boundary at `q = 2` comes from, and
it is why the two finite branches are produced by different arguments, both of
them outside this module: `coarse_ellipticity_lower_branchPayload_two_le_of_finiteQPresplit`
(`FiniteQPresplit.lean`) on `2 <= q`, and
`coarse_ellipticity_lower_branchPayload_lt_two_of_finiteQPresplit`
(`FiniteQLtTwoPresplit.lean`) on `q < 2`, at the corrected order `2/q`.

The boundary itself is inherited from the proved `lowerEllipticityProfile`'s
case split (`Section3/Exponent.lean`), which is read off branch by branch
below; what this module adds is the exhaustiveness of the three branches, so
that a caller holding all three payloads holds the all-`q` one.

## What is proved here

* `coarseEllipticityExponent_trichotomy` --- the admissible exponent carrier is
  a covering by the three source branches (exhaustiveness is what is proved;
  disjointness is not needed and not claimed ---).
* `lowerEllipticityProfile_finite_of_lt_two`,
  `lowerEllipticityProfile_finite_of_two_le`,
  `lowerEllipticityProfile_infinity` --- the three profile values, read off the
  frozen statement's raw parameters branch by branch.
* `rpow_two_mul_div_le` --- the constant reconciliation of the corrected
  `q < 2` leg: the two renderings of its base differ by `2^{2/r} <= 4`, a
  dimension-only factor, because every admissible exponent satisfies `1 <= r`.
* `coarse_ellipticity_lower_payload_of_branchPayloads` --- **the unification**:
  three branch payloads give the all-`q` payload of
  `coarse_ellipticity_lower_leg_body_of_familySplitPayload`.

## What is *not* proved in this module

This module does not itself produce any of the three branch payloads.  They
remain explicit inputs of the unification.  The downstream superposed-flux
provider supplies the branch payloads and proves
`superposedFlux_coarse_ellipticity_lower_leg`; the separate downstream theorem
`superposedFlux_coarse_ellipticity_upper_leg` supplies the upper leg, and the
now-proved frozen export consumes both through the assembly theorem.  In
particular the `q < 2` branch payload is *not* derived from
the `2 <= q` one: on the frozen window the two profiles are incomparable (the
base `s/(2s - gamma)` exceeds one exactly when `s <= gamma`, and the frozen
window `s in [gamma/2 + exp(...), 1]` contains points on both sides), so neither
branch implies the other.

## References

* ABK26, `p.cg.ellipticity.bounds`, statement, proof; the coarse-grained
  ellipticity constants.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

/-! ## 1. The three source branches of the admissible exponent carrier -/

/-- The admissible exponent carrier of the frozen statement is exactly the union
of the three source branches: finite below two, finite at least two, and the
infinity endpoint. -/
theorem coarseEllipticityExponent_trichotomy (q : CoarseEllipticityExponent) :
    (∃ r : {r : ℝ // 1 ≤ r}, (r : ℝ) < 2 ∧
        q = CoarseEllipticityExponent.finite r) ∨
      (∃ r : {r : ℝ // 1 ≤ r}, 2 ≤ (r : ℝ) ∧
          q = CoarseEllipticityExponent.finite r) ∨
        q = CoarseEllipticityExponent.infinity := by
  obtain ⟨q, hq⟩ := q
  cases q with
  | finite r =>
      by_cases hr : r < 2
      · exact Or.inl ⟨⟨r, hq⟩, hr, rfl⟩
      · exact Or.inr (Or.inl ⟨⟨r, hq⟩, not_lt.1 hr, rfl⟩)
  | infinity => exact Or.inr (Or.inr rfl)

/-- The deterministic lower profile on the frozen statement's raw parameters, in
the corrected finite `q < 2` branch. -/
theorem lowerEllipticityProfile_finite_of_lt_two (C gamma s : ℝ)
    (r : {r : ℝ // 1 ≤ r}) (hr : (r : ℝ) < 2) :
    lowerEllipticityProfile C gamma s (CoarseEllipticityExponent.finite r) =
      C * Real.rpow (s / (2 * s - gamma)) (2 / (r : ℝ)) := by
  simp only [lowerEllipticityProfile, CoarseEllipticityExponent.finite, hr,
    ↓reduceIte]

/-- The deterministic lower profile on the frozen statement's raw parameters, in
the printed finite `2 <= q` branch. -/
theorem lowerEllipticityProfile_finite_of_two_le (C gamma s : ℝ)
    (r : {r : ℝ // 1 ≤ r}) (hr : 2 ≤ (r : ℝ)) :
    lowerEllipticityProfile C gamma s (CoarseEllipticityExponent.finite r) =
      C * s * (2 * s - gamma)⁻¹ := by
  simp only [lowerEllipticityProfile, CoarseEllipticityExponent.finite,
    not_lt.mpr hr, ↓reduceIte]

/-- The deterministic lower profile at the infinity endpoint: the direct
constant, with no pole. -/
theorem lowerEllipticityProfile_infinity (C gamma s : ℝ) :
    lowerEllipticityProfile C gamma s CoarseEllipticityExponent.infinity = C :=
  rfl

/-! ## 2. The constant reconciliation of the corrected `q < 2` leg -/

/-- They differ by `2^{2/r} <= 4`, a dimension-only factor, because every
admissible exponent satisfies `1 <= r`. -/
theorem rpow_two_mul_div_le {x : ℝ} (hx : 0 ≤ x) {r : ℝ} (hr : 1 ≤ r) :
    Real.rpow (2 * x) (2 / r) ≤ 4 * Real.rpow x (2 / r) := by
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hexp : 2 / r ≤ 2 := by
    rw [div_le_iff₀ hrpos]
    linarith
  have hsplit : Real.rpow (2 * x) (2 / r)
      = Real.rpow 2 (2 / r) * Real.rpow x (2 / r) :=
    Real.mul_rpow (by norm_num) hx
  have hfour : Real.rpow 2 (2 / r) ≤ 4 := by
    have hmono : Real.rpow 2 (2 / r) ≤ Real.rpow 2 2 :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hstep : Real.rpow (2 : ℝ) (2 : ℝ) = Real.rpow (2 : ℝ) ((1 : ℝ) + 1) :=
      congrArg (Real.rpow (2 : ℝ)) (by norm_num)
    have htwo : Real.rpow (2 : ℝ) (2 : ℝ) = 4 :=
      calc Real.rpow (2 : ℝ) (2 : ℝ)
          = Real.rpow (2 : ℝ) ((1 : ℝ) + 1) := hstep
        _ = Real.rpow (2 : ℝ) 1 * Real.rpow (2 : ℝ) 1 :=
            Real.rpow_add (by norm_num) 1 1
        _ = 4 := by
            have hone : Real.rpow (2 : ℝ) 1 = 2 := Real.rpow_one 2
            rw [hone]
            norm_num
    exact htwo ▸ hmono
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hx _)

/-! ## 3. The all-`q` unification -/

/-- **The all-`q` lower payload from its three source branches.**

The frozen display's single deterministic slot
`lowerEllipticityProfile Clow gamma s q` is the union of three distinct source
facts; this theorem is the union, and nothing else.  Its output is verbatim the
`payload` binder of `coarse_ellipticity_lower_leg_body_of_familySplitPayload`,
so composing the two proves the local lower-leg result from the three branches.

All three inputs remain explicit obligations of this helper; a concrete
downstream caller supplies them in the proof of
`superposedFlux_coarse_ellipticity_lower_leg`. -/
theorem coarse_ellipticity_lower_payload_of_branchPayloads (d : ℕ) {Clow : ℝ}
    (payloadLtTwo :
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ r : {r : ℝ // 1 ≤ r}, (r : ℝ) < 2 →
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              ∃ Ydet Y : Cutoff.CutoffSample d → ℝ,
                (∀ omega, ∀ L : ℤ, m - 1 ≤ L →
                    Observable.cutoffLowerEllipticityInv
                          M m L s
                          (by
                            exact
                              (add_pos
                                (div_pos M.shellPrefix.gamma_pos (by norm_num))
                              (Real.exp_pos
                                (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                    M.gamma⁻¹)))).trans_le hsWindow.1)
                          (CoarseEllipticityExponent.finite r) omega *
                        (Annealed.sigmaBar M (m - 1) : ℝ) ≤
                      Ydet omega + Y omega) ∧
                (∀ omega, Ydet omega ≤
                  Clow * Real.rpow (s / (2 * s - M.gamma)) (2 / (r : ℝ))) ∧
                Measurable Y ∧
                HCPolySupport.IndependentSums.IsBigOWith
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma
                    ((1 - sigma) / 2)) Y
                  (Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))))
    (payloadTwoLe :
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ r : {r : ℝ // 1 ≤ r}, 2 ≤ (r : ℝ) →
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              ∃ Ydet Y : Cutoff.CutoffSample d → ℝ,
                (∀ omega, ∀ L : ℤ, m - 1 ≤ L →
                    Observable.cutoffLowerEllipticityInv
                          M m L s
                          (by
                            exact
                              (add_pos
                                (div_pos M.shellPrefix.gamma_pos (by norm_num))
                              (Real.exp_pos
                                (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                    M.gamma⁻¹)))).trans_le hsWindow.1)
                          (CoarseEllipticityExponent.finite r) omega *
                        (Annealed.sigmaBar M (m - 1) : ℝ) ≤
                      Ydet omega + Y omega) ∧
                (∀ omega, Ydet omega ≤
                  Clow * s * (2 * s - M.gamma)⁻¹) ∧
                Measurable Y ∧
                HCPolySupport.IndependentSums.IsBigOWith
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma
                    ((1 - sigma) / 2)) Y
                  (Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))))
    (payloadInfinity :
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              ∃ Ydet Y : Cutoff.CutoffSample d → ℝ,
                (∀ omega, ∀ L : ℤ, m - 1 ≤ L →
                    Observable.cutoffLowerEllipticityInv
                          M m L s
                          (by
                            exact
                              (add_pos
                                (div_pos M.shellPrefix.gamma_pos (by norm_num))
                              (Real.exp_pos
                                (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                    M.gamma⁻¹)))).trans_le hsWindow.1)
                          CoarseEllipticityExponent.infinity omega *
                        (Annealed.sigmaBar M (m - 1) : ℝ) ≤
                      Ydet omega + Y omega) ∧
                (∀ omega, Ydet omega ≤ Clow) ∧
                Measurable Y ∧
                HCPolySupport.IndependentSums.IsBigOWith
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma
                    ((1 - sigma) / 2)) Y
                  (Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))) :
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ q : CoarseEllipticityExponent,
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              ∃ Ydet Y : Cutoff.CutoffSample d → ℝ,
                (∀ omega, ∀ L : ℤ, m - 1 ≤ L →
                    Observable.cutoffLowerEllipticityInv
                          M m L s
                          (by
                            exact
                              (add_pos
                                (div_pos M.shellPrefix.gamma_pos (by norm_num))
                              (Real.exp_pos
                                (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                    M.gamma⁻¹)))).trans_le hsWindow.1)
                          q omega *
                        (Annealed.sigmaBar M (m - 1) : ℝ) ≤
                      Ydet omega + Y omega) ∧
                (∀ omega,
                  Ydet omega ≤ lowerEllipticityProfile Clow M.gamma s q) ∧
                Measurable Y ∧
                HCPolySupport.IndependentSums.IsBigOWith
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma
                    ((1 - sigma) / 2)) Y
                  (Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  intro M m E hstate sigma hsigma hE1 hE2 q s hsWindow
  rcases coarseEllipticityExponent_trichotomy q with
    ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | rfl
  · obtain ⟨Ydet, Y, hdom, hdet, hYmeas, htail⟩ :=
      payloadLtTwo M m E hstate sigma hsigma hE1 hE2 r hr s hsWindow
    refine ⟨Ydet, Y, hdom, ?_, hYmeas, htail⟩
    intro omega
    rw [lowerEllipticityProfile_finite_of_lt_two Clow M.gamma s r hr]
    exact hdet omega
  · obtain ⟨Ydet, Y, hdom, hdet, hYmeas, htail⟩ :=
      payloadTwoLe M m E hstate sigma hsigma hE1 hE2 r hr s hsWindow
    refine ⟨Ydet, Y, hdom, ?_, hYmeas, htail⟩
    intro omega
    rw [lowerEllipticityProfile_finite_of_two_le Clow M.gamma s r hr]
    exact hdet omega
  · obtain ⟨Ydet, Y, hdom, hdet, hYmeas, htail⟩ :=
      payloadInfinity M m E hstate sigma hsigma hE1 hE2 s hsWindow
    refine ⟨Ydet, Y, hdom, ?_, hYmeas, htail⟩
    intro omega
    rw [lowerEllipticityProfile_infinity Clow M.gamma s]
    exact hdet omega

/-! ## 4. The `2 <= q` branch, reduced to the per-scale block split -/


end Algsuperdiff.Section3.Provider.CoarseEllipticity
