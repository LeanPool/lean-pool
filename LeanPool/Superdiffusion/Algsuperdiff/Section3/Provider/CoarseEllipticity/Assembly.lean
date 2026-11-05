/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffMultiscaleEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ConstantWeakening

/-!
# Assembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `p.cg.ellipticity.bounds`: the two-leg assembly and the constant normalization

Proposition `p.cg.ellipticity.bounds` (ABK26, statement) is a single `∃ C(d)`
carrying **two** displays under one constant: `e.cg.ellip.lower` and
`e.cg.ellip.upper`.  Its frozen Lean surface is
`Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds`.

This module is the *assembly* layer directly below that frozen statement.  It
contains no analysis at all: it is the exact bookkeeping that lets the two
displays be proved **independently**, each with its own constant, and then be
combined into the frozen statement, and it is the exact bookkeeping that lets a
consumer normalize the frozen constant.

## What is proved here

* `coarse_ellipticity_bounds_body_of_legs` --- from the lower display at a
  constant `Clow > 0` and the upper display at a constant `Cup > 0`, the frozen
  `∀`-body at any common `Ccg ≥ max Clow Cup`.
* `coarse_ellipticity_bounds_of_legs` --- the **lossless conditional
  assembly**.  From the two legs, each in its own `∃ C > 0` form, it derives the
  frozen statement **verbatim**, at `Ccg = max Clow Cup`.  The proved frozen
  export now uses the exact application
  ```
  exact Algsuperdiff.Section3.Provider.CoarseEllipticity.coarse_ellipticity_bounds_of_legs
    d hlower hupper
  ```
  at the assembly layer, with `hlower` and `hupper` supplied by the proved
  production legs.

## Why the constant may be increased (the direction of every slot)

* `max (exp (C / sigma)) cstar⁻¹ ≤ E` --- an **hypothesis**, and it is
  **stronger** at the larger constant (`sigma > 0`), so it implies the
  hypothesis at the smaller one.
* `s ∈ Icc (gamma/2 + exp (-(C⁻¹E⁻²gamma⁻¹))) 1` --- an **hypothesis**, and its
  lower endpoint *increases* with `C` (because `C⁻¹` decreases and
  `E⁻²gamma⁻¹ ≥ 0`), so the window at the larger constant is contained in the
  window at the smaller one.
* the deterministic lower profile `lowerEllipticityProfile C gamma s q` --- a
  **conclusion** slot, and it increases with `C` in each of the three branches
  (`lowerEllipticityProfile_mono_const`).
* the rare-lane scale `exp (-(C⁻¹E⁻²gamma⁻¹))` --- a **conclusion** slot, and it
  increases with `C`.
* the upper deterministic shift `C` and its typical amplitude
  `C cstar⁻¹ s gamma (2s-gamma)⁻³` --- **conclusion** slots, both increasing in
  `C` on the source window (`cstar > 0`, `s > 0`, `gamma > 0`,
  `2s - gamma > 0`).

The two positivity facts `0 < s` and `0 < 2 * s - gamma` used above are
**theorems** from the source window, not binders: the window's lower endpoint
`gamma/2 + exp(...)` already exceeds `gamma/2`.

## The proof-term slot of the observables

The frozen statement passes the positivity proof `0 < s` to
`Observable.cutoffLowerEllipticityInv` / `Observable.cutoffUpperEllipticity` as
an explicit argument, built from `hsWindow.1`.  A leg stated at `Clow` builds
that argument from *its* window.  The two terms are proofs of the same `Prop`
and are therefore definitionally equal, so the observables literally coincide;
no transport is needed and none is performed.

## What is *not* claimed

This module itself does not prove or assign status to
`p.cg.ellipticity.bounds`.  What is delivered here is that the node factors
through two independently typed leg statements and that the frozen constant can
be normalized; this helper carries no node status.

## References

* ABK26, `p.cg.ellipticity.bounds`, statement, proof; `e.cg.ellip.lower`,
  `e.cg.ellip.upper`.
* All three are already encoded in the frozen statement and in
  `Algsuperdiff/Section3/Exponent.lean`; this module changes none of them.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3

/-- **The two-leg assembly, on the `∀`-body.**

From the lower coarse-ellipticity display at a constant `Clow` and the upper
one at a constant `Cup`, the frozen statement's `∀`-body holds at any common
constant `Ccg` dominating both.  Every slot moves in the direction that makes
this monotonicity, and only monotonicity; see the module docstring. -/
theorem coarse_ellipticity_bounds_body_of_legs (d : ℕ) {Clow Cup Ccg : ℝ}
    (hClow : 0 < Clow) (hCup : 0 < Cup)
    (hlowle : Clow ≤ Ccg) (huple : Cup ≤ Ccg)
    (hlow :
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
                                (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                    M.gamma⁻¹)))).trans_le hsWindow.1)
                          q omega *
                        (Annealed.sigmaBar M (m - 1) : ℝ))
                  (m - 1)
                  (lowerEllipticityProfile Clow M.gamma s q)
                  (Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))))
    (hup :
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Cup / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ q : CoarseEllipticityExponent,
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
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
                            (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                M.gamma⁻¹)))).trans_le hsWindow.1)
                      q omega *
                    (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹)
                Cup
                (Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
                  (2 * s - M.gamma)⁻¹ ^ 3)
                (Real.exp
                  (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))) :
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
  intro M m E hstate sigma hsigma hE1 hE2 q s hsWindow
  -- standing model facts
  have hgamma : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcstar : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hrate : (0 : ℝ) ≤ ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ :=
    mul_nonneg (sq_nonneg _) (inv_nonneg.2 hgamma.le)
  -- the source window already forces the two positivity facts
  have hexpCcg : (0 : ℝ) < Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
    Real.exp_pos _
  have hwin : M.gamma / 2 + Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ s :=
    hsWindow.1
  have hspos : (0 : ℝ) < s := by linarith
  have hgap : (0 : ℝ) < 2 * s - M.gamma := by linarith
  -- the rare-lane scale increases with the constant
  have hrateLow : Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ ≤
      Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (inv_anti₀ hClow hlowle) (sq_nonneg _))
      (inv_nonneg.2 hgamma.le)
  have hrateUp : Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ ≤
      Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (inv_anti₀ hCup huple) (sq_nonneg _))
      (inv_nonneg.2 hgamma.le)
  have hexpLow : Real.exp (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
      Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
    Real.exp_le_exp.2 (by linarith)
  have hexpUp : Real.exp (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
      Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
    Real.exp_le_exp.2 (by linarith)
  -- the admissibility gate is stronger at the larger constant
  have hsigmapos : (0 : ℝ) < sigma := hsigma.1
  have hE1low : max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    max_le ((Real.exp_le_exp.2 (by gcongr)).trans ((le_max_left _ _).trans hE1))
      ((le_max_right _ _).trans hE1)
  have hE1up : max (Real.exp (Cup / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    max_le ((Real.exp_le_exp.2 (by gcongr)).trans ((le_max_left _ _).trans hE1))
      ((le_max_right _ _).trans hE1)
  -- the source window is narrower at the larger constant
  have hwinlow : s ∈ Set.Icc
      (M.gamma / 2 + Real.exp (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1 :=
    ⟨by linarith, hsWindow.2⟩
  have hwinup : s ∈ Set.Icc
      (M.gamma / 2 + Real.exp (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1 :=
    ⟨by linarith, hsWindow.2⟩
  refine ⟨?_, ?_⟩
  · exact isLowerIntegerFamilyOrlicz_mono
      (hlow M m E hstate sigma hsigma hE1low hE2 q s hwinlow)
      (lowerEllipticityProfile_mono_const hspos.le hgap.le hlowle q) hexpLow
  · refine isDeterministicShiftTwoTermOneSidedOrlicz_mono
      (hup M m E hstate sigma hsigma hE1up hE2 q s hwinup) huple ?_ hexpUp
    have hfac : (0 : ℝ) ≤
        (Disorder.cstar M)⁻¹ * s * M.gamma * (2 * s - M.gamma)⁻¹ ^ 3 :=
      mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hcstar.le) hspos.le)
        hgamma.le) (pow_nonneg (inv_nonneg.2 hgap.le) 3)
    calc Cup * (Disorder.cstar M)⁻¹ * s * M.gamma * (2 * s - M.gamma)⁻¹ ^ 3
        = Cup * ((Disorder.cstar M)⁻¹ * s * M.gamma *
            (2 * s - M.gamma)⁻¹ ^ 3) := by ring
      _ ≤ Ccg * ((Disorder.cstar M)⁻¹ * s * M.gamma *
            (2 * s - M.gamma)⁻¹ ^ 3) := mul_le_mul_of_nonneg_right huple hfac
      _ = Ccg * (Disorder.cstar M)⁻¹ * s * M.gamma *
            (2 * s - M.gamma)⁻¹ ^ 3 := by ring

/-- **Lossless conditional assembly for `p.cg.ellipticity.bounds`.**

From the two printed displays, each supplied with its own dimension-only
constant, the frozen statement **verbatim**, at the combined constant `max Clow
Cup`.  Both displays remain explicit A arguments of this helper.  The concrete
downstream theorems `superposedFlux_coarse_ellipticity_lower_leg` and
`superposedFlux_coarse_ellipticity_upper_leg` supply the two arguments; this
conditional helper itself carries no node status. -/
theorem coarse_ellipticity_bounds_of_legs (d : ℕ)
    (hlower : ∃ Clow : ℝ, 0 < Clow ∧
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
                                (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                    M.gamma⁻¹)))).trans_le hsWindow.1)
                          q omega *
                        (Annealed.sigmaBar M (m - 1) : ℝ))
                  (m - 1)
                  (lowerEllipticityProfile Clow M.gamma s q)
                  (Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))))
    (hupper : ∃ Cup : ℝ, 0 < Cup ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Cup / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ q : CoarseEllipticityExponent,
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
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
                            (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                M.gamma⁻¹)))).trans_le hsWindow.1)
                      q omega *
                    (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹)
                Cup
                (Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
                  (2 * s - M.gamma)⁻¹ ^ 3)
                (Real.exp
                  (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))) :
    ∃ Ccg : ℝ, 0 < Ccg ∧
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
  obtain ⟨Clow, hClow, hlow⟩ := hlower
  obtain ⟨Cup, hCup, hup⟩ := hupper
  exact ⟨max Clow Cup, lt_of_lt_of_le hClow (le_max_left _ _),
    coarse_ellipticity_bounds_body_of_legs d hClow hCup (le_max_left _ _)
      (le_max_right _ _) hlow hup⟩


end Algsuperdiff.Section3.Provider.CoarseEllipticity
