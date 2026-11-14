/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.CoarseEllipticityBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseMomentsCloseOrlicz

/-!
# PrincipalResponseMomentsCloseEighth

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# Provider: the eighth-moment display

The second inequality of the first moment display in Step 3 of
`l.approximate.recurrence.formula` reads,

```
E[ |Ahom_{m-1}^{-1/2} A_m(cu_n) Ahom_{m-1}^{-1/2}|^8 ]^{1/8}
  <= C E[ ( shom_{m-1}^{-1} Lambda_{cgamma,1}(cu_m)
             + shom_{m-1} lambda^{-1}_{cgamma,1}(cu_m) )^8 ]^{1/8}
  <= C cgamma^{-1} .
```

This module supplies the **second** inequality, i.e. the eighth moment of the
gauged sum of the two multiscale ellipticity endpoints, directly from the frozen
coarse-graining ellipticity anchor
`Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds` at `s = cgamma`,
`q = finite 1`.  The first inequality (the deterministic operator bound) is the
subject of `PrincipalResponseMomentsOperator.lean` and is not touched here.

## How the anchor is used

The anchor supplies, for one dimensional constant `Ccg`, two weak-Orlicz legs:

* an `IsDeterministicShiftTwoTermOneSidedOrlicz` upper leg for
  `Lambda_{s,q}(cu_m; a_m) shom_{m-1}^{-1}`, at deterministic shift `Ccg` and
  two lanes `Gamma_1` and `Gamma_{(1-sigma)/3}`, of amplitudes
  `Ccg cstar^{-1} s cgamma (2s-cgamma)^{-3}` and `exp(-Ccg^{-1}E^{-2}cgamma^{-1})`;
* an `IsLowerIntegerFamilyOrlicz` lower leg for
  `lambda^{-1}_{s,q}(cu_m; a_L) shom_{m-1}` valid **simultaneously for every**
  `L >= m-1` with a single witness, at deterministic profile
  `lowerEllipticityProfile Ccg cgamma s q` and one lane
  `Gamma_{(1-sigma)/2}` of amplitude `exp(-Ccg^{-1}E^{-2}cgamma^{-1})`.

Adding the two endpoints therefore gives one deterministic shift and three
lanes, which is exactly the hypothesis of the engine
`integral_rpow_eight_le_of_shift_add_three_orlicz`.  Because the lower carrier's
witness does not depend on `L`, the supremum over `L >= m-1` costs nothing: the
statement below is uniform in `L`, quantified after the moment.

The free exponent `sigma` of the anchor is instantiated at its most permissive
admissible value `sigma = 1/2`, which is also the value that makes the anchor's
own premise `exp(Ccg/sigma) <= E` weakest.  The two small lanes then sit at the
fixed classes `Gamma_{1/6}` and `Gamma_{1/4}`, so the moment constants are
absolute and no uniformity in `sigma` is needed.

## Where `s = cgamma` sits in the window

The anchor's window is `s in [cgamma/2 + exp(-Ccg^{-1}E^{-2}cgamma^{-1}), 1]`.
Taking `s = cgamma` requires `exp(-Ccg^{-1}E^{-2}cgamma^{-1}) <= cgamma/2`,
which is a genuine smallness condition; it is carried below as the **explicit
gate** `hgap`, stated with the exported constant `C` (which the proof chooses
`>= Ccg`, so that `hgap` implies the anchor's own window condition).  No
printed buffer constant is hard-coded, as required.

This is `lowerEllipticityProfile_at_gamma_one`.

## Main results

* `coarseExponentOne`: the admissible finite exponent `q = 1`.
* `lowerEllipticityProfile_at_gamma_one`: the corrected lower profile collapses
  to `Ccg` at `s = cgamma`, `q = finite 1`.
* `integral_coarseEllipticityGauge_rpow_eight_le`: **the eighth-moment bound**.

## References

* ABK26 (the moment display of Step 3).
* ABK26, `p.cg.ellipticity.bounds`.
* ABK26, `e.cgamma.constraints` ("increasing `M`.").
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3

noncomputable section

/-- The admissible finite exponent `q = 1`. -/
def coarseExponentOne : CoarseEllipticityExponent :=
  CoarseEllipticityExponent.finite ⟨1, le_refl 1⟩

/-- **The corrected lower profile is `Ccg` at `s = cgamma`, `q = 1`.**  The base `s
/ (2s - cgamma)` of the corrected finite-`q` real power is exactly `1` there,
so its pole is inert. -/
theorem lowerEllipticityProfile_at_gamma_one (Ccg gamma : ℝ) (hgamma : 0 < gamma) :
    lowerEllipticityProfile Ccg gamma gamma coarseExponentOne = Ccg := by
  have hbase : gamma / (2 * gamma - gamma) = 1 := by
    rw [show 2 * gamma - gamma = gamma by ring, div_self (ne_of_gt hgamma)]
  simp only [coarseExponentOne, lowerEllipticityProfile, CoarseEllipticityExponent.finite,
    hbase]
  norm_num

/-- The aggregate lane constant of the display: the deterministic shifts of the
two legs plus the three class constants of the lanes, at `sigma = 1/2`. -/
def eighthLaneConst (Ccg : ℝ) : ℝ :=
  4 * (2 * Ccg + orliczEighthMomentScale 1 * Ccg +
    orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 3) +
    orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 2))

variable {d : ℕ}

/-- Absorb the common deterministic and Orlicz lanes into the eighth-moment constant. -/
theorem eighthLane_rpow_absorption (M : ABKModel d) (E Ccg C : ℝ)
    (hCcg0 : 0 < Ccg) (hLaneC : eighthLaneConst Ccg ≤ C) :
    (4 * (2 * Ccg + orliczEighthMomentScale 1 *
      (Ccg * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) +
      orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 3) *
        Real.exp (-(Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹)) +
      orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 2) *
        Real.exp (-(Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹)))) ^ (8 : ℝ) ≤
      (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) ^ (8 : ℝ) := by
  have hcstarPos : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hk10 : 0 < orliczEighthMomentScale 1 :=
    orliczEighthMomentScale_pos (by norm_num)
  have hk20 : 0 < orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 3) :=
    orliczEighthMomentScale_pos (by norm_num)
  have hk30 : 0 < orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 2) :=
    orliczEighthMomentScale_pos (by norm_num)
  have hcinvPos : (0 : ℝ) < (Disorder.cstar M)⁻¹ := inv_pos.2 hcstarPos
  have hginvPos : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 hgammaPos
  have hcinv : (2 : ℝ) / 3 ≤ (Disorder.cstar M)⁻¹ := by
    calc (2 : ℝ) / 3 = ((3 : ℝ) / 2)⁻¹ := by norm_num
      _ ≤ (Disorder.cstar M)⁻¹ :=
          inv_anti₀ hcstarPos (Provider.Disorder.cstar_le_three_halves M)
  have hginv : (4 : ℝ) ≤ M.gamma⁻¹ := by
    calc (4 : ℝ) = ((1 : ℝ) / 4)⁻¹ := by norm_num
      _ ≤ M.gamma⁻¹ := inv_anti₀ hgammaPos M.shellPrefix.gamma_le_quarter
  have ht1 : (1 : ℝ) ≤ (Disorder.cstar M)⁻¹ * M.gamma⁻¹ := by
    have h := mul_le_mul hcinv hginv (by norm_num : (0 : ℝ) ≤ 4) hcinvPos.le
    linarith
  have ht0 : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ * M.gamma⁻¹ := by linarith
  have hAnn : (0 : ℝ) ≤ Ccg * (Disorder.cstar M)⁻¹ * M.gamma⁻¹ :=
    (mul_pos (mul_pos hCcg0 hcinvPos) hginvPos).le
  have hsmall : Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ 1 := by
    refine Real.exp_le_one_iff.2 ?_
    have hnn : (0 : ℝ) ≤ Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := by positivity
    linarith
  have hexpT : Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
      (Disorder.cstar M)⁻¹ * M.gamma⁻¹ := hsmall.trans ht1
  refine Real.rpow_le_rpow ?_ ?_ (by norm_num)
  · have h1 : (0 : ℝ) ≤ orliczEighthMomentScale 1 *
        (Ccg * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) := mul_nonneg hk10.le hAnn
    have h2 : (0 : ℝ) ≤ orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 3) *
        Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
      mul_nonneg hk20.le (Real.exp_pos _).le
    have h3 : (0 : ℝ) ≤ orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 2) *
        Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
      mul_nonneg hk30.le (Real.exp_pos _).le
    linarith
  · have h0 : 2 * Ccg ≤ 2 * Ccg * ((Disorder.cstar M)⁻¹ * M.gamma⁻¹) :=
      le_mul_of_one_le_right (by linarith) ht1
    have h2 : orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 3) *
          Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
        orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 3) *
          ((Disorder.cstar M)⁻¹ * M.gamma⁻¹) :=
      mul_le_mul_of_nonneg_left hexpT hk20.le
    have h3 : orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 2) *
          Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
        orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 2) *
          ((Disorder.cstar M)⁻¹ * M.gamma⁻¹) :=
      mul_le_mul_of_nonneg_left hexpT hk30.le
    have hkey : 4 * (2 * Ccg + orliczEighthMomentScale 1 *
          (Ccg * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) +
        orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 3) *
          Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) +
        orliczEighthMomentScale ((1 - (1 : ℝ) / 2) / 2) *
          Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) ≤
        eighthLaneConst Ccg * ((Disorder.cstar M)⁻¹ * M.gamma⁻¹) := by
      rw [eighthLaneConst]
      linarith
    refine hkey.trans ?_
    calc eighthLaneConst Ccg * ((Disorder.cstar M)⁻¹ * M.gamma⁻¹)
        ≤ C * ((Disorder.cstar M)⁻¹ * M.gamma⁻¹) :=
          mul_le_mul_of_nonneg_right hLaneC ht0
      _ = C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹ := by ring


/-! ## The eighth moment of the gauged ellipticity sum -/

/-- **The second inequality of the moment display at ABK26.**

For one constant `C` depending only on the dimension, whenever the induction
state holds at scale `m-1` with parameter `E`, the parameters obey the anchor's
own premises, and the anchor's lower window endpoint sits below `cgamma`, the
gauged sum of the two multiscale ellipticity endpoints lies in `L^8` and has
eighth moment inside `(C cstar^{-1} cgamma^{-1})^8`, uniformly over the family
index `L >= m-1` of the anchor's lower leg. -/
theorem integral_coarseEllipticityGauge_rpow_eight_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        max (Real.exp (2 * C)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
        M.gamma / 2 + Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma →
        ∀ L : ℤ, m - 1 ≤ L →
          MemLp
              (fun omega =>
                Observable.cutoffUpperEllipticity M m m M.gamma
                      M.shellPrefix.gamma_pos coarseExponentOne omega *
                    (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ +
                  Observable.cutoffLowerEllipticityInv M m L M.gamma
                      M.shellPrefix.gamma_pos coarseExponentOne omega *
                    (Annealed.sigmaBar M (m - 1) : ℝ))
              8 (Cutoff.cutoffSampleLaw M).toMeasure ∧
            ∫ omega,
                (Observable.cutoffUpperEllipticity M m m M.gamma
                      M.shellPrefix.gamma_pos coarseExponentOne omega *
                    (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ +
                  Observable.cutoffLowerEllipticityInv M m L M.gamma
                      M.shellPrefix.gamma_pos coarseExponentOne omega *
                    (Annealed.sigmaBar M (m - 1) : ℝ)) ^ (8 : ℝ)
                ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
              (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) ^ (8 : ℝ) := by
  obtain ⟨Ccg, hCcg0, hCcg⟩ := Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds d
  refine ⟨max Ccg (eighthLaneConst Ccg), lt_of_lt_of_le hCcg0 (le_max_left _ _), ?_⟩
  intro M m E hstate hE hEupper hgap L hL
  set C : ℝ := max Ccg (eighthLaneConst Ccg) with hC
  have hCcgleC : Ccg ≤ C := by rw [hC]; exact le_max_left _ _
  have hLaneC : eighthLaneConst Ccg ≤ C := by rw [hC]; exact le_max_right _ _
  have hC0 : 0 < C := lt_of_lt_of_le hCcg0 hCcgleC
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hgammaNe : M.gamma ≠ 0 := ne_of_gt hgammaPos
  have hcstarPos : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  -- the anchor's premises at `sigma = 1/2`
  have hsigma : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨by norm_num, le_refl _⟩
  have hEanchor : max (Real.exp (Ccg / (1 / 2))) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hE)
    refine le_trans (Real.exp_le_exp.2 ?_) ((le_max_left _ _).trans hE)
    have : Ccg / (1 / 2 : ℝ) = 2 * Ccg := by ring
    rw [this]
    linarith
  have hXpos : (0 : ℝ) ≤ ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := by positivity
  have hexpMono :
      Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
        Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) := by
    refine Real.exp_le_exp.2 ?_
    have hinv : C⁻¹ ≤ Ccg⁻¹ := by
      exact inv_anti₀ hCcg0 hCcgleC
    have : C⁻¹ * (((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) ≤ Ccg⁻¹ * (((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) :=
      mul_le_mul_of_nonneg_right hinv hXpos
    linarith [this]
  have hwin : M.gamma ∈ Set.Icc
      (M.gamma / 2 + Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1 := by
    constructor
    · linarith [hexpMono, hgap]
    · linarith [M.shellPrefix.gamma_le_quarter]
  obtain ⟨hLower, hUpper⟩ :=
    hCcg M m E hstate (1 / 2) hsigma hEanchor hEupper coarseExponentOne M.gamma hwin
  obtain ⟨W, hW⟩ := hLower
  obtain ⟨_hUmeas, Y, Z, _hPsi1, _hPsi2, hA1pos, hA2pos, _hshiftMeas, hYm, hZm,
    hdomYZ, hYt, hZt⟩ := hUpper
  -- the deterministic profile of the lower leg at `s = cgamma`, `q = 1`
  have hprof := lowerEllipticityProfile_at_gamma_one Ccg M.gamma hgammaPos
  -- the polynomial amplitude of the `Gamma_1` lane at `s = cgamma`
  have hA1eq :
      Ccg * (Disorder.cstar M)⁻¹ * M.gamma * M.gamma * (2 * M.gamma - M.gamma)⁻¹ ^ 3 =
        Ccg * (Disorder.cstar M)⁻¹ * M.gamma⁻¹ := by
    rw [show 2 * M.gamma - M.gamma = M.gamma by ring]
    field_simp
  -- the domination of the summed observable
  have hX0 : ∀ omega,
      0 ≤ Observable.cutoffUpperEllipticity M m m M.gamma
              M.shellPrefix.gamma_pos coarseExponentOne omega *
            (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ +
          Observable.cutoffLowerEllipticityInv M m L M.gamma
              M.shellPrefix.gamma_pos coarseExponentOne omega *
            (Annealed.sigmaBar M (m - 1) : ℝ) := by
    intro omega
    have hsig : (0 : ℝ) < (Annealed.sigmaBar M (m - 1) : ℝ) :=
      (Annealed.sigmaBar M (m - 1)).2
    have h1 := Observable.cutoffUpperEllipticity_nonneg M m m M.gamma
      M.shellPrefix.gamma_pos coarseExponentOne omega
    have h2 := Observable.cutoffLowerEllipticityInv_nonneg M m L M.gamma
      M.shellPrefix.gamma_pos coarseExponentOne omega
    have h3 : (0 : ℝ) ≤ (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ := (inv_pos.2 hsig).le
    positivity
  have hdom : ∀ omega,
      Observable.cutoffUpperEllipticity M m m M.gamma
            M.shellPrefix.gamma_pos coarseExponentOne omega *
          (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ +
        Observable.cutoffLowerEllipticityInv M m L M.gamma
            M.shellPrefix.gamma_pos coarseExponentOne omega *
          (Annealed.sigmaBar M (m - 1) : ℝ) ≤
        2 * Ccg + Y omega + Z omega + W omega := by
    intro omega
    have hup := hdomYZ omega
    have hlow := hW.dominates omega L hL
    rw [hprof] at hlow
    simp only at hup hlow
    linarith
  have hXm : AEStronglyMeasurable
      (fun omega =>
        Observable.cutoffUpperEllipticity M m m M.gamma
              M.shellPrefix.gamma_pos coarseExponentOne omega *
            (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ +
          Observable.cutoffLowerEllipticityInv M m L M.gamma
              M.shellPrefix.gamma_pos coarseExponentOne omega *
            (Annealed.sigmaBar M (m - 1) : ℝ))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (((Observable.measurable_cutoffUpperEllipticity M m m M.gamma
            M.shellPrefix.gamma_pos coarseExponentOne).mul_const _).add
        ((Observable.measurable_cutoffLowerEllipticityInv M m L M.gamma
            M.shellPrefix.gamma_pos coarseExponentOne).mul_const _)).aestronglyMeasurable
  have hmain := integral_rpow_eight_le_of_shift_add_three_orlicz
    (mu := (Cutoff.cutoffSampleLaw M).toMeasure)
    (b := 2 * Ccg) (s1 := 1)
    (by norm_num) (by norm_num) (by norm_num) hA1pos hA2pos hW.scale_pos
    (by linarith) hYm hZm hW.measurable_witness hYt hZt hW.tail hXm hX0 hdom
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  rw [hA1eq]
  exact eighthLane_rpow_absorption M (E : ℝ) Ccg C hCcg0 hLaneC

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
