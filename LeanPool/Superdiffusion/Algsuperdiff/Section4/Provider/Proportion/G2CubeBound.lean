/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ErrorSwitch
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2Score
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.TranslationCovariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionBounds

/-!
# G2CubeBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-cube two-term display of the `𝒢₂` atom (`hcube`)

ABK26, §4.1, Step 1 of `l.ratio.of.good.scales.for.mathcal.E`:

> By Proposition `p.induction.bounds`, subadditivity of `𝓔`,
> `e.powerofGammasigma` and `e.maxy.bound` …

This module discharges the **first two** of those four citations for the `𝒢₂`
per-cube atom, i.e. it produces

```
𝓔_{s,2,2}(□_n; 𝐚_{n−2}, σ_{n−2}) ≤ 𝒪_{Γ_2}(A₁) + 𝒪_{Γ_{1/2}}(A₂)
```

— the hypothesis `hcube` of `isTwoTermBigOWith_errorAnnMax`.  (The remaining two
citations, `e.powerofGammasigma` and `e.maxy.bound`, are already performed in
`G2AtomTail.lean`.)

## The reading of the citation

The anchor `Frozen.Section3.induction_bounds` is stated at the **diagonal**
triple `(𝐚_m, □_m, σ_m)` and at the exponent pair `(∞,2)`; the `𝒢₂` atom needs
the **off-diagonal** triple `(𝐚_{n−2}, □_n, σ_{n−2})` at `(2,2)`.  Read at
`m:= n − 2`, the anchor already carries the atom's coefficient scale **and**
its comparator scale: `𝐚_{n−2}` and `σ_{n−2}`.  The *only* remaining
discrepancy is the domain scale, `n − 2` versus `n`, and that is exactly what
"subadditivity of `𝓔`" transports — from the `3^{2d}` sub-cubes of `□_n` at
scale `n − 2` up to `□_n` itself.  No field switch and no comparator switch
occurs anywhere in the derivation.

The three ingredients:

* `Support.homogenizationErrorOnCube_two_two_le_sqrt_three_mul` — subadditivity
  of `𝓔` at `(2,2)`, two scales up, at the numerical cost `√3` (`ErrorSwitch`).
* `BadEvents.homogenizationErrorOnCube_translateCutoffSample` — the exponent-
  generic pathwise translation covariance, which turns the functional at a
  sub-cube into the functional at the centred cube read at a translated sample.
  This is stationarity, not a new estimate.
* `isBigOWith_fmax` at the machine-computed count `#(descendants) = (3^d)^2` —
  `e.maxy.bound` over the sub-cubes.  Its cost is the dimensional penalty
  `annulusPenalty d σ 1 = (1 + 2d log 3)^{1/σ}`, a constant.

## Scope

Provider material: proved local helpers.

## References

* ABK26, `p.induction.bounds`, `e.subaddJ.nosymm`,
  `e.mathcalE.squared.max.bound`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- The paper-wide assumption `2 ≤ d`, stored in the model. -/
private theorem neZero_of_model (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-! ## The sub-cube count -/

/-- The descendants of a triadic cube two scales down number `(3^d)^2`. -/
private theorem card_descendantsAtScale_sub_two (Q : TriadicCube d) :
    (descendantsAtScale Q (Q.scale - 2)).card = (3 ^ d) ^ 2 := by
  have hk : Q.scale - 2 ≤ Q.scale := by omega
  have hdepth : Int.toNat (Q.scale - (Q.scale - 2)) = 2 := by
    rw [sub_sub_cancel]
    rfl
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk, hdepth, descendantsAtDepth_card]

/-- `log #(sub-cubes) ≤ annulusPenalty d σ 1 ^ σ − 1`: the interface the union
bound `isBigOWith_fmax` consumes, at the sub-cube family. -/
private theorem log_card_le_annulusPenalty_one (Q : TriadicCube d) {sigma : ℝ}
    (hsigma : 0 < sigma) :
    Real.log (((descendantsAtScale Q (Q.scale - 2)).card : ℕ) : ℝ) ≤
      annulusPenalty d sigma 1 ^ sigma - 1 := by
  have hlog : Real.log (((descendantsAtScale Q (Q.scale - 2)).card : ℕ) : ℝ) =
      2 * (d : ℝ) * Real.log 3 := by
    rw [card_descendantsAtScale_sub_two Q]
    push_cast
    rw [← pow_mul, Real.log_pow]
    push_cast
    ring
  rw [hlog]
  refine le_of_eq ?_
  rw [annulusPenalty_rpow d hsigma 1]
  push_cast
  ring

/-! ## The per-cube two-term display -/

/-- **The `𝒢₂` per-cube atom, from the anchor at the coefficient scale.**

Given the two-term `(Γ_2, Γ_{1/2})` display for the `(∞,2)` cutoff homogenization
error at the DIAGONAL scale `n − 2` — which is exactly what
`Frozen.Section3.induction_bounds` supplies — the `𝒢₂` observable
`𝓔_{s,2,2}(□_n; 𝐚_{n−2}, σ_{n−2})` obeys the same two-term display, with the
amplitudes multiplied by `√3` (subadditivity of `𝓔`) and by the dimensional
union-bound penalty over the `(3^d)^2` sub-cubes. -/
theorem isTwoTermBigOWith_annularErrorObservable_of_diagonal (M : ABKModel d)
    {s : ℝ} (hs : 0 < s) (n : ℤ) {A1 A2 : ℝ}
    (hdiag : Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M (n - 2) ⟨s, hs⟩) A1 A2) :
    Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Support.annularErrorObservable M n ⟨s, hs⟩)
      (Real.sqrt 3 * (annulusPenalty d 2 1 * A1))
      (Real.sqrt 3 * (annulusPenalty d (1 / 2) 1 * A2)) := by
  classical
  let : NeZero d := neZero_of_model M
  obtain ⟨Y, Z, -, -, hA1, hA2, -, hYm, hZm, hdom, hYt, hZt⟩ := hdiag
  set law := (Cutoff.cutoffSampleLaw M).toMeasure with hlaw
  set a0 := Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (n - 2)) with ha0
  set Qn : TriadicCube d := originCube d n with hQn
  set S := descendantsAtScale Qn (Qn.scale - 2) with hS
  -- the two translated maxima
  set Ymax : Cutoff.CutoffSample d → ℝ := fun omega =>
    fmax S (fun R => Y (Cutoff.translateCutoffSample (triadicCubeShift R) omega))
    with hYmax
  set Zmax : Cutoff.CutoffSample d → ℝ := fun omega =>
    fmax S (fun R => Z (Cutoff.translateCutoffSample (triadicCubeShift R) omega))
    with hZmax
  have hYmaxm : Measurable Ymax :=
    measurable_fmax _ fun R => hYm.comp (Cutoff.measurable_translateCutoffSample _)
  have hZmaxm : Measurable Zmax :=
    measurable_fmax _ fun R => hZm.comp (Cutoff.measurable_translateCutoffSample _)
  have hYmaxt : IsBigOWith law (gammaSigma 2) Ymax (annulusPenalty d 2 1 * A1) :=
    isBigOWith_fmax _ (by norm_num) hA1.le
      (one_le_annulusPenalty d (by norm_num) 1)
      (log_card_le_annulusPenalty_one Qn (by norm_num))
      (fun R _ => isBigOWith_comp_measurePreserving
        (GoodEvents.measurePreserving_translateCutoffSample M _) hYm hYt)
  have hZmaxt : IsBigOWith law (gammaSigma (1 / 2)) Zmax
      (annulusPenalty d (1 / 2) 1 * A2) :=
    isBigOWith_fmax _ (by norm_num) hA2.le
      (one_le_annulusPenalty d (by norm_num) 1)
      (log_card_le_annulusPenalty_one Qn (by norm_num))
      (fun R _ => isBigOWith_comp_measurePreserving
        (GoodEvents.measurePreserving_translateCutoffSample M _) hZm hZt)
  -- (i) the observable is a.e. the literal `(2,2)` error at the centred cube
  have hobs : Support.annularErrorObservable M n ⟨s, hs⟩ =ᵐ[law]
      fun omega => Ch02.HomogenizationErrorOnCube Qn s (.finite 2) (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M (n - 2) omega) a0 := by
    refine (Support.annularErrorAtom_ae_eq_annularErrorObservable M n ⟨s, hs⟩).symm.trans
      (Filter.Eventually.of_forall fun omega => ?_)
    exact Support.cutoffHomogenizationErrorRaw22_characterization M (n - 2) n s
      (Annealed.sigmaBar M (n - 2)) omega
  -- (ii) at every sub-cube, the literal `(∞,2)` error is a.e. dominated by the
  -- anchor's two witnesses read at the translated sample
  have hsub : ∀ᵐ omega ∂law, ∀ R ∈ S,
      Ch02.HomogenizationErrorOnCube R s .infinity (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M (n - 2) omega) a0 ≤
        Y (Cutoff.translateCutoffSample (triadicCubeShift R) omega) +
          Z (Cutoff.translateCutoffSample (triadicCubeShift R) omega) := by
    rw [Filter.eventually_all_finset]
    intro R hR
    have hscaleR : R.scale = Qn.scale - 2 :=
      descendant_scale_eq_of_mem_descendantsAtScale hR
    have hraw : ∀ᵐ omega ∂law,
        Observable.cutoffHomogenizationErrorRaw M (n - 2) (n - 2) s
            (Annealed.sigmaBar M (n - 2))
            (Cutoff.translateCutoffSample (triadicCubeShift R) omega) =
          Observable.cutoffHomogenizationError M (n - 2) ⟨s, hs⟩
            (Cutoff.translateCutoffSample (triadicCubeShift R) omega) :=
      (GoodEvents.measurePreserving_translateCutoffSample M
        (triadicCubeShift R)).quasiMeasurePreserving.ae
        (Observable.cutoffHomogenizationErrorRaw_ae_eq_representative M (n - 2)
          (n - 2) hs (Annealed.sigmaBar M (n - 2)))
    filter_upwards [hraw] with omega hrawomega
    have hcov := Provider.BadEvents.homogenizationErrorOnCube_translateCutoffSample
      M (n - 2) R s .infinity (.finite 2) a0 omega
    have hscaleQ : Qn.scale = n := rfl
    rw [hscaleR, hscaleQ] at hcov
    have hchar := Observable.cutoffHomogenizationErrorRaw_characterization M (n - 2)
      (n - 2) s (Annealed.sigmaBar M (n - 2))
      (Cutoff.translateCutoffSample (triadicCubeShift R) omega)
    rw [hcov, ← hchar, hrawomega]
    exact hdom _
  -- (iii) assemble the pointwise domination
  have hle : ∀ᵐ omega ∂law, Support.annularErrorObservable M n ⟨s, hs⟩ omega ≤
      Real.sqrt 3 * Ymax omega + Real.sqrt 3 * Zmax omega := by
    filter_upwards [hobs, hsub] with omega hobsomega hsubomega
    have hB0 : 0 ≤ Ymax omega + Zmax omega :=
      add_nonneg (fmax_nonneg _ _) (fmax_nonneg _ _)
    have hbd : ∀ R ∈ descendantsAtScale Qn (Qn.scale - 2),
        Ch02.HomogenizationErrorOnCube R s .infinity (.finite 2)
          (Cutoff.coefficientCutoffTriadicCoeffFamily M (n - 2) omega) a0 ≤
          Ymax omega + Zmax omega := by
      intro R hR
      have hRS : R ∈ S := hR
      refine (hsubomega R hRS).trans ?_
      exact add_le_add
        (le_fmax (S := S)
          (f := fun T => Y (Cutoff.translateCutoffSample (triadicCubeShift T) omega)) hRS)
        (le_fmax (S := S)
          (f := fun T => Z (Cutoff.translateCutoffSample (triadicCubeShift T) omega)) hRS)
    have hkey := Support.homogenizationErrorOnCube_two_two_le_sqrt_three_mul Qn hs
      (Cutoff.coefficientCutoffTriadicCoeffFamily M (n - 2) omega) a0 hB0 hbd
    rw [hobsomega]
    calc Ch02.HomogenizationErrorOnCube Qn s (.finite 2) (.finite 2)
            (Cutoff.coefficientCutoffTriadicCoeffFamily M (n - 2) omega) a0
        ≤ Real.sqrt 3 * (Ymax omega + Zmax omega) := hkey
      _ = Real.sqrt 3 * Ymax omega + Real.sqrt 3 * Zmax omega := by ring
  refine Provider.Tail.isTwoTermBigOWith_of_ae_le
    (Probability.isAdmissibleTail_gammaSigma (by norm_num))
    (Probability.isAdmissibleTail_gammaSigma (by norm_num))
    ?_ ?_ (Support.measurable_annularErrorObservable M n ⟨s, hs⟩)
    (hYmaxm.const_mul _) (hZmaxm.const_mul _) hle
    (hYmaxt.const_mul (Real.sqrt_nonneg 3)) (hZmaxt.const_mul (Real.sqrt_nonneg 3))
  · have hpen : (0 : ℝ) < annulusPenalty d 2 1 :=
      lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    exact mul_pos h3 (mul_pos hpen hA1)
  · have hpen : (0 : ℝ) < annulusPenalty d (1 / 2) 1 :=
      lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    exact mul_pos h3 (mul_pos hpen hA2)

/-! ## The endpoint -/

/-- **`hcube`, unconditionally, from the Section 3 anchor.**

For every model in the printed regime `γ ≤ C^{−10}c⋆^{10}` and every `s` in the
standing window `[8γ, 1]`, the `𝒢₂` per-cube observable
`𝓔_{s,2,2}(□_n; 𝐚_{n−2}, σ_{n−2})` obeys a two-term `(Γ_2, Γ_{1/2})` display
**with amplitudes independent of `n`** — the hypothesis `hcube` of
`isTwoTermBigOWith_errorAnnMax`, `isTwoTermBigOWith_Xcal` and the `𝒢₂` moment
engine.

The only hypotheses are the anchor's own: the dimensional constant `C`, the
regime `γ ≤ C^{−10}c⋆^{10}` (the transfer gap, carried explicitly rather than
assumed away) and the window `s ∈ [8γ, 1]`. -/
theorem exists_isTwoTermBigOWith_annularErrorObservable (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
          ∀ n : ℤ,
            Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
              (gammaSigma 2) (gammaSigma (1 / 2))
              (Support.annularErrorObservable M n
                ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8)
                  M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              (Real.sqrt 3 * (annulusPenalty d 2 1 *
                (C * (Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma)))
              (Real.sqrt 3 * (annulusPenalty d (1 / 2) 1 *
                Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹)))) := by
  obtain ⟨C, hC, hbounds⟩ := Algsuperdiff.Frozen.Section3.induction_bounds d
  refine ⟨C, hC, fun M hregime s hsWindow n => ?_⟩
  exact isTwoTermBigOWith_annularErrorObservable_of_diagonal M
    ((mul_pos (by norm_num : (0 : ℝ) < 8) M.shellPrefix.gamma_pos).trans_le hsWindow.1)
    n ((hbounds M hregime).1 (n - 2) s hsWindow)

end

end Algsuperdiff.Section4.Provider.Proportion
