/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2CubeBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MajorantMeasurability

/-!
# ErrorSlotB4

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# B4 at the Step-3 shell cube: the two-scale `(2,2)` error display

## What this module does

Bullet (B4) quotes `p.induction.bounds` at the off-diagonal triple
`(𝓔_{s,2,2}, □_j, 𝐚_{j−2}, shom_{j−2})` while the proposition is proved at the
diagonal triple and at the exponent pair `(∞,2)`.

That gap is already closed in the Section-4 material proved here, and this
module records the exact handle and lifts it to the cube family the Step-3
shell actually uses:

* the index shift and the exponent switch are
  `Proportion.exists_isTwoTermBigOWith_annularErrorObservable`, which reads the
  `Frozen.Section3.induction_bounds` at `m := j − 2` (so the coefficient scale
  `𝐚_{j−2}` AND the comparator scale `σ_{j−2}` are the anchor's own) and lifts
  the DOMAIN scale from `j − 2` to `j` through
  `Support.homogenizationErrorOnCube_two_two_le_sqrt_three_mul` (subadditivity
  of `𝓔` at the finite spatial exponent, cost `√3`) and the maximum lemma over
  the `(3^d)^2` sub-cubes (cost `Proportion.annulusPenalty d σ 1`, a
  `d`-constant);
* the passage from the O cube `□_j` to the Step-3 shell cube `3^j v + □_j` is
  stationarity: `isTwoTermBigOWith_comp_translateCutoffSample` below carries a
  two-term display along any real translation of the sample, because both
  witnesses are carried by the proved one-term transport
  `Stream.isBigOWith_comp_translateCutoffSample`.

## What is NOT claimed

No moment conversion is performed here: bullet (B4)'s "hence, for every `q ∈
[1,∞)`" line (`e.moments.OGamma2`) is a separate Step-4 item.

## References

* ABK26, (bullet (B4)), (`p.induction.bounds`),
  (`e.mathcalE.squared.max.bound`).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Provider.Annular

noncomputable section

variable {d : ℕ}

/-! ## 1. Two-term displays travel along real translations of the sample -/

/-- **Stationarity for a two-term display.**  Both witnesses of a
`Probability.IsTwoTermBigOWith` are ordinary one-term weak-Orlicz bounds, and the
cutoff-sample law is invariant under every real translation, so the whole display
holds verbatim for the observable read at the translated sample. -/
theorem isTwoTermBigOWith_comp_translateCutoffSample (M : ABKModel d) (z : Vec d)
    {Psi1 Psi2 : ℝ → ℝ} {X : Cutoff.CutoffSample d → ℝ} {A1 A2 : ℝ}
    (h : Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      Psi1 Psi2 X A1 A2) :
    Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure Psi1 Psi2
      (fun omega : Cutoff.CutoffSample d => X (Cutoff.translateCutoffSample z omega))
      A1 A2 := by
  obtain ⟨Y, Z, hPsi1, hPsi2, hA1, hA2, hX, hY, hZ, hle, hYb, hZb⟩ := h
  refine ⟨fun omega : Cutoff.CutoffSample d => Y (Cutoff.translateCutoffSample z omega),
    fun omega : Cutoff.CutoffSample d => Z (Cutoff.translateCutoffSample z omega),
    hPsi1, hPsi2, hA1, hA2,
    hX.comp (Cutoff.measurable_translateCutoffSample z),
    hY.comp (Cutoff.measurable_translateCutoffSample z),
    hZ.comp (Cutoff.measurable_translateCutoffSample z),
    fun omega => hle _,
    isBigOWith_comp_translateCutoffSample M z hY hYb,
    isBigOWith_comp_translateCutoffSample M z hZ hZb⟩

/-! ## 2. B4 at the Step-3 shell cube -/

/-- **Bullet (B4) at every Step-3 shell cube.**

For every model in the anchor's regime and every `s` in its window, the `(2,2)`
homogenization error on the cube `3^j v + □_j` with the coefficient field
`𝐚_{j−2}` and the comparator `σ_{j−2}` obeys a two-term `(Γ₂, Γ_{1/2})`
display with amplitudes independent of the cube -- the printed `𝒪_{Γ₂}(C s^{-1}
γ^{1/2}) + 𝒪_{Γ_{1/2}}(exp(−C^{-1} γ^{-1}))`, with the manuscript's `C(d, c⋆)`
convention absorbing the explicit `√3 · annulusPenalty d σ 1 · c⋆`-factors
carried here. -/
theorem exists_isTwoTermBigOWith_annularErrorObservable_translate (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
          ∀ R : TriadicCube d,
            Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
              (gammaSigma 2) (gammaSigma (1 / 2))
              (fun omega : Cutoff.CutoffSample d =>
                Support.annularErrorObservable M R.scale
                  ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩
                  (Cutoff.translateCutoffSample
                    (Support.triadicLatticePoint R.scale R.index) omega))
              (Real.sqrt 3 * (Proportion.annulusPenalty d 2 1 *
                (C * (Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma)))
              (Real.sqrt 3 * (Proportion.annulusPenalty d (1 / 2) 1 *
                Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹)))) := by
  obtain ⟨C, hC, hall⟩ :=
    Proportion.exists_isTwoTermBigOWith_annularErrorObservable d
  refine ⟨C, hC, fun M hregime s hsWindow R => ?_⟩
  exact isTwoTermBigOWith_comp_translateCutoffSample M
    (Support.triadicLatticePoint R.scale R.index)
    (hall M hregime s hsWindow R.scale)

/-! ## 3. The a.e. bridge to the literal `(2,2)` error -/

/-- **The literal `(2,2)` error of the Step-3 shell agrees almost everywhere with
the observable of the display above.**  This is the honest interface: the literal
object is a.e. measurable only, so it can carry the display only through this
identification. -/
theorem ae_eq_annularErrorObservable_translate (M : ABKModel d)
    (R : TriadicCube d) (s : {s : ℝ // 0 < s}) :
    (fun omega : Cutoff.CutoffSample d =>
        Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError (s : ℝ)
          (.finite 2) (.finite 2)
          (unitRescaledCutoffCoeff M R (R.scale - 2) omega)
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (R.scale - 2))))
      =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      fun omega : Cutoff.CutoffSample d =>
        Support.annularErrorObservable M R.scale s
          (Cutoff.translateCutoffSample
            (Support.triadicLatticePoint R.scale R.index) omega) :=
  unitCubeHomogenizationError22_unitRescaledCutoffCoeff_ae_eq_annularErrorObservable
    M R.scale R.index s

end

end Algsuperdiff.Section4.Provider.BoundsEaL
