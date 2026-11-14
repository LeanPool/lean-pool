/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.Definitions
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffLawTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.TranslatedTransport

/-!
# OscillationProbability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The scale-resolved oscillation probability bound

This module proves the oscillation branch of ABK26's Lemma
`l.bad.event.probabilities` (statement, proof Step 2): for every integer scale
`j`, every centre `z` in `3^j Z^d` and every `L >= j`,

```
P[ B_{osc,L}(z + square_j) ] <= exp( - c E^{-2} gamma^{-1} 3^{(3/2)(L-j)} ) .
```

## The proof, and what each step uses

*Step 2* of the manuscript's proof reads: by `e.nabla.jk.O` and `e.maxy.bound`,
`3^{2j} ||grad j_L||_{W^{1,infinity}(z+square_j)} <= O_{Gamma_2}(^{gamma L -
(L-j)})`; comparing with the `e.BoscL.def` threshold gives `exp(-c c_star
gamma^{-1} 3^{2(4/5 - gamma)(L-j)})`, and then `gamma <= 1/20` converts the
exponent `2(4/5 - gamma)` into `3/2`.

Here the first display is `shellOscGauge_le_shellDerivGauge` together with the
proved translated single-shell gauge
`Provider.Stream.isBigOWith_gammaSigma_shellDerivGauge_cube_translate`
(`e.nabla.jk.O` at the base point `z`) transported to the cutoff sample law by
`Provider.Stream.isBigOWith_cutoffSampleLaw_comp_val`.  No maximum over centres
is taken, so `e.maxy.bound` (`l.maximums.Gamma.s`) is not needed at this point:
the translated law of a single shell already carries the amplitude of the
centered one.  The constant `C` of the manuscript's display is `1` here.

## Admissibility

The tail hypothesis of a weak-Orlicz bound is only available above the
amplitude, so the threshold-to-amplitude ratio must be at least one.  That is
exactly the content of `unitGate`, and
`unitGate_of_admissible` derives it from the manuscript's own admissibility
`e.bad.event.admissibility.prelim` with the dimension-only
choice `C(d) := 25 / delta_osc(d)^2`, so nothing is added to the source
hypotheses.

The conversion of `2(4/5 - gamma)` into `3/2` needs `gamma <= 1/20`, which the
manuscript's proof uses ("where we used `gamma <= 1/20` in the last step").

## Main results

* `measureReal_badOscAt_le`: the sharp bound, exponent `2(4/5 - gamma)(L-j)`.
* `measureReal_badOscAt_le_printed`: the manuscript's display `e.BoscL.prob`.

## References

* ABK26, `l.bad.event.probabilities`.
* ABK26, `e.nabla.jk.O`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## The admissibility gate -/

/-- The threshold-to-amplitude gate of the weak-Orlicz tail: the `e.BoscL.def`
threshold at `L = j` is at least the amplitude of `e.nabla.jk.O`. -/
def unitGate (M : ABKModel d) : Prop :=
  1 ≤ (1 / 5 : ℝ) * deltaOsc d * Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
    (Real.sqrt M.gamma)⁻¹

/-! ## The tail of the single-shell oscillation gauge -/

/-- `e.nabla.jk.O` at the base point of `Q`, transported to the cutoff sample
law and rescaled into the `e.BoscL.def` gauge: the manuscript's display
`3^{2j} ||grad j_L||_{W^{1,infinity}(z+square_j)} <= O_{Gamma_2}(3^{gamma L - (L-j)})`,
with constant one. -/
theorem isBigOWith_gammaSigma_shellOscGauge (M : ABKModel d) (Q : TriadicCube d)
    {L : ℤ} (hL : Q.scale ≤ L) :
    IndependentSums.IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 2) (shellOscGauge Q L)
      ((3 : ℝ) ^ (Q.scale : ℝ) * (3 : ℝ) ^ ((M.gamma - 1) * (L : ℝ))) := by
  have hshell := isBigOWith_gammaSigma_shellDerivGauge_cube_translate M hL
    (cubeBasePoint Q)
  have hcut :
      IndependentSums.IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (IndependentSums.gammaSigma 2)
        (fun omega : CutoffSample d =>
          localCubeDerivNorm Q.scale
              (ShellField.translate (cubeBasePoint Q) (omega.1 L)) +
            (3 : ℝ) ^ Q.scale *
              localCubeSecondDerivNorm Q.scale
                (ShellField.translate (cubeBasePoint Q) (omega.1 L)))
        ((3 : ℝ) ^ ((M.gamma - 1) * (L : ℝ))) :=
    isBigOWith_cutoffSampleLaw_comp_val hshell
  have hscaled := hcut.const_mul
    (c := (3 : ℝ) ^ (Q.scale : ℝ))
    (Real.rpow_nonneg (by norm_num) _)
  refine hscaled.of_le fun omega => ?_
  have hz : (3 : ℝ) ^ (Q.scale : ℝ) = (3 : ℝ) ^ Q.scale := by
    rw [Real.rpow_intCast]
  rw [hz]
  exact shellOscGauge_le_shellDerivGauge Q L omega

/-! ## The probability bound -/

/-- The sharp form of ABK26 `e.BoscL.prob`: the exponent carries the honest rate
`2(4/5 - gamma)(L-j)` and the explicit constant `delta_osc(d)^2 / 25`. -/
theorem measureReal_badOscAt_le (M : ABKModel d) (Q : TriadicCube d) {L : ℤ}
    (hL : Q.scale ≤ L) (hgate : unitGate M) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real (badOscAt M Q L) ≤
      Real.exp (-((1 / 25 : ℝ) * deltaOsc d ^ 2 *
        Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * (4 / 5 - M.gamma) * ((L : ℝ) - (Q.scale : ℝ))))) := by
  classical
  have hc : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hgq : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hLR : (0 : ℝ) ≤ (L : ℝ) - (Q.scale : ℝ) := by
    have : (Q.scale : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  set base : ℝ := (1 / 5 : ℝ) * deltaOsc d *
    Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹
    with hbase
  set t : ℝ := base * (3 : ℝ) ^ ((4 / 5 - M.gamma) * ((L : ℝ) - (Q.scale : ℝ)))
    with ht
  -- the tail is applicable
  have hpow_ge_one : (1 : ℝ) ≤
      (3 : ℝ) ^ ((4 / 5 - M.gamma) * ((L : ℝ) - (Q.scale : ℝ))) := by
    refine Real.one_le_rpow (by norm_num) ?_
    have h45 : (0 : ℝ) ≤ 4 / 5 - M.gamma := by linarith
    exact mul_nonneg h45 hLR
  have ht1 : 1 ≤ t := by
    rw [ht]
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ base * (3 : ℝ) ^ ((4 / 5 - M.gamma) * ((L : ℝ) - (Q.scale : ℝ))) :=
        mul_le_mul hgate hpow_ge_one (by norm_num) (le_trans zero_le_one hgate)
  -- the amplitude times `t` is exactly the threshold
  have hamp : (3 : ℝ) ^ (Q.scale : ℝ) * (3 : ℝ) ^ ((M.gamma - 1) * (L : ℝ)) * t =
      oscThresholdAt M Q.scale L := by
    have h3 : (0 : ℝ) < 3 := by norm_num
    rw [ht, hbase, oscThresholdAt, oscThreshold]
    rw [show (3 : ℝ) ^ (Q.scale : ℝ) * (3 : ℝ) ^ ((M.gamma - 1) * (L : ℝ)) =
        (3 : ℝ) ^ ((Q.scale : ℝ) + (M.gamma - 1) * (L : ℝ)) from
      (Real.rpow_add h3 _ _).symm]
    rw [show (3 : ℝ) ^ ((Q.scale : ℝ) + (M.gamma - 1) * (L : ℝ)) *
          ((1 / 5 : ℝ) * deltaOsc d *
            Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
              (Real.sqrt M.gamma)⁻¹ *
            (3 : ℝ) ^ ((4 / 5 - M.gamma) * ((L : ℝ) - (Q.scale : ℝ)))) =
        (1 / 5 : ℝ) * deltaOsc d *
            Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
            (Real.sqrt M.gamma)⁻¹ *
          ((3 : ℝ) ^ ((Q.scale : ℝ) + (M.gamma - 1) * (L : ℝ)) *
            (3 : ℝ) ^ ((4 / 5 - M.gamma) * ((L : ℝ) - (Q.scale : ℝ)))) by ring]
    rw [← Real.rpow_add h3]
    rw [show (1 / 5 : ℝ) *
          (deltaOsc d * Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
            (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (Q.scale : ℝ))) *
          (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((L : ℝ) - (Q.scale : ℝ))) =
        (1 / 5 : ℝ) * deltaOsc d *
            Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
            (Real.sqrt M.gamma)⁻¹ *
          ((3 : ℝ) ^ (M.gamma * (Q.scale : ℝ)) *
            (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((L : ℝ) - (Q.scale : ℝ)))) by ring]
    rw [← Real.rpow_add h3]
    congr 2
    ring
  -- the squared ratio is the displayed rate
  have hsq : t ^ 2 = (1 / 25 : ℝ) * deltaOsc d ^ 2 *
      Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
      (3 : ℝ) ^ (2 * (4 / 5 - M.gamma) * ((L : ℝ) - (Q.scale : ℝ))) := by
    have hcs : Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) ^ 2 =
        Algsuperdiff.Section3.Disorder.cstar M := Real.sq_sqrt hc.le
    have hgs : Real.sqrt M.gamma ^ 2 = M.gamma := Real.sq_sqrt hg.le
    have hgpos : Real.sqrt M.gamma ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hg)
    have hrp : ((3 : ℝ) ^ ((4 / 5 - M.gamma) * ((L : ℝ) - (Q.scale : ℝ)))) ^ 2 =
        (3 : ℝ) ^ (2 * (4 / 5 - M.gamma) * ((L : ℝ) - (Q.scale : ℝ))) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ ((4 / 5 - M.gamma) *
        ((L : ℝ) - (Q.scale : ℝ)))) 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
      ring_nf
    rw [ht, hbase, mul_pow, hrp]
    rw [show ((1 / 5 : ℝ) * deltaOsc d *
        Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
        (Real.sqrt M.gamma)⁻¹) ^ 2 =
        (1 / 25 : ℝ) * deltaOsc d ^ 2 *
          Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) ^ 2 *
          ((Real.sqrt M.gamma) ^ 2)⁻¹ by
      field_simp
      ring]
    rw [hcs, hgs]
  -- apply the weak-Orlicz tail
  have htail := isBigOWith_gammaSigma_shellOscGauge M Q hL ht1
  have hevent : IndependentSums.upperTailEvent (shellOscGauge Q L)
      ((3 : ℝ) ^ (Q.scale : ℝ) * (3 : ℝ) ^ ((M.gamma - 1) * (L : ℝ)) * t) =
      badOscAt M Q L := by
    rw [hamp]
    rfl
  rw [hevent] at htail
  refine le_trans htail ?_
  rw [IndependentSums.gammaSigma_inv]
  have htt : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast t 2]
    norm_num
  rw [htt, hsq]

/-- ABK26's displayed oscillation bound `e.BoscL.prob`:

```
P[ B_{osc,L}(z + square_j) ] <= exp( - c E^{-2} gamma^{-1} 3^{(3/2)(L-j)} ) ,
```

with `c = delta_osc(d)^2 / 25`.

`hgamma20` is the manuscript's own proof-side gate `gamma <= 1/20`; `hEc` is the
consequence `E^{-2} <= c_star` of the printed admissibility `E >= C c_star^{-1}`
for any `C >= 1` and `E >= 1`. -/
theorem measureReal_badOscAt_le_printed (M : ABKModel d) (Q : TriadicCube d)
    {L : ℤ} (hL : Q.scale ≤ L) (hgate : unitGate M)
    (hgamma20 : M.gamma ≤ 1 / 20) {E : ℝ}
    (hEc : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real (badOscAt M Q L) ≤
      Real.exp (-((1 / 25 : ℝ) * deltaOsc d ^ 2 * E⁻¹ ^ 2 * M.gamma⁻¹ *
        (3 : ℝ) ^ ((3 / 2 : ℝ) * ((L : ℝ) - (Q.scale : ℝ))))) := by
  have hbase := measureReal_badOscAt_le M Q hL hgate
  refine le_trans hbase (Real.exp_le_exp.2 ?_)
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hLR : (0 : ℝ) ≤ (L : ℝ) - (Q.scale : ℝ) := by
    have : (Q.scale : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  have hdelta : 0 < deltaOsc d := deltaOsc_pos d
  have hginv : 0 < M.gamma⁻¹ := inv_pos.2 hg
  have hexp : (3 : ℝ) ^ ((3 / 2 : ℝ) * ((L : ℝ) - (Q.scale : ℝ))) ≤
      (3 : ℝ) ^ (2 * (4 / 5 - M.gamma) * ((L : ℝ) - (Q.scale : ℝ))) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    nlinarith [hLR, hgamma20]
  have hEnn : (0 : ℝ) ≤ E⁻¹ ^ 2 := sq_nonneg _
  have hpow_pos : (0 : ℝ) <
      (3 : ℝ) ^ ((3 / 2 : ℝ) * ((L : ℝ) - (Q.scale : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmain : (1 / 25 : ℝ) * deltaOsc d ^ 2 * E⁻¹ ^ 2 * M.gamma⁻¹ *
      (3 : ℝ) ^ ((3 / 2 : ℝ) * ((L : ℝ) - (Q.scale : ℝ))) ≤
      (1 / 25 : ℝ) * deltaOsc d ^ 2 *
        Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * (4 / 5 - M.gamma) * ((L : ℝ) - (Q.scale : ℝ))) := by
    have hc1 : (1 / 25 : ℝ) * deltaOsc d ^ 2 * E⁻¹ ^ 2 * M.gamma⁻¹ ≤
        (1 / 25 : ℝ) * deltaOsc d ^ 2 *
          Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ := by
      have := mul_le_mul_of_nonneg_left hEc
        (by positivity : (0 : ℝ) ≤ (1 / 25 : ℝ) * deltaOsc d ^ 2)
      nlinarith [hginv, this]
    have hnn : (0 : ℝ) ≤ (1 / 25 : ℝ) * deltaOsc d ^ 2 * E⁻¹ ^ 2 * M.gamma⁻¹ := by
      positivity
    calc (1 / 25 : ℝ) * deltaOsc d ^ 2 * E⁻¹ ^ 2 * M.gamma⁻¹ *
          (3 : ℝ) ^ ((3 / 2 : ℝ) * ((L : ℝ) - (Q.scale : ℝ)))
        ≤ (1 / 25 : ℝ) * deltaOsc d ^ 2 * E⁻¹ ^ 2 * M.gamma⁻¹ *
          (3 : ℝ) ^ (2 * (4 / 5 - M.gamma) * ((L : ℝ) - (Q.scale : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp hnn
      _ ≤ (1 / 25 : ℝ) * deltaOsc d ^ 2 *
            Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
            (3 : ℝ) ^ (2 * (4 / 5 - M.gamma) * ((L : ℝ) - (Q.scale : ℝ))) := by
          refine mul_le_mul_of_nonneg_right hc1 ?_
          exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  linarith

end

end Algsuperdiff.Section3.Provider.BadEvents
