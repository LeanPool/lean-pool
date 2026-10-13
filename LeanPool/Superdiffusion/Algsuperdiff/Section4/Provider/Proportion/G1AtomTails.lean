/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.StreamDerivativeSumBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.ProductPower
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TwoTermCalculus
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffLawTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementTranslation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.ShellBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Events

/-!
# G1AtomTails

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `𝒢₁` per-shell atom tails

ABK26's `l.ratio.of.good.scales.for.k` bounds the density of scales at which
the event `𝒢₁(m; s, T)` of `d.good.event.for.lambda` fails.  Its two lanes feed
the concentration proposition with two families of atoms:

* **large waves** (Step 1) `X_k = 3^{(2-γ)k} ‖∇j_k‖_{W^{1,∞}(□_k)}`, whose
  `Γ₂` moment bound is `e.G1scalecount.Xk.pedant.bound`;
* **small waves** (Step 2) `3^{(2-γ)k} ‖j_k‖_{W^{2,∞}(z+□_k)}` at a lattice
  centre `z`, whose squares carry the `Γ₁` moment bound `e.Xmk.pedant.bound`.

This module produces both tails, uniformly in the shell index `k` and (for the
second family) in the *real* centre `z`.

## Where the tails come from, and the dimension bookkeeping the source omits

Here the cancellation is explicit and *exact*: the proved Section 3
realizations of the manuscript's own per-shell displays are

* `e.jk.O` `isBigOWith_gammaSigma_localCubeControl_shell`: `‖j_k‖_{L∞(□_k)} ≤
  𝒪_{Γ₂}(3^{γk})`,

both with amplitude constant `1`.  Multiplying by `3^{(1-γ)k}` and `3^{-γk}`
respectively makes both amplitudes `1`, uniformly in `k` — which is exactly what
the Appendix-D array of `p.concentration.for.scales` needs.

The anchor `Algsuperdiff.Frozen.Section3.stream_derivative_sum_bound` gives the
same derivative statement at the one-shell window `(l, n, m) = (k, k-1, k)`, at
the strictly larger amplitude `C · min(γ^{-1}, 1) · 3^{(γ-1)k}`; it carries no
`Γ₂` statement for the value leg (its `L^∞` clauses are stated for the *square*
at `Γ₁`).  The per-shell displays above are the manuscript's own cited inputs,
so they are what is consumed here.

## Carriers

The Section 3 displays live on `Cutoff.ShellSeq d` under `M.P`, while the
Section 4 events live on `Cutoff.CutoffSample d` under
`Cutoff.cutoffSampleLaw`.  The transfer is the proved
`isBigOWith_cutoffSampleLaw_comp_val` (the inclusion `Subtype.val` is a
measurable embedding preserving the mass of *every* subset).  The lattice
centre is reached by `isBigOWith_comp_translateCutoffSample`, the proved
real-translation invariance of the cutoff-sample law; no lattice restriction is
used, so the per-centre tail holds at every `z : Vec d`.

## References

* ABK26, `d.good.event.for.lambda`.
* ABK26, `l.ratio.of.good.scales.for.k`.
* ABK26, (`e.jk.O`, `e.nabla.jk.O`), (the gauges).
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Reading one shell of a cutoff sample -/

/-- The `k`-th shell of a cutoff sample, as a measurable map. -/
theorem measurable_shellCoord (k : ℤ) :
    Measurable fun omega : Cutoff.CutoffSample d => omega.1 k :=
  (measurable_pi_apply k).comp measurable_subtype_coe

/-! ## 2. The two exponent identities

The manuscript's `3^{(2-γ)k}` splits against the two proved amplitudes.  Both
identities are pure `rpow` arithmetic and are isolated so that no numeric
tactic ever sees a transcendental atom. -/

/-- `Real.rpow`-form of the exponent addition law at base `3`, stated so that
`rw` matches the explicit `Real.rpow` spelling used throughout this file. -/
theorem rpow_add_three (x y : ℝ) :
    Real.rpow 3 (x + y) = Real.rpow 3 x * Real.rpow 3 y :=
  Real.rpow_add (by norm_num) x y

/-- `Real.rpow`-form of the integer-exponent identification at base `3`. -/
theorem rpow_intCast_three (k : ℤ) :
    Real.rpow 3 ((k : ℤ) : ℝ) = (3 : ℝ) ^ k :=
  Real.rpow_intCast 3 k

theorem rpow_zero_three : Real.rpow 3 0 = 1 :=
  Real.rpow_zero 3

/-- Nonnegativity of `Real.rpow 3`, in the explicit `Real.rpow` spelling. -/
theorem rpow_nonneg_three (x : ℝ) : 0 ≤ Real.rpow 3 x :=
  Real.rpow_nonneg (by norm_num) x

/-- Positivity of `Real.rpow 3`, in the explicit `Real.rpow` spelling. -/
theorem rpow_pos_three (x : ℝ) : 0 < Real.rpow 3 x :=
  Real.rpow_pos_of_pos (by norm_num) x

/-- Monotonicity of `Real.rpow 3` in the exponent, in the explicit spelling. -/
theorem rpow_le_rpow_three {x y : ℝ} (h : x ≤ y) : Real.rpow 3 x ≤ Real.rpow 3 y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- The exponential form of `Real.rpow 3`, in the explicit spelling. -/
theorem rpow_def_three (y : ℝ) : Real.rpow 3 y = Real.exp (Real.log 3 * y) :=
  Real.rpow_def_of_pos (by norm_num) y

/-- The negative-exponent law for `Real.rpow 3`, in the explicit spelling. -/
theorem rpow_neg_three (y : ℝ) : Real.rpow 3 (-y) = (Real.rpow 3 y)⁻¹ :=
  Real.rpow_neg (by norm_num) y

private theorem rpow_two_sub_split (gamma : ℝ) (k : ℤ) :
    Real.rpow 3 ((2 - gamma) * (k : ℝ)) =
      Real.rpow 3 ((1 - gamma) * (k : ℝ)) * (3 : ℝ) ^ k := by
  rw [← rpow_intCast_three k, ← rpow_add_three]
  congr 1
  ring

private theorem rpow_two_sub_split_two (gamma : ℝ) (k : ℤ) :
    Real.rpow 3 ((2 - gamma) * (k : ℝ)) * (3 : ℝ) ^ (-2 * k) =
      Real.rpow 3 (-(gamma * (k : ℝ))) := by
  rw [← rpow_intCast_three (-2 * k), ← rpow_add_three]
  congr 1
  push_cast
  ring

/-! ## 3. The deterministic gauge dominations -/

/-- **The large-waves atom is dominated by the `e.nabla.jk.O` gauge.**  The
volume-normalized gauge is a maximum of two legs, so it is below their sum, and
the weight `3^{(2-γ)k}` splits as `3^{(1-γ)k}·3^{k}` — the exact form of the
cancellation the source performs silently. -/
theorem three_rpow_mul_shellW1InfGradNorm_le (gamma : ℝ) (k : ℤ)
    (j : Algsuperdiff.Frozen.Assumptions.ShellField d) :
    Real.rpow 3 ((2 - gamma) * (k : ℝ)) * shellW1InfGradNorm k j ≤
      Real.rpow 3 ((1 - gamma) * (k : ℝ)) *
        (Provider.Stream.localCubeDerivNorm k j +
          (3 : ℝ) ^ k * Provider.Stream.localCubeSecondDerivNorm k j) := by
  have hk : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hstep : (3 : ℝ) ^ k * shellW1InfGradNorm k j ≤
      Provider.Stream.localCubeDerivNorm k j +
        (3 : ℝ) ^ k * Provider.Stream.localCubeSecondDerivNorm k j := by
    have hmax : shellW1InfGradNorm k j ≤
        Provider.Stream.localCubeSecondDerivNorm k j +
          (3 : ℝ) ^ (-k) * Provider.Stream.localCubeDerivNorm k j := by
      refine max_le ?_ ?_
      · have := mul_nonneg (zpow_pos (show (0 : ℝ) < 3 by norm_num) (-k)).le
          (Provider.Stream.localCubeDerivNorm_nonneg k j)
        linarith only [this]
      · have := Provider.Stream.localCubeSecondDerivNorm_nonneg k j
        linarith only [this]
    have hmul := mul_le_mul_of_nonneg_left hmax hk.le
    have hcancel : (3 : ℝ) ^ k * ((3 : ℝ) ^ (-k) *
        Provider.Stream.localCubeDerivNorm k j) =
        Provider.Stream.localCubeDerivNorm k j := by
      rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      simp
    calc (3 : ℝ) ^ k * shellW1InfGradNorm k j
        ≤ (3 : ℝ) ^ k * (Provider.Stream.localCubeSecondDerivNorm k j +
            (3 : ℝ) ^ (-k) * Provider.Stream.localCubeDerivNorm k j) := hmul
      _ = Provider.Stream.localCubeDerivNorm k j +
            (3 : ℝ) ^ k * Provider.Stream.localCubeSecondDerivNorm k j := by
            rw [mul_add, hcancel]; ring
  rw [rpow_two_sub_split gamma k, mul_assoc]
  exact mul_le_mul_of_nonneg_left hstep
    (Real.rpow_nonneg (by norm_num) _)

/-- The `‖·‖_{W^{2,∞}(□_k)}` gauge measured at the *origin* cube: the maximum of
the first-order gauge and the normalized value leg.  `shellW2InfNormAt z k` is
this gauge applied to the translated field, by definition. -/
def w2Gauge (k : ℤ) (j : Algsuperdiff.Frozen.Assumptions.ShellField d) : ℝ :=
  max (shellW1InfGradNorm k j)
    ((3 : ℝ) ^ (-2 * k) * Algsuperdiff.Section3.Cutoff.localCubeControl k j)

theorem measurable_w2Gauge (k : ℤ) :
    Measurable (w2Gauge (d := d) k) :=
  (measurable_shellW1InfGradNorm k).max
    (measurable_const.mul
      (Algsuperdiff.Section3.Cutoff.measurable_localCubeControl k))

/-- **The small-waves atom is dominated by the sum of the two `𝒪_{Γ₂}` gauges.**
The `W^{2,∞}` gauge is a maximum of three legs; the two derivative legs are the
`e.nabla.jk.O` gauge at weight `3^{(1-γ)k}` and the value leg is `e.jk.O` at
weight `3^{-γk}`. -/
theorem three_rpow_mul_w2Gauge_le (gamma : ℝ) (k : ℤ)
    (j : Algsuperdiff.Frozen.Assumptions.ShellField d) :
    Real.rpow 3 ((2 - gamma) * (k : ℝ)) * w2Gauge k j ≤
      Real.rpow 3 ((1 - gamma) * (k : ℝ)) *
          (Provider.Stream.localCubeDerivNorm k j +
            (3 : ℝ) ^ k * Provider.Stream.localCubeSecondDerivNorm k j) +
        Real.rpow 3 (-(gamma * (k : ℝ))) *
          Algsuperdiff.Section3.Cutoff.localCubeControl k j := by
  have hsplit : w2Gauge k j ≤ shellW1InfGradNorm k j +
      (3 : ℝ) ^ (-2 * k) * Algsuperdiff.Section3.Cutoff.localCubeControl k j := by
    refine max_le ?_ ?_
    · have := mul_nonneg (zpow_pos (show (0 : ℝ) < 3 by norm_num) (-2 * k)).le
        (Algsuperdiff.Section3.Cutoff.localCubeControl_nonneg k j)
      linarith only [this]
    · have := shellW1InfGradNorm_nonneg k j
      linarith only [this]
  have hnn : (0 : ℝ) ≤ Real.rpow 3 ((2 - gamma) * (k : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  calc Real.rpow 3 ((2 - gamma) * (k : ℝ)) * w2Gauge k j
      ≤ Real.rpow 3 ((2 - gamma) * (k : ℝ)) *
          (shellW1InfGradNorm k j +
            (3 : ℝ) ^ (-2 * k) *
              Algsuperdiff.Section3.Cutoff.localCubeControl k j) :=
        mul_le_mul_of_nonneg_left hsplit hnn
    _ = Real.rpow 3 ((2 - gamma) * (k : ℝ)) * shellW1InfGradNorm k j +
          Real.rpow 3 (-(gamma * (k : ℝ))) *
            Algsuperdiff.Section3.Cutoff.localCubeControl k j := by
        rw [mul_add, ← mul_assoc, rpow_two_sub_split_two gamma k]
    _ ≤ Real.rpow 3 ((1 - gamma) * (k : ℝ)) *
            (Provider.Stream.localCubeDerivNorm k j +
              (3 : ℝ) ^ k * Provider.Stream.localCubeSecondDerivNorm k j) +
          Real.rpow 3 (-(gamma * (k : ℝ))) *
            Algsuperdiff.Section3.Cutoff.localCubeControl k j :=
        add_le_add (three_rpow_mul_shellW1InfGradNorm_le gamma k j) le_rfl

/-! ## 4. The two normalized shell observables and their `Γ₂` tails

Both are stated on `Cutoff.ShellSeq d` first (that is where the Section 3
displays live) and then transferred. -/

/-- The `e.nabla.jk.O` gauge at the shell's own scale, weighted so that its
amplitude is `1`. -/
def derivLeg (gamma : ℝ) (k : ℤ) (omega : Cutoff.ShellSeq d) : ℝ :=
  Real.rpow 3 ((1 - gamma) * (k : ℝ)) *
    (Provider.Stream.localCubeDerivNorm k (omega k) +
      (3 : ℝ) ^ k * Provider.Stream.localCubeSecondDerivNorm k (omega k))

/-- The `e.jk.O` value leg, weighted so that its amplitude is `1`. -/
def valueLeg (gamma : ℝ) (k : ℤ) (omega : Cutoff.ShellSeq d) : ℝ :=
  Real.rpow 3 (-(gamma * (k : ℝ))) *
    Algsuperdiff.Section3.Cutoff.localCubeControl k (omega k)

private theorem derivLeg_nonneg (gamma : ℝ) (k : ℤ) (omega : Cutoff.ShellSeq d) :
    0 ≤ derivLeg gamma k omega :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Provider.Stream.shellDerivGauge_nonneg k (omega k))

private theorem valueLeg_nonneg (gamma : ℝ) (k : ℤ) (omega : Cutoff.ShellSeq d) :
    0 ≤ valueLeg gamma k omega :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Algsuperdiff.Section3.Cutoff.localCubeControl_nonneg k (omega k))

private theorem measurable_derivLeg (gamma : ℝ) (k : ℤ) :
    Measurable (derivLeg (d := d) gamma k) :=
  ((Provider.Stream.measurable_shellDerivGauge k).comp
    (measurable_pi_apply k)).const_mul _

private theorem measurable_valueLeg (gamma : ℝ) (k : ℤ) :
    Measurable (valueLeg (d := d) gamma k) :=
  ((Algsuperdiff.Section3.Cutoff.measurable_localCubeControl k).comp
    (measurable_pi_apply k)).const_mul _

private theorem isBigOWith_derivLeg (M : ABKModel d) (k : ℤ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2) (derivLeg M.gamma k) 1 := by
  have h := (Provider.Stream.isBigOWith_gammaSigma_shellDerivGauge M k).const_mul
    (c := Real.rpow 3 ((1 - M.gamma) * (k : ℝ)))
    (Real.rpow_nonneg (by norm_num) _)
  have hscale : Real.rpow 3 ((1 - M.gamma) * (k : ℝ)) *
      Real.rpow 3 ((M.gamma - 1) * (k : ℝ)) = 1 := by
    rw [← rpow_add_three,
      show (1 - M.gamma) * (k : ℝ) + (M.gamma - 1) * (k : ℝ) = 0 by ring,
      rpow_zero_three]
  rw [hscale] at h
  exact h

private theorem isBigOWith_valueLeg (M : ABKModel d) (k : ℤ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2) (valueLeg M.gamma k) 1 := by
  have h := (Provider.Stream.isBigOWith_gammaSigma_localCubeControl_shell M k).const_mul
    (c := Real.rpow 3 (-(M.gamma * (k : ℝ))))
    (Real.rpow_nonneg (by norm_num) _)
  have hscale : Real.rpow 3 (-(M.gamma * (k : ℝ))) *
      Real.rpow 3 (M.gamma * (k : ℝ)) = 1 := by
    rw [← rpow_add_three,
      show -(M.gamma * (k : ℝ)) + M.gamma * (k : ℝ) = 0 by ring,
      rpow_zero_three]
  rw [hscale] at h
  exact h

/-! ## 5. The large-waves atom `X_k` -/

/-- **The large-waves atom**: `X_k = 3^{(2-γ)k} ‖∇j_k‖_{W^{1,∞}(□_k)}`, the score
field of `𝒢₁`'s first condition read at its own scale. -/
def atomG1a (M : ABKModel d) (k : ℤ) (omega : Cutoff.CutoffSample d) : ℝ :=
  Real.rpow 3 ((2 - M.gamma) * (k : ℝ)) * shellW1InfGradNorm k (omega.1 k)

theorem atomG1a_nonneg (M : ABKModel d) (k : ℤ) (omega : Cutoff.CutoffSample d) :
    0 ≤ atomG1a M k omega :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _) (shellW1InfGradNorm_nonneg _ _)

theorem measurable_atomG1a (M : ABKModel d) (k : ℤ) :
    Measurable (atomG1a M k) :=
  ((measurable_shellW1InfGradNorm k).comp (measurable_shellCoord k)).const_mul _

/-- **`e.G1scalecount.Xk.pedant.bound`, in tail form.**  The large-waves atom has
a `Γ₂` upper tail at amplitude `1`, uniformly in the shell index `k`.  Only the
manuscript's own per-shell display `e.nabla.jk.O` enters. -/
theorem isBigOWith_atomG1a (M : ABKModel d) (k : ℤ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (atomG1a M k) 1 := by
  refine Provider.Stream.isBigOWith_cutoffSampleLaw_of_forall_eq_comp_val
    (X := fun omega : Cutoff.ShellSeq d =>
      Real.rpow 3 ((2 - M.gamma) * (k : ℝ)) * shellW1InfGradNorm k (omega k))
    (fun _ => rfl) ?_
  exact (isBigOWith_derivLeg M k).of_le fun omega =>
    three_rpow_mul_shellW1InfGradNorm_le M.gamma k (omega k)

/-! ## 6. The small-waves atom at a real centre -/

/-- The `Γ₂` amplitude of the small-waves atom: the two-term triangle constant
against the two unit amplitudes of `e.nabla.jk.O` and `e.jk.O`. -/
def atomG1bScale : ℝ := gammaTriangleConst 2 * 2

theorem atomG1bScale_pos : 0 < atomG1bScale := by
  have := gammaTriangleConst_pos (σ := (2 : ℝ))
  unfold atomG1bScale
  positivity

/-- **The small-waves atom**, before squaring: `3^{(2-γ)k} ‖j_k‖_{W^{2,∞}(z+□_k)}`
at the centre `z`. -/
def atomG1b (M : ABKModel d) (k : ℤ) (z : Vec d)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  Real.rpow 3 ((2 - M.gamma) * (k : ℝ)) * shellW2InfNormAt z k (omega.1 k)

theorem measurable_atomG1b (M : ABKModel d) (k : ℤ) (z : Vec d) :
    Measurable (atomG1b M k z) :=
  ((measurable_shellW2InfNormAt z k).comp (measurable_shellCoord k)).const_mul _

/-- **`e.Xmk.pedant.bound`, in tail form, before the squaring and the lattice
maximum.**  The small-waves atom has a `Γ₂` upper tail at the amplitude
`atomG1bScale`, uniformly in the shell index `k` *and* in the real centre `z`.
Uniformity in `z` is the proved real-translation invariance of the
cutoff-sample law; no lattice restriction enters. -/
theorem isBigOWith_atomG1b (M : ABKModel d) (k : ℤ) (z : Vec d) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (atomG1b M k z) atomG1bScale := by
  have hbase : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega : Cutoff.CutoffSample d =>
        Real.rpow 3 ((2 - M.gamma) * (k : ℝ)) * w2Gauge k (omega.1 k))
      atomG1bScale := by
    have hsum : IsBigOWith M.P.toMeasure (gammaSigma 2)
        (fun omega : Cutoff.ShellSeq d =>
          derivLeg M.gamma k omega + valueLeg M.gamma k omega)
        (gammaTriangleConst 2 * (1 + 1)) :=
      Provider.Orlicz.isBigOWith_gammaSigma_add (by norm_num)
        (derivLeg_nonneg M.gamma k) (valueLeg_nonneg M.gamma k)
        (measurable_derivLeg M.gamma k) (measurable_valueLeg M.gamma k)
        zero_le_one zero_le_one (isBigOWith_derivLeg M k) (isBigOWith_valueLeg M k)
    have hconst : gammaTriangleConst (2 : ℝ) * (1 + 1) = atomG1bScale := by
      unfold atomG1bScale
      norm_num
    rw [hconst] at hsum
    have hdom : IsBigOWith M.P.toMeasure (gammaSigma 2)
        (fun omega : Cutoff.ShellSeq d =>
          Real.rpow 3 ((2 - M.gamma) * (k : ℝ)) * w2Gauge k (omega k))
        atomG1bScale := by
      refine hsum.of_le fun omega => ?_
      have := three_rpow_mul_w2Gauge_le M.gamma k (omega k)
      simpa only [derivLeg, valueLeg] using this
    exact Provider.Stream.isBigOWith_cutoffSampleLaw_of_forall_eq_comp_val
      (fun _ => rfl) hdom
  have hmeas : Measurable fun omega : Cutoff.CutoffSample d =>
      Real.rpow 3 ((2 - M.gamma) * (k : ℝ)) * w2Gauge k (omega.1 k) :=
    ((measurable_w2Gauge k).comp (measurable_shellCoord k)).const_mul _
  exact Provider.Stream.isBigOWith_comp_translateCutoffSample M z hmeas hbase

end

end Algsuperdiff.Section4.Provider.Proportion
