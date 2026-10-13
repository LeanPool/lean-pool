/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.CenteredIdentification
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState

/-!
# LocalProbability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The local bad-event probability `e.Bloc.prob`

This module proves the local branch of ABK26's Lemma `l.bad.event.probabilities`
(statement, proof Step 1): for every integer scale `j <= m - 1` and every centre
`z` in `3^j Z^d`,

```
P[ B_loc(z + square_j) ] <= exp( - c E^{-2} gamma^{-1} ) ,
```

with the explicit dimension-free `c = 1/512`.

## The proof

*Step 1* of the manuscript reads: by `e.bound.Lambdas.by.Es`,
`sigma_j^{-1} Lambda_{1/4,2}(z+square_j; a_j) <= 4 + 4 E^2` and similarly for
`sigma_j lambda_{1/4,2}^{-1}`; hence by Markov and the induction hypothesis
`e.new.induction.for.shom`, the probability is at most `exp(-c E^{-2}gamma^{-1})`.

Here the two halves are:

* `CenteredIdentification.measureReal_badLoc_le_measureReal_centeredTail`
  (the sharp comparison, the deterministic translation covariance of
  `TranslationCovariance.lean`, and the translation invariance of the cutoff
  sample law) reduces to `P[ E_{1/4,infinity,2}(square_j; a_j, sigma_j) > 1 ]`;
* the second clause of the induction state
  `Algsuperdiff.Frozen.Section3.inductionState` at `s = 1/4` gives the two-term
  weak-Orlicz bound
  `E_{1/4,infinity,2}(square_j) <= O_{Gamma_2}(4 E gamma^{1/2}) +
  O_{Gamma_{1/2}}(16 exp(-E^{-3}gamma^{-1}))`, and the two tails are evaluated
  at the levels `t_1 = (2 A_1)^{-1}`, `t_2 = (2 A_2)^{-1}` splitting the
  threshold `1 = 1/2 + 1/2`.

The first tail contributes `exp(-E^{-2}gamma^{-1}/64)`, the second
`exp(-(exp(E^{-3}gamma^{-1})/32)^{1/2})`, and the second is far smaller than the
first in the admissible range.

## The admissibility gate

Both weak-Orlicz tails are only available at levels `t >= 1`, so the amplitudes
must be below the threshold: `8 E gamma^{1/2} <= 1`.  With `gamma <= E^{-5}`
this reads `8 E^{-3/2} <= 1`, i.e. `E >= 4`.  Likewise `s = 1/4` lies in the
induction state's window `[8 gamma, 1]` only when `gamma <= 1/32`, which again
needs a lower bound on `E`.  The lower bound is therefore carried explicitly
here as `4 <= E`; it is exactly what `E >= C(d) c_star^{-1}` yields at `C(d):=
4 C_0(d)` for any dimension-only `c_star <= C_0(d)`.

## Main results

* `measureReal_upperTail_le_of_isTwoTermBigOWith`: the union bound for a
  two-term weak-Orlicz relation.
* `measureReal_badLoc_le`: the displayed bound `e.Bloc.prob`.

## References

* ABK26, `l.bad.event.probabilities`.
* ABK26, `d.mathcalS.def` / `e.new.induction.for.shom`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The union bound behind a two-term weak-Orlicz tail -/

/-- Splitting a threshold into the two scaled levels of a two-term weak-Orlicz
relation bounds the upper tail by the sum of the two tail values. -/
theorem measureReal_upperTail_le_of_isTwoTermBigOWith {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsFiniteMeasure mu]
    {Psi1 Psi2 : ℝ → ℝ} {X : Omega → ℝ} {A1 A2 theta t1 t2 : ℝ}
    (h : Algsuperdiff.Section3.Probability.IsTwoTermBigOWith mu Psi1 Psi2 X A1 A2)
    (ht1 : 1 ≤ t1) (ht2 : 1 ≤ t2) (hth : A1 * t1 + A2 * t2 ≤ theta) :
    mu.real {omega | theta < X omega} ≤ (Psi1 t1)⁻¹ + (Psi2 t2)⁻¹ := by
  obtain ⟨Y, Z, _, _, _, _, _, _, _, hle, hY, hZ⟩ := h
  have hsub : {omega | theta < X omega} ⊆
      IndependentSums.upperTailEvent Y (A1 * t1) ∪
        IndependentSums.upperTailEvent Z (A2 * t2) := by
    intro omega homega
    by_contra hcon
    have h1 : Y omega ≤ A1 * t1 := by
      by_contra h1
      exact hcon (Or.inl (not_le.1 h1))
    have h2 : Z omega ≤ A2 * t2 := by
      by_contra h2
      exact hcon (Or.inr (not_le.1 h2))
    have hsum := hle omega
    have hlt : theta < X omega := homega
    linarith only [h1, h2, hsum, hlt, hth]
  calc mu.real {omega | theta < X omega}
      ≤ mu.real (IndependentSums.upperTailEvent Y (A1 * t1) ∪
          IndependentSums.upperTailEvent Z (A2 * t2)) :=
        measureReal_mono hsub (measure_ne_top mu _)
    _ ≤ mu.real (IndependentSums.upperTailEvent Y (A1 * t1)) +
          mu.real (IndependentSums.upperTailEvent Z (A2 * t2)) :=
        measureReal_union_le _ _
    _ ≤ (Psi1 t1)⁻¹ + (Psi2 t2)⁻¹ := add_le_add (hY ht1) (hZ ht2)

/-- Elementary: a positive real is at most half its product with a factor at
least two.  Extracted so that the exponential estimates below never send an
arithmetic closer into a large context. -/
private theorem le_half_mul_of_two_le {a b : ℝ} (ha : 0 < a) (hb : 2 ≤ b) :
    a ≤ a * b / 2 := by
  have h : a * 2 ≤ a * b := mul_le_mul_of_nonneg_left hb ha.le
  linarith only [h]

/-! ## The displayed bound `e.Bloc.prob` -/

/-- **ABK26 `e.Bloc.prob`**.  Under the induction state `S(m-1, E)`, for every
triadic cube `Q = z + square_j` with `j <= m - 1`,

```
P[ B_loc(z + square_j) ] <= exp( - (1/512) E^{-2} gamma^{-1} ) .
``` -/
theorem measureReal_badLoc_le (M : ABKModel d) (Q : TriadicCube d) {m : ℤ}
    {E : ℝ} (hE : 1 ≤ E) (hE4 : 4 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hj : Q.scale ≤ m - 1) (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    (cutoffSampleLaw M).toMeasure.real (badLoc M Q) ≤
      Real.exp (-((1 / 512 : ℝ) * E⁻¹ ^ 2 * M.gamma⁻¹)) := by
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hE0 : (0 : ℝ) < E := by linarith only [hE4]
  have hE5pos : (0 : ℝ) < E ^ (5 : ℕ) := by positivity
  have hEpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have hgamma' : M.gamma ≤ (E ^ (5 : ℕ))⁻¹ := by rw [← hEpow]; exact hgamma
  have hg5 : E ^ (5 : ℕ) ≤ M.gamma⁻¹ := by
    rw [le_inv_comm₀ hE5pos hg]
    exact hgamma'
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = E⁻¹ ^ 3 * M.gamma⁻¹ := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = E⁻¹ ^ 2 * M.gamma⁻¹ := ⟨_, rfl⟩
  -- the elementary parameter inequalities
  have hu2 : E ^ 2 ≤ u := by
    have hcoef : (0 : ℝ) ≤ E⁻¹ ^ 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hg5 hcoef
    have heq : E⁻¹ ^ 3 * E ^ (5 : ℕ) = E ^ 2 := by
      field_simp
    rw [heq] at hmul
    rw [hu]
    exact hmul
  have hE16 : (16 : ℝ) ≤ E ^ 2 := by
    have h := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 4) hE4
    rw [pow_two]
    linarith only [h]
  have hu16 : (16 : ℝ) ≤ u := le_trans hE16 hu2
  have hu0 : (0 : ℝ) ≤ u := by linarith only [hu16]
  have husq : (256 : ℝ) ≤ u ^ 2 := by
    have h := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 16) hu16
    rw [pow_two]
    linarith only [h]
  have hRu : R = E * u := by
    rw [hR, hu]
    field_simp
  have hR64 : (64 : ℝ) ≤ R := by
    rw [hRu]
    have h : (4 : ℝ) * 16 ≤ E * u := mul_le_mul hE4 hu16 (by norm_num) hE0.le
    linarith only [h]
  have hEu : E ≤ u := by
    have h : E * 1 ≤ E * E :=
      mul_le_mul_of_nonneg_left (by linarith only [hE4]) hE0.le
    linarith only [h, hu2]
  have hRle : R ≤ u ^ 2 := by
    rw [hRu]
    have h : E * u ≤ u * u := mul_le_mul_of_nonneg_right hEu hu0
    linarith only [h]
  -- `s = 1/4` is inside the induction state's window
  have hginv1024 : (1024 : ℝ) ≤ M.gamma⁻¹ := by
    have hE3 : (64 : ℝ) ≤ E ^ 3 := by
      have h : (16 : ℝ) * 4 ≤ E ^ 2 * E :=
        mul_le_mul hE16 hE4 (by norm_num) (by positivity)
      linarith only [h]
    have hsplit : M.gamma⁻¹ = u * E ^ 3 := by
      rw [hu]
      field_simp
    rw [hsplit]
    have h : (16 : ℝ) * 64 ≤ u * E ^ 3 :=
      mul_le_mul hu16 hE3 (by norm_num) hu0
    linarith only [h]
  have hg32 : M.gamma ≤ (32 : ℝ)⁻¹ :=
    (le_inv_comm₀ (by norm_num) hg).mp (by linarith only [hginv1024])
  have hg32' : M.gamma ≤ 1 / 32 := by
    have h : (32 : ℝ)⁻¹ = 1 / 32 := by norm_num
    rw [h] at hg32
    exact hg32
  have hwindow : (1 / 4 : ℝ) ∈ Set.Icc (8 * M.gamma) 1 :=
    ⟨by linarith only [hg32'], by norm_num⟩
  -- the induction state's two-term weak-Orlicz bound at `s = 1/4`
  have htail : Algsuperdiff.Section3.Probability.IsTwoTermBigOWith
      (cutoffSampleLaw M).toMeasure (IndependentSums.gammaSigma 2)
      (IndependentSums.gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M Q.scale quarter)
      (E * (1 / 4 : ℝ)⁻¹ * Real.sqrt M.gamma)
      (((1 / 4 : ℝ)⁻¹) ^ 2 * Real.exp (-(E⁻¹ ^ 3 * M.gamma⁻¹))) :=
    hS.2 Q.scale hj (1 / 4 : ℝ) hwindow
  have hA1 : E * (1 / 4 : ℝ)⁻¹ * Real.sqrt M.gamma
      = 4 * E * Real.sqrt M.gamma := by
    rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num]
    ring
  have hA2 : ((1 / 4 : ℝ)⁻¹) ^ 2 * Real.exp (-(E⁻¹ ^ 3 * M.gamma⁻¹))
      = 16 * Real.exp (-u) := by
    rw [hu]
    norm_num
  rw [hA1, hA2] at htail
  -- the two levels
  obtain ⟨t1, ht1def⟩ : ∃ t : ℝ, t = Real.sqrt (R / 64) := ⟨_, rfl⟩
  obtain ⟨t2, ht2def⟩ : ∃ t : ℝ, t = Real.exp u / 32 := ⟨_, rfl⟩
  have hkey : Real.sqrt M.gamma * Real.sqrt (R / 64) = E⁻¹ / 8 := by
    rw [← Real.sqrt_mul hg.le]
    rw [show M.gamma * (R / 64) = (E⁻¹ / 8) ^ 2 by
      rw [hR]
      field_simp
      ring]
    exact Real.sqrt_sq (by positivity)
  have hA1t1 : 4 * E * Real.sqrt M.gamma * t1 = 1 / 2 := by
    calc 4 * E * Real.sqrt M.gamma * t1
        = 4 * E * (Real.sqrt M.gamma * Real.sqrt (R / 64)) := by
          rw [ht1def]; ring
      _ = 4 * E * (E⁻¹ / 8) := by rw [hkey]
      _ = 4 * (E * E⁻¹) / 8 := by ring
      _ = 1 / 2 := by rw [mul_inv_cancel₀ hE0.ne']; norm_num
  have hexpne : Real.exp u ≠ 0 := Real.exp_ne_zero u
  have hA2t2 : 16 * Real.exp (-u) * t2 = 1 / 2 := by
    calc 16 * Real.exp (-u) * t2
        = 16 * ((Real.exp u)⁻¹ * Real.exp u) / 32 := by
          rw [ht2def, Real.exp_neg]; ring
      _ = 1 / 2 := by rw [inv_mul_cancel₀ hexpne]; norm_num
  have ht1 : 1 ≤ t1 := by
    have h1 : (1 : ℝ) ≤ R / 64 := by linarith only [hR64]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (R / 64) := Real.sqrt_le_sqrt h1
      _ = t1 := ht1def.symm
  -- the exponential lower bound `exp u >= (u/4)^4`
  have hunn : (0 : ℝ) ≤ u / 4 := by linarith only [hu0]
  have hulin : u / 4 ≤ Real.exp (u / 4) := by
    have h := Real.add_one_le_exp (u / 4)
    linarith only [h]
  have hexpsplit : Real.exp u = Real.exp (u / 4) ^ 4 := by
    have hquad : Real.exp (u / 4) ^ 4
        = Real.exp (u / 4 + (u / 4 + (u / 4 + u / 4))) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add]
      ring
    rw [hquad]
    congr 1
    ring
  have hexplb : (u / 4) ^ 4 ≤ Real.exp u := by
    have hs1 : (u / 4) ^ 2 ≤ Real.exp (u / 4) ^ 2 := by
      have hmul := mul_self_le_mul_self hunn hulin
      calc (u / 4) ^ 2 = u / 4 * (u / 4) := by ring
        _ ≤ Real.exp (u / 4) * Real.exp (u / 4) := hmul
        _ = Real.exp (u / 4) ^ 2 := by ring
    have hs2 : ((u / 4) ^ 2) ^ 2 ≤ (Real.exp (u / 4) ^ 2) ^ 2 := by
      have hmul := mul_self_le_mul_self (sq_nonneg (u / 4)) hs1
      calc ((u / 4) ^ 2) ^ 2 = (u / 4) ^ 2 * (u / 4) ^ 2 := by ring
        _ ≤ Real.exp (u / 4) ^ 2 * Real.exp (u / 4) ^ 2 := hmul
        _ = (Real.exp (u / 4) ^ 2) ^ 2 := by ring
    have hl : (u / 4) ^ 4 = ((u / 4) ^ 2) ^ 2 := by ring
    have hr : (Real.exp (u / 4) ^ 2) ^ 2 = Real.exp (u / 4) ^ 4 := by ring
    rw [hl, hexpsplit, ← hr]
    exact hs2
  have hu256 : (256 : ℝ) ≤ (u / 4) ^ 4 := by
    have hq : (4 : ℝ) ≤ u / 4 := by linarith only [hu16]
    have hq2 : (16 : ℝ) ≤ (u / 4) ^ 2 := by
      rw [pow_two]
      have hmul := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 4) hq
      linarith only [hmul]
    have hpow : (u / 4) ^ 4 = (u / 4) ^ 2 * (u / 4) ^ 2 := by ring
    rw [hpow]
    have hmul := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 16) hq2
    linarith only [hmul]
  have hexp256 : (256 : ℝ) ≤ Real.exp u := le_trans hu256 hexplb
  have ht2pos : (0 : ℝ) < t2 := by
    rw [ht2def]
    positivity
  have ht2 : 1 ≤ t2 := by
    rw [ht2def]
    linarith only [hexp256]
  -- the union bound
  have hbound := measureReal_upperTail_le_of_isTwoTermBigOWith htail ht1 ht2
    (by linarith only [hA1t1, hA2t2] :
      4 * E * Real.sqrt M.gamma * t1 + 16 * Real.exp (-u) * t2 ≤ 1)
  rw [IndependentSums.gammaSigma_inv, IndependentSums.gammaSigma_inv] at hbound
  -- evaluate the two tail exponents
  have hrp1 : t1 ^ (2 : ℝ) = R / 64 := by
    have hcast : t1 ^ (2 : ℝ) = t1 ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast t1 2]
      norm_num
    rw [hcast, ht1def, Real.sq_sqrt (by linarith only [hR64])]
  have hrp2 : t2 ^ (1 / 2 : ℝ) = Real.sqrt t2 := (Real.sqrt_eq_rpow t2).symm
  rw [hrp1, hrp2] at hbound
  -- the first tail is below half the target
  have hpartA : Real.exp (-(R / 64)) ≤ Real.exp (-(R / 512)) / 2 := by
    have hy : (23 : ℝ) / 16 ≤ Real.exp (7 * R / 1024) := by
      have h1 := Real.add_one_le_exp (7 * R / 1024)
      have h2 : (7 : ℝ) / 16 ≤ 7 * R / 1024 := by linarith only [hR64]
      linarith only [h1, h2]
    have hsq : (2 : ℝ) ≤ Real.exp (7 * R / 1024) * Real.exp (7 * R / 1024) := by
      have hy0 : (0 : ℝ) ≤ (23 : ℝ) / 16 := by norm_num
      have hprod := mul_self_le_mul_self hy0 hy
      linarith only [hprod]
    have hsplit : Real.exp (-(R / 512)) =
        Real.exp (-(R / 64)) *
          (Real.exp (7 * R / 1024) * Real.exp (7 * R / 1024)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    exact le_half_mul_of_two_le (Real.exp_pos _) hsq
  -- the second tail is below half the target
  have hb1 : R / 512 + 1 ≤ 3 * u ^ 2 / 512 := by linarith only [hRle, husq]
  have hb2 : (R / 512 + 1) ^ 2 ≤ (3 * u ^ 2 / 512) ^ 2 := by
    have hnn : (0 : ℝ) ≤ R / 512 + 1 := by linarith only [hR64]
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hnn hb1
  have hu4nn : (0 : ℝ) ≤ u ^ 4 := by positivity
  have hb3 : 32 * (3 * u ^ 2 / 512) ^ 2 ≤ Real.exp u := by
    have hquart : (u / 4) ^ 4 = u ^ 4 / 256 := by ring
    rw [hquart] at hexplb
    have hcoef : 32 * (3 * u ^ 2 / 512) ^ 2 = 9 * u ^ 4 / 8192 := by ring
    rw [hcoef]
    linarith only [hexplb, hu4nn]
  have hb4 : (R / 512 + 1) ^ 2 ≤ t2 := by
    rw [ht2def]
    linarith only [hb2, hb3]
  have hb5 : R / 512 + 1 ≤ Real.sqrt t2 := by
    rw [Real.le_sqrt (by linarith only [hR64]) ht2pos.le]
    exact hb4
  have hpartB : Real.exp (-Real.sqrt t2) ≤ Real.exp (-(R / 512)) / 2 := by
    have hexp2 : (2 : ℝ) ≤ Real.exp (Real.sqrt t2 - R / 512) := by
      have h1 := Real.add_one_le_exp (Real.sqrt t2 - R / 512)
      linarith only [h1, hb5]
    have hsplit : Real.exp (-(R / 512)) =
        Real.exp (-Real.sqrt t2) * Real.exp (Real.sqrt t2 - R / 512) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    exact le_half_mul_of_two_le (Real.exp_pos _) hexp2
  -- assemble
  have htarget : Real.exp (-((1 / 512 : ℝ) * E⁻¹ ^ 2 * M.gamma⁻¹))
      = Real.exp (-(R / 512)) := by
    congr 1
    rw [hR]
    ring
  rw [htarget]
  calc (cutoffSampleLaw M).toMeasure.real (badLoc M Q)
      ≤ (cutoffSampleLaw M).toMeasure.real
          {omega | 1 < Observable.cutoffHomogenizationError M Q.scale quarter omega} :=
        measureReal_badLoc_le_measureReal_centeredTail M Q
    _ ≤ Real.exp (-(R / 64)) + Real.exp (-Real.sqrt t2) := hbound
    _ ≤ Real.exp (-(R / 512)) := by linarith only [hpartA, hpartB]

end

end Algsuperdiff.Section3.Provider.BadEvents
