/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.RandomScaleWitness
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# WindowTails

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Geometric tails for the random minimal scale

The random minimal scale of a bad-window family has an exponential tail once
the individual bad-window probabilities do.  This module keeps the prefactor
form `P[N ≤ Z] ≤ C exp (-c₀ N)`, which preserves the rate and makes the
length-zero window free.

## Contents

1. `measureReal_le_tsum_of_subset` — real countable subadditivity along an
   inclusion, with no measurability hypothesis on the sets.
2. `minimalScale_tail_sum_le` — the geometric summation over the windows of
   length `≥ M` covered by `minimalScaleEN_tail_eq`.
3. `minimalScaleEN_exp_tail_const` — the packaged prefactor tail bound.
4. `measureReal_le_card_mul_of_cover` — the union bound over a finite family of
   centres covering a bad window.
5. `count_exp_absorb_const` — absorption of a centre count into the prefactor.
6. `windowTailConst` and `windowScale_tail_const_of_center_tails` — the assembled
   producer.

Everything is generic over the sample space `Ω`, the measure `P`, and the centre
index type `ι`: no source-specific carrier appears.  In particular the centre
count and the covering property are *inputs* of the assembly lemmas here; a
consumer with a concrete centre family discharges both as theorems.
-/

namespace Algsuperdiff.Probability

open MeasureTheory
open scoped ENNReal

noncomputable section

section Generic

variable {Ω : Type*}

/-- A vanishing upper bound on all natural-number tails excludes the infinite value.
No measurability of the random scale is needed. -/
theorem ae_ne_top_of_enat_tail_tendsto_zero [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℕ∞} {b : ℕ → ℝ≥0∞}
    (hlim : Filter.Tendsto b Filter.atTop (nhds 0))
    (htail : ∀ N : ℕ, P {omega | (N : ℕ∞) ≤ X omega} ≤ b N) :
    ∀ᵐ omega ∂P, X omega ≠ ⊤ := by
  rw [MeasureTheory.ae_iff]
  have hsub : ∀ N : ℕ, {omega | ¬ X omega ≠ ⊤} ⊆ {omega | (N : ℕ∞) ≤ X omega} := by
    intro N omega homega
    have htop : X omega = ⊤ := not_not.mp homega
    simp only [Set.mem_ofPred_eq, htop, le_top]
  exact le_antisymm (ge_of_tendsto' hlim fun N =>
    le_trans (measure_mono (hsub N)) (htail N)) zero_le

/-- A shifted exponential tail makes an extended-natural random scale finite almost surely. -/
theorem ae_ne_top_of_enat_exponential_tail [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℕ∞} (Cst : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (htail : ∀ N : ℕ, P {omega | (N : ℕ∞) ≤ X omega} ≤
      ENNReal.ofReal (Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b))) :
    ∀ᵐ omega ∂P, X omega ≠ ⊤ := by
  set r : ℝ := Real.exp (-(a / b)) with hrdef
  have hr0 : (0 : ℝ) ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have hab : (0 : ℝ) < a / b := div_pos ha hb
    have hlt := Real.exp_lt_exp.mpr (show -(a / b) < (0 : ℝ) by linarith only [hab])
    rwa [Real.exp_zero] at hlt
  have hpow : ∀ N : ℕ, r ^ N = Real.exp (-(a / b) * (N : ℝ)) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ih, hrdef, ← Real.exp_add]
        congr 1
        push_cast
        ring
  have hrw : ∀ N : ℕ, Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b) =
      Cst * Real.exp (a * Cst / b) * r ^ N := by
    intro N
    have hstep : Cst * Real.exp (a * Cst / b) * r ^ N =
        Cst * (Real.exp (a * Cst / b) * Real.exp (-(a / b) * (N : ℝ))) := by
      rw [hpow N]; ring
    rw [hstep, ← Real.exp_add]
    have harg : a * Cst / b + -(a / b) * (N : ℝ) = -(a * ((N : ℝ) - Cst)) / b := by
      field_simp
      ring
    rw [harg]
  have hlim : Filter.Tendsto
      (fun N : ℕ => ENNReal.ofReal (Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b)))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun N : ℕ => Cst * Real.exp (a * Cst / b) * r ^ N)
        Filter.atTop (nhds (Cst * Real.exp (a * Cst / b) * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul _
    rw [mul_zero] at h0
    have hreal : Filter.Tendsto
        (fun N : ℕ => Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b)) Filter.atTop
        (nhds 0) := h0.congr fun N => (hrw N).symm
    have hcomp := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    simpa using! hcomp
  exact ae_ne_top_of_enat_tail_tendsto_zero hlim htail

/-- **Real countable subadditivity along an inclusion.**  If `S ⊆ ⋃ i, T i` and
each `P.real (T i)` is dominated by a summable nonnegative `b i`, then
`P.real S ≤ ∑' i, b i`.  The route is `measure_iUnion_le` in `ℝ≥0∞`, which is
valid for arbitrary — not necessarily measurable — sets, followed by a single
`toReal`. -/
theorem measureReal_le_tsum_of_subset [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {S : Set Ω} {T : ℕ → Set Ω} (hsub : S ⊆ ⋃ i, T i)
    {b : ℕ → ℝ} (hb0 : ∀ i, 0 ≤ b i) (hb : ∀ i, P.real (T i) ≤ b i)
    (hsum : Summable b) : P.real S ≤ ∑' i, b i := by
  have hstep : P S ≤ ENNReal.ofReal (∑' i, b i) := by
    calc P S ≤ P (⋃ i, T i) := measure_mono hsub
      _ ≤ ∑' i, P (T i) := measure_iUnion_le _
      _ ≤ ∑' i, ENNReal.ofReal (b i) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          have hrw : P (T i) = ENNReal.ofReal (P.real (T i)) := by
            rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P (T i))]
          rw [hrw]
          exact ENNReal.ofReal_le_ofReal (hb i)
      _ = ENNReal.ofReal (∑' i, b i) := (ENNReal.ofReal_tsum_of_nonneg hb0 hsum).symm
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hstep
  rwa [ENNReal.toReal_ofReal (tsum_nonneg hb0), ← measureReal_def] at hle

/-- The geometric-series representation of the shifted per-window bound. -/
private theorem exp_window_repr (B c₀ : ℝ) (M i : ℕ) :
    B * Real.exp (-c₀ * ((M : ℝ) + (i : ℝ)))
      = (B * Real.exp (-c₀ * (M : ℝ))) * (Real.exp (-c₀)) ^ i := by
  have h1 : (Real.exp (-c₀)) ^ i = Real.exp ((i : ℝ) * (-c₀)) :=
    (Real.exp_nat_mul (-c₀) i).symm
  have h2 : Real.exp (-c₀ * ((M : ℝ) + (i : ℝ)))
      = Real.exp (-c₀ * (M : ℝ)) * Real.exp ((i : ℝ) * (-c₀)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, h2]; ring

/-- **The core geometric summation.**  The tail at level `M + 1` sums the
per-window bounds over all windows of length `≥ M`. -/
theorem minimalScale_tail_sum_le [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (bad : ℕ → Ω → Prop) {B c₀ : ℝ} (hB : 0 ≤ B)
    (hc₀ : 0 < c₀)
    (hwin : ∀ n : ℕ, P.real {ω | bad n ω} ≤ B * Real.exp (-c₀ * (n : ℝ)))
    (M : ℕ) :
    P.real {ω | ((M + 1 : ℕ) : ℕ∞) ≤ minimalScaleEN bad ω}
      ≤ B * Real.exp (-c₀ * (M : ℝ)) / (1 - Real.exp (-c₀)) := by
  have hq0 : (0 : ℝ) ≤ Real.exp (-c₀) := (Real.exp_pos _).le
  have hq1 : Real.exp (-c₀) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_lt_exp.2 (by linarith only [hc₀])
  set b : ℕ → ℝ := fun i => B * Real.exp (-c₀ * ((M : ℝ) + (i : ℝ))) with hbdef
  have hb0 : ∀ i, 0 ≤ b i := fun i => mul_nonneg hB (Real.exp_pos _).le
  have hb : ∀ i, P.real {ω | bad (M + i) ω} ≤ b i := by
    intro i
    have hw := hwin (M + i)
    rw [show ((M + i : ℕ) : ℝ) = (M : ℝ) + (i : ℝ) by push_cast; ring] at hw
    exact hw
  have hrepr : b = fun i => (B * Real.exp (-c₀ * (M : ℝ))) * (Real.exp (-c₀)) ^ i := by
    funext i
    rw [hbdef]
    exact exp_window_repr B c₀ M i
  have hsum : Summable b := by
    rw [hrepr]
    exact (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have htsum : ∑' i, b i
      = (B * Real.exp (-c₀ * (M : ℝ))) * (1 - Real.exp (-c₀))⁻¹ := by
    rw [hrepr, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  calc P.real {ω | ((M + 1 : ℕ) : ℕ∞) ≤ minimalScaleEN bad ω}
      ≤ ∑' i, b i :=
        measureReal_le_tsum_of_subset (minimalScaleEN_tail_subset bad M) hb0 hb hsum
    _ = B * Real.exp (-c₀ * (M : ℝ)) / (1 - Real.exp (-c₀)) := by
        rw [htsum, div_eq_mul_inv]

/-- **The geometric tail of the minimal scale, prefactor form.**  From per-window
tails `P[bad n] ≤ B · exp (-c₀ n)` with `B ≥ 1`, the minimal scale satisfies

`P[N ≤ Z] ≤ (B · exp c₀ / (1 - exp (-c₀))) · exp (-c₀ N)`,

with the rate untouched and the geometric-summation constant explicit. -/
theorem minimalScaleEN_exp_tail_const [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (bad : ℕ → Ω → Prop) {B c₀ : ℝ} (hB : 1 ≤ B)
    (hc₀ : 0 < c₀)
    (hwin : ∀ n : ℕ, P.real {ω | bad n ω} ≤ B * Real.exp (-c₀ * (n : ℝ)))
    (N : ℕ) :
    P.real {ω | (N : ℕ∞) ≤ minimalScaleEN bad ω}
      ≤ (B * Real.exp c₀ / (1 - Real.exp (-c₀))) * Real.exp (-c₀ * (N : ℝ)) := by
  have hq1 : Real.exp (-c₀) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_lt_exp.2 (by linarith only [hc₀])
  have hg : 0 < 1 - Real.exp (-c₀) := by linarith only [hq1]
  have hgle : 1 - Real.exp (-c₀) ≤ 1 := by
    linarith only [(Real.exp_pos (-c₀)).le]
  have hexp1 : 1 ≤ Real.exp c₀ := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_le_exp.2 (by linarith only [hc₀])
  have hcancel : Real.exp c₀ * Real.exp (-c₀) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    refine le_trans measureReal_le_one ?_
    have hprod : (1 : ℝ) ≤ B * Real.exp c₀ := by
      have h := mul_le_mul hB hexp1 zero_le_one (le_trans zero_le_one hB)
      rwa [one_mul] at h
    have hone : (1 : ℝ) ≤ B * Real.exp c₀ / (1 - Real.exp (-c₀)) := by
      rw [le_div_iff₀ hg]
      linarith only [hprod, hgle]
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    exact hone
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 1 := ⟨N - 1, by omega⟩
    refine le_trans
      (minimalScale_tail_sum_le P bad (by linarith only [hB]) hc₀ hwin M) ?_
    have hsplit : Real.exp (-c₀ * ((M + 1 : ℕ) : ℝ))
        = Real.exp (-c₀ * (M : ℝ)) * Real.exp (-c₀) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    have hnum : B * Real.exp c₀ * (Real.exp (-c₀ * (M : ℝ)) * Real.exp (-c₀))
        = B * Real.exp (-c₀ * (M : ℝ)) := by
      calc B * Real.exp c₀ * (Real.exp (-c₀ * (M : ℝ)) * Real.exp (-c₀))
          = B * Real.exp (-c₀ * (M : ℝ)) * (Real.exp c₀ * Real.exp (-c₀)) := by ring
        _ = B * Real.exp (-c₀ * (M : ℝ)) := by rw [hcancel, mul_one]
    rw [hsplit, div_mul_eq_mul_div, hnum]

/-! ### The union bound over a finite covering family -/

/-- **Union bound along a finite covering family.**  If every sample in the event
`{q}` is witnessed by some member `z` of the finite family `Z`, and each event
`{p z}` has probability at most `K`, then `P[q] ≤ |Z| · K`.  No measurability of
any of the sets is required. -/
theorem measureReal_le_card_mul_of_cover [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ι : Type*} (Z : Finset ι) (p : ι → Ω → Prop)
    (q : Ω → Prop) {K : ℝ} (hcover : ∀ ω, q ω → ∃ z ∈ Z, p z ω)
    (hz : ∀ z ∈ Z, P.real {ω | p z ω} ≤ K) :
    P.real {ω | q ω} ≤ (Z.card : ℝ) * K := by
  have hsub : {ω | q ω} ⊆ ⋃ z ∈ Z, {ω | p z ω} := by
    intro ω hω
    obtain ⟨z, hzZ, hzω⟩ := hcover ω hω
    exact Set.mem_biUnion hzZ hzω
  calc P.real {ω | q ω} ≤ P.real (⋃ z ∈ Z, {ω | p z ω}) :=
        measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ z ∈ Z, P.real {ω | p z ω} := measureReal_biUnion_finset_le Z _
    _ ≤ ∑ _z ∈ Z, K := Finset.sum_le_sum hz
    _ = (Z.card : ℝ) * K := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### Absorbing a centre count into the rate -/

/-- **Centre-count absorption, prefactor form.**
`3^{D(n+1)} · exp (-c₁ n) ≤ 3^D · exp (-c₀ n)` as soon as
`c₁ ≥ D · log 3 + c₀`.  Unlike `count_exp_absorb` this form keeps an
`n`-proportional per-window rate; the price is the constant `3^D`. -/
theorem count_exp_absorb_const {D : ℕ} {c₁ c₀ : ℝ} (n : ℕ)
    (h : (D : ℝ) * Real.log 3 + c₀ ≤ c₁) :
    ((3 : ℝ) ^ (D * (n + 1))) * Real.exp (-c₁ * (n : ℝ))
      ≤ (3 : ℝ) ^ D * Real.exp (-c₀ * (n : ℝ)) := by
  have hsplit : ((3 : ℝ) ^ (D * (n + 1))) = (3 : ℝ) ^ D * (3 : ℝ) ^ (D * n) := by
    rw [← pow_add]; congr 1; ring
  have hexp : ((3 : ℝ) ^ (D * n)) = Real.exp (Real.log 3 * ((D : ℝ) * (n : ℝ))) := by
    rw [← Real.rpow_natCast (3 : ℝ) (D * n),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [hsplit, hexp, mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hslack : (0 : ℝ) ≤ c₁ - ((D : ℝ) * Real.log 3 + c₀) := by linarith only [h]
  linarith only [mul_nonneg hslack hn]

/-! ### The prefactor constant -/

/-- The prefactor of the minimal-scale tail in its rate-preserving form: a
centre count `3^D` times the geometric-summation constant
`exp c₀ / (1 - exp (-c₀))`. -/
def windowTailConst (D : ℕ) (c₀ : ℝ) : ℝ :=
  (3 : ℝ) ^ D * Real.exp c₀ / (1 - Real.exp (-c₀))

theorem windowTailConst_eq (D : ℕ) (c₀ : ℝ) :
    windowTailConst D c₀ = (3 : ℝ) ^ D * Real.exp c₀ / (1 - Real.exp (-c₀)) := rfl


/-- A large-power regime supplies the two rates used in window-tail absorption. -/
theorem rates_ge_of_large_power {C K gamma numerator : ℝ}
    (hC : 1 ≤ C) (hK : 0 < K) (hKC : K ≤ C) (hgamma : 0 < gamma)
    (hregime : C ^ (10 : ℕ) * gamma ≤ numerator) :
    C ≤ numerator / (K * gamma) ∧ 1 ≤ numerator / (C * gamma) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hpower : C ≤ C ^ (10 : ℕ) := by
    calc C = C ^ (1 : ℕ) := (pow_one C).symm
      _ ≤ C ^ (10 : ℕ) := pow_le_pow_right₀ hC (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ (mul_pos hK hgamma)]
    refine le_trans ?_ hregime
    have hfactor : C * K ≤ C ^ (10 : ℕ) := by
      calc C * K ≤ C * C := mul_le_mul_of_nonneg_left hKC hCpos.le
        _ = C ^ (2 : ℕ) := by ring
        _ ≤ C ^ (10 : ℕ) := pow_le_pow_right₀ hC (by norm_num)
    calc C * (K * gamma) = (C * K) * gamma := by ring
      _ ≤ C ^ (10 : ℕ) * gamma := mul_le_mul_of_nonneg_right hfactor hgamma.le
  · rw [le_div_iff₀ (mul_pos hCpos hgamma), one_mul]
    exact (mul_le_mul_of_nonneg_right hpower hgamma.le).trans hregime

/-- A rate of at least one absorbs the geometric prefactor after shifting the tail by one. -/
theorem windowTailConst_mul_exp_le_shift (D : ℕ) {rate C : ℝ}
    (hrate : 1 ≤ rate) (hC : 2 * (3 : ℝ) ^ D ≤ C) (N : ℝ) :
    windowTailConst D rate * Real.exp (-rate * N) ≤
      C * Real.exp (-rate * (N - 1)) := by
  have hCnn : 0 ≤ C := (by positivity : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ D).trans hC
  have hexpneg : Real.exp (-rate) ≤ 1 / 2 := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have hcancel : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hmono : Real.exp (-rate) ≤ Real.exp (-1 : ℝ) :=
      Real.exp_le_exp.2 (by linarith only [hrate])
    have hmul := mul_le_mul_of_nonneg_left htwo (Real.exp_pos (-1 : ℝ)).le
    linarith only [hmono, hmul, hcancel]
  have hdenominator : 0 < 1 - Real.exp (-rate) := by linarith only [hexpneg]
  have hfrac : (3 : ℝ) ^ D / (1 - Real.exp (-rate)) ≤ C := by
    rw [div_le_iff₀ hdenominator]
    have hhalf : (1 / 2 : ℝ) ≤ 1 - Real.exp (-rate) := by linarith only [hexpneg]
    have hmul := mul_le_mul_of_nonneg_left hhalf hCnn
    linarith only [hmul, hC]
  have hcombine : Real.exp rate * Real.exp (-rate * N) = Real.exp (-rate * (N - 1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    windowTailConst D rate * Real.exp (-rate * N) =
        ((3 : ℝ) ^ D / (1 - Real.exp (-rate))) *
          (Real.exp rate * Real.exp (-rate * N)) := by rw [windowTailConst_eq]; ring
    _ = ((3 : ℝ) ^ D / (1 - Real.exp (-rate))) * Real.exp (-rate * (N - 1)) := by
      rw [hcombine]
    _ ≤ C * Real.exp (-rate * (N - 1)) :=
      mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le

/-- Weaken the rate of a probability tail, retaining its prefactor and handling length zero. -/
theorem measure_exponential_tail_weaken_rate [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (events : ℕ → Set Ω) {A C gamma numerator : ℝ}
    (hA : 1 ≤ A) (hAC : A ≤ C) (hgamma : 0 < gamma) (hnumerator : 0 ≤ numerator)
    (htail : ∀ N : ℕ, 0 < N → P (events N) ≤
      ENNReal.ofReal (A * Real.exp (-(((N : ℝ) - 1) * numerator) / (A * gamma))))
    (N : ℕ) :
    P (events N) ≤
      ENNReal.ofReal (A * Real.exp (-(((N : ℝ) - 1) * numerator) / (C * gamma))) := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hCpos : 0 < C := hApos.trans_le hAC
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hmeasure : P (events 0) ≤ ENNReal.ofReal 1 := by
      simpa only [measure_univ, ENNReal.ofReal_one] using
        (measure_mono (Set.subset_univ (events 0)) : P (events 0) ≤ P Set.univ)
    refine hmeasure.trans (ENNReal.ofReal_le_ofReal ?_)
    have hexponent : 0 ≤ -(((0 : ℝ) - 1) * numerator) / (C * gamma) :=
      div_nonneg (by linarith only [hnumerator]) (mul_pos hCpos hgamma).le
    have hmul := mul_le_mul_of_nonneg_left (Real.one_le_exp hexponent) hApos.le
    simp only [mul_one] at hmul
    simpa only [Nat.cast_zero] using hA.trans hmul
  · refine (htail N hN).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hApos.le))
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN.ne'
    have hfactor : 0 ≤ ((N : ℝ) - 1) * numerator :=
      mul_nonneg (by linarith only [hNreal]) hnumerator
    have hquotient := div_le_div_of_nonneg_left hfactor (mul_pos hApos hgamma)
      (mul_le_mul_of_nonneg_right hAC hgamma.le)
    rw [neg_div, neg_div]
    exact neg_le_neg hquotient

/-! ### The assembled producers -/

/-- **The minimal-scale tail from per-centre window tails, prefactor form.**

Same architecture as `windowScale_tail_of_center_tails`, but with the
per-witness tails at the `n`-proportional rate `exp (-c₁ n)` and required only
for `n ≥ 1`: the length-`0` window is absorbed by `P ≤ 1 ≤ 3^D`.  The conclusion
keeps the rate `c₀` untouched and pays the prefactor `windowTailConst D c₀`. -/
theorem windowScale_tail_const_of_center_tails [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {ι : Type*} {D : ℕ} (bad : ℕ → Ω → Prop)
    (centers : ℕ → Finset ι) (centerBad : ι → ℕ → Ω → Prop) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀)
    (hcard : ∀ n : ℕ, ((centers n).card : ℝ) ≤ (3 : ℝ) ^ (D * (n + 1)))
    (habsorb : (D : ℝ) * Real.log 3 + c₀ ≤ c₁)
    (hcover : ∀ (n : ℕ) (ω : Ω), bad n ω → ∃ z ∈ centers n, centerBad z n ω)
    (hcenter : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ centers n,
      P.real {ω | centerBad z n ω} ≤ Real.exp (-c₁ * (n : ℝ)))
    (N : ℕ) :
    P.real {ω | (N : ℕ∞) ≤ minimalScaleEN bad ω}
      ≤ windowTailConst D c₀ * Real.exp (-c₀ * (N : ℝ)) := by
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ D := one_le_pow₀ (by norm_num)
  rw [windowTailConst_eq]
  refine minimalScaleEN_exp_tail_const P bad (B := (3 : ℝ) ^ D) h3 hc₀ (fun n => ?_) N
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    refine le_trans measureReal_le_one ?_
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    exact h3
  · calc P.real {ω | bad n ω}
        ≤ ((centers n).card : ℝ) * Real.exp (-c₁ * (n : ℝ)) :=
          measureReal_le_card_mul_of_cover (centers n) (fun z ω => centerBad z n ω)
            (fun ω => bad n ω) (hcover n) (hcenter n hnpos)
      _ ≤ ((3 : ℝ) ^ (D * (n + 1))) * Real.exp (-c₁ * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (hcard n) (Real.exp_pos _).le
      _ ≤ (3 : ℝ) ^ D * Real.exp (-c₀ * (n : ℝ)) := count_exp_absorb_const n habsorb

end Generic

end

end Algsuperdiff.Probability
