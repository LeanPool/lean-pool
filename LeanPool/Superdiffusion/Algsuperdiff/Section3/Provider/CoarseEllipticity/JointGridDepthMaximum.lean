/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.GridWeights

/-!
# JointGridDepthMaximum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A joint grid-and-depth `Gamma_1` maximum

This file combines the spatial grid entropy and the countable depth entropy
before taking any per-depth maximum.  If the row at depth `k` has at most
`exp (growth * (k + 1))` entries and every entry has a common one-sided
`Gamma_1` bound at scale `a k`, then one random envelope controls every row
simultaneously at the deterministic price

`(growth + 2) * (k + 1) * a k`.

The simultaneous domination is necessarily almost everywhere under marginal
tail hypotheses.  No pointwise conclusion is asserted: the downstream null-set
patch is responsible for converting this output into an everywhere statement
when that is needed.

The triadic specialization uses
`growth = d * log 3`, since the depth-`k` row contains exactly
`3 ^ (d * (k + 1))` descendants.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums

noncomputable section

variable {Omega ι : Type*}

/-- The entropy constant which pays for both a row of exponential size and
the countable union over depths. -/
def jointDepthEntropyConst (growth : ℝ) : ℝ :=
  growth + 2

theorem jointDepthEntropyConst_pos {growth : ℝ} (hgrowth : 0 ≤ growth) :
    0 < jointDepthEntropyConst growth := by
  unfold jointDepthEntropyConst
  linarith

/-- The positive deterministic denominator used to normalize row `k`. -/
def gradedFiniteEnvelopeScale (growth : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  jointDepthEntropyConst growth * ((k : ℝ) + 1) * a k

theorem gradedFiniteEnvelopeScale_pos {growth : ℝ} {a : ℕ → ℝ}
    (hgrowth : 0 ≤ growth) (ha : ∀ k, 0 < a k) (k : ℕ) :
    0 < gradedFiniteEnvelopeScale growth a k := by
  unfold gradedFiniteEnvelopeScale
  exact mul_pos (mul_pos (jointDepthEntropyConst_pos hgrowth) (by positivity)) (ha k)

/-- The extended-valued joint maximum.  Keeping this intermediate object makes the
countable supremum measurable without first assuming that it is finite. -/
def gradedFiniteEnvelopeENNReal (I : ℕ → Finset ι)
    (X : ℕ → ι → Omega → ℝ) (a : ℕ → ℝ) (growth : ℝ) (omega : Omega) : ENNReal :=
  ⨆ k : ℕ, ⨆ i : {i // i ∈ I k},
    ENNReal.ofReal (X k i.1 omega / gradedFiniteEnvelopeScale growth a k)

/-- The real-valued common envelope.  Its almost-everywhere finiteness is a
theorem below, not an implicit pointwise consequence of the marginal tails. -/
def gradedFiniteEnvelope (I : ℕ → Finset ι)
    (X : ℕ → ι → Omega → ℝ) (a : ℕ → ℝ) (growth : ℝ) (omega : Omega) : ℝ :=
  (gradedFiniteEnvelopeENNReal I X a growth omega).toReal

theorem gradedFiniteEnvelope_nonneg (I : ℕ → Finset ι)
    (X : ℕ → ι → Omega → ℝ) (a : ℕ → ℝ) (growth : ℝ) (omega : Omega) :
    0 ≤ gradedFiniteEnvelope I X a growth omega :=
  ENNReal.toReal_nonneg

theorem measurable_gradedFiniteEnvelope (I : ℕ → Finset ι)
    (X : ℕ → ι → Omega → ℝ) (a : ℕ → ℝ) (growth : ℝ)
    [MeasurableSpace Omega]
    (hXmeas : ∀ k i, i ∈ I k → Measurable (X k i)) :
    Measurable (gradedFiniteEnvelope I X a growth) := by
  apply Measurable.ennreal_toReal
  apply Measurable.iSup
  intro k
  apply Measurable.iSup
  intro i
  exact ((hXmeas k i.1 i.2).div_const _).ennreal_ofReal

/-- The bad event in one finite row at threshold `t`. -/
def gradedFiniteRowEvent (I : ℕ → Finset ι) (X : ℕ → ι → Omega → ℝ)
    (a : ℕ → ℝ) (growth t : ℝ) (k : ℕ) : Set Omega :=
  ⋃ i ∈ I k, upperTailEvent (X k i)
    (gradedFiniteEnvelopeScale growth a k * t)

/-- The bad event at any depth at threshold `t`. -/
def gradedFiniteAllRowsEvent (I : ℕ → Finset ι) (X : ℕ → ι → Omega → ℝ)
    (a : ℕ → ℝ) (growth t : ℝ) : Set Omega :=
  ⋃ k : ℕ, gradedFiniteRowEvent I X a growth t k

private theorem two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  linarith [Real.add_one_le_exp (1 : ℝ)]

private theorem exp_neg_le_half {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-t) ≤ 1 / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp t :=
    two_le_exp_one.trans (Real.exp_le_exp.2 ht)
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos t)]
  linarith

private theorem summable_exp_neg_two_mul_succ {t : ℝ} (ht : 1 ≤ t) :
    Summable fun k : ℕ => Real.exp (-(2 * ((k : ℝ) + 1) * t)) := by
  have hq0 : 0 ≤ Real.exp (-(2 * t)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(2 * t)) < 1 := by
    have hneg : -(2 * t) < 0 := by linarith
    simpa only [Real.exp_zero] using Real.exp_lt_exp.2 hneg
  have hgeom : Summable fun k : ℕ => Real.exp (-(2 * t)) ^ (k + 1) :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_right _).congr
      fun k => (pow_succ _ k).symm
  refine hgeom.congr fun k => ?_
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem tsum_exp_neg_two_mul_succ_le {t : ℝ} (ht : 1 ≤ t) :
    ∑' k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) * t)) ≤ Real.exp (-t) := by
  let u : ℝ := Real.exp (-t)
  let q : ℝ := Real.exp (-(2 * t))
  have hu0 : 0 < u := Real.exp_pos _
  have hu_half : u ≤ 1 / 2 := exp_neg_le_half ht
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    have hneg : -(2 * t) < 0 := by linarith
    simpa only [q, Real.exp_zero] using Real.exp_lt_exp.2 hneg
  have hq_eq : q = u ^ 2 := by
    dsimp [q, u]
    rw [show -(2 * t) = (-t) + (-t) by ring, Real.exp_add]
    ring
  have hsum : ∑' k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) * t)) =
      (1 - q)⁻¹ * q := by
    have hterm : ∀ k : ℕ,
        Real.exp (-(2 * ((k : ℝ) + 1) * t)) = q ^ (k + 1) := by
      intro k
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [tsum_congr hterm]
    have hpow : ∀ k : ℕ, q ^ (k + 1) = q ^ k * q := fun k => pow_succ q k
    rw [tsum_congr hpow, tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
  have hq_half : q ≤ 1 / 2 := by
    rw [hq_eq]
    nlinarith [hu0, hu_half]
  have hden : 0 < 1 - q := by linarith
  have hinv : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hden]
    linarith
  rw [hsum]
  calc
    (1 - q)⁻¹ * q ≤ 2 * q := mul_le_mul_of_nonneg_right hinv hq0
    _ = 2 * u ^ 2 := by rw [hq_eq]
    _ ≤ u := by nlinarith

private theorem measureReal_gradedFiniteRowEvent_le
    [MeasurableSpace Omega] {mu : Measure Omega} [IsFiniteMeasure mu]
    (I : ℕ → Finset ι) (X : ℕ → ι → Omega → ℝ) (a : ℕ → ℝ)
    {growth t : ℝ} (hgrowth : 0 ≤ growth) (ht : 1 ≤ t)
    (hcard : ∀ k, ((I k).card : ℝ) ≤
      Real.exp (growth * ((k : ℝ) + 1)))
    (hX : ∀ k i, i ∈ I k →
      IsBigOWith mu (gammaSigma 1) (X k i) (a k)) (k : ℕ) :
    mu.real (gradedFiniteRowEvent I X a growth t k) ≤
      Real.exp (-(2 * ((k : ℝ) + 1) * t)) := by
  let u : ℝ := jointDepthEntropyConst growth * ((k : ℝ) + 1) * t
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hu1 : 1 ≤ u := by
    have hconst : 2 ≤ jointDepthEntropyConst growth := by
      unfold jointDepthEntropyConst
      linarith
    dsimp [u]
    nlinarith [mul_le_mul hconst hk1 zero_le_one (by linarith : 0 ≤
      jointDepthEntropyConst growth)]
  have hmember : ∀ i ∈ I k,
      mu.real (upperTailEvent (X k i)
        (gradedFiniteEnvelopeScale growth a k * t)) ≤ Real.exp (-u) := by
    intro i hi
    have htail := (isBigOWith_gammaSigma_iff.mp (hX k i hi)) hu1
    have hthreshold : gradedFiniteEnvelopeScale growth a k * t = a k * u := by
      dsimp [gradedFiniteEnvelopeScale, u]
      ring
    rw [hthreshold]
    simpa only [Real.rpow_one] using htail
  have hrow := measureReal_biUnion_finset_le (μ := mu) (I k)
    (fun i => upperTailEvent (X k i)
      (gradedFiniteEnvelopeScale growth a k * t))
  have hsum :
      (∑ i ∈ I k, mu.real (upperTailEvent (X k i)
        (gradedFiniteEnvelopeScale growth a k * t))) ≤
        ∑ _i ∈ I k, Real.exp (-u) :=
    Finset.sum_le_sum fun i hi => hmember i hi
  have hcardmul : ((I k).card : ℝ) * Real.exp (-u) ≤
      Real.exp (growth * ((k : ℝ) + 1)) * Real.exp (-u) :=
    mul_le_mul_of_nonneg_right (hcard k) (Real.exp_pos _).le
  have hexponent :
      growth * ((k : ℝ) + 1) - u ≤ -(2 * ((k : ℝ) + 1) * t) := by
    have hnonpos : growth * ((k : ℝ) + 1) * (1 - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hgrowth (by positivity)) (sub_nonpos.mpr ht)
    dsimp [u, jointDepthEntropyConst]
    linarith
  calc
    mu.real (gradedFiniteRowEvent I X a growth t k)
        ≤ ∑ i ∈ I k, mu.real (upperTailEvent (X k i)
            (gradedFiniteEnvelopeScale growth a k * t)) := by
          simpa only [gradedFiniteRowEvent] using hrow
    _ ≤ ∑ _i ∈ I k, Real.exp (-u) := hsum
    _ = ((I k).card : ℝ) * Real.exp (-u) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (growth * ((k : ℝ) + 1)) * Real.exp (-u) := hcardmul
    _ = Real.exp (growth * ((k : ℝ) + 1) - u) := by
      rw [← Real.exp_add, sub_eq_add_neg]
    _ ≤ Real.exp (-(2 * ((k : ℝ) + 1) * t)) := Real.exp_le_exp.2 hexponent

/-- The spatial and depth entropies are paid in one union bound. -/
theorem measureReal_gradedFiniteAllRowsEvent_le
    [MeasurableSpace Omega] {mu : Measure Omega} [IsFiniteMeasure mu]
    (I : ℕ → Finset ι) (X : ℕ → ι → Omega → ℝ) (a : ℕ → ℝ)
    {growth t : ℝ} (hgrowth : 0 ≤ growth) (ht : 1 ≤ t)
    (hcard : ∀ k, ((I k).card : ℝ) ≤
      Real.exp (growth * ((k : ℝ) + 1)))
    (hX : ∀ k i, i ∈ I k →
      IsBigOWith mu (gammaSigma 1) (X k i) (a k)) :
    mu.real (gradedFiniteAllRowsEvent I X a growth t) ≤ Real.exp (-t) := by
  have hrow : ∀ k : ℕ,
      mu.real (gradedFiniteRowEvent I X a growth t k) ≤
        Real.exp (-(2 * ((k : ℝ) + 1) * t)) :=
    measureReal_gradedFiniteRowEvent_le I X a hgrowth ht hcard hX
  have hsummable := summable_exp_neg_two_mul_succ ht
  have hmeasure : mu (gradedFiniteAllRowsEvent I X a growth t) ≤
      ENNReal.ofReal
        (∑' k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) * t))) := by
    unfold gradedFiniteAllRowsEvent
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) hsummable]
    exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun k => by
      rw [← ENNReal.ofReal_toReal (measure_ne_top mu _)]
      exact ENNReal.ofReal_le_ofReal (hrow k))
  calc
    mu.real (gradedFiniteAllRowsEvent I X a growth t)
        ≤ (ENNReal.ofReal
          (∑' k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) * t)))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
    _ = ∑' k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) * t)) :=
      ENNReal.toReal_ofReal (tsum_nonneg fun k => (Real.exp_pos _).le)
    _ ≤ Real.exp (-t) := tsum_exp_neg_two_mul_succ_le ht

/-- The real common envelope has a unit-scale one-sided `Gamma_1` tail. -/
theorem isBigOWith_gammaSigma_one_gradedFiniteEnvelope
    [MeasurableSpace Omega] {mu : Measure Omega} [IsFiniteMeasure mu]
    (I : ℕ → Finset ι) (X : ℕ → ι → Omega → ℝ) (a : ℕ → ℝ)
    {growth : ℝ} (hgrowth : 0 ≤ growth) (ha : ∀ k, 0 < a k)
    (hcard : ∀ k, ((I k).card : ℝ) ≤
      Real.exp (growth * ((k : ℝ) + 1)))
    (hX : ∀ k i, i ∈ I k →
      IsBigOWith mu (gammaSigma 1) (X k i) (a k)) :
    IsBigOWith mu (gammaSigma 1) (gradedFiniteEnvelope I X a growth) 1 := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  have hsubset : upperTailEvent (gradedFiniteEnvelope I X a growth) (1 * t) ⊆
      gradedFiniteAllRowsEvent I X a growth t := by
    intro omega homega
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    have hVpos : 0 < gradedFiniteEnvelope I X a growth omega := by
      rw [mem_upperTailEvent] at homega
      have htV : t < gradedFiniteEnvelope I X a growth omega := by
        simpa only [one_mul] using homega
      exact lt_of_le_of_lt ht0 htV
    have hfinite : gradedFiniteEnvelopeENNReal I X a growth omega ≠ ⊤ :=
      (ENNReal.toReal_pos_iff.mp hVpos).2.ne
    have hsup : ENNReal.ofReal t < gradedFiniteEnvelopeENNReal I X a growth omega :=
      (ENNReal.ofReal_lt_iff_lt_toReal ht0 hfinite).2 (by
        rw [mem_upperTailEvent] at homega
        simpa only [gradedFiniteEnvelope, one_mul] using homega)
    rw [gradedFiniteEnvelopeENNReal, lt_iSup_iff] at hsup
    obtain ⟨k, hk⟩ := hsup
    rw [lt_iSup_iff] at hk
    obtain ⟨i, hi⟩ := hk
    have hreal : t < X k i.1 omega / gradedFiniteEnvelopeScale growth a k :=
      (ENNReal.ofReal_lt_ofReal_iff'.mp hi).1
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    refine Set.mem_iUnion.2 ⟨i.1, Set.mem_iUnion.2 ⟨i.2, ?_⟩⟩
    rw [mem_upperTailEvent]
    have hscale := gradedFiniteEnvelopeScale_pos hgrowth ha k
    have hmul := (lt_div_iff₀ hscale).mp hreal
    simpa only [mul_comm] using hmul
  calc
    mu.real (upperTailEvent (gradedFiniteEnvelope I X a growth) (1 * t))
        ≤ mu.real (gradedFiniteAllRowsEvent I X a growth t) :=
      measureReal_mono hsubset
    _ ≤ Real.exp (-t) :=
      measureReal_gradedFiniteAllRowsEvent_le I X a hgrowth ht hcard hX
    _ = Real.exp (-(t ^ (1 : ℝ))) := by rw [Real.rpow_one]

private theorem summable_exp_neg_natCast_add_one :
    Summable fun n : ℕ => Real.exp (-((n : ℝ) + 1)) := by
  let q : ℝ := Real.exp (-1)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    simpa only [Real.exp_zero] using Real.exp_lt_exp.2 (by norm_num : (-1 : ℝ) < 0)
  have hgeom : Summable fun n : ℕ => q ^ n :=
    summable_geometric_of_lt_one hq0 hq1
  refine (hgeom.mul_right q).congr fun n => ?_
  dsimp [q]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- The extended joint maximum is finite almost everywhere.  This is the
precise Borel--Cantelli step which cannot be strengthened to pointwise
finiteness from marginal tail assumptions alone. -/
theorem ae_gradedFiniteEnvelopeENNReal_ne_top
    [MeasurableSpace Omega] {mu : Measure Omega} [IsFiniteMeasure mu]
    (I : ℕ → Finset ι) (X : ℕ → ι → Omega → ℝ) (a : ℕ → ℝ)
    {growth : ℝ} (hgrowth : 0 ≤ growth) (ha : ∀ k, 0 < a k)
    (hcard : ∀ k, ((I k).card : ℝ) ≤
      Real.exp (growth * ((k : ℝ) + 1)))
    (hX : ∀ k i, i ∈ I k →
      IsBigOWith mu (gammaSigma 1) (X k i) (a k)) :
    ∀ᵐ omega ∂mu, gradedFiniteEnvelopeENNReal I X a growth omega ≠ ⊤ := by
  let E : ℕ → Set Omega := fun n =>
    gradedFiniteAllRowsEvent I X a growth ((n : ℝ) + 1)
  have hEreal : ∀ n : ℕ, mu.real (E n) ≤ Real.exp (-((n : ℝ) + 1)) := by
    intro n
    have ht : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    simpa only [E] using
      (measureReal_gradedFiniteAllRowsEvent_le I X a hgrowth ht hcard hX)
  have hEennreal : ∀ n : ℕ,
      mu (E n) ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) + 1))) := by
    intro n
    rw [← ENNReal.ofReal_toReal (measure_ne_top mu (E n))]
    exact ENNReal.ofReal_le_ofReal (hEreal n)
  have hsum_ne_top : (∑' n : ℕ, mu (E n)) ≠ ⊤ := by
    have hmajor_ne_top :
        (∑' n : ℕ, ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)))) ≠ ⊤ :=
      summable_exp_neg_natCast_add_one.tsum_ofReal_ne_top
    exact ne_top_of_le_ne_top hmajor_ne_top (ENNReal.tsum_le_tsum hEennreal)
  filter_upwards [ae_eventually_notMem hsum_ne_top] with omega homega
  intro htop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 homega
  have hnot : omega ∉ E N := hN N le_rfl
  apply hnot
  rw [gradedFiniteEnvelopeENNReal, iSup₂_eq_top] at htop
  obtain ⟨k, i, hi⟩ := htop (ENNReal.ofReal ((N : ℝ) + 1)) ENNReal.ofReal_lt_top
  have hreal : (N : ℝ) + 1 <
      X k i.1 omega / gradedFiniteEnvelopeScale growth a k :=
    (ENNReal.ofReal_lt_ofReal_iff'.mp hi).1
  show omega ∈ gradedFiniteAllRowsEvent I X a growth ((N : ℝ) + 1)
  refine Set.mem_iUnion.2 ⟨k, ?_⟩
  refine Set.mem_iUnion.2 ⟨i.1, Set.mem_iUnion.2 ⟨i.2, ?_⟩⟩
  rw [mem_upperTailEvent]
  have hscale := gradedFiniteEnvelopeScale_pos hgrowth ha k
  have hmul := (lt_div_iff₀ hscale).mp hreal
  simpa only [mul_comm] using hmul

/-- Almost everywhere, the single envelope simultaneously dominates every
member in every row. -/
theorem ae_le_gradedFiniteEnvelope
    [MeasurableSpace Omega] {mu : Measure Omega} [IsFiniteMeasure mu]
    (I : ℕ → Finset ι) (X : ℕ → ι → Omega → ℝ) (a : ℕ → ℝ)
    {growth : ℝ} (hgrowth : 0 ≤ growth) (ha : ∀ k, 0 < a k)
    (hcard : ∀ k, ((I k).card : ℝ) ≤
      Real.exp (growth * ((k : ℝ) + 1)))
    (hX : ∀ k i, i ∈ I k →
      IsBigOWith mu (gammaSigma 1) (X k i) (a k)) :
    ∀ᵐ omega ∂mu, ∀ k i, i ∈ I k →
      X k i omega ≤ gradedFiniteEnvelopeScale growth a k *
        gradedFiniteEnvelope I X a growth omega := by
  filter_upwards [ae_gradedFiniteEnvelopeENNReal_ne_top I X a hgrowth ha hcard hX]
    with omega hfinite
  intro k i hi
  have hcomponent : ENNReal.ofReal
      (X k i omega / gradedFiniteEnvelopeScale growth a k) ≤
      gradedFiniteEnvelopeENNReal I X a growth omega := by
    unfold gradedFiniteEnvelopeENNReal
    exact (le_iSup (fun j : {j // j ∈ I k} =>
      ENNReal.ofReal (X k j.1 omega / gradedFiniteEnvelopeScale growth a k))
        ⟨i, hi⟩).trans (le_iSup (fun n : ℕ =>
          ⨆ j : {j // j ∈ I n},
            ENNReal.ofReal (X n j.1 omega /
              gradedFiniteEnvelopeScale growth a n)) k)
  have hreal : X k i omega / gradedFiniteEnvelopeScale growth a k ≤
      gradedFiniteEnvelope I X a growth omega := by
    exact (ENNReal.ofReal_le_iff_le_toReal hfinite).1 hcomponent
  have hscale := gradedFiniteEnvelopeScale_pos hgrowth ha k
  have hmul := (div_le_iff₀ hscale).mp hreal
  simpa only [mul_comm] using hmul

/-- The reusable generic package: one explicit nonnegative measurable
`Gamma_1` envelope, with simultaneous almost-everywhere row domination. -/
theorem gradedFiniteEnvelope_spec
    [MeasurableSpace Omega] {mu : Measure Omega} [IsFiniteMeasure mu]
    (I : ℕ → Finset ι) (X : ℕ → ι → Omega → ℝ) (a : ℕ → ℝ)
    {growth : ℝ} (hgrowth : 0 ≤ growth) (ha : ∀ k, 0 < a k)
    (hcard : ∀ k, ((I k).card : ℝ) ≤
      Real.exp (growth * ((k : ℝ) + 1)))
    (hXmeas : ∀ k i, i ∈ I k → Measurable (X k i))
    (hX : ∀ k i, i ∈ I k →
      IsBigOWith mu (gammaSigma 1) (X k i) (a k)) :
    (∀ omega, 0 ≤ gradedFiniteEnvelope I X a growth omega) ∧
      Measurable (gradedFiniteEnvelope I X a growth) ∧
      IsBigOWith mu (gammaSigma 1) (gradedFiniteEnvelope I X a growth) 1 ∧
      (∀ᵐ omega ∂mu, ∀ k i, i ∈ I k →
        X k i omega ≤ gradedFiniteEnvelopeScale growth a k *
          gradedFiniteEnvelope I X a growth omega) := by
  exact ⟨gradedFiniteEnvelope_nonneg I X a growth,
    measurable_gradedFiniteEnvelope I X a growth hXmeas,
    isBigOWith_gammaSigma_one_gradedFiniteEnvelope I X a hgrowth ha hcard hX,
    ae_le_gradedFiniteEnvelope I X a hgrowth ha hcard hX⟩

/-! ## The triadic grid specialization -/

/-- The dimension-only joint entropy constant for triadic descendants. -/
def triadicJointDepthEntropyConst (d : ℕ) : ℝ :=
  jointDepthEntropyConst ((d : ℝ) * Real.log 3)

theorem triadicJointDepthEntropyConst_pos (d : ℕ) :
    0 < triadicJointDepthEntropyConst d := by
  apply jointDepthEntropyConst_pos
  exact mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg (by norm_num))

/-- The exact triadic descendant count, rewritten in exponential-entropy
form for the generic joint maximum theorem. -/
theorem card_descendantsAtScale_originCube_le_exp (d : ℕ) (m : ℤ) (k : ℕ) :
    ((descendantsAtScale (originCube d m) (m - 1 - (k : ℤ))).card : ℝ) ≤
      Real.exp (((d : ℝ) * Real.log 3) * ((k : ℝ) + 1)) := by
  rw [card_descendantsAtScale_originCube]
  have hcast : ((3 ^ (d * (k + 1)) : ℕ) : ℝ) =
      (3 : ℝ) ^ (d * (k + 1)) := by norm_cast
  rw [hcast]
  have hexp : (3 : ℝ) ^ (d * (k + 1)) =
      Real.exp (((d * (k + 1) : ℕ) : ℝ) * Real.log 3) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  rw [hexp]
  apply le_of_eq
  congr 1
  push_cast
  ring

/-- The one random variable which jointly dominates all triadic descendants
at all positive scale gaps. -/
def jointGridDepthEnvelope (d : ℕ) (m : ℤ)
    (X : ℕ → TriadicCube d → Omega → ℝ) (a : ℕ → ℝ) : Omega → ℝ :=
  gradedFiniteEnvelope
    (fun k => descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    X a ((d : ℝ) * Real.log 3)

/-- The triadic joint grid-and-depth maximum package.  One measurable
nonnegative `Gamma_1` envelope controls every depth and every descendant
almost everywhere; the deterministic loss is linear in `k + 1` and depends
only on the dimension through `triadicJointDepthEntropyConst`. -/
theorem jointGridDepthEnvelope_spec
    [MeasurableSpace Omega] {mu : Measure Omega} [IsFiniteMeasure mu]
    (d : ℕ) (m : ℤ) (X : ℕ → TriadicCube d → Omega → ℝ) (a : ℕ → ℝ)
    (ha : ∀ k, 0 < a k)
    (hXmeas : ∀ (k : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
        Measurable (X k R))
    (hX : ∀ (k : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
        IsBigOWith mu (gammaSigma 1) (X k R) (a k)) :
    (∀ omega, 0 ≤ jointGridDepthEnvelope d m X a omega) ∧
      Measurable (jointGridDepthEnvelope d m X a) ∧
      IsBigOWith mu (gammaSigma 1) (jointGridDepthEnvelope d m X a) 1 ∧
      (∀ᵐ omega ∂mu, ∀ (k : ℕ) (R : TriadicCube d),
        R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
          X k R omega ≤
            triadicJointDepthEntropyConst d * ((k : ℝ) + 1) * a k *
              jointGridDepthEnvelope d m X a omega) := by
  have hgrowth : 0 ≤ (d : ℝ) * Real.log 3 :=
    mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg (by norm_num))
  have hgeneric := gradedFiniteEnvelope_spec
    (mu := mu)
    (fun k => descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    X a hgrowth ha (card_descendantsAtScale_originCube_le_exp d m) hXmeas hX
  simpa only [jointGridDepthEnvelope, gradedFiniteEnvelopeScale,
    triadicJointDepthEntropyConst] using hgeneric

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
