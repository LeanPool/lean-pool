/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedIndependentEndpoint

/-!
# MomentBoostedColoring

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Internal finite-color transport for the moment-boosted endpoint

This is the finite-range coloring step used by the large-cube route.  Each
color class is treated by the sharp independent-family endpoint, then a
finite union transfers the one-sided tail to their sum.  The resulting color
factor is fixed once the spatial dimension and the coloring scale are fixed;
it is deliberately left explicit here so that the stream application can
absorb it into its single dimension-only constant.

No generic `Gamma_sigma` triangle inequality occurs in this module.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open HCPolySupport HCPolySupport.IndependentSums
open scoped BigOperators

noncomputable section

private theorem sqrt_card_filter_le {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (c : ι → κ) (b : κ) :
    Real.sqrt (((s.filter fun i => c i = b).card : ℝ)) ≤ Real.sqrt (s.card : ℝ) := by
  apply Real.sqrt_le_sqrt
  exact_mod_cast Finset.card_filter_le (s := s) (p := fun i => c i = b)

private theorem finite_color_exponential_absorption {q x : ℝ}
    (hq : 1 ≤ q) (hx : 1 ≤ x) :
    q * Real.exp (-(q * x)) ≤ Real.exp (-x) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqm : 0 ≤ q - 1 := by linarith
  have hqexp : q ≤ Real.exp (q - 1) := by
    have h := Real.add_one_le_exp (q - 1)
    nlinarith
  have hmult : q - 1 ≤ (q - 1) * x := by
    nlinarith
  calc
    q * Real.exp (-(q * x)) ≤ Real.exp (q - 1) * Real.exp (-(q * x)) :=
      mul_le_mul_of_nonneg_right hqexp (by positivity)
    _ = Real.exp ((q - 1) - q * x) := by
      rw [← Real.exp_add]
      congr 1
    _ ≤ Real.exp (-x) := Real.exp_le_exp.2 (by nlinarith)

private theorem rpow_color_multiplier {q sigma t : ℝ}
    (hq : 1 ≤ q) (hsigma : 0 < sigma) (ht : 1 ≤ t) :
    (q ^ (1 / sigma) * t) ^ sigma = q * t ^ sigma := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  rw [Real.mul_rpow (Real.rpow_nonneg hq0 _) ht0,
    ← Real.rpow_mul hq0]
  have hcancel : (1 / sigma) * sigma = 1 := by
    field_simp [hsigma.ne']
  rw [hcancel, Real.rpow_one]

/-- A finite family split into independent color classes has the same sharp
one-sided stretched-exponential endpoint, with an explicit finite-color
factor.  This is internal infrastructure; all locality and stationarity
requirements are supplied later by the stream-specific application. -/
theorem isBigOWith_gammaSigma_finset_sum_momentBoosted_colored
    {Omega iota kappa : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] [DecidableEq kappa]
    {X : iota → Omega → ℝ} {s : Finset iota} {color : iota → kappa}
    {sigma : ℝ}
    (hs : s.Nonempty)
    (h_indep : ∀ b ∈ s.image color,
      iIndepFun
        (fun i : {i // i ∈ s.filter (fun j => color j = b)} => X i.1) mu)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) mu)
    (h_sq : ∀ i ∈ s, Integrable (fun omega => |X i omega| ^ (2 : ℕ)) mu)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hX : ∀ i ∈ s, IsBigOWith mu (momentBoostedGammaSigma sigma) (X i) 1)
    (hmean : ∀ i ∈ s, ∫ omega, X i omega ∂mu = 0)
    (hsecond : ∀ i ∈ s, ∫ omega, |X i omega| ^ (2 : ℕ) ∂mu ≤ 1) :
    IsBigOWith mu (gammaSigma sigma) (fun omega => ∑ i ∈ s, X i omega)
      (16 * ((s.image color).card : ℝ) *
        ((s.image color).card : ℝ) ^ (1 / sigma) *
        Real.sqrt (momentBoostedIndependentVariance sigma) * Real.sqrt (s.card : ℝ)) := by
  classical
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  let colors : Finset kappa := s.image color
  let q : ℝ := colors.card
  let D : ℝ := momentBoostedIndependentVariance sigma
  let R : ℝ := s.card
  let u : ℝ := q ^ (1 / sigma) * t
  let B : ℝ := 16 * Real.sqrt D * Real.sqrt R * u
  have hcolors : colors.Nonempty := by
    dsimp [colors]
    exact hs.image color
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.succ_le_of_lt hcolors.card_pos
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast hs.card_pos
  have hD : 0 < D := by
    dsimp [D]
    exact momentBoostedIndependentVariance_pos
  have hu : 1 ≤ u := by
    dsimp [u]
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow hq (by positivity)) ht
  have hu_sigma : u ^ sigma = q * t ^ sigma := by
    dsimp [u]
    exact rpow_color_multiplier hq hsigma ht
  have hclass : ∀ b ∈ colors,
      IsBigOWith mu (gammaSigma sigma)
        (fun omega => ∑ i ∈ s.filter (fun j => color j = b), X i omega)
        (16 * Real.sqrt D *
          Real.sqrt (((s.filter (fun j => color j = b)).card : ℝ))) := by
    intro b hb
    let sb : Finset iota := s.filter (fun j => color j = b)
    have hsb : sb.Nonempty := by
      rcases Finset.mem_image.mp (by simpa [colors] using hb) with ⟨i, hi, hcolor⟩
      refine ⟨i, ?_⟩
      simp [sb, hi, hcolor]
    let Y : {i // i ∈ sb} → Omega → ℝ := fun i => X i.1
    have hY_indep : iIndepFun Y mu := by
      simpa [Y, sb] using h_indep b (by simpa [colors] using hb)
    have hY_meas : ∀ i, Measurable (Y i) := fun i => h_meas i.1
    have hY_int : ∀ i ∈ sb.attach, Integrable (Y i) mu := by
      intro i _
      exact h_int i.1 (Finset.mem_of_mem_filter i.1 i.2)
    have hY_sq : ∀ i ∈ sb.attach,
        Integrable (fun omega => |Y i omega| ^ (2 : ℕ)) mu := by
      intro i _
      exact h_sq i.1 (Finset.mem_of_mem_filter i.1 i.2)
    have hY_tail : ∀ i ∈ sb.attach,
        IsBigOWith mu (momentBoostedGammaSigma sigma) (Y i) 1 := by
      intro i _
      exact hX i.1 (Finset.mem_of_mem_filter i.1 i.2)
    have hY_mean : ∀ i ∈ sb.attach, ∫ omega, Y i omega ∂mu = 0 := by
      intro i _
      exact hmean i.1 (Finset.mem_of_mem_filter i.1 i.2)
    have hY_second : ∀ i ∈ sb.attach,
        ∫ omega, |Y i omega| ^ (2 : ℕ) ∂mu ≤ 1 := by
      intro i _
      exact hsecond i.1 (Finset.mem_of_mem_filter i.1 i.2)
    have hendpoint := isBigOWith_gammaSigma_finset_sum_momentBoosted_independent
      (mu := mu) (X := Y) (s := sb.attach) (sigma := sigma)
      (by simpa using hsb) hY_indep hY_meas hY_int hY_sq hsigma hsigma_one
      hY_tail hY_mean hY_second
    have hsum :
        (fun omega => ∑ i ∈ sb.attach, Y i omega) =
          fun omega => ∑ i ∈ sb, X i omega := by
      funext omega
      simpa only [Y] using Finset.sum_attach (s := sb) (f := fun i => X i omega)
    rw [hsum] at hendpoint
    simpa [sb, D] using hendpoint
  have hsubset :
      upperTailEvent (fun omega => ∑ i ∈ s, X i omega) (q * B) ⊆
        ⋃ b ∈ colors,
          upperTailEvent (fun omega => ∑ i ∈ s.filter (fun j => color j = b), X i omega) B := by
    intro omega homega
    by_contra hnot
    have hterm : ∀ b ∈ colors,
        ∑ i ∈ s.filter (fun j => color j = b), X i omega ≤ B := by
      intro b hb
      apply le_of_not_gt
      intro hgt
      apply hnot
      simp only [Set.mem_iUnion, upperTailEvent, Set.mem_ofPred_eq]
      exact ⟨b, hb, hgt⟩
    have hsum :
        ∑ b ∈ colors, ∑ i ∈ s.filter (fun j => color j = b), X i omega ≤
          ∑ _b ∈ colors, B := by
      exact Finset.sum_le_sum fun b hb => hterm b hb
    have hfiber :
        ∑ b ∈ colors, ∑ i ∈ s.filter (fun j => color j = b), X i omega =
          ∑ i ∈ s, X i omega :=
      Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image_of_mem color hi) (fun i => X i omega)
    have hbound : ∑ i ∈ s, X i omega ≤ q * B := by
      rw [← hfiber]
      simpa [q, nsmul_eq_mul] using hsum
    exact (not_lt_of_ge hbound homega)
  have htail : ∀ b ∈ colors,
      mu.real
          (upperTailEvent
            (fun omega => ∑ i ∈ s.filter (fun j => color j = b), X i omega) B) ≤
        Real.exp (-(u ^ sigma)) := by
    intro b hb
    let sb : Finset iota := s.filter (fun j => color j = b)
    have hscale :
        (16 * Real.sqrt D * Real.sqrt ((sb.card : ℝ))) * u ≤ B := by
      have hsqrt := sqrt_card_filter_le s color b
      have hlead : 0 ≤ 16 * Real.sqrt D := by positivity
      have hu0 : 0 ≤ u := zero_le_one.trans hu
      calc
        (16 * Real.sqrt D * Real.sqrt ((sb.card : ℝ))) * u =
            (16 * Real.sqrt D) * Real.sqrt ((sb.card : ℝ)) * u := by ring
        _ ≤ (16 * Real.sqrt D) * Real.sqrt R * u :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsqrt hlead) hu0
        _ = B := by ring
    have hmono :
        upperTailEvent (fun omega => ∑ i ∈ sb, X i omega) B ⊆
          upperTailEvent (fun omega => ∑ i ∈ sb, X i omega)
            ((16 * Real.sqrt D * Real.sqrt ((sb.card : ℝ))) * u) := by
      intro omega homega
      exact lt_of_le_of_lt hscale homega
    calc
      mu.real (upperTailEvent (fun omega => ∑ i ∈ sb, X i omega) B) ≤
          mu.real
            (upperTailEvent (fun omega => ∑ i ∈ sb, X i omega)
              ((16 * Real.sqrt D * Real.sqrt ((sb.card : ℝ))) * u)) :=
        measureReal_mono hmono
      _ ≤ Real.exp (-(u ^ sigma)) := by
        have h := hclass b hb
        rw [isBigOWith_gammaSigma_iff] at h
        exact h hu
  calc
    mu.real
        (upperTailEvent (fun omega => ∑ i ∈ s, X i omega)
          ((16 * q * q ^ (1 / sigma) * Real.sqrt D * Real.sqrt R) * t)) ≤
        mu.real
          (⋃ b ∈ colors,
            upperTailEvent
              (fun omega => ∑ i ∈ s.filter (fun j => color j = b), X i omega) B) := by
          have hmeasure := measureReal_mono hsubset (measure_ne_top mu _)
          simpa [B, u, mul_assoc, mul_left_comm, mul_comm] using hmeasure
    _ ≤ ∑ b ∈ colors,
        mu.real
          (upperTailEvent
            (fun omega => ∑ i ∈ s.filter (fun j => color j = b), X i omega) B) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _b ∈ colors, Real.exp (-(u ^ sigma)) :=
      Finset.sum_le_sum fun b hb => htail b hb
    _ = q * Real.exp (-(u ^ sigma)) := by
      simp [q, nsmul_eq_mul]
    _ = q * Real.exp (-(q * t ^ sigma)) := by rw [hu_sigma]
    _ ≤ Real.exp (-(t ^ sigma)) :=
      finite_color_exponential_absorption hq (Real.one_le_rpow ht hsigma.le)

end

end Algsuperdiff.Section3.Provider.Stream
