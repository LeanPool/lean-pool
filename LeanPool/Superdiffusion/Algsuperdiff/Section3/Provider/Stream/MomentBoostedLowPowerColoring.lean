/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedLowPowerBernstein
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.ConcentrationAEMeasurable

/-!
# MomentBoostedLowPowerColoring

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Internal colored concave-power transport for the low-power route

This module transports the raw quadratic-plus-linear Bernstein tail through a
finite range coloring and then through a concave power `r` in `[1/2, 1]`.
Keeping both regimes before the power is exactly what preserves the
`card^{-1/2}` gain at `r = p / 2`.

The proof is internal probability infrastructure.  Its finite-family inputs
are discharged by the stream-specific partition construction; it is not a
source-facing substitute for the large-cube theorem.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory Filter
open HCPolySupport HCPolySupport.IndependentSums
open scoped BigOperators

noncomputable section

/-- A dimensionless color factor for the two-regime low-power transport. -/
noncomputable def momentBoostedLowPowerColorConst (q : ℝ) : ℝ :=
  momentBoostedBernsteinQuadratic * momentBoostedBernsteinLinear * q * (q + 2)

theorem momentBoostedBernsteinQuadratic_one_le :
    1 ≤ momentBoostedBernsteinQuadratic := by
  unfold momentBoostedBernsteinQuadratic
  have hbase := one_le_momentBoostedBernsteinBase
  have hsq : (1 : ℝ) ≤ momentBoostedBernsteinBase ^ (2 : ℕ) := by nlinarith
  nlinarith

theorem momentBoostedBernsteinLinear_one_le :
    1 ≤ momentBoostedBernsteinLinear := by
  unfold momentBoostedBernsteinLinear
  nlinarith [one_le_momentBoostedBernsteinBase]

theorem momentBoostedLowPowerColorConst_pos {q : ℝ} (hq : 0 < q) :
    0 < momentBoostedLowPowerColorConst q := by
  unfold momentBoostedLowPowerColorConst
  exact mul_pos
    (mul_pos (mul_pos momentBoostedBernsteinQuadratic_pos
      momentBoostedBernsteinLinear_pos) hq)
    (by linarith)

theorem one_le_momentBoostedLowPowerColorConst {q : ℝ} (hq : 1 ≤ q) :
    1 ≤ momentBoostedLowPowerColorConst q := by
  unfold momentBoostedLowPowerColorConst
  have hq2 : 1 ≤ q + 2 := by linarith
  have hDL : 1 ≤ momentBoostedBernsteinQuadratic * momentBoostedBernsteinLinear :=
    one_le_mul_of_one_le_of_one_le momentBoostedBernsteinQuadratic_one_le
      momentBoostedBernsteinLinear_one_le
  have hqprod : 1 ≤ q * (q + 2) := one_le_mul_of_one_le_of_one_le hq hq2
  calc
    (1 : ℝ) ≤
        (momentBoostedBernsteinQuadratic * momentBoostedBernsteinLinear) *
          (q * (q + 2)) := one_le_mul_of_one_le_of_one_le hDL hqprod
    _ = momentBoostedBernsteinQuadratic * momentBoostedBernsteinLinear * q *
          (q + 2) := by ring

theorem momentBoostedLowPowerColorConst_mono {q Q : ℝ}
    (hq : 0 ≤ q) (hqQ : q ≤ Q) :
    momentBoostedLowPowerColorConst q ≤ momentBoostedLowPowerColorConst Q := by
  have hQ : 0 ≤ Q := hq.trans hqQ
  have hprod : q * (q + 2) ≤ Q * (Q + 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqQ) (by linarith : 0 ≤ q + Q + 2)]
  unfold momentBoostedLowPowerColorConst
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod
    (mul_nonneg momentBoostedBernsteinQuadratic_pos.le
      momentBoostedBernsteinLinear_pos.le)

private theorem rpow_le_add_rpow_sub_one {x sigma : ℝ}
    (hx : 0 ≤ x) (hsigma : 1 ≤ sigma) :
    x ^ sigma ≤ (1 + x) ^ sigma - 1 := by
  have hpow : (1 : ℝ) ^ sigma + x ^ sigma ≤ (1 + x) ^ sigma :=
    Real.add_rpow_le_rpow_add zero_le_one hx hsigma
  rw [Real.one_rpow] at hpow
  linarith

private theorem lowPower_linear_scale_le
    {N C t sigma : ℝ}
    (hN : 1 ≤ N) (hC : 1 ≤ C) (ht : 0 ≤ t)
    (hsigma_one : 1 ≤ sigma) (hsigma_two : sigma ≤ 2) :
    C * t ^ sigma ≤ N * (C * t / Real.sqrt N) ^ sigma := by
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hsqrtN : 0 < Real.sqrt N :=
    Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hN)
  have hsqrtN_one : 1 ≤ Real.sqrt N := (Real.one_le_sqrt).2 hN
  have hsqrt_pow_le : (Real.sqrt N) ^ sigma ≤ N := by
    calc
      (Real.sqrt N) ^ sigma ≤ (Real.sqrt N) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hsqrtN_one hsigma_two
      _ = (Real.sqrt N) ^ (2 : ℕ) := Real.rpow_two _
      _ = N := Real.sq_sqrt hN0
  have hCpow : C ≤ C ^ sigma := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hC hsigma_one
  have hratio : 1 ≤ N / (Real.sqrt N) ^ sigma := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hsqrtN _)).2
    simpa only [one_mul] using hsqrt_pow_le
  have hrewrite :
      (C * t / Real.sqrt N) ^ sigma =
        C ^ sigma * t ^ sigma / (Real.sqrt N) ^ sigma := by
    rw [Real.div_rpow (mul_nonneg hC0 ht) hsqrtN.le, Real.mul_rpow hC0 ht]
  rw [hrewrite]
  calc
    C * t ^ sigma ≤ C ^ sigma * t ^ sigma :=
      mul_le_mul_of_nonneg_right hCpow (Real.rpow_nonneg ht _)
    _ ≤ (N / (Real.sqrt N) ^ sigma) * (C ^ sigma * t ^ sigma) :=
      le_mul_of_one_le_left
        (mul_nonneg (Real.rpow_nonneg hC0 _) (Real.rpow_nonneg ht _)) hratio
    _ = N * (C ^ sigma * t ^ sigma / (Real.sqrt N) ^ sigma) := by ring

private theorem two_mul_color_exp_le {q z : ℝ} (hq : 1 ≤ q) (hz : 1 ≤ z) :
    2 * q * Real.exp (-((q + 2) * z)) ≤ Real.exp (-z) := by
  have hqexp : 2 * q ≤ Real.exp ((q + 1) * z) := by
    calc
      2 * q ≤ Real.exp q := Real.two_mul_le_exp
      _ ≤ Real.exp ((q + 1) * z) := Real.exp_le_exp.2 (by
        calc
          q = q * 1 := by ring
          _ ≤ q * z := mul_le_mul_of_nonneg_left hz (zero_le_one.trans hq)
          _ ≤ (q + 1) * z :=
            mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans hz))
  calc
    2 * q * Real.exp (-((q + 2) * z)) ≤
        Real.exp ((q + 1) * z) * Real.exp (-((q + 2) * z)) :=
      mul_le_mul_of_nonneg_right hqexp (Real.exp_pos _).le
    _ = Real.exp (-z) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- A finite-range coloring preserves the raw Bernstein two-regime tail. -/
theorem measureReal_upperTailEvent_finset_sum_le_momentBoostedColoredBernstein
    {Omega iota kappa : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] [DecidableEq kappa]
    {X : iota → Omega → ℝ} {s : Finset iota} {color : iota → kappa} {a : ℝ}
    (h_indep : ∀ b ∈ s.image color,
      iIndepFun (fun i : {i // i ∈ s.filter (fun j => color j = b)} => X i.1) mu)
    (h_meas : ∀ i, Measurable (X i)) (ha : 0 ≤ a)
    (hX : ∀ i ∈ s, IsBigO mu (gammaSigma 1) (X i) 1)
    (hmean : ∀ i ∈ s, ∫ omega, X i omega ∂mu = 0) :
    mu.real (upperTailEvent (fun omega => ∑ i ∈ s, X i omega)
      (((s.image color).card : ℝ) * a)) ≤
      ((s.image color).card : ℝ) *
        (Real.exp (-(a ^ (2 : ℕ)) /
          (momentBoostedBernsteinQuadratic * (s.card : ℝ))) +
          Real.exp (-a / momentBoostedBernsteinLinear)) := by
  classical
  let colors := s.image color
  let Y : kappa → Omega → ℝ := fun b omega =>
    ∑ i ∈ s.filter (fun j => color j = b), X i omega
  have hpartition : ∀ omega, ∑ b ∈ colors, Y b omega = ∑ i ∈ s, X i omega := by
    intro omega
    exact Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_image_of_mem color hi) (fun i => X i omega)
  have hclass : ∀ b ∈ colors,
      mu.real (upperTailEvent (Y b) a) ≤
        Real.exp (-(a ^ (2 : ℕ)) /
          (momentBoostedBernsteinQuadratic * (s.card : ℝ))) +
          Real.exp (-a / momentBoostedBernsteinLinear) := by
    intro b hb
    let sb := s.filter (fun j => color j = b)
    have hsb : sb.Nonempty := by
      obtain ⟨i, hi, hci⟩ := Finset.mem_image.mp hb
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
    have hraw := measureReal_upperTailEvent_finset_sum_le_momentBoostedBernstein
      (mu := mu) (X := fun i : {i // i ∈ sb} => X i.1) (s := sb.attach) (a := a)
      (h_indep b hb) (fun i => h_meas i.1)
      (Finset.attach_nonempty_iff.mpr hsb) ha
      (fun i _ => hX i.1 (Finset.mem_of_mem_filter i.1 i.2))
      (fun i _ => hmean i.1 (Finset.mem_of_mem_filter i.1 i.2))
    have hfun : (fun omega => ∑ i ∈ sb.attach, X i.1 omega) = Y b := by
      funext omega
      simpa only [Y, sb] using Finset.sum_attach (s := sb) (f := fun i => X i omega)
    have hcard : ((sb.attach.card : ℕ) : ℝ) ≤ (s.card : ℝ) := by
      rw [Finset.card_attach]
      exact_mod_cast Finset.card_filter_le (s := s) (p := fun j => color j = b)
    have hcard_pos : 0 < ((sb.attach.card : ℕ) : ℝ) := by
      exact_mod_cast (Finset.attach_nonempty_iff.mpr hsb).card_pos
    have hfrac : a ^ (2 : ℕ) /
        (momentBoostedBernsteinQuadratic * (s.card : ℝ)) ≤
        a ^ (2 : ℕ) /
          (momentBoostedBernsteinQuadratic * ((sb.attach.card : ℕ) : ℝ)) := by
      exact div_le_div_of_nonneg_left (sq_nonneg a)
        (mul_pos momentBoostedBernsteinQuadratic_pos hcard_pos)
        (mul_le_mul_of_nonneg_left hcard momentBoostedBernsteinQuadratic_pos.le)
    have hgaussian :
        Real.exp (-(a ^ (2 : ℕ)) /
          (momentBoostedBernsteinQuadratic * ((sb.attach.card : ℕ) : ℝ))) ≤
          Real.exp (-(a ^ (2 : ℕ)) /
            (momentBoostedBernsteinQuadratic * (s.card : ℝ))) := by
      apply Real.exp_le_exp.2
      simpa only [neg_div] using neg_le_neg hfrac
    rw [hfun] at hraw
    exact hraw.trans (add_le_add hgaussian le_rfl)
  have hsubset :
      upperTailEvent (fun omega => ∑ i ∈ s, X i omega)
          (((s.image color).card : ℝ) * a) ⊆
        ⋃ b ∈ colors, upperTailEvent (Y b) a := by
    intro omega homega
    by_contra hnot
    have hall : ∀ b ∈ colors, Y b omega ≤ a := by
      intro b hb
      by_contra hba
      have hmem : omega ∈ upperTailEvent (Y b) a := lt_of_not_ge hba
      exact hnot (Set.mem_iUnion.2 ⟨b, Set.mem_iUnion.2 ⟨hb, hmem⟩⟩)
    have hsum : ∑ b ∈ colors, Y b omega ≤ ∑ _b ∈ colors, a :=
      Finset.sum_le_sum hall
    have hle : ∑ i ∈ s, X i omega ≤ ((s.image color).card : ℝ) * a := by
      rw [← hpartition omega]
      calc
        ∑ b ∈ colors, Y b omega ≤ ∑ _b ∈ colors, a := hsum
        _ = ((s.image color).card : ℝ) * a := by
          simp only [Finset.sum_const, nsmul_eq_mul, colors]
    exact (not_lt_of_ge hle) homega
  calc
    mu.real (upperTailEvent (fun omega => ∑ i ∈ s, X i omega)
        (((s.image color).card : ℝ) * a)) ≤
        mu.real (⋃ b ∈ colors, upperTailEvent (Y b) a) :=
      measureReal_mono hsubset (measure_ne_top mu _)
    _ ≤ ∑ b ∈ colors, mu.real (upperTailEvent (Y b) a) :=
      measureReal_biUnion_finset_le colors fun b => upperTailEvent (Y b) a
    _ ≤ ∑ _b ∈ colors,
        (Real.exp (-(a ^ (2 : ℕ)) /
          (momentBoostedBernsteinQuadratic * (s.card : ℝ))) +
          Real.exp (-a / momentBoostedBernsteinLinear)) := Finset.sum_le_sum hclass
    _ = ((s.image color).card : ℝ) *
        (Real.exp (-(a ^ (2 : ℕ)) /
          (momentBoostedBernsteinQuadratic * (s.card : ℝ))) +
          Real.exp (-a / momentBoostedBernsteinLinear)) := by
      simp only [Finset.sum_const, nsmul_eq_mul, colors]

private theorem lowPower_colored_bernstein_tail_le
    {N q sigma t a : ℝ}
    (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hsigma_one : 1 ≤ sigma) (hsigma_two : sigma ≤ 2) (ht : 1 ≤ t)
    (ha_gaussian : momentBoostedLowPowerColorConst q * Real.sqrt N * t / q ≤ a)
    (ha_linear : momentBoostedLowPowerColorConst q * t ^ sigma / q ≤ a) :
    q * (Real.exp (-(a ^ (2 : ℕ)) /
      (momentBoostedBernsteinQuadratic * N)) +
      Real.exp (-a / momentBoostedBernsteinLinear)) ≤ Real.exp (-(t ^ sigma)) := by
  let C := momentBoostedLowPowerColorConst q
  let D := momentBoostedBernsteinQuadratic
  let L := momentBoostedBernsteinLinear
  let z := t ^ sigma
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hz_one : 1 ≤ z := by
    dsimp [z]
    exact Real.one_le_rpow ht (zero_le_one.trans hsigma_one)
  have htz : z ≤ t ^ (2 : ℕ) := by
    dsimp [z]
    calc
      t ^ sigma ≤ t ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht hsigma_two
      _ = t ^ (2 : ℕ) := Real.rpow_two _
  have hD : 1 ≤ D := by simpa [D] using momentBoostedBernsteinQuadratic_one_le
  have hL : 1 ≤ L := by simpa [L] using momentBoostedBernsteinLinear_one_le
  have hC : 1 ≤ C := by
    simpa [C] using one_le_momentBoostedLowPowerColorConst hq
  have hquad_coeff : q + 2 ≤ C ^ (2 : ℕ) / (D * q ^ (2 : ℕ)) := by
    have hden : 0 < D * q ^ (2 : ℕ) := by positivity
    apply (le_div_iff₀ hden).2
    change (q + 2) * (D * q ^ (2 : ℕ)) ≤
      (D * L * q * (q + 2)) ^ (2 : ℕ)
    have hLsq : 1 ≤ L ^ (2 : ℕ) := by nlinarith [sq_nonneg (L - 1)]
    have hDLsq : 1 ≤ D * L ^ (2 : ℕ) :=
      one_le_mul_of_one_le_of_one_le hD hLsq
    have hfactor : 1 ≤ D * L ^ (2 : ℕ) * (q + 2) :=
      one_le_mul_of_one_le_of_one_le hDLsq (by linarith)
    have hleft : 0 ≤ (q + 2) * (D * q ^ (2 : ℕ)) := by positivity
    calc
      (q + 2) * (D * q ^ (2 : ℕ)) ≤
          ((q + 2) * (D * q ^ (2 : ℕ))) *
            (D * L ^ (2 : ℕ) * (q + 2)) :=
        le_mul_of_one_le_right hleft hfactor
      _ = (D * L * q * (q + 2)) ^ (2 : ℕ) := by ring
  have hgaussian_base : 0 ≤ C * Real.sqrt N * t / q := by positivity
  have hsquares : (C * Real.sqrt N * t / q) ^ (2 : ℕ) ≤ a ^ (2 : ℕ) :=
    pow_le_pow_left₀ hgaussian_base ha_gaussian 2
  have hnormalized_square :
      (C * Real.sqrt N * t / q) ^ (2 : ℕ) / (D * N) =
        (C ^ (2 : ℕ) / (D * q ^ (2 : ℕ))) * t ^ (2 : ℕ) := by
    conv_lhs => rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (zero_le_one.trans hN)]
    field_simp [hN0.ne', hq0.ne']
  have hquad : (q + 2) * z ≤ a ^ (2 : ℕ) / (D * N) := by
    calc
      (q + 2) * z ≤ (q + 2) * t ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left htz (by linarith)
      _ ≤ (C ^ (2 : ℕ) / (D * q ^ (2 : ℕ))) * t ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hquad_coeff (sq_nonneg t)
      _ = (C * Real.sqrt N * t / q) ^ (2 : ℕ) / (D * N) := hnormalized_square.symm
      _ ≤ a ^ (2 : ℕ) / (D * N) :=
        div_le_div_of_nonneg_right hsquares (by positivity)
  have hlinear_coeff : q + 2 ≤ C / (L * q) := by
    have hden : 0 < L * q := by positivity
    apply (le_div_iff₀ hden).2
    change (q + 2) * (L * q) ≤ D * L * q * (q + 2)
    have hleft : 0 ≤ (q + 2) * (L * q) := by positivity
    calc
      (q + 2) * (L * q) ≤ ((q + 2) * (L * q)) * D :=
        le_mul_of_one_le_right hleft hD
      _ = D * L * q * (q + 2) := by ring
  have hlinear : (q + 2) * z ≤ a / L := by
    calc
      (q + 2) * z ≤ (C / (L * q)) * z :=
        mul_le_mul_of_nonneg_right hlinear_coeff (Real.rpow_nonneg ht0 _)
      _ = (C * z / q) / L := by ring
      _ ≤ a / L := by
        dsimp only [C, z] at ha_linear ⊢
        exact div_le_div_of_nonneg_right ha_linear (by positivity)
  have hgauss_exp : Real.exp (-(a ^ (2 : ℕ)) / (D * N)) ≤
      Real.exp (-((q + 2) * z)) := by
    apply Real.exp_le_exp.2
    simpa only [neg_div] using neg_le_neg hquad
  have hlin_exp : Real.exp (-a / L) ≤ Real.exp (-((q + 2) * z)) := by
    apply Real.exp_le_exp.2
    simpa only [neg_div] using neg_le_neg hlinear
  calc
    q * (Real.exp (-(a ^ (2 : ℕ)) / (D * N)) + Real.exp (-a / L)) ≤
        q * (Real.exp (-((q + 2) * z)) + Real.exp (-((q + 2) * z))) :=
      mul_le_mul_of_nonneg_left (add_le_add hgauss_exp hlin_exp) (zero_le_one.trans hq)
    _ = 2 * q * Real.exp (-((q + 2) * z)) := by ring
    _ ≤ Real.exp (-z) := two_mul_color_exp_le hq hz_one
    _ = Real.exp (-(t ^ sigma)) := by rfl

/--
**Concave-power endpoint with raw colored Bernstein input.**  This is the
deterministic two-regime transport later instantiated with `r = p / 2`, the
scale-two descendant mass `Y`, and the scale-`p` mass `Z`.
-/
theorem sub_rpow_isBigOWith_gammaSigma_of_momentBoostedColoredBernstein
    {Omega iota kappa : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] [DecidableEq kappa]
    {X : iota → Omega → ℝ} {s : Finset iota} {color : iota → kappa}
    {Y Z : Omega → ℝ} {r H K : ℝ}
    (hs : s.Nonempty)
    (h_indep : ∀ b ∈ s.image color,
      iIndepFun (fun i : {i // i ∈ s.filter (fun j => color j = b)} => X i.1) mu)
    (h_meas : ∀ i, Measurable (X i))
    (hX : ∀ i ∈ s, IsBigO mu (gammaSigma 1) (X i) 1)
    (hmean : ∀ i ∈ s, ∫ omega, X i omega ∂mu = 0)
    (hr_half : (1 : ℝ) / 2 ≤ r) (hr_one : r ≤ 1)
    (hH : 0 < H) (hK : 0 < K) (hKH : K ≤ H)
    (hY_nonneg : 0 ≤ᵐ[mu] Y)
    (hZY : Z ≤ᵐ[mu] fun omega => (Y omega) ^ r)
    (hYsum : Y ≤ᵐ[mu] fun omega =>
      H + (K / (s.card : ℝ)) * ∑ i ∈ s, X i omega) :
    IsBigOWith mu (gammaSigma r⁻¹) (fun omega => Z omega - H ^ r)
      (momentBoostedLowPowerColorConst ((s.image color).card : ℝ) * H ^ r /
        Real.sqrt (s.card : ℝ)) := by
  classical
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  let N : ℝ := s.card
  let q : ℝ := (s.image color).card
  let C : ℝ := momentBoostedLowPowerColorConst q
  let sigma : ℝ := r⁻¹
  let x : ℝ := C * t / Real.sqrt N
  let delta : ℝ := (1 + x) ^ sigma - 1
  let a : ℝ := N * delta / q
  let z : ℝ := t ^ sigma
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hr_half
  have hsigma_one : 1 ≤ sigma := by
    dsimp [sigma]
    exact (one_le_inv₀ hr).2 hr_one
  have hsigma_two : sigma ≤ 2 := by
    dsimp [sigma]
    have hraw := (inv_le_inv₀ hr (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).2 hr_half
    norm_num at hraw ⊢
    exact hraw
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hs.card_pos
  have hN_one : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast Nat.succ_le_of_lt hs.card_pos
  have hcolors : (s.image color).Nonempty := hs.image color
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast hcolors.card_pos
  have hq_one : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.succ_le_of_lt hcolors.card_pos
  have hC_one : 1 ≤ C := by
    simpa [C] using one_le_momentBoostedLowPowerColorConst hq_one
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hx0 : 0 ≤ x := by positivity
  have hone_x : 1 ≤ 1 + x := by linarith
  have hdelta_x : x ≤ delta := by
    dsimp [delta]
    have hpow := Real.self_le_rpow_of_one_le hone_x hsigma_one
    linarith
  have hdelta_xpow : x ^ sigma ≤ delta := by
    dsimp [delta]
    exact rpow_le_add_rpow_sub_one hx0 hsigma_one
  have hdelta0 : 0 ≤ delta := hx0.trans hdelta_x
  have ha0 : 0 ≤ a := by positivity
  have hsigma_r : sigma * r = 1 := by
    dsimp [sigma]
    field_simp [hr.ne']
  have hscale :
      (momentBoostedLowPowerColorConst ((s.image color).card : ℝ) * H ^ r /
          Real.sqrt (s.card : ℝ)) * t = H ^ r * x := by
    dsimp [C, q, N, x]
    ring
  have htarget_subset :
      upperTailEvent (fun omega => Z omega - H ^ r)
          ((momentBoostedLowPowerColorConst ((s.image color).card : ℝ) * H ^ r /
            Real.sqrt (s.card : ℝ)) * t) ≤ᵐ[mu]
        upperTailEvent (fun omega => ∑ i ∈ s, X i omega) (q * a) := by
    filter_upwards [hY_nonneg, hZY, hYsum] with omega hY0 hZYomega hYsumomega homega
    have hZlarge : H ^ r * (1 + x) < Z omega := by
      rw [hscale] at homega
      calc
        H ^ r * (1 + x) = H ^ r * x + H ^ r := by ring
        _ < Z omega := lt_sub_iff_add_lt.mp homega
    have hpow_large : H ^ r * (1 + x) < (Y omega) ^ r :=
      lt_of_lt_of_le hZlarge hZYomega
    have hbase0 : 0 ≤ H * (1 + x) ^ sigma := by positivity
    have hbase_pow : (H * (1 + x) ^ sigma) ^ r = H ^ r * (1 + x) := by
      rw [Real.mul_rpow hH.le (Real.rpow_nonneg (by linarith) _),
        ← Real.rpow_mul (by linarith : 0 ≤ 1 + x), hsigma_r, Real.rpow_one]
    have hbase_ltY : H * (1 + x) ^ sigma < Y omega := by
      apply (Real.rpow_lt_rpow_iff hbase0 hY0 hr).1
      simpa only [hbase_pow] using hpow_large
    have hHdelta : H * delta < (K / N) * ∑ i ∈ s, X i omega := by
      calc
        H * delta = H * (1 + x) ^ sigma - H := by
          dsimp [delta]
          ring
        _ < Y omega - H := sub_lt_sub_right hbase_ltY H
        _ ≤ (H + (K / N) * ∑ i ∈ s, X i omega) - H :=
          sub_le_sub_right hYsumomega H
        _ = (K / N) * ∑ i ∈ s, X i omega := by ring
    have hKdelta : K * delta < (K / N) * ∑ i ∈ s, X i omega :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hKH hdelta0) hHdelta
    have hdelta_avg : delta < (∑ i ∈ s, X i omega) / N := by
      have hrewrite : (K / N) * ∑ i ∈ s, X i omega =
          K * ((∑ i ∈ s, X i omega) / N) := by ring
      rw [hrewrite] at hKdelta
      exact lt_of_mul_lt_mul_left hKdelta hK.le
    have hsum_large : N * delta < ∑ i ∈ s, X i omega := by
      simpa [mul_comm] using (lt_div_iff₀ hN).mp hdelta_avg
    have hqa : q * a = N * delta := by
      dsimp only [a]
      field_simp [hq.ne']
    rw [hqa]
    exact hsum_large
  have htail := measureReal_upperTailEvent_finset_sum_le_momentBoostedColoredBernstein
    (mu := mu) (X := X) (s := s) (color := color) (a := a)
    h_indep h_meas ha0 hX hmean
  have hmeasure :
      mu.real (upperTailEvent (fun omega => Z omega - H ^ r)
        ((momentBoostedLowPowerColorConst ((s.image color).card : ℝ) * H ^ r /
          Real.sqrt (s.card : ℝ)) * t)) ≤
        mu.real (upperTailEvent (fun omega => ∑ i ∈ s, X i omega) (q * a)) :=
    Book.Ch04.measureReal_mono_ae htarget_subset
  have ha_gaussian : C * Real.sqrt N * t / q ≤ a := by
    have hNdelta : N * x ≤ N * delta :=
      mul_le_mul_of_nonneg_left hdelta_x hN.le
    have hNx : N * x = C * Real.sqrt N * t := by
      dsimp only [x]
      calc
        N * (C * t / Real.sqrt N) = C * t * (N / Real.sqrt N) := by ring
        _ = C * t * Real.sqrt N := by rw [Real.div_sqrt]
        _ = C * Real.sqrt N * t := by ring
    dsimp only [a]
    rw [hNx] at hNdelta
    exact div_le_div_of_nonneg_right hNdelta hq.le
  have hNxpow : C * z ≤ N * x ^ sigma := by
    simpa only [x, z] using
      lowPower_linear_scale_le hN_one hC_one ht0 hsigma_one hsigma_two
  have hNdelta_pow : N * x ^ sigma ≤ N * delta :=
    mul_le_mul_of_nonneg_left hdelta_xpow hN.le
  have ha_linear : C * z / q ≤ a := by
    dsimp only [a]
    exact div_le_div_of_nonneg_right (hNxpow.trans hNdelta_pow) hq.le
  have htail_decay :
      q * (Real.exp (-(a ^ (2 : ℕ)) /
        (momentBoostedBernsteinQuadratic * N)) +
        Real.exp (-a / momentBoostedBernsteinLinear)) ≤ Real.exp (-z) := by
    simpa only [C, z] using lowPower_colored_bernstein_tail_le
      hN_one hq_one hsigma_one hsigma_two ht
      (by simpa only [C] using ha_gaussian)
      (by simpa only [C, z] using ha_linear)
  calc
    mu.real (upperTailEvent (fun omega => Z omega - H ^ r)
        ((momentBoostedLowPowerColorConst ((s.image color).card : ℝ) * H ^ r /
          Real.sqrt (s.card : ℝ)) * t)) ≤
        mu.real (upperTailEvent (fun omega => ∑ i ∈ s, X i omega) (q * a)) := hmeasure
    _ ≤ q * (Real.exp (-(a ^ (2 : ℕ)) /
        (momentBoostedBernsteinQuadratic * N)) +
        Real.exp (-a / momentBoostedBernsteinLinear)) := by
      simpa only [q, N] using htail
    _ ≤ Real.exp (-z) := htail_decay
    _ = Real.exp (-(t ^ r⁻¹)) := by rfl

end

end Algsuperdiff.Section3.Provider.Stream
