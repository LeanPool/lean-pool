/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.Inflate
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.ColoredAverage
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.GeometricSums

/-!
# CubeMass

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weighted inflated-cube masses

This file records the bad-vertex count along one deterministic path, the
centered indicator of an inflated cube event, and the coloured average bound
for the scale-`L` weighted mass of the cubes that a path touches.
-/

namespace Algsuperdiff.Section5.Percolation

open MeasureTheory ProbabilityTheory
open HCPolySupport.IndependentSums
open scoped BigOperators

private theorem isBigO_gammaTwo_indicator_of_measureReal_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : Set Ω} {R : ℝ} (hR : 0 < R)
    (hE : P.real E ≤ Real.exp (-(R ^ 2))) :
    IsBigO P (gammaSigma 2) (E.indicator fun _ => (1 : ℝ)) R⁻¹ := by
  rw [isBigO_gammaSigma_iff]
  intro t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hRinv : 0 ≤ R⁻¹ := (inv_pos.mpr hR).le
  by_cases hcut : R⁻¹ * t < 1
  · have htail : absTailEvent (E.indicator fun _ => (1 : ℝ)) (R⁻¹ * t) = E := by
      ext ω
      by_cases hω : ω ∈ E
      · simp only [mem_absTailEvent, Set.indicator_of_mem hω, abs_one,
          hcut, hω]
      · have hnonneg : 0 ≤ R⁻¹ * t := mul_nonneg hRinv ht0
        simp only [mem_absTailEvent, Set.indicator_of_notMem hω, abs_zero,
          hω, iff_false]
        exact not_lt.mpr hnonneg
    rw [htail]
    have htR : t < R := by
      rw [inv_mul_eq_div, div_lt_one hR] at hcut
      exact hcut
    apply hE.trans
    rw [Real.exp_le_exp]
    have htSq : t ^ 2 ≤ R ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self ht0 (le_of_lt htR)
    simpa only [Real.rpow_two] using neg_le_neg htSq
  · have hthreshold : 1 ≤ R⁻¹ * t := le_of_not_gt hcut
    have htail : absTailEvent (E.indicator fun _ => (1 : ℝ)) (R⁻¹ * t) = ∅ := by
      ext ω
      by_cases hω : ω ∈ E
      · simp only [mem_absTailEvent, Set.indicator_of_mem hω, abs_one,
          Set.mem_empty_iff_false, iff_false]
        exact not_lt.mpr hthreshold
      · have hnonneg : 0 ≤ R⁻¹ * t := mul_nonneg hRinv ht0
        simp only [mem_absTailEvent, Set.indicator_of_notMem hω, abs_zero,
          Set.mem_empty_iff_false, iff_false]
        exact not_lt.mpr hnonneg
    rw [htail]
    simpa only [measureReal_empty] using (Real.exp_pos (-(t ^ 2))).le

private theorem isBigO_gammaTwo_centeredIndicator_of_measureReal_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Set Ω} {R : ℝ} (hR : 1 ≤ R)
    (hE : P.real E ≤ Real.exp (-(R ^ 2))) :
    IsBigO P (gammaSigma 2)
      (fun ω => E.indicator (fun _ => (1 : ℝ)) ω - P.real E)
      (2 * R⁻¹) := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hraw := isBigO_gammaTwo_indicator_of_measureReal_le hRpos hE
  rw [isBigO_gammaSigma_iff] at hraw ⊢
  intro t ht
  have hApos : 0 < R⁻¹ := inv_pos.mpr hRpos
  have hp0 : 0 ≤ P.real E := measureReal_nonneg
  have hpA : P.real E ≤ R⁻¹ := by
    apply hE.trans
    have hRexp : R ≤ Real.exp (R ^ 2) := by
      have hRleExpR : R ≤ Real.exp R := by
        have hexp := Real.add_one_le_exp R
        linarith only [hexp]
      have hRsq : R ≤ R ^ 2 := by
        calc
          R = R * 1 := by ring
          _ ≤ R * R := mul_le_mul_of_nonneg_left hR hRpos.le
          _ = R ^ 2 := by ring
      exact hRleExpR.trans (Real.exp_le_exp.mpr hRsq)
    rw [Real.exp_neg]
    exact inv_anti₀ hRpos hRexp
  have hAt : R⁻¹ ≤ R⁻¹ * t := le_mul_of_one_le_right hApos.le ht
  have hsub :
      absTailEvent
          (fun ω => E.indicator (fun _ => (1 : ℝ)) ω - P.real E)
          ((2 * R⁻¹) * t) ⊆
        absTailEvent (E.indicator fun _ => (1 : ℝ)) (R⁻¹ * t) := by
    intro ω hω
    rw [mem_absTailEvent] at hω ⊢
    have hpAbs : |P.real E| ≤ R⁻¹ := by
      rw [abs_of_nonneg hp0]
      exact hpA
    have hbound : |E.indicator (fun _ => (1 : ℝ)) ω - P.real E| ≤
        |E.indicator (fun _ => (1 : ℝ)) ω| + R⁻¹ := by
      exact (abs_sub _ _).trans
        (add_le_add_right hpAbs _)
    have htwo : (2 * R⁻¹) * t = R⁻¹ * t + R⁻¹ * t := by ring
    rw [htwo] at hω
    linarith only [hω, hbound, hAt]
  exact (measureReal_mono hsub (measure_ne_top P _)).trans (hraw ht)

/-- The number of distinct vertices of `Γ` at which the all-scale inflated bad
event occurs, represented as a real random variable. -/
noncomputable def inflatedVertexCount {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (Γ : List (Site d)) (ω : Ω) : ℝ :=
  ∑ z ∈ Γ.toFinset,
    (inflatedBadSet B z).indicator (fun _ => (1 : ℝ)) ω

/-- The scale-`L` inflated-cube count is the sum of the corresponding event
indicators over the touched cubes. -/
theorem coe_inflatedCubeCount_eq {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (L : ℕ) (Γ : List (Site d)) (ω : Ω) :
    (inflatedCubeCount B L Γ ω : ℝ) =
      ∑ v ∈ touchingCenters L Γ,
        (inflatedBadEvent B L v).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  unfold inflatedCubeCount
  generalize touchingCenters L Γ = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih =>
      by_cases hω : ω ∈ inflatedBadEvent B L v
      · have hvf : v ∉ s.filter (fun u => ω ∈ inflatedBadEvent B L u) := by
          intro hvf
          exact hv (Finset.mem_of_mem_filter v hvf)
        rw [Finset.filter_insert, ite_eq_left hω, Finset.card_insert_of_notMem hvf,
          Nat.cast_add, Nat.cast_one, ih, Finset.sum_insert hv,
          Set.indicator_of_mem hω]
        ac_rfl
      · rw [Finset.filter_insert, ite_eq_right hω, ih, Finset.sum_insert hv,
          Set.indicator_of_notMem hω, zero_add]

/-- The centered indicator of one inflated cube event. -/
noncomputable def centeredInflatedCubeIndicator
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : ℕ → Site d → Set Ω) (L : ℕ) (v : Site d) (ω : Ω) : ℝ :=
  (inflatedBadEvent B L v).indicator (fun _ => (1 : ℝ)) ω -
    P.real (inflatedBadEvent B L v)

private theorem iIndepFun_centeredInflatedCubeIndicator_of_sameColor
    {Ω : Type*} [MeasurableSpace Ω] {d L : ℕ} (P : Measure Ω)
    (B : ℕ → Site d → Set Ω) (hsep : SepIndep P B)
    (hB : ∀ L z, MeasurableSet (B L z)) (s : Finset (Site d))
    (b : Fin d → ZMod 3) (hcolor : ∀ v ∈ s, centerColor v = b) :
    ProbabilityTheory.iIndepFun
      (fun v : {v // v ∈ s} => centeredInflatedCubeIndicator P B L v.1) P := by
  have hraw := iIndepFun_inflatedIndicator_of_sameColor (L := L)
    P B hsep hB s b hcolor
  have hcomp := hraw.comp
    (g := fun i (x : ℝ) => x - P.real (inflatedBadEvent B L i.1))
    (fun _ => measurable_id.sub measurable_const)
  simpa only [centeredInflatedCubeIndicator, Function.comp_apply] using! hcomp

private theorem measurable_centeredInflatedCubeIndicator
    {Ω : Type*} [MeasurableSpace Ω] {d L : ℕ} (P : Measure Ω)
    {B : ℕ → Site d → Set Ω} (hB : ∀ L z, MeasurableSet (B L z))
    (v : Site d) : Measurable (centeredInflatedCubeIndicator P B L v) := by
  exact (measurable_const.indicator (measurableSet_inflatedBadEvent hB L v)).sub
    measurable_const

private theorem integral_centeredInflatedCubeIndicator
    {Ω : Type*} [MeasurableSpace Ω] {d L : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] {B : ℕ → Site d → Set Ω}
    (hB : ∀ L z, MeasurableSet (B L z)) (v : Site d) :
    ∫ ω, centeredInflatedCubeIndicator P B L v ω ∂P = 0 := by
  have hmeasEvent := measurableSet_inflatedBadEvent hB L v
  simp only [centeredInflatedCubeIndicator]
  rw [integral_sub]
  · have hint : ∫ ω, (inflatedBadEvent B L v).indicator
        (fun _ => (1 : ℝ)) ω ∂P = P.real (inflatedBadEvent B L v) := by
      simpa only [Pi.one_apply] using! integral_indicator_one hmeasEvent
    rw [hint]
    simp only [integral_const, smul_eq_mul, probReal_univ, one_mul, sub_self]
  · exact (integrable_indicator_iff hmeasEvent).mpr (integrable_const _).integrableOn
  · exact integrable_const _

/-- The centered inflated-cube indicators along one path satisfy the coloured
finite-range concentration estimate. -/
theorem isBigO_gammaTwo_average_centeredInflatedCubeIndicator
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → Site d → Set Ω) (hB : ∀ L z, MeasurableSet (B L z))
    (hsep : SepIndep P B) (L : ℕ) (Γ : List (Site d))
    (R : ℝ) (hR : 1 ≤ R)
    (htail : ∀ v ∈ touchingCenters L Γ,
      P.real (inflatedBadEvent B L v) ≤ Real.exp (-(R ^ 2))) :
    IsBigO P (gammaSigma 2)
      (fun ω => (((touchingCenters L Γ).card : ℕ) : ℝ)⁻¹ *
        ∑ v ∈ touchingCenters L Γ, centeredInflatedCubeIndicator P B L v ω)
      (gammaTriangleConst 2 *
        HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        (Real.sqrt (3 ^ d : ℝ) *
          (Real.sqrt (((touchingCenters L Γ).card : ℕ) : ℝ) /
            (((touchingCenters L Γ).card : ℕ) : ℝ))) *
        (2 * R⁻¹)) := by
  classical
  let s := touchingCenters L Γ
  let X : Site d → Ω → ℝ := fun v => centeredInflatedCubeIndicator P B L v
  have hindep : ∀ b ∈ s.image centerColor,
      ProbabilityTheory.iIndepFun
        (fun (i : {i // i ∈ s.filter (fun j => centerColor j = b)}) => X i.1) P := by
    intro b hb
    have hcentered := iIndepFun_centeredInflatedCubeIndicator_of_sameColor (L := L)
      P B hsep hB (s.filter fun j => centerColor j = b) b
      (fun v hv => (Finset.mem_filter.mp hv).2)
    simpa only [X] using hcentered
  have hmeas : ∀ v ∈ s, Measurable (X v) := by
    intro v _hv
    exact measurable_centeredInflatedCubeIndicator P hB v
  have hX : ∀ v ∈ s, IsBigO P (gammaSigma 2) (X v) (2 * R⁻¹) := by
    intro v hv
    simpa only [X, centeredInflatedCubeIndicator] using!
      isBigO_gammaTwo_centeredIndicator_of_measureReal_le hR (htail v hv)
  have hmean : ∀ v ∈ s, ∫ ω, X v ω ∂P = 0 := by
    intro v _hv
    simpa only [X] using integral_centeredInflatedCubeIndicator P hB v
  have hsqrt :
      ∑ b ∈ s.image centerColor,
          Real.sqrt ((s.filter (fun j => centerColor j = b)).card : ℝ) ≤
        Real.sqrt (3 ^ d : ℝ) * Real.sqrt (s.card : ℝ) := by
    have h := Algsuperdiff.Probability.sum_sqrt_class_card_le
      (κ := Fin d → ZMod 3) s centerColor
    simpa only [Fintype.card_pi, Fintype.card_fin, ZMod.card,
      Finset.prod_const, Finset.card_univ, Nat.cast_pow, Nat.cast_ofNat] using h
  have hK : 0 < 2 * R⁻¹ := mul_pos (by norm_num) (inv_pos.mpr (zero_lt_one.trans_le hR))
  exact Algsuperdiff.Probability.isBigO_gammaSigma_average_colored
    (P := P) (s := s) (c := centerColor) (X := X)
    (σ := 2) (K := 2 * R⁻¹) (colorCount := (3 ^ d : ℝ))
    (by norm_num) le_rfl hK hindep hmeas hX hmean hsqrt

/-- The centered scale-`L` contribution to the weighted cube mass. -/
noncomputable def centeredWeightedCubeMassAt
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : ℕ → Site d → Set Ω) (Γ : List (Site d)) (L : ℕ) (ω : Ω) : ℝ :=
  (3 : ℝ) ^ L *
    ((inflatedCubeCount B L Γ ω : ℝ) -
      ∑ v ∈ touchingCenters L Γ, P.real (inflatedBadEvent B L v))

/-- The colored estimate for one centered, scale-weighted cube count. -/
theorem isBigO_gammaTwo_centeredWeightedCubeMassAt
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → Site d → Set Ω) (hB : ∀ L z, MeasurableSet (B L z))
    (hsep : SepIndep P B) (L : ℕ) (Γ : List (Site d))
    (R : ℝ) (hR : 1 ≤ R)
    (htail : ∀ v ∈ touchingCenters L Γ,
      P.real (inflatedBadEvent B L v) ≤ Real.exp (-(R ^ 2))) :
    IsBigO P (gammaSigma 2) (centeredWeightedCubeMassAt P B Γ L)
      (((3 : ℝ) ^ L * (touchingCenters L Γ).card) *
        (gammaTriangleConst 2 *
          HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
          (Real.sqrt (3 ^ d : ℝ) *
            (Real.sqrt (((touchingCenters L Γ).card : ℕ) : ℝ) /
              (((touchingCenters L Γ).card : ℕ) : ℝ))) *
          (2 * R⁻¹))) := by
  classical
  have havg := isBigO_gammaTwo_average_centeredInflatedCubeIndicator
    P B hB hsep L Γ R hR htail
  have hmul := IsBigO.const_mul
    (c := (3 : ℝ) ^ L * (touchingCenters L Γ).card)
    (mul_nonneg (by positivity) (Nat.cast_nonneg (touchingCenters L Γ).card)) havg
  have hfun :
      (fun ω => ((3 : ℝ) ^ L * (touchingCenters L Γ).card) *
        ((((touchingCenters L Γ).card : ℕ) : ℝ)⁻¹ *
          ∑ v ∈ touchingCenters L Γ,
            centeredInflatedCubeIndicator P B L v ω)) =
        centeredWeightedCubeMassAt P B Γ L := by
    funext ω
    rw [centeredWeightedCubeMassAt, coe_inflatedCubeCount_eq,
      ← Finset.sum_sub_distrib]
    by_cases hs : (touchingCenters L Γ).Nonempty
    · have hcard : (((touchingCenters L Γ).card : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast hs.card_ne_zero
      simp only [centeredInflatedCubeIndicator]
      field_simp
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simp only [Finset.card_empty, Nat.cast_zero, inv_zero, mul_zero,
        Finset.sum_empty]
  simpa only [hfun] using hmul

end Algsuperdiff.Section5.Percolation
