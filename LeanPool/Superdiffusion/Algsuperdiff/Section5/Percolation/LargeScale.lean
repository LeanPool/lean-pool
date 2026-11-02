/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.SmallScale

/-!
# LargeScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Large scales and the fixed-path weighted-cube bound

This file bounds the probability that an inflated cube of scale larger than the
path length occurs on the path, and combines that with the small-scale bound
into the fixed-path estimate for the weighted-cube event.
-/

namespace Algsuperdiff.Section5.Percolation

open MeasureTheory ProbabilityTheory
open HCPolySupport.IndependentSums
open scoped BigOperators

/-- The event that an occurring inflated cube touches `Γ` at scale `L`. -/
noncomputable def scaleOccurrenceEvent {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (Γ : List (Site d)) (L : ℕ) : Set Ω :=
  {ω | 0 < inflatedCubeCount B L Γ ω}

/-- The union of occurring touched-cube events over scales larger than the
path length. -/
noncomputable def largeScaleOccurrenceEvent {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (Γ : List (Site d)) : Set Ω :=
  ⋃ L : ℕ, if Γ.length < 3 ^ L then scaleOccurrenceEvent B Γ L else ∅

private theorem weightedCubeMassOn_le_small_of_not_mem_largeScale
    {Ω : Type*} {d : ℕ} (B : ℕ → Site d → Set Ω)
    (Γ : List (Site d)) (ω : Ω)
    (hω : ω ∉ largeScaleOccurrenceEvent B Γ) (scales : Finset ℕ) :
    weightedCubeMassOn B Γ scales ω ≤
      weightedCubeMassOn B Γ (smallScales Γ) ω := by
  classical
  let s := scales.filter fun L => 3 ^ L ≤ Γ.length
  have hsum :
      ∑ L ∈ s, (3 : ℝ) ^ L * inflatedCubeCount B L Γ ω =
        ∑ L ∈ scales, (3 : ℝ) ^ L * inflatedCubeCount B L Γ ω := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro L hL hLs
    have hlarge : Γ.length < 3 ^ L := by
      have hnotSmall : ¬3 ^ L ≤ Γ.length := by
        intro hsmall
        exact hLs (Finset.mem_filter.mpr ⟨hL, hsmall⟩)
      omega
    have hnotOccurrence : ω ∉ scaleOccurrenceEvent B Γ L := by
      intro hoccurs
      apply hω
      rw [largeScaleOccurrenceEvent, Set.mem_iUnion]
      refine ⟨L, ?_⟩
      rw [ite_eq_left hlarge]
      exact hoccurs
    have hcount : inflatedCubeCount B L Γ ω = 0 := by
      apply Nat.eq_zero_of_not_pos
      exact hnotOccurrence
    rw [hcount, Nat.cast_zero, mul_zero]
  rw [weightedCubeMassOn, ← hsum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro L hL
    rw [mem_smallScales_iff]
    exact (Finset.mem_filter.mp hL).2
  · intro L _hsmall _hnot
    exact mul_nonneg (by positivity) (Nat.cast_nonneg _)

/-- A weighted partial sum can exceed a threshold only through a large-scale
occurrence or through the canonical finite sum over small scales. -/
theorem weightedCubeEvent_subset_largeScale_union_small
    {Ω : Type*} {d : ℕ} (B : ℕ → Site d → Set Ω)
    (Γ : List (Site d)) (r : ℝ) :
    weightedCubeEvent B Γ r ⊆
      largeScaleOccurrenceEvent B Γ ∪
        {ω | r < weightedCubeMassOn B Γ (smallScales Γ) ω} := by
  intro ω hω
  by_cases hlarge : ω ∈ largeScaleOccurrenceEvent B Γ
  · exact Or.inl hlarge
  · right
    obtain ⟨scales, hmass⟩ := hω
    exact hmass.trans_le
      (weightedCubeMassOn_le_small_of_not_mem_largeScale B Γ ω hlarge scales)

private theorem scaleOccurrenceEvent_eq_biUnion {Ω : Type*} {d L : ℕ}
    (B : ℕ → Site d → Set Ω) (Γ : List (Site d)) :
    scaleOccurrenceEvent B Γ L =
      ⋃ v ∈ touchingCenters L Γ, inflatedBadEvent B L v := by
  classical
  ext ω
  simp only [scaleOccurrenceEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro h
    rw [inflatedCubeCount, Finset.card_pos] at h
    obtain ⟨v, hv⟩ := h
    exact ⟨v, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
  · rintro ⟨v, hv, hω⟩
    rw [inflatedCubeCount, Finset.card_pos]
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hω⟩⟩

private theorem exp_large_scale_tail_le {a T : ℝ} (ha : 1 ≤ a) (hT : 2 ≤ T)
    {n L : ℕ} (hlarge : n < 3 ^ L) :
    Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L) / 2)) ≤
      Real.exp (-(T ^ 2 * n / 4)) * (3 : ℝ) ^ (-(L : ℝ)) := by
  have hlog : Real.log 3 ≤ 2 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)).trans
      (by norm_num)
  have hqNatA : (3 : ℝ) ^ L ≤ (3 : ℝ) ^ (a * L) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg L))
  have hqA : (n : ℝ) ≤ (3 : ℝ) ^ (a * L) := by
    have hnq : (n : ℝ) ≤ (3 : ℝ) ^ L := by exact_mod_cast hlarge.le
    exact hnq.trans hqNatA
  have hTsq : (4 : ℝ) ≤ T ^ 2 := by
    have ht := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) hT
    calc
      (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ T * T := ht
      _ = T ^ 2 := by ring
  have hlogL : (L : ℝ) * Real.log 3 ≤ (3 : ℝ) ^ (a * L) := by
    have hLq : (2 : ℝ) * L ≤ (3 : ℝ) ^ L := by
      exact_mod_cast two_mul_le_three_pow L
    calc
      (L : ℝ) * Real.log 3 ≤ L * 2 :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg L)
      _ = 2 * L := by ring
      _ ≤ (3 : ℝ) ^ L := hLq
      _ ≤ (3 : ℝ) ^ (a * L) := hqNatA
  have hfirst : T ^ 2 * n / 4 ≤
      T ^ 2 * (3 : ℝ) ^ (a * L) / 4 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqA (sq_nonneg T)) (by norm_num)
  have hsecond : (L : ℝ) * Real.log 3 ≤
      T ^ 2 * (3 : ℝ) ^ (a * L) / 4 := by
    calc
      (L : ℝ) * Real.log 3 ≤ (3 : ℝ) ^ (a * L) := hlogL
      _ = 4 * (3 : ℝ) ^ (a * L) / 4 := by ring
      _ ≤ T ^ 2 * (3 : ℝ) ^ (a * L) / 4 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hTsq (by positivity)
  have hexponent : T ^ 2 * n / 4 + (L : ℝ) * Real.log 3 ≤
      T ^ 2 * (3 : ℝ) ^ (a * L) / 2 := by
    linarith only [hfirst, hsecond]
  have hrpow : (3 : ℝ) ^ (-(L : ℝ)) =
      Real.exp (-((L : ℝ) * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  rw [hrpow, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith only [hexponent])

private theorem measureReal_largeScaleOccurrenceEvent_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P]
    (B : ℕ → Site d → Set Ω) (a T : ℝ)
    (hBtail : ∀ L z,
      P.real (B L z) ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L))))
    (ha : 1 ≤ a) (hT : 2 * (d + 1) ≤ T)
    (Γ : List (Site d)) (hΓ : IsPath Γ) :
    P.real (largeScaleOccurrenceEvent B Γ) ≤
      (3 : ℝ) ^ d * Real.exp (-(T ^ 2 * Γ.length / 4)) *
        Algsuperdiff.Probability.geomTailConst 1 := by
  let K : ℝ := (3 : ℝ) ^ d * Real.exp (-(T ^ 2 * Γ.length / 4))
  let E : ℕ → Set Ω := fun L =>
    if Γ.length < 3 ^ L then scaleOccurrenceEvent B Γ L else ∅
  have hTtwo : (2 : ℝ) ≤ T :=
    (by norm_num : (2 : ℝ) ≤ 2 * (d + 1)).trans hT
  have hterm : ∀ L, P.real (E L) ≤ K * (3 : ℝ) ^ (-(1 * (L : ℝ))) := by
    intro L
    dsimp only [E]
    split_ifs with hlarge
    · rw [scaleOccurrenceEvent_eq_biUnion]
      have hcard : (touchingCenters L Γ).card ≤ 3 ^ d := by
        have h := card_touchingCenters_le_three_pow_mul_blocks (L := L) hΓ
        have hdiv : Γ.length / 3 ^ L = 0 := Nat.div_eq_of_lt hlarge
        rw [hdiv, zero_add, mul_one] at h
        exact h
      have hone := measureReal_biUnion_finset_le (μ := P)
        (touchingCenters L Γ) (inflatedBadEvent B L)
      have htail := measureReal_inflatedBadEvent_le_exp_half
        P B a T hBtail ha hT L
      calc
        P.real (⋃ v ∈ touchingCenters L Γ, inflatedBadEvent B L v) ≤
            ∑ v ∈ touchingCenters L Γ, P.real (inflatedBadEvent B L v) := hone
        _ ≤ ∑ _v ∈ touchingCenters L Γ,
            Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L) / 2)) :=
          Finset.sum_le_sum fun v _hv => htail v
        _ = (touchingCenters L Γ).card *
            Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L) / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (3 : ℝ) ^ d *
            Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L) / 2)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.exp_pos _).le
        _ ≤ (3 : ℝ) ^ d *
            (Real.exp (-(T ^ 2 * Γ.length / 4)) * (3 : ℝ) ^ (-(L : ℝ))) :=
          mul_le_mul_of_nonneg_left (exp_large_scale_tail_le ha hTtwo hlarge)
            (pow_nonneg (by norm_num) d)
        _ = K * (3 : ℝ) ^ (-(1 * (L : ℝ))) := by
          dsimp only [K]
          have hp : (3 : ℝ) ^ (-(L : ℝ)) = (3 : ℝ) ^ (-(1 * (L : ℝ))) := by
            congr 1
            ring
          rw [hp]
          ring
    · simp only [measureReal_empty]
      positivity
  have hseries := Algsuperdiff.Probability.hasSum_threePow_neg (by norm_num : (0 : ℝ) < 1)
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hsum : HasSum (fun L : ℕ => K * (3 : ℝ) ^ (-(1 * (L : ℝ))))
      (K * Algsuperdiff.Probability.geomTailConst 1) := hseries.mul_left K
  have hmeasure : P (largeScaleOccurrenceEvent B Γ) ≤
      ENNReal.ofReal (K * Algsuperdiff.Probability.geomTailConst 1) := by
    rw [show largeScaleOccurrenceEvent B Γ = ⋃ L, E L by rfl]
    rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg
      (fun L => mul_nonneg hK0 (Real.rpow_nonneg (by norm_num) _)) hsum.summable]
    refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun L => ?_)
    rw [← ENNReal.ofReal_toReal (measure_ne_top P (E L))]
    exact ENNReal.ofReal_le_ofReal (hterm L)
  calc
    P.real (largeScaleOccurrenceEvent B Γ) =
        (P (largeScaleOccurrenceEvent B Γ)).toReal := rfl
    _ ≤ (ENNReal.ofReal (K * Algsuperdiff.Probability.geomTailConst 1)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
    _ = K * Algsuperdiff.Probability.geomTailConst 1 := by
      exact ENNReal.toReal_ofReal
        (mul_nonneg hK0
          (Algsuperdiff.Probability.geomTailConst_pos (by norm_num)).le)
    _ = (3 : ℝ) ^ d * Real.exp (-(T ^ 2 * Γ.length / 4)) *
        Algsuperdiff.Probability.geomTailConst 1 := rfl

private theorem measureReal_weightedCubeEvent_le_of_bounds
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → Site d → Set Ω) (Γ : List (Site d))
    (r A t s : ℝ)
    (hcenter : IsBigO P (gammaSigma 2)
      (centeredWeightedCubeMassOn P B Γ (smallScales Γ)) A)
    (hmean : expectedWeightedCubeMassOn P B Γ (smallScales Γ) ≤ r / 2)
    (hlarge : P.real (largeScaleOccurrenceEvent B Γ) ≤ Real.exp (-(s ^ 2)))
    (hAt : A * t ≤ r / 2) (ht : 2 ≤ t) (hts : t ^ 2 ≤ s ^ 2) :
    P.real (weightedCubeEvent B Γ r) ≤ Real.exp (-(t ^ 2 / 2)) := by
  have hsmall :
      {ω | r < weightedCubeMassOn B Γ (smallScales Γ) ω} ⊆
        absTailEvent
          (centeredWeightedCubeMassOn P B Γ (smallScales Γ)) (A * t) := by
    intro ω hω
    change r < weightedCubeMassOn B Γ (smallScales Γ) ω at hω
    rw [weightedCubeMassOn_eq_centered_add_expected P B Γ (smallScales Γ) ω] at hω
    rw [mem_absTailEvent]
    have hcenterLower : r / 2 <
        centeredWeightedCubeMassOn P B Γ (smallScales Γ) ω := by
      linarith only [hω, hmean]
    have habs := le_abs_self
      (centeredWeightedCubeMassOn P B Γ (smallScales Γ) ω)
    linarith only [hAt, hcenterLower, habs]
  have hsubset : weightedCubeEvent B Γ r ⊆
      largeScaleOccurrenceEvent B Γ ∪
        absTailEvent
          (centeredWeightedCubeMassOn P B Γ (smallScales Γ)) (A * t) :=
    (weightedCubeEvent_subset_largeScale_union_small B Γ r).trans
      (Set.union_subset_union_right _ hsmall)
  have hcenterTail := (isBigO_gammaSigma_iff.mp hcenter) (show 1 ≤ t by
    exact one_le_two.trans ht)
  have hcenterTailNat :
      P.real (absTailEvent
        (centeredWeightedCubeMassOn P B Γ (smallScales Γ)) (A * t)) ≤
          Real.exp (-(t ^ (2 : ℕ))) := by
    simpa only [Real.rpow_two] using hcenterTail
  have hlargeToT : Real.exp (-(s ^ 2)) ≤ Real.exp (-(t ^ 2)) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hts)
  have htwoExp : (2 : ℝ) ≤ Real.exp (t ^ 2 / 2) := by
    have hsq : (4 : ℝ) ≤ t ^ 2 := by
      nlinarith only [ht]
    have hone : (1 : ℝ) ≤ t ^ 2 / 2 := by linarith only [hsq]
    have htwo : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le.trans' (by norm_num)
    exact htwo.trans (Real.exp_le_exp.mpr hone)
  calc
    P.real (weightedCubeEvent B Γ r) ≤
        P.real (largeScaleOccurrenceEvent B Γ ∪
          absTailEvent
            (centeredWeightedCubeMassOn P B Γ (smallScales Γ)) (A * t)) :=
      measureReal_mono hsubset (measure_ne_top P _)
    _ ≤ P.real (largeScaleOccurrenceEvent B Γ) +
          P.real (absTailEvent
            (centeredWeightedCubeMassOn P B Γ (smallScales Γ)) (A * t)) :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-(t ^ 2)) + Real.exp (-(t ^ 2)) :=
      add_le_add (hlarge.trans hlargeToT) hcenterTailNat
    _ = 2 * Real.exp (-(t ^ 2)) := by
      exact (two_mul (Real.exp (-(t ^ 2)))).symm
    _ ≤ Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2)) :=
      mul_le_mul_of_nonneg_right htwoExp (Real.exp_pos _).le
    _ = Real.exp (-(t ^ 2 / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring

private theorem largeScale_comparisonBounds1 :
    ∀ {Ω : Type u_1} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) (B : ℕ → Site d → Set Ω)
      (a T lam : ℝ)
      (_ : (1 : ℝ) ≤ T) (_ : lam < (1 : ℝ)) (Γ : List (Site d)) (_ : (0 : ℕ) < Γ.length),
      let b : ℝ := a - (1 : ℝ);
      let q : ℝ := b * T * lam;
      let K : ℝ := fixedPathTailScaleConst d;
      let D : ℝ := pathBoundPrefactorConst d;
      let n : ℝ := (↑Γ.length : ℝ);
      let t : ℝ := q * √n * K⁻¹;
      let s : ℝ := T * √n / (4 : ℝ);
      ∀ (_ : (0 : ℝ) < T) (_ : (0 : ℝ) < K) (_ : (0 : ℝ) < D) (_ : (0 : ℝ) < n) (_ : √n ^ (2 : ℕ)
        = n)
        (_ : (0 : ℝ) < q) (_ : (64 : ℝ) * ((↑d : ℝ) + (1 : ℝ)) * K ≤ q)
        (_ : q ≤ ((↑d : ℝ) + (1 : ℝ)) * (T * lam)) (_ : (64 : ℝ) * D ≤ T * lam) (_ : T * lam < T)
        (_ : (8 : ℝ) ≤ T)
        (_ : P.real (largeScaleOccurrenceEvent B Γ) ≤ D * Real.exp (-(T ^ (2 : ℕ) * n / (4 : ℝ)))),
        P.real (largeScaleOccurrenceEvent B Γ) ≤ Real.exp (-s ^ (2 : ℕ)) ∧ (2 : ℝ) ≤ t ∧ t ^ (2 :
          ℕ) ≤ s ^ (2 : ℕ) := by
  intro _ _ d P B _ T lam _ hlamOne Γ hΓpos _ q K D n t s hTpos hKpos hDpos hnpos hsqrtSq hqpos
    hqScale hqUpper hD_Tlam hTlamLt hTeight hlargeRaw
  have hDleT : D ≤ T := by
    have hDle64D : D ≤ 64 * D := by linarith only [hDpos]
    exact hDle64D.trans (hD_Tlam.trans hTlamLt.le)
  have hTquad : T ≤ T ^ 2 * n / 8 := by
    have hnOne : (1 : ℝ) ≤ n := by
      have hnOneNat : 1 ≤ Γ.length := hΓpos
      dsimp only [n]
      exact_mod_cast hnOneNat
    have hT8 : 8 * T ≤ T ^ 2 := by nlinarith only [hTeight]
    calc
      T = 8 * T / 8 := by ring
      _ ≤ T ^ 2 / 8 := div_le_div_of_nonneg_right hT8 (by norm_num)
      _ ≤ T ^ 2 * n / 8 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hnOne (sq_nonneg T)
  have hDexp : D ≤ Real.exp (T ^ 2 * n / 8) := by
    have hexp := Real.add_one_le_exp (T ^ 2 * n / 8)
    exact hDleT.trans (hTquad.trans (by linarith only [hexp]))
  have hsSq : s ^ 2 = T ^ 2 * n / 16 := by
    dsimp only [s]
    rw [div_pow, mul_pow, hsqrtSq]
    norm_num
  have hlarge : P.real (largeScaleOccurrenceEvent B Γ) ≤ Real.exp (-(s ^ 2)) := by
    apply hlargeRaw.trans
    calc
      D * Real.exp (-(T ^ 2 * n / 4)) ≤
          Real.exp (T ^ 2 * n / 8) *
            Real.exp (-(T ^ 2 * n / 4)) :=
        mul_le_mul_of_nonneg_right hDexp (Real.exp_pos _).le
      _ = Real.exp (-(T ^ 2 * n / 8)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(s ^ 2)) := by
        rw [Real.exp_le_exp, hsSq]
        have hnonneg : 0 ≤ T ^ 2 * n := mul_nonneg (sq_nonneg T) hnpos.le
        linarith only [hnonneg]
  have htTwo : 2 ≤ t := by
    have hqK : 64 * ((d : ℝ) + 1) ≤ q * K⁻¹ := by
      apply (le_mul_inv_iff₀ hKpos).2
      simpa only [mul_assoc] using hqScale
    have hsqrtOne : 1 ≤ Real.sqrt n := by
      have hnOneNat : 1 ≤ Γ.length := hΓpos
      have hnOne : (1 : ℝ) ≤ n := by
        dsimp only [n]
        exact_mod_cast hnOneNat
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hnOne
    calc
      (2 : ℝ) ≤ 64 := by norm_num
      _ ≤ 64 * ((d : ℝ) + 1) := by
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith only [hd0]
      _ ≤ q * K⁻¹ := hqK
      _ = (q * K⁻¹) * 1 := by ring
      _ ≤ (q * K⁻¹) * Real.sqrt n :=
        mul_le_mul_of_nonneg_left hsqrtOne
          (mul_nonneg hqpos.le (inv_nonneg.mpr hKpos.le))
      _ = t := by dsimp only [t]; ring
  have htNonneg : 0 ≤ t := zero_le_two.trans htTwo
  have hsNonneg : 0 ≤ s := by dsimp only [s]; positivity
  have hqT : q ≤ ((d : ℝ) + 1) * T := by
    have hTlamLe : T * lam ≤ T := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hlamOne.le hTpos.le
    exact hqUpper.trans (mul_le_mul_of_nonneg_left hTlamLe (by positivity))
  have hratio : q * K⁻¹ ≤ T / 8 := by
    apply (mul_inv_le_iff₀ hKpos).2
    have hKdim : 8 * ((d : ℝ) + 1) ≤ K := by
      simpa only [K] using fixedPathTailScale_dimension_le d
    have h8q : 8 * q ≤ T * K := by
      calc
        8 * q ≤ 8 * (((d : ℝ) + 1) * T) :=
          mul_le_mul_of_nonneg_left hqT (by norm_num)
        _ = T * (8 * ((d : ℝ) + 1)) := by ring
        _ ≤ T * K := mul_le_mul_of_nonneg_left hKdim hTpos.le
    linarith only [h8q]
  have htLeS : t ≤ s := by
    dsimp only [t, s]
    calc
      q * Real.sqrt n * K⁻¹ = (q * K⁻¹) * Real.sqrt n := by ring
      _ ≤ (T / 8) * Real.sqrt n :=
        mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg _)
      _ ≤ (T / 4) * Real.sqrt n := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        linarith only [hTpos]
      _ = T * Real.sqrt n / 4 := by ring
  have hts : t ^ 2 ≤ s ^ 2 := by
    nlinarith only [htNonneg, hsNonneg, htLeS]
  exact ⟨hlarge, htTwo, hts⟩

/-- A deterministic path obeys the weighted inflated-cube tail at the
dimension-only rate used in the path union bound. -/
theorem measureReal_weightedCubeEvent_le_fixedPath
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → Site d → Set Ω) (a T lam : ℝ)
    (hBmeas : ∀ L z, MeasurableSet (B L z))
    (hsep : SepIndep P B)
    (hBtail : ∀ L z,
      P.real (B L z) ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L))))
    (ha : 1 < a) (had : a ≤ d) (hTone : 1 ≤ T)
    (hlam : 0 < lam) (hlamOne : lam < 1)
    (hgate : pathBoundGateConst d * lam⁻¹ * (a - 1)⁻¹ ≤ T)
    (Γ : List (Site d)) (hΓ : IsPath Γ) (hΓpos : 0 < Γ.length) :
    P.real (weightedCubeEvent B Γ (lam * Γ.length / 2)) ≤
      Real.exp (-(fixedPathRateConst d *
        ((a - 1) * T * lam) ^ 2 * Γ.length)) := by
  let b : ℝ := a - 1
  let q : ℝ := b * T * lam
  let K : ℝ := fixedPathTailScaleConst d
  let D : ℝ := pathBoundPrefactorConst d
  let n : ℝ := Γ.length
  let t : ℝ := q * Real.sqrt n * K⁻¹
  let s : ℝ := T * Real.sqrt n / 4
  have hb : 0 < b := by dsimp only [b]; linarith only [ha]
  have hbDim : b ≤ d + 1 := by
    dsimp only [b]
    have hd : (d : ℝ) ≤ d + 1 := by norm_num
    linarith only [had, hd]
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hKpos : 0 < K := by
    dsimp only [K]
    exact fixedPathTailScaleConst_pos d
  have hDpos : 0 < D := by
    dsimp only [D]
    exact pathBoundPrefactorConst_pos d
  have hnpos : 0 < n := by
    dsimp only [n]
    exact_mod_cast hΓpos
  have hsqrtPos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsqrtSq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hnpos.le
  have hqGate : pathBoundGateConst d ≤ q := by
    simpa only [q, b] using gateConst_le_product ha hlam hgate
  have hqpos : 0 < q := (pathBoundGateConst_pos d).trans_le hqGate
  have hqScale : 64 * ((d : ℝ) + 1) * K ≤ q := by
    have h := gateConst_scale_le d
    simpa only [K] using h.trans hqGate
  have hqPrefactor : 64 * ((d : ℝ) + 1) * D ≤ q := by
    have h := gateConst_prefactor_le d
    simpa only [D] using h.trans hqGate
  have hqOne : 64 * ((d : ℝ) + 1) ≤ q := gateConst_one_le d |>.trans hqGate
  have hTlam0 : 0 ≤ T * lam := mul_nonneg hTpos.le hlam.le
  have hqUpper : q ≤ ((d : ℝ) + 1) * (T * lam) := by
    dsimp only [q]
    calc
      b * T * lam = b * (T * lam) := by ring
      _ ≤ (d + 1) * (T * lam) :=
        mul_le_mul_of_nonneg_right hbDim hTlam0
  have hD_Tlam : 64 * D ≤ T * lam := by
    have hprod : ((d : ℝ) + 1) * (64 * D) ≤
        ((d : ℝ) + 1) * (T * lam) := by
      calc
        ((d : ℝ) + 1) * (64 * D) = 64 * ((d : ℝ) + 1) * D := by ring
        _ ≤ q := hqPrefactor
        _ ≤ ((d : ℝ) + 1) * (T * lam) := hqUpper
    have hdimPos : (0 : ℝ) < d + 1 := by positivity
    nlinarith only [hprod, hdimPos]
  have hOne_Tlam : 64 ≤ T * lam := by
    have hprod : ((d : ℝ) + 1) * 64 ≤
        ((d : ℝ) + 1) * (T * lam) := by
      calc
        ((d : ℝ) + 1) * 64 = 64 * ((d : ℝ) + 1) := by ring
        _ ≤ q := hqOne
        _ ≤ ((d : ℝ) + 1) * (T * lam) := hqUpper
    have hdimPos : (0 : ℝ) < d + 1 := by positivity
    nlinarith only [hprod, hdimPos]
  have hTlamLt : T * lam < T := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hlamOne hTpos
  have hTeight : 8 ≤ T := by
    linarith only [hOne_Tlam, hTlamLt]
  have hTthreshold : 2 * (d + 1) ≤ T := by
    have hTlamLe : T * lam ≤ T := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hlamOne.le hTpos.le
    have hqUpperT : q ≤ ((d : ℝ) + 1) * T := by
      exact hqUpper.trans (mul_le_mul_of_nonneg_left hTlamLe (by positivity))
    have hKdim : 8 * ((d : ℝ) + 1) ≤ K := by
      simpa only [K] using fixedPathTailScale_dimension_le d
    have hlargeDim : 512 * ((d : ℝ) + 1) ^ 2 ≤ q := by
      calc
        512 * ((d : ℝ) + 1) ^ 2 =
            64 * ((d : ℝ) + 1) * (8 * ((d : ℝ) + 1)) := by ring
        _ ≤ 64 * ((d : ℝ) + 1) * K :=
          mul_le_mul_of_nonneg_left hKdim (by positivity)
        _ ≤ q := hqScale
    have hdimPos : (0 : ℝ) < d + 1 := by positivity
    nlinarith only [hlargeDim, hqUpperT, hdimPos]
  have hcenter := isBigO_gammaTwo_centeredWeightedCubeMassOn_small
    P B hBmeas hsep a T hBtail ha hTthreshold Γ hΓ hΓpos
  have hgeom := geomTailConst_half_sub_one_le (d := d) ha had
  have hcenterScale :
      gammaTriangleConst 2 * fixedPathLayerConst d * Real.sqrt n * T⁻¹ *
          Algsuperdiff.Probability.geomTailConst (b / 2) ≤
        gammaTriangleConst 2 * fixedPathLayerConst d * Real.sqrt n * T⁻¹ *
          (2 * (d + 1) * b⁻¹) := by
    have hcoef : 0 ≤ gammaTriangleConst 2 * fixedPathLayerConst d *
        Real.sqrt n * T⁻¹ :=
      mul_nonneg
        (mul_nonneg
          (mul_nonneg gammaTriangleConst_pos.le (fixedPathLayerConst_pos d).le)
          (Real.sqrt_nonneg _))
        (inv_nonneg.mpr hTpos.le)
    exact mul_le_mul_of_nonneg_left (by simpa only [b] using hgeom) hcoef
  have hAt :
      (gammaTriangleConst 2 * fixedPathLayerConst d * Real.sqrt n * T⁻¹ *
        Algsuperdiff.Probability.geomTailConst (b / 2)) * t ≤
          (lam * n / 2) / 2 := by
    apply (mul_le_mul_of_nonneg_right hcenterScale (by
      dsimp only [t]
      positivity)).trans
    have hcore := fixedPathTailScale_core_le d
    have hcoef :
        2 * (d + 1) * (gammaTriangleConst 2 * fixedPathLayerConst d) * K⁻¹ ≤
          1 / 4 := by
      apply (mul_inv_le_iff₀ hKpos).2
      have hcoreK :
          8 * (d + 1) * (gammaTriangleConst 2 * fixedPathLayerConst d) ≤ K := by
        simpa only [K] using hcore
      linarith only [hcoreK]
    have heq :
        (gammaTriangleConst 2 * fixedPathLayerConst d * Real.sqrt n * T⁻¹ *
            (2 * (d + 1) * b⁻¹)) * t =
          (2 * (d + 1) *
              (gammaTriangleConst 2 * fixedPathLayerConst d) * K⁻¹) *
            (lam * n) := by
      dsimp only [t, q]
      field_simp
      rw [hsqrtSq]
    rw [heq]
    convert mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg hlam.le hnpos.le) using 1
    all_goals ring
  have hmeanRaw := expectedWeightedCubeMassOn_small_le
    P B a T hBtail ha.le hTthreshold Γ hΓ
  have hmeanRewrite :
      2 * (3 : ℝ) ^ d * Γ.length * Real.exp (-(T ^ 2 / 4)) *
          Algsuperdiff.Probability.geomTailConst 1 =
        2 * D * n * Real.exp (-(T ^ 2 / 4)) := by
    dsimp only [D, n, pathBoundPrefactorConst]
    ring
  rw [hmeanRewrite] at hmeanRaw
  have hExpInv := exp_neg_sq_div_four_le_inv hTeight
  have hcoefMean : 2 * D * T⁻¹ ≤ lam / 4 := by
    apply (mul_inv_le_iff₀ hTpos).2
    linarith only [hD_Tlam, hDpos]
  have hmean : expectedWeightedCubeMassOn P B Γ (smallScales Γ) ≤
      (lam * n / 2) / 2 := by
    apply hmeanRaw.trans
    calc
      2 * D * n * Real.exp (-(T ^ 2 / 4)) ≤ 2 * D * n * T⁻¹ :=
        mul_le_mul_of_nonneg_left hExpInv
          (mul_nonneg (mul_nonneg (by norm_num) hDpos.le) hnpos.le)
      _ = (2 * D * T⁻¹) * n := by ring
      _ ≤ (lam / 4) * n :=
        mul_le_mul_of_nonneg_right hcoefMean hnpos.le
      _ = (lam * n / 2) / 2 := by ring
  have hlargeRaw := measureReal_largeScaleOccurrenceEvent_le
    P B a T hBtail ha.le hTthreshold Γ hΓ
  have hlargeRewrite :
      (3 : ℝ) ^ d * Real.exp (-(T ^ 2 * Γ.length / 4)) *
          Algsuperdiff.Probability.geomTailConst 1 =
        D * Real.exp (-(T ^ 2 * n / 4)) := by
    dsimp only [D, n, pathBoundPrefactorConst]
    ring
  rw [hlargeRewrite] at hlargeRaw
  obtain ⟨hlarge, htTwo, hts⟩ :=
    (show (P.real (largeScaleOccurrenceEvent B Γ) ≤ Real.exp (-(s ^ 2))) ∧ (2 ≤ t) ∧ (t ^ 2 ≤ s ^
      2) from
      @largeScale_comparisonBounds1 (Ω) (by infer_instance) (d) (P) (B) (a) (T) (lam) (hTone)
        (hlamOne) (Γ) (hΓpos) (hTpos) (hKpos) (hDpos) (hnpos) (hsqrtSq) (hqpos) (hqScale)
          (hqUpper) (hD_Tlam) (hTlamLt) (hTeight) (hlargeRaw))
  have htail := measureReal_weightedCubeEvent_le_of_bounds
    P B Γ (lam * n / 2)
      (gammaTriangleConst 2 * fixedPathLayerConst d * Real.sqrt n * T⁻¹ *
        Algsuperdiff.Probability.geomTailConst (b / 2)) t s
      (by simpa only [n, b] using hcenter) hmean hlarge hAt htTwo hts
  have hrate : t ^ 2 / 2 =
      fixedPathRateConst d * q ^ 2 * n := by
    dsimp only [t, K, fixedPathRateConst]
    rw [mul_pow, mul_pow, hsqrtSq]
    field_simp
  simpa only [n, b, q, hrate] using htail

end Algsuperdiff.Section5.Percolation
