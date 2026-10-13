/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.CubeMass

/-!
# FixedPath

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Fixed-path multiscale concentration

This file assembles, for one deterministic path, the Gaussian tail parameter of
an inflated cube event, the finite partial sums of the scale-weighted
inflated-cube counts, and the small-scale Orlicz bound for those sums.
-/

namespace Algsuperdiff.Section5.Percolation

open MeasureTheory ProbabilityTheory
open HCPolySupport.IndependentSums
open scoped BigOperators

/-- The natural Gaussian tail parameter at scale `L` after absorbing the
volume of an inflated cube. -/
noncomputable def inflatedTailRate (a T : ℝ) (L : ℕ) : ℝ :=
  T / 2 * (3 : ℝ) ^ (a * L / 2)

/-- The inflated tail parameter is at least one in the admissible range. -/
theorem one_le_inflatedTailRate {a T : ℝ} (ha : 0 ≤ a) (hT : 2 ≤ T)
    (L : ℕ) : 1 ≤ inflatedTailRate a T L := by
  have hpow : 1 ≤ (3 : ℝ) ^ (a * L / 2) := by
    apply Real.one_le_rpow (by norm_num)
    positivity
  have hhalf : 1 ≤ T / 2 := by linarith only [hT]
  exact (show (1 : ℝ) = 1 * 1 by norm_num) ▸
    mul_le_mul hhalf hpow zero_le_one (by linarith only [hhalf])

/-- The absorbed inflated-event tail is bounded by the square of its natural
scale parameter. -/
theorem measureReal_inflatedBadEvent_le_tailRate
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (B : ℕ → Site d → Set Ω) (a T : ℝ)
    (hB : ∀ L z,
      P.real (B L z) ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L))))
    (ha : 1 ≤ a) (hT : 2 * (d + 1) ≤ T) (L : ℕ) (v : Site d) :
    P.real (inflatedBadEvent B L v) ≤
      Real.exp (-(inflatedTailRate a T L ^ 2)) := by
  have hhalf := measureReal_inflatedBadEvent_le_exp_half P B a T hB ha hT L v
  apply hhalf.trans
  rw [Real.exp_le_exp]
  apply neg_le_neg
  have hpow : ((3 : ℝ) ^ (a * L / 2)) ^ 2 = (3 : ℝ) ^ (a * L) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [inflatedTailRate, mul_pow, hpow]
  have hthree : 0 ≤ (3 : ℝ) ^ (a * L) := by positivity
  have hTtwo : 0 ≤ T ^ 2 := sq_nonneg T
  calc
    (T / 2) ^ 2 * (3 : ℝ) ^ (a * L) =
        (T ^ 2 / 4) * (3 : ℝ) ^ (a * L) := by ring
    _ ≤ (T ^ 2 / 2) * (3 : ℝ) ^ (a * L) := by
      apply mul_le_mul_of_nonneg_right _ hthree
      linarith only [hTtwo]
    _ = T ^ 2 * (3 : ℝ) ^ (a * L) / 2 := by ring

/-- A dimension-dependent constant for the centered contribution of one
scale along a fixed path. -/
noncomputable def fixedPathLayerConst (d : ℕ) : ℝ :=
  8 * gammaTriangleConst 2 *
    HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
      (3 : ℝ) ^ (2 * d)

theorem fixedPathLayerConst_pos (d : ℕ) : 0 < fixedPathLayerConst d := by
  unfold fixedPathLayerConst
  exact mul_pos
    (mul_pos (mul_pos (by norm_num) gammaTriangleConst_pos)
      (Algsuperdiff.Probability.gammaSigmaIndependentSumConst_pos (by norm_num)))
    (by positivity)


/-- The real-valued scale-`L` inflated-cube count is measurable. -/
theorem measurable_coe_inflatedCubeCount {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {B : ℕ → Site d → Set Ω}
    (hB : ∀ L z, MeasurableSet (B L z)) (L : ℕ) (Γ : List (Site d)) :
    Measurable fun ω => (inflatedCubeCount B L Γ ω : ℝ) := by
  simp_rw [coe_inflatedCubeCount_eq]
  apply Finset.measurable_sum
  intro v _hv
  exact measurable_const.indicator (measurableSet_inflatedBadEvent hB L v)

/-- A finite partial sum of the scale-weighted inflated-cube counts. -/
noncomputable def weightedCubeMassOn {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (Γ : List (Site d))
    (scales : Finset ℕ) (ω : Ω) : ℝ :=
  ∑ L ∈ scales, (3 : ℝ) ^ L * inflatedCubeCount B L Γ ω

/-- The event that some finite partial scale sum exceeds `r`.  This avoids any
convention for a divergent real series while expressing the nonnegative
infinite sum used in the percolation argument. -/
noncomputable def weightedCubeEvent {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (Γ : List (Site d)) (r : ℝ) : Set Ω :=
  {ω | ∃ scales : Finset ℕ, r < weightedCubeMassOn B Γ scales ω}

private theorem siteDist_getElem_zero_le {d : ℕ} {Γ : List (Site d)}
    (hΓ : IsPath Γ) {n : ℕ} (hn : n < Γ.length) (hzero : 0 < Γ.length) :
    siteDist Γ[0] Γ[n] ≤ n := by
  induction n with
  | zero => exact (siteDist_self Γ[0]).le
  | succ n ih =>
      have hnPrev : n < Γ.length := by omega
      have hprev := ih hnPrev
      have hstep : siteDist Γ[n] Γ[n + 1] = 1 := hΓ.getElem n hn
      calc
        siteDist Γ[0] Γ[n + 1] ≤ siteDist Γ[0] Γ[n] + siteDist Γ[n] Γ[n + 1] :=
          siteDist_triangle _ _ _
        _ ≤ n + 1 := by rw [hstep]; omega

private theorem centerIndex_sub_mem_cubeSites_one {d L : ℕ} {z y : Site d}
    (hzy : siteDist z y < 3 ^ L) :
    centerIndex L z - centerIndex L y ∈ cubeSites d 1 := by
  apply mem_cubeSites_of_inCube
  intro i
  have hi := natAbs_centerIndex_sub_le_one_of_siteDist_lt hzy i
  change 2 * ((centerIndex L z) i - (centerIndex L y) i).natAbs < 3
  omega

private theorem card_touchingCenters_le_three_pow_of_short_path
    {d L : ℕ} {Γ : List (Site d)} (hΓ : IsPath Γ)
    (hlen : Γ.length ≤ 3 ^ L) :
    (touchingCenters L Γ).card ≤ 3 ^ d := by
  classical
  cases Γ with
  | nil => simp only [touchingCenters, List.toFinset_nil, Finset.image_empty,
      Finset.card_empty, Nat.zero_le]
  | cons x xs =>
      let f : Site d → Site d := fun v => v - centerIndex L x
      have hf : Function.Injective f := by
        intro v w hvw
        funext a
        have ha := congr_fun hvw a
        dsimp only [f, Pi.sub_apply] at ha
        omega
      have hsubset : (touchingCenters L (x :: xs)).image f ⊆ cubeSites d 1 := by
        intro u hu
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨z, hz, hvz⟩ := Finset.mem_image.mp hv
        have hzList : z ∈ x :: xs := List.mem_toFinset.mp hz
        obtain ⟨t, ht⟩ := List.mem_iff_get.mp hzList
        have hdistLe := siteDist_getElem_zero_le hΓ t.isLt (by simp)
        have hdist : siteDist z x < 3 ^ L := by
          rw [← ht, siteDist_comm]
          exact hdistLe.trans_lt (lt_of_lt_of_le t.isLt hlen)
        rw [← hvz]
        exact centerIndex_sub_mem_cubeSites_one hdist
      calc
        (touchingCenters L (x :: xs)).card =
            ((touchingCenters L (x :: xs)).image f).card :=
          (Finset.card_image_of_injective _ hf).symm
        _ ≤ (cubeSites d 1).card := Finset.card_le_card hsubset
        _ = 3 ^ d := by rw [card_cubeSites]; simp

/-- The `b`-th consecutive block of at most `3^L` path vertices. -/
def pathBlock {d : ℕ} (L : ℕ) (Γ : List (Site d)) (b : ℕ) : List (Site d) :=
  (Γ.drop (b * 3 ^ L)).take (3 ^ L)

private theorem get_mem_pathBlock {d L : ℕ} (Γ : List (Site d))
    (t : Fin Γ.length) : Γ.get t ∈ pathBlock L Γ (t.1 / 3 ^ L) := by
  let q := 3 ^ L
  let b := t.1 / q
  let r := t.1 % q
  have hq : 0 < q := pow_pos (by norm_num) L
  have hrq : r < q := Nat.mod_lt _ hq
  have hindex : b * q + r = t.1 := by
    dsimp only [b, r]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod t.1 q
  have hrDrop : r < (Γ.drop (b * q)).length := by
    rw [List.length_drop]
    omega
  have hrTake : r < ((Γ.drop (b * q)).take q).length := by
    rw [List.length_take]
    exact lt_min hrq hrDrop
  apply List.mem_iff_get.mpr
  refine ⟨⟨r, hrTake⟩, ?_⟩
  simp only [pathBlock, List.get_eq_getElem,
    List.getElem_take, List.getElem_drop]
  have hindexFull : t.1 / 3 ^ L * 3 ^ L + r = t.1 := by
    simpa only [q, b] using hindex
  simp only [hindexFull]

/-- A lattice path of vertex length `n` touches at most
`3^d (⌊n / 3^L⌋ + 1)` canonical scale-`L` cubes. -/
theorem card_touchingCenters_le_three_pow_mul_blocks {d L : ℕ}
    {Γ : List (Site d)} (hΓ : IsPath Γ) :
    (touchingCenters L Γ).card ≤
      3 ^ d * (Γ.length / 3 ^ L + 1) := by
  classical
  let blocks := Finset.range (Γ.length / 3 ^ L + 1)
  have hsubset : touchingCenters L Γ ⊆
      blocks.biUnion fun b => touchingCenters L (pathBlock L Γ b) := by
    intro v hv
    obtain ⟨z, hz, hvz⟩ := Finset.mem_image.mp hv
    have hzList : z ∈ Γ := List.mem_toFinset.mp hz
    obtain ⟨t, ht⟩ := List.mem_iff_get.mp hzList
    apply Finset.mem_biUnion.mpr
    have hdiv : t.1 / 3 ^ L ≤ Γ.length / 3 ^ L :=
      Nat.div_le_div_right t.isLt.le
    refine ⟨t.1 / 3 ^ L, Finset.mem_range.mpr (by omega), ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨z, List.mem_toFinset.mpr ?_, hvz⟩
    rw [← ht]
    exact get_mem_pathBlock Γ t
  have hblock : ∀ b ∈ blocks,
      (touchingCenters L (pathBlock L Γ b)).card ≤ 3 ^ d := by
    intro b _hb
    apply card_touchingCenters_le_three_pow_of_short_path
    · exact (hΓ.drop (b * 3 ^ L)).take (3 ^ L)
    · rw [pathBlock, List.length_take]
      exact Nat.min_le_left _ _
  calc
    (touchingCenters L Γ).card ≤
        (blocks.biUnion fun b => touchingCenters L (pathBlock L Γ b)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ b ∈ blocks, (touchingCenters L (pathBlock L Γ b)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ blocks, 3 ^ d := Finset.sum_le_sum hblock
    _ = 3 ^ d * (Γ.length / 3 ^ L + 1) := by
      rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_range,
        Nat.mul_comm]

/-- At scales no larger than a path, side length times the number of touched
cubes is at most twice the dimension factor times the vertex length. -/
theorem three_pow_mul_card_touchingCenters_le {d L : ℕ}
    {Γ : List (Site d)} (hΓ : IsPath Γ) (hsmall : 3 ^ L ≤ Γ.length) :
    3 ^ L * (touchingCenters L Γ).card ≤ 2 * 3 ^ d * Γ.length := by
  have hcard := card_touchingCenters_le_three_pow_mul_blocks (L := L) hΓ
  have hmul := Nat.mul_le_mul_left (3 ^ L) hcard
  have hdiv : 3 ^ L * (Γ.length / 3 ^ L) ≤ Γ.length :=
    Nat.mul_div_le Γ.length (3 ^ L)
  calc
    3 ^ L * (touchingCenters L Γ).card ≤
        3 ^ L * (3 ^ d * (Γ.length / 3 ^ L + 1)) := hmul
    _ = 3 ^ d * (3 ^ L * (Γ.length / 3 ^ L) + 3 ^ L) := by ring
    _ ≤ 3 ^ d * (Γ.length + Γ.length) := by
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add hdiv hsmall
    _ = 2 * 3 ^ d * Γ.length := by ring

private theorem weighted_sqrt_touchingCenters_le
    {d L : ℕ} {Γ : List (Site d)} (hΓ : IsPath Γ)
    (hsmall : 3 ^ L ≤ Γ.length) :
    (3 : ℝ) ^ L * Real.sqrt ((touchingCenters L Γ).card : ℝ) ≤
      2 * (3 : ℝ) ^ d * Real.sqrt (Γ.length : ℝ) *
        Real.sqrt ((3 : ℝ) ^ L) := by
  let q : ℕ := 3 ^ L
  let c : ℕ := (touchingCenters L Γ).card
  let n : ℕ := Γ.length
  let D : ℕ := 3 ^ d
  have hDpos : 0 < D := pow_pos (by norm_num) d
  have hqc : q * c ≤ 2 * D * n := by
    simpa only [q, c, n, D] using
      three_pow_mul_card_touchingCenters_le hΓ hsmall
  have hleft0 : 0 ≤ (q : ℝ) * Real.sqrt (c : ℝ) :=
    mul_nonneg (Nat.cast_nonneg q) (Real.sqrt_nonneg _)
  have hright0 : 0 ≤ 2 * (D : ℝ) * Real.sqrt (n : ℝ) * Real.sqrt (q : ℝ) := by
    positivity
  have hqcR : (q : ℝ) * c ≤ 2 * D * n := by exact_mod_cast hqc
  have hsqrtC : Real.sqrt (c : ℝ) ^ 2 = c := Real.sq_sqrt (Nat.cast_nonneg c)
  have hsqrtN : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hsqrtQ : Real.sqrt (q : ℝ) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hDpos
  have hsq : ((q : ℝ) * Real.sqrt (c : ℝ)) ^ 2 ≤
      (2 * (D : ℝ) * Real.sqrt (n : ℝ) * Real.sqrt (q : ℝ)) ^ 2 := by
    calc
      ((q : ℝ) * Real.sqrt (c : ℝ)) ^ 2 = (q : ℝ) * ((q : ℝ) * c) := by
        rw [mul_pow, hsqrtC]
        ring
      _ ≤ (q : ℝ) * (2 * D * n) :=
        mul_le_mul_of_nonneg_left hqcR (Nat.cast_nonneg q)
      _ ≤ (2 * (D : ℝ) * Real.sqrt (n : ℝ) * Real.sqrt (q : ℝ)) ^ 2 := by
        rw [mul_pow, mul_pow, hsqrtN, hsqrtQ]
        have hnonneg : 0 ≤ (2 : ℝ) * D * n * q := by positivity
        nlinarith only [hD1, hnonneg]
  have hmain := (sq_le_sq₀ hleft0 hright0).mp hsq
  simpa only [q, c, n, D, Nat.cast_pow, Nat.cast_ofNat] using hmain

private theorem inflatedTailRate_inv_eq {a T : ℝ} (hT : 0 < T) (L : ℕ) :
    (inflatedTailRate a T L)⁻¹ =
      2 * T⁻¹ * (3 : ℝ) ^ (-(a * L / 2)) := by
  have hpow : (3 : ℝ) ^ (a * L / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  rw [inflatedTailRate, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  field_simp

private theorem sqrt_three_pow_mul_decay {a : ℝ} (L : ℕ) :
    Real.sqrt ((3 : ℝ) ^ L) * (3 : ℝ) ^ (-(a * L / 2)) =
      (3 : ℝ) ^ (-(((a - 1) / 2) * L)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- At a scale no larger than the path length, the centered weighted cube
count has the square-root path-size concentration scale and the geometric
decay `3^{-(a-1)L/2}`. -/
theorem isBigO_gammaTwo_centeredWeightedCubeMassAt_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → Site d → Set Ω) (hBmeas : ∀ L z, MeasurableSet (B L z))
    (hsep : SepIndep P B) (a T : ℝ)
    (hBtail : ∀ L z,
      P.real (B L z) ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L))))
    (ha : 1 ≤ a) (hT : 2 * (d + 1) ≤ T)
    (L : ℕ) (Γ : List (Site d)) (hΓ : IsPath Γ)
    (hsmall : 3 ^ L ≤ Γ.length) :
    IsBigO P (gammaSigma 2) (centeredWeightedCubeMassAt P B Γ L)
      (fixedPathLayerConst d * Real.sqrt (Γ.length : ℝ) * T⁻¹ *
        (3 : ℝ) ^ (-(((a - 1) / 2) * L))) := by
  let R := inflatedTailRate a T L
  have hTtwo : 2 ≤ T := by
    have hd : (2 : ℝ) ≤ 2 * (d + 1) := by norm_num
    exact hd.trans hT
  have hR : 1 ≤ R := one_le_inflatedTailRate (zero_le_one.trans ha) hTtwo L
  have htail : ∀ v ∈ touchingCenters L Γ,
      P.real (inflatedBadEvent B L v) ≤ Real.exp (-(R ^ 2)) := by
    intro v _hv
    exact measureReal_inflatedBadEvent_le_tailRate P B a T hBtail ha hT L v
  have hraw := isBigO_gammaTwo_centeredWeightedCubeMassAt
    P B hBmeas hsep L Γ R hR htail
  apply hraw.mono_scale
  clear hraw
  have hTpos : 0 < T := zero_lt_two.trans_le hTtwo
  have hDone : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hsqrtD : Real.sqrt ((3 : ℝ) ^ d) ≤ (3 : ℝ) ^ d :=
    Algsuperdiff.Probability.sqrt_le_self_of_one_le hDone
  by_cases hc : (touchingCenters L Γ).card = 0
  · simp only [hc, Nat.cast_zero, Real.sqrt_zero, zero_div, mul_zero]
    have hbase3 : (0 : ℝ) ≤ 3 := by norm_num
    have htarget : 0 ≤ fixedPathLayerConst d * Real.sqrt (Γ.length : ℝ) *
        T⁻¹ * (3 : ℝ) ^ (-((a - 1) / 2 * ↑L)) :=
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (fixedPathLayerConst_pos d).le (Real.sqrt_nonneg _))
          (inv_nonneg.mpr hTpos.le))
        (Real.rpow_nonneg hbase3 _)
    calc
      0 * (0 * (2 * R⁻¹)) = 0 := by ring
      _ ≤ fixedPathLayerConst d * Real.sqrt (Γ.length : ℝ) * T⁻¹ *
          (3 : ℝ) ^ (-((a - 1) / 2 * ↑L)) := htarget
  · have hcR : (((touchingCenters L Γ).card : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hc
    have hweighted := weighted_sqrt_touchingCenters_le hΓ hsmall
    have hconstants : 0 ≤ gammaTriangleConst (2 : ℝ) := gammaTriangleConst_pos.le
    have hindependent : 0 ≤
        HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst (2 : ℝ) :=
      (Algsuperdiff.Probability.gammaSigmaIndependentSumConst_pos (by norm_num)).le
    have hD0 : 0 ≤ (3 : ℝ) ^ d := by positivity
    have hrootN : 0 ≤ Real.sqrt (Γ.length : ℝ) := Real.sqrt_nonneg _
    have hdecay0 : 0 ≤ (3 : ℝ) ^ (-(((a - 1) / 2) * L)) := by positivity
    have hTinv : 0 ≤ T⁻¹ := inv_nonneg.mpr hTpos.le
    have hsmallDecay : 0 ≤ (3 : ℝ) ^ (-(a * L / 2)) := by positivity
    rw [inflatedTailRate_inv_eq hTpos L]
    have hnormalize :
        (((3 : ℝ) ^ L * (touchingCenters L Γ).card) *
          (gammaTriangleConst 2 *
            HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
            (Real.sqrt ((3 : ℝ) ^ d) *
              (Real.sqrt ((touchingCenters L Γ).card : ℝ) /
                ((touchingCenters L Γ).card : ℝ))) *
            (2 * (2 * T⁻¹ * (3 : ℝ) ^ (-(a * L / 2)))))) =
          (3 : ℝ) ^ L * Real.sqrt ((touchingCenters L Γ).card : ℝ) *
            (gammaTriangleConst 2 *
              HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
              Real.sqrt ((3 : ℝ) ^ d) *
              (2 * (2 * T⁻¹ * (3 : ℝ) ^ (-(a * L / 2))))) := by
      field_simp
    rw [hnormalize]
    have hfactor :
        gammaTriangleConst 2 *
            HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
            Real.sqrt ((3 : ℝ) ^ d) *
            (2 * (2 * T⁻¹ * (3 : ℝ) ^ (-(a * L / 2)))) ≤
          gammaTriangleConst 2 *
            HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
            (3 : ℝ) ^ d *
            (4 * T⁻¹ * (3 : ℝ) ^ (-(a * L / 2))) := by
      have hAK : 0 ≤ gammaTriangleConst 2 *
          HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 :=
        mul_nonneg hconstants hindependent
      calc
        gammaTriangleConst 2 *
              HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
              Real.sqrt ((3 : ℝ) ^ d) *
              (2 * (2 * T⁻¹ * (3 : ℝ) ^ (-(a * L / 2)))) =
            (gammaTriangleConst 2 *
              HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
              Real.sqrt ((3 : ℝ) ^ d)) *
              (4 * T⁻¹ * (3 : ℝ) ^ (-(a * L / 2))) := by ring
        _ ≤ (gammaTriangleConst 2 *
              HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
              (3 : ℝ) ^ d) *
              (4 * T⁻¹ * (3 : ℝ) ^ (-(a * L / 2))) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hsqrtD hAK
          · positivity
    have hfactorLeft0 : 0 ≤ gammaTriangleConst 2 *
          HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((3 : ℝ) ^ d) *
          (2 * (2 * T⁻¹ * (3 : ℝ) ^ (-(a * L / 2)))) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hconstants hindependent) (Real.sqrt_nonneg _))
        (mul_nonneg (by norm_num)
          (mul_nonneg (mul_nonneg (by norm_num) hTinv) hsmallDecay))
    have hweightedUpper0 : 0 ≤
        2 * (3 : ℝ) ^ d * Real.sqrt (Γ.length : ℝ) *
          Real.sqrt ((3 : ℝ) ^ L) := by positivity
    unfold fixedPathLayerConst
    calc
      (3 : ℝ) ^ L * Real.sqrt ((touchingCenters L Γ).card : ℝ) *
          (gammaTriangleConst 2 *
            HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
            Real.sqrt ((3 : ℝ) ^ d) *
            (2 * (2 * T⁻¹ * (3 : ℝ) ^ (-(a * L / 2))))) ≤
          (2 * (3 : ℝ) ^ d * Real.sqrt (Γ.length : ℝ) *
            Real.sqrt ((3 : ℝ) ^ L)) *
            (gammaTriangleConst 2 *
              HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
              (3 : ℝ) ^ d *
              (4 * T⁻¹ * (3 : ℝ) ^ (-(a * L / 2)))) := by
        apply mul_le_mul
        · exact hweighted
        · exact hfactor
        · exact hfactorLeft0
        · exact hweightedUpper0
      _ = 8 * gammaTriangleConst 2 *
            HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
            (3 : ℝ) ^ (2 * d) * Real.sqrt (Γ.length : ℝ) * T⁻¹ *
            (3 : ℝ) ^ (-(((a - 1) / 2) * L)) := by
        rw [show (3 : ℝ) ^ (2 * d) = ((3 : ℝ) ^ d) ^ 2 by
          rw [Nat.mul_comm, pow_mul]]
        rw [← sqrt_three_pow_mul_decay (a := a) L]
        ring

/-- The finite set of scales whose triadic side length does not exceed the
vertex length of `Γ`. -/
def smallScales {d : ℕ} (Γ : List (Site d)) : Finset ℕ :=
  (Finset.range (Γ.length + 1)).filter fun L => 3 ^ L ≤ Γ.length

@[simp] theorem mem_smallScales_iff {d L : ℕ} {Γ : List (Site d)} :
    L ∈ smallScales Γ ↔ 3 ^ L ≤ Γ.length := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, h⟩
    have hL : L ≤ 3 ^ L := by
      induction L with
      | zero => norm_num
      | succ L ih =>
          rw [pow_succ]
          have hp : 0 < 3 ^ L := pow_pos (by norm_num) L
          omega
    omega

/-- The centered weighted mass over a finite set of scales. -/
noncomputable def centeredWeightedCubeMassOn
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : ℕ → Site d → Set Ω) (Γ : List (Site d))
    (scales : Finset ℕ) (ω : Ω) : ℝ :=
  ∑ L ∈ scales, centeredWeightedCubeMassAt P B Γ L ω

/-- The centered mass over all small scales has a uniform Gaussian scale
controlled by the geometric closure at exponent `(a-1)/2`. -/
theorem isBigO_gammaTwo_centeredWeightedCubeMassOn_small
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → Site d → Set Ω) (hBmeas : ∀ L z, MeasurableSet (B L z))
    (hsep : SepIndep P B) (a T : ℝ)
    (hBtail : ∀ L z,
      P.real (B L z) ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L))))
    (ha : 1 < a) (hT : 2 * (d + 1) ≤ T)
    (Γ : List (Site d)) (hΓ : IsPath Γ) (hΓpos : 0 < Γ.length) :
    IsBigO P (gammaSigma 2)
      (centeredWeightedCubeMassOn P B Γ (smallScales Γ))
      (gammaTriangleConst 2 * fixedPathLayerConst d *
        Real.sqrt (Γ.length : ℝ) * T⁻¹ *
          Algsuperdiff.Probability.geomTailConst ((a - 1) / 2)) := by
  let s := smallScales Γ
  let A : ℕ → ℝ := fun L => fixedPathLayerConst d *
    Real.sqrt (Γ.length : ℝ) * T⁻¹ *
      (3 : ℝ) ^ (-(((a - 1) / 2) * L))
  have hs : s.Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_smallScales_iff]
    simpa only [pow_zero] using! hΓpos
  have hTpos : 0 < T := by
    have : (0 : ℝ) < 2 * (d + 1) := by positivity
    exact this.trans_le hT
  have hApos : ∀ L ∈ s, 0 < A L := by
    intro L _hL
    exact mul_pos
      (mul_pos
        (mul_pos (fixedPathLayerConst_pos d) (Real.sqrt_pos.mpr (by exact_mod_cast hΓpos)))
        (inv_pos.mpr hTpos))
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hAtail : ∀ L ∈ s,
      IsBigO P (gammaSigma 2) (fun ω => centeredWeightedCubeMassAt P B Γ L ω)
        (A L) := by
    intro L hL
    exact isBigO_gammaTwo_centeredWeightedCubeMassAt_le
      P B hBmeas hsep a T hBtail ha.le hT L Γ hΓ
        (mem_smallScales_iff.mp hL)
  have hAmeas : ∀ L ∈ s,
      Measurable (fun ω => centeredWeightedCubeMassAt P B Γ L ω) := by
    intro L _hL
    exact measurable_const.mul
      ((measurable_coe_inflatedCubeCount hBmeas L Γ).sub measurable_const)
  have hsum := isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P) (s := s)
    (X := fun L ω => centeredWeightedCubeMassAt P B Γ L ω)
    (a := A) (σ := (2 : ℝ)) (by norm_num) hs hApos hAtail hAmeas
  apply hsum.mono_scale
  have hα : 0 < (a - 1) / 2 := by linarith only [ha]
  have hgeom := Algsuperdiff.Probability.sum_threePow_neg_le hα s
  have hcoef : 0 ≤ gammaTriangleConst 2 * fixedPathLayerConst d *
      Real.sqrt (Γ.length : ℝ) * T⁻¹ :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg gammaTriangleConst_pos.le (fixedPathLayerConst_pos d).le)
        (Real.sqrt_nonneg _))
      (inv_nonneg.mpr hTpos.le)
  change gammaTriangleConst 2 * ∑ L ∈ s, A L ≤ _
  calc
    gammaTriangleConst 2 * ∑ L ∈ s, A L =
        (gammaTriangleConst 2 * fixedPathLayerConst d *
          Real.sqrt (Γ.length : ℝ) * T⁻¹) *
          ∑ L ∈ s, (3 : ℝ) ^ (-(((a - 1) / 2) * L)) := by
      simp only [A]
      calc
        gammaTriangleConst 2 *
              ∑ L ∈ s, fixedPathLayerConst d * Real.sqrt (Γ.length : ℝ) *
                T⁻¹ * (3 : ℝ) ^ (-((a - 1) / 2 * ↑L)) =
            ∑ L ∈ s, gammaTriangleConst 2 *
              (fixedPathLayerConst d * Real.sqrt (Γ.length : ℝ) * T⁻¹ *
                (3 : ℝ) ^ (-((a - 1) / 2 * ↑L))) := by
          rw [Finset.mul_sum]
        _ = ∑ L ∈ s,
              (gammaTriangleConst 2 * fixedPathLayerConst d *
                Real.sqrt (Γ.length : ℝ) * T⁻¹) *
                (3 : ℝ) ^ (-((a - 1) / 2 * ↑L)) := by
          apply Finset.sum_congr rfl
          intro L _hL
          ring
        _ = (gammaTriangleConst 2 * fixedPathLayerConst d *
              Real.sqrt (Γ.length : ℝ) * T⁻¹) *
              ∑ L ∈ s, (3 : ℝ) ^ (-((a - 1) / 2 * ↑L)) := by
          rw [Finset.mul_sum]
    _ ≤ (gammaTriangleConst 2 * fixedPathLayerConst d *
          Real.sqrt (Γ.length : ℝ) * T⁻¹) *
          Algsuperdiff.Probability.geomTailConst ((a - 1) / 2) :=
      mul_le_mul_of_nonneg_left hgeom hcoef
    _ = gammaTriangleConst 2 * fixedPathLayerConst d *
        Real.sqrt (Γ.length : ℝ) * T⁻¹ *
          Algsuperdiff.Probability.geomTailConst ((a - 1) / 2) := by ring

end Algsuperdiff.Section5.Percolation
