/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.Minimizer

/-!
# SmallScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Rate constants and the small-scale mass bound

This file fixes the dimension-dependent constants of the percolation estimate,
records the arithmetic of the admissibility gate, and bounds the expected
small-scale weighted cube mass along one deterministic path.
-/

namespace Algsuperdiff.Section5.Percolation

open MeasureTheory ProbabilityTheory
open HCPolySupport.IndependentSums
open scoped BigOperators

/-- The dimension-dependent normalization used in the fixed-path Gaussian
tail. -/
noncomputable def fixedPathTailScaleConst (d : ℕ) : ℝ :=
  8 * ((d : ℝ) + 1) *
    (1 + gammaTriangleConst 2 * fixedPathLayerConst d)

theorem fixedPathTailScaleConst_pos (d : ℕ) :
    0 < fixedPathTailScaleConst d := by
  unfold fixedPathTailScaleConst
  exact mul_pos (mul_pos (by norm_num) (by positivity))
    (by
      have hcore : 0 < gammaTriangleConst 2 * fixedPathLayerConst d :=
        mul_pos gammaTriangleConst_pos (fixedPathLayerConst_pos d)
      linarith only [hcore])

/-- The dimension-dependent prefactor in the large-scale union bound. -/
noncomputable def pathBoundPrefactorConst (d : ℕ) : ℝ :=
  (3 : ℝ) ^ d * Algsuperdiff.Probability.geomTailConst 1

theorem pathBoundPrefactorConst_pos (d : ℕ) :
    0 < pathBoundPrefactorConst d := by
  unfold pathBoundPrefactorConst
  exact mul_pos (by positivity)
    (Algsuperdiff.Probability.geomTailConst_pos (by norm_num))

/-- A dimension-dependent threshold that absorbs the fixed-path, large-scale,
mean, path-counting, and geometric-series constants. -/
noncomputable def pathBoundGateConst (d : ℕ) : ℝ :=
  64 * ((d : ℝ) + 1) *
    (1 + fixedPathTailScaleConst d + pathBoundPrefactorConst d)

theorem pathBoundGateConst_pos (d : ℕ) : 0 < pathBoundGateConst d := by
  unfold pathBoundGateConst
  exact mul_pos (mul_pos (by norm_num) (by positivity))
    (by
      have hK := fixedPathTailScaleConst_pos d
      have hP := pathBoundPrefactorConst_pos d
      linarith only [hK, hP])

/-- The fixed-path quadratic rate after the two-event union bound. -/
noncomputable def fixedPathRateConst (d : ℕ) : ℝ :=
  (2 * fixedPathTailScaleConst d ^ 2)⁻¹

theorem fixedPathRateConst_pos (d : ℕ) : 0 < fixedPathRateConst d := by
  unfold fixedPathRateConst
  exact inv_pos.mpr
    (mul_pos (by norm_num) (pow_pos (fixedPathTailScaleConst_pos d) 2))

/-- The rate retained after absorbing the finite path count. -/
noncomputable def pathLengthRateConst (d : ℕ) : ℝ :=
  fixedPathRateConst d / 2

theorem pathLengthRateConst_pos (d : ℕ) : 0 < pathLengthRateConst d := by
  unfold pathLengthRateConst
  exact div_pos (fixedPathRateConst_pos d) (by norm_num)

/-- The rate retained after summing over all possible excess path lengths. -/
noncomputable def pathBoundRateConst (d : ℕ) : ℝ :=
  pathLengthRateConst d / 2

theorem pathBoundRateConst_pos (d : ℕ) : 0 < pathBoundRateConst d := by
  unfold pathBoundRateConst
  exact div_pos (pathLengthRateConst_pos d) (by norm_num)

theorem gateConst_le_product {d : ℕ} {a T lam : ℝ}
    (ha : 1 < a) (hlam : 0 < lam)
    (hgate : pathBoundGateConst d * lam⁻¹ * (a - 1)⁻¹ ≤ T) :
    pathBoundGateConst d ≤ (a - 1) * T * lam := by
  have hb : 0 < a - 1 := by linarith only [ha]
  have hmul : 0 ≤ (a - 1) * lam := mul_nonneg hb.le hlam.le
  calc
    pathBoundGateConst d =
        (pathBoundGateConst d * lam⁻¹ * (a - 1)⁻¹) *
          ((a - 1) * lam) := by
      field_simp
    _ ≤ T * ((a - 1) * lam) :=
      mul_le_mul_of_nonneg_right hgate hmul
    _ = (a - 1) * T * lam := by ring

theorem fixedPathTailScale_core_le (d : ℕ) :
    8 * ((d : ℝ) + 1) * (gammaTriangleConst 2 * fixedPathLayerConst d) ≤
      fixedPathTailScaleConst d := by
  unfold fixedPathTailScaleConst
  have hcore : 0 ≤ gammaTriangleConst 2 * fixedPathLayerConst d :=
    mul_nonneg gammaTriangleConst_pos.le (fixedPathLayerConst_pos d).le
  exact mul_le_mul_of_nonneg_left
    (by linarith only [hcore] :
      gammaTriangleConst 2 * fixedPathLayerConst d ≤
        1 + gammaTriangleConst 2 * fixedPathLayerConst d)
    (by positivity)

theorem fixedPathTailScale_dimension_le (d : ℕ) :
    8 * ((d : ℝ) + 1) ≤ fixedPathTailScaleConst d := by
  unfold fixedPathTailScaleConst
  have hcore : 0 ≤ gammaTriangleConst 2 * fixedPathLayerConst d :=
    mul_nonneg gammaTriangleConst_pos.le (fixedPathLayerConst_pos d).le
  calc
    8 * ((d : ℝ) + 1) = 8 * ((d : ℝ) + 1) * 1 := by ring
    _ ≤ 8 * ((d : ℝ) + 1) *
        (1 + gammaTriangleConst 2 * fixedPathLayerConst d) :=
      mul_le_mul_of_nonneg_left (by linarith only [hcore]) (by positivity)

theorem gateConst_scale_le (d : ℕ) :
    64 * ((d : ℝ) + 1) * fixedPathTailScaleConst d ≤ pathBoundGateConst d := by
  unfold pathBoundGateConst
  have hP := (pathBoundPrefactorConst_pos d).le
  exact mul_le_mul_of_nonneg_left
    (by linarith only [hP] : fixedPathTailScaleConst d ≤
      1 + fixedPathTailScaleConst d + pathBoundPrefactorConst d)
    (by positivity)

theorem gateConst_prefactor_le (d : ℕ) :
    64 * ((d : ℝ) + 1) * pathBoundPrefactorConst d ≤ pathBoundGateConst d := by
  unfold pathBoundGateConst
  have hK := (fixedPathTailScaleConst_pos d).le
  exact mul_le_mul_of_nonneg_left
    (by linarith only [hK] : pathBoundPrefactorConst d ≤
      1 + fixedPathTailScaleConst d + pathBoundPrefactorConst d)
    (by positivity)

theorem gateConst_one_le (d : ℕ) :
    64 * ((d : ℝ) + 1) ≤ pathBoundGateConst d := by
  unfold pathBoundGateConst
  have hK := (fixedPathTailScaleConst_pos d).le
  have hP := (pathBoundPrefactorConst_pos d).le
  calc
    64 * ((d : ℝ) + 1) = 64 * ((d : ℝ) + 1) * 1 := by ring
    _ ≤ 64 * ((d : ℝ) + 1) *
        (1 + fixedPathTailScaleConst d + pathBoundPrefactorConst d) :=
      mul_le_mul_of_nonneg_left (by linarith only [hK, hP]) (by positivity)

theorem entropy_le_fixedPathRate_of_gate {d : ℕ} {a T lam : ℝ}
    (ha : 1 < a) (hlam : 0 < lam)
    (hgate : pathBoundGateConst d * lam⁻¹ * (a - 1)⁻¹ ≤ T) :
    8 * ((d : ℝ) + 1) ≤
      fixedPathRateConst d * ((a - 1) * T * lam) ^ 2 := by
  let K : ℝ := fixedPathTailScaleConst d
  let q : ℝ := (a - 1) * T * lam
  have hKpos : 0 < K := by
    dsimp only [K]
    exact fixedPathTailScaleConst_pos d
  have hqGate : pathBoundGateConst d ≤ q := by
    simpa only [q] using gateConst_le_product ha hlam hgate
  have hqScale : 64 * ((d : ℝ) + 1) * K ≤ q := by
    have h := gateConst_scale_le d
    simpa only [K] using h.trans hqGate
  have hqK : 64 * ((d : ℝ) + 1) ≤ q * K⁻¹ := by
    apply (le_mul_inv_iff₀ hKpos).2
    simpa only [mul_assoc] using hqScale
  have hleft0 : 0 ≤ 64 * ((d : ℝ) + 1) := by positivity
  have hsq := pow_le_pow_left₀ hleft0 hqK 2
  have hdimOne : (1 : ℝ) ≤ d + 1 := by norm_num
  have hbase : 8 * ((d : ℝ) + 1) ≤
      (64 * ((d : ℝ) + 1)) ^ 2 / 2 := by
    nlinarith only [hdimOne]
  have hrateEq :
      fixedPathRateConst d * q ^ 2 = (q * K⁻¹) ^ 2 / 2 := by
    dsimp only [K, fixedPathRateConst]
    field_simp
  calc
    8 * ((d : ℝ) + 1) ≤ (64 * ((d : ℝ) + 1)) ^ 2 / 2 := hbase
    _ ≤ (q * K⁻¹) ^ 2 / 2 :=
      div_le_div_of_nonneg_right hsq (by norm_num)
    _ = fixedPathRateConst d * q ^ 2 := hrateEq.symm
    _ = fixedPathRateConst d * ((a - 1) * T * lam) ^ 2 := by rfl

theorem exp_neg_sq_div_four_le_inv {T : ℝ} (hT : 8 ≤ T) :
    Real.exp (-(T ^ 2 / 4)) ≤ T⁻¹ := by
  have hTpos : 0 < T := (by norm_num : (0 : ℝ) < 8).trans_le hT
  have hquad : T ≤ T ^ 2 / 4 := by
    nlinarith only [hT]
  have hTexp : T ≤ Real.exp (T ^ 2 / 4) := by
    have hexp := Real.add_one_le_exp (T ^ 2 / 4)
    exact hquad.trans (by linarith only [hexp])
  rw [Real.exp_neg]
  exact inv_anti₀ hTpos hTexp

theorem geomTailConst_half_sub_one_le {d : ℕ} {a : ℝ}
    (ha : 1 < a) (had : a ≤ d) :
    Algsuperdiff.Probability.geomTailConst ((a - 1) / 2) ≤
      2 * (d + 1) * (a - 1)⁻¹ := by
  let x : ℝ := (a - 1) / 2
  let u : ℝ := Real.log 3 * x
  have hx : 0 < x := by dsimp only [x]; linarith only [ha]
  have hlogLower : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hlogUpper : Real.log 3 ≤ 2 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)).trans
      (by norm_num)
  have hu : 0 < u := mul_pos (zero_lt_one.trans_le hlogLower) hx
  have hxu : x ≤ u := by
    dsimp only [u]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hlogLower hx.le
  have hua : u ≤ a - 1 := by
    dsimp only [u, x]
    have := mul_le_mul_of_nonneg_right hlogUpper (by linarith only [ha] : 0 ≤ (a - 1) / 2)
    linarith only [this]
  have hud : u ≤ d := hua.trans (by linarith only [had])
  have hexpInv : Real.exp (-u) ≤ (1 + u)⁻¹ := by
    have hbase := Real.add_one_le_exp u
    have hden : 0 < 1 + u := by linarith only [hu]
    rw [Real.exp_neg]
    exact inv_anti₀ hden (by simpa only [add_comm] using hbase)
  have hdenom : x / (d + 1) ≤ 1 - Real.exp (-u) := by
    have hfrac : x / (d + 1) ≤ u / (1 + u) := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < d + 1) (by linarith only [hu] : 0 < 1 + u)]
      have hdu : 1 + u ≤ d + 1 := by linarith only [hud]
      calc
        x * (1 + u) ≤ u * (1 + u) :=
          mul_le_mul_of_nonneg_right hxu (by linarith only [hu])
        _ ≤ u * (d + 1) := mul_le_mul_of_nonneg_left hdu hu.le
    calc
      x / (d + 1) ≤ u / (1 + u) := hfrac
      _ = 1 - (1 + u)⁻¹ := by field_simp; ring
      _ ≤ 1 - Real.exp (-u) := sub_le_sub_left hexpInv 1
  have hdenomPos : 0 < 1 - Real.exp (-u) := lt_of_lt_of_le
    (div_pos hx (by positivity)) hdenom
  have hrpow : (3 : ℝ) ^ (-x) = Real.exp (-u) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    dsimp only [u]
    ring
  rw [Algsuperdiff.Probability.geomTailConst, hrpow]
  have hinv := inv_anti₀ (div_pos hx (by positivity : (0 : ℝ) < d + 1)) hdenom
  have hright : (x / (d + 1))⁻¹ = 2 * (d + 1) * (a - 1)⁻¹ := by
    dsimp only [x]
    have ha1 : a - 1 ≠ 0 := ne_of_gt (by linarith only [ha])
    field_simp
  rw [hright] at hinv
  exact hinv

theorem two_mul_le_three_pow (L : ℕ) : 2 * L ≤ 3 ^ L := by
  induction L with
  | zero => norm_num
  | succ L ih =>
      rw [pow_succ]
      have hp : 1 ≤ 3 ^ L := one_le_pow₀ (by norm_num)
      omega

private theorem exp_scale_tail_le {a T : ℝ} (ha : 1 ≤ a) (hT : 2 ≤ T)
    (L : ℕ) :
    Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L) / 2)) ≤
      Real.exp (-(T ^ 2 / 4)) * (3 : ℝ) ^ (-(L : ℝ)) := by
  have hlog : Real.log 3 ≤ 2 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)).trans
      (by norm_num)
  have hqA : (3 : ℝ) ^ L ≤ (3 : ℝ) ^ (a * L) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg L)
  have hqAone : (1 : ℝ) ≤ (3 : ℝ) ^ (a * L) := by
    exact Real.one_le_rpow (by norm_num)
      (mul_nonneg (zero_le_one.trans ha) (Nat.cast_nonneg L))
  have hTsq : (4 : ℝ) ≤ T ^ 2 := by
    have := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) hT
    calc
      (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ T * T := this
      _ = T ^ 2 := by ring
  have hLq : (2 : ℝ) * L ≤ (3 : ℝ) ^ L := by
    exact_mod_cast two_mul_le_three_pow L
  have hlogL : (L : ℝ) * Real.log 3 ≤ (3 : ℝ) ^ (a * L) := by
    calc
      (L : ℝ) * Real.log 3 ≤ L * 2 :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg L)
      _ = 2 * L := by ring
      _ ≤ (3 : ℝ) ^ L := hLq
      _ ≤ (3 : ℝ) ^ (a * L) := hqA
  have hexponent : T ^ 2 / 4 + (L : ℝ) * Real.log 3 ≤
      T ^ 2 * (3 : ℝ) ^ (a * L) / 2 := by
    have hfirst : T ^ 2 / 4 ≤ T ^ 2 * (3 : ℝ) ^ (a * L) / 4 := by
      calc
        T ^ 2 / 4 = (T ^ 2 / 4) * 1 := by ring
        _ ≤ (T ^ 2 / 4) * (3 : ℝ) ^ (a * L) :=
          mul_le_mul_of_nonneg_left hqAone (div_nonneg (sq_nonneg T) (by norm_num))
        _ = T ^ 2 * (3 : ℝ) ^ (a * L) / 4 := by ring
    have hsecond : (L : ℝ) * Real.log 3 ≤
        T ^ 2 * (3 : ℝ) ^ (a * L) / 4 := by
      calc
        (L : ℝ) * Real.log 3 ≤ (3 : ℝ) ^ (a * L) := hlogL
        _ = 4 * (3 : ℝ) ^ (a * L) / 4 := by ring
        _ ≤ T ^ 2 * (3 : ℝ) ^ (a * L) / 4 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hTsq (by positivity)
    linarith only [hfirst, hsecond]
  have hrpow : (3 : ℝ) ^ (-(L : ℝ)) =
      Real.exp (-((L : ℝ) * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  rw [hrpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [hexponent]

/-- The deterministic mean of the weighted inflated-cube count over a finite
set of scales. -/
noncomputable def expectedWeightedCubeMassOn
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : ℕ → Site d → Set Ω) (Γ : List (Site d))
    (scales : Finset ℕ) : ℝ :=
  ∑ L ∈ scales, (3 : ℝ) ^ L *
    ∑ v ∈ touchingCenters L Γ, P.real (inflatedBadEvent B L v)

/-- Weighted mass is its centered part plus its deterministic mean. -/
theorem weightedCubeMassOn_eq_centered_add_expected
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : ℕ → Site d → Set Ω) (Γ : List (Site d))
    (scales : Finset ℕ) (ω : Ω) :
    weightedCubeMassOn B Γ scales ω =
      centeredWeightedCubeMassOn P B Γ scales ω +
        expectedWeightedCubeMassOn P B Γ scales := by
  rw [weightedCubeMassOn, centeredWeightedCubeMassOn,
    expectedWeightedCubeMassOn, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro L _hL
  rw [centeredWeightedCubeMassAt]
  ring

/-- The deterministic mean over all small scales is bounded by a geometric
multiple of the path length. -/
theorem expectedWeightedCubeMassOn_small_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (B : ℕ → Site d → Set Ω) (a T : ℝ)
    (hBtail : ∀ L z,
      P.real (B L z) ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L))))
    (ha : 1 ≤ a) (hT : 2 * (d + 1) ≤ T)
    (Γ : List (Site d)) (hΓ : IsPath Γ) :
    expectedWeightedCubeMassOn P B Γ (smallScales Γ) ≤
      2 * (3 : ℝ) ^ d * Γ.length * Real.exp (-(T ^ 2 / 4)) *
        Algsuperdiff.Probability.geomTailConst 1 := by
  have hTtwo : (2 : ℝ) ≤ T :=
    (by norm_num : (2 : ℝ) ≤ 2 * (d + 1)).trans hT
  rw [expectedWeightedCubeMassOn]
  calc
    ∑ L ∈ smallScales Γ, (3 : ℝ) ^ L *
          ∑ v ∈ touchingCenters L Γ, P.real (inflatedBadEvent B L v) ≤
        ∑ L ∈ smallScales Γ,
          2 * (3 : ℝ) ^ d * Γ.length *
            (Real.exp (-(T ^ 2 / 4)) * (3 : ℝ) ^ (-(L : ℝ))) := by
      apply Finset.sum_le_sum
      intro L hL
      have hsmall := mem_smallScales_iff.mp hL
      have hcardNat := three_pow_mul_card_touchingCenters_le hΓ hsmall
      have hcard : (3 : ℝ) ^ L * (touchingCenters L Γ).card ≤
          2 * (3 : ℝ) ^ d * Γ.length := by exact_mod_cast hcardNat
      have htail := measureReal_inflatedBadEvent_le_exp_half
        P B a T hBtail ha hT L
      have hsum : ∑ v ∈ touchingCenters L Γ,
          P.real (inflatedBadEvent B L v) ≤
          (touchingCenters L Γ).card *
            Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L) / 2)) := by
        calc
          ∑ v ∈ touchingCenters L Γ, P.real (inflatedBadEvent B L v) ≤
              ∑ _v ∈ touchingCenters L Γ,
                Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L) / 2)) := by
            exact Finset.sum_le_sum fun v _hv => htail v
          _ = (touchingCenters L Γ).card *
              Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L) / 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      calc
        (3 : ℝ) ^ L * ∑ v ∈ touchingCenters L Γ,
              P.real (inflatedBadEvent B L v) ≤
            ((3 : ℝ) ^ L * (touchingCenters L Γ).card) *
              Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L) / 2)) := by
          calc
            (3 : ℝ) ^ L * ∑ v ∈ touchingCenters L Γ,
                  P.real (inflatedBadEvent B L v) ≤
                (3 : ℝ) ^ L * ((touchingCenters L Γ).card *
                  Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L) / 2))) :=
              mul_le_mul_of_nonneg_left hsum
                (show (0 : ℝ) ≤ (3 : ℝ) ^ L from pow_nonneg (by norm_num) L)
            _ = ((3 : ℝ) ^ L * (touchingCenters L Γ).card) *
                  Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L) / 2)) := by ring
        _ ≤ (2 * (3 : ℝ) ^ d * Γ.length) *
              Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L) / 2)) :=
          mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
        _ ≤ (2 * (3 : ℝ) ^ d * Γ.length) *
              (Real.exp (-(T ^ 2 / 4)) * (3 : ℝ) ^ (-(L : ℝ))) :=
          mul_le_mul_of_nonneg_left (exp_scale_tail_le ha hTtwo L)
            (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) d))
              (Nat.cast_nonneg Γ.length))
        _ = 2 * (3 : ℝ) ^ d * Γ.length *
              (Real.exp (-(T ^ 2 / 4)) * (3 : ℝ) ^ (-(L : ℝ))) := by ring
    _ = (2 * (3 : ℝ) ^ d * Γ.length * Real.exp (-(T ^ 2 / 4))) *
        ∑ L ∈ smallScales Γ, (3 : ℝ) ^ (-(1 * (L : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro L _hL
      have hpow : (3 : ℝ) ^ (-(L : ℝ)) =
          (3 : ℝ) ^ (-(1 * (L : ℝ))) := by
        congr 1
        ring
      rw [hpow]
      ring
    _ ≤ (2 * (3 : ℝ) ^ d * Γ.length * Real.exp (-(T ^ 2 / 4))) *
        Algsuperdiff.Probability.geomTailConst 1 := by
      apply mul_le_mul_of_nonneg_left
      · exact Algsuperdiff.Probability.sum_threePow_neg_le (by norm_num) _
      · positivity
    _ = 2 * (3 : ℝ) ^ d * Γ.length * Real.exp (-(T ^ 2 / 4)) *
        Algsuperdiff.Probability.geomTailConst 1 := by ring

end Algsuperdiff.Section5.Percolation
