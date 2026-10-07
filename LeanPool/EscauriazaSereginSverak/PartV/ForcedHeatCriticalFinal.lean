/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatCriticalBound

/-!
# The critical `L⁵` and `L^∞ L³` bounds for the smooth forced heat response

Letting the regularization vanish in the window estimates and applying
Hölder's inequality to `Y = ∫∫ |Z| |g|²` gives, with `B = ∫∫ |g|^{5/2}`,

`∫∫ |Z|⁵ ≤ C B²` and `∫ |Z(t)|³ ≤ C B^{6/5}` for `0 ≤ t ≤ τ`,

the smooth-data form of `eq:pv-stokes-l5` in `lem:pv-stokes`, with an absolute
constant `C`.
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem inv_succ_tendsto :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    tendsto_one_div_add_atTop_nhds_zero_nat
    (Eventually.of_forall fun n => by
      change (0 : ℝ) < 1 / ((n : ℝ) + 1)
      positivity)

/-- The space-time `L⁵` integral of the response is bounded by `C Y^{5/3}`. -/
theorem response_rpow_five_le {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    (hgpos : ∀ i j, tsupport (g i j) ⊆ {p | 0 < p.2}) {τ : ℝ} (hτ : 0 ≤ τ) :
    Integrable (fun p => (∑ i : Fin 3, (responseVec g p i) ^ 2) ^ (5 / 2 : ℝ))
        ((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) ∧
    ∫ p, (∑ i : Fin 3, (responseVec g p i) ^ 2) ^ (5 / 2 : ℝ)
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) ≤
      criticalGNConstant * (∫ p, vec3EuclideanNorm (responseVec g p) *
        ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2
          ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ)))) ^ (5 / 3 : ℝ) := by
  set μ := (volume : Measure Vec3).prod (volume.restrict (Ioc (0 : ℝ) τ))
  obtain ⟨M, hM, hq⟩ := response_sq_decay hg hgc
  have hT : ContDiff ℝ 1 (heatRegTest 1) := (heatRegTest_contDiff one_pos).of_le (by simp)
  obtain ⟨hZc, _, _⟩ := response_continuity hg hgc hT
  let q : Vec3 × ℝ → ℝ := fun p => ∑ i : Fin 3, (responseVec g p i) ^ 2
  have hq0 (p : Vec3 × ℝ) : 0 ≤ q p := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hqc : Continuous q := continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp hZc).pow 2
  have hqM (p : Vec3 × ℝ) : q p ≤ M ^ 2 := by
    have hn := (hq p).1
    have hsq := vec3EuclideanNorm_sq (responseVec g p)
    nlinarith only [hn, hsq, vec3EuclideanNorm_nonneg (responseVec g p)]
  have hlimb (p : Vec3 × ℝ) : q p ^ (5 / 2 : ℝ) ≤ (M ^ 2) ^ (3 / 2 : ℝ) * M /
      (1 + vec3EuclideanNorm p.1) ^ 6 := by
    calc
      q p ^ (5 / 2 : ℝ) = q p ^ (1 : ℝ) * q p ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_add' (hq0 p) (by norm_num)]
        norm_num
      _ ≤ (M ^ 2) ^ (3 / 2 : ℝ) * (M / (1 + vec3EuclideanNorm p.1) ^ 6) := by
        rw [Real.rpow_one, mul_comm]
        exact mul_le_mul (Real.rpow_le_rpow (hq0 p) (hqM p) (by norm_num)) (hq p).2 (hq0 p)
          (by positivity)
      _ = _ := by ring
  have hlimc : Continuous (fun p => q p ^ (5 / 2 : ℝ)) :=
    hqc.rpow_const fun _ => Or.inr (by norm_num)
  have hlimint : Integrable (fun p => q p ^ (5 / 2 : ℝ)) μ :=
    integrable_window_of_decay (C := (M ^ 2) ^ (3 / 2 : ℝ) * M) hlimc (by positivity)
      fun x t _ => by
        rw [abs_of_nonneg (Real.rpow_nonneg (hq0 _) _)]
        exact hlimb (x, t)
  refine ⟨hlimint, ?_⟩
  let η : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hηpos (n : ℕ) : 0 < η n := by positivity
  let F : ℕ → Vec3 × ℝ → ℝ := fun n p => |heatRegG (η n) (responseVec g p)| ^ (10 / 3 : ℝ)
  have hFc (n : ℕ) : Continuous (F n) :=
    (((heatRegG_contDiff (hηpos n)).continuous.comp hZc).abs.rpow_const
      fun _ => Or.inr (by norm_num))
  have hFle (n : ℕ) (p : Vec3 × ℝ) : F n p ≤ q p ^ (5 / 2 : ℝ) := by
    obtain ⟨hG0, hGle⟩ := heatRegG_nonneg_le_rpow (hηpos n) (responseVec g p)
    calc
      F n p ≤ (q p ^ (3 / 4 : ℝ)) ^ (10 / 3 : ℝ) := by
        simp only [F]
        rw [abs_of_nonneg hG0]
        exact Real.rpow_le_rpow hG0 hGle (by norm_num)
      _ = q p ^ (5 / 2 : ℝ) := by
        rw [← Real.rpow_mul (hq0 p)]
        norm_num
  have hlim (p : Vec3 × ℝ) : Tendsto (fun n => F n p) atTop (𝓝 (q p ^ (5 / 2 : ℝ))) := by
    have h1 := (heatRegG_tendsto_rpow (responseVec g p)).comp inv_succ_tendsto
    have hcont : Continuous (fun y : ℝ => |y| ^ (10 / 3 : ℝ)) :=
      continuous_abs.rpow_const fun _ => Or.inr (by norm_num)
    have h2 := (hcont.tendsto _).comp h1
    have hval : |q p ^ (3 / 4 : ℝ)| ^ (10 / 3 : ℝ) = q p ^ (5 / 2 : ℝ) := by
      rw [abs_of_nonneg (Real.rpow_nonneg (hq0 p) _), ← Real.rpow_mul (hq0 p)]
      norm_num
    rw [hval] at h2
    exact h2
  have hDCT := tendsto_integral_of_dominated_convergence (μ := μ) (F := F)
    (fun p => q p ^ (5 / 2 : ℝ)) (fun n => (hFc n).aestronglyMeasurable) hlimint
    (fun n => Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact hFle n p)
    (Eventually.of_forall hlim)
  exact le_of_tendsto' hDCT fun n =>
    response_critical_profile_window_le hg hgc hgpos (hηpos n) hτ

/-- For every time in the window, the spatial `L³` integral of the response is
bounded by `3 Y`. -/
theorem response_rpow_three_le {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    (hgpos : ∀ i j, tsupport (g i j) ⊆ {p | 0 < p.2}) {τ : ℝ} (hτ : 0 ≤ τ)
    {t : ℝ} (ht : t ∈ Icc 0 τ) :
    ∫ x, (∑ i : Fin 3, (responseVec g (x, t) i) ^ 2) ^ (3 / 2 : ℝ) ≤
      3 * ∫ p, vec3EuclideanNorm (responseVec g p) * ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2
          ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) := by
  obtain ⟨M, hM, hq⟩ := response_sq_decay hg hgc
  have hT : ContDiff ℝ 1 (heatRegTest 1) := (heatRegTest_contDiff one_pos).of_le (by simp)
  obtain ⟨hZc, _, _⟩ := response_continuity hg hgc hT
  have hsc : Continuous (fun x : Vec3 => ((x, t) : Vec3 × ℝ)) :=
    continuous_id.prodMk continuous_const
  let q : Vec3 → ℝ := fun x => ∑ i : Fin 3, (responseVec g (x, t) i) ^ 2
  have hq0 (x : Vec3) : 0 ≤ q x := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hqc : Continuous q := continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp (hZc.comp hsc)).pow 2
  have hqint : Integrable q := integrable_of_abs_le_decay_six' hM hqc fun x => by
    rw [abs_of_nonneg (hq0 x)]
    exact (hq (x, t)).2
  let η : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hηpos (n : ℕ) : 0 < η n := by positivity
  have hηle (n : ℕ) : η n ≤ 1 := by
    simp only [η]
    rw [div_le_one (by positivity)]
    have := Nat.cast_nonneg (α := ℝ) n
    linarith only [this]
  let F : ℕ → Vec3 → ℝ := fun n x => heatRegEnergy (η n) (responseVec g (x, t))
  have hFc (n : ℕ) : Continuous (F n) :=
    (heatRegEnergy_contDiff (hηpos n)).continuous.comp (hZc.comp hsc)
  have hFle (n : ℕ) (x : Vec3) : ‖F n x‖ ≤ ((3 + 2 * M) / 6) * q x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (heatRegEnergy_nonneg (hηpos n) _)]
    refine (heatRegEnergy_le_mul_sum_sq (hηpos n) hM _ (hq (x, t)).1).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith only [hηle n]) (hq0 x)
  have hlim (x : Vec3) : Tendsto (fun n => F n x) atTop
      (𝓝 ((1 / 3 : ℝ) * q x ^ (3 / 2 : ℝ))) :=
    (heatRegEnergy_tendsto_rpow (responseVec g (x, t))).comp inv_succ_tendsto
  have hDCT := tendsto_integral_of_dominated_convergence (F := F)
    (fun x => ((3 + 2 * M) / 6) * q x) (fun n => (hFc n).aestronglyMeasurable)
    (hqint.const_mul _) (fun n => Eventually.of_forall (hFle n)) (Eventually.of_forall hlim)
  have hbound := le_of_tendsto' hDCT fun n =>
    (response_critical_window_bounds hg hgc hgpos (hηpos n) hτ).1 t ht
  rw [integral_const_mul] at hbound
  linarith only [hbound]

/-- Hölder's inequality for `Y = ∫∫ |Z| |g|²` with exponents `5` and `5/4`. -/
theorem response_forcing_holder {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    (hgpos : ∀ i j, tsupport (g i j) ⊆ {p | 0 < p.2}) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ p, vec3EuclideanNorm (responseVec g p) * ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) ≤
      (∫ p, (∑ i : Fin 3, (responseVec g p i) ^ 2) ^ (5 / 2 : ℝ)
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ)))) ^ (1 / 5 : ℝ) *
      (∫ p, (∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2) ^ (5 / 4 : ℝ)
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ)))) ^ (4 / 5 : ℝ) := by
  set μ := (volume : Measure Vec3).prod (volume.restrict (Ioc (0 : ℝ) τ))
  have hT : ContDiff ℝ 1 (heatRegTest 1) := (heatRegTest_contDiff one_pos).of_le (by simp)
  obtain ⟨hZc, _, _⟩ := response_continuity hg hgc hT
  obtain ⟨hA5int, _⟩ := response_rpow_five_le hg hgc hgpos hτ
  let n : Vec3 × ℝ → ℝ := fun p => vec3EuclideanNorm (responseVec g p)
  let S : Vec3 × ℝ → ℝ := fun p => ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2
  have hn0 (p : Vec3 × ℝ) : 0 ≤ n p := vec3EuclideanNorm_nonneg _
  have hS0 (p : Vec3 × ℝ) : 0 ≤ S p :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hnc : Continuous n := continuous_vec3EuclideanNorm.comp hZc
  have hSc : Continuous S := continuous_finsetSum _ fun i _ => continuous_finsetSum _
    fun j _ => (hg i j).continuous.pow 2
  have hn5 (p : Vec3 × ℝ) : n p ^ (5 : ℝ) =
      (∑ i : Fin 3, (responseVec g p i) ^ 2) ^ (5 / 2 : ℝ) := by
    simp only [n, vec3EuclideanNorm, Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    norm_num
  have hSc5 : HasCompactSupport (fun p => S p ^ (5 / 4 : ℝ)) := by
    have hSsupp : HasCompactSupport S := by
      have hsum := HasCompactSupport.finset_sum (s := Finset.univ)
        (f := fun i (p : Vec3 × ℝ) => ∑ j : Fin 3, (g i j p) ^ 2) fun i _ => by
          have hsum' := HasCompactSupport.finset_sum (s := Finset.univ)
            (f := fun j (p : Vec3 × ℝ) => (g i j p) ^ 2) fun j _ => by
              exact (hgc i j).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
          convert hsum' using 1
          funext p
          simp only [Finset.sum_apply]
      convert hsum using 1
      funext p
      simp only [S, Finset.sum_apply]
    exact hSsupp.comp_left (g := fun y : ℝ => y ^ (5 / 4 : ℝ)) (Real.zero_rpow (by norm_num))
  have hS54int : Integrable (fun p => S p ^ (5 / 4 : ℝ)) μ := by
    have hglob : Integrable (fun p => S p ^ (5 / 4 : ℝ))
        ((volume : Measure Vec3).prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact (hSc.rpow_const fun _ => Or.inr (by norm_num)).integrable_of_hasCompactSupport
        hSc5
    have hon := hglob.integrableOn (s := univ ×ˢ Ioc 0 τ)
    rw [IntegrableOn, ← window_prod_eq] at hon
    exact hon
  have hmemn : MemLp n (ENNReal.ofReal 5) μ := by
    rw [← integrable_norm_rpow_iff hnc.aestronglyMeasurable (by norm_num) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by norm_num)]
    refine hA5int.congr (Eventually.of_forall fun p => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hn0 p)]
    exact (hn5 p).symm
  have hmemS : MemLp S (ENNReal.ofReal (5 / 4)) μ := by
    rw [← integrable_norm_rpow_iff hSc.aestronglyMeasurable (by norm_num)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by norm_num)]
    refine hS54int.congr (Eventually.of_forall fun p => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hS0 p)]
  have hconj : (5 : ℝ).HolderConjugate (5 / 4) :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).2 (by norm_num)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hconj (Eventually.of_forall hn0)
    (Eventually.of_forall hS0) hmemn hmemS
  simp_rw [hn5] at hH
  have h45 : (1 : ℝ) / (5 / 4) = 4 / 5 := by norm_num
  rw [h45] at hH
  exact hH

/-- The absolute constant of the smooth-data critical estimate. -/
@[expose] def criticalResponseConstant : ℝ :=
  criticalGNConstant ^ (3 / 2 : ℝ) + 3 * criticalGNConstant ^ (3 / 10 : ℝ)

theorem criticalResponseConstant_nonneg : 0 ≤ criticalResponseConstant := by
  have := criticalGNConstant_nonneg
  unfold criticalResponseConstant
  positivity

/-- The critical estimate for the smooth forced heat response: with
`B = ∫∫_{(0,τ]} |g|^{5/2}`, `∫∫_{(0,τ]} |Z|⁵ ≤ C B²` and
`∫ |Z(t)|³ ≤ C B^{6/5}` for `0 ≤ t ≤ τ`, with an absolute constant `C`. -/
theorem response_critical_estimate {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    (hgpos : ∀ i j, tsupport (g i j) ⊆ {p | 0 < p.2}) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ p, (∑ i : Fin 3, (responseVec g p i) ^ 2) ^ (5 / 2 : ℝ)
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) ≤
      criticalResponseConstant * (∫ p, (∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2) ^ (5 / 4 : ℝ)
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ)))) ^ 2 ∧
    ∀ t ∈ Icc 0 τ, ∫ x, (∑ i : Fin 3, (responseVec g (x, t) i) ^ 2) ^ (3 / 2 : ℝ) ≤
      criticalResponseConstant * (∫ p, (∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2) ^ (5 / 4 : ℝ)
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ)))) ^ (6 / 5 : ℝ) := by
  set μ := (volume : Measure Vec3).prod (volume.restrict (Ioc (0 : ℝ) τ))
  set A5 : ℝ := ∫ p, (∑ i : Fin 3, (responseVec g p i) ^ 2) ^ (5 / 2 : ℝ) ∂μ with hA5
  set B : ℝ := ∫ p, (∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2) ^ (5 / 4 : ℝ) ∂μ with hB
  set Y : ℝ := ∫ p, vec3EuclideanNorm (responseVec g p) *
    ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2 ∂μ with hY
  set K : ℝ := criticalGNConstant with hK
  have hK0 : 0 ≤ K := criticalGNConstant_nonneg
  have hA50 : 0 ≤ A5 := integral_nonneg fun p =>
    Real.rpow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) _
  have hB0 : 0 ≤ B := integral_nonneg fun p => Real.rpow_nonneg
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) _
  have hY0 : 0 ≤ Y := integral_nonneg fun p => mul_nonneg (vec3EuclideanNorm_nonneg _)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hA := (response_rpow_five_le hg hgc hgpos hτ).2
  have hH := response_forcing_holder hg hgc hgpos hτ
  change A5 ≤ K * Y ^ (5 / 3 : ℝ) at hA
  change Y ≤ A5 ^ (1 / 5 : ℝ) * B ^ (4 / 5 : ℝ) at hH
  have hY53 : Y ^ (5 / 3 : ℝ) ≤ A5 ^ (1 / 3 : ℝ) * B ^ (4 / 3 : ℝ) := by
    calc
      Y ^ (5 / 3 : ℝ) ≤ (A5 ^ (1 / 5 : ℝ) * B ^ (4 / 5 : ℝ)) ^ (5 / 3 : ℝ) :=
        Real.rpow_le_rpow hY0 hH (by norm_num)
      _ = A5 ^ (1 / 3 : ℝ) * B ^ (4 / 3 : ℝ) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hA50,
          ← Real.rpow_mul hB0]
        norm_num
  have hA' : A5 ≤ K * (A5 ^ (1 / 3 : ℝ) * B ^ (4 / 3 : ℝ)) :=
    hA.trans (mul_le_mul_of_nonneg_left hY53 hK0)
  have hA5B : A5 ≤ K ^ (3 / 2 : ℝ) * B ^ 2 := by
    rcases hA50.eq_or_lt with h0 | hpos
    · rw [← h0]
      positivity
    · have hsplit : A5 = A5 ^ (1 / 3 : ℝ) * A5 ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_add hpos]
        norm_num
      have h13 : 0 < A5 ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hpos _
      have h23 : A5 ^ (2 / 3 : ℝ) ≤ K * B ^ (4 / 3 : ℝ) := by
        have h := hA'
        rw [hsplit] at h
        have h' : A5 ^ (1 / 3 : ℝ) * A5 ^ (2 / 3 : ℝ) ≤
            A5 ^ (1 / 3 : ℝ) * (K * B ^ (4 / 3 : ℝ)) := by
          calc
            A5 ^ (1 / 3 : ℝ) * A5 ^ (2 / 3 : ℝ) ≤
                K * ((A5 ^ (1 / 3 : ℝ) * A5 ^ (2 / 3 : ℝ)) ^ (1 / 3 : ℝ) *
                  B ^ (4 / 3 : ℝ)) := h
            _ = A5 ^ (1 / 3 : ℝ) * (K * B ^ (4 / 3 : ℝ)) := by
              rw [← hsplit]
              ring
        exact le_of_mul_le_mul_left h' h13
      calc
        A5 = (A5 ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
          rw [← Real.rpow_mul hA50]
          norm_num
        _ ≤ (K * B ^ (4 / 3 : ℝ)) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) h23 (by norm_num)
        _ = K ^ (3 / 2 : ℝ) * B ^ 2 := by
          rw [Real.mul_rpow hK0 (by positivity), ← Real.rpow_mul hB0]
          norm_num
  have hC32 : K ^ (3 / 2 : ℝ) ≤ criticalResponseConstant := by
    unfold criticalResponseConstant
    have : 0 ≤ 3 * criticalGNConstant ^ (3 / 10 : ℝ) := by positivity
    linarith only [this]
  have hC310 : 3 * K ^ (3 / 10 : ℝ) ≤ criticalResponseConstant := by
    unfold criticalResponseConstant
    have : 0 ≤ criticalGNConstant ^ (3 / 2 : ℝ) := by positivity
    linarith only [this]
  refine ⟨hA5B.trans (mul_le_mul_of_nonneg_right hC32 (sq_nonneg _)), ?_⟩
  intro t ht
  have h3 := response_rpow_three_le hg hgc hgpos hτ ht
  change _ ≤ 3 * Y at h3
  have hYB : Y ≤ K ^ (3 / 10 : ℝ) * B ^ (6 / 5 : ℝ) := by
    calc
      Y ≤ A5 ^ (1 / 5 : ℝ) * B ^ (4 / 5 : ℝ) := hH
      _ ≤ (K ^ (3 / 2 : ℝ) * B ^ 2) ^ (1 / 5 : ℝ) * B ^ (4 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hA50 hA5B (by norm_num)) (by positivity)
      _ = K ^ (3 / 10 : ℝ) * B ^ (6 / 5 : ℝ) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hK0,
          ← Real.rpow_natCast, ← Real.rpow_mul hB0, mul_assoc,
          ← Real.rpow_add' hB0 (by norm_num)]
        norm_num
  calc
    _ ≤ 3 * Y := h3
    _ ≤ 3 * (K ^ (3 / 10 : ℝ) * B ^ (6 / 5 : ℝ)) := by linarith only [hYB]
    _ = (3 * K ^ (3 / 10 : ℝ)) * B ^ (6 / 5 : ℝ) := by ring
    _ ≤ criticalResponseConstant * B ^ (6 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right hC310 (by positivity)

end ESS

end
