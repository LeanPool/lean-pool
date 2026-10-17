/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexSeparationCounting
public import Mathlib.Data.Nat.Find
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.GCongr

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.Foundation.Separation

open Filter

theorem scale_exists (K : ℕ) : ∃ n : ℕ, K ≤ 2 ^ (n ^ 2) := by
  refine ⟨K + 1, ?_⟩
  have hK : K < 2 ^ K := Nat.lt_pow_self (by decide : 1 < 2)
  exact hK.le.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))

noncomputable def gridScale (K : ℕ) : ℕ := Nat.find (scale_exists K)

theorem population_le_scale (K : ℕ) : K ≤ 2 ^ ((gridScale K) ^ 2) :=
  Nat.find_spec (scale_exists K)

theorem previous_scale_lt_population {K : ℕ} (hn : 0 < gridScale K) :
    2 ^ ((gridScale K - 1) ^ 2) < K := by
  exact lt_of_not_ge (Nat.find_min (scale_exists K) (Nat.sub_lt hn (by decide)))

theorem scale_pos {K : ℕ} (hK : 1 < K) : 0 < gridScale K := by
  have h := population_le_scale K
  by_contra hn
  have hz : gridScale K = 0 := Nat.eq_zero_of_not_pos hn
  simp only [hz, zero_pow (by decide : 2 ≠ 0), pow_zero] at h
  exact (not_le_of_gt hK) h

theorem scale_gt_of_population_gt {K n : ℕ} (hK : 2 ^ (n ^ 2) < K) :
    n < gridScale K := by
  by_contra hn
  have hscale : gridScale K ≤ n := Nat.le_of_not_gt hn
  have hp : 2 ^ ((gridScale K) ^ 2) ≤ 2 ^ (n ^ 2) :=
    Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left hscale 2)
  exact (not_le_of_gt hK) ((population_le_scale K).trans hp)

theorem gridScale_monotone : Monotone gridScale := by
  intro K L hKL
  exact Nat.find_min' (scale_exists K) (hKL.trans (population_le_scale L))

def gridDimension (K : ℕ) : ℕ := gridScale K + 4

def gridWidth (K : ℕ) : ℕ := 2 ^ (gridScale K + 2)

def gridGroupOrder (K : ℕ) : ℕ := (4 * gridWidth K) ^ gridDimension K

theorem gridDimension_pos (K : ℕ) : 0 < gridDimension K := by
  simp [gridDimension]

theorem gridWidth_ge_two (K : ℕ) : 2 ≤ gridWidth K := by
  simpa only [gridWidth, pow_one] using
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ gridScale K + 2))

private theorem dimension_le_power (n : ℕ) : n + 4 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 2 ^ (n + 2 + 1) = 2 ^ (n + 2) * 2 := pow_succ _ _
    have he : n + 1 + 2 = n + 2 + 1 := by omega
    rw [he, hp]
    omega

theorem grid_population_bound (K : ℕ) :
    (gridDimension K * gridWidth K ^ 2 + 1) * K ≤
      gridWidth K ^ gridDimension K := by
  let n := gridScale K
  have hd : n + 4 ≤ 2 ^ (n + 2) := dimension_le_power n
  have hq : 0 < 2 ^ (n + 2) := by positivity
  have hcolorpos : 0 < (n + 4) * (2 ^ (n + 2)) ^ 2 := by positivity
  have hcolor : (n + 4) * (2 ^ (n + 2)) ^ 2 + 1 ≤ 2 ^ (3 * n + 7) := by
    calc
      (n + 4) * (2 ^ (n + 2)) ^ 2 + 1 ≤
          2 * ((n + 4) * (2 ^ (n + 2)) ^ 2) := by nlinarith
      _ ≤ 2 * (2 ^ (n + 2) * (2 ^ (n + 2)) ^ 2) := by gcongr
      _ = 2 ^ (3 * n + 7) := by
        rw [← pow_mul, ← pow_add, ← pow_succ']
        congr 1
        omega
  calc
    (gridDimension K * gridWidth K ^ 2 + 1) * K ≤
        2 ^ (3 * n + 7) * 2 ^ (n ^ 2) :=
      Nat.mul_le_mul hcolor (population_le_scale K)
    _ = 2 ^ (3 * n + 7 + n ^ 2) := (pow_add _ _ _).symm
    _ ≤ 2 ^ ((n + 2) * (n + 4)) :=
      Nat.pow_le_pow_right (by decide) (by nlinarith)
    _ = gridWidth K ^ gridDimension K := by
      simp only [gridWidth, gridDimension, n, pow_mul]

theorem gridGroupOrder_eq (K : ℕ) :
    gridGroupOrder K = 2 ^ ((gridScale K + 4) ^ 2) := by
  unfold gridGroupOrder gridWidth gridDimension
  have hb : 4 * 2 ^ (gridScale K + 2) = 2 ^ (gridScale K + 4) := by
    calc
      4 * 2 ^ (gridScale K + 2) = 2 ^ 2 * 2 ^ (gridScale K + 2) := by norm_num
      _ = 2 ^ (2 + (gridScale K + 2)) := (pow_add _ _ _).symm
      _ = 2 ^ (gridScale K + 4) := by congr 1; omega
  rw [hb, ← pow_mul, pow_two]

theorem gridGroupOrder_pos (K : ℕ) : 0 < gridGroupOrder K := by
  rw [gridGroupOrder_eq]
  positivity

theorem population_le_gridGroupOrder (K : ℕ) : K ≤ gridGroupOrder K := by
  rw [gridGroupOrder_eq]
  exact (population_le_scale K).trans
    (Nat.pow_le_pow_right (by decide)
      (Nat.pow_le_pow_left (Nat.le_add_right (gridScale K) 4) 2))

theorem gridGroupOrder_monotone : Monotone gridGroupOrder := by
  intro K L hKL
  rw [gridGroupOrder_eq, gridGroupOrder_eq]
  exact Nat.pow_le_pow_right (by decide)
    (Nat.pow_le_pow_left (Nat.add_le_add_right (gridScale_monotone hKL) 4) 2)

theorem asymptotic_grid_tags_slices (K : ℕ) :
    ∃ tags : Finset (Grid (gridDimension K) (gridWidth K)), tags.card = K ∧
      (∃ radius : Fin (gridDimension K * gridWidth K ^ 2 + 1),
        ∀ t ∈ tags, normColor t = radius) ∧
      ∀ t ∈ tags, ∃ slice : Finset (Grid (gridDimension K) (gridWidth K)),
        slice.card = K ∧ ∃ level : Fin (gridDimension K * gridWidth K ^ 2 + 1),
          ∀ u ∈ slice, dotColor t u = level :=
  grid_tags_slices (grid_population_bound K) (grid_population_bound K)

theorem log_gridGroupOrder (K : ℕ) :
    Real.log (gridGroupOrder K : ℝ) = ((gridScale K : ℝ) + 4) ^ 2 * Real.log 2 := by
  rw [gridGroupOrder_eq, Nat.cast_pow, Real.log_pow]
  norm_cast

theorem log_population_le_log_gridGroupOrder {K : ℕ} (hK : 0 < K) :
    Real.log (K : ℝ) ≤ Real.log (gridGroupOrder K : ℝ) := by
  exact Real.log_le_log (by exact_mod_cast hK)
    (by exact_mod_cast population_le_gridGroupOrder K)

theorem previous_scale_log_lt {K : ℕ} (hK : 1 < K) :
    ((gridScale K : ℝ) - 1) ^ 2 * Real.log 2 < Real.log (K : ℝ) := by
  have hn : 1 ≤ gridScale K := scale_pos hK
  have hp : (0 : ℝ) < (2 : ℝ) ^ ((gridScale K - 1) ^ 2) := by positivity
  have hc : (2 : ℝ) ^ ((gridScale K - 1) ^ 2) < (K : ℝ) := by
    exact_mod_cast previous_scale_lt_population (scale_pos hK)
  have h := Real.log_lt_log hp hc
  simpa only [Real.log_pow, Nat.cast_pow, Nat.cast_sub hn, Nat.cast_one] using h

theorem log_gridGroupOrder_le_of_scale {K : ℕ} {ε : ℝ}
    (hK : 1 < K) (hε : 0 ≤ ε)
    (hscale : 10 * (gridScale K : ℝ) + 15 ≤
      ε * ((gridScale K : ℝ) - 1) ^ 2) :
    Real.log (gridGroupOrder K : ℝ) ≤ (1 + ε) * Real.log (K : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpoly : ((gridScale K : ℝ) + 4) ^ 2 ≤
      (1 + ε) * ((gridScale K : ℝ) - 1) ^ 2 := by nlinarith
  calc
    Real.log (gridGroupOrder K : ℝ) =
        ((gridScale K : ℝ) + 4) ^ 2 * Real.log 2 := log_gridGroupOrder K
    _ ≤ ((1 + ε) * ((gridScale K : ℝ) - 1) ^ 2) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hpoly hlog2.le
    _ = (1 + ε) * (((gridScale K : ℝ) - 1) ^ 2 * Real.log 2) := by ring
    _ ≤ (1 + ε) * Real.log (K : ℝ) :=
      mul_le_mul_of_nonneg_left (previous_scale_log_lt hK).le (by positivity)

private theorem scale_error_bound {n ε : ℝ} (hn : 2 ≤ n) (hε : 0 ≤ ε)
    (hlarge : 72 ≤ ε * n) : 10 * n + 15 ≤ ε * (n - 1) ^ 2 := by
  have hsq : n ^ 2 ≤ 4 * (n - 1) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hε
  have hlarge' := mul_le_mul_of_nonneg_right hlarge (by linarith : 0 ≤ n)
  nlinarith

theorem eventually_log_gridGroupOrder_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop,
      Real.log (gridGroupOrder K : ℝ) ≤ (1 + ε) * Real.log (K : ℝ) := by
  obtain ⟨m : ℕ, hm⟩ := exists_nat_gt (max 2 (72 / ε))
  refine eventually_atTop.2 ⟨2 ^ (m ^ 2) + 1, ?_⟩
  intro K hK
  have hKm : 2 ^ (m ^ 2) < K := by omega
  have hn := scale_gt_of_population_gt hKm
  have hnR : (m : ℝ) < (gridScale K : ℝ) := by exact_mod_cast hn
  have hm2 : 2 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmε : 72 / ε < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have hnε : 72 ≤ ε * (gridScale K : ℝ) := by
    have hdiv : 72 / ε < (gridScale K : ℝ) := hmε.trans hnR
    have hmul := (div_lt_iff₀ hε).1 hdiv
    nlinarith
  have hKone : 1 < K := by
    have hp : 1 ≤ 2 ^ (m ^ 2) := Nat.one_le_pow _ _ (by decide)
    omega
  exact log_gridGroupOrder_le_of_scale hKone hε.le
    (scale_error_bound (by linarith) hε.le hnε)

theorem uniform_log_gridGroupOrder_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ,
      Real.log (gridGroupOrder K : ℝ) ≤ (1 + ε) * Real.log (K : ℝ) + C := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (eventually_log_gridGroupOrder_le hε)
  refine ⟨Real.log (gridGroupOrder K₀ : ℝ), Real.log_natCast_nonneg _, ?_⟩
  intro K
  by_cases hK : K₀ ≤ K
  · exact (hK₀ K hK).trans (le_add_of_nonneg_right (Real.log_natCast_nonneg _))
  · have horder : gridGroupOrder K ≤ gridGroupOrder K₀ :=
      gridGroupOrder_monotone (Nat.le_of_lt (Nat.lt_of_not_ge hK))
    have hpos : (0 : ℝ) < (gridGroupOrder K : ℝ) := by
      rw [gridGroupOrder_eq, Nat.cast_pow]
      positivity
    have hcast : (gridGroupOrder K : ℝ) ≤ (gridGroupOrder K₀ : ℝ) := by
      exact_mod_cast horder
    have hlog := Real.log_le_log hpos hcast
    have hnonneg : 0 ≤ (1 + ε) * Real.log (K : ℝ) :=
      mul_nonneg (by linarith) (Real.log_natCast_nonneg K)
    linarith

theorem tendsto_log_gridGroupOrder_div_log_population :
    Tendsto (fun K : ℕ => Real.log (gridGroupOrder K : ℝ) / Real.log (K : ℝ))
      atTop (nhds 1) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    refine eventually_atTop.2 ⟨2, ?_⟩
    intro K hK
    have hKone : 1 < K := by omega
    have hlog : 0 < Real.log (K : ℝ) :=
      Real.log_pos (by exact_mod_cast hKone)
    have hle := log_population_le_log_gridGroupOrder (by omega : 0 < K)
    exact ha.trans_le ((le_div_iff₀ hlog).2 (by simpa using hle))
  · intro b hb
    have he : 0 < (b - 1) / 2 := by linarith
    filter_upwards [eventually_log_gridGroupOrder_le he,
      (eventually_atTop.2 ⟨2, fun K (hK : 2 ≤ K) => hK⟩)] with K hcost hK
    have hlog : 0 < Real.log (K : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < K by omega))
    have hratio : Real.log (gridGroupOrder K : ℝ) / Real.log (K : ℝ) ≤
        1 + (b - 1) / 2 := (div_le_iff₀ hlog).2 hcost
    linarith

theorem tendsto_log_gridGroupOrder_div_nat {K : ℕ → ℕ} {H : ℝ}
    (hK : ∀ N, 0 < K N) (hH : 0 ≤ H)
    (hpop : Tendsto (fun N => Real.log (K N : ℝ) / (N : ℝ)) atTop (nhds H)) :
    Tendsto (fun N => Real.log (gridGroupOrder (K N) : ℝ) / (N : ℝ))
      atTop (nhds H) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [(tendsto_order.1 hpop).1 a ha,
      (eventually_atTop.2 ⟨1, fun N (hN : 1 ≤ N) => hN⟩)] with N haN hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact haN.trans_le (div_le_div_of_nonneg_right
      (log_population_le_log_gridGroupOrder (hK N)) hNpos.le)
  · intro b hb
    let ε := (b - H) / (2 * (H + 1))
    have hdenom : 0 < 2 * (H + 1) := by linarith
    have hε : 0 < ε := div_pos (by linarith) hdenom
    obtain ⟨C, hC, hbound⟩ := uniform_log_gridGroupOrder_le hε
    have hεeq : ε * (2 * (H + 1)) = b - H := div_mul_cancel₀ _ hdenom.ne'
    have hlimitlt : (1 + ε) * H < b := by nlinarith
    have hconstant : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hupper : Tendsto
        (fun N : ℕ => (1 + ε) * (Real.log (K N : ℝ) / (N : ℝ)) + C / (N : ℝ))
        atTop (nhds ((1 + ε) * H)) := by
      simpa using (hpop.const_mul (1 + ε)).add hconstant
    filter_upwards [(tendsto_order.1 hupper).2 b hlimitlt,
      (eventually_atTop.2 ⟨1, fun N (hN : 1 ≤ N) => hN⟩)] with N hbN hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hle := div_le_div_of_nonneg_right (hbound (K N)) hNpos.le
    have heq : ((1 + ε) * Real.log (K N : ℝ) + C) / (N : ℝ) =
        (1 + ε) * (Real.log (K N : ℝ) / (N : ℝ)) + C / (N : ℝ) := by ring
    rw [heq] at hle
    exact hle.trans_lt hbN

theorem log_nat_prod {I : Type*} (s : Finset I) (a : I → ℕ)
    (ha : ∀ i ∈ s, 0 < a i) :
    Real.log ((∏ i ∈ s, a i : ℕ) : ℝ) = ∑ i ∈ s, Real.log (a i : ℝ) := by
  rw [Nat.cast_prod]
  exact Real.log_prod (s := s) (f := fun i => (a i : ℝ)) fun i hi =>
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (ha i hi))

theorem tendsto_log_nat_prod_div_nat {I : Type*} (s : Finset I)
    {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto (fun N => Real.log ((∏ i ∈ s, K i N : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, H i)) := by
  have hsum := tendsto_finsetSum s hpop
  apply hsum.congr
  intro N
  rw [log_nat_prod s (fun i => K i N) (fun i hi => hK i hi N)]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem tendsto_log_gridGroupOrder_prod_div_nat {I : Type*} (s : Finset I)
    {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N) (hH : ∀ i ∈ s, 0 ≤ H i)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto (fun N => Real.log ((∏ i ∈ s, gridGroupOrder (K i N) : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, H i)) := by
  exact tendsto_log_nat_prod_div_nat s (fun i hi N => gridGroupOrder_pos (K i N))
    (fun i hi => tendsto_log_gridGroupOrder_div_nat (hK i hi) (hH i hi) (hpop i hi))

theorem tendsto_log_nat_weighted_prod_div_nat {I : Type*} (s : Finset I) (w : I → ℕ)
    {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto (fun N => Real.log ((∏ i ∈ s, (K i N) ^ w i : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, (w i : ℝ) * H i)) := by
  apply tendsto_log_nat_prod_div_nat s
  · intro i hi N
    exact pow_pos (hK i hi N) _
  · intro i hi
    simpa only [Nat.cast_pow, Real.log_pow, mul_div_assoc] using
      (hpop i hi).const_mul (w i : ℝ)

theorem tendsto_log_gridGroupOrder_weighted_prod_div_nat {I : Type*}
    (s : Finset I) (w : I → ℕ) {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N) (hH : ∀ i ∈ s, 0 ≤ H i)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto
      (fun N => Real.log ((∏ i ∈ s, gridGroupOrder (K i N) ^ w i : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, (w i : ℝ) * H i)) := by
  exact tendsto_log_nat_weighted_prod_div_nat s w
    (fun i hi N => gridGroupOrder_pos (K i N))
    (fun i hi => tendsto_log_gridGroupOrder_div_nat (hK i hi) (hH i hi) (hpop i hi))

end MatrixMultiplication.Foundation.Separation

end

end MatrixMultiplicationAllFields
