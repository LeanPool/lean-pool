/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.ScalesConcentration.TailAssembly

/-!
# Mgf

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Concentration for scale arrays — Step 3 (integer exponential moment)

This module assembles the per-column exponential-moment bound (`e.Zj.mgf.twosided`)

`E[e^{a Z_j}] ≤ 1 + C₃ (3/λ)^p 3^{-(sp/2) d_j}`,  `a = ⅛ (log 3) sp = mgfRate s p`,

from the Step-2 geometric tail (`Zj_tail`).  Because `Z_j ≤ m+1` is bounded,
the layer-cake sum is finite; the exponential moment is realized in `ℝ≥0∞` as
`∫⁻ (ofReal(e^a))^{Z_j}`, the exact quantity that enters `expZfun`.

The proof: pointwise `B^{Z} ≤ ∑_{n=0}^{N}(if n ≤ Z then B^n else 0)` (single term
domination), integrate to `1 + ∑_{n=1}^{N} B^n P[Z ≥ n]`, insert the tail, and
sum the resulting geometric series (`mgf_series_bound`).  The constant works out
to `C₂(1 + (1-3^{-1/8})⁻¹) ≤ C₃`, folding `(2·3^{s/4})^p ≤ 3^p`.
-/

namespace Algsuperdiff.Section4.Probability.ScalesConcentration

open MeasureTheory Finset
open scoped ENNReal NNReal

/-- Geometric sum with a truncated (`ℕ`) shift: `∑_{n=1}^N ρ^{n-2} ≤ 1 + (1-ρ)⁻¹`. -/
lemma geom_natsub_sum {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ρ ^ (n - 2) ≤ 1 + (1 - ρ)⁻¹ := by
  have hins : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1notin : (1 : ℕ) ∉ Finset.Icc 2 N := by simp
  rw [hins, Finset.sum_insert h1notin]
  have hfirst : ρ ^ (1 - 2) = 1 := by norm_num
  rw [hfirst]
  have hrest : ∑ n ∈ Finset.Icc 2 N, ρ ^ (n - 2) ≤ (1 - ρ)⁻¹ := by
    have hreindex : ∑ n ∈ Finset.Icc 2 N, ρ ^ (n - 2) = ∑ k ∈ Finset.range (N - 1), ρ ^ k := by
      rw [← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one,
        Finset.sum_Ico_eq_sum_range, show N + 1 - 2 = N - 1 by omega]
      exact Finset.sum_congr rfl (fun k _ => by congr 1; omega)
    rw [hreindex]
    calc ∑ k ∈ Finset.range (N - 1), ρ ^ k
        ≤ ∑' k : ℕ, ρ ^ k :=
          (summable_geometric_of_lt_one hρ0 hρ1).sum_le_tsum _ (fun k _ => pow_nonneg hρ0 k)
      _ = (1 - ρ)⁻¹ := tsum_geometric_of_lt_one hρ0 hρ1
  linarith

/-- The key numeric fact `2·3^{s/4} ≤ 3` for `s ≤ 1`. -/
lemma two_mul_rpow_quarter_le {s : ℝ} (hs1 : s ≤ 1) : 2 * (3 : ℝ) ^ (s / 4) ≤ 3 := by
  have hmono : (3 : ℝ) ^ (s / 4) ≤ (3 : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hval : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = 3 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by norm_num) _
  nlinarith [hmono, hval, hnn, sq_nonneg ((3 : ℝ) ^ ((1 : ℝ) / 4) - 3 / 2),
    sq_nonneg ((3 : ℝ) ^ ((1 : ℝ) / 4) + 3 / 2), sq_nonneg ((3 : ℝ) ^ ((1 : ℝ) / 4))]

/-- **Step-3 series bound.**  `∑_{n=1}^N e^{a n} 3^{-(sp/4)(n-2)₊} ≤ 3^{sp/4}(1+(1-3^{-1/8})⁻¹)`. -/
lemma mgf_series_bound {s p : ℝ} (hsp : 1 ≤ s * p) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, Real.exp (mgfRate s p) ^ n
        * (3 : ℝ) ^ (-(s * p / 4 * max ((n : ℝ) - 2) 0))
      ≤ (3 : ℝ) ^ (s * p / 4) * (1 + (1 - (3 : ℝ) ^ (-(1 / 8 : ℝ)))⁻¹) := by
  set u := s * p with hu
  have hu1 : 1 ≤ u := hsp
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu1
  have hb : Real.exp (mgfRate s p) = (3 : ℝ) ^ (u / 8) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    rw [mgfRate, hu]; ring
  have hρ1 : (3 : ℝ) ^ (-(u / 8)) < 1 := by
    rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).2 (by linarith)
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      Real.exp (mgfRate s p) ^ n * (3 : ℝ) ^ (-(s * p / 4 * max ((n : ℝ) - 2) 0))
        ≤ (3 : ℝ) ^ (u / 4) * ((3 : ℝ) ^ (-(u / 8))) ^ (n - 2) := by
    intro n hn'
    have hnge : 1 ≤ n := (Finset.mem_Icc.1 hn').1
    have hLexp : Real.exp (mgfRate s p) ^ n * (3 : ℝ) ^ (-(s * p / 4 * max ((n : ℝ) - 2) 0))
        = (3 : ℝ) ^ ((u / 8) * (n : ℝ) - u / 4 * max ((n : ℝ) - 2) 0) := by
      rw [hb, ← Real.rpow_natCast ((3 : ℝ) ^ (u / 8)) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤
        3),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
    have hRexp : (3 : ℝ) ^ (u / 4) * ((3 : ℝ) ^ (-(u / 8))) ^ (n - 2)
        = (3 : ℝ) ^ (u / 4 - (u / 8) * ((n - 2 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(u / 8))) (n - 2),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1; ring
    rw [hLexp, hRexp]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    rcases le_or_gt 2 n with h2 | h2
    · have h2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
      have hM : max ((n : ℝ) - 2) 0 = (n : ℝ) - 2 := by rw [max_eq_left]; linarith
      have hk : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_sub h2]; norm_num
      rw [hM, hk]; apply le_of_eq; ring
    · have hn1 : n = 1 := by omega
      subst hn1
      have hM : max (((1 : ℕ) : ℝ) - 2) 0 = 0 := by rw [max_eq_right]; norm_num
      have hk0 : ((1 - 2 : ℕ) : ℝ) = 0 := by norm_num
      rw [hM, hk0]; push_cast; linarith [hu0]
  calc ∑ n ∈ Finset.Icc 1 N, Real.exp (mgfRate s p) ^ n
          * (3 : ℝ) ^ (-(s * p / 4 * max ((n : ℝ) - 2) 0))
      ≤ ∑ n ∈ Finset.Icc 1 N, (3 : ℝ) ^ (u / 4) * ((3 : ℝ) ^ (-(u / 8))) ^ (n - 2) :=
        Finset.sum_le_sum hterm
    _ = (3 : ℝ) ^ (u / 4) * ∑ n ∈ Finset.Icc 1 N, ((3 : ℝ) ^ (-(u / 8))) ^ (n - 2) := by
        rw [Finset.mul_sum]
    _ ≤ (3 : ℝ) ^ (s * p / 4) * (1 + (1 - (3 : ℝ) ^ (-(1 / 8 : ℝ)))⁻¹) := by
        rw [← hu]
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
        have hgeo := geom_natsub_sum (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) hρ1 N hN
        have h38 : (3 : ℝ) ^ (-(u / 8)) ≤ (3 : ℝ) ^ (-(1 / 8 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        have hpos8 : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 / 8 : ℝ)) := one_sub_rpow_pos (by norm_num)
        have hinv : (1 - (3 : ℝ) ^ (-(u / 8)))⁻¹ ≤ (1 - (3 : ℝ) ^ (-(1 / 8 : ℝ)))⁻¹ :=
          inv_anti₀ hpos8 (by linarith)
        linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Step 3 exponential moment** (`e.Zj.mgf.twosided`).
`∫⁻ (ofReal(e^a))^{Z_j} ≤ ofReal(1 + C₃(3/λ)^p 3^{-(sp/2)d_j})`. -/
lemma Zj_mgf {X : ℤ → ℤ → Ω → ℝ} {s p lam : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hp : 1 ≤ p)
    (hsp : 1 ≤ s * p) (hlam : 0 < lam)
    (hXmeas : ∀ k j, Measurable (X k j))
    (hmomL : ∀ k j, ∫⁻ ω, ENNReal.ofReal ((X k j ω) ^ p) ∂P ≤ 1)
    (m : ℕ) (j : ℤ) (dj : ℕ)
    (hdj : ∀ k ∈ Finset.Icc (0 : ℤ) (m : ℤ), dj ≤ (k - j).natAbs) :
    ∫⁻ ω, (ENNReal.ofReal (Real.exp (mgfRate s p))) ^ (Zcount X s lam m j ω) ∂P
      ≤ ENNReal.ofReal (1 + C₃ * (3 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))) := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  set B := ENNReal.ofReal (Real.exp (mgfRate s p)) with hB
  set N := m + 1 with hN
  have hZle : ∀ ω, Zcount X s lam m j ω ≤ N := by
    intro ω
    rw [hN, Zcount]
    calc ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ), (if thr s lam k j < X k j ω then 1 else 0)
        ≤ ∑ _k ∈ Finset.Icc (0 : ℤ) (m : ℤ), 1 :=
          Finset.sum_le_sum (fun k _ => by split <;> simp)
      _ = m + 1 := by rw [Finset.sum_const, Int.card_Icc]; simp
  have hZmeas : Measurable (fun ω => Zcount X s lam m j ω) := by
    unfold Zcount
    refine Finset.measurable_sum _ (fun k _ => ?_)
    exact Measurable.ite (measurableSet_lt measurable_const (hXmeas k j))
      measurable_const measurable_const
  have hset : ∀ n : ℕ, MeasurableSet {ω | n ≤ Zcount X s lam m j ω} :=
    fun n => measurableSet_le measurable_const hZmeas
  -- pointwise domination by the finite layer-cake sum
  have hpt : ∀ ω, B ^ (Zcount X s lam m j ω)
      ≤ ∑ n ∈ Finset.Icc 0 N, (if n ≤ Zcount X s lam m j ω then B ^ n else 0) := by
    intro ω
    have hZmem : Zcount X s lam m j ω ∈ Finset.Icc 0 N :=
      Finset.mem_Icc.2 ⟨Nat.zero_le _, hZle ω⟩
    calc B ^ (Zcount X s lam m j ω)
        = (if Zcount X s lam m j ω ≤ Zcount X s lam m j ω
            then B ^ (Zcount X s lam m j ω) else 0) := by simp
      _ ≤ ∑ n ∈ Finset.Icc 0 N, (if n ≤ Zcount X s lam m j ω then B ^ n else 0) :=
          Finset.single_le_sum (f := fun n => if n ≤ Zcount X s lam m j ω then B ^ n else 0)
            (fun n _ => zero_le) hZmem
  -- integrate
  have hint_le : ∫⁻ ω, B ^ (Zcount X s lam m j ω) ∂P
      ≤ ∑ n ∈ Finset.Icc 0 N, B ^ n * P {ω | n ≤ Zcount X s lam m j ω} := by
    calc ∫⁻ ω, B ^ (Zcount X s lam m j ω) ∂P
        ≤ ∫⁻ ω, ∑ n ∈ Finset.Icc 0 N, (if n ≤ Zcount X s lam m j ω then B ^ n else 0) ∂P :=
          lintegral_mono (fun ω => hpt ω)
      _ = ∑ n ∈ Finset.Icc 0 N, ∫⁻ ω, (if n ≤ Zcount X s lam m j ω then B ^ n else 0) ∂P := by
          rw [lintegral_finsetSum]
          exact fun n _ => Measurable.ite (hset n) measurable_const measurable_const
      _ = ∑ n ∈ Finset.Icc 0 N, B ^ n * P {ω | n ≤ Zcount X s lam m j ω} := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          have hcong : ∫⁻ ω, (if n ≤ Zcount X s lam m j ω then B ^ n else 0) ∂P
              = ∫⁻ ω, B ^ n * Set.indicator {ω | n ≤ Zcount X s lam m j ω} 1 ω ∂P := by
            apply lintegral_congr
            intro ω
            rw [Set.indicator_apply]
            by_cases h : n ≤ Zcount X s lam m j ω <;> simp [h]
          rw [hcong, lintegral_const_mul _ (measurable_one.indicator (hset n)),
            lintegral_indicator_one (hset n)]
  -- split off n = 0
  have hsplit : ∑ n ∈ Finset.Icc 0 N, B ^ n * P {ω | n ≤ Zcount X s lam m j ω}
      = 1 + ∑ n ∈ Finset.Icc 1 N, B ^ n * P {ω | n ≤ Zcount X s lam m j ω} := by
    rw [show Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp)]
    congr 1
    simp only [pow_zero, one_mul]
    rw [show {ω | (0 : ℕ) ≤ Zcount X s lam m j ω} = (Set.univ : Set Ω) from by ext ω; simp]
    simp
  -- tail bound on the n ≥ 1 part
  have htail : ∑ n ∈ Finset.Icc 1 N, B ^ n * P {ω | n ≤ Zcount X s lam m j ω}
      ≤ ENNReal.ofReal (C₃ * (3 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))) := by
    -- per-term: B^n * P ≤ ofReal(e^{a n} * tail_n)
    have hpertermR : ∀ n, 1 ≤ n → B ^ n * P {ω | n ≤ Zcount X s lam m j ω}
        ≤ ENNReal.ofReal (Real.exp (mgfRate s p) ^ n
            * (C₂ * (2 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))
              * (3 : ℝ) ^ (-(s * p / 4 * max ((n : ℝ) - 2) 0)))) := by
      intro n hn1
      have htailn := Zj_tail (P := P) (X := X) hs hp hsp hlam hXmeas hmomL m j dj hdj n hn1
      have hBn : B ^ n = ENNReal.ofReal (Real.exp (mgfRate s p) ^ n) := by
        rw [hB, ← ENNReal.ofReal_pow (Real.exp_nonneg _)]
      calc B ^ n * P {ω | n ≤ Zcount X s lam m j ω}
          ≤ B ^ n * ENNReal.ofReal (C₂ * (2 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))
              * (3 : ℝ) ^ (-(s * p / 4 * max ((n : ℝ) - 2) 0))) :=
            mul_le_mul_right htailn _
        _ = ENNReal.ofReal (Real.exp (mgfRate s p) ^ n
              * (C₂ * (2 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))
                * (3 : ℝ) ^ (-(s * p / 4 * max ((n : ℝ) - 2) 0)))) := by
            rw [hBn, ← ENNReal.ofReal_mul (pow_nonneg (Real.exp_nonneg _) n)]
    -- sum the per-term bounds
    calc ∑ n ∈ Finset.Icc 1 N, B ^ n * P {ω | n ≤ Zcount X s lam m j ω}
        ≤ ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (Real.exp (mgfRate s p) ^ n
            * (C₂ * (2 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))
              * (3 : ℝ) ^ (-(s * p / 4 * max ((n : ℝ) - 2) 0)))) :=
          Finset.sum_le_sum (fun n hn => hpertermR n (Finset.mem_Icc.1 hn).1)
      _ = ENNReal.ofReal (∑ n ∈ Finset.Icc 1 N, Real.exp (mgfRate s p) ^ n
            * (C₂ * (2 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))
              * (3 : ℝ) ^ (-(s * p / 4 * max ((n : ℝ) - 2) 0)))) :=
          (ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (pow_nonneg (Real.exp_nonneg _) n)
            (mul_nonneg (mul_nonneg (mul_nonneg C₂_pos.le
              (Real.rpow_nonneg (div_nonneg (by norm_num) hlam.le) _))
              (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg (by norm_num) _)))).symm
      _ ≤ ENNReal.ofReal (C₃ * (3 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))) := by
          apply ENNReal.ofReal_le_ofReal
          -- factor out the constant, apply mgf_series_bound, fold
          have hfactor : ∑ n ∈ Finset.Icc 1 N, Real.exp (mgfRate s p) ^ n
              * (C₂ * (2 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))
                * (3 : ℝ) ^ (-(s * p / 4 * max ((n : ℝ) - 2) 0)))
              = (C₂ * (2 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ))))
                * ∑ n ∈ Finset.Icc 1 N, Real.exp (mgfRate s p) ^ n
                  * (3 : ℝ) ^ (-(s * p / 4 * max ((n : ℝ) - 2) 0)) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
          rw [hfactor]
          have hSbound := mgf_series_bound hsp N (by rw [hN]; omega)
          have h2lamnn : (0 : ℝ) ≤ (2 / lam) ^ p :=
            Real.rpow_nonneg (div_nonneg (by norm_num) hlam.le) _
          have h3lamnn : (0 : ℝ) ≤ (3 / lam) ^ p :=
            Real.rpow_nonneg (div_nonneg (by norm_num) hlam.le) _
          have h34nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ))) :=
            Real.rpow_nonneg (by norm_num) _
          have h14nn : (0 : ℝ) ≤ (3 : ℝ) ^ (s * p / 4) := Real.rpow_nonneg (by norm_num) _
          have hcnn : (0 : ℝ) ≤ C₂ * (2 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ))) :=
            mul_nonneg (mul_nonneg C₂_pos.le h2lamnn) h34nn
          -- fold (2/λ)^p 3^{sp/4} ≤ (3/λ)^p
          have hfold : (2 / lam) ^ p * (3 : ℝ) ^ (s * p / 4) ≤ (3 / lam) ^ p := by
            have hrw : (3 : ℝ) ^ (s * p / 4) = ((3 : ℝ) ^ (s / 4)) ^ p := by
              rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]; congr 1; ring
            rw [hrw, ← Real.mul_rpow (div_nonneg (by norm_num) hlam.le)
              (Real.rpow_nonneg (by norm_num) _)]
            apply Real.rpow_le_rpow (mul_nonneg (div_nonneg (by norm_num) hlam.le)
              (Real.rpow_nonneg (by norm_num) _)) _ hp0.le
            rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlam]
            nlinarith [two_mul_rpow_quarter_le hs1]
          -- C₂ K₁ ≤ C₃
          have hK1 : C₂ * (1 + (1 - (3 : ℝ) ^ (-(1 / 8 : ℝ)))⁻¹) ≤ C₃ := by
            rw [C₃]
            have hle1 : (1 : ℝ) - (3 : ℝ) ^ (-(1 / 8 : ℝ)) ≤ 1 := by
              have := Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) (-(1 / 8 : ℝ)); linarith
            have hr : (1 : ℝ) ≤ (1 - (3 : ℝ) ^ (-(1 / 8 : ℝ)))⁻¹ :=
              (one_le_inv₀ (one_sub_rpow_pos (by norm_num))).mpr hle1
            nlinarith [C₂_pos, hr]
          calc (C₂ * (2 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ))))
                * ∑ n ∈ Finset.Icc 1 N, Real.exp (mgfRate s p) ^ n
                    * (3 : ℝ) ^ (-(s * p / 4 * max ((n : ℝ) - 2) 0))
              ≤ (C₂ * (2 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ))))
                * ((3 : ℝ) ^ (s * p / 4) * (1 + (1 - (3 : ℝ) ^ (-(1 / 8 : ℝ)))⁻¹)) :=
                mul_le_mul_of_nonneg_left hSbound hcnn
            _ = (C₂ * (1 + (1 - (3 : ℝ) ^ (-(1 / 8 : ℝ)))⁻¹))
                  * ((2 / lam) ^ p * (3 : ℝ) ^ (s * p / 4))
                  * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ))) := by ring
            _ ≤ C₃ * (3 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ))) := by
                refine mul_le_mul (mul_le_mul hK1 hfold (mul_nonneg h2lamnn h14nn) C₃_pos.le)
                  (le_refl _) h34nn (mul_nonneg C₃_pos.le h3lamnn)
  -- assemble
  calc ∫⁻ ω, B ^ (Zcount X s lam m j ω) ∂P
      ≤ ∑ n ∈ Finset.Icc 0 N, B ^ n * P {ω | n ≤ Zcount X s lam m j ω} := hint_le
    _ = 1 + ∑ n ∈ Finset.Icc 1 N, B ^ n * P {ω | n ≤ Zcount X s lam m j ω} := hsplit
    _ ≤ 1 + ENNReal.ofReal (C₃ * (3 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))) :=
        add_le_add le_rfl htail
    _ = ENNReal.ofReal (1 + C₃ * (3 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))) := by
        rw [ENNReal.ofReal_add (by norm_num) (by have := C₃_pos.le; positivity)]
        simp

end Algsuperdiff.Section4.Probability.ScalesConcentration
