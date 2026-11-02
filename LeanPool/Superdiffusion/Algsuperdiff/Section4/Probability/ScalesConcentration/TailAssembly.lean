/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.ScalesConcentration.Tail
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.ScalesConcentration.Reduction

/-!
# TailAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Concentration for scale arrays — Step 2 assembly (`e.Zj.tail.twosided`)

This module assembles the geometric tail bound for a single column count `Z_j`
from the two kernels proved in `Tail.lean` (`shell_max`, `column_markov`):

`P[Z_j ≥ n] ≤ C₂ (2/λ)^p 3^{-(sp/2) d_j} 3^{-(sp/4)(n-2)₊}`  (`Zj_tail`),

for `n ≥ 1`, where `d_j = dist(j, {0,…,m})` enters through the hypothesis
`hdj : ∀ k ∈ Icc 0 m, d_j ≤ |k-j|`.  The proof is a finite union bound over the
"exceeding" rows (`measure_biUnion_finset_le`), per-row Markov (`column_markov`),
and the geometric regrouping of shells (`geom_shell_sum`, using the `≤ 2` members
per shell from `shell_max`'s hypothesis).

The moment input is the honest lintegral form
`hmomL : ∫⁻ ofReal((X k j)^p) ≤ 1`, exactly what `column_markov` consumes.

No independence is used here.
-/

namespace Algsuperdiff.Section4.Probability.ScalesConcentration

open MeasureTheory Finset
open scoped ENNReal NNReal

/-- At most two integers `k` sit at a given shell distance `ℓ` from `j`
(namely `j ± ℓ`). -/
lemma fiber_card_le_two (S : Finset ℤ) (j : ℤ) (ℓ : ℕ) :
    (S.filter (fun k => (k - j).natAbs = ℓ)).card ≤ 2 := by
  classical
  have hsub : S.filter (fun k => (k - j).natAbs = ℓ) ⊆ ({j - ℓ, j + ℓ} : Finset ℤ) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rcases Int.natAbs_eq_iff.1 hk.2 with h | h
    · have hk' : k = j + ℓ := by omega
      simp [hk']
    · have hk' : k = j - ℓ := by omega
      simp [hk']
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  simp

/-- **Geometric shell regrouping.**  For `q ∈ [0,1)`, a finite set `K` of
integers with at most two members per shell (`hfib`) and all shells `≥ L₀`
(`hL`), the sum `∑_{k∈K} q^{|k-j|}` is at most `2 q^{L₀}/(1-q)`. -/
lemma geom_shell_sum {j : ℤ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (K : Finset ℤ)
    (hfib : ∀ ℓ : ℕ, (K.filter (fun k => (k - j).natAbs = ℓ)).card ≤ 2)
    (L₀ : ℕ) (hL : ∀ k ∈ K, L₀ ≤ (k - j).natAbs) :
    ∑ k ∈ K, q ^ (k - j).natAbs ≤ 2 * q ^ L₀ / (1 - q) := by
  classical
  have h1q : (0 : ℝ) < 1 - q := by linarith
  rcases K.eq_empty_or_nonempty with hK | hK
  · subst hK; simp only [Finset.sum_empty]; positivity
  · set img := K.image (fun k => (k - j).natAbs) with himg
    have himgne : img.Nonempty := hK.image _
    -- fiberwise decomposition
    have hfiber : ∑ k ∈ K, q ^ (k - j).natAbs
        = ∑ ℓ ∈ img, (K.filter (fun k => (k - j).natAbs = ℓ)).card • q ^ ℓ := by
      rw [← Finset.sum_fiberwise_of_maps_to' (g := fun k => (k - j).natAbs) (t := img)
            (fun k hk => Finset.mem_image_of_mem _ hk) (fun ℓ => q ^ ℓ)]
      exact Finset.sum_congr rfl fun ℓ _ => Finset.sum_const _
    -- bound each fiber card by 2
    have hle2 : ∑ ℓ ∈ img, (K.filter (fun k => (k - j).natAbs = ℓ)).card • q ^ ℓ
        ≤ ∑ ℓ ∈ img, 2 * q ^ ℓ := by
      refine Finset.sum_le_sum fun ℓ _ => ?_
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib ℓ) (pow_nonneg hq0 ℓ)
    -- geometric bound on ∑ over the image
    have hgeom : ∑ ℓ ∈ img, q ^ ℓ ≤ q ^ L₀ * (1 - q)⁻¹ := by
      set M := img.max' himgne with hM
      have hsub : img ⊆ Finset.Ico L₀ (M + 1) := by
        intro ℓ hℓ
        rw [Finset.mem_Ico]
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hℓ
        exact ⟨hL k hk, by have := Finset.le_max' img _ hℓ; omega⟩
      calc ∑ ℓ ∈ img, q ^ ℓ
          ≤ ∑ ℓ ∈ Finset.Ico L₀ (M + 1), q ^ ℓ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ℓ _ _ => pow_nonneg hq0 ℓ)
        _ = ∑ i ∈ Finset.range (M + 1 - L₀), q ^ (L₀ + i) := Finset.sum_Ico_eq_sum_range _ _ _
        _ = q ^ L₀ * ∑ i ∈ Finset.range (M + 1 - L₀), q ^ i := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [pow_add]
        _ ≤ q ^ L₀ * (1 - q)⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0 L₀)
            calc ∑ i ∈ Finset.range (M + 1 - L₀), q ^ i
                ≤ ∑' i : ℕ, q ^ i :=
                  (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun i _ => pow_nonneg hq0 i)
              _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1
    calc ∑ k ∈ K, q ^ (k - j).natAbs
        = ∑ ℓ ∈ img, (K.filter (fun k => (k - j).natAbs = ℓ)).card • q ^ ℓ := hfiber
      _ ≤ ∑ ℓ ∈ img, 2 * q ^ ℓ := hle2
      _ = 2 * ∑ ℓ ∈ img, q ^ ℓ := by rw [Finset.mul_sum]
      _ ≤ 2 * (q ^ L₀ * (1 - q)⁻¹) := by
            exact mul_le_mul_of_nonneg_left hgeom (by norm_num)
      _ = 2 * q ^ L₀ / (1 - q) := by ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- **Step 2 tail bound** (`e.Zj.tail.twosided`).  For a single column `j` and
`n ≥ 1`,
`P[Z_j ≥ n] ≤ C₂ (2/λ)^p 3^{-(sp/2) d_j} 3^{-(sp/4)(n-2)₊}`. -/
lemma Zj_tail {X : ℤ → ℤ → Ω → ℝ} {s p lam : ℝ} (hs : 0 < s) (hp : 1 ≤ p)
    (hsp : 1 ≤ s * p) (hlam : 0 < lam)
    (hXmeas : ∀ k j, Measurable (X k j))
    (hmomL : ∀ k j, ∫⁻ ω, ENNReal.ofReal ((X k j ω) ^ p) ∂P ≤ 1)
    (m : ℕ) (j : ℤ) (dj : ℕ)
    (hdj : ∀ k ∈ Finset.Icc (0 : ℤ) (m : ℤ), dj ≤ (k - j).natAbs)
    (n : ℕ) (hn : 1 ≤ n) :
    P {ω | n ≤ Zcount X s lam m j ω}
      ≤ ENNReal.ofReal (C₂ * (2 / lam) ^ p
          * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))
          * (3 : ℝ) ^ (-(s * p / 4 * (max ((n : ℝ) - 2) 0)))) := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  set K := (Finset.Icc (0 : ℤ) (m : ℤ)).filter
    (fun k => 2 * dj + n ≤ 2 * (k - j).natAbs + 2) with hKdef
  -- Event inclusion into a finite union of per-row exceedances.
  have hincl : {ω | n ≤ Zcount X s lam m j ω}
      ⊆ ⋃ k ∈ K, {ω | thr s lam k j < X k j ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    set E := (Finset.Icc (0 : ℤ) (m : ℤ)).filter (fun k => thr s lam k j < X k j ω) with hE
    have hZcard : Zcount X s lam m j ω = E.card := by
      rw [Zcount, hE, Finset.card_filter]
    rw [hZcard] at hω
    have hEne : E.Nonempty := Finset.card_pos.1 (lt_of_lt_of_le hn hω)
    have hEsub : ∀ k ∈ E, dj ≤ (k - j).natAbs :=
      fun k hk => hdj k (Finset.mem_of_mem_filter k hk)
    have hEfib : ∀ ℓ : ℕ, (E.filter (fun k => (k - j).natAbs = ℓ)).card ≤ 2 :=
      fun ℓ => fiber_card_le_two E j ℓ
    obtain ⟨k, hkE, hk2⟩ := shell_max E hEne hEsub hEfib hω
    have hkIcc : k ∈ Finset.Icc (0 : ℤ) (m : ℤ) := Finset.mem_of_mem_filter k hkE
    have hkthr : thr s lam k j < X k j ω := (Finset.mem_filter.1 hkE).2
    have hkK : k ∈ K := by rw [hKdef]; exact Finset.mem_filter.2 ⟨hkIcc, hk2⟩
    exact Set.mem_biUnion hkK hkthr
  -- Per-row Markov bound.
  have hterm : ∀ k, P {ω | thr s lam k j < X k j ω}
      ≤ ENNReal.ofReal ((2 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * ((k - j).natAbs : ℝ)))) := by
    intro k
    have hthrpos : 0 < thr s lam k j := by
      rw [thr]; exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _)
    have hmk := column_markov (hXmeas k j) (hmomL k j) hp0 hthrpos
    refine hmk.trans (le_of_eq ?_)
    congr 1
    rw [thr, idist_eq,
      Real.mul_rpow (by linarith : (0 : ℝ) ≤ lam / 2) (Real.rpow_nonneg (by norm_num) _)]
    have hlam2 : (lam / 2) ^ (-p) = (2 / lam) ^ p := by
      rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ lam / 2),
        ← Real.inv_rpow (by linarith : (0 : ℝ) ≤ lam / 2), inv_div]
    rw [hlam2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      show s / 2 * ((k - j).natAbs : ℝ) * (-p) = -(s * p / 2 * ((k - j).natAbs : ℝ)) by ring]
  -- Geometric bound on the real sum over K.
  have hrealsum : ∑ k ∈ K, (3 : ℝ) ^ (-(s * p / 2 * ((k - j).natAbs : ℝ)))
      ≤ C₂ * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))
          * (3 : ℝ) ^ (-(s * p / 4 * (max ((n : ℝ) - 2) 0))) := by
    set c : ℝ := s * p / 2 with hc
    have hcpos : 0 < c := by rw [hc]; exact div_pos (mul_pos hs hp0) (by norm_num)
    set q : ℝ := (3 : ℝ) ^ (-c) with hq
    have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos (by norm_num) _).le
    have hq1 : q < 1 := by
      rw [hq, show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
      exact (Real.rpow_lt_rpow_left_iff (by norm_num)).2 (by linarith)
    have hconv : ∀ k : ℤ, (3 : ℝ) ^ (-(c * ((k - j).natAbs : ℝ))) = q ^ (k - j).natAbs := by
      intro k
      rw [hq, ← Real.rpow_natCast ((3 : ℝ) ^ (-c)) (k - j).natAbs,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1; ring
    -- The term in the goal equals q^{|k-j|}.
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ K) => hconv k)]
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · rw [hKe]; simp only [Finset.sum_empty]
      exact mul_nonneg (mul_nonneg C₂_pos.le (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (by norm_num) _)
    · -- L₀ = minimal shell in K
      set img := K.image (fun k => (k - j).natAbs) with himg
      have himgne : img.Nonempty := hKne.image _
      set L₀ := img.min' himgne with hL₀
      have hLmem : L₀ ∈ img := img.min'_mem himgne
      obtain ⟨k₀, hk₀K, hk₀⟩ := Finset.mem_image.1 hLmem
      have hLlow : ∀ k ∈ K, L₀ ≤ (k - j).natAbs :=
        fun k hk => img.min'_le _ (Finset.mem_image_of_mem _ hk)
      have hfibK : ∀ ℓ : ℕ, (K.filter (fun k => (k - j).natAbs = ℓ)).card ≤ 2 :=
        fun ℓ => fiber_card_le_two K j ℓ
      have hgeom := geom_shell_sum hq0 hq1 K hfibK L₀ hLlow
      -- Lower bound on L₀: L₀ ≥ dj + (n-2)₊/2.
      have hk₀mem : k₀ ∈ Finset.Icc (0 : ℤ) (m : ℤ) :=
        Finset.mem_of_mem_filter k₀ (by rw [hKdef] at hk₀K; exact hk₀K)
      have hk₀filt : 2 * dj + n ≤ 2 * (k₀ - j).natAbs + 2 := by
        rw [hKdef] at hk₀K; exact (Finset.mem_filter.1 hk₀K).2
      have hk₀dj : dj ≤ (k₀ - j).natAbs := hdj k₀ hk₀mem
      have hsp2 : (0 : ℝ) ≤ s * p / 2 := le_of_lt (div_pos (mul_pos hs hp0) (by norm_num))
      have hLbig : (dj : ℝ) + max ((n : ℝ) - 2) 0 / 2 ≤ (L₀ : ℝ) := by
        rw [← hk₀]
        rcases le_or_gt 2 (n : ℝ) with hn2 | hn2
        · have hmax : max ((n : ℝ) - 2) 0 = (n : ℝ) - 2 := by
            rw [max_eq_left]; linarith
          rw [hmax]
          have hAr : (2 * dj + n : ℝ) ≤ 2 * (k₀ - j).natAbs + 2 := by exact_mod_cast hk₀filt
          linarith
        · have hmax : max ((n : ℝ) - 2) 0 = 0 := by rw [max_eq_right]; linarith
          rw [hmax]
          have hBr : (dj : ℝ) ≤ (k₀ - j).natAbs := by exact_mod_cast hk₀dj
          linarith
      -- q^{L₀} ≤ 3^{-(sp/2)dj} 3^{-(sp/4)(n-2)₊}.
      have hqL : q ^ L₀ ≤ (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))
          * (3 : ℝ) ^ (-(s * p / 4 * (max ((n : ℝ) - 2) 0))) := by
        have hqLr : q ^ L₀ = (3 : ℝ) ^ (-(c * (L₀ : ℝ))) := by
          rw [hq, ← Real.rpow_natCast ((3 : ℝ) ^ (-c)) L₀,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
          congr 1; ring
        rw [hqLr, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        rw [hc]
        nlinarith [mul_le_mul_of_nonneg_left hLbig hsp2]
      -- constant 2/(1-q) ≤ C₂
      have hqhalf : q ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [hq]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        rw [hc]; linarith
      have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)) := one_sub_rpow_pos (by norm_num)
      have hdenle : (1 : ℝ) - (3 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 - q := by linarith
      have h1q : (0 : ℝ) < 1 - q := by linarith
      have hconst : 2 / (1 - q) ≤ C₂ := by
        rw [C₂, div_le_div_iff₀ h1q hden]
        linarith [hdenle, h1q]
      -- assemble
      calc ∑ k ∈ K, q ^ (k - j).natAbs
          ≤ 2 * q ^ L₀ / (1 - q) := hgeom
        _ = (2 / (1 - q)) * q ^ L₀ := by ring
        _ ≤ C₂ * ((3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))
              * (3 : ℝ) ^ (-(s * p / 4 * (max ((n : ℝ) - 2) 0)))) :=
            mul_le_mul hconst hqL (pow_nonneg hq0 L₀) C₂_pos.le
        _ = C₂ * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))
              * (3 : ℝ) ^ (-(s * p / 4 * (max ((n : ℝ) - 2) 0))) := by ring
  -- Assemble the measure bound.
  calc P {ω | n ≤ Zcount X s lam m j ω}
      ≤ P (⋃ k ∈ K, {ω | thr s lam k j < X k j ω}) := measure_mono hincl
    _ ≤ ∑ k ∈ K, P {ω | thr s lam k j < X k j ω} := measure_biUnion_finset_le K _
    _ ≤ ∑ k ∈ K, ENNReal.ofReal ((2 / lam) ^ p
          * (3 : ℝ) ^ (-(s * p / 2 * ((k - j).natAbs : ℝ)))) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = ENNReal.ofReal (∑ k ∈ K, (2 / lam) ^ p
          * (3 : ℝ) ^ (-(s * p / 2 * ((k - j).natAbs : ℝ)))) :=
        (ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)).symm
    _ = ENNReal.ofReal ((2 / lam) ^ p * ∑ k ∈ K,
          (3 : ℝ) ^ (-(s * p / 2 * ((k - j).natAbs : ℝ)))) := by rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal ((2 / lam) ^ p * (C₂ * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))
          * (3 : ℝ) ^ (-(s * p / 4 * (max ((n : ℝ) - 2) 0))))) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left hrealsum (by positivity)
    _ = ENNReal.ofReal (C₂ * (2 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dj : ℝ)))
          * (3 : ℝ) ^ (-(s * p / 4 * (max ((n : ℝ) - 2) 0)))) := by
        congr 1; ring

end Algsuperdiff.Section4.Probability.ScalesConcentration
