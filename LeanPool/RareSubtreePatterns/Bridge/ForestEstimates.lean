/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Setup.Toolkit
public import LeanPool.RareSubtreePatterns.Bridge.Kemperman

import LeanPool.RareSubtreePatterns.RegularVariation.Karamata
import LeanPool.RareSubtreePatterns.RegularVariation.Consequences
import LeanPool.RareSubtreePatterns.Bienayme.Normalization

/-!
# Forest estimates: Lemma `lem:forest_estimates`

Work package WP2b of the bridge plan. Source lines 1119–1180 (Lemma 3.5 and its proof, inventory
L3.5, proof step P03), 1328–1342 (`P(|𝒯| = n) ≍ 1 / (n a_n)`, B11).

Notation: `𝒢_ℓ` is a forest of `ℓ` independent `μ`-Bienaymé trees, `P(|𝒢_ℓ| = q)` is
`(forestSizeWeight μ ℓ q).toReal`, `Ψ_m(x) = walkProb μ m x` (zero for negative time) and
`supWalk μ m = sup_x Ψ_m(x)`.

## Main statements

* `forestSizeWeight_toReal_le` / `forest_local_le` (local forest bound):
  `P(|𝒢_ℓ| = q) ≤ C ℓ / (q a_q)` for `q ≥ 1` (Kemperman's formula `natCast_mul_forestSizeWeight`
  and the global local bound `sup_le`); `tree_size_asymp`: `c / (n a_n) ≤ P(|𝒯| = n) ≤ C / (n a_n)`
  at admissible `n ≥ 1` (source line 1329).
* `forest_tail_le` (first estimate of Lemma 3.5): `P(|𝒢_ℓ| > m) ≤ C ℓ / a_m` for all `ℓ` and
  `m ≥ 1` (Karamata's tail bound).
* `forest_weighted_tail_sup_le` (second estimate, **numerator form**, corrections F3/F12 of the
  bridge plan): `E[sup_x Ψ_{N-|𝒢_ℓ|}(x) 1{|𝒢_ℓ| > m}] ≤ C ℓ / (a_m a_N)` for all `ℓ`, `m ≥ 1`
  and `N ≥ 2m`; `forest_weighted_tail_le` is the same bound for an arbitrary endpoint selector
  `e : ℕ → ℤ`; `forest_weighted_tail_div_le` is the paper's form, dividing by `Ψ_n(-1)` at an
  admissible `n`.
* ENNReal forms `forestSizeWeight_tail_le_ofReal`, `forestSizeWeight_weighted_tail_le_ofReal`
  used for the lintegral computations of `Bridge/Microscopic.lean`.

The paper states the estimates for `ℓ ≥ 1`; the empty forest `ℓ = 0` (`|𝒢_0| = 0`) is handled
separately here (`forestSizeWeight_zero_left`) and all bounds hold for every `ℓ`. In the periodic
case the paper's second estimate divides by `Ψ_n(-1)` and is later applied at times `n - c` where
`Ψ_{n-c}(-1)` may vanish; the numerator form avoids this (correction F3).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PoissonDeclumping.Bridge

open PlaneTree

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

/-! ### `sup_x Ψ_m(x)` -/

/-- `supWalk μ m = sup_x Ψ_m(x)` (zero for negative `m`). -/
noncomputable def supWalk (μ : PMF ℕ) (m : ℤ) : ℝ := ⨆ x : ℤ, walkProb μ m x

theorem bddAbove_range_walkProb (μ : PMF ℕ) (m : ℤ) : BddAbove (Set.range (walkProb μ m)) :=
  ⟨1, by rintro _ ⟨x, rfl⟩; exact walkProb_le_one μ m x⟩

theorem walkProb_le_supWalk (μ : PMF ℕ) (m x : ℤ) : walkProb μ m x ≤ supWalk μ m :=
  le_ciSup (bddAbove_range_walkProb μ m) x

theorem supWalk_nonneg (μ : PMF ℕ) (m : ℤ) : 0 ≤ supWalk μ m :=
  (walkProb_nonneg μ m 0).trans (walkProb_le_supWalk μ m 0)

theorem supWalk_le_one (μ : PMF ℕ) (m : ℤ) : supWalk μ m ≤ 1 :=
  ciSup_le fun x => walkProb_le_one μ m x

theorem supWalk_of_neg (μ : PMF ℕ) {m : ℤ} (hm : m < 0) : supWalk μ m = 0 := by
  simp [supWalk, walkProb_of_neg μ hm]

/-- `sup_x Ψ_m(x) ≤ C / a_m` for every `m ≥ 1` (field `sup_le`). -/
theorem exists_supWalk_le (hT : StableToolkit μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → supWalk μ m ≤ C / a m := by
  obtain ⟨C, hC⟩ := hT.sup_le
  refine ⟨max C 0, le_max_right _ _, fun m hm => ciSup_le fun x => ?_⟩
  exact (hC m hm x).trans (by gcongr; exacts [(hT.pos m hm).le, le_max_left _ _])

/-- `sup_x Ψ_m(x) ≤ C / a_n` whenever `n ≤ 2m` (`exists_le_div_of_le_two_mul`). -/
theorem exists_supWalk_le_of_le_two_mul (hT : StableToolkit μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → n ≤ 2 * m → supWalk μ m ≤ C / a n := by
  obtain ⟨C, hC0, hC⟩ := hT.exists_le_div_of_le_two_mul
  exact ⟨C, hC0, fun n m hn hm hnm => ciSup_le fun x => hC n m hn hm hnm x⟩

/-! ### The empty forest and total masses -/

/-- The empty forest has `0` vertices: `P(|𝒢_0| = q) = 1{q = 0}`. -/
theorem forestSizeWeight_zero_left (μ : PMF ℕ) (q : ℕ) :
    forestSizeWeight μ 0 q = if q = 0 then 1 else 0 := by
  rw [forestSizeWeight, tsum_eq_single (fun i : Fin 0 => i.elim0)]
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty]
    by_cases hq : q = 0
    · simp [hq]
    · rw [ite_eq_right (Ne.symm hq), ite_eq_right hq]
  · intro f hf
    exact absurd (funext fun i => i.elim0) hf

theorem tsum_forestSizeWeight_le_one (μ : PMF ℕ) (ℓ : ℕ) : ∑' q, forestSizeWeight μ ℓ q ≤ 1 := by
  rw [tsum_forestSizeWeight]
  exact pow_le_one₀ zero_le (bienayme_univ_le_one μ)

theorem summable_forestSizeWeight_toReal (μ : PMF ℕ) (ℓ : ℕ) :
    Summable (fun q => (forestSizeWeight μ ℓ q).toReal) :=
  ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
    (tsum_forestSizeWeight_le_one μ ℓ))

/-! ### Local bounds -/

/-- **Local forest bound** (source lines 1137–1141): there is `C ≥ 0` with
`P(|𝒢_ℓ| = q) ≤ C ℓ / (q a_q)` for all `ℓ` and all `q ≥ 1`. -/
theorem forestSizeWeight_toReal_le (hT : StableToolkit μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ q : ℕ, 1 ≤ q →
      (forestSizeWeight μ ℓ q).toReal ≤ C * ℓ / (q * a q) := by
  obtain ⟨C, hC⟩ := hT.sup_le
  refine ⟨max C 0, le_max_right _ _, fun ℓ q hq => ?_⟩
  have haq : 0 < a q := hT.pos q hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · rw [forestSizeWeight_zero_left, ite_eq_right (by omega)]
    simp
  · rw [forestSizeWeight_toReal_eq μ hℓ hq]
    have h1 : walkProb μ q (-ℓ) ≤ max C 0 / a q :=
      (hC q hq _).trans (by gcongr; exact le_max_left _ _)
    calc (ℓ : ℝ) / q * walkProb μ q (-ℓ) ≤ ℓ / q * (max C 0 / a q) := by gcongr
      _ = max C 0 * ℓ / (q * a q) := by field_simp

/-- **Lemma `lem:forest_estimates`, local form** (plan WP2b.4): one `C` with
`P(|𝒢_ℓ| = N) ≤ C ℓ / (N a_N)` for `ℓ, N ≥ 1`. -/
theorem forest_local_le (hT : StableToolkit μ α a) :
    ∃ C : ℝ, ∀ ℓ N : ℕ, 1 ≤ ℓ → 1 ≤ N →
      (forestSizeWeight μ ℓ N).toReal ≤ C * ℓ / (N * a N) := by
  obtain ⟨C, -, hC⟩ := forestSizeWeight_toReal_le hT
  exact ⟨C, fun ℓ N _ hN => hC ℓ N hN⟩

/-- **`P(|𝒯| = n) ≍ 1 / (n a_n)` along admissible sizes** (source line 1329, B11): one pair
`c > 0`, `C` with `c / (n a_n) ≤ P(|𝒯| = n) ≤ C / (n a_n)` at every admissible `n ≥ 1`. -/
theorem tree_size_asymp (hT : StableToolkit μ α a) :
    ∃ c C : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → Admissible μ n →
      c / (n * a n) ≤ (bienayme μ).real {T | T.vertexCount = n} ∧
        (bienayme μ).real {T | T.vertexCount = n} ≤ C / (n * a n) := by
  obtain ⟨c, hc, hlow⟩ := hT.exists_lower_bound_neg_one
  obtain ⟨C, hC⟩ := hT.sup_le
  refine ⟨c, C, hc, fun n hn hadm => ?_⟩
  have han : 0 < a n := hT.pos n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hψ : 0 < walkProb μ n (-1) := (walkProb_neg_one_pos_iff μ n).2 hadm
  have hD := walkProb_neg_one μ n
  have h1 := hlow n hn hψ
  have h2 := hC n hn (-1)
  rw [hD] at h1 h2
  constructor
  · rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ han] at h1
    nlinarith
  · rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ han] at h2
    nlinarith

/-! ### The forest-size tail (first estimate of Lemma 3.5) -/

/-- **Lemma `lem:forest_estimates`, first estimate** (source lines 1124–1148): one `C` with
`P(|𝒢_ℓ| > m) ≤ C ℓ / a_m` for every `ℓ` and every `m ≥ 1`. -/
theorem forest_tail_le (hT : StableToolkit μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ m : ℕ, 1 ≤ m →
      ∑' q, (Set.Ioi m).indicator (fun q => (forestSizeWeight μ ℓ q).toReal) q ≤ C * ℓ / a m := by
  obtain ⟨C₀, hC₀, hloc⟩ := forestSizeWeight_toReal_le hT
  obtain ⟨K, hK, hKt⟩ := hT.regularlyVarying.karamata_tail_tsum hT.monotone hT.pos hT.rho_pos
  have hsum := hT.regularlyVarying.summable_inv_mul hT.monotone hT.pos hT.rho_pos
  refine ⟨C₀ * K, by positivity, fun ℓ m hm => ?_⟩
  have ham : 0 < a m := hT.pos m hm
  have hle : ∀ q, (Set.Ioi m).indicator (fun q => (forestSizeWeight μ ℓ q).toReal) q ≤
      (C₀ * ℓ) * (Set.Ioi m).indicator (fun q : ℕ => 1 / ((q : ℝ) * a q)) q := by
    intro q
    by_cases hq : q ∈ Set.Ioi m
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      have hq1 : 1 ≤ q := by have := Set.mem_Ioi.1 hq; omega
      calc (forestSizeWeight μ ℓ q).toReal ≤ C₀ * ℓ / (q * a q) := hloc ℓ q hq1
        _ = C₀ * ℓ * (1 / (q * a q)) := by ring
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, mul_zero]
  have hs2 : Summable fun q => (C₀ * ℓ) *
      (Set.Ioi m).indicator (fun q : ℕ => 1 / ((q : ℝ) * a q)) q :=
    (hsum.indicator _).mul_left _
  have hs1 : Summable fun q =>
      (Set.Ioi m).indicator (fun q => (forestSizeWeight μ ℓ q).toReal) q :=
    (summable_forestSizeWeight_toReal μ ℓ).indicator _
  calc ∑' q, (Set.Ioi m).indicator (fun q => (forestSizeWeight μ ℓ q).toReal) q
      ≤ ∑' q, (C₀ * ℓ) * (Set.Ioi m).indicator (fun q : ℕ => 1 / ((q : ℝ) * a q)) q :=
        hs1.tsum_le_tsum hle hs2
    _ = (C₀ * ℓ) * ∑' q, (Set.Ioi m).indicator (fun q : ℕ => 1 / ((q : ℝ) * a q)) q :=
        tsum_mul_left
    _ ≤ (C₀ * ℓ) * (K / a m) := by gcongr; exact hKt m hm
    _ = C₀ * K * ℓ / a m := by ring

/-! ### The bridge-weighted tail (second estimate of Lemma 3.5, numerator form) -/

/-- **Lemma `lem:forest_estimates`, second estimate, numerator form** (source lines 1149–1179,
corrections F3/F12): one `C` such that for all `ℓ`, all `m ≥ 1` and all `N ≥ 2m`,
`E[sup_x Ψ_{N-|𝒢_ℓ|}(x) 1{|𝒢_ℓ| > m}] ≤ C ℓ / (a_m a_N)`. The sum is split at `q = N/2`: for
`q ≤ N/2`, `sup_x Ψ_{N-q} ≤ C / a_N`; for `N/2 < q ≤ N`, `P(|𝒢_ℓ| = q) ≤ C ℓ / (N a_N)` and
`∑_{h ≤ N} sup_x Ψ_h ≤ 1 + C N / a_N` (Karamata; the term `h = 0` is `Ψ_0(0) = 1`); `q > N`
contributes nothing. -/
theorem forest_weighted_tail_sup_le (hT : StableToolkit μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ m N : ℕ, 1 ≤ m → 2 * m ≤ N →
      ∑' q, (Set.Ioi m).indicator
        (fun q => (forestSizeWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q ≤
        C * ℓ / (a m * a N) := by
  obtain ⟨C₀, hC₀, hloc⟩ := forestSizeWeight_toReal_le hT
  obtain ⟨C₁, hC₁, hsup2⟩ := exists_supWalk_le_of_le_two_mul hT
  obtain ⟨S₀, hS₀, hsup⟩ := exists_supWalk_le hT
  obtain ⟨C₂, hC₂, htail⟩ := forest_tail_le hT
  obtain ⟨C₃, hC₃, hcomp⟩ := hT.regularlyVarying.exists_le_mul_of_le_mul hT.monotone hT.pos
    hT.rho_pos.le 2
  obtain ⟨C₄, hC₄, hkar⟩ := hT.regularlyVarying.karamata_sum hT.monotone hT.pos hT.rho_pos.le
    hT.rho_lt_one
  obtain ⟨C₅, hC₅, hlin⟩ := hT.regularlyVarying.exists_le_mul hT.monotone hT.pos hT.rho_pos.le
    hT.rho_lt_one
  set K : ℝ := 2 * C₀ * C₃ with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨C₁ * C₂ + K * C₅ + K * S₀ * C₄, by positivity, fun ℓ m N hm hmN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have ham : 0 < a m := hT.pos m hm
  have haN : 0 < a N := hT.pos N hN1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hamN : a m ≤ a N := hT.monotone (by omega)
  have hℓ : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  -- the comparison function `g h ≥ sup_x Ψ_h`
  set g : ℕ → ℝ := fun h => if h = 0 then 1 else S₀ / a h with hgdef
  have hg0 : ∀ h, 0 ≤ g h := by
    intro h
    simp only [hgdef]
    split_ifs with hh
    · exact zero_le_one
    · exact div_nonneg hS₀ (hT.pos h (by omega)).le
  have hsupg : ∀ h : ℕ, supWalk μ h ≤ g h := by
    intro h
    simp only [hgdef]
    split_ifs with hh
    · exact supWalk_le_one μ _
    · exact hsup h (by omega)
  set F : ℕ → ℝ := (Set.Ioi m).indicator (fun q => (forestSizeWeight μ ℓ q).toReal) with hFdef
  set B : ℕ → ℝ := fun q => if q ≤ N then g (N - q) else 0 with hBdef
  have hF0 : ∀ q, 0 ≤ F q := fun q => Set.indicator_nonneg (fun q _ => ENNReal.toReal_nonneg) q
  have hB0 : ∀ q, 0 ≤ B q := by
    intro q
    simp only [hBdef]
    split_ifs
    · exact hg0 _
    · exact le_rfl
  have hFs : Summable F := (summable_forestSizeWeight_toReal μ ℓ).indicator _
  have hBs : Summable B := by
    refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun q hq => ?_
    simp only [hBdef]
    rw [ite_eq_right]
    intro hqN
    exact absurd (Finset.mem_range.2 (by omega)) hq
  -- termwise domination
  have hterm : ∀ q, (Set.Ioi m).indicator
      (fun q => (forestSizeWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q ≤
      C₁ / a N * F q + K * ℓ / (N * a N) * B q := by
    intro q
    have hr1 : 0 ≤ C₁ / a N * F q := mul_nonneg (by positivity) (hF0 q)
    have hr2 : 0 ≤ K * ℓ / (N * a N) * B q := mul_nonneg (by positivity) (hB0 q)
    by_cases hq : q ∈ Set.Ioi m
    · rw [Set.indicator_of_mem hq]
      have hqm : m < q := hq
      have hq1 : 1 ≤ q := by omega
      have hfq0 : 0 ≤ (forestSizeWeight μ ℓ q).toReal := ENNReal.toReal_nonneg
      rcases le_or_gt q N with hqN | hqN
      · have hcast : (N : ℤ) - q = ((N - q : ℕ) : ℤ) := by push_cast [hqN]; ring
        rw [hcast]
        rcases le_or_gt (2 * q) N with h2q | h2q
        · -- `q ≤ N / 2`: `sup_x Ψ_{N-q} ≤ C₁ / a_N`
          have hs := hsup2 N (N - q) hN1 (by omega) (by omega)
          have hFq : F q = (forestSizeWeight μ ℓ q).toReal := by
            rw [hFdef, Set.indicator_of_mem hq]
          calc (forestSizeWeight μ ℓ q).toReal * supWalk μ ((N - q : ℕ) : ℤ)
              ≤ (forestSizeWeight μ ℓ q).toReal * (C₁ / a N) := by gcongr
            _ = C₁ / a N * F q := by rw [hFq]; ring
            _ ≤ _ := le_add_of_nonneg_right hr2
        · -- `N / 2 < q ≤ N`
          have haq : 0 < a q := hT.pos q hq1
          have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
          have hNq : a N ≤ C₃ * a q := hcomp q N hq1 (by exact_mod_cast h2q.le)
          have hf : (forestSizeWeight μ ℓ q).toReal ≤ K * ℓ / (N * a N) := by
            calc (forestSizeWeight μ ℓ q).toReal ≤ C₀ * ℓ / (q * a q) := hloc ℓ q hq1
              _ ≤ K * ℓ / (N * a N) := by
                rw [div_le_div_iff₀ (by positivity) (by positivity), hKdef]
                have h2 : (N : ℝ) ≤ 2 * q := by exact_mod_cast h2q.le
                have : (N : ℝ) * a N ≤ 2 * q * (C₃ * a q) :=
                  mul_le_mul h2 hNq haN.le (by positivity)
                nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ C₀ * ℓ by positivity)]
          have hBq : B q = g (N - q) := by simp only [hBdef]; rw [ite_eq_left hqN]
          calc (forestSizeWeight μ ℓ q).toReal * supWalk μ ((N - q : ℕ) : ℤ)
              ≤ K * ℓ / (N * a N) * g (N - q) :=
                mul_le_mul hf (hsupg _) (supWalk_nonneg μ _) (by positivity)
            _ = K * ℓ / (N * a N) * B q := by rw [hBq]
            _ ≤ _ := le_add_of_nonneg_left hr1
      · rw [supWalk_of_neg μ (by omega), mul_zero]
        exact add_nonneg hr1 hr2
    · rw [Set.indicator_of_notMem hq]
      exact add_nonneg hr1 hr2
  -- the two sums
  have hsumB : ∑' q, B q ≤ 1 + S₀ * C₄ * N / a N := by
    rw [tsum_eq_sum (s := Finset.range (N + 1)) fun q hq => by
      simp only [hBdef]
      rw [ite_eq_right]
      intro hqN
      exact absurd (Finset.mem_range.2 (by omega)) hq]
    have h1 : ∑ q ∈ Finset.range (N + 1), B q = ∑ h ∈ Finset.range (N + 1), g h := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hq' := Finset.mem_range.1 hq
      simp only [hBdef]
      rw [ite_eq_left (by omega)]
      congr 1
      omega
    rw [h1, Finset.sum_range_succ', Finset.range_eq_Ico]
    have h2 : ∑ h ∈ Finset.Ico 0 N, g (h + 1) = ∑ h ∈ Finset.Icc 1 N, S₀ / a h := by
      rw [Finset.sum_Ico_add' (c := 1), zero_add, Finset.Ico_add_one_right_eq_Icc]
      refine Finset.sum_congr rfl fun h hh => ?_
      have := (Finset.mem_Icc.1 hh).1
      simp only [hgdef]
      rw [ite_eq_right (by omega)]
    have h3 : ∑ h ∈ Finset.Icc 1 N, S₀ / a h = S₀ * ∑ h ∈ Finset.Icc 1 N, 1 / a h := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => by ring
    rw [h2, h3]
    have hg00 : g 0 = 1 := by simp [hgdef]
    rw [hg00]
    have := hkar N
    have h4 : S₀ * ∑ h ∈ Finset.Icc 1 N, 1 / a h ≤ S₀ * (C₄ * N / a N) :=
      mul_le_mul_of_nonneg_left this hS₀
    calc S₀ * ∑ h ∈ Finset.Icc 1 N, 1 / a h + 1 ≤ S₀ * (C₄ * N / a N) + 1 := by linarith
      _ = 1 + S₀ * C₄ * N / a N := by ring
  have hsumF : ∑' q, F q ≤ C₂ * ℓ / a m := htail ℓ m hm
  have hs_lhs : Summable fun q => (Set.Ioi m).indicator
      (fun q => (forestSizeWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q := by
    refine Summable.of_nonneg_of_le (fun q => ?_) hterm ((hFs.mul_left _).add (hBs.mul_left _))
    exact Set.indicator_nonneg (fun q _ => mul_nonneg ENNReal.toReal_nonneg
      (supWalk_nonneg μ _)) q
  calc ∑' q, (Set.Ioi m).indicator
        (fun q => (forestSizeWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q
      ≤ ∑' q, (C₁ / a N * F q + K * ℓ / (N * a N) * B q) :=
        hs_lhs.tsum_le_tsum hterm ((hFs.mul_left _).add (hBs.mul_left _))
    _ = C₁ / a N * ∑' q, F q + K * ℓ / (N * a N) * ∑' q, B q := by
        rw [(hFs.mul_left _).tsum_add (hBs.mul_left _), tsum_mul_left, tsum_mul_left]
    _ ≤ C₁ / a N * (C₂ * ℓ / a m) + K * ℓ / (N * a N) * (1 + S₀ * C₄ * N / a N) := by
        gcongr
    _ ≤ (C₁ * C₂ + K * C₅ + K * S₀ * C₄) * ℓ / (a m * a N) := by
        have hlinN : a m ≤ C₅ * N := hamN.trans (hlin N hN1)
        have e1 : C₁ / a N * (C₂ * ℓ / a m) = C₁ * C₂ * ℓ / (a m * a N) := by
          field_simp
        have e2 : K * ℓ / (N * a N) * 1 ≤ K * C₅ * ℓ / (a m * a N) := by
          rw [mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
          have : K * ℓ * (a m * a N) ≤ K * ℓ * (C₅ * N * a N) := by gcongr
          nlinarith
        have e3 : K * ℓ / (N * a N) * (S₀ * C₄ * N / a N) ≤ K * S₀ * C₄ * ℓ / (a m * a N) := by
          have : K * ℓ / (N * a N) * (S₀ * C₄ * N / a N) = K * S₀ * C₄ * ℓ / (a N * a N) := by
            field_simp
          rw [this]
          gcongr
        calc C₁ / a N * (C₂ * ℓ / a m) + K * ℓ / (N * a N) * (1 + S₀ * C₄ * N / a N)
            = C₁ / a N * (C₂ * ℓ / a m) + K * ℓ / (N * a N) * 1 +
              K * ℓ / (N * a N) * (S₀ * C₄ * N / a N) := by ring
          _ ≤ C₁ * C₂ * ℓ / (a m * a N) + K * C₅ * ℓ / (a m * a N) +
              K * S₀ * C₄ * ℓ / (a m * a N) := by rw [e1]; gcongr
          _ = _ := by ring

/-- **Lemma `lem:forest_estimates`, second estimate, numerator form with an endpoint selector**
(plan WP2b.2): one `C` such that for all `ℓ`, `m ≥ 1`, `N ≥ 2m` and every `e : ℕ → ℤ`,
`∑_{q > m} P(|𝒢_ℓ| = q) Ψ_{N-q}(e q) ≤ C ℓ / (a_m a_N)` (the selector `e` encodes `sup_x`). -/
theorem forest_weighted_tail_le (hT : StableToolkit μ α a) :
    ∃ C : ℝ, ∀ ℓ m N : ℕ, 1 ≤ m → 2 * m ≤ N → ∀ e : ℕ → ℤ,
      ∑' q, (Set.Ioi m).indicator
        (fun q => (forestSizeWeight μ ℓ q).toReal * walkProb μ ((N : ℤ) - q) (e q)) q ≤
        C * ℓ / (a m * a N) := by
  obtain ⟨C, -, hC⟩ := forest_weighted_tail_sup_le hT
  refine ⟨C, fun ℓ m N hm hmN e => ?_⟩
  have hle : ∀ q, (Set.Ioi m).indicator
      (fun q => (forestSizeWeight μ ℓ q).toReal * walkProb μ ((N : ℤ) - q) (e q)) q ≤
      (Set.Ioi m).indicator
        (fun q => (forestSizeWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q :=
    fun q => Set.indicator_le_indicator
      (mul_le_mul_of_nonneg_left (walkProb_le_supWalk μ _ _) ENNReal.toReal_nonneg)
  have hs2 : Summable fun q => (Set.Ioi m).indicator
      (fun q => (forestSizeWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q :=
    Summable.of_nonneg_of_le
      (fun q => Set.indicator_nonneg (fun q _ => mul_nonneg ENNReal.toReal_nonneg
        (supWalk_nonneg μ _)) q)
      (fun q => Set.indicator_le_indicator
        (mul_le_of_le_one_right ENNReal.toReal_nonneg (supWalk_le_one μ _)))
      ((summable_forestSizeWeight_toReal μ ℓ).indicator _)
  have hs1 : Summable fun q => (Set.Ioi m).indicator
      (fun q => (forestSizeWeight μ ℓ q).toReal * walkProb μ ((N : ℤ) - q) (e q)) q :=
    Summable.of_nonneg_of_le
      (fun q => Set.indicator_nonneg (fun q _ => mul_nonneg ENNReal.toReal_nonneg
        (walkProb_nonneg μ _ _)) q) hle hs2
  exact (hs1.tsum_le_tsum hle hs2).trans (hC ℓ m N hm hmN)

/-- **Lemma `lem:forest_estimates`, second estimate, the paper's form** (source lines 1127–1132):
one `C` such that for all `ℓ`, `m ≥ 1`, admissible `n ≥ 2m` and every `e : ℕ → ℤ`,
`Ψ_n(-1)⁻¹ E[Ψ_{n-|𝒢_ℓ|}(e |𝒢_ℓ|) 1{|𝒢_ℓ| > m}] ≤ C ℓ / a_m` (`Ψ_n(-1) ≥ c / a_n`). -/
theorem forest_weighted_tail_div_le (hT : StableToolkit μ α a) :
    ∃ C : ℝ, ∀ ℓ m n : ℕ, 1 ≤ m → 2 * m ≤ n → Admissible μ n → ∀ e : ℕ → ℤ,
      (walkProb μ n (-1))⁻¹ * ∑' q, (Set.Ioi m).indicator
        (fun q => (forestSizeWeight μ ℓ q).toReal * walkProb μ ((n : ℤ) - q) (e q)) q ≤
        C * ℓ / a m := by
  obtain ⟨C, hC⟩ := forest_weighted_tail_le hT
  obtain ⟨c, hc, hlow⟩ := hT.exists_lower_bound_neg_one
  refine ⟨max C 0 / c, fun ℓ m n hm hmn hadm e => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have han : 0 < a n := hT.pos n hn1
  have ham : 0 < a m := hT.pos m hm
  have hψ : 0 < walkProb μ n (-1) := (walkProb_neg_one_pos_iff μ n).2 hadm
  have hinv : (walkProb μ n (-1))⁻¹ ≤ a n / c := by
    rw [inv_le_comm₀ hψ (by positivity), inv_div]
    exact hlow n hn1 hψ
  have h1 := hC ℓ m n hm hmn e
  have h0 : 0 ≤ ∑' q, (Set.Ioi m).indicator
      (fun q => (forestSizeWeight μ ℓ q).toReal * walkProb μ ((n : ℤ) - q) (e q)) q :=
    tsum_nonneg fun q => Set.indicator_nonneg (fun q _ => mul_nonneg ENNReal.toReal_nonneg
      (walkProb_nonneg μ _ _)) q
  have h2 : C * ℓ / (a m * a n) ≤ max C 0 * ℓ / (a m * a n) := by
    gcongr; exact le_max_left _ _
  calc (walkProb μ n (-1))⁻¹ * _ ≤ a n / c * (max C 0 * ℓ / (a m * a n)) :=
        mul_le_mul hinv (h1.trans h2) h0 (by positivity)
    _ = max C 0 / c * ℓ / a m := by field_simp

/-! ### ENNReal forms (for lintegral computations) -/

theorem ofReal_indicator_toReal {s : Set ℕ} {f : ℕ → ℝ≥0∞} (hf : ∀ q, f q ≠ ∞) (q : ℕ) :
    ENNReal.ofReal (s.indicator (fun q => (f q).toReal) q) = s.indicator f q := by
  by_cases hq : q ∈ s
  · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, ENNReal.ofReal_toReal (hf q)]
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, ENNReal.ofReal_zero]

/-- ENNReal form of `forest_tail_le`. -/
theorem forestSizeWeight_tail_le_ofReal (hT : StableToolkit μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ m : ℕ, 1 ≤ m →
      ∑' q, (Set.Ioi m).indicator (forestSizeWeight μ ℓ) q ≤ ENNReal.ofReal (C * ℓ / a m) := by
  obtain ⟨C, hC0, hC⟩ := forest_tail_le hT
  refine ⟨C, hC0, fun ℓ m hm => ?_⟩
  have h := ENNReal.ofReal_le_ofReal (hC ℓ m hm)
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun q => Set.indicator_nonneg (fun q _ => ENNReal.toReal_nonneg) q)
    ((summable_forestSizeWeight_toReal μ ℓ).indicator _)] at h
  simpa only [ofReal_indicator_toReal (forestSizeWeight_ne_top μ ℓ)] using h

/-- ENNReal form of `forest_weighted_tail_sup_le`. -/
theorem forestSizeWeight_weighted_tail_le_ofReal (hT : StableToolkit μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ m N : ℕ, 1 ≤ m → 2 * m ≤ N →
      ∑' q, (Set.Ioi m).indicator
        (fun q => forestSizeWeight μ ℓ q * ENNReal.ofReal (supWalk μ ((N : ℤ) - q))) q ≤
        ENNReal.ofReal (C * ℓ / (a m * a N)) := by
  obtain ⟨C, hC0, hC⟩ := forest_weighted_tail_sup_le hT
  refine ⟨C, hC0, fun ℓ m N hm hmN => ?_⟩
  have h := ENNReal.ofReal_le_ofReal (hC ℓ m N hm hmN)
  have hnn : ∀ q, 0 ≤ (Set.Ioi m).indicator
      (fun q => (forestSizeWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q :=
    fun q => Set.indicator_nonneg (fun q _ => mul_nonneg ENNReal.toReal_nonneg
      (supWalk_nonneg μ _)) q
  have hs : Summable fun q => (Set.Ioi m).indicator
      (fun q => (forestSizeWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q :=
    Summable.of_nonneg_of_le hnn
      (fun q => Set.indicator_le_indicator
        (mul_le_of_le_one_right ENNReal.toReal_nonneg (supWalk_le_one μ _)))
      ((summable_forestSizeWeight_toReal μ ℓ).indicator _)
  rw [ENNReal.ofReal_tsum_of_nonneg hnn hs] at h
  refine le_trans (le_of_eq (tsum_congr fun q => ?_)) h
  by_cases hq : q ∈ Set.Ioi m
  · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (forestSizeWeight_ne_top μ ℓ
        q)]
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, ENNReal.ofReal_zero]

end PoissonDeclumping.Bridge
