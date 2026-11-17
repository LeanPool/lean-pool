/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Setup.Marks


/-!
# Elementary criteria used in the applications (Sections 6–7)

* `eventually_mul_add_le_rpow`: if `f_n ≤ n^{o(1)}` (in the form: for every `δ > 0`, eventually
  `f_n ≤ n^δ`), then also `C f_n + D ≤ n^{o(1)}`. This is how the hypotheses
  "`s_{r,k_n} + ℓ_{r,k_n} = n^{o(1)}`", "`k_n = n^{o(1)}`", "`κ^{k_n} = n^{o(1)}`" of Lemmas
  `lem:S_rary` and `lem:S_lh` (source lines 2644–2653, 3053–3064) are transported to the moment
  bound `E_{k_n}[C_{k_n} + L_{k_n}] = n^{o(1)}` required by Lemma `lem:critM`.
* `nonClustering_of_pairSum_le`: the final step of the proofs of Lemmas `lem:S_rary`(ii),
  `lem:C_rary` and `lem:C_lh` (source lines 2750–2753, 2787–2791, 3234–3236): a summed pair bound
  `∑_{ℓ=1}^{M_n} A_n(ℓ) ≤ K π_n + C M_n π_n²` gives Assumption (C) as soon as `M_n = o(n)` and
  `K π_n = o(n π_n²)` (e.g. `K = 0`, or `n π_n → ∞`).
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace PoissonDeclumping

/-- If `f_n ≤ n^δ` eventually for every `δ > 0`, then the same holds for `C f_n + D`
(`C ≥ 0`), along any filter finer than `atTop`. -/
theorem eventually_mul_add_le_rpow {l : Filter ℕ} (hl : l ≤ atTop) {f : ℕ → ℝ}
    (hf : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in l, f n ≤ (n : ℝ) ^ δ) {C : ℝ} (hC : 0 ≤ C) (D : ℝ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in l, C * f n + D ≤ (n : ℝ) ^ δ := by
  intro δ hδ
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop hδ2).comp tendsto_natCast_atTop_atTop
  filter_upwards [hf (δ / 2) hδ2, hl (ht.eventually_ge_atTop (C + |D| + 1)),
    hl (eventually_gt_atTop 0)] with n hn hy hn0
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  set y := (n : ℝ) ^ (δ / 2) with hy_def
  have hy1 : 1 ≤ y := by have := abs_nonneg D; linarith
  have hsq : (n : ℝ) ^ δ = y * y := by
    rw [hy_def, ← Real.rpow_add hn0']
    ring_nf
  rw [hsq]
  calc C * f n + D ≤ C * y + |D| * y := by
        gcongr
        calc D ≤ |D| := le_abs_self D
          _ = |D| * 1 := (mul_one _).symm
          _ ≤ |D| * y := mul_le_mul_of_nonneg_left hy1 (abs_nonneg D)
    _ = (C + |D|) * y := by ring
    _ ≤ y * y := mul_le_mul_of_nonneg_right (by linarith) (by linarith)

/-- A conditional measure has total mass at most one (it is `0` when the conditioning event is
null). -/
theorem cond_univ_le_one {α : Type*} [MeasurableSpace α] (ν : MeasureTheory.Measure α)
    [MeasureTheory.IsFiniteMeasure ν] (s : Set α) : ProbabilityTheory.cond ν s Set.univ ≤ 1 := by
  by_cases h : ν s = 0
  · rw [ProbabilityTheory.cond_eq_zero_of_meas_eq_zero h]
    exact zero_le
  · have := ProbabilityTheory.cond_isProbabilityMeasure (μ := ν) h
    rw [MeasureTheory.measure_univ]

theorem pairProb_nonneg (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ) (n ℓ : ℕ) :
    0 ≤ pairProb μ G k n ℓ := MeasureTheory.measureReal_nonneg

/-- A summed pair bound `∑_{ℓ=1}^{M_n} A_n(ℓ) ≤ K π_n + C M_n π_n²` gives Assumption (C) when
`M_n = o(n)` and `K π_n = o(n π_n²)` along admissible sizes. -/
theorem nonClustering_of_pairSum_le {μ : PMF ℕ} {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hM : (fun n => (M n : ℝ)) =o[atTop] (fun n => (n : ℝ))) {K C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in admissibleSizes μ,
      K * markProb μ G k n ≤ ε * ((n : ℝ) * markProb μ G k n ^ 2))
    (h : ∀ n, ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ ≤
      K * markProb μ G k n + C * M n * markProb μ G k n ^ 2) :
    NonClustering μ G k M := by
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  rw [NonClustering, isLittleO_iff]
  intro c hc
  have hc2 : 0 < c / 2 := half_pos hc
  have hc3 : 0 < c / 2 / (C + 1) := div_pos hc2 (by linarith)
  filter_upwards [hK (c / 2) hc2, hl (hM.bound hc3)] with n hKn hMn
  have hpos : 0 ≤ ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ :=
    Finset.sum_nonneg fun ℓ _ => pairProb_nonneg μ G k n ℓ
  have hπ : 0 ≤ markProb μ G k n := MeasureTheory.measureReal_nonneg
  have hπ2 : 0 ≤ (n : ℝ) * markProb μ G k n ^ 2 := by positivity
  rw [Real.norm_natCast, Real.norm_natCast] at hMn
  rw [Real.norm_of_nonneg hpos, Real.norm_of_nonneg hπ2]
  have hCM : C * (M n : ℝ) ≤ c / 2 * (n : ℝ) := by
    calc C * M n ≤ C * (c / 2 / (C + 1) * n) := mul_le_mul_of_nonneg_left hMn hC
      _ = c / 2 * n * (C / (C + 1)) := by field_simp
      _ ≤ c / 2 * n * 1 := by
          gcongr
          rw [div_le_one (by linarith)]
          linarith
      _ = c / 2 * (n : ℝ) := mul_one _
  calc ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ
      ≤ K * markProb μ G k n + C * M n * markProb μ G k n ^ 2 := h n
    _ ≤ c / 2 * ((n : ℝ) * markProb μ G k n ^ 2) + c / 2 * (n : ℝ) * markProb μ G k n ^ 2 := by
        gcongr
    _ = c * ((n : ℝ) * markProb μ G k n ^ 2) := by ring

/-- The condition `K π_n = o(n π_n²)` of `nonClustering_of_pairSum_le` holds when `n π_n → ∞`. -/
theorem eventually_mul_le_of_tendsto {μ : PMF ℕ} {G : ℕ → PlaneTree → Prop} {k : ℕ → ℕ}
    (hπ : Tendsto (fun n : ℕ => (n : ℝ) * markProb μ G k n) (admissibleSizes μ) atTop) (K : ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in admissibleSizes μ,
      K * markProb μ G k n ≤ ε * ((n : ℝ) * markProb μ G k n ^ 2) := by
  filter_upwards [hπ.eventually_ge_atTop (K / ε)] with n hn
  have hπ0 : 0 ≤ markProb μ G k n := MeasureTheory.measureReal_nonneg
  have : K ≤ ε * ((n : ℝ) * markProb μ G k n) := by
    rw [div_le_iff₀ hε] at hn
    linarith
  calc K * markProb μ G k n ≤ ε * ((n : ℝ) * markProb μ G k n) * markProb μ G k n :=
        mul_le_mul_of_nonneg_right this hπ0
    _ = ε * ((n : ℝ) * markProb μ G k n ^ 2) := by ring

end PoissonDeclumping
