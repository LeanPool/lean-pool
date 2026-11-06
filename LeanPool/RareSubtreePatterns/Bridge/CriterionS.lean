/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Setup.Toolkit
public import LeanPool.RareSubtreePatterns.Setup.Marks

import LeanPool.RareSubtreePatterns.RegularVariation.Consequences
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# A criterion for Assumption (S): Lemma `lem:critM`

Source lines 1051–1110 (Lemma 3.4 and its proof), 264–268 (the remark that
`E_{k_n}[C_{k_n} + L_{k_n}] = n^{o(1)}` suffices), inventory L3.4.

For `η ∈ (0, 1 - 1/α)` the cutoff is `M_n = max 1 ⌊n^(1-η)⌋₊`; it equals the paper's
`⌊n^(1-η)⌋` for every `n ≥ 1`, and the `max 1` only repairs `n = 0` so that `IsCutoff` holds
(correction F11 of `docs/BRIDGE_PLAN.md`).

* `isCutoff_max_one_floor_rpow`: `M_n` is a cutoff sequence (`M_n ≥ 1`, `M_n → ∞`,
  `M_n = o(n)`) for `η ∈ (0, 1)`.
* `measureReal_lt_le_div`: Markov's inequality `P(C > x) ≤ E[C] / x` for the core size of a
  decomposition (any measure, finite first moment).
* `critM` (**Lemma `lem:critM`**): given the decompositions `ρ_k` of Assumption (S) (only
  required at marks of positive probability, as in `StructuralMicroscopic`) with
  `E_{k_n}[C_{k_n} + L_{k_n}] ≤ n^δ` eventually along admissible sizes for every `δ > 0`,
  Assumption (S) holds with respect to `M_n`. The proof is the paper's: Markov's inequality and
  the regular-variation limits `tendsto_mul_div_floor_rpow`, `tendsto_div_floor_rpow`.

The hypothesis `E_{k_n}[C + L] = n^{o(1)}` is used only through its upper half
`E_{k_n}[C + L] ≤ n^{o(1)}`, and only along admissible sizes; this is how it is stated.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal

namespace PoissonDeclumping.Bridge

/-- The polynomial cutoff `M_n = max 1 ⌊n^(1-η)⌋₊` (`= ⌊n^(1-η)⌋` for `n ≥ 1`) is a cutoff
sequence for `η ∈ (0, 1)`: `M_n ≥ 1`, `M_n → ∞` and `M_n = o(n)` (source line 233). -/
theorem isCutoff_max_one_floor_rpow {η : ℝ} (h0 : 0 < η) (h1 : η < 1) :
    IsCutoff (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) where
  pos n _ := Nat.lt_of_lt_of_le Nat.one_pos (le_max_left 1 _)
  tendsto_atTop := tendsto_atTop_mono (fun n => le_max_right 1 _)
    (tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop))
  isLittleO := by
    rw [isLittleO_iff]
    intro c hc
    have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-η)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop h0).comp tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (ge_mem_nhds hc), eventually_ge_atTop 1] with n hn hn1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < n := by linarith
    have hx1 : 1 ≤ (n : ℝ) ^ (1 - η) := Real.one_le_rpow hnR (by linarith)
    have hM : max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊ = ⌊(n : ℝ) ^ (1 - η)⌋₊ :=
      max_eq_right (Nat.le_floor (by exact_mod_cast hx1))
    rw [Real.norm_natCast, Real.norm_natCast, hM]
    calc (⌊(n : ℝ) ^ (1 - η)⌋₊ : ℝ) ≤ (n : ℝ) ^ (1 - η) := Nat.floor_le (by positivity)
      _ = (n : ℝ) ^ (-η) * n := by
          rw [← Real.rpow_add_one hn0.ne']
          ring_nf
      _ ≤ c * n := mul_le_mul_of_nonneg_right hn hn0.le

/-- Markov's inequality for the core size `C` of a decomposition (source line 1093):
`P(C > x) ≤ E[C] / x` for `x > 0`, for any measure with `E[C] < ∞`. -/
theorem measureReal_lt_le_div (ρ : Measure (PlaneTree × ℕ × List PlaneTree)) {x : ℝ}
    (hx : 0 < x) (hfin : ∫⁻ ω, (ω.2.1 : ℝ≥0∞) ∂ρ ≠ ∞) :
    ρ.real {ω | x < ω.2.1} ≤ (∫⁻ ω, (ω.2.1 : ℝ≥0∞) ∂ρ).toReal / x := by
  have hsub : {ω : PlaneTree × ℕ × List PlaneTree | x < ω.2.1} ⊆
      {ω | ENNReal.ofReal x ≤ (ω.2.1 : ℝ≥0∞)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hω.le
  have hmk := mul_meas_ge_le_lintegral₀ (μ := ρ)
    (f := fun ω : PlaneTree × ℕ × List PlaneTree => (ω.2.1 : ℝ≥0∞))
    (Measurable.of_discrete).aemeasurable (ENNReal.ofReal x)
  have h2 : ENNReal.ofReal x * ρ {ω | x < ω.2.1} ≤ ∫⁻ ω, (ω.2.1 : ℝ≥0∞) ∂ρ :=
    le_trans (mul_le_mul_right (measure_mono hsub) _) hmk
  have h3 := ENNReal.toReal_mono hfin h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hx.le, ← measureReal_def] at h3
  rw [le_div_iff₀ hx, mul_comm]
  exact h3

/-- **Lemma `lem:critM`** (source lines 1055–1109). Let `ρ_j` be decompositions as in
Assumption (S) (`Skeleton`, required at every mark of positive probability) with
`E_{k_n}[C_{k_n} + L_{k_n}] = n^{o(1)}`, used in the form: for every `δ > 0`, eventually along
admissible sizes, `E_{k_n}[C_{k_n} + L_{k_n}] ≤ n^δ`. Then for every `η ∈ (0, 1 - 1/α)`
Assumption (S) holds along `(k_n)` with respect to `M_n = max 1 ⌊n^(1-η)⌋₊` (which is
`⌊n^(1-η)⌋` for `n ≥ 1`), with the same decompositions `ρ`. -/
theorem critM {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (hT : StableToolkit μ α a) {η : ℝ}
    (hη : 0 < η ∧ η < 1 - 1 / α) {G : ℕ → PlaneTree → Prop} {k : ℕ → ℕ}
    (ρ : ℕ → Measure (PlaneTree × ℕ × List PlaneTree))
    (hρ : ∀ j, 0 < PlaneTree.bienayme μ {T | G j T} → Skeleton μ (G j) (ρ j))
    (hmom : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ,
      ∫⁻ ω, ((ω.2.1 : ℝ≥0∞) + (ω.2.2.length : ℝ≥0∞)) ∂ρ (k n) ≤
        ENNReal.ofReal ((n : ℝ) ^ δ)) :
    StructuralMicroscopic μ a G k (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) := by
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hrv := hT.regularlyVarying
  have hα1 : η < 1 := by have := hT.rho_pos; linarith
  -- the cutoff equals `⌊n^(1-η)⌋₊ ≥ 1` for `n ≥ 1`
  have hMeq : ∀ n : ℕ, 1 ≤ n →
      max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊ = ⌊(n : ℝ) ^ (1 - η)⌋₊ ∧ 1 ≤ ⌊(n : ℝ) ^ (1 - η)⌋₊ := by
    intro n hn1
    have hx1 : 1 ≤ (n : ℝ) ^ (1 - η) :=
      Real.one_le_rpow (by exact_mod_cast hn1) (by linarith)
    have h1 : 1 ≤ ⌊(n : ℝ) ^ (1 - η)⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
    exact ⟨max_eq_right h1, h1⟩
  -- the two moments, eventually finite and `≤ n^δ`
  set eC : ℕ → ℝ := fun n => (∫⁻ ω, (ω.2.1 : ℝ≥0∞) ∂ρ (k n)).toReal
  set eL : ℕ → ℝ := fun n => (∫⁻ ω, (ω.2.2.length : ℝ≥0∞) ∂ρ (k n)).toReal
  have hCle : ∀ n, ∫⁻ ω, (ω.2.1 : ℝ≥0∞) ∂ρ (k n) ≤
      ∫⁻ ω, ((ω.2.1 : ℝ≥0∞) + (ω.2.2.length : ℝ≥0∞)) ∂ρ (k n) :=
    fun n => lintegral_mono fun ω => le_self_add
  have hLle : ∀ n, ∫⁻ ω, (ω.2.2.length : ℝ≥0∞) ∂ρ (k n) ≤
      ∫⁻ ω, ((ω.2.1 : ℝ≥0∞) + (ω.2.2.length : ℝ≥0∞)) ∂ρ (k n) :=
    fun n => lintegral_mono fun ω => le_add_self
  have hfin := hmom 1 one_pos
  have hCfin : ∀ᶠ n in admissibleSizes μ, ∫⁻ ω, (ω.2.1 : ℝ≥0∞) ∂ρ (k n) ≠ ∞ := by
    filter_upwards [hfin] with n hn
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hCle n).trans hn)
  have hLfin : ∀ᶠ n in admissibleSizes μ, ∫⁻ ω, (ω.2.2.length : ℝ≥0∞) ∂ρ (k n) ≠ ∞ := by
    filter_upwards [hfin] with n hn
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hLle n).trans hn)
  have heC : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ, eC n ≤ (n : ℝ) ^ δ := by
    intro δ hδ
    filter_upwards [hmom δ hδ] with n hn
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) ((hCle n).trans hn)
  have heL : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ, eL n ≤ (n : ℝ) ^ δ := by
    intro δ hδ
    filter_upwards [hmom δ hδ] with n hn
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) ((hLle n).trans hn)
  refine ⟨ρ, hρ, fun ε hε => ?_, ?_⟩
  · -- `a_n P_{k_n}(C > ε M_n) ≤ a_n E[C] / (ε M_n) → 0`
    have hlim := hrv.tendsto_mul_div_floor_rpow hT.monotone hT.pos hT.rho_pos.le hη.2 hl
      (Eventually.of_forall fun n => ENNReal.toReal_nonneg) heC hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [hl (eventually_ge_atTop 1)] with n hn1
      exact mul_nonneg (hT.pos n hn1).le measureReal_nonneg
    · filter_upwards [hCfin, hl (eventually_ge_atTop 1)] with n hfn hn1
      obtain ⟨hM, hM1⟩ := hMeq n hn1
      have hMpos : (0 : ℝ) < (⌊(n : ℝ) ^ (1 - η)⌋₊ : ℝ) := by exact_mod_cast hM1
      have hx : 0 < ε * (⌊(n : ℝ) ^ (1 - η)⌋₊ : ℝ) := mul_pos hε hMpos
      simp only [hM]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (measureReal_lt_le_div (ρ (k n)) hx hfn)
        (hT.pos n hn1).le
  · -- `E[L] / a_{M_n} → 0`
    have hlim := hrv.tendsto_div_floor_rpow hT.monotone hT.pos hT.rho_pos hα1 hl
      (Eventually.of_forall fun n => ENNReal.toReal_nonneg) heL
    have hlim' := ENNReal.tendsto_ofReal hlim
    rw [ENNReal.ofReal_zero] at hlim'
    refine hlim'.congr' ?_
    filter_upwards [hLfin, hl (eventually_ge_atTop 1)] with n hfn hn1
    obtain ⟨hM, hM1⟩ := hMeq n hn1
    simp only [hM]
    rw [ENNReal.ofReal_div_of_pos (hT.pos _ hM1)]
    rw [ENNReal.ofReal_toReal hfn]

end PoissonDeclumping.Bridge
