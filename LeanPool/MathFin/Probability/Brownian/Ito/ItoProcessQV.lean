/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.QuadraticVariationL2
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

/-!
# Quadratic variation of an Itô process: the drift contributes nothing

Saporito, Theorem 7.4.5: an Itô process `X_t = X₀ + ∫₀ᵗ a ds + ∫₀ᵗ σ dB`
has quadratic variation `⟨X⟩_t = ∫₀ᵗ σ² ds` — the drift drops out entirely.

This file derives the theorem's celebrated content in the constant-`σ`,
Lipschitz-drift regime: for `X_t = X₀ + A_t + σ·B_t` with the drift path `A`
`Cₐ`-Lipschitz in time (exactly what `A_t = ∫₀ᵗ a ds` with `|a| ≤ Cₐ` gives),
the equipartition squared-increment sums of `X` over `[0, T]` converge in
mean square to `σ²·T = ∫₀ᵀ σ² ds`:

  `E[(∑ₖ (ΔXₖ)² − σ²T)²] → 0`.

Expanding `(ΔXₖ)² = (ΔAₖ)² + 2σ·ΔAₖΔBₖ + σ²(ΔBₖ)²`, the three pieces die at
explicit rates:

* the **pure drift** term is squeezed pathwise: `∑(ΔAₖ)² ≤ Cₐ²T²/n`;
* the **cross** term dies in `L²` at rate `1/n`: Cauchy–Schwarz against
  `E[(ΔBₖ)²] = Δt`;
* the **diffusion** term is `σ²(∑(ΔBₖ)² − T)`, the Brownian quadratic
  variation (`QuadraticVariationL2.sum_increment_sq_sub_sq_le`), with its
  `2T²/n` Gaussian-kurtosis rate.

Time- or state-dependent `σ` requires the stochastic-integral-as-process
layer (Summit B); the drift-immunity mechanism is identical.

## Main results

* `ItoProcessQV.tendsto_qv_ito_process` — `∑ₖ (ΔXₖ)² → σ²T` in `L²`
  (Theorem 7.4.5 in the constant-`σ` regime, fully derived).

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 7.4.5

## Tags

quadratic variation, Itô process, drift immunity, mean-square convergence, realized variance,
MSC 60H05, MSC 60J65, MSC 60G44
-/

@[expose] public section

namespace MathFin

namespace ItoProcessQV

open MeasureTheory ProbabilityTheory ItoIsometryAdapted MathFin.QuadraticVariationL2 Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

private theorem integral_add_three_sq_le {E F G : Ω → ℝ}
    (hE2_int : Integrable (fun ω ↦ (E ω) ^ 2) μ)
    (hF2_int : Integrable (fun ω ↦ (F ω) ^ 2) μ)
    (hG2_int : Integrable (fun ω ↦ (G ω) ^ 2) μ) :
    ∫ ω, (E ω + F ω + G ω) ^ 2 ∂μ ≤
      3 * ∫ ω, (E ω) ^ 2 ∂μ + 3 * ∫ ω, (F ω) ^ 2 ∂μ + 3 * ∫ ω, (G ω) ^ 2 ∂μ := by
  have h3 : ∀ ω, (E ω + F ω + G ω) ^ 2
      ≤ 3 * (E ω) ^ 2 + 3 * (F ω) ^ 2 + 3 * (G ω) ^ 2 := fun ω ↦ by
    nlinarith [sq_nonneg (E ω - F ω), sq_nonneg (E ω - G ω), sq_nonneg (F ω - G ω)]
  calc ∫ ω, (E ω + F ω + G ω) ^ 2 ∂μ
    _ ≤ ∫ ω, (3 * (E ω) ^ 2 + 3 * (F ω) ^ 2 + 3 * (G ω) ^ 2) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
          (((hE2_int.const_mul 3).add (hF2_int.const_mul 3)).add
            (hG2_int.const_mul 3)) (Eventually.of_forall h3)
    _ = 3 * ∫ ω, (E ω) ^ 2 ∂μ + 3 * ∫ ω, (F ω) ^ 2 ∂μ + 3 * ∫ ω, (G ω) ^ 2 ∂μ := by
        have hEF : Integrable (fun ω ↦ 3 * (E ω) ^ 2 + 3 * (F ω) ^ 2) μ :=
          (hE2_int.const_mul 3).add (hF2_int.const_mul 3)
        have hG3 : Integrable (fun ω ↦ 3 * (G ω) ^ 2) μ := hG2_int.const_mul 3
        rw [integral_add hEF hG3,
          integral_add (hE2_int.const_mul 3) (hF2_int.const_mul 3),
          integral_const_mul, integral_const_mul, integral_const_mul]

/-- Per-`n` mean-square bound: the squared-increment sum of the Itô process
misses `σ²T` by at most `C/n`. -/
private lemma qv_bound (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    {X A : ℝ≥0 → Ω → ℝ} {X₀ : Ω → ℝ} {σ Ca : ℝ} (hCa : 0 ≤ Ca)
    (hX : ∀ t ω, X t ω = X₀ ω + A t ω + σ * B t ω)
    (hA_meas : ∀ t, Measurable (A t))
    (hA_lip : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → ∀ ω, |A t ω - A s ω| ≤ Ca * ((t : ℝ) - s))
    {n : ℕ} (hn : 0 < n) :
    ∫ ω, (∑ k ∈ Finset.range n,
        (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2
          - σ ^ 2 * (T : ℝ)) ^ 2 ∂μ
      ≤ (3 * (Ca ^ 2 * (T : ℝ) ^ 2) ^ 2 + 12 * σ ^ 2 * Ca ^ 2 * (T : ℝ) ^ 3
          + 6 * σ ^ 4 * (T : ℝ) ^ 2) / n := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith
  have hmono : Monotone (unifPart T n) := unifPart_mono T n
  have hs0 : unifPart T n 0 = 0 := unifPart_zero T n
  have hsn : unifPart T n n = T := unifPart_self T hn.ne'
  have hle : ∀ k, unifPart T n k ≤ unifPart T n (k + 1) := fun k ↦
    hmono (Nat.le_succ k)
  have hgapeq : ∀ k, (unifPart T n (k + 1) : ℝ) - unifPart T n k = (T : ℝ) / n :=
    unifPart_succ_sub T n
  -- abbreviations for the three pieces
  set E : Ω → ℝ := fun ω ↦ ∑ k ∈ Finset.range n,
    (A (unifPart T n (k + 1)) ω - A (unifPart T n k) ω) ^ 2 with hE
  set F : Ω → ℝ := fun ω ↦ 2 * σ * ∑ k ∈ Finset.range n,
    (A (unifPart T n (k + 1)) ω - A (unifPart T n k) ω)
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) with hF
  set G : Ω → ℝ := fun ω ↦ σ ^ 2 * ((∑ k ∈ Finset.range n,
    (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) - (T : ℝ)) with hG
  -- pointwise decomposition
  have hsplit : ∀ ω, (∑ k ∈ Finset.range n,
      (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2)
        - σ ^ 2 * (T : ℝ) = E ω + F ω + G ω := by
    intro ω
    have hterm : ∀ k ∈ Finset.range n,
        (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2
          = (A (unifPart T n (k + 1)) ω - A (unifPart T n k) ω) ^ 2
            + (2 * σ * ((A (unifPart T n (k + 1)) ω - A (unifPart T n k) ω)
                * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
              + σ ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) :=
      fun k _ ↦ by simp only [hX]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hE, hF, hG]
    ring
  -- measurabilities
  have hΔA_meas : ∀ k : ℕ, Measurable fun ω ↦
      A (unifPart T n (k + 1)) ω - A (unifPart T n k) ω := fun k ↦
    (hA_meas _).sub (hA_meas _)
  have hΔB_meas : ∀ k : ℕ, Measurable fun ω ↦
      B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω := fun k ↦
    (hBmeas _).sub (hBmeas _)
  -- drift increment bound
  have hΔA_bd : ∀ k : ℕ, ∀ ω,
      |A (unifPart T n (k + 1)) ω - A (unifPart T n k) ω| ≤ Ca * ((T : ℝ) / n) := by
    intro k ω
    calc |A (unifPart T n (k + 1)) ω - A (unifPart T n k) ω|
        ≤ Ca * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := hA_lip (hle k) ω
      _ = Ca * ((T : ℝ) / n) := by rw [hgapeq k]
  -- Brownian increment moments
  have hΔB2 : ∀ k : ℕ, MemLp (fun ω ↦
      B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) 2 μ := fun k ↦
    (memLp_increment_four hB (unifPart T n k) (unifPart T n (k + 1))).mono_exponent
      (by norm_num)
  have hΔB_int_sq : ∀ k : ℕ, ∫ ω,
      (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 ∂μ = (T : ℝ) / n := by
    intro k
    rw [integral_increment_sq (μ := μ) hB (hle k), hgapeq k]
  -- ===== bound for the pure-drift term =====
  have hE_nonneg : ∀ ω, 0 ≤ E ω := fun ω ↦
    Finset.sum_nonneg fun k _ ↦ sq_nonneg _
  have hE_bd : ∀ ω, E ω ≤ Ca ^ 2 * (T : ℝ) ^ 2 / n := by
    intro ω
    have hsum : E ω ≤ ∑ _k ∈ Finset.range n, (Ca * ((T : ℝ) / n)) ^ 2 := by
      rw [hE]
      refine Finset.sum_le_sum fun k _ ↦ ?_
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hΔA_bd k ω) 2
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    calc E ω ≤ (n : ℝ) * (Ca * ((T : ℝ) / n)) ^ 2 := hsum
      _ = Ca ^ 2 * (T : ℝ) ^ 2 / n := by field_simp
  have hIE : ∫ ω, (E ω) ^ 2 ∂μ ≤ (Ca ^ 2 * (T : ℝ) ^ 2 / n) ^ 2 := by
    have hpt : ∀ ω, (E ω) ^ 2 ≤ (Ca ^ 2 * (T : ℝ) ^ 2 / n) ^ 2 := fun ω ↦
      pow_le_pow_left₀ (hE_nonneg ω) (hE_bd ω) 2
    calc ∫ ω, (E ω) ^ 2 ∂μ
        ≤ ∫ _ω, (Ca ^ 2 * (T : ℝ) ^ 2 / n) ^ 2 ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
            (integrable_const _) (Eventually.of_forall hpt)
      _ = (Ca ^ 2 * (T : ℝ) ^ 2 / n) ^ 2 := by
          rw [integral_const]
          simp [measureReal_def]
  -- ===== bound for the diffusion term =====
  have hG_inner_memLp : MemLp (fun ω ↦ (∑ k ∈ Finset.range n,
      (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) - (T : ℝ)) 2 μ := by
    have hsum : MemLp (fun ω ↦ ∑ k ∈ Finset.range n,
        (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) 2 μ := by
      apply memLp_finsetSum
      intro k _
      simpa using memLp_increment_sq_centered_two hB (unifPart T n k) (unifPart T n (k + 1)) 0
    exact hsum.sub (memLp_const (T : ℝ))
  have hIG : ∫ ω, (G ω) ^ 2 ∂μ ≤ σ ^ 4 * (2 * ((T : ℝ) / n) * T) := by
    have hbound := sum_increment_sq_sub_sq_le (μ := μ) hB hBmeas hmono hs0 n
      (fun k _ ↦ le_of_eq (hgapeq k))
    rw [hsn] at hbound
    have hpt : ∀ ω, (G ω) ^ 2 = σ ^ 4 * ((∑ k ∈ Finset.range n,
        (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) - (T : ℝ)) ^ 2 :=
      fun ω ↦ by simp only [hG]; ring
    have hcongr : ∫ ω, (G ω) ^ 2 ∂μ = ∫ ω, σ ^ 4 * ((∑ k ∈ Finset.range n,
        (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) - (T : ℝ)) ^ 2 ∂μ :=
      integral_congr_ae (Eventually.of_forall hpt)
    rw [hcongr, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hbound (by positivity)
  -- ===== bound for the cross term =====
  have hΔAB_memLp : ∀ k ∈ Finset.range n, MemLp (fun ω ↦
      (A (unifPart T n (k + 1)) ω - A (unifPart T n k) ω)
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) 2 μ := by
    intro k _
    refine MemLp.of_le ((hΔB2 k).const_mul (Ca * ((T : ℝ) / n)))
      ((hΔA_meas k).mul (hΔB_meas k)).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg hCa, abs_of_nonneg (show (0 : ℝ) ≤ (T : ℝ) / n by positivity)]
    exact mul_le_mul_of_nonneg_right (hΔA_bd k ω) (abs_nonneg _)
  have hF_memLp : MemLp F 2 μ := by
    rw [hF]
    exact (memLp_finsetSum _ hΔAB_memLp).const_mul _
  have hIF : ∫ ω, (F ω) ^ 2 ∂μ ≤ 4 * σ ^ 2 * Ca ^ 2 * (T : ℝ) ^ 3 / n := by
    -- pointwise: F² ≤ 4σ²(CaT/n)² · n · ∑(ΔBₖ)²
    have hpt : ∀ ω, (F ω) ^ 2 ≤ 4 * σ ^ 2 * (Ca * ((T : ℝ) / n)) ^ 2
        * ((n : ℝ) * ∑ k ∈ Finset.range n,
          (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) := by
      intro ω
      let a (k : ℕ) := A (unifPart T n (k + 1)) ω - A (unifPart T n k) ω
      let b (k : ℕ) := B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω
      have ha : (∑ k ∈ Finset.range n, (a k) ^ 2) ≤ (n : ℝ) * (Ca * ((T : ℝ) / n)) ^ 2 := by
        calc (∑ k ∈ Finset.range n, (a k) ^ 2)
          _ ≤ ∑ _k ∈ Finset.range n, (Ca * ((T : ℝ) / n)) ^ 2 := by
            exact Finset.sum_le_sum fun k _ ↦ by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hΔA_bd k ω) 2
          _ = _ := by simp [nsmul_eq_mul]
      rw [hF, mul_pow]
      change (2 * σ) ^ 2 * (∑ k ∈ Finset.range n, a k * b k) ^ 2 ≤
        4 * σ ^ 2 * (Ca * ((T : ℝ) / n)) ^ 2 * (n * ∑ k ∈ Finset.range n, (b k) ^ 2)
      calc (2 * σ) ^ 2 * (∑ k ∈ Finset.range n, a k * b k) ^ 2
        _ ≤ (2 * σ) ^ 2 *
            ((∑ k ∈ Finset.range n, (a k) ^ 2) * (∑ k ∈ Finset.range n, (b k) ^ 2)) := by
          gcongr
          exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ ≤ (2 * σ) ^ 2 * (n * (Ca * ((T : ℝ) / n)) ^ 2 *
            (∑ k ∈ Finset.range n, (b k) ^ 2)) := by gcongr
        _ = _ := by ring
    have hRHS_int : Integrable (fun ω ↦ 4 * σ ^ 2 * (Ca * ((T : ℝ) / n)) ^ 2
        * ((n : ℝ) * ∑ k ∈ Finset.range n,
          (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2)) μ := by
      refine Integrable.const_mul ?_ _
      refine Integrable.const_mul ?_ _
      exact integrable_finsetSum _ fun k _ ↦ (hΔB2 k).integrable_sq
    calc ∫ ω, (F ω) ^ 2 ∂μ
        ≤ ∫ ω, 4 * σ ^ 2 * (Ca * ((T : ℝ) / n)) ^ 2
            * ((n : ℝ) * ∑ k ∈ Finset.range n,
              (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
            hRHS_int (Eventually.of_forall hpt)
      _ = 4 * σ ^ 2 * (Ca * ((T : ℝ) / n)) ^ 2 * ((n : ℝ)
            * ∑ k ∈ Finset.range n, ((T : ℝ) / n)) := by
          rw [integral_const_mul, integral_const_mul, integral_finsetSum _
            (fun k _ ↦ (hΔB2 k).integrable_sq)]
          congr 2
          exact Finset.sum_congr rfl fun k _ ↦ hΔB_int_sq k
      _ = 4 * σ ^ 2 * Ca ^ 2 * (T : ℝ) ^ 3 / n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  -- ===== integrabilities for the assembly =====
  have hE_meas : Measurable E := by
    rw [hE]
    exact Finset.measurable_sum _ fun k _ ↦ (hΔA_meas k).pow_const 2
  have hE2_int : Integrable (fun ω ↦ (E ω) ^ 2) μ := by
    refine Integrable.mono' (integrable_const ((Ca ^ 2 * (T : ℝ) ^ 2 / n) ^ 2))
      ((hE_meas.pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hE_nonneg ω) (hE_bd ω) 2
  have hF2_int : Integrable (fun ω ↦ (F ω) ^ 2) μ := hF_memLp.integrable_sq
  have hG2_int : Integrable (fun ω ↦ (G ω) ^ 2) μ := by
    have : MemLp G 2 μ := by
      rw [hG]
      exact hG_inner_memLp.const_mul _
    exact this.integrable_sq
  -- ===== assembly =====
  calc ∫ ω, (∑ k ∈ Finset.range n,
      (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2
        - σ ^ 2 * (T : ℝ)) ^ 2 ∂μ
      = ∫ ω, (E ω + F ω + G ω) ^ 2 ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω ↦ by simp only [hsplit])
    _ ≤ 3 * ∫ ω, (E ω) ^ 2 ∂μ + 3 * ∫ ω, (F ω) ^ 2 ∂μ + 3 * ∫ ω, (G ω) ^ 2 ∂μ :=
        integral_add_three_sq_le hE2_int hF2_int hG2_int
    _ ≤ 3 * (Ca ^ 2 * (T : ℝ) ^ 2 / n) ^ 2 + 3 * (4 * σ ^ 2 * Ca ^ 2 * (T : ℝ) ^ 3 / n)
          + 3 * (σ ^ 4 * (2 * ((T : ℝ) / n) * T)) := by
        gcongr
    _ ≤ (3 * (Ca ^ 2 * (T : ℝ) ^ 2) ^ 2 + 12 * σ ^ 2 * Ca ^ 2 * (T : ℝ) ^ 3
          + 6 * σ ^ 4 * (T : ℝ) ^ 2) / n := by
        rw [div_pow]
        have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        have h1 : 3 * ((Ca ^ 2 * (T : ℝ) ^ 2) ^ 2 / (n : ℝ) ^ 2)
            ≤ 3 * ((Ca ^ 2 * (T : ℝ) ^ 2) ^ 2 / n) := by
          gcongr
        have h2 : (3 : ℝ) * (4 * σ ^ 2 * Ca ^ 2 * (T : ℝ) ^ 3 / n)
            = 12 * σ ^ 2 * Ca ^ 2 * (T : ℝ) ^ 3 / n := by ring
        have h3' : (3 : ℝ) * (σ ^ 4 * (2 * ((T : ℝ) / n) * T))
            = 6 * σ ^ 4 * (T : ℝ) ^ 2 / n := by ring
        rw [h2, h3']
        rw [show (3 * (Ca ^ 2 * (T : ℝ) ^ 2) ^ 2 + 12 * σ ^ 2 * Ca ^ 2 * (T : ℝ) ^ 3
            + 6 * σ ^ 4 * (T : ℝ) ^ 2) / n
          = 3 * ((Ca ^ 2 * (T : ℝ) ^ 2) ^ 2 / n) + 12 * σ ^ 2 * Ca ^ 2 * (T : ℝ) ^ 3 / n
            + 6 * σ ^ 4 * (T : ℝ) ^ 2 / n from by ring]
        gcongr

/-- **Theorem 7.4.5 (quadratic variation of an Itô process), constant-`σ`
regime, fully derived.** For `X_t = X₀ + A_t + σ·B_t` with `A` a
`Cₐ`-Lipschitz drift path (the integrated form of a bounded drift), the
equipartition squared-increment sums of `X` over `[0, T]` converge in mean
square to `σ²·T = ∫₀ᵀ σ² ds`: the **drift contributes nothing** to the
quadratic variation. -/
theorem tendsto_qv_ito_process (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    {X A : ℝ≥0 → Ω → ℝ} {X₀ : Ω → ℝ} {σ Ca : ℝ} (hCa : 0 ≤ Ca)
    (hX : ∀ t ω, X t ω = X₀ ω + A t ω + σ * B t ω)
    (hA_meas : ∀ t, Measurable (A t))
    (hA_lip : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → ∀ ω, |A t ω - A s ω| ≤ Ca * ((t : ℝ) - s)) :
    Tendsto (fun n : ℕ ↦ ∫ ω, (∑ k ∈ Finset.range n,
        (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2
          - σ ^ 2 * (T : ℝ)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  refine squeeze_zero'
    (g := fun n : ℕ ↦ (3 * (Ca ^ 2 * (T : ℝ) ^ 2) ^ 2
      + 12 * σ ^ 2 * Ca ^ 2 * (T : ℝ) ^ 3 + 6 * σ ^ 4 * (T : ℝ) ^ 2) / n)
    (Eventually.of_forall fun n ↦ integral_nonneg fun ω ↦ sq_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat _)
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact qv_bound hB hBmeas T hCa hX hA_meas hA_lip hn

end ItoProcessQV

end MathFin
