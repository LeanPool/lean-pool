/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# FiniteCorridorIteration

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Finite weighted-defect corridor iteration

This module is a Provider helper: it proves an arithmetic statement about an
abstract sequence and makes no source-node status claim.

```text
F t ≤ A δ₁ (δ₁ + 3⁻ᵗ) + C ∑_{k=1}^{t} 3⁻ᵏ (F (t - k) - F t),      t ≥ j₀,
```

together with the initialization `e.iter.init`, which supplies the crude
`O(E²γ)` estimate `F t ≤ K₀ δ₁` at every scale of the physical corridor `[L, L
+ t]`.  The nonnegativity of the response mean is a *separate* source input,
namely `J ≥ 0` from `e.Jenergyv.nosymm`; it is not part of the §A.4 display.
Only predecessors `t - k` with `0 ≤ t - k ≤ t` occur, so no value below the
cutoff is ever used: that is precisely what replaces the printed bi-infinite
iteration.

```text
F (j₀ + j) ≤ K δ₁ (δ₁ + ρ ^ j),      ρ ∈ (0, 1),
```

where `K = finiteCorridorAmplitude A₀ r j₀` and `ρ = finiteCorridorDecayRate C`
are built only from the recurrence data `A`, `C`, `K₀`, `j₀` and the geometric
weight `r`.  `exists_finiteCorridor_weightedDefect_decay` states that
quantifier order explicitly.

The weight `r` is kept abstract subject to `0 ≤ r ≤ 1/3`.  The single parameter
`r` governs BOTH, so `r = 3⁻ᵈ` is admissible only for a consumer whose lag
weights are also `3⁻ᵈᵏ`; a consumer holding the source's `3⁻ᵏ` lag weights
takes `r = 1/3` and weakens any sharper forcing decay to `3⁻ᵗ`.  No
instantiation is performed here: the proved
`exists_relativeCutoff_finiteCorridor_fluctuationVariance_bound`
(`CombineFiniteVariance.lean`) is a two-plus-eight variance-channel bound
carrying `Real.rpow 3 (-d * (n - L).toNat)`, so passing to a mean recurrence,
converting `rpow` to the natural-number power `r ^ t`, and checking `3⁻ᵈ ≤ 1/3`
(which needs `1 ≤ d`) are consumer obligations.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

/-! ### Elementary finite sums -/

/-- Closed form of the finite half-geometric first moment. -/
private theorem halfWeightedSum_eq (j : ℕ) :
    ∑ k ∈ Finset.Icc 1 j, (k : ℝ) * (1 / 2 : ℝ) ^ k =
      2 - ((j : ℝ) + 2) * (1 / 2 : ℝ) ^ j := by
  induction j with
  | zero =>
      rw [Finset.Icc_eq_empty (by omega)]
      norm_num
  | succ j ih =>
      have hins : Finset.Icc 1 (j + 1) = insert (j + 1) (Finset.Icc 1 j) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : (j + 1) ∉ Finset.Icc 1 j := fun hmem => by
        have hle := (Finset.mem_Icc.mp hmem).2
        omega
      rw [hins, Finset.sum_insert hnot, ih]
      push_cast
      simp only [pow_succ]
      ring

/-- The finite half-geometric first moments are bounded by `2`. -/
private theorem halfWeightedSum_le_two (j : ℕ) :
    ∑ k ∈ Finset.Icc 1 j, (k : ℝ) * (1 / 2 : ℝ) ^ k ≤ 2 := by
  rw [halfWeightedSum_eq j]
  have hprod : 0 ≤ ((j : ℝ) + 2) * (1 / 2 : ℝ) ^ j := by positivity
  linarith

/-- Bernoulli's inequality in the form used by the defect kernel. -/
private theorem one_sub_pow_le_mul_one_sub {ρ : ℝ} (hρ0 : 0 ≤ ρ) (k : ℕ) :
    1 - ρ ^ k ≤ (1 - ρ) * (k : ℝ) := by
  have hB : 1 + (k : ℝ) * (ρ - 1) ≤ (1 + (ρ - 1)) ^ k :=
    one_add_mul_le_pow (by linarith) k
  rw [show (1 : ℝ) + (ρ - 1) = ρ by ring] at hB
  linarith

/-! ### The weighted-defect kernel -/

/-- The kernel inequality that closes the finite strong induction: it pays for
replacing the predecessor weight `ρ ^ (j - k)` by the current weight `ρ ^ j`
inside the finite lag sum. -/
def WeightedDefectKernel (C r ρ : ℝ) : Prop :=
  ∀ j : ℕ,
    C * ∑ k ∈ Finset.Icc 1 j, r ^ k * (ρ ^ (j - k) - ρ ^ j) ≤
      (1 / 2 : ℝ) * ρ ^ j

/-- A geometric lag weight satisfies the kernel inequality as soon as it is
dominated by half the rate and the rate is close enough to one. -/
private theorem weightedDefectKernel_of_two_mul_le {C r ρ : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hrρ : 2 * r ≤ ρ) (hsmall : 2 * C * (1 - ρ) ≤ (1 / 2 : ℝ)) :
    WeightedDefectKernel C r ρ := by
  intro j
  have hhalf : r ≤ ρ * (1 / 2 : ℝ) := by linarith
  have hterm : ∀ k ∈ Finset.Icc 1 j,
      r ^ k * (ρ ^ (j - k) - ρ ^ j) ≤
        ρ ^ j * (1 - ρ) * ((k : ℝ) * (1 / 2 : ℝ) ^ k) := by
    intro k hk
    have hkj : k ≤ j := (Finset.mem_Icc.mp hk).2
    have hmix : r ^ k * ρ ^ (j - k) ≤ ρ ^ j * (1 / 2 : ℝ) ^ k := by
      calc r ^ k * ρ ^ (j - k)
          ≤ (ρ * (1 / 2 : ℝ)) ^ k * ρ ^ (j - k) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hhalf k)
              (pow_nonneg hρ0 (j - k))
        _ = ρ ^ (j - k) * ρ ^ k * (1 / 2 : ℝ) ^ k := by
            rw [mul_pow]
            ring
        _ = ρ ^ j * (1 / 2 : ℝ) ^ k := by
            rw [pow_sub_mul_pow ρ hkj]
    have hdiff : ρ ^ (j - k) - ρ ^ j = ρ ^ (j - k) * (1 - ρ ^ k) := by
      rw [mul_sub, mul_one, pow_sub_mul_pow ρ hkj]
    have hle : ρ ^ k ≤ 1 := pow_le_one₀ hρ0 hρ1
    rw [hdiff, ← mul_assoc]
    calc r ^ k * ρ ^ (j - k) * (1 - ρ ^ k)
        ≤ ρ ^ j * (1 / 2 : ℝ) ^ k * ((1 - ρ) * (k : ℝ)) :=
          mul_le_mul hmix (one_sub_pow_le_mul_one_sub hρ0 k) (by linarith)
            (by positivity)
      _ = ρ ^ j * (1 - ρ) * ((k : ℝ) * (1 / 2 : ℝ) ^ k) := by ring
  have hfactor : 0 ≤ ρ ^ j * (1 - ρ) :=
    mul_nonneg (pow_nonneg hρ0 j) (by linarith)
  have hsum2 : (∑ k ∈ Finset.Icc 1 j, r ^ k * (ρ ^ (j - k) - ρ ^ j)) ≤
      2 * (1 - ρ) * ρ ^ j := by
    calc (∑ k ∈ Finset.Icc 1 j, r ^ k * (ρ ^ (j - k) - ρ ^ j))
        ≤ ∑ k ∈ Finset.Icc 1 j,
            ρ ^ j * (1 - ρ) * ((k : ℝ) * (1 / 2 : ℝ) ^ k) :=
          Finset.sum_le_sum hterm
      _ = ρ ^ j * (1 - ρ) *
            ∑ k ∈ Finset.Icc 1 j, (k : ℝ) * (1 / 2 : ℝ) ^ k := by
          rw [Finset.mul_sum]
      _ ≤ ρ ^ j * (1 - ρ) * 2 :=
          mul_le_mul_of_nonneg_left (halfWeightedSum_le_two j) hfactor
      _ = 2 * (1 - ρ) * ρ ^ j := by ring
  have hmul := mul_le_mul_of_nonneg_left hsum2 hC
  have hrate := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hρ0 j)
  linarith

/-! ### The iteration constants -/

/-- The geometric rate produced by the finite weighted-defect iteration.  It
depends only on the defect coefficient `C` of the recurrence. -/
noncomputable def finiteCorridorDecayRate (C : ℝ) : ℝ := 1 - (4 * (C + 1))⁻¹

/-- The amplitude produced by the finite weighted-defect iteration.  It depends
only on the forcing coefficient `A`, the defect coefficient `C`, the crude
initialization coefficient `K₀`, the geometric weight `r` and the initial
separation `j₀` of the recurrence. -/
def finiteCorridorAmplitude (A C K₀ r : ℝ) (j₀ : ℕ) : ℝ :=
  2 * (A + 2 * K₀ + C * K₀ * (j₀ : ℝ) * r)

private theorem finiteCorridorGap_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < (4 * (C + 1))⁻¹ :=
  inv_pos.mpr (by linarith)

private theorem finiteCorridorGap_le {C : ℝ} (hC : 0 ≤ C) :
    (4 * (C + 1))⁻¹ ≤ 1 / 4 := by
  have hden : (0 : ℝ) < 4 * (C + 1) := by linarith
  have h := mul_le_mul_of_nonneg_left (show (4 : ℝ) ≤ 4 * (C + 1) by linarith)
    (inv_nonneg.mpr hden.le)
  rw [inv_mul_cancel₀ (ne_of_gt hden)] at h
  linarith

private theorem finiteCorridorGap_small {C : ℝ} (hC : 0 ≤ C) :
    2 * C * (4 * (C + 1))⁻¹ ≤ 1 / 2 := by
  have hden : (0 : ℝ) < 4 * (C + 1) := by linarith
  have h := mul_le_mul_of_nonneg_left (show 4 * C ≤ 4 * (C + 1) by linarith)
    (inv_nonneg.mpr hden.le)
  rw [inv_mul_cancel₀ (ne_of_gt hden)] at h
  linarith

/-- The rate is positive. -/
theorem finiteCorridorDecayRate_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < finiteCorridorDecayRate C := by
  have hle := finiteCorridorGap_le hC
  simp only [finiteCorridorDecayRate]
  linarith

/-- The rate is a genuine contraction factor. -/
theorem finiteCorridorDecayRate_lt_one {C : ℝ} (hC : 0 ≤ C) :
    finiteCorridorDecayRate C < 1 := by
  have hpos := finiteCorridorGap_pos hC
  simp only [finiteCorridorDecayRate]
  linarith

/-- The amplitude is nonnegative. -/
theorem finiteCorridorAmplitude_nonneg {A C K₀ r : ℝ} (j₀ : ℕ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hK₀ : 0 ≤ K₀) (hr0 : 0 ≤ r) :
    0 ≤ finiteCorridorAmplitude A C K₀ r j₀ := by
  have h : 0 ≤ C * K₀ * (j₀ : ℝ) * r :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hK₀) (Nat.cast_nonneg j₀)) hr0
  simp only [finiteCorridorAmplitude]
  linarith

private theorem finiteCorridorDecayRate_kernel {C r : ℝ} (hC : 0 ≤ C)
    (hr0 : 0 ≤ r) (hr3 : r ≤ 1 / 3) :
    WeightedDefectKernel C r (finiteCorridorDecayRate C) := by
  have hle := finiteCorridorGap_le hC
  have hpos := finiteCorridorGap_pos hC
  have hsmall := finiteCorridorGap_small hC
  refine weightedDefectKernel_of_two_mul_le hC hr0 ?_ ?_ ?_ ?_
  · simp only [finiteCorridorDecayRate]
    linarith
  · simp only [finiteCorridorDecayRate]
    linarith
  · simp only [finiteCorridorDecayRate]
    linarith
  · simp only [finiteCorridorDecayRate]
    linarith

/-! ### The unshifted finite iteration -/

/-- The finite weighted-defect recurrence produces a geometric bound.  At depth
`j` the recurrence only mentions the earlier values `F (j - k)` with
`1 ≤ k ≤ j`, so the induction never leaves the finite corridor `[0, j]`. -/
private theorem weightedDefect_decay_of_kernel {F : ℕ → ℝ} {A C K₀ K δ r ρ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hrρ : r ≤ ρ)
    (hK : 0 ≤ K) (hAK : 2 * A ≤ K) (hK₀K : K₀ ≤ K)
    (hkernel : WeightedDefectKernel C r ρ)
    (hinit : F 0 ≤ K₀ * δ)
    (hrec : ∀ j : ℕ,
      F j ≤ A * δ * (δ + r ^ j) +
        C * ∑ k ∈ Finset.Icc 1 j, r ^ k * (F (j - k) - F j)) :
    ∀ j : ℕ, F j ≤ K * δ * (δ + ρ ^ j) := by
  have hρ0 : 0 ≤ ρ := hr.trans hrρ
  have hKδ : 0 ≤ K * δ := mul_nonneg hK hδ
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        have h1 : K₀ * δ ≤ K * δ := mul_le_mul_of_nonneg_right hK₀K hδ
        have h2 : 0 ≤ K * δ * δ := mul_nonneg hKδ hδ
        rw [pow_zero]
        linarith
      · have hT : 0 ≤ ∑ k ∈ Finset.Icc 1 j, r ^ k :=
          Finset.sum_nonneg fun k _ => pow_nonneg hr k
        have hsum : (∑ k ∈ Finset.Icc 1 j, r ^ k * (F (j - k) - F j)) ≤
            K * δ ^ 2 * (∑ k ∈ Finset.Icc 1 j, r ^ k) +
              K * δ * (∑ k ∈ Finset.Icc 1 j, r ^ k * ρ ^ (j - k)) -
              F j * (∑ k ∈ Finset.Icc 1 j, r ^ k) := by
          calc (∑ k ∈ Finset.Icc 1 j, r ^ k * (F (j - k) - F j))
              ≤ ∑ k ∈ Finset.Icc 1 j,
                  r ^ k * (K * δ * (δ + ρ ^ (j - k)) - F j) := by
                refine Finset.sum_le_sum fun k hk => ?_
                have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
                exact mul_le_mul_of_nonneg_left
                  (sub_le_sub_right (ih (j - k) (by omega)) (F j))
                  (pow_nonneg hr k)
            _ = ∑ k ∈ Finset.Icc 1 j,
                  (K * δ ^ 2 * r ^ k + K * δ * (r ^ k * ρ ^ (j - k)) -
                    F j * r ^ k) :=
                Finset.sum_congr rfl fun k _ => by ring
            _ = K * δ ^ 2 * (∑ k ∈ Finset.Icc 1 j, r ^ k) +
                  K * δ * (∑ k ∈ Finset.Icc 1 j, r ^ k * ρ ^ (j - k)) -
                  F j * (∑ k ∈ Finset.Icc 1 j, r ^ k) := by
                rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
                  ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        have hkernel' : C * ((∑ k ∈ Finset.Icc 1 j, r ^ k * ρ ^ (j - k)) -
            ρ ^ j * (∑ k ∈ Finset.Icc 1 j, r ^ k)) ≤ (1 / 2 : ℝ) * ρ ^ j := by
          have hUT : (∑ k ∈ Finset.Icc 1 j, r ^ k * ρ ^ (j - k)) -
              ρ ^ j * (∑ k ∈ Finset.Icc 1 j, r ^ k) =
                ∑ k ∈ Finset.Icc 1 j, r ^ k * (ρ ^ (j - k) - ρ ^ j) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun k _ => by ring
          rw [hUT]
          exact hkernel j
        have hrpow : r ^ j ≤ ρ ^ j := pow_le_pow_left₀ hr hrρ j
        have hKhalf : (0 : ℝ) ≤ K / 2 * δ := by linarith
        have hAδ : A * δ ≤ K / 2 * δ :=
          mul_le_mul_of_nonneg_right (by linarith) hδ
        have hforce : A * δ * (δ + r ^ j) + (1 / 2 : ℝ) * K * δ * ρ ^ j ≤
            K * δ * (δ + ρ ^ j) := by
          have hAr : A * δ * r ^ j ≤ K / 2 * δ * ρ ^ j :=
            mul_le_mul hAδ hrpow (pow_nonneg hr j) hKhalf
          have hAδsq : A * δ * δ ≤ K / 2 * δ * δ :=
            mul_le_mul_of_nonneg_right hAδ hδ
          have hKδsq : 0 ≤ K * δ * δ := mul_nonneg hKδ hδ
          linarith
        have hsumC := mul_le_mul_of_nonneg_left hsum hC
        have hkernelMul := mul_le_mul_of_nonneg_left hkernel' hKδ
        have hjrec := hrec j
        have hpre : F j ≤ K * δ * (δ + ρ ^ j) +
            C * (∑ k ∈ Finset.Icc 1 j, r ^ k) * (K * δ * (δ + ρ ^ j) - F j) := by
          linarith
        have hCT : 0 ≤ C * (∑ k ∈ Finset.Icc 1 j, r ^ k) := mul_nonneg hC hT
        by_contra hcon
        push Not at hcon
        have hXle : K * δ * (δ + ρ ^ j) - F j ≤ 0 := by linarith
        have hmul2 : C * (∑ k ∈ Finset.Icc 1 j, r ^ k) *
            (K * δ * (δ + ρ ^ j) - F j) ≤
              C * (∑ k ∈ Finset.Icc 1 j, r ^ k) * 0 :=
          mul_le_mul_of_nonneg_left hXle hCT
        rw [mul_zero] at hmul2
        linarith

/-! ### The shifted finite corridor iteration -/

/-- The lags that cross the fixed initial separation form a finite prefix of
exactly `j₀` terms, each carrying one weight factor `r` beyond `r ^ j`.  They
are controlled by the crude corridor bound alone. -/
private theorem earlyPrefix_sum_le {F : ℕ → ℝ} {K₀ δ r : ℝ} (j₀ j : ℕ)
    (hK₀ : 0 ≤ K₀) (hδ : 0 ≤ δ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hFnonneg : ∀ t : ℕ, 0 ≤ F t) (hcrude : ∀ t : ℕ, F t ≤ K₀ * δ) :
    ∑ k ∈ Finset.Icc (j + 1) (j₀ + j), r ^ k * (F (j₀ + j - k) - F (j₀ + j)) ≤
      K₀ * δ * ((j₀ : ℝ) * r) * r ^ j := by
  have hKδ : 0 ≤ K₀ * δ := mul_nonneg hK₀ hδ
  have hterm : ∀ k ∈ Finset.Icc (j + 1) (j₀ + j),
      r ^ k * (F (j₀ + j - k) - F (j₀ + j)) ≤ r ^ (j + 1) * (K₀ * δ) := by
    intro k hk
    have hjk : j + 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hpow : r ^ k ≤ r ^ (j + 1) := pow_le_pow_of_le_one hr0 hr1 hjk
    have hdiff : F (j₀ + j - k) - F (j₀ + j) ≤ K₀ * δ := by
      have h1 := hcrude (j₀ + j - k)
      have h2 := hFnonneg (j₀ + j)
      linarith
    calc r ^ k * (F (j₀ + j - k) - F (j₀ + j))
        ≤ r ^ k * (K₀ * δ) :=
          mul_le_mul_of_nonneg_left hdiff (pow_nonneg hr0 k)
      _ ≤ r ^ (j + 1) * (K₀ * δ) := mul_le_mul_of_nonneg_right hpow hKδ
  have hcard : (Finset.Icc (j + 1) (j₀ + j)).card = j₀ := by
    rw [Nat.card_Icc]
    omega
  calc ∑ k ∈ Finset.Icc (j + 1) (j₀ + j),
        r ^ k * (F (j₀ + j - k) - F (j₀ + j))
      ≤ ∑ _k ∈ Finset.Icc (j + 1) (j₀ + j), r ^ (j + 1) * (K₀ * δ) :=
        Finset.sum_le_sum hterm
    _ = (j₀ : ℝ) * (r ^ (j + 1) * (K₀ * δ)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = K₀ * δ * ((j₀ : ℝ) * r) * r ^ j := by
        rw [pow_succ]
        ring

/-- `F` is an arbitrary real sequence; nothing below mentions `J`, the coefficient
field, the cutoff `L` or the direction `e`.  Under the intended instantiation
`F t = 𝔼[J(□_{L+t}, σ_L^{-1/2}e, σ_L^{1/2}e; a_L)]` the hypotheses read:

* `hFnonneg`: the response mean is nonnegative.  This is NOT part of the §A.4
  display; it is the separate source fact `J ≥ 0` (`e.Jenergyv.nosymm`).  It
  is not needed for the truth of the conclusion — truncating `F` at `0` removes
  it — and is kept only because it shortens the prefix estimate.
* `hcrude`: the initialization `e.iter.init`, i.e. the crude `O(E²γ)` bound
  `F t ≤ K₀ δ₁`, available at every scale of the corridor `[L, L + t]`.
* `hrec`: the finite pre-extension recurrence, whose lag sum ranges over `1 ≤ k
  ≤ t` only.

Establishing `hcrude`, `hrec`, `hFnonneg` for the actual response mean, and
identifying `A`, `C`, `K₀`, `j₀`, `r` with dimension-only constants, is
consumer work not done here; so is the selection of `k₁`. -/
theorem finiteCorridor_weightedDefect_iteration {F : ℕ → ℝ} {A C K₀ δ r : ℝ}
    {j₀ : ℕ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hK₀ : 0 ≤ K₀) (hδ : 0 ≤ δ)
    (hr0 : 0 ≤ r) (hr3 : r ≤ 1 / 3)
    (hFnonneg : ∀ t : ℕ, 0 ≤ F t)
    (hcrude : ∀ t : ℕ, F t ≤ K₀ * δ)
    (hrec : ∀ t : ℕ, j₀ < t →
      F t ≤ A * δ * (δ + r ^ t) +
        C * ∑ k ∈ Finset.Icc 1 t, r ^ k * (F (t - k) - F t)) :
    ∀ j : ℕ, F (j₀ + j) ≤
      finiteCorridorAmplitude A C K₀ r j₀ * δ *
        (δ + finiteCorridorDecayRate C ^ j) := by
  have hgapLe := finiteCorridorGap_le hC
  have hshift : 0 ≤ C * K₀ * (j₀ : ℝ) * r :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hK₀) (Nat.cast_nonneg j₀)) hr0
  have hHrec : ∀ j : ℕ,
      F (j₀ + j) ≤ (A + K₀ + C * K₀ * (j₀ : ℝ) * r) * δ * (δ + r ^ j) +
        C * ∑ k ∈ Finset.Icc 1 j,
          r ^ k * (F (j₀ + (j - k)) - F (j₀ + j)) := by
    intro j
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, pow_zero]
      have h1 : F (j₀ + 0) ≤ K₀ * δ := hcrude (j₀ + 0)
      have h2 : 0 ≤ (A + K₀ + C * K₀ * (j₀ : ℝ) * r) * δ * δ :=
        mul_nonneg (mul_nonneg (by linarith) hδ) hδ
      have h3 : K₀ * δ ≤ (A + K₀ + C * K₀ * (j₀ : ℝ) * r) * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ
      linarith
    · have hraw := hrec (j₀ + j) (by omega)
      have hsplit : Finset.Icc 1 (j₀ + j) =
          Finset.Icc 1 j ∪ Finset.Icc (j + 1) (j₀ + j) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_union]
        omega
      have hdisj : Disjoint (Finset.Icc 1 j) (Finset.Icc (j + 1) (j₀ + j)) := by
        rw [Finset.disjoint_left]
        intro k hk1 hk2
        have h1 := (Finset.mem_Icc.mp hk1).2
        have h2 := (Finset.mem_Icc.mp hk2).1
        omega
      rw [hsplit, Finset.sum_union hdisj] at hraw
      have hinternal :
          ∑ k ∈ Finset.Icc 1 j, r ^ k * (F (j₀ + j - k) - F (j₀ + j)) =
            ∑ k ∈ Finset.Icc 1 j, r ^ k * (F (j₀ + (j - k)) - F (j₀ + j)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkj : k ≤ j := (Finset.mem_Icc.mp hk).2
        have hidx : j₀ + j - k = j₀ + (j - k) := by omega
        rw [hidx]
      rw [hinternal] at hraw
      have hprefixC : C * ∑ k ∈ Finset.Icc (j + 1) (j₀ + j),
            r ^ k * (F (j₀ + j - k) - F (j₀ + j)) ≤
          C * (K₀ * δ * ((j₀ : ℝ) * r) * r ^ j) :=
        mul_le_mul_of_nonneg_left
          (earlyPrefix_sum_le j₀ j hK₀ hδ hr0 (by linarith) hFnonneg hcrude) hC
      have hpow : r ^ (j₀ + j) ≤ r ^ j :=
        pow_le_pow_of_le_one hr0 (by linarith) (by omega)
      have hforce : A * δ * (δ + r ^ (j₀ + j)) ≤ A * δ * (δ + r ^ j) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA hδ)
      have hgeom : 0 ≤ δ + r ^ j := by
        have := pow_nonneg hr0 j
        linarith
      have hK₀G : 0 ≤ K₀ * δ * (δ + r ^ j) :=
        mul_nonneg (mul_nonneg hK₀ hδ) hgeom
      have hXG : C * K₀ * (j₀ : ℝ) * r * δ * r ^ j ≤
          C * K₀ * (j₀ : ℝ) * r * δ * (δ + r ^ j) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hshift hδ)
      linarith
  have hinit : F (j₀ + 0) ≤ K₀ * δ := hcrude (j₀ + 0)
  have hcore := weightedDefect_decay_of_kernel
    (F := fun t : ℕ => F (j₀ + t))
    (A := A + K₀ + C * K₀ * (j₀ : ℝ) * r) (C := C) (K₀ := K₀)
    (K := finiteCorridorAmplitude A C K₀ r j₀) (δ := δ) (r := r)
    (ρ := finiteCorridorDecayRate C)
    hC hδ hr0
    (by simp only [finiteCorridorDecayRate]; linarith)
    (finiteCorridorAmplitude_nonneg j₀ hA hC hK₀ hr0)
    (by simp only [finiteCorridorAmplitude]; linarith)
    (by simp only [finiteCorridorAmplitude]; linarith)
    (finiteCorridorDecayRate_kernel hC hr0 hr3) hinit hHrec
  exact hcore

end Algsuperdiff.Section3.Provider.Homogenization
