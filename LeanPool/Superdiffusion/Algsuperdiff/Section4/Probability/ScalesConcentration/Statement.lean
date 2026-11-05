/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.ScalesConcentration.Chernoff

/-!
# Statement

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Concentration for scale arrays — main statement (`p.concentration.for.scales`)

This module states and proves (`sorry`-free) Proposition
`p.concentration.for.scales` (ABK26, Appendix D, `e.no.bad.scales.twosided`).

## What is proved

* **Step 1 (`Reduction.lean`)** — the deterministic reduction of the row
  exceedance count to `∑_j Z_j`, including the geometric weight bound
  (`Weights.lean`).
* **Steps 2–3 (`Tail.lean`, `TailAssembly.lean`, `Mgf.lean`)** — the geometric
  tail `Zj_tail` and integer MGF `Zj_mgf`.
* **Step 4 (`Chernoff.lean`, `full_mgf_bound`)** — the residue-class MGF bound
  `∫⁻ expZfun ≤ exp(C₆ r⁻¹ (3/λ)^p (m+1))`, via Hölder-over-residues and
  within-class independence (`ColumnsIndep`); generic helpers in `MgfProduct.lean`.
* **Step 5 (`Chernoff.lean`, `count_chernoff_bound`)** — the Chernoff bound on
  `∑_j Z_j`, derived from `full_mgf_bound` by Markov.

Every leg of the assembly is `sorry`-free.

## Independence hypothesis (design choice)

`ColumnsIndep r`: for every residue `b` modulo `r`, the columns `{X_{·, jr+b}:
j ∈ ℤ}`, viewed as `(ℤ → ℝ)`-valued random variables, are mutually independent
(`iIndepFun`).  This is the weakest faithful reading of
`e.independent.columns.twosided` that mathlib's `iIndepFun` A supports cleanly;
it is implied by the paper's two-set `r`-dependence hypothesis (see
`Defs.lean`).

## Deviations from the paper

1. Threshold prefactor `9` in place of `6`, from the clean geometric constant
   `6/s` (`≤ 3/t`) instead of the sharp `4/s`; see `Weights.lean`.  With the
   sharp bound the prefactor would be `6`.  The exponential rate is identical.
2. The proposition is stated for the window `{0, …, m}` (`m₀ = 0`); the general
   `m₀` follows by translating the array `X_{k,j} = X_{k+m₀,j}`, exactly the
   paper's WLOG reduction.

## The moment hypothesis is the lintegral form — a recorded finding

The moment hypothesis is `hmomL: ∀ k j, ∫⁻ ω.ofReal ((X k j ω)^p) ∂P ≤ 1`, the
faithful `ℝ≥0∞` reading of the paper's `E[X_{k,j}^p] ≤ 1` for the nonnegative
array `X`.  The Bochner form `∫ (X k j)^p ∂P ≤ 1` is **not** usable: Bochner
integration returns the junk value `0` for a non-integrable nonnegative
function, so a heavy-tailed i.i.d. array satisfies the Bochner hypothesis
vacuously while `∫⁻ expZfun = ⊤`, which makes the proposition false as stated.
-/

namespace Algsuperdiff.Section4.Probability.ScalesConcentration

open MeasureTheory ProbabilityTheory Finset Real
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Proposition `p.concentration.for.scales`** (`e.no.bad.scales.twosided`),
stated for the window `{0, …, m}` (`m₀ = 0`).

For a nonnegative array `X` with unit `p`-th moments and residue-class
independence, the density of "bad scales" — rows `k` whose geometrically
weighted sum `Y_k = ∑_j 3^{-s|k-j|} X_{k,j}` exceeds the threshold — is
exponentially unlikely to exceed `θ`.

The universal constant is `Cstar = 16 C₆ / log 3`; the threshold prefactor is
`9` (paper: `6`), see the module docstring.

## Moment hypothesis — the honest reading of `E[X^p] ≤ 1`

The `p`-th moment hypothesis is stated in the **lintegral form** `hmomL : ∀ k
j, ∫⁻ ω.ofReal ((X k j ω) ^ p) ∂P ≤ 1`.  This is the faithful reading of the
paper's `E[X_{k,j}^p] ≤ 1` for the *nonnegative* array `X`: it is the Lebesgue
integral of `X^p` as an unsigned quantity, and it is meaningful even when `X^p`
is not Bochner-integrable.  The Bochner form `∫ ω, (X k j ω)^p ∂P ≤ 1` is
*insufficient* — indeed it makes the statement false — because the Bochner
integral returns the junk value `0` for a non-integrable nonnegative array, so
a heavy-tailed i.i.d. array vacuously satisfies `∫ X^p ≤ 1` while `∫⁻ expZfun =
⊤`. -/
theorem p_concentration_for_scales_Cstar
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℤ → ℤ → Ω → ℝ)
    {p s : ℝ} {r : ℕ} (hp : 1 ≤ p) (hs : 0 < s) (hs1 : s ≤ 1)
    (hsp : 1 ≤ s * p) (hr : 1 ≤ r)
    (hXmeas : ∀ k j, Measurable (X k j))
    (hXnn : ∀ k j ω, 0 ≤ X k j ω)
    (hmomL : ∀ k j, ∫⁻ ω, ENNReal.ofReal ((X k j ω) ^ p) ∂P ≤ 1)
    (hindep : ColumnsIndep P X r) :
    ∀ (m : ℕ) (θ : ℝ), (r : ℤ) ≤ (m : ℤ) → 0 < θ → θ ≤ 1 →
      P {ω | θ < (1 / ((m : ℝ) + 1)) *
          ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
            (if 9 * s⁻¹ * Cstar ^ (1 / p) * θ ^ (-1 / p) < Yk X s k ω
              then (1 : ℝ) else 0)}
        ≤ ENNReal.ofReal (Real.exp (-(s * p * θ) / (16 * (r : ℝ)) * ((m : ℝ) + 1))) := by
  classical
  intro m θ hrm hθ0 hθ1
  set lam : ℝ := 3 * Cstar ^ (1 / p) * θ ^ (-1 / p) with hlam
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlam0 : 0 ≤ lam := by
    have : 0 ≤ Cstar ^ (1 / p) := (Real.rpow_nonneg Cstar_pos.le _)
    have hθr : 0 ≤ θ ^ (-1 / p) := Real.rpow_nonneg hθ0.le _
    positivity
  -- the threshold in the event equals `3 λ / s`
  have hthr : 9 * s⁻¹ * Cstar ^ (1 / p) * θ ^ (-1 / p) = 3 * lam / s := by
    rw [hlam]; field_simp; ring
  -- set inclusion into the count event
  have hsub : {ω | θ < (1 / ((m : ℝ) + 1)) *
        ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
          (if 9 * s⁻¹ * Cstar ^ (1 / p) * θ ^ (-1 / p) < Yk X s k ω
            then (1 : ℝ) else 0)}
      ⊆ {ω | ENNReal.ofReal (θ * ((m : ℝ) + 1))
        < ∑' j : ℤ, (Zcount X s lam m j ω : ℝ≥0∞)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [one_div, inv_mul_eq_div, lt_div_iff₀ hmpos] at hω
    -- hω: θ * ((m:ℝ)+1) < ∑ k, (if 9*… < Yk then 1 else 0)
    have hcast : ENNReal.ofReal (∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
            (if 9 * s⁻¹ * Cstar ^ (1 / p) * θ ^ (-1 / p) < Yk X s k ω
              then (1 : ℝ) else 0))
        = ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
            (if 3 * lam / s < Yk X s k ω then (1 : ℝ≥0∞) else 0) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hthr]
      by_cases h : 3 * lam / s < Yk X s k ω <;> simp [h]
    have hstep1 := sum_indicator_Yk_le_tsum_Zcount (s := s) (lam := lam) hs hs1 X m ω hlam0
      (fun k j => hXnn k j ω)
    calc ENNReal.ofReal (θ * ((m : ℝ) + 1))
        < ENNReal.ofReal (∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
            (if 9 * s⁻¹ * Cstar ^ (1 / p) * θ ^ (-1 / p) < Yk X s k ω
              then (1 : ℝ) else 0)) :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hω
      _ = ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
            (if 3 * lam / s < Yk X s k ω then (1 : ℝ≥0∞) else 0) := hcast
      _ ≤ ∑' j : ℤ, (Zcount X s lam m j ω : ℝ≥0∞) := hstep1
  calc P {ω | θ < (1 / ((m : ℝ) + 1)) *
          ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
            (if 9 * s⁻¹ * Cstar ^ (1 / p) * θ ^ (-1 / p) < Yk X s k ω
              then (1 : ℝ) else 0)}
      ≤ P {ω | ENNReal.ofReal (θ * ((m : ℝ) + 1))
          < ∑' j : ℤ, (Zcount X s lam m j ω : ℝ≥0∞)} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(s * p * θ) / (16 * (r : ℝ)) * ((m : ℝ) + 1))) := by
        rw [hlam]
        exact count_chernoff_bound (P := P) (X := X) hp hs hs1 hsp hr hXmeas hmomL hindep
          m θ hrm hθ0

end Algsuperdiff.Section4.Probability.ScalesConcentration
