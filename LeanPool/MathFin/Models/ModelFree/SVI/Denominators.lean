/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.Matrices
public import Mathlib.Analysis.Normed.Field.Basic

/-! # Companion and Hermite matrices, and their denominators

Part of the SVI polynomial-sign certificate (#174).

The companion matrix `companion f n`, the Hermite matrix `hermite f q n` of traces of
`q·Xⁱ⁺ʲ`, and the factor `leadingCoeff^38`, positive when the leading coefficient is nonzero, which
clears every denominator for `n ≤ 9` and `q.natDegree ≤ 22` (`clearedHermite_eq_smul`).

## Main definitions

* `companion`: the companion matrix of `f` at size `n`, normalised by the leading coefficient.
* `hermite`: the Hermite matrix of `f` with weight `q` at size `n`; entry `(i, j)` is
  `∑ᵣ qᵣ·tr(Cⁱ⁺ʲ⁺ʳ)` for the companion matrix `C`.

## Main results

* `trace_companion_pow`: `tr(Cʳ) = leadingCoeff⁻¹ ^ r · tr(scaledCompanion ^ r)`.
* `clear_scalar_power`: for `ℓ ≠ 0` and `r ≤ 38`, `ℓ^38 · (ℓ⁻¹)^r = ℓ^(38 - r)`.
* `clearedHermite_eq_smul`: for `leadingCoeff ≠ 0`, `n ≤ 9` and `q.natDegree ≤ 22`,
  `clearedHermite f q n = leadingCoeff^38 • hermite f q n`.
* `clearing_factor_pos`: `0 < leadingCoeff^38` when the leading coefficient is nonzero.

## Tags

Hermite matrix, companion matrix, clearing denominators, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- The companion matrix of `f` at size `n`, normalised by the leading coefficient. -/
noncomputable def companion (f : ℝ[X]) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  f.leadingCoeff⁻¹ • scaledCompanion f n

/-- The Hermite matrix of `f` with weight `q` at size `n`: entry `(i, j)` is `∑ᵣ qᵣ·tr(Cⁱ⁺ʲ⁺ʳ)` for
the companion matrix `C`. -/
noncomputable def hermite (f q : ℝ[X]) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ ∑ r ∈ q.support,
    q.coeff r * Matrix.trace ((companion f n) ^ (i.val + j.val + r))

theorem trace_companion_pow (f : ℝ[X]) (n r : ℕ) :
    Matrix.trace ((companion f n)^r) =
      f.leadingCoeff⁻¹ ^ r * Matrix.trace ((scaledCompanion f n)^r) := by
  simp [companion, _root_.smul_pow, Matrix.trace_smul]

theorem clear_scalar_power (ell : ℝ) (he : ell ≠ 0) (r : ℕ) (hr : r ≤ 38) :
    ell^38 * (ell⁻¹)^r = ell^(38-r) := by
  rw [inv_pow, ← pow_sub₀ ell he hr]

theorem clearedHermite_eq_smul (f q : ℝ[X]) (n : ℕ)
    (hf : f.leadingCoeff ≠ 0) (hn : n ≤ 9) (hq : q.natDegree ≤ 22) :
    clearedHermite f q n = f.leadingCoeff^38 • hermite f q n := by
  ext i j
  simp only [clearedHermite, hermite, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, trace_companion_pow]
  apply Finset.sum_congr rfl
  intro r hr
  have hb := exponent_bound n hn i j r ((le_natDegree_of_ne_zero
    (mem_support_iff.mp hr)).trans hq)
  rw [← clear_scalar_power f.leadingCoeff hf _ hb]
  ring

theorem clearing_factor_pos (f : ℝ[X]) (hf : f.leadingCoeff ≠ 0) :
    0 < f.leadingCoeff^38 := by positivity

end SVI
end MathFin
