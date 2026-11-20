/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupEulerMultiplier.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupMultiplier
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Topology.UniformSpace.Dini
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! # Positive backward Euler spectral approximations -/

@[expose] public section
open Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Dyadic backward Euler multiplier of a nonnegative scalar generator. -/
def dyadicEulerMultiplier (j : ℕ) (x : ℝ) : ℝ :=
  ((1 + x / (2 ^ j : ℕ))⁻¹) ^ (2 ^ j : ℕ)

/-- Increasing the number of Euler steps decreases the scalar approximation. -/
theorem dyadicEulerMultiplier_antitone {x : ℝ} (hx : 0 ≤ x) :
    Antitone (fun j => dyadicEulerMultiplier j x) := by
  apply antitone_nat_of_succ_le
  intro j
  let k : ℕ := 2 ^ j
  have hk : 0 < (k : ℝ) := by dsimp [k]; positivity
  have hp : 0 < 1 + x / (k : ℝ) := by positivity
  have hp2 : 0 < 1 + x / (2 * (k : ℝ)) := by positivity
  have hb : (1 + x / (k : ℝ)) ≤ (1 + x / (2 * (k : ℝ))) ^ 2 := by
    field_simp
    nlinarith [sq_nonneg x]
  have hi : ((1 + x / (2 * (k : ℝ)))⁻¹)^2 ≤ (1 + x / (k : ℝ))⁻¹ := by
    rw [inv_pow]
    exact inv_anti₀ hp hb
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ((1 + x / (2 * (k : ℝ)))⁻¹)^2) hi k
  simpa [dyadicEulerMultiplier, pow_succ, k, Nat.cast_mul, pow_mul, mul_comm] using hh

/-- Scalar backward Euler approximations converge to the exact exponential. -/
theorem dyadicEulerMultiplier_tendsto (x : ℝ) :
    Tendsto (fun j => dyadicEulerMultiplier j x) atTop (𝓝 (Real.exp (-x))) := by
  have h := (Real.tendsto_one_add_div_pow_exp x).inv₀ (Real.exp_ne_zero x)
  have hpow : Tendsto (fun j : ℕ => (2 : ℕ)^j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hh := h.comp hpow
  simpa [dyadicEulerMultiplier, inv_pow, Real.exp_neg, Function.comp_def] using hh

/-- A backward Euler resolvent, expressed in the original resolvent coordinate. -/
def backwardEulerResolventMultiplier (c r : ℝ) : ℝ := r / (r + c * (1 - r))

theorem backwardEulerResolventMultiplier_den_pos {c r : ℝ} (hc : 0 < c)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : 0 < r + c * (1 - r) := by
  by_cases hz : r = 0
  · simp [hz, hc]
  · have hp : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hz)
    exact add_pos_of_pos_of_nonneg hp (mul_nonneg hc.le (sub_nonneg.mpr hr.2))

theorem backwardEulerResolventMultiplier_continuousOn {c : ℝ} (hc : 0 < c) :
    ContinuousOn (backwardEulerResolventMultiplier c) (Set.Icc (0 : ℝ) 1) := by
  apply continuousOn_id.div (continuousOn_id.add (continuousOn_const.mul
    (continuousOn_const.sub continuousOn_id)))
  exact fun r hr => (backwardEulerResolventMultiplier_den_pos hc hr).ne'

theorem backwardEulerResolventMultiplier_graph_identity {c r : ℝ}
    (hc : 0 < c) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    r * (backwardEulerResolventMultiplier c r -
      (backwardEulerResolventMultiplier c r - 1) / c) =
      backwardEulerResolventMultiplier c r := by
  unfold backwardEulerResolventMultiplier
  have hd := (backwardEulerResolventMultiplier_den_pos hc hr).ne'
  field_simp; ring

/-- Continuous dyadic backward Euler approximations including spectral zero. -/
def resolventEulerMultiplier (t : ℝ) (j : ℕ) (r : ℝ) : ℝ :=
  (backwardEulerResolventMultiplier (t / (2 ^ j : ℕ)) r) ^ (2 ^ j : ℕ)

theorem resolventEulerMultiplier_eq_rate {t r : ℝ} (hr : 0 < r) (j : ℕ) :
    resolventEulerMultiplier t j r = dyadicEulerMultiplier j (t * (r⁻¹ - 1)) := by
  unfold resolventEulerMultiplier dyadicEulerMultiplier backwardEulerResolventMultiplier
  congr 1
  have hk : (2 ^ j : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem resolventEulerMultiplier_continuousOn {t : ℝ} (ht : 0 < t) (j : ℕ) :
    ContinuousOn (resolventEulerMultiplier t j) (Set.Icc (0 : ℝ) 1) :=
  (backwardEulerResolventMultiplier_continuousOn (by positivity : 0 < t / (2 ^ j : ℕ))).pow _

theorem resolventEulerMultiplier_antitone {t r : ℝ} (ht : 0 < t)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : Antitone (fun j => resolventEulerMultiplier t j r) := by
  by_cases hz : r = 0
  · intro j k hjk
    simp [resolventEulerMultiplier, backwardEulerResolventMultiplier, hz]
  · have hp : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hz)
    have hx : 0 ≤ t * (r⁻¹ - 1) := by
      have hi : 1 ≤ r⁻¹ := (one_le_inv₀ hp).mpr hr.2
      exact mul_nonneg ht.le (sub_nonneg.mpr hi)
    simpa only [resolventEulerMultiplier_eq_rate hp] using dyadicEulerMultiplier_antitone hx

theorem resolventEulerMultiplier_tendsto {t r : ℝ} (ht : 0 < t)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun j => resolventEulerMultiplier t j r) atTop
      (𝓝 (resolventEvolutionMultiplier t r)) := by
  by_cases hz : r = 0
  · simp [resolventEulerMultiplier, backwardEulerResolventMultiplier, hz,
      resolventEvolutionMultiplier_nonpositive ht (le_refl 0)]
  · have hp : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hz)
    rw [resolventEvolutionMultiplier_positive_formula ht hp]
    simpa only [resolventEulerMultiplier_eq_rate hp, neg_mul] using
      dyadicEulerMultiplier_tendsto (t * (r⁻¹ - 1))

/-- Uniform Euler convergence on the entire spectrum, including zero accumulation. -/
theorem resolventEulerMultiplier_tendstoUniformlyOn {t : ℝ} (ht : 0 < t) :
    TendstoUniformlyOn (resolventEulerMultiplier t) (resolventEvolutionMultiplier t)
      atTop (Set.Icc (0 : ℝ) 1) :=
  Antitone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
    (resolventEulerMultiplier_continuousOn ht)
    (fun _ hr => resolventEulerMultiplier_antitone ht hr)
    (resolventEvolutionMultiplier_continuous t).continuousOn
    (fun _ hr => resolventEulerMultiplier_tendsto ht hr)

end
end GinibrePoincare
