/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianDyadicCovariance.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicTents
public import Mathlib.Analysis.SpecificLimits.Normed
/-!
# Alternative Bakry Emery Brownian dyadic covariance

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryBrownianDyadicKernel_tendsto`.
-/

@[expose] public section
open Set Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- The Brownian bridge covariance kernel `min s t - s * t`. -/
def bakryBrownianBridgeKernel (s t : ℝ) : ℝ := min s t - s*t

/-- Clipping of a real number to the unit interval: `max 0 (min 1 s)`. -/
def bakryBrownianClip (s : ℝ) : ℝ := max 0 (min 1 s)

theorem bakryBrownianClip_of_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    bakryBrownianClip s = s := by
  simp [bakryBrownianClip, min_eq_right hs.2, max_eq_right hs.1]

theorem bakryBrownianClip_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    bakryBrownianClip s = 0 := by
  rw [bakryBrownianClip, min_eq_right (hs.trans (by norm_num)), max_eq_left hs]

theorem bakryBrownianClip_of_one_le {s : ℝ} (hs : 1 ≤ s) :
    bakryBrownianClip s = 1 := by
  simp [bakryBrownianClip, min_eq_left hs]

theorem bakryBrownianBridgeKernel_split_ordered (s t : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    bakryBrownianBridgeKernel s t = min s (1-s)*min t (1-t) +
      (bakryBrownianBridgeKernel (bakryBrownianClip (2*s)) (bakryBrownianClip (2*t)) +
       bakryBrownianBridgeKernel (bakryBrownianClip (2*s-1)) (bakryBrownianClip (2*t-1)))/2 := by
  by_cases ht2 : 2*t ≤ 1
  · rw [bakryBrownianClip_of_mem ⟨by linarith [hs.1], by linarith⟩,
      bakryBrownianClip_of_mem ⟨by linarith [ht.1], ht2⟩,
      bakryBrownianClip_of_nonpos (by linarith : 2*s-1 ≤ 0),
      bakryBrownianClip_of_nonpos (by linarith : 2*t-1 ≤ 0)]
    simp only [bakryBrownianBridgeKernel, min_eq_left hst,
      min_eq_left (show s ≤ 1-s by linarith), min_eq_left (show t ≤ 1-t by linarith),
      min_eq_left (show 2*s ≤ 2*t by linarith), min_self, mul_zero, sub_zero]
    ring
  · by_cases hs2 : 2*s ≤ 1
    · rw [bakryBrownianClip_of_mem ⟨by linarith [hs.1], hs2⟩,
        bakryBrownianClip_of_one_le (by linarith : 1 ≤ 2*t),
        bakryBrownianClip_of_nonpos (by linarith : 2*s-1 ≤ 0),
        bakryBrownianClip_of_mem ⟨by linarith, by linarith [ht.2]⟩]
      simp only [bakryBrownianBridgeKernel, min_eq_left hst,
        min_eq_left (show s ≤ 1-s by linarith), min_eq_right (show 1-t ≤ t by linarith),
        min_eq_left hs2, min_eq_left (show 0 ≤ 2*t-1 by linarith), mul_one, zero_mul, sub_self]
      ring
    · rw [bakryBrownianClip_of_one_le (by linarith : 1 ≤ 2*s),
        bakryBrownianClip_of_one_le (by linarith : 1 ≤ 2*t),
        bakryBrownianClip_of_mem ⟨by linarith, by linarith [hs.2]⟩,
        bakryBrownianClip_of_mem ⟨by linarith, by linarith [ht.2]⟩]
      simp only [bakryBrownianBridgeKernel, min_eq_left hst,
        min_eq_right (show 1-s ≤ s by linarith), min_eq_right (show 1-t ≤ t by linarith),
        min_self, mul_one, sub_self, min_eq_left (show 2*s-1 ≤ 2*t-1 by linarith)]
      ring

theorem bakryBrownianBridgeKernel_split (s t : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    bakryBrownianBridgeKernel s t = min s (1-s)*min t (1-t) +
      (bakryBrownianBridgeKernel (bakryBrownianClip (2*s)) (bakryBrownianClip (2*t)) +
       bakryBrownianBridgeKernel (bakryBrownianClip (2*s-1)) (bakryBrownianClip (2*t-1)))/2 := by
  rcases le_total s t with h | h
  · exact bakryBrownianBridgeKernel_split_ordered s t hs ht h
  · have hh := bakryBrownianBridgeKernel_split_ordered t s ht hs h
    simpa only [bakryBrownianBridgeKernel, min_comm, mul_comm] using hh

theorem bakryBrownianClip_mem (s : ℝ) : bakryBrownianClip s ∈ Icc (0 : ℝ) 1 := by
  unfold bakryBrownianClip
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem bakryBrownianBridgeKernel_bounds (s t : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ bakryBrownianBridgeKernel s t ∧ bakryBrownianBridgeKernel s t ≤ 1/4 := by
  rcases hs with ⟨hs0, hs1⟩
  rcases ht with ⟨ht0, ht1⟩
  rcases le_total s t with h | h
  · rw [bakryBrownianBridgeKernel, min_eq_left h]
    constructor <;> nlinarith [sq_nonneg (s-1/2)]
  · rw [bakryBrownianBridgeKernel, min_eq_right h]
    constructor <;> nlinarith [sq_nonneg (t-1/2)]

theorem bakryBrownianClip_double (s : ℝ) :
    bakryBrownianClip (2 * bakryBrownianClip s) = bakryBrownianClip (2*s) ∧
    bakryBrownianClip (2 * bakryBrownianClip s - 1) = bakryBrownianClip (2*s-1) := by
  by_cases h0 : s ≤ 0
  · rw [bakryBrownianClip_of_nonpos h0,
      bakryBrownianClip_of_nonpos (by linarith : 2*s ≤ 0),
      bakryBrownianClip_of_nonpos (by linarith : 2*s-1 ≤ 0)]
    norm_num [bakryBrownianClip]
  · by_cases h1 : 1 ≤ s
    · rw [bakryBrownianClip_of_one_le h1,
        bakryBrownianClip_of_one_le (by linarith : 1 ≤ 2*s),
        bakryBrownianClip_of_one_le (by linarith : 1 ≤ 2*s-1)]
      norm_num [bakryBrownianClip]
    · rw [bakryBrownianClip_of_mem (s := s) ⟨by linarith, by linarith⟩]
      exact ⟨rfl, rfl⟩

theorem bakryBrownianTent_clip (s : ℝ) :
    max 0 (min s (1-s)) = min (bakryBrownianClip s) (1-bakryBrownianClip s) := by
  by_cases h0 : s ≤ 0
  · rw [bakryBrownianClip_of_nonpos h0, min_eq_left (by linarith : s ≤ 1-s), max_eq_left h0]
    norm_num
  · by_cases h1 : 1 ≤ s
    · rw [bakryBrownianClip_of_one_le h1, min_eq_right (by linarith : 1-s ≤ s),
        max_eq_left (by linarith : 1-s ≤ 0)]
      norm_num
    · rw [bakryBrownianClip_of_mem ⟨by linarith, by linarith⟩,
        max_eq_right (le_min (by linarith) (by linarith))]

theorem bakryBrownianBridgeKernel_clipped_split (s t : ℝ) :
    bakryBrownianBridgeKernel (bakryBrownianClip s) (bakryBrownianClip t) =
      max 0 (min s (1-s))*max 0 (min t (1-t)) +
      (bakryBrownianBridgeKernel (bakryBrownianClip (2*s)) (bakryBrownianClip (2*t)) +
       bakryBrownianBridgeKernel (bakryBrownianClip (2*s-1)) (bakryBrownianClip (2*t-1)))/2 := by
  have h := bakryBrownianBridgeKernel_split (bakryBrownianClip s) (bakryBrownianClip t)
    (bakryBrownianClip_mem s) (bakryBrownianClip_mem t)
  rw [(bakryBrownianClip_double s).1, (bakryBrownianClip_double t).1,
    (bakryBrownianClip_double s).2, (bakryBrownianClip_double t).2,
    ← bakryBrownianTent_clip s,← bakryBrownianTent_clip t] at h
  exact h

/-- The Brownian bridge kernel of the dyadic cell `[k / 2^n, (k + 1) / 2^n]`, evaluated at the
rescaled and clipped points `2^n s - k` and `2^n t - k`. -/
def bakryBrownianDyadicCellKernel (n k : ℕ) (s t : ℝ) : ℝ :=
  bakryBrownianBridgeKernel (bakryBrownianClip ((2 : ℝ)^n*s-k))
    (bakryBrownianClip ((2 : ℝ)^n*t-k))

/-- The covariance `s t + ∑_{n < N} 2^(-n) ∑_k T_{n,k}(s) T_{n,k}(t)` of the `N`-th partial
dyadic Brownian series, where `T_{n,k}` are the dyadic tents. -/
def bakryBrownianDyadicKernel (N : ℕ) (s t : Icc (0 : ℝ) 1) : ℝ :=
  (s : ℝ)*(t : ℝ) + ∑ n ∈ Finset.range N, (1/2 : ℝ)^n *
    ∑ k : Fin (2^n), bakryBrownianDyadicTent n k s * bakryBrownianDyadicTent n k t

theorem bakryBrownianDyadicCellKernel_split (n : ℕ) (k : Fin (2 ^ n))
    (s t : Icc (0 : ℝ) 1) :
    bakryBrownianDyadicCellKernel n k.val s t =
      bakryBrownianDyadicTent n k s * bakryBrownianDyadicTent n k t +
      (bakryBrownianDyadicCellKernel (n+1) (2*k.val) s t +
       bakryBrownianDyadicCellKernel (n+1) (2*k.val+1) s t)/2 := by
  have h := bakryBrownianBridgeKernel_clipped_split
    ((2 : ℝ)^n*(s : ℝ)-k.val) ((2 : ℝ)^n*(t : ℝ)-k.val)
  have hc (x : ℝ) : 2*((2 : ℝ)^n*x-k.val) = (2 : ℝ)^(n+1)*x-(2*k.val : ℕ) := by
    simp only [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hc' (x : ℝ) : 2*((2 : ℝ)^n*x-k.val)-1 = (2 : ℝ)^(n+1)*x-(2*k.val+1 : ℕ) := by
    simp only [pow_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  have ht (x : Icc (0 : ℝ) 1) :
      max 0 (min ((2 : ℝ)^n*(x : ℝ)-k.val) (1-((2 : ℝ)^n*(x : ℝ)-k.val))) =
      bakryBrownianDyadicTent n k x := by
    change max 0 (min _ _) = max 0 (min _ _)
    simp only [Nat.cast_add, Nat.cast_one]
    congr 2
    ring
  rw [hc', hc', hc, hc, ht, ht] at h
  exact h

theorem bakryBrownianBridgeKernel_le_tent (s t : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    bakryBrownianBridgeKernel s t ≤ min s (1-s) := by
  rcases hs with ⟨hs0, hs1⟩
  rcases ht with ⟨ht0, ht1⟩
  unfold bakryBrownianBridgeKernel
  apply le_min
  · rcases le_total s t with h | h
    · rw [min_eq_left h]
      nlinarith
    · rw [min_eq_right h]
      nlinarith
  · rcases le_total s t with h | h
    · rw [min_eq_left h]
      nlinarith [mul_nonneg (show 0 ≤ 1-s by linarith) (show 0 ≤ 1-t by linarith)]
    · rw [min_eq_right h]
      nlinarith [mul_nonneg (show 0 ≤ 1-s by linarith) (show 0 ≤ 1-t by linarith)]

theorem bakryBrownianDyadicCellKernel_eq_zero (n : ℕ) (k : Fin (2 ^ n))
    (s t : Icc (0 : ℝ) 1) (hk : bakryBrownianDyadicTent n k s = 0) :
    bakryBrownianDyadicCellKernel n k.val s t = 0 := by
  let a : ℝ := (2 : ℝ)^n*(s : ℝ)-k.val
  let b : ℝ := (2 : ℝ)^n*(t : ℝ)-k.val
  have h0 := (bakryBrownianBridgeKernel_bounds (bakryBrownianClip a) (bakryBrownianClip b)
    (bakryBrownianClip_mem a) (bakryBrownianClip_mem b)).1
  have h1 := bakryBrownianBridgeKernel_le_tent (bakryBrownianClip a) (bakryBrownianClip b)
    (bakryBrownianClip_mem a) (bakryBrownianClip_mem b)
  rw [← bakryBrownianTent_clip] at h1
  have ht : max 0 (min a (1-a)) = 0 := by
    convert hk using 1; simp only [bakryBrownianDyadicTent, ContinuousMap.coe_mk,
      Nat.cast_add, Nat.cast_one]; congr 2; dsimp [a]; ring
  rw [ht] at h1
  exact le_antisymm h1 h0

/-- The residual covariance at level `n`: `2^(-n)` times the sum over the `2^n` dyadic cells of
the cell bridge kernels `bakryBrownianDyadicCellKernel`. -/
def bakryBrownianDyadicResidual (n : ℕ) (s t : Icc (0 : ℝ) 1) : ℝ :=
  (1/2 : ℝ)^n * ∑ k : Fin (2^n), bakryBrownianDyadicCellKernel n k.val s t

theorem bakryBrownianDyadicResidual_bounds (n : ℕ) (s t : Icc (0 : ℝ) 1) :
    0 ≤ bakryBrownianDyadicResidual n s t ∧
      bakryBrownianDyadicResidual n s t ≤ (1/2 : ℝ)^n/4 := by
  have hcell (k : Fin (2^n)) :
      0 ≤ bakryBrownianDyadicCellKernel n k.val s t ∧
      bakryBrownianDyadicCellKernel n k.val s t ≤ 1/4 :=
    bakryBrownianBridgeKernel_bounds _ _ (bakryBrownianClip_mem _) (bakryBrownianClip_mem _)
  have hsum : (∑ k : Fin (2^n), bakryBrownianDyadicCellKernel n k.val s t) ≤ 1/4 := by
    by_cases he : ∃ k, bakryBrownianDyadicTent n k s ≠ 0
    · obtain ⟨k, hk⟩ := he
      rw [Finset.sum_eq_single k]
      · exact (hcell k).2
      · intro j _ hj
        rcases bakryBrownianDyadicTent_disjoint n j k hj s with hz | hz
        · exact bakryBrownianDyadicCellKernel_eq_zero n j s t hz
        · exact (hk hz).elim
      · simp
    · push Not at he
      have hz (k : Fin (2^n)) := bakryBrownianDyadicCellKernel_eq_zero n k s t (he k)
      simp only [hz, Finset.sum_const_zero]
      norm_num
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun k _ => (hcell k).1))
  · exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)

theorem bakryBrownian_sum_double (m : ℕ) (f : ℕ → ℝ) :
    (∑ j : Fin (m*2), f j.val) = ∑ k : Fin m, (f (2*k.val)+f (2*k.val+1)) := by
  rw [← finProdFinEquiv.sum_comp (fun j : Fin (m*2) => f j.val)]
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, finProdFinEquiv, Nat.add_comm]

theorem bakryBrownianDyadicResidual_step (n : ℕ) (s t : Icc (0 : ℝ) 1) :
    bakryBrownianDyadicResidual n s t =
      (1/2 : ℝ)^n * (∑ k : Fin (2^n), bakryBrownianDyadicTent n k s * bakryBrownianDyadicTent n k t)
          +
      bakryBrownianDyadicResidual (n+1) s t := by
  unfold bakryBrownianDyadicResidual
  rw [show 2^(n+1) = 2^n*2 from pow_succ 2 n,
    bakryBrownian_sum_double (2^n) (fun j => bakryBrownianDyadicCellKernel (n+1) j s t)]
  simp_rw [bakryBrownianDyadicCellKernel_split n _ s t]
  rw [Finset.sum_add_distrib,← Finset.sum_div, pow_succ]
  ring

theorem bakryBrownianDyadicKernel_add_residual (N : ℕ) (s t : Icc (0 : ℝ) 1) :
    bakryBrownianDyadicKernel N s t + bakryBrownianDyadicResidual N s t = min (s : ℝ) (t : ℝ) := by
  induction N with
  | zero =>
    simp only [bakryBrownianDyadicKernel, bakryBrownianDyadicResidual, Finset.range_zero,
      Finset.sum_empty, add_zero, pow_zero, one_mul]
    rw [show (∑ k : Fin (2^0), bakryBrownianDyadicCellKernel 0 k.val s t) =
        bakryBrownianDyadicCellKernel 0 0 s t by exact Fin.sum_univ_one _]
    unfold bakryBrownianDyadicCellKernel
    simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero,
      bakryBrownianClip_of_mem s.property, bakryBrownianClip_of_mem t.property,
      bakryBrownianBridgeKernel]
    ring
  | succ N ih =>
    have hr := bakryBrownianDyadicResidual_step N s t
    unfold bakryBrownianDyadicKernel at ih ⊢
    rw [Finset.sum_range_succ]
    linarith

theorem bakryBrownianDyadicResidual_tendsto (s t : Icc (0 : ℝ) 1) :
    Tendsto (fun N => bakryBrownianDyadicResidual N s t) atTop (𝓝 0) := by
  have hpow : Tendsto (fun N : ℕ => (1/2 : ℝ)^N / 4) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)).div_const 4
  exact squeeze_zero (fun N => (bakryBrownianDyadicResidual_bounds N s t).1)
    (fun N => (bakryBrownianDyadicResidual_bounds N s t).2) hpow

theorem bakryBrownianDyadicKernel_tendsto (s t : Icc (0 : ℝ) 1) :
    Tendsto (fun N => bakryBrownianDyadicKernel N s t) atTop (𝓝 (min (s : ℝ) (t : ℝ))) := by
  have h := (tendsto_const_nhds (x := min (s : ℝ) (t : ℝ)) (f := atTop)).sub
      (bakryBrownianDyadicResidual_tendsto s t)
  simpa only [sub_zero] using h.congr (fun N => by
    have hh := bakryBrownianDyadicKernel_add_residual N s t
    linarith)

end
end GinibrePoincare
