/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.MixedSmoothness.MixedLittlewoodPaley
public import LeanPool.FunctionSpaces.Rd.Atoms.AtomSynthesis
public import Mathlib.Analysis.SpecificLimits.Normed

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Approximation on hyperbolic crosses

The **level** of `k ∈ ℕ^d` is `|k|_1 = ∑_i k_i` (`Rd.level`), and the **hyperbolic cross** of level
`N` is `{k : |k|_1 ≤ N}` (`Rd.hyperbolicCross`). The partial sum
`S_N f = ∑_{|k|_1 ≤ N} δ_k ⋆ f` of the tensor Littlewood–Paley decomposition
(`Rd.hyperbolicSum`) is band-limited to the union of the dyadic rectangles of these blocks.

* **The tail** (`Rd.enorm_sub_hyperbolicSum_le`): `‖f - S_N f‖_p ≤ ∑_{|k|_1 > N} ‖δ_k ⋆ f‖_p`, by
  the tensor Littlewood–Paley decomposition.
* **Counting** (`Rd.card_levelSet_le`): `#{k ∈ ℕ^d : |k|_1 = n} ≤ (n + 1)^(d-1)`, since an index of
  level `n` is determined by its first `d - 1` coordinates.
* **The rate** (`Rd.enorm_sub_hyperbolicSum_le_mixedLPNorm`): for real `s` and `1 ≤ q ≤ ∞`,
  `‖f - S_N f‖_p ≤ C 2^(-sN) (N + 1)^((d-1)(1-1/q)) ‖(2^(s|k|_1) ‖δ_k ⋆ f‖_p)_k‖_{ℓ_q}` with
  `C = ∑_l 2^(-sl) (l + 1)^((d-1)(1-1/q))` (`Rd.hyperbolicCrossConst`): on each level Hölder's
  inequality costs `#{|k|_1 = n}^(1-1/q) ≤ (n + 1)^((d-1)(1-1/q))`, and
  `∑_{n > N} 2^(-sn) (n + 1)^a ≤ C 2^(-sN) (N + 1)^a`. For `s > 0` the constant is finite
  (`Rd.hyperbolicCrossConst_ne_top`, `Rd.enorm_sub_hyperbolicSum_le_of_pos`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

open ENNReal (dyadicWeight lqNorm)

namespace Rd

variable {d : ℕ}

/-! ### Levels -/

/-- The **level** `|k|_1 = ∑_i k_i` of `k ∈ ℕ^d`. -/
def level (k : Fin d → ℕ) : ℕ := ∑ i, k i

/-- A coordinate is at most the level. -/
theorem le_level (k : Fin d → ℕ) (i : Fin d) : k i ≤ level k :=
  Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)

/-- The indices of level `n`, `{k ∈ ℕ^d : |k|_1 = n}`: Mathlib's
`Finset.Nat.antidiagonalTuple d n`. -/
def levelSet (n : ℕ) : Finset (Fin d → ℕ) := Finset.Nat.antidiagonalTuple d n

/-- `k` lies in the level set of `n` iff `|k|_1 = n`. -/
theorem mem_levelSet {n : ℕ} {k : Fin d → ℕ} : k ∈ levelSet n ↔ level k = n :=
  Finset.Nat.mem_antidiagonalTuple

/-- **Counting**: `#{k ∈ ℕ^d : |k|_1 = n} ≤ (n + 1)^(d-1)`, since an index of level `n` is
determined by its first `d - 1` coordinates. -/
theorem card_levelSet_le (n : ℕ) : (levelSet (d := d) n).card ≤ (n + 1) ^ (d - 1) := by
  cases d with
  | zero =>
    calc (levelSet (d := 0) n).card
        ≤ (Fintype.piFinset fun _ : Fin 0 => Finset.range (n + 1)).card :=
          Finset.card_le_card fun k _ => Fintype.mem_piFinset.2 fun i => i.elim0
      _ = (n + 1) ^ (0 - 1) := by simp
  | succ e =>
    refine (Finset.card_le_card_of_injOn (fun k : Fin (e + 1) → ℕ => fun i : Fin e => k i.castSucc)
      (t := Fintype.piFinset fun _ : Fin e => Finset.range (n + 1)) (fun k hk => ?_)
      (fun k hk k' hk' hkk' => ?_)).trans ?_
    · have hk' := mem_levelSet.1 hk
      simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
      exact fun i => Nat.lt_succ_of_le (hk' ▸ le_level k _)
    · have h1 := mem_levelSet.1 hk
      have h2 := mem_levelSet.1 hk'
      have hcast : ∀ i : Fin e, k i.castSucc = k' i.castSucc := fun i => congr_fun hkk' i
      simp only [level, Fin.sum_univ_castSucc] at h1 h2
      have hsum : ∑ i : Fin e, k i.castSucc = ∑ i : Fin e, k' i.castSucc :=
        Finset.sum_congr rfl fun i _ => hcast i
      funext i
      cases i using Fin.lastCases with
      | last => omega
      | cast i => exact hcast i
    · simp [Fintype.card_piFinset]

/-- `2^(s|k|_1) = ∏_i 2^(s k_i)`. -/
theorem mixedWeight_eq_dyadicWeight_level (s : ℝ) (k : Fin d → ℕ) :
    mixedWeight s k = dyadicWeight s (level k) := by
  rw [mixedWeight, level]
  induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
  | empty => simp [ENNReal.dyadicWeight_zero_right]
  | insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ENNReal.dyadicWeight_add_nat]

/-- **Regrouping by levels**: `∑_k F_k ≤ ∑_n ∑_{|k|_1 = n} F_k`. -/
theorem tsum_le_tsum_levelSet (F : (Fin d → ℕ) → ℝ≥0∞) :
    ∑' k, F k ≤ ∑' n, ∑ k ∈ levelSet n, F k := by
  rw [tsum_eq_iSup_sum]
  refine iSup_le fun T => ?_
  calc ∑ k ∈ T, F k = ∑ n ∈ T.image level, ∑ k ∈ T.filter (fun k => level k = n), F k :=
        (Finset.sum_fiberwise_of_maps_to (fun k hk => Finset.mem_image_of_mem level hk) F).symm
    _ ≤ ∑ n ∈ T.image level, ∑ k ∈ levelSet n, F k :=
        Finset.sum_le_sum fun n _ => Finset.sum_le_sum_of_subset fun k hk =>
          mem_levelSet.2 (Finset.mem_filter.1 hk).2
    _ ≤ ∑' n, ∑ k ∈ levelSet n, F k := sum_le_tsum _

/-- **Hölder's inequality on a finite set**: `∑_{k ∈ S} x_k ≤ #S^(1-1/q) ‖x‖_{ℓ_q}` for
`1 ≤ q ≤ ∞`. -/
theorem sum_le_card_rpow_mul_lqNorm {q : ℝ≥0∞} (hq : 1 ≤ q) (S : Finset (Fin d → ℕ))
    (x : (Fin d → ℕ) → ℝ≥0∞) :
    ∑ k ∈ S, x k ≤ (S.card : ℝ≥0∞) ^ (1 - 1 / q.toReal) * lqNorm q x := by
  rcases eq_or_ne q ∞ with rfl | hq'
  · simp only [ENNReal.toReal_top, div_zero, sub_zero, ENNReal.rpow_one, ENNReal.lqNorm_top]
    calc ∑ k ∈ S, x k ≤ ∑ _k ∈ S, ⨆ k', x k' := Finset.sum_le_sum fun k _ => le_iSup x k
      _ = (S.card : ℝ≥0∞) * ⨆ k', x k' := by rw [Finset.sum_const, nsmul_eq_mul]
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  set r := q.toReal
  have hr : 1 ≤ r := ENNReal.one_le_toReal_of_one_le hq hq'
  have hr0 : 0 < r := by linarith
  have hpow : (∑ k ∈ S, x k) ^ r ≤ (S.card : ℝ≥0∞) ^ (r - 1) * lqNorm q x ^ r := by
    refine (ENNReal.rpow_sum_le_const_mul_sum_rpow (s := S) (f := x) hr).trans
      (mul_le_mul' le_rfl ?_)
    rw [ENNReal.lqNorm_rpow hq0 hq']
    exact sum_le_tsum _
  calc ∑ k ∈ S, x k = ((∑ k ∈ S, x k) ^ r) ^ (1 / r) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
    _ ≤ ((S.card : ℝ≥0∞) ^ (r - 1) * lqNorm q x ^ r) ^ (1 / r) :=
        ENNReal.rpow_le_rpow hpow (by positivity)
    _ = (S.card : ℝ≥0∞) ^ (1 - 1 / r) * lqNorm q x := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
        congr 2
        field_simp

/-! ### The series of the rate -/

/-- **A polynomial times a geometric series converges**:
`∑_l 2^(-sl) (l + 1)^a < ∞` for `s > 0` and `a ≥ 0` (Mathlib's
`summable_pow_mul_geometric_of_norm_lt_one`). -/
theorem tsum_dyadicWeight_mul_rpow_ne_top {s : ℝ} (hs : 0 < s) {a : ℝ} (ha : 0 ≤ a) :
    ∑' l : ℕ, dyadicWeight (-s) l * ((l + 1 : ℕ) : ℝ≥0∞) ^ a ≠ ∞ := by
  set K := ⌈a⌉₊
  set r : ℝ := (2 : ℝ) ^ (-s)
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hsum : Summable fun l : ℕ => r ^ l * (((l + 1 : ℕ) : ℝ) ^ K) := by
    have h := (summable_nat_add_iff 1).2 (summable_pow_mul_geometric_of_norm_lt_one K
      (r := r) (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1))
    refine (h.mul_left r⁻¹).congr fun l => ?_
    simp only [pow_succ]
    field_simp
  have hterm : ∀ l : ℕ, dyadicWeight (-s) l * ((l + 1 : ℕ) : ℝ≥0∞) ^ a ≤
      ENNReal.ofReal (r ^ l * (((l + 1 : ℕ) : ℝ) ^ K)) := fun l => by
    have h1 : dyadicWeight (-s) l = ENNReal.ofReal (r ^ l) := by
      rw [ENNReal.dyadicWeight_eq_pow, ENNReal.ofReal_pow hr0.le]
      congr 1
      rw [show r = (2 : ℝ) ^ (-s) from rfl, ← ENNReal.ofReal_rpow_of_pos two_pos,
        ENNReal.ofReal_ofNat]
    have h2 : ((l + 1 : ℕ) : ℝ≥0∞) ^ a ≤ ENNReal.ofReal (((l + 1 : ℕ) : ℝ) ^ K) := by
      rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) ha]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos l) (Nat.le_ceil a)
    rw [h1, ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' le_rfl h2
  refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hterm)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

/-- **The tail of the rate series**: `∑_{n > N} 2^(-sn) (n + 1)^a ≤ C 2^(-sN) (N + 1)^a` with
`C = ∑_l 2^(-sl) (l + 1)^a`, from `n + 1 ≤ (n - N + 1)(N + 1)`. -/
theorem tsum_tail_le (s : ℝ) {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    ∑' n : ℕ, (if N < n then dyadicWeight (-s) n * ((n + 1 : ℕ) : ℝ≥0∞) ^ a else 0) ≤
      (∑' l : ℕ, dyadicWeight (-s) l * ((l + 1 : ℕ) : ℝ≥0∞) ^ a) *
        (dyadicWeight (-s) N * ((N + 1 : ℕ) : ℝ≥0∞) ^ a) := by
  rw [← CompleteLattice.summable.sum_add_tsum_nat_add' (k := N)]
  have hzero : ∑ i ∈ Finset.range N,
      (if N < i then dyadicWeight (-s) i * ((i + 1 : ℕ) : ℝ≥0∞) ^ a else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have : ¬ N < i := by
        have := Finset.mem_range.1 hi
        omega
      simp [this]
  rw [hzero, zero_add, ← ENNReal.tsum_mul_right]
  refine tsum_le_tsum fun l => ?_
  split_ifs with h
  · rw [ENNReal.dyadicWeight_add_nat]
    calc dyadicWeight (-s) l * dyadicWeight (-s) N * ((l + N + 1 : ℕ) : ℝ≥0∞) ^ a
        ≤ dyadicWeight (-s) l * dyadicWeight (-s) N *
            (((l + 1 : ℕ) : ℝ≥0∞) ^ a * ((N + 1 : ℕ) : ℝ≥0∞) ^ a) := by
          refine mul_le_mul' le_rfl ?_
          rw [← ENNReal.mul_rpow_of_nonneg _ _ ha]
          refine ENNReal.rpow_le_rpow ?_ ha
          rw [← Nat.cast_mul]
          exact_mod_cast (by nlinarith : l + N + 1 ≤ (l + 1) * (N + 1))
      _ = dyadicWeight (-s) l * ((l + 1 : ℕ) : ℝ≥0∞) ^ a *
            (dyadicWeight (-s) N * ((N + 1 : ℕ) : ℝ≥0∞) ^ a) := by ring
  · exact zero_le

/-! ### Hyperbolic cross partial sums -/

/-- The **hyperbolic cross** `{k ∈ ℕ^d : |k|_1 ≤ N}`. -/
def hyperbolicCross (N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (N + 1)).filter fun k => level k ≤ N

/-- `k` lies in the hyperbolic cross of level `N` iff `|k|_1 ≤ N`. -/
theorem mem_hyperbolicCross {N : ℕ} {k : Fin d → ℕ} : k ∈ hyperbolicCross N ↔ level k ≤ N := by
  simp only [hyperbolicCross, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨fun i => Nat.lt_succ_of_le ((le_level k i).trans h), h⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **hyperbolic cross partial sum** `S_N f = ∑_{|k|_1 ≤ N} δ_k ⋆ f`, band-limited to the union
of the dyadic rectangles of the blocks with `|k|_1 ≤ N`. -/
noncomputable def hyperbolicSum (hp : p ≠ ∞) (N : ℕ)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) : Lp ℂ p (volume : Measure (Fin d → ℝ)) :=
  ∑ k ∈ hyperbolicCross N, mixedBlock hp k f

/-- **The tail of the hyperbolic cross**: `‖f - S_N f‖_p ≤ ∑_{|k|_1 > N} ‖δ_k ⋆ f‖_p`, by the tensor
Littlewood–Paley decomposition. -/
theorem enorm_sub_hyperbolicSum_le (hp : p ≠ ∞) (N : ℕ)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖f - hyperbolicSum hp N f‖ₑ ≤
      ∑' k, if level k ≤ N then 0 else ‖mixedBlock hp k f‖ₑ := by
  set u : (Fin d → ℕ) → Lp ℂ p (volume : Measure (Fin d → ℝ)) := fun k =>
    if level k ≤ N then 0 else mixedBlock hp k f
  have hrep : Tendsto (fun J => ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (J + 1)),
      u k) atTop (𝓝 (f - hyperbolicSum hp N f)) := by
    refine ((tendsto_sum_mixedBlock hp f).sub_const (hyperbolicSum hp N f)).congr' ?_
    filter_upwards [eventually_ge_atTop N] with J hJ
    have hcross : (Fintype.piFinset fun _ : Fin d => Finset.range (J + 1)).filter
        (fun k => level k ≤ N) = hyperbolicCross N := by
      ext k
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, mem_hyperbolicCross]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨fun i => Nat.lt_succ_of_le (((le_level k i).trans h).trans hJ), h⟩
    simp only [u, hyperbolicSum]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, ← hcross, eq_comm, eq_sub_iff_add_eq,
      add_comm, Finset.sum_filter_add_sum_filter_not]
  refine (ENNReal.le_tsum_of_tendsto_finsetSum (Q := fun x : Lp ℂ p (volume : Measure (Fin d →
    ℝ)) =>
    ‖x‖ₑ) (C := 1) ENNReal.one_ne_top (fun x y => eNorm_add_le x y) (fun x => (one_mul _).ge)
    hrep).trans (le_of_eq ?_)
  refine tsum_congr fun k => ?_
  by_cases h : level k ≤ N <;> simp [u, h]

/-- The **constant of hyperbolic cross approximation**,
`C(d, s, q) = ∑_l 2^(-sl) (l + 1)^((d-1)(1-1/q)) ∈ [0, ∞]`. -/
noncomputable def hyperbolicCrossConst (d : ℕ) (s : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' l : ℕ, dyadicWeight (-s) l * ((l + 1 : ℕ) : ℝ≥0∞) ^ (((d - 1 : ℕ) : ℝ) * (1 - 1 / q.toReal))

/-- The constant of hyperbolic cross approximation is finite for `s > 0` and `1 ≤ q ≤ ∞`
(`Rd.tsum_dyadicWeight_mul_rpow_ne_top` with `a = (d-1)(1-1/q) ≥ 0`). -/
theorem hyperbolicCrossConst_ne_top {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    hyperbolicCrossConst d s q ≠ ∞ :=
  tsum_dyadicWeight_mul_rpow_ne_top hs
    (mul_nonneg (Nat.cast_nonneg _) (one_sub_one_div_toReal_nonneg hq))

/-- **Hyperbolic cross approximation**: for `1 ≤ p < ∞`, `f ∈ L_p(ℝ^d)`, real `s`, `1 ≤ q ≤ ∞`
and `N ∈ ℕ`,
`‖f - S_N f‖_p ≤ C 2^(-sN) (N + 1)^((d-1)(1-1/q)) ‖(2^(s|k|_1) ‖δ_k ⋆ f‖_p)_k‖_{ℓ_q}` with
`C = Rd.hyperbolicCrossConst d s q ∈ [0, ∞]`. The constant is finite for `s > 0` and `∞` for
`s ≤ 0`; `Rd.enorm_sub_hyperbolicSum_le_of_pos` states the bound for `s > 0` with `C` as a real
number. -/
theorem enorm_sub_hyperbolicSum_le_mixedLPNorm (hp : p ≠ ∞) (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (N : ℕ) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖f - hyperbolicSum hp N f‖ₑ ≤ hyperbolicCrossConst d s q *
        (dyadicWeight (-s) N * ((N + 1 : ℕ) : ℝ≥0∞) ^ (((d - 1 : ℕ) : ℝ) * (1 - 1 / q.toReal))) *
        mixedLPNorm hp s q f := by
  unfold hyperbolicCrossConst
  set a := ((d - 1 : ℕ) : ℝ) * (1 - 1 / q.toReal)
  have hq1 := one_sub_one_div_toReal_nonneg hq
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) hq1
  set X := mixedLPNorm hp s q f
  -- each level costs `2^(-sn) (n + 1)^a X`
  have hlevel : ∀ n, ∑ k ∈ levelSet n, ‖mixedBlock hp k f‖ₑ ≤
      dyadicWeight (-s) n * ((n + 1 : ℕ) : ℝ≥0∞) ^ a * X := fun n => by
    have hw : ∀ k ∈ levelSet n, ‖mixedBlock hp k f‖ₑ =
        dyadicWeight (-s) n * (mixedWeight s k * ‖mixedBlock hp k f‖ₑ) := fun k hk => by
      rw [mixedWeight_eq_dyadicWeight_level, mem_levelSet.1 hk, ← mul_assoc,
        ENNReal.dyadicWeight_neg_mul_self, one_mul]
    rw [Finset.sum_congr rfl hw, ← Finset.mul_sum, mul_assoc]
    refine mul_le_mul' le_rfl ((sum_le_card_rpow_mul_lqNorm hq (levelSet n)
      fun k => mixedWeight s k * ‖mixedBlock hp k f‖ₑ).trans (mul_le_mul' ?_ le_rfl))
    calc ((levelSet (d := d) n).card : ℝ≥0∞) ^ (1 - 1 / q.toReal)
        ≤ (((n + 1) ^ (d - 1) : ℕ) : ℝ≥0∞) ^ (1 - 1 / q.toReal) :=
          ENNReal.rpow_le_rpow (by exact_mod_cast card_levelSet_le n) hq1
      _ = ((n + 1 : ℕ) : ℝ≥0∞) ^ a := by
          rw [Nat.cast_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  calc ‖f - hyperbolicSum hp N f‖ₑ
      ≤ ∑' k, (if level k ≤ N then 0 else ‖mixedBlock hp k f‖ₑ) :=
        enorm_sub_hyperbolicSum_le hp N f
    _ ≤ ∑' n, ∑ k ∈ levelSet n, (if level k ≤ N then 0 else ‖mixedBlock hp k f‖ₑ) :=
        tsum_le_tsum_levelSet _
    _ ≤ ∑' n : ℕ, (if N < n then dyadicWeight (-s) n * ((n + 1 : ℕ) : ℝ≥0∞) ^ a else 0) * X := by
        refine tsum_le_tsum fun n => ?_
        have hk : ∀ k ∈ levelSet n, (if level k ≤ N then 0 else ‖mixedBlock hp k f‖ₑ) =
            if N < n then ‖mixedBlock hp k f‖ₑ else 0 := fun k hk => by
          rw [mem_levelSet.1 hk]
          split_ifs <;> first | rfl | omega
        rw [Finset.sum_congr rfl hk]
        split_ifs with h
        · exact hlevel n
        · simp
    _ = (∑' n : ℕ, (if N < n then dyadicWeight (-s) n * ((n + 1 : ℕ) : ℝ≥0∞) ^ a else 0)) * X :=
        ENNReal.tsum_mul_right
    _ ≤ _ := mul_le_mul' (tsum_tail_le s ha N) le_rfl

/-- **Hyperbolic cross approximation for `s > 0`**: for `1 ≤ p < ∞`, `f ∈ L_p(ℝ^d)`, `s > 0`,
`1 ≤ q ≤ ∞` and `N ∈ ℕ`, with the real constant `C = C(d, s, q) < ∞`,
`‖f - S_N f‖_p ≤ C 2^(-sN) (N + 1)^((d-1)(1-1/q)) ‖(2^(s|k|_1) ‖δ_k ⋆ f‖_p)_k‖_{ℓ_q}`
(`Rd.enorm_sub_hyperbolicSum_le_mixedLPNorm`, `Rd.hyperbolicCrossConst_ne_top`). -/
theorem enorm_sub_hyperbolicSum_le_of_pos (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (N : ℕ) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖f - hyperbolicSum hp N f‖ₑ ≤ ((hyperbolicCrossConst d s q).toNNReal : ℝ≥0∞) *
        (dyadicWeight (-s) N * ((N + 1 : ℕ) : ℝ≥0∞) ^ (((d - 1 : ℕ) : ℝ) * (1 - 1 / q.toReal))) *
        mixedLPNorm hp s q f := by
  rw [ENNReal.coe_toNNReal (hyperbolicCrossConst_ne_top hs hq)]
  exact enorm_sub_hyperbolicSum_le_mixedLPNorm hp s hq N f

end Rd
