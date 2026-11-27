/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Lq
public import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Analysis.PSeries
public import Mathlib.Data.Nat.Log

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Cauchy condensation with power weights and dyadic sums

For a **decreasing** sequence `b : ℕ → ℝ≥0∞` and a real exponent `γ`, the weighted series
`∑ₙ (n + 1) ^ γ b n` and its dyadic version `∑ₖ 2 ^ (k (γ + 1)) b (2 ^ k)` are comparable:

* `tsum_pow_mul_le_dyadic`:
  `∑ₙ (n+1)^γ b n ≤ b 0 + 2^(max γ 0) ∑ₖ 2^(k(γ+1)) b (2^k)`;
* `dyadic_le_tsum_pow_mul`:
  `∑ₖ 2^(k(γ+1)) b (2^(k+1)) ≤ 2^(max (-γ) 0) ∑ₙ (n+1)^γ b n`;

and the analogous statements for suprema, `iSup_pow_mul_le_dyadic` and
`dyadic_le_iSup_pow_mul`; for the sequence capped at `b (2^m)`,
`∑ₖ min(b k, b (2^m)) ≤ 2 ∑_{l ≥ 0} 2^(m+l) b (2^(m+l))` (`tsum_min_le_dyadic`); and
`∑ₖ 2^k b (2^k) ≤ 2 ∑ₙ b n` (`tsum_two_pow_mul_le_two_mul`).  The proof
splits `ℕ \ {0}` into the dyadic blocks `[2^k, 2^(k+1))`, which have `2^k` elements, on which
`b` is at most `b (2^k)` and at least `b (2^(k+1))`, and on which `(n+1)^γ` is within a factor
`2^|γ|` of `2^(kγ)`. Every `n ≥ 1` is `2^k + i` for exactly one pair with `0 ≤ i < 2^k`
(`Nat.exists_eq_two_pow_add`, `Nat.two_pow_add_eq_iff`), so a series over `ℕ` is its first term
plus the sums over these blocks (`tsum_eq_add_tsum_two_pow_add`, with the finite form
`sum_range_two_pow_eq`).

For `γ = 0` this is Cauchy's condensation test (Mathlib: `ENNReal.le_tsum_condensed`,
`ENNReal.tsum_condensed_le`).  The weight `(n + 1) ^ γ` is in general increasing, so the
weighted sequence is not decreasing and Mathlib's version does not apply to it directly.
These estimates are what makes Pietsch's quasi-norm `‖(n^(s - 1/q) E_{n-1})ₙ‖_q` equivalent to
the dyadic one `‖(2^(ks) E_{2^k})ₖ‖_q`.

Three sums over dyadic scales follow:

* **the dyadic sum** `∑_{j ∈ ℕ} min(2^j a, (2^j a)⁻¹) ≤ 4` for `a ∈ [0, ∞]`
  (`tsum_min_two_pow_le`), the sum behind the Hörmander condition for dyadic dilations, with
  `min(x, x⁻¹)² ≤ min(x, x⁻¹)` for its squares (`min_inv_sq_le`);
* **finitely many changed terms**: `∑_j u_j ≤ ∑_j v_j + ∑_{i < N} u_i` when `u_j = v_j` for
  `j ≥ N` (`tsum_le_tsum_add_sum_of_forall_ge_eq`);
* **dyadic scales of an annulus**: a sequence bounded by `M` whose nonzero terms have `t / 2^j`
  in `[a, 2^N a]`, `a > 0`, sums to at most `(N + 1) M` (`tsum_le_of_dyadic_annulus`).

The last section proves the **interpolation inequality for dyadic suprema** (Brezis–Mironescu;
Johnsen–Sickel, Lemma 2): for `σ₁ < σ₀` and `0 < θ < 1`,
`∑_j 2^(j(θσ₀ + (1-θ)σ₁)) a_j ≤ c (sup_j 2^(jσ₀) a_j)^θ (sup_j 2^(jσ₁) a_j)^(1-θ)`
(`tsum_dyadicWeight_mul_le_iSup`, constant `dyadicInterpConst`). The series is split at the
index where the two bounds `2^(jθδ) sup_j 2^(jσ₁) a_j` and `2^(-j(1-θ)δ) sup_j 2^(jσ₀) a_j` of
its terms cross, `δ = σ₀ - σ₁`, and each part is a geometric series.
-/

@[expose] public section

open Finset Filter
open scoped ENNReal

namespace ENNReal

/-- The initial segment `[0, 2^K)` of `ℕ` is `{0}` together with the dyadic blocks
`[2^k, 2^(k+1))`, `k < K`. -/
theorem sum_range_two_pow_eq {M : Type*} [AddCommMonoid M] (g : ℕ → M) (K : ℕ) :
    ∑ n ∈ range (2 ^ K), g n = g 0 + ∑ k ∈ range K, ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), g n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [← Finset.sum_range_add_sum_Ico g (Nat.pow_le_pow_right two_pos (Nat.le_succ K)), ih,
      Finset.sum_range_succ, add_assoc]

/-- For `0 ≤ i < 2^k`, `⌊log₂ (2^k + i)⌋ = k`, since `2^k ≤ 2^k + i < 2^(k+1)`. -/
theorem _root_.Nat.log_two_pow_add {k i : ℕ} (hi : i < 2 ^ k) : Nat.log 2 (2 ^ k + i) = k :=
  Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_add_right _ _) (by rw [pow_succ, mul_two]; omega)

/-- Every `n ≥ 1` is `2^k + i` with `0 ≤ i < 2^k`, namely for `k = ⌊log₂ n⌋`. -/
theorem _root_.Nat.exists_eq_two_pow_add {n : ℕ} (hn : n ≠ 0) :
    ∃ k i, i < 2 ^ k ∧ 2 ^ k + i = n := by
  have h1 := Nat.pow_log_le_self 2 hn
  have h2 := Nat.lt_pow_succ_log_self _root_.one_lt_two n
  rw [pow_succ, mul_two] at h2
  exact ⟨Nat.log 2 n, n - 2 ^ Nat.log 2 n, by omega, by omega⟩

/-- `2^k + i = 2^l + j` with `i < 2^k` and `j < 2^l` iff `k = l` and `i = j`: the level is
`⌊log₂ (2^k + i)⌋` (`Nat.log_two_pow_add`). -/
theorem _root_.Nat.two_pow_add_eq_iff {k l i j : ℕ} (hi : i < 2 ^ k) (hj : j < 2 ^ l) :
    2 ^ k + i = 2 ^ l + j ↔ k = l ∧ i = j := by
  constructor
  · intro h
    have hkl : k = l := by rw [← Nat.log_two_pow_add hi, h, Nat.log_two_pow_add hj]
    subst hkl
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **Splitting `ℕ` into dyadic blocks**: `∑_n g(n) = g(0) + ∑_k ∑_{i<2^k} g(2^k + i)` for every
family `g` in `[0, ∞]`, since `(k, i) ↦ 2^k + i` maps the pairs with `i < 2^k` bijectively onto
the positive integers. The series form of `ENNReal.sum_range_two_pow_eq`. -/
theorem tsum_eq_add_tsum_two_pow_add (g : ℕ → ℝ≥0∞) :
    ∑' n, g n = g 0 + ∑' k, ∑ i : Fin (2 ^ k), g (2 ^ k + i) := by
  have hinj : Function.Injective fun s : (Σ k, Fin (2 ^ k)) => 2 ^ s.1 + (s.2 : ℕ) := by
    rintro ⟨k, i⟩ ⟨l, j⟩ h
    obtain ⟨rfl, h2⟩ := (Nat.two_pow_add_eq_iff i.isLt j.isLt).1 h
    rw [Fin.ext h2]
  rw [tsum_eq_add_tsum_ite 0, ← hinj.tsum_eq ?hs, tsum_sigma']
  · congr 1
    refine tsum_congr fun k => ?_
    rw [tsum_fintype]
    exact Finset.sum_congr rfl fun i _ => ite_eq_right (by positivity)
  · intro n hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hn (ite_eq_left rfl)
    obtain ⟨k, i, hi, rfl⟩ := Nat.exists_eq_two_pow_add hn0
    exact ⟨⟨k, ⟨i, hi⟩⟩, rfl⟩

/-- `2^k = 2^(k · 1)`, the dyadic weight of exponent `1`. -/
theorem natCast_two_pow_eq (k : ℕ) : ((2 ^ k : ℕ) : ℝ≥0∞) = dyadicWeight 1 k := by
  rw [← natCast_two_pow_rpow, ENNReal.rpow_one]

/-- A dyadic block `[2^k, 2^(k+1))` has `2^k` elements. -/
theorem card_Ico_two_pow (k : ℕ) : (Ico (2 ^ k) (2 ^ (k + 1))).card = 2 ^ k := by
  rw [Nat.card_Ico, pow_succ]; omega

/-- On the dyadic block `[2^k, 2^(k+1))`, `(n + 1)^γ ≤ 2^(max γ 0) 2^(kγ)`. -/
theorem natCast_succ_rpow_le {k n : ℕ} (hn : n ∈ Ico (2 ^ k) (2 ^ (k + 1))) (γ : ℝ) :
    ((n + 1 : ℕ) : ℝ≥0∞) ^ γ ≤ 2 ^ max γ 0 * dyadicWeight γ k := by
  rw [Finset.mem_Ico] at hn
  rcases le_or_gt 0 γ with hγ | hγ
  · rw [max_eq_left hγ]
    calc ((n + 1 : ℕ) : ℝ≥0∞) ^ γ ≤ ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) ^ γ := by
          gcongr; exact_mod_cast hn.2
      _ = 2 ^ γ * dyadicWeight γ k := by rw [natCast_two_pow_rpow, dyadicWeight_succ]
  · rw [max_eq_right hγ.le, ENNReal.rpow_zero, one_mul, ← natCast_two_pow_rpow]
    exact rpow_le_rpow_of_nonpos (by exact_mod_cast hn.1.trans (Nat.le_succ n)) hγ.le

/-- On the dyadic block `[2^k, 2^(k+1))`, `2^(kγ) ≤ 2^(max (-γ) 0) (n + 1)^γ`. -/
theorem dyadicWeight_le_natCast_succ_rpow {k n : ℕ} (hn : n ∈ Ico (2 ^ k) (2 ^ (k + 1)))
    (γ : ℝ) : dyadicWeight γ k ≤ 2 ^ max (-γ) 0 * ((n + 1 : ℕ) : ℝ≥0∞) ^ γ := by
  rw [Finset.mem_Ico] at hn
  rcases le_or_gt 0 γ with hγ | hγ
  · rw [max_eq_right (neg_nonpos.2 hγ), ENNReal.rpow_zero, one_mul, ← natCast_two_pow_rpow]
    gcongr; exact_mod_cast hn.1.trans (Nat.le_succ n)
  · rw [max_eq_left (neg_nonneg.2 hγ.le)]
    have h1 : ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) ^ γ ≤ ((n + 1 : ℕ) : ℝ≥0∞) ^ γ :=
      rpow_le_rpow_of_nonpos (by exact_mod_cast hn.2) hγ.le
    rw [natCast_two_pow_rpow, dyadicWeight_succ] at h1
    calc dyadicWeight γ k = 2 ^ (-γ) * (2 ^ γ * dyadicWeight γ k) := by
          rw [← mul_assoc, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top,
            neg_add_cancel, ENNReal.rpow_zero, one_mul]
      _ ≤ _ := by gcongr

variable {b : ℕ → ℝ≥0∞}

/-- The weighted sum over a dyadic block is at most `2^(max γ 0) 2^(k(γ+1)) b (2^k)`. -/
theorem sum_Ico_pow_mul_le (hb : Antitone b) (γ : ℝ) (k : ℕ) :
    ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n ≤
      2 ^ max γ 0 * dyadicWeight (γ + 1) k * b (2 ^ k) := by
  calc ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n
      ≤ ∑ _n ∈ Ico (2 ^ k) (2 ^ (k + 1)), 2 ^ max γ 0 * dyadicWeight γ k * b (2 ^ k) := by
        gcongr with n hn
        · exact natCast_succ_rpow_le hn γ
        · exact hb (Finset.mem_Ico.1 hn).1
    _ = 2 ^ max γ 0 * dyadicWeight (γ + 1) k * b (2 ^ k) := by
        rw [Finset.sum_const, card_Ico_two_pow, nsmul_eq_mul, dyadicWeight_add,
          natCast_two_pow_eq]
        ring

/-- The weighted sum over a dyadic block is at least `2^(-max (-γ) 0) 2^(k(γ+1)) b (2^(k+1))`. -/
theorem le_sum_Ico_pow_mul (hb : Antitone b) (γ : ℝ) (k : ℕ) :
    dyadicWeight (γ + 1) k * b (2 ^ (k + 1)) ≤
      2 ^ max (-γ) 0 * ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n := by
  calc dyadicWeight (γ + 1) k * b (2 ^ (k + 1))
      = ∑ _n ∈ Ico (2 ^ k) (2 ^ (k + 1)), dyadicWeight γ k * b (2 ^ (k + 1)) := by
        rw [Finset.sum_const, card_Ico_two_pow, nsmul_eq_mul, dyadicWeight_add,
          natCast_two_pow_eq]
        ring
    _ ≤ ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), 2 ^ max (-γ) 0 * (((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [← mul_assoc]
        exact mul_le_mul' (dyadicWeight_le_natCast_succ_rpow hn γ)
          (hb (Finset.mem_Ico.1 hn).2.le)
    _ = _ := by rw [Finset.mul_sum]

/-- **Weighted condensation, upper bound**:
`∑ₙ (n+1)^γ b n ≤ b 0 + 2^(max γ 0) ∑ₖ 2^(k(γ+1)) b (2^k)` for decreasing `b`. -/
theorem tsum_pow_mul_le_dyadic (hb : Antitone b) (γ : ℝ) :
    ∑' n, ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n ≤
      b 0 + 2 ^ max γ 0 * ∑' k, dyadicWeight (γ + 1) k * b (2 ^ k) := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two)]
  refine iSup_le fun K => ?_
  rw [sum_range_two_pow_eq]
  simp only [Nat.cast_one, Nat.zero_add, ENNReal.one_rpow, one_mul]
  gcongr
  calc ∑ k ∈ range K, ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n
      ≤ ∑ k ∈ range K, 2 ^ max γ 0 * (dyadicWeight (γ + 1) k * b (2 ^ k)) := by
        gcongr with k
        rw [← mul_assoc]; exact sum_Ico_pow_mul_le hb γ k
    _ ≤ ∑' k, 2 ^ max γ 0 * (dyadicWeight (γ + 1) k * b (2 ^ k)) := sum_le_tsum _
    _ = _ := ENNReal.tsum_mul_left

/-- **Weighted condensation, lower bound**:
`∑ₖ 2^(k(γ+1)) b (2^(k+1)) ≤ 2^(max (-γ) 0) ∑ₙ (n+1)^γ b n` for decreasing `b`. -/
theorem dyadic_le_tsum_pow_mul (hb : Antitone b) (γ : ℝ) :
    ∑' k, dyadicWeight (γ + 1) k * b (2 ^ (k + 1)) ≤
      2 ^ max (-γ) 0 * ∑' n, ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun K => ?_
  calc ∑ k ∈ range K, dyadicWeight (γ + 1) k * b (2 ^ (k + 1))
      ≤ ∑ k ∈ range K, 2 ^ max (-γ) 0 *
          ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n := by
        exact Finset.sum_le_sum fun k _ => le_sum_Ico_pow_mul hb γ k
    _ = 2 ^ max (-γ) 0 * ∑ k ∈ range K,
          ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n := by
        rw [Finset.mul_sum]
    _ ≤ 2 ^ max (-γ) 0 * ∑ n ∈ range (2 ^ K), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n := by
        rw [sum_range_two_pow_eq]; gcongr; exact le_add_self
    _ ≤ _ := by gcongr; exact sum_le_tsum _

/-- **Condensation for suprema**, upper bound: for decreasing `b` and `s ≥ 0`,
`supₙ (n+1)^s b n ≤ b 0 + 2^s supₖ 2^(ks) b (2^k)`. -/
theorem iSup_pow_mul_le_dyadic (hb : Antitone b) {s : ℝ} (hs : 0 ≤ s) :
    ⨆ n, ((n + 1 : ℕ) : ℝ≥0∞) ^ s * b n ≤ b 0 + 2 ^ s * ⨆ k, dyadicWeight s k * b (2 ^ k) := by
  refine iSup_le fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set k := Nat.log 2 n
  have hmem : n ∈ Ico (2 ^ k) (2 ^ (k + 1)) :=
    Finset.mem_Ico.2 ⟨Nat.pow_log_le_self 2 hn.ne', Nat.lt_pow_succ_log_self Nat.one_lt_two n⟩
  calc ((n + 1 : ℕ) : ℝ≥0∞) ^ s * b n ≤ 2 ^ s * dyadicWeight s k * b (2 ^ k) := by
        gcongr
        · simpa [max_eq_left hs] using natCast_succ_rpow_le hmem s
        · exact hb (Finset.mem_Ico.1 hmem).1
    _ ≤ 2 ^ s * ⨆ k, dyadicWeight s k * b (2 ^ k) := by
        rw [mul_assoc]; gcongr; exact le_iSup (fun k => dyadicWeight s k * b (2 ^ k)) k
    _ ≤ _ := le_add_self

/-- **Condensation for suprema**, lower bound: for `s ≥ 0`,
`supₖ 2^(ks) b (2^k) ≤ supₙ (n+1)^s b n`. -/
theorem dyadic_le_iSup_pow_mul {s : ℝ} (hs : 0 ≤ s) :
    ⨆ k, dyadicWeight s k * b (2 ^ k) ≤ ⨆ n, ((n + 1 : ℕ) : ℝ≥0∞) ^ s * b n := by
  refine iSup_le fun k => ?_
  calc dyadicWeight s k * b (2 ^ k) ≤ ((2 ^ k + 1 : ℕ) : ℝ≥0∞) ^ s * b (2 ^ k) := by
        rw [← natCast_two_pow_rpow]; gcongr; exact_mod_cast Nat.le_succ _
    _ ≤ _ := le_iSup (fun n => ((n + 1 : ℕ) : ℝ≥0∞) ^ s * b n) (2 ^ k)

/-- `1 + ∑_{j < m} 2^j = 2^m` in `[0, ∞]`, Mathlib's geometric sum `geom_sum_mul_add` for
`x = 1`. -/
theorem one_add_sum_range_two_pow (m : ℕ) :
    1 + ∑ j ∈ range m, (2 : ℝ≥0∞) ^ j = 2 ^ m := by
  have h := geom_sum_mul_add (1 : ℝ≥0∞) m
  rw [one_add_one_eq_two, mul_one] at h
  rw [add_comm, h]

/-- **Condensation of a capped decreasing sequence**: for decreasing `b` and every `m`,
`∑_k min(b_k, b_{2^m}) ≤ 2 ∑_{l ≥ 0} 2^(m+l) b_{2^(m+l)}`. Cauchy condensation
(`ENNReal.tsum_pow_mul_le_dyadic` with `γ = 0`) applies to the decreasing sequence
`min(b_k, b_{2^m})`; its first `m + 1` dyadic terms are at most `b_{2^m}` with total weight
`1 + ∑_{j < m} 2^j = 2^m`, and the others are at most `2^(m+l) b_{2^(m+l)}`. This bounds the
tail `∑_{k ≥ 2^m} b_k` together with `2^m b_{2^m}`. -/
theorem tsum_min_le_dyadic (hb : Antitone b) (m : ℕ) :
    ∑' k, min (b k) (b (2 ^ m)) ≤ 2 * ∑' l, 2 ^ (m + l) * b (2 ^ (m + l)) := by
  set T := ∑' l, (2 : ℝ≥0∞) ^ (m + l) * b (2 ^ (m + l))
  have hd : Antitone fun k => min (b k) (b (2 ^ m)) := fun i j hij => min_le_min (hb hij) le_rfl
  have hcond := tsum_pow_mul_le_dyadic hd 0
  simp only [ENNReal.rpow_zero, one_mul, max_self, zero_add, dyadicWeight_eq_pow,
    ENNReal.rpow_one] at hcond
  rw [← CompleteLattice.summable.sum_add_tsum_nat_add' (k := m)
    (f := fun k => (2 : ℝ≥0∞) ^ k * min (b (2 ^ k)) (b (2 ^ m))), ← add_assoc] at hcond
  have hhead : min (b 0) (b (2 ^ m)) +
      ∑ k ∈ range m, 2 ^ k * min (b (2 ^ k)) (b (2 ^ m)) ≤ 2 ^ m * b (2 ^ m) := by
    calc min (b 0) (b (2 ^ m)) + ∑ k ∈ range m, 2 ^ k * min (b (2 ^ k)) (b (2 ^ m))
        ≤ b (2 ^ m) + ∑ k ∈ range m, 2 ^ k * b (2 ^ m) := by
          gcongr
          · exact min_le_right _ _
          · exact min_le_right _ _
      _ = (1 + ∑ k ∈ range m, (2 : ℝ≥0∞) ^ k) * b (2 ^ m) := by rw [add_mul, one_mul, sum_mul]
      _ = 2 ^ m * b (2 ^ m) := by rw [one_add_sum_range_two_pow]
  have hT : 2 ^ m * b (2 ^ m) ≤ T := by
    simpa using le_tsum (f := fun l => (2 : ℝ≥0∞) ^ (m + l) * b (2 ^ (m + l))) 0
  have htail : ∑' k, 2 ^ (k + m) * min (b (2 ^ (k + m))) (b (2 ^ m)) ≤ T :=
    tsum_le_tsum fun l => by rw [add_comm l m]; gcongr; exact min_le_left _ _
  calc ∑' k, min (b k) (b (2 ^ m)) ≤ _ := hcond
    _ ≤ T + T := add_le_add (hhead.trans hT) htail
    _ = 2 * T := (two_mul T).symm

/-- **Condensation with constant `2`**: `∑_k 2^k b_{2^k} ≤ 2 ∑_n b_n` for decreasing `b`. The
term `k = 0` is `b_1`; the block `(2^k, 2^(k+1)]` has `2^k` indices with terms at least
`b_{2^(k+1)}`, and these blocks cover the indices `n ≥ 2`, so
`∑_k 2^k b_{2^(k+1)} ≤ ∑_{n ≥ 2} b_n` (Mathlib's `Finset.sum_condensed_le'`). Mathlib's
`ENNReal.tsum_condensed_le` gives the bound `b_1 + 2 ∑_n b_n`. -/
theorem tsum_two_pow_mul_le_two_mul (hb : Antitone b) :
    ∑' k, 2 ^ k * b (2 ^ k) ≤ 2 * ∑' n, b n := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1)]
  refine iSup_le fun K => ?_
  have hc := Finset.sum_condensed_le' (f := b) (fun _ _ _ h => hb h) K
  have hK : 1 < 2 ^ K + 1 := Nat.lt_add_of_pos_left (Nat.two_pow_pos K)
  calc ∑ k ∈ range (K + 1), (2 : ℝ≥0∞) ^ k * b (2 ^ k)
      = b 1 + 2 * ∑ k ∈ range K, 2 ^ k • b (2 ^ (k + 1)) := by
        rw [sum_range_succ', mul_sum, add_comm]
        simp [pow_succ', mul_assoc, nsmul_eq_mul]
    _ ≤ b 1 + 2 * ∑ n ∈ Ico 2 (2 ^ K + 1), b n := by gcongr
    _ ≤ 2 * (b 1 + ∑ n ∈ Ico 2 (2 ^ K + 1), b n) := by
        rw [mul_add]; gcongr; exact le_mul_of_one_le_left' one_le_two
    _ = 2 * ∑ n ∈ Ico 1 (2 ^ K + 1), b n := by rw [sum_eq_sum_Ico_succ_bot hK]
    _ ≤ 2 * ∑' n, b n := by gcongr; exact sum_le_tsum _

/-! ### The dyadic sum -/

/-- **Geometric partial sums**: `∑_{j < J} r^j ≤ r^J (r - 1)⁻¹` for `1 ≤ r < ∞`, from the
geometric sum `(∑_{j < J} r^j)(r - 1) + 1 = r^J` (Mathlib's `geom_sum_mul_add` with
`x = r - 1`). -/
theorem sum_range_pow_le_pow_mul_inv {r : ℝ≥0∞} (hr1 : 1 ≤ r) (hr : r ≠ ∞) (J : ℕ) :
    ∑ j ∈ range J, r ^ j ≤ r ^ J * (r - 1)⁻¹ := by
  have h := geom_sum_mul_add (r - 1) J
  rw [tsub_add_cancel_of_le hr1] at h
  rw [← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inr (pow_ne_zero _ (one_pos.trans_le hr1).ne'))
      (Or.inl (tsub_le_self.trans_lt hr.lt_top).ne)]
  rw [← h]
  exact le_self_add

/-- `∑_{j < N} 2^j ≤ 2^N` in `[0, ∞]`, the case `r = 2` of
`ENNReal.sum_range_pow_le_pow_mul_inv`. -/
theorem sum_range_two_pow_le (N : ℕ) : ∑ j ∈ Finset.range N, (2 : ℝ≥0∞) ^ j ≤ 2 ^ N := by
  have h := sum_range_pow_le_pow_mul_inv one_le_two ofNat_ne_top N
  rwa [ENNReal.sub_eq_of_eq_add one_ne_top one_add_one_eq_two.symm, inv_one, mul_one] at h

/-- For `a ≠ 0` in `[0, ∞]` there is `j ∈ ℕ` with `2^j a > 1`: Mathlib's
`ENNReal.exists_nat_mul_gt` gives `n a > 1`, and `n < 2^n`. -/
theorem exists_one_lt_two_pow_mul {a : ℝ≥0∞} (ha : a ≠ 0) : ∃ j : ℕ, 1 < 2 ^ j * a := by
  obtain ⟨n, hn⟩ := exists_nat_mul_gt ha one_ne_top
  refine ⟨n, hn.trans_le ?_⟩
  gcongr
  exact_mod_cast (Nat.lt_two_pow_self).le

/-- The terms `min(2^j a, (2^j a)⁻¹)` with `2^j a ≤ 1`, the indices `j < j₀`, add up to at most
`2`: they are at most `2^j a`, and `∑_{j < j₀} 2^j a ≤ 2^{j₀} a ≤ 2` when `2^{j₀ - 1} a ≤ 1`. -/
theorem sum_range_min_two_pow_le {a : ℝ≥0∞} {j₀ : ℕ} (h : ∀ j < j₀, ¬ 1 < 2 ^ j * a) :
    ∑ j ∈ Finset.range j₀, min (2 ^ j * a) (2 ^ j * a)⁻¹ ≤ 2 := by
  cases j₀ with
  | zero => simp
  | succ m =>
    have hm : 2 ^ m * a ≤ 1 := not_lt.1 (h m (Nat.lt_succ_self m))
    calc ∑ j ∈ Finset.range (m + 1), min (2 ^ j * a) (2 ^ j * a)⁻¹
        ≤ ∑ j ∈ Finset.range (m + 1), 2 ^ j * a := Finset.sum_le_sum fun j _ => min_le_left _ _
      _ = (∑ j ∈ Finset.range (m + 1), (2 : ℝ≥0∞) ^ j) * a := (Finset.sum_mul _ _ _).symm
      _ ≤ 2 ^ (m + 1) * a := by gcongr; exact sum_range_two_pow_le _
      _ = 2 * (2 ^ m * a) := by ring
      _ ≤ 2 * 1 := by gcongr
      _ = 2 := mul_one 2

/-- The terms `min(2^{i+j₀} a, (2^{i+j₀} a)⁻¹)` with `2^{j₀} a > 1` add up to at most `2`: they
are at most `2^{-i}`. -/
theorem tsum_min_two_pow_add_le {a : ℝ≥0∞} {j₀ : ℕ} (h : 1 < 2 ^ j₀ * a) :
    ∑' i, min (2 ^ (i + j₀) * a) (2 ^ (i + j₀) * a)⁻¹ ≤ 2 := by
  have hterm : ∀ i : ℕ, min (2 ^ (i + j₀) * a) (2 ^ (i + j₀) * a)⁻¹ ≤ 2⁻¹ ^ i := fun i => by
    refine (min_le_right _ _).trans ?_
    rw [pow_add, mul_assoc, ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), ENNReal.inv_pow]
    calc (2⁻¹ : ℝ≥0∞) ^ i * (2 ^ j₀ * a)⁻¹ ≤ 2⁻¹ ^ i * 1 := by
          gcongr
          exact ENNReal.inv_le_one.2 h.le
      _ = 2⁻¹ ^ i := mul_one _
  exact (tsum_le_tsum hterm).trans_eq ENNReal.tsum_geometric_two

/-- **The dyadic sum of `min(t, t⁻¹)`**: for every `a ∈ [0, ∞]`,
`∑_{j ∈ ℕ} min(2^j a, (2^j a)⁻¹) ≤ 4`. With `j₀` the least `j` such that `2^j a > 1`, the terms
below `j₀` add up to at most `2` (`ENNReal.sum_range_min_two_pow_le`) and the terms from `j₀` on
to at most `2` (`ENNReal.tsum_min_two_pow_add_le`). -/
theorem tsum_min_two_pow_le (a : ℝ≥0∞) : ∑' j : ℕ, min (2 ^ j * a) (2 ^ j * a)⁻¹ ≤ 4 := by
  classical
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hex := exists_one_lt_two_pow_mul ha
  rw [← CompleteLattice.summable.sum_add_tsum_nat_add' (k := Nat.find hex)]
  calc _ ≤ 2 + 2 := add_le_add (sum_range_min_two_pow_le fun j hj => Nat.find_min hex hj)
        (tsum_min_two_pow_add_le (Nat.find_spec hex))
    _ = 4 := by norm_num

/-- `min(x, x⁻¹)² ≤ min(x, x⁻¹)` in `ℝ≥0∞`, since `min(x, x⁻¹) ≤ 1` (Mathlib's `sq_le`). -/
theorem min_inv_sq_le (x : ℝ≥0∞) : min x x⁻¹ ^ 2 ≤ min x x⁻¹ := by
  have h1 : min x x⁻¹ ≤ 1 := by
    rcases le_total x 1 with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (ENNReal.inv_le_one.2 h)
  exact sq_le zero_le h1

/-! ### Finitely many changed terms -/

/-- **Finitely many changed terms**: if `u_j = v_j` for every `j ≥ N`, then
`∑_j u_j ≤ ∑_j v_j + ∑_{i < N} u_i` in `[0, ∞]`. -/
theorem tsum_le_tsum_add_sum_of_forall_ge_eq {u v : ℕ → ℝ≥0∞} {N : ℕ}
    (h : ∀ j, N ≤ j → u j = v j) : ∑' j, u j ≤ ∑' j, v j + ∑ i ∈ Finset.range N, u i := by
  calc ∑' j, u j = ∑ i ∈ Finset.range N, u i + ∑' i, u (i + N) :=
        (CompleteLattice.summable (f := fun i => u (i + N))).sum_add_tsum_nat_add'.symm
    _ = ∑ i ∈ Finset.range N, u i + ∑' i, v (i + N) := by
        rw [tsum_congr fun i => h _ (Nat.le_add_left N i)]
    _ ≤ ∑ i ∈ Finset.range N, u i + ∑' j, v j :=
        add_le_add_right (tsum_comp_le_tsum_of_injective (add_left_injective N) v) _
    _ = ∑' j, v j + ∑ i ∈ Finset.range N, u i := add_comm _ _

/-! ### Sums with few nonzero terms -/

/-- **Dyadic scales of an annulus**: for `a > 0`, if `a ≤ t / 2^j` and `t / 2^i ≤ 2^N a`, then
`j ≤ i + N`, since `2^j a ≤ t ≤ 2^{i+N} a`. -/
theorem _root_.Nat.le_add_of_dyadic_annulus {a t : ℝ} (ha : 0 < a) {i j N : ℕ}
    (hj : a ≤ t / 2 ^ j) (hi : t / 2 ^ i ≤ 2 ^ N * a) : j ≤ i + N := by
  rw [le_div_iff₀ (by positivity)] at hj
  rw [div_le_iff₀ (by positivity)] at hi
  have h : a * 2 ^ j ≤ a * 2 ^ (i + N) := by
    calc a * 2 ^ j ≤ t := hj
      _ ≤ 2 ^ N * a * 2 ^ i := hi
      _ = a * 2 ^ (i + N) := by ring
  exact (_root_.pow_le_pow_iff_right₀ (_root_.one_lt_two (α := ℝ))).1
    (_root_.le_of_mul_le_mul_left h ha)

/-- **A sum with at most `N + 1` nonzero terms**: if `u_j ≤ M` for every `j` and `u_j ≠ 0` only
for `i₀ ≤ j ≤ i₀ + N`, then `∑_j u_j ≤ (N + 1) M`. -/
theorem tsum_le_of_mem_Icc {u : ℕ → ℝ≥0∞} {M : ℝ≥0∞} {i₀ N : ℕ}
    (hM : ∀ j, u j ≤ M) (hu : ∀ j, u j ≠ 0 → j ∈ Finset.Icc i₀ (i₀ + N)) :
    ∑' j, u j ≤ (N + 1) * M := by
  rw [tsum_eq_sum (s := Finset.Icc i₀ (i₀ + N)) fun j hj => not_not.1 fun h => hj (hu j h)]
  calc ∑ j ∈ Finset.Icc i₀ (i₀ + N), u j ≤ ∑ _j ∈ Finset.Icc i₀ (i₀ + N), M :=
        Finset.sum_le_sum fun j _ => hM j
    _ = (N + 1) * M := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show i₀ + N + 1 - i₀ = N + 1 by omega]
        push_cast
        rfl

/-- **At most `N + 1` dyadic scales see a point of an annulus**: for `a > 0`, if `u_j ≤ M` for
every `j` and `u_j ≠ 0` only when `t / 2^j` lies in the annulus `[a, 2^N a]`, then
`∑_j u_j ≤ (N + 1) M`. With `i₀` the least `j` with `u_j ≠ 0`, every such `j` satisfies
`i₀ ≤ j ≤ i₀ + N` (`Nat.le_add_of_dyadic_annulus`, `ENNReal.tsum_le_of_mem_Icc`). -/
theorem tsum_le_of_dyadic_annulus {u : ℕ → ℝ≥0∞} {M : ℝ≥0∞} {a t : ℝ}
    (ha : 0 < a) {N : ℕ} (hM : ∀ j, u j ≤ M)
    (hu : ∀ j, u j ≠ 0 → a ≤ t / 2 ^ j ∧ t / 2 ^ j ≤ 2 ^ N * a) :
    ∑' j, u j ≤ (N + 1) * M := by
  classical
  by_cases hex : ∃ j, u j ≠ 0
  · exact tsum_le_of_mem_Icc hM fun j hj => Finset.mem_Icc.2
      ⟨Nat.find_min' hex hj, Nat.le_add_of_dyadic_annulus ha (hu j hj).1
        (hu _ (Nat.find_spec hex)).2⟩
  · push Not at hex
    simp [hex]

/-! ### Interpolation of dyadic suprema -/

/-- The **constant of the dyadic interpolation inequality**,
`c(δ, θ) = 2^(θδ) (2^(θδ) - 1)⁻¹ + (1 - 2^(-(1-θ)δ))⁻¹`
(`ENNReal.tsum_dyadicWeight_mul_le_iSup`): the first summand bounds the geometric sum of the
low indices, the second that of the high indices. -/
noncomputable def dyadicInterpConst (δ θ : ℝ) : ℝ≥0∞ :=
  2 ^ (θ * δ) * (2 ^ (θ * δ) - 1)⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-((1 - θ) * δ)))⁻¹

/-- The constant `c(δ, θ)` is finite for `δ > 0` and `0 < θ < 1`. -/
theorem dyadicInterpConst_ne_top {δ θ : ℝ} (hδ : 0 < δ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    dyadicInterpConst δ θ ≠ ∞ := by
  refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
    (ENNReal.two_rpow_ne_top _) ?_,
    one_sub_two_rpow_neg_inv_ne_top (_root_.mul_pos (sub_pos.2 hθ1) hδ)⟩
  rw [ENNReal.inv_ne_top]
  exact (tsub_pos_of_lt (ENNReal.one_lt_rpow one_lt_two (_root_.mul_pos hθ0 hδ))).ne'

/-- The constant `c(δ, θ)` is at least `1`. -/
theorem one_le_dyadicInterpConst (δ θ : ℝ) : 1 ≤ dyadicInterpConst δ θ :=
  (one_le_one_sub_two_rpow_neg_inv _).trans le_add_self

variable {δ θ : ℝ} {X Y : ℝ≥0∞}

/-- **The low-index bound**: if `Y ≤ 2^(-Kδ) X`, then `2^(Kθδ) Y ≤ X^θ Y^(1-θ)` for
`0 ≤ θ ≤ 1`, since `Y^θ ≤ 2^(-Kθδ) X^θ`. -/
theorem dyadicWeight_mul_le_rpow_mul_rpow (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {K : ℕ}
    (hK : Y ≤ dyadicWeight (-δ) K * X) :
    dyadicWeight (θ * δ) K * Y ≤ X ^ θ * Y ^ (1 - θ) := by
  have h1 : Y ^ θ ≤ dyadicWeight (-(θ * δ)) K * X ^ θ := by
    calc Y ^ θ ≤ (dyadicWeight (-δ) K * X) ^ θ := ENNReal.rpow_le_rpow hK hθ0
      _ = dyadicWeight (-(θ * δ)) K * X ^ θ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0, dyadicWeight_rpow]
          congr 2
          ring
  calc dyadicWeight (θ * δ) K * Y = dyadicWeight (θ * δ) K * Y ^ θ * Y ^ (1 - θ) := by
        rw [mul_assoc, rpow_mul_rpow_one_sub _ hθ0 hθ1]
    _ ≤ dyadicWeight (θ * δ) K * (dyadicWeight (-(θ * δ)) K * X ^ θ) * Y ^ (1 - θ) := by
        gcongr
    _ = X ^ θ * Y ^ (1 - θ) := by
        rw [← mul_assoc, dyadicWeight_mul_neg_self, one_mul]

/-- **The high-index bound**: if `2^(-Jδ) X ≤ Y`, then `2^(-J(1-θ)δ) X ≤ X^θ Y^(1-θ)` for
`0 ≤ θ ≤ 1`, since `2^(-J(1-θ)δ) X^(1-θ) = (2^(-Jδ) X)^(1-θ) ≤ Y^(1-θ)`. -/
theorem dyadicWeight_neg_mul_le_rpow_mul_rpow (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {J : ℕ}
    (hJ : dyadicWeight (-δ) J * X ≤ Y) :
    dyadicWeight (-((1 - θ) * δ)) J * X ≤ X ^ θ * Y ^ (1 - θ) := by
  have h1 : dyadicWeight (-((1 - θ) * δ)) J * X ^ (1 - θ) ≤ Y ^ (1 - θ) := by
    calc dyadicWeight (-((1 - θ) * δ)) J * X ^ (1 - θ)
        = (dyadicWeight (-δ) J * X) ^ (1 - θ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.2 hθ1), dyadicWeight_rpow]
          congr 2
          ring
      _ ≤ Y ^ (1 - θ) := ENNReal.rpow_le_rpow hJ (sub_nonneg.2 hθ1)
  calc dyadicWeight (-((1 - θ) * δ)) J * X
      = X ^ θ * (dyadicWeight (-((1 - θ) * δ)) J * X ^ (1 - θ)) := by
        conv_lhs => rw [← rpow_mul_rpow_one_sub X hθ0 hθ1]
        ring
    _ ≤ X ^ θ * Y ^ (1 - θ) := by gcongr

/-- **The low indices**: if `b_j ≤ 2^(jθδ) Y` for every `j` and `Y ≤ 2^(-Kδ) X`, then
`∑_{j ≤ K} b_j ≤ 2^(θδ) (2^(θδ) - 1)⁻¹ X^θ Y^(1-θ)` for `θ ∈ [0, 1]` and `δ ≥ 0`. The geometric
sum is at most `2^((K+1)θδ) (2^(θδ) - 1)⁻¹` (`ENNReal.sum_range_pow_le_pow_mul_inv`), and
`2^(Kθδ) Y ≤ X^θ Y^(1-θ)` (`ENNReal.dyadicWeight_mul_le_rpow_mul_rpow`). -/
theorem sum_range_succ_le_of_le_dyadicWeight (hδ : 0 ≤ δ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlow : ∀ j, b j ≤ dyadicWeight (θ * δ) j * Y) {K : ℕ}
    (hK : Y ≤ dyadicWeight (-δ) K * X) :
    ∑ j ∈ range (K + 1), b j ≤
      2 ^ (θ * δ) * (2 ^ (θ * δ) - 1)⁻¹ * (X ^ θ * Y ^ (1 - θ)) := by
  have hr1 : 1 ≤ (2 : ℝ≥0∞) ^ (θ * δ) := ENNReal.one_le_two_rpow (mul_nonneg hθ0 hδ)
  have hr : (2 : ℝ≥0∞) ^ (θ * δ) ≠ ∞ :=
    ENNReal.two_rpow_ne_top _
  calc ∑ j ∈ range (K + 1), b j
      ≤ ∑ j ∈ range (K + 1), ((2 : ℝ≥0∞) ^ (θ * δ)) ^ j * Y :=
        Finset.sum_le_sum fun j _ => (hlow j).trans_eq (by rw [dyadicWeight_eq_pow])
    _ = (∑ j ∈ range (K + 1), ((2 : ℝ≥0∞) ^ (θ * δ)) ^ j) * Y := (Finset.sum_mul _ _ _).symm
    _ ≤ ((2 : ℝ≥0∞) ^ (θ * δ)) ^ (K + 1) * (2 ^ (θ * δ) - 1)⁻¹ * Y := by
        gcongr
        exact sum_range_pow_le_pow_mul_inv hr1 hr _
    _ = 2 ^ (θ * δ) * (2 ^ (θ * δ) - 1)⁻¹ * (dyadicWeight (θ * δ) K * Y) := by
        rw [dyadicWeight_eq_pow, pow_succ]
        ring
    _ ≤ _ := mul_le_mul' le_rfl (dyadicWeight_mul_le_rpow_mul_rpow hθ0 hθ1 hK)

/-- **The high indices**: if `b_j ≤ 2^(-j(1-θ)δ) X` for every `j` and `2^(-Jδ) X ≤ Y`, then
`∑_{i} b_{i+J} ≤ (1 - 2^(-(1-θ)δ))⁻¹ X^θ Y^(1-θ)` for `θ ∈ [0, 1]`: the geometric series
`∑_i 2^(-i(1-θ)δ)` (`ENNReal.tsum_dyadicWeight_neg`) times
`2^(-J(1-θ)δ) X ≤ X^θ Y^(1-θ)` (`ENNReal.dyadicWeight_neg_mul_le_rpow_mul_rpow`). -/
theorem tsum_add_le_of_le_dyadicWeight_neg (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hhigh : ∀ j, b j ≤ dyadicWeight (-((1 - θ) * δ)) j * X) {J : ℕ}
    (hJ : dyadicWeight (-δ) J * X ≤ Y) :
    ∑' i, b (i + J) ≤ (1 - (2 : ℝ≥0∞) ^ (-((1 - θ) * δ)))⁻¹ * (X ^ θ * Y ^ (1 - θ)) := by
  calc ∑' i, b (i + J)
      ≤ ∑' i, dyadicWeight (-((1 - θ) * δ)) i * (dyadicWeight (-((1 - θ) * δ)) J * X) :=
        tsum_le_tsum fun i => (hhigh (i + J)).trans_eq (by
          rw [dyadicWeight_add_nat, mul_assoc])
    _ = (1 - (2 : ℝ≥0∞) ^ (-((1 - θ) * δ)))⁻¹ * (dyadicWeight (-((1 - θ) * δ)) J * X) := by
        rw [ENNReal.tsum_mul_right, tsum_dyadicWeight_neg]
    _ ≤ _ := mul_le_mul' le_rfl (dyadicWeight_neg_mul_le_rpow_mul_rpow hθ0 hθ1 hJ)

/-- For `δ > 0`, `X < ∞` and `Y > 0` there is `J` with `2^(-Jδ) X ≤ Y`, since
`2^(-Jδ) X → 0` (Mathlib's `ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one`). -/
theorem exists_dyadicWeight_neg_mul_le (hδ : 0 < δ) (hX : X ≠ ∞) (hY : Y ≠ 0) :
    ∃ J : ℕ, dyadicWeight (-δ) J * X ≤ Y := by
  have h : Tendsto (fun J : ℕ => dyadicWeight (-δ) J * X) atTop (nhds 0) := by
    simp_rw [dyadicWeight_eq_pow]
    simpa using ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (two_rpow_neg_lt_one hδ)) (Or.inr hX)
  obtain ⟨J, hJ⟩ := ((tendsto_order.1 h).2 Y (pos_iff_ne_zero.2 hY)).exists
  exact ⟨J, hJ.le⟩

/-- **Splitting a series into low and high indices**: with `δ > 0`, `0 < θ < 1`, `X < ∞` and
`Y > 0`, if `b_j ≤ 2^(jθδ) Y` and `b_j ≤ 2^(-j(1-θ)δ) X` for every `j`, then
`∑_j b_j ≤ c(δ, θ) X^θ Y^(1-θ)`. The series is split at the least `J` with `2^(-Jδ) X ≤ Y`
(`ENNReal.exists_dyadicWeight_neg_mul_le`): the indices `j < J` are bounded by
`ENNReal.sum_range_succ_le_of_le_dyadicWeight`, the indices `j ≥ J` by
`ENNReal.tsum_add_le_of_le_dyadicWeight_neg`. -/
theorem tsum_le_dyadicInterpConst_of_ne (hδ : 0 < δ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hX : X ≠ ∞) (hY : Y ≠ 0) (hlow : ∀ j, b j ≤ dyadicWeight (θ * δ) j * Y)
    (hhigh : ∀ j, b j ≤ dyadicWeight (-((1 - θ) * δ)) j * X) :
    ∑' j, b j ≤ dyadicInterpConst δ θ * (X ^ θ * Y ^ (1 - θ)) := by
  classical
  have hex := exists_dyadicWeight_neg_mul_le hδ hX hY
  rw [← CompleteLattice.summable.sum_add_tsum_nat_add' (k := Nat.find hex), dyadicInterpConst,
    add_mul]
  refine add_le_add ?_
    (tsum_add_le_of_le_dyadicWeight_neg hθ0.le hθ1.le hhigh (Nat.find_spec hex))
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, Finset.sum_range_zero]
    exact zero_le
  obtain ⟨K, hK⟩ := Nat.exists_eq_add_of_lt hpos
  rw [hK, zero_add]
  refine sum_range_succ_le_of_le_dyadicWeight hδ.le hθ0.le hθ1.le hlow ?_
  have := Nat.find_min hex (show K < Nat.find hex by omega)
  rw [not_le] at this
  exact this.le

/-- **Splitting a series into low and high indices**, for all `X, Y ∈ [0, ∞]`: with `δ > 0` and
`0 < θ < 1`, if `b_j ≤ 2^(jθδ) Y` and `b_j ≤ 2^(-j(1-θ)δ) X` for every `j`, then
`∑_j b_j ≤ c(δ, θ) X^θ Y^(1-θ)`. For `Y = 0` every `b_j` is `0`; for `X = ∞` and `Y > 0` the
right side is `∞`; otherwise this is `ENNReal.tsum_le_dyadicInterpConst_of_ne`. -/
theorem tsum_le_dyadicInterpConst (hδ : 0 < δ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hlow : ∀ j, b j ≤ dyadicWeight (θ * δ) j * Y)
    (hhigh : ∀ j, b j ≤ dyadicWeight (-((1 - θ) * δ)) j * X) :
    ∑' j, b j ≤ dyadicInterpConst δ θ * (X ^ θ * Y ^ (1 - θ)) := by
  rcases eq_or_ne Y 0 with rfl | hY
  · have hb : ∀ j, b j = 0 := fun j => le_antisymm ((hlow j).trans_eq (mul_zero _)) zero_le
    simp [hb]
  rcases eq_or_ne X ∞ with rfl | hX
  · have h1 : Y ^ (1 - θ) ≠ 0 := (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hY)
      (sub_nonneg.2 hθ1.le)).ne'
    rw [ENNReal.top_rpow_of_pos hθ0, ENNReal.top_mul h1,
      ENNReal.mul_top (one_pos.trans_le (one_le_dyadicInterpConst δ θ)).ne']
    exact le_top
  exact tsum_le_dyadicInterpConst_of_ne hδ hθ0 hθ1 hX hY hlow hhigh

/-- **The interpolation inequality for dyadic suprema** (Brezis–Mironescu 2001; Johnsen–Sickel
2007, Lemma 2 for `q = 1`): for `σ₁ < σ₀`, `0 < θ < 1` and every sequence `a` in `[0, ∞]`,

`∑_j 2^(j(θσ₀ + (1-θ)σ₁)) a_j ≤ c(σ₀ - σ₁, θ) (sup_j 2^(jσ₀) a_j)^θ (sup_j 2^(jσ₁) a_j)^(1-θ)`

with `c = ENNReal.dyadicInterpConst`. With `δ = σ₀ - σ₁`, every term is at most
`2^(jθδ) sup_j 2^(jσ₁) a_j` and at most `2^(-j(1-θ)δ) sup_j 2^(jσ₀) a_j`
(`ENNReal.tsum_le_dyadicInterpConst`). -/
theorem tsum_dyadicWeight_mul_le_iSup {σ₀ σ₁ : ℝ} (hσ : σ₁ < σ₀) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (a : ℕ → ℝ≥0∞) :
    ∑' j, dyadicWeight (θ * σ₀ + (1 - θ) * σ₁) j * a j ≤
      dyadicInterpConst (σ₀ - σ₁) θ * (⨆ j, dyadicWeight σ₀ j * a j) ^ θ *
        (⨆ j, dyadicWeight σ₁ j * a j) ^ (1 - θ) := by
  rw [mul_assoc]
  refine tsum_le_dyadicInterpConst (sub_pos.2 hσ) hθ0 hθ1 (fun j => ?_) (fun j => ?_)
  · calc dyadicWeight (θ * σ₀ + (1 - θ) * σ₁) j * a j
        = dyadicWeight (θ * (σ₀ - σ₁)) j * (dyadicWeight σ₁ j * a j) := by
          rw [← mul_assoc, ← dyadicWeight_add]
          congr 2
          ring
      _ ≤ _ := mul_le_mul' le_rfl (le_iSup (fun j => dyadicWeight σ₁ j * a j) j)
  · calc dyadicWeight (θ * σ₀ + (1 - θ) * σ₁) j * a j
        = dyadicWeight (-((1 - θ) * (σ₀ - σ₁))) j * (dyadicWeight σ₀ j * a j) := by
          rw [← mul_assoc, ← dyadicWeight_add]
          congr 2
          ring
      _ ≤ _ := mul_le_mul' le_rfl (le_iSup (fun j => dyadicWeight σ₀ j * a j) j)

/-- **The interpolation inequality for dyadic suprema in `ℓ_q`** (Brezis–Mironescu 2001;
Johnsen–Sickel 2007, Lemma 2): for `1 ≤ q ≤ ∞`, `σ₁ < σ₀` and `0 < θ < 1`,
`‖(2^(j(θσ₀ + (1-θ)σ₁)) a_j)_j‖_{ℓ_q} ≤
  c(σ₀ - σ₁, θ) (sup_j 2^(jσ₀) a_j)^θ (sup_j 2^(jσ₁) a_j)^(1-θ)`, since the `ℓ_q` norm is at
most the sum (`ENNReal.lqNorm_le_lqNorm_one`). -/
theorem lqNorm_dyadicWeight_mul_le_iSup {q : ℝ≥0∞} (hq : 1 ≤ q) {σ₀ σ₁ : ℝ} (hσ : σ₁ < σ₀)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (a : ℕ → ℝ≥0∞) :
    lqNorm q (fun j => dyadicWeight (θ * σ₀ + (1 - θ) * σ₁) j * a j) ≤
      dyadicInterpConst (σ₀ - σ₁) θ * (⨆ j, dyadicWeight σ₀ j * a j) ^ θ *
        (⨆ j, dyadicWeight σ₁ j * a j) ^ (1 - θ) :=
  (lqNorm_le_lqNorm_one hq _).trans (tsum_dyadicWeight_mul_le_iSup hσ hθ0 hθ1 a)

end ENNReal
