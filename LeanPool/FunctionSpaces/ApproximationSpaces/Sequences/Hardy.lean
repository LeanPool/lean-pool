/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Lq

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Discrete Hardy inequalities and geometric convolutions

For `α > 0`, `1 ≤ q ≤ ∞` and a sequence `b : ℕ → ℝ≥0∞`, with `C_α = (1 - 2^(-α))⁻¹`:

* `hardy_sum_le`:
  `‖(2^(-kα) ∑_{j ≤ k} b j)ₖ‖_q ≤ C_α ‖(2^(-kα) b k)ₖ‖_q`;
* `hardy_tail_le`:
  `‖(2^(kα) ∑_{i ≥ 0} b (k + i))ₖ‖_q ≤ C_α ‖(2^(kα) b k)ₖ‖_q`.

These are the two estimates behind every telescoping argument in approximation theory: the
first controls partial sums of dyadic blocks (Bernstein side), the second controls tails
(Jackson and Nikolskii side).  Both are Young's inequality `‖w * c‖_q ≤ ‖w‖_1 ‖c‖_q` for the
geometric kernel `w i = 2^(-iα)`.  The proof writes the convolution as a series of shifted
copies of `c` and uses the **countable Minkowski inequality** `lqNorm_tsum_le`, the case of
`MeasureTheory.eLpNorm_tsum_le` for the counting measure; monotone convergence (`lqNorm_iSup`, the
case of `MeasureTheory.eLpNorm_iSup_of_directed`) gives the norm of a sequence as the supremum of
the norms of its truncations, which increase (`lqNorm_eq_iSup_lqNorm_ite`, `monotone_ite_lt`).
Shifts do not increase the norm, so window sums cost a constant:
`‖(∑_{k = j - c}^{j + c} b_k)_j‖_q ≤ (2c + 1) ‖b‖_q` (`lqNorm_sum_Icc_le`).

Together they bound an **almost diagonal sum**: with `c_{ij} = 2^(-(i-j)L)` for `j ≤ i` and
`c_{ij} = 1` for `j > i`, `‖(2^(is) ∑_j c_{ij} a_j)_i‖_q ≤ C ‖(2^(js) a_j)_j‖_q` for `0 < s < L`
(`lqNorm_almostDiagonal_le`), with the constant `C = (1 - 2^(-(L-s)))⁻¹ + (1 - 2^(-s))⁻¹`
(`almostDiagonalConst`); the same bound holds for every sequence below `C' ∑_j c_{ij} m_j`
(`lqNorm_le_almostDiagonalConst_mul_of_le`).

For `0 < q ≤ 1` the same three estimates hold with the constants of the `q`-th powers: the
Hardy inequalities with `γ_{α,q} = (1 - 2^(-αq))^(-1/q)` (`hardy_tail_le_of_le_one`,
`hardy_sum_le_of_le_one`, with `dyadicGeomConst`) and the almost diagonal sum with
`almostDiagonalConst (sq) (Lq) ^ (1/q)` (`lqNorm_almostDiagonal_le_of_le_one`). The `q`-th power of
a sum is at most the sum of the `q`-th powers, so each is the estimate for `ℓ_1` applied to the
`q`-th powers. For every exponent `q` both Hardy inequalities hold with the constant
`hardyConst α q`, which is `(1 - 2^(-α))⁻¹` for `q ≥ 1` and `γ_{α,q}` otherwise
(`hardy_tail_le'`, `hardy_sum_le'`).

The Minkowski inequalities and monotone convergence hold for families on every countable index
set, and so does the rule for powers inside the norm, `‖(a_i^r)_i‖_{ℓ_{q/r}} = ‖a‖_{ℓ_q}^r` for
`r > 0` (`lqNorm_fun_rpow`, `lqNorm_div_fun_rpow`).  On `ℤ`, the norm is invariant under shifts
(`lqNorm_comp_add_int`), which gives Young's inequality for a series of shifts
(`lqNorm_tsum_shift_le`) and the two **geometric convolutions**
`‖(∑_{j ≥ 0} 2^(-(j+1)α) c_{m-(j+1)})_m‖_q ≤ (1 - 2^(-α))⁻¹ ‖c‖_q` and the same bound for
`(∑_{j ≥ 0} 2^(-jα) c_{m+j})_m` (`lqNorm_tsum_geom_sub_le`, `lqNorm_tsum_geom_add_le`), the
convolutions behind the reiteration theorem.
-/

@[expose] public section

open Finset Filter MeasureTheory
open scoped ENNReal

namespace ENNReal

variable {q : ℝ≥0∞}

section Countable

variable {κ : Type*} [MeasurableSpace κ] [Countable κ] [MeasurableSingletonClass κ]

/-- **Monotone convergence** for the `ℓ_q` norm: for an increasing sequence of families indexed
by a countable set, the norm of the pointwise supremum is the supremum of the norms
(`MeasureTheory.eLpNorm_iSup_of_directed` for the counting measure). -/
theorem lqNorm_iSup {F : ℕ → κ → ℝ≥0∞} (hF : Monotone F) :
    lqNorm q (fun k => ⨆ N, F N k) = ⨆ N, lqNorm q (F N) :=
  eLpNorm_iSup_of_directed (fun _ => (measurable_of_countable _).aemeasurable) hF.directed_le q

omit [Countable κ] [MeasurableSingletonClass κ] in
/-- **Minkowski's inequality for finite sums** of families. -/
theorem lqNorm_sum_le (hq : 1 ≤ q) {ι : Type*} (s : Finset ι) (f : ι → κ → ℝ≥0∞) :
    lqNorm q (fun k => ∑ i ∈ s, f i k) ≤ ∑ i ∈ s, lqNorm q (f i) := by
  have : (fun k => ∑ i ∈ s, f i k) = ∑ i ∈ s, f i := by funext k; simp
  rw [this]
  exact eLpNorm_sum_le hq

omit [Countable κ] [MeasurableSingletonClass κ] in
/-- **Minkowski's inequality for series** of families: the norm of a pointwise sum is at most the
sum of the norms (`MeasureTheory.eLpNorm_tsum_le` for the counting measure). -/
theorem lqNorm_tsum_le (hq : 1 ≤ q) (f : ℕ → κ → ℝ≥0∞) :
    lqNorm q (fun k => ∑' i, f i k) ≤ ∑' i, lqNorm q (f i) :=
  eLpNorm_tsum_le hq

/-- **Powers inside an `ℓ_u` norm**: `‖(a_i^r)_i‖_{ℓ_u} = ‖a‖_{ℓ_{u r}}^r` for `r > 0`
(`MeasureTheory.eLpNorm_fun_rpow` for the counting measure). -/
theorem lqNorm_fun_rpow (u : ℝ≥0∞) {r : ℝ} (hr : 0 < r) (a : κ → ℝ≥0∞) :
    lqNorm u (fun i => a i ^ r) = lqNorm (u * ENNReal.ofReal r) a ^ r :=
  MeasureTheory.eLpNorm_fun_rpow (measurable_of_countable a).aemeasurable hr u

/-- **Powers inside an `ℓ_q` norm, quotient form**: `‖(a_i^r)_i‖_{ℓ_{q/r}} = ‖a‖_{ℓ_q}^r` for
every `r > 0` and every exponent `q`, with `∞ / r = ∞`. For `0 < r ≤ 1` the `r`-th powers of a
sum are subadditive, so estimates in `ℓ_q` for sums of `r`-th powers pass through `ℓ_{q/r}`. -/
theorem lqNorm_div_fun_rpow {r : ℝ} (hr : 0 < r) (q : ℝ≥0∞) (a : κ → ℝ≥0∞) :
    lqNorm (q / ENNReal.ofReal r) (fun i => a i ^ r) = lqNorm q a ^ r := by
  rw [lqNorm_fun_rpow _ hr,
    ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top]

end Countable

/-- **The truncations of a sequence increase**: `J ↦ (a_j 1_{j < J})_j` is monotone. -/
theorem monotone_ite_lt (a : ℕ → ℝ≥0∞) :
    Monotone fun (J j : ℕ) => if j < J then a j else 0 := by
  intro J J' hJ j
  dsimp only
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (lt_of_lt_of_le h1 hJ) h2
  · exact zero_le
  · exact le_rfl

/-- **`ℓ_q` norms of truncations increase to the norm**: for every sequence `a` in `[0, ∞]`,
`‖a‖_{ℓ_q} = sup_J ‖(a_j 1_{j < J})_j‖_{ℓ_q}`, the case of `ENNReal.lqNorm_iSup` for the
truncations of `a`. -/
theorem lqNorm_eq_iSup_lqNorm_ite (a : ℕ → ℝ≥0∞) :
    lqNorm q a = ⨆ J : ℕ, lqNorm q (fun j => if j < J then a j else 0) := by
  rw [← lqNorm_iSup (monotone_ite_lt a)]
  congr 1
  funext j
  refine le_antisymm (le_iSup_of_le (j + 1) (by simp)) (iSup_le fun J => ?_)
  split_ifs
  · exact le_rfl
  · exact zero_le

/-- Dropping the first `i` terms does not increase the norm
(`ENNReal.lqNorm_comp_le_of_injective` for `n ↦ n + i`). -/
theorem lqNorm_shift_le' (i : ℕ) (a : ℕ → ℝ≥0∞) : lqNorm q (fun n => a (n + i)) ≤ lqNorm q a :=
  lqNorm_comp_le_of_injective (add_left_injective i) a

/-- Shifting a sequence to the right by `i` places, filling with zeros, does not increase the
norm: the shifted sequence is the extension by zero of `a` along `k ↦ k + i`
(`ENNReal.lqNorm_extend_zero`). -/
theorem lqNorm_shiftRight_le (i : ℕ) (a : ℕ → ℝ≥0∞) :
    lqNorm q (fun k => if i ≤ k then a (k - i) else 0) ≤ lqNorm q a := by
  have h : (fun k => if i ≤ k then a (k - i) else 0) = Function.extend (· + i) a 0 := by
    funext k
    split_ifs with hk
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
      rw [Nat.add_sub_cancel]
      exact ((add_left_injective i).extend_apply a 0 m).symm
    · rw [Function.extend_apply' _ _ _ fun ⟨m, hm⟩ => hk (hm ▸ Nat.le_add_left i m)]
      rfl
  rw [h, lqNorm_extend_zero (add_left_injective i)]

/-! ### Window sums -/

/-- **Window sums as shifted sequences**: for `c, j ∈ ℕ` and `b : ℕ → [0, ∞]`,
`∑_{k = j - c}^{j + c} b_k = ∑_{i < 2c + 1} b_{j + i - c}`, where the terms with `j + i < c` are
`0` (Mathlib's `Finset.sum_nbij'` with `k ↦ k + c - j`). -/
theorem sum_Icc_eq_sum_range_ite (c j : ℕ) (b : ℕ → ℝ≥0∞) :
    ∑ k ∈ Finset.Icc (j - c) (j + c), b k =
      ∑ i ∈ Finset.range (2 * c + 1), if c ≤ j + i then b (j + i - c) else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun k => k + c - j) (fun i => j + i - c) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  · intro i hi
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hi ⊢
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    omega
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    congr 1
    omega

/-- **One shifted sequence**: for `c, i ∈ ℕ`, the sequence `j ↦ b_{j + i - c}` (with the terms
`j + i < c` set to `0`) has `ℓ_q` norm at most `‖b‖_{ℓ_q}`: it is a shift of `b` to the right
(`ENNReal.lqNorm_shiftRight_le`) for `i ≤ c`, and to the left (`ENNReal.lqNorm_shift_le'`)
otherwise. -/
theorem lqNorm_ite_add_sub_le {q : ℝ≥0∞} (c i : ℕ) (b : ℕ → ℝ≥0∞) :
    lqNorm q (fun j => if c ≤ j + i then b (j + i - c) else 0) ≤ lqNorm q b := by
  rcases le_or_gt i c with hic | hic
  · have h : (fun j => if c ≤ j + i then b (j + i - c) else 0) =
        fun j => if c - i ≤ j then b (j - (c - i)) else 0 := by
      funext j
      split_ifs with h1 h2 h2
      · congr 1
        omega
      · exfalso
        omega
      · exfalso
        omega
      · rfl
    rw [h]
    exact lqNorm_shiftRight_le _ b
  · have h : (fun j => if c ≤ j + i then b (j + i - c) else 0) = fun j => b (j + (i - c)) := by
      funext j
      split_ifs with h1
      · congr 1
        omega
      · exfalso
        omega
    rw [h]
    exact lqNorm_shift_le' _ b

/-- **Window sums in `ℓ_q`**: for `1 ≤ q ≤ ∞`, `c ∈ ℕ` and every sequence `b` in `[0, ∞]`,
`‖(∑_{k = j - c}^{j + c} b_k)_j‖_{ℓ_q} ≤ (2c + 1) ‖b‖_{ℓ_q}`: the window sum is a sum of `2c + 1`
shifted sequences (`ENNReal.sum_Icc_eq_sum_range_ite`, `ENNReal.lqNorm_ite_add_sub_le`), and
Minkowski's inequality applies (`ENNReal.lqNorm_sum_le`). -/
theorem lqNorm_sum_Icc_le {q : ℝ≥0∞} (hq : 1 ≤ q) (c : ℕ) (b : ℕ → ℝ≥0∞) :
    lqNorm q (fun j => ∑ k ∈ Finset.Icc (j - c) (j + c), b k) ≤ (2 * c + 1) * lqNorm q b := by
  simp_rw [sum_Icc_eq_sum_range_ite c _ b]
  refine (lqNorm_sum_le hq _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => lqNorm_ite_add_sub_le c i b).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  exact le_rfl

/-! ### Hardy's inequalities -/

/-- **Hardy's inequality for tails**: for `α > 0` and `1 ≤ q ≤ ∞`,
`‖(2^(kα) ∑_{i ≥ 0} b (k + i))ₖ‖_q ≤ (1 - 2^(-α))⁻¹ ‖(2^(kα) b k)ₖ‖_q`. -/
theorem hardy_tail_le (hq : 1 ≤ q) (α : ℝ) (b : ℕ → ℝ≥0∞) :
    lqNorm q (fun k => dyadicWeight α k * ∑' i, b (k + i)) ≤
      (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ * lqNorm q (fun k => dyadicWeight α k * b k) := by
  set c : ℕ → ℝ≥0∞ := fun k => dyadicWeight α k * b k
  have hterm : ∀ k, dyadicWeight α k * ∑' i, b (k + i) =
      ∑' i, dyadicWeight (-α) i * c (k + i) := fun k => by
    rw [← ENNReal.tsum_mul_left]
    congr 1; funext i
    simp only [c, dyadicWeight_add_nat, ← mul_assoc]
    rw [mul_comm (dyadicWeight (-α) i), mul_assoc (dyadicWeight α k), dyadicWeight_neg_mul_self,
      mul_one]
  simp_rw [hterm]
  calc lqNorm q (fun k => ∑' i, dyadicWeight (-α) i * c (k + i))
      ≤ ∑' i, lqNorm q (fun k => dyadicWeight (-α) i * c (k + i)) :=
        lqNorm_tsum_le hq (fun i k => dyadicWeight (-α) i * c (k + i))
    _ = ∑' i, dyadicWeight (-α) i * lqNorm q (fun k => c (k + i)) := by
        simp_rw [lqNorm_const_mul]
    _ ≤ ∑' i, dyadicWeight (-α) i * lqNorm q c := by
        gcongr with i; exact lqNorm_shift_le' i c
    _ = (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ * lqNorm q c := by
        rw [ENNReal.tsum_mul_right]
        simp_rw [dyadicWeight_eq_pow]
        rw [ENNReal.tsum_geometric]

/-- **Hardy's inequality for partial sums**: for `α > 0` and `1 ≤ q ≤ ∞`,
`‖(2^(-kα) ∑_{j ≤ k} b j)ₖ‖_q ≤ (1 - 2^(-α))⁻¹ ‖(2^(-kα) b k)ₖ‖_q`. -/
theorem hardy_sum_le (hq : 1 ≤ q) (α : ℝ) (b : ℕ → ℝ≥0∞) :
    lqNorm q (fun k => dyadicWeight (-α) k * ∑ j ∈ range (k + 1), b j) ≤
      (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ * lqNorm q (fun k => dyadicWeight (-α) k * b k) := by
  set c : ℕ → ℝ≥0∞ := fun k => dyadicWeight (-α) k * b k
  set g : ℕ → ℕ → ℝ≥0∞ := fun i k => dyadicWeight (-α) i * (if i ≤ k then c (k - i) else 0)
  have hterm : ∀ k, dyadicWeight (-α) k * ∑ j ∈ range (k + 1), b j = ∑' i, g i k := fun k => by
    rw [tsum_eq_sum (s := range (k + 1)) fun i hi => by
      simp [g, not_le.2 (by simpa using hi : k < i)]]
    rw [Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hk : k = (k - i) + i := (Nat.sub_add_cancel hik).symm
    simp only [g, c, hik, ↓reduceIte, add_tsub_cancel_right]
    rw [← mul_assoc, ← dyadicWeight_add_nat, add_comm i, ← hk]
  simp_rw [hterm]
  calc lqNorm q (fun k => ∑' i, g i k) ≤ ∑' i, lqNorm q (g i) := lqNorm_tsum_le hq g
    _ = ∑' i, dyadicWeight (-α) i * lqNorm q (fun k => if i ≤ k then c (k - i) else 0) := by
        simp_rw [g, lqNorm_const_mul]
    _ ≤ ∑' i, dyadicWeight (-α) i * lqNorm q c := by
        gcongr with i; exact lqNorm_shiftRight_le i c
    _ = (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ * lqNorm q c := by
        rw [ENNReal.tsum_mul_right]
        simp_rw [dyadicWeight_eq_pow]
        rw [ENNReal.tsum_geometric]

/-! ### Hardy's inequalities for `0 < q ≤ 1` -/

/-- **Hardy's inequality for tails, `0 < q ≤ 1`**:
`‖(2^(kα) ∑_{i ≥ 0} b (k + i))ₖ‖_q ≤ γ_{α,q} ‖(2^(kα) b k)ₖ‖_q` with
`γ_{α,q} = (1 - 2^(-αq))^(-1/q)` (`ENNReal.dyadicGeomConst`); for `q = 0` both sides are the
degenerate value `0`. The `q`-th power of a series is at most the series of the `q`-th powers
(`ENNReal.rpow_tsum_le_tsum_rpow`), and Hardy's inequality for `ℓ_1` with the exponent `αq`
(`ENNReal.hardy_tail_le`) bounds the result. -/
theorem hardy_tail_le_of_le_one (hq1 : q ≤ 1) (α : ℝ) (b : ℕ → ℝ≥0∞) :
    lqNorm q (fun k => dyadicWeight α k * ∑' i, b (k + i)) ≤
      dyadicGeomConst α q * lqNorm q (fun k => dyadicWeight α k * b k) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  obtain ⟨hp, hp1⟩ := toReal_mem_Ioc_of_le_one hq0 hq1
  rw [dyadicGeomConst]
  refine lqNorm_le_rpow_mul_of_tsum_rpow_le (ne_top_of_le_ne_top one_ne_top hq1) ?_
  set p := q.toReal
  calc ∑' k, (dyadicWeight α k * ∑' i, b (k + i)) ^ p
      ≤ ∑' k, dyadicWeight (α * p) k * ∑' i, (fun j => b j ^ p) (k + i) :=
        tsum_le_tsum fun k => by
          rw [mul_rpow_of_nonneg _ _ hp.le, dyadicWeight_rpow]
          gcongr
          exact rpow_tsum_le_tsum_rpow _ hp hp1
    _ = lqNorm 1 (fun k => dyadicWeight (α * p) k * ∑' i, (fun j => b j ^ p) (k + i)) :=
        (lqNorm_one _).symm
    _ ≤ (1 - 2 ^ (-(α * p)))⁻¹ * lqNorm 1 (fun k => dyadicWeight (α * p) k * b k ^ p) :=
        hardy_tail_le le_rfl (α * p) (fun j => b j ^ p)
    _ = (1 - 2 ^ (-(α * p)))⁻¹ * ∑' k, (dyadicWeight α k * b k) ^ p := by
        rw [lqNorm_one]
        congr 1
        refine tsum_congr fun k => ?_
        rw [mul_rpow_of_nonneg _ _ hp.le, dyadicWeight_rpow]

/-- **Hardy's inequality for partial sums, `0 < q ≤ 1`**:
`‖(2^(-kα) ∑_{j ≤ k} b j)ₖ‖_q ≤ γ_{α,q} ‖(2^(-kα) b k)ₖ‖_q` with
`γ_{α,q} = (1 - 2^(-αq))^(-1/q)` (`ENNReal.dyadicGeomConst`); for `q = 0` both sides are the
degenerate value `0`. The `q`-th power of a finite sum is at most the sum of the `q`-th powers
(`ENNReal.rpow_sum_le_sum_rpow`), and Hardy's inequality for `ℓ_1` with the exponent `αq`
(`ENNReal.hardy_sum_le`) bounds the result. -/
theorem hardy_sum_le_of_le_one (hq1 : q ≤ 1) (α : ℝ) (b : ℕ → ℝ≥0∞) :
    lqNorm q (fun k => dyadicWeight (-α) k * ∑ j ∈ range (k + 1), b j) ≤
      dyadicGeomConst α q * lqNorm q (fun k => dyadicWeight (-α) k * b k) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  obtain ⟨hp, hp1⟩ := toReal_mem_Ioc_of_le_one hq0 hq1
  rw [dyadicGeomConst]
  refine lqNorm_le_rpow_mul_of_tsum_rpow_le (ne_top_of_le_ne_top one_ne_top hq1) ?_
  set p := q.toReal
  have hw : ∀ k, dyadicWeight (-α) k ^ p = dyadicWeight (-(α * p)) k := fun k => by
    rw [dyadicWeight_rpow, neg_mul]
  calc ∑' k, (dyadicWeight (-α) k * ∑ j ∈ range (k + 1), b j) ^ p
      ≤ ∑' k, dyadicWeight (-(α * p)) k * ∑ j ∈ range (k + 1), b j ^ p :=
        tsum_le_tsum fun k => by
          rw [mul_rpow_of_nonneg _ _ hp.le, hw]
          gcongr
          exact rpow_sum_le_sum_rpow _ _ hp hp1
    _ = lqNorm 1 (fun k => dyadicWeight (-(α * p)) k * ∑ j ∈ range (k + 1), b j ^ p) :=
        (lqNorm_one _).symm
    _ ≤ (1 - 2 ^ (-(α * p)))⁻¹ * lqNorm 1 (fun k => dyadicWeight (-(α * p)) k * b k ^ p) :=
        hardy_sum_le le_rfl (α * p) (fun j => b j ^ p)
    _ = (1 - 2 ^ (-(α * p)))⁻¹ * ∑' k, (dyadicWeight (-α) k * b k) ^ p := by
        rw [lqNorm_one]
        congr 1
        refine tsum_congr fun k => ?_
        rw [mul_rpow_of_nonneg _ _ hp.le, hw]

/-! ### Hardy's inequalities for every exponent -/

/-- The constant of Hardy's inequalities for every exponent `q`: `(1 - 2^(-α))⁻¹` for
`1 ≤ q ≤ ∞` (`ENNReal.hardy_tail_le`, `ENNReal.hardy_sum_le`) and
`γ_{α,q} = (1 - 2^(-αq))^(-1/q)` for `q < 1` (`ENNReal.dyadicGeomConst`). -/
noncomputable def hardyConst (α : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  if 1 ≤ q then (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ else dyadicGeomConst α q

/-- The constant `hardyConst α q` is finite for `α > 0`. -/
theorem hardyConst_ne_top {α : ℝ} (hα : 0 < α) (q : ℝ≥0∞) : hardyConst α q ≠ ∞ := by
  unfold hardyConst
  split_ifs
  · exact one_sub_two_rpow_neg_inv_ne_top hα
  · exact dyadicGeomConst_ne_top hα q

/-- **Hardy's inequality for tails, every exponent**:
`‖(2^(kα) ∑_{i ≥ 0} b (k + i))ₖ‖_q ≤ hardyConst α q · ‖(2^(kα) b k)ₖ‖_q` for every `q`, by
`ENNReal.hardy_tail_le` for `q ≥ 1` and `ENNReal.hardy_tail_le_of_le_one` for `q < 1`. -/
theorem hardy_tail_le' (α : ℝ) (b : ℕ → ℝ≥0∞) :
    lqNorm q (fun k => dyadicWeight α k * ∑' i, b (k + i)) ≤
      hardyConst α q * lqNorm q (fun k => dyadicWeight α k * b k) := by
  unfold hardyConst
  split_ifs with hq
  · exact hardy_tail_le hq α b
  · exact hardy_tail_le_of_le_one (not_le.1 hq).le α b

/-- **Hardy's inequality for partial sums, every exponent**:
`‖(2^(-kα) ∑_{j ≤ k} b j)ₖ‖_q ≤ hardyConst α q · ‖(2^(-kα) b k)ₖ‖_q` for every `q`, by
`ENNReal.hardy_sum_le` for `q ≥ 1` and `ENNReal.hardy_sum_le_of_le_one` for `q < 1`. -/
theorem hardy_sum_le' (α : ℝ) (b : ℕ → ℝ≥0∞) :
    lqNorm q (fun k => dyadicWeight (-α) k * ∑ j ∈ range (k + 1), b j) ≤
      hardyConst α q * lqNorm q (fun k => dyadicWeight (-α) k * b k) := by
  unfold hardyConst
  split_ifs with hq
  · exact hardy_sum_le hq α b
  · exact hardy_sum_le_of_le_one (not_le.1 hq).le α b

/-! ### Almost diagonal sums -/

/-- **An almost diagonal sum in weighted `ℓ_q`**:
`‖(2^(is) ∑_j c_{ij} a_j)_i‖_{ℓ_q} ≤ ((1 - 2^(-(L-s)))⁻¹ + (1 - 2^(-s))⁻¹) ‖(2^(js) a_j)_j‖_{ℓ_q}`
with `c_{ij} = 2^(-(i-j)L)` for `j ≤ i` and `c_{ij} = 1` for `j > i`, by Hardy's inequalities for
the sum below and the tail above the diagonal (finite for `0 < s < L`). -/
theorem lqNorm_almostDiagonal_le (hq : 1 ≤ q) (s L : ℝ) (a : ℕ → ℝ≥0∞) :
    lqNorm q (fun i => dyadicWeight s i *
      ∑' j, (if j ≤ i then dyadicWeight (-L) (i - j) else 1) * a j) ≤
      ((1 - (2 : ℝ≥0∞) ^ (-(L - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹) *
        lqNorm q (fun j => dyadicWeight s j * a j) := by
  set X := lqNorm q (fun j => dyadicWeight s j * a j)
  have hsplit : ∀ i, ∑' j, (if j ≤ i then dyadicWeight (-L) (i - j) else 1) * a j =
      ∑ j ∈ Finset.range (i + 1), dyadicWeight (-L) (i - j) * a j + ∑' t, a (t + (i + 1)) :=
    fun i => by
      rw [← Summable.sum_add_tsum_nat_add' (k := i + 1) CompleteLattice.summable]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        have hji : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        simp only [hji, ↓reduceIte]
      · refine tsum_congr fun t => ?_
        have hti : ¬(t + (i + 1) ≤ i) := by omega
        simp only [hti, ↓reduceIte, one_mul]
  have hP : lqNorm q (fun i => dyadicWeight s i *
      ∑ j ∈ Finset.range (i + 1), dyadicWeight (-L) (i - j) * a j) ≤
      (1 - (2 : ℝ≥0∞) ^ (-(L - s)))⁻¹ * X := by
    have h := ENNReal.hardy_sum_le hq (L - s)
      (fun j => dyadicWeight (L - s) j * (dyadicWeight s j * a j))
    have h1 : (fun i => dyadicWeight s i *
          ∑ j ∈ Finset.range (i + 1), dyadicWeight (-L) (i - j) * a j) =
        fun i => dyadicWeight (-(L - s)) i *
          ∑ j ∈ Finset.range (i + 1), dyadicWeight (L - s) j * (dyadicWeight s j * a j) := by
      funext i
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hL : dyadicWeight L j = dyadicWeight (L - s) j * dyadicWeight s j := by
        rw [← dyadicWeight_add, sub_add_cancel]
      rw [← mul_assoc, dyadicWeight_mul_dyadicWeight_neg_sub s L
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), hL]
      ring
    have h2 : (fun k => dyadicWeight (-(L - s)) k *
        (dyadicWeight (L - s) k * (dyadicWeight s k * a k))) = fun k => dyadicWeight s k * a k := by
      funext k
      rw [← mul_assoc, ENNReal.dyadicWeight_neg_mul_self, one_mul]
    rw [h1]
    rw [h2] at h
    exact h
  have hT : lqNorm q (fun i => dyadicWeight s i * ∑' t, a (t + (i + 1))) ≤
      (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X := by
    refine (ENNReal.lqNorm_mono fun i => ?_).trans (ENNReal.hardy_tail_le hq s a)
    have hinj : Function.Injective fun t : ℕ => t + 1 := add_left_injective 1
    have htail : ∑' t, a (t + (i + 1)) ≤ ∑' n, a (i + n) :=
      calc ∑' t, a (t + (i + 1)) = ∑' t, (fun n => a (i + n)) (t + 1) := by
            congr 1
            funext t
            congr 1
            omega
        _ ≤ ∑' n, a (i + n) := tsum_comp_le_tsum_of_injective hinj (fun n => a (i + n))
    exact mul_le_mul' le_rfl htail
  calc lqNorm q (fun i => dyadicWeight s i *
        ∑' j, (if j ≤ i then dyadicWeight (-L) (i - j) else 1) * a j)
      = lqNorm q (fun i => dyadicWeight s i *
          ∑ j ∈ Finset.range (i + 1), dyadicWeight (-L) (i - j) * a j +
          dyadicWeight s i * ∑' t, a (t + (i + 1))) := by
        congr 1
        funext i
        rw [hsplit i, mul_add]
    _ ≤ lqNorm q (fun i => dyadicWeight s i *
          ∑ j ∈ Finset.range (i + 1), dyadicWeight (-L) (i - j) * a j) +
        lqNorm q (fun i => dyadicWeight s i * ∑' t, a (t + (i + 1))) :=
        ENNReal.lqNorm_add_le hq _ _
    _ ≤ (1 - (2 : ℝ≥0∞) ^ (-(L - s)))⁻¹ * X + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X := add_le_add hP hT
    _ = _ := by ring

/-- The constant `(1 - 2^(-(L-s)))⁻¹ + (1 - 2^(-s))⁻¹` of the almost diagonal estimate in `ℓ_q`
(`ENNReal.lqNorm_almostDiagonal_le`). -/
noncomputable def almostDiagonalConst (s L : ℝ) : ℝ≥0∞ :=
  (1 - (2 : ℝ≥0∞) ^ (-(L - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹

/-- The constant of the almost diagonal estimate is finite for `0 < s < L`. -/
theorem almostDiagonalConst_ne_top {s L : ℝ} (hs : 0 < s) (hsL : s < L) :
    ENNReal.almostDiagonalConst s L ≠ ∞ :=
  add_ne_top.2 ⟨one_sub_two_rpow_neg_inv_ne_top (sub_pos.2 hsL),
    one_sub_two_rpow_neg_inv_ne_top hs⟩

/-- **An almost diagonal sum in weighted `ℓ_q`, `0 < q ≤ 1`**: with `c_{ij} = 2^(-(i-j)L)` for
`j ≤ i` and `c_{ij} = 1` for `j > i`,
`‖(2^(is) ∑_j c_{ij} a_j)_i‖_{ℓ_q} ≤ A_{sq,Lq}^(1/q) ‖(2^(js) a_j)_j‖_{ℓ_q}` with
`A_{s,L} = ENNReal.almostDiagonalConst s L`, finite for `0 < s < L`; for `q = 0` both sides are
the degenerate value `0`. The `q`-th power of the inner series is at most `∑_j c_{ij}^q a_j^q`
(`ENNReal.rpow_tsum_le_tsum_rpow`), and `c_{ij}^q` is the coefficient of the exponent `Lq`, so
the estimate for `ℓ_1` with the exponents `sq` and `Lq` (`ENNReal.lqNorm_almostDiagonal_le`)
applies to `(a_j^q)_j`. -/
theorem lqNorm_almostDiagonal_le_of_le_one (hq1 : q ≤ 1) (s L : ℝ) (a : ℕ → ℝ≥0∞) :
    lqNorm q (fun i => dyadicWeight s i *
      ∑' j, (if j ≤ i then dyadicWeight (-L) (i - j) else 1) * a j) ≤
      almostDiagonalConst (s * q.toReal) (L * q.toReal) ^ (1 / q.toReal) *
        lqNorm q (fun j => dyadicWeight s j * a j) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  obtain ⟨hp, hp1⟩ := toReal_mem_Ioc_of_le_one hq0 hq1
  refine lqNorm_le_rpow_mul_of_tsum_rpow_le (ne_top_of_le_ne_top one_ne_top hq1) ?_
  set p := q.toReal
  have hc : ∀ i j, (if j ≤ i then dyadicWeight (-L) (i - j) else 1) ^ p =
      if j ≤ i then dyadicWeight (-(L * p)) (i - j) else 1 := fun i j => by
    split_ifs
    · rw [dyadicWeight_rpow, neg_mul]
    · exact one_rpow p
  calc ∑' i, (dyadicWeight s i * ∑' j, (if j ≤ i then dyadicWeight (-L) (i - j) else 1) * a j) ^ p
      ≤ ∑' i, dyadicWeight (s * p) i *
          ∑' j, (if j ≤ i then dyadicWeight (-(L * p)) (i - j) else 1) * a j ^ p :=
        tsum_le_tsum fun i => by
          rw [mul_rpow_of_nonneg _ _ hp.le, dyadicWeight_rpow]
          gcongr
          refine (rpow_tsum_le_tsum_rpow _ hp hp1).trans_eq (tsum_congr fun j => ?_)
          rw [mul_rpow_of_nonneg _ _ hp.le, hc]
    _ = lqNorm 1 (fun i => dyadicWeight (s * p) i *
          ∑' j, (if j ≤ i then dyadicWeight (-(L * p)) (i - j) else 1) * a j ^ p) :=
        (lqNorm_one _).symm
    _ ≤ almostDiagonalConst (s * p) (L * p) *
          lqNorm 1 (fun j => dyadicWeight (s * p) j * a j ^ p) :=
        lqNorm_almostDiagonal_le le_rfl (s * p) (L * p) (fun j => a j ^ p)
    _ = almostDiagonalConst (s * p) (L * p) * ∑' j, (dyadicWeight s j * a j) ^ p := by
        rw [lqNorm_one]
        congr 1
        refine tsum_congr fun j => ?_
        rw [mul_rpow_of_nonneg _ _ hp.le, dyadicWeight_rpow]

/-- **The almost diagonal step at one point**: if `a_j ≤ C ∑_i c_{ji} m_i` for every `j`, with
`c_{ji} = 2^(-(j-i)L)` for `i ≤ j` and `c_{ji} = 1` for `i > j`, then for `1 ≤ q ≤ ∞`,
`‖(2^(js) a_j)_j‖_{ℓ_q} ≤ C A_{s,L} ‖(2^(is) m_i)_i‖_{ℓ_q}` with
`A_{s,L} = ENNReal.almostDiagonalConst s L`. -/
theorem lqNorm_le_almostDiagonalConst_mul_of_le {q : ℝ≥0∞} (hq : 1 ≤ q) (s L : ℝ) {C : ℝ≥0∞}
    {a m : ℕ → ℝ≥0∞}
    (h : ∀ j, a j ≤ C * ∑' i, (if i ≤ j then dyadicWeight (-L) (j - i) else 1) * m i) :
    lqNorm q (fun j => dyadicWeight s j * a j) ≤
      C * ENNReal.almostDiagonalConst s L * lqNorm q (fun i => dyadicWeight s i * m i) := by
  calc lqNorm q (fun j => dyadicWeight s j * a j)
      ≤ lqNorm q (fun j => C * (dyadicWeight s j *
          ∑' i, (if i ≤ j then dyadicWeight (-L) (j - i) else 1) * m i)) :=
        lqNorm_mono fun j => by
          rw [mul_left_comm]
          gcongr
          exact h j
    _ = C * lqNorm q (fun j => dyadicWeight s j *
          ∑' i, (if i ≤ j then dyadicWeight (-L) (j - i) else 1) * m i) :=
        lqNorm_const_mul _ _
    _ ≤ C * (ENNReal.almostDiagonalConst s L * lqNorm q (fun i => dyadicWeight s i * m i)) := by
        gcongr
        exact lqNorm_almostDiagonal_le hq s L m
    _ = _ := by rw [mul_assoc]

/-! ### Sequences on `ℤ` -/

/-- The geometric series without its first term is at most the full series:
`∑_{j ≥ 0} 2^(-(j+1)α) ≤ (1 - 2^(-α))⁻¹` for every real `α`. -/
theorem tsum_dyadicWeight_neg_succ_le (α : ℝ) :
    ∑' j : ℕ, dyadicWeight (-α) (j + 1) ≤ (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ :=
  (tsum_comp_le_tsum_of_injective (add_left_injective 1) (dyadicWeight (-α))).trans_eq
    (tsum_dyadicWeight_neg α)

/-- **A series over `ℤ` split at `m`**:
`∑_{n ∈ ℤ} f n = ∑_{j ≥ 0} f(m + j) + ∑_{j ≥ 0} f(m - (j+1))`, the terms with `n ≥ m` and those
with `n < m` (Mathlib's `tsum_of_nat_of_neg_add_one` after the shift `n ↦ m + n`). -/
theorem tsum_int_eq_tsum_add_tsum_sub (m : ℤ) (f : ℤ → ℝ≥0∞) :
    ∑' n, f n = ∑' j : ℕ, f (m + j) + ∑' j : ℕ, f (m - (j + 1)) := by
  rw [← (Equiv.addLeft m).tsum_eq f,
    tsum_of_nat_of_neg_add_one CompleteLattice.summable CompleteLattice.summable]
  simp only [Equiv.coe_addLeft, ← sub_eq_add_neg]

/-- **The `ℓ_q` norm on `ℤ` is shift invariant**: `‖(a(k + i))_k‖_{ℓ_q} = ‖a‖_{ℓ_q}` for every
`a : ℤ → [0, ∞]`, every `i ∈ ℤ` and every exponent `q`, since `k ↦ k + i` is a bijection of `ℤ`
(`lqNorm_comp_equiv` for Mathlib's `Equiv.addRight`). -/
theorem lqNorm_comp_add_int (q : ℝ≥0∞) (a : ℤ → ℝ≥0∞) (i : ℤ) :
    lqNorm q (fun k : ℤ => a (k + i)) = lqNorm q a :=
  lqNorm_comp_equiv (Equiv.addRight i) a

/-- **Young's inequality for a series of shifts on `ℤ`**: for weights `w_j ≥ 0`, shifts
`s_j ∈ ℤ` and `1 ≤ q ≤ ∞`, `‖(∑_j w_j c_{m + s_j})_{m ∈ ℤ}‖_{ℓ_q} ≤ (∑_j w_j) ‖c‖_{ℓ_q}`, by the
countable Minkowski inequality and the invariance of the norm under shifts. -/
theorem lqNorm_tsum_shift_le (hq : 1 ≤ q) (w : ℕ → ℝ≥0∞) (s : ℕ → ℤ) (c : ℤ → ℝ≥0∞) :
    lqNorm q (fun m => ∑' j, w j * c (m + s j)) ≤ (∑' j, w j) * lqNorm q c :=
  calc lqNorm q (fun m => ∑' j, w j * c (m + s j))
      ≤ ∑' j, lqNorm q (fun m => w j * c (m + s j)) :=
        lqNorm_tsum_le hq fun j m => w j * c (m + s j)
    _ = ∑' j, w j * lqNorm q c := by
        congr 1
        funext j
        rw [lqNorm_const_mul, lqNorm_comp_add_int]
    _ = (∑' j, w j) * lqNorm q c := ENNReal.tsum_mul_right

/-- **The geometric convolution from below on `ℤ`**: for `1 ≤ q ≤ ∞` and every real `α`,
`‖(∑_{j ≥ 0} 2^(-(j+1)α) c_{m-(j+1)})_{m ∈ ℤ}‖_{ℓ_q} ≤ (1 - 2^(-α))⁻¹ ‖c‖_{ℓ_q}`. -/
theorem lqNorm_tsum_geom_sub_le (hq : 1 ≤ q) (α : ℝ) (c : ℤ → ℝ≥0∞) :
    lqNorm q (fun m => ∑' j : ℕ, dyadicWeight (-α) (j + 1) * c (m - (j + 1))) ≤
      (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ * lqNorm q c := by
  have h := lqNorm_tsum_shift_le hq (fun j => dyadicWeight (-α) (j + 1))
    (fun j => -((j : ℤ) + 1)) c
  simp only [← sub_eq_add_neg] at h
  exact h.trans (by gcongr; exact tsum_dyadicWeight_neg_succ_le α)

/-- **The geometric convolution from above on `ℤ`**: for `1 ≤ q ≤ ∞` and every real `α`,
`‖(∑_{j ≥ 0} 2^(-jα) c_{m+j})_{m ∈ ℤ}‖_{ℓ_q} ≤ (1 - 2^(-α))⁻¹ ‖c‖_{ℓ_q}`. -/
theorem lqNorm_tsum_geom_add_le (hq : 1 ≤ q) (α : ℝ) (c : ℤ → ℝ≥0∞) :
    lqNorm q (fun m => ∑' j : ℕ, dyadicWeight (-α) j * c (m + j)) ≤
      (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ * lqNorm q c :=
  (lqNorm_tsum_shift_le hq (dyadicWeight (-α)) (fun j => (j : ℤ)) c).trans_eq
    (by rw [tsum_dyadicWeight_neg])

end ENNReal
