/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Fourier.Convolution
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Hardy

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Sequences on `ℕ^d`

The quasi-norms of the spaces of dominating mixed smoothness are `ℓ_q` norms of families indexed by
`k ∈ ℕ^d = Fin d → ℕ` with the **mixed weights** `2^(s|k|_1) = ∏_i 2^(s k_i)` (`Rd.mixedWeight`).
The `ℓ_q` norm on `ℕ^d` is `ENNReal.lqNorm`, the `L_q` norm for the counting measure, as on `ℕ`.

**The Schur test** (`Rd.lqNorm_schur_le`): if the row sums and the column sums of a nonnegative
matrix `w` are at most `A`, then `‖(∑_k w(m, k) b_k)_m‖_{ℓ_q} ≤ A ‖b‖_{ℓ_q}`, `1 ≤ q ≤ ∞`, by the
weighted Jensen inequality `(∑_k w b)^q ≤ (∑_k w)^(q-1) ∑_k w b^q`
(`MeasureTheory.lintegral_mul_rpow_le` for the counting measure).

**The almost diagonal lemma on `ℕ^d`** (`Rd.lqNorm_almostDiagonal_pi_le`): with the coefficients
`c(i, j) = 2^(-(i-j)L)` for `j ≤ i` and `1` for `j > i` (`Rd.almostDiagCoeff`) and `0 < s < L`,

`‖(2^(s|m|_1) ∑_k ∏_i c(m_i, k_i) a_k)_m‖_{ℓ_q} ≤ C^d ‖(2^(s|k|_1) a_k)_k‖_{ℓ_q}`,

`C = (1 - 2^(-(L-s)))⁻¹ + (1 - 2^(-s))⁻¹`. The matrix `2^(s|m|_1) ∏_i c(m_i, k_i) 2^(-s|k|_1)` is a
product over the coordinates of `u(m_i - k_i)` with `u(l) = 2^(-(L-s) l)` for `l ≥ 0` and
`u(l) = 2^(s l)` for `l < 0`, so its row and column sums are at most `(∑_{l ∈ ℤ} u(l))^d = C^d`.
This replaces the one-dimensional Hardy inequalities of `ENNReal.lqNorm_almostDiagonal_le`, which
do not iterate over the coordinates. With termwise bounds
`a_m ≤ C^d ∑_k ∏_i c(m_i, k_i) x_k` it gives
`‖(2^(s|m|_1) a_m)_m‖_{ℓ_q} ≤ (C C_s)^d ‖(2^(s|k|_1) x_k)_k‖_{ℓ_q}`
(`Rd.lqNorm_le_of_le_almostDiagonal_pi`).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

open ENNReal (dyadicWeight lqNorm)

namespace Rd

variable {d : ℕ} {q : ℝ≥0∞}

/-! ### The Schur test -/

/-- **The Schur test** on `ℓ_q`: if the row sums and the column sums of a nonnegative matrix `w` are
at most `A`, then `‖(∑_k w(m, k) b_k)_m‖_{ℓ_q} ≤ A ‖b‖_{ℓ_q}` for `1 ≤ q ≤ ∞`, by the weighted
Jensen inequality `(∑_k w b)^q ≤ (∑_k w)^(q-1) ∑_k w b^q`. -/
theorem lqNorm_schur_le {ι κ : Type*} [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] [MeasurableSpace κ] [Countable κ] [MeasurableSingletonClass κ]
    (hq : 1 ≤ q) {w : ι → κ → ℝ≥0∞} {A : ℝ≥0∞} (hrow : ∀ m, ∑' k, w m k ≤ A)
    (hcol : ∀ k, ∑' m, w m k ≤ A) (b : κ → ℝ≥0∞) :
    lqNorm q (fun m => ∑' k, w m k * b k) ≤ A * lqNorm q b := by
  rcases eq_or_ne q ∞ with rfl | hq'
  · rw [ENNReal.lqNorm_top, ENNReal.lqNorm_top]
    refine iSup_le fun m => ?_
    calc ∑' k, w m k * b k ≤ ∑' k, w m k * ⨆ k', b k' :=
          tsum_le_tsum fun k => mul_le_mul' le_rfl (le_iSup b k)
      _ = (∑' k, w m k) * ⨆ k', b k' := ENNReal.tsum_mul_right
      _ ≤ A * ⨆ k', b k' := mul_le_mul' (hrow m) le_rfl
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  set r := q.toReal
  have hr : 1 ≤ r := ENNReal.one_le_toReal_of_one_le hq hq'
  have hr0 : 0 < r := by linarith
  rw [ENNReal.lqNorm_eq_tsum hq0 hq', ENNReal.lqNorm_eq_tsum hq0 hq']
  -- the weighted Jensen inequality in each row
  have hjensen : ∀ m, (∑' k, w m k * b k) ^ r ≤ A ^ (r - 1) * ∑' k, w m k * b k ^ r := fun m => by
    have h := lintegral_mul_rpow_le (μ := (Measure.count : Measure κ)) hr
      (measurable_of_countable (w m)).aemeasurable (measurable_of_countable b).aemeasurable
    simp only [lintegral_count] at h
    exact h.trans (mul_le_mul' (ENNReal.rpow_le_rpow (hrow m) (by linarith)) le_rfl)
  have hsum : ∑' m, (∑' k, w m k * b k) ^ r ≤ A ^ r * ∑' k, b k ^ r := by
    calc ∑' m, (∑' k, w m k * b k) ^ r ≤ ∑' m, A ^ (r - 1) * ∑' k, w m k * b k ^ r :=
          tsum_le_tsum hjensen
      _ = A ^ (r - 1) * ∑' k, (∑' m, w m k) * b k ^ r := by
          rw [ENNReal.tsum_mul_left, tsum_comm]
          simp_rw [ENNReal.tsum_mul_right]
      _ ≤ A ^ (r - 1) * ∑' k, A * b k ^ r :=
          mul_le_mul' le_rfl (tsum_le_tsum fun k => mul_le_mul' (hcol k) le_rfl)
      _ = A ^ r * ∑' k, b k ^ r := by
          rw [ENNReal.tsum_mul_left, ← mul_assoc]
          congr 1
          conv_rhs => rw [show r = (r - 1) + 1 by ring]
          rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
  calc (∑' m, (∑' k, w m k * b k) ^ r) ^ (1 / r)
      ≤ (A ^ r * ∑' k, b k ^ r) ^ (1 / r) := ENNReal.rpow_le_rpow hsum (by positivity)
    _ = A * (∑' k, b k ^ r) ^ (1 / r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hr0.ne', ENNReal.rpow_one]

/-- **Sums of products over `ℕ^d`**: `∑_k ∏_i f_i(k_i) ≤ ∏_i ∑_j f_i(j)`, from the finite boxes
(Mathlib's `Finset.prod_univ_sum`). -/
theorem tsum_prod_le_prod_tsum (f : Fin d → ℕ → ℝ≥0∞) :
    ∑' k : Fin d → ℕ, ∏ i, f i (k i) ≤ ∏ i, ∑' j, f i j := by
  rw [tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  set N := S.sup fun k => Finset.univ.sup k
  have hsub : S ⊆ Fintype.piFinset fun _ => Finset.range (N + 1) := fun k hk => by
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Finset.le_sup (f := k) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun k => Finset.univ.sup k) hk)
  calc ∑ k ∈ S, ∏ i, f i (k i)
      ≤ ∑ k ∈ Fintype.piFinset (fun _ => Finset.range (N + 1)), ∏ i, f i (k i) :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∏ i, ∑ j ∈ Finset.range (N + 1), f i j := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' j, f i j := Finset.prod_le_prod fun i _ => sum_le_tsum _

/-! ### The almost diagonal lemma -/

/-- The **mixed weight** `2^(s|k|_1) = ∏_i 2^(s k_i)`. -/
noncomputable def mixedWeight (s : ℝ) (k : Fin d → ℕ) : ℝ≥0∞ := ∏ i, dyadicWeight s (k i)

/-- The mixed weights are finite. -/
theorem mixedWeight_ne_top (s : ℝ) (k : Fin d → ℕ) : mixedWeight s k ≠ ∞ :=
  ENNReal.prod_ne_top fun i _ => ENNReal.dyadicWeight_ne_top s (k i)

/-- `2^(-s|k|_1) 2^(s|k|_1) = 1`. -/
theorem mixedWeight_neg_mul_self (s : ℝ) (k : Fin d → ℕ) :
    mixedWeight (-s) k * mixedWeight s k = 1 := by
  rw [mixedWeight, mixedWeight, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => ENNReal.dyadicWeight_neg_mul_self s (k i)

/-- The coefficient `c(i, j) = 2^(-(i-j)L)` for `j ≤ i` and `1` for `j > i` of the almost diagonal
lemma. -/
noncomputable def almostDiagCoeff (L : ℝ) (i j : ℕ) : ℝ≥0∞ :=
  if j ≤ i then dyadicWeight (-L) (i - j) else 1

/-- The profile `u(l) = 2^(-(L-s) l)` for `l ≥ 0` and `2^(s l)` for `l < 0` on `ℤ`. -/
noncomputable def almostDiagProfile (s L : ℝ) (l : ℤ) : ℝ≥0∞ :=
  if 0 ≤ l then (2 : ℝ≥0∞) ^ ((l : ℝ) * (s - L)) else (2 : ℝ≥0∞) ^ ((l : ℝ) * s)

/-- `2^(s i) c(i, j) 2^(-s j) = u(i - j)`. -/
theorem dyadicWeight_mul_almostDiagCoeff_mul (s L : ℝ) (i j : ℕ) :
    dyadicWeight s i * almostDiagCoeff L i j * dyadicWeight (-s) j =
      almostDiagProfile s L ((i : ℤ) - j) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  have h2' : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
  simp only [almostDiagCoeff, almostDiagProfile, ENNReal.dyadicWeight]
  by_cases hji : j ≤ i
  · have hl : (0 : ℤ) ≤ (i : ℤ) - j := by omega
    simp only [hji, hl, ↓reduceIte]
    rw [← ENNReal.rpow_add _ _ h2 h2', ← ENNReal.rpow_add _ _ h2 h2']
    congr 1
    push_cast [Nat.cast_sub hji]
    ring
  · have hl : ¬ (0 : ℤ) ≤ (i : ℤ) - j := by omega
    simp only [hji, hl, ↓reduceIte]
    rw [mul_one, ← ENNReal.rpow_add _ _ h2 h2']
    congr 1
    push_cast
    ring

/-- `∑_{l ∈ ℤ} u(l) ≤ (1 - 2^(-(L-s)))⁻¹ + (1 - 2^(-s))⁻¹`, two geometric series. -/
theorem tsum_almostDiagProfile_le (s L : ℝ) (hs : 0 ≤ s) :
    ∑' l, almostDiagProfile s L l ≤
      (1 - (2 : ℝ≥0∞) ^ (-(L - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ := by
  rw [(CompleteLattice.summable.hasSum.of_nat_of_neg_add_one
    CompleteLattice.summable.hasSum).tsum_eq]
  refine add_le_add (le_of_eq ?_) ?_
  · rw [← ENNReal.tsum_dyadicWeight_neg]
    refine tsum_congr fun n => ?_
    simp only [almostDiagProfile, Int.natCast_nonneg, ↓reduceIte, ENNReal.dyadicWeight]
    congr 1
    push_cast
    ring
  · rw [← ENNReal.tsum_dyadicWeight_neg]
    refine tsum_le_tsum fun n => ?_
    have hneg : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1) := by omega
    simp only [almostDiagProfile, hneg, ↓reduceIte, ENNReal.dyadicWeight]
    refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    push_cast
    nlinarith

/-- **The almost diagonal lemma on `ℕ^d`**: for `0 < s < L` and `1 ≤ q ≤ ∞`,
`‖(2^(s|m|_1) ∑_k ∏_i c(m_i, k_i) a_k)_m‖_{ℓ_q} ≤ C^d ‖(2^(s|k|_1) a_k)_k‖_{ℓ_q}` with
`C = (1 - 2^(-(L-s)))⁻¹ + (1 - 2^(-s))⁻¹`, by the Schur test: the matrix
`2^(s|m|_1) ∏_i c(m_i, k_i) 2^(-s|k|_1) = ∏_i u(m_i - k_i)` has row and column sums at most `C^d`.
-/
theorem lqNorm_almostDiagonal_pi_le (hq : 1 ≤ q) {s L : ℝ} (hs : 0 ≤ s)
    (a : (Fin d → ℕ) → ℝ≥0∞) :
    lqNorm q (fun m => mixedWeight s m *
        ∑' k, (∏ i, almostDiagCoeff L (m i) (k i)) * a k) ≤
      ENNReal.almostDiagonalConst s L ^ d * lqNorm q (fun k => mixedWeight s k * a k) := by
  set C := ENNReal.almostDiagonalConst s L
  set w : (Fin d → ℕ) → (Fin d → ℕ) → ℝ≥0∞ := fun m k =>
    ∏ i, almostDiagProfile s L ((m i : ℤ) - k i)
  have hw : ∀ m k, mixedWeight s m * (∏ i, almostDiagCoeff L (m i) (k i)) * mixedWeight (-s) k =
      w m k := fun m k => by
    simp only [w, mixedWeight, ← dyadicWeight_mul_almostDiagCoeff_mul, Finset.prod_mul_distrib]
  have hprof : ∑' l, almostDiagProfile s L l ≤ C := tsum_almostDiagProfile_le s L hs
  have hrow : ∀ m, ∑' k, w m k ≤ C ^ d := fun m => by
    refine (tsum_prod_le_prod_tsum fun i j => almostDiagProfile s L ((m i : ℤ) - j)).trans ?_
    calc ∏ i, ∑' j : ℕ, almostDiagProfile s L ((m i : ℤ) - j) ≤ ∏ _i : Fin d, C :=
          Finset.prod_le_prod fun i _ => le_trans
            (tsum_comp_le_tsum_of_injective (fun j j' h => by simpa using h) _) hprof
      _ = C ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcol : ∀ k, ∑' m, w m k ≤ C ^ d := fun k => by
    refine (tsum_prod_le_prod_tsum fun i j => almostDiagProfile s L ((j : ℤ) - k i)).trans ?_
    calc ∏ i, ∑' j : ℕ, almostDiagProfile s L ((j : ℤ) - k i) ≤ ∏ _i : Fin d, C :=
          Finset.prod_le_prod fun i _ => le_trans
            (tsum_comp_le_tsum_of_injective (fun j j' h => by simpa using h) _) hprof
      _ = C ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine le_trans (le_of_eq ?_) (lqNorm_schur_le hq hrow hcol _)
  congr 1
  funext m
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [← hw m k]
  calc mixedWeight s m * ((∏ i, almostDiagCoeff L (m i) (k i)) * a k)
      = mixedWeight s m * (∏ i, almostDiagCoeff L (m i) (k i)) *
          (mixedWeight (-s) k * mixedWeight s k) * a k := by
        rw [mixedWeight_neg_mul_self, mul_one, mul_assoc]
    _ = mixedWeight s m * (∏ i, almostDiagCoeff L (m i) (k i)) * mixedWeight (-s) k *
          (mixedWeight s k * a k) := by ring

/-- **The almost diagonal lemma for termwise bounds**: for `0 ≤ s`, `1 ≤ q ≤ ∞` and
`C ∈ [0, ∞]`, if `a_m ≤ C^d ∑_k ∏_i c(m_i, k_i) x_k` for every `m ∈ ℕ^d`, then
`‖(2^(s|m|_1) a_m)_m‖_{ℓ_q} ≤ (C C_s)^d ‖(2^(s|k|_1) x_k)_k‖_{ℓ_q}` with the constant `C_s` of
`Rd.lqNorm_almostDiagonal_pi_le`, by the homogeneity of the `ℓ_q` norm and that lemma. -/
theorem lqNorm_le_of_le_almostDiagonal_pi (hq : 1 ≤ q) {s L : ℝ} (hs : 0 ≤ s) {C : ℝ≥0∞}
    {a x : (Fin d → ℕ) → ℝ≥0∞}
    (ha : ∀ m, a m ≤ C ^ d * ∑' k, (∏ i, almostDiagCoeff L (m i) (k i)) * x k) :
    lqNorm q (fun m => mixedWeight s m * a m) ≤
      (C * ENNReal.almostDiagonalConst s L) ^ d * lqNorm q (fun k => mixedWeight s k * x k) := by
  calc lqNorm q (fun m => mixedWeight s m * a m)
      ≤ lqNorm q (fun m => C ^ d * (mixedWeight s m *
          ∑' k, (∏ i, almostDiagCoeff L (m i) (k i)) * x k)) :=
        ENNReal.lqNorm_mono fun m => by
          calc mixedWeight s m * a m
              ≤ mixedWeight s m * (C ^ d *
                  ∑' k, (∏ i, almostDiagCoeff L (m i) (k i)) * x k) :=
                mul_le_mul' le_rfl (ha m)
            _ = _ := by ring
    _ = C ^ d * lqNorm q (fun m => mixedWeight s m *
          ∑' k, (∏ i, almostDiagCoeff L (m i) (k i)) * x k) := ENNReal.lqNorm_const_mul _ _
    _ ≤ C ^ d * (ENNReal.almostDiagonalConst s L ^ d * lqNorm q (fun k => mixedWeight s k * x k)) :=
        mul_le_mul' le_rfl (lqNorm_almostDiagonal_pi_le hq hs _)
    _ = _ := by rw [mul_pow, mul_assoc]

end Rd
