/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Blocks

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Synthesis with decay

A block decomposition `f = ∑ g_j` with `g_j ∈ A (2^j)` controls `‖f‖_{A^s_q}`
(`ApproximationSpaces.Decompositions.Blocks`).  Atoms of a function space lie in no fixed set of
approximants, so their blocks need a weaker hypothesis: `g_j` has size `ε_j` and is
**approximable at rate `σ` from level `j` on**,

`‖g_j‖ ≤ ε_j`,   `E_{2^k}(g_j) ≤ C 2^(-(k-j)σ) ε_j`   for `k ≥ j`.

Then for `0 < s < σ` and `1 ≤ q ≤ ∞` (`ApproximationScheme.approxNormDyadic_le_of_hasSum_decay`)

`‖f‖_{A^s_q} ≤ (2 (1 - 2^(-s))⁻¹ + C (1 - 2^(-(σ-s)))⁻¹) ‖(2^(js) ε_j)_j‖_{ℓ_q}`

in the dyadic quasi-norm.  The levels `j ≤ k` are approximated together, which needs a
**linear** scheme (`ApproximationScheme.IsLinear`: each `A n` closed under addition), so that
`E_n(f + g) ≤ E_n(f) + E_n(g)`; the levels `j > k` are estimated by their size.  The two parts
are the two Hardy inequalities, with exponents `σ - s` and `s`.
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {A : ApproximationScheme X} {s : ℝ} {q : ℝ≥0∞}

/-- A scheme is **linear** if every set of approximants is closed under addition, so that it is
a linear subspace. -/
def IsLinear (A : ApproximationScheme X) : Prop := ∀ n, ∀ a ∈ A n, ∀ b ∈ A n, a + b ∈ A n

/-- The scheme of an increasing sequence of subspaces is linear. -/
theorem isLinear_ofSubmodules (V : ℕ → Submodule ℝ X) (h0 : V 0 = ⊥) (hV : Monotone V) :
    (ofSubmodules V h0 hV).IsLinear := fun n a ha b hb => by
  rw [mem_ofSubmodules] at ha hb ⊢
  exact (V n).add_mem ha hb

/-- The dyadic scheme of an increasing sequence of subspaces is linear. -/
theorem isLinear_ofMonotoneSubmodules (V : ℕ → Submodule ℝ X) (hV : Monotone V) :
    (ofMonotoneSubmodules V hV).IsLinear :=
  isLinear_ofSubmodules _ _ _

/-- The image of a linear scheme under a linear map is linear. -/
theorem IsLinear.map {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (hA : A.IsLinear)
    (T : X →ₗ[ℝ] Y) : (A.map T).IsLinear := fun n a ha b hb => by
  obtain ⟨a', ha', rfl⟩ := A.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := A.mem_map.1 hb
  exact A.mem_map.2 ⟨a' + b', hA n a' ha' b' hb', map_add T a' b'⟩

/-- For a linear scheme the error is subadditive at a fixed complexity:
`E_n(f + g) ≤ E_n(f) + E_n(g)`. -/
theorem approxError_add_le_of_isLinear (hA : A.IsLinear) (n : ℕ) (f g : X) :
    A.approxError (f + g) n ≤ A.approxError f n + A.approxError g n :=
  approxError_add_le_of_add_mem (hA n) f g

/-- `E_n(∑ g_j) ≤ ∑ E_n(g_j)` for a linear scheme (Mathlib's `Finset.le_sum_of_subadditive`). -/
theorem approxError_sum_le_of_isLinear (hA : A.IsLinear) (n : ℕ) {ι : Type*} (t : Finset ι)
    (g : ι → X) : A.approxError (∑ j ∈ t, g j) n ≤ ∑ j ∈ t, A.approxError (g j) n :=
  Finset.le_sum_of_subadditive (A.approxError · n) (approxError_zero_left n).le
    (approxError_add_le_of_isLinear hA n) t g

/-- The algebra of the weights: `2^(ks) 2^(-(k-j)σ) = 2^(-k(σ-s)) 2^(jσ)` for `j ≤ k`
(`ENNReal.dyadicWeight_mul_dyadicWeight_neg_sub`). -/
theorem dyadicWeight_mul_dyadicWeight_sub {σ : ℝ} {j k : ℕ} (hjk : j ≤ k) (c e : ℝ≥0∞) :
    dyadicWeight s k * (c * dyadicWeight (-σ) (k - j) * e) =
      c * (dyadicWeight (-(σ - s)) k * (dyadicWeight σ j * e)) :=
  calc dyadicWeight s k * (c * dyadicWeight (-σ) (k - j) * e)
      = c * (dyadicWeight s k * dyadicWeight (-σ) (k - j)) * e := by ring
    _ = _ := by rw [ENNReal.dyadicWeight_mul_dyadicWeight_neg_sub s σ hjk]; ring

/-- **Synthesis with decay**: for a linear scheme, `f = ∑ g_j` with `‖g_j‖ ≤ ε_j` and
`E_{2^k}(g_j) ≤ C 2^(-(k-j)σ) ε_j` for `k ≥ j` satisfies
`‖f‖_{A^s_q} ≤ (2 (1 - 2^(-s))⁻¹ + C (1 - 2^(-(σ-s)))⁻¹) ‖(2^(js) ε_j)_j‖_{ℓ_q}` (dyadic
quasi-norm).  The constant is finite for `0 < s < σ`. -/
theorem approxNormDyadic_le_of_hasSum_decay (hA : A.IsLinear) (hq : 1 ≤ q) {σ : ℝ}
    {C : ℝ≥0∞} {f : X} {g : ℕ → X} (hf : HasSum g f) {ε : ℕ → ℝ≥0∞}
    (hsize : ∀ j, ‖g j‖ₑ ≤ ε j)
    (hdecay : ∀ j k, j ≤ k → A.approxError (g j) (2 ^ k) ≤ C * dyadicWeight (-σ) (k - j) * ε j) :
    A.approxNormDyadic s q f ≤ (2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ +
      C * (1 - (2 : ℝ≥0∞) ^ (-(σ - s)))⁻¹) * lqNorm q (fun j => dyadicWeight s j * ε j) := by
  set Cs := (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹
  set Cα := (1 - (2 : ℝ≥0∞) ^ (-(σ - s)))⁻¹
  set P := lqNorm q (fun j => dyadicWeight s j * ε j)
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  -- the tail of the series
  have htail : ∀ k, ‖f - ∑ j ∈ range (k + 1), g j‖ₑ ≤ ∑' i, ε (k + i) := fun k => by
    calc _ ≤ ∑' i, ‖g (i + (k + 1))‖ₑ := hf.enorm_sub_sum_range_le (k + 1)
      _ ≤ ∑' i, ε (i + (k + 1)) := tsum_le_tsum fun i => hsize _
      _ = ∑' i, ε (k + (i + 1)) := by congr 1; funext i; congr 1; omega
      _ ≤ ∑' i, ε (k + i) :=
          tsum_comp_le_tsum_of_injective Nat.succ_injective (fun i => ε (k + i))
  -- the dyadic errors
  have herr : ∀ k, A.approxSeqDyadic s f k ≤
      C * (dyadicWeight (-(σ - s)) k * ∑ j ∈ range (k + 1), dyadicWeight σ j * ε j) +
        dyadicWeight s k * ∑' i, ε (k + i) := fun k => by
    have h1 : A.approxError (∑ j ∈ range (k + 1), g j) (2 ^ k) ≤
        ∑ j ∈ range (k + 1), C * dyadicWeight (-σ) (k - j) * ε j :=
      (approxError_sum_le_of_isLinear hA _ _ _).trans (Finset.sum_le_sum fun j hj =>
        hdecay j k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
    calc A.approxSeqDyadic s f k = dyadicWeight s k * A.approxError f (2 ^ k) := rfl
      _ ≤ dyadicWeight s k * (∑ j ∈ range (k + 1), C * dyadicWeight (-σ) (k - j) * ε j +
            ∑' i, ε (k + i)) := by
          gcongr
          exact (approxError_le_approxError_add_enorm _ f _).trans (add_le_add h1 (htail k))
      _ = ∑ j ∈ range (k + 1), dyadicWeight s k * (C * dyadicWeight (-σ) (k - j) * ε j) +
            dyadicWeight s k * ∑' i, ε (k + i) := by rw [mul_add, Finset.mul_sum]
      _ = C * (dyadicWeight (-(σ - s)) k * ∑ j ∈ range (k + 1), dyadicWeight σ j * ε j) +
            dyadicWeight s k * ∑' i, ε (k + i) := by
          rw [Finset.sum_congr rfl fun j hj => dyadicWeight_mul_dyadicWeight_sub
            (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) C (ε j), ← Finset.mul_sum,
            ← Finset.mul_sum]
  have hHs : lqNorm q (fun k => dyadicWeight (-(σ - s)) k *
      ∑ j ∈ range (k + 1), dyadicWeight σ j * ε j) ≤ Cα * P := by
    refine (ENNReal.hardy_sum_le hq (σ - s) (fun j => dyadicWeight σ j * ε j)).trans_eq ?_
    congr 2; funext k
    rw [← mul_assoc, ← ENNReal.dyadicWeight_add]; congr 2; ring
  have hHt : lqNorm q (fun k => dyadicWeight s k * ∑' i, ε (k + i)) ≤ Cs * P :=
    ENNReal.hardy_tail_le hq s ε
  have hf0 : ‖f‖ₑ ≤ Cs * P := by
    calc ‖f‖ₑ ≤ ∑' i, ε i := by
          rw [← hf.tsum_eq]
          exact eNorm_tsum_le_tsum_eNorm.trans (tsum_le_tsum hsize)
      _ = dyadicWeight s 0 * ∑' i, ε (0 + i) := by simp
      _ ≤ lqNorm q (fun k => dyadicWeight s k * ∑' i, ε (k + i)) :=
          ENNReal.le_lqNorm hq0 (fun k => dyadicWeight s k * ∑' i, ε (k + i)) 0
      _ ≤ Cs * P := hHt
  calc A.approxNormDyadic s q f = ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f) := rfl
    _ ≤ Cs * P + (C * (Cα * P) + Cs * P) := by
        gcongr
        calc lqNorm q (A.approxSeqDyadic s f)
            ≤ lqNorm q (fun k => C * (dyadicWeight (-(σ - s)) k *
                ∑ j ∈ range (k + 1), dyadicWeight σ j * ε j) +
                dyadicWeight s k * ∑' i, ε (k + i)) := ENNReal.lqNorm_mono herr
          _ ≤ C * lqNorm q (fun k => dyadicWeight (-(σ - s)) k *
                ∑ j ∈ range (k + 1), dyadicWeight σ j * ε j) +
                lqNorm q (fun k => dyadicWeight s k * ∑' i, ε (k + i)) := by
              refine (ENNReal.lqNorm_add_le hq _ _).trans ?_
              rw [ENNReal.lqNorm_const_mul]
          _ ≤ C * (Cα * P) + Cs * P := by gcongr
    _ = (2 * Cs + C * Cα) * P := by ring

end ApproximationScheme
