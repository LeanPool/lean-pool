/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Dyadic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The linear structure of `A^s_q`

For `s ≥ 0` and `1 ≤ q ≤ ∞` the approximation space `A^s_q` is a linear subspace of `X`, and
its quasi-norm satisfies the **quasi-triangle inequality**

`‖f + g‖_{A^s_q} ≤ C (‖f‖_{A^s_q} + ‖g‖_{A^s_q})`

(`approxNormDyadic_add_le` with `C = 2 · 2^s` for the dyadic quasi-norm, `approxNorm_add_le`
with `C = 8 · (2^s)^3` for Pietsch's; these constants are not optimised).  The reason is
`E_{2n}(f + g) ≤ E_n(f) + E_n(g)`: in the dyadic form, the errors of `f + g` at `2^(k+1)` are
controlled by those of `f` and `g` at `2^k`, at the cost of the factor `2^s`.

`ApproximationScheme.approxSpace A s q hs hq` is `A^s_q` as a `Submodule ℝ X`.  A `Submodule`
must carry the proof that it is closed under addition, which holds for `s ≥ 0` and `q ≥ 1`;
hence the two hypotheses are arguments of the definition.  The approximants themselves lie in
every `A^s_q` (`memApprox_of_mem`), and for `s > 0` the space lies in the closure of `⋃ A n`.
-/

@[expose] public section

open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {A : ApproximationScheme X} {s : ℝ} {q : ℝ≥0∞}

/-- The dyadic sequence of `f + g` at `k + 1` is controlled by those of `f` and `g` at `k`. -/
theorem approxSeqDyadic_add_le_succ (f g : X) (k : ℕ) :
    A.approxSeqDyadic s (f + g) (k + 1) ≤
      2 ^ s * (A.approxSeqDyadic s f k + A.approxSeqDyadic s g k) := by
  rw [approxSeqDyadic, ENNReal.dyadicWeight_succ, mul_assoc, approxSeqDyadic, approxSeqDyadic,
    ← mul_add]
  gcongr
  exact approxError_add_le_pow_succ k f g

/-- **Quasi-triangle inequality** for the dyadic quasi-norm, with constant `2 · 2^s`. -/
theorem approxNormDyadic_add_le (hq : 1 ≤ q) (hs : 0 ≤ s) (f g : X) :
    A.approxNormDyadic s q (f + g) ≤
      2 * 2 ^ s * (A.approxNormDyadic s q f + A.approxNormDyadic s q g) := by
  have h2s := ENNReal.one_le_two_rpow hs
  have hfg : ‖f + g‖ₑ ≤ ‖f‖ₑ + ‖g‖ₑ := eNorm_add_le f g
  have hD : lqNorm q (A.approxSeqDyadic s (f + g)) ≤ (‖f‖ₑ + ‖g‖ₑ) +
      2 ^ s * (lqNorm q (A.approxSeqDyadic s f) + lqNorm q (A.approxSeqDyadic s g)) := by
    refine (ENNReal.lqNorm_le_head_add_shift hq _).trans (add_le_add ?_ ?_)
    · rw [approxSeqDyadic_zero]; exact (approxError_le_enorm _ 1).trans hfg
    · calc lqNorm q (fun k => A.approxSeqDyadic s (f + g) (k + 1))
          ≤ lqNorm q (fun k => 2 ^ s * (A.approxSeqDyadic s f k + A.approxSeqDyadic s g k)) :=
            ENNReal.lqNorm_mono fun k => approxSeqDyadic_add_le_succ f g k
        _ = 2 ^ s * lqNorm q (fun k => A.approxSeqDyadic s f k + A.approxSeqDyadic s g k) :=
            ENNReal.lqNorm_const_mul _ _
        _ ≤ _ := by gcongr; exact ENNReal.lqNorm_add_le hq _ _
  calc A.approxNormDyadic s q (f + g) = ‖f + g‖ₑ + lqNorm q (A.approxSeqDyadic s (f + g)) := rfl
    _ ≤ (‖f‖ₑ + ‖g‖ₑ) + ((‖f‖ₑ + ‖g‖ₑ) +
          2 ^ s * (lqNorm q (A.approxSeqDyadic s f) + lqNorm q (A.approxSeqDyadic s g))) :=
        add_le_add hfg hD
    _ = 2 * (‖f‖ₑ + ‖g‖ₑ) +
          2 ^ s * (lqNorm q (A.approxSeqDyadic s f) + lqNorm q (A.approxSeqDyadic s g)) := by ring
    _ ≤ 2 * 2 ^ s * (‖f‖ₑ + ‖g‖ₑ) +
          2 * 2 ^ s * (lqNorm q (A.approxSeqDyadic s f) + lqNorm q (A.approxSeqDyadic s g)) := by
        gcongr
        · exact le_mul_of_one_le_right' h2s
        · exact le_mul_of_one_le_left' one_le_two
    _ = 2 * 2 ^ s * (A.approxNormDyadic s q f + A.approxNormDyadic s q g) := by
        simp only [approxNormDyadic]; ring

/-- **Quasi-triangle inequality** for Pietsch's quasi-norm, with the (not optimised) constant
`8 · (2^s)^3`, obtained through the dyadic quasi-norm. -/
theorem approxNorm_add_le (hq : 1 ≤ q) (hs : 0 ≤ s) (f g : X) :
    A.approxNorm s q (f + g) ≤ 8 * (2 ^ s) ^ 3 * (A.approxNorm s q f + A.approxNorm s q g) := by
  calc A.approxNorm s q (f + g) ≤ 2 ^ s * A.approxNormDyadic s q (f + g) :=
        approxNorm_le_approxNormDyadic hq hs _
    _ ≤ 2 ^ s * (2 * 2 ^ s * (A.approxNormDyadic s q f + A.approxNormDyadic s q g)) := by
        gcongr; exact approxNormDyadic_add_le hq hs f g
    _ ≤ 2 ^ s * (2 * 2 ^ s * (4 * 2 ^ s * A.approxNorm s q f + 4 * 2 ^ s * A.approxNorm s q g)) :=
      by
        gcongr <;> exact approxNormDyadic_le_approxNorm hq hs _
    _ = 8 * (2 ^ s) ^ 3 * (A.approxNorm s q f + A.approxNorm s q g) := by ring

/-- For `s ≥ 0` and `q ≥ 1`, `A^s_q` is closed under addition. -/
theorem MemApprox.add (hq : 1 ≤ q) (hs : 0 ≤ s) {f g : X} (hf : A.MemApprox s q f)
    (hg : A.MemApprox s q g) : A.MemApprox s q (f + g) := by
  rw [memApprox_iff_approxNormDyadic_lt_top hq hs] at hf hg ⊢
  exact (approxNormDyadic_add_le hq hs f g).trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by norm_num) (ENNReal.two_rpow_ne_top s).lt_top)
    (ENNReal.add_lt_top.2 ⟨hf, hg⟩))

/-- For `s ≥ 0` and `q ≥ 1`, `A^s_q` is closed under subtraction. -/
theorem MemApprox.sub (hq : 1 ≤ q) (hs : 0 ≤ s) {f g : X} (hf : A.MemApprox s q f)
    (hg : A.MemApprox s q g) : A.MemApprox s q (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hq hs hg.neg

/-- For `s ≥ 0` and `q ≥ 1`, `A^s_q` is closed under finite sums. -/
theorem MemApprox.sum (hq : 1 ≤ q) (hs : 0 ≤ s) {ι : Type*} (t : Finset ι) {f : ι → X}
    (hf : ∀ i ∈ t, A.MemApprox s q (f i)) : A.MemApprox s q (∑ i ∈ t, f i) :=
  Finset.sum_induction f (A.MemApprox s q) (fun _ _ ha hb => ha.add hq hs hb)
    (memApprox_zero s q) hf

/-- **Approximants lie in every approximation space**: an element of `A m` has only finitely
many nonzero dyadic errors. -/
theorem memApprox_of_mem (hq : 1 ≤ q) (hs : 0 ≤ s) {m : ℕ} {a : X} (ha : a ∈ A m) :
    A.MemApprox s q a := by
  rw [memApprox_iff_lqNorm_dyadic_lt_top hq hs]
  have hzero : ∀ k ∉ Finset.range m, A.approxSeqDyadic s a k = 0 := fun k hk => by
    have hmk : m ≤ 2 ^ k :=
      (not_lt.1 (Finset.mem_range.not.1 hk)).trans (Nat.lt_two_pow_self).le
    rw [approxSeqDyadic, approxError_eq_zero_of_mem (A.mono hmk ha), mul_zero]
  calc lqNorm q (A.approxSeqDyadic s a) ≤ ∑' k, A.approxSeqDyadic s a k :=
        ENNReal.lqNorm_le_lqNorm_one hq _
    _ = ∑ k ∈ Finset.range m, A.approxSeqDyadic s a k := tsum_eq_sum hzero
    _ < ∞ := ENNReal.sum_lt_top.2 fun k _ =>
        ENNReal.mul_lt_top (ENNReal.dyadicWeight_lt_top s k) (approxError_ne_top a _).lt_top

variable (A)

/-- The **approximation space** `A^s_q` as a real subspace of `X`, for `s ≥ 0`, `1 ≤ q ≤ ∞`. -/
def approxSpace (s : ℝ) (q : ℝ≥0∞) (hs : 0 ≤ s) (hq : 1 ≤ q) : Submodule ℝ X where
  carrier := {f | A.MemApprox s q f}
  zero_mem' := memApprox_zero s q
  add_mem' hf hg := MemApprox.add hq hs hf hg
  smul_mem' c _ hf := MemApprox.smul hf c

variable {A}

/-- Membership in the approximation space as a submodule. -/
@[simp]
theorem mem_approxSpace {hs : 0 ≤ s} {hq : 1 ≤ q} {f : X} :
    f ∈ A.approxSpace s q hs hq ↔ A.MemApprox s q f := Iff.rfl

/-- `⋃ A n ⊆ A^s_q`. -/
theorem iUnion_subset_approxSpace (hs : 0 ≤ s) (hq : 1 ≤ q) :
    (⋃ n, A n) ⊆ A.approxSpace s q hs hq := fun _ hf =>
  let ⟨_, hn⟩ := Set.mem_iUnion.1 hf
  memApprox_of_mem hq hs hn

/-- For `s > 0`, `A^s_q` lies in the closure of `⋃ A n`. -/
theorem approxSpace_subset_closure (hs : 0 < s) (hq : 1 ≤ q) :
    (A.approxSpace s q hs.le hq : Set X) ⊆ closure (⋃ n, A n) := fun _ hf =>
  mem_closure_iUnion_of_memApprox hq hs hf

end ApproximationScheme
