/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteMonomialSpan.lean.
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

public import LeanPool.GinibrePoincare.Analysis.ComplexHermiteOrthogonality

/-! # Triangular inversion between complex Hermites and monomials -/


@[expose] public section


open scoped ComplexConjugate BigOperators

namespace GinibrePoincare
namespace ComplexHermite

noncomputable section

/-- Span of normalized complex Hermite functions whose two indices lie in a
fixed rectangle. -/
def normalizedEvalRectangleSpan (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    Submodule ℂ (ℂ → ℂ) :=
  Submodule.span ℂ {f | ∃ a ≤ p, ∃ b ≤ q, f = normalizedEval n hn a b}

theorem normalizedEval_mem_rectangleSpan (n : ℕ) (hn : 0 < n)
    {p q a b : ℕ} (ha : a ≤ p) (hb : b ≤ q) :
    normalizedEval n hn a b ∈ normalizedEvalRectangleSpan n hn p q := by
  apply Submodule.subset_span
  exact ⟨a, ha, b, hb, rfl⟩

theorem normalizedEvalRectangleSpan_mono (n : ℕ) (hn : 0 < n)
    {p q P Q : ℕ} (hp : p ≤ P) (hq : q ≤ Q) :
    normalizedEvalRectangleSpan n hn p q ≤
      normalizedEvalRectangleSpan n hn P Q := by
  apply Submodule.span_mono
  rintro f ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, ha.trans hp, b, hb.trans hq, rfl⟩

private theorem oneDimNormalization_ne_zero (n : ℕ) (hn : 0 < n) (p : ℕ) :
    oneDimNormalization n p ≠ 0 := by
  unfold oneDimNormalization
  positivity

/-- Every diagonal mixed monomial is in the rectangular span of normalized
complex Hermite functions.  This is the algebraic triangular inversion. -/
theorem mixedMonomial_mem_normalizedEvalRectangleSpan
    (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    (fun z : ℂ ↦ z ^ p * (conj z) ^ q) ∈
      normalizedEvalRectangleSpan n hn p q := by
  induction h : min p q using Nat.strong_induction_on generalizing p q with
  | ind m ih =>
      let S := normalizedEvalRectangleSpan n hn p q
      let N : ℂ :=
        ((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ)
      have hN : N ≠ 0 := by
        unfold N
        exact Complex.ofReal_ne_zero.mpr
          (mul_ne_zero (oneDimNormalization_ne_zero n hn p)
            (oneDimNormalization_ne_zero n hn q))
      have hHerm : normalizedEval n hn p q ∈ S :=
        normalizedEval_mem_rectangleSpan n hn le_rfl le_rfl
      let rest : ℂ → ℂ := fun z ↦
        ∑ k ∈ (Finset.range (min p q + 1)).erase 0,
          (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
              (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
            z ^ (p - k) * (conj z) ^ (q - k)
      have hrest : rest ∈ S := by
        rw [show rest = ∑ k ∈ (Finset.range (min p q + 1)).erase 0,
            fun z ↦ (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
              (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
              z ^ (p - k) * (conj z) ^ (q - k) by
          funext z
          simp [rest]]
        apply Submodule.sum_mem
        intro k hk
        have hkRange : k ∈ Finset.range (min p q + 1) :=
          (Finset.mem_erase.mp hk).2
        have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hk_le : k ≤ min p q := by
          exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hkRange)
        have hkmin : min (p - k) (q - k) < m := by
          omega
        have hlower := ih _ hkmin (p - k) (q - k) (by rfl)
        have hmono : normalizedEvalRectangleSpan n hn (p - k) (q - k) ≤ S :=
          normalizedEvalRectangleSpan_mono n hn (Nat.sub_le _ _) (Nat.sub_le _ _)
        have hsmul := S.smul_mem
          (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
            (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ))
          (hmono hlower)
        convert hsmul using 1
        ext z
        simp [smul_eq_mul]
        ring
      have hexpand : normalizedEval n hn p q =
          fun z ↦ N * (z ^ p * (conj z) ^ q + rest z) := by
        funext z
        rw [normalizedEval_eq_sum]
        change N * _ = _
        congr 1
        have hzero : 0 ∈ Finset.range (min p q + 1) := by simp
        rw [← Finset.sum_erase_add _ _ hzero]
        simp [rest]
      have hsum : (fun z ↦ N * (z ^ p * (conj z) ^ q + rest z)) ∈ S := by
        rw [← hexpand]
        exact hHerm
      have hscaled : (fun z ↦ N * (z ^ p * (conj z) ^ q)) ∈ S := by
        have := S.sub_mem hsum (S.smul_mem N hrest)
        convert this using 1
        ext z
        simp
        ring
      have := S.smul_mem N⁻¹ hscaled
      convert this using 1
      ext z
      simp [hN]

/-- Rectangular span of ordinary diagonal mixed monomials. -/
def mixedMonomialRectangleSpan (p q : ℕ) : Submodule ℂ (ℂ → ℂ) :=
  Submodule.span ℂ {f | ∃ a ≤ p, ∃ b ≤ q,
    f = fun z : ℂ ↦ z ^ a * (conj z) ^ b}

theorem mixedMonomialRectangleSpan_mono {p q P Q : ℕ}
    (hp : p ≤ P) (hq : q ≤ Q) :
    mixedMonomialRectangleSpan p q ≤ mixedMonomialRectangleSpan P Q := by
  apply Submodule.span_mono
  rintro f ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, ha.trans hp, b, hb.trans hq, rfl⟩

theorem normalizedEval_mem_mixedMonomialRectangleSpan
    (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    normalizedEval n hn p q ∈ mixedMonomialRectangleSpan p q := by
  rw [show normalizedEval n hn p q = fun z ↦
      ((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ) *
        ∑ k ∈ Finset.range (min p q + 1),
          (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
              (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
            z ^ (p - k) * (conj z) ^ (q - k) by
    funext z
    exact normalizedEval_eq_sum n hn p q z]
  have hsum : (fun z : ℂ ↦
      ∑ k ∈ Finset.range (min p q + 1),
        (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
            (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
          z ^ (p - k) * (conj z) ^ (q - k)) ∈
      mixedMonomialRectangleSpan p q := by
    rw [show (fun z : ℂ ↦ ∑ k ∈ Finset.range (min p q + 1),
        (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
          (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
          z ^ (p-k) * (conj z) ^ (q-k)) =
        ∑ k ∈ Finset.range (min p q + 1), fun z : ℂ ↦
          (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
            (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
            z ^ (p-k) * (conj z) ^ (q-k) by funext z; simp]
    apply Submodule.sum_mem
    intro k hk
    have hm : (fun z : ℂ ↦ z ^ (p-k) * (conj z) ^ (q-k)) ∈
        mixedMonomialRectangleSpan p q := by
      apply Submodule.subset_span
      exact ⟨p-k, Nat.sub_le _ _, q-k, Nat.sub_le _ _, rfl⟩
    have hs := (mixedMonomialRectangleSpan p q).smul_mem
      (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
        (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) hm
    convert hs using 1
    ext z
    simp [smul_eq_mul]
    ring
  have hs := (mixedMonomialRectangleSpan p q).smul_mem
    (((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ)) hsum
  convert hs using 1

theorem normalizedEvalRectangleSpan_eq_mixedMonomialRectangleSpan
    (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    normalizedEvalRectangleSpan n hn p q = mixedMonomialRectangleSpan p q := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro f ⟨a, ha, b, hb, rfl⟩
    exact (mixedMonomialRectangleSpan_mono ha hb)
      (normalizedEval_mem_mixedMonomialRectangleSpan n hn a b)
  · apply Submodule.span_le.2
    rintro f ⟨a, ha, b, hb, rfl⟩
    exact (normalizedEvalRectangleSpan_mono n hn ha hb)
      (mixedMonomial_mem_normalizedEvalRectangleSpan n hn a b)

end
end ComplexHermite
end GinibrePoincare
