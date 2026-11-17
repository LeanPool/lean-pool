/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.OrthantHilbertPolynomial

/-! The maximal orthants determine the leading term of the Hilbert polynomial.
In particular its factorial-normalized leading coefficient is a positive
integer, counted by cells of the standard-exponent partition. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A nonempty sum of shifted binomial polynomials of dimensions `dim i` has degree the maximal
dimension `m` and leading coefficient `d / m!`, where `d > 0` is the number of summands of maximal
dimension. -/
lemma sum_preHilbertPoly_leading {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (dim shift : ι → ℕ) :
    let m := s.sup dim
    let d := (s.filter (fun i => dim i = m)).card
    let P := ∑ i ∈ s, Polynomial.preHilbertPoly ℚ (dim i) (shift i)
    0 < d ∧ P.natDegree = m ∧ P.leadingCoeff = (d : ℚ) / m.factorial := by
  dsimp only
  let m := s.sup dim
  let d := (s.filter (fun i => dim i = m)).card
  let P := ∑ i ∈ s, Polynomial.preHilbertPoly ℚ (dim i) (shift i)
  have hd : 0 < d := by
    apply Finset.card_pos.mpr
    obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup s hs dim
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, he.symm⟩⟩
  have hle : P.natDegree ≤ m := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    rw [Polynomial.natDegree_preHilbertPoly]
    exact Finset.le_sup hi
  have hc : P.coeff m = (d : ℚ) * (m.factorial : ℚ)⁻¹ := by
    simp only [P, Polynomial.finsetSum_coeff]
    calc
      _ = ∑ i ∈ s, if dim i = m then (m.factorial : ℚ)⁻¹ else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases he : dim i = m
        · rw [he, Polynomial.coeff_preHilbertPoly_self, ite_eq_left rfl]
        · rw [ite_eq_right he]
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [Polynomial.natDegree_preHilbertPoly]
          exact lt_of_le_of_ne (Finset.le_sup hi) he
      _ = _ := by rw [← Finset.sum_filter]; simp [d]
  have hc0 : P.coeff m ≠ 0 := by
    rw [hc]
    apply mul_ne_zero
    · exact_mod_cast Nat.ne_of_gt hd
    · exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m)
  have he : P.natDegree = m := le_antisymm hle (Polynomial.le_natDegree_of_ne_zero hc0)
  refine ⟨hd, he, ?_⟩
  rw [Polynomial.leadingCoeff, he, hc, div_eq_mul_inv]

open Classical in
/-- The cells `b ∈ {0, …, B}^σ` of the clamped orthant partition that lie in `S`. -/
def lowerSetOrthantPatterns {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (B : ℕ) : Finset (σ → Fin (B + 1)) :=
  Finset.univ.filter (fun b => (fun i => (b i).val) ∈ S)

open Classical in
/-- The orthant polynomial of `S` is the sum, over the cells of `S`, of the shifted binomial
polynomials of the corresponding orthants. -/
lemma lowerSetOrthantPolynomial_eq_sum {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (B : ℕ) :
    lowerSetOrthantPolynomial S B =
      ∑ b ∈ lowerSetOrthantPatterns S B,
        Polynomial.preHilbertPoly ℚ (Fintype.card (orthantFree b)) (orthantBaseDegree b) := by
  simp only [lowerSetOrthantPolynomial, lowerSetOrthantPatterns, Finset.sum_filter]

/-- A nonempty lower set has a positive integer multiplicity and an eventual
polynomial of degree at most the number of exponent coordinates. -/
theorem lowerSet_eventually_polynomial_positive {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (hS : IsLowerSet S) (hSne : S.Nonempty) :
    ∃ (P : Polynomial ℚ) (d : ℕ), 0 < d ∧
      P.natDegree ≤ Fintype.card σ ∧
      P.leadingCoeff = (d : ℚ) / P.natDegree.factorial ∧
      ∃ N : ℕ, ∀ n ≥ N, P.eval (n : ℚ) =
        (Nat.card {a : σ → ℕ // a ∈ S ∧ ∑ i, a i ≤ n} : ℚ) := by
  classical
  obtain ⟨B, _, hB⟩ := lowerSet_clamp_stabilizes S hS
  let s := lowerSetOrthantPatterns S B
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := hSne
    refine ⟨exponentPattern B a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact (hB a).mp ha
  obtain ⟨hd, hdeg, hlc⟩ := sum_preHilbertPoly_leading s hs
    (fun b => Fintype.card (orthantFree b)) orthantBaseDegree
  let P := lowerSetOrthantPolynomial S B
  have hPe : P = ∑ b ∈ s,
      Polynomial.preHilbertPoly ℚ (Fintype.card (orthantFree b)) (orthantBaseDegree b) :=
    lowerSetOrthantPolynomial_eq_sum S B
  refine ⟨P, _, hd, ?_, ?_, Fintype.card σ * B,
    fun n hn => lowerSetOrthantPolynomial_eval S B hB n hn⟩
  · rw [hPe, hdeg]
    apply Finset.sup_le
    intro b _
    exact Fintype.card_subtype_le _
  · rw [hPe, hdeg]
    exact hlc

end
end CCDN
