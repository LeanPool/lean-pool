/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.MonomialOrthants
public import LeanPool.CCDN.ForMathlib.MvPolynomial
public import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Data.Sym.Card

/-! Counting the finite orthant partition gives an eventual polynomial
for every lower set of exponent vectors, in arbitrary finite dimension. -/

@[expose] public section
namespace CCDN
noncomputable section

open Classical in
/-- The bijection between exponent vectors in `σ → ℕ` of total degree at most `N` and multisets of
size `N` on `Option σ`. -/
def boundedExponentVectorEquivSym (σ : Type*) [Fintype σ] (N : ℕ) :
    {a : σ → ℕ // ∑ i, a i ≤ N} ≃ Sym (Option σ) N :=
  (Sym.equivNatSumLeOfFintype σ N).symm

instance finite_boundedExponentVectors {σ : Type*} [Fintype σ] (N : ℕ) :
    Finite {a : σ → ℕ // ∑ i, a i ≤ N} :=
  Finite.of_equiv (Sym (Option σ) N) (boundedExponentVectorEquivSym σ N).symm

open Classical in
private lemma card_boundedExponentVectors {σ : Type*} [Fintype σ] (N : ℕ) :
    Nat.card {a : σ → ℕ // ∑ i, a i ≤ N} =
      (Fintype.card σ + N).choose (Fintype.card σ) := by
  rw [Nat.card_congr (boundedExponentVectorEquivSym σ N), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose, Fintype.card_option]
  rw [show Fintype.card σ + 1 + N - 1 = Fintype.card σ + N by omega]
  exact Nat.choose_symm_add.symm

instance finite_boundedLowerExponents {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (N : ℕ) : Finite {a : σ → ℕ // a ∈ S ∧ ∑ i, a i ≤ N} :=
  Finite.of_injective (fun a => (⟨a.val, a.property.2⟩ :
    {a : σ → ℕ // ∑ i, a i ≤ N}))
    (fun _ _ h => Subtype.ext (congrArg
      (fun a : {a : σ → ℕ // ∑ i, a i ≤ N} => a.val) h))

private lemma orthantBaseDegree_le {σ : Type*} [Fintype σ] {B : ℕ}
    (b : σ → Fin (B + 1)) : orthantBaseDegree b ≤ Fintype.card σ * B := by
  calc
    _ ≤ ∑ _ : σ, B := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (b i).isLt)
    _ = _ := by simp

open Classical in
/-- Exact eventual counting formula for a lower set partitioned into its
translated orthants. -/
private theorem lowerSet_orthant_count {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (B : ℕ)
    (hstable : ∀ a, a ∈ S ↔ clampExponent B a ∈ S)
    (N : ℕ) (hN : Fintype.card σ * B ≤ N) :
    Nat.card {a : σ → ℕ // a ∈ S ∧ ∑ i, a i ≤ N} =
      ∑ b : σ → Fin (B + 1), if (fun i => (b i).val) ∈ S then
        (Fintype.card (orthantFree b) + (N - orthantBaseDegree b)).choose
          (Fintype.card (orthantFree b)) else 0 := by
  classical
  let A := {a : σ → ℕ // a ∈ S ∧ ∑ i, a i ≤ N}
  let f : A → (σ → Fin (B + 1)) := fun a => exponentPattern B a.val
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : (fun i => (b i).val) ∈ S
  · rw [ite_eq_left hb]
    let E : {a : A // f a = b} ≃
        {a : σ → ℕ // clampExponent B a = (fun i => (b i).val) ∧ ∑ i, a i ≤ N} :=
      { toFun := fun a => ⟨a.val.val, by
          constructor
          · funext i
            exact congrArg Fin.val (congrFun a.property i)
          · exact a.val.property.2⟩
        invFun := fun a => ⟨⟨a.val, by
          constructor
          · apply (hstable a.val).mpr
            rw [a.property.1]
            exact hb
          · exact a.property.2⟩, by
            funext i
            apply Fin.ext
            exact congrFun a.property.1 i⟩
        left_inv := fun a => by apply Subtype.ext; apply Subtype.ext; rfl
        right_inv := fun a => by apply Subtype.ext; rfl }
    rw [Nat.card_congr E,
      ← Nat.card_congr (boundedOrthantEquiv b ((orthantBaseDegree_le b).trans hN)),
      card_boundedExponentVectors]
  · rw [ite_eq_right hb]
    let : IsEmpty {a : A // f a = b} := ⟨fun a => by
      apply hb
      have hh := (hstable a.val.val).mp a.val.property.1
      have he : clampExponent B a.val.val = (fun i => (b i).val) := by
        funext i
        exact congrArg Fin.val (congrFun a.property i)
      rwa [he] at hh⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

/-- The orthant polynomial is a finite positive sum of shifted binomial
polynomials. Its coefficients are rational, while its large integer values
count exponent vectors exactly. -/
def lowerSetOrthantPolynomial {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (B : ℕ) : Polynomial ℚ := by
  classical
  exact ∑ b : σ → Fin (B + 1), if (fun i => (b i).val) ∈ S then
    Polynomial.preHilbertPoly ℚ (Fintype.card (orthantFree b)) (orthantBaseDegree b) else 0

/-- If membership in `S` is determined by clamping exponents at `B`, then for `N ≥ |σ| · B` the
orthant polynomial of `S` evaluated at `N` counts the vectors of `S` of total degree at most `N`. -/
lemma lowerSetOrthantPolynomial_eval {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (B : ℕ)
    (hstable : ∀ a, a ∈ S ↔ clampExponent B a ∈ S)
    (N : ℕ) (hN : Fintype.card σ * B ≤ N) :
    (lowerSetOrthantPolynomial S B).eval (N : ℚ) =
      (Nat.card {a : σ → ℕ // a ∈ S ∧ ∑ i, a i ≤ N} : ℚ) := by
  classical
  rw [lowerSet_orthant_count S B hstable N hN]
  simp only [lowerSetOrthantPolynomial, Polynomial.eval_finsetSum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with hb
  · rw [Polynomial.preHilbertPoly_eq_choose_add_sub]
    · congr 2
      have hbN := (orthantBaseDegree_le b).trans hN
      omega
    · exact ((orthantBaseDegree_le b).trans hN).trans (Nat.le_add_right _ _)
  · simp

/-- Every lower exponent set has an eventual counting polynomial.
The threshold and the polynomial are constructed from its finite orthant
partition. -/
theorem lowerSet_eventually_polynomial {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (hS : IsLowerSet S) :
    ∃ P : Polynomial ℚ, ∃ N : ℕ, ∀ n ≥ N,
      P.eval (n : ℚ) =
        (Nat.card {a : σ → ℕ // a ∈ S ∧ ∑ i, a i ≤ n} : ℚ) := by
  obtain ⟨B, _, hB⟩ := lowerSet_clamp_stabilizes S hS
  exact ⟨lowerSetOrthantPolynomial S B, Fintype.card σ * B,
    fun n hn => lowerSetOrthantPolynomial_eval S B hB n hn⟩

end
end CCDN
