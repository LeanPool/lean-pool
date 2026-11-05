/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Matrix minors in ideals
-/

@[expose] public section

namespace LatinQuarter

open scoped BigOperators Matrix

variable {R : Type*} [CommRing R]

/-- All minors of size `t` lie in `J`. Repeated indices are allowed;
their determinants are zero. -/
def AllMinorsIn {m n : Type*} (M : Matrix m n R) (t : ℕ) (J : Ideal R) : Prop :=
  ∀ (r : Fin t → m) (c : Fin t → n), (M.submatrix r c).det ∈ J

theorem allMinorsIn_mul_left {m n p : Type*} [Fintype n]
    (A : Matrix m n R) (B : Matrix n p R) {t : ℕ} {J : Ideal R}
    (hB : AllMinorsIn B t J) : AllMinorsIn (A * B) t J := by
  classical
  intro r c
  have heq : (A * B).submatrix r c =
      fun i => ∑ j, A (r i) j • (fun l => B j (c l)) := by
    ext i l
    simp [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  change Matrix.detRowAlternating.toMultilinearMap
    (fun i => ∑ j, A (r i) j • (fun l => B j (c l))) ∈ J
  rw [MultilinearMap.map_sum]
  apply Submodule.sum_mem
  intro f _
  rw [MultilinearMap.map_smul_univ]
  exact J.smul_mem _ (hB f c)

theorem allMinorsIn_transpose {m n : Type*} (M : Matrix m n R)
    {t : ℕ} {J : Ideal R} (hM : AllMinorsIn M t J) :
    AllMinorsIn M.transpose t J := by
  intro r c
  simpa only [← Matrix.transpose_submatrix, Matrix.det_transpose] using hM c r

theorem allMinorsIn_mul_right {m n p : Type*} [Fintype n]
    (A : Matrix m n R) (B : Matrix n p R) {t : ℕ} {J : Ideal R}
    (hA : AllMinorsIn A t J) : AllMinorsIn (A * B) t J := by
  have h := allMinorsIn_mul_left B.transpose A.transpose (allMinorsIn_transpose A hA)
  have h' := allMinorsIn_transpose (B.transpose * A.transpose) h
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h'

/-- A determinant with `s.card` rows in an ideal lies in that ideal power. -/
theorem det_mem_pow_of_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (J : Ideal R) (s : Finset ι)
    (h : ∀ i ∈ s, ∀ j, M i j ∈ J) : M.det ∈ J ^ s.card := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply Submodule.sum_mem
  intro σ _
  apply Ideal.mul_mem_left
  change (∏ i, M i (σ i)) ∈ J ^ s.card
  rw [← Finset.prod_mul_prod_compl s]
  apply Ideal.mul_mem_right
  have hp := Ideal.prod_mem_prod (I := fun _ : ι => J) (x := fun i => M i (σ i))
    (s := s) (fun i hi => h i hi (σ i))
  simpa using hp

/-- The lower block rows supply enough factors from the residual ideal. -/
theorem allMinorsIn_fromBlocks_diagonal {k h t : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (Z : Matrix (Fin h) (Fin h) R)
    (J : Ideal R) (hZ : ∀ i j, Z i j ∈ J) :
    AllMinorsIn (Matrix.fromBlocks A 0 0 Z) t (J ^ (t - k)) := by
  classical
  intro r c
  by_cases hr : Function.Injective r
  · let s : Finset (Fin t) := Finset.univ.filter (fun i => (r i).isRight)
    have htop : sᶜ.card ≤ k := by
      have hsub : sᶜ.image r ⊆
          Finset.univ.map (Function.Embedding.inl : Fin k ↪ Fin k ⊕ Fin h) := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        cases he : r i with
        | inl a => simp
        | inr b => simp [s, he] at hi
      have hc := Finset.card_le_card hsub
      simpa [Finset.card_image_of_injective _ hr] using hc
    have hs : t - k ≤ s.card := by
      have hc := Finset.card_add_card_compl s
      simp only [Fintype.card_fin] at hc
      omega
    apply Ideal.pow_le_pow_right hs
    apply det_mem_pow_of_rows _ J s
    intro i hi j
    have hir : (r i).isRight := (Finset.mem_filter.mp hi).2
    cases he : r i with
    | inl a => simp [he] at hir
    | inr b =>
      cases hc : c j with
      | inl a => simp [Matrix.submatrix, he, hc]
      | inr d => simpa [Matrix.submatrix, he, hc] using hZ b d
  · simp only [Function.Injective, not_forall] at hr
    obtain ⟨a, b, hab⟩ := hr
    have he : r a = r b := by tauto
    have hn : a ≠ b := by tauto
    rw [Matrix.det_zero_of_row_eq hn (by ext j; simp [Matrix.submatrix, he])]
    exact Ideal.zero_mem _

end LatinQuarter
