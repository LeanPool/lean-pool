/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.BooleanMatrixPolynomial
public import LeanPool.NoncommutativeAMGM.Extraction

/-! # Ordered matrix words and their square-free Boolean supports -/

@[expose] public section
open scoped BigOperators
namespace NoncommutativeAMGM
theorem sum_pow_ordered {R ι : Type*} [Semiring R] [Fintype ι] (A : ι → R) (m : ℕ) :
    (∑ i, A i) ^ m = ∑ f : Fin m → ι, (List.ofFn fun j ↦ A (f j)).prod := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    have he : (∑ f : Fin (m + 1) → ι, (List.ofFn fun j ↦ A (f j)).prod) =
        ∑ i : ι, ∑ f : Fin m → ι,
          (List.ofFn fun j ↦ A (Fin.cons (α := fun _ : Fin (m + 1) ↦ ι) i f j)).prod := by
      rw [← (Fin.consEquiv (fun _ : Fin (m + 1) ↦ ι)).sum_comp,
        Fintype.sum_prod_type]
      rfl
    rw [he, pow_succ', ih, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    simp [List.ofFn_succ]
theorem sum_injective_words {R : Type*} [AddCommMonoid R] (n m : ℕ)
    (w : (Fin m → Fin n) → R) :
    (∑ f : Fin m → Fin n, if Function.Injective f then w f else 0) =
      ∑ f : Fin m ↪ Fin n, w f := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := Function.Injective)
    ((Finset.univ : Finset (Fin m → Fin n)).filter Function.Injective)
    (by intro f; simp)]
  exact Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin m) (Fin n))
    _ _ (fun _ ↦ rfl)

/-- The distinct variables appearing in an ordered index tuple. -/
noncomputable def tupleSupport {n m : ℕ} (f : Fin m → Fin n) : Finset (Fin n) := Finset.univ.image f

theorem tupleSupport_card_le {n m : ℕ} (f : Fin m → Fin n) : (tupleSupport f).card ≤ m := by
  simpa [tupleSupport] using Finset.card_image_le (s := Finset.univ) (f := f)

theorem tupleSupport_card_eq_iff {n m : ℕ} (f : Fin m → Fin n) :
    (tupleSupport f).card = m ↔ Function.Injective f := by
  classical
  constructor
  · intro he
    have hc : (Finset.univ.image f).card = (Finset.univ : Finset (Fin m)).card := by
      simpa [tupleSupport] using he
    simpa using (Finset.card_image_iff.mp hc)
  · intro hf
    have hc := (Finset.card_image_iff (s := (Finset.univ : Finset (Fin m)))
      (f := f)).mpr (fun a _ b _ he ↦ hf he)
    simpa [tupleSupport] using hc

theorem tupleSupport_succ {n m : ℕ} (f : Fin (m + 1) → Fin n) :
    tupleSupport f = insert (f 0) (tupleSupport (fun j ↦ f j.succ)) := by
  classical
  ext i
  simp [tupleSupport, Fin.exists_fin_succ, eq_comm]

theorem booleanLinearMatrix_eq_sum {n : ℕ} {ι : Type*} (E : Fin n → Matrix ι ι ℝ) :
    booleanLinearMatrix E = ∑ a, booleanVar a • constantBooleanMatrix n (E a) := by
  apply Matrix.ext
  intro i j
  simp only [booleanLinearMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    constantBooleanMatrix, Matrix.map_apply]

/-- Each matrix word reduces to the monomial on its exact set of variable indices. -/
theorem boolean_matrix_word {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Fin n → Matrix ι ι ℝ) (m : ℕ) (f : Fin m → Fin n) :
    (List.ofFn fun j ↦ booleanVar (f j) • constantBooleanMatrix n (E (f j))).prod =
      booleanMonomial (tupleSupport f) 1 •
        constantBooleanMatrix n ((List.ofFn fun j ↦ E (f j)).prod) := by
  classical
  induction m with
  | zero => simp [tupleSupport, booleanMonomial_empty, constantBooleanMatrix_one]
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih (fun j ↦ f j.succ), Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← constantBooleanMatrix_mul]
    simp only [booleanVar, booleanMonomial_mul, one_mul, Finset.singleton_union,
      tupleSupport_succ]

/-- Exact expansion of the Boolean matrix power, retaining all repeated-index words. -/
theorem booleanLinearMatrix_pow {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Fin n → Matrix ι ι ℝ) (m : ℕ) :
    booleanLinearMatrix E ^ m = ∑ f : Fin m → Fin n,
      booleanMonomial (tupleSupport f) 1 •
        constantBooleanMatrix n ((List.ofFn fun j ↦ E (f j)).prod) := by
  rw [booleanLinearMatrix_eq_sum, sum_pow_ordered]
  apply Finset.sum_congr rfl
  intro f _
  exact boolean_matrix_word E m f

theorem booleanMonomial_mul_constant {n : ℕ} (S : Finset (Fin n)) (a : ℝ) :
    booleanMonomial S 1 * algebraMap ℝ (BooleanPolynomial n) a = booleanMonomial S a := by
  change booleanMonomial S 1 * booleanMonomial ∅ a = booleanMonomial S a
  rw [booleanMonomial_mul]
  simp

/-- The degree-`m` Boolean coefficient sum of `Bᵐ` consists exactly of injective ordered words. -/
theorem booleanLinearMatrix_pow_top {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Fin n → Matrix ι ι ℝ) (m : ℕ) :
    booleanMatrixImage (layerCoefficientSum n m) (booleanLinearMatrix E ^ m) =
      distinctProductSum n m E := by
  classical
  apply Matrix.ext
  intro i j
  change layerCoefficientSum n m ((booleanLinearMatrix E ^ m) i j) = _
  rw [booleanLinearMatrix_pow, Matrix.sum_apply, map_sum]
  simp only [Matrix.smul_apply, smul_eq_mul, constantBooleanMatrix, Matrix.map_apply,
    booleanMonomial_mul_constant, layerCoefficientSum_monomial]
  simp_rw [tupleSupport_card_eq_iff]
  rw [sum_injective_words]
  exact (Matrix.sum_apply i j Finset.univ
    (fun f : Fin m ↪ Fin n ↦ (List.ofFn fun k ↦ E (f k)).prod)).symm

theorem layerCoefficientSum_eq_zero {n r d : ℕ} (f : BooleanPolynomial n)
    (hf : BooleanDegreeLE f d) (hdr : d < r) : layerCoefficientSum n r f = 0 := by
  classical
  have he : f = ∑ S ∈ f.coeff.support, booleanMonomial S.toFinset (f.coeff S) :=
    (MonoidAlgebra.sum_coeff_single f).symm
  rw [he, map_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [layerCoefficientSum_monomial]
  have hdegree := hf S (Finsupp.mem_support_iff.mp hS)
  change S.toFinset.card ≤ d at hdegree
  exact ite_eq_right (ne_of_lt (hdegree.trans_lt hdr))

end NoncommutativeAMGM
