/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm, Yi Lee, Xiaodi Wu, Runzhou Tao
-/
module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto

/-!
# Binary matrix row spaces and logical-operator distance

Ported to Lean Pool from QCL-SUAT/Lean-QEC at
`a0855f8a6374c1dda2097bbf07f33ba53760fdcd`. Declarations are placed in
`QECCertificates`, with three uniquely named extensions of `Matrix`; imports and
module syntax are updated. The span-generator equivalence has its quantifiers corrected.

Lean-QEC, Copyright 2026 The Lean-QEC Authors (Mattias Ehatamm, Yi Lee, Xiaodi Wu,
Runzhou Tao). This product includes software developed as part of the paper
"End-to-End Formalization of Quantum Error Correction" (arXiv:2605.16523).
Licensed under the Apache License, Version 2.0.
-/

@[expose] public section

namespace QECCertificates

noncomputable instance submoduleSetFintype
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : Fintype ↑(C : Set (Fin n → ZMod 2)) := by
  classical
  infer_instance

lemma zmod2_val_eq_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a.1 = 1 := by
  have hlt : a.1 < 2 := a.2
  have hne : a.1 ≠ 0 := fun h => ha ((ZMod.val_eq_zero a).mp h)
  omega

lemma zmod2_val_eq_zero_of_ne_one (a : ZMod 2) (ha : a ≠ 1) : a.1 = 0 := by
  fin_cases a
  · rfl
  contradiction

/-- The submodule spanned by the rows of a matrix. -/
def _root_.Matrix.certificateRowSpace {α β γ : Type*} [Semiring γ] (M : Matrix α β γ) :=
    (Submodule.span γ (Set.range M))

lemma Matrix.row_mem_rowSpace {α β γ : Type*} {i : α} [Semiring γ] {M : Matrix α β γ} :
  M i ∈ M.certificateRowSpace := by
  apply Submodule.mem_span_of_mem (Set.mem_range_self _)

lemma Submodule.mem_span_range_iff_sum {α : Type*} {n : ℕ} (x : Fin n → (ZMod 2)) (v : α → Fin n →
    (ZMod 2))
  : x ∈ Submodule.span (ZMod 2) (Set.range v) ↔ ∃ S : Finset α, ∑ s ∈ S, v s = x := by
  refine ⟨fun hx => ?_, ?_⟩
  · rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hx
    obtain ⟨ c, rfl ⟩ := hx
    use c.support.filter (fun s => c s = 1)
    rw [ Finset.sum_filter ]; congr ; ext x i
    rcases Fin.exists_fin_two.mp ⟨ c x, rfl ⟩ with h | h
    · have h01 : ¬ ((0 : ZMod 2) = 1) := by norm_num
      rw [ h ]
      change (if (0 : ZMod 2) = 1 then v x i else 0) = (0 : ZMod 2) * v x i
      simp [ h01 ]
    · rw [ h ]
      change (if (1 : ZMod 2) = 1 then v x i else 0) = (1 : ZMod 2) * v x i
      simp
  · exact fun ⟨ S, hS ⟩ => hS ▸ Submodule.sum_mem _ fun i _ => Submodule.subset_span (
    Set.mem_range_self _ )

-- rowspace already contains the zero vector
-- no need to remove it again
/-- Minimum Hamming weight in the first kernel outside the second row space, or n + 1 if empty. -/
noncomputable def minWeightKernelOutsideRowSpace {n k₁ k₂ : ℕ}
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) : ℕ :=
  let undetectable_errors : Set (Fin n → ZMod 2) :=
    (LinearMap.ker M₁.toLin' \ M₂.certificateRowSpace)
  match Finset.min (Finset.image hammingNorm undetectable_errors.toFinset) with
  | ⊤ => n + 1
  | some a => a

lemma min_weight_ker_not_mem_rowspace_pos {n k₁ k₂ : ℕ}
  {M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)} :
  0 < minWeightKernelOutsideRowSpace M₁ M₂ := by
  unfold minWeightKernelOutsideRowSpace
  extract_lets undetectable_errors
  rcases h: (Finset.image hammingNorm undetectable_errors.toFinset).min with _ | m'
  · simp
  simp only
  apply Finset.mem_of_min at h
  simp only [Finset.mem_image] at h
  rcases h with ⟨nontrivial_error, h, rfl⟩
  by_contra
  apply Nat.eq_zero_of_not_pos at this
  rw [hammingNorm_eq_zero] at this
  subst this undetectable_errors
  simp at h

lemma mem_ker_iff_dotProd_rows_eq_zero {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin n
    → (ZMod 2)) :
  x ∈ ((LinearMap.ker M.toLin')) ↔ ∀ i, (M i) ⬝ᵥ x = 0 := by
  constructor
  · intro h i
    simpa [Matrix.mulVec, dotProduct] using congr_fun h i
  · intro h
    ext i
    simpa [Matrix.mulVec, dotProduct] using h i

/-
Helper: backward direction - if y is in ker and y ⬝ x = 1, then x is not in certificateRowSpace
-/
lemma ker_dotProduct_rowSpace_eq_zero {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2))
    (y : Fin n → ZMod 2) (x : Fin n → ZMod 2)
    (hy : y ∈ LinearMap.ker M.toLin') (hx : x ∈ M.certificateRowSpace) : y ⬝ᵥ x = 0 := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      rw [dotProduct_comm]
      exact (mem_ker_iff_dotProd_rows_eq_zero M y).mp hy i
  | zero => simp
  | add a b ha hb iha ihb => rw [dotProduct_add, iha, ihb, add_zero]
  | smul c a ha iha => rw [dotProduct_smul, iha, smul_zero]

lemma dual_eq_dotProduct {n : ℕ} (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
    f v = (fun i => f (Pi.single i 1)) ⬝ᵥ v := by
  convert f.pi_apply_eq_sum_univ v using 1
  simp only [dotProduct, smul_eq_mul, mul_comm]
  exact Finset.sum_congr rfl fun i _ => by congr; ext j; aesop
/-
Helper: if x ∉ certificateRowSpace, we can construct a y in ker with y ⬝ x = 1
-/
lemma exists_ker_dotProduct_eq_one_of_not_mem_rowSpace {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod
    2))
    (x : Fin n → ZMod 2) (hx : x ∉ M.certificateRowSpace) :
    ∃ y ∈ LinearMap.ker M.toLin', y ⬝ᵥ x = 1 := by
  classical
  unfold Matrix.certificateRowSpace at hx
  let : Module.Free (ZMod 2) ((Fin n → ZMod 2) ⧸ Submodule.span (ZMod 2) (Set.range M)) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace (ZMod 2) _)
  obtain ⟨f, hfx, hf_bot⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (R := ZMod 2) (M := Fin n → ZMod 2) hx inferInstance
  refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
  · rw [mem_ker_iff_dotProd_rows_eq_zero]
    intro i
    rw [dotProduct_comm]
    rw [← dual_eq_dotProduct]
    have : f (M i) ∈ Submodule.map f (Submodule.span (ZMod 2) (Set.range M)) :=
      Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self i))
    rw [hf_bot] at this
    exact (Submodule.mem_bot _).mp this
  · -- Since $f x \neq 0$, we have $f x = 1$.
    have hfx_one : f x = 1 := by
      rcases Fin.exists_fin_two.mp ⟨ f x, rfl ⟩ with h | h
      · exact absurd h hfx
      · exact h
    convert hfx_one using 1
    convert dual_eq_dotProduct f x |> Eq.symm

lemma not_mem_rowspace_iff_exists_mem_ker {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin
    n → (ZMod 2)) :
  x ∉ M.certificateRowSpace ↔ ∃ y ∈ (LinearMap.ker M.toLin'), y ⬝ᵥ x = 1 := by
  constructor
  · exact exists_ker_dotProduct_eq_one_of_not_mem_rowSpace M x
  · rintro ⟨y, hy_ker, hy_dot⟩ hx
    have := ker_dotProduct_rowSpace_eq_zero M y x hy_ker hx
    simp_all

/-- A binary vector pairs nontrivially with the span exactly when it does with a generator. -/
lemma ex_mem_submodule_non_orth_iff_non_orth_mem_basis {n : ℕ}
    (S : Set (Fin n → ZMod 2)) (x : Fin n → ZMod 2) :
    (∃ y ∈ Submodule.span (ZMod 2) S, y ⬝ᵥ x = 1) ↔ ∃ s ∈ S, s ⬝ᵥ x = 1 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    by_contra h
    have hzero : ∀ s ∈ S, s ⬝ᵥ x = 0 := by
      intro s hs
      rcases Fin.exists_fin_two.mp ⟨s ⬝ᵥ x, rfl⟩ with hz | ho
      · exact hz
      · exact False.elim (h ⟨s, hs, ho⟩)
    have hspan : ∀ z ∈ Submodule.span (ZMod 2) S, z ⬝ᵥ x = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact hzero z hz
      | zero => simp
      | add a b ha hb iha ihb => rw [add_dotProduct, iha, ihb, add_zero]
      | smul c a ha iha => rw [smul_dotProduct, iha, smul_zero]
    exact one_ne_zero (hyx.symm.trans (hspan y hy))
  · rintro ⟨s, hs, hsx⟩
    exact ⟨s, Submodule.subset_span hs, hsx⟩

lemma weight_le_disj {n k : ℕ} {z : Fin n → (ZMod 2)} : hammingNorm z ≤ k ↔ ∑ i, (z i).1 ≤ k := by
  simp +decide only [hammingNorm]
  rw [ Finset.card_filter ]
  exact iff_of_eq ( by congr; ext i; rcases z i with ( _ | _ | i ) <;> trivial )

lemma sum_id_dotProduct_eq {n : ℕ} (S : Finset (Fin n → ZMod 2)) (x : Fin n → ZMod 2) :
  S.sum id ⬝ᵥ x = S.sum (fun s => s ⬝ᵥ x) := by
  induction S using Finset.induction_on with
  | empty => simp [dotProduct]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, id, add_dotProduct, ih]

lemma exists_dotProduct_one_of_sum
  {n : ℕ} {S : Finset (Fin n → ZMod 2)} {y x : Fin n → ZMod 2}
  (hS_sum : S.sum id = y) (hy : y ⬝ᵥ x = 1) :
  ∃ s ∈ S, s ⬝ᵥ x = 1 := by
  by_contra h_all
  push Not at h_all
  have h_zero : ∀ s ∈ S, s ⬝ᵥ x = 0 := by
    intro s hs
    rcases Fin.exists_fin_two.mp ⟨s ⬝ᵥ x, rfl⟩ with h | h
    · exact h
    · exact absurd h (h_all s hs)
  have : S.sum id ⬝ᵥ x = 0 := by
    rw [sum_id_dotProduct_eq]
    exact Finset.sum_eq_zero (fun s hs => h_zero s hs)
  rw [hS_sum] at this
  exact absurd this (by rw [hy]; decide)

lemma Matrix.mem_rowSpace_ZMod2 {n₁ n₂ : ℕ}
  {M : Matrix (Fin n₁) (Fin n₂) (ZMod 2)}
  {x : Fin n₂ → (ZMod 2)} :
  x ∈ M.certificateRowSpace ↔
  ∃ (S : Finset ((Fin n₂) → (ZMod 2))),
    S ⊆ (Finset.image M Finset.univ) ∧ S.sum id = x := by
  constructor
  · intro hx
    have h_sum : ∀ (y : Fin n₂ → ZMod 2),
        y ∈ Submodule.span (ZMod 2) (Set.range M) →
        ∃ S : Finset (Fin n₂ → ZMod 2), S ⊆ Finset.image M Finset.univ ∧ S.sum id = y := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨ i, rfl ⟩ := hz
          refine ⟨ { M i }, ?_, ?_ ⟩
          · intro w hw
            rw [Finset.mem_singleton] at hw
            subst hw
            exact Finset.mem_image.mpr ⟨ i, Finset.mem_univ i, rfl ⟩
          · simp
      | zero => exact ⟨ ∅, by simp, by simp ⟩
      | add a b ha hb iha ihb =>
          obtain ⟨ S₁, hS₁, hS₁' ⟩ := iha
          obtain ⟨ S₂, hS₂, hS₂' ⟩ := ihb
          have hd : Disjoint (S₁ \ S₂) (S₂ \ S₁) := by
            apply Finset.disjoint_left.mpr
            intro z hz₁ hz₂
            rw [Finset.mem_sdiff] at hz₁ hz₂
            exact hz₂.2 hz₁.1
          have hsub : S₁ \ S₂ ∪ S₂ \ S₁ ⊆ Finset.image M Finset.univ := by
            intro z hz
            rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hz
            rcases hz with ⟨ h1, _ ⟩ | ⟨ h2, _ ⟩
            · exact hS₁ h1
            · exact hS₂ h2
          have h1 : (S₁ \ S₂).sum id + (S₁ ∩ S₂).sum id = a := by
            have hset : S₁ \ (S₁ ∩ S₂) = S₁ \ S₂ := by
              ext z; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
            rw [← hset, Finset.sum_sdiff (Finset.inter_subset_left : S₁ ∩ S₂ ⊆ S₁)]
            exact hS₁'
          have h2 : (S₂ \ S₁).sum id + (S₁ ∩ S₂).sum id = b := by
            have hset : S₂ \ (S₁ ∩ S₂) = S₂ \ S₁ := by
              ext z; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
            rw [← hset, Finset.sum_sdiff (Finset.inter_subset_right : S₁ ∩ S₂ ⊆ S₂)]
            exact hS₂'
          refine ⟨ S₁ \ S₂ ∪ S₂ \ S₁, hsub, ?_ ⟩
          rw [Finset.sum_union hd]
          have hzz : (S₁ ∩ S₂).sum id + (S₁ ∩ S₂).sum id = 0 := by
            funext i
            simp only [Pi.add_apply, Pi.zero_apply]
            rw [← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]
          calc (S₁ \ S₂).sum id + (S₂ \ S₁).sum id
              = ((S₁ \ S₂).sum id + (S₂ \ S₁).sum id) +
                ((S₁ ∩ S₂).sum id + (S₁ ∩ S₂).sum id) := by rw [hzz, add_zero]
            _ = ((S₁ \ S₂).sum id + (S₁ ∩ S₂).sum id) +
                ((S₂ \ S₁).sum id + (S₁ ∩ S₂).sum id) := by abel
            _ = a + b := by rw [h1, h2]
      | smul c a ha iha =>
          obtain ⟨ S, hS, hS' ⟩ := iha
          rcases Fin.exists_fin_two.mp ⟨ c, rfl ⟩ with h | h
          · rw [h]
            refine ⟨ ∅, ?_, ?_ ⟩
            · intro z hz; simp at hz
            · ext i
              change (0 : ZMod 2) = (0 : ZMod 2) * a i
              ring
          · rw [h]
            refine ⟨ S, hS, ?_ ⟩
            rw [hS']
            ext i
            change a i = (1 : ZMod 2) * a i
            ring
    exact h_sum x hx
  · rintro ⟨ S, hS₁, hS₂ ⟩
    rw [← hS₂]
    exact Submodule.sum_mem _ fun s hs =>
      Submodule.subset_span <| Set.mem_range.mpr <| by
        obtain ⟨ i, -, hi ⟩ := Finset.mem_image.mp (hS₁ hs)
        exact ⟨ i, hi ⟩

lemma exists_row_of_exists_mem_rowspace_non_orth {n k : ℕ}
  {M : Matrix (Fin k) (Fin n) (ZMod 2)}
  {x y : Fin n → (ZMod 2)}
  (hy₁ : y ∈ M.certificateRowSpace)
  (hy₂ : y ⬝ᵥ x = 1) :
  ∃ r, (M r) ⬝ᵥ x = 1 := by
  rw [Matrix.mem_rowSpace_ZMod2] at hy₁
  obtain ⟨S, hS_sub, hS_sum⟩ := hy₁
  obtain ⟨s, hs_mem, hs_dot⟩ := exists_dotProduct_one_of_sum hS_sum hy₂
  obtain ⟨ i, -, hi ⟩ := Finset.mem_image.mp (hS_sub hs_mem)
  refine ⟨ i, ?_ ⟩
  rwa [hi]

/-- Every row of the first matrix is orthogonal to every row of the second. -/
def _root_.Matrix.certificateMutuallyOrthogonalRows {α β γ δ : Type*} [Fintype γ] [Mul δ]
    [AddCommMonoid δ]
  (M₁ : Matrix α γ δ) (M₂ : Matrix β γ δ) : Prop := ∀ a b, M₁ a ⬝ᵥ M₂ b = 0

/-- The first matrix row space equals the kernel of the second matrix. -/
def _root_.Matrix.certificateIsKernelFor {k₁ k₂ n : ℕ} (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)) (M₂
    : Matrix (Fin k₂) (Fin n) (ZMod 2))
  : Prop := M₁.certificateRowSpace = LinearMap.ker M₂.toLin'

lemma Matrix.is_ker_for_of_rank_sum_mutually_orth
  {k₁ k₂ r₁ r₂ n : ℕ}
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (hr₁ : r₁ ≤ M₁.rank)
  (hr₂ : r₂ ≤ M₂.rank)
  (hrn : r₁ + r₂ = n)
  (ho : M₁.certificateMutuallyOrthogonalRows M₂) :
  M₂.certificateIsKernelFor M₁ := by
    classical
    have h_dim_ker : Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' M₁)) = n - Matrix.rank
      M₁ := by
      have := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) (Matrix.mulVecLin M₁)
      exact eq_tsub_of_add_eq ( by norm_num at *; linarith! )
    have h_finrank_M₂ : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range M₂)) =
      Matrix.rank M₂ := by
      rw [Matrix.rank_eq_finrank_span_row M₂]
      congr 1
    have h_subspace : Submodule.span (ZMod 2) (Set.range M₂) ≤ LinearMap.ker (Matrix.toLin' M₁) :=
      by
      rw [ Submodule.span_le ]
      rintro _ ⟨i, rfl⟩
      change Matrix.mulVec M₁ (M₂ i) = 0
      exact funext fun j => by simpa [ Matrix.mulVec, dotProduct ] using ho j i
    have h_eq : Submodule.span (ZMod 2) (Set.range M₂) = LinearMap.ker (Matrix.toLin' M₁) := by
      exact Submodule.eq_of_le_of_finrank_le (K := ZMod 2) h_subspace ( by omega )
    exact h_eq

lemma Matrix.rank_le_of_submatrix_independent
  {k r n : ℕ}
  (M : Matrix (Fin r) (Fin n) (ZMod 2))
  (inds : Fin k → Fin r)
  (_inds_mono : StrictMono inds)
  (h_ind : LinearIndependent (ZMod 2) (M.submatrix inds id)) :
  k ≤ M.rank := by
    have hrow : LinearIndependent (ZMod 2) ((M.submatrix inds id).row) := by
      simpa only [Matrix.row] using h_ind
    have h_submatrix_rank : (M.submatrix inds id).rank = k := by
      simpa using LinearIndependent.rank_matrix hrow
    calc k = (M.submatrix inds id).rank := h_submatrix_rank.symm
      _ ≤ M.rank := Matrix.rank_submatrix_le M inds id

end QECCertificates
