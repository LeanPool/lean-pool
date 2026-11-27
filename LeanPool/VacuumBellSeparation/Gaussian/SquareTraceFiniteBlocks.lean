/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteBasisCompression
public import LeanPool.VacuumBellSeparation.Gaussian.HilbertSchmidtMatrixExtension

/-!
# The full actual square trace is controlled by finite square blocks

Parseval and nonnegative Tonelli identify the square trace of a bounded
selfadjoint operator with the full squared matrix-coefficient sum. Every
finite set of index pairs is contained in a square block. Consequently
uniform bounds for the genuine finite compression square traces control
the full extended square trace, with no countability or prior finiteness.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Matrix
open scoped ENNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem ennreal_double_tsum_le_of_square_blocks (a : ι → ι → ℝ≥0∞) {C : ℝ≥0∞}
    (h : ∀ s : Finset ι, ∑ i ∈ s, ∑ j ∈ s, a i j ≤ C) :
    ∑' i, ∑' j, a i j ≤ C := by
  classical
  rw [← tsum_prod]
  apply CompleteLattice.summable.tsum_le_of_sum_le
  intro t
  let s := t.image Prod.fst ∪ t.image Prod.snd
  have ht : t ⊆ s ×ˢ s := by
    intro x hx
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩),
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
  calc
    ∑ x ∈ t, a x.1 x.2 ≤ ∑ x ∈ s ×ˢ s, a x.1 x.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg ht (fun _ _ _ => zero_le)
    _ = ∑ i ∈ s, ∑ j ∈ s, a i j := Finset.sum_product' _ _ _
    _ ≤ C := h s

omit [CompleteSpace E] in
theorem basisHilbertSchmidtSquare_eq_matrix (b : HilbertBasis ι ℂ E)
    (A : E →L[ℂ] E) :
    basisHilbertSchmidtSquare b A =
      matrixHilbertSchmidtSquare (fun i j => inner ℂ (b i) (A (b j))) := by
  unfold basisHilbertSchmidtSquare matrixHilbertSchmidtSquare
  calc
    (∑' j, ENNReal.ofReal (‖A (b j)‖ ^ 2)) =
        ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (b i) (A (b j))‖ ^ 2) :=
      tsum_congr fun j => (tsum_basis_inner_norm_sq b (A (b j))).symm
    _ = _ := tsum_comm

theorem positiveTrace_square_eq_matrix (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    positiveTrace (A * A) =
      matrixHilbertSchmidtSquare (fun i j => inner ℂ (b i) (A (b j))) := by
  have he : A.adjoint.comp A = A * A := by
    change star A * A = A * A
    rw [hA.star_eq]
  rw [← he, positiveTrace_adjoint_comp b, basisHilbertSchmidtSquare_eq_matrix]

section Finite
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem finitePositivePowerTrace_two_eq_matrix {A : Matrix κ κ ℂ}
    (hA : A.PosSemidef) :
    finitePositivePowerTrace A 2 = matrixHilbertSchmidtSquare A := by
  let b := (EuclideanSpace.basisFun κ ℂ).toHilbertBasis
  have hT : 0 ≤ (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)) A :=
    map_nonneg (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)) hA.nonneg
  have hpow : ((Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)) A) ^ (2 : ℝ) =
      ((Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)) A) ^ (2 : ℕ) := by
    simpa only [Nat.cast_ofNat] using
      (CFC.rpow_natCast ((Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)) A) 2 hT)
  rw [← positiveTrace_toEuclideanCLM_rpow hA 2,
    hpow, pow_two, positiveTrace_square_eq_matrix b hT.isSelfAdjoint]
  congr 1
  funext i j
  simpa only [b, OrthonormalBasis.coe_toHilbertBasis] using euclidean_coordinate_inner_matrix A i j

theorem finiteBasisCompression_square_trace (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (hf : Function.Injective f) {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    finitePositivePowerTrace (finiteBasisCompression b f hf A) 2 =
      ∑ i, ∑ j, ENNReal.ofReal (‖inner ℂ (b (f i)) (A (b (f j)))‖ ^ 2) := by
  rw [finitePositivePowerTrace_two_eq_matrix (finiteBasisCompression_posSemidef b f hf hA)]
  simp only [matrixHilbertSchmidtSquare, tsum_fintype, finiteBasisCompression_entry]

end Finite

/-- Uniform square-trace bounds on actual finite coordinate compressions
imply the full extended square-trace bound for the given bounded operator. -/
theorem positiveTrace_square_le_of_finite_compressions [DecidableEq ι]
    (b : HilbertBasis ι ℂ E) {A : E →L[ℂ] E} (hA : 0 ≤ A) {C : ℝ≥0∞}
    (h : ∀ s : Finset ι,
      finitePositivePowerTrace (finiteBasisCompression b (fun i : s => (i : ι))
        Subtype.val_injective A) 2 ≤ C) :
    positiveTrace (A ^ (2 : ℝ)) ≤ C := by
  have hpow : A ^ (2 : ℝ) = A ^ (2 : ℕ) := by
    simpa only [Nat.cast_ofNat] using (CFC.rpow_natCast A 2 hA)
  rw [hpow, pow_two, positiveTrace_square_eq_matrix b hA.isSelfAdjoint]
  apply ennreal_double_tsum_le_of_square_blocks
  intro s
  have hs := h s
  rw [finiteBasisCompression_square_trace b _ _ hA] at hs
  let q : ι → ι → ℝ≥0∞ := fun i j =>
    ENNReal.ofReal (‖inner ℂ (b i) (A (b j))‖ ^ 2)
  change (∑ i : s, ∑ j : s, q i j) ≤ C at hs
  change (∑ i ∈ s, ∑ j ∈ s, q i j) ≤ C
  calc
    (∑ i ∈ s, ∑ j ∈ s, q i j) = ∑ i : s, ∑ j ∈ s, q i j :=
      Finset.sum_subtype s (fun _ => Iff.rfl) (fun i => ∑ j ∈ s, q i j)
    _ = ∑ i : s, ∑ j : s, q i j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_subtype s (fun _ => Iff.rfl) (q i)
    _ ≤ C := hs

end VacuumBellSeparation.Gaussian
