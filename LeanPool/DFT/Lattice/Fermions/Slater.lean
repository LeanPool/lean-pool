/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Fermions.Configurations

/-!
# Slater determinants in first quantisation

`slater_eigen`: for orbitals with `h φ_j = ε_j φ_j`, the Slater amplitude `Ψ(τ) = det[φ_j(τ_k)]`
satisfies `Σ_k Σ_b h(τ_k, b) Ψ(τ with τ_k := b) = (Σ_j ε_j) Ψ(τ)`; signs and Pauli exclusion come
from the determinant.
-/

@[expose] public section

namespace DFT

section

open Matrix

variable {M N : ℕ}

/-- Slater amplitude of a position tuple. -/
def slater (φ : Fin N → Fin M → ℝ) (τ : Fin N → Fin M) : ℝ :=
  (Matrix.of fun k j => φ j (τ k)).det

lemma slater_eq_sum (φ : Fin N → Fin M → ℝ) (τ : Fin N → Fin M) :
    slater φ τ = ∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : ℝ) * ∏ j, φ j (τ (σ j)) := by
  simp [slater, Matrix.det_apply, Units.smul_def]

/-- One term of the Leibniz expansion, summed against `h` in the slot occupied by orbital `σ⁻¹ i`.
-/
lemma sum_update_prod (h : Matrix (Fin M) (Fin M) ℝ) (φ : Fin N → Fin M → ℝ) (ε : Fin N → ℝ)
    (hφ : ∀ j, h *ᵥ φ j = ε j • φ j) (τ : Fin N → Fin M) (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    ∑ b, h (τ i) b * ∏ j, φ j (Function.update τ i b (σ j)) =
      ε (σ.symm i) * ∏ j, φ j (τ (σ j)) := by
  set j0 := σ.symm i
  have hsplit : ∀ b, ∏ j, φ j (Function.update τ i b (σ j)) =
      φ j0 b * ∏ j ∈ Finset.univ.erase j0, φ j (τ (σ j)) := by
    intro b
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j0)]
    congr 1
    · simp [j0]
    · apply Finset.prod_congr rfl
      intro j hj
      have hne : σ j ≠ i := by
        intro h'; apply (Finset.mem_erase.mp hj).1; simp [j0, ← h']
      simp [Function.update_of_ne hne]
  have hall : ∏ j, φ j (τ (σ j)) = φ j0 (τ i) * ∏ j ∈ Finset.univ.erase j0, φ j (τ (σ j)) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j0)]
    simp [j0]
  simp_rw [hsplit]
  have hev : ∑ b, h (τ i) b * φ j0 b = ε j0 * φ j0 (τ i) := by
    have := congrFun (hφ j0) (τ i)
    simpa [Matrix.mulVec, dotProduct] using this
  calc ∑ b, h (τ i) b * (φ j0 b * ∏ j ∈ Finset.univ.erase j0, φ j (τ (σ j)))
      = (∑ b, h (τ i) b * φ j0 b) * ∏ j ∈ Finset.univ.erase j0, φ j (τ (σ j)) := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring
    _ = ε j0 * ∏ j, φ j (τ (σ j)) := by rw [hev, hall]; ring

/-- **Slater lemma (first quantisation).** -/
theorem slater_eigen (h : Matrix (Fin M) (Fin M) ℝ) (φ : Fin N → Fin M → ℝ) (ε : Fin N → ℝ)
    (hφ : ∀ j, h *ᵥ φ j = ε j • φ j) (τ : Fin N → Fin M) :
    ∑ i, ∑ b, h (τ i) b * slater φ (Function.update τ i b) = (∑ j, ε j) * slater φ τ := by
  simp_rw [slater_eq_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  have key : ∀ i, ∑ b, h (τ i) b *
      ((Equiv.Perm.sign σ : ℝ) * ∏ j, φ j (Function.update τ i b (σ j))) =
      (Equiv.Perm.sign σ : ℝ) * (ε (σ.symm i) * ∏ j, φ j (τ (σ j))) := by
    intro i
    rw [← sum_update_prod h φ ε hφ τ σ i, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _; ring
  simp_rw [key]
  have : ∑ i, ε (σ.symm i) = ∑ j, ε j := Equiv.sum_comp σ.symm ε
  rw [← this, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _; ring

end

end DFT
