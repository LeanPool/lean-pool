/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Fermions.SecondQuantization

/-!
# Cauchy–Binet for Slater determinants

* `gram φ ψ`: the overlap matrix `G_{ij} = Σ_x φ_i(x) ψ_j(x)` of two families of `N` orbitals.
* `det_gram`: `det G = Σ_τ Ψ_φ(τ) Π_j ψ_j(τ_j)` (sum over all position tuples).
* `cauchy_binet`: `Σ_s Ψ_φ(s) Ψ_ψ(s) = det G` (sum over configurations).
* `slater_orthonormal`: Slater determinants of orthonormal orbitals, indexed by orbital subsets, are
  orthonormal.
-/

@[expose] public section

namespace DFT

open Matrix

variable {M N : ℕ}

/-- Overlap matrix of two families of orbitals. -/
def gram (φ ψ : Fin N → Fin M → ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i j => ∑ x, φ i x * ψ j x

lemma det_gram (φ ψ : Fin N → Fin M → ℝ) :
    (gram φ ψ).det = ∑ τ : Fin N → Fin M, slater φ τ * ∏ j, ψ j (τ j) := by
  rw [det_apply]
  simp only [gram]
  have h1 : ∀ σ : Equiv.Perm (Fin N), ∏ i, ∑ x, φ (σ i) x * ψ i x =
      ∑ τ : Fin N → Fin M, ∏ i, (φ (σ i) (τ i) * ψ i (τ i)) := fun σ => Fintype.prod_sum _
  simp_rw [h1, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  rw [slater_eq_sum, Finset.sum_mul]
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin N)))]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Units.smul_def, zsmul_eq_mul]
  rw [Finset.prod_mul_distrib, ← mul_assoc]
  congr 2
  rw [← Equiv.prod_comp σ (fun x => φ (σ⁻¹ x) (τ x))]
  apply Finset.prod_congr rfl; intro i _; simp

/-- **Cauchy–Binet** for Slater determinants. -/
theorem cauchy_binet (φ ψ : Fin N → Fin M → ℝ) :
    ∑ s : Conf M N, slaterC φ s * slaterC ψ s = (gram φ ψ).det := by
  rw [det_gram]
  simp_rw [slater_expand φ, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  -- Σ_τ amp s τ Π ψ_j(τ_j) = Ψ_ψ(s), via `det_gram` for the indicator orbitals of `s`
  have hind := det_gram (fun j x => if x = τs s j then (1 : ℝ) else 0) ψ
  have hG : gram (fun j x => if x = τs s j then (1 : ℝ) else 0) ψ =
      Matrix.of fun k j => ψ j (τs s k) := by
    ext k j; simp [gram]
  rw [hG] at hind
  have hamp : ∑ τ : Fin N → Fin M, amp s τ * slaterC φ s * ∏ j, ψ j (τ j) =
      slaterC φ s * ∑ τ : Fin N → Fin M, slater (fun j x => if x = τs s j then (1 : ℝ) else 0) τ *
        ∏ j, ψ j (τ j) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro τ _; simp only [amp]; ring
  rw [hamp, ← hind]
  rfl

/-- Slater determinant of the orbitals selected by an orbital subset `S`. -/
def slaterSub (φ : Fin M → Fin M → ℝ) (S : Conf M N) : Conf M N → ℝ :=
  slaterC (fun j => φ (τs S j))

/-- **Orthonormality of Slater determinants.** -/
theorem slater_orthonormal {φ : Fin M → Fin M → ℝ}
    (hφ : ∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0) (S T : Conf M N) :
    ∑ s, slaterSub φ S s * slaterSub φ T s = if S = T then 1 else 0 := by
  rw [slaterSub, slaterSub, cauchy_binet]
  have : gram (fun j => φ (τs S j)) (fun j => φ (τs T j)) =
      Matrix.of fun k j => if τs S k = τs T j then (1 : ℝ) else 0 := by
    ext k j; simp [gram, hφ]
  rw [this, ← amp_tau_eq]
  rfl

end DFT
