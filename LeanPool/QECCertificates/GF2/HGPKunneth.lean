/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.KunnethCore
public import LeanPool.QECCertificates.GF2.HGPTranspose
public import LeanPool.QECCertificates.GF2.RankCertificate

/-!
# The dimension tensor formula for HGP: `k = k₁k₂ + k₁ᵀk₂ᵀ`

The **number of logical qubits** of the Tillich–Zémor hypergraph product satisfies a
Künneth-type tensor formula:

$$k(\mathrm{HGP}(H_1,H_2)) \;=\; k_1k_2 + k_1^\top k_2^\top,\qquad
k_1 = \dim\ker H_1,\quad k_1^\top=\dim\ker H_1^\top,$$

where $k = n - \operatorname{rank}H_X - \operatorname{rank}H_Z$ ($n = n_1n_2+r_1r_2$).
The first part gives the construction and the CSS orthogonality, the second the compression
identity and the third the distance lower bound; this module supplies the **dimension
side**, and with it the picture is complete: both the distance side and the dimension side
are structural theorems for arbitrary inputs $H_1,H_2$.

## Proof outline

The rank of `hgpHX` is the rank of a block matrix:

$$\operatorname{rank}[\,A\otimes I_s \mid I_p\otimes B^\top\,]
= \operatorname{rank}(A\otimes I_s) + \operatorname{rank}(I_p\otimes B^\top)
 - \dim\big(\mathrm{im}(A\otimes I_s)\cap \mathrm{im}(I_p\otimes B^\top)\big),$$

and each of the three terms is a dimension fact from `KunnethCore`:

| term | identification | dimension |
|---|---|---|
| `im(A ⊗ I)` | matrices with columns in `col A` (`colsSub`) | `s · rank A` (`finrank_colsSub`) |
| `im(I ⊗ Bᵀ)` | matrices with rows in `row B` (`rowsSub`) | `p · rank B` (`finrank_rowsSub`) |
| intersection | **columns in `col A` and rows in `row B`** | `rank A · rank B`
    (`finrank_colsRows`, the tensor intersection of subspaces) |

For $H_Z$ the transport goes along the transpose code (`mulVec_swap_eq` from the third
part):
$H_Z(A,B)$ and $H_X(A^\top,B^\top)$ differ only by the block swap of the columns, so their
ranks agree, and the distance side runs on the same argument.

## Main results

* `rank_hgpHX_add`: `rank H_X + rank A · rank B = n₂ · rank A + r₁ · rank B`
* `rank_hgpHZ_add`: `rank H_Z + rank A · rank B = r₂ · rank A + n₁ · rank B`
* **`hgp_kunneth`**: $k = k_1k_2+k_1^\top k_2^\top$ (subtraction form).
-/

@[expose] public section

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {p q r s : ℕ} {r₁ n₁ r₂ n₂ : ℕ}

/-! ## 1. The two block maps `M ↦ A·M` and `N ↦ N·B` -/

/-- **Left multiplication block** `M ↦ A·M` (that is, $A\otimes I$): the rows `p` carry the
action of `A` and the columns stay fixed. -/
noncomputable def mulLeft (A : Matrix (Fin p) (Fin q) (ZMod 2)) : VMat q s →ₗ[ZMod 2] VMat p s where
  toFun M := fun ij => ∑ a, A ij.1 a * M (a, ij.2)
  map_add' M N := by
    ext ⟨i, j⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c M := by
    ext ⟨i, j⟩
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro x _
    ring

/-- **Right multiplication block** `N ↦ N·B` (that is, $I\otimes B$): the columns carry the
action of `B` and the rows stay fixed. -/
noncomputable def mulRight (B : Matrix (Fin r) (Fin s) (ZMod 2)) : VMat p r →ₗ[ZMod 2] VMat p s
    where
  toFun N := fun ij => ∑ t, N (ij.1, t) * B t ij.2
  map_add' M N := by
    ext ⟨i, j⟩
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    ext ⟨i, j⟩
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

/-! ## 2. The images of the two blocks: column and row constraints -/

/-- **The image of the left block is the column-constraint space**: the image of `M ↦ A·M`
consists exactly of the matrices whose every column lies in the column space of `A`. -/
theorem range_mulLeft (A : Matrix (Fin p) (Fin q) (ZMod 2)) :
    LinearMap.range (mulLeft (s := s) A) = colsSub (LinearMap.range A.mulVecLin) := by
  ext X
  constructor
  · rintro ⟨M, rfl⟩ j
    refine ⟨colOf M j, ?_⟩
    funext i
    rw [Matrix.mulVecLin_apply]
    simp only [Matrix.mulVec, dotProduct, colOf_apply, mulLeft, LinearMap.coe_mk,
      AddHom.coe_mk]
  · intro hX
    choose f hf using fun j => hX j
    refine ⟨fun aj => f aj.2 aj.1, ?_⟩
    funext ij
    obtain ⟨i, j⟩ := ij
    have hstep : ∑ x, A i x * f j x = X (i, j) := by
      have h := congrFun (hf j) i
      rw [Matrix.mulVecLin_apply] at h
      simp only [Matrix.mulVec, dotProduct, colOf_apply] at h
      exact h
    exact hstep

/-- **The image of the right block is the row-constraint space**: the image of `N ↦ N·B`
consists exactly of the matrices whose every row lies in the row space of `B`. -/
theorem range_mulRight (B : Matrix (Fin r) (Fin s) (ZMod 2)) :
    LinearMap.range (mulRight (p := p) B) = rowsSub (Matrix.certificateRowSpace B) := by
  ext X
  constructor
  · rintro ⟨N, rfl⟩ i
    have hrow : rowOf (mulRight B N) i = ∑ t, N (i, t) • (fun j => B t j) := by
      funext j
      simp only [rowOf_apply, mulRight, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
    rw [hrow]
    exact Submodule.sum_mem _ fun t _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · intro hX
    choose f hf using fun i => (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2)
      (v := B) (x := rowOf X i)).mp (hX i)
    refine ⟨fun it => f it.1 it.2, ?_⟩
    funext ij
    obtain ⟨i, j⟩ := ij
    have hstep : ∑ t, f i t * B t j = X (i, j) := by
      have h := congrFun (hf i) j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowOf_apply] at h
      exact h
    exact hstep

/-! ## 3. The rank of `H_X` -/

/-- Block reading (product index): the left block `n₁×n₂`. -/
def blkL (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) : VMat n₁ n₂ :=
  fun ab => v (Sum.inl ab)

/-- Block reading (product index): the right block `r₁×r₂`. -/
def blkR (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) : VMat r₁ r₂ :=
  fun st => v (Sum.inr st)

/-- **The block action of `H_X`**: `H_X v = A·U + R·B` (with `U = blkL v` and `R = blkR v`),
the "sum of matrices" form of the compression identity. -/
theorem hgpHX_mulVecLin_eq_blocks (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    (hgpHX A B).mulVecLin v
      = mulLeft (s := n₂) A (blkL v) + mulRight (p := r₁) B (blkR v) := by
  funext ij
  obtain ⟨i, j⟩ := ij
  rw [Matrix.mulVecLin_apply, hgpHX_mulVec_apply, Matrix.mul_apply, Matrix.mul_apply]
  rfl

/-- **The rank of `H_X` equals the dimension of the sum of the images of the two blocks**. -/
theorem rank_hgpHX_add (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (hgpHX A B).rank + A.rank * B.rank = A.rank * n₂ + B.rank * r₁ := by
  have hrange : LinearMap.range (hgpHX A B).mulVecLin
      = LinearMap.range (mulLeft (s := n₂) A) ⊔ LinearMap.range (mulRight (p := r₁) B) := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rintro X ⟨v, rfl⟩
      rw [hgpHX_mulVecLin_eq_blocks]
      exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨blkL v, rfl⟩)
        (Submodule.mem_sup_right ⟨blkR v, rfl⟩)
    · rintro X ⟨M, rfl⟩
      refine ⟨Sum.elim M (0 : VMat r₁ r₂), ?_⟩
      rw [hgpHX_mulVecLin_eq_blocks]
      have h1 : blkL (Sum.elim M (0 : VMat r₁ r₂)) = M := rfl
      have h2 : blkR (Sum.elim M (0 : VMat r₁ r₂)) = 0 := rfl
      rw [h1, h2, map_zero, add_zero]
    · rintro X ⟨N, rfl⟩
      refine ⟨Sum.elim (0 : VMat n₁ n₂) N, ?_⟩
      rw [hgpHX_mulVecLin_eq_blocks]
      have h1 : blkL (Sum.elim (0 : VMat n₁ n₂) N) = 0 := rfl
      have h2 : blkR (Sum.elim (0 : VMat n₁ n₂) N) = N := rfl
      rw [h1, h2, map_zero, zero_add]
  let L1 : Submodule (ZMod 2) (VMat r₁ n₂) := LinearMap.range (mulLeft (s := n₂) A)
  let L2 : Submodule (ZMod 2) (VMat r₁ n₂) := LinearMap.range (mulRight (p := r₁) B)
  have hL1 : L1 = colsSub (LinearMap.range A.mulVecLin) := range_mulLeft A
  have hL2 : L2 = rowsSub (Matrix.certificateRowSpace B) := range_mulRight B
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 2) (V := VMat r₁ n₂)
    (s := L1) (t := L2)
  have h1 : Module.finrank (ZMod 2) L1 = A.rank * n₂ := by
    rw [hL1, finrank_colsSub]
    exact mul_comm _ _
  have h2 : Module.finrank (ZMod 2) L2 = B.rank * r₁ := by
    rw [hL2, finrank_rowsSub, ← Matrix.rank_eq_finrank_rowSpace B]
    exact mul_comm _ _
  have h3 : Module.finrank (ZMod 2) ↥(L1 ⊓ L2) = A.rank * B.rank := by
    rw [hL1, hL2, finrank_colsRows, ← Matrix.rank_eq_finrank_rowSpace B]
    rfl
  have hrank : (hgpHX A B).rank = Module.finrank (ZMod 2) ↥(L1 ⊔ L2) := by
    rw [Matrix.rank, hrange]
  rw [hrank]
  rw [h3, h1, h2] at hsup
  exact hsup

/-! ## 4. The rank of `H_Z` (transport along the transpose code) -/

/-- **The rank of `H_Z` equals the rank of `H_X` on the transposed inputs**: the two
matrices differ only by the block swap of the columns (`mulVec_swap_eq` from the third
part), so their images agree. -/
theorem rank_hgpHZ_eq (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (hgpHZ A B).rank = (hgpHX A.transpose B.transpose).rank := by
  have hrange : LinearMap.range (hgpHZ A B).mulVecLin
      = LinearMap.range (hgpHX A.transpose B.transpose).mulVecLin := by
    ext X
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨fun c => v (swapBlocks c), by
        funext x
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, mulVec_swap_eq]⟩
    · rintro ⟨w, rfl⟩
      exact ⟨fun c => w (swapBlocks c), by
        funext x
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, mulVec_swap_eq]
        congr 1
        funext c
        simp only [swapBlocks_swapBlocks]⟩
  rw [Matrix.rank, Matrix.rank, hrange]

/-- **The rank of `H_Z`**: the same shape as `rank_hgpHX_add`, with `n₂ ↦ r₂` and
`r₁ ↦ n₁`. -/
theorem rank_hgpHZ_add (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (hgpHZ A B).rank + A.rank * B.rank = A.rank * r₂ + B.rank * n₁ := by
  have h := rank_hgpHX_add A.transpose B.transpose
  rw [Matrix.rank_transpose, Matrix.rank_transpose] at h
  rw [rank_hgpHZ_eq]
  exact h

/-! ## 5. The dimension tensor formula -/

/-- **Dimension tensor formula (integer form)**: rewrite `k = n - rank H_X - rank H_Z`
additively and do the polynomial arithmetic over `ℤ` (`nlinarith`), which avoids truncated
subtraction in `ℕ`. -/
theorem hgp_kunneth_int (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    ((hgpHX A B).rank : ℤ) + ((hgpHZ A B).rank : ℤ)
      + (((n₁ : ℤ) - A.rank) * ((n₂ : ℤ) - B.rank)
        + ((r₁ : ℤ) - A.rank) * ((r₂ : ℤ) - B.rank))
      = (n₁ : ℤ) * n₂ + (r₁ : ℤ) * r₂ := by
  have h1 : ((hgpHX A B).rank : ℤ) + (A.rank : ℤ) * B.rank
      = (A.rank : ℤ) * n₂ + (B.rank : ℤ) * r₁ := by
    exact_mod_cast rank_hgpHX_add A B
  have h2 : ((hgpHZ A B).rank : ℤ) + (A.rank : ℤ) * B.rank
      = (A.rank : ℤ) * r₂ + (B.rank : ℤ) * n₁ := by
    exact_mod_cast rank_hgpHZ_add A B
  nlinarith [h1, h2]

/-- **Dimension tensor formula for HGP (Künneth)**: the number of logical qubits
$k = n - \operatorname{rank}H_X - \operatorname{rank}H_Z$ is exactly
$k_1k_2 + k_1^\top k_2^\top$ (the sum of the products of the kernel dimensions of the two
classical codes).

This is the last piece: the distance side (the third part together with the dual side) and
the dimension side (this theorem) together give the HGP family parameters for $n\ge144$ a
**structural assertion that does not rely on enumeration**. -/
theorem hgp_kunneth (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (n₁ * n₂ + r₁ * r₂) - (hgpHX A B).rank - (hgpHZ A B).rank
      = (n₁ - A.rank) * (n₂ - B.rank) + (r₁ - A.rank) * (r₂ - B.rank) := by
  have hA1 : A.rank ≤ n₁ := A.rank_le_width
  have hA2 : A.rank ≤ r₁ := A.rank_le_height
  have hB1 : B.rank ≤ n₂ := B.rank_le_width
  have hB2 : B.rank ≤ r₂ := B.rank_le_height
  have hb : (hgpHX A B).rank + (hgpHZ A B).rank ≤ n₁ * n₂ + r₁ * r₂ := by
    by_contra hcon
    have hlt : ((n₁ : ℤ) * n₂ + (r₁ : ℤ) * r₂)
        < ((hgpHX A B).rank : ℤ) + ((hgpHZ A B).rank : ℤ) := by
      exact_mod_cast Nat.not_le.mp hcon
    have h1' : (0 : ℤ) ≤ (n₁ : ℤ) - A.rank := by
      have : (A.rank : ℤ) ≤ (n₁ : ℤ) := by exact_mod_cast hA1
      linarith
    have h2' : (0 : ℤ) ≤ (n₂ : ℤ) - B.rank := by
      have : (B.rank : ℤ) ≤ (n₂ : ℤ) := by exact_mod_cast hB1
      linarith
    have h3' : (0 : ℤ) ≤ (r₁ : ℤ) - A.rank := by
      have : (A.rank : ℤ) ≤ (r₁ : ℤ) := by exact_mod_cast hA2
      linarith
    have h4' : (0 : ℤ) ≤ (r₂ : ℤ) - B.rank := by
      have : (B.rank : ℤ) ≤ (r₂ : ℤ) := by exact_mod_cast hB2
      linarith
    have hnn : (0 : ℤ) ≤ ((n₁ : ℤ) - A.rank) * ((n₂ : ℤ) - B.rank)
        + ((r₁ : ℤ) - A.rank) * ((r₂ : ℤ) - B.rank) := by nlinarith [h1', h2', h3', h4']
    have := hgp_kunneth_int A B
    linarith
  have hle1 : (hgpHX A B).rank ≤ n₁ * n₂ + r₁ * r₂ := le_trans (Nat.le_add_right _ _) hb
  have hle2 : (hgpHZ A B).rank ≤ (n₁ * n₂ + r₁ * r₂) - (hgpHX A B).rank := by omega
  apply Nat.cast_injective (R := ℤ)
  have hcast : (((n₁ * n₂ + r₁ * r₂) - (hgpHX A B).rank - (hgpHZ A B).rank : ℕ) : ℤ)
      = (n₁ : ℤ) * n₂ + (r₁ : ℤ) * r₂ - (hgpHX A B).rank - (hgpHZ A B).rank := by
    rw [Nat.cast_sub hle2, Nat.cast_sub hle1]
    push_cast
    ring
  have hcast2 : (((n₁ - A.rank) * (n₂ - B.rank) + (r₁ - A.rank) * (r₂ - B.rank) : ℕ) : ℤ)
      = ((n₁ : ℤ) - A.rank) * ((n₂ : ℤ) - B.rank)
        + ((r₁ : ℤ) - A.rank) * ((r₂ : ℤ) - B.rank) := by
    push_cast [Nat.cast_sub hA1, Nat.cast_sub hA2, Nat.cast_sub hB1, Nat.cast_sub hB2]
    ring
  rw [hcast, hcast2]
  linarith [hgp_kunneth_int A B]

end QECCertificates
