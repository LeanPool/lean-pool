/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module

public import LeanPool.QECCertificates.GF2.HGPCompression

/-!
# Hypergraph-product transpose transport

Swapping the column blocks identifies the Z check with the X check on transposed
inputs, preserving kernels, row spaces and Hamming weight. This transport supports
both the dimension formula and the distance bounds without importing a cleaning proof.

Split from upstream `GF2/HGPCleaningDual.lean` without changing the declarations.
-/

@[expose] public section

namespace QECCertificates

open _root_.Matrix
open scoped BigOperators

variable {r₁ n₁ r₂ n₂ : ℕ}

/-! ## 1. The block swap -/

/-- **The block swap**, an involution: $\alpha\oplus\beta \to \beta\oplus\alpha$. It is
exactly the `Equiv.sumComm` appearing in `hgpHZ_transpose_inputs_apply`. -/
def swapBlocks {α β : Type*} : α ⊕ β → β ⊕ α := Sum.swap

/-- The block swap is an involution. -/
lemma swapBlocks_swapBlocks {α β : Type*} (c : α ⊕ β) : swapBlocks (swapBlocks c) = c := by
  rcases c with ab | st <;> rfl

/-- The block swap is injective. -/
lemma swapBlocks_injective {α β : Type*} : Function.Injective (swapBlocks (α := α) (β := β)) := by
  intro a b hab
  have h := congrArg (swapBlocks (α := β) (β := α)) hab
  simpa only [swapBlocks_swapBlocks] using h

/-- **The block swap preserves weight**. -/
lemma hammingNorm_swapBlocks
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hammingNorm (fun c => v (swapBlocks c)) = hammingNorm v := by
  have h₁ : hammingNorm (fun c : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂) => v (swapBlocks c))
      ≤ hammingNorm v :=
    hammingNorm_le_of_injective (fun c => swapBlocks c)
      (fun _ _ hab => swapBlocks_injective hab) v
  have h₂ : hammingNorm v
      ≤ hammingNorm (fun c : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂) => v (swapBlocks c)) := by
    have h := hammingNorm_le_of_injective (swapBlocks (α := (Fin n₁ × Fin n₂)) (β := (Fin r₁ × Fin
      r₂)))
      (swapBlocks_injective) (fun c => v (swapBlocks c))
    simpa only [swapBlocks_swapBlocks] using h
  exact le_antisymm h₁ h₂

/-! ## 2. The row identity and the correspondence of kernels -/

/-- **The row identity**: row $x$ of $H_Z(H_1^\top,H_2^\top)$ is row $x$ of
$H_X(H_1,H_2)$ followed by the block swap, entrywise, straight from the transpose-code
relation of part two. -/
lemma hgpHZ_row_eq_swap (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) (x : Fin n₁ × Fin r₂) :
    hgpHZ H₁ H₂ x = fun c => hgpHX H₁.transpose H₂.transpose x (swapBlocks c) := by
  funext c
  rcases c with ab | st
  · have h := hgpHZ_transpose_inputs_apply H₁.transpose H₂.transpose x (Sum.inl ab)
    simpa only [Equiv.sumComm_apply, swapBlocks, Matrix.transpose_transpose] using h
  · have h := hgpHZ_transpose_inputs_apply H₁.transpose H₂.transpose x (Sum.inr st)
    simpa only [Equiv.sumComm_apply, swapBlocks, Matrix.transpose_transpose] using h

/-- **The row identity for the dot products**: the two kernel conditions are equal row by
row, not merely vanishing together. -/
theorem mulVec_swap_eq (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (x : Fin n₁ × Fin r₂) :
    (hgpHZ H₁ H₂ *ᵥ v) x
      = (hgpHX H₁.transpose H₂.transpose *ᵥ (fun c => v (swapBlocks c))) x := by
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  have h₁ : (∑ c, hgpHZ H₁ H₂ x c * v c)
      = ∑ c, hgpHX H₁.transpose H₂.transpose x (swapBlocks c) * v c := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [congrFun (hgpHZ_row_eq_swap H₁ H₂ x) c]
  rw [h₁]
  refine Finset.sum_bij (fun c _ => swapBlocks c) ?_ ?_ ?_ ?_
  · intro c _; exact Finset.mem_univ _
  · intro c _ c' _ h; exact swapBlocks_injective h
  · intro c' _; exact ⟨swapBlocks c', Finset.mem_univ _, swapBlocks_swapBlocks c'⟩
  · intro c _
    rw [swapBlocks_swapBlocks]

/-- **The correspondence of kernels**: $v\in\ker H_Z(H_1,H_2)$ exactly when the swapped
$v$ lies in $\ker H_X(H_1^\top,H_2^\top)$. -/
theorem hgpHZ_mulVec_eq_zero_iff_swap (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hgpHZ H₁ H₂ *ᵥ v = 0 ↔
      hgpHX H₁.transpose H₂.transpose *ᵥ (fun c => v (swapBlocks c)) = 0 := by
  constructor <;> intro h
  · funext x
    rw [← mulVec_swap_eq H₁ H₂ v x, congrFun h x]
  · funext x
    rw [mulVec_swap_eq H₁ H₂ v x, congrFun h x]

/-- **The correspondence of row spaces**: for a vector $w$ that after the swap lies in the
row space of $H_Z(H_1^\top,H_2^\top)$, swapping once more puts it in the row space of
$H_X(H_1,H_2)$; for $v := w\circ\text{swap}$ this says
$v\in\mathrm{row}H_X(H_1,H_2)$. -/
theorem mem_rowSpace_X_of_swap_mem_rowSpace_Z (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (h : (fun c => v (swapBlocks c)) ∈ (hgpHZ H₁.transpose H₂.transpose).certificateRowSpace) :
    v ∈ (hgpHX H₁ H₂).certificateRowSpace := by
  have hgen : ∀ x : Fin r₁ × Fin n₂,
      (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) =>
        (hgpHZ H₁.transpose H₂.transpose x) (swapBlocks c)) ∈ (hgpHX H₁ H₂).certificateRowSpace :=
          by
    intro x
    have hrow : (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) =>
        (hgpHZ H₁.transpose H₂.transpose x) (swapBlocks c)) = hgpHX H₁ H₂ x := by
      funext c
      rw [hgpHZ_transpose_inputs_apply H₁ H₂ x (swapBlocks c)]
      congr 1
      rcases c with ab | st
      · rfl
      · rfl
    rw [hrow]
    exact Submodule.subset_span ⟨x, rfl⟩
  have hclosure : ∀ w : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂) → ZMod 2,
      w ∈ (hgpHZ H₁.transpose H₂.transpose).certificateRowSpace →
      (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => w (swapBlocks c))
        ∈ (hgpHX H₁ H₂).certificateRowSpace := by
    intro w hw
    have hw' : w ∈ Submodule.span (ZMod 2)
        (Set.range fun x : Fin r₁ × Fin n₂ => hgpHZ H₁.transpose H₂.transpose x) := hw
    refine Submodule.span_induction
      (p := fun w _ => (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => w (swapBlocks c))
        ∈ (hgpHX H₁ H₂).certificateRowSpace) ?_ ?_ ?_ ?_ hw'
    · intro g hg
      obtain ⟨x, rfl⟩ := hg
      exact hgen x
    · have hz : (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) =>
          (0 : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂) → ZMod 2) (swapBlocks c)) = 0 := by
        funext c; rfl
      rw [hz]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      have hadd : (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => (a + b) (swapBlocks c))
          = (fun c => a (swapBlocks c)) + fun c => b (swapBlocks c) := by
        funext c; rfl
      rw [hadd]
      exact Submodule.add_mem _ ha hb
    · intro cf a _ ha
      have hsmul : (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => (cf • a) (swapBlocks c))
          = cf • (fun c => a (swapBlocks c)) := by
        funext c; rfl
      rw [hsmul]
      exact Submodule.smul_mem _ cf ha
  have := hclosure (fun c => v (swapBlocks c)) h
  simpa only [swapBlocks_swapBlocks] using this

end QECCertificates
