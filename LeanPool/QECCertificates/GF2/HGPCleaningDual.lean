/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.HGPCleaning
public import LeanPool.QECCertificates.GF2.HGPTranspose

/-!
# HGP, part three (the dual side): the Z-distance lower bound, by transporting the
transpose code

The X side (`GF2/HGPCleaning`) proves that $v\in\ker H_X$, $v\notin\mathrm{row}H_Z$
$\Longrightarrow \min(d_1,d_2^\top)\le|v|$. This module gives the dual statement

$$v\in\ker H_Z,\; v\notin\mathrm{row}H_X \;\Longrightarrow\
\min(d_1^\top,\, d_2) \le |v|,\qquad
d_1^\top=\min\ker H_1^\top,\; d_2=\min\ker H_2 .$$

**The route: transporting the transpose code.** Part two already proves
(`hgpHZ_transpose_inputs_apply`) that
$$\text{row }x\text{ of }H_Z(H_1^\top,H_2^\top)
= \big(\text{row }x\text{ of }H_X(H_1,H_2)\big)\circ(\text{block swap}),$$
that is, the two matrices are **entrywise identical and differ only by the block swap of
their columns**. Hence:

* `hgpHZ_row_eq_swap`: the row identity, entrywise, straight from the transpose-code
  relation of part two
* `mulVec_swap_eq` / `hgpHZ_mulVec_eq_zero_iff_swap`: $v\in\ker H_Z(H_1,H_2)$ exactly when
  the swapped $v$ lies in $\ker H_X(H_1^\top,H_2^\top)$, with **the two dot products equal
  row by row**, not merely vanishing together
* `mem_rowSpace_X_of_swap_mem_rowSpace_Z`: the correspondence of row spaces, generator by
  generator and then by subspace induction
* `hammingNorm_swapBlocks`: the block swap preserves weight.

Together, the four make **the Z-side theorem a direct instance of the X-side theorem on
transposed inputs** (`hgp_Z_distance_ge`): the cleaning argument need not be reworked. That
is what the phrase "transpose code" does for the distance analysis.
-/

@[expose] public section

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {r₁ n₁ r₂ n₂ : ℕ}

/-! ## 3. The Z-distance lower bound, a transposed instance of the X-side theorem -/

/-- **The Z-distance lower bound for HGP**: a nonzero Z-type operator outside the row
space of `H_X` has weight at least $\min(d_1^\top, d_2)$, the smaller of the **transpose-code
distance** and the distance of the right code.

The proof swaps the blocks of $v$ and applies the X-side theorem to the inputs
$(H_1^\top,H_2^\top)$. Transposition interchanges $d_1\leftrightarrow d_1^\top$ and
$d_2^\top\leftrightarrow d_2$, so the $\min(d_1,d_2^\top)$ of the X side is
$\min(d_1^\top,d_2)$ here. -/
theorem hgp_Z_distance_ge (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).certificateRowSpace) {d₁T d₂ : ℕ}
    (hd₁ : ∀ w : Vec r₁, w ≠ 0 → H₁.transpose *ᵥ w = 0 → d₁T ≤ hammingNorm w)
    (hd₂ : ∀ w : Vec n₂, w ≠ 0 → H₂ *ᵥ w = 0 → d₂ ≤ hammingNorm w) :
    min d₁T d₂ ≤ hammingNorm v := by
  have hmain := hgp_X_distance_ge (H₁ := H₁.transpose) (H₂ := H₂.transpose)
    (v := fun c => v (swapBlocks c)) (d₁ := d₁T) (d₂T := d₂)
    ((hgpHZ_mulVec_eq_zero_iff_swap H₁ H₂ v).mp hv)
    (fun hmem => hlog (mem_rowSpace_X_of_swap_mem_rowSpace_Z H₁ H₂ hmem))
    hd₁
    (fun w hw hw0 => hd₂ w hw (by simpa [Matrix.transpose_transpose] using hw0))
  rwa [hammingNorm_swapBlocks] at hmain

/-! ## 4. The Z-side versions of the four "cleaning step can be dropped" lemmas
(transposed instances of the X-side theorems)

The X side (`GF2/HGPCleaning` §6) proves that **each** of the two steps of the cleaning
lower bound can be replaced by a single kernel condition, leaving only one factor in the
bound. This section transports the four lemmas to the Z side **without changing a single
argument**, performing the same three-step transport as in `hgp_Z_distance_ge`: the
correspondence of kernels, the correspondence of row spaces, and preservation of weight. The
two "row cleaning can be dropped" lemmas become $d_2\le|v|$ and the two "column cleaning can
be dropped" lemmas become $d_1^\top\le|v|$:

| X side (kernel condition → remaining factor) | Z side |
|---|---|
| $\ker H_1=0$ (or $\ker H_2=0$) $\Rightarrow d_2^\top$ | $\ker H_1^\top=0$ (or $\ker H_2^\top=0$)
    $\Rightarrow d_2$ |
| $\ker H_1^\top=0$ (or $\ker H_2^\top=0$) $\Rightarrow d_1$ | $\ker H_1=0$ (or $\ker H_2=0$)
    $\Rightarrow d_1^\top$ | -/

/-- **A lower bound on $d_Z$, the $\ker H_1=0$ branch**: when $H_1$ is injective, the
single factor $d_1^\top$ suffices. -/
theorem hgp_Z_distance_ge_of_H1Ker_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).certificateRowSpace) {d₁T : ℕ}
    (hd₁ : ∀ w : Vec r₁, w ≠ 0 → H₁.transpose *ᵥ w = 0 → d₁T ≤ hammingNorm w)
    (hT : ∀ u : Vec n₁, H₁ *ᵥ u = 0 → u = 0) :
    d₁T ≤ hammingNorm v := by
  have hmain := hgp_X_distance_ge_of_adjoint_ker_trivial (H₁ := H₁.transpose)
    (H₂ := H₂.transpose) (v := fun c => v (swapBlocks c)) (d₁ := d₁T)
    ((hgpHZ_mulVec_eq_zero_iff_swap H₁ H₂ v).mp hv)
    (fun hmem => hlog (mem_rowSpace_X_of_swap_mem_rowSpace_Z H₁ H₂ hmem))
    hd₁
    (fun u hu => by simpa [Matrix.transpose_transpose] using hT u hu)
  rwa [hammingNorm_swapBlocks] at hmain

/-- **A lower bound on $d_Z$, the $\ker H_2^\top=0$ branch**: when $H_2^\top$ is
injective, the single factor $d_2$ suffices. -/
theorem hgp_Z_distance_ge_of_H2TKer_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).certificateRowSpace) {d₂ : ℕ}
    (hd₂ : ∀ w : Vec n₂, w ≠ 0 → H₂ *ᵥ w = 0 → d₂ ≤ hammingNorm w)
    (hT : ∀ u : Vec r₂, H₂.transpose *ᵥ u = 0 → u = 0) :
    d₂ ≤ hammingNorm v := by
  have hmain := hgp_X_distance_ge_of_H2Ker_trivial (H₁ := H₁.transpose)
    (H₂ := H₂.transpose) (v := fun c => v (swapBlocks c)) (d₂T := d₂)
    ((hgpHZ_mulVec_eq_zero_iff_swap H₁ H₂ v).mp hv)
    (fun hmem => hlog (mem_rowSpace_X_of_swap_mem_rowSpace_Z H₁ H₂ hmem))
    (fun w hw hw0 => hd₂ w hw (by simpa [Matrix.transpose_transpose] using hw0))
    hT
  rwa [hammingNorm_swapBlocks] at hmain

/-- **A lower bound on $d_Z$, the $\ker H_1^\top=0$ branch**: when $H_1^\top$ is
injective, the single factor $d_2$ suffices. -/
theorem hgp_Z_distance_ge_of_H1TKer_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).certificateRowSpace) {d₂ : ℕ}
    (hd₂ : ∀ w : Vec n₂, w ≠ 0 → H₂ *ᵥ w = 0 → d₂ ≤ hammingNorm w)
    (hT : ∀ u : Vec r₁, H₁.transpose *ᵥ u = 0 → u = 0) :
    d₂ ≤ hammingNorm v := by
  have hmain := hgp_X_distance_ge_of_H1Ker_trivial (H₁ := H₁.transpose)
    (H₂ := H₂.transpose) (v := fun c => v (swapBlocks c)) (d₂T := d₂)
    ((hgpHZ_mulVec_eq_zero_iff_swap H₁ H₂ v).mp hv)
    (fun hmem => hlog (mem_rowSpace_X_of_swap_mem_rowSpace_Z H₁ H₂ hmem))
    (fun w hw hw0 => hd₂ w hw (by simpa [Matrix.transpose_transpose] using hw0))
    hT
  rwa [hammingNorm_swapBlocks] at hmain

/-- **A lower bound on $d_Z$, the $\ker H_2=0$ branch**: when $H_2$ is injective, the
single factor $d_1^\top$ suffices. -/
theorem hgp_Z_distance_ge_of_H2Ker_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).certificateRowSpace) {d₁T : ℕ}
    (hd₁ : ∀ w : Vec r₁, w ≠ 0 → H₁.transpose *ᵥ w = 0 → d₁T ≤ hammingNorm w)
    (hT : ∀ u : Vec n₂, H₂ *ᵥ u = 0 → u = 0) :
    d₁T ≤ hammingNorm v := by
  have hmain := hgp_X_distance_ge_of_H2TKer_trivial (H₁ := H₁.transpose)
    (H₂ := H₂.transpose) (v := fun c => v (swapBlocks c)) (d₁ := d₁T)
    ((hgpHZ_mulVec_eq_zero_iff_swap H₁ H₂ v).mp hv)
    (fun hmem => hlog (mem_rowSpace_X_of_swap_mem_rowSpace_Z H₁ H₂ hmem))
    hd₁
    (fun u hu => by simpa [Matrix.transpose_transpose] using hT u hu)
  rwa [hammingNorm_swapBlocks] at hmain

end QECCertificates
