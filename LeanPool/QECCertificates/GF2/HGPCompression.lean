/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.HGP

/-!
# HGP, part two: the compression identity, the transpose code, and the single-block weight lower
    bound (continued)

The first part (`GF2/HGP`) gives the construction and the CSS orthogonality. This module
supplies the three building blocks needed for the **distance analysis**.

## 1. The compression identity

Read a vector `v` as two matrices over the two blocks of the column space, `blockL v`
($n_1\times n_2$) and `blockR v` ($r_1\times r_2$). Entrywise computation gives

$$H_X\, v = 0 \iff H_1 \cdot \mathrm{blockL}\,v = \mathrm{blockR}\,v \cdot H_2,\qquad
H_Z\, v = 0 \iff \mathrm{blockL}\,v \cdot H_2^\top = H_1^\top \cdot \mathrm{blockR}\,v.$$

The first of the two presents the pair $U = \mathrm{blockL}\,v$, $R = \mathrm{blockR}\,v$
as a **commuting square** ($H_1 U = R H_2$), which is exactly the entrywise form of the
"chain map" picture of the hypergraph product. Every case of the distance lower bound
starts from the identity on that same side.

## 2. The transpose code

Take the inputs transposed and use them as **new** parity-check matrices. Then the column
space of `hgpHZ H₁ᵀ H₂ᵀ` is $(r_1 r_2) \oplus (n_1 n_2)$ (the two blocks exchange their
shapes), and after "swapping the two blocks" its row `(a, d)` agrees **entrywise** with the
same row of `hgpHX H₁ H₂`:

`hgpHZ H₁ᵀ H₂ᵀ x c = hgpHX H₁ H₂ x (sumComm c)`.

So `HGP(H₁ᵀ, H₂ᵀ)` is exactly the **transpose code** of `HGP(H₁, H₂)`: the X-side analysis
and the Z-side analysis are two applications of one and the same argument, which is the
source of the distance of `ker H₂ᵀ` (the transpose-code distance) appearing in the lower
bound formula.

## 3. The single-block weight lower bound

If an X-type operator has support only in the left block (`blockR v = 0`), the compression
identity forces every column to be a kernel vector of $H_1$; the weight of any nonzero
column is at least the left-code distance `d₁`, and the weight of a single column is at
most the weight of the whole vector:
  `d₁ ≤ hammingNorm (column) ≤ hammingNorm v`

The right block gives `d₂ᵀ` (the distance of $\ker H_2^\top$) in the same way. **The case
where both blocks are nonzero at once**, that is, where the two contributions cancel each
other, requires the cleaning/quotient argument provided by `GF2/HGPCleaning`; this module
supplies the single-block bounds used by that argument.

## Main results

* `hgpHX_mulVec_eq_zero_iff` / `hgpHZ_mulVec_eq_zero_iff`: the compression identity.
* `hgpHZ_transpose_inputs_apply`: the transpose-code relation.
* `hgp_hammingNorm_ge_of_pure_left` / `_of_pure_right`: the single-block weight lower bound.
-/

@[expose] public section

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {r₁ n₁ r₂ n₂ : ℕ}

/-! ## Reading the blocks -/

/-- Read a vector as a matrix on the left block ($n_1\times n_2$). -/
def blockL (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    Matrix (Fin n₁) (Fin n₂) (ZMod 2) :=
  fun a b => v (Sum.inl (a, b))

/-- Read a vector as a matrix on the right block ($r_1\times r_2$). -/
def blockR (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    Matrix (Fin r₁) (Fin r₂) (ZMod 2) :=
  fun s t => v (Sum.inr (s, t))

@[simp] lemma blockL_apply (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2)
    (a : Fin n₁) (b : Fin n₂) : blockL v a b = v (Sum.inl (a, b)) := rfl

@[simp] lemma blockR_apply (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2)
    (s : Fin r₁) (t : Fin r₂) : blockR v s t = v (Sum.inr (s, t)) := rfl

/-! ## Slicing lemmas for the entrywise computation -/

/-- "Take one column" on a product index: `Σ_{a,b} A a · [j = b] · F a b = Σ_a A a · F a j`. -/
lemma sum_prod_slice_snd {m k : ℕ} (A : Fin m → ZMod 2) (F : Fin m → Fin k → ZMod 2)
    (j : Fin k) :
    (∑ p : Fin m × Fin k, A p.1 * (if j = p.2 then 1 else 0) * F p.1 p.2)
      = ∑ a, A a * F a j := by
  rw [Fintype.sum_prod_type (f := fun p : Fin m × Fin k =>
    A p.1 * (if j = p.2 then 1 else 0) * F p.1 p.2)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (s := Finset.univ)
    (f := fun b => A a * (if j = b then 1 else 0) * F a b) j ?_ ?_]
  · rw [ite_eq_left rfl, mul_one]
  · intro b _ hb
    rw [ite_eq_right (fun h => hb h.symm), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- "Take one row" on a product index: `Σ_{a,b} [i = a] · B b · F a b = Σ_b B b · F i b`. -/
lemma sum_prod_slice_fst {m k : ℕ} (B : Fin k → ZMod 2) (F : Fin m → Fin k → ZMod 2)
    (i : Fin m) :
    (∑ p : Fin m × Fin k, (if i = p.1 then 1 else 0) * B p.2 * F p.1 p.2)
      = ∑ b, B b * F i b := by
  rw [Fintype.sum_prod_type (f := fun p : Fin m × Fin k =>
    (if i = p.1 then 1 else 0) * B p.2 * F p.1 p.2)]
  rw [Finset.sum_eq_single (s := Finset.univ)
    (f := fun a : Fin m => ∑ b : Fin k, (if i = a then 1 else 0) * B b * F a b) i ?_ ?_]
  · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right (fun h => ha h.symm), zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ## The compression identity -/

/-- **X side, entrywise**: `(H_X v)_{(i,j)} = (H_1 · U)_{ij} + (R · H_2)_{ij}`, where
`U = blockL v` and `R = blockR v`.

The two sums reduce by the **definitions** of `H_X`, `H_1 ⊗ I` and `I ⊗ H_2` (at the `rfl`
level), and one slicing lemma each then collapses the sum over the product index into a
sum over a single index. -/
theorem hgpHX_mulVec_apply (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (i : Fin r₁) (j : Fin n₂) :
    (hgpHX H₁ H₂ *ᵥ v) (i, j) = (H₁ * blockL v) i j + (blockR v * H₂) i j := by
  have hL : (hgpHX H₁ H₂ *ᵥ v) (i, j)
      = (∑ ab : Fin n₁ × Fin n₂, (H₁ i ab.1 * (if j = ab.2 then 1 else 0)) * v (Sum.inl ab))
      + (∑ st : Fin r₁ × Fin r₂, ((if i = st.1 then 1 else 0) * H₂ st.2 j) * v (Sum.inr st)) := by
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    congr 1
  have hR1 : (H₁ * blockL v) i j = ∑ a, H₁ i a * v (Sum.inl (a, j)) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [blockL_apply]
  have hR2 : (blockR v * H₂) i j = ∑ t, H₂ t j * v (Sum.inr (i, t)) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun t _ => by rw [blockR_apply, mul_comm]
  rw [hL, hR1, hR2,
    sum_prod_slice_snd (A := fun a => H₁ i a) (F := fun a b => v (Sum.inl (a, b))) j,
    sum_prod_slice_fst (B := fun t => H₂ t j) (F := fun s t => v (Sum.inr (s, t))) i]

/-- **Z side, entrywise**: `(H_Z v)_{(a,d)} = (U · H_2ᵀ)_{ad} + (H_1ᵀ · R)_{ad}`. -/
theorem hgpHZ_mulVec_apply (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (a : Fin n₁) (d : Fin r₂) :
    (hgpHZ H₁ H₂ *ᵥ v) (a, d) = (blockL v * H₂.transpose) a d + (H₁.transpose * blockR v) a d := by
  have hL : (hgpHZ H₁ H₂ *ᵥ v) (a, d)
      = (∑ ab : Fin n₁ × Fin n₂, ((if a = ab.1 then 1 else 0) * H₂ d ab.2) * v (Sum.inl ab))
      + (∑ st : Fin r₁ × Fin r₂, (H₁ st.1 a * (if d = st.2 then 1 else 0)) * v (Sum.inr st)) := by
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    congr 1
  have hR1 : (blockL v * H₂.transpose) a d = ∑ b, H₂ d b * v (Sum.inl (a, b)) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => by
      rw [Matrix.transpose_apply, blockL_apply, mul_comm]
  have hR2 : (H₁.transpose * blockR v) a d = ∑ s, H₁ s a * v (Sum.inr (s, d)) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun s _ => by
      rw [Matrix.transpose_apply, blockR_apply]
  rw [hL, hR1, hR2,
    sum_prod_slice_fst (B := fun b => H₂ d b) (F := fun a b => v (Sum.inl (a, b))) a,
    sum_prod_slice_snd (A := fun s => H₁ s a) (F := fun s t => v (Sum.inr (s, t))) d]

/-- **Compression identity (X side)**: $H_X v = 0 \iff H_1\,U = R\,H_2$.

The equality on the right is the statement that $(U, R)$ is a chain map; the whole case
analysis of the distance lower bound unfolds from it. -/
theorem hgpHX_mulVec_eq_zero_iff (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hgpHX H₁ H₂ *ᵥ v = 0 ↔ H₁ * blockL v = blockR v * H₂ := by
  constructor
  · intro hv
    funext i j
    have h := congrFun hv (i, j)
    rw [hgpHX_mulVec_apply] at h
    simp only [Pi.zero_apply] at h
    exact (add_eq_zero_iff_eq _ _).mp h
  · intro hcomp
    funext x
    obtain ⟨i, j⟩ := x
    rw [hgpHX_mulVec_apply, hcomp]
    simp only [Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _

/-- **Compression identity (Z side)**: $H_Z v = 0 \iff U\,H_2^\top = H_1^\top\,R$. -/
theorem hgpHZ_mulVec_eq_zero_iff (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hgpHZ H₁ H₂ *ᵥ v = 0 ↔ blockL v * H₂.transpose = H₁.transpose * blockR v := by
  constructor
  · intro hv
    funext a d
    have h := congrFun hv (a, d)
    rw [hgpHZ_mulVec_apply] at h
    simp only [Pi.zero_apply] at h
    exact (add_eq_zero_iff_eq _ _).mp h
  · intro hcomp
    funext x
    obtain ⟨a, d⟩ := x
    rw [hgpHZ_mulVec_apply, hcomp]
    simp only [Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _

/-! ## The transpose code -/

/-- **Transpose-code relation**: the Z parity-check matrix obtained from the transposed
inputs agrees entrywise with the original X parity-check matrix, under the column
relabelling that swaps the two blocks. Hence `HGP(H₁ᵀ, H₂ᵀ)` is the transpose code of
`HGP(H₁, H₂)`, and the X-side and Z-side distance analyses are two applications of one
and the same argument. -/
theorem hgpHZ_transpose_inputs_apply (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) (x : Fin r₁ × Fin n₂)
    (c : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂)) :
    hgpHZ H₁.transpose H₂.transpose x c
      = hgpHX H₁ H₂ x (Equiv.sumComm _ _ c) := by
  rcases c with st | ab
  · obtain ⟨s, t⟩ := st; rfl
  · obtain ⟨a, b⟩ := ab; rfl

/-! ## The single-block weight lower bound -/

/-- Pulling a vector back along an injection does not increase its weight (the support
embeds under the injection). -/
lemma hammingNorm_le_of_injective {α β : Type*} [Fintype α] [Fintype β] (e : α → β)
    (he : Function.Injective e) (v : β → ZMod 2) :
    hammingNorm (fun a => v (e a)) ≤ hammingNorm v := by
  change (Finset.univ.filter (fun a => v (e a) ≠ 0)).card
    ≤ (Finset.univ.filter (fun b => v b ≠ 0)).card
  refine Finset.card_le_card_of_injOn e ?_ ?_
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ h
    exact he h

/-- **Single-block weight lower bound (left)**: an X-type operator supported only in the
left block has weight at least the left-code distance `d₁`.

Every column of the left block lies in `ker H₁` (compression identity plus `blockR v = 0`),
a nonzero column has weight at least `d₁`, and a single column weighs no more than the
whole vector. -/
theorem hgp_hammingNorm_ge_of_pure_left {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0) (hR : blockR v = 0) {d : ℕ}
    (hd : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d ≤ hammingNorm w)
    (hL : blockL v ≠ 0) : d ≤ hammingNorm v := by
  have hcomp : H₁ * blockL v = 0 := by
    have h := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
    rw [hR, Matrix.zero_mul] at h
    exact h
  obtain ⟨a, b, hab⟩ : ∃ a b, blockL v a b ≠ 0 := by
    by_contra hcon
    exact hL (funext fun a => funext fun b => by
      by_contra hc
      exact hcon ⟨a, b, hc⟩)
  have hcol : H₁ *ᵥ (fun a' => blockL v a' b) = 0 := by
    funext a'
    have h2 : (H₁ * blockL v) a' b = 0 := by rw [hcomp]; rfl
    rw [Matrix.mulVec, dotProduct, ← Matrix.mul_apply]
    exact h2
  have hcolne : (fun a' => blockL v a' b) ≠ 0 :=
    fun h => hab (by simpa using congrFun h a)
  calc d ≤ hammingNorm (fun a' => blockL v a' b) := hd _ hcolne hcol
    _ ≤ hammingNorm (fun p : Fin n₁ × Fin n₂ => blockL v p.1 p.2) :=
        hammingNorm_le_of_injective (fun a' : Fin n₁ => (a', b))
          (fun _ _ h => congrArg Prod.fst h) (fun p : Fin n₁ × Fin n₂ => blockL v p.1 p.2)
    _ ≤ hammingNorm v :=
        hammingNorm_le_of_injective (fun p : Fin n₁ × Fin n₂ => Sum.inl p)
          Sum.inl_injective v

/-- **Single-block weight lower bound (right)**: an X-type operator supported only in the
right block has weight at least the distance of `ker H₂ᵀ` (the **transpose-code distance**
`d₂ᵀ`), which is exactly why the transpose code appears in the lower bound formula.

Every row `r_i` of the right block satisfies `H₂ᵀ r_i = 0` (compression identity plus
`blockL v = 0`). -/
theorem hgp_hammingNorm_ge_of_pure_right {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0) (hL : blockL v = 0) {d : ℕ}
    (hd : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d ≤ hammingNorm w)
    (hR : blockR v ≠ 0) : d ≤ hammingNorm v := by
  have hcomp : blockR v * H₂ = 0 := by
    have h := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
    rw [hL, Matrix.mul_zero] at h
    exact h.symm
  obtain ⟨s, t, hst⟩ : ∃ s t, blockR v s t ≠ 0 := by
    by_contra hcon
    exact hR (funext fun s => funext fun t => by
      by_contra hc
      exact hcon ⟨s, t, hc⟩)
  have hrow : H₂.transpose *ᵥ (fun t' => blockR v s t') = 0 := by
    funext t'
    have h2 : (blockR v * H₂) s t' = 0 := by rw [hcomp]; rfl
    have h3 : (H₂.transpose *ᵥ (fun t' => blockR v s t')) t' = (blockR v * H₂) s t' := by
      rw [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun t _ => by rw [Matrix.transpose_apply, mul_comm]
    rw [h3]
    exact h2
  have hrowne : (fun t' => blockR v s t') ≠ 0 :=
    fun h => hst (by simpa using congrFun h t)
  calc d ≤ hammingNorm (fun t' => blockR v s t') := hd _ hrowne hrow
    _ ≤ hammingNorm (fun q : Fin r₁ × Fin r₂ => blockR v q.1 q.2) :=
        hammingNorm_le_of_injective (fun t' : Fin r₂ => (s, t'))
          (fun _ _ h => congrArg Prod.snd h) (fun q : Fin r₁ × Fin r₂ => blockR v q.1 q.2)
    _ ≤ hammingNorm v :=
        hammingNorm_le_of_injective (fun q : Fin r₁ × Fin r₂ => Sum.inr q)
          Sum.inr_injective v

end QECCertificates
