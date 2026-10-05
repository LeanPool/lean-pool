/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.HGPCompression
public import LeanPool.QECCertificates.GF2.Canonical
public import LeanPool.QECCertificates.GF2.KernelBasis

/-!
# HGP, part three: the cleaning argument and the X distance lower bound

The first part gave the construction and CSS orthogonality, the second the compression identity
$H_Xv=0 \iff H_1U=RH_2$, the transposed-code relation and the **single-block** weight lower bound.
This part adds the cleaning/quotient argument for mixed blocks (both blocks nonzero at once), so
that the X distance lower bound of the HGP holds for **every** nontrivial logical operator:

$$d_X \ge \min(d_1,\; d_2^\top),\qquad
d_1 = \min\ker H_1,\quad d_2^\top = \min\ker H_2^\top.$$

## 1. The cleaning lemma (the core of this part)

Let $v = (U,R) \in \ker H_X$, that is $H_1U = RH_2$, and let $|v|$ denote the weight.

* **Row cleaning** (`blockL_rows_mem_of_small`): if $|v| < d_1$, then every row of $U$ lies in the
  row space of $H_2$.
  Proof: if some row $U_{a\cdot}$ has nonzero dot product with $z\in\ker H_2$, let
  $x_a := U_{a\cdot}\cdot z$; the compression identity gives $H_1 x = 0$, while $x \ne 0$ and
  $|x| \le |v| < d_1$, contradicting "every kernel vector has weight at least $d_1$".
* **Column cleaning** (`blockR_cols_mem_of_small`): if $|v| < d_2^\top$, then every column of $R$
  lies in the column space of $H_1$ (the symmetric argument, with $w\in\ker H_1^\top$).

Both are **weight-counting** arguments: the contradiction comes from the direct clash between
"every kernel vector has weight at least the distance" and "the support of that vector is a subset
of the support of $v$". No enumeration is needed.

## 2. Consistency (the cleaning certificate)

Row cleaning gives $C_0$ with $C_0H_2 = U$; column cleaning makes every column of
$\rho := R + H_1C_0$ lie in the column space of $H_1$, with $\rho H_2 = 0$. This part proves
(`exists_cleaning_cert`) that

$$\text{the columns all lie in }\mathrm{col}(H_1)\;\wedge\;\rho H_2 = 0
\;\Longrightarrow\; \exists D,\; H_1D = \rho \;\wedge\; DH_2 = 0.$$

**The construction is explicit**: the columns of $\rho$ are read back through `rowReduce`
(`colList H₁`) by `col_decomp`, the coefficients are the entries of the pivot rows, and then the
preimage `preimage` is applied.

## 3. Assembly

$C := C_0 + D$ satisfies both $CH_2 = U$ and $H_1C = R$, so
$v = (CH_2,\, H_1C) = \sum_{a,d}C_{ad}\cdot(\text{row }(a,d)\text{ of }H_Z)$
lies in $\mathrm{row}\,H_Z$ (`sum_smul_hgpHZ_apply` + `mem_spanL_hgpHZ_of_blocks`).

## Main results

* `exists_ker_dot_ne_zero_of_not_mem` / `mem_spanL_of_forall_dot_eq_zero`: the **separation
  lemma**, that the row space is exactly the orthogonal complement of the kernel (realised
  constructively through the elimination residual and a kernel vector).
* `blockL_rows_mem_of_small` / `blockR_cols_mem_of_small`: the two cleaning lemmas.
* `exists_cleaning_cert`: the consistency construction of the cleaning certificate.
* **`hgp_X_distance_ge`**: $v\in\ker H_X$, $v\notin\mathrm{row}H_Z$, $v\ne0$
  $\Longrightarrow \min(d_1, d_2^\top) \le |v|$, the general lower bound for X-type logical
  operators, complementary to the single-block lower bound of the second part (which needs no
  quotient).
-/

@[expose] public section

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {r₁ n₁ r₂ n₂ : ℕ}

/-! ## 1. Row and column lists, and preimages -/

/-- The rows of a matrix, as a list of `Vec`. -/
def matRowList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) : List (Vec k) :=
  List.ofFn fun i => fun j => M i j

/-- The columns of a matrix, as a list of `Vec` (the vector length is the number of rows). -/
def colList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) : List (Vec m) :=
  matRowList M.transpose

lemma mem_matRowList {m k : ℕ} {M : Matrix (Fin m) (Fin k) (ZMod 2)} {y : Vec k} :
    y ∈ matRowList M ↔ ∃ i, (fun j => M i j) = y := by
  rw [matRowList, List.mem_ofFn]

/-- A vector in the column span is the image of right multiplication (the columns are the images
    of the
unit vectors under that map). -/
lemma exists_mulVec_of_mem_spanL_colList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec m} (h : y ∈ spanL (colList M)) : ∃ x : Vec k, M *ᵥ x = y := by
  have h' : y ∈ Submodule.span (ZMod 2) {v : Vec m | v ∈ colList M} := h
  refine Submodule.span_induction (p := fun v _ => ∃ x : Vec k, M *ᵥ x = v)
    ?_ ?_ ?_ ?_ h'
  · intro v hv
    obtain ⟨i, hi⟩ := mem_matRowList.mp hv
    refine ⟨unitVec i, ?_⟩
    funext j
    rw [← congrFun hi j]
    rw [Matrix.mulVec, dotProduct]
    have hsum : (∑ b, M j b * unitVec i b) = M j i := by
      rw [Finset.sum_eq_single i]
      · rw [unitVec, ite_eq_left rfl, mul_one]
      · intro b _ hb
        rw [unitVec, ite_eq_right (fun h : b = i => hb h), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsum]
    exact (Matrix.transpose_apply M i j).symm
  · exact ⟨0, by simp⟩
  · intro x y _ _ hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [Matrix.mulVec_add, ha, hb]⟩
  · intro c x _ hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨c • a, by rw [Matrix.mulVec_smul, ha]⟩

/-- The image of right multiplication lies in the column span. -/
lemma mulVec_mem_spanL_colList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) (x : Vec k) :
    M *ᵥ x ∈ spanL (colList M) := by
  have hsum : M *ᵥ x = ∑ t : Fin k, x t • (fun i => M i t) := by
    funext i
    rw [Matrix.mulVec, dotProduct, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hsum]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
  refine subset_spanL ?_
  rw [colList, matRowList, List.mem_ofFn]
  exact ⟨t, rfl⟩

/-- A vector in the row span is a linear combination of the rows with some coefficient vector:
`∃ λ, ∀ j, Σ_t λ_t M_{tj} = y_j`. -/
lemma exists_coeff_of_mem_spanL_matRowList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec k} (h : y ∈ spanL (matRowList M)) :
    ∃ co : Vec m, ∀ j, (∑ t, co t * M t j) = y j := by
  have h' : y ∈ Submodule.span (ZMod 2) {v : Vec k | v ∈ matRowList M} := h
  refine Submodule.span_induction
    (p := fun v _ => ∃ co : Vec m, ∀ j, (∑ t, co t * M t j) = v j) ?_ ?_ ?_ ?_ h'
  · intro v hv
    obtain ⟨i, hi⟩ := mem_matRowList.mp hv
    refine ⟨unitVec i, fun j => ?_⟩
    rw [← hi]
    have hsum : (∑ t, unitVec i t * M t j) = M i j := by
      rw [Finset.sum_eq_single i]
      · rw [unitVec, ite_eq_left rfl, one_mul]
      · intro b _ hb
        rw [unitVec, ite_eq_right (fun h : b = i => hb h), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsum]
  · exact ⟨0, fun j => by simp⟩
  · intro x y _ _ hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, fun j => ?_⟩
    change (∑ t, (a + b) t * M t j) = x j + y j
    rw [← ha j, ← hb j]
    simp_rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Pi.add_apply, add_mul]
  · intro c x _ hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨c • a, fun j => ?_⟩
    change (∑ t, (c • a) t * M t j) = c • (x j)
    rw [← ha j, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring

/-- The preimage of right multiplication: `M *ᵥ preimage M y = y` whenever `y` lies in the column
span (see `preimage_spec`). -/
noncomputable def preimage {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) (y : Vec m) : Vec k :=
  if h : ∃ x : Vec k, M *ᵥ x = y then Classical.choose h else 0

lemma preimage_spec {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) {y : Vec m}
    (h : ∃ x : Vec k, M *ᵥ x = y) : M *ᵥ preimage M y = y := by
  rw [preimage, dite_eq_left h]
  exact Classical.choose_spec h

/-- **Row decomposition**: if every row of `U` lies in the row space of `M`, then `U = C * M`. -/
lemma exists_mul_eq_of_rows_mem {m k p : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    (U : Matrix (Fin p) (Fin k) (ZMod 2))
    (h : ∀ a, (fun j => U a j) ∈ spanL (matRowList M)) :
    ∃ C : Matrix (Fin p) (Fin m) (ZMod 2), C * M = U := by
  classical
  choose c hc using fun a => exists_coeff_of_mem_spanL_matRowList M (h a)
  refine ⟨Matrix.of fun a t => c a t, ?_⟩
  ext a j
  rw [Matrix.mul_apply]
  simpa only [Matrix.of_apply] using hc a j

/-! ## 2. Separation lemma: the row space is the orthogonal complement of the kernel -/

/-- A kernel vector is orthogonal to the whole row space. -/
lemma dot_eq_zero_of_mem_kerL_of_mem_spanL {n : ℕ} {L : List (Vec n)} {z u : Vec n}
    (hz : z ∈ kerL L) (hu : u ∈ spanL L) : u ⬝ᵥ z = 0 := by
  refine Submodule.span_induction (p := fun u _ => u ⬝ᵥ z = 0) ?_ ?_ ?_ ?_ hu
  · intro v hv
    exact (mem_kerL.mp hz) v hv
  · simp
  · intro x y _ _ hx hy
    rw [add_dotProduct, hx, hy, add_zero]
  · intro c x _ hx
    rw [smul_dotProduct, hx, smul_zero]

/-- **Separation lemma**: a vector outside the row space has nonzero dot product with some kernel
vector.

The construction is explicit: reduce `y` against the output of the elimination, so that the
residual `y'` is nonzero (otherwise `y` would lie in the row space) and vanishes on the pivot
columns; take the free column `j` at which `y'` is nonzero, and `kerVec D j` is the required kernel
vector (it is 1 on the free column `j` and 0 on the other free columns, while `y'` is nonzero only
on free columns). -/
theorem exists_ker_dot_ne_zero_of_not_mem {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec k} (h : y ∉ spanL (matRowList M)) :
    ∃ z : Vec k, M *ᵥ z = 0 ∧ y ⬝ᵥ z ≠ 0 := by
  classical
  set D : List (PivRow k) := rowReduce (matRowList M) with hD
  set y' : Vec k := reduceAgainst D y with hy'
  have hDred : IsReduced D := by rw [hD]; exact isReduced_rowReduce _
  have hy'mem : y + y' ∈ spanL (matRowList M) := by
    rw [hy', hD, ← spanL_rowReduce (matRowList M)]
    exact add_reduceAgainst_mem _ _
  have hy'0 : y' ≠ 0 := by
    intro hzero
    exact h (by rw [hzero, add_zero] at hy'mem; exact hy'mem)
  obtain ⟨j, hj⟩ : ∃ j, y' j ≠ 0 := by
    by_contra hcon
    refine hy'0 (funext fun j => ?_)
    by_contra hc
    exact hcon ⟨j, hc⟩
  have hfree : IsFreeCol D j := by
    by_contra hnf
    have hex : ∃ ri ∈ D, ri.2 = j := by simpa [IsFreeCol] using hnf
    obtain ⟨ri, hri, hrj⟩ := hex
    have hzero := reduceAgainst_apply_piv hDred y ri hri
    rw [hrj] at hzero
    exact hj hzero
  have hker : kerVec D j ∈ kerL (matRowList M) := by
    have h1 : kerVec D j ∈ kerL (rowList D) := kerVec_mem_kerL hDred j
    have h2 : kerL (rowList D) = kerL (matRowList M) := by
      apply kerL_eq_of_spanL_eq
      rw [hD]
      exact spanL_rowReduce (matRowList M)
    rwa [h2] at h1
  refine ⟨kerVec D j, ?_, ?_⟩
  · funext i
    rw [Matrix.mulVec, dotProduct]
    exact (mem_kerL.mp hker) (fun b => M i b) (by
      rw [matRowList, List.mem_ofFn]; exact ⟨i, rfl⟩)
  · intro hzero
    have hsplit : y = y' + (y + y') := by rw [add_add_same_right]
    have hdot : y ⬝ᵥ kerVec D j
        = y' ⬝ᵥ kerVec D j + (y + y') ⬝ᵥ kerVec D j := by
      calc y ⬝ᵥ kerVec D j = (y' + (y + y')) ⬝ᵥ kerVec D j :=
            congrArg (fun u => u ⬝ᵥ kerVec D j) hsplit
        _ = y' ⬝ᵥ kerVec D j + (y + y') ⬝ᵥ kerVec D j := by rw [add_dotProduct]
    have hsecond : (y + y') ⬝ᵥ kerVec D j = 0 :=
      dot_eq_zero_of_mem_kerL_of_mem_spanL hker hy'mem
    have hfirst : y' ⬝ᵥ kerVec D j = y' j := by
      rw [dotProduct]
      refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin k)))
        (f := fun b => y' b * kerVec D j b) j ?_ ?_).trans ?_
      · intro b _ hb
        by_cases hbfree : IsFreeCol D b
        · rw [kerVec_apply_free hbfree, ite_eq_right hb, mul_zero]
        · have hex : ∃ ri ∈ D, ri.2 = b := by simpa [IsFreeCol] using hbfree
          obtain ⟨ri, hri, hrb⟩ := hex
          rw [← hrb, hy', reduceAgainst_apply_piv hDred y ri hri, zero_mul]
      · intro hnot
        exact absurd (Finset.mem_univ j) hnot
      · rw [kerVec_apply_free hfree, ite_eq_left rfl, mul_one]
    rw [hdot, hfirst, hsecond, add_zero] at hzero
    exact hj hzero

/-- **Decidable form of the separation lemma**: a vector orthogonal to the whole kernel lies in the
row space. -/
theorem mem_spanL_of_forall_dot_eq_zero {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec k} (h : ∀ z : Vec k, M *ᵥ z = 0 → y ⬝ᵥ z = 0) :
    y ∈ spanL (matRowList M) := by
  by_contra hmem
  obtain ⟨z, hz, hdot⟩ := exists_ker_dot_ne_zero_of_not_mem M hmem
  exact hdot (h z hz)

/-! ## 3. Weight counting: row-wise and column-wise dot products do not increase the weight -/

/-- The weight after row-wise dot products is at most the weight of the whole vector (every row that
is nonzero contributes one support point). -/
lemma rowDot_hammingNorm_le
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (z : Vec n₂) :
    hammingNorm (fun a : Fin n₁ => ∑ b, v (Sum.inl (a, b)) * z b) ≤ hammingNorm v := by
  classical
  rcases isEmpty_or_nonempty (Fin n₂) with hemp | hne
  · change (Finset.univ.filter (fun a : Fin n₁ => (∑ b, v (Sum.inl (a, b)) * z b) ≠ 0)).card
      ≤ (Finset.univ.filter (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => v c ≠ 0)).card
    have hzero : ∀ a : Fin n₁, (∑ b : Fin n₂, v (Sum.inl (a, b)) * z b) = 0 :=
      fun a => Finset.sum_eq_zero fun b _ => (hemp.false b).elim
    simp only [hzero, ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty,
      Nat.zero_le]
  · obtain ⟨b₀⟩ := hne
    change (Finset.univ.filter (fun a : Fin n₁ => (∑ b, v (Sum.inl (a, b)) * z b) ≠ 0)).card
      ≤ (Finset.univ.filter (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => v c ≠ 0)).card
    let g : Fin n₁ → Fin n₂ := fun a =>
      if h : ∃ b, v (Sum.inl (a, b)) ≠ 0 then Classical.choose h else b₀
    refine Finset.card_le_card_of_injOn
      (fun a => (Sum.inl (a, g a) : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂))) ?_ ?_
    · intro a ha
      have hne : (∑ b, v (Sum.inl (a, b)) * z b) ≠ 0 := (Finset.mem_filter.mp ha).2
      have hex : ∃ b, v (Sum.inl (a, b)) ≠ 0 := by
        by_contra hcon
        exact hne (Finset.sum_eq_zero fun b _ => by
          have hb : v (Sum.inl (a, b)) = 0 := by by_contra hb'; exact hcon ⟨b, hb'⟩
          rw [hb, zero_mul])
      have hg : v (Sum.inl (a, g a)) ≠ 0 := by
        dsimp only [g]
        rw [dite_eq_left hex]
        exact Classical.choose_spec hex
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
    · intro a _ a' _ h
      exact congrArg Prod.fst (Sum.inl_injective h)

/-- The weight after column-wise dot products is at most the weight of the whole vector (every
    column
that is nonzero contributes one support point). -/
lemma colDot_hammingNorm_le
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (w : Vec r₁) :
    hammingNorm (fun t : Fin r₂ => ∑ i, v (Sum.inr (i, t)) * w i) ≤ hammingNorm v := by
  classical
  rcases isEmpty_or_nonempty (Fin r₁) with hemp | hne
  · change (Finset.univ.filter (fun t : Fin r₂ => (∑ i, v (Sum.inr (i, t)) * w i) ≠ 0)).card
      ≤ (Finset.univ.filter (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => v c ≠ 0)).card
    have hzero : ∀ t : Fin r₂, (∑ i : Fin r₁, v (Sum.inr (i, t)) * w i) = 0 :=
      fun t => Finset.sum_eq_zero fun i _ => (hemp.false i).elim
    simp only [hzero, ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty,
      Nat.zero_le]
  · obtain ⟨i₀⟩ := hne
    change (Finset.univ.filter (fun t : Fin r₂ => (∑ i, v (Sum.inr (i, t)) * w i) ≠ 0)).card
      ≤ (Finset.univ.filter (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => v c ≠ 0)).card
    let g : Fin r₂ → Fin r₁ := fun t =>
      if h : ∃ i, v (Sum.inr (i, t)) ≠ 0 then Classical.choose h else i₀
    refine Finset.card_le_card_of_injOn
      (fun t => (Sum.inr (g t, t) : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂))) ?_ ?_
    · intro t ht
      have hne : (∑ i, v (Sum.inr (i, t)) * w i) ≠ 0 := (Finset.mem_filter.mp ht).2
      have hex : ∃ i, v (Sum.inr (i, t)) ≠ 0 := by
        by_contra hcon
        exact hne (Finset.sum_eq_zero fun i _ => by
          have hi : v (Sum.inr (i, t)) = 0 := by by_contra hi'; exact hcon ⟨i, hi'⟩
          rw [hi, zero_mul])
      have hg : v (Sum.inr (g t, t)) ≠ 0 := by
        dsimp only [g]
        rw [dite_eq_left hex]
        exact Classical.choose_spec hex
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
    · intro t _ t' _ h
      exact congrArg Prod.snd (Sum.inr_injective h)

/-! ## 4. The cleaning lemmas -/

/-- **Row cleaning**: if $|v| < d_1$, every row of `blockL v` lies in the row space of `H₂`.

The proof uses the **matrix-level** form of the compression identity: if some row has nonzero dot
product with `z ∈ ker H₂`, then `blockL v *ᵥ z ≠ 0`, whereas
`H₁ *ᵥ (blockL v *ᵥ z) = (H₁ * blockL v) *ᵥ z = (blockR v * H₂) *ᵥ z = blockR v *ᵥ (H₂ *ᵥ z) = 0`,
which contradicts `d₁`. -/
theorem blockL_rows_mem_of_small
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂) {d₁ : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hsmall : hammingNorm v < d₁) (a : Fin n₁) :
    (fun b => blockL v a b) ∈ spanL (matRowList H₂) := by
  refine mem_spanL_of_forall_dot_eq_zero H₂ fun z hz => ?_
  by_contra hne
  let u : Vec n₁ := fun a => ∑ b, blockL v a b * z b
  have hu_eq : u = blockL v *ᵥ z := rfl
  have hxzero : H₁ *ᵥ u = 0 := by
    rw [hu_eq, Matrix.mulVec_mulVec, hcomp, ← Matrix.mulVec_mulVec, hz]
    simp
  have hxne : u ≠ 0 := by
    intro hzero
    refine hne ?_
    rw [dotProduct]
    have h1 : u a = 0 := by rw [hzero]; rfl
    exact h1
  have hge : d₁ ≤ hammingNorm u := hd₁ _ hxne hxzero
  have hle : hammingNorm u ≤ hammingNorm v := rowDot_hammingNorm_le v z
  omega

/-- **Column cleaning**: if $|v| < d_2^\top$, every column of `blockR v` lies in the column space of
`H₁`.

The dual matrix-level argument: the transposed-code identity for `(blockR v)ᵀ *ᵥ w` gives
`H₂ᵀ *ᵥ ((blockR v)ᵀ *ᵥ w) = (blockL v)ᵀ *ᵥ (H₁ᵀ *ᵥ w) = 0`. -/
theorem blockR_cols_mem_of_small
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂) {d₂T : ℕ}
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w)
    (hsmall : hammingNorm v < d₂T) (t : Fin r₂) :
    (fun i => blockR v i t) ∈ spanL (colList H₁) := by
  rw [colList]
  refine mem_spanL_of_forall_dot_eq_zero H₁.transpose fun w hw => ?_
  by_contra hne
  let y : Vec r₂ := fun t => ∑ i, blockR v i t * w i
  have hy_eq : y = (blockR v).transpose *ᵥ w := rfl
  have hyzero : H₂.transpose *ᵥ y = 0 := by
    rw [hy_eq, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← hcomp, Matrix.transpose_mul,
      ← Matrix.mulVec_mulVec, hw]
    simp
  have hyne : y ≠ 0 := by
    intro hzero
    refine hne ?_
    rw [dotProduct]
    have h1 : y t = 0 := by rw [hzero]; rfl
    exact h1
  have hge : d₂T ≤ hammingNorm y := hd₂ _ hyne hyzero
  have hle : hammingNorm y ≤ hammingNorm v := colDot_hammingNorm_le v w
  omega

/-! ## 5. Consistency: column decomposition and the cleaning certificate -/

/-- **Column decomposition** (read back from the elimination): if every column of `M` lies in the
    span
of the row list `c`, the pivot rows of the elimination output give an explicit set of coefficients:
`M i j = Σ_{ri} M ri.2 j * ri.1 i`. -/
lemma col_decomp {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) (c : List (Vec m))
    (hc : ∀ j : Fin k, (fun i => M i j) ∈ spanL c) (i : Fin m) (j : Fin k) :
    M i j = ∑ ri ∈ (rowReduce c).toFinset, (M ri.2 j) * (ri.1 i) := by
  have hmem : (fun i => M i j) ∈ spanL (rowList (rowReduce c)) := by
    rw [spanL_rowReduce]
    exact hc j
  have h := congrFun (readOff_eq_of_mem_spanL (isReduced_rowReduce c) hmem) i
  rw [readOff_apply] at h
  exact h.symm

/-- **Cleaning certificate (consistency)**: a matrix `ρ` whose columns all lie in the column space
    of
`H₁` and which satisfies `ρ H₂ = 0` can be written as `H₁ D` with `D H₂ = 0`, that is, it can be
cleaned.

Construction: `D = Σ_{ri} preimage(ri.1) ⊗ (row ri.2 of ρ)`, where `ri` runs over the pivot rows of
`rowReduce (colList H₁)` (`col_decomp` supplies the coefficients). -/
theorem exists_cleaning_cert {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)} {ρ : Matrix (Fin r₁) (Fin r₂) (ZMod 2)}
    (hcol : ∀ j, (fun i => ρ i j) ∈ spanL (colList H₁))
    (hrow : ρ * H₂ = 0) :
    ∃ D : Matrix (Fin n₁) (Fin r₂) (ZMod 2), H₁ * D = ρ ∧ D * H₂ = 0 := by
  classical
  have hmem : ∀ ri ∈ rowReduce (colList H₁), ri.1 ∈ spanL (colList H₁) := by
    intro ri hri
    have h1 : ri.1 ∈ spanL (rowList (rowReduce (colList H₁))) :=
      subset_spanL (by rw [rowList]; exact List.mem_map_of_mem hri)
    rwa [spanL_rowReduce] at h1
  refine ⟨Matrix.of fun a j => ∑ ri ∈ (rowReduce (colList H₁)).toFinset,
    ρ ri.2 j * (preimage H₁ ri.1) a, ?_, ?_⟩
  · ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner : ∀ ri ∈ (rowReduce (colList H₁)).toFinset,
        (∑ a, H₁ i a * (ρ ri.2 j * (preimage H₁ ri.1) a)) = ρ ri.2 j * ri.1 i := by
      intro ri hri
      have hpre : H₁ *ᵥ preimage H₁ ri.1 = ri.1 :=
        preimage_spec H₁ (exists_mulVec_of_mem_spanL_colList H₁
          (hmem ri (List.mem_toFinset.mp hri)))
      have hstep : (∑ a, H₁ i a * (ρ ri.2 j * (preimage H₁ ri.1) a))
          = ρ ri.2 j * (H₁ *ᵥ preimage H₁ ri.1) i := by
        rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [hstep, hpre]
    rw [Finset.sum_congr rfl hinner]
    exact (col_decomp ρ (colList H₁) hcol i j).symm
  · ext a t
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun ri _ => ?_
    have hstep : (∑ j, (ρ ri.2 j * (preimage H₁ ri.1) a) * H₂ j t)
        = (preimage H₁ ri.1) a * (ρ * H₂) ri.2 t := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hstep, hrow]
    simp

/-! ## 6. Assembly: combinations of the rows of `H_Z`, and the main theorem -/

/-- A vector of the form `(C H₂, H₁ C)` is a linear combination of the rows of `H_Z` (computed
entrywise). -/
theorem sum_smul_hgpHZ_apply (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) (C : Matrix (Fin n₁) (Fin r₂) (ZMod 2))
    (c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂)) :
    (∑ p : Fin n₁ × Fin r₂, C p.1 p.2 • hgpHZ H₁ H₂ p) c
      = Sum.elim (fun ab => (C * H₂) ab.1 ab.2) (fun st => (H₁ * C) st.1 st.2) c := by
  rw [Finset.sum_apply]
  rcases c with ab | st
  · obtain ⟨a, b⟩ := ab
    simp only [Pi.smul_apply, smul_eq_mul, hgpHZ_inl]
    change (∑ p : Fin n₁ × Fin r₂, C p.1 p.2 * ((if p.1 = a then 1 else 0) * H₂ p.2 b))
      = (C * H₂) a b
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hstep : ∀ a' : Fin n₁, (∑ d, C a' d * ((if a' = a then 1 else 0) * H₂ d b))
        = (if a' = a then 1 else 0) * (∑ d, C a' d * H₂ d b) := by
      intro a'
      have hterm : ∀ d : Fin r₂, C a' d * ((if a' = a then 1 else 0) * H₂ d b)
          = (if a' = a then 1 else 0) * (C a' d * H₂ d b) := fun d => by ring
      rw [Finset.sum_congr rfl fun d _ => hterm d, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a' _ => hstep a']
    rw [Finset.sum_eq_single a]
    · rw [ite_eq_left rfl, one_mul]
    · intro a' _ ha'
      rw [ite_eq_right (fun h : a' = a => ha' h), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · obtain ⟨s, t⟩ := st
    simp only [Pi.smul_apply, smul_eq_mul, hgpHZ_inr]
    change (∑ p : Fin n₁ × Fin r₂, C p.1 p.2 * (H₁ s p.1 * (if p.2 = t then 1 else 0)))
      = (H₁ * C) s t
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hstep : ∀ a' : Fin n₁, (∑ d, C a' d * (H₁ s a' * (if d = t then 1 else 0)))
        = H₁ s a' * C a' t := by
      intro a'
      have hterm : ∀ d : Fin r₂, C a' d * (H₁ s a' * (if d = t then 1 else 0))
          = H₁ s a' * (C a' d * (if d = t then 1 else 0)) := fun d => by ring
      rw [Finset.sum_congr rfl fun d _ => hterm d]
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_eq_single t]
      · rw [ite_eq_left rfl, mul_one]
      · intro d _ hd
        rw [ite_eq_right (fun h : d = t => hd h), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ t) h
    rw [Finset.sum_congr rfl fun a' _ => hstep a']

/-- A vector whose two blocks are `C H₂` and `H₁ C` lies in the row space of `H_Z` (the same
    object as
`Matrix.certificateRowSpace` in LeanQEC). -/
theorem mem_rowSpace_hgpHZ_of_blocks {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    {C : Matrix (Fin n₁) (Fin r₂) (ZMod 2)}
    (hU : blockL v = C * H₂) (hR : blockR v = H₁ * C) :
    v ∈ (hgpHZ H₁ H₂).certificateRowSpace := by
  have hv : v = ∑ p : Fin n₁ × Fin r₂, C p.1 p.2 • hgpHZ H₁ H₂ p := by
    funext c
    rw [sum_smul_hgpHZ_apply]
    rcases c with ab | st
    · obtain ⟨a, b⟩ := ab
      rw [← hU]
      rfl
    · obtain ⟨s, t⟩ := st
      rw [← hR]
      rfl
  rw [hv]
  refine Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨p, rfl⟩

/-- **X distance lower bound for the HGP (the cleaning theorem)**: a nonzero X-type operator outside
the row space of `H_Z`, that is a nontrivial X-type logical operator, has weight at least
$\min(d_1, d_2^\top)$, the smaller of the left code distance and the transposed code distance.

This is complementary to the single-block lower bounds of the second part: those need no "outside
the row space" hypothesis, whereas this theorem also covers **mixed blocks** (both blocks nonzero
at once), at the cost of being stated in the quotient. -/
theorem hgp_X_distance_ge (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₁ d₂T : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w) :
    min d₁ d₂T ≤ hammingNorm v := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hcomp : H₁ * blockL v = blockR v * H₂ := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
  have hsmall₁ : hammingNorm v < d₁ := lt_of_lt_of_le hlt (min_le_left _ _)
  have hsmall₂ : hammingNorm v < d₂T := lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨C₀, hC₀⟩ := exists_mul_eq_of_rows_mem H₂ (blockL v)
    (fun a => blockL_rows_mem_of_small hcomp hd₁ hsmall₁ a)
  have hcol : ∀ j, (fun i => (blockR v + H₁ * C₀) i j) ∈ spanL (colList H₁) := by
    intro j
    change ((fun i => blockR v i j) + fun i => (H₁ * C₀) i j) ∈ spanL (colList H₁)
    refine Submodule.add_mem _ ?_ ?_
    · exact blockR_cols_mem_of_small (H₁ := H₁) (H₂ := H₂) hcomp hd₂ hsmall₂ j
    · change H₁ *ᵥ (fun t => C₀ t j) ∈ spanL (colList H₁)
      exact mulVec_mem_spanL_colList H₁ (fun t => C₀ t j)
  have hrowρ : (blockR v + H₁ * C₀) * H₂ = 0 := by
    rw [Matrix.add_mul]
    have h2 : H₁ * C₀ * H₂ = blockR v * H₂ := by
      have hassoc : H₁ * C₀ * H₂ = H₁ * (C₀ * H₂) := by simp only [Matrix.mul_assoc]
      rw [hassoc, hC₀, hcomp]
    rw [h2]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨D, hD₁, hD₂⟩ := exists_cleaning_cert (H₁ := H₁) (H₂ := H₂) hcol hrowρ
  refine hlog ?_
  refine mem_rowSpace_hgpHZ_of_blocks (C := C₀ + D) ?_ ?_
  · rw [Matrix.add_mul, hC₀, hD₂, add_zero]
  · rw [Matrix.mul_add, hD₁]
    have key : ∀ a b : ZMod 2, a + (b + a) = b := by
      intro a b
      rw [add_comm b a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    ext i j
    simp only [Matrix.add_apply]
    exact (key _ _).symm

/-! ## 6. Each of the two premises of the cleaning lower bound **can be dropped**: only one route
    counts

The two steps of the cleaning lower bound `hgp_X_distance_ge` each need a **weight hypothesis**:
row cleaning needs $|v|<d_1$, column cleaning needs $|v|<d_2^\top$. This section shows that **each
step can be replaced by a kernel condition**, leaving the lower bound with a single factor:

* **Row cleaning** (the rows of `blockL v` lie in the row space of $H_2$) holds
  **unconditionally** when $\ker H_1=0$ **or** $\ker H_2=0$. In the first case $H_1$ is
  **injective**: the identity of that step maps $u:=U z$ to $H_1u=0$, so $u=0$. In the second case
  the orthogonality to be proved is **vacuous**, since $\ker H_2$ contains only $0$.
* **Column cleaning** (the columns of `blockR v` lie in the column space of $H_1$) is discharged
  symmetrically by $\ker H_1^\top=0$ (the column space is already full) **or** by
  $\ker H_2^\top=0$ (where $y:=R^\top w$ is pinned to $0$ by $H_2^\top y=0$ together with
  injectivity).

The four distance theorems are the output of this section: the first two give $d_2^\top\le|v|$ (the
factor $d_1$ **does not participate**), the last two give $d_1\le|v|$ ($d_2^\top$ does not
participate). **This is exactly the case in which the certificate kernel of one route is
trivial**: a downstream development uses it to close the "$\ge$" half of C1 on the residual
classes. -/

/-! ### 6.1. Four lemmas on dropping a cleaning step -/

/-- **Row cleaning (branch $\ker H_1=0$)**: when $H_1$ is injective, every row of `blockL v` lies in
the row space of $H_2$ **unconditionally**.

This is isomorphic to `blockL_rows_mem_of_small`, except that the "contradiction with $d_1$" step
is replaced by **injectivity**: the identity of that step already sends $u:=U z$ into $\ker H_1$,
so $u=0$; neither $u\ne 0$ nor a weight hypothesis is needed. -/
theorem blockL_rows_mem_of_H1Ker_trivial
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂)
    (hT : ∀ u : Vec n₁, H₁ *ᵥ u = 0 → u = 0) (a : Fin n₁) :
    (fun b => blockL v a b) ∈ spanL (matRowList H₂) := by
  refine mem_spanL_of_forall_dot_eq_zero H₂ fun z hz => ?_
  have hzero : blockL v *ᵥ z = 0 := hT _ (by
    rw [Matrix.mulVec_mulVec, hcomp, ← Matrix.mulVec_mulVec, hz]
    simp)
  have := congrFun hzero a
  rw [dotProduct]
  exact this

/-- **Row cleaning (branch $\ker H_2=0$)**: when $H_2$ is injective the orthogonality hypothesis is
**vacuous**: the required $\langle U_{a\cdot},z\rangle=0$ is asked only for $z\in\ker H_2$, where
$z=0$ is the only element. (This branch therefore **does not need** the compression identity: the
conclusion mentions only `blockL v` and $H_2$.) -/
theorem blockL_rows_mem_of_H2Ker_trivial
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hT : ∀ u : Vec n₂, H₂ *ᵥ u = 0 → u = 0) (a : Fin n₁) :
    (fun b => blockL v a b) ∈ spanL (matRowList H₂) :=
  mem_spanL_of_forall_dot_eq_zero H₂ fun z hz => by
    rw [hT z hz]
    simp [dotProduct]

/-- **Column cleaning (branch $\ker H_1^\top=0$)**: here the columns of $H_1$ already span the whole
of `Vec r₁`, so the conclusion holds **unconditionally**. (Again the compression identity is **not
needed**.) -/
theorem blockR_cols_mem_of_adjoint_ker_trivial
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hT : ∀ u : Vec r₁, H₁.transpose *ᵥ u = 0 → u = 0) (t : Fin r₂) :
    (fun i => blockR v i t) ∈ spanL (colList H₁) :=
  mem_spanL_of_forall_dot_eq_zero H₁.transpose fun z hz => by
    rw [hT z hz]
    simp [dotProduct]

/-- **Column cleaning (branch $\ker H_2^\top=0$)**: isomorphic to `blockR_cols_mem_of_small`, but
    the
"contradiction with $d_2^\top$" step is replaced by **injectivity**: the identity already sends
$y:=R^\top w$ into $\ker H_2^\top$, so $y=0$. -/
theorem blockR_cols_mem_of_H2TKer_trivial
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂)
    (hT : ∀ u : Vec r₂, H₂.transpose *ᵥ u = 0 → u = 0) (t : Fin r₂) :
    (fun i => blockR v i t) ∈ spanL (colList H₁) := by
  rw [colList]
  refine mem_spanL_of_forall_dot_eq_zero H₁.transpose fun w hw => ?_
  have hyzero : H₂.transpose *ᵥ ((blockR v).transpose *ᵥ w) = 0 := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← hcomp, Matrix.transpose_mul,
      ← Matrix.mulVec_mulVec, hw]
    simp
  have hy := hT _ hyzero
  have hy' : ∀ t, ((blockR v).transpose *ᵥ w) t = 0 := fun t => by
    simpa using congrFun hy t
  rw [dotProduct]
  exact hy' t

/-! ### 6.2. Two assembly theorems, each dropping one step -/

/-- **Cleaning lower bound with row cleaning free**: as soon as the rows of `blockL v` lie in the
    row
space of $H_2$ **unconditionally**, the single factor $d_2^\top$ suffices; the rest is word for
word `hgp_X_distance_ge` (column cleaning still uses $|v|<d_2^\top$). -/
theorem hgp_X_distance_ge_of_rowClean_free
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₂T : ℕ}
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w)
    (hrow : ∀ a, (fun b => blockL v a b) ∈ spanL (matRowList H₂)) :
    d₂T ≤ hammingNorm v := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hcomp : H₁ * blockL v = blockR v * H₂ := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
  obtain ⟨C, hC⟩ := exists_mul_eq_of_rows_mem H₂ (blockL v) hrow
  have hrowρ : (blockR v + H₁ * C) * H₂ = 0 := by
    rw [Matrix.add_mul]
    have h2 : H₁ * C * H₂ = blockR v * H₂ := by
      have hassoc : H₁ * C * H₂ = H₁ * (C * H₂) := by simp only [Matrix.mul_assoc]
      rw [hassoc, hC, hcomp]
    rw [h2]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hcolρ : ∀ j, (fun i => (blockR v + H₁ * C) i j) ∈ spanL (colList H₁) := by
    intro j
    change ((fun i => blockR v i j) + fun i => (H₁ * C) i j) ∈ spanL (colList H₁)
    refine Submodule.add_mem _ ?_ ?_
    · exact blockR_cols_mem_of_small hcomp hd₂ hlt j
    · change H₁ *ᵥ (fun t => C t j) ∈ spanL (colList H₁)
      exact mulVec_mem_spanL_colList H₁ (fun t => C t j)
  obtain ⟨D, hD₁, hD₂⟩ := exists_cleaning_cert (H₁ := H₁) (H₂ := H₂) hcolρ hrowρ
  refine hlog ?_
  refine mem_rowSpace_hgpHZ_of_blocks (C := C + D) ?_ ?_
  · rw [Matrix.add_mul, hC, hD₂, add_zero]
  · rw [Matrix.mul_add, hD₁]
    have key : ∀ a b : ZMod 2, a + (b + a) = b := by
      intro a b
      rw [add_comm b a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    ext i j
    simp only [Matrix.add_apply]
    exact (key _ _).symm

/-- **Cleaning lower bound with column cleaning free**: as soon as the columns of `blockR v` lie in
the column space of $H_1$ **unconditionally**, the single factor $d_1$ suffices (row cleaning still
uses $|v|<d_1$). -/
theorem hgp_X_distance_ge_of_colClean_free
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₁ : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hcol : ∀ t, (fun i => blockR v i t) ∈ spanL (colList H₁)) :
    d₁ ≤ hammingNorm v := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hcomp : H₁ * blockL v = blockR v * H₂ := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
  obtain ⟨C, hC⟩ := exists_mul_eq_of_rows_mem H₂ (blockL v)
    (fun a => blockL_rows_mem_of_small hcomp hd₁ hlt a)
  have hrowρ : (blockR v + H₁ * C) * H₂ = 0 := by
    rw [Matrix.add_mul]
    have h2 : H₁ * C * H₂ = blockR v * H₂ := by
      have hassoc : H₁ * C * H₂ = H₁ * (C * H₂) := by simp only [Matrix.mul_assoc]
      rw [hassoc, hC, hcomp]
    rw [h2]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hcolρ : ∀ j, (fun i => (blockR v + H₁ * C) i j) ∈ spanL (colList H₁) := by
    intro j
    change ((fun i => blockR v i j) + fun i => (H₁ * C) i j) ∈ spanL (colList H₁)
    refine Submodule.add_mem _ ?_ ?_
    · exact hcol j
    · change H₁ *ᵥ (fun t => C t j) ∈ spanL (colList H₁)
      exact mulVec_mem_spanL_colList H₁ (fun t => C t j)
  obtain ⟨D, hD₁, hD₂⟩ := exists_cleaning_cert (H₁ := H₁) (H₂ := H₂) hcolρ hrowρ
  refine hlog ?_
  refine mem_rowSpace_hgpHZ_of_blocks (C := C + D) ?_ ?_
  · rw [Matrix.add_mul, hC, hD₂, add_zero]
  · rw [Matrix.mul_add, hD₁]
    have key : ∀ a b : ZMod 2, a + (b + a) = b := by
      intro a b
      rw [add_comm b a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    ext i j
    simp only [Matrix.add_apply]
    exact (key _ _).symm

/-! ### 6.3. Four distance theorems -/

/-- **Lower bound for $d_X$ (branch $\ker H_1=0$)**: when $H_1$ is injective the single factor
$d_2^\top$ suffices. -/
theorem hgp_X_distance_ge_of_H1Ker_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₂T : ℕ}
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w)
    (hT : ∀ u : Vec n₁, H₁ *ᵥ u = 0 → u = 0) :
    d₂T ≤ hammingNorm v :=
  hgp_X_distance_ge_of_rowClean_free H₁ H₂ hv hlog hd₂ fun a =>
    blockL_rows_mem_of_H1Ker_trivial (H₁ := H₁) (H₂ := H₂)
      ((hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv) hT a

/-- **Lower bound for $d_X$ (branch $\ker H_2=0$)**: when $H_2$ is injective the single factor
$d_2^\top$ suffices. -/
theorem hgp_X_distance_ge_of_H2Ker_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₂T : ℕ}
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w)
    (hT : ∀ u : Vec n₂, H₂ *ᵥ u = 0 → u = 0) :
    d₂T ≤ hammingNorm v :=
  hgp_X_distance_ge_of_rowClean_free H₁ H₂ hv hlog hd₂ fun a =>
    blockL_rows_mem_of_H2Ker_trivial (H₂ := H₂) hT a

/-- **Lower bound for $d_X$ (branch $\ker H_2^\top=0$)**: when $H_2^\top$ is injective the single
    factor
$d_1$ suffices. -/
theorem hgp_X_distance_ge_of_H2TKer_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₁ : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hT : ∀ u : Vec r₂, H₂.transpose *ᵥ u = 0 → u = 0) :
    d₁ ≤ hammingNorm v :=
  hgp_X_distance_ge_of_colClean_free H₁ H₂ hv hlog hd₁ fun t =>
    blockR_cols_mem_of_H2TKer_trivial (H₁ := H₁) (H₂ := H₂)
      ((hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv) hT t

/-- **Lower bound for $d_X$, the branch where the certificate kernel is trivial**: if
$\ker H_1^\top = 0$, then every X-type logical operator has weight $\ge d_1$.

**Which gap this fills**: the cleaning lower bound `hgp_X_distance_ge` gives $\min(d_1,d_2^\top)$,
and $d_2^\top$ may be **strictly smaller yet unattainable**; "the certificate kernel of the right
route is trivial" ($\ker H_1^\top=0$) is exactly that situation. The theorem says that the smaller
value then **does not participate** in the lower bound and $d_1$ alone suffices.

**Proof** (isomorphic to the cleaning lower bound, but using only **row cleaning** plus a
**surjectivity**): suppose $|v|<d_1$. Row cleaning gives $U = C\,H_2$ (where $U$ is `blockL v`), so
the remainder $\rho := R + H_1C$ satisfies $\rho H_2 = 0$. Now $\ker H_1^\top = 0$ together with
the separation lemma `mem_spanL_of_forall_dot_eq_zero` gives that **the columns of $H_1$ are
surjective** (every vector of `Vec r₁` lies in the span of $\mathrm{colList}\,H_1$), so every
column of $\rho$ lies there too. Both conditions are met, and `exists_cleaning_cert` gives $D$ with
$H_1D = \rho$ and $DH_2 = 0$, so `v` and `(C+D)` form a stabilizer and $v$ lies in the row space,
contradicting that $v$ is not a logical operator. -/
theorem hgp_X_distance_ge_of_adjoint_ker_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₁ : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hT : ∀ u : Vec r₁, H₁.transpose *ᵥ u = 0 → u = 0) :
    d₁ ≤ hammingNorm v :=
  hgp_X_distance_ge_of_colClean_free H₁ H₂ hv hlog hd₁ fun t =>
    blockR_cols_mem_of_adjoint_ker_trivial (H₁ := H₁) hT t

end QECCertificates
