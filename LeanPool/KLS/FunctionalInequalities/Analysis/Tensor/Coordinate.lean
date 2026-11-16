/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.Symmetrization
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Partial symmetrization of coordinate tensors

Bizeul–Klartag–Lehec, *Presenting a proof of the Kannan–Lovász–Simonovits conjecture*
(arXiv:2610.05474v1), Lemma 2.2, in the source's coordinates. A real tensor with `k` indices in
`Fin n` is a vector of `Coord n k = EuclideanSpace ℝ (Fin k → Fin n)`, so its norm is the
Hilbert–Schmidt norm of the source. Permuting index positions is an orthogonal representation of
`Perm (Fin k)`, and `S_q` averages over the permutations of the first `q` positions, leaving the
trailing positions fixed. If `3d ≤ k` and a tensor is symmetric in its first `d` indices and in its
next `2d` indices, then `|A| ≤ 4^d |S_{2d} A|`. The dimension `n` is arbitrary, including `0`.
-/

@[expose] public section

noncomputable section

open Finset

namespace FunctionalInequalities.Analysis.Tensor

/-- Real tensors with `k` indices, each ranging over `Fin n`, as a Euclidean space: the norm is the
Hilbert–Schmidt norm `|A| = (∑_{i₁,…,i_k} A_{i₁…i_k}²)^{1/2}` of BKL Section 2. -/
abbrev Coord (n k : ℕ) : Type := EuclideanSpace ℝ (Fin k → Fin n)

/-- The positions `a ≤ p < b` among the `k` index positions. -/
def slots (k a b : ℕ) : Finset (Fin k) :=
  univ.filter fun p => a ≤ p.val ∧ p.val < b

/-- Permuting the index positions of a tensor: `(slotPerm σ A) i = A (i ∘ σ)`. -/
def slotPerm (n k : ℕ) (σ : Equiv.Perm (Fin k)) : Coord n k ≃ₗᵢ[ℝ] Coord n k :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.arrowCongr σ (Equiv.refl (Fin n)))

theorem slotPerm_apply (n k : ℕ) (σ : Equiv.Perm (Fin k)) (A : Coord n k) (i : Fin k → Fin n) :
    slotPerm n k σ A i = A (i ∘ σ) := by
    simp [slotPerm, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft', Equiv.arrowCongr, Function.comp_def]

theorem slotPerm_one (n k : ℕ) : slotPerm n k 1 = 1 := by
    apply LinearIsometryEquiv.ext
    intro A
    apply PiLp.ext
    intro i
    rw [slotPerm_apply]
    simp

theorem slotPerm_mul (n k : ℕ) (σ τ : Equiv.Perm (Fin k)) :
    slotPerm n k (σ * τ) = slotPerm n k σ * slotPerm n k τ := by
    ext A i
    simp [slotPerm_apply, LinearIsometryEquiv.coe_mul, Function.comp_apply,
      Function.comp_assoc]

/-- The orthogonal representation of `Perm (Fin k)` on tensors with `k` indices by permutation of
index positions. -/
def slotRep (n k : ℕ) : Equiv.Perm (Fin k) →* (Coord n k ≃ₗᵢ[ℝ] Coord n k) where
  toFun := slotPerm n k
  map_one' := slotPerm_one n k
  map_mul' := slotPerm_mul n k

/-- `S_q A`: the average of `A` over all permutations of its first `q` indices. -/
def symmetrize (n k q : ℕ) (A : Coord n k) : Coord n k :=
  blockAverage (slotRep n k) (slots k 0 q) A

/-- The number of positions `a ≤ p < b` among `k` positions, for `b ≤ k`. -/
theorem card_slots {k a b : ℕ} (hb : b ≤ k) : (slots k a b).card = b - a := by
    have hmap : (slots k a b).map Fin.valEmbedding = Ico a b := by
      ext x
      constructor
      · intro hx
        rcases mem_map.mp hx with ⟨p, hp, rfl⟩
        apply mem_Ico.mpr
        simpa [slots] using hp
      · intro hx
        have hx' : a ≤ x ∧ x < b := mem_Ico.mp hx
        let p : Fin k := ⟨x, lt_of_lt_of_le hx'.2 hb⟩
        apply mem_map.mpr
        refine ⟨p, ?_, ?_⟩
        · simpa [slots, p] using hx'
        · simp [p]
    calc
      (slots k a b).card = ((slots k a b).map Fin.valEmbedding).card := by simp
      _ = (Ico a b).card := by rw [hmap]
      _ = b - a := by simp

/-- **BKL Lemma 2.2.** Let `d ≥ 0` and let `A` be a tensor with `k ≥ 3d` indices over `Fin n`,
invariant under permutations of its first `d` indices and under permutations of its next `2d`
indices. Then `|A| ≤ 4^d |S_{2d} A|`. Indices beyond the first `3d` are untouched. -/
theorem norm_le_four_pow_mul_norm_symmetrize {n k d : ℕ} (hk : 3 * d ≤ k) (A : Coord n k)
    (h₁ : ∀ σ ∈ fixingOutside (slots k 0 d), slotRep n k σ A = A)
    (h₂ : ∀ σ ∈ fixingOutside (slots k d (3 * d)), slotRep n k σ A = A) :
    ‖A‖ ≤ (4 : ℝ) ^ d * ‖symmetrize n k (2 * d) A‖ := by
    change
      ‖A‖ ≤ (4 : ℝ) ^ d *
        ‖blockAverage (slotRep n k) (slots k 0 (2 * d)) A‖
    have hAcard : (slots k 0 d).card = d := by
      rw [card_slots (k := k) (a := 0) (b := d) (by omega)]
      omega
    have hBcard : (slots k d (3 * d)).card = 2 * d := by
      rw [card_slots (k := k) (a := d) (b := 3 * d) hk]
      omega
    have hQcard : (slots k 0 (2 * d)).card = 2 * d := by
      rw [card_slots (k := k) (a := 0) (b := 2 * d) (by omega)]
      omega
    have hdis : Disjoint (slots k 0 d) (slots k d (3 * d)) := by
      refine Finset.disjoint_left.2 ?_
      intro x hx₁ hx₂
      simp [slots] at hx₁ hx₂
      omega
    have hAQ : slots k 0 d ⊆ slots k 0 (2 * d) := by
      intro x hx
      simp [slots] at hx ⊢
      omega
    have hQ : slots k 0 (2 * d) ⊆ slots k 0 d ∪ slots k d (3 * d) := by
      intro x hx
      simp only [slots, zero_le, true_and, mem_filter, mem_univ, mem_union] at hx ⊢
      by_cases h : x.val < d
      · left
        omega
      · right
        omega
    exact
      norm_le_four_pow_mul_norm_blockAverage
        (ρ := slotRep n k) (A := slots k 0 d) (B := slots k d (3 * d))
        (Q := slots k 0 (2 * d)) (d := d)
        hAcard hBcard hdis hAQ hQ hQcard A h₁ h₂


/-! ### Disjoint copy blocks -/

private theorem blocks_injective {ι κ : Type*} {d : ℕ} (hd : 0 < d) :
    Function.Injective
      (fun p : κ × (Fin d → ι) => fun k => some (p.1, p.2 k)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have hp (k : Fin d) : (i, j k) = (i', j' k) := by
    exact Option.some.inj (congrFun h k)
  have hi : i = i' := by
    exact congrArg (fun q : κ × ι => q.1) (hp ⟨0, hd⟩)
  have hj : j = j' := by
    funext k
    exact congrArg (fun q : κ × ι => q.2) (hp k)
  cases hi
  cases hj
  rfl

section FiniteIndex

variable {ι κ : Type*}
  [Fintype ι] [Fintype κ]

/--
**Disjoint copy blocks** (BKL Proposition 7.1, the Hilbert–Schmidt estimate after (112)). For `d >
0` the map `(i, j) ↦ (fun k => some (i, j k))` is injective,
so the block entries of `A` are a subfamily of all entries. -/
theorem sum_sq_blocks_le {d : ℕ} (hd : 0 < d) (A : (Fin d → Option (κ × ι)) → ℝ) :
    ∑ i : κ, ∑ j : Fin d → ι, A (fun k => some (i, j k)) ^ 2 ≤ ∑ J, A J ^ 2 := by
  classical
  let f : κ × (Fin d → ι) → (Fin d → Option (κ × ι)) := fun p k => some (p.1, p.2 k)
  have hf : Function.Injective f := by
    dsimp [f]
    exact blocks_injective hd
  have hsum :
    (Finset.univ : Finset (κ × (Fin d → ι))).sum (fun p => A (f p) ^ 2) =
      (Finset.univ.image f).sum (fun J => A J ^ 2) := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hf hab
  calc
    ∑ i : κ, ∑ j : Fin d → ι, A (fun k => some (i, j k)) ^ 2 =
        ∑ p : κ × (Fin d → ι), A (f p) ^ 2 := by
      simp only [f, Fintype.sum_prod_type]
    _ = (Finset.univ.image f).sum (fun J => A J ^ 2) := hsum
    _ ≤ (Finset.univ : Finset (Fin d → Option (κ × ι))).sum (fun J => A J ^ 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro J hJ
        simp
      · intro J hJ hJ'
        positivity

/--
If every block entry is `c` times a common array `T`, the block energy `|κ| c² |T|²` is at most
the whole Hilbert–Schmidt energy (the source's use, with `|κ| = N` and `c = d!/(σ√N)`). -/
theorem card_mul_sq_mul_sum_sq_le_of_blocks {d : ℕ} (hd : 0 < d)
    (A : (Fin d → Option (κ × ι)) → ℝ) (c : ℝ) (T : (Fin d → ι) → ℝ)
    (hA : ∀ i j, A (fun k => some (i, j k)) = c * T j) :
    (Fintype.card κ : ℝ) * c ^ 2 * ∑ j, T j ^ 2 ≤ ∑ J, A J ^ 2 := by
  have h := sum_sq_blocks_le hd A
  simp only [hA, mul_pow, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at h
  linarith

end FiniteIndex


/-- **Row contraction** (BKL (101)–(102), at the level of finite arrays): a row bound
`Σ_j (Σ_k v_k T(j,k))² ≤ b Σ_k v_k²` for every `v` gives `Σ_i Σ_j (Σ_k S(i,k) T(j,k))² ≤
b Σ_i Σ_k S(i,k)²` for every array `S`. -/
theorem sum_sq_contract_le {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (T : ρ → κ → ℝ) {b : ℝ}
    (hT : ∀ v : κ → ℝ, ∑ j, (∑ k, v k * T j k) ^ 2 ≤ b * ∑ k, v k ^ 2) (S : ι → κ → ℝ) :
    ∑ i, ∑ j, (∑ k, S i k * T j k) ^ 2 ≤ b * ∑ i, ∑ k, S i k ^ 2 := by
    calc
      ∑ i, ∑ j, (∑ k, S i k * T j k) ^ 2 ≤
          ∑ i, (b * ∑ k, S i k ^ 2) := by
        exact Finset.sum_le_sum (fun i _ => hT (S i))
      _ = b * ∑ i, ∑ k, S i k ^ 2 := by
        rw [Finset.mul_sum]

section WeightedSymmetricSums

/-- **Letwin (2.12), finite form** (arXiv:2607.24164v1, proof of Theorem 2.5, p. 10): for an array
`T` symmetric in its first two indices and weights `b`,
`Σ b_i² T_{ijk}² − Σ b_i b_j T_{ijk}² = ½ Σ (b_i − b_j)² T_{ijk}²`; in particular the left side is
nonnegative. Stated for arbitrary real weights (the source has nonnegative eigenvalues).
-/
theorem sum_weight_sq_mul_sq_sub_eq_half_sum_sq_sub_mul_sq {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (T : ι → ι → ι → ℝ) (hT : ∀ i j k, T i j k = T j i k) :
    (∑ i, ∑ j, ∑ k, (b i) ^ 2 * (T i j k) ^ 2) -
        (∑ i, ∑ j, ∑ k, b i * b j * (T i j k) ^ 2) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k,
        (b i - b j) ^ 2 * (T i j k) ^ 2 := by
  classical
  have hswap : (∑ i, ∑ j, ∑ k, (b j) ^ 2 * (T i j k) ^ 2) =
      ∑ i, ∑ j, ∑ k, (b i) ^ 2 * (T i j k) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hT j i k]
  calc
    _ = (1 / 2 : ℝ) *
        ((∑ i, ∑ j, ∑ k, (b i) ^ 2 * (T i j k) ^ 2) +
         (∑ i, ∑ j, ∑ k, (b j) ^ 2 * (T i j k) ^ 2) -
         2 * (∑ i, ∑ j, ∑ k, b i * b j * (T i j k) ^ 2)) := by rw [hswap]; ring
    _ = _ := by
      congr 1
      simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

end WeightedSymmetricSums

end FunctionalInequalities.Analysis.Tensor
