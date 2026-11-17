/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Perm

/-!
# Partial symmetrization in orthogonal permutation representations

Bizeul–Klartag–Lehec, *Presenting a proof of the Kannan–Lovász–Simonovits conjecture*
(arXiv:2610.05474v1), Lemma 2.2, in the form of an orthogonal representation of a permutation
group. The coordinate-tensor statement of the source is in `Analysis/Tensor/Coordinate.lean`.

Let `ρ` be an orthogonal representation of `Perm Ω` on a real inner product space, `A` and `B`
disjoint sets of positions with `|A| = d`, `|B| = 2d`, and `Q` a set of `2d` positions with
`A ⊆ Q ⊆ A ∪ B` (in the source: the first `d`, the next `2d` and the first `2d` indices). If `v`
is invariant under the permutations supported in `A` and under those supported in `B`, then
`‖v‖ ≤ C(2d, d) ‖S_Q v‖ ≤ 4^d ‖S_Q v‖`, where `S_Q` averages over the permutations supported in
`Q`. The proof is the source's: the subset-sum identity (25) for the translates `T_F`, which
holds for every family of vectors indexed by `d`-subsets, and the identification of each inner
sum with `C(2d, d)` times a translate of `S_Q v`.
-/

@[expose] public section

noncomputable section

open Finset

namespace FunctionalInequalities.Analysis.Tensor

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The permutations of `Ω` fixing every point outside `s`. -/
def fixingOutside (s : Finset Ω) : Finset (Equiv.Perm Ω) :=
  univ.filter fun σ => ∀ x, x ∉ s → σ x = x

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The average of `ρ σ v` over the permutations fixing every point outside `s` (the operator
`S_q` of the source when `s` is the set of the first `q` positions). -/
def blockAverage (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) (s : Finset Ω) (v : V) : V :=
  ((fixingOutside s).card : ℝ)⁻¹ • ∑ σ ∈ fixingOutside s, ρ σ v

section SubsetSum

variable {α : Type*} [DecidableEq α]

/-- The square of the norm of a finite sum is the double sum of inner products. -/
theorem norm_sq_sum_eq_sum_sum_inner {ι : Type*} (s : Finset ι) (x : ι → V) :
    ‖∑ i ∈ s, x i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, inner ℝ (x i) (x j) := by
    calc
      ‖∑ i ∈ s, x i‖ ^ 2 =
          inner ℝ (∑ i ∈ s, x i) (∑ i ∈ s, x i) := by
        exact (real_inner_self_eq_norm_sq _).symm
      _ = ∑ i ∈ s, inner ℝ (x i) (∑ j ∈ s, x j) := by
        rw [sum_inner]
      _ = ∑ i ∈ s, ∑ j ∈ s, inner ℝ (x i) (x j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [inner_sum]

/-- Counting supersets: for `d`-subsets `F, F'` of a set `U` with `3d` elements, the number of
`2d`-subsets of `U` containing `F ∪ F'` is `C(d + |F ∩ F'|, d)`. -/
theorem card_filter_union_subset (U : Finset α) {d : ℕ} (hU : U.card = 3 * d) {F F' : Finset α}
    (hF : F ∈ U.powersetCard d) (hF' : F' ∈ U.powersetCard d) :
    ((U.powersetCard (2 * d)).filter fun E => F ∪ F' ⊆ E).card =
      (d + (F ∩ F').card).choose d := by
    classical
    have hFsub : F ⊆ U := (mem_powersetCard.mp hF).1
    have hF'sub : F' ⊆ U := (mem_powersetCard.mp hF').1
    have hFcard : F.card = d := (mem_powersetCard.mp hF).2
    have hF'card : F'.card = d := (mem_powersetCard.mp hF').2
    let K := F ∪ F'
    let r := (F ∩ F').card
    have hKsub : K ⊆ U := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hFsub hx
      · exact hF'sub hx
    have hKcard : K.card = 2 * d - r := by
      have h := Finset.card_union_add_card_inter F F'
      dsimp [K, r]
      omega
    have hrle : r ≤ d := by
      have hi : (F ∩ F').card ≤ F.card :=
        Finset.card_le_card inter_subset_left
      dsimp [r]
      omega
    have hdiffcard : (U \ K).card = d + r := by
      have hc : (U \ K).card = U.card - (K ∩ U).card :=
        Finset.card_sdiff
      rw [inter_eq_left.mpr hKsub, hU, hKcard] at hc
      omega
    let S := (U.powersetCard (2 * d)).filter fun E => K ⊆ E
    let T := (U \ K).powersetCard r
    have hcard : S.card = T.card := by
      apply Finset.card_bij (fun E _ => E \ K)
      · intro E hE
        have hEp : E ∈ U.powersetCard (2 * d) :=
          (mem_filter.mp hE).1
        have hEK : K ⊆ E :=
          (mem_filter.mp hE).2
        apply mem_powersetCard.mpr
        constructor
        · intro x hx
          have hxE : x ∈ E := (Finset.mem_sdiff.mp hx).1
          have hxK : x ∉ K := (Finset.mem_sdiff.mp hx).2
          exact Finset.mem_sdiff.mpr
            ⟨(mem_powersetCard.mp hEp).1 hxE, hxK⟩
        · have hc : (E \ K).card = E.card - (K ∩ E).card :=
            Finset.card_sdiff
          rw [inter_eq_left.mpr hEK, (mem_powersetCard.mp hEp).2, hKcard] at hc
          omega
      · intro E hE E' hE' heq
        have hEK : K ⊆ E := (mem_filter.mp hE).2
        have hE'K : K ⊆ E' := (mem_filter.mp hE').2
        have h₁ : (E \ K) ∪ K = E := by
          ext x
          by_cases hx : x ∈ K
          · simp [hx, hEK hx]
          · simp [hx]
        have h₂ : (E' \ K) ∪ K = E' := by
          ext x
          by_cases hx : x ∈ K
          · simp [hx, hE'K hx]
          · simp [hx]
        rw [← h₁, ← h₂, heq]
      · intro X hX
        have hXp : X ∈ (U \ K).powersetCard r := hX
        have hXsub : X ⊆ U \ K :=
          (mem_powersetCard.mp hXp).1
        have hXKsub : X ∪ K ⊆ U := by
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact (Finset.mem_sdiff.mp (hXsub hx)).1
          · exact hKsub hx
        have hXdis : Disjoint X K := by
          rw [Finset.disjoint_left]
          intro x hxX hxK
          exact (Finset.mem_sdiff.mp (hXsub hxX)).2 hxK
        have hXKcard : (X ∪ K).card = 2 * d := by
          have hc := Finset.card_union_of_disjoint hXdis
          rw [(mem_powersetCard.mp hXp).2, hKcard] at hc
          omega
        refine ⟨X ∪ K, ?_, ?_⟩
        · apply mem_filter.mpr
          constructor
          · exact mem_powersetCard.mpr ⟨hXKsub, hXKcard⟩
          · exact Finset.subset_union_right
        · ext x
          by_cases hxK : x ∈ K
          · have hxnot : x ∉ X := by
              intro hxX
              exact (Finset.mem_sdiff.mp (hXsub hxX)).2 hxK
            simp [hxK, hxnot]
          · simp [hxK]
    calc
      ((U.powersetCard (2 * d)).filter fun E => F ∪ F' ⊆ E).card = S.card := by
        rfl
      _ = T.card := hcard
      _ = (U \ K).card.choose r := by
        simp [T]
      _ = (d + r).choose r := by
        rw [hdiffcard]
      _ = (d + r).choose d := by
        simpa [Nat.add_comm] using (@Nat.choose_symm_add r d)

private theorem sum_choose_mul_choose (d r : ℕ) :
    ∑ s ∈ range (d + 1), d.choose s * r.choose s = (d + r).choose d := by
  have hv := Nat.add_choose_eq d r d
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  have hv' :
      (d + r).choose d =
        ∑ s ∈ range (d + 1), d.choose s * r.choose (d - s) := by
    simpa using hv
  let f : ℕ → ℕ := fun s => d.choose s * r.choose s
  have hr :
      (∑ s ∈ range (d + 1), f s) =
        ∑ s ∈ range (d + 1), f (d - s) := by
    have h := Finset.sum_range_reflect (f := f) (n := d + 1)
    simpa using h.symm
  calc
    ∑ s ∈ range (d + 1), d.choose s * r.choose s =
        ∑ s ∈ range (d + 1), d.choose (d - s) * r.choose (d - s) := by
          simpa [f] using hr
    _ = ∑ s ∈ range (d + 1), d.choose s * r.choose (d - s) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs' : s ≤ d := by
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hs)
      rw [Nat.choose_symm hs']
    _ = (d + r).choose d := hv'.symm

/-- Counting subsets with Vandermonde's identity: for `d`-subsets `F, F'` of `U`,
`∑_{s ≤ d} C(d, s) · #{S ⊆ U : |S| = s, S ⊆ F ∩ F'} = C(d + |F ∩ F'|, d)`. -/
theorem sum_choose_mul_card_filter_subset (U : Finset α) {d : ℕ} {F F' : Finset α}
    (hF : F ∈ U.powersetCard d) (hF' : F' ∈ U.powersetCard d) :
    ∑ s ∈ range (d + 1), d.choose s * ((U.powersetCard s).filter fun S => S ⊆ F ∩ F').card =
      (d + (F ∩ F').card).choose d := by
    have hFU : F ⊆ U := (Finset.mem_powersetCard.mp hF).1
    have hF'U : F' ⊆ U := (Finset.mem_powersetCard.mp hF').1
    have hInterU : F ∩ F' ⊆ U := inter_subset_left.trans hFU
    have hcard (s : ℕ) :
        ((U.powersetCard s).filter (fun S => S ⊆ F ∩ F')).card =
          (F ∩ F').card.choose s := by
      have heq :
          (U.powersetCard s).filter (fun S => S ⊆ F ∩ F') =
            (F ∩ F').powersetCard s := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨_, hS⟩, hsubset⟩
          exact ⟨hsubset, hS⟩
        · rintro ⟨hsubset, hS⟩
          exact ⟨⟨hsubset.trans hInterU, hS⟩, hsubset⟩
      rw [heq, Finset.card_powersetCard]
    simp_rw [hcard]
    exact sum_choose_mul_choose d (F ∩ F').card

/--
Expanding squared norms of filtered sums: for a family `𝓔`, a finite index set `P` and a relation
`r`, `∑_{E ∈ 𝓔} ‖∑_{F ∈ P, r F E} x_F‖² = ∑_{F, F' ∈ P} #{E ∈ 𝓔 : r F E ∧ r F' E} ⟪x_F, x_F'⟫`. -/
theorem sum_norm_sq_sum_filter {β ι : Type*} (𝓔 : Finset β) (P : Finset ι) (r : ι → β → Prop)
    [∀ F E, Decidable (r F E)] (x : ι → V) :
    ∑ E ∈ 𝓔, ‖∑ F ∈ P.filter (fun F => r F E), x F‖ ^ 2 =
      ∑ F ∈ P, ∑ F' ∈ P, ((𝓔.filter fun E => r F E ∧ r F' E).card : ℝ) * inner ℝ (x F) (x F') := by
  classical
    calc
    ∑ E ∈ 𝓔, ‖∑ F ∈ P.filter (fun F => r F E), x F‖ ^ 2 =
        ∑ E ∈ 𝓔, ∑ F ∈ P, ∑ F' ∈ P, if r F E ∧ r F' E then inner ℝ (x F) (x F') else 0 := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [norm_sq_sum_eq_sum_sum_inner]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro F hF
      by_cases h : r F E
      · simp only [h, ↓reduceIte]
        apply Finset.sum_congr rfl
        intro F' hF'
        by_cases h' : r F' E <;> simp [h']
      · simp [h]
    _ = ∑ F ∈ P, ∑ E ∈ 𝓔, ∑ F' ∈ P, if r F E ∧ r F' E then inner ℝ (x F) (x F') else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ F ∈ P, ∑ F' ∈ P, ∑ E ∈ 𝓔, if r F E ∧ r F' E then inner ℝ (x F) (x F') else 0 := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [Finset.sum_comm]
    _ =
        ∑ F ∈ P,
          ∑ F' ∈ P, ((𝓔.filter (fun E => r F E ∧ r F' E)).card : ℝ) * inner ℝ (x F) (x F') := by
      apply Finset.sum_congr rfl
      intro F hF
      apply Finset.sum_congr rfl
      intro F' hF'
      rw [← Finset.sum_filter]
      simp [nsmul_eq_mul]

/-- For `E ⊆ U`, the `d`-subsets of `E` are the `d`-subsets of `U` contained in `E`. -/
theorem powersetCard_eq_filter_subset {U E : Finset α} (hE : E ⊆ U) (d : ℕ) :
    E.powersetCard d = (U.powersetCard d).filter (· ⊆ E) := by
    ext F
    simp only [Finset.mem_powersetCard, Finset.mem_filter]
    constructor
    · rintro ⟨hFE, hcard⟩
      exact ⟨⟨Finset.Subset.trans hFE hE, hcard⟩, hFE⟩
    · rintro ⟨⟨hFU, hcard⟩, hFE⟩
      exact ⟨hFE, hcard⟩

/-- **BKL (25), equality.** For any family `x` of vectors indexed by the `d`-subsets of a set
`U` with `3d` elements,
`∑_{|E| = 2d} ‖∑_{F ⊆ E} x_F‖² = ∑_{s=0}^{d} C(d, s) ∑_{|S| = s} ‖∑_{S ⊆ F} x_F‖²`,
all subsets being subsets of `U` and `F` ranging over `d`-subsets. -/
theorem sum_norm_sq_sum_subset_eq (U : Finset α) {d : ℕ} (hU : U.card = 3 * d)
    (x : Finset α → V) :
    ∑ E ∈ U.powersetCard (2 * d), ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2 =
      ∑ s ∈ range (d + 1), (d.choose s : ℝ) *
        ∑ S ∈ U.powersetCard s, ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2 := by
    classical
    let P := U.powersetCard d
    let Q := U.powersetCard (2 * d)
    have hL :
        (∑ E ∈ Q, ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2) =
          ∑ F ∈ P, ∑ F' ∈ P,
            ((d + (F ∩ F').card).choose d : ℝ) *
              inner ℝ (x F) (x F') := by
      calc
        (∑ E ∈ Q, ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2) =
            ∑ E ∈ Q, ‖∑ F ∈ P.filter (fun F => F ⊆ E), x F‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro E hE
              rw [powersetCard_eq_filter_subset
                ((Finset.mem_powersetCard.mp hE).1) d]
        _ = ∑ F ∈ P, ∑ F' ∈ P,
            ((Q.filter fun E => F ⊆ E ∧ F' ⊆ E).card : ℝ) *
              inner ℝ (x F) (x F') := by
              exact sum_norm_sq_sum_filter Q P (fun F E => F ⊆ E) x
        _ = ∑ F ∈ P, ∑ F' ∈ P,
            ((d + (F ∩ F').card).choose d : ℝ) *
              inner ℝ (x F) (x F') := by
              apply Finset.sum_congr rfl
              intro F hF
              apply Finset.sum_congr rfl
              intro F' hF'
              have hu :
                  Q.filter (fun E => F ⊆ E ∧ F' ⊆ E) =
                    Q.filter (fun E => F ∪ F' ⊆ E) := by
                ext E
                simp [Finset.union_subset_iff]
              rw [hu, card_filter_union_subset U hU hF hF']
    have hS (s : ℕ) :
        (∑ S ∈ U.powersetCard s,
            ‖∑ F ∈ P.filter (fun F => S ⊆ F), x F‖ ^ 2) =
          ∑ F ∈ P, ∑ F' ∈ P,
            (((U.powersetCard s).filter
                (fun S => S ⊆ F ∩ F')).card : ℝ) *
              inner ℝ (x F) (x F') := by
      calc
        (∑ S ∈ U.powersetCard s,
            ‖∑ F ∈ P.filter (fun F => S ⊆ F), x F‖ ^ 2) =
            ∑ F ∈ P, ∑ F' ∈ P,
              (((U.powersetCard s).filter
                  (fun S => S ⊆ F ∧ S ⊆ F')).card : ℝ) *
                inner ℝ (x F) (x F') := by
              exact sum_norm_sq_sum_filter
                (U.powersetCard s) P (fun F S => S ⊆ F) x
        _ = ∑ F ∈ P, ∑ F' ∈ P,
            (((U.powersetCard s).filter
                (fun S => S ⊆ F ∩ F')).card : ℝ) *
              inner ℝ (x F) (x F') := by
              apply Finset.sum_congr rfl
              intro F hF
              apply Finset.sum_congr rfl
              intro F' hF'
              have hi :
                  (U.powersetCard s).filter
                      (fun S => S ⊆ F ∧ S ⊆ F') =
                    (U.powersetCard s).filter
                      (fun S => S ⊆ F ∩ F') := by
                ext S
                simp [Finset.subset_inter_iff]
              rw [hi]
    have hcoef {F F' : Finset α} (hF : F ∈ P) (hF' : F' ∈ P) :
        ∑ s ∈ range (d + 1), (d.choose s : ℝ) *
            (((U.powersetCard s).filter
                (fun S => S ⊆ F ∩ F')).card : ℝ) =
          ((d + (F ∩ F').card).choose d : ℝ) := by
      exact_mod_cast sum_choose_mul_card_filter_subset U hF hF'
    have hR :
        (∑ s ∈ range (d + 1), (d.choose s : ℝ) *
          ∑ S ∈ U.powersetCard s,
            ‖∑ F ∈ P.filter (fun F => S ⊆ F), x F‖ ^ 2) =
          ∑ F ∈ P, ∑ F' ∈ P,
            ((d + (F ∩ F').card).choose d : ℝ) *
              inner ℝ (x F) (x F') := by
      calc
        (∑ s ∈ range (d + 1), (d.choose s : ℝ) *
          ∑ S ∈ U.powersetCard s,
            ‖∑ F ∈ P.filter (fun F => S ⊆ F), x F‖ ^ 2) =
            ∑ s ∈ range (d + 1), (d.choose s : ℝ) *
              (∑ F ∈ P, ∑ F' ∈ P,
                (((U.powersetCard s).filter
                    (fun S => S ⊆ F ∩ F')).card : ℝ) *
                  inner ℝ (x F) (x F')) := by
              apply Finset.sum_congr rfl
              intro s hs
              rw [hS s]
        _ = ∑ F ∈ P, ∑ F' ∈ P,
            (∑ s ∈ range (d + 1), (d.choose s : ℝ) *
              (((U.powersetCard s).filter
                  (fun S => S ⊆ F ∩ F')).card : ℝ)) *
                inner ℝ (x F) (x F') := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro F hF
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro F' hF'
              simp_rw [← mul_assoc]
              rw [← Finset.sum_mul]
        _ = ∑ F ∈ P, ∑ F' ∈ P,
            ((d + (F ∩ F').card).choose d : ℝ) *
              inner ℝ (x F) (x F') := by
              apply Finset.sum_congr rfl
              intro F hF
              apply Finset.sum_congr rfl
              intro F' hF'
              rw [hcoef hF hF']
    exact hL.trans hR.symm

omit [DecidableEq α] in
/-- **BKL (25), inequality.** Under the same assumptions,
`∑_{|F| = d} ‖x_F‖² ≤ ∑_{|E| = 2d} ‖∑_{F ⊆ E} x_F‖²`. -/
theorem sum_norm_sq_le_sum_norm_sq_sum_subset (U : Finset α) {d : ℕ} (hU : U.card = 3 * d)
    (x : Finset α → V) :
    ∑ F ∈ U.powersetCard d, ‖x F‖ ^ 2 ≤
      ∑ E ∈ U.powersetCard (2 * d), ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2 := by
  classical
    have hfilter (S : Finset α) (hS : S ∈ U.powersetCard d) :
        (U.powersetCard d).filter (S ⊆ ·) = {S} := by
      ext F
      constructor
      · intro hF
        have hFU : F ∈ U.powersetCard d := (mem_filter.mp hF).1
        have hSF : S ⊆ F := (mem_filter.mp hF).2
        have hScard : S.card = d := (Finset.mem_powersetCard.mp hS).2
        have hFcard : F.card = d := (Finset.mem_powersetCard.mp hFU).2
        have hEq : S = F :=
          Finset.eq_of_subset_of_card_le hSF (by omega)
        simp [hEq]
      · intro hF
        have hEq : F = S := by simpa using hF
        subst F
        exact mem_filter.mpr ⟨hS, subset_rfl⟩
    have hinner :
        (∑ S ∈ U.powersetCard d,
            ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2) =
          ∑ S ∈ U.powersetCard d, ‖x S‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      rw [hfilter S hS]
      simp
    have hbase :
        (∑ F ∈ U.powersetCard d, ‖x F‖ ^ 2) =
          (d.choose d : ℝ) *
            ∑ S ∈ U.powersetCard d,
              ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2 := by
      simp [hinner]
    have hnonneg :
        ∀ s ∈ range (d + 1),
          0 ≤ (d.choose s : ℝ) *
            ∑ S ∈ U.powersetCard s,
              ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2 := by
      intro s hs
      apply mul_nonneg
      · exact_mod_cast Nat.zero_le (d.choose s)
      · apply Finset.sum_nonneg
        intro S hS
        exact sq_nonneg _
    calc
      ∑ F ∈ U.powersetCard d, ‖x F‖ ^ 2 =
          (d.choose d : ℝ) *
            ∑ S ∈ U.powersetCard d,
              ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2 := hbase
      _ ≤ ∑ s ∈ range (d + 1), (d.choose s : ℝ) *
            ∑ S ∈ U.powersetCard s,
              ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2 :=
        Finset.single_le_sum (fun s hs => hnonneg s hs)
          (mem_range.mpr (Nat.lt_succ_self d))
      _ = ∑ E ∈ U.powersetCard (2 * d),
            ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2 :=
        (sum_norm_sq_sum_subset_eq U hU x).symm

end SubsetSum

/-- Two subsets of `W` with the same cardinality are related by a permutation fixing every point
outside `W`. -/
theorem exists_mem_fixingOutside_image_eq {W s t : Finset Ω} (hs : s ⊆ W) (ht : t ⊆ W)
    (hst : s.card = t.card) : ∃ σ ∈ fixingOutside W, s.image σ = t := by
    classical
    have hcard : (W \ s).card = (W \ t).card := by
      rw [card_sdiff_of_subset hs, card_sdiff_of_subset ht, hst]
    let e₁ : {x // x ∈ s} ≃ {x // x ∈ t} :=
      Fintype.equivOfCardEq (by
        simpa only [Fintype.card_coe] using hst)
    let e₂ : {x // x ∈ W \ s} ≃ {x // x ∈ W \ t} :=
      Fintype.equivOfCardEq (by
        simpa only [Fintype.card_coe] using hcard)
    let f : Ω → Ω := fun x =>
      if hx : x ∈ s then
        (e₁ ⟨x, hx⟩ : Ω)
      else if hx : x ∈ W \ s then
        (e₂ ⟨x, hx⟩ : Ω)
      else x
    let g : Ω → Ω := fun x =>
      if hx : x ∈ t then
        (e₁.symm ⟨x, hx⟩ : Ω)
      else if hx : x ∈ W \ t then
        (e₂.symm ⟨x, hx⟩ : Ω)
      else x
    have hf_s : ∀ (x : Ω) (hx : x ∈ s),
        f x = (e₁ ⟨x, hx⟩ : Ω) := by
      intro x hx
      simp only [f, dite_eq_left hx]
    have hf_ws : ∀ (x : Ω) (hx : x ∈ W \ s),
        f x = (e₂ ⟨x, hx⟩ : Ω) := by
      intro x hx
      have hxs : x ∉ s := (Finset.mem_sdiff.mp hx).2
      simp only [f, dite_eq_right hxs, dite_eq_left hx]
    have hf_out : ∀ (x : Ω) (hx : x ∉ W), f x = x := by
      intro x hx
      have hxs : x ∉ s := fun h => hx (hs h)
      have hws : x ∉ W \ s := by
        intro h
        exact hx (Finset.mem_sdiff.mp h).1
      simp only [f, dite_eq_right hxs, dite_eq_right hws]
    have hg_t : ∀ (x : Ω) (hx : x ∈ t),
        g x = (e₁.symm ⟨x, hx⟩ : Ω) := by
      intro x hx
      simp only [g, dite_eq_left hx]
    have hg_wt : ∀ (x : Ω) (hx : x ∈ W \ t),
        g x = (e₂.symm ⟨x, hx⟩ : Ω) := by
      intro x hx
      have hxt : x ∉ t := (Finset.mem_sdiff.mp hx).2
      simp only [g, dite_eq_right hxt, dite_eq_left hx]
    have hg_out : ∀ (x : Ω) (hx : x ∉ W), g x = x := by
      intro x hx
      have hxt : x ∉ t := fun h => hx (ht h)
      have hwt : x ∉ W \ t := by
        intro h
        exact hx (Finset.mem_sdiff.mp h).1
      simp only [g, dite_eq_right hxt, dite_eq_right hwt]
    have hfg : ∀ x, g (f x) = x := by
      intro x
      by_cases hxs : x ∈ s
      · have hfx : f x = (e₁ ⟨x, hxs⟩ : Ω) := hf_s x hxs
        have he : (e₁ ⟨x, hxs⟩ : Ω) ∈ t :=
          (e₁ ⟨x, hxs⟩).property
        calc
          g (f x) = g (e₁ ⟨x, hxs⟩ : Ω) := congrArg g hfx
          _ = (e₁.symm (e₁ ⟨x, hxs⟩) : Ω) := by
            simpa using hg_t (e₁ ⟨x, hxs⟩ : Ω) he
          _ = x := by
            simp
      · by_cases hws : x ∈ W \ s
        · have hfx : f x = (e₂ ⟨x, hws⟩ : Ω) := hf_ws x hws
          have he : (e₂ ⟨x, hws⟩ : Ω) ∈ W \ t :=
            (e₂ ⟨x, hws⟩).property
          calc
            g (f x) = g (e₂ ⟨x, hws⟩ : Ω) := congrArg g hfx
            _ = (e₂.symm (e₂ ⟨x, hws⟩) : Ω) := by
              simpa using hg_wt (e₂ ⟨x, hws⟩ : Ω) he
            _ = x := by
              simp
        · have hxW : x ∉ W := by
            intro hx
            exact hws (Finset.mem_sdiff.mpr ⟨hx, hxs⟩)
          calc
            g (f x) = g x := congrArg g (hf_out x hxW)
            _ = x := hg_out x hxW
    have hgf : ∀ x, f (g x) = x := by
      intro x
      by_cases hxt : x ∈ t
      · have hgx : g x = (e₁.symm ⟨x, hxt⟩ : Ω) := hg_t x hxt
        have he : (e₁.symm ⟨x, hxt⟩ : Ω) ∈ s :=
          (e₁.symm ⟨x, hxt⟩).property
        calc
          f (g x) = f (e₁.symm ⟨x, hxt⟩ : Ω) := congrArg f hgx
          _ = (e₁ (e₁.symm ⟨x, hxt⟩) : Ω) := by
            simpa using hf_s (e₁.symm ⟨x, hxt⟩ : Ω) he
          _ = x := by
            simp
      · by_cases hwt : x ∈ W \ t
        · have hgx : g x = (e₂.symm ⟨x, hwt⟩ : Ω) := hg_wt x hwt
          have he : (e₂.symm ⟨x, hwt⟩ : Ω) ∈ W \ s :=
            (e₂.symm ⟨x, hwt⟩).property
          calc
            f (g x) = f (e₂.symm ⟨x, hwt⟩ : Ω) := congrArg f hgx
            _ = (e₂ (e₂.symm ⟨x, hwt⟩) : Ω) := by
              simpa using hf_ws (e₂.symm ⟨x, hwt⟩ : Ω) he
            _ = x := by
              simp
        · have hxW : x ∉ W := by
            intro hx
            exact hwt (Finset.mem_sdiff.mpr ⟨hx, hxt⟩)
          calc
            f (g x) = f x := congrArg f (hg_out x hxW)
            _ = x := hf_out x hxW
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        calc
          x = g (f x) := (hfg x).symm
          _ = g (f y) := congrArg g hxy
          _ = y := hfg y
      · intro y
        exact ⟨g y, hgf y⟩
    let σ : Equiv.Perm Ω := Equiv.ofBijective f hf
    refine ⟨σ, ?_, ?_⟩
    · simp only [fixingOutside, mem_filter, mem_univ, true_and]
      intro x hx
      change f x = x
      exact hf_out x hx
    · have hsub : s.image σ ⊆ t := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        change f y ∈ t
        rw [hf_s y hy]
        exact (e₁ ⟨y, hy⟩).property
      have hcard_image : (s.image σ).card = s.card := by
        rw [Finset.card_image_iff]
        intro a ha b hb hab
        exact σ.injective hab
      apply Finset.eq_of_subset_of_card_le hsub
      rw [hcard_image, hst]

/-- If `v` is invariant under the permutations supported in `A` and in `B` (disjoint), then
`ρ σ v` for `σ` fixing everything outside `A ∪ B` depends only on the image `σ(A)`. -/
theorem apply_eq_of_image_eq (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) {A B : Finset Ω} (v : V)
    (hvA : ∀ σ ∈ fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ fixingOutside B, ρ σ v = v)
    {σ τ : Equiv.Perm Ω} (hσ : σ ∈ fixingOutside (A ∪ B)) (hτ : τ ∈ fixingOutside (A ∪ B))
    (h : A.image σ = A.image τ) : ρ σ v = ρ τ v := by
    let π : Equiv.Perm Ω := τ⁻¹ * σ
    have hπ : π ∈ fixingOutside (A ∪ B) := by
      simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ hτ ⊢
      intro x hx
      have hs : σ x = x := hσ x hx
      have ht : τ x = x := hτ x hx
      have hti : τ⁻¹ x = x := by
        apply τ.injective
        calc
          τ (τ⁻¹ x) = x := τ.apply_symm_apply x
          _ = τ x := ht.symm
      change τ⁻¹ (σ x) = x
      rw [hs, hti]
    have hπfix : ∀ x, x ∉ A ∪ B → π x = x := by
      simpa [fixingOutside] using hπ
    have hA : ∀ x, x ∈ A ↔ π x ∈ A := by
      intro x
      constructor
      · intro hx
        have htx : σ x ∈ A.image τ := by
          rw [← h]
          exact mem_image_of_mem σ hx
        rcases mem_image.mp htx with ⟨y, hy, hxy⟩
        have hπxy : π x = y := by
          apply τ.injective
          calc
            τ (π x) = σ x := by simp [π]
            _ = τ y := hxy.symm
        rw [hπxy]
        exact hy
      · intro hx
        have hst : σ x ∈ A.image τ := by
          have hxy : σ x = τ (π x) := by simp [π]
          rw [hxy]
          exact mem_image_of_mem τ hx
        have hss : σ x ∈ A.image σ := by
          rw [h]
          exact hst
        rcases mem_image.mp hss with ⟨y, hy, hxy⟩
        have hyx : y = x := σ.injective hxy
        simpa [hyx] using hy
    have hA' : ∀ x, π x ∈ A ↔ x ∈ A := fun x => (hA x).symm
    let α : Equiv.Perm Ω := Equiv.Perm.ofSubtype (π.subtypePerm hA')
    have hαA : ∀ x, x ∈ A → α x = π x := by
      intro x hx
      change (Equiv.Perm.ofSubtype (π.subtypePerm hA')) x = π x
      exact Equiv.Perm.ofSubtype_apply_of_mem (π.subtypePerm hA') hx
    have hαnot : ∀ x, x ∉ A → α x = x := by
      intro x hx
      change (Equiv.Perm.ofSubtype (π.subtypePerm hA')) x = x
      exact Equiv.Perm.ofSubtype_apply_of_not_mem (π.subtypePerm hA') hx
    have hα : α ∈ fixingOutside A := by
      simp only [fixingOutside, mem_filter, mem_univ, true_and]
      intro x hx
      exact hαnot x hx
    let β : Equiv.Perm Ω := α⁻¹ * π
    have hβ : β ∈ fixingOutside B := by
      simp only [fixingOutside, mem_filter, mem_univ, true_and]
      intro x hxB
      by_cases hxA : x ∈ A
      · have hπxA : π x ∈ A := (hA x).mp hxA
        have hi : α⁻¹ (π x) = x := by
          apply α.injective
          calc
            α (α⁻¹ (π x)) = π x := α.apply_symm_apply (π x)
            _ = α x := (hαA x hxA).symm
        change α⁻¹ (π x) = x
        exact hi
      · have hxU : x ∉ A ∪ B := by
          simp [hxA, hxB]
        have hπx : π x = x := hπfix x hxU
        have hαx : α x = x := hαnot x hxA
        have hαix : α⁻¹ x = x := by
          apply α.injective
          calc
            α (α⁻¹ x) = x := α.apply_symm_apply x
            _ = α x := hαx.symm
        change α⁻¹ (π x) = x
        rw [hπx]
        exact hαix
    have hpab : α * β = π := by
      simp [β]
    have hpv : ρ π v = v := by
      calc
        ρ π v = ρ (α * β) v := by rw [hpab]
        _ = ρ α (ρ β v) := by simp
        _ = ρ α v := by rw [hvB β hβ]
        _ = v := hvA α hα
    have hτσ : τ * π = σ := by
      simp [π]
    calc
      ρ σ v = ρ (τ * π) v := by rw [hτσ]
      _ = ρ τ (ρ π v) := by simp
      _ = ρ τ v := by rw [hpv]

/-- Permutations fixing everything outside `Q` map `A ⊆ Q` to a subset of `Q` of the same size. -/
theorem image_mem_powersetCard_of_mem_fixingOutside {A Q : Finset Ω} (hAQ : A ⊆ Q)
    {σ : Equiv.Perm Ω} (hσ : σ ∈ fixingOutside Q) : A.image σ ∈ Q.powersetCard A.card := by
    refine Finset.mem_powersetCard.mpr ?_
    constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      by_contra hnot
      have hxx : σ (σ a) = σ a := by
        exact (show ∀ y, y ∉ Q → σ y = y from by
          simpa [fixingOutside] using hσ) (σ a) hnot
      have heq : σ a = a := σ.injective hxx
      have haQ : a ∈ Q := hAQ ha
      exact hnot (by simpa [heq] using haQ)
    · exact Finset.card_image_of_injective _ σ.injective

/-- `fixingOutside` is monotone. -/
theorem fixingOutside_mono {s t : Finset Ω} (hst : s ⊆ t) : fixingOutside s ⊆ fixingOutside t := by
    intro σ hσ
    have hσ' : ∀ x, x ∉ s → σ x = x := by
      simpa [fixingOutside] using hσ
    have h : ∀ x, x ∉ t → σ x = x := by
      intro x hx
      apply hσ' x
      intro hxs
      exact hx (hst hxs)
    simpa [fixingOutside] using h

/-- `fixingOutside s` is closed under multiplication. -/
theorem mul_mem_fixingOutside {s : Finset Ω} {σ τ : Equiv.Perm Ω}
    (hσ : σ ∈ fixingOutside s) (hτ : τ ∈ fixingOutside s) :
    σ * τ ∈ fixingOutside s := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ hτ ⊢
  intro x hx
  simp [Equiv.Perm.coe_mul, hσ x hx, hτ x hx]

/-- `fixingOutside s` is closed under inversion. -/
theorem inv_mem_fixingOutside {s : Finset Ω} {σ : Equiv.Perm Ω}
    (hσ : σ ∈ fixingOutside s) :
    (σ⁻¹ : Equiv.Perm Ω) ∈ fixingOutside s := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ ⊢
  intro x hx
  have h := congrArg (fun y => σ⁻¹ y) (hσ x hx)
  simpa using h.symm

section PermutationImages

omit [Fintype Ω]
private lemma image_mul_perm (S : Finset Ω) (σ τ : Equiv.Perm Ω) :
    S.image (σ * τ) = (S.image τ).image σ := by
  simp [Finset.image_image, Equiv.Perm.coe_mul]

private lemma image_inv_image_perm (S : Finset Ω) (σ : Equiv.Perm Ω) :
    (S.image σ).image (σ⁻¹ : Equiv.Perm Ω) = S := by
  simp [Finset.image_image]

end PermutationImages

/-- All fibers of `σ ↦ A.image σ` on `fixingOutside Q` over the `|A|`-subsets of `Q` have the same
size. -/
theorem card_fiber_eq {A Q : Finset Ω} {F F' : Finset Ω}
    (hF : F ∈ Q.powersetCard A.card) (hF' : F' ∈ Q.powersetCard A.card) :
    ((fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = F).card =
      ((fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = F').card := by
    have hFsub : F ⊆ Q := (Finset.mem_powersetCard.mp hF).1
    have hF'sub : F' ⊆ Q := (Finset.mem_powersetCard.mp hF').1
    have hcards : F.card = F'.card :=
      (Finset.mem_powersetCard.mp hF).2.trans
        (Finset.mem_powersetCard.mp hF').2.symm
    obtain ⟨g, hg, hgf⟩ :=
      exists_mem_fixingOutside_image_eq hFsub hF'sub hcards
    have hgf_inv : F'.image (g⁻¹ : Equiv.Perm Ω) = F := by
      calc
        F'.image (g⁻¹ : Equiv.Perm Ω) =
            (F.image g).image (g⁻¹ : Equiv.Perm Ω) := by
              rw [hgf]
        _ = F := image_inv_image_perm F g
    refine Finset.card_bij'
      (s := (fixingOutside Q).filter
        (fun σ : Equiv.Perm Ω => A.image σ = F))
      (t := (fixingOutside Q).filter
        (fun σ : Equiv.Perm Ω => A.image σ = F'))
      (fun σ _ => g * σ) (fun τ _ => g⁻¹ * τ) ?_ ?_ ?_ ?_
    · intro σ hσ
      refine mem_filter.mpr ⟨mul_mem_fixingOutside hg (mem_filter.mp hσ).1, ?_⟩
      rw [image_mul_perm, (mem_filter.mp hσ).2, hgf]
    · intro τ hτ
      refine mem_filter.mpr
        ⟨mul_mem_fixingOutside (inv_mem_fixingOutside hg) (mem_filter.mp hτ).1, ?_⟩
      rw [image_mul_perm, (mem_filter.mp hτ).2, hgf_inv]
    · intro σ hσ
      exact inv_mul_cancel_left g σ
    · intro τ hτ
      exact mul_inv_cancel_left g τ

/-- Grouping a block sum by the image of `A`: if `ρ σ v = T (A.image σ)` for every `σ` fixing
everything outside `A ∪ B`, then for `A ⊆ Q ⊆ A ∪ B`,
`∑_{σ ∈ fixingOutside Q} ρ σ v = (#fixingOutside Q / C(|Q|, |A|)) • ∑_{F ⊆ Q, |F| = |A|} T F`. -/
theorem sum_fixingOutside_eq_smul_sum (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) {A B Q : Finset Ω}
    (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (v : V) (T : Finset Ω → V)
    (hT : ∀ σ ∈ fixingOutside (A ∪ B), ρ σ v = T (A.image σ)) :
    ∑ σ ∈ fixingOutside Q, ρ σ v =
      (((fixingOutside Q).card : ℝ) / (Q.card.choose A.card : ℝ)) •
        ∑ F ∈ Q.powersetCard A.card, T F := by
    have hA : A ∈ Q.powersetCard A.card := by
      simp [hAQ]
    let M : ℕ :=
      ((fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = A).card
    have hfiber :
        ∀ F ∈ Q.powersetCard A.card,
          ((fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = F).card = M := by
      intro F hF
      exact card_fiber_eq hF hA
    have hmap :
        ∀ σ ∈ fixingOutside Q,
          A.image σ ∈ Q.powersetCard A.card :=
      fun σ hσ => image_mem_powersetCard_of_mem_fixingOutside hAQ hσ
    have hinner :
        ∀ F ∈ Q.powersetCard A.card,
          ∑ σ ∈ (fixingOutside Q).filter
              (fun σ : Equiv.Perm Ω => A.image σ = F), T (A.image σ) =
            M • T F := by
      intro F hF
      calc
        ∑ σ ∈ (fixingOutside Q).filter
            (fun σ : Equiv.Perm Ω => A.image σ = F), T (A.image σ) =
            ∑ σ ∈ (fixingOutside Q).filter
              (fun σ : Equiv.Perm Ω => A.image σ = F), T F := by
                apply Finset.sum_congr rfl
                intro σ hσ
                simp only [Finset.mem_filter] at hσ
                exact congrArg T hσ.2
        _ = M • T F := by
          simp [M, hfiber F hF]
    have hsum :
        (∑ σ ∈ fixingOutside Q, ρ σ v) =
          M • ∑ F ∈ Q.powersetCard A.card, T F := by
      calc
        ∑ σ ∈ fixingOutside Q, ρ σ v =
            ∑ σ ∈ fixingOutside Q, T (A.image σ) := by
              apply Finset.sum_congr rfl
              intro σ hσ
              exact hT σ (fixingOutside_mono hQ hσ)
        _ = ∑ F ∈ Q.powersetCard A.card,
              ∑ σ ∈ (fixingOutside Q).filter
                (fun σ : Equiv.Perm Ω => A.image σ = F), T (A.image σ) := by
              rw [Finset.sum_fiberwise_of_maps_to hmap]
        _ = ∑ F ∈ Q.powersetCard A.card, M • T F := by
              apply Finset.sum_congr rfl
              intro F hF
              exact hinner F hF
        _ = M • ∑ F ∈ Q.powersetCard A.card, T F := by
              simp [Finset.smul_sum]
    have hcard :
        (fixingOutside Q).card =
          Q.card.choose A.card * M := by
      calc
        (fixingOutside Q).card =
            ∑ σ ∈ fixingOutside Q, (1 : ℕ) := by simp
        _ = ∑ F ∈ Q.powersetCard A.card,
              ∑ σ ∈ (fixingOutside Q).filter
                (fun σ : Equiv.Perm Ω => A.image σ = F), (1 : ℕ) := by
              rw [Finset.sum_fiberwise_of_maps_to hmap]
        _ = ∑ F ∈ Q.powersetCard A.card,
              ((fixingOutside Q).filter
                (fun σ : Equiv.Perm Ω => A.image σ = F)).card := by
              simp
        _ = ∑ F ∈ Q.powersetCard A.card, M := by
              apply Finset.sum_congr rfl
              intro F hF
              exact hfiber F hF
        _ = (Q.powersetCard A.card).card * M := by
              simp
        _ = Q.card.choose A.card * M := by
              rw [Finset.card_powersetCard]
    have hchoose : 0 < Q.card.choose A.card :=
      Nat.choose_pos (Finset.card_le_card hAQ)
    have hM :
        (M : ℝ) =
          ((fixingOutside Q).card : ℝ) / (Q.card.choose A.card : ℝ) := by
      have hc : (Q.card.choose A.card : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hchoose)
      apply (eq_div_iff hc).2
      rw [show ((fixingOutside Q).card : ℝ) =
          (Q.card.choose A.card : ℝ) * (M : ℝ) by
            exact_mod_cast hcard]
      ring
    calc
      ∑ σ ∈ fixingOutside Q, ρ σ v =
          M • ∑ F ∈ Q.powersetCard A.card, T F := hsum
      _ = (M : ℝ) • ∑ F ∈ Q.powersetCard A.card, T F := by
        simp only [Nat.cast_smul_eq_nsmul]
      _ = (((fixingOutside Q).card : ℝ) / (Q.card.choose A.card : ℝ)) •
            ∑ F ∈ Q.powersetCard A.card, T F := by
        rw [hM]

section PermutationSubsets

omit [Fintype Ω]
/-- Equivariance of subset sums: if `ρ g (T F) = T (F.image g)` for every `F`, then the sum of
`T` over the `k`-subsets of `g(Q)` is `ρ g` applied to the sum over the `k`-subsets of `Q`. -/
theorem sum_powersetCard_image_eq (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) (g : Equiv.Perm Ω)
    (T : Finset Ω → V) (hT : ∀ F, ρ g (T F) = T (F.image g)) (Q : Finset Ω) (k : ℕ) :
    ∑ F ∈ (Q.image g).powersetCard k, T F = ρ g (∑ F ∈ Q.powersetCard k, T F) := by
    have hpow :
        (Q.image g).powersetCard k =
          (Q.powersetCard k).map (Finset.mapEmbedding g.toEmbedding).toEmbedding := by
      simpa [Finset.map_eq_image] using
        (Finset.powersetCard_map g.toEmbedding k Q)
    calc
      ∑ F ∈ (Q.image g).powersetCard k, T F =
          ∑ F ∈ Q.powersetCard k, T (F.image g) := by
            rw [hpow, Finset.sum_map]
            simp [Finset.map_eq_image]
      _ = ∑ F ∈ Q.powersetCard k, ρ g (T F) := by
            apply Finset.sum_congr rfl
            intro F hF
            exact (hT F).symm
      _ = ρ g (∑ F ∈ Q.powersetCard k, T F) := by
            rw [map_sum]

private lemma image_image_perm (A : Finset Ω) (g τ : Equiv.Perm Ω) :
    (A.image τ).image g = A.image (g * τ) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    exact Finset.mem_image.mpr ⟨z, hz, by simp [Equiv.Perm.mul_apply]⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    exact Finset.mem_image.mpr
      ⟨τ z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, by simp [Equiv.Perm.mul_apply]⟩

end PermutationSubsets

/--
**BKL Lemma 2.2** (orthogonal-representation form, with the stronger binomial factor `C(2d, d)`). -/
theorem norm_le_choose_mul_norm_blockAverage (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V))
    {A B Q : Finset Ω} {d : ℕ} (hA : A.card = d) (hB : B.card = 2 * d) (hAB : Disjoint A B)
    (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (hQc : Q.card = 2 * d) (v : V)
    (hvA : ∀ σ ∈ fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ fixingOutside B, ρ σ v = v) :
    ‖v‖ ≤ ((2 * d).choose d : ℝ) * ‖blockAverage ρ Q v‖ := by
  classical
  let W := A ∪ B
  let T : Finset Ω → V := fun F =>
    if h : ∃ σ ∈ fixingOutside W, A.image σ = F then ρ (Classical.choose h) v else 0
  have hAW : A ⊆ W := by
    intro x hx
    exact mem_union_left B hx
  have hWQ : Q ⊆ W := by simpa [W] using hQ
  have hWcard : W.card = 3 * d := by
    dsimp [W]
    rw [card_union_of_disjoint hAB, hA, hB]
    omega
  have hT : ∀ σ ∈ fixingOutside W, ρ σ v = T (A.image σ) := by
    intro σ hσ
    let hh : ∃ τ ∈ fixingOutside W, A.image τ = A.image σ := ⟨σ, hσ, rfl⟩
    have hc := Classical.choose_spec hh
    have heq : ρ σ v = ρ (Classical.choose hh) v := by
      apply apply_eq_of_image_eq ρ v hvA hvB
      · exact hσ
      · exact hc.1
      · exact hc.2.symm
    simpa [T, hh] using heq
  have hprod :
    ∀ {g τ : Equiv.Perm Ω},
      g ∈ fixingOutside W → τ ∈ fixingOutside W → g * τ ∈ fixingOutside W := by
    intro g τ hg hτ
    simp only [fixingOutside, mem_filter, mem_univ, true_and] at hg hτ ⊢
    intro x hx
    simp [Equiv.Perm.mul_apply, hg x hx, hτ x hx]
  have hTinvariant : ∀ g ∈ fixingOutside W, ∀ F, ρ g (T F) = T (F.image g) := by
    intro g hg F
    by_cases hF : ∃ τ ∈ fixingOutside W, A.image τ = F
    · rcases hF with ⟨τ, hτ, rfl⟩
      have hgt : g * τ ∈ fixingOutside W := hprod hg hτ
      have him := image_image_perm A g τ
      calc
        ρ g (T (A.image τ)) = ρ g (ρ τ v) := by rw [hT τ hτ]
        _ = ρ (g * τ) v := by simp
        _ = T (A.image (g * τ)) := hT (g * τ) hgt
        _ = T ((A.image τ).image g) := by rw [him]
    · have hF' : ¬∃ τ ∈ fixingOutside W, A.image τ = F.image g := by
        intro h'
        rcases h' with ⟨τ, hτ, hτim⟩
        have hgi : (g⁻¹ : Equiv.Perm Ω) ∈ fixingOutside W := inv_mem_fixingOutside hg
        have hgt : (g⁻¹ : Equiv.Perm Ω) * τ ∈ fixingOutside W := hprod hgi hτ
        have him : A.image ((g⁻¹ : Equiv.Perm Ω) * τ) = F := by
          calc
            A.image ((g⁻¹ : Equiv.Perm Ω) * τ) = (A.image τ).image (g⁻¹ : Equiv.Perm Ω) := by
              rw [image_image_perm]
            _ = (F.image g).image (g⁻¹ : Equiv.Perm Ω) := by rw [hτim]
            _ = F := by
              ext x
              simp
        exact hF ⟨(g⁻¹ : Equiv.Perm Ω) * τ, hgt, him⟩
      simp [T, hF, hF', map_zero]
  have hTnorm : ∀ F ∈ W.powersetCard d, ‖T F‖ = ‖v‖ := by
    intro F hF
    have hFsub : F ⊆ W := (mem_powersetCard.mp hF).1
    have hFcard : F.card = d := (mem_powersetCard.mp hF).2
    obtain ⟨σ, hσ, hσim⟩ := exists_mem_fixingOutside_image_eq hAW hFsub (by simp [hA, hFcard])
    have hTF : T F = ρ σ v := by
      rw [← hσim]
      exact (hT σ hσ).symm
    rw [hTF, (ρ σ).norm_map]
  have hsum :
    ∑ σ ∈ fixingOutside Q, ρ σ v =
      (((fixingOutside Q).card : ℝ) / ((2 * d).choose d : ℝ)) • ∑ F ∈ Q.powersetCard d, T F := by
    simpa [hA, hQc] using
      (sum_fixingOutside_eq_smul_sum ρ (A := A) (B := B) (Q := Q) hAQ hQ v T hT)
  have hS : (∑ F ∈ Q.powersetCard d, T F) = ((2 * d).choose d : ℝ) • blockAverage ρ Q v := by
    rw [blockAverage, hsum]
    have hN : (fixingOutside Q).card ≠ 0 := by
      apply Finset.card_ne_zero.mpr
      exact ⟨1, by simp [fixingOutside]⟩
    have hC : (2 * d).choose d ≠ 0 := by
      have hp : 0 < (2 * d).choose d := by
        apply Nat.choose_pos
        omega
      omega
    simp only [smul_smul]
    field_simp [hN, hC]
    simp
  have hinner :
    ∀ E ∈ W.powersetCard (2 * d),
      ‖∑ F ∈ E.powersetCard d, T F‖ = ((2 * d).choose d : ℝ) * ‖blockAverage ρ Q v‖ := by
    intro E hE
    have hEsub : E ⊆ W := (mem_powersetCard.mp hE).1
    have hEcard : E.card = 2 * d := (mem_powersetCard.mp hE).2
    obtain ⟨g, hg, hgim⟩ := exists_mem_fixingOutside_image_eq hWQ hEsub (by simp [hQc, hEcard])
    have hs := sum_powersetCard_image_eq ρ g T (fun F => hTinvariant g hg F) Q d
    have hsumE : ∑ F ∈ E.powersetCard d, T F = ρ g (∑ F ∈ Q.powersetCard d, T F) := by
      rw [← hgim]
      exact hs
    rw [hsumE, (ρ g).norm_map, hS, norm_smul]
    congr 1
    exact abs_of_nonneg (by positivity)
  have hineq := sum_norm_sq_le_sum_norm_sq_sum_subset W (d := d) hWcard T
  have hleft : ∑ F ∈ W.powersetCard d, ‖T F‖ ^ 2 = ((3 * d).choose d : ℝ) * ‖v‖ ^ 2 := by
    calc
      ∑ F ∈ W.powersetCard d, ‖T F‖ ^ 2 = ∑ F ∈ W.powersetCard d, ‖v‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro F hF
        rw [hTnorm F hF]
      _ = ((W.powersetCard d).card : ℝ) * ‖v‖ ^ 2 := by simp
      _ = ((3 * d).choose d : ℝ) * ‖v‖ ^ 2 := by rw [card_powersetCard, hWcard]
  have hright :
    ∑ E ∈ W.powersetCard (2 * d), ‖∑ F ∈ E.powersetCard d, T F‖ ^ 2 =
      ((3 * d).choose (2 * d) : ℝ) * (((2 * d).choose d : ℝ) * ‖blockAverage ρ Q v‖) ^ 2 := by
    calc
      ∑ E ∈ W.powersetCard (2 * d), ‖∑ F ∈ E.powersetCard d, T F‖ ^ 2 =
          ∑ E ∈ W.powersetCard (2 * d), (((2 * d).choose d : ℝ) * ‖blockAverage ρ Q v‖) ^ 2 := by
        apply Finset.sum_congr rfl
        intro E hE
        rw [hinner E hE]
      _ =
          ((W.powersetCard (2 * d)).card : ℝ) *
            (((2 * d).choose d : ℝ) * ‖blockAverage ρ Q v‖) ^ 2 := by
        simp
      _ = ((3 * d).choose (2 * d) : ℝ) * (((2 * d).choose d : ℝ) * ‖blockAverage ρ Q v‖) ^ 2 := by
        rw [card_powersetCard, hWcard]
  rw [hleft, hright] at hineq
  have hchoose : (3 * d).choose d = (3 * d).choose (2 * d) := by
    have h := Nat.choose_symm (by omega : d ≤ 3 * d)
    have hd : 3 * d - d = 2 * d := by omega
    simpa [hd] using h.symm
  have hc : 0 < ((3 * d).choose d : ℝ) := by
    have hp : 0 < (3 * d).choose d := by
      apply Nat.choose_pos
      omega
    exact_mod_cast hp
  have hsq : ‖v‖ ^ 2 ≤ (((2 * d).choose d : ℝ) * ‖blockAverage ρ Q v‖) ^ 2 := by
    rw [← hchoose] at hineq
    exact le_of_mul_le_mul_left hineq hc
  exact (pow_le_pow_iff_left₀ (norm_nonneg v) (by positivity) two_ne_zero).1 hsq

/-- **BKL Lemma 2.2** (orthogonal-representation form): `‖v‖ ≤ 4^d ‖S_Q v‖`. -/
theorem norm_le_four_pow_mul_norm_blockAverage (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V))
    {A B Q : Finset Ω} {d : ℕ} (hA : A.card = d) (hB : B.card = 2 * d) (hAB : Disjoint A B)
    (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (hQc : Q.card = 2 * d) (v : V)
    (hvA : ∀ σ ∈ fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ fixingOutside B, ρ σ v = v) :
    ‖v‖ ≤ (4 : ℝ) ^ d * ‖blockAverage ρ Q v‖ := by
    have hchoose_nat : (2 * d).choose d ≤ 4 ^ d := by
      simpa only [Nat.centralBinom_eq_two_mul_choose] using
        (Nat.centralBinom_le_four_pow d)
    have hchoose_real : ((2 * d).choose d : ℝ) ≤ (4 : ℝ) ^ d := by
      exact_mod_cast hchoose_nat
    have hnorm : 0 ≤ ‖blockAverage ρ Q v‖ := norm_nonneg _
    calc
      ‖v‖ ≤ ((2 * d).choose d : ℝ) * ‖blockAverage ρ Q v‖ :=
        norm_le_choose_mul_norm_blockAverage ρ hA hB hAB hAQ hQ hQc v hvA hvB
      _ ≤ (4 : ℝ) ^ d * ‖blockAverage ρ Q v‖ :=
        mul_le_mul_of_nonneg_right hchoose_real hnorm

end FunctionalInequalities.Analysis.Tensor
