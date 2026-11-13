/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

/-
Authors: David Muñoz-Lahoz
-/

public import LeanPool.FBLOrderContinuity.BanLat.Sublattice
public import LeanPool.OrderClosures.BanLat.Basic



/-!
# The Riesz decomposition theorem

This file collects the Riesz decomposition theorem and its refinements in a lattice-ordered
abelian group: the binary form, the matrix form for two partitions of the same sum, the
version with a finite sum on the left, the absolute-value decomposition, and the
identification of sum intervals.
-/

@[expose] public section

open scoped Pointwise

section LatticeOrderedGroup

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

/-- Riesz decomposition: if `0 ≤ x ≤ y + z` with `y, z ≥ 0`, then `x = x₁ + x₂`
with `0 ≤ x₁ ≤ y` and `0 ≤ x₂ ≤ z`. -/
theorem riesz_decomposition (x y z : X) (xnonneg : 0 ≤ x) (ynonneg : 0 ≤ y)
  (znonneg : 0 ≤ z) (h : x ≤ y + z) : ∃ x1 x2 : X, (0 ≤ x1) ∧ (x1 ≤ y) ∧
  (0 ≤ x2) ∧ (x2 ≤ z) ∧ (x = x1 + x2) := by
    use (x ⊓ y); use (x - x ⊓ y)
    repeat (any_goals constructor)
    · exact le_inf xnonneg ynonneg
    · exact inf_le_right
    · simp
    · rw [sub_inf]
      have : x - y ≤ z := by
        calc
          x - y = x + (-y) := by rw [sub_eq_add_neg]
              _ ≤ (y + z) + (-y) := by apply add_le_add h (le_refl (-y))
              _ ≤ z := by simp
      rw [le_iff_posPart_negPart] at this
      rw [sub_self, sup_comm, ← posPart_def]
      rw [← posPart_of_nonneg znonneg]
      exact this.1
    · simp

private lemma riesz_split_sum :
    ∀ {n : ℕ} (u : X) (z : Fin n → X), 0 ≤ u → (∀ j, 0 ≤ z j) →
      u ≤ ∑ j, z j →
      ∃ x : Fin n → X, (∀ j, 0 ≤ x j) ∧ (∀ j, x j ≤ z j) ∧ u = ∑ j, x j := by
  intro n
  induction n with
  | zero =>
    intro u z hu _ h
    refine ⟨Fin.elim0, fun j => j.elim0, fun j => j.elim0, ?_⟩
    rw [Fin.sum_univ_zero] at h ⊢
    exact le_antisymm h hu
  | succ n ih =>
    intro u z hu hz h
    rw [Fin.sum_univ_succ] at h
    obtain ⟨a, b, ha_nn, ha_le, hb_nn, hb_le, hab⟩ :=
      riesz_decomposition u (z 0) (∑ j : Fin n, z j.succ) hu (hz 0)
        (Finset.sum_nonneg fun j _ => hz _) h
    obtain ⟨x', hx'_nn, hx'_le, hx'_sum⟩ :=
      ih b (fun j => z j.succ) hb_nn (fun j => hz _) hb_le
    refine ⟨Fin.cons a x', ?_, ?_, ?_⟩
    · intro j
      induction j using Fin.cases with
      | zero => simpa using ha_nn
      | succ i => simpa using hx'_nn i
    · intro j
      induction j using Fin.cases with
      | zero => simpa using ha_le
      | succ i => simpa using hx'_le i
    · rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [hab, hx'_sum]

/-- Matrix form of Riesz decomposition: if two finite sums of non-negative vectors agree,
there is a non-negative matrix whose row sums recover the first family and whose column
sums recover the second. -/
theorem riesz_decomposition_matrix :
    ∀ {m n : ℕ} (u : Fin m → X) (z : Fin n → X),
      (∀ i, 0 ≤ u i) → (∀ j, 0 ≤ z j) → ∑ i, u i = ∑ j, z j →
      ∃ x : Fin m → Fin n → X,
        (∀ i j, 0 ≤ x i j) ∧
        (∀ i, u i = ∑ j, x i j) ∧
        (∀ j, z j = ∑ i, x i j) := by
  intro m
  induction m with
  | zero =>
    intro n u z _ hz heq
    refine ⟨fun i _ => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    intro j
    have h0 : ∑ j, z j = 0 := by rw [← heq, Fin.sum_univ_zero]
    have hzj : z j ≤ 0 := by
      have := Finset.single_le_sum (f := z) (fun j' _ => hz j') (Finset.mem_univ j)
      rw [h0] at this; exact this
    rw [le_antisymm hzj (hz j)]
    exact (Fin.sum_univ_zero _).symm
  | succ m ih =>
    intro n u z hu hz heq
    have hu0_le : u 0 ≤ ∑ j, z j := by
      rw [← heq, Fin.sum_univ_succ]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hu _)
    obtain ⟨x0, hx0_nn, hx0_le, hx0_sum⟩ :=
      riesz_split_sum (u 0) z (hu 0) hz hu0_le
    let z' : Fin n → X := fun j => z j - x0 j
    have hz'_nn : ∀ j, 0 ≤ z' j := fun j => sub_nonneg.mpr (hx0_le j)
    have heq' : ∑ i, (u ∘ Fin.succ) i = ∑ j, z' j := by
      rw [Fin.sum_univ_succ] at heq
      have hsum_sub : ∑ j, z' j = (∑ j, z j) - ∑ j, x0 j := by
        simp [z', Finset.sum_sub_distrib]
      rw [hsum_sub, ← heq, ← hx0_sum]
      simp [Function.comp]
    obtain ⟨y, hy_nn, hy_row, hy_col⟩ :=
      ih (u ∘ Fin.succ) z' (fun i => hu _) hz'_nn heq'
    refine ⟨Fin.cons x0 y, ?_, ?_, ?_⟩
    · intro i j
      induction i using Fin.cases with
      | zero => simpa using hx0_nn j
      | succ i => simpa using hy_nn i j
    · intro i
      induction i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        rw [hx0_sum]
      | succ i =>
        simp only [Fin.cons_succ]
        exact hy_row i
    · intro j
      rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      have hz'_eq : z j - x0 j = ∑ i, y i j := hy_col j
      have : z j = x0 j + (z j - x0 j) := by abel
      rw [this, hz'_eq]

/-- Riesz decomposition with several summands on the left: if `∑ᵢ uᵢ ≤ x + y` with all
terms non-negative, each `uᵢ` splits as `vᵢ + wᵢ` so that `∑ᵢ vᵢ ≤ x` and `∑ᵢ wᵢ ≤ y`. -/
theorem riesz_decomposition_sum_le {k : ℕ} (u : Fin k → X) (x y : X)
    (hu : ∀ i, 0 ≤ u i) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ∑ i, u i ≤ x + y) :
    ∃ v w : Fin k → X,
      (∀ i, 0 ≤ v i) ∧ (∀ i, 0 ≤ w i) ∧
      (∑ i, v i ≤ x) ∧ (∑ i, w i ≤ y) ∧
      (∀ i, u i = v i + w i) := by
  obtain ⟨a, b, ha_nn, ha_le, hb_nn, hb_le, hab⟩ :=
    riesz_decomposition (∑ i, u i) x y (Finset.sum_nonneg fun i _ => hu _) hx hy h
  let z : Fin 2 → X := ![a, b]
  have hz_nn : ∀ j, 0 ≤ z j := by
    intro j; fin_cases j
    · exact ha_nn
    · exact hb_nn
  have hsum_eq : ∑ i, u i = ∑ j, z j := by
    rw [hab, Fin.sum_univ_two]
    rfl
  obtain ⟨M, hM_nn, hM_row, hM_col⟩ :=
    riesz_decomposition_matrix u z hu hz_nn hsum_eq
  refine ⟨fun i => M i 0, fun i => M i 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact hM_nn i 0
  · intro i; exact hM_nn i 1
  · have hcol := hM_col 0
    have : a = ∑ i, M i 0 := hcol
    rw [← this]; exact ha_le
  · have hcol := hM_col 1
    have : b = ∑ i, M i 1 := hcol
    rw [← this]; exact hb_le
  · intro i
    have := hM_row i
    rw [Fin.sum_univ_two] at this
    exact this

/-- Decomposing a vector according to a splitting of its absolute value: if `|x| = u + v`
with `u, v ≥ 0`, then `x = y + z` for some `y, z` with `|y| = u` and `|z| = v`. -/
theorem exists_abs_decomposition {x u v : X} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : |x| = u + v) :
    ∃ y z : X, x = y + z ∧ |y| = u ∧ |z| = v := by
  set a := x⁺ ⊓ u with ha_def
  set b := x⁻ ⊓ u with hb_def
  have ha_nn : 0 ≤ a := le_inf (posPart_nonneg _) hu
  have hb_nn : 0 ≤ b := le_inf (negPart_nonneg _) hu
  have ha_le_pp : a ≤ x⁺ := inf_le_left
  have hb_le_np : b ≤ x⁻ := inf_le_left
  have ha_le_u : a ≤ u := inf_le_right
  have hb_le_u : b ≤ u := inf_le_right
  have hab_disj : a ⊓ b = 0 := by
    apply le_antisymm _ (le_inf ha_nn hb_nn)
    calc a ⊓ b ≤ x⁺ ⊓ x⁻ := inf_le_inf ha_le_pp hb_le_np
      _ = 0 := posPart_inf_negPart_eq_zero _
  have hab_eq : a + b = u := by
    have hle : a + b ≤ u := by
      have e : a + b = a ⊔ b := by
        have := inf_add_sup a b
        rw [hab_disj, zero_add] at this
        exact this.symm
      rw [e]; exact sup_le ha_le_u hb_le_u
    have hge : u ≤ a + b := by
      have hle_u : u ≤ x⁺ + x⁻ := by
        rw [posPart_add_negPart, h]
        exact le_add_of_nonneg_right hv
      obtain ⟨u₁, u₂, h1_nn, h1_le, h2_nn, h2_le, huuv⟩ :=
        riesz_decomposition u x⁺ x⁻ hu (posPart_nonneg _) (negPart_nonneg _) hle_u
      have h1a : u₁ ≤ a := le_inf h1_le (by rw [huuv]; exact le_add_of_nonneg_right h2_nn)
      have h2b : u₂ ≤ b := le_inf h2_le (by rw [huuv]; exact le_add_of_nonneg_left h1_nn)
      rw [huuv]; exact add_le_add h1a h2b
    exact le_antisymm hle hge
  let y := a - b
  refine ⟨y, x - y, by abel, ?_, ?_⟩
  · have hy_pp : y⁺ = a := (uniqueness_posPart y rfl hab_disj).symm
    have hy_np : y⁻ = b := by
      have hneg : -y = b - a := by simp [y]
      have hba_disj : b ⊓ a = 0 := by rw [inf_comm]; exact hab_disj
      have h1 : (-y)⁺ = b := (uniqueness_posPart (-y) hneg hba_disj).symm
      rw [← posPart_neg]; exact h1
    rw [← posPart_add_negPart, hy_pp, hy_np, hab_eq]
  · -- |x - y| = v
    -- z = x - y = (x⁺ - a) - (x⁻ - b)
    set a' := x⁺ - a with ha'_def
    set b' := x⁻ - b with hb'_def
    have ha'_nn : 0 ≤ a' := sub_nonneg.mpr ha_le_pp
    have hb'_nn : 0 ≤ b' := sub_nonneg.mpr hb_le_np
    have ha'_le_pp : a' ≤ x⁺ := sub_le_self _ ha_nn
    have hb'_le_np : b' ≤ x⁻ := sub_le_self _ hb_nn
    have hab'_disj : a' ⊓ b' = 0 := by
      apply le_antisymm _ (le_inf ha'_nn hb'_nn)
      calc a' ⊓ b' ≤ x⁺ ⊓ x⁻ := inf_le_inf ha'_le_pp hb'_le_np
        _ = 0 := posPart_inf_negPart_eq_zero _
    have hxy : x - y = a' - b' := by
      change x - (a - b) = (x⁺ - a) - (x⁻ - b)
      conv_lhs => rw [← posPart_sub_negPart x]
      abel
    have hz_pp : (x - y)⁺ = a' := by
      rw [hxy]; exact (uniqueness_posPart _ rfl hab'_disj).symm
    have hz_np : (x - y)⁻ = b' := by
      rw [hxy]
      have hneg : -(a' - b') = b' - a' := by abel
      have hba'_disj : b' ⊓ a' = 0 := by rw [inf_comm]; exact hab'_disj
      have h1 : (-(a' - b'))⁺ = b' := (uniqueness_posPart _ hneg hba'_disj).symm
      rw [← posPart_neg]; exact h1
    have hab'_sum : a' + b' = v := by
      have key : (a + b) + (a' + b') = u + v := by
        change (a + b) + ((x⁺ - a) + (x⁻ - b)) = u + v
        rw [← h, ← posPart_add_negPart]
        abel
      rw [hab_eq] at key
      exact add_left_cancel key
    rw [← posPart_add_negPart, hz_pp, hz_np, hab'_sum]

/-- Riesz decomposition for the absolute value: if `|x| ≤ v₁ + ⋯ + vₙ` with each `vᵢ ≥ 0`,
then `x = x₁ + ⋯ + xₙ` with `|xᵢ| ≤ |x| ⊓ vᵢ`. -/
theorem riesz_decomposition_abs :
    ∀ {n : ℕ} (x : X) (v : Fin n → X),
      (∀ i, 0 ≤ v i) → |x| ≤ ∑ i, v i →
      ∃ y : Fin n → X, x = ∑ i, y i ∧ ∀ i, |y i| ≤ |x| ⊓ v i := by
  intro n
  induction n with
  | zero =>
    intro x v _ h
    rw [Fin.sum_univ_zero] at h
    have habs : |x| = 0 := le_antisymm h (abs_nonneg _)
    have hx : x = 0 := (abs_eq_zero_iff_zero x).mp habs
    refine ⟨Fin.elim0, ?_, ?_⟩
    · rw [Fin.sum_univ_zero]; exact hx
    · intro i; exact i.elim0
  | succ n ih =>
    intro x v hv h
    rw [Fin.sum_univ_succ] at h
    -- Split |x| = u + w with 0 ≤ u ≤ v 0 and 0 ≤ w ≤ ∑ v i.succ
    obtain ⟨u, w, hu_nn, hu_le, hw_nn, hw_le, huw⟩ :=
      riesz_decomposition |x| (v 0) (∑ i : Fin n, v i.succ) (abs_nonneg _) (hv 0)
        (Finset.sum_nonneg fun i _ => hv _) h
    -- Split x = y0 + x' with |y0| = u and |x'| = w
    obtain ⟨y0, x', hxsum, hy0_abs, hx'_abs⟩ := exists_abs_decomposition hu_nn hw_nn huw
    -- Apply ih to x' and v ∘ Fin.succ
    have hx'_le : |x'| ≤ ∑ i : Fin n, v i.succ := hx'_abs ▸ hw_le
    obtain ⟨y', hy'_sum, hy'_abs⟩ := ih x' (fun i => v i.succ) (fun i => hv _) hx'_le
    refine ⟨Fin.cons y0 y', ?_, ?_⟩
    · rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [hxsum, hy'_sum]
    · intro i
      induction i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        refine le_inf ?_ ?_
        · rw [hy0_abs, huw]; exact le_add_of_nonneg_right hw_nn
        · rw [hy0_abs]; exact hu_le
      | succ i =>
        simp only [Fin.cons_succ]
        have h1 : |y' i| ≤ |x'| ⊓ v i.succ := hy'_abs i
        have h2 : |x'| ≤ |x| := by
          rw [hx'_abs, huw]
          exact le_add_of_nonneg_left hu_nn
        exact h1.trans (inf_le_inf_right _ h2)

/-- The order intervals of non-negative endpoints satisfy `[0, x] + [0, y] = [0, x + y]`. -/
theorem Icc_add_Icc_of_nonneg {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Set.Icc (0 : X) x + Set.Icc (0 : X) y = Set.Icc (0 : X) (x + y) := by
  ext c
  rw [Set.mem_add]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨add_nonneg ha.1 hb.1, add_le_add ha.2 hb.2⟩
  · rintro ⟨hc0, hc⟩
    obtain ⟨a, b, ha0, ha, hb0, hb, heq⟩ := riesz_decomposition c x y hc0 hx hy hc
    exact ⟨a, ⟨ha0, ha⟩, b, ⟨hb0, hb⟩, heq.symm⟩

end LatticeOrderedGroup
