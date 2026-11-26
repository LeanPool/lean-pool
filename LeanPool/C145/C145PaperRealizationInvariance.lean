/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145GraphSpectralRealization

/-! Any two actual positively oriented realizations of one graph and port
have the same columns, rates and actual overlaps after a derived permutation.
The permutation fixes ground and restricts to the nonground coordinates. -/

@[expose] public section

noncomputable section
namespace C145.PaperRealizationInvariance
open scoped BigOperators
open Matrix C145.GraphSpectralRealization

private theorem frame_expansion {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (x : Fin (n + 1) → ℝ) (v : Fin (n + 1)) :
    (∑ j, Q v j * ((fun w => Q w j) ⬝ᵥ x)) = x v := by
  unfold dotProduct
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ w, ∑ j, Q v j * (Q w j * x w)) =
        ∑ w, (∑ j, Q v j * Q w j) * x w := by
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = x v := by
      simp_rw [C145PhysicalFrame.columnOrthonormal_rowComplete Q hQ v]
      simp

variable {n : ℕ} {μ : ℝ}
  {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : Fin (n + 1) → ℝ}

private theorem realization_generator_symm (S : OrientedRealization μ W b) :
    (generator μ W).IsSymm := by
  rw [← S.original_generator]
  apply Matrix.IsSymm.ext
  intro v w
  unfold C145CoordinatePermutation.spectralGenerator
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem cross_overlap_zero (S0 S1 : OrientedRealization μ W b)
    (i j : Fin (n + 1)) (h : S1.rates j ≠ S0.rates i) :
    (fun v => S1.Q v j) ⬝ᵥ (fun v => S0.Q v i) = 0 := by
  have hs := realization_generator_symm S0
  have he := hs.dotProduct_mulVec_comm
    (x := fun v => S1.Q v j) (y := fun v => S0.Q v i)
  rw [S0.eigenvectors i, S1.eigenvectors j, dotProduct_smul,
    dotProduct_smul, dotProduct_comm (fun v => S0.Q v i) (fun v => S1.Q v j)] at he
  change -S0.rates i * _ = -S1.rates j * _ at he
  exact (mul_eq_zero.mp (by nlinarith :
    (S1.rates j - S0.rates i) *
      ((fun v => S1.Q v j) ⬝ᵥ (fun v => S0.Q v i)) = 0)).resolve_left
        (sub_ne_zero.mpr h)

/-- Every rate of either realization is actually a rate of the other one. -/
theorem realization_rate_exists (S0 S1 : OrientedRealization μ W b)
    (i : Fin (n + 1)) : ∃ j, S1.rates j = S0.rates i := by
  by_contra h
  have hz : ∀ j, (fun v => S1.Q v j) ⬝ᵥ (fun v => S0.Q v i) = 0 := by
    intro j
    apply cross_overlap_zero S0 S1 i j
    exact fun hj => h ⟨j, hj⟩
  have hcol : ∀ v, S0.Q v i = 0 := by
    intro v
    have hx := frame_expansion S1.Q S1.orthonormal (fun w => S0.Q w i) v
    simpa only [hz, mul_zero, Finset.sum_const_zero] using hx.symm
  have hh := S0.orthonormal i i
  simp [hcol] at hh

/-- Simple spectrum, normalization and positive actual port overlaps force
literal equality, including the sign, of columns with equal rates. -/
theorem realization_columns_eq_of_rate_eq (S0 S1 : OrientedRealization μ W b)
    (i j : Fin (n + 1)) (hr : S1.rates j = S0.rates i) :
    ∀ v, S1.Q v j = S0.Q v i := by
  let a : ℝ := (fun v => S1.Q v j) ⬝ᵥ (fun v => S0.Q v i)
  have hcol : ∀ v, S0.Q v i = a * S1.Q v j := by
    intro v
    have hx := frame_expansion S1.Q S1.orthonormal (fun w => S0.Q w i) v
    have hsum : (∑ k, S1.Q v k *
        ((fun w => S1.Q w k) ⬝ᵥ (fun w => S0.Q w i))) = S1.Q v j * a := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        rw [cross_overlap_zero S0 S1 i k (by
          intro hk
          exact hkj (S1.simple (hk.trans hr.symm)))]
        exact mul_zero _
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    rw [hsum] at hx
    exact hx.symm.trans (mul_comm _ _)
  have haa : a * a = 1 := by
    have h0 : (∑ v, S0.Q v i * S0.Q v i) = 1 := by
      simpa using S0.orthonormal i i
    have h1 : (∑ v, S1.Q v j * S1.Q v j) = 1 := by
      simpa using S1.orthonormal j j
    calc
      a * a = a * a * (∑ v, S1.Q v j * S1.Q v j) := by rw [h1, mul_one]
      _ = ∑ v, S0.Q v i * S0.Q v i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        rw [hcol]
        ring
      _ = 1 := h0
  have hov : C145.Pulse.modalOverlap S0.Q b i =
      a * C145.Pulse.modalOverlap S1.Q b j := by
    unfold C145.Pulse.modalOverlap
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [hcol]
    ring
  have hp0 := S0.positive_overlap i
  have hp1 := S1.positive_overlap j
  rw [hov] at hp0
  have ha : 0 < a := (mul_pos_iff_of_pos_right hp1).mp hp0
  have ha1 : a = 1 := by nlinarith
  intro v
  simpa only [ha1, one_mul] using (hcol v).symm

/-- The modal relabeling is derived from the actual common generator, rather
than assumed as an additional equivalence premise. -/
theorem realizations_equivalent (S0 S1 : OrientedRealization μ W b) :
    ∃ e : Fin (n + 1) ≃ Fin (n + 1),
      e 0 = 0 ∧ (∀ i, S1.rates (e i) = S0.rates i) ∧
      (∀ v i, S1.Q v (e i) = S0.Q v i) ∧
      (∀ i, C145.Pulse.modalOverlap S1.Q b (e i) =
        C145.Pulse.modalOverlap S0.Q b i) ∧ S0.c = S1.c := by
  choose f hf using realization_rate_exists S0 S1
  have hinj : Function.Injective f := by
    intro i j hij
    apply S0.simple
    rw [← hf i, ← hf j, hij]
  let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, rfl⟩)
  have he : ∀ i, S1.rates (e i) = S0.rates i := hf
  have he0 : e 0 = 0 := by
    apply S1.simple
    rw [he, S0.ground_rate, S1.ground_rate]
  have hQ : ∀ v i, S1.Q v (e i) = S0.Q v i :=
    fun v i => realization_columns_eq_of_rate_eq S0 S1 i (e i) (he i) v
  refine ⟨e, he0, he, hQ, ?_, ?_⟩
  · intro i
    unfold C145.Pulse.modalOverlap
    simp_rw [hQ]
  · have h := hQ 0 0
    rw [he0, S0.ground, S1.ground] at h
    exact h.symm

/-- Any permutation fixing ground has an actual permutation of `Fin n` whose
successor coordinates commute with the original permutation. -/
def nongroundEquiv (e : Fin (n + 1) ≃ Fin (n + 1)) (he0 : e 0 = 0) : Fin n ≃ Fin n := by
  have hn : ∀ i : Fin n, e i.succ ≠ 0 := by
    intro i h
    exact Fin.succ_ne_zero i (e.injective (h.trans he0.symm))
  let f : Fin n → Fin n := fun i => (e i.succ).pred (hn i)
  have hf : ∀ i, (f i).succ = e i.succ := fun i => Fin.succ_pred _ _
  have hi : Function.Injective f := by
    intro i j h
    apply Fin.succ_injective
    apply e.injective
    rw [← hf i, ← hf j, h]
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hi, rfl⟩)

@[simp] theorem nongroundEquiv_succ (e : Fin (n + 1) ≃ Fin (n + 1))
    (he0 : e 0 = 0) (i : Fin n) :
    (nongroundEquiv e he0 i).succ = e i.succ := by
  have hn : e i.succ ≠ 0 := fun h =>
    Fin.succ_ne_zero i (e.injective (h.trans he0.symm))
  change ((e i.succ).pred hn).succ = e i.succ
  exact Fin.succ_pred _ hn

/-- Practical full and nonground matching package for ordering-independent
paper quantities. It includes the literal columns and the positive overlaps. -/
theorem realizations_full_and_nonground_equivalent
    (S0 S1 : OrientedRealization μ W b) :
    ∃ (e : Fin (n + 1) ≃ Fin (n + 1)) (p : Fin n ≃ Fin n),
      e 0 = 0 ∧ (∀ i, (p i).succ = e i.succ) ∧
      (∀ i, S1.rates (e i) = S0.rates i) ∧
      (∀ v i, S1.Q v (e i) = S0.Q v i) ∧
      (∀ i, C145.Pulse.modalOverlap S1.Q b (e i) =
        C145.Pulse.modalOverlap S0.Q b i) ∧
      (∀ i : Fin n, S1.rates (p i).succ = S0.rates i.succ) ∧
      (∀ v (i : Fin n), S1.Q v (p i).succ = S0.Q v i.succ) ∧
      (∀ i : Fin n, C145.Pulse.modalOverlap S1.Q b (p i).succ =
        C145.Pulse.modalOverlap S0.Q b i.succ) ∧ S0.c = S1.c := by
  obtain ⟨e, he0, hr, hQ, ha, hc⟩ := realizations_equivalent S0 S1
  let p := nongroundEquiv e he0
  have hp : ∀ i : Fin n, (p i).succ = e i.succ := nongroundEquiv_succ e he0
  refine ⟨e, p, he0, hp, hr, hQ, ha, ?_, ?_, ?_, hc⟩
  · intro i; rw [hp]; exact hr i.succ
  · intro v i; rw [hp]; exact hQ v i.succ
  · intro i; rw [hp]; exact ha i.succ

end C145.PaperRealizationInvariance

end
