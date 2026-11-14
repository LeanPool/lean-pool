/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexEqualSummandASI

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Rectangular matrix multiplication algorithms and their asymptotic exponents. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

namespace Tensor

open MatrixMultiplication.Foundation.Tensor

theorem rectangular_rank_of_injective
    {K A B C A' B' C' : Type*} [CommSemiring K]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq A'] [DecidableEq B'] [DecidableEq C'] {R : ℕ}
    (h : RankAtMost (matrixCoefficients (K := K) A B C) R)
    (f : A' → A) (hf : Function.Injective f)
    (g : B' → B) (hg : Function.Injective g)
    (j : C' → C) (hj : Function.Injective j) :
    RankAtMost (matrixCoefficients (K := K) A' B' C') R := by
  have hp := h.pullback (fun x : A' × B' => (f x.1, g x.2))
    (fun y : B' × C' => (g y.1, j y.2))
    (fun z : C' × A' => (j z.1, f z.2))
  convert hp using 1
  funext x y z
  simp only [pullback, matrixCoefficients, hf.eq_iff, hg.eq_iff, hj.eq_iff]

theorem rectangular_directSum_rank_of_injective
    {K ι κ A B C A' B' C' : Type*} [CommSemiring K]
    [DecidableEq ι] [DecidableEq κ]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq A'] [DecidableEq B'] [DecidableEq C'] {R : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) R)
    (e : κ → ι) (he : Function.Injective e)
    (f : A' → A) (hf : Function.Injective f)
    (g : B' → B) (hg : Function.Injective g)
    (j : C' → C) (hj : Function.Injective j) :
    RankAtMost (directSum (fun _ : κ => matrixCoefficients (K := K) A' B' C')) R := by
  have hp := h.pullback
    (fun x : κ × (A' × B') => (e x.1, (f x.2.1, g x.2.2)))
    (fun y : κ × (B' × C') => (e y.1, (g y.2.1, j y.2.2)))
    (fun z : κ × (C' × A') => (e z.1, (j z.2.1, f z.2.2)))
  convert hp using 1
  funext x y z
  simp only [pullback, directSum, matrixCoefficients,
    he.eq_iff, hf.eq_iff, hg.eq_iff, hj.eq_iff]

theorem rectangular_directSum_power_rank {K : Type*} [CommSemiring K]
    {a b c L R t : ℕ}
    (h : RankAtMost (power (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c))) t) R) :
    RankAtMost (directSum (fun _ : Fin (L ^ t) =>
      matrixCoefficients (K := K) (Fin (a ^ t)) (Fin (b ^ t)) (Fin (c ^ t)))) R := by
  have hmatrix := matrixCoefficients_directSum_rank_of_power h
  let tags : Fin (L ^ t) ≃ (Fin t → Fin L) := Fintype.equivOfCardEq (by simp)
  let rows : Fin (a ^ t) ≃ (Fin t → Fin a) := Fintype.equivOfCardEq (by simp)
  let inner : Fin (b ^ t) ≃ (Fin t → Fin b) := Fintype.equivOfCardEq (by simp)
  let cols : Fin (c ^ t) ≃ (Fin t → Fin c) := Fintype.equivOfCardEq (by simp)
  exact rectangular_directSum_rank_of_injective hmatrix tags tags.injective
    rows rows.injective inner inner.injective cols cols.injective

theorem rectangular_pow_batchRank {K : Type*} [CommSemiring K]
    {a b c L r : ℕ} (hL : 0 < L)
    (hbatch : RankAtMost (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c))) r) :
    ∀ t : ℕ, RankAtMost
      (matrixCoefficients (K := K) (Fin (a ^ t)) (Fin (b ^ t)) (Fin (c ^ t)))
      (batchRank L r t) := by
  intro t
  induction t with
  | zero => exact matrixCoefficients_fin_one_rank (K := K)
  | succ t ih =>
    let rows : Fin (a ^ (t + 1)) ≃ Fin (a ^ t) × Fin a :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    let inner : Fin (b ^ (t + 1)) ≃ Fin (b ^ t) × Fin b :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    let cols : Fin (c ^ (t + 1)) ≃ Fin (c ^ t) × Fin c :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    have hp := matrixCoefficients_rank_of_product (ih.batch_product_ceiling hbatch hL)
    have hr := rectangular_rank_of_injective hp
      rows rows.injective inner inner.injective cols cols.injective
    simpa only [batchRank_succ] using hr

theorem rectangular_polynomial_power_rank {K : Type*} [Field K] [CharZero K]
    {a b c L r d D : ℕ}
    (P : PolynomialApproximation (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c))) r d D) (t : ℕ) :
    RankAtMost (directSum (fun _ : Fin (L ^ t) =>
      matrixCoefficients (K := K) (Fin (a ^ t)) (Fin (b ^ t)) (Fin (c ^ t))))
      ((D * t + 1) * r ^ t) :=
  rectangular_directSum_power_rank (P.rank_power t)

theorem rectangular_directSum_cyclic_rank
    {K ι A B C : Type*} [CommSemiring K]
    [DecidableEq ι] [DecidableEq A] [DecidableEq B] [DecidableEq C] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r) :
    RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) B C A)) r := by
  rcases h with ⟨a, b, c, heq⟩
  refine ⟨b, c, a, ?_⟩
  funext x y z
  have hcyc : directSum (fun _ : ι => matrixCoefficients (K := K) B C A) x y z =
      directSum (fun _ : ι => matrixCoefficients (K := K) A B C) z x y := by
    have htags : (x.1 = y.1 ∧ x.1 = z.1) ↔ (z.1 = x.1 ∧ z.1 = y.1) := by
      constructor
      · rintro ⟨hxy, hxz⟩
        exact ⟨hxz.symm, hxz.symm.trans hxy⟩
      · rintro ⟨hzx, hzy⟩
        exact ⟨hzx.symm.trans hzy, hzx.symm⟩
    simp only [directSum, htags]
    split_ifs
    · exact (matrixCoefficients_cyclic (K := K) x.2 y.2 z.2).symm
    · rfl
  rw [hcyc, congrFun (congrFun (congrFun heq z) x) y]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [rankOne]
  ring

theorem rectangular_directSum_rank_lower {K : Type*} [Field K]
    {a b L r : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : RankAtMost (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin a))) r) :
    L * a ^ 2 ≤ r ∧ L * (a * b) ≤ r := by
  let : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  let : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  constructor
  · simpa only [Fintype.card_fin, pow_two] using
      directSum_matrixCoefficients_rank_lower h
  · simpa only [Fintype.card_fin] using
      directSum_matrixCoefficients_rank_lower (rectangular_directSum_cyclic_rank h)

end Tensor
end MatrixMultiplication

end

end MatrixMultiplicationAllFields
