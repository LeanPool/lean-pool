/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.RingTheory.Derivation.Lie

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.DimsData
public import LeanPool.RoyStrongSix.M2.Index

/-!
# Invariant derivations on `B = K[X, Y, Z]` (Roy §8.3.2)

For `w = (ξ, η) ∈ K^{d₀} × K^{d₁}`:

  `D_w = Σ ξ_k ∂/∂X_k + Σ η_j (Y_j ∂/∂Y_j − Z_j ∂/∂Z_j)`.

* `Dw_X`, `Dw_Y`, `Dw_Z`: the values on the variables.
* `Dw_comm`: the `D_w` commute. Their commutator is a derivation vanishing on the variables.
* `Dw_mem_FLE`: `D_w` preserves block degrees.
* `Dw_transl`: `D_w` commutes with translations.
* `Dw_IG`: `D_w` maps `I_G` into itself.
* `Dw_liftP`: on `K[X, Y]`, `D_w` is `StrongSix.Thm1.invDer w`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule StrongSix.Thm1

namespace StrongSix.M2

variable {K : Type*} [Field K] [CharZero K] {d0 d1 : ℕ}

local notation "B" => MvPolynomial (V3 d0 d1) K

/-- The invariant derivation `D_w`. -/
noncomputable def Dw (w : LieG K d0 d1) : Derivation K B B :=
  ∑ k, w.1 k • pderiv (Sum.inl k) +
    ∑ j, w.2 j • ((X (Sum.inr (Sum.inl j)) : B) • pderiv (Sum.inr (Sum.inl j)) -
      (X (Sum.inr (Sum.inr j)) : B) • pderiv (Sum.inr (Sum.inr j)))

omit [CharZero K] in
theorem Dw_apply (w : LieG K d0 d1) (P : B) :
    Dw w P = ∑ k, w.1 k • pderiv (Sum.inl k) P +
      ∑ j, w.2 j • (X (Sum.inr (Sum.inl j)) * pderiv (Sum.inr (Sum.inl j)) P -
        X (Sum.inr (Sum.inr j)) * pderiv (Sum.inr (Sum.inr j)) P) := by
  simp [Dw, Derivation.coe_sub]

omit [CharZero K] in
theorem Dw_X (w : LieG K d0 d1) (k : Fin d0) : Dw w (X (Sum.inl k)) = C (w.1 k) := by
  classical
  rw [Dw_apply]
  simp only [pderiv_X, Pi.single_apply, Sum.inl.injEq]
  simp [smul_eq_C_mul]

omit [CharZero K] in
theorem Dw_Y (w : LieG K d0 d1) (j : Fin d1) :
    Dw w (X (Sum.inr (Sum.inl j))) = w.2 j • X (Sum.inr (Sum.inl j)) := by
  classical
  rw [Dw_apply]
  simp only [pderiv_X, Pi.single_apply]
  simp []

omit [CharZero K] in
theorem Dw_Z (w : LieG K d0 d1) (j : Fin d1) :
    Dw w (X (Sum.inr (Sum.inr j))) = -(w.2 j • X (Sum.inr (Sum.inr j))) := by
  classical
  rw [Dw_apply]
  simp only [pderiv_X, Pi.single_apply]
  simp []

omit [CharZero K] in
theorem Dw_C (w : LieG K d0 d1) (c : K) : Dw w (C c) = 0 := by
  rw [Dw_apply]; simp []

omit [CharZero K] in
/-- **The `D_w` commute.** -/
theorem Dw_comm (w w' : LieG K d0 d1) (P : B) : Dw w (Dw w' P) = Dw w' (Dw w P) := by
  have h : ⁅Dw w, Dw w'⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [Derivation.commutator_apply, Derivation.zero_apply]
    rcases v with k | j | j
    · rw [Dw_X, Dw_X, Dw_C, Dw_C, sub_self]
    · rw [Dw_Y, Dw_Y, Derivation.map_smul, Derivation.map_smul, Dw_Y, Dw_Y, smul_smul, smul_smul,
        mul_comm, sub_self]
    · rw [Dw_Z, Dw_Z, Derivation.map_neg, Derivation.map_neg, Derivation.map_smul,
        Derivation.map_smul, Dw_Z, Dw_Z, smul_neg, smul_neg, smul_smul, smul_smul, mul_comm,
          sub_self]
  have := congrArg (fun D : Derivation K B B => D P) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at this
  exact sub_eq_zero.mp this

/-! ### Block degrees -/

theorem bdeg_tsub_le (β : V3 d0 d1 → Fin 2) (m n : V3 d0 d1 →₀ ℕ) (i : Fin 2) :
    bdeg β (m - n) i ≤ bdeg β m i := by
  unfold bdeg
  exact Finset.sum_le_sum fun v _ => by split_ifs <;> simp

omit [CharZero K] in
theorem Dw_monomial_mem (w : LieG K d0 d1) {D : Fin 2 → ℕ} {e : V3 d0 d1 →₀ ℕ} (he : e ∈ S blk D)
    (c : K) : Dw w (monomial e c) ∈ FLE K blk D := by
  classical
  have hm : ∀ v, (monomial (e - Finsupp.single v 1) (c * e v) : B) ∈ FLE K blk D := fun v =>
    (monomial_mem_restrictSupport (R := K)).mpr
      (Or.inl fun i => (bdeg_tsub_le blk e _ i).trans (he i))
  have he' : (monomial e c : B) ∈ FLE K blk D :=
    (monomial_mem_restrictSupport (R := K)).mpr (Or.inl he)
  have h1 : ∀ k : Fin d0, w.1 k • pderiv (Sum.inl k) (monomial e c : B) ∈ FLE K blk D := by
    intro k
    rw [pderiv_monomial]
    exact Submodule.smul_mem _ _ (hm _)
  have h2 : ∀ v : V3 d0 d1, (X v * pderiv v (monomial e c) : B) ∈ FLE K blk D := by
    intro v
    rw [X_mul_pderiv_monomial]
    exact nsmul_mem he' _
  rw [Dw_apply]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => h1 k)
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.sub_mem _ (h2 _) (h2 _)))

omit [CharZero K] in
/-- **`D_w` preserves block degrees.** -/
theorem Dw_mem_FLE (w : LieG K d0 d1) {D : Fin 2 → ℕ} {P : B} (hP : P ∈ FLE K blk D) :
    Dw w P ∈ FLE K blk D := by
  have hsum : Dw w P = ∑ e ∈ P.support, Dw w (monomial e (P.coeff e)) := by
    conv_lhs => rw [P.as_sum]
    exact map_sum (Dw w).toLinearMap _ _
  rw [hsum]
  have hP' : ∀ e ∈ P.support, e ∈ S blk D := fun e he => (mem_restrictSupport_iff (R := K)).mp hP he
  exact Submodule.sum_mem _ fun e he => Dw_monomial_mem w (hP' e he) _

/-! ### Translations, `I_G`, and `K[X, Y]` -/

omit [CharZero K] in
theorem Dw_translVar (w : LieG K d0 d1) (g : GPt K d0 d1) (v : V3 d0 d1) :
    Dw w (translVar g v) = transl g (Dw w (X v)) := by
  rcases v with k | j | j
  · simp only [translVar, Sum.elim_inl, map_add, Dw_X, Dw_C, add_zero, transl, aeval_C,
      algebraMap_eq]
  · simp only [translVar, Sum.elim_inr, Sum.elim_inl, Derivation.leibniz, Dw_C, Dw_Y,
      transl, map_smul, aeval_X, smul_eq_mul]
    rw [smul_eq_C_mul, smul_eq_C_mul]; ring
  · simp only [translVar, Sum.elim_inr, Derivation.leibniz, Dw_C, Dw_Z,       transl, map_neg,
    map_smul, aeval_X, smul_eq_mul]
    rw [smul_eq_C_mul, smul_eq_C_mul]; ring

omit [CharZero K] in
/-- **`D_w` commutes with translations.** -/
theorem Dw_transl (w : LieG K d0 d1) (g : GPt K d0 d1) (P : B) :
    Dw w (transl g P) = transl g (Dw w P) := by
  induction P using MvPolynomial.induction_on with
  | C c => rw [Dw_C, map_zero, transl, aeval_C, algebraMap_eq, Dw_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    have h1 : Dw w (p * X v) = p * Dw w (X v) + X v * Dw w p := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have h2 : Dw w (transl g (p * X v)) =
        transl g p * Dw w (transl g (X v)) + transl g (X v) * Dw w (transl g p) := by
      rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [h2, h1, map_add, map_mul, map_mul, hp,
      show transl g (X v) = translVar g v from aeval_X _ _, Dw_translVar]

omit [CharZero K] in
theorem Dw_lG (w : LieG K d0 d1) (j : Fin d1) :
    Dw w (X (Sum.inr (Sum.inl j)) * X (Sum.inr (Sum.inr j)) - 1 : B) = 0 := by
  rw [map_sub, Derivation.leibniz, Dw_Y, Dw_Z, Derivation.map_one_eq_zero]
  simp only [smul_eq_mul, mul_neg]
  rw [smul_eq_C_mul, smul_eq_C_mul]; ring

omit [CharZero K] in
/-- **`D_w` preserves `I_G`.** -/
theorem Dw_IG (w : LieG K d0 d1) {P : B} (hP : P ∈ (IG : Ideal B)) : Dw w P ∈ (IG : Ideal B) := by
  rw [IG, Ideal.ofList] at hP ⊢
  induction hP using Submodule.span_induction with
  | mem x hx =>
    simp only [lG, List.mem_ofFn, Set.mem_ofPred_eq] at hx
    obtain ⟨j, rfl⟩ := hx
    rw [Dw_lG]; exact Ideal.zero_mem _
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  | smul a x hx' hx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ (Ideal.span_le.mpr
      (fun _ h => Ideal.subset_span h) hx'))

/-- `StrongSix.Thm1.invDer` as a derivation. -/
noncomputable def invDerD (w : LieG K d0 d1) :
    Derivation K (MvPolynomial (Var d0 d1) K) (MvPolynomial (Var d0 d1) K) :=
  ∑ i, w.1 i • pderiv (Sum.inl i) + ∑ j, w.2 j • ((X (Sum.inr j) : MvPolynomial (Var d0 d1) K) •
    pderiv (Sum.inr j))

omit [CharZero K] in
theorem invDerD_apply (w : LieG K d0 d1) (P : MvPolynomial (Var d0 d1) K) :
    invDerD w P = invDer w P := by
  simp [invDerD, invDer]

omit [CharZero K] in
theorem invDerD_X (w : LieG K d0 d1) (v : Var d0 d1) :
    liftP (invDerD w (X v)) = Dw w (liftP (X v)) := by
  classical
  rw [invDerD_apply]
  rcases v with k | j
  · simp only [invDer, pderiv_X, Pi.single_apply, Sum.inl.injEq, mul_zero,
      reduceCtorEq, ite_false, smul_ite, smul_zero,       Finset.sum_const_zero, add_zero]
    simp [liftP, Dw_X, smul_eq_C_mul]
  · simp only [invDer, pderiv_X, Pi.single_apply, Sum.inr.injEq, mul_ite, mul_one, mul_zero,
      reduceCtorEq, ite_false, smul_ite, smul_zero,       Finset.sum_const_zero, zero_add]
    simp [liftP, Dw_Y]

omit [CharZero K] in
/-- **On `K[X, Y]`, `D_w` is `invDer w`.** -/
theorem Dw_liftP (w : LieG K d0 d1) (P : MvPolynomial (Var d0 d1) K) :
    Dw w (liftP P) = liftP (invDer w P) := by
  rw [← invDerD_apply]
  induction P using MvPolynomial.induction_on with
  | C c => simp [liftP]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, map_add, map_mul, map_mul, hp, invDerD_X]

end StrongSix.M2

end LeanPool
