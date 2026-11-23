/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Generic.Krylov

/-!
# Strong-potential limit: the interaction drops out of the leading coefficient

Along `v = λ u`, entries `(Hᵏ)_{yc}` have degree `≤ k − d(y)` for any `d` growing by at most one per
hop (`entry_bound`), with interaction-independent top coefficient (`entry_top`). Hence `det_top` and
`krylovPoly_ne_zero_of_top`: a nonzero leading coefficient for the free problem gives (H*) for every
configuration-diagonal interaction.
-/

@[expose] public section

namespace DFT

section

open Polynomial Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Hamiltonian along the line `v = λ u` as a polynomial matrix in `λ`. -/
noncomputable def Hl (A : Matrix C C ℝ) (V w : C → ℝ) : Matrix C C ℝ[X] :=
  A.map Polynomial.C + Matrix.diagonal (fun y => Polynomial.C (V y) + Polynomial.C (w y) * X)

/-- `d` grows by at most one along off-diagonal entries of `A`. -/
def Lip (A : Matrix C C ℝ) (d : C → ℕ) : Prop := ∀ y z, y ≠ z → A y z ≠ 0 → d y ≤ d z + 1

omit [Fintype C] in
lemma Hl_apply (A : Matrix C C ℝ) (V w : C → ℝ) (y z : C) :
    Hl A V w y z = Polynomial.C (A y z) + if y = z then
        Polynomial.C (V y) + Polynomial.C (w y) * X else 0 := by
  simp [Hl, Matrix.diagonal_apply]

/-- Coefficient of `(Hl ^ (k+1)) y c` as a sum over the middle index. -/
lemma pow_succ_coeff (A : Matrix C C ℝ) (V w : C → ℝ) (k : ℕ) (y c : C) (m : ℕ) :
    ((Hl A V w ^ (k + 1)) y c).coeff m =
      (A y y + V y) * ((Hl A V w ^ k) y c).coeff m +
      (if m = 0 then 0 else w y * ((Hl A V w ^ k) y c).coeff (m - 1)) +
      ∑ z ∈ Finset.univ.erase y, A y z * ((Hl A V w ^ k) z c).coeff m := by
  rw [pow_succ', Matrix.mul_apply, finsetSum_coeff,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ y)]
  congr 1
  · rw [Hl_apply, ite_eq_left rfl]
    have hpoly : Polynomial.C (A y y) + (Polynomial.C (V y) + Polynomial.C (w y) * X) =
        Polynomial.C (A y y + V y) + Polynomial.C (w y) * X := by
      simp [map_add]; ring
    have hc1 : (Polynomial.C (A y y + V y) * (Hl A V w ^ k) y c).coeff m =
        (A y y + V y) * ((Hl A V w ^ k) y c).coeff m := coeff_C_mul _
    have hc2 : (Polynomial.C (w y) * X * (Hl A V w ^ k) y c).coeff m =
        if m = 0 then 0 else w y * ((Hl A V w ^ k) y c).coeff (m - 1) := by
      rw [mul_assoc, coeff_C_mul]
      rcases m with _ | m
      · simp
      · rw [coeff_X_mul]; simp
    rw [hpoly, add_mul, coeff_add, hc1, hc2]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [Hl_apply, ite_eq_right (Finset.mem_erase.mp hz).1.symm, add_zero, coeff_C_mul]

/-- Degree bound: no coefficients above `k - d y`. -/
theorem entry_bound {A : Matrix C C ℝ} {d : C → ℕ} (hL : Lip A d) {c : C} (hc : d c = 0)
    (V w : C → ℝ) : ∀ k y m, k < m + d y → ((Hl A V w ^ k) y c).coeff m = 0 := by
  intro k
  induction k with
  | zero =>
    intro y m hm
    by_cases hy : y = c
    · subst hy; rw [hc] at hm; simp [pow_zero, coeff_one]; omega
    · simp [pow_zero, hy]
  | succ k ih =>
    intro y m hm
    rw [pow_succ_coeff]
    have h1 : ((Hl A V w ^ k) y c).coeff m = 0 := ih y m (by omega)
    have h2 : (if m = 0 then 0 else w y * ((Hl A V w ^ k) y c).coeff (m - 1)) = 0 := by
      split_ifs with hm0
      · rfl
      · rw [ih y (m - 1) (by omega), mul_zero]
    have h3 : ∑ z ∈ Finset.univ.erase y, A y z * ((Hl A V w ^ k) z c).coeff m = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      by_cases hA : A y z = 0
      · rw [hA, zero_mul]
      · have := hL y z (Finset.mem_erase.mp hz).1.symm hA
        rw [ih z m (by omega), mul_zero]
    rw [h1, h2, h3]; ring

/-- The top coefficient (degree `k - d y`) does not depend on the interaction. -/
theorem entry_top {A : Matrix C C ℝ} {d : C → ℕ} (hL : Lip A d) {c : C} (hc : d c = 0)
    (V V' w : C → ℝ) : ∀ k y, d y ≤ k →
      ((Hl A V w ^ k) y c).coeff (k - d y) = ((Hl A V' w ^ k) y c).coeff (k - d y) := by
  intro k
  induction k with
  | zero =>
    intro y hy
    simp [pow_zero]
  | succ k ih =>
    intro y hy
    rw [pow_succ_coeff, pow_succ_coeff]
    have e1 : ((Hl A V w ^ k) y c).coeff (k + 1 - d y) = 0 := entry_bound hL hc V w k y _ (by omega)
    have e1' : ((Hl A V' w ^ k) y c).coeff (k + 1 - d y) = 0 :=
        entry_bound hL hc V' w k y _ (by omega)
    rw [e1, e1', mul_zero, mul_zero, zero_add, zero_add]
    congr 1
    · split_ifs with h0
      · rfl
      · have : k + 1 - d y - 1 = k - d y := by omega
        rw [this, ih y (by omega)]
    · apply Finset.sum_congr rfl
      intro z hz
      by_cases hA : A y z = 0
      · rw [hA, zero_mul, zero_mul]
      · have hlip := hL y z (Finset.mem_erase.mp hz).1.symm hA
        by_cases hdz : d z + 1 = d y
        · have : k + 1 - d y = k - d z := by omega
          rw [this, ih z (by omega)]
        · rw [entry_bound hL hc V w k z _ (by omega), entry_bound hL hc V' w k z _ (by omega)]

lemma entry_natDegree {A : Matrix C C ℝ} {d : C → ℕ} (hL : Lip A d) {c : C} (hc : d c = 0)
    (V w : C → ℝ) (k : ℕ) (y : C) : ((Hl A V w ^ k) y c).natDegree ≤ k - d y :=
  natDegree_le_iff_coeff_eq_zero.mpr (fun N hN => entry_bound hL hc V w k y N (by omega))

lemma entry_zero {A : Matrix C C ℝ} {d : C → ℕ} (hL : Lip A d) {c : C} (hc : d c = 0)
    (V w : C → ℝ) {k : ℕ} {y : C} (hk : k < d y) : (Hl A V w ^ k) y c = 0 := by
  ext m; rw [entry_bound hL hc V w k y m (by omega)]; simp

/-- Top coefficient of a product of polynomials with degree bounds. -/
lemma prod_coeff_top {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) (e : ι → ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ e i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (f i).coeff (e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, (f i).natDegree ≤ e i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hdeg : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, e i := by
      refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum hs)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
      coeff_mul_add_eq_of_natDegree_le (hf a (Finset.mem_insert_self a s)) hdeg, ih hs]

/-- Products: the top coefficient depends only on the top coefficients of the factors. -/
lemma prod_top {ι : Type*} (s : Finset ι) (f g : ι → ℝ[X]) (e : ι → ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ e i) (hg : ∀ i ∈ s, (g i).natDegree ≤ e i)
    (he : ∀ i ∈ s, (f i).coeff (e i) = (g i).coeff (e i)) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, e i ∧ (∏ i ∈ s, g i).natDegree ≤ ∑ i ∈ s, e i ∧
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, e i) = (∏ i ∈ s, g i).coeff (∑ i ∈ s, e i) := by
  refine ⟨(Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum hf),
    (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum hg), ?_⟩
  rw [prod_coeff_top s f e hf, prod_coeff_top s g e hg]
  exact Finset.prod_congr rfl he

/-- The leading Krylov determinant coefficient is the determinant of the entrywise leading
coefficients, using zero for configurations out of reach. -/
theorem det_coeff_eq {A : Matrix C C ℝ} {d : C → ℕ} (hL : Lip A d) {c : C} (hc : d c = 0)
    (V w : C → ℝ) (ord : C → ℕ) :
    (kry (Hl A V w) c ord).det.coeff (∑ j, ord j - ∑ y, d y) =
      (Matrix.of fun y j => if d y ≤ ord j then
        ((Hl A V w ^ ord j) y c).coeff (ord j - d y) else 0).det := by
  simp only [Matrix.det_apply, finsetSum_coeff, kry]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Units.smul_def, Units.smul_def, zsmul_eq_mul, zsmul_eq_mul, ← Polynomial.C_eq_intCast,
    coeff_C_mul]
  congr 1
  by_cases hall : ∀ i, d (σ i) ≤ ord i
  · have hsum : ∑ j, ord j - ∑ y, d y = ∑ i, (ord i - d (σ i)) := by
      rw [Finset.sum_tsub_distrib _ (fun i _ => hall i), Equiv.sum_comp σ d]
    rw [hsum, prod_coeff_top _ _ _ (fun i _ => entry_natDegree hL hc V w _ _)]
    exact Finset.prod_congr rfl (fun i _ => by simp [hall i])
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (entry_zero hL hc V w hi)]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.not_le.mpr hi])

/-- **Interaction independence.** The coefficient of degree `Σ ord − Σ d` of the Krylov determinant
does not depend on the configuration-diagonal interaction. -/
theorem det_top {A : Matrix C C ℝ} {d : C → ℕ} (hL : Lip A d) {c : C} (hc : d c = 0)
    (V V' w : C → ℝ) (ord : C → ℕ) :
    (kry (Hl A V w) c ord).det.coeff (∑ j, ord j - ∑ y, d y) =
      (kry (Hl A V' w) c ord).det.coeff (∑ j, ord j - ∑ y, d y) := by
  rw [det_coeff_eq hL hc V w ord, det_coeff_eq hL hc V' w ord]
  congr 1
  ext y j
  simp only [of_apply]
  split_ifs with hy
  · exact entry_top hL hc V V' w _ _ hy
  · rfl

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype C] [DecidableEq V] in
lemma Hl_eval (A : Matrix C C ℝ) (Vint : C → ℝ) (n : V → C → ℝ) (u : V → ℝ) (lam : ℝ) :
    (Hl A Vint (fun y => ∑ i, u i * n i y)).map (Polynomial.eval lam) =
      hamN (A + Matrix.diagonal Vint) n (lam • u) := by
  ext a b
  by_cases h : a = b
  · subst h
    simp only [Hl, map_sum, map_mul, Finset.sum_mul, map_apply, Matrix.add_apply,
      diagonal_apply_eq, eval_add, eval_C, hamN, Pi.smul_apply, smul_eq_mul]
    rw [add_assoc]; congr 1; congr 1
    rw [← Polynomial.coe_evalRingHom, map_sum]
    apply Finset.sum_congr rfl; intro i _; simp; ring
  · simp [Hl, hamN, h]

omit [DecidableEq V] in
lemma det_kry_eval (A : Matrix C C ℝ) (Vint : C → ℝ) (n : V → C → ℝ) (u : V → ℝ) (c : C)
    (ord : C → ℕ)
    (lam : ℝ) :
    (kry (Hl A Vint (fun y => ∑ i, u i * n i y)) c ord).det.eval lam =
      (kry (hamN (A + Matrix.diagonal Vint) n (lam • u)) c ord).det := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det, ← Hl_eval]
  congr 1
  ext i j
  have hp : ((Hl A Vint (fun y => ∑ i, u i * n i y)).map (Polynomial.eval lam)) ^ ord j =
      ((Hl A Vint (fun y => ∑ i, u i * n i y)) ^ ord j).map (Polynomial.eval lam) := by
    rw [← Polynomial.coe_evalRingHom, ← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply]
  simp only [kry, RingHom.mapMatrix_apply, Matrix.map_apply, hp, Polynomial.coe_evalRingHom]

omit [DecidableEq V] in
/-- **Reduction to free fermions.** If the leading strong-potential coefficient of the
*non-interacting* Krylov determinant is nonzero along some direction `u`, then the Krylov polynomial
is nonzero for *every* configuration-diagonal interaction. -/
theorem krylovPoly_ne_zero_of_top {A : Matrix C C ℝ} {d : C → ℕ} (hL : Lip A d) {c : C}
    (hc : d c = 0)
    (n : V → C → ℝ) (u : V → ℝ) (ord : C → ℕ)
    (htop : (kry (Hl A 0 (fun y => ∑ i, u i * n i y)) c ord).det.coeff (∑ j, ord j - ∑ y, d y) ≠ 0)
    (Vint : C → ℝ) : krylovPoly (A + Matrix.diagonal Vint) n c ord ≠ 0 := by
  set w : C → ℝ := fun y => ∑ i, u i * n i y
  have hP : (kry (Hl A Vint w) c ord).det ≠ 0 := by
    intro h0
    apply htop
    rw [← det_top hL hc Vint 0 w ord, h0, coeff_zero]
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, (kry (Hl A Vint w) c ord).det.eval lam ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hP (Polynomial.funext (fun r => by simp [hall r]))
  intro hK
  apply hlam
  rw [det_kry_eval, ← eval_krylovPoly, hK, map_zero]

end

end DFT
