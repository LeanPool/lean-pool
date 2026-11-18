/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Matrix energy, Sylvester equations and cyclic trace estimates

Derived from the corresponding part of the upstream triangular Hilbert form proof.

The cyclic trace argument adapts `TwoCommuting/Auto/Sec3MatrixInequalities.lean`.
Joris Roos’s `lean-twocommuting` revision `33b69ccacc013c703a151421658187ea4d2029fb`
credits these Apache-2.0 Lean proofs to Claude.
-/

@[expose] public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

open Matrix MeasureTheory Filter Topology

namespace Triangular.Auto

noncomputable section

section HilbertSchmidt

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The squared Hilbert–Schmidt norm of a complex matrix. -/
def hsSq (R : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, ‖R i j‖ ^ 2

/-- The real Hilbert–Schmidt inner product. -/
def hsRe (X Y : Matrix m n ℂ) : ℝ := ((Xᴴ * Y).trace).re

lemma hsSq_nonneg (R : Matrix m n ℂ) : 0 ≤ hsSq R := by unfold hsSq; positivity

lemma hsRe_eq_sum (X Y : Matrix m n ℂ) :
    hsRe X Y = ∑ i, ∑ j, ((starRingEnd ℂ) (X i j) * Y i j).re := by
  simp only [hsRe, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, RCLike.star_def]
  rw [Finset.sum_comm]

lemma hsRe_self (X : Matrix m n ℂ) : hsRe X X = hsSq X := by
  rw [hsRe_eq_sum, hsSq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  norm_cast

lemma re_trace_conjTranspose_mul_self (X : Matrix m n ℂ) : ((Xᴴ * X).trace).re = hsSq X :=
  hsRe_self X

lemma hsRe_comm (X Y : Matrix m n ℂ) : hsRe X Y = hsRe Y X := by
  rw [hsRe_eq_sum, hsRe_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.conj_re ((starRingEnd ℂ) (X i j) * Y i j)]
  simp [mul_comm]

lemma hsRe_add_right (X Y Z : Matrix m n ℂ) :
    hsRe X (Y + Z) = hsRe X Y + hsRe X Z := by
  simp [hsRe, Matrix.mul_add, Matrix.trace_add]

lemma hsRe_smul_right (c : ℝ) (X Y : Matrix m n ℂ) :
    hsRe X (c • Y) = c * hsRe X Y := by
  simp [hsRe, Matrix.mul_smul, Matrix.trace_smul]

lemma hsRe_neg_right (X Y : Matrix m n ℂ) :
    hsRe X (-Y) = - hsRe X Y := by
  simp [hsRe, Matrix.mul_neg, Matrix.trace_neg]

lemma hsRe_sub_right (X Y Z : Matrix m n ℂ) :
    hsRe X (Y - Z) = hsRe X Y - hsRe X Z := by
  rw [sub_eq_add_neg, hsRe_add_right, hsRe_neg_right, ← sub_eq_add_neg]

lemma abs_hsRe_le (X Y : Matrix m n ℂ) : |hsRe X Y| ≤ √(hsSq X) * √(hsSq Y) := by
  rw [hsRe_eq_sum]
  have h1 : |∑ i, ∑ j, ((starRingEnd ℂ) (X i j) * Y i j).re| ≤ ∑ i, ∑ j, ‖X i j‖ * ‖Y i j‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (Complex.abs_re_le_norm _).trans ?_
    simp
  refine h1.trans ?_
  have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (m × n)) (fun p => ‖X p.1 p.2‖) (fun p
      => ‖Y p.1 p.2‖)
  simp only [Fintype.sum_prod_type] at this
  exact this

end HilbertSchmidt

section PositiveMatrices

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
lemma re_trace_nonneg_of_posSemidef {P : Matrix n n ℂ} (hP : P.PosSemidef) : 0 ≤ (P.trace).re := by
  have := hP.trace_nonneg
  exact (Complex.nonneg_iff.1 this).1

omit [DecidableEq m] in
lemma re_trace_conj_mul_mul_ge {B : Matrix n n ℂ} {β : ℝ}
    (hB : (B - (β : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (Z : Matrix n m ℂ) :
    β * hsSq Z ≤ ((Zᴴ * B * Z).trace).re := by
  have h := re_trace_nonneg_of_posSemidef (hB.conjTranspose_mul_mul_same Z)
  have e : Zᴴ * (B - (β : ℂ) • 1) * Z = Zᴴ * B * Z - (β : ℂ) • (Zᴴ * Z) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [e, Matrix.trace_sub, Complex.sub_re, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    re_trace_conjTranspose_mul_self] at h
  linarith

lemma sylvester_lower {B : Matrix n n ℂ} {A : Matrix m m ℂ} {α β : ℝ}
    (hB : (B - (β : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hA : (A - (α : ℂ) • (1 : Matrix m m ℂ)).PosSemidef) (Z : Matrix n m ℂ) :
    (α + β) * hsSq Z ≤ hsRe Z (B * Z + Z * A) := by
  rw [hsRe_add_right]
  have h1 : β * hsSq Z ≤ hsRe Z (B * Z) := by
    have := re_trace_conj_mul_mul_ge hB Z
    rwa [Matrix.mul_assoc] at this
  have h2 : α * hsSq Z ≤ hsRe Z (Z * A) := by
    have := re_trace_conj_mul_mul_ge hA Zᴴ
    rw [Matrix.conjTranspose_conjTranspose] at this
    have e : (Z * A * Zᴴ).trace = (Zᴴ * (Z * A)).trace := by
      rw [Matrix.trace_mul_comm]
    rw [e] at this
    have hs : hsSq Zᴴ = hsSq Z := by
      unfold hsSq; rw [Finset.sum_comm]; simp [Matrix.conjTranspose_apply]
    rw [hs] at this
    exact this
  linarith

omit [DecidableEq m] [DecidableEq n] in
lemma hsSq_mul_le {k : Type*} [Fintype k] (X : Matrix m n ℂ) (Y : Matrix n k ℂ) :
    hsSq (X * Y) ≤ hsSq X * hsSq Y := by
  unfold hsSq
  have key : ∀ i j, ‖(X * Y) i j‖ ^ 2 ≤ (∑ l, ‖X i l‖ ^ 2) * (∑ l, ‖Y l j‖ ^ 2) := by
    intro i j
    rw [Matrix.mul_apply]
    refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
    simp only [norm_mul]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖X i l‖) (fun l => ‖Y l j‖)
  calc ∑ i, ∑ j, ‖(X * Y) i j‖ ^ 2 ≤ ∑ i, ∑ j, (∑ l, ‖X i l‖ ^ 2) * (∑ l, ‖Y l j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ l, ‖X i l‖ ^ 2) * ∑ j, ∑ l, ‖Y l j‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = _ := by rw [Finset.sum_comm (f := fun j l => ‖Y l j‖ ^ 2)]

end PositiveMatrices

section SpectralEnergy

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The real trace of the continuous functional calculus of a matrix. -/
def trF (f : ℝ → ℝ) (P : Matrix n n ℂ) : ℝ := ((cfc f P).trace).re

omit [DecidableEq m] in
lemma trace_conj_unitary (U : Matrix.unitaryGroup n ℂ) (D : Matrix n n ℂ) :
    ((U : Matrix n n ℂ) * D * star (U : Matrix n n ℂ)).trace = D.trace := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]

omit [DecidableEq m] in
lemma trF_eq_sum (f : ℝ → ℝ) {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    trF f P = ∑ i, f (hP.eigenvalues i) := by
  rw [trF, hP.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_conj_unitary]
  simp [Matrix.trace_diagonal]

omit [DecidableEq m] in
lemma sum_eigenvalues_eq_roots (g : ℂ → ℝ) {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    ∑ i, g (hP.eigenvalues i) = (P.charpoly.roots.map g).sum := by
  rw [hP.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

theorem trF_conjTranspose_mul_self_eq (f : ℝ → ℝ) (hf : f 0 = 0) (R : Matrix m n ℂ) :
    trF f (Rᴴ * R) = trF f (R * Rᴴ) := by
  have h1 : (Rᴴ * R).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self R
  have h2 : (R * Rᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self R
  rw [trF_eq_sum f h1, trF_eq_sum f h2]
  set g : ℂ → ℝ := fun z => f z.re
  have e1 : ∑ i, f (h1.eigenvalues i) = ∑ i, g (h1.eigenvalues i) := by simp [g]
  have e2 : ∑ i, f (h2.eigenvalues i) = ∑ i, g (h2.eigenvalues i) := by simp [g]
  rw [e1, e2, sum_eigenvalues_eq_roots g h1, sum_eigenvalues_eq_roots g h2]
  have hc := Matrix.charpoly_mul_comm' R Rᴴ
  have hroots := congrArg Polynomial.roots hc
  rw [Polynomial.roots_mul (by
      exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_mul (by
      exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hroots
  have hm := congrArg (fun s => (s.map g).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton, g, Complex.zero_re, hf, smul_zero,
    zero_add] at hm
  exact hm.symm

/-- The real trace of the matrix power with exponent `3 / 2`. -/
def energy (P : Matrix n n ℂ) : ℝ := trF (fun x => x ^ (3 / 2 : ℝ)) P

/-- The shifted spectral energy with the value at the zero matrix subtracted. -/
def energyReg (η : ℝ) (P : Matrix n n ℂ) : ℝ :=
  trF (fun x => (x + η) ^ (3 / 2 : ℝ) - η ^ (3 / 2 : ℝ)) P

lemma energyReg_zero (P : Matrix n n ℂ) :
    energyReg 0 P = energy P := by
  simp [energyReg, energy, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]

theorem energyReg_conjTranspose_mul_self_eq (η : ℝ) (R : Matrix m n ℂ) :
    energyReg η (Rᴴ * R) = energyReg η (R * Rᴴ) :=
  trF_conjTranspose_mul_self_eq _ (by simp) R

omit [DecidableEq m] in
theorem energy_conjTranspose_mul_self_le (R : Matrix m n ℂ) :
    energy (Rᴴ * R) ≤ hsSq R ^ (3 / 2 : ℝ) := by
  have h1 : (Rᴴ * R).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self R
  have hnn : ∀ i, 0 ≤ h1.eigenvalues i :=
    fun i => Matrix.eigenvalues_conjTranspose_mul_self_nonneg R i
  have htr : ∑ i, h1.eigenvalues i = hsSq R := by
    have := h1.trace_eq_sum_eigenvalues
    rw [← re_trace_conjTranspose_mul_self, this]
    simp
  rw [energy, trF_eq_sum _ h1, ← htr]
  set S := ∑ i, h1.eigenvalues i
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => hnn i
  calc ∑ i, h1.eigenvalues i ^ (3 / 2 : ℝ) ≤ ∑ i, h1.eigenvalues i * S ^ (1 / 2 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' (hnn i) (by norm_num),
          Real.rpow_one]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hnn i) (Finset.single_le_sum (fun j _ =>
            hnn j) (Finset.mem_univ i)) (by norm_num)) (hnn i)
    _ = S ^ (3 / 2 : ℝ) := by
        rw [← Finset.sum_mul, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
          Real.rpow_add' hS (by norm_num), Real.rpow_one]

omit [Fintype m] [DecidableEq m] in
lemma hsRe_conj_unitary (U : Matrix.unitaryGroup n ℂ) (X Y : Matrix n n ℂ) :
    hsRe (star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) (star (U : Matrix n n ℂ) * Y * (U :
      Matrix n n ℂ)) = hsRe X Y := by
  unfold hsRe
  congr 1
  simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  have hU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_mul_star_self U
  have hU2 : ∀ Z : Matrix n n ℂ, (U : Matrix n n ℂ) * ((U : Matrix n n ℂ)ᴴ * Z) = Z := by
    intro Z; rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hU2]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hU, Matrix.mul_one]

omit [Fintype m] [DecidableEq m] in
lemma hsRe_diagonal_mul (a : n → ℝ) (X : Matrix n n ℂ) :
    hsRe X (diagonal (fun i => (a i : ℂ)) * X) = ∑ i, ∑ j, a i * ‖X i j‖ ^ 2 := by
  rw [hsRe_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diagonal_mul, mul_left_comm, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  norm_cast

omit [Fintype m] [DecidableEq m] in
lemma hsRe_mul_diagonal (a : n → ℝ) (X : Matrix n n ℂ) :
    hsRe X (X * diagonal (fun i => (a i : ℂ))) = ∑ i, ∑ j, a j * ‖X i j‖ ^ 2 := by
  rw [hsRe_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, ← mul_assoc, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, mul_comm]
  norm_cast

omit [Fintype m] [DecidableEq m] in
lemma sqrt_eq_conj_diagonal {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    CFC.sqrt P = (hP.1.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i =>
      ((√(hP.1.eigenvalues i) : ℝ) : ℂ)) * star (hP.1.eigenvectorUnitary : Matrix n n ℂ) := by
  rw [CFC.sqrt_eq_real_sqrt P hP.nonneg, cfcₙ_eq_cfc, hP.1.cfc_eq, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply]
  rfl

lemma ofReal_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

omit [Fintype m] [DecidableEq m] in
/-- The quadratic variational expression for the Sylvester cost. -/
def costInt (A K X : Matrix n n ℂ) : ℝ := 2 * hsRe K X - (hsRe X (A * X) + hsRe X (X * A))

/-- The nonnegative extended-real supremum defining the spectral cost of `K` at `P`. -/
def matCost (P K : Matrix n n ℂ) : ℝ≥0∞ :=
  ⨆ X : Matrix n n ℂ, ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt P) K X)

omit [Fintype m] [DecidableEq m] in
lemma costInt_conj (U : Matrix.unitaryGroup n ℂ) (a : n → ℝ) {A : Matrix n n ℂ}
    (hA : A = (U : Matrix n n ℂ) * diagonal (fun i => (a i : ℂ)) * star (U : Matrix n n ℂ))
    (K X : Matrix n n ℂ) :
    costInt A K X = ∑ i, ∑ j, (2 * ((starRingEnd ℂ) ((star (U : Matrix n n ℂ) * K * (U : Matrix
      n n ℂ)) i j) * (star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) i j).re - (a i + a j) *
      ‖(star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) i j‖ ^ 2) := by
  set D : Matrix n n ℂ := diagonal fun i => (a i : ℂ)
  set Xt := star (U : Matrix n n ℂ) * X * U
  set Kt := star (U : Matrix n n ℂ) * K * U
  have hUU : star (U : Matrix n n ℂ) * U = 1 := Unitary.coe_star_mul_self U
  have e1 : star (U : Matrix n n ℂ) * (A * X) * U = D * Xt := by
    rw [hA]
    simp only [Xt, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have e2 : star (U : Matrix n n ℂ) * (X * A) * U = Xt * D := by
    rw [hA]
    simp only [Xt, Matrix.mul_assoc, hUU, Matrix.mul_one]
  have h1 : hsRe K X = hsRe Kt Xt := (hsRe_conj_unitary U K X).symm
  have h2 : hsRe X (A * X) = hsRe Xt (D * Xt) := by
    rw [← hsRe_conj_unitary U X (A * X), e1]
  have h3 : hsRe X (X * A) = hsRe Xt (Xt * D) := by
    rw [← hsRe_conj_unitary U X (X * A), e2]
  rw [costInt, h1, h2, h3, hsRe_diagonal_mul, hsRe_mul_diagonal, hsRe_eq_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [Fintype m] [DecidableEq m] in
lemma ofReal_costTerm_le (k x : ℂ) {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal ((3 / 2) * (2 * ((starRingEnd ℂ) k * x).re - c * ‖x‖ ^ 2)) ≤ ENNReal.ofReal
      ((3 / 2) * ‖k‖ ^ 2) / ENNReal.ofReal c := by
  rcases hc.eq_or_lt with rfl | hc
  · by_cases hk : k = 0
    · subst hk; simp
    · rw [ENNReal.ofReal_zero, ENNReal.div_zero (by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)]
      exact le_top
  · rw [← ENNReal.ofReal_div_of_pos hc]
    apply ENNReal.ofReal_le_ofReal
    have h1 : ((starRingEnd ℂ) k * x).re ≤ ‖k‖ * ‖x‖ := by
      refine (Complex.re_le_norm _).trans ?_
      simp
    rw [le_div_iff₀ hc]
    nlinarith [sq_nonneg (‖k‖ - c * ‖x‖), norm_nonneg k, norm_nonneg x]

omit [Fintype m] [DecidableEq m] in
/-- The positive square root of a unitary conjugate of a nonnegative diagonal matrix. -/
lemma sqrt_eq_unitary_diagonal {P : Matrix n n ℂ} (U : Matrix.unitaryGroup n ℂ) (p : n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hPU : P = (U : Matrix n n ℂ) * diagonal (fun i => (p i : ℂ)) * star (U : Matrix n n ℂ)) :
    CFC.sqrt P = (U : Matrix n n ℂ) * diagonal (fun i => (√(p i) : ℂ)) *
      star (U : Matrix n n ℂ) := by
  have hD : (diagonal (fun i => ((√(p i) : ℝ) : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; intro i; exact_mod_cast Real.sqrt_nonneg _
  have hnn : 0 ≤ (U : Matrix n n ℂ) * diagonal (fun i => ((√(p i) : ℝ) : ℂ)) *
      star (U : Matrix n n ℂ) := by
    have := hD.mul_mul_conjTranspose_same (U : Matrix n n ℂ)
    rw [← Matrix.star_eq_conjTranspose] at this
    exact this.nonneg
  refine CFC.sqrt_unique ?_ hnn
  have hUU : star (U : Matrix n n ℂ) * U = 1 := Unitary.coe_star_mul_self U
  calc (U : Matrix n n ℂ) * diagonal (fun i => ((√(p i) : ℝ) : ℂ)) * star (U : Matrix n n ℂ) * ((U
      : Matrix n n ℂ) * diagonal (fun i => ((√(p i) : ℝ) : ℂ)) * star (U : Matrix n n ℂ))
      = (U : Matrix n n ℂ) * (diagonal (fun i => ((√(p i) : ℝ) : ℂ)) * (star (U : Matrix n n ℂ) *
          U) * diagonal (fun i => ((√(p i) : ℝ) : ℂ))) *
            star (U : Matrix n n ℂ) := by simp only [Matrix.mul_assoc]
    _ = P := by
      rw [hUU, Matrix.mul_one, Matrix.diagonal_mul_diagonal, hPU]
      congr 3; funext i
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp i)]

theorem matCost_eq_sum_of_conj {P : Matrix n n ℂ} (U : Matrix.unitaryGroup n ℂ) (p : n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hPU : P = (U : Matrix n n ℂ) * diagonal (fun i => ((p i : ℝ) : ℂ)) * star (U : Matrix n n
      ℂ)) (K : Matrix n n ℂ) :
    matCost P K = ∑ i, ∑ j, ENNReal.ofReal ((3 / 2) * ‖(star (U : Matrix n n ℂ) * K * (U :
      Matrix n n ℂ)) i j‖ ^ 2) / ENNReal.ofReal (√(p i) + √(p j)) := by
  classical
  have hA := sqrt_eq_unitary_diagonal U p hp hPU
  set c : n → n → ℝ := fun i j => √(p i) + √(p j)
  have hc : ∀ i j, 0 ≤ c i j := fun i j => by positivity
  set Kt := star (U : Matrix n n ℂ) * K * U
  have hUU : star (U : Matrix n n ℂ) * U = 1 := Unitary.coe_star_mul_self U
  have hUU' : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self U
  have hconj : ∀ Y : Matrix n n ℂ,
      star (U : Matrix n n ℂ) * ((U : Matrix n n ℂ) * Y * star (U : Matrix n n ℂ)) * U = Y := by
    intro Y
    simp only [Matrix.mul_assoc, hUU, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  apply le_antisymm
  · refine iSup_le fun X => ?_
    rw [costInt_conj U (fun i => √(p i)) hA, Finset.mul_sum]
    refine (ofReal_sum_le' _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    refine (ofReal_sum_le' _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    exact ofReal_costTerm_le _ _ (hc i j)
  · by_cases hinf : ∃ i j, c i j = 0 ∧ Kt i j ≠ 0
    · obtain ⟨i0, j0, hc0, hk0⟩ := hinf
      have htop : matCost P K = ⊤ := by
        refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
        set lam : ℝ := (r : ℝ) / (3 * ‖Kt i0 j0‖ ^ 2) + 1
        set Yt : Matrix n n ℂ := Matrix.of fun i j =>
          if i = i0 ∧ j = j0 then (lam : ℂ) * Kt i0 j0 else 0
        refine le_trans ?_ (le_iSup _ ((U : Matrix n n ℂ) * Yt * star (U : Matrix n n ℂ)))
        rw [costInt_conj U (fun i => √(p i)) hA, hconj]
        have hsum : ∑ i, ∑ j, (2 * ((starRingEnd ℂ) (Kt i j) * Yt i j).re -
            c i j * ‖Yt i j‖ ^ 2) = 2 * lam * ‖Kt i0 j0‖ ^ 2 := by
          rw [Finset.sum_eq_single i0, Finset.sum_eq_single j0]
          · simp only [Yt, Matrix.of_apply, and_self, ite_true, hc0, zero_mul, sub_zero]
            rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (Kt i0 j0)), mul_assoc,
              ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul,
              Complex.normSq_eq_norm_sq]
            norm_cast; ring
          · intro j _ hj; simp [Yt, hj]
          · simp
          · intro i _ hi
            refine Finset.sum_eq_zero fun j _ => ?_
            simp [Yt, hi]
          · simp
        rw [hsum, ← ENNReal.ofReal_coe_nnreal]
        apply ENNReal.ofReal_le_ofReal
        have hk : 0 < ‖Kt i0 j0‖ ^ 2 := by positivity
        have : (r : ℝ) ≤ 3 * ‖Kt i0 j0‖ ^ 2 * lam := by
          simp only [lam]
          have : 3 * ‖Kt i0 j0‖ ^ 2 * ((r : ℝ) / (3 * ‖Kt i0 j0‖ ^ 2)) = r := by
            field_simp
          rw [mul_add, this]
          nlinarith [NNReal.coe_nonneg r]
        nlinarith
      rw [htop]; exact le_top
    · push Not at hinf
      set Yt : Matrix n n ℂ := Matrix.of fun i j =>
        if c i j = 0 then 0 else Kt i j / (c i j : ℂ)
      refine le_trans ?_ (le_iSup _ ((U : Matrix n n ℂ) * Yt * star (U : Matrix n n ℂ)))
      rw [costInt_conj U (fun i => √(p i)) hA, hconj]
      have hterm : ∀ i j, (3 / 2) * (2 * ((starRingEnd ℂ) (Kt i j) * Yt i j).re -
          c i j * ‖Yt i j‖ ^ 2) = (3 / 2) * ‖Kt i j‖ ^ 2 / c i j := by
        intro i j
        by_cases h0 : c i j = 0
        · simp [Yt, h0, hinf i j h0]
        · have hcpos : 0 < c i j := lt_of_le_of_ne (hc i j) (Ne.symm h0)
          simp only [Yt, Matrix.of_apply, h0, ite_false]
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hc i j), div_pow]
          have : ((starRingEnd ℂ) (Kt i j) * (Kt i j / (c i j : ℂ))).re =
              ‖Kt i j‖ ^ 2 / c i j := by
            rw [mul_div_assoc', ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
            rw [show ((‖Kt i j‖ ^ 2 : ℝ) : ℂ) / (c i j : ℂ) = ((‖Kt i j‖ ^ 2 / c i j : ℝ) : ℂ)
              by push_cast; ring]
            rw [Complex.ofReal_re]
          rw [this]
          field_simp
          ring
      have hsum : (3 / 2) * ∑ i, ∑ j, (2 * ((starRingEnd ℂ) (Kt i j) * Yt i j).re -
          c i j * ‖Yt i j‖ ^ 2) = ∑ i, ∑ j, (3 / 2) * ‖Kt i j‖ ^ 2 / c i j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => hterm i j
      rw [hsum]
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => by
        have := hc i j; positivity)]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by have := hc i j; positivity)]
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases h0 : c i j = 0
      · simp [h0, hinf i j h0]
      · have hcpos : 0 < c i j := lt_of_le_of_ne (hc i j) (Ne.symm h0)
        rw [ENNReal.ofReal_div_of_pos hcpos]

omit [Fintype m] [DecidableEq m] in
theorem matCost_eq_sum {P : Matrix n n ℂ} (hP : P.PosSemidef) (K : Matrix n n ℂ) :
    matCost P K = ∑ i, ∑ j, ENNReal.ofReal ((3 / 2) * ‖(star (hP.1.eigenvectorUnitary : Matrix n
      n ℂ) * K * (hP.1.eigenvectorUnitary : Matrix n n ℂ)) i j‖ ^ 2) / ENNReal.ofReal
      (√(hP.1.eigenvalues i) + √(hP.1.eigenvalues j)) := by
  refine matCost_eq_sum_of_conj _ _ hP.eigenvalues_nonneg ?_ K
  have := hP.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  exact this

/-- The matrix `K` expressed in an orthonormal eigenbasis of a Hermitian matrix `P`. -/
def eigCoord {P : Matrix n n ℂ} (hP : P.IsHermitian) (K : Matrix n n ℂ) : Matrix n n ℂ :=
  star (hP.eigenvectorUnitary : Matrix n n ℂ) * K * (hP.eigenvectorUnitary : Matrix n n ℂ)

omit [Fintype m] [DecidableEq m] in
lemma eigCoord_add {P : Matrix n n ℂ} (hP : P.IsHermitian) (K L : Matrix n n ℂ) :
    eigCoord hP (K + L) = eigCoord hP K + eigCoord hP L := by
  simp [eigCoord, Matrix.mul_add, Matrix.add_mul]

omit [Fintype m] [DecidableEq m] in
lemma eigCoord_sub {P : Matrix n n ℂ} (hP : P.IsHermitian) (K L : Matrix n n ℂ) :
    eigCoord hP (K - L) = eigCoord hP K - eigCoord hP L := by
  simp [eigCoord, Matrix.mul_sub, Matrix.sub_mul]

omit [Fintype m] [DecidableEq m] in
lemma sqrt_eigenvalues_pos {P : Matrix n n ℂ} (hP : P.PosDef) (i : n) : 0 < √(hP.1.eigenvalues i) :=
  Real.sqrt_pos.2 (hP.eigenvalues_pos i)

omit [Fintype m] [DecidableEq m] in
theorem matCost_toReal_eq {P : Matrix n n ℂ} (hP : P.PosDef) (K : Matrix n n ℂ) :
    matCost P K ≠ ⊤ ∧ (matCost P K).toReal = ∑ i, ∑ j, (3 / 2) * ‖eigCoord hP.1 K i j‖ ^ 2 /
      (√(hP.1.eigenvalues i) + √(hP.1.eigenvalues j)) := by
  have hc : ∀ i j, 0 < √(hP.1.eigenvalues i) + √(hP.1.eigenvalues j) := fun i j =>
    add_pos (sqrt_eigenvalues_pos hP i) (sqrt_eigenvalues_pos hP j)
  have h := matCost_eq_sum hP.posSemidef K
  have e : ∀ i j, ENNReal.ofReal ((3 / 2) * ‖eigCoord hP.1 K i j‖ ^ 2) /
      ENNReal.ofReal (√(hP.1.eigenvalues i) + √(hP.1.eigenvalues j)) =
      ENNReal.ofReal ((3 / 2) * ‖eigCoord hP.1 K i j‖ ^ 2 / (√(hP.1.eigenvalues i) +
          √(hP.1.eigenvalues j))) := fun i j =>
    (ENNReal.ofReal_div_of_pos (hc i j)).symm
  simp only [eigCoord] at e
  simp only [e] at h
  have h' : matCost P K = ENNReal.ofReal (∑ i, ∑ j, (3 / 2) * ‖eigCoord hP.1 K i j‖ ^ 2 /
      (√(hP.1.eigenvalues i) + √(hP.1.eigenvalues j))) := by
    rw [h, ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => by
      have := hc i j; positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by have := hc i j; positivity)]
    rfl
  refine ⟨by rw [h']; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [h', ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    have := hc i j; positivity)]

omit [Fintype m] [DecidableEq m] in
lemma matCost_ne_top {P : Matrix n n ℂ} (hP : P.PosDef) (K : Matrix n n ℂ) :
    matCost P K ≠ ⊤ := (matCost_toReal_eq hP K).1

/-- The real polarization of the spectral cost. -/
def matCostBil (P K L : Matrix n n ℂ) :
    ℝ := ((matCost P (K + L)).toReal - (matCost P (K - L)).toReal) / 4

omit [Fintype m] [DecidableEq m] in
theorem matCostBil_eq {P : Matrix n n ℂ} (hP : P.PosDef) (K L : Matrix n n ℂ) :
    matCostBil P K L = ∑ i, ∑ j, (3 / 2) * ((starRingEnd ℂ) (eigCoord hP.1 K i j) * eigCoord
      hP.1 L i j).re / (√(hP.1.eigenvalues i) + √(hP.1.eigenvalues j)) := by
  rw [matCostBil, (matCost_toReal_eq hP _).2, (matCost_toReal_eq hP _).2, eigCoord_add,
    eigCoord_sub, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.add_apply, Matrix.sub_apply]
  set a := eigCoord hP.1 K i j
  set b := eigCoord hP.1 L i j
  have hab : ‖a + b‖ ^ 2 - ‖a - b‖ ^ 2 = 4 * ((starRingEnd ℂ) a * b).re := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
      Complex.normSq_sub]
    simp [Complex.mul_re]
    ring
  rw [div_sub_div_same, ← mul_sub, hab]
  ring

omit [Fintype m] [DecidableEq m] in
theorem matCostBil_self {P : Matrix n n ℂ} (hP : P.PosDef) (K : Matrix n n ℂ) :
    matCostBil P K K = (matCost P K).toReal := by
  rw [matCostBil_eq hP, (matCost_toReal_eq hP K).2]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  norm_cast

omit [Fintype m] [DecidableEq m] in
theorem abs_matCostBil_le {P : Matrix n n ℂ} (hP : P.PosDef) (K L : Matrix n n ℂ) :
    |matCostBil P K L| ≤ √(matCost P K).toReal * √(matCost P L).toReal := by
  rw [matCostBil_eq hP, (matCost_toReal_eq hP K).2, (matCost_toReal_eq hP L).2]
  set c : n → n → ℝ := fun i j => √(hP.1.eigenvalues i) + √(hP.1.eigenvalues j)
  have hc : ∀ i j, 0 < c i j := fun i j =>
    add_pos (sqrt_eigenvalues_pos hP i) (sqrt_eigenvalues_pos hP j)
  set a := eigCoord hP.1 K
  set b := eigCoord hP.1 L
  have key : |∑ i, ∑ j, (3 / 2) * ((starRingEnd ℂ) (a i j) * b i j).re / c i j| ≤
      ∑ i, ∑ j, (√(3 / 2) * ‖a i j‖ / √(c i j)) * (√(3 / 2) * ‖b i j‖ / √(c i j)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have h1 : |((starRingEnd ℂ) (a i j) * b i j).re| ≤ ‖a i j‖ * ‖b i j‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_; simp
    have hcij := hc i j
    rw [abs_div, abs_mul, abs_of_pos hcij, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    have : √(3 / 2) * ‖a i j‖ / √(c i j) * (√(3 / 2) * ‖b i j‖ / √(c i j)) = (3 / 2) * (‖a i j‖ * ‖b
        i j‖) / c i j := by
      rw [div_mul_div_comm, mul_mul_mul_comm, Real.mul_self_sqrt (by norm_num),
        Real.mul_self_sqrt hcij.le]
    rw [this]
    gcongr
  refine key.trans ?_
  have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (n × n)) (fun p => √(3 / 2) * ‖a p.1
      p.2‖ / √(c p.1 p.2)) (fun p => √(3 / 2) * ‖b p.1 p.2‖ / √(c p.1 p.2))
  simp only [Fintype.sum_prod_type] at this
  refine this.trans (le_of_eq ?_)
  congr 2
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (hc i j).le]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (hc i j).le]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
lemma hsSq_eq_zero_iff (Z : Matrix n n ℂ) : hsSq Z = 0 ↔ Z = 0 := by
  constructor
  · intro h
    have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
      fun j _ => sq_nonneg ‖Z i j‖)).1 h
    ext i j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖Z i j‖)).1 (h' i
        (Finset.mem_univ i)) j (Finset.mem_univ j)
    simpa using this
  · rintro rfl; simp [hsSq]

omit [Fintype m] [DecidableEq m] in
lemma sqrt_hsSq_le_sylvester {B A : Matrix n n ℂ} {α β : ℝ} (hαβ : 0 < α + β)
    (hB : (B - (β : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hA : (A - (α : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (Z : Matrix n n ℂ) :
    √(hsSq Z) ≤ √(hsSq (B * Z + Z * A)) / (α + β) := by
  have h1 := sylvester_lower hB hA Z
  have h2 := (le_abs_self _).trans (abs_hsRe_le Z (B * Z + Z * A))
  rw [le_div_iff₀ hαβ]
  rcases (hsSq_nonneg Z).eq_or_lt with h0 | hpos
  · rw [← h0, Real.sqrt_zero, zero_mul]; exact Real.sqrt_nonneg _
  · have hs : 0 < √(hsSq Z) := Real.sqrt_pos.2 hpos
    have : (α + β) * (√(hsSq Z) * √(hsSq Z)) ≤ √(hsSq Z) * √(hsSq (B * Z + Z * A)) := by
      rw [Real.mul_self_sqrt (hsSq_nonneg Z)]; linarith
    nlinarith

open Classical in
/-- A chosen solution of the Sylvester equation `A * X + X * A = Y`, or zero if none exists. -/
def sylvSol (A Y : Matrix n n ℂ) : Matrix n n ℂ :=
  if h : ∃ X, A * X + X * A = Y then h.choose else 0

omit [Fintype m] [DecidableEq m] in
theorem sylvSol_spec {A : Matrix n n ℂ} {α : ℝ} (hα : 0 < α)
    (hA : (A - (α : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (Y : Matrix n n ℂ) :
    A * sylvSol A Y + sylvSol A Y * A = Y ∧ ∀ X, A * X + X * A = Y → X = sylvSol A Y := by
  let L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
    { toFun := fun X => A * X + X * A
      map_add' := fun X Z => by simp only [Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c X => by simp [smul_add] }
  have hinj : Function.Injective L := by
    intro X Z hXZ
    have h0 : A * (X - Z) + (X - Z) * A = 0 := by
      have : A * X + X * A = A * Z + Z * A := hXZ
      rw [Matrix.mul_sub, Matrix.sub_mul]
      rw [show A * X - A * Z + (X * A - Z * A) = (A * X + X * A) - (A * Z + Z * A) by abel,
        this, sub_self]
    have := sqrt_hsSq_le_sylvester (by linarith : 0 < α + α) hA hA (X - Z)
    rw [h0] at this
    simp only [hsSq, Matrix.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, Real.sqrt_zero, zero_div] at this
    have h2 : hsSq (X - Z) = 0 := by
      have := Real.sqrt_eq_zero'.1 (le_antisymm this (Real.sqrt_nonneg _))
      exact le_antisymm this (hsSq_nonneg _)
    exact sub_eq_zero.1 ((hsSq_eq_zero_iff _).1 h2)
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.1 hinj
  have hex : ∃ X, A * X + X * A = Y := hsurj Y
  have hspec : A * sylvSol A Y + sylvSol A Y * A = Y := by
    rw [sylvSol, dite_eq_left hex]; exact hex.choose_spec
  refine ⟨hspec, fun X hX => hinj ?_⟩
  change A * X + X * A = A * sylvSol A Y + sylvSol A Y * A
  rw [hX, hspec]

end SpectralEnergy

section EnergyRegularization

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma sqrt_sub_posSemidef {Y : Matrix n n ℂ} {η : ℝ} (hη : 0 ≤ η)
    (hY : (Y - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    (CFC.sqrt Y - ((√η : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  have halg : ∀ r : ℝ≥0, algebraMap ℝ≥0 (Matrix n n ℂ) r = ((r : ℝ) : ℂ) • 1 := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  set r : ℝ≥0 := ⟨η, hη⟩ with hr
  have h1 : algebraMap ℝ≥0 (Matrix n n ℂ) r ≤ Y := by
    rw [halg, Matrix.le_iff]; exact hY
  have h2 := CFC.sqrt_le_sqrt _ _ h1
  rw [CFC.sqrt_algebraMap, halg] at h2
  rw [Matrix.le_iff] at h2
  convert h2 using 3
  rw [Real.coe_sqrt]; rfl

omit [DecidableEq n] in
lemma tendsto_hsSq_sub {α : Type*} {l : Filter α} {f : α → Matrix n n ℂ} {g : Matrix n n ℂ}
    (h : ∀ i j, Tendsto (fun a => f a i j) l (𝓝 (g i j))) :
    Tendsto (fun a => hsSq (f a - g)) l (𝓝 0) := by
  have : (0 : ℝ) = ∑ i : n, ∑ j : n, ‖(0 : ℂ)‖ ^ 2 := by simp
  rw [this]
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  refine ((continuous_norm.tendsto _).comp ?_).pow 2
  have := (h i j).sub (tendsto_const_nhds (x := g i j))
  simpa using this

omit [DecidableEq n] in
lemma norm_entry_le_sqrt_hsSq (Z : Matrix n n ℂ) (i j : n) : ‖Z i j‖ ≤ √(hsSq Z) := by
  refine Real.le_sqrt_of_sq_le ?_
  unfold hsSq
  refine (Finset.single_le_sum (f := fun j => ‖Z i j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ
      j)).trans ?_
  exact Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖ ^ 2) (fun i _ => Finset.sum_nonneg fun j _
      => sq_nonneg _) (Finset.mem_univ i)

theorem hasDerivAt_sqrt_curve {Y : ℝ → Matrix n n ℂ} {Y' : Matrix n n ℂ} {θ₀ η : ℝ} (hη : 0 < η)
    (hpos : ∀ θ, (Y θ - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hY : ∀ i j, HasDerivAt (fun θ => Y θ i j) (Y' i j) θ₀) :
    ∀ i j, HasDerivAt (fun θ => CFC.sqrt (Y θ) i j) (sylvSol (CFC.sqrt (Y θ₀)) Y' i j) θ₀ := by
  set A : ℝ → Matrix n n ℂ := fun θ => CFC.sqrt (Y θ)
  set A0 := A θ₀
  set X := sylvSol A0 Y'
  have hs : 0 < √η := Real.sqrt_pos.2 hη
  have hAlow : ∀ θ, (A θ - ((√η : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
    fun θ => sqrt_sub_posSemidef hη.le (hpos θ)
  have hX := (sylvSol_spec hs (hAlow θ₀) Y').1
  have hAA : ∀ θ, A θ * A θ = Y θ := fun θ =>
    CFC.sqrt_mul_sqrt_self _ (by
      have := (hpos θ).add (Matrix.PosSemidef.smul (Matrix.PosSemidef.one) (by
        exact_mod_cast hη.le : (0 : ℂ) ≤ (η : ℂ)))
      simp only [sub_add_cancel] at this
      exact this.nonneg)
  have hsyl : ∀ θ Z, √(hsSq Z) ≤ √(hsSq (A θ * Z + Z * A0)) / (√η + √η) := fun θ Z =>
    sqrt_hsSq_le_sylvester (by linarith) (hAlow θ) (hAlow θ₀) Z
  have hYc : ∀ i j, Tendsto (fun θ => Y θ i j) (𝓝 θ₀) (𝓝 (Y θ₀ i j)) := fun i j =>
    (hY i j).continuousAt.tendsto
  have hAc : Tendsto (fun θ => √(hsSq (A θ - A0))) (𝓝 θ₀) (𝓝 0) := by
    have hY0 := tendsto_hsSq_sub hYc
    have hb : Tendsto (fun θ => √(hsSq (Y θ - Y θ₀)) / (√η + √η)) (𝓝 θ₀) (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hY0
      simpa using this.div_const (√η + √η)
    refine squeeze_zero (fun θ => Real.sqrt_nonneg _) (fun θ => ?_) hb
    have := hsyl θ (A θ - A0)
    have e : A θ * (A θ - A0) + (A θ - A0) * A0 = Y θ - Y θ₀ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← hAA θ, ← hAA θ₀]
      abel
    rwa [e] at this
  have hD : ∀ i j, Tendsto (fun θ => ((θ - θ₀)⁻¹ • (Y θ - Y θ₀)) i j) (𝓝[≠] θ₀) (𝓝 (Y' i j)) := by
    intro i j
    have := (hasDerivAt_iff_tendsto_slope.1 (hY i j))
    refine this.congr fun θ => ?_
    simp [slope_def_module, Matrix.smul_apply, Matrix.sub_apply]
  have hD0 := tendsto_hsSq_sub hD
  have hQ : Tendsto (fun θ => √(hsSq ((θ - θ₀)⁻¹ • (A θ - A0) - X))) (𝓝[≠] θ₀) (𝓝 0) := by
    have hb : Tendsto (fun θ => (√(hsSq ((θ - θ₀)⁻¹ • (Y θ - Y θ₀) - Y')) +
        √(hsSq (A θ - A0)) * √(hsSq X)) / (√η + √η)) (𝓝[≠] θ₀) (𝓝 0) := by
      have h1 := (Real.continuous_sqrt.tendsto 0).comp hD0
      have h2 := (hAc.mono_left (nhdsWithin_le_nhds (s := {θ₀}ᶜ))).mul_const (√(hsSq X))
      have := (h1.add h2).div_const (√η + √η)
      simpa using this
    refine squeeze_zero (fun θ => Real.sqrt_nonneg _) (fun θ => ?_) hb
    set Q := (θ - θ₀)⁻¹ • (A θ - A0)
    have e : A θ * (Q - X) + (Q - X) * A0 = ((θ - θ₀)⁻¹ • (Y θ - Y θ₀) - Y') - (A θ - A0) * X := by
      have e1 : A θ * Q + Q * A0 = (θ - θ₀)⁻¹ • (Y θ - Y θ₀) := by
        simp only [Q, Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
        congr 1
        rw [Matrix.mul_sub, Matrix.sub_mul, ← hAA θ, ← hAA θ₀]
        abel
      rw [Matrix.mul_sub, Matrix.sub_mul, ← hX]
      rw [show A θ * Q - A θ * X + (Q * A0 - X * A0) = (A θ * Q + Q * A0) - (A θ * X + X * A0) by
          abel, e1, Matrix.sub_mul]
      abel
    have h1 := hsyl θ (Q - X)
    rw [e] at h1
    refine h1.trans ?_
    gcongr
    have h3 : √(hsSq (((θ - θ₀)⁻¹ • (Y θ - Y θ₀) - Y') - (A θ - A0) * X)) ≤
        √(hsSq ((θ - θ₀)⁻¹ • (Y θ - Y θ₀) - Y')) + √(hsSq ((A θ - A0) * X)) := by
      set U := (θ - θ₀)⁻¹ • (Y θ - Y θ₀) - Y'
      set V := (A θ - A0) * X
      have hUV := hsRe_comm U V
      have hexp : hsSq (U - V) = hsSq U - 2 * hsRe U V + hsSq V := by
        rw [← hsRe_self, ← hsRe_self U, ← hsRe_self V]
        unfold hsRe
        simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
          Complex.sub_re]
        have : ((Vᴴ * U).trace).re = ((Uᴴ * V).trace).re := by
          have := hsRe_comm V U; unfold hsRe at this; exact this
        linarith
      have hcs := abs_hsRe_le U V
      rw [Real.sqrt_le_left (by positivity), hexp]
      have hU := Real.sq_sqrt (hsSq_nonneg U)
      have hV := Real.sq_sqrt (hsSq_nonneg V)
      nlinarith [abs_le.1 hcs, Real.sqrt_nonneg (hsSq U), Real.sqrt_nonneg (hsSq V)]
    refine h3.trans (add_le_add le_rfl ?_)
    rw [← Real.sqrt_mul (hsSq_nonneg _)]
    exact Real.sqrt_le_sqrt (hsSq_mul_le _ _)
  intro i j
  rw [hasDerivAt_iff_tendsto_slope]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun θ => norm_nonneg _) (fun θ => ?_) hQ
  have := norm_entry_le_sqrt_hsSq ((θ - θ₀)⁻¹ • (A θ - A0) - X) i j
  refine le_trans (le_of_eq ?_) this
  simp [slope_def_module, Matrix.smul_apply, Matrix.sub_apply, A, A0]

omit [Fintype n] in
lemma posDef_add_smul_one {P : Matrix n n ℂ} (hP : P.PosSemidef) {η : ℝ} (hη : 0 < η) :
    (P + (η : ℂ) • (1 : Matrix n n ℂ)).PosDef :=
  Matrix.PosDef.posSemidef_add hP (Matrix.PosDef.one.smul (by exact_mod_cast hη))

omit [Fintype n] in
lemma add_smul_one_sub_posSemidef {P : Matrix n n ℂ} (hP : P.PosSemidef) (η : ℝ) :
    (P + (η : ℂ) • (1 : Matrix n n ℂ) - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  simpa using hP

omit [DecidableEq n] in
lemma hasDerivAt_re_trace_mul {F G : ℝ → Matrix n n ℂ} {F' G' : Matrix n n ℂ} {θ₀ : ℝ}
    (hF : ∀ i j, HasDerivAt (fun θ => F θ i j) (F' i j) θ₀)
    (hG : ∀ i j, HasDerivAt (fun θ => G θ i j) (G' i j) θ₀) :
    HasDerivAt (fun θ => ((F θ * G θ).trace).re) (((F' * G θ₀ + F θ₀ * G').trace).re) θ₀ := by
  have h : HasDerivAt (fun θ => (F θ * G θ).trace) ((F' * G θ₀ + F θ₀ * G').trace) θ₀ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.add_apply,
      ← Finset.sum_add_distrib]
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun k _ => ?_
    exact (hF i k).mul (hG k i)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ₀ h

lemma add_smul_one_eq_conj {P : Matrix n n ℂ} (hP : P.IsHermitian) (c : ℝ) :
    P + (c : ℂ) • 1 = (hP.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i =>
      ((hP.eigenvalues i + c : ℝ) : ℂ)) * star (hP.eigenvectorUnitary : Matrix n n ℂ) := by
  have hUU : (hP.eigenvectorUnitary : Matrix n n ℂ) *
      star (hP.eigenvectorUnitary : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self _
  conv_lhs => rw [hP.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [show diagonal (fun i => ((hP.eigenvalues i + c : ℝ) : ℂ)) =
    diagonal (RCLike.ofReal ∘ hP.eigenvalues) + (c : ℂ) • 1 by
      ext i j; by_cases h : i = j <;> simp [h]]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU]

lemma sqrt_add_smul_eq {P : Matrix n n ℂ} (hP : P.PosSemidef) {η : ℝ} (hη : 0 ≤ η) :
    CFC.sqrt (P + (η : ℂ) • 1) = (hP.1.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i =>
      ((√(hP.1.eigenvalues i + η) : ℝ) : ℂ)) * star (hP.1.eigenvectorUnitary : Matrix n n ℂ) :=
  sqrt_eq_unitary_diagonal _ _ (fun i => add_nonneg (hP.eigenvalues_nonneg i) hη)
    (add_smul_one_eq_conj hP.1 η)

lemma energyReg_eq_trace {P : Matrix n n ℂ} (hP : P.PosSemidef) {η : ℝ} (hη : 0 ≤ η) :
    energyReg η P = (((P + (η : ℂ) • 1) * CFC.sqrt (P + (η : ℂ) • 1)).trace).re - η ^ (3 / 2 :
      ℝ) * Fintype.card n := by
  set U := hP.1.eigenvectorUnitary
  set p := hP.1.eigenvalues
  have hUU : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self U
  have hU'U : star (U : Matrix n n ℂ) * U = 1 := Unitary.coe_star_mul_self U
  have hp : ∀ i, 0 ≤ p i := hP.eigenvalues_nonneg
  have hPY : P + (η : ℂ) • 1 = (U : Matrix n n ℂ) *
      diagonal (fun i => ((p i + η : ℝ) : ℂ)) * star (U : Matrix n n ℂ) :=
    add_smul_one_eq_conj hP.1 η
  have hsq := sqrt_add_smul_eq hP hη
  rw [energyReg, trF_eq_sum _ hP.1, hsq, hPY]
  have : (U : Matrix n n ℂ) * diagonal (fun i => ((p i + η : ℝ) : ℂ)) * star (U : Matrix n n ℂ) *
      ((U : Matrix n n ℂ) * diagonal (fun i => ((√(p i + η) : ℝ) : ℂ)) *
        star (U : Matrix n n ℂ)) = (U : Matrix n n ℂ) *
          diagonal (fun i => (((p i + η) * √(p i + η) : ℝ) : ℂ)) * star (U : Matrix n n ℂ) := by
    calc _ = (U : Matrix n n ℂ) * (diagonal (fun i => ((p i + η : ℝ) : ℂ)) * (star (U : Matrix n n
        ℂ) * U) * diagonal (fun i => ((√(p i + η) : ℝ) : ℂ))) *
              star (U : Matrix n n ℂ) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hU'U, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        congr 3; funext i; push_cast; ring
  rw [this, trace_conj_unitary, Matrix.trace_diagonal, Complex.re_sum, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_re, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' (by linarith [hp i]) (by norm_num), Real.rpow_one, Real.sqrt_eq_rpow]
  · simp [mul_comm]

theorem hasDerivAt_energyReg {P : ℝ → Matrix n n ℂ} {P' : Matrix n n ℂ} {θ₀ η : ℝ} (hη : 0 < η)
    (hP : ∀ θ, (P θ).PosSemidef) (hd : ∀ i j, HasDerivAt (fun θ => P θ i j) (P' i j) θ₀) :
    HasDerivAt (fun θ => energyReg η (P θ)) ((3 / 2) * ((CFC.sqrt (P θ₀ + (η : ℂ) • 1) *
      P').trace).re) θ₀ := by
  set Y : ℝ → Matrix n n ℂ := fun θ => P θ + (η : ℂ) • 1
  have hY : ∀ i j, HasDerivAt (fun θ => Y θ i j) (P' i j) θ₀ := by
    intro i j
    have := (hd i j).add_const (((η : ℂ) • (1 : Matrix n n ℂ)) i j)
    simpa [Y] using this
  have hpos : ∀ θ, (Y θ - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := fun θ =>
    add_smul_one_sub_posSemidef (hP θ) η
  have hA := hasDerivAt_sqrt_curve hη hpos hY
  set A0 := CFC.sqrt (Y θ₀)
  set X := sylvSol A0 P'
  have hs : 0 < √η := Real.sqrt_pos.2 hη
  have hXs : A0 * X + X * A0 = P' := (sylvSol_spec hs (sqrt_sub_posSemidef hη.le (hpos θ₀)) P').1
  have hT := hasDerivAt_re_trace_mul hY hA
  have heq : ∀ θ, energyReg η (P θ) = ((Y θ * CFC.sqrt (Y θ)).trace).re -
      η ^ (3 / 2 : ℝ) * Fintype.card n := fun θ => energyReg_eq_trace (hP θ) hη.le
  simp_rw [heq]
  refine (hT.sub_const _).congr_deriv ?_
  have hAA : A0 * A0 = Y θ₀ := CFC.sqrt_mul_sqrt_self _ (by
    have := (posDef_add_smul_one (hP θ₀) hη).posSemidef; exact this.nonneg)
  have h1 : (Y θ₀ * X).trace = (1 / 2 : ℂ) * (A0 * P').trace := by
    have e : (A0 * P').trace = (A0 * (A0 * X + X * A0)).trace := by rw [hXs]
    have e2 : (A0 * (X * A0)).trace = (A0 * A0 * X).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    rw [e, Matrix.mul_add, Matrix.trace_add, e2, ← Matrix.mul_assoc, ← hAA]
    ring
  rw [Matrix.trace_add, h1, Matrix.trace_mul_comm P']
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  ring

omit [Fintype n] in
lemma exists_lower_bound_of_posDef [Finite n] {Y : Matrix n n ℂ} (hY : Y.PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ (Y - (μ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  let := Fintype.ofFinite n
  by_cases hn : IsEmpty n
  · exact ⟨1, one_pos, by
      rw [show Y - ((1 : ℝ) : ℂ) • (1 : Matrix n n ℂ) = 0 from Subsingleton.elim _ _]
      exact Matrix.PosSemidef.zero⟩
  rw [not_isEmpty_iff] at hn
  set μ := Finset.univ.inf' Finset.univ_nonempty (fun i => hY.1.eigenvalues i)
  have hμ : 0 < μ := (Finset.lt_inf'_iff _).2 fun i _ => hY.eigenvalues_pos i
  refine ⟨μ, hμ, ?_⟩
  have e := add_smul_one_eq_conj hY.1 (-μ)
  rw [show Y - (μ : ℂ) • 1 = Y + ((-μ : ℝ) : ℂ) • 1 by push_cast; rw [neg_smul, sub_eq_add_neg]]
  rw [e]
  have hD : (diagonal (fun i => ((hY.1.eigenvalues i + -μ : ℝ) : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    have : μ ≤ hY.1.eigenvalues i := Finset.inf'_le _ (Finset.mem_univ i)
    exact_mod_cast (by linarith : (0 : ℝ) ≤ hY.1.eigenvalues i + -μ)
  have := hD.mul_mul_conjTranspose_same (hY.1.eigenvectorUnitary : Matrix n n ℂ)
  rwa [← Matrix.star_eq_conjTranspose] at this

lemma eigCoord_sylvSol {Y : Matrix n n ℂ} (hY : Y.PosDef) (K : Matrix n n ℂ) (i j : n) :
    eigCoord hY.1 (sylvSol (CFC.sqrt Y) K) i j = eigCoord hY.1 K i j / ((√(hY.1.eigenvalues i) +
      √(hY.1.eigenvalues j) : ℝ) : ℂ) := by
  obtain ⟨U, hUdef⟩ : ∃ U, U = hY.1.eigenvectorUnitary := ⟨_, rfl⟩
  set a : n → ℝ := fun i => √(hY.1.eigenvalues i)
  have hE : ∀ Z, eigCoord hY.1 Z = star (U : Matrix n n ℂ) * Z * (U : Matrix n n ℂ) := by
    intro Z; rw [hUdef]; rfl
  have hU'U : star (U : Matrix n n ℂ) * U = 1 := Unitary.coe_star_mul_self U
  have hl : ∀ Z : Matrix n n ℂ, star (U : Matrix n n ℂ) * ((U : Matrix n n ℂ) * Z) = Z := by
    intro Z; rw [← Matrix.mul_assoc, hU'U, Matrix.one_mul]
  obtain ⟨μ, hμ, hμY⟩ := exists_lower_bound_of_posDef hY
  have hX := (sylvSol_spec (Real.sqrt_pos.2 hμ) (sqrt_sub_posSemidef hμ.le hμY) K).1
  set X := sylvSol (CFC.sqrt Y) K
  have hsq : CFC.sqrt Y = (U : Matrix n n ℂ) * diagonal (fun i => (a i : ℂ)) *
      star (U : Matrix n n ℂ) := by rw [hUdef]; exact sqrt_eq_conj_diagonal hY.posSemidef
  have key : diagonal (fun i => (a i : ℂ)) * eigCoord hY.1 X + eigCoord hY.1 X *
      diagonal (fun i => (a i : ℂ)) = eigCoord hY.1 K := by
    rw [← hX]
    simp only [hE, hsq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hl, hU'U,
      Matrix.mul_one]
  have := congrFun (congrFun key i) j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  have hc : ((a i + a j : ℝ) : ℂ) ≠ 0 := by
    have := add_pos (sqrt_eigenvalues_pos hY i) (sqrt_eigenvalues_pos hY j)
    exact_mod_cast this.ne'
  rw [← this, eq_div_iff hc]
  push_cast
  ring

lemma re_trace_sylvSol_mul {Y K G : Matrix n n ℂ} (hY : Y.PosDef) (hG : G.IsHermitian) :
    (3 / 2) * ((sylvSol (CFC.sqrt Y) K * G).trace).re = matCostBil Y K G := by
  obtain ⟨U, hUdef⟩ : ∃ U, U = hY.1.eigenvectorUnitary := ⟨_, rfl⟩
  have hE : ∀ Z, eigCoord hY.1 Z = star (U : Matrix n n ℂ) * Z * (U : Matrix n n ℂ) := by
    intro Z; rw [hUdef]; rfl
  have hUU : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self U
  set X := sylvSol (CFC.sqrt Y) K
  have htr : (X * G).trace = (eigCoord hY.1 X * eigCoord hY.1 G).trace := by
    rw [hE, hE]
    calc (X * G).trace = (star (U : Matrix n n ℂ) * (X * G) * U).trace := by
          rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
      _ = _ := by
          congr 1
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (U : Matrix n n ℂ), hUU, Matrix.one_mul]
  have hGt : ∀ i j, eigCoord hY.1 G j i = star (eigCoord hY.1 G i j) := by
    intro i j
    have hH : (eigCoord hY.1 G).IsHermitian := by
      rw [hE, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        hG.eq, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    exact (hH.apply j i).symm
  rw [htr, matCostBil_eq hY, Matrix.trace, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag, Matrix.mul_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eigCoord_sylvSol hY K i j, hGt i j]
  set c := √(hY.1.eigenvalues i) + √(hY.1.eigenvalues j)
  set k := eigCoord hY.1 K i j
  set g := eigCoord hY.1 G i j
  have hcne : c ≠ 0 := (add_pos (sqrt_eigenvalues_pos hY i) (sqrt_eigenvalues_pos hY j)).ne'
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hcne
  have e : k / (c : ℂ) * star g = ((1 / c : ℝ) : ℂ) * (k * star g) := by
    push_cast; field_simp
  have e2 : (k * star g).re = ((starRingEnd ℂ) k * g).re := by
    rw [RCLike.star_def, ← Complex.conj_re]; simp
  rw [e, Complex.re_ofReal_mul, e2]
  field_simp

theorem hasDerivAt_energy_hessian {P G : ℝ → Matrix n n ℂ} {P' G' : Matrix n n ℂ} {θ₀ η : ℝ}
    (hη : 0 < η) (hP : ∀ θ, (P θ).PosSemidef)
    (hd : ∀ i j, HasDerivAt (fun θ => P θ i j) (P' i j) θ₀)
    (hG : ∀ i j, HasDerivAt (fun θ => G θ i j) (G' i j) θ₀) (hGH : (G θ₀).IsHermitian) :
    HasDerivAt (fun θ => (3 / 2) * ((CFC.sqrt (P θ + (η : ℂ) • 1) * G θ).trace).re) (matCostBil
      (P θ₀ + (η : ℂ) • 1) P' (G θ₀) + (3 / 2) * ((CFC.sqrt (P θ₀ + (η : ℂ) • 1) * G').trace).re)
      θ₀ := by
  set Y : ℝ → Matrix n n ℂ := fun θ => P θ + (η : ℂ) • 1
  have hY : ∀ i j, HasDerivAt (fun θ => Y θ i j) (P' i j) θ₀ := by
    intro i j
    have := (hd i j).add_const (((η : ℂ) • (1 : Matrix n n ℂ)) i j)
    simpa [Y] using this
  have hpos : ∀ θ, (Y θ - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := fun θ =>
    add_smul_one_sub_posSemidef (hP θ) η
  have hA := hasDerivAt_sqrt_curve hη hpos hY
  have hT := (hasDerivAt_re_trace_mul hA hG).const_mul (3 / 2 : ℝ)
  refine hT.congr_deriv ?_
  rw [Matrix.trace_add, Complex.add_re, mul_add,
    re_trace_sylvSol_mul (posDef_add_smul_one (hP θ₀) hη) hGH]

omit [DecidableEq n] in
lemma sqrt_smul_eq {n : Type*} [Fintype n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) {a : ℝ}
    (ha : 0 ≤ a) :
    open scoped Classical in CFC.sqrt ((a : ℂ) • Q) = ((√a : ℝ) : ℂ) • CFC.sqrt Q := by
  classical
  have hs : (CFC.sqrt Q).PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hnn : 0 ≤ ((√a : ℝ) : ℂ) • CFC.sqrt Q := (hs.smul (by exact_mod_cast Real.sqrt_nonneg a : (0
      : ℂ) ≤ ((√a : ℝ) : ℂ))).nonneg
  refine CFC.sqrt_unique ?_ hnn
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, CFC.sqrt_mul_sqrt_self Q hQ.nonneg,
    ← Complex.ofReal_mul, Real.mul_self_sqrt ha]

omit [DecidableEq n] in
lemma quadForm_mono {A B : Matrix n n ℂ} (hAB : (B - A).PosSemidef) (X : Matrix n n ℂ) :
    hsRe X (A * X) + hsRe X (X * A) ≤ hsRe X (B * X) + hsRe X (X * B) := by
  classical
  have h0 : ((B - A) - ((0 : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by simpa using hAB
  have := sylvester_lower h0 h0 X
  simp only [add_zero, zero_mul] at this
  rw [hsRe_add_right, Matrix.sub_mul, Matrix.mul_sub, hsRe_sub_right, hsRe_sub_right] at this
  linarith

theorem matCost_comparison {P Q : Matrix n n ℂ} (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 < a)
    (hPQ : P ≤ (a : ℂ) • Q) (K : Matrix n n ℂ) :
    ENNReal.ofReal (√a)⁻¹ * matCost Q K ≤ matCost P K := by
  have hsa : 0 < √a := Real.sqrt_pos.2 ha
  have hsqrt : CFC.sqrt P ≤ ((√a : ℝ) : ℂ) • CFC.sqrt Q := by
    rw [← sqrt_smul_eq hQ ha.le]; exact CFC.sqrt_le_sqrt _ _ hPQ
  rw [matCost, matCost, ENNReal.mul_iSup]
  refine iSup_le fun Z => ?_
  refine le_trans ?_ (le_iSup _ ((√a)⁻¹ • Z))
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hmono := quadForm_mono (Matrix.le_iff.1 hsqrt) ((√a)⁻¹ • Z)
  unfold costInt
  have e1 : hsRe K ((√a)⁻¹ • Z) = (√a)⁻¹ * hsRe K Z := hsRe_smul_right _ _ _
  have e2 : hsRe ((√a)⁻¹ • Z) ((((√a : ℝ) : ℂ) • CFC.sqrt Q) * ((√a)⁻¹ • Z)) +
      hsRe ((√a)⁻¹ • Z) (((√a)⁻¹ • Z) * (((√a : ℝ) : ℂ) • CFC.sqrt Q)) =
      (√a)⁻¹ * (hsRe Z (CFC.sqrt Q * Z) + hsRe Z (Z * CFC.sqrt Q)) := by
    have hcs : ((√a : ℝ) : ℂ) • CFC.sqrt Q = (√a) • CFC.sqrt Q := Complex.coe_smul _ _
    have hsc : (√a)⁻¹ * √a = 1 := inv_mul_cancel₀ hsa.ne'
    have hsc' : √a * (√a)⁻¹ = 1 := mul_inv_cancel₀ hsa.ne'
    have hc : ∀ (c : ℝ) (X Y : Matrix n n ℂ), hsRe (c • X) Y = c * hsRe X Y := by
      intro c X Y; rw [hsRe_comm, hsRe_smul_right, hsRe_comm]
    rw [hcs]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsc, hsc', one_smul, hc]
    ring
  rw [e1] at *
  nlinarith [hmono, e2]

omit [Fintype n] [DecidableEq n] in
lemma re_diag_le_of_sub_posSemidef {A B : Matrix n n ℂ} (hAB : (B - A).PosSemidef) (i : n) :
    (A i i).re ≤ (B i i).re := by
  have := hAB.diag_nonneg (i := i)
  rw [Matrix.sub_apply] at this
  have := (Complex.nonneg_iff.1 this).1
  rw [Complex.sub_re] at this
  linarith

end EnergyRegularization

section SylvesterCost

variable {n : Type*} [Fintype n] [DecidableEq n] {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}

/-- The matrix obtained by integrating each entry against `ν`. -/
def matIntegral (ν : Measure Z) (M : Z → Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => ∫ z, M z i j ∂ν

omit [DecidableEq n] [Fintype n] in
lemma matIntegral_apply (M : Z → Matrix n n ℂ) (i j : n) :
    matIntegral ν M i j = ∫ z, M z i j ∂ν := rfl

lemma ofReal_integral_le_lintegral {f : Z → ℝ} (hf : Integrable f ν) :
    ENNReal.ofReal (∫ z, f z ∂ν) ≤ ∫⁻ z, ENNReal.ofReal (f z) ∂ν := by
  have h1 : ∫ z, f z ∂ν ≤ ∫ z, max (f z) 0 ∂ν :=
    integral_mono hf (hf.sup (integrable_zero _ _ _)) fun z => le_max_left _ _
  have h2 := ofReal_integral_eq_lintegral_ofReal (hf.sup (integrable_zero _ _ _))
      (Filter.Eventually.of_forall fun z => le_max_right (f z) 0)
  simp only [Pi.sup_apply, Pi.zero_apply] at h2
  refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
  rw [h2]
  congr 1; funext z
  rcases le_total (f z) 0 with h | h
  · simp [max_eq_right h, ENNReal.ofReal_of_nonpos h]
  · simp [max_eq_left h]

omit [DecidableEq n] in
lemma integrable_sum_mul {M : Z → Matrix n n ℂ} (hM : ∀ i j, Integrable (fun z => M z i j) ν)
    (C : Matrix n n ℂ) :
    Integrable (fun z => ∑ i, ∑ j, M z i j * C i j) ν :=
  integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hM i j).mul_const _

omit [DecidableEq n] in
lemma re_sum_matIntegral_mul {M : Z → Matrix n n ℂ}
    (hM : ∀ i j, Integrable (fun z => M z i j) ν) (C : Matrix n n ℂ) :
    (∑ i, ∑ j, matIntegral ν M i j * C i j).re = ∫ z, (∑ i, ∑ j, M z i j * C i j).re ∂ν := by
  have h := integral_re (integrable_sum_mul hM C)
  simp only [RCLike.re_to_complex] at h
  simp only [matIntegral_apply]
  rw [h]
  congr 1
  symm
  calc ∫ z, ∑ i, ∑ j, M z i j * C i j ∂ν = ∑ i, ∫ z, ∑ j, M z i j * C i j ∂ν :=
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hM i j).mul_const _
    _ = ∑ i, ∑ j, ∫ z, M z i j * C i j ∂ν :=
        Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => (hM i j).mul_const _
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        integral_mul_const _ _

omit [DecidableEq n] in
lemma re_trace_mul_eq_sum (C B : Matrix n n ℂ) :
    ((C * B).trace).re = (∑ i, ∑ j, B i j * C j i).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [DecidableEq n] in
lemma re_trace_mul_matIntegral {M : Z → Matrix n n ℂ}
    (hM : ∀ i j, Integrable (fun z => M z i j) ν) (C : Matrix n n ℂ) :
    ((C * matIntegral ν M).trace).re = ∫ z, ((C * M z).trace).re ∂ν := by
  rw [re_trace_mul_eq_sum]
  have := re_sum_matIntegral_mul hM Cᵀ
  simp only [Matrix.transpose_apply] at this
  rw [this]
  congr 1; funext z
  rw [re_trace_mul_eq_sum]

omit [DecidableEq n] in
lemma integrable_re_trace_mul {M : Z → Matrix n n ℂ}
    (hM : ∀ i j, Integrable (fun z => M z i j) ν) (C : Matrix n n ℂ) :
    Integrable (fun z => ((C * M z).trace).re) ν := by
  simp_rw [re_trace_mul_eq_sum, Complex.re_sum]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((hM i j).mul_const _).re

omit [DecidableEq n] [Fintype n] in
lemma matIntegral_posSemidef [Finite n] {M : Z → Matrix n n ℂ} (hM : ∀ z, (M z).PosSemidef)
    (hMi : ∀ i j, Integrable (fun z => M z i j) ν) :
    (matIntegral ν M).PosSemidef := by
  let := Fintype.ofFinite n
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hint : ∀ x : n → ℂ, Integrable (fun z => star x ⬝ᵥ (M z *ᵥ x)) ν := by
    intro x
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      ((hMi i j).mul_const _).const_mul _
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, matIntegral_apply, RCLike.star_def]
    rw [← integral_conj]
    congr 1; funext z
    rw [← RCLike.star_def, ← Matrix.conjTranspose_apply, (hM z).1.eq]
  · have hq : ∀ z, 0 ≤ star x ⬝ᵥ (M z *ᵥ x) := fun z =>
      (Matrix.posSemidef_iff_dotProduct_mulVec.1 (hM z)).2 x
    have e : star x ⬝ᵥ (matIntegral ν M *ᵥ x) = ∫ z, star x ⬝ᵥ (M z *ᵥ x) ∂ν := by
      simp only [dotProduct, Matrix.mulVec, matIntegral_apply, Finset.mul_sum]
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        ((hMi i j).mul_const _).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => ((hMi i j).mul_const _).const_mul _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_mul_const]
    rw [e, Complex.nonneg_iff]
    have hre := integral_re (hint x)
    have him := integral_im (hint x)
    simp only [RCLike.re_to_complex, RCLike.im_to_complex] at hre him
    constructor
    · rw [← hre]; exact integral_nonneg fun z => (Complex.nonneg_iff.1 (hq z)).1
    · rw [← him]
      rw [show (fun z => (star x ⬝ᵥ (M z *ᵥ x)).im) = fun _ => (0 : ℝ) from
        funext fun z => ((Complex.nonneg_iff.1 (hq z)).2).symm]
      simp

omit [DecidableEq n] in
lemma hsRe_eq_re_trace (X Y : Matrix n n ℂ) : hsRe X Y = ((Xᴴ * Y).trace).re := rfl

omit [DecidableEq n] in
lemma hsRe_mul_left_eq (A X : Matrix n n ℂ) :
    hsRe X (A * X) = (((X * Xᴴ) * A).trace).re := by
  rw [hsRe_eq_re_trace, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]

omit [DecidableEq n] in
lemma hsRe_mul_right_eq (A X : Matrix n n ℂ) :
    hsRe X (X * A) = (((Xᴴ * X) * A).trace).re := by
  rw [hsRe_eq_re_trace, ← Matrix.mul_assoc]

theorem matCost_average_le [IsProbabilityMeasure ν] {T K : Z → Matrix n n ℂ}
    (hTm : Measurable T) (hT : ∀ z, (T z).PosSemidef)
    (hTi : ∀ i j, Integrable (fun z => T z i j) ν)
    (hKi : ∀ i j, Integrable (fun z => K z i j) ν) :
    matCost (matIntegral ν T) (matIntegral ν K) ≤ ∫⁻ z, matCost (T z) (K z) ∂ν := by
  set S : Z → Matrix n n ℂ := fun z => CFC.sqrt (T z)
  have hSm : Measurable S := CFC.measurable_sqrt.comp hTm
  have hSH : ∀ z, (S z).IsHermitian := fun z => (CFC.sqrt_nonneg (T z)).posSemidef.1
  have hSS : ∀ z, S z * S z = T z := fun z => CFC.sqrt_mul_sqrt_self _ (hT z).nonneg
  have hSentry : ∀ i j, Measurable fun z => S z i j := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hSm)
  have htr : ∀ z, hsSq (S z) = ∑ k, (T z k k).re := by
    intro z
    rw [← re_trace_conjTranspose_mul_self, (hSH z).eq, hSS z, Matrix.trace, Complex.re_sum]
    rfl
  have hSi : ∀ i j, Integrable (fun z => S z i j) ν := by
    intro i j
    have hg : Integrable (fun z => 1 + ∑ k, (T z k k).re) ν := (integrable_const (1 : ℝ)).add
        (integrable_finsetSum Finset.univ fun k _ => (hTi k k).re)
    refine Integrable.mono' hg (hSentry i j).aestronglyMeasurable (Filter.Eventually.of_forall fun z
        => ?_)
    refine (norm_entry_le_sqrt_hsSq (S z) i j).trans ?_
    rw [htr z]
    have h0 : 0 ≤ ∑ k, (T z k k).re := by rw [← htr z]; exact hsSq_nonneg _
    exact Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  set A := matIntegral ν S
  have hA : A.PosSemidef := matIntegral_posSemidef (fun z => (CFC.sqrt_nonneg _).posSemidef) hSi
  have hmulA : ∀ (B : Z → Matrix n n ℂ), (∀ i j, Integrable (fun z => B z i j) ν) →
      ∀ (C : Matrix n n ℂ) i j, Integrable (fun z => (B z * C) i j) ν ∧
        Integrable (fun z => (C * B z) i j) ν ∧
        ∫ z, (B z * C) i j ∂ν = (matIntegral ν B * C) i j ∧
        ∫ z, (C * B z) i j ∂ν = (C * matIntegral ν B) i j := by
    intro B hB C i j
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun k _ => (hB i k).mul_const _
    · simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun k _ => (hB k j).const_mul _
    · simp only [Matrix.mul_apply, matIntegral_apply]
      calc ∫ z, ∑ k, B z i k * C k j ∂ν = ∑ k, ∫ z, B z i k * C k j ∂ν :=
            integral_finsetSum _ fun k _ => (hB i k).mul_const _
        _ = _ := Finset.sum_congr rfl fun k _ => integral_mul_const _ _
    · simp only [Matrix.mul_apply, matIntegral_apply]
      calc ∫ z, ∑ k, C i k * B z k j ∂ν = ∑ k, ∫ z, C i k * B z k j ∂ν :=
            integral_finsetSum _ fun k _ => (hB k j).const_mul _
        _ = _ := Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  have hA2 : (matIntegral ν T - A * A).PosSemidef := by
    set M : Z → Matrix n n ℂ := fun z => (S z - A)ᴴ * (S z - A)
    have hMe : ∀ z, M z = T z - S z * A - A * S z + A * A := by
      intro z
      simp only [M, Matrix.conjTranspose_sub, (hSH z).eq, hA.1.eq, Matrix.sub_mul,
        Matrix.mul_sub, hSS z]
      abel
    have hMi : ∀ i j, Integrable (fun z => M z i j) ν := by
      intro i j
      simp only [hMe, Matrix.add_apply, Matrix.sub_apply]
      exact (((hTi i j).sub (hmulA S hSi A i j).1).sub (hmulA S hSi A i j).2.1).add
          (integrable_const _)
    have hpsd := matIntegral_posSemidef (fun z => Matrix.posSemidef_conjTranspose_mul_self (S z -
        A)) hMi
    convert hpsd using 1
    ext i j
    have hI1 := (hmulA S hSi A i j).1
    have hI2 := (hmulA S hSi A i j).2.1
    have e1 : ∫ z, ((S z - A)ᴴ * (S z - A)) i j ∂ν =
        ∫ z, (T z i j - (S z * A) i j - (A * S z) i j + (A * A) i j) ∂ν := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      have := congrFun (congrFun (hMe z) i) j
      simp only [Matrix.add_apply, Matrix.sub_apply] at this
      exact this
    have e2 : ∫ z, (T z i j - (S z * A) i j - (A * S z) i j + (A * A) i j) ∂ν = (∫ z, T z i j ∂ν) -
        (∫ z, (S z * A) i j ∂ν) - (∫ z, (A * S z) i j ∂ν) + (A * A) i j := by
      have h1 : Integrable (fun z => T z i j - (S z * A) i j - (A * S z) i j) ν := ((hTi i j).sub
          hI1).sub hI2
      calc _ = (∫ z, (T z i j - (S z * A) i j - (A * S z) i j) ∂ν) + ∫ _z, (A * A) i j ∂ν :=
            integral_add h1 (integrable_const _)
        _ = _ := by
          rw [integral_const, probReal_univ, one_smul]
          congr 1
          calc _ = (∫ z, (T z i j - (S z * A) i j) ∂ν) - ∫ z, (A * S z) i j ∂ν :=
                integral_sub ((hTi i j).sub hI1) hI2
            _ = _ := by rw [integral_sub (hTi i j) hI1]
    change matIntegral ν T i j - (A * A) i j = matIntegral ν (fun z => (S z - A)ᴴ * (S z - A)) i j
    rw [matIntegral_apply, matIntegral_apply, e1, e2, (hmulA S hSi A i j).2.2.1, (hmulA S hSi A i
        j).2.2.2]
    ring
  have hle : A ≤ CFC.sqrt (matIntegral ν T) := by
    rw [← CFC.sqrt_mul_self A hA.nonneg]
    exact CFC.sqrt_le_sqrt _ _ (Matrix.le_iff.2 hA2)
  refine iSup_le fun X => ?_
  have hq := quadForm_mono (Matrix.le_iff.1 hle) X
  have hlin1 : hsRe (matIntegral ν K) X = ∫ z, hsRe (K z) X ∂ν := by
    rw [hsRe_comm, hsRe_eq_re_trace, re_trace_mul_matIntegral hKi]
    congr 1; funext z; rw [hsRe_comm]; rfl
  have hlin2 : hsRe X (A * X) = ∫ z, hsRe X (S z * X) ∂ν := by
    rw [hsRe_mul_left_eq, re_trace_mul_matIntegral hSi]
    congr 1; funext z; rw [hsRe_mul_left_eq]
  have hlin3 : hsRe X (X * A) = ∫ z, hsRe X (X * S z) ∂ν := by
    rw [hsRe_mul_right_eq, re_trace_mul_matIntegral hSi]
    congr 1; funext z; rw [hsRe_mul_right_eq]
  have hi1 : Integrable (fun z => hsRe (K z) X) ν := by
    have := integrable_re_trace_mul hKi Xᴴ
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [← hsRe_eq_re_trace, hsRe_comm]
  have hi2 : Integrable (fun z => hsRe X (S z * X)) ν := by
    have := integrable_re_trace_mul hSi (X * Xᴴ)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [hsRe_mul_left_eq]
  have hi3 : Integrable (fun z => hsRe X (X * S z)) ν := by
    have := integrable_re_trace_mul hSi (Xᴴ * X)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [hsRe_mul_right_eq]
  have hi23 : Integrable (fun z => hsRe X (S z * X) + hsRe X (X * S z)) ν := hi2.add hi3
  have hi123 : Integrable (fun z => 2 * hsRe (K z) X - (hsRe X (S z * X) + hsRe X (X * S z))) ν :=
      (hi1.const_mul 2).sub hi23
  have hci : Integrable (fun z => (3 / 2) * costInt (S z) (K z) X) ν := hi123.const_mul _
  have hcomp : (3 / 2) * costInt (CFC.sqrt (matIntegral ν T)) (matIntegral ν K) X ≤
      ∫ z, (3 / 2) * costInt (S z) (K z) X ∂ν := by
    rw [integral_const_mul]
    unfold costInt
    have e : ∫ z, (2 * hsRe (K z) X - (hsRe X (S z * X) + hsRe X (X * S z))) ∂ν =
        2 * hsRe (matIntegral ν K) X - (hsRe X (A * X) + hsRe X (X * A)) := by
      rw [integral_sub (hi1.const_mul 2) hi23, integral_const_mul, integral_add hi2 hi3,
        ← hlin1, ← hlin2, ← hlin3]
    rw [e]
    nlinarith [hq]
  calc ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt (matIntegral ν T)) (matIntegral ν K) X)
      ≤ ENNReal.ofReal (∫ z, (3 / 2) * costInt (S z) (K z) X ∂ν) :=
        ENNReal.ofReal_le_ofReal hcomp
    _ ≤ ∫⁻ z, ENNReal.ofReal ((3 / 2) * costInt (S z) (K z) X) ∂ν :=
        ofReal_integral_le_lintegral hci
    _ ≤ ∫⁻ z, matCost (T z) (K z) ∂ν :=
        lintegral_mono fun z => le_iSup (fun X => ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt (T z))
            (K z) X)) X

end SylvesterCost

section CostProps

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma costInt_smul (A K X : Matrix n n ℂ) (c : ℝ) :
    costInt A (c • K) (c • X) = c ^ 2 * costInt A K X := by
  have hc : ∀ (X Y : Matrix n n ℂ), hsRe (c • X) Y = c * hsRe X Y := by
    intro X Y; rw [hsRe_comm, hsRe_smul_right, hsRe_comm]
  unfold costInt
  simp only [Matrix.mul_smul, Matrix.smul_mul, hsRe_smul_right, hc]
  ring

lemma matCost_smul (P K : Matrix n n ℂ) {c : ℝ} (hc : c ≠ 0) :
    matCost P (c • K) = ENNReal.ofReal (c ^ 2) * matCost P K := by
  rw [matCost, matCost, ENNReal.mul_iSup]
  apply le_antisymm
  · refine iSup_le fun X => ?_
    refine le_trans (le_of_eq ?_) (le_iSup _ (c⁻¹ • X))
    rw [← ENNReal.ofReal_mul (sq_nonneg c)]
    congr 1
    have := costInt_smul (CFC.sqrt P) K (c⁻¹ • X) c
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul] at this
    rw [this]; ring
  · refine iSup_le fun X => ?_
    refine le_trans (le_of_eq ?_) (le_iSup _ (c • X))
    rw [← ENNReal.ofReal_mul (sq_nonneg c), costInt_smul]
    ring_nf

lemma matCost_add3_le (P K₁ K₂ K₃ : Matrix n n ℂ) :
    matCost P (K₁ + K₂ + K₃) ≤ 3 * (matCost P K₁ + matCost P K₂ + matCost P K₃) := by
  have h9 : ∀ K, matCost P ((3 : ℝ) • K) = 9 * matCost P K := by
    intro K; rw [matCost_smul P K (by norm_num : (3 : ℝ) ≠ 0)]; norm_num
  refine iSup_le fun X => ?_
  set A := CFC.sqrt P
  have e : (3 / 2) * costInt A (K₁ + K₂ + K₃) X = (1 / 3) * ((3 / 2) * costInt A ((3 : ℝ) • K₁) X +
      (3 / 2) * costInt A ((3 : ℝ) • K₂) X + (3 / 2) * costInt A ((3 : ℝ) • K₃) X) := by
    unfold costInt
    have hc : ∀ (K Y : Matrix n n ℂ), hsRe ((3 : ℝ) • K) Y = 3 * hsRe K Y := by
      intro K Y; rw [hsRe_comm, hsRe_smul_right, hsRe_comm]
    have hadd : ∀ (K L Y : Matrix n n ℂ), hsRe (K + L) Y = hsRe K Y + hsRe L Y := by
      intro K L Y; rw [hsRe_comm, hsRe_add_right, hsRe_comm, hsRe_comm Y]
    rw [hadd, hadd, hc, hc, hc]
    ring
  rw [e]
  have hle : ∀ K, ENNReal.ofReal ((3 / 2) * costInt A K X) ≤ matCost P K := fun K =>
    le_iSup (fun X => ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt P) K X)) X
  calc ENNReal.ofReal ((1 / 3) * ((3 / 2) * costInt A ((3 : ℝ) • K₁) X + (3 / 2) * costInt A ((3 :
      ℝ) • K₂) X + (3 / 2) * costInt A ((3 : ℝ) • K₃) X))
      ≤ ENNReal.ofReal (1 / 3) * (ENNReal.ofReal ((3 / 2) * costInt A ((3 : ℝ) • K₁) X) +
          ENNReal.ofReal ((3 / 2) * costInt A ((3 : ℝ) • K₂) X) +
          ENNReal.ofReal ((3 / 2) * costInt A ((3 : ℝ) • K₃) X)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        gcongr
        exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
    _ ≤ ENNReal.ofReal (1 / 3) * (matCost P ((3 : ℝ) • K₁) + matCost P ((3 : ℝ) • K₂) +
          matCost P ((3 : ℝ) • K₃)) := by gcongr <;> exact hle _
    _ = 3 * (matCost P K₁ + matCost P K₂ + matCost P K₃) := by
        rw [h9, h9, h9, ← mul_add, ← mul_add, ← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
        norm_num

lemma matCost_anti {P Q : Matrix n n ℂ} (hQ : Q.PosSemidef) (hPQ : P ≤ Q) (K : Matrix n n ℂ) :
    matCost Q K ≤ matCost P K := by
  have := matCost_comparison hQ one_pos (by simpa using hPQ) K
  simpa using this

lemma matCost_isometry {k : Type*} [Fintype k] [DecidableEq k] (E : Matrix k n ℂ)
    (hE : Eᴴ * E = 1) {T : Matrix n n ℂ} (hT : T.PosSemidef) (K : Matrix n n ℂ) :
    matCost (E * T * Eᴴ) (E * K * Eᴴ) = matCost T K := by
  set S := CFC.sqrt T
  have hSp : S.PosSemidef := (CFC.sqrt_nonneg T).posSemidef
  have hSS : S * S = T := CFC.sqrt_mul_sqrt_self T hT.nonneg
  have hE2 : ∀ (Z : Matrix n n ℂ), Eᴴ * (E * Z) = Z := by
    intro Z; rw [← Matrix.mul_assoc, hE, Matrix.one_mul]
  have hE2k : ∀ (Z : Matrix n k ℂ), Eᴴ * (E * Z) = Z := by
    intro Z; rw [← Matrix.mul_assoc, hE, Matrix.one_mul]
  have hsq : CFC.sqrt (E * T * Eᴴ) = E * S * Eᴴ := by
    have hnn : 0 ≤ E * S * Eᴴ := (hSp.mul_mul_conjTranspose_same E).nonneg
    refine CFC.sqrt_unique ?_ hnn
    simp only [Matrix.mul_assoc, hE2k]
    rw [← Matrix.mul_assoc S S, hSS]
  have hcyc : ∀ (X Y : Matrix n n ℂ), hsRe (E * X * Eᴴ) (E * Y * Eᴴ) = hsRe X Y := by
    intro X Y
    unfold hsRe
    congr 1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      hE2k]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc, hE, Matrix.mul_one]
  have hEE : ∀ (X Y : Matrix n n ℂ), E * X * Eᴴ * (E * Y * Eᴴ) = E * (X * Y) * Eᴴ := by
    intro X Y
    simp only [Matrix.mul_assoc, hE2k]
  set G : Matrix k k ℂ := 1 - E * Eᴴ
  have hGH : Gᴴ = G := by
    simp only [G, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hGG : G * G = G := by
    simp only [G, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, hE2k]
    abel
  have hS0 : (S - ((0 : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by simpa using hSp
  apply le_antisymm
  · rw [matCost]
    refine iSup_le fun X => ?_
    refine le_trans ?_ (le_iSup (fun X => ENNReal.ofReal ((3 / 2) * costInt S K X)) (Eᴴ * X * E))
    apply ENNReal.ofReal_le_ofReal
    rw [hsq]
    unfold costInt
    have h1 : hsRe (E * K * Eᴴ) X = hsRe K (Eᴴ * X * E) := by
      unfold hsRe
      congr 1
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    have hq1 : hsRe (Eᴴ * X * E) (S * (Eᴴ * X * E)) ≤ hsRe X (E * S * Eᴴ * X) := by
      set B := Eᴴ * X
      have hnn := re_trace_conj_mul_mul_ge hS0 (B * G)
      simp only [zero_mul] at hnn
      have e1 : hsRe X (E * S * Eᴴ * X) = ((Bᴴ * S * B).trace).re := by
        unfold hsRe; congr 1
        simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      have e2 : hsRe (Eᴴ * X * E) (S * (Eᴴ * X * E)) = ((Bᴴ * S * B * (E * Eᴴ)).trace).re := by
        unfold hsRe; congr 1
        simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
      have e3 : ((B * G)ᴴ * S * (B * G)).trace = (Bᴴ * S * B).trace - (Bᴴ * S * B * (E * Eᴴ)).trace
          := by
        rw [Matrix.conjTranspose_mul, hGH]
        calc (G * Bᴴ * S * (B * G)).trace = (G * (Bᴴ * S * B * G)).trace := by
              simp only [Matrix.mul_assoc]
          _ = (Bᴴ * S * B * G * G).trace := by rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
          _ = (Bᴴ * S * B * G).trace := by rw [Matrix.mul_assoc _ G G, hGG]
          _ = _ := by simp only [G, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
      rw [e1, e2]
      rw [e3, Complex.sub_re] at hnn
      linarith
    have hq2 : hsRe (Eᴴ * X * E) ((Eᴴ * X * E) * S) ≤ hsRe X (X * (E * S * Eᴴ)) := by
      set C := X * E
      have hnn := re_trace_conj_mul_mul_ge hS0 (G * C)ᴴ
      simp only [zero_mul, Matrix.conjTranspose_conjTranspose] at hnn
      have e1 : hsRe X (X * (E * S * Eᴴ)) = ((Cᴴ * C * S).trace).re := by
        unfold hsRe; congr 1
        simp only [C, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm Eᴴ]
        simp only [Matrix.mul_assoc]
      have e2 : hsRe (Eᴴ * X * E) ((Eᴴ * X * E) * S) = ((Cᴴ * (E * Eᴴ) * C * S).trace).re := by
        unfold hsRe; congr 1
        simp only [C, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      have e3 : ((G * C) * S * (G * C)ᴴ).trace = (Cᴴ * C * S).trace - (Cᴴ * (E * Eᴴ) * C * S).trace
          := by
        rw [Matrix.conjTranspose_mul, hGH]
        calc (G * C * S * (Cᴴ * G)).trace = (G * (C * S * Cᴴ * G)).trace := by
              simp only [Matrix.mul_assoc]
          _ = (C * S * Cᴴ * G * G).trace := by rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
          _ = (C * S * Cᴴ * G).trace := by rw [Matrix.mul_assoc _ G G, hGG]
          _ = (G * (C * S * Cᴴ)).trace := Matrix.trace_mul_comm _ _
          _ = _ := by
              simp only [G, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
              congr 1
              · rw [Matrix.trace_mul_comm (C * S) Cᴴ]; simp only [C, Matrix.mul_assoc]
              · simp only [Matrix.mul_assoc]
                rw [Matrix.trace_mul_comm Cᴴ]
                simp only [Matrix.mul_assoc]
      rw [e1, e2]
      rw [e3, Complex.sub_re] at hnn
      linarith
    rw [h1]
    nlinarith [hq1, hq2]
  · rw [matCost]
    refine iSup_le fun X => ?_
    refine le_trans (le_of_eq ?_) (le_iSup (fun Y => ENNReal.ofReal ((3 / 2) *
      costInt (CFC.sqrt (E * T * Eᴴ)) (E * K * Eᴴ) Y)) (E * X * Eᴴ))
    rw [hsq]
    unfold costInt
    rw [hcyc, hEE, hEE, hcyc, hcyc]

end CostProps

section CyclicTraceCore

lemma sum_triple_by_min {κ : Type*} [LinearOrder κ] {M : Type*} [AddCommMonoid M]
    (f : κ → κ → κ → M) (hf : ∀ i j k, f i j k = f j k i) (s : Finset κ) :
    ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i j k = ∑ μ ∈ s, (3 • ∑ j ∈ s.filter (μ < ·), ∑ k ∈ s.filter (μ
      < ·), f μ j k + 3 • ∑ k ∈ s.filter (μ < ·), f μ μ k + f μ μ μ) := by
  classical
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a t ha ih =>
    have hat : a ∉ t := fun h => lt_irrefl a (ha a h)
    have hfa : (insert a t).filter (a < ·) = t := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, h⟩
        · exact absurd h (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, ha x hx⟩
    have hfμ : ∀ μ ∈ t, (insert a t).filter (μ < ·) = t.filter (μ < ·) := by
      intro μ hμ
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, h⟩
        · exact absurd (ha μ hμ) (not_lt.2 h.le)
        · exact ⟨hx, h⟩
      · rintro ⟨hx, h⟩; exact ⟨Or.inr hx, h⟩
    have hR : ∑ μ ∈ insert a t, (3 • ∑ j ∈ (insert a t).filter (μ < ·),
        ∑ k ∈ (insert a t).filter (μ < ·), f μ j k +
        3 • ∑ k ∈ (insert a t).filter (μ < ·), f μ μ k + f μ μ μ) =
        (3 • ∑ j ∈ t, ∑ k ∈ t, f a j k + 3 • ∑ k ∈ t, f a a k + f a a a) +
        ∑ μ ∈ t, (3 • ∑ j ∈ t.filter (μ < ·), ∑ k ∈ t.filter (μ < ·), f μ j k +
          3 • ∑ k ∈ t.filter (μ < ·), f μ μ k + f μ μ μ) := by
      rw [Finset.sum_insert hat, hfa]
      congr 1
      exact Finset.sum_congr rfl fun μ hμ => by rw [hfμ μ hμ]
    rw [hR, ← ih]
    have c1 : ∀ k, f k a a = f a a k := fun k => by rw [hf, hf]
    have c2 : ∀ k, f a k a = f a a k := fun k => by rw [← hf]
    have c3 : ∀ j k, f j a k = f a k j := fun j k => hf j a k
    have c4 : ∀ j k, f j k a = f a j k := fun j k => by rw [hf, hf]
    have e1 : ∑ j ∈ t, f a j a = ∑ k ∈ t, f a a k := Finset.sum_congr rfl fun j _ => c2 j
    have e2 : ∑ i ∈ t, f i a a = ∑ k ∈ t, f a a k := Finset.sum_congr rfl fun i _ => c1 i
    have e3 : ∑ i ∈ t, ∑ k ∈ t, f i a k = ∑ j ∈ t, ∑ k ∈ t, f a j k := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => c3 i k
    have e4 : ∑ i ∈ t, ∑ j ∈ t, f i j a = ∑ j ∈ t, ∑ k ∈ t, f a j k :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => c4 i j
    simp only [Finset.sum_insert hat, Finset.sum_add_distrib]
    rw [e1, e2, e3, e4]
    simp only [succ_nsmul, zero_nsmul, zero_add]
    abel

lemma sum_pair_by_min {κ : Type*} [LinearOrder κ] {M : Type*} [AddCommMonoid M] (g : κ → κ → M)
    (s : Finset κ) :
    ∑ i ∈ s, ∑ j ∈ s, g i j = ∑ μ ∈ s, (g μ μ + ∑ j ∈ s.filter (μ < ·), (g μ j + g j μ)) := by
  classical
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a t ha ih =>
    have hat : a ∉ t := fun h => lt_irrefl a (ha a h)
    have hfa : (insert a t).filter (a < ·) = t := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, h⟩
        · exact absurd h (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, ha x hx⟩
    have hfμ : ∀ μ ∈ t, (insert a t).filter (μ < ·) = t.filter (μ < ·) := by
      intro μ hμ
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, h⟩
        · exact absurd (ha μ hμ) (not_lt.2 h.le)
        · exact ⟨hx, h⟩
      · rintro ⟨hx, h⟩; exact ⟨Or.inr hx, h⟩
    have hR : ∑ μ ∈ insert a t, (g μ μ + ∑ j ∈ (insert a t).filter (μ < ·), (g μ j + g j μ)) = (g a
        a + ∑ j ∈ t, (g a j + g j a)) +
        ∑ μ ∈ t, (g μ μ + ∑ j ∈ t.filter (μ < ·), (g μ j + g j μ)) := by
      rw [Finset.sum_insert hat, hfa]
      congr 1
      exact Finset.sum_congr rfl fun μ hμ => by rw [hfμ μ hμ]
    rw [hR, ← ih]
    simp only [Finset.sum_insert hat, Finset.sum_add_distrib]
    abel

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma norm_entry_sum_sq_le {D : Matrix κ κ ℂ} (hD : D.IsHermitian) {d : ℝ}
    (hDd : ((d ^ 2 : ℝ) • (1 : Matrix κ κ ℂ) - D * D).PosSemidef) (i : κ) :
    ∑ j, ‖D i j‖ ^ 2 ≤ d ^ 2 := by
  have h := re_diag_le_of_sub_posSemidef hDd i
  have e : ((D * D) i i).re = ∑ j, ‖D i j‖ ^ 2 := by
    rw [Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hD.apply j i, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [e] at h
  simpa [Matrix.smul_apply, Matrix.one_apply_eq, ← Complex.ofReal_pow] using h

lemma norm_diag_le {D : Matrix κ κ ℂ} (hD : D.IsHermitian) {d : ℝ} (hd : 0 ≤ d)
    (hDd : ((d ^ 2 : ℝ) • (1 : Matrix κ κ ℂ) - D * D).PosSemidef) (i : κ) :
    ‖D i i‖ ≤ d := by
  have h := norm_entry_sum_sq_le hD hDd i
  have : ‖D i i‖ ^ 2 ≤ d ^ 2 := (Finset.single_le_sum (f := fun j => ‖D i j‖ ^ 2) (fun j _ =>
      sq_nonneg _) (Finset.mem_univ i)).trans h
  exact abs_le_of_sq_le_sq' this hd |>.2 |> fun h => by
    simpa [abs_of_nonneg (norm_nonneg _)] using (sq_le_sq₀ (norm_nonneg _) hd).1 this

lemma norm_quadForm_le {D : Matrix κ κ ℂ} (hD : D.IsHermitian) {d : ℝ} (hd : 0 ≤ d)
    (hDd : ((d ^ 2 : ℝ) • (1 : Matrix κ κ ℂ) - D * D).PosSemidef) (v : κ → ℂ) :
    ‖∑ j, ∑ k, star (v j) * D j k * v k‖ ≤ d * ∑ j, ‖v j‖ ^ 2 := by
  set w : κ → ℂ := D *ᵥ v
  have e1 : ∑ j, ∑ k, star (v j) * D j k * v k = ∑ j, star (v j) * w j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [w, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hw : ∑ j, ‖w j‖ ^ 2 ≤ d ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
    have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hDd).2 v
    have e2 : star v ⬝ᵥ ((((d ^ 2 : ℝ) • (1 : Matrix κ κ ℂ)) - D * D) *ᵥ v) = ((d ^ 2 * ∑ j, ‖v j‖ ^
        2 - ∑ j, ‖w j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec]
      have ha : star v ⬝ᵥ ((d ^ 2 : ℝ) • v) = ((d ^ 2 * ∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) := by
        simp only [dotProduct, Pi.smul_apply, Pi.star_apply, Complex.real_smul, RCLike.star_def]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_left_comm, Complex.conj_mul']
      have hb : star v ⬝ᵥ (D *ᵥ (D *ᵥ v)) = ((∑ j, ‖w j‖ ^ 2 : ℝ) : ℂ) := by
        rw [Matrix.dotProduct_mulVec, show star v ᵥ* D = star w by
          rw [Matrix.star_mulVec, hD.eq]]
        simp only [dotProduct, Pi.star_apply, RCLike.star_def]
        push_cast
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm, Complex.mul_conj']
      rw [ha, hb]; push_cast; ring
    rw [e2] at hq
    have := (Complex.nonneg_iff.1 hq).1
    simp only [Complex.ofReal_re] at this
    linarith
  rw [e1]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul, norm_star]
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  have hS : 0 ≤ ∑ j, ‖v j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  calc √(∑ j, ‖v j‖ ^ 2) * √(∑ j, ‖w j‖ ^ 2) ≤ √(∑ j, ‖v j‖ ^ 2) * √(d ^ 2 * ∑ j, ‖v j‖ ^ 2) :=
        by gcongr
    _ = d * ∑ j, ‖v j‖ ^ 2 := by
        rw [Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd, ← mul_assoc, mul_comm _ d, mul_assoc,
          Real.mul_self_sqrt hS]

theorem norm_cubic_sum_le (m : κ → ℝ) {D : Matrix κ κ ℂ} (hD : D.IsHermitian) {d : ℝ}
    (hd : 0 ≤ d) (hDd : ((d ^ 2 : ℝ) • (1 : Matrix κ κ ℂ) - D * D).PosSemidef) :
    ‖∑ i, ∑ j, ∑ k, ((m i * m j * m k : ℝ) : ℂ) * D i j * D j k * D k i‖ ≤ 5 * d * ∑ i, ∑ j, |m
      i| ^ 2 * |m j| ^ 2 * ‖D i j‖ ^ 2 / (|m i| + |m j|) := by
  classical
  set q : κ → ℝ := fun i => |m i| with hqdef
  have hq0 : ∀ i, 0 ≤ q i := fun i => abs_nonneg _
  set e := Fintype.equivFin κ
  let : LinearOrder κ := LinearOrder.lift' (fun i => toLex (OrderDual.toDual (q i), e i)) (fun i j h
      => by
      have := congrArg (fun x => (ofLex x).2) h
      exact e.injective this)
  have hord : ∀ i j, i < j → q j ≤ q i := by
    intro i j hij
    have h : toLex (OrderDual.toDual (q i), e i) < toLex (OrderDual.toDual (q j), e j) := hij
    rw [Prod.Lex.toLex_lt_toLex] at h
    rcases h with h | ⟨h, _⟩
    · exact (OrderDual.toDual_lt_toDual.1 h).le
    · exact (OrderDual.toDual_inj.1 h) ▸ le_rfl
  have hDn : ∀ i j, ‖D j i‖ = ‖D i j‖ := fun i j => by rw [← hD.apply i j, norm_star]
  have hrow := norm_entry_sum_sq_le hD hDd
  have hdiag := norm_diag_le hD hd hDd
  set f : κ → κ → κ → ℂ := fun i j k => ((m i * m j * m k : ℝ) : ℂ) * D i j * D j k * D k i
  have hf : ∀ i j k, f i j k = f j k i := by intro i j k; simp only [f]; push_cast; ring
  have hsum := sum_triple_by_min f hf Finset.univ
  simp only [f] at hsum
  rw [hsum]
  set F : κ → Finset κ := fun μ => Finset.univ.filter (μ < ·)
  set A : κ → ℝ := fun μ => q μ ^ 3 * ‖D μ μ‖ ^ 2
  set S : κ → ℝ := fun μ => ∑ j ∈ F μ, q j ^ 2 * ‖D μ j‖ ^ 2
  set E : κ → ℝ := fun μ => q μ * S μ
  have hA0 : ∀ μ, 0 ≤ A μ := fun μ => by have := hq0 μ; positivity
  have hS0 : ∀ μ, 0 ≤ S μ := fun μ => Finset.sum_nonneg fun j _ => by
    have := hq0 j; positivity
  have hE0 : ∀ μ, 0 ≤ E μ := fun μ => mul_nonneg (hq0 μ) (hS0 μ)
  have hT1 : ∀ μ, ‖∑ j ∈ F μ, ∑ k ∈ F μ, ((m μ * m j * m k : ℝ) : ℂ) * D μ j * D j k * D k μ‖ ≤
      d * E μ := by
    intro μ
    set v : κ → ℂ := fun j => if μ < j then (m j : ℂ) * D j μ else 0
    have hv : ∑ j ∈ F μ, ∑ k ∈ F μ, ((m μ * m j * m k : ℝ) : ℂ) * D μ j * D j k * D k μ = (m μ : ℂ)
        * ∑ j, ∑ k, star (v j) * D j k * v k := by
      rw [Finset.mul_sum]
      simp only [F, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      split_ifs with hj
      · refine Finset.sum_congr rfl fun k _ => ?_
        simp only [v, hj, ite_true]
        split_ifs with hk
        · rw [star_mul', ← hD.apply μ j]
          simp only [RCLike.star_def, Complex.conj_ofReal]
          push_cast; ring
        · simp
      · simp [v, hj]
    rw [hv, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hq := norm_quadForm_le hD hd hDd v
    have hvn : ∑ j, ‖v j‖ ^ 2 = S μ := by
      simp only [S, F, Finset.sum_filter, v]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, hDn]
      · simp
    rw [hvn] at hq
    calc |m μ| * ‖∑ j, ∑ k, star (v j) * D j k * v k‖ ≤ |m μ| * (d * S μ) := by gcongr
      _ = d * E μ := by simp only [E, q]; ring
  have hT2 : ∀ μ, ‖∑ k ∈ F μ, ((m μ * m μ * m k : ℝ) : ℂ) * D μ μ * D μ k * D k μ‖ ≤
      d * (√(A μ) * √(E μ)) := by
    intro μ
    have e1 : ∀ k, ((m μ * m μ * m k : ℝ) : ℂ) * D μ μ * D μ k * D k μ = ((m μ * m μ : ℝ) : ℂ) * D μ
        μ * ((m k * ‖D μ k‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      have hp : D μ k * D k μ = ((‖D μ k‖ ^ 2 : ℝ) : ℂ) := by
        rw [← hD.apply k μ, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc
        _ = ((m μ * m μ * m k : ℝ) : ℂ) * D μ μ * (D μ k * D k μ) := by ring
        _ = _ := by rw [hp]; push_cast; ring
    simp_rw [e1]
    rw [← Finset.mul_sum, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖∑ k ∈ F μ, ((m k * ‖D μ k‖ ^ 2 : ℝ) : ℂ)‖ ≤ ∑ k ∈ F μ, q k * ‖D μ k‖ ^ 2 := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖D μ k‖)]
    have h2 : ∑ k ∈ F μ, q k * ‖D μ k‖ ^ 2 ≤ √(S μ) * d := by
      have := Real.sum_mul_le_sqrt_mul_sqrt (F μ) (fun k => q k * ‖D μ k‖) (fun k => ‖D μ k‖)
      have hs1 : ∑ k ∈ F μ, (q k * ‖D μ k‖) ^ 2 = S μ :=
        Finset.sum_congr rfl fun k _ => by ring
      have hs2 : √(∑ k ∈ F μ, ‖D μ k‖ ^ 2) ≤ d := by
        refine Real.sqrt_le_iff.2 ⟨hd, ?_⟩
        exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun k _ _ => sq_nonneg _).trans (hrow μ)
      calc ∑ k ∈ F μ, q k * ‖D μ k‖ ^ 2 = ∑ k ∈ F μ, (q k * ‖D μ k‖) * ‖D μ k‖ :=
            Finset.sum_congr rfl fun k _ => by ring
        _ ≤ √(∑ k ∈ F μ, (q k * ‖D μ k‖) ^ 2) * √(∑ k ∈ F μ, ‖D μ k‖ ^ 2) := this
        _ ≤ √(S μ) * d := by rw [hs1]; exact mul_le_mul_of_nonneg_left hs2 (Real.sqrt_nonneg _)
    have hmm : |m μ * m μ| = q μ ^ 2 := by simp [q, abs_mul, sq]
    rw [hmm]
    calc q μ ^ 2 * ‖D μ μ‖ * ‖∑ k ∈ F μ, ((m k * ‖D μ k‖ ^ 2 : ℝ) : ℂ)‖
        ≤ q μ ^ 2 * ‖D μ μ‖ * (√(S μ) * d) := by
          have := hq0 μ
          gcongr
          exact h1.trans h2
      _ = d * (√(A μ) * √(E μ)) := by
          have hq := hq0 μ
          rw [← Real.sqrt_mul (hA0 μ), show A μ * E μ = (q μ ^ 2 * ‖D μ μ‖) ^ 2 * S μ by
            simp only [A, E]; ring, Real.sqrt_mul (sq_nonneg _),
            Real.sqrt_sq (by positivity)]
          ring
  have hT3 : ∀ μ, ‖((m μ * m μ * m μ : ℝ) : ℂ) * D μ μ * D μ μ * D μ μ‖ ≤ d * A μ := by
    intro μ
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, A]
    have h := hdiag μ
    have := norm_nonneg (D μ μ)
    have hq := hq0 μ
    calc |m μ| * |m μ| * |m μ| * ‖D μ μ‖ * ‖D μ μ‖ * ‖D μ μ‖ =
        q μ ^ 3 * ‖D μ μ‖ ^ 2 * ‖D μ μ‖ := by simp only [q]; ring
      _ ≤ q μ ^ 3 * ‖D μ μ‖ ^ 2 * d := by gcongr
      _ = _ := by ring
  have hgroup : ∀ μ, ‖3 • ∑ j ∈ F μ, ∑ k ∈ F μ, ((m μ * m j * m k : ℝ) : ℂ) * D μ j * D j k *
      D k μ + 3 • ∑ k ∈ F μ, ((m μ * m μ * m k : ℝ) : ℂ) * D μ μ * D μ k * D k μ +
      ((m μ * m μ * m μ : ℝ) : ℂ) * D μ μ * D μ μ * D μ μ‖ ≤
        d * (3 * E μ + 3 * (√(A μ) * √(E μ)) + A μ) := by
    intro μ
    refine (norm_add₃_le).trans ?_
    rw [nsmul_eq_mul, nsmul_eq_mul, norm_mul, norm_mul]
    simp only [Nat.cast_ofNat, Complex.norm_ofNat]
    nlinarith [hT1 μ, hT2 μ, hT3 μ]
  have hA : ∑ μ, √(A μ) * √(E μ) ≤ √(∑ μ, A μ) * √(∑ μ, E μ) := by
    have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun μ => √(A μ)) (fun μ => √(E μ))
    simpa [Real.sq_sqrt (hA0 _), Real.sq_sqrt (hE0 _)] using this
  have hAE : 3 * (√(∑ μ, A μ) * √(∑ μ, E μ)) ≤ (3 / 2) * (∑ μ, A μ + ∑ μ, E μ) := by
    have hSA : 0 ≤ ∑ μ, A μ := Finset.sum_nonneg fun μ _ => hA0 μ
    have hSE : 0 ≤ ∑ μ, E μ := Finset.sum_nonneg fun μ _ => hE0 μ
    have h1 := Real.sq_sqrt hSA
    have h2 := Real.sq_sqrt hSE
    nlinarith [sq_nonneg (√(∑ μ, A μ) - √(∑ μ, E μ))]
  set g : κ → κ → ℝ := fun i j => |m i| ^ 2 * |m j| ^ 2 * ‖D i j‖ ^ 2 / (|m i| + |m j|)
  have hQ : ∑ μ, (A μ / 2 + E μ) ≤ ∑ i, ∑ j, g i j := by
    rw [sum_pair_by_min g Finset.univ]
    refine Finset.sum_le_sum fun μ _ => ?_
    have hg1 : g μ μ = A μ / 2 := by
      simp only [g, A, q]
      rcases (abs_nonneg (m μ)).eq_or_lt with h | h
      · rw [← h]; simp
      · field_simp; ring
    have hg2 : E μ ≤ ∑ j ∈ F μ, (g μ j + g j μ) := by
      simp only [E, S, Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjμ : q j ≤ q μ := hord μ j (Finset.mem_filter.1 hj).2
      simp only [g, hDn μ j]
      have h1 := hq0 μ; have h2 := hq0 j
      change q μ * (q j ^ 2 * ‖D μ j‖ ^ 2) ≤ q μ ^ 2 * q j ^ 2 * ‖D μ j‖ ^ 2 / (q μ + q j) +
        q j ^ 2 * q μ ^ 2 * ‖D μ j‖ ^ 2 / (q j + q μ)
      rcases (add_nonneg h1 h2).eq_or_lt with h0 | h0
      · have hμ0 : q μ = 0 := by linarith
        simp [hμ0]
      · rw [add_comm (q j) (q μ), ← add_div, le_div_iff₀ h0]
        have := norm_nonneg (D μ j)
        nlinarith [mul_nonneg (mul_nonneg h1 (sq_nonneg (q j))) (sq_nonneg ‖D μ j‖),
          mul_nonneg (mul_nonneg (mul_nonneg h1 (sq_nonneg (q j))) (sq_nonneg ‖D μ j‖))
              (sub_nonneg.2 hjμ)]
    linarith
  calc ‖∑ μ, (3 • ∑ j ∈ F μ, ∑ k ∈ F μ, ((m μ * m j * m k : ℝ) : ℂ) * D μ j * D j k * D k μ +
        3 • ∑ k ∈ F μ, ((m μ * m μ * m k : ℝ) : ℂ) * D μ μ * D μ k * D k μ +
        ((m μ * m μ * m μ : ℝ) : ℂ) * D μ μ * D μ μ * D μ μ)‖
      ≤ ∑ μ, d * (3 * E μ + 3 * (√(A μ) * √(E μ)) + A μ) := (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun μ _ => hgroup μ)
    _ = d * (3 * ∑ μ, E μ + 3 * ∑ μ, √(A μ) * √(E μ) + ∑ μ, A μ) := by
        rw [← Finset.mul_sum]
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ d * (5 * ∑ μ, (A μ / 2 + E μ)) := by
        apply mul_le_mul_of_nonneg_left _ hd
        have hsplit : ∑ μ, (A μ / 2 + E μ) = (∑ μ, A μ) / 2 + ∑ μ, E μ := by
          rw [Finset.sum_add_distrib, Finset.sum_div]
        have hE : 0 ≤ ∑ μ, E μ := Finset.sum_nonneg fun μ _ => hE0 μ
        rw [hsplit]
        nlinarith [hA, hAE]
    _ ≤ 5 * d * ∑ i, ∑ j, g i j := by nlinarith [hQ]

end CyclicTraceCore

section ThreeBlocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Flatten a three-by-three array of matrix blocks to the product index type. -/
def blk3 (X : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ :=
  Matrix.comp _ _ _ _ _ X

omit [DecidableEq ι] in
lemma blk3_mul (X Y : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) :
    blk3 (X * Y) = blk3 X * blk3 Y := (Matrix.compRingEquiv (Fin 3) ι ℂ).map_mul X Y

omit [DecidableEq ι] [Fintype ι] in
lemma blk3_add (X Y : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) :
    blk3 (X + Y) = blk3 X + blk3 Y := by
  rfl

omit [Fintype ι] in
lemma blk3_one : blk3 (1 : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) = 1 := Matrix.comp_one

omit [DecidableEq ι] in
lemma blk3_trace (X : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) :
    (blk3 X).trace = (X 0 0).trace + (X 1 1).trace + (X 2 2).trace := by
  simp only [blk3, Matrix.trace, Matrix.diag, Matrix.comp_apply, Fintype.sum_prod_type,
    Fin.sum_univ_three]

/-- The matrix sending a pair of vectors into the designated two blocks. -/
def emb2 (p r : Fin 3) : Matrix (Fin 3 × ι) (ι ⊕ ι) ℂ :=
  Matrix.of fun x s => Sum.elim (fun b => if x = (p, b) then (1 : ℂ) else 0) (fun b => if x = (r, b)
      then (1 : ℂ) else 0) s

lemma emb2_isometry {p r : Fin 3} (hpr : p ≠ r) : (emb2 (ι := ι) p r)ᴴ * emb2 (ι := ι) p r = 1 := by
  ext s t
  rcases s with a | a <;> rcases t with b | b <;>
    simp only [emb2, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Sum.elim_inl, Sum.elim_inr, Matrix.one_apply, Prod.mk.injEq,
      apply_ite star, star_one, star_zero, ite_and, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, ite_false] <;>
    simp [hpr, hpr.symm, eq_comm]

lemma emb2_conj_fromBlocks₁₂ (X11 X12 X21 X22 : Matrix ι ι ℂ) :
    emb2 (ι := ι) 1 2 * Matrix.fromBlocks X11 X12 X21 X22 * (emb2 (ι := ι) 1 2)ᴴ =
      blk3 !![0, 0, 0; 0, X11, X12; 0, X21, X22] := by
  ext ⟨w, a⟩ ⟨w', b⟩
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, emb2, Matrix.of_apply, Sum.elim_inl,
    Sum.elim_inr, Matrix.conjTranspose_apply, blk3, Matrix.comp_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  fin_cases w <;> fin_cases w' <;> simp [Prod.ext_iff]

lemma emb2_conj_fromBlocks₂₀ (X11 X12 X21 X22 : Matrix ι ι ℂ) :
    emb2 (ι := ι) 2 0 * Matrix.fromBlocks X11 X12 X21 X22 * (emb2 (ι := ι) 2 0)ᴴ =
      blk3 !![X22, 0, X21; 0, 0, 0; X12, 0, X11] := by
  ext ⟨w, a⟩ ⟨w', b⟩
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, emb2, Matrix.of_apply, Sum.elim_inl,
    Sum.elim_inr, Matrix.conjTranspose_apply, blk3, Matrix.comp_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  fin_cases w <;> fin_cases w' <;> simp [Prod.ext_iff]

lemma emb2_conj_fromBlocks₀₁ (X11 X12 X21 X22 : Matrix ι ι ℂ) :
    emb2 (ι := ι) 0 1 * Matrix.fromBlocks X11 X12 X21 X22 * (emb2 (ι := ι) 0 1)ᴴ =
      blk3 !![X11, X12, 0; X21, X22, 0; 0, 0, 0] := by
  ext ⟨w, a⟩ ⟨w', b⟩
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, emb2, Matrix.of_apply, Sum.elim_inl,
    Sum.elim_inr, Matrix.conjTranspose_apply, blk3, Matrix.comp_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  fin_cases w <;> fin_cases w' <;> simp [Prod.ext_iff]

omit [DecidableEq ι] [Fintype ι] in
lemma blk3_conjTranspose (a b c d e f g h i : Matrix ι ι ℂ) :
    (blk3 !![a, b, c; d, e, f; g, h, i])ᴴ = blk3 !![aᴴ, dᴴ, gᴴ; bᴴ, eᴴ, hᴴ; cᴴ, fᴴ, iᴴ] := by
  ext ⟨w, x⟩ ⟨w', y⟩
  fin_cases w <;> fin_cases w' <;> simp [blk3, Matrix.comp_apply, Matrix.conjTranspose_apply]

/-- The matrix embedding a vector into one of the three blocks. -/
def emb1 (p : Fin 3) : Matrix (Fin 3 × ι) ι ℂ :=
  Matrix.of fun x b => if x = (p, b) then (1 : ℂ) else 0

lemma blk3_diag_eq (X0 X1 X2 : Matrix ι ι ℂ) :
    blk3 !![X0, 0, 0; 0, X1, 0; 0, 0, X2] = emb1 (ι := ι) 0 * X0 * (emb1 (ι := ι) 0)ᴴ + emb1 (ι :=
        ι) 1 * X1 * (emb1 (ι := ι) 1)ᴴ +
        emb1 (ι := ι) 2 * X2 * (emb1 (ι := ι) 2)ᴴ := by
  ext ⟨w, a⟩ ⟨w', b⟩
  simp only [Matrix.add_apply, Matrix.mul_apply, emb1, Matrix.of_apply,
    Matrix.conjTranspose_apply, blk3, Matrix.comp_apply]
  fin_cases w <;> fin_cases w' <;> simp [Prod.ext_iff]

end ThreeBlocks

section CyclicTrace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The horizontal concatenation of the forward edge and the adjoint of the backward edge. -/
def rowMat (W V : Matrix ι ι ℂ) : Matrix ι (ι ⊕ ι) ℂ := Matrix.fromCols W Vᴴ

omit [DecidableEq ι] in
lemma rowMat_insert (W V D : Matrix ι ι ℂ) :
    (rowMat W V)ᴴ * D * rowMat W V = Matrix.fromBlocks (Wᴴ * D * W) (Wᴴ * D * Vᴴ) (V * D * W) (V
      * D * Vᴴ) := by
  simp [rowMat, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.mul_assoc]

omit [DecidableEq ι] in
lemma rowMat_gram (W V : Matrix ι ι ℂ) :
    (rowMat W V)ᴴ * rowMat W V = Matrix.fromBlocks (Wᴴ * W) (Wᴴ * Vᴴ) (V * W) (V * Vᴴ) := by
  simp [rowMat, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose]

variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)

/-- The Hermitian block matrix with the three cyclic edge matrices off the diagonal. -/
def cycMb : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ) := !![0, W0, W2ᴴ; W0ᴴ, 0, W1; W2, W1ᴴ, 0]

/-- The block-diagonal matrix of the three vertex weights. -/
def cycDb : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ) := !![D0, 0, 0; 0, D1, 0; 0, 0, D2]

/-- The projector onto block zero. -/
def cycP0 : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ) := !![1, 0, 0; 0, 0, 0; 0, 0, 0]

/-- The projector onto block one. -/
def cycP1 : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ) := !![0, 0, 0; 0, 1, 0; 0, 0, 0]

/-- The projector onto block two. -/
def cycP2 : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ) := !![0, 0, 0; 0, 0, 0; 0, 0, 1]

lemma cyc_cube_trace :
    ((blk3 (cycDb D0 D1 D2) * blk3 (cycMb W0 W1 W2)) ^ 3).trace = 3 * (D0 * W0 * D1 * W1 * D2 *
      W2).trace + 3 * (D0 * W2ᴴ * D2 * W1ᴴ * D1 * W0ᴴ).trace := by
  rw [← blk3_mul, pow_three, ← blk3_mul, ← blk3_mul, blk3_trace]
  simp only [cycDb, cycMb, Matrix.mul_fin_three, mul_zero, zero_mul, add_zero, zero_add,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_fin_const, Matrix.trace_add]
  have c1 : (D1 * (W1 * (D2 * (W2 * (D0 * W0))))).trace = (D0 * (W0 * (D1 * (W1 * (D2 *
      W2))))).trace := by
    have := Matrix.trace_mul_comm (D1 * W1 * D2 * W2) (D0 * W0)
    simpa only [Matrix.mul_assoc] using this
  have c2 : (D2 * (W2 * (D0 * (W0 * (D1 * W1))))).trace = (D0 * (W0 * (D1 * (W1 * (D2 *
      W2))))).trace := by
    have := Matrix.trace_mul_comm (D2 * W2) (D0 * W0 * D1 * W1)
    simpa only [Matrix.mul_assoc] using this
  have c3 : (D1 * (W0ᴴ * (D0 * (W2ᴴ * (D2 * W1ᴴ))))).trace = (D0 * (W2ᴴ * (D2 * (W1ᴴ * (D1 *
      W0ᴴ))))).trace := by
    have := Matrix.trace_mul_comm (D1 * W0ᴴ) (D0 * W2ᴴ * D2 * W1ᴴ)
    simpa only [Matrix.mul_assoc] using this
  have c4 : (D2 * (W1ᴴ * (D1 * (W0ᴴ * (D0 * W2ᴴ))))).trace = (D0 * (W2ᴴ * (D2 * (W1ᴴ * (D1 *
      W0ᴴ))))).trace := by
    have := Matrix.trace_mul_comm (D2 * W1ᴴ * D1 * W0ᴴ) (D0 * W2ᴴ)
    simpa only [Matrix.mul_assoc] using this
  simp only [Matrix.mul_assoc] at *
  rw [c1, c2, c3, c4]
  ring

omit [DecidableEq ι] in
lemma cyc_backward_conj (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian) (hD2 : D2.IsHermitian) :
    (D0 * W2ᴴ * D2 * W1ᴴ * D1 * W0ᴴ).trace = star ((D0 * W0 * D1 * W1 * D2 * W2).trace) := by
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, hD0.eq, hD1.eq, hD2.eq, Matrix.mul_assoc]
  have := Matrix.trace_mul_comm D0 (W2ᴴ * (D2 * (W1ᴴ * (D1 * W0ᴴ))))
  simp only [Matrix.mul_assoc] at this
  rw [this]

omit [DecidableEq ι] [Fintype ι] in
lemma cycMb_isHermitian : (blk3 (cycMb W0 W1 W2)).IsHermitian := by
  rw [Matrix.IsHermitian, cycMb, blk3_conjTranspose]
  simp

omit [DecidableEq ι] [Fintype ι] in
lemma cycDb_isHermitian (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian) (hD2 : D2.IsHermitian) :
    (blk3 (cycDb D0 D1 D2)).IsHermitian := by
  rw [Matrix.IsHermitian, cycDb, blk3_conjTranspose]
  simp [hD0.eq, hD1.eq, hD2.eq]

omit [DecidableEq ι] [Fintype ι] in
lemma blk3_smul (c : ℂ) (X : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) :
    blk3 (c • X) = c • blk3 X := by
  ext ⟨v, a⟩ ⟨w, b⟩; simp [blk3, Matrix.comp_apply]

lemma cyc_sq_bound {d : ℝ} (h0 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D0 * D0).PosSemidef)
    (h1 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D1 * D1).PosSemidef)
    (h2 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D2 * D2).PosSemidef) :
    ((d ^ 2 : ℝ) • (1 : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) - blk3 (cycDb D0 D1 D2) * blk3 (cycDb
      D0 D1 D2)).PosSemidef := by
  have e : (d ^ 2 : ℝ) • (1 : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) -
      blk3 (cycDb D0 D1 D2) * blk3 (cycDb D0 D1 D2) =
      blk3 !![(d ^ 2 : ℝ) • 1 - D0 * D0, 0, 0; 0, (d ^ 2 : ℝ) • 1 - D1 * D1, 0;
        0, 0, (d ^ 2 : ℝ) • 1 - D2 * D2] := by
    rw [← blk3_mul, ← blk3_one, show ((d ^ 2 : ℝ) • blk3 (1 : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ))
        : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) = blk3 (((d ^ 2 : ℝ) : ℂ) • 1) by
        rw [blk3_smul]; rfl]
    ext ⟨v, a⟩ ⟨w, b⟩
    fin_cases v <;> fin_cases w <;>
      simp [blk3, Matrix.comp_apply, cycDb, Matrix.one_fin_three,
        Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
  rw [e, blk3_diag_eq]
  refine ((h0.mul_mul_conjTranspose_same _).add (h1.mul_mul_conjTranspose_same _)).add
      (h2.mul_mul_conjTranspose_same _)

lemma trace_cube_eigen {κ : Type*} [Fintype κ] [DecidableEq κ] (U : Matrix.unitaryGroup κ ℂ)
    (m : κ → ℝ) (Dt : Matrix κ κ ℂ) :
    (((U : Matrix κ κ ℂ) * Dt * star (U : Matrix κ κ ℂ) * ((U : Matrix κ κ ℂ) * diagonal (fun i
      => (m i : ℂ)) * star (U : Matrix κ κ ℂ))) ^ 3).trace = ∑ i, ∑ j, ∑ k, ((m i * m j * m k : ℝ)
      : ℂ) * Dt i j * Dt j k * Dt k i := by
  have hU'U : star (U : Matrix κ κ ℂ) * U = 1 := Unitary.coe_star_mul_self U
  set A := Dt * diagonal (fun i => (m i : ℂ))
  have hA : (U : Matrix κ κ ℂ) * Dt * star (U : Matrix κ κ ℂ) * ((U : Matrix κ κ ℂ) * diagonal (fun
      i => (m i : ℂ)) * star (U : Matrix κ κ ℂ)) = (U : Matrix κ κ ℂ) * A * star (U : Matrix κ κ ℂ)
      := by
    simp only [A, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (U : Matrix κ κ ℂ)) (U : Matrix κ κ ℂ), hU'U, Matrix.one_mul]
  have hcube : ((U : Matrix κ κ ℂ) * A * star (U : Matrix κ κ ℂ)) ^ 3 = (U : Matrix κ κ ℂ) * (A ^ 3)
      * star (U : Matrix κ κ ℂ) := by
    simp only [pow_three, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (U : Matrix κ κ ℂ)) (U : Matrix κ κ ℂ), hU'U, Matrix.one_mul,
      ← Matrix.mul_assoc (star (U : Matrix κ κ ℂ)) (U : Matrix κ κ ℂ), hU'U, Matrix.one_mul]
  have hAe : ∀ x y, A x y = Dt x y * (m y : ℂ) := fun x y => by
    simp only [A, Matrix.mul_diagonal]
  rw [hA, hcube, trace_conj_unitary, pow_three]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum, hAe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring

lemma conj_unitary_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (U : Matrix.unitaryGroup κ ℂ)
    (X Y : Matrix κ κ ℂ) :
    star (U : Matrix κ κ ℂ) * (X * Y) * (U : Matrix κ κ ℂ) = (star (U : Matrix κ κ ℂ) * X * U) *
      (star (U : Matrix κ κ ℂ) * Y * U) := by
  have hUU2 : ∀ Z : Matrix κ κ ℂ, (U : Matrix κ κ ℂ) * (star (U : Matrix κ κ ℂ) * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, show (U : Matrix κ κ ℂ) * star (U : Matrix κ κ ℂ) = 1 from
      Unitary.coe_mul_star_self U, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hUU2]

lemma matCost_eigen_sandwich {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Matrix.unitaryGroup κ ℂ) (m : κ → ℝ) (D : Matrix κ κ ℂ) :
    matCost (((U : Matrix κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ)) *
      ((U : Matrix κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ))) (((U :
      Matrix κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ)) * D * ((U : Matrix
      κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ))) = ENNReal.ofReal ((3 / 2)
      * ∑ i, ∑ j, |m i| ^ 2 * |m j| ^ 2 * ‖(star (U : Matrix κ κ ℂ) * D * U) i j‖ ^ 2 / (|m i| +
      |m j|)) := by
  set M := (U : Matrix κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ)
  have hU'U : star (U : Matrix κ κ ℂ) * U = 1 := Unitary.coe_star_mul_self U
  have hUMU : star (U : Matrix κ κ ℂ) * M * U = diagonal (fun i => (m i : ℂ)) := by
    simp only [M, Matrix.mul_assoc, hU'U, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hU'U, Matrix.one_mul]
  have hMM : M * M = (U : Matrix κ κ ℂ) * diagonal (fun i => ((m i ^ 2 : ℝ) : ℂ)) *
      star (U : Matrix κ κ ℂ) := by
    simp only [M, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (U : Matrix κ κ ℂ)) (U : Matrix κ κ ℂ), hU'U, Matrix.one_mul,
      ← Matrix.mul_assoc (diagonal _) (diagonal _), Matrix.diagonal_mul_diagonal]
    congr 3; funext i; push_cast; ring
  have hent : star (U : Matrix κ κ ℂ) * (M * D * M) * U =
      diagonal (fun i => (m i : ℂ)) * (star (U : Matrix κ κ ℂ) * D * U) *
        diagonal (fun i => (m i : ℂ)) := by
    rw [conj_unitary_mul, conj_unitary_mul, hUMU]
  rw [hMM, matCost_eq_sum_of_conj U (fun i => m i ^ 2) (fun i => sq_nonneg _) rfl, hent]
  set Dt := star (U : Matrix κ κ ℂ) * D * U
  have hterm : ∀ i j, ENNReal.ofReal ((3 / 2) * ‖(diagonal (fun i => (m i : ℂ)) * Dt *
      diagonal (fun i => (m i : ℂ))) i j‖ ^ 2) / ENNReal.ofReal (√(m i ^ 2) + √(m j ^ 2)) =
      ENNReal.ofReal ((3 / 2) * (|m i| ^ 2 * |m j| ^ 2 * ‖Dt i j‖ ^ 2 / (|m i| + |m j|))) := by
    intro i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
    have hnorm : ‖(m i : ℂ) * Dt i j * (m j : ℂ)‖ ^ 2 = |m i| ^ 2 * |m j| ^ 2 * ‖Dt i j‖ ^ 2 := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]; ring
    rw [hnorm]
    rcases (add_nonneg (abs_nonneg (m i)) (abs_nonneg (m j))).eq_or_lt with h | h
    · have hi : |m i| = 0 := by linarith [abs_nonneg (m i), abs_nonneg (m j)]
      rw [← h, hi]; simp
    · rw [← ENNReal.ofReal_div_of_pos h, mul_div_assoc]
  simp_rw [hterm]
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]

private lemma cyc_project_gram_zero :
    blk3 (cycMb W0 W1 W2) * blk3 cycP0 * blk3 (cycMb W0 W1 W2) =
      emb2 (ι := ι) 1 2 * ((rowMat W0 W2)ᴴ * rowMat W0 W2) * (emb2 (ι := ι) 1 2)ᴴ := by
  rw [rowMat_gram, emb2_conj_fromBlocks₁₂, ← blk3_mul, ← blk3_mul]
  congr 1
  simp only [cycMb, cycP0, Matrix.mul_fin_three, mul_zero, zero_mul, add_zero, mul_one]

private lemma cyc_project_insert_zero :
    blk3 (cycMb W0 W1 W2) * blk3 cycP0 * blk3 (cycDb D0 D1 D2) * blk3 (cycMb W0 W1 W2) =
      emb2 (ι := ι) 1 2 * ((rowMat W0 W2)ᴴ * D0 * rowMat W0 W2) * (emb2 (ι := ι) 1 2)ᴴ := by
  rw [rowMat_insert, emb2_conj_fromBlocks₁₂, ← blk3_mul, ← blk3_mul, ← blk3_mul]
  congr 1
  simp only [cycMb, cycP0, cycDb, Matrix.mul_fin_three, mul_zero, zero_mul, add_zero, one_mul,
    Matrix.mul_assoc]

private lemma cyc_project_gram_one :
    blk3 (cycMb W0 W1 W2) * blk3 cycP1 * blk3 (cycMb W0 W1 W2) =
      emb2 (ι := ι) 2 0 * ((rowMat W1 W0)ᴴ * rowMat W1 W0) * (emb2 (ι := ι) 2 0)ᴴ := by
  rw [rowMat_gram, emb2_conj_fromBlocks₂₀, ← blk3_mul, ← blk3_mul]
  congr 1
  simp only [cycMb, cycP1, Matrix.mul_fin_three, mul_zero, zero_mul, add_zero, zero_add,
    mul_one]

private lemma cyc_project_insert_one :
    blk3 (cycMb W0 W1 W2) * blk3 cycP1 * blk3 (cycDb D0 D1 D2) * blk3 (cycMb W0 W1 W2) =
      emb2 (ι := ι) 2 0 * ((rowMat W1 W0)ᴴ * D1 * rowMat W1 W0) * (emb2 (ι := ι) 2 0)ᴴ := by
  rw [rowMat_insert, emb2_conj_fromBlocks₂₀, ← blk3_mul, ← blk3_mul, ← blk3_mul]
  congr 1
  simp only [cycMb, cycP1, cycDb, Matrix.mul_fin_three, mul_zero, zero_mul, add_zero,
    zero_add, one_mul, Matrix.mul_assoc]

private lemma cyc_project_gram_two :
    blk3 (cycMb W0 W1 W2) * blk3 cycP2 * blk3 (cycMb W0 W1 W2) =
      emb2 (ι := ι) 0 1 * ((rowMat W2 W1)ᴴ * rowMat W2 W1) * (emb2 (ι := ι) 0 1)ᴴ := by
  rw [rowMat_gram, emb2_conj_fromBlocks₀₁, ← blk3_mul, ← blk3_mul]
  congr 1
  simp only [cycMb, cycP2, Matrix.mul_fin_three, mul_zero, zero_mul, add_zero, zero_add,
    mul_one]

private lemma cyc_project_insert_two :
    blk3 (cycMb W0 W1 W2) * blk3 cycP2 * blk3 (cycDb D0 D1 D2) * blk3 (cycMb W0 W1 W2) =
      emb2 (ι := ι) 0 1 * ((rowMat W2 W1)ᴴ * D2 * rowMat W2 W1) * (emb2 (ι := ι) 0 1)ᴴ := by
  rw [rowMat_insert, emb2_conj_fromBlocks₀₁, ← blk3_mul, ← blk3_mul, ← blk3_mul]
  congr 1
  simp only [cycMb, cycP2, cycDb, Matrix.mul_fin_three, mul_zero, zero_mul, add_zero,
    zero_add, one_mul, Matrix.mul_assoc]

theorem cyc_cube_le (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian) (hD2 : D2.IsHermitian) {d : ℝ}
    (hd : 0 ≤ d) (h0 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D0 * D0).PosSemidef)
    (h1 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D1 * D1).PosSemidef)
    (h2 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D2 * D2).PosSemidef) :
    ENNReal.ofReal ‖((blk3 (cycDb D0 D1 D2) * blk3 (cycMb W0 W1 W2)) ^ 3).trace‖ ≤
      ENNReal.ofReal (10 * d) * (matCost ((rowMat W0 W2)ᴴ * rowMat W0 W2) ((rowMat W0 W2)ᴴ * D0 *
      rowMat W0 W2) + matCost ((rowMat W1 W0)ᴴ * rowMat W1 W0) ((rowMat W1 W0)ᴴ * D1 * rowMat W1
      W0) + matCost ((rowMat W2 W1)ᴴ * rowMat W2 W1) ((rowMat W2 W1)ᴴ * D2 * rowMat W2 W1)) := by
  set M := blk3 (cycMb W0 W1 W2)
  set D := blk3 (cycDb D0 D1 D2)
  have hMH : M.IsHermitian := cycMb_isHermitian W0 W1 W2
  have hDH : D.IsHermitian := cycDb_isHermitian D0 D1 D2 hD0 hD1 hD2
  have hDd : ((d ^ 2 : ℝ) • (1 : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) - D * D).PosSemidef :=
    cyc_sq_bound D0 D1 D2 h0 h1 h2
  have hMM : (M * M).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self M
    rwa [hMH.eq] at this
  have hPsum : blk3 (cycP0 (ι := ι)) + blk3 cycP1 + blk3 cycP2 = 1 := by
    rw [← blk3_add, ← blk3_add, ← blk3_one]
    congr 1
    simp [cycP0, cycP1, cycP2, Matrix.one_fin_three]
  have hPSDcompl : ∀ P : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ), (blk3 P)ᴴ = blk3 P →
      blk3 P * blk3 P = blk3 P → (M * M - M * blk3 P * M).PosSemidef := by
    intro P hPH hPP
    have e : M * M - M * blk3 P * M = ((1 - blk3 P) * M)ᴴ * ((1 - blk3 P) * M) := by
      have hG : (1 - blk3 P)ᴴ * (1 - blk3 P) = 1 - blk3 P := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.mul_sub, hPP, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
        abel
      calc M * M - M * blk3 P * M = M * (1 - blk3 P) * M := by
            rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
        _ = M * ((1 - blk3 P)ᴴ * (1 - blk3 P)) * M := by rw [hG]
        _ = _ := by
            rw [Matrix.conjTranspose_mul, hMH.eq]; simp only [Matrix.mul_assoc]
    rw [e]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have hP0H : (blk3 (cycP0 (ι := ι)))ᴴ = blk3 cycP0 := by
    rw [cycP0, blk3_conjTranspose]; simp
  have hP1H : (blk3 (cycP1 (ι := ι)))ᴴ = blk3 cycP1 := by
    rw [cycP1, blk3_conjTranspose]; simp
  have hP2H : (blk3 (cycP2 (ι := ι)))ᴴ = blk3 cycP2 := by
    rw [cycP2, blk3_conjTranspose]; simp
  have hP0P : blk3 (cycP0 (ι := ι)) * blk3 cycP0 = blk3 cycP0 := by
    rw [← blk3_mul]; congr 1
    ext v w; fin_cases v <;> fin_cases w <;> simp [cycP0, Matrix.mul_apply, Fin.sum_univ_three]
  have hP1P : blk3 (cycP1 (ι := ι)) * blk3 cycP1 = blk3 cycP1 := by
    rw [← blk3_mul]; congr 1
    ext v w; fin_cases v <;> fin_cases w <;> simp [cycP1, Matrix.mul_apply, Fin.sum_univ_three]
  have hP2P : blk3 (cycP2 (ι := ι)) * blk3 cycP2 = blk3 cycP2 := by
    rw [← blk3_mul]; congr 1
    ext v w; fin_cases v <;> fin_cases w <;> simp [cycP2, Matrix.mul_apply, Fin.sum_univ_three]
  have hT0 := cyc_project_gram_zero W0 W1 W2
  have hK0 := cyc_project_insert_zero W0 W1 W2 D0 D1 D2
  have hT1 := cyc_project_gram_one W0 W1 W2
  have hK1 := cyc_project_insert_one W0 W1 W2 D0 D1 D2
  have hT2 := cyc_project_gram_two W0 W1 W2
  have hK2 := cyc_project_insert_two W0 W1 W2 D0 D1 D2
  have hc : ∀ (P : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) (p r : Fin 3) (hpr : p ≠ r) (W V Dv :
      Matrix ι ι ℂ), (blk3 P)ᴴ = blk3 P → blk3 P * blk3 P = blk3 P →
      M * blk3 P * M = emb2 (ι := ι) p r * ((rowMat W V)ᴴ * rowMat W V) * (emb2 (ι := ι) p r)ᴴ →
      M * blk3 P * D * M = emb2 (ι := ι) p r * ((rowMat W V)ᴴ * Dv * rowMat W V) * (emb2 (ι := ι) p
          r)ᴴ →
      matCost (M * M) (M * blk3 P * D * M) ≤
        matCost ((rowMat W V)ᴴ * rowMat W V) ((rowMat W V)ᴴ * Dv * rowMat W V) := by
    intro P p r hpr W V Dv hPH hPP hT hK
    rw [← matCost_isometry (emb2 (ι := ι) p r) (emb2_isometry hpr)
        (Matrix.posSemidef_conjTranspose_mul_self _), ← hT, ← hK]
    exact matCost_anti hMM (Matrix.le_iff.2 (hPSDcompl P hPH hPP)) _
  have e0 := hc _ 1 2 (by decide) W0 W2 D0 hP0H hP0P hT0 hK0
  have e1 := hc _ 2 0 (by decide) W1 W0 D1 hP1H hP1P hT1 hK1
  have e2 := hc _ 0 1 (by decide) W2 W1 D2 hP2H hP2P hT2 hK2
  have hsplit : M * blk3 cycP0 * D * M + M * blk3 cycP1 * D * M + M * blk3 cycP2 * D * M =
      M * D * M := by
    rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.add_mul,
      ← Matrix.mul_add, ← Matrix.mul_add, hPsum, Matrix.mul_one]
  have hb3 := matCost_add3_le (M * M) (M * blk3 cycP0 * D * M) (M * blk3 cycP1 * D * M) (M * blk3
      cycP2 * D * M)
  rw [hsplit] at hb3
  obtain ⟨U, hUdef⟩ : ∃ U, U = hMH.eigenvectorUnitary := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m, m = hMH.eigenvalues := ⟨_, rfl⟩
  have hU'U : star (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) * U = 1 := Unitary.coe_star_mul_self U
  have hUU : (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) *
      star (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) = 1 := Unitary.coe_mul_star_self U
  have hMU : M = (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) * diagonal (fun i => (m i : ℂ)) *
      star (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) := by
    rw [hUdef, hmdef]
    have := hMH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  obtain ⟨Dt, hDtdef⟩ : ∃ Dt, Dt = star (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) * D * U :=
    ⟨_, rfl⟩
  have hDU : D = (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) * Dt *
      star (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) := by
    rw [hDtdef]
    simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
    rw [Matrix.mul_assoc, hUU, Matrix.mul_one]
  have hDtH : Dt.IsHermitian := by
    rw [hDtdef, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, hDH.eq, Matrix.mul_assoc]
  have hDtd : ((d ^ 2 : ℝ) • (1 : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) - Dt * Dt).PosSemidef := by
    have := hDd.conjTranspose_mul_mul_same (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ)
    convert this using 1
    rw [← Matrix.star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hU'U, hDtdef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) (star (U : Matrix (Fin 3 × ι) (Fin
        3 × ι) ℂ)), hUU, Matrix.one_mul]
  have hcore := norm_cubic_sum_le m hDtH hd hDtd
  have htr : ((D * M) ^ 3).trace =
      ∑ i, ∑ j, ∑ k, ((m i * m j * m k : ℝ) : ℂ) * Dt i j * Dt j k * Dt k i := by
    rw [hDU, hMU]; exact trace_cube_eigen U m Dt
  rw [htr]
  have hcostQ : matCost (M * M) (M * D * M) = ENNReal.ofReal ((3 / 2) *
      ∑ i, ∑ j, |m i| ^ 2 * |m j| ^ 2 * ‖Dt i j‖ ^ 2 / (|m i| + |m j|)) := by
    rw [hMU, hDtdef]
    exact matCost_eigen_sandwich U m D
  calc ENNReal.ofReal ‖∑ i, ∑ j, ∑ k, ((m i * m j * m k : ℝ) : ℂ) * Dt i j * Dt j k * Dt k i‖
      ≤ ENNReal.ofReal (5 * d * ∑ i, ∑ j, |m i| ^ 2 * |m j| ^ 2 * ‖Dt i j‖ ^ 2 / (|m i| + |m j|)) :=
          ENNReal.ofReal_le_ofReal hcore
    _ = ENNReal.ofReal (10 / 3 * d) * matCost (M * M) (M * D * M) := by
        rw [hcostQ, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (10 / 3 * d) * (3 * (matCost (M * M) (M * blk3 cycP0 * D * M) +
          matCost (M * M) (M * blk3 cycP1 * D * M) + matCost (M * M) (M * blk3 cycP2 * D * M)))
        := by gcongr
    _ ≤ ENNReal.ofReal (10 / 3 * d) * (3 * (
          matCost ((rowMat W0 W2)ᴴ * rowMat W0 W2) ((rowMat W0 W2)ᴴ * D0 * rowMat W0 W2) +
          matCost ((rowMat W1 W0)ᴴ * rowMat W1 W0) ((rowMat W1 W0)ᴴ * D1 * rowMat W1 W0) +
          matCost ((rowMat W2 W1)ᴴ * rowMat W2 W1) ((rowMat W2 W1)ᴴ * D2 * rowMat W2 W1))) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

lemma rowMat_cost_unitary (R : Matrix ι (ι ⊕ ι) ℂ) (Uu : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (hU : Uu * Uuᴴ = 1) (Dv : Matrix ι ι ℂ) :
    matCost ((R * Uu)ᴴ * (R * Uu)) ((R * Uu)ᴴ * Dv * (R * Uu)) = matCost (Rᴴ * R) (Rᴴ * Dv * R) :=
        by
  have hE : (Uuᴴ)ᴴ * Uuᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hU
  have h1 : (R * Uu)ᴴ * (R * Uu) = Uuᴴ * (Rᴴ * R) * (Uuᴴ)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc]
  have h2 : (R * Uu)ᴴ * Dv * (R * Uu) = Uuᴴ * (Rᴴ * Dv * R) * (Uuᴴ)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc]
  rw [h1, h2]
  exact matCost_isometry Uuᴴ hE (Matrix.posSemidef_conjTranspose_mul_self R) _

lemma phaseBlocks_unitary {c : ℂ} (hc : ‖c‖ = 1) (left : Bool) :
    (if left then Matrix.fromBlocks (c • (1 : Matrix ι ι ℂ)) 0 0 1 else Matrix.fromBlocks 1 0 0
      (c • (1 : Matrix ι ι ℂ))) * (if left then Matrix.fromBlocks (c • (1 : Matrix ι ι ℂ)) 0 0 1
      else Matrix.fromBlocks 1 0 0 (c • (1 : Matrix ι ι ℂ)))ᴴ = 1 := by
  have hcc : c * star c = 1 := by
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  have hcc2 : (starRingEnd ℂ) c * c = 1 := by rw [mul_comm]; simpa using hcc
  cases left <;>
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, smul_smul, hcc2,
        Matrix.fromBlocks_one, Matrix.conjTranspose_smul]

theorem cyclic_trace_control (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian)
    (hD2 : D2.IsHermitian) {d : ℝ} (hd : 0 ≤ d)
    (h0 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D0 * D0).PosSemidef)
    (h1 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D1 * D1).PosSemidef)
    (h2 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D2 * D2).PosSemidef) :
    ENNReal.ofReal ‖(D0 * W0 * D1 * W1 * D2 * W2).trace‖ ≤ ENNReal.ofReal (5 / 3 * d) * (matCost
      ((rowMat W0 W2)ᴴ * rowMat W0 W2) ((rowMat W0 W2)ᴴ * D0 * rowMat W0 W2) + matCost ((rowMat W1
      W0)ᴴ * rowMat W1 W0) ((rowMat W1 W0)ᴴ * D1 * rowMat W1 W0) + matCost ((rowMat W2 W1)ᴴ *
      rowMat W2 W1) ((rowMat W2 W1)ᴴ * D2 * rowMat W2 W1)) := by
  set t := (D0 * W0 * D1 * W1 * D2 * W2).trace
  by_cases ht : t = 0
  · rw [ht, norm_zero, ENNReal.ofReal_zero]; exact zero_le
  set c : ℂ := star t / (‖t‖ : ℂ)
  have htn : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 ht
  have hc : ‖c‖ = 1 := by
    simp only [c, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg t)]
    exact div_self (norm_ne_zero_iff.2 ht)
  have hct : c * t = (‖t‖ : ℂ) := by
    simp only [c]
    rw [div_mul_eq_mul_div, RCLike.star_def, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    field_simp
  set W0' := c • W0
  have ht' : (D0 * W0' * D1 * W1 * D2 * W2).trace = (‖t‖ : ℂ) := by
    simp only [W0', Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    exact hct
  have hcube := cyc_cube_trace W0' W1 W2 D0 D1 D2
  rw [cyc_backward_conj W0' W1 W2 D0 D1 D2 hD0 hD1 hD2, ht'] at hcube
  have h6 : ‖((blk3 (cycDb D0 D1 D2) * blk3 (cycMb W0' W1 W2)) ^ 3).trace‖ = 6 * ‖t‖ := by
    rw [hcube, RCLike.star_def, Complex.conj_ofReal]
    rw [show (3 : ℂ) * (‖t‖ : ℂ) + 3 * (‖t‖ : ℂ) = ((6 * ‖t‖ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmain := cyc_cube_le W0' W1 W2 D0 D1 D2 hD0 hD1 hD2 hd h0 h1 h2
  rw [h6] at hmain
  have hR0 : rowMat W0' W2 = rowMat W0 W2 * Matrix.fromBlocks (c • (1 : Matrix ι ι ℂ)) 0 0 1 := by
    rw [show rowMat W0 W2 * Matrix.fromBlocks (c • (1 : Matrix ι ι ℂ)) 0 0 1 =
      Matrix.fromCols (W0 * (c • 1) + W2ᴴ * 0) (W0 * 0 + W2ᴴ * 1) from
        Matrix.fromCols_mul_fromBlocks _ _ _ _ _ _]
    simp [rowMat, W0']
  have hR1 : rowMat W1 W0' =
      rowMat W1 W0 * Matrix.fromBlocks 1 0 0 (star c • (1 : Matrix ι ι ℂ)) := by
    rw [show rowMat W1 W0 * Matrix.fromBlocks 1 0 0 (star c • (1 : Matrix ι ι ℂ)) =
      Matrix.fromCols (W1 * 1 + W0ᴴ * 0) (W1 * 0 + W0ᴴ * (star c • 1)) from
        Matrix.fromCols_mul_fromBlocks _ _ _ _ _ _]
    simp [rowMat, W0', Matrix.conjTranspose_smul]
  have hc' : ‖star c‖ = 1 := by rw [norm_star, hc]
  have e0 : matCost ((rowMat W0' W2)ᴴ * rowMat W0' W2) ((rowMat W0' W2)ᴴ * D0 * rowMat W0' W2) =
      matCost ((rowMat W0 W2)ᴴ * rowMat W0 W2) ((rowMat W0 W2)ᴴ * D0 * rowMat W0 W2) := by
    rw [hR0]; exact rowMat_cost_unitary _ _ (by simpa using phaseBlocks_unitary hc true) _
  have e1 : matCost ((rowMat W1 W0')ᴴ * rowMat W1 W0') ((rowMat W1 W0')ᴴ * D1 * rowMat W1 W0') =
      matCost ((rowMat W1 W0)ᴴ * rowMat W1 W0) ((rowMat W1 W0)ᴴ * D1 * rowMat W1 W0) := by
    rw [hR1]; exact rowMat_cost_unitary _ _ (by simpa using phaseBlocks_unitary hc' false) _
  rw [e0, e1] at hmain
  have h6' : ENNReal.ofReal (6 * ‖t‖) = ENNReal.ofReal 6 * ENNReal.ofReal ‖t‖ :=
    ENNReal.ofReal_mul (by norm_num)
  rw [h6'] at hmain
  have h10 : ENNReal.ofReal (10 * d) = ENNReal.ofReal 6 * ENNReal.ofReal (5 / 3 * d) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  rw [h10, mul_assoc] at hmain
  exact (ENNReal.mul_le_mul_iff_right (by simp) ENNReal.ofReal_ne_top).1 hmain

end CyclicTrace

end

end Triangular.Auto
