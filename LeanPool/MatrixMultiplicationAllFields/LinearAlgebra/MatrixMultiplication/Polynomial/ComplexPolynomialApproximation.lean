/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Topology.Algebra.Polynomial

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {F X Y Z : Type*} [Field F]

theorem coeff_eq_sum_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → F) (hnodes : Function.Injective nodes)
    (p : Polynomial F) (d : ℕ) (hdegree : p.degree < Fintype.card ι) :
    p.coeff d = ∑ i, p.eval (nodes i) *
      (Lagrange.basis Finset.univ nodes i).coeff d := by
  have hinj : Set.InjOn nodes (↑(Finset.univ : Finset ι)) := hnodes.injOn
  have hinterp := Lagrange.eq_interpolate hinj (by simpa using hdegree)
    (f := p)
  calc
    p.coeff d = (Lagrange.interpolate Finset.univ nodes
        (fun i => p.eval (nodes i))).coeff d := congrArg (fun q => q.coeff d) hinterp
    _ = _ := by
      simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul]

theorem RankAtMost.coeff {ι : Type*} [Fintype ι]
    (nodes : ι → F) (hnodes : Function.Injective nodes)
    {P : Tensor (Polynomial F) X Y Z} {r : ℕ} (hP : RankAtMost P r)
    (d : ℕ) (hdegree : ∀ x y z, (P x y z).degree < Fintype.card ι) :
    RankAtMost (fun x y z => (P x y z).coeff d) (Fintype.card ι * r) := by
  classical
  rcases hP with ⟨a, b, c, rfl⟩
  let w : ι → F := fun i => (Lagrange.basis Finset.univ nodes i).coeff d
  let aa : (ι × Fin r) → X → F := fun i x => w i.1 * (a i.2 x).eval (nodes i.1)
  let bb : (ι × Fin r) → Y → F := fun i y => (b i.2 y).eval (nodes i.1)
  let cc : (ι × Fin r) → Z → F := fun i z => (c i.2 z).eval (nodes i.1)
  have heq : (fun x y z => (∑ j, rankOne (a j) (b j) (c j) x y z).coeff d) =
      fun x y z => ∑ i, rankOne (aa i) (bb i) (cc i) x y z := by
    funext x y z
    rw [coeff_eq_sum_eval nodes hnodes _ d (hdegree x y z)]
    simp only [Fintype.sum_prod_type, rankOne, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [aa, bb, cc, w]
    ring
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

/-- A bounded-degree, bounded-rank polynomial tensor with specified leading tensor and
vanishing order. -/
structure PolynomialApproximation (T : Tensor F X Y Z) (r d D : ℕ) where
  /-- Polynomial coefficients of the approximating tensor family. -/
  polynomial : Tensor (Polynomial F) X Y Z
  rank_bound : RankAtMost polynomial r
  vanishes : ∀ x y z k, k < d → (polynomial x y z).coeff k = 0
  leading : ∀ x y z, (polynomial x y z).coeff d = T x y z
  degree_bound : ∀ x y z, (polynomial x y z).degree ≤ D

namespace PolynomialApproximation

variable {T : Tensor F X Y Z} {r d D : ℕ}

/-- Remove the common power of the polynomial variable from an approximation. -/
def normalized (A : PolynomialApproximation T r d D) :
    Tensor (Polynomial F) X Y Z :=
  fun x y z => Classical.choose (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x y z))

theorem polynomial_eq (A : PolynomialApproximation T r d D) (x : X) (y : Y) (z : Z) :
    A.polynomial x y z = Polynomial.X ^ d * A.normalized x y z :=
  Classical.choose_spec (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x y z))

theorem normalized_constant (A : PolynomialApproximation T r d D)
    (x : X) (y : Y) (z : Z) : (A.normalized x y z).coeff 0 = T x y z := by
  have h := A.leading x y z
  rw [A.polynomial_eq] at h
  simpa only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self] using h

theorem power_polynomial_eq (A : PolynomialApproximation T r d D) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z) :
    Tensor.power A.polynomial n x y z =
      Polynomial.X ^ (d * n) * Tensor.power A.normalized n x y z := by
  simp [Tensor.power, A.polynomial_eq, Finset.prod_mul_distrib, ← pow_mul]

/-- Tensor-power a polynomial approximation, multiplying rank bounds and adding degrees. -/
def power (A : PolynomialApproximation T r d D) (n : ℕ) :
    PolynomialApproximation (Tensor.power T n) (r ^ n) (d * n) (D * n) where
  polynomial := Tensor.power A.polynomial n
  rank_bound := A.rank_bound.power n
  vanishes := by
    intro x y z k hk
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hk, ite_false]
  leading := by
    intro x y z
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
      Tensor.power, Polynomial.coeff_zero_prod, A.normalized_constant]
  degree_bound := by
    intro x y z
    apply Polynomial.degree_le_of_natDegree_le
    calc
      (Tensor.power A.polynomial n x y z).natDegree ≤
          ∑ i, (A.polynomial (x i) (y i) (z i)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _i : Fin n, D := by
        apply Finset.sum_le_sum
        intro i hi
        exact Polynomial.natDegree_le_of_degree_le (A.degree_bound (x i) (y i) (z i))
      _ = D * n := by simp [Nat.mul_comm]

theorem rank_power [CharZero F] (A : PolynomialApproximation T r d D) (n : ℕ) :
    RankAtMost (Tensor.power T n) ((D * n + 1) * r ^ n) := by
  let nodes : Fin (D * n + 1) → F := fun i => (i.val : F)
  have hinj : Function.Injective nodes := by
    intro i j h
    apply Fin.ext
    exact Nat.cast_injective h
  have hdegree (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z) :
      ((A.power n).polynomial x y z).degree < Fintype.card (Fin (D * n + 1)) := by
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt ((A.power n).degree_bound x y z)
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self (D * n)))
  have h := (A.power n).rank_bound.coeff nodes hinj (d * n) hdegree
  have heq : (fun x y z => ((A.power n).polynomial x y z).coeff (d * n)) =
      Tensor.power T n := by
    funext x y z
    exact (A.power n).leading x y z
  rw [heq, Fintype.card_fin] at h
  exact h

theorem rank_normalized_eval (A : PolynomialApproximation T r d D)
    (t : F) (ht : t ≠ 0) :
    RankAtMost (fun x y z => (A.normalized x y z).eval t) r := by
  have h := (A.rank_bound.map (Polynomial.evalRingHom t)).scale ((t ^ d)⁻¹)
  change RankAtMost (fun x y z => (t ^ d)⁻¹ * (A.polynomial x y z).eval t) r at h
  have heq : (fun x y z => (t ^ d)⁻¹ * (A.polynomial x y z).eval t) =
      fun x y z => (A.normalized x y z).eval t := by
    funext x y z
    rw [A.polynomial_eq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d ht), one_mul]
  rw [heq] at h
  exact h

theorem borderRankAtMost
    {S : Tensor ℂ X Y Z} (A : PolynomialApproximation S r d D) :
    BorderRankAtMost S r := by
  let f : ℂ → Tensor ℂ X Y Z := fun t x y z => (A.normalized x y z).eval t
  have hf : Continuous f := by
    apply continuous_pi
    intro x
    apply continuous_pi
    intro y
    apply continuous_pi
    intro z
    exact (A.normalized x y z).continuous
  have hclosed : IsClosed {t : ℂ | BorderRankAtMost (f t) r} :=
    isClosed_closure.preimage hf
  have hsubset : ({0}ᶜ : Set ℂ) ⊆ {t : ℂ | BorderRankAtMost (f t) r} := by
    intro t ht
    exact (A.rank_normalized_eval t (by simpa using ht)).borderRankAtMost
  have hz := closure_minimal hsubset hclosed ((dense_compl_singleton (0 : ℂ)) 0)
  have heq : f 0 = S := by
    funext x y z
    simp only [f, ← Polynomial.coeff_zero_eq_eval_zero, A.normalized_constant]
  change BorderRankAtMost (f 0) r at hz
  rw [heq] at hz
  exact hz

end PolynomialApproximation

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixMultiplicationAllFields
