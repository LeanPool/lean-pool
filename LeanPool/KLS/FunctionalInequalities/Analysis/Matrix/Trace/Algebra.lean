/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Finite real matrix trace algebra and the elementary trace-energy bound
-/

@[expose] public section

open Matrix

namespace FunctionalInequalities.Analysis

variable {n : Type*} [Fintype n] [DecidableEq n]

section TraceEnergy

/--
**Trace energy**: `Σ_i (tr B_i)² ≤ n · Σ_{i,j,k} (B_i)_{jk}²` for real `n × n` matrices, no symmetry
assumed. Cauchy–Schwarz on the diagonal and the nonnegative off-diagonal squares. -/
theorem sum_trace_sq_le_card_mul_sum_sq {n : ℕ} (B : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ i : Fin n, Matrix.trace (B i) ^ 2) ≤
      (n : ℝ) * ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (B i j k) ^ 2 := by
  have hdiag (i : Fin n) :
    (∑ j : Fin n, (B i j j) ^ 2) ≤ ∑ j : Fin n, ∑ k : Fin n, (B i j k) ^ 2 := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hs : (B i j j) ^ 2 ≤ ∑ k ∈ (Finset.univ : Finset (Fin n)), (B i j k) ^ 2 := by
      exact
        Finset.single_le_sum (s := (Finset.univ : Finset (Fin n))) (f := fun k : Fin n =>
          (B i j k) ^ 2) (fun k hk => sq_nonneg _) (Finset.mem_univ j)
    simpa using hs
  have hi (i : Fin n) :
    (Matrix.trace (B i)) ^ 2 ≤ (n : ℝ) * ∑ j : Fin n, ∑ k : Fin n, (B i j k) ^ 2 := by
    have hcs : (∑ j : Fin n, B i j j) ^ 2 ≤ (n : ℝ) * ∑ j : Fin n, (B i j j) ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := fun j : Fin n =>
          B i j j))
    have hmul :
      (n : ℝ) * ∑ j : Fin n, (B i j j) ^ 2 ≤
        (n : ℝ) * ∑ j : Fin n, ∑ k : Fin n, (B i j k) ^ 2 :=
      mul_le_mul_of_nonneg_left (hdiag i) (by positivity)
    change (∑ j : Fin n, B i j j) ^ 2 ≤ (n : ℝ) * ∑ j : Fin n, ∑ k : Fin n, (B i j k) ^ 2
    exact hcs.trans hmul
  calc
    ∑ i : Fin n, Matrix.trace (B i) ^ 2 ≤
        ∑ i : Fin n, (n : ℝ) * ∑ j : Fin n, ∑ k : Fin n, (B i j k) ^ 2 :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = (n : ℝ) * ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (B i j k) ^ 2 := by rw [Finset.mul_sum]

end TraceEnergy

end FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis

section TraceFourProduct

private theorem reverse_triple_sum {n : ℕ} (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ d, ∑ c, ∑ b, f b c d) = ∑ b, ∑ c, ∑ d, f b c d := by
  calc
    (∑ d, ∑ c, ∑ b, f b c d) = ∑ d, ∑ b, ∑ c, f b c d := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ c, f b c d := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ d, f b c d := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm

/-- The trace of a four-fold product of square matrices as one sum over index quadruples:
`tr(A H B J) = ∑ (A_{ab} B_{cd}) (H_{bc} J_{da})`. -/
theorem trace_mul_mul_mul_eq_sum {n : ℕ} (A H B J : Matrix (Fin n) (Fin n) ℝ) :
    (A * H * B * J).trace =
      ∑ q : Fin n × Fin n × Fin n × Fin n,
        (A q.1 q.2.1 * B q.2.2.1 q.2.2.2) *
          (H q.2.1 q.2.2.1 * J q.2.2.2 q.1) := by
  simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ d, ∑ c, ∑ b, A a b * H b c * B c d * J d a) =
        ∑ b, ∑ c, ∑ d, A a b * H b c * B c d * J d a :=
      reverse_triple_sum _
    _ = ∑ b, ∑ c, ∑ d, (A a b * B c d) * (H b c * J d a) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      ring

end TraceFourProduct

end FunctionalInequalities.Analysis

section MatrixProductEntryTrace

open Matrix

namespace FunctionalInequalities.Analysis

/--
For symmetric `S` and `D`, `∑ᵢⱼ (S A S)ᵢⱼ (S D S)ᵢⱼ = tr((S S) A (S S) D)`; all finite dimensions.
-/
theorem sum_matrix_product_entry_mul_eq_trace {n : ℕ} (S A D : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.IsSymm) (hD : D.IsSymm) :
    (∑ p : Fin n × Fin n, (S * A * S) p.1 p.2 * (S * D * S) p.1 p.2) =
      ((S * S) * A * (S * S) * D).trace := by
  classical
  have hSt : S.transpose = S := hS
  have hDt : D.transpose = D := hD
  have hQ : (S * D * S).transpose = S * D * S := by
    simp only [Matrix.transpose_mul, hSt, hDt, Matrix.mul_assoc]
  have hentry (i j : Fin n) : (S * D * S) j i = (S * D * S) i j := congrFun (congrFun hQ i) j
  calc
    _ = ((S * A * S) * (S * D * S)).trace := by
      simp only [Fintype.sum_prod_type]
      change
        (∑ i : Fin n, ∑ j : Fin n, (S * A * S) i j * (S * D * S) i j) =
          ∑ i : Fin n, ∑ j : Fin n, (S * A * S) i j * (S * D * S) j i
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hentry]
    _ = _ := by simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (S * A * S * S * D) S

/--
Entrywise inverse-quadratic energies of `S Tₖ S` sum to the trace energy `∑ₖₗ Rₖₗ tr((S S) Tₖ (S S)
Tₗ)` for symmetric
`S`, `Tₖ` and an arbitrary real `R`; all finite dimensions. -/
theorem sum_matrix_product_entry_quadratic_eq_trace {m n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.IsSymm) (R : Matrix (Fin m) (Fin m) ℝ) (T : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ k, (T k).IsSymm) :
    (∑ p : Fin n × Fin n,
        (fun k => (S * T k * S) p.1 p.2) ⬝ᵥ (R *ᵥ (fun k => (S * T k * S) p.1 p.2))) =
      ∑ k : Fin m, ∑ l : Fin m, R k l * ((S * S) * T k * (S * S) * T l).trace := by
  classical
  have hOne (p : Fin n × Fin n) :
    (fun k => (S * T k * S) p.1 p.2) ⬝ᵥ (R *ᵥ (fun k => (S * T k * S) p.1 p.2)) =
      ∑ q : Fin m × Fin m, R q.1 q.2 * ((S * T q.1 * S) p.1 p.2 * (S * T q.2 * S) p.1 p.2) := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [hOne]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [show
      (∑ i : Fin n, ∑ j : Fin n, (S * T k * S) i j * (S * T l * S) i j) =
        ((S * S) * T k * (S * S) * T l).trace
      from by
      simpa only [Fintype.sum_prod_type] using
        sum_matrix_product_entry_mul_eq_trace S (T k) (T l) hS (hT l)]

end FunctionalInequalities.Analysis

end MatrixProductEntryTrace

/-! ### Trace identities for transposed products, noise shifts and conjugations

Finite identities over any finite index type: `tr ((A + t 1)ᵀ (A + t 1))`, invariance under a
symmetric involution, and `tr` of `S H S` and of its square. -/

section


namespace FunctionalInequalities.Analysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_transpose_mul_shift_one (A : Matrix ι ι ℝ) (t : ℝ) :
    Matrix.trace ((A + t • 1).transpose * (A + t • 1)) =
      Matrix.trace (A.transpose * A) + 2 * t * Matrix.trace A + (Fintype.card ι : ℝ) * t ^ 2 := by
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_transpose, Matrix.trace_one, smul_eq_mul]
  ring

theorem trace_transpose_mul_right_involution (A Q : Matrix ι ι ℝ) (hQ : Q.IsSymm)
    (hQQ : Q * Q = 1) :
    Matrix.trace ((A * Q).transpose * (A * Q)) = Matrix.trace (A.transpose * A) := by
  rw [Matrix.transpose_mul, hQ]
  calc
    Matrix.trace (Q * A.transpose * (A * Q)) = Matrix.trace ((A.transpose * A * Q) * Q) := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm Q (A.transpose * A * Q)
    _ = Matrix.trace (A.transpose * A) := by rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]

section TraceConjugation

omit [DecidableEq ι]
theorem trace_symmetric_conjugation (S H : Matrix ι ι ℝ) :
    Matrix.trace (S * H * S) = Matrix.trace ((S * S) * H) := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle S H S

theorem trace_transpose_conjugation_sq (S H : Matrix ι ι ℝ) (hS : S.IsSymm) (hH : H.IsSymm) :
    Matrix.trace ((S * H * S).transpose * (S * H * S)) =
      Matrix.trace ((S * S) * H * (S * S) * H) := by
  have hSt : S.transpose = S := hS
  have hHt : H.transpose = H := hH
  have ht : (S * H * S).transpose = S * H * S := by
    simp only [Matrix.transpose_mul, hSt, hHt, Matrix.mul_assoc]
  rw [ht]
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (S * H * S * S * H) S

end TraceConjugation

end FunctionalInequalities.Analysis

end
