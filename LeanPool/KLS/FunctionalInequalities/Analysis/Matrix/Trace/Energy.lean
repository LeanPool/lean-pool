/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.NoncommRing
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Trace.Power

/-!
# Spectral trace positivity, Jordan domination and tensor comparison
-/

@[expose] public section

open Matrix
namespace FunctionalInequalities.Analysis

section JordanTrace

/-! ### Positive spectral functions and trace energy of symmetric matrices

Support for Letwin, arXiv:2607.24164v1, Theorem 2.5 (the extension from positive semidefinite to all
symmetric `B`):
a nonnegative real function of a symmetric matrix is positive semidefinite
(`cfc_posSemidef_of_nonneg`, through the
orthonormal spectral representation `cfc_eq_mul_diagonal_mul`); for positive semidefinite `P`, `N`
and symmetric `H`
the mixed trace `tr(P H N H)` is nonnegative (`trace_cross_nonneg`); a positive semidefinite weight
makes the trace
energy `tr(B H B H)` of a symmetric `B` nonnegative (`trace_energy_nonneg`); and
`tr((P − N) H (P − N) H) ≤ tr(P H P H) + tr(N H N H)` without commutation
(`jordan_trace_domination`). Arbitrary
finite index types, including the empty one. Not provided here: the measure extension, the moment
map, Brascamp–Lieb
or Theorem 2.5 itself.
-/

open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Positivity of a real diagonal matrix, proved by an explicit Gram factor. -/
private theorem diagonal_posSemidef [Finite ι] (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (Matrix.diagonal d).PosSemidef := by
  let : Fintype ι := Fintype.ofFinite ι
  let D : Matrix ι ι ℝ := Matrix.diagonal (fun i => Real.sqrt (d i))
  have he : D.conjTranspose * D = Matrix.diagonal d := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [D, Matrix.mul_apply, Matrix.diagonal_apply, pow_two] using
        Real.sq_sqrt (hd i)
    · simp [D, Matrix.mul_apply, Matrix.diagonal_apply, hij]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self D

omit [Fintype ι] [DecidableEq ι] in
/-- For real matrices, positive semidefiniteness entails symmetry. -/
private theorem real_posSemidef_isSymm {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    A.IsSymm := by
  change A.transpose = A
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hA.isHermitian.eq

/-- Positivity of a nonnegative real spectral function, using the actual
orthonormal spectral representation of the matrix CFC. -/
theorem cfc_posSemidef_of_nonneg (B : Matrix ι ι ℝ) (hB : B.IsSymm)
    (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) : (cfc f B).PosSemidef := by
  have hHerm : B.IsHermitian := by
    change B.conjTranspose = B
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hB.eq]
  rw [FunctionalInequalities.Analysis.cfc_eq_mul_diagonal_mul hHerm f]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (diagonal_posSemidef (fun i => f (hHerm.eigenvalues i))
      (fun i => hf (hHerm.eigenvalues i))).mul_mul_conjTranspose_same
        (hHerm.eigenvectorUnitary : Matrix ι ι ℝ)

omit [DecidableEq ι] in
/-- A mixed weighted trace is nonnegative. The weight need only be symmetric;
it need not be positive semidefinite. -/
theorem trace_cross_nonneg {P N H : Matrix ι ι ℝ}
    (hP : P.PosSemidef) (hN : N.PosSemidef) (hH : H.IsSymm) :
    0 ≤ (P * H * N * H).trace := by
  classical
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  have he : (P * H * N * H).trace =
      ((X * H) * N * (X * H).conjTranspose).trace := by
    simp only [hX, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hH.eq]
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm X.transpose (X * H * N * H))
  rw [he]
  exact (hN.mul_mul_conjTranspose_same (X * H)).trace_nonneg

omit [DecidableEq ι] in
/-- A positive semidefinite weight makes the trace energy of every symmetric
real matrix nonnegative. -/
theorem trace_energy_nonneg {B H : Matrix ι ι ℝ}
    (hB : B.IsSymm) (hH : H.PosSemidef) :
    0 ≤ (B * H * B * H).trace := by
  classical
  have hHs : H.IsSymm := real_posSemidef_isSymm hH
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  have hX' : H = X.conjTranspose * X := by
    simpa only [Matrix.star_eq_conjTranspose] using hX
  let C : Matrix ι ι ℝ := X * B * X.conjTranspose
  have hC : C.IsSymm := by
    change C.transpose = C
    simp [C, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_mul, Matrix.mul_assoc, hB.eq]
  have hCpsd : (C * C).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hC.eq] using
      (Matrix.posSemidef_conjTranspose_mul_self C)
  have heq : (B * H * B * H).trace = (C * C).trace := by
    calc
      (B * H * B * H).trace =
          (B * (X.conjTranspose * X) * B *
            (X.conjTranspose * X)).trace := by rw [hX']
      _ = (X * (B * X.conjTranspose * X * B * X.conjTranspose)).trace := by
        simpa [Matrix.mul_assoc] using
          (Matrix.trace_mul_comm
            (B * X.conjTranspose * X * B * X.conjTranspose) X)
      _ = (C * C).trace := by simp [C, Matrix.mul_assoc]
  rw [heq]
  exact hCpsd.trace_nonneg

omit [DecidableEq ι] in
/-- Jordan decomposition gives pointwise trace-energy domination for every
symmetric weight, without a commutation assumption. -/
theorem jordan_trace_domination {P N H : Matrix ι ι ℝ}
    (hP : P.PosSemidef) (hN : N.PosSemidef) (hH : H.IsSymm) :
    ((P - N) * H * (P - N) * H).trace ≤
      (P * H * P * H).trace + (N * H * N * H).trace := by
  classical
  have hPNH := trace_cross_nonneg (P := P) (N := N) hP hN hH
  have hNPH := trace_cross_nonneg (P := N) (N := P) hN hP hH
  have hexpand :
      ((P - N) * H * (P - N) * H).trace =
        (P * H * P * H).trace - (P * H * N * H).trace -
          (N * H * P * H).trace + (N * H * N * H).trace := by
    calc
      ((P - N) * H * (P - N) * H).trace =
          (P * H * P * H - P * H * N * H -
            N * H * P * H + N * H * N * H).trace := by
        congr 1
        noncomm_ring
      _ = (P * H * P * H).trace - (P * H * N * H).trace -
          (N * H * P * H).trace + (N * H * N * H).trace := by
        simp only [Matrix.trace_add, Matrix.trace_sub]
  rw [hexpand]
  linarith

end JordanTrace

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section TensorComparison

private lemma letwin_real_transpose {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    Mᵀ = M := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hM.eq

open scoped MatrixOrder in
private lemma letwin_psd_factor {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, A = Pᵀ * P := by
  classical
  obtain ⟨P, hP⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  refine ⟨P, ?_⟩
  simpa only [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hP

private lemma letwin_trace_square_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (A * A).trace ≤ (A * Aᵀ).trace := by
  classical
  change (∑ i, ∑ j, A i j * A j i) ≤ ∑ i, ∑ j, A i j * A i j
  have hswap :
      (∑ i, ∑ j, A j i * A j i) = ∑ i, ∑ j, A i j * A i j := by
    rw [Finset.sum_comm]
  have h :
      2 * (∑ i, ∑ j, A i j * A j i) ≤
        (∑ i, ∑ j, A i j * A i j) + (∑ i, ∑ j, A j i * A j i) := by
    calc
      2 * (∑ i, ∑ j, A i j * A j i) =
          ∑ i, ∑ j, 2 * (A i j * A j i) := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ i, ∑ j, (A i j * A i j + A j i * A j i) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        nlinarith only [sq_nonneg (A i j - A j i)]
      _ = (∑ i, ∑ j, A i j * A i j) +
          (∑ i, ∑ j, A j i * A j i) := by
        simp only [Finset.sum_add_distrib]
  rw [hswap] at h
  linarith

private lemma letwin_trace_sandwich {n : ℕ}
    (P X : Matrix (Fin n) (Fin n) ℝ) :
    (P * X * Pᵀ).trace = (X * (Pᵀ * P)).trace := by
  calc
    (P * X * Pᵀ).trace = (P * (X * Pᵀ)).trace := by
      rw [Matrix.mul_assoc]
    _ = ((X * Pᵀ) * P).trace := Matrix.trace_mul_comm _ _
    _ = (X * (Pᵀ * P)).trace := by
      rw [Matrix.mul_assoc]

private lemma letwin_trace_sandwich_product {n : ℕ}
    (P X Y : Matrix (Fin n) (Fin n) ℝ) :
    ((P * X * Pᵀ) * (P * Y * Pᵀ)).trace =
      ((X * (Pᵀ * P)) * (Y * (Pᵀ * P))).trace := by
  calc
    ((P * X * Pᵀ) * (P * Y * Pᵀ)).trace =
        (P * (X * (Pᵀ * P) * Y) * Pᵀ).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((X * (Pᵀ * P) * Y) * (Pᵀ * P)).trace := by
      simpa only [Matrix.mul_assoc] using
        (letwin_trace_sandwich P (X * (Pᵀ * P) * Y))
    _ = ((X * (Pᵀ * P)) * (Y * (Pᵀ * P))).trace := by
      simp only [Matrix.mul_assoc]

private lemma letwin_slice_comparison {n : ℕ}
    (H B S P : Matrix (Fin n) (Fin n) ℝ)
    (hH : Hᵀ = H) (hB : Bᵀ = B) (hS : Sᵀ = S)
    (hcancel : H * (Pᵀ * P) = 1) :
    (B * S * B * S).trace ≤
      ((B * H * B) * S * (Pᵀ * P) * S).trace := by
  have hx : (S * B * H) * (Pᵀ * P) = S * B := by
    calc
      (S * B * H) * (Pᵀ * P) = (S * B) * (H * (Pᵀ * P)) := by
        rw [Matrix.mul_assoc]
      _ = S * B := by
        rw [hcancel, Matrix.mul_one]
  have ht :
      (P * (S * B * H) * Pᵀ)ᵀ = P * (H * B * S) * Pᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
      hH, hB, hS, Matrix.mul_assoc]
  have h := letwin_trace_square_le (P * (S * B * H) * Pᵀ)
  rw [ht] at h
  simp only [letwin_trace_sandwich_product, hx] at h
  calc
    (B * S * B * S).trace = (S * (B * S * B)).trace :=
      Matrix.trace_mul_comm _ _
    _ = ((S * B) * (S * B)).trace := by
      simp only [Matrix.mul_assoc]
    _ ≤ ((S * B) * ((H * B * S) * (Pᵀ * P))).trace := h
    _ = (S * (B * H * B * S * (Pᵀ * P))).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((B * H * B) * S * (Pᵀ * P) * S).trace :=
      Matrix.trace_mul_comm _ _

private lemma letwin_trace_weighted_slices {n : ℕ}
    (P A C : Matrix (Fin n) (Fin n) ℝ)
    (V : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ k, (A * (∑ a, P k a • V a) * C *
      (∑ b, P k b • V b)).trace) =
      ∑ a, ∑ b, (Pᵀ * P) a b * (A * V a * C * V b).trace := by
  classical
  have expand (x : Fin n → ℝ) :
      (A * (∑ a, x a • V a) * C * (∑ b, x b • V b)).trace =
        ∑ a, ∑ b, (x a * x b) * (A * V a * C * V b).trace := by
    have hf :
        A * (∑ a, x a • V a) * C = ∑ a, x a • (A * V a * C) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_smul_comm, smul_mul_assoc]
    have hm :
        A * (∑ a, x a • V a) * C * (∑ b, x b • V b) =
          ∑ a, ∑ b, (x a * x b) • (A * V a * C * V b) := by
      rw [hf, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hm]
    simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  calc
    (∑ k, (A * (∑ a, P k a • V a) * C *
        (∑ b, P k b • V b)).trace) =
        ∑ k, ∑ a, ∑ b, (P k a * P k b) * (A * V a * C * V b).trace := by
      apply Finset.sum_congr rfl
      intro k _
      exact expand (fun a => P k a)
    _ = ∑ a, ∑ b, ∑ k,
        (P k a * P k b) * (A * V a * C * V b).trace := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, (Pᵀ * P) a b * (A * V a * C * V b).trace := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_mul]
      rfl

private lemma letwin_sum_four_swap {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ i, ∑ j, f a b i j) =
      ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := by
  classical
  have h :
      (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
        f p.1 p.2 q.1 q.2) =
      ∑ q : Fin n × Fin n, ∑ p : Fin n × Fin n,
        f p.1 p.2 q.1 q.2 := Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using h

private lemma letwin_trace_contract {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) :
    (M * N).trace = ∑ i, ∑ j, M i j * N i j := by
  classical
  change (∑ i, ∑ j, M i j * N j i) = ∑ i, ∑ j, M i j * N i j
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hm : M j i = M i j :=
    congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hM
  rw [hm]

private lemma letwin_tensor_trace_identity {n : ℕ}
    (G M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M)
    (T : Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ a b c, T a b c = T a c b) :
    (∑ a, ∑ c, G a c *
      (M * Matrix.of (fun i j => T a i j) * G *
        Matrix.of (fun i j => T c i j)).trace) =
      ∑ i, ∑ j, M i j *
        ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * T a b i * T c d j := by
  classical
  let V : Fin n → Matrix (Fin n) (Fin n) ℝ :=
    fun a => Matrix.of (fun i j => T a i j)
  change (∑ a, ∑ c, G a c * (M * V a * G * V c).trace) = _
  have entry (i j : Fin n) :
      (∑ a, ∑ c, G a c * (V a * G * V c) i j) =
        ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * T a b i * T c d j := by
    calc
      (∑ a, ∑ c, G a c * (V a * G * V c) i j) =
          ∑ a, ∑ c, ∑ b, ∑ d,
            G a c * G b d * T a b i * T c d j := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro c _
        change G a c * (∑ d, (∑ b, T a i b * G b d) * T c d j) = _
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro d _
        rw [hT a i b]
        ring
      _ = ∑ a, ∑ b, ∑ c, ∑ d,
          G a c * G b d * T a b i * T c d j := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
  have ht (a c : Fin n) :
      (M * V a * G * V c).trace =
        ∑ i, ∑ j, M i j * (V a * G * V c) i j := by
    calc
      (M * V a * G * V c).trace = (M * (V a * G * V c)).trace := by
        simp only [Matrix.mul_assoc]
      _ = ∑ i, ∑ j, M i j * (V a * G * V c) i j :=
        letwin_trace_contract M _ hM
  calc
    (∑ a, ∑ c, G a c * (M * V a * G * V c).trace) =
        ∑ a, ∑ c, ∑ i, ∑ j,
          M i j * (G a c * (V a * G * V c) i j) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      rw [ht a c]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, ∑ a, ∑ c,
        M i j * (G a c * (V a * G * V c) i j) :=
      letwin_sum_four_swap _
    _ = ∑ i, ∑ j, M i j *
        (∑ a, ∑ c, G a c * (V a * G * V c) i j) := by
      simp only [Finset.mul_sum]
    _ = ∑ i, ∑ j, M i j *
        ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * T a b i * T c d j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [entry i j]

/-- **Letwin's tensor comparison** (Letwin arXiv:2607.24164v1, (2.12), p. 10), in arbitrary
coordinates: for a positive definite `H` (the Hessian `∇²φ(y)`), a symmetric `B` and a fully
symmetric 3-tensor `T` (the third derivatives `∂_{abi}φ(y)`), with slices `(T_a)_{ij} = T a i j`,
`∑_{a,b} (H⁻¹)_{ab} tr(B T_a B T_b) ≤ ∑_{i,j} (B H B)_{ij} ∑_{a,b,c,d} (H⁻¹)_{ac} (H⁻¹)_{bd} T_{abi}
T_{cdj}`. -/
theorem letwin_tensor_comparison {n : ℕ} (H B : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (hB : B.IsHermitian) (T : Fin n → Fin n → Fin n → ℝ) (hT₁ : ∀ a b c, T a b c = T b a c)
    (hT₂ : ∀ a b c, T a b c = T a c b) :
    ∑ a,
        ∑ b,
          H⁻¹ a b *
            (B * Matrix.of (fun i j => T a i j) * B * Matrix.of (fun i j => T b i j)).trace ≤
      ∑ i, ∑ j, (B * H * B) i j * ∑ a, ∑ b, ∑ c, ∑ d, H⁻¹ a c * H⁻¹ b d * T a b i * T c d j := by
  classical
  have hHt : Hᵀ = H := letwin_real_transpose H hH.isHermitian
  have hBt : Bᵀ = B := letwin_real_transpose B hB
  have hInv : (H⁻¹).PosSemidef := hH.inv.posSemidef
  obtain ⟨P, hP⟩ := letwin_psd_factor (H⁻¹) hInv
  have hcancel : H * (Pᵀ * P) = 1 := by
    rw [← hP]
    exact Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos))
  let V : Fin n → Matrix (Fin n) (Fin n) ℝ := fun a => Matrix.of (fun i j => T a i j)
  let S : Fin n → Matrix (Fin n) (Fin n) ℝ := fun k => ∑ a, (P k a) • V a
  have hSt (k : Fin n) : (S k)ᵀ = S k := by
    ext i j
    change (∑ a, (P k a) • V a) j i = (∑ a, (P k a) • V a) i j
    simp only [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    change P k a * T a j i = P k a * T a i j
    congr 1
    calc
      T a j i = T j a i := hT₁ a j i
      _ = T j i a := hT₂ j a i
      _ = T i j a := hT₁ j i a
      _ = T i a j := hT₂ i j a
      _ = T a i j := hT₁ i a j
  have hMt : (B * H * B)ᵀ = B * H * B := by
    simp only [Matrix.transpose_mul, hBt, hHt, Matrix.mul_assoc]
  change (∑ a, ∑ b, H⁻¹ a b * (B * V a * B * V b).trace) ≤ _
  calc
    (∑ a, ∑ b, H⁻¹ a b * (B * V a * B * V b).trace) = ∑ k, (B * S k * B * S k).trace := by
      symm
      simpa only [S, hP] using letwin_trace_weighted_slices P B B V
    _ ≤ ∑ k, ((B * H * B) * S k * (Pᵀ * P) * S k).trace := by
      apply Finset.sum_le_sum
      intro k _
      exact letwin_slice_comparison H B (S k) P hHt hBt (hSt k) hcancel
    _ = ∑ a, ∑ c, (Pᵀ * P) a c * ((B * H * B) * V a * (Pᵀ * P) * V c).trace :=
      letwin_trace_weighted_slices P (B * H * B) (Pᵀ * P) V
    _ = ∑ i, ∑ j, (B * H * B) i j * ∑ a, ∑ b, ∑ c, ∑ d, H⁻¹ a c * H⁻¹ b d * T a b i * T c d j := by
      simpa only [V, hP] using (letwin_tensor_trace_identity (Pᵀ * P) (B * H * B) hMt T hT₂)

end TensorComparison

end FunctionalInequalities.Analysis
