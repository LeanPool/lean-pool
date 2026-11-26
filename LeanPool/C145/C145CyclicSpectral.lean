/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145PhysicalFrame
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! Actual real Krylov spanning forces every spectral overlap to be nonzero and
every eigenvalue to be simple. No such conclusions are scientific premises. -/

@[expose] public section

noncomputable section
namespace C145.CyclicSpectral
open scoped BigOperators
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The iterates of the generator on the port span the whole vertex space. -/
def KrylovCyclic (A : Matrix V V ℝ) (b : V → ℝ) : Prop :=
  Submodule.span ℝ (Set.range (fun k : ℕ => A ^ k *ᵥ b)) = ⊤

theorem cyclic_annihilator (A : Matrix V V ℝ) (b x : V → ℝ)
    (hc : KrylovCyclic A b)
    (hx : ∀ k : ℕ, x ⬝ᵥ (A ^ k *ᵥ b) = 0) : x = 0 := by
  have hall : ∀ y ∈ Submodule.span ℝ (Set.range (fun k : ℕ => A ^ k *ᵥ b)),
      x ⬝ᵥ y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hx k
    | zero => simp
    | add y z _ _ hy hz => simp [dotProduct_add, hy, hz]
    | smul a y _ hy => simp [dotProduct_smul, hy]
  apply dotProduct_self_eq_zero.mp
  exact hall x (by rw [hc]; trivial)

theorem eigenvector_overlap_ne_zero (A : Matrix V V ℝ) (hs : A.IsSymm)
    (b x : V → ℝ) (hc : KrylovCyclic A b) (lam : ℝ)
    (he : A *ᵥ x = lam • x) (hx : x ≠ 0) : x ⬝ᵥ b ≠ 0 := by
  intro hz
  apply hx
  apply cyclic_annihilator A b x hc
  intro k
  induction k with
  | zero => simpa using hz
  | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, hs.dotProduct_mulVec_comm,
        he, dotProduct_smul, dotProduct_comm (A ^ k *ᵥ b) x, ih, smul_zero]

theorem eigenvalues_injective_of_cyclic {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hs : A.IsSymm)
    (b : Fin (n + 1) → ℝ) (hc : KrylovCyclic A b)
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : Fin (n + 1) → ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (he : ∀ i, A *ᵥ (fun v => Q v i) = lam i • (fun v => Q v i)) :
    Function.Injective lam := by
  intro i j hij
  by_contra hne
  let ai := (fun v => Q v i) ⬝ᵥ b
  let aj := (fun v => Q v j) ⬝ᵥ b
  have haj : aj ≠ 0 := eigenvector_overlap_ne_zero A hs b _ hc (lam j) (he j) (by
    intro hz
    have hh := hQ j j
    simp only at hh
    have hz' : ∀ v, Q v j = 0 := congrFun hz
    simp [hz'] at hh)
  let x : Fin (n + 1) → ℝ := aj • (fun v => Q v i) - ai • (fun v => Q v j)
  have hex : A *ᵥ x = lam i • x := by
    simp only [x, Matrix.mulVec_sub, Matrix.mulVec_smul, he, ← hij]
    module
  have hxb : x ⬝ᵥ b = 0 := by
    simp only [x, sub_dotProduct, smul_dotProduct]
    dsimp [ai, aj]; ring
  have hxz : x = 0 := by
    by_contra hx
    exact eigenvector_overlap_ne_zero A hs b x hc (lam i) hex hx hxb
  have hdot := congrArg (fun z => (fun v => Q v i) ⬝ᵥ z) hxz
  have hii : (fun v => Q v i) ⬝ᵥ (fun v => Q v i) = 1 := by
    simpa [dotProduct] using hQ i i
  have hij' : (fun v => Q v i) ⬝ᵥ (fun v => Q v j) = 0 := by
    simpa [dotProduct, hne] using hQ i j
  simp only [dotProduct_sub, dotProduct_smul, hii, smul_eq_mul, mul_one, hij', mul_zero,
    sub_zero, dotProduct_zero, x] at hdot
  exact haj hdot

theorem hermitian_frame {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.IsHermitian) :
    C145PhysicalFrame.ColumnOrthonormal
      (fun v i => (hA.eigenvectorBasis i) v) := by
  intro i j
  have hh := (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i j
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using hh

end C145.CyclicSpectral

end
