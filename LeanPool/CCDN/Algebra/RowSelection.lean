/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.MonomialEvaluationMatrix
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import LeanPool.CCDN.ForMathlib.Matrix

/-!
Independent rows can be selected from the finite evaluation matrix.
A nonzero annihilator gives the strict rank deficiency required by Bombieri--Vaaler.

The determinant argument selects independent evaluation rows. This module justifies why a
coefficient vector annihilating those rows vanishes on every point whose row they span.
-/

@[expose] public section

namespace CCDN

open Matrix

private theorem dotProduct_eq_zero_of_mem_span {s N : ℕ}
    (A : Matrix (Fin s) (Fin N) ℚ) (v : Fin N → ℚ) (hAv : A *ᵥ v = 0)
    {r : Fin N → ℚ} (hr : r ∈ Submodule.span ℚ (Set.range A.row)) : r ⬝ᵥ v = 0 := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨i, rfl⟩ := hr
    exact congrFun hAv i
  | zero => simp
  | add x y hx hy ihx ihy => simp [add_dotProduct, ihx, ihy]
  | smul a x hx ih => simp [smul_dotProduct, ih]

private theorem integer_dotProduct_eq_zero_of_mem_span {s N : ℕ}
    (A : Matrix (Fin s) (Fin N) ℤ) (v : Fin N → ℤ) (hAv : A *ᵥ v = 0)
    {r : Fin N → ℤ}
    (hr : (fun j => (r j : ℚ)) ∈ Submodule.span ℚ (Set.range (A.map ((↑) : ℤ → ℚ)).row)) :
    r ⬝ᵥ v = 0 := by
  have hAvQ : A.map ((↑) : ℤ → ℚ) *ᵥ (fun j => (v j : ℚ)) = 0 := by
    ext i
    have hi := congrFun hAv i
    change ∑ j, (A i j : ℚ) * (v j : ℚ) = 0
    exact_mod_cast hi
  have h := dotProduct_eq_zero_of_mem_span _ _ hAvQ hr
  simp only [dotProduct] at h ⊢
  exact_mod_cast h

/-- If an integer coefficient vector `v` annihilates the evaluation matrix of the monomials
`mon` at the points `points`, then the polynomial with coefficients `v` vanishes at every
integer point `x` whose monomial evaluation row lies in the `ℚ`-span of the matrix rows. -/
theorem vanishes_of_evaluation_row_mem_span {n N s : ℕ}
    (mon : Fin N → (Fin n →₀ ℕ)) (points : Fin s → (Fin n → ℤ))
    (v : Fin N → ℤ) (hAv : evaluationMatrix mon points *ᵥ v = 0)
    (x : Fin n → ℤ)
    (hx : (fun j => (((mon j).prod (fun k e => x k ^ e) : ℤ) : ℚ)) ∈
      Submodule.span ℚ (Set.range ((evaluationMatrix mon points).map ((↑) : ℤ → ℚ)).row)) :
    MvPolynomial.eval x (polynomialOfCoefficients mon v) = 0 := by
  have h := integer_dotProduct_eq_zero_of_mem_span _ _ hAv hx
  simpa [polynomialOfCoefficients, MvPolynomial.eval_monomial, dotProduct, mul_comm] using h

end CCDN

namespace CCDN
open Matrix

/-- Every matrix with `N` columns has an injectively indexed family of `s ≤ N` linearly
independent rows spanning its row space. -/
theorem exists_independent_spanning_rows {F ι : Type*} [Field F] {N : ℕ}
    (A : Matrix ι (Fin N) F) :
    ∃ (s : ℕ) (a : Fin s → ι), Function.Injective a ∧
      LinearIndependent F (A.submatrix a id).row ∧
      Submodule.span F (Set.range (A.submatrix a id).row) =
        Submodule.span F (Set.range A.row) ∧ s ≤ N := by
  obtain ⟨s, a, ha, hli, hs⟩ := Matrix.exists_fin_linearIndependent_row_span_eq A
  exact ⟨s, a, ha, hli, hs, by simpa using hli.fintype_card_le_finrank⟩

/-- A nonzero relation on all columns forces every independent row family
to contain strictly fewer rows than columns. -/
private theorem independent_rows_lt_of_kernel {s N : ℕ} (A : Matrix (Fin s) (Fin N) ℚ)
    (hA : LinearIndependent ℚ A.row) (v : Fin N → ℚ) (hv : v ≠ 0)
    (hker : A *ᵥ v = 0) : s < N := by
  have hle : s ≤ N := by simpa using hA.fintype_card_le_finrank
  by_contra h
  have he : s = N := by omega
  by_cases hs : s = 0
  · have hN : N = 0 := by omega
    apply hv
    funext j
    have hj := j.isLt
    omega
  let : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
  have hspan : Submodule.span ℚ (Set.range A.row) = ⊤ :=
    hA.span_eq_top_of_card_eq_finrank (by simpa using he)
  apply hv
  funext j
  have hz := dotProduct_eq_zero_of_mem_span A v hker
    (r := Pi.single j 1) (by rw [hspan]; trivial)
  simpa using hz

/-- If a rational matrix with `N` columns has a nonzero kernel vector, then some injectively
indexed family of `s < N` linearly independent rows spans its row space. -/
theorem exists_independent_spanning_rows_lt {t N : ℕ}
    (A : Matrix (Fin t) (Fin N) ℚ) (v : Fin N → ℚ) (hv : v ≠ 0)
    (hker : A *ᵥ v = 0) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧
      LinearIndependent ℚ (A.submatrix a id).row ∧
      Submodule.span ℚ (Set.range (A.submatrix a id).row) =
        Submodule.span ℚ (Set.range A.row) ∧ s < N := by
  obtain ⟨s, a, ha, hi, hs, _⟩ := exists_independent_spanning_rows A
  refine ⟨s, a, ha, hi, hs, independent_rows_lt_of_kernel _ hi v hv ?_⟩
  ext i
  exact congrFun hker (a i)

end CCDN
