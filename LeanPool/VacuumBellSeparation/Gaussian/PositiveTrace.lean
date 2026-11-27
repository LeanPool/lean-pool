/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Tactic.TypeStar

/-!
# The extended trace of a positive Hilbert-space operator

The trace is an `ENNReal` sum, so it also applies to positive operators whose
trace is infinite. Basis independence is proved by Parseval and Tonelli for
the positive square root. No finite-dimensionality or trace-class hypothesis
is hidden in the definition.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι κ : Type*}

omit [CompleteSpace E] in
/-- Parseval in the real, nonnegative form needed for the extended trace. -/
theorem hasSum_basis_inner_norm_sq (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => ‖inner ℂ (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := Complex.hasSum_re (b.hasSum_inner_mul_inner x x)
  have hterm (i : ι) :
      (inner ℂ x (b i) * inner ℂ (b i) x).re = ‖inner ℂ (b i) x‖ ^ 2 := by
    rw [← inner_conj_symm, Complex.conj_mul']
    simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  have hself : (inner ℂ x x).re = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]
  simpa only [hterm, hself] using h

omit [CompleteSpace E] in
theorem tsum_basis_inner_norm_sq (b : HilbertBasis ι ℂ E) (x : E) :
    ∑' i, ENNReal.ofReal (‖inner ℂ (b i) x‖ ^ 2) =
      ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
    (hasSum_basis_inner_norm_sq b x).summable,
    (hasSum_basis_inner_norm_sq b x).tsum_eq]

/-- The squared Hilbert--Schmidt sum in a specified orthonormal basis.
It is permitted to be infinite. -/
noncomputable def basisSquareTrace (b : HilbertBasis ι ℂ E) (A : E →L[ℂ] E) :
    ℝ≥0∞ := ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)

/-- Basis independence for the self-adjoint operator to which we will apply
the square-root construction. -/
theorem basisSquareTrace_eq (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    basisSquareTrace b A = basisSquareTrace c A := by
  have hentry (i : ι) (j : κ) :
      ‖inner ℂ (c j) (A (b i))‖ = ‖inner ℂ (b i) (A (c j))‖ := by
    rw [← A.adjoint_inner_left, hA.adjoint_eq, norm_inner_symm]
  unfold basisSquareTrace
  calc
    (∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)) =
        ∑' i, ∑' j, ENNReal.ofReal (‖inner ℂ (c j) (A (b i))‖ ^ 2) := by
      exact tsum_congr fun i => (tsum_basis_inner_norm_sq c (A (b i))).symm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (c j) (A (b i))‖ ^ 2) :=
      tsum_comm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (b i) (A (c j))‖ ^ 2) := by
      exact tsum_congr fun j => tsum_congr fun i => by rw [hentry]
    _ = ∑' j, ENNReal.ofReal (‖A (c j)‖ ^ 2) := by
      exact tsum_congr fun j => tsum_basis_inner_norm_sq b (A (c j))

/-- The extended positive trace. For positive `T`, this is the sum of the
diagonal matrix elements in every Hilbert basis. Its meaning on nonpositive
inputs is deliberately not used. -/
noncomputable def positiveTrace (T : E →L[ℂ] E) : ℝ≥0∞ :=
  basisSquareTrace
    (Classical.choose (Classical.choose_spec (exists_hilbertBasis (𝕜 := ℂ) (E := E))))
    (CFC.sqrt T)

theorem positiveTrace_eq_basisSquareTrace (b : HilbertBasis ι ℂ E)
    (T : E →L[ℂ] E) : positiveTrace T = basisSquareTrace b (CFC.sqrt T) := by
  unfold positiveTrace
  exact basisSquareTrace_eq _ b (CFC.sqrt_nonneg T).isSelfAdjoint

theorem sqrt_norm_sq_eq_diagonal {T : E →L[ℂ] E} (hT : 0 ≤ T) (x : E) :
    ‖CFC.sqrt T x‖ ^ 2 = (inner ℂ x (T x)).re := by
  have hs : IsSelfAdjoint (CFC.sqrt T) := (CFC.sqrt_nonneg T).isSelfAdjoint
  have heq : inner ℂ (CFC.sqrt T x) (CFC.sqrt T x) = inner ℂ x (T x) := by
    rw [← (CFC.sqrt T).adjoint_inner_right, hs.adjoint_eq,
      ← mul_apply_eq_comp, ← pow_two, CFC.sq_sqrt T hT]
  calc
    ‖CFC.sqrt T x‖ ^ 2 = (inner ℂ (CFC.sqrt T x) (CFC.sqrt T x)).re := by
      rw [inner_self_eq_norm_sq_to_K]
      simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]
    _ = _ := congrArg Complex.re heq

/-- The ordinary definition of positive trace as an extended diagonal sum,
now independent of the chosen basis by the preceding proof. -/
theorem positiveTrace_eq_tsum_diagonal (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : 0 ≤ T) :
    positiveTrace T = ∑' i, ENNReal.ofReal ((inner ℂ (b i) (T (b i))).re) := by
  rw [positiveTrace_eq_basisSquareTrace b]
  unfold basisSquareTrace
  exact tsum_congr fun i => by rw [sqrt_norm_sq_eq_diagonal hT]

/-- Finiteness of the extended trace is the trace-class condition for a
positive operator. Positivity is retained as an explicit part of this predicate. -/
def IsPositiveTraceClass (T : E →L[ℂ] E) : Prop :=
  0 ≤ T ∧ positiveTrace T < ∞

theorem isPositiveTraceClass_of_summable_diagonal (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : 0 ≤ T)
    (hs : Summable fun i => (inner ℂ (b i) (T (b i))).re) :
    IsPositiveTraceClass T := by
  refine ⟨hT, ?_⟩
  rw [positiveTrace_eq_tsum_diagonal b hT]
  exact hs.tsum_ofReal_lt_top

/-- A faithful density operator on the actual Hilbert space. Faithfulness
means injectivity. -/
def IsFaithfulDensity (T : E →L[ℂ] E) : Prop :=
  0 ≤ T ∧ positiveTrace T = 1 ∧ Function.Injective T

theorem IsFaithfulDensity.isPositiveTraceClass {T : E →L[ℂ] E}
    (hT : IsFaithfulDensity T) : IsPositiveTraceClass T := by
  refine ⟨hT.1, ?_⟩
  rw [hT.2.1]
  exact ENNReal.one_lt_top

end VacuumBellSeparation.Gaussian
