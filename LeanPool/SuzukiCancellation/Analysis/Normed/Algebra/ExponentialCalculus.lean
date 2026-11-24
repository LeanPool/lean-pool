/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.RealScalar
public import LeanPool.SuzukiCancellation.Analysis.Calculus.Taylor
public import LeanPool.SuzukiCancellation.Analysis.Calculus.IteratedDeriv.ListProd
public import LeanPool.SuzukiCancellation.Algebra.Algebra.ScalarIdentities
public import LeanPool.SuzukiCancellation.Algebra.Star.SkewAdjoint
public import LeanPool.SuzukiCancellation.Analysis.Normed.Module.RealScalar
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.Exponential
public import LeanPool.SuzukiCancellation.Algebra.BigOperators.FinAntidiagonal
public import LeanPool.SuzukiCancellation.Analysis.Calculus.ListProd

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Calculus of normed algebra exponentials

Exponential derivatives, smoothness and skew-adjoint estimates in complete normed algebras.

The real scalar action in the derivative statements is the canonical extension from `ℚ`.
Use `open scoped RealScalar` when applying them to a complete normed `ℚ`-algebra.

## Main results

* `iteratedDeriv_exp_smul_const`: the higher derivative of the exponential curve.
* `contDiff_exp_smul_const`: smoothness.
* `exp_smul_mem_unitary_of_skewAdjoint`, `norm_exp_smul_of_skewAdjoint`: unitary evolution.
* `norm_pow_mul_exp_le`: a power times an exponential.
-/

@[expose] public section

namespace TrotterError

open NormedSpace
open Asymptotics
open Finset
open scoped Topology BigOperators ContDiff algebraMap

section

open scoped RealScalar

/-- Exponentials of real multiples of one generator form an additive one-parameter group. -/
lemma exp_smul_mul_exp_smul {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
    [CompleteSpace A] (G : A) (x y : ℝ) :
    exp (x • G) * exp (y • G) = exp ((x + y) • G) := by
  rw [← exp_add_of_commute (((Commute.refl G).smul_left x).smul_right y), ← add_smul]

/-- The `q`-th iterated derivative of `u ↦ exp (u • A)` is `u ↦ A^q * exp (u • A)`. -/
theorem iteratedDeriv_exp_smul_const {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A : 𝔸) (q : ℕ) :
    iteratedDeriv q (fun u : ℝ => exp (u • A)) = fun u : ℝ => A ^ q * exp (u • A) := by
  induction q with
  | zero =>
      simp [iteratedDeriv_zero]
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [((hasDerivAt_exp_smul_const' A t).const_mul (A ^ q)).deriv]
      simp [pow_succ, mul_assoc]

/-- `u ↦ exp (u • A)` is `C^m` at every point. -/
lemma contDiffAt_exp_smul_const {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A : 𝔸) (m : ℕ) (t : ℝ) :
    ContDiffAt ℝ m (fun u : ℝ => exp (u • A)) t :=
  (NormedSpace.exp_analytic (t • A)).contDiffAt.comp t
    (ContDiffAt.smul (f := fun u : ℝ => u) (g := fun _ : ℝ => A) contDiffAt_id contDiffAt_const)

/-- `u ↦ exp (u • A)` is smooth. -/
lemma contDiff_exp_smul_const {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A : 𝔸) :
    ContDiff ℝ ∞ (fun t : ℝ => exp (t • A)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  exact ((NormedSpace.exp_analytic (t • A)).contDiffAt).comp t
    (ContDiffAt.smul (f := fun u : ℝ => u) (g := fun _ : ℝ => A) contDiffAt_id contDiffAt_const)

end

/-- The exponential of a real multiple of a skew-adjoint element is unitary. -/
lemma exp_smul_mem_unitary_of_skewAdjoint {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸]
    [StarModule ℝ 𝔸] {a : 𝔸} (ha : star a = -a) (t : ℝ) :
    exp (t • a) ∈ unitary 𝔸 := by
  have hta : star (t • a) = -(t • a) := by
    rw [StarModule.star_smul, ha, smul_neg, star_trivial]
  exact exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.mem_iff.mpr hta)

/-- In a C*-algebra, the exponential of an anti-Hermitian (`star a = -a`) multiple is unitary,
hence has norm `1`: `‖exp (t • a)‖ = 1`. -/
lemma norm_exp_smul_of_skewAdjoint {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] {a : 𝔸} (ha : star a = -a) (t : ℝ) :
    ‖exp (t • a)‖ = 1 :=
  CStarRing.norm_of_mem_unitary (exp_smul_mem_unitary_of_skewAdjoint ha t)

/-- A skew-adjoint exponential is a contraction, including in the zero algebra. -/
lemma norm_exp_smul_le_one_of_skewAdjoint {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [StarModule ℝ 𝔸]
    {a : 𝔸} (ha : star a = -a) (t : ℝ) : ‖exp (t • a)‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial 𝔸 with h | h
  · have := h
    simp [Subsingleton.elim (exp (t • a)) 0]
  · have := h
    exact (norm_exp_smul_of_skewAdjoint ha t).le

/-- For a single element, the norm of `H^k * exp (s • H)` is bounded by
`‖H‖^k * Real.exp (s * ‖H‖)` whenever `s ≥ 0` (the paper's single-element bound,
prelim.tex:186–187). -/
theorem norm_pow_mul_exp_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedSpace ℝ 𝔸] [NormOneClass 𝔸] (H : 𝔸) (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ‖H ^ k * exp (s • H)‖ ≤ ‖H‖ ^ k * Real.exp (s * ‖H‖) := by
  calc
    ‖H ^ k * exp (s • H)‖ ≤ ‖H ^ k‖ * ‖exp (s • H)‖ := norm_mul_le _ _
    _ ≤ ‖H‖ ^ k * Real.exp ‖s • H‖ := mul_le_mul (norm_pow_le H k) (FQFP.norm_exp_le (s • H))
          (norm_nonneg _) (pow_nonneg (norm_nonneg H) k)
    _ = ‖H‖ ^ k * Real.exp (s * ‖H‖) := by
        congr 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]

end TrotterError
