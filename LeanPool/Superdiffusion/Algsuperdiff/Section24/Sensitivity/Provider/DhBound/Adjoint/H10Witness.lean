/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.DhIdentification
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly.SplitIdentity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.GradientUniqueness

/-!
# H10Witness

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The zero-trace witness for the response combination `½(∇v* + ∇v) + p`

Source: ABK26.  The `D_h` splitting identity
`quadForm_coarseMatrixDerivative_eq_split` consumes a single input, namely that
the combination

  `∇w + ∇w* + p = ½ (∇v(·,U,p,q;a) + ∇v(·,U,p,-q;aᵗ)) + p`

belongs to `L²_{pot,0}(U)`, i.e. is a.e. the gradient of an honest `H¹₀(U)`
function.  This module supplies that witness at an arbitrary Chapter 2 domain.

The proof is an adjoint flip carried out inside the doubled-`mu` formalism.
Let `X` be a minimizer of `mu(U, (-p, q); a)`, which exists at every Chapter 2
domain and coefficient by `doubledMuTheory`.  Two facts about `X` combine:

* admissibility.  `IsDoubledMuAdmissible U (-p, q) X` says by definition that
  `X.potential - (-p) ∈ L²_{pot,0}(U)`, and the `L²_{pot,0}` predicate is
  literally "a.e. equal to the gradient of an `H¹₀` function".  So the `H¹₀`
  witness is *already there*; only its gradient has to be identified.
* extraction.  Writing `B x` for the lower block of `A(x) X(x)`, the public
  CoarseGraining extraction lemma gives `X.potential + B =ᵃᵉ ∇v` for the primal
  canonical maximizer at `(p, q)`, and its flip-flip/transpose companion
  `doubledMuMinimizer_neg_left_extracts_adjointMaximizerGradient` (proved in
  `Provider/Path/DhIdentification.lean`) gives `X.potential - B =ᵃᵉ ∇v*` for
  the adjoint canonical maximizer of `aᵗ` at `(p, -q)`.  Adding the two kills
  `B` and yields `X.potential =ᵃᵉ ½ (∇v* + ∇v)`.

Chapter 2 a.e. uniqueness of maximizer gradients then replaces the two
canonical maximizers by arbitrary given ones, which is exactly the hypothesis
shape of the splitting identity.

No convexity, ellipticity, selection, representative, or recovery-system
premise is needed beyond what `Domain d` and `CoeffOn U` already carry.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Adjoint

open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section24.Sensitivity.Provider.Path
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The potential block of a `mu`-minimizer is the half-sum of the two
maximizer gradients -/

/-- **Adjoint flip for the potential block.**  For a doubled-`mu` minimizer `X`
at loading `(-p, q)`, the potential block is a.e. the half-sum of the adjoint
and primal canonical response-maximizer gradients.

This is the sum of the two extraction lemmas: the lower block image `B` of `X`
enters the primal extraction with a `+` and the adjoint extraction with a `-`,
so it cancels. -/
theorem potential_ae_eq_half_add_canonicalMaximizerGradients
    {U : Domain d} (a : CoeffOn U) (p q : Vec d) {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U a (-p, q) X) :
    X.potential =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => (2 : ℝ)⁻¹ •
        ((canonicalMaximizer (responseExistenceTheory U a.transpose)
              p (-q)).toSolution.toH1.grad x
          + (canonicalMaximizer (responseExistenceTheory U a)
              p q).toSolution.toH1.grad x) := by
  have hplus :=
    doubledMuMinimizer_negLeft_eq_canonicalGradient U a p q hX
  have hminus :=
    doubledMuMinimizer_neg_left_extracts_adjointMaximizerGradient a p q hX
  filter_upwards [hplus, hminus] with x h1 h2
  funext i
  have e1 : X.potential x i +
      (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).2 i =
      (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad x i :=
    congrFun h1 i
  have e2 : X.potential x i -
      (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).2 i =
      (canonicalMaximizer (responseExistenceTheory U a.transpose)
        p (-q)).toSolution.toH1.grad x i :=
    congrFun h2 i
  change X.potential x i = (2 : ℝ)⁻¹ *
    ((canonicalMaximizer (responseExistenceTheory U a.transpose)
        p (-q)).toSolution.toH1.grad x i
      + (canonicalMaximizer (responseExistenceTheory U a)
          p q).toSolution.toH1.grad x i)
  linarith

/-! ## The `H¹₀` witness at a general Chapter 2 domain -/

/-- **The zero-trace witness for the response combination.**

At any Chapter 2 domain `U` and coefficient `a`, given a response maximizer `v`
for `(a, p, q)` and a maximizer `vAdj` for the adjoint problem `(aᵗ, p, -q)`,
the field `½ (∇vAdj + ∇v) + p` is a.e. the gradient of an `H¹₀(U)` function.

This is exactly the `u`-premise of
`quadForm_coarseMatrixDerivative_eq_split`. -/
theorem exists_h10Function_grad_ae_eq_halfSum_add_const
    (U : Domain d) (a : CoeffOn U) (p q : Vec d)
    (vAdj : Solution U a.transpose) (v : Solution U a)
    (hvAdj : IsResponseMaximizer U a.transpose p (-q) vAdj)
    (hv : IsResponseMaximizer U a p q v) :
    ∃ u : H10Function ((U : Set (Vec d))),
      ∀ᵐ x ∂ volumeMeasureOn ((U : Set (Vec d))),
        u.toH1Function.grad x =
          (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x) + p := by
  classical
  obtain ⟨X, hX⟩ := (doubledMuTheory U a).minimizer_exists (-p, q)
  obtain ⟨u, hu⟩ := hX.1.1.2
  refine ⟨u, ?_⟩
  have hpot := potential_ae_eq_half_add_canonicalMaximizerGradients a p q hX
  have hAdj :
      (canonicalMaximizer (responseExistenceTheory U a.transpose)
          p (-q)).toSolution.toH1.grad
        =ᵐ[volumeMeasureOn (U : Set (Vec d))] vAdj.toH1.grad :=
    canonicalMaximizer_sameGradientAE_of_isResponseMaximizer hvAdj
  have hPrimal :
      (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad
        =ᵐ[volumeMeasureOn (U : Set (Vec d))] v.toH1.grad :=
    canonicalMaximizer_sameGradientAE_of_isResponseMaximizer hv
  filter_upwards [hu, hpot, hAdj, hPrimal] with x h0 h1 h2 h3
  funext i
  have e0 : X.potential x i - -p i = u.toH1Function.grad x i := congrFun h0 i
  have e1 : X.potential x i = (2 : ℝ)⁻¹ *
      ((canonicalMaximizer (responseExistenceTheory U a.transpose)
          p (-q)).toSolution.toH1.grad x i
        + (canonicalMaximizer (responseExistenceTheory U a)
            p q).toSolution.toH1.grad x i) := congrFun h1 i
  have e2 : (canonicalMaximizer (responseExistenceTheory U a.transpose)
      p (-q)).toSolution.toH1.grad x i = vAdj.toH1.grad x i := congrFun h2 i
  have e3 : (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad x i
      = v.toH1.grad x i := congrFun h3 i
  change u.toH1Function.grad x i =
    (2 : ℝ)⁻¹ * (vAdj.toH1.grad x i + v.toH1.grad x i) + p i
  rw [← e2, ← e3, ← e1]
  linarith

/-! ## The frozen unit-cube carrier -/

/-- **The zero-trace witness at the frozen unit-cube carrier.** -/
theorem exists_h10Function_grad_ae_eq_halfSum_add_const_unitCube
    (a : CoeffOn (cubeDomain (originCube d 0))) (p q : Vec d)
    (vAdj : Solution (cubeDomain (originCube d 0)) a.transpose)
    (v : Solution (cubeDomain (originCube d 0)) a)
    (hvAdj : IsResponseMaximizer (cubeDomain (originCube d 0)) a.transpose p (-q) vAdj)
    (hv : IsResponseMaximizer (cubeDomain (originCube d 0)) a p q v) :
    ∃ u : H10Function ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      ∀ᵐ x ∂ volumeMeasureOn
          ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
        u.toH1Function.grad x =
          (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x) + p :=
  exists_h10Function_grad_ae_eq_halfSum_add_const
    (cubeDomain (originCube d 0)) a p q vAdj v hvAdj hv

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Adjoint

