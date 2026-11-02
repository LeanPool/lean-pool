/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.CoarseGaugeNullLagrangian
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.SolutionIntegrability

/-!
# CoarseGaugeResponse

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the response functional under a constant skew shift of the field

With the admissible class fixed by `isAHarmonicGradient_sub_const_skew`, the
shift `a |-> a - hbar` of ABK26 acts on the Chapter 2 response functional
`Homogenization.Book.Ch02.responseJ` by a *shear of the load*:

```
J(U, p, q; a - hbar) = J(U, p, q - hbar p; a) .
```

Indeed the response integrand
`- (1/2) grad v . symm(a) grad v - p . a grad v + q . grad v`
changes only in its middle term, by `p . hbar grad v = - (hbar p) . grad v`,
and its first term does not change at all because `symm(a - hbar) = symm(a)`.

The two solution transfers `transferSolutionSub` and `transferSolutionAdd`
realize the class bijection at the level of
`Homogenization.Book.Ch02.Solution`, keeping the underlying `H^1` function; the
flux `L^2` bound they need is CoarseGraining's
`Homogenization.Book.Ch02.Solution.flux_memVectorL2`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02

variable {d : ℕ}

/-! ## The class bijection -/

/-- An `a`-harmonic function, read as an `(a - hbar)`-harmonic function. -/
noncomputable def transferSolutionSub {U : Domain d} {a b : CoeffOn U}
    {hbar : Mat d} (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar)
    (u : Solution U a) : Solution U b where
  toH1 := u.toH1
  isHarmonic := by
    have h := isAHarmonicGradient_sub_const_skew (U := (U : Set (Vec d)))
      U.isOpen hskew (Solution.flux_memVectorL2 u) u.isHarmonic
    have hfun : b.toCoeffField = fun x => a.toCoeffField x - hbar := funext hab
    rw [hfun]
    exact h

/-- An `(a - hbar)`-harmonic function, read as an `a`-harmonic function. -/
noncomputable def transferSolutionAdd {U : Domain d} {a b : CoeffOn U}
    {hbar : Mat d} (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar)
    (v : Solution U b) : Solution U a where
  toH1 := v.toH1
  isHarmonic := by
    have hneg : matTranspose (-hbar) = -(-hbar) := by
      rw [matTranspose_neg, hskew]
    have h := isAHarmonicGradient_sub_const_skew (U := (U : Set (Vec d)))
      U.isOpen hneg (Solution.flux_memVectorL2 v) v.isHarmonic
    have hfun : a.toCoeffField = fun x => b.toCoeffField x - -hbar := by
      funext x
      rw [hab x, sub_neg_eq_add, sub_add_cancel]
    rw [hfun]
    exact h

/-! ## The sheared response -/

/-- The response integrand for `a - hbar` at load `(p, q)` is the response
integrand for `a` at the sheared load `(p, q - hbar p)`. -/
theorem responseIntegrand_sub_const_skew {U : Domain d} {a b : CoeffOn U}
    {hbar : Mat d} (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar)
    (p q : Vec d) (v : Solution U b) (u : Solution U a)
    (hgrad : v.toH1.grad = u.toH1.grad) :
    responseIntegrand U b p q v =
      responseIntegrand U a p (q - matVecMul hbar p) u := by
  funext x
  simp only [responseIntegrand]
  rw [hgrad, hab x, symmPart_sub_of_transpose_eq_neg hskew, sub_matVecMul,
    vecDot_sub_right, vecDot_matVecMul_swap_of_transpose_eq_neg hskew p,
    vecDot_sub_left]
  ring

theorem responseValue_sub_const_skew {U : Domain d} {a b : CoeffOn U}
    {hbar : Mat d} (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar)
    (p q : Vec d) (v : Solution U b) (u : Solution U a)
    (hgrad : v.toH1.grad = u.toH1.grad) :
    responseValue U b p q v = responseValue U a p (q - matVecMul hbar p) u := by
  unfold responseValue
  rw [responseIntegrand_sub_const_skew hskew hab p q v u hgrad]

/-- The load shear identity for the Chapter 2 response functional. -/
theorem responseJ_sub_const_skew {U : Domain d} {a b : CoeffOn U}
    {hbar : Mat d} (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar)
    (p q : Vec d) :
    responseJ U b p q = responseJ U a p (q - matVecMul hbar p) := by
  unfold responseJ
  congr 1
  ext m
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨transferSolutionAdd hskew hab v,
      responseValue_sub_const_skew hskew hab p q v
        (transferSolutionAdd hskew hab v) rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨transferSolutionSub hskew hab u,
      (responseValue_sub_const_skew hskew hab p q
        (transferSolutionSub hskew hab u) u rfl).symm⟩

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
