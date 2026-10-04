/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.CoeffC2


/-!
# `Cᵏ` coefficients indexed by the derivative order

Higher interior regularity (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1,
Theorem 2) runs by induction on `m`, and its hypothesis moves with the induction: reaching
`u ∈ H^{m+2}_loc` asks for `aᵢⱼ ∈ C^{m+1}`. A hypothesis whose derivative order is fixed by
the name of the structure cannot be the induction hypothesis of that argument, so
`IsC1Coeff` and `IsC2Coeff` each state one instance of a family and neither states the
family. This file gives the family.

`IsCkCoeff A k` bundles `ContDiff ℝ k` on every entry together with a uniform bound on each
iterated derivative of order `1 ≤ m ≤ k`. Orders start at one because order zero is already
supplied by `EllipticCoeff.Λ`, so the mixin adds exactly the derivative data and nothing that
the bundle beneath it already supplies.

The bounds are collected as a single function `bound : ℕ → ℝ` rather than as one field per
order. A `Fin (k+1)`-indexed family would record the order in its type and force a cast at every
use; the constraint `1 ≤ m ≤ k` in `iteratedFDeriv_bdd` says which values of the function are
meaningful, and `mono` then restricts to a lower order without touching it.

Derivatives are taken as `iteratedFDeriv`, where `IsC2Coeff` nests `fderiv` inside `fderiv`.
The two agree at order two (`norm_fderiv_fderiv_eq` below, from Mathlib's
`norm_iteratedFDeriv_fderiv` and `norm_iteratedFDeriv_one`), and only the iterated form has
a statement at a general order.

## Main declarations

* `IsCkCoeff`: the indexed mixin.
* `IsCkCoeff.mono`: an order-`k` bundle is an order-`l` bundle for every `l ≤ k`.
* `IsCkCoeff.toIsC1Coeff`, `IsC1Coeff.toIsCkCoeff`: the round trip at order one.
* `IsCkCoeff.toIsC2Coeff`, `IsC2Coeff.toIsCkCoeff`: the round trip at order two.

Both existing structures are left in place and unchanged, so every current consumer of
`IsC1Coeff` and `IsC2Coeff` is untouched, and a consumer written against the family can be
fed from either by the conversions above.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- The second derivative read as a nested `fderiv` and as `iteratedFDeriv` have the same
norm. This is the bridge between `IsC2Coeff.hess_bdd` and `IsCkCoeff.iteratedFDeriv_bdd`
at order two. -/
theorem norm_fderiv_fderiv_eq (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

/-- A `Cᵏ` ellipticity bundle: every coefficient entry is `k` times continuously
differentiable, with a uniform bound `bound m` on the iterated derivative of each order
`1 ≤ m ≤ k`. A mixin on top of `EllipticCoeff`, in the manner of `IsC1Coeff`, indexed by the
order so that it can serve as the induction hypothesis of Evans §6.3.1, Theorem 2. -/
structure IsCkCoeff (A : EllipticCoeff d) (k : ℕ) where
  /-- Every coefficient entry is `k` times continuously differentiable. -/
  contDiff : ∀ i j, ContDiff ℝ k (fun x => A.a x i j)
  /-- The uniform bound on the derivatives of each order. Only the values at `1 ≤ m ≤ k`
  are constrained by `iteratedFDeriv_bdd`. -/
  bound : ℕ → ℝ
  /-- Every bound is nonnegative. -/
  bound_nonneg : ∀ m, 0 ≤ bound m
  /-- The iterated derivative of order `m` of every entry is bounded by `bound m` at every
  point, for every order `m` between one and `k`. -/
  iteratedFDeriv_bdd : ∀ i j, ∀ m, 1 ≤ m → m ≤ k → ∀ x,
    ‖iteratedFDeriv ℝ m (fun y => A.a y i j) x‖ ≤ bound m

namespace IsCkCoeff

variable {A : EllipticCoeff d} {k l : ℕ}

/-- An order-`k` bundle is an order-`l` bundle for every `l ≤ k`: the differentiability
weakens by `ContDiff.of_le` and the bounds are inherited unchanged. -/
def mono (hA : IsCkCoeff A k) (hlk : l ≤ k) : IsCkCoeff A l where
  contDiff i j := (hA.contDiff i j).of_le (by exact_mod_cast hlk)
  bound := hA.bound
  bound_nonneg := hA.bound_nonneg
  iteratedFDeriv_bdd i j m hm hml x :=
    hA.iteratedFDeriv_bdd i j m hm (hml.trans hlk) x

/-- An order-`k` bundle with `1 ≤ k` is a `C¹` bundle, at the order-one bound. -/
def toIsC1Coeff (hA : IsCkCoeff A k) (hk : 1 ≤ k) : IsC1Coeff A where
  contDiff i j := (hA.contDiff i j).of_le (by exact_mod_cast hk)
  A1 := hA.bound 1
  A1_nonneg := hA.bound_nonneg 1
  grad_bdd i j x := by
    have h := hA.iteratedFDeriv_bdd i j 1 le_rfl hk x
    rwa [norm_iteratedFDeriv_one] at h

/-- An order-`k` bundle with `2 ≤ k` is a `C²` bundle, at the order-one and order-two
bounds. -/
def toIsC2Coeff (hA : IsCkCoeff A k) (hk : 2 ≤ k) : IsC2Coeff A where
  contDiff i j := (hA.contDiff i j).of_le (by exact_mod_cast hk)
  A1 := hA.bound 1
  A1_nonneg := hA.bound_nonneg 1
  grad_bdd i j x := by
    have h := hA.iteratedFDeriv_bdd i j 1 le_rfl (one_le_two.trans hk) x
    rwa [norm_iteratedFDeriv_one] at h
  A2 := hA.bound 2
  A2_nonneg := hA.bound_nonneg 2
  hess_bdd i j x := by
    have h := hA.iteratedFDeriv_bdd i j 2 one_le_two hk x
    rwa [norm_fderiv_fderiv_eq]

end IsCkCoeff

/-- A `C¹` bundle is an order-one bundle, the single bound `A1` serving every order. -/
def IsC1Coeff.toIsCkCoeff {A : EllipticCoeff d} (hA : IsC1Coeff A) : IsCkCoeff A 1 where
  contDiff := hA.contDiff
  bound _ := hA.A1
  bound_nonneg _ := hA.A1_nonneg
  iteratedFDeriv_bdd i j m hm hm1 x := by
    obtain rfl : m = 1 := le_antisymm hm1 hm
    rw [norm_iteratedFDeriv_one]
    exact hA.grad_bdd i j x

/-- A `C²` bundle is an order-two bundle, `A1` at order one and `A2` above it. -/
def IsC2Coeff.toIsCkCoeff {A : EllipticCoeff d} (hA : IsC2Coeff A) : IsCkCoeff A 2 where
  contDiff := hA.contDiff
  bound m := if m = 1 then hA.A1 else hA.A2
  bound_nonneg m := by
    by_cases hm : m = 1 <;> simp [hm, hA.A1_nonneg, hA.A2_nonneg]
  iteratedFDeriv_bdd i j m hm hm2 x := by
    interval_cases m
    · simpa using (norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fun y => A.a y i j) (x := x)).le.trans
        (hA.grad_bdd i j x)
    · simpa [norm_fderiv_fderiv_eq] using hA.hess_bdd i j x

end EllipticPdes.Regularity
