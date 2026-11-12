/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PartialOdometer
public import LeanPool.ApollonianSuperharmonic.FordVertexDomain

-- [TABLET NODE: P4217T2SquareRestriction]

/-!
# P4217T2SquareRestriction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a nonnegative integer $q$ and an integer lattice function $g$, let
$\operatorname{SqRes}_q(g)$ have domain
$\{(r,t):r,t\in\{0,\ldots,q\}\}$, value $g(x)$ on
$\operatorname{FordVertexDomain}(q)$, and value zero elsewhere. This defines
the partial odometer $\operatorname{SqRes}_q(g)$.
-/
noncomputable def P4217T2SquareRestriction (q : Nat)
    (g : IntegerLatticeFunction) : PartialOdometer := by
-- BODY
  classical
  exact
  { domain := (((Finset.range (q + 1)).product (Finset.range (q + 1))).image
      (fun a => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt)))
    value := fun x => if x ∈ FordVertexDomain q then g x else 0
    value_outside := by
      intro x hx
      apply ite_eq_right
      rintro ⟨hr, hrq, hi, hiq⟩
      apply hx
      apply Finset.mem_image.mpr
      refine ⟨(x.re.toNat, x.im.toNat), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Finset.mem_range.mpr (by omega)⟩
      · apply Zsqrtd.ext <;> simp [hr, hi] }

end ApollonianSuperharmonic

end
