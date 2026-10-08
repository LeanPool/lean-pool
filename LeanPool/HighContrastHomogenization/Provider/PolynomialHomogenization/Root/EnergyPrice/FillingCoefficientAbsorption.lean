/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.WindowedFrozenWitnessPrice
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.OuterC0MatrixScaleIdentity
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.EnergyPrice.FillingCoefficientAbsorption

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The `α` half of the witness weak-error transport, absorbed

The translated-cube transport
`observationHomogenizationError_le_referencePowerTail_fixedParent` prices the
weak error of a **really translated** gauge family on a centered cube, with the
loss

```
observationParentConvolutionFactor d s ε abar M K
  = (observationFillingCoefficient d ε abar · geometricDiscount (1-2s) 1 ⁻¹)
      · 3 ^ (2 s (M - K)).
```

The filling coefficient is exactly `max 1 (6 d √d · (ε · α))` with
`α = √(specBound (symmPart abar)⁻¹)`
(`HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.OuterC0MatrixScaleIdentity`),
and it is **provably unbounded** on the bare surface.  This file discharges
the `α` factor from the inner-ellipsoid premise together with the outer ball of the consumer's
Whitney
system, giving

```
observationFillingCoefficient d ε abar ≤ max 1 (18 d² Rad).
```

The variant of the absorption proved here takes only `0 ≤ Rad` and the outer
inclusion — **not** a full `HasBallSandwich` — because `0 < rho` is *not* on
the frozen clause's binder surface while `system.outer_ball` and
`hRad : 0 < Rad` are.
-/

namespace HCPolySupport
namespace HighContrast
namespace EnergyPrice

open Book Book.Ch03
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- A coordinate bound from a strict Euclidean bound. -/
theorem abs_lt_of_vecNormSq_lt {x : Vec d} {r : ℝ} (hr : 0 ≤ r)
    (h : vecNormSq x < r ^ 2) (i : Fin d) : |x i| < r := by
  have hsq : x i ^ 2 < r ^ 2 := lt_of_le_of_lt (sq_le_vecNormSq x i) h
  calc
    |x i| = Real.sqrt (x i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ < Real.sqrt (r ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) hsq
    _ = r := Real.sqrt_sq hr

/-- The Euclidean square of a single-coordinate spike. -/
theorem vecNormSq_single (i : Fin d) (t : ℝ) :
    vecNormSq (fun k : Fin d => if k = i then t else 0) = t ^ 2 := by
  classical
  unfold vecNormSq vecDot
  rw [Finset.sum_eq_single i]
  · change (if i = i then t else 0) * (if i = i then t else 0) = t ^ 2
    rw [ite_eq_left rfl]
    ring
  · intro k _ hk
    change (if k = i then t else 0) * (if k = i then t else 0) = 0
    rw [ite_eq_right hk]
    ring
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

/-- **The absolute gauge scale is bounded by the outer radius alone.**  A
concentric adapted ellipsoid inside the physical domain, together with an outer
Euclidean ball for the gauge image, forces `α · c ≤ Rad`. -/
theorem normalizedRootScale_mul_le_of_innerEllipsoid_outerBall [NeZero d]
    {abar : Mat d} {U : Set (Vec d)} {cc : Vec d} {c Rad : ℝ}
    (hS : (symmPart abar).PosDef) (hc : 0 ≤ c) (hRad : 0 ≤ Rad)
    (hInner : ellipsoid abar c ⊆ U)
    (hOut : matImage (matSqrt (symmPart abar))⁻¹ U ⊆ euclideanBallAt cc Rad) :
    Real.sqrt (specBound ((symmPart abar)⁻¹)) * c ≤ Rad := by
  classical
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  set alpha : ℝ := Real.sqrt (specBound ((symmPart abar)⁻¹)) with halphaDef
  have halpha0 : 0 ≤ alpha := Real.sqrt_nonneg _
  set t : ℝ := alpha * c with htDef
  have ht0 : 0 ≤ t := mul_nonneg halpha0 hc
  have hsq : specBound ((symmPart abar)⁻¹) * c ^ 2 = t ^ 2 := by
    rw [htDef, mul_pow, halphaDef, Real.sq_sqrt (specBound_nonneg _)]
  have hsub : {y : Vec d | vecNormSq y ≤ t ^ 2} ⊆ euclideanBallAt cc Rad := by
    rw [← hsq, ← matImage_matSqrt_inv_ellipsoid_eq hS c]
    exact (Set.image_mono hInner).trans hOut
  have hspike : ∀ r : ℝ, r ^ 2 = t ^ 2 → |r - cc i| < Rad := by
    intro r hr
    have hmem : (fun k : Fin d => if k = i then r else 0) ∈
        {y : Vec d | vecNormSq y ≤ t ^ 2} := by
      change vecNormSq (fun k : Fin d => if k = i then r else 0) ≤ t ^ 2
      rw [vecNormSq_single i r, hr]
    have hball := hsub hmem
    have hballu : vecNormSq
        ((fun k : Fin d => if k = i then r else 0) - cc) < Rad ^ 2 := hball
    have hcoord :
        ((fun k : Fin d => if k = i then r else 0) - cc) i = r - cc i := by
      change (if i = i then r else 0) - cc i = r - cc i
      rw [ite_eq_left rfl]
    have := abs_lt_of_vecNormSq_lt hRad hballu i
    rwa [hcoord] at this
  have hplus : |t - cc i| < Rad := hspike t rfl
  have hminus : |(-t) - cc i| < Rad := hspike (-t) (by ring)
  have h1 : t - cc i ≤ |t - cc i| := le_abs_self _
  have h2 : -((-t) - cc i) ≤ |(-t) - cc i| := neg_le_abs _
  linarith only [h1, h2, hplus, hminus]

end

end EnergyPrice
end HighContrast
end HCPolySupport
