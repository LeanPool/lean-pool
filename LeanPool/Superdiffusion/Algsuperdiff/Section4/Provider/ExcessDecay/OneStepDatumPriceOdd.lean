/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddValue

/-!
# OneStepDatumPriceOdd

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Pricing the odd-class defect: the split, the reduction, and the refutation

`OneStepBoundaryOdd` compresses the boundary branch's whole datum contribution
into the single scalar `oddClassDefect x m n V c A` recorded as its residue the
pricing

```text
  oddClassDefect x m n V c A ≤ C(d) · (3^{n-2})^{3/2} · [∇h]_{C^{0,1/2}(U₂)} ,
```

read as the manuscript's second boundary-Schauder leg.  This module settles the
shape of that residue.

## 1. The universally quantified reading is refuted

`oddClassDefect x m n V c A` is stated for an **arbitrary** odd affine datum
`(c,A) ∈ 𝕃_odd`.  At the zero competitor the defect is exactly the seminorm of
that datum (`oddClassDefect_zero_competitor`), so on any window carrying the
affine nondegeneracy the defect is **strictly positive** for every nonzero odd
affine datum (`oddClassDefect_zero_competitor_pos`) — while the datum side of the
pricing may be `0` (take `h ≡ 0`; note that `hVodd` already forces a *continuous*
competitor to vanish on the met face, so `h ≡ 0` on the face is the compatible
datum, not an extra assumption).  The pricing therefore cannot hold for an
arbitrary member of the odd class: it must be read **existentially**, at the best
odd affine datum, exactly as the manuscript's `min` over `𝕃_odd` does.

## 2. The best odd datum: the split at the met face

At a single met face `{yᵢ = a}` the odd class is the line `ℝ·(yᵢ − a)`
(`OddReflectionMap.slope_eq_zero_of_ne_of_meets`).  The canonical odd affine
datum attached to `(c,A)` is therefore its **normal part** `Aᵢ·(yᵢ − a)`
(`oddAffineIntercept`, `oddAffineSlope`), and the complement — the **even part**
`evenAffineIntercept`, `evenAffineSlope` — has vanishing `i`-slope
(`evenAffineSlope_apply_self`), i.e. it is constant along the reflection.

`oddClassDefect_oddPart_le` prices the defect at the odd part of *any* affine
datum by that datum's own excess gap plus the seminorm of the even part; at an
affine minimizer the gap vanishes and the reduction is exact:

```text
  oddClassDefect x m n V (odd part of ℓ*) ≤ ‖even part of ℓ*‖_{L²(U₂)} .
```

## 3. The exact remaining inequality (reported, not proved)

Let `V` be odd about the met face and harmonic on the doubled window, and let
`ℓ*` be an affine minimizer of `V` on `U₂`.  What remains is

```text
  ‖even part of ℓ*‖_{L²(U₂)}  ≤  C(d) · affineExcessRaw U₂ V .        (★)
```

Both sides are `L²(U₂)` quantities of the *same* homogeneity in `V`, and neither
mentions `h`; `(★)` is exactly the statement that odd harmonic functions cannot
approximate a nonzero even affine function on the half-box better than a fixed
fraction.  It is true — a competitor odd about the face vanishes there, while an
even affine function does not, and harmonicity **across** the face (the doubled
window puts the face in the interior) caps the transition rate at the window
scale, so the near-face slab already costs a fixed fraction of `‖even part‖`.
Its formalization needs interior gradient estimates for harmonic functions at
the face together with a reverse-Chebyshev bound for affine functions, and is
not attempted here.

`(★)` prices the defect by the excess itself, **not** by `[∇h]`.  That is the
architectural finding of this module: under `hVodd` the competitor vanishes on
the met face, i.e. the datum has already been subtracted, so the manuscript's
`[∇h]_{C^{0,1/2}(U₂)}` leg cannot enter through `oddClassDefect`; it belongs to
the (still missing) reduction from the true competitor `v = h` on `∂□_m` to an
odd one.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory
open HCPolySupport (Vec vecDot)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The odd/even split of an affine datum at a met upper face -/

/-- The intercept of the **normal part** `Aᵢ·(yᵢ − a)` of the affine datum
`(c,A)` at the met upper `i`-face `{yᵢ = a}`, `a = (1/2)·3^m`, in the
`affineLift` parametrization. -/
def oddAffineIntercept (x : Vec d) (m : ℤ) (i : Fin d) (A : Vec d) : ℝ :=
  A i * (x i - (1 / 2 : ℝ) * (3 : ℝ) ^ m)

/-- The slope of the normal part: `A` with every tangential coordinate erased. -/
def oddAffineSlope (i : Fin d) (A : Vec d) : Vec d := fun j => if j = i then A i else 0

/-- The slope of the **even part**: `A` minus its normal part. -/
def evenAffineSlope (i : Fin d) (A : Vec d) : Vec d := A - oddAffineSlope i A

/-- The intercept of the even part, in the `affineEval` parametrization. -/
def evenAffineIntercept (x : Vec d) (m : ℤ) (i : Fin d) (c : ℝ) (A : Vec d) : ℝ :=
  (c - vecDot A x) - (oddAffineIntercept x m i A - vecDot (oddAffineSlope i A) x)

@[simp] theorem oddAffineSlope_apply_self (i : Fin d) (A : Vec d) :
    oddAffineSlope i A i = A i := by
  rw [oddAffineSlope, ite_eq_left rfl]

/-- **The even part is constant along the reflection**: its normal slope
vanishes. -/
@[simp] theorem evenAffineSlope_apply_self (i : Fin d) (A : Vec d) :
    evenAffineSlope i A i = 0 := by
  rw [evenAffineSlope, Pi.sub_apply, oddAffineSlope_apply_self, sub_self]

/-- The normal part pairs with a vector through its `i`-coordinate only. -/
theorem vecDot_oddAffineSlope (i : Fin d) (A y : Vec d) :
    vecDot (oddAffineSlope i A) y = A i * y i := by
  classical
  have h : vecDot (oddAffineSlope i A) y = ∑ j : Fin d, oddAffineSlope i A j * y j := rfl
  have h2 : ∑ j : Fin d, oddAffineSlope i A j * y j = oddAffineSlope i A i * y i :=
    Finset.sum_eq_single i (fun j _ hji => by rw [oddAffineSlope, ite_eq_right hji, zero_mul])
      (fun hcon => absurd (Finset.mem_univ i) hcon)
  rw [h, h2, oddAffineSlope_apply_self]

/-- The normal part is the affine function `Aᵢ·(yᵢ − a)`. -/
theorem affineLift_oddAffineDatum (x : Vec d) (m : ℤ) (i : Fin d) (A y : Vec d) :
    affineLift x (oddAffineIntercept x m i A) (oddAffineSlope i A) y
      = A i * (y i - (1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
  have h : affineLift x (oddAffineIntercept x m i A) (oddAffineSlope i A) y
      = oddAffineIntercept x m i A + vecDot (oddAffineSlope i A) (y - x) := rfl
  rw [h, vecDot_oddAffineSlope, oddAffineIntercept, Pi.sub_apply]
  ring

/-- **The normal part lies in the odd class.**  In the one-met-face regime the
canonical odd affine datum attached to `(c,A)` is admissible for
`OneStepBoundaryOdd`. -/
theorem isOddAffineData_oddAffineDatum {x : Vec d} {m k : ℤ} {i : Fin d} (hkm : k < m)
    (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (A : Vec d) :
    IsOddAffineData x m k (oddAffineIntercept x m i A) (oddAffineSlope i A) := by
  classical
  constructor
  · intro j hj y hy
    by_cases hji : j = i
    · subst hji
      rw [affineLift_oddAffineDatum, hy, sub_self, mul_zero]
    · exact absurd hj (hother j hji).1
  · intro j hj _ _
    by_cases hji : j = i
    · subst hji
      exact absurd hj (not_meetsLowerFace_of_meetsUpperFace hkm hup)
    · exact absurd hj (hother j hji).2

/-! ## 2. The reduction: the defect at the normal part -/

/-- The affine datum splits: `ℓ = (normal part) + (even part)`, pointwise. -/
theorem affineEval_split (x : Vec d) (m : ℤ) (i : Fin d) (c : ℝ) (A y : Vec d) :
    affineEval (c - vecDot A x) A y
      = affineEval (oddAffineIntercept x m i A - vecDot (oddAffineSlope i A) x)
          (oddAffineSlope i A) y
        + affineEval (evenAffineIntercept x m i c A) (evenAffineSlope i A) y := by
  rw [evenAffineIntercept, evenAffineSlope]
  have h := affineEval_sub (c - vecDot A x)
    (oddAffineIntercept x m i A - vecDot (oddAffineSlope i A) x) A (oddAffineSlope i A) y
  rw [← h]
  ring

/-- **The reduction.**  The defect at the normal part of an affine datum is at
most that datum's own gap to the excess minimum plus the seminorm of the even
part. -/
theorem oddClassDefect_oddPart_le {m n : ℤ} {x : Vec d} {i : Fin d} {V : Vec d → ℝ}
    (hV : MemLp V 2 (volume.restrict (truncatedWindow x m (n - 2)))) (c : ℝ) (A : Vec d) :
    oddClassDefect x m n V (oddAffineIntercept x m i A) (oddAffineSlope i A)
      ≤ (affineDistOn (truncatedWindow x m (n - 2)) V (c - vecDot A x) A
            - affineExcessRaw (truncatedWindow x m (n - 2)) V)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (affineEval (evenAffineIntercept x m i c A) (evenAffineSlope i A)) := by
  set W : Set (Vec d) := truncatedWindow x m (n - 2) with hWdef
  set g : Vec d → ℝ := affineEval (evenAffineIntercept x m i c A) (evenAffineSlope i A)
    with hgdef
  have hsplit : (fun y => V y
        - affineEval (oddAffineIntercept x m i A - vecDot (oddAffineSlope i A) x)
            (oddAffineSlope i A) y)
      = fun y => (V y - affineEval (c - vecDot A x) A y) + g y := by
    funext y
    rw [hgdef, affineEval_split x m i c A y]
    ring
  have hmemL : MemLp (fun y => V y - affineEval (c - vecDot A x) A y) 2
      (volume.restrict W) :=
    hV.sub (memLp_affineEval_truncatedWindow x m (n - 2) (c - vecDot A x) A)
  have hmemg : MemLp g 2 (volume.restrict W) :=
    memLp_affineEval_truncatedWindow x m (n - 2) _ _
  have htri := normalizedL2On_add_le (W := W)
    (f := fun y => V y - affineEval (c - vecDot A x) A y) (g := g) hmemL hmemg
  have hkey : affineDistOn W V
        (oddAffineIntercept x m i A - vecDot (oddAffineSlope i A) x) (oddAffineSlope i A)
      ≤ affineDistOn W V (c - vecDot A x) A + normalizedL2On W g := by
    rw [affineDistOn_eq_normalizedL2On, hsplit]
    exact htri
  rw [oddClassDefect]
  linarith only [hkey]

/-- **The reduction at a minimizer.**  If `(c,A)` attains the excess minimum on
`U₂`, the defect at its normal part is at most the seminorm of its even part.
This is the exact residue: what remains's is the bound of the right side by
`C(d) · affineExcessRaw U₂ V`. -/
theorem oddClassDefect_oddPart_le_evenPart {m n : ℤ} {x : Vec d} {i : Fin d}
    {V : Vec d → ℝ} (hV : MemLp V 2 (volume.restrict (truncatedWindow x m (n - 2))))
    {c : ℝ} {A : Vec d}
    (hmin : IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A) :
    oddClassDefect x m n V (oddAffineIntercept x m i A) (oddAffineSlope i A)
      ≤ normalizedL2On (truncatedWindow x m (n - 2))
          (affineEval (evenAffineIntercept x m i c A) (evenAffineSlope i A)) := by
  have h := oddClassDefect_oddPart_le (i := i) hV c A
  rw [IsAffineMinimizer] at hmin
  rw [hmin] at h
  linarith only [h]

/-! ## 3. The refutation of the universally quantified pricing -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
