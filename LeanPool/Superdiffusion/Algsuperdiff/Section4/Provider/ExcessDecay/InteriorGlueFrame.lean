/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OffGridErrorCarrier
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Translation

/-!
# InteriorGlueFrame

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The off-grid error is a *cube* error in the translated frame

**It is not new: CoarseGraining already proves it**, unconditionally,
sorry-free, with oleans built —
`Homogenization/CoarseGraining/Translation.lean` carries the full covariance of
the coarse-graining apparatus under a *real* translation:

```text
  ResponseJ (w + U) p q a = ResponseJ U p q (a(· + w))        (:372)
  BlockJ    (w + U) P Q a = BlockJ    U P Q (a(· + w))        (:303)
  Mu        (w + U) P   a = Mu        U P   (a(· + w))        (:116)
  σ⋆, σ⋆⁻¹, κ, σ, b coarse: the same, at :378--:439 .
```

```text
  𝓔_{t,∞,2}(w + P; g, a₀) = 𝓔_{t,∞,2}(P; g(·+w), a₀) .
```

## What this unblocks (and what it does not)

With this bridge, the child-frame composition can
feed `InteriorGlueCap`'s cap at the root, *provided* the child-frame family is
built from the **parent's** flux-corrected field rather than the child's own
(the child-frame family uses the child's own
antisymmetric increment, which is a different — equally valid — shift of the same
equation).  That re-basing, the analogous transport of the coarse-grained
ellipticity factors `λ_{r,q}`, `Λ_{r,q}`, and the energy-average transport are
the remaining assembly steps; none of them is assumed here.

## References

* CoarseGraining, `Homogenization/CoarseGraining/Translation.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ}

/-! ## 1. The adjoint commutes with the translation -/

/-- Transposition and translation of a coefficient field commute. -/
theorem adjointCoeffField_translateCoeffField (w : Vec d) (g : CoeffField d) :
    adjointCoeffField (translateCoeffField w g) =
      translateCoeffField w (adjointCoeffField g) := rfl

/-! ## 2. The set-level doubled response is translation covariant -/

/-- **The doubled response of a translated set.**  Both halves move by
CoarseGraining's `ResponseJ_translateSet_eq_translateCoeffField`; the adjoint
half needs the commutation of §1. -/
theorem setDoubledResponseJ_translateSet (w : Vec d) (V : Set (Vec d))
    (g : CoeffField d) (P Q : BlockVec d) :
    setDoubledResponseJ (translateSet w V) g P Q =
      setDoubledResponseJ V (translateCoeffField w g) P Q := by
  rw [setDoubledResponseJ, setDoubledResponseJ,
    ResponseJ_translateSet_eq_translateCoeffField,
    ResponseJ_translateSet_eq_translateCoeffField,
    adjointCoeffField_translateCoeffField]

/-! ## 3. The one-cube quantity -/

variable [NeZero d]

omit [NeZero d] in
/-- **The off-grid one-cube maximum is CoarseGraining's, in the translated frame.** -/
theorem offGridBlockResponseValueSet_eq_translate (w : Vec d) (R : TriadicCube d)
    (A : Ch02.TriadicCoeffFamily d) (g : CoeffField d)
    (hg : (A.coeffOn R).toCoeffField = translateCoeffField w g) (a0 : Mat d) :
    offGridBlockResponseValueSet w R g a0 =
      Ch02.normalizedBlockResponseValueSet R A a0 := by
  ext m
  rw [offGridBlockResponseValueSet, Ch02.normalizedBlockResponseValueSet]
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, he, ?_⟩
    rw [offGridCube, setDoubledResponseJ_translateSet,
      setDoubledResponseJ_openCubeSet R A _ hg]
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, he, ?_⟩
    rw [offGridCube, setDoubledResponseJ_translateSet,
      setDoubledResponseJ_openCubeSet R A _ hg]

omit [NeZero d] in
theorem offGridBlockResponseMax_eq_translate (w : Vec d) (R : TriadicCube d)
    (A : Ch02.TriadicCoeffFamily d) (g : CoeffField d)
    (hg : (A.coeffOn R).toCoeffField = translateCoeffField w g) (a0 : Mat d) :
    offGridBlockResponseMax w R g a0 = Ch02.normalizedBlockResponseMax R A a0 := by
  rw [offGridBlockResponseMax, Ch02.normalizedBlockResponseMax,
    offGridBlockResponseValueSet_eq_translate w R A g hg]

/-! ## 4. The shells and the multiscale error -/

omit [NeZero d] in
theorem offGridShellMax_eq_translate (w : Vec d) (P : TriadicCube d) (k : ℤ)
    (A : Ch02.TriadicCoeffFamily d) (g : CoeffField d)
    (hg : ∀ Q : TriadicCube d, (A.coeffOn Q).toCoeffField = translateCoeffField w g)
    (a0 : Mat d) :
    offGridShellMax w P k g a0 =
      Ch02.maxDescendantNormalizedBlockResponseAtScale P k A a0 := by
  rw [offGridShellMax, Ch02.maxDescendantNormalizedBlockResponseAtScale]
  refine congrArg (Ch02.finsetSupReal (descendantsAtScale P k)) ?_
  funext R
  exact offGridBlockResponseMax_eq_translate w R A g (hg R) a0

omit [NeZero d] in
/-- **The frame bridge.**

The multiscale error of the *off-grid* cube `w + P`, taken with the ambient
field `g`, equals CoarseGraining's cube error of `P` taken with the
*translated* field `g(· + w)`. -/
theorem offGridErrorFunctional_eq_homogenizationErrorOnCube_translate (w : Vec d)
    (P : TriadicCube d) {t : ℝ} (ht : 0 < t) (A : Ch02.TriadicCoeffFamily d)
    (g : CoeffField d)
    (hg : ∀ Q : TriadicCube d, (A.coeffOn Q).toCoeffField = translateCoeffField w g)
    (a0 : Mat d) :
    offGridErrorFunctional w P t g a0 =
      Ch02.HomogenizationErrorOnCube P t .infinity (.finite 2) A a0 := by
  have hshell : ∀ l : ℕ, offGridShellMax w P (P.scale - (l : ℤ)) g a0 =
      Ch02.maxDescendantNormalizedBlockResponseAtScale P (P.scale - (l : ℤ)) A a0 :=
    fun l => offGridShellMax_eq_translate w P _ A g hg a0
  have hsum : (∑' l : ℕ, Ch02.geometricWeight t 2 l *
      offGridShellMax w P (P.scale - (l : ℤ)) g a0) =
      Ch02.HomogenizationErrorOnCube P t .infinity (.finite 2) A a0 ^ 2 := by
    rw [Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum P ht A a0]
    exact tsum_congr fun l => by rw [hshell l]
  rw [offGridErrorFunctional, hsum]
  exact Real.sqrt_sq (homogenizationErrorOnCube_infinity_two_nonneg P A a0 ht)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
