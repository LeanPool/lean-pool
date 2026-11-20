/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Conventions
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Assembling maps into `R3` from their three coordinates

`R3 = EuclideanSpace ℝ (Fin 3)` is a `WithLp` structure rather than a plain pi type, so
`hasDerivAt_pi` and `contDiff_pi` do not apply to it directly: a curve or a map into `R3` has to
be pushed through the continuous linear equivalence `EuclideanSpace.equiv (Fin 3) ℝ`.  This
module does that once, in the three shapes the development uses — extensionality (`r3_ext`), a
`ContDiff` statement (`contDiff_r3_of_contDiff_coords`) and a derivative (`hasDerivAt_r3`) —
together with the two coordinate projections `a ↦ (a 0, a 1)` and `a ↦ a 2` that split a point
of `ℝ³` into a chart pair and an axial coordinate.

The first two coordinates are packaged as the chart pair `ℝ × ℝ`, which is the shape the
transverse flows of `FastDynamo/Dynamics/Flow/` and `FastDynamo/Dynamics/Ideal/` produce; nothing
here refers to a flow, a velocity or a parameter.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-- Extensionality for `R3` through the three coordinates, in the form the assembly lemmas
below and the explicit lifts of `FastDynamo/Dynamics/Flow/TorusFlow.lean` need:
`EuclideanSpace` does not accept a bare `funext` and `Fin 3` has three cases. -/
theorem r3_ext {x y : R3} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) : x = y := by
  refine PiLp.ext fun j ↦ ?_
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

/-! ## Smooth maps into `R3` -/

/-- **Assembling a smooth `R3`-valued map from three smooth coordinates.**  `R3` is a `WithLp`
structure rather than a pi type, so the assembly goes through the continuous linear equivalence
`EuclideanSpace.equiv`; this is the `ContDiff` companion of `hasDerivAt_r3`
below. -/
theorem contDiff_r3_of_contDiff_coords {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v w : E → ℝ} {n : ℕ∞} (hu : ContDiff ℝ n u) (hv : ContDiff ℝ n v) (hw : ContDiff ℝ n w) :
    ContDiff ℝ n fun a ↦ (EuclideanSpace.equiv (Fin 3) ℝ).symm ![u a, v a, w a] := by
  refine (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp ?_
  rw [contDiff_pi]
  intro j
  fin_cases j
  · simpa using hu
  · simpa using hv
  · simpa using hw

/-- The transverse coordinate pair of a point of `ℝ³` depends smoothly on the point. -/
theorem contDiff_r3Pair {n : ℕ∞} : ContDiff ℝ n fun a : R3 ↦ (a 0, a 1) :=
  ContDiff.prodMk (contDiff_piLp_apply 2 (i := (0 : Fin 3)))
    (contDiff_piLp_apply 2 (i := (1 : Fin 3)))

/-- The axial coordinate of a point of `ℝ³` depends smoothly on the point. -/
theorem contDiff_r3Axial {n : ℕ∞} : ContDiff ℝ n fun a : R3 ↦ a 2 :=
  contDiff_piLp_apply 2 (i := (2 : Fin 3))

/-- **Assembling a curve in `R3` from its three coordinates.**  `R3 = EuclideanSpace ℝ (Fin 3)`
is a `WithLp` structure rather than a plain pi type, so `hasDerivAt_pi` does not apply to it; the
curve is pushed through the continuous linear equivalence `EuclideanSpace.equiv (Fin 3) ℝ`
instead.  The first two coordinates are packaged as a curve in the chart `ℝ × ℝ`, which is the
shape the transverse flow produces. -/
theorem hasDerivAt_r3 {f : ℝ → ℝ × ℝ} {g : ℝ → ℝ} {u : ℝ × ℝ} {d : ℝ} {w : R3} {t : ℝ}
    (hf : HasDerivAt f u t) (hg : HasDerivAt g d t)
    (h0 : w 0 = u.1) (h1 : w 1 = u.2) (h2 : w 2 = d) :
    HasDerivAt
      (fun s : ℝ ↦ (EuclideanSpace.equiv (Fin 3) ℝ).symm ![(f s).1, (f s).2, g s]) w t := by
  have hf1 : HasDerivAt (fun s : ℝ ↦ (f s).1) u.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hf
  have hf2 : HasDerivAt (fun s : ℝ ↦ (f s).2) u.2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hf
  have hpi : HasDerivAt (fun s : ℝ ↦ (![(f s).1, (f s).2, g s] : Fin 3 → ℝ))
      (![u.1, u.2, d] : Fin 3 → ℝ) t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hf1
    · exact hf2
    · exact hg
  have hcomp := ((EuclideanSpace.equiv (Fin 3) ℝ).symm :
    (Fin 3 → ℝ) →L[ℝ] R3).hasFDerivAt.comp_hasDerivAt t hpi
  have hw : ((EuclideanSpace.equiv (Fin 3) ℝ).symm : (Fin 3 → ℝ) →L[ℝ] R3)
      (![u.1, u.2, d] : Fin 3 → ℝ) = w := r3_ext h0.symm h1.symm h2.symm
  rw [hw] at hcomp
  exact hcomp

end

end FastDynamo
