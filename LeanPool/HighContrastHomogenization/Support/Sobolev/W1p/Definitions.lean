/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.WeakDerivatives
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Coarse-graining support: Support.Sobolev.W1p.Definitions

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport

/-!
`W^{1,p}(U)` and `W^{1,p}_0(U)` witnesses parallel the existing `H¹` encoding
but keep the exponent `p` explicit.
-/

/-- Membership in `Lᵖ` for Lebesgue measure restricted to `U`. -/
abbrev MemLpOn {d : ℕ} (U : Set (Vec d)) (p : ENNReal) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u p (MeasureTheory.volume.restrict U)

/-- Membership in `Lᵖ(U)` of every coordinate of the supplied gradient field. -/
@[expose]
def GradMemLpOn {d : ℕ} (U : Set (Vec d)) (p : ENNReal) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemLpOn U p (fun x => Du x i)

/-- A scalar function and weak gradient with value and gradient coordinates in `Lᵖ(U)`. -/
structure W1pFunction {d : ℕ} (U : Set (Vec d)) (p : ENNReal) where
  /-- The pointwise scalar representative of the Sobolev function. -/
  toFun : Vec d → ℝ
  /-- The pointwise weak gradient, with coordinates in `Lᵖ(U)`. -/
  grad : Vec d → Vec d
  memLp : MemLpOn U p toFun
  gradMemLp : GradMemLpOn U p grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

instance {d : ℕ} {U : Set (Vec d)} {p : ENNReal} :
    CoeFun (W1pFunction U p) (fun _ => Vec d → ℝ) where
  coe u := u.toFun

/-- Existence of a `W¹ᵖ` representative on `U` equal to the given function. -/
@[expose]
def MemW1p {d : ℕ} (U : Set (Vec d)) (p : ENNReal) (u : Vec d → ℝ) : Prop :=
  ∃ v : W1pFunction U p, v.toFun = u

/-- The exact supported smooth approximation data needed to upgrade a
`W1pFunction` witness to `W10pFunction`.

This is intentionally a separate zero-trace hypothesis: bounded open convexity
gives a natural smooth approximation mechanism for bare `W^{1,p}` functions,
but it does not imply compactly supported approximation inside `U` for every
Sobolev function. -/
structure W1pFunction.SupportedSmoothApproximation {d : ℕ} {U : Set (Vec d)}
    {p : ENNReal} (u : W1pFunction U p) where
  /-- The smooth sequence supported compactly in `U` and converging in value and gradient in
  `Lᵖ`. -/
  approx : ℕ → Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fun x => approx n x - u.toFun x) p
        (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0)
  tendsto_approx_grad :
    ∀ i : Fin d,
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm
          (fun x => (fderiv ℝ (approx n) x) (basisVec i) - u.grad x i) p
          (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0)

/-- Proposition-valued form of `SupportedSmoothApproximation`, useful when the
actual approximating sequence should remain hidden. -/
@[expose]
def W1pFunction.HasSupportedSmoothApproximation {d : ℕ} {U : Set (Vec d)}
    {p : ENNReal} (u : W1pFunction U p) : Prop :=
  Nonempty u.SupportedSmoothApproximation

/-- A `W¹ᵖ` function approximated in value and gradient by smooth functions compactly supported
in `U`. -/
structure W10pFunction {d : ℕ} (U : Set (Vec d)) (p : ENNReal) extends W1pFunction U p where
  /-- The smooth compactly supported sequence converging in value and gradient in `Lᵖ(U)`. -/
  approx : ℕ → Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fun x => approx n x - toW1pFunction.toFun x) p
        (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0)
  tendsto_approx_grad :
    ∀ i : Fin d,
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm
          (fun x => (fderiv ℝ (approx n) x) (basisVec i) - toW1pFunction.grad x i) p
          (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0)

instance {d : ℕ} {U : Set (Vec d)} {p : ENNReal} :
    CoeFun (W10pFunction U p) (fun _ => Vec d → ℝ) where
  coe u := u.toW1pFunction.toFun

/-- Existence of a `W¹ᵖ₀` representative on `U` equal to the given function. -/
@[expose]
def MemW10p {d : ℕ} (U : Set (Vec d)) (p : ENNReal) (u : Vec d → ℝ) : Prop :=
  ∃ v : W10pFunction U p, v.toW1pFunction.toFun = u

end HCPolySupport
