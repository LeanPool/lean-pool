/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Ambient.Basic
public import LeanPool.HighContrastHomogenization.Support.Sobolev.WeakDerivatives
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Coarse-graining support: Support.Sobolev.H1.Definitions

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport

/-!
`H¹(U)` is modeled here by explicit witnesses: a function, a candidate weak
gradient, `L²` control on both, and the integration-by-parts identity against
smooth compactly supported tests. `H¹₀(U)` adds the usual approximation package
by smooth compactly supported functions supported in `U`.
-/

/-- Square-integrability with respect to Lebesgue measure restricted to `U`. -/
abbrev MemL2On {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict U)

/-- Square-integrability on `U` of every coordinate of the supplied gradient field. -/
@[expose]
def GradMemL2On {d : ℕ} (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemL2On U (fun x => Du x i)

/-- A scalar function and weak gradient whose components are square-integrable on `U`. -/
structure H1Function {d : ℕ} (U : Set (Vec d)) where
  /-- The pointwise scalar representative of the Sobolev function. -/
  toFun : Vec d → ℝ
  /-- The pointwise weak gradient, with square-integrable coordinates on `U`. -/
  grad : Vec d → Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

instance {d : ℕ} {U : Set (Vec d)} : CoeFun (H1Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toFun

/-- Existence of an `H¹` representative on `U` equal to the given function. -/
@[expose]
def MemH1 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∃ v : H1Function U, v.toFun = u

/-- An `H¹` function approximated in value and gradient by smooth functions compactly supported
in `U`. -/
structure H10Function {d : ℕ} (U : Set (Vec d)) extends H1Function U where
  /-- The smooth compactly supported sequence converging in `H¹` on `U`. -/
  approx : ℕ → Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fun x => approx n x - toH1Function.toFun x) 2
        (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0)
  tendsto_approx_grad :
    ∀ i : Fin d,
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm
          (fun x => (fderiv ℝ (approx n) x) (basisVec i) - toH1Function.grad x i) 2
          (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0)

instance {d : ℕ} {U : Set (Vec d)} : CoeFun (H10Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toH1Function.toFun

/-- Existence of an `H¹₀` representative on `U` equal to the given function. -/
@[expose]
def MemH10 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∃ v : H10Function U, v.toH1Function.toFun = u

/-- Vanishing of the function's Lebesgue integral over `U`. -/
@[expose]
noncomputable def MeanZeroOn {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∫ x in U, u x ∂MeasureTheory.volume = 0

end HCPolySupport
