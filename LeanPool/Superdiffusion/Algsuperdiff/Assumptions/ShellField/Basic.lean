/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Assumptions.ShellFieldBorelMeasurableSpace
public import LeanPool.HighContrastHomogenization.Support.Probability.RegCoeffField.Endomorphisms
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Basic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Basic A for regular shell fields

This module equips the exact frozen shell-field carrier with its
compact-open topology and Borel measurable space.  It also
exposes the value and first- and second-derivative data, derives the exact
`C^2` regularity, proves that values determine a shell, and gives the
measurable forgetful map into CoarseGraining's `RegCoeffField`.
-/

namespace Algsuperdiff.Frozen.Assumptions

open HCPolySupport MeasureTheory Topology
open scoped Matrix.Norms.Elementwise

noncomputable section

/-- The ambient compact-open triple underlying the frozen shell carrier. -/
abbrev ShellAmbient (d : ℕ) :=
  C(Vec d, Mat d) ×
    (C(Vec d, Vec d →L[ℝ] Mat d) ×
      C(Vec d, Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)))

instance shellFieldNormedAddCommGroup (d : ℕ) :
    NormedAddCommGroup (Vec d →L[ℝ] Mat d) :=
  ContinuousLinearMap.toNormedAddCommGroup

instance shellFieldNormedSpace (d : ℕ) :
    NormedSpace ℝ (Vec d →L[ℝ] Mat d) :=
  ContinuousLinearMap.toNormedSpace

noncomputable instance shellFieldTopologicalSpace (d : ℕ) :
    TopologicalSpace (ShellField d) :=
  shellFieldCompactOpenTopology d

noncomputable instance shellFieldMeasurableSpace (d : ℕ) :
    MeasurableSpace (ShellField d) :=
  shellFieldBorelMeasurableSpace d

instance shellFieldBorelSpace (d : ℕ) : BorelSpace (ShellField d) :=
  ⟨rfl⟩

namespace ShellField

variable {d : ℕ}

instance instCoeFunShellField : CoeFun (ShellField d) (fun _ ↦ Vec d → Mat d) :=
  ⟨fun j ↦ j.1.1⟩

/-- The continuous first derivative stored in the exact frozen carrier. -/
def deriv (j : ShellField d) : C(Vec d, Vec d →L[ℝ] Mat d) :=
  j.1.2.1

/-- The continuous second derivative stored in the exact frozen carrier. -/
def secondDeriv (j : ShellField d) :
    C(Vec d, Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  j.1.2.2

theorem hasFDerivAt (j : ShellField d) (x : Vec d) :
    HasFDerivAt j (deriv j x) x :=
  j.2.1 x

theorem deriv_hasFDerivAt (j : ShellField d) (x : Vec d) :
    HasFDerivAt (deriv j) (secondDeriv j x) x :=
  j.2.2.1 x

/-- The stored first derivative is continuously differentiable. -/
theorem contDiff_deriv (j : ShellField d) :
    ContDiff ℝ 1 (deriv j) :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨secondDeriv j, (secondDeriv j).continuous, j.deriv_hasFDerivAt⟩

/-- A frozen shell field is genuinely `C^2`, with no added regularity
hypothesis. -/
theorem contDiff_two (j : ShellField d) :
    ContDiff ℝ 2 j := by
  exact (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
    ⟨deriv j, j.contDiff_deriv, j.hasFDerivAt⟩

theorem skew_entry (j : ShellField d) (x : Vec d) (i k : Fin d) :
    j x i k = -j x k i :=
  j.2.2.2 x i k

theorem skew (j : ShellField d) (x : Vec d) :
    matTranspose (j x) = -j x := by
  ext i k
  exact j.skew_entry x k i

/-- A derivative compatible with the same value field is unique. -/
theorem deriv_unique (j : ShellField d) {x : Vec d} {D : Vec d →L[ℝ] Mat d}
    (hD : HasFDerivAt j D x) :
    D = deriv j x :=
  hD.unique (j.hasFDerivAt x)

/-- A second derivative compatible with the stored first derivative is
unique. -/
theorem secondDeriv_unique (j : ShellField d) {x : Vec d}
    {D : Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)}
    (hD : HasFDerivAt (deriv j) D x) :
    D = secondDeriv j x :=
  hD.unique (j.deriv_hasFDerivAt x)

/-- Shell values determine the entire regular-version datum, including both
stored derivatives. -/
@[ext]
theorem ext {j k : ShellField d} (h : ∀ x, j x = k x) : j = k := by
  have hval : j.1.1 = k.1.1 := ContinuousMap.ext h
  have hfirst : j.1.2.1 = k.1.2.1 := by
    apply ContinuousMap.ext
    intro x
    apply k.deriv_unique
    simpa only [hval] using! j.hasFDerivAt x
  have hsecond : j.1.2.2 = k.1.2.2 := by
    apply ContinuousMap.ext
    intro x
    apply k.secondDeriv_unique
    simpa only [deriv, hfirst] using! j.deriv_hasFDerivAt x
  apply Subtype.ext
  exact Prod.ext hval (Prod.ext hfirst hsecond)

/-- Forget the shell packaging while retaining the literal matrix values. -/
def forgetShell (j : ShellField d) : RegCoeffField d where
  toFun := j
  entry_measurable := fun i k ↦
    ((continuous_apply k).comp
      ((continuous_apply i).comp j.1.1.continuous)).measurable
  entry_locInt := fun i k ↦
    ((continuous_apply k).comp
      ((continuous_apply i).comp j.1.1.continuous)).locallyIntegrable

@[simp]
theorem forgetShell_apply (j : ShellField d) (x : Vec d) :
    forgetShell j x = j x :=
  rfl

/-- Evaluation at a fixed point is continuous in the compact-open topology. -/
theorem continuous_eval (x : Vec d) :
    Continuous (fun j : ShellField d ↦ j x) :=
  (continuous_eval_const x).comp continuous_subtype_val.fst

theorem measurable_eval (x : Vec d) :
    Measurable (fun j : ShellField d ↦ j x) :=
  (continuous_eval x).measurable

theorem measurable_eval_entry (x : Vec d) (i k : Fin d) :
    Measurable (fun j : ShellField d ↦ j x i k) :=
  ((continuous_apply k).comp
    ((continuous_apply i).comp (continuous_eval x))).measurable

/-- Evaluation of the stored first derivative at a fixed point is continuous
in the compact-open topology. -/
theorem continuous_eval_deriv (x : Vec d) :
    Continuous (fun j : ShellField d ↦ deriv j x) :=
  (continuous_eval_const x).comp continuous_subtype_val.snd.fst

/-- Evaluation of the stored second derivative at a fixed point is continuous
in the compact-open topology. -/
theorem continuous_eval_secondDeriv (x : Vec d) :
    Continuous (fun j : ShellField d ↦ secondDeriv j x) :=
  (continuous_eval_const x).comp continuous_subtype_val.snd.snd

private theorem measurable_forgetShell_entryTest (i k : Fin d)
    (phi : Vec d → ℝ) (hphi : IsProbeR phi) :
    Measurable (fun j : ShellField d ↦ entryTestR i k phi (forgetShell j)) := by
  let F : ShellField d × Vec d → ℝ :=
    fun q ↦ q.1 q.2 i k * phi q.2
  have hFcont : Continuous (fun q : ShellField d × Vec d ↦ q.1 q.2 i k) := by
    have hval : Continuous (fun q : ShellField d × Vec d ↦ q.1 q.2) :=
      ContinuousEval.continuous_eval.comp
        (((continuous_subtype_val.comp continuous_fst).fst).prodMk continuous_snd)
    exact (continuous_apply k).comp ((continuous_apply i).comp hval)
  have hFmeas : Measurable F :=
    hFcont.measurable.mul (hphi.measurable.comp measurable_snd)
  have hInt : StronglyMeasurable
      (fun j : ShellField d ↦ ∫ x, F (j, x) ∂volume) :=
    hFmeas.stronglyMeasurable.integral_prod_right'
  have hEq : (fun j : ShellField d ↦ ∫ x, F (j, x) ∂volume) =
      fun j ↦ entryTestR i k phi (forgetShell j) := by
    funext j
    rfl
  rw [← hEq]
  exact hInt.measurable

/-- The forgetful map is measurable for CoarseGraining's full regular-field
sigma-field, including the compactly supported integral generators. -/
theorem measurable_forgetShell :
    Measurable (forgetShell (d := d)) := by
  refine measurable_into_regCoeffField' ?_ ?_
  · intro x i k
    exact measurable_eval_entry x i k
  · intro i k phi hphi
    exact measurable_forgetShell_entryTest i k phi hphi

end ShellField

end

end Algsuperdiff.Frozen.Assumptions
