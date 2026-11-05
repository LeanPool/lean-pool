/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.Actions
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.Topology.Algebra.MulAction

/-!
# TranslationAction

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Real translation action on shell-value paths

The manuscript uses the real translation convention `(τ_z f)(x) = f(x + z)`.
This module proves that it is a jointly continuous additive action on the
compact-open carrier `C(Vec d, Mat d)`, the carrier of the stationary
zero-shell law used by J4.
-/

namespace Algsuperdiff.Frozen.Assumptions.ShellField

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-- The Borel sigma-field of the compact-open shell-value path space. -/
noncomputable instance valuePathMeasurableSpace (d : ℕ) :
    MeasurableSpace C(Vec d, Mat d) :=
  borel C(Vec d, Mat d)

instance valuePathBorelSpace (d : ℕ) : BorelSpace C(Vec d, Mat d) :=
  ⟨rfl⟩

/-- The value component of a regular shell field, viewed as a compact-open
continuous matrix-valued path.  This is the canonical carrier of the
zero-shell law used in J1 and J4. -/
def valuePath (j : ShellField d) : C(Vec d, Mat d) :=
  j.1.1

theorem continuous_valuePath : Continuous (valuePath (d := d)) :=
  continuous_subtype_val.fst

theorem measurable_valuePath : Measurable (valuePath (d := d)) :=
  continuous_valuePath.measurable

/-- The continuous map `x ↦ x + z` used to express a real translation. -/
def translationMap (z : Vec d) : C(Vec d, Vec d) :=
  ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩

private theorem continuous_translationMap :
    Continuous (fun z : Vec d ↦ translationMap z) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun q : Vec d × Vec d ↦ q.2 + q.1)
  exact continuous_snd.add continuous_fst

private theorem continuous_precompose_translation {E : Type*} [TopologicalSpace E]
    [LocallyCompactPair (Vec d) E] :
    Continuous (fun q : Vec d × C(Vec d, E) ↦ q.2.comp (translationMap q.1)) := by
  exact continuous_snd.compCM (continuous_translationMap.comp continuous_fst)

/-! ## Value-path translations -/

/-- Real translation of a shell-value path in the manuscript convention
`f(x) ↦ f(x + z)`. -/
def translateValue (z : Vec d) (f : C(Vec d, Mat d)) : C(Vec d, Mat d) :=
  f.comp (translationMap z)

@[simp]
theorem translateValue_apply (z : Vec d) (f : C(Vec d, Mat d)) (x : Vec d) :
    translateValue z f x = f (x + z) :=
  rfl

/-- Joint continuity in the shift and the compact-open value path. -/
theorem continuous_translateValue_joint :
    Continuous (fun q : Vec d × C(Vec d, Mat d) ↦ translateValue q.1 q.2) := by
  exact continuous_precompose_translation (d := d) (E := Mat d)

@[simp]
theorem translateValue_zero (f : C(Vec d, Mat d)) :
    translateValue 0 f = f := by
  apply ContinuousMap.ext
  intro x
  simp only [translateValue_apply, add_zero]

@[simp]
theorem translateValue_add (z w : Vec d) (f : C(Vec d, Mat d)) :
    translateValue (z + w) f = translateValue z (translateValue w f) := by
  apply ContinuousMap.ext
  intro x
  simp only [translateValue_apply, add_assoc]

/-- The real translations of value paths, in the manuscript convention
`z +ᵥ f = f(· + z)`. -/
noncomputable instance valuePathAddAction : AddAction (Vec d) (C(Vec d, Mat d)) where
  vadd := translateValue
  zero_vadd := translateValue_zero
  add_vadd := translateValue_add

@[simp]
theorem vadd_apply (z : Vec d) (f : C(Vec d, Mat d)) (x : Vec d) :
    (z +ᵥ f) x = f (x + z) :=
  translateValue_apply z f x

/-- The joint continuity statement expressed through the additive action. -/
theorem continuous_vadd_joint :
    Continuous (fun q : Vec d × C(Vec d, Mat d) ↦ q.1 +ᵥ q.2) :=
  continuous_translateValue_joint

/-- The orbit of a fixed value path is continuous in the translation vector. -/
theorem continuous_vadd_const (f : C(Vec d, Mat d)) :
    Continuous (fun z : Vec d ↦ z +ᵥ f) :=
  continuous_vadd_joint.comp (continuous_id.prodMk continuous_const)

/-- Translation by a fixed vector is continuous on value paths. -/
theorem continuous_const_vadd (z : Vec d) :
    Continuous (fun f : C(Vec d, Mat d) ↦ z +ᵥ f) :=
  continuous_vadd_joint.comp (continuous_const.prodMk continuous_id)

noncomputable instance valuePathContinuousVAdd : ContinuousVAdd (Vec d) (C(Vec d, Mat d)) :=
  ⟨continuous_vadd_joint⟩

/-- Joint measurability of the real translation action. -/
theorem measurable_vadd_joint :
    Measurable (Function.uncurry (· +ᵥ ·) :
      Vec d × C(Vec d, Mat d) → C(Vec d, Mat d)) :=
  continuous_vadd_joint.measurable

noncomputable instance valuePathMeasurableVAdd : MeasurableVAdd (Vec d) (C(Vec d, Mat d)) where
  measurable_const_vadd := fun z ↦ (continuous_const_vadd z).measurable
  measurable_vadd_const := fun f ↦ (continuous_vadd_const f).measurable

noncomputable instance valuePathMeasurableVAdd₂ : MeasurableVAdd₂ (Vec d) (C(Vec d, Mat d)) :=
  ⟨measurable_vadd_joint⟩

/-! ## Projection compatibility -/

@[simp]
theorem valuePath_translate (z : Vec d) (j : ShellField d) :
    valuePath (translate z j) = translateValue z (valuePath j) := by
  apply ContinuousMap.ext
  intro x
  rfl

theorem valuePath_negate_apply (j : ShellField d) (x : Vec d) :
    valuePath (negate j) x = -valuePath j x := by
  exact negate_apply j x

@[simp]
theorem valuePath_negate (j : ShellField d) :
    valuePath (negate j) = -valuePath j := by
  apply ContinuousMap.ext
  intro x
  exact valuePath_negate_apply j x

/-! ## Local sigma-fields on the canonical value-path carrier -/

end

end Algsuperdiff.Frozen.Assumptions.ShellField
