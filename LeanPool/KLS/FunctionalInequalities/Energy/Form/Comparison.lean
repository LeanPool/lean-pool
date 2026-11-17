/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Form.Functional

/-!
# Pointwise comparison of extended energies

This module keeps comparison data at the functional level. If `lower ≤ upper` pointwise, every
finite-energy point for `upper` also has finite `lower` energy. The direction of the induced
Poincaré-constant comparison is stated later, after variance has been added.
-/

@[expose] public section

namespace FunctionalInequalities.Energy.Functional

variable {X : Type*}

/-- Pointwise order between two extended energy functionals. -/
def PointwiseLE (lower upper : Functional X) : Prop :=
  ∀ x, lower x ≤ upper x

/-- Pointwise comparison is reflexive. -/
theorem pointwiseLE_refl (energy : Functional X) : energy.PointwiseLE energy :=
  fun _ ↦ le_rfl

/-- Pointwise comparison is transitive. -/
theorem PointwiseLE.trans {first second third : Functional X}
    (h₁ : first.PointwiseLE second) (h₂ : second.PointwiseLE third) :
    first.PointwiseLE third :=
  fun x ↦ (h₁ x).trans (h₂ x)

/-- Mutual pointwise comparison identifies the two functionals. -/
theorem PointwiseLE.antisymm {left right : Functional X}
    (h₁ : left.PointwiseLE right) (h₂ : right.PointwiseLE left) : left = right :=
  Functional.ext fun x ↦ le_antisymm (h₁ x) (h₂ x)

/-- A point with finite upper energy also has finite lower energy. -/
def domainMap {lower upper : Functional X} (h : lower.PointwiseLE upper) :
    upper.domain → lower.domain :=
  fun x ↦ ⟨x.1, ne_top_of_le_ne_top x.2 (h x.1)⟩

/-- The domain map does not change the ambient point. -/
@[simp]
theorem coe_domainMap {lower upper : Functional X} (h : lower.PointwiseLE upper)
    (x : upper.domain) : (domainMap h x : X) = x.1 :=
  rfl

/-- Pointwise comparison descends to the certified finite values. -/
theorem finiteValue_domainMap_le {lower upper : Functional X}
    (h : lower.PointwiseLE upper) (x : upper.domain) :
    lower.finiteValue (domainMap h x) ≤ upper.finiteValue x := by
  exact ENNReal.coe_le_coe.mp (by simpa using h x.1)

end FunctionalInequalities.Energy.Functional
