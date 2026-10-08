/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.GroupTheory.CoprodILemmas
public import Mathlib.GroupTheory.HNNExtension
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# The two-stage HNN model for Borisov's four-relator group

The base is the free group on `d` and `e`.  Two injective substitutions encode
the power maps

```
  alpha : d ↦ d,  e ↦ e⁴,
  beta  : d ↦ d⁴, e ↦ e.
```

The first HNN extension adjoins `s₁` along these substitutions.  The second
adjoins `s₂` along the transported copies of the same associated subgroups.
The resulting group `Gamma3`, together with `d3`, `e3`,
`firstStableInStageThree`, and `secondStableInStageThree`,
is the low-level semantic model used by the Borisov normal-form arguments.
The presentation-facing equivalence is constructed separately in
`GroupUndecidability.Borisov.Model.G0HNN`.
-/

@[expose] public section

open Function
open Monoid

namespace Undecidability.BorisovHNNModel

noncomputable section

/-! ## The rank-two free base and the two injective substitutions -/

/-- The free group on the two base generators. -/
abbrev Base := FreeGroup (Fin 2)

/-- The first free base generator `d`. -/
def d : Base := FreeGroup.of 0
/-- The second free base generator `e`. -/
def e : Base := FreeGroup.of 1

/-- The infinite-cyclic-group homomorphism multiplying an exponent by four. -/
def intFour : Multiplicative ℤ →* Multiplicative ℤ where
  toFun z := Multiplicative.ofAdd (4 * Multiplicative.toAdd z)
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp [mul_add]

private theorem intFour_injective : Injective intFour := by
  intro x y h
  apply Multiplicative.toAdd.injective
  have h' := congrArg Multiplicative.toAdd h
  simp only [intFour] at h'
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h'

/-- The injective endomorphism taking the cyclic free generator to its fourth power. -/
def cyclicFour : FreeGroup Unit →* FreeGroup Unit :=
  FreeGroup.mulEquivIntOfUnique.symm.toMonoidHom.comp
    (intFour.comp FreeGroup.mulEquivIntOfUnique.toMonoidHom)

private theorem cyclicFour_injective : Injective cyclicFour :=
  FreeGroup.mulEquivIntOfUnique.symm.injective.comp
    (intFour_injective.comp FreeGroup.mulEquivIntOfUnique.injective)

private theorem cyclicFour_generator :
    cyclicFour (FreeGroup.of ()) = FreeGroup.of () ^ 4 := by
  apply FreeGroup.mulEquivIntOfUnique.injective
  simp [cyclicFour, intFour, FreeGroup.mulEquivIntOfUnique,
    FreeGroup.equivIntOfUnique]

/-- The component substitutions fixing the first cyclic generator and powering the second. -/
def componentA : (i : Fin 2) → FreeGroup Unit →* FreeGroup Unit
  | 0 => MonoidHom.id _
  | 1 => cyclicFour

/-- The component substitutions powering the first cyclic generator and fixing the second. -/
def componentB : (i : Fin 2) → FreeGroup Unit →* FreeGroup Unit
  | 0 => cyclicFour
  | 1 => MonoidHom.id _

private theorem componentA_injective (i : Fin 2) : Injective (componentA i) := by
  fin_cases i
  · exact Function.injective_id
  · exact cyclicFour_injective

private theorem componentB_injective (i : Fin 2) : Injective (componentB i) := by
  fin_cases i
  · exact cyclicFour_injective
  · exact Function.injective_id

/-- The free-base substitution induced componentwise through the cyclic free-product representation.
-/
def freeProductSubstitution
    (f : (i : Fin 2) → FreeGroup Unit →* FreeGroup Unit) : Base →* Base :=
  freeGroupEquivCoprodI.symm.toMonoidHom.comp
    ((CoprodI.familyMap f).comp freeGroupEquivCoprodI.toMonoidHom)

/-- The injective substitution fixing `d` and taking `e` to its fourth power. -/
def alpha : Base →* Base := freeProductSubstitution componentA
/-- The injective substitution taking `d` to its fourth power and fixing `e`. -/
def beta : Base →* Base := freeProductSubstitution componentB

theorem alpha_injective : Injective alpha :=
  freeGroupEquivCoprodI.symm.injective.comp
    ((CoprodI.familyMap_injective componentA componentA_injective).comp
      freeGroupEquivCoprodI.injective)

theorem beta_injective : Injective beta :=
  freeGroupEquivCoprodI.symm.injective.comp
    ((CoprodI.familyMap_injective componentB componentB_injective).comp
      freeGroupEquivCoprodI.injective)

@[simp] theorem alpha_d : alpha d = d := by
  simp [alpha, d, freeProductSubstitution, componentA, CoprodI.familyMap]

@[simp] theorem alpha_e : alpha e = e ^ 4 := by
  simp [alpha, e, freeProductSubstitution, componentA, cyclicFour_generator,
    CoprodI.familyMap]

@[simp] theorem beta_d : beta d = d ^ 4 := by
  simp [beta, d, freeProductSubstitution, componentB, cyclicFour_generator,
    CoprodI.familyMap]

@[simp] theorem beta_e : beta e = e := by
  simp [beta, e, freeProductSubstitution, componentB, CoprodI.familyMap]

theorem alpha_eq_lift : alpha = FreeGroup.lift ![d, e ^ 4] := by
  ext i
  fin_cases i
  · simpa [d] using alpha_d
  · simpa [e] using alpha_e

theorem beta_eq_lift : beta = FreeGroup.lift ![d ^ 4, e] := by
  ext i
  fin_cases i
  · simpa [d] using beta_d
  · simpa [e] using beta_e

/-! ## The first HNN extension, adjoining `s₁` -/

/-- The image subgroup of the first injective base substitution. -/
abbrev A0 : Subgroup Base := alpha.range
/-- The image subgroup of the second injective base substitution. -/
abbrev B0 : Subgroup Base := beta.range

/-- The equivalence between the free base group and the first image subgroup. -/
noncomputable def inA0 : Base ≃* A0 := MonoidHom.ofInjective alpha_injective
/-- The equivalence between the free base group and the second image subgroup. -/
noncomputable def inB0 : Base ≃* B0 := MonoidHom.ofInjective beta_injective

/-- The isomorphism between the two associated image subgroups. -/
noncomputable def phi0 : A0 ≃* B0 :=
  inA0.symm.trans inB0

@[simp] theorem phi0_inA0 (x : Base) : phi0 (inA0 x) = inB0 x := by
  simp [phi0]

@[simp] theorem coe_inA0 (x : Base) : (inA0 x : Base) = alpha x :=
  MonoidHom.ofInjective_apply alpha_injective

@[simp] theorem coe_inB0 (x : Base) : (inB0 x : Base) = beta x :=
  MonoidHom.ofInjective_apply beta_injective

/-- The HNN extension adjoining the first stable generator. -/
abbrev Stage1 := HNNExtension Base A0 B0 phi0

/-- The inclusion of the free base into the first HNN extension. -/
def of0 : Base →* Stage1 := HNNExtension.of
/-- The first HNN stable generator. -/
def s1 : Stage1 := HNNExtension.t

theorem of0_injective : Injective of0 := HNNExtension.of_injective phi0

theorem stage1_s1_mul_d : s1 * of0 d = of0 (d ^ 4) * s1 := by
  simpa [s1, of0] using
    (HNNExtension.t_mul_of (φ := phi0) (inA0 d))

theorem stage1_s1_mul_e_four : s1 * of0 (e ^ 4) = of0 e * s1 := by
  simpa [s1, of0] using
    (HNNExtension.t_mul_of (φ := phi0) (inA0 e))

theorem stage1_d_four_mul_s1 : of0 (d ^ 4) * s1 = s1 * of0 d :=
  stage1_s1_mul_d.symm

theorem stage1_e_mul_s1 : of0 e * s1 = s1 * of0 (e ^ 4) :=
  stage1_s1_mul_e_four.symm

/-! ## The second HNN extension

This adjoins `s₂` to a transported copy of the same pair of associated
subgroups.
-/

/-- The first associated subgroup carried into the first HNN extension. -/
abbrev A1 : Subgroup Stage1 := A0.map of0
/-- The second associated subgroup carried into the first HNN extension. -/
abbrev B1 : Subgroup Stage1 := B0.map of0

/-- The equivalence onto the carried first associated subgroup. -/
noncomputable def inA1 : A0 ≃* A1 :=
  A0.equivMapOfInjective of0 of0_injective

/-- The equivalence onto the carried second associated subgroup. -/
noncomputable def inB1 : B0 ≃* B1 :=
  B0.equivMapOfInjective of0 of0_injective

/-- The associated-subgroup isomorphism transported into the first HNN extension. -/
noncomputable def phi1 : A1 ≃* B1 :=
  inA1.symm.trans (phi0.trans inB1)

@[simp] theorem phi1_inA1 (a : A0) : phi1 (inA1 a) = inB1 (phi0 a) := by
  simp [phi1]

@[simp] theorem coe_inA1 (a : A0) : (inA1 a : Stage1) = of0 a :=
  Subgroup.coe_equivMapOfInjective_apply A0 of0 of0_injective a

@[simp] theorem coe_inB1 (b : B0) : (inB1 b : Stage1) = of0 b :=
  Subgroup.coe_equivMapOfInjective_apply B0 of0 of0_injective b

/-- The HNN extension adjoining the second stable generator. -/
abbrev Gamma3 := HNNExtension Stage1 A1 B1 phi1

/-- The inclusion of the first HNN extension into the second HNN extension. -/
def of1 : Stage1 →* Gamma3 := HNNExtension.of
/-- The image of `d` after the two HNN extensions. -/
def d3 : Gamma3 := of1 (of0 d)
/-- The image of `e` after the two HNN extensions. -/
def e3 : Gamma3 := of1 (of0 e)
/-- The image of the first stable generator after adjoining the second. -/
def firstStableInStageThree : Gamma3 := of1 s1
/-- The second stable generator in the two-HNN-extension model. -/
def secondStableInStageThree : Gamma3 := HNNExtension.t

theorem of1_injective : Injective of1 := HNNExtension.of_injective phi1

theorem baseEmbedding_injective : Injective (of1.comp of0) :=
  of1_injective.comp of0_injective

theorem gamma3_d_four_mul_s1 : d3 ^ 4 * firstStableInStageThree = firstStableInStageThree * d3 := by
  simpa [d3, firstStableInStageThree, map_pow] using congrArg of1 stage1_d_four_mul_s1

theorem gamma3_e_mul_s1 : e3 * firstStableInStageThree = firstStableInStageThree * e3 ^ 4 := by
  simpa [e3, firstStableInStageThree, map_pow] using congrArg of1 stage1_e_mul_s1

theorem gamma3_s2_mul_d : secondStableInStageThree * d3 = d3 ^ 4 * secondStableInStageThree := by
  simpa [secondStableInStageThree, d3, of1] using
    (HNNExtension.t_mul_of (φ := phi1) (inA1 (inA0 d)))

theorem gamma3_s2_mul_e_four :
    secondStableInStageThree * e3 ^ 4 = e3 * secondStableInStageThree := by
  simpa [secondStableInStageThree, e3, of1, map_pow] using
    (HNNExtension.t_mul_of (φ := phi1) (inA1 (inA0 e)))

theorem gamma3_d_four_mul_s2 : d3 ^ 4 * secondStableInStageThree = secondStableInStageThree * d3 :=
  gamma3_s2_mul_d.symm

theorem gamma3_e_mul_s2 : e3 * secondStableInStageThree = secondStableInStageThree * e3 ^ 4 :=
  gamma3_s2_mul_e_four.symm

end
end Undecidability.BorisovHNNModel
