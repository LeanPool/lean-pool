/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.TwoTorsion
public import Mathlib.RingTheory.ClassGroup.ExtendedHom

import LeanPool.CCDN.ForMathlib.ClassGroupAction

/-! The group-theoretic part of quadratic class-group descent. An
involution on an elementary abelian two-group has at least the square
root of the group's cardinality in fixed points. This is applied to the
action of a field involution on two-torsion ideal classes. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped NumberField

private theorem two_torsion_card_le_involution_fixed_square
    {G : Type*} [CommGroup G] [Finite G]
    (σ : G →* G) (hσ : Function.Involutive σ) (hG : ∀ x : G, x ^ 2 = 1) :
    Nat.card G ≤ Nat.card (σ.eqLocus (MonoidHom.id G)) ^ 2 := by
  let τ : G →* G := (MonoidHom.id G) * σ
  have hker : τ.ker ≤ σ.eqLocus (MonoidHom.id G) := by
    intro x hx
    change x * σ x = 1 at hx
    change σ x = x
    apply mul_left_cancel (a := x)
    exact hx.trans (by simpa only [pow_two] using (hG x).symm)
  have hrange : τ.range ≤ σ.eqLocus (MonoidHom.id G) := by
    rintro x ⟨y, rfl⟩
    change σ (y * σ y) = y * σ y
    rw [map_mul, hσ, mul_comm]
  have hk := Nat.card_le_card_of_injective (Subgroup.inclusion hker)
    (Subgroup.inclusion_injective hker)
  have hr := Nat.card_le_card_of_injective (Subgroup.inclusion hrange)
    (Subgroup.inclusion_injective hrange)
  calc
    Nat.card G = Nat.card τ.ker * Nat.card τ.range :=
      (Subgroup.card_ker_mul_card_range τ).symm
    _ ≤ Nat.card (σ.eqLocus (MonoidHom.id G)) *
        Nat.card (σ.eqLocus (MonoidHom.id G)) := Nat.mul_le_mul hk hr
    _ = Nat.card (σ.eqLocus (MonoidHom.id G)) ^ 2 := (pow_two _).symm

variable (K : Type*) [Field K]

/-- The action of a field automorphism on two-torsion ideal classes. -/
def classGroupTwoTorsionAction (σ : K ≃+* K) :
    classGroupTwoTorsion K →* classGroupTwoTorsion K where
  toFun c := ⟨ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ) c, by
    change (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ) c.val) ^ 2 = 1
    rw [← map_pow, show c.val ^ 2 = 1 from c.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' c d := Subtype.ext (map_mul _ _ _)

private theorem classGroupTwoTorsionAction_involutive (σ : K ≃+* K)
    (hσ : Function.Involutive σ) :
    Function.Involutive (classGroupTwoTorsionAction K σ) := by
  have hσO : Function.Involutive (RingOfIntegers.mapRingEquiv σ) := by
    intro x
    exact RingOfIntegers.ext (hσ x)
  intro c
  apply Subtype.ext
  exact classGroup_mulEquiv_involutive _ hσO c

/-- Two-torsion classes fixed by the specified field automorphism. -/
def fixedClassGroupTwoTorsion (σ : K ≃+* K) : Subgroup (classGroupTwoTorsion K) :=
  (classGroupTwoTorsionAction K σ).eqLocus (MonoidHom.id _)

/-- A two-torsion class lies in the `σ`-fixed subgroup if and only if `σ` maps its underlying ideal
class to itself. -/
@[simp]
theorem mem_fixedClassGroupTwoTorsion (σ : K ≃+* K) (c : classGroupTwoTorsion K) :
    c ∈ fixedClassGroupTwoTorsion K σ ↔
      ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ) c.val = c.val :=
  Subtype.ext_iff

variable [NumberField K]

/-- For an involutive automorphism `σ` of `K`, the order of the two-torsion subgroup of the class
group is at most the square of the order of its `σ`-fixed subgroup. -/
theorem classGroupTwoTorsionCard_le_fixed_square (σ : K ≃+* K)
    (hσ : Function.Involutive σ) :
    classGroupTwoTorsionCard K ≤ Nat.card (fixedClassGroupTwoTorsion K σ) ^ 2 := by
  apply two_torsion_card_le_involution_fixed_square
    (classGroupTwoTorsionAction K σ) (classGroupTwoTorsionAction_involutive K σ hσ)
  intro c
  exact Subtype.ext c.property

end
end CCDN
