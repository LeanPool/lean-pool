/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Foundations.RelationAlgebra.Basic

/-! # Element properties for relation algebras

Reflexivity, symmetry, and transitivity are the three properties used to describe
the elements of a complex relation algebra in its atom structure.
-/

@[expose] public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra

variable {α : Type*}

/-- A reflexive element of a relation algebra. -/
class IsRelRefl [One α] [LE α] (a : α) : Prop where
  protected one_le : 1 ≤ a

/-- A symmetric element of a relation algebra. Note that this is a class version of Mathlib's
`IsSelfAdjoint`. -/
class IsRelSymm [Star α] (a : α) : Prop where
  protected star_eq : star a = a

/-- A transitive element of a relation algebra. -/
class IsRelTrans [Mul α] [LE α] (a : α) : Prop where
  protected mul_self_le : a * a ≤ a

lemma isRelRefl_iff [One α] [LE α] {a : α} : IsRelRefl a ↔ 1 ≤ a :=
  ⟨@IsRelRefl.one_le _ _ _ a, IsRelRefl.mk⟩

lemma isRelSymm_iff [Star α] {a : α} : IsRelSymm a ↔ star a = a :=
  ⟨@IsRelSymm.star_eq _ _ a, IsRelSymm.mk⟩

lemma isRelTrans_iff [Mul α] [LE α] {a : α} : IsRelTrans a ↔ a * a ≤ a :=
  ⟨@IsRelTrans.mul_self_le _ _ _ a, IsRelTrans.mk⟩

end FiniteIntegralRelationAlgebras.RelationAlgebra
