/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Examples.FinitelyPresentable

/-!
# Quotients of a theory of presheaf type: homogeneous models (roadmap 3.6)

For a topology `J` on the opposite of the category of finitely presentable set-models of `T`, a
set-model is `J`-homogeneous (`LeanPool.ClassifyingTopoi.SetModel.IsHomogeneous`) when every
homomorphism from a finitely presentable model `c` extends along some arrow of each `J`-covering
sieve on `c`.

## Main results

* `LeanPool.ClassifyingTopoi.SetModel.isHomogeneous_iff`: a finitely presentable model is
  `J`-homogeneous exactly when it is `J`-irreducible, that is, when only the maximal sieve covers
  it. One direction pulls a covering sieve back along a homomorphism; for the other, the identity
  extends along an arrow of the sieve, which is therefore split and lies in the sieve.
* `LeanPool.ClassifyingTopoi.isSetModel_iff_isIrreducibleObject`: hence, for a quotient `T'` whose
  set-models among those of `T` are the homogeneous ones, a finitely presentable model is a model
  of `T'` exactly when it is `J`-irreducible.

## Not formalised

The existence of the quotient `T'` classified by the topology induced by `J` on a small site
equivalent to the opposite of the finitely presentable models
(`exists_quotient_isSetModel_iff_isHomogeneous`) needs the identification of the classifying
topos of a theory of presheaf type with the presheaves on its finitely presentable models
(roadmap 3.5), which is not formalised.
-/

@[expose] public section

universe u u₁ u₂

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language CategoryTheory Opposite

variable {L : Language.{u₁, u₂}}

/-- **3.6.** A set-model is `J`-homogeneous, for a topology `J` on the opposite of the finitely
presentable models, when every homomorphism from a finitely presentable model `c` lifts through
a map of each `J`-covering sieve on `c`. -/
def SetModel.IsHomogeneous {T : GeometricTheory.{u} L}
    (J : GrothendieckTopology (FPModel T)ᵒᵖ) (M : SetModel T) : Prop :=
  ∀ (c : FPModel T) (S : Sieve (Opposite.op c)), S ∈ J (Opposite.op c) →
    ∀ y : c.obj ⟶ M, ∃ (d : FPModel T) (f : c ⟶ d), S.arrows f.op ∧
      ∃ u : d.obj ⟶ M, f.hom ≫ u = y

/-- **3.6.** A finitely presentable model is homogeneous exactly when only the maximal sieve
covers it. -/
theorem SetModel.isHomogeneous_iff {T : GeometricTheory.{u} L}
    (J : GrothendieckTopology (FPModel T)ᵒᵖ) (M : FPModel T) :
    M.obj.IsHomogeneous J ↔ ∀ S : Sieve (Opposite.op M), S ∈ J (Opposite.op M) → S = ⊤ := by
  constructor
  · intro h S hS
    obtain ⟨d, f, hf, u, hu⟩ := h M S hS (𝟙 _)
    rw [← Sieve.id_mem_iff_eq_top]
    have e : (ObjectProperty.homMk u : d ⟶ M).op ≫ f.op = 𝟙 (op M) := by
      rw [← op_comp]
      exact congrArg Quiver.Hom.op (ObjectProperty.hom_ext _ hu)
    simpa [e] using S.downward_closed hf (ObjectProperty.homMk u : d ⟶ M).op
  · intro h c S hS y
    have hS' := h _ (J.pullback_stable (ObjectProperty.homMk y : c ⟶ M).op hS)
    have := (Sieve.id_mem_iff_eq_top (S := S.pullback (ObjectProperty.homMk y : c ⟶ M).op)).2 hS'
    exact ⟨M, ObjectProperty.homMk y, by simpa using this, 𝟙 _, Category.comp_id _⟩

/-- **3.6.** A finitely presentable model is a model of the quotient exactly when it is
`J`-irreducible. -/
theorem isSetModel_iff_isIrreducibleObject {T T' : GeometricTheory.{u} L}
    (J : GrothendieckTopology (FPModel T)ᵒᵖ)
    (hT' : ∀ M : SetModel T, T'.IsSetModel M.carrier ↔ M.IsHomogeneous J) (M : FPModel T) :
    T'.IsSetModel M.obj.carrier ↔
      ∀ S : Sieve (Opposite.op M), S ∈ J (Opposite.op M) → S = ⊤ :=
  (hT' M.obj).trans (SetModel.isHomogeneous_iff J M)

end LeanPool.ClassifyingTopoi
