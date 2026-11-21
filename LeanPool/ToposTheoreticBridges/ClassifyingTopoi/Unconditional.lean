/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.SyntacticSite
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.QuotientTransport

/-!
# Classifying sites: the unconditional results (roadmap 2.3, 2.4, 2.5)

In the universe `max u₁ u₂ u` of the language and of the theory's disjunctions:

* `LeanPool.ClassifyingTopoi.exists_isClassifyingSite` (roadmap 2.3): every geometric theory has a
  classifying site, the Horn category of the language with the topology classifying the theory
  as a quotient of the empty theory (`LeanPool.ClassifyingTopoi.Syntactic`);
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_interp_eq_of_subobject` (roadmap 2.4): in
  a classifying topos, every subobject of a power of the generic model is the interpretation of a
  geometric formula. It holds on the Horn sites, and transfers to every classifying site along
  the equivalence of classifying topoi;
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_quotient_theory` (roadmap 2.5, converse):
  every topology finer than the topology of a classifying site classifies a quotient of the
  theory, with the sheafified generic model; together with `exists_quotient_topology`, the
  correspondence `IsClassifyingSite.HasQuotientTopologies` holds on every classifying site
  (`IsClassifyingSite.hasQuotientTopologies_of_univ`);
* `LeanPool.ClassifyingTopoi.MoritaEquivalent.exists_orderIso_quotients`: bridges between
  Morita-equivalent theories, an order isomorphism between their quotients carrying each quotient
  to a Morita-equivalent one, with no hypothesis on the classifying sites;
* `LeanPool.ClassifyingTopoi.moritaEquivalent_refl`: Morita equivalence is reflexive.

The classifying site is not the geometric syntactic category of the theory (formulas in context,
provably functional relations, syntactic topology), and no proof theory is formalised: the sites
are equivalent as far as their topoi of sheaves are concerned, by
`IsClassifyingSite.exists_equivalence`.
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits

attribute [local instance high] Sheaf.instHasColimitsOfShape

variable {L : Language.{u₁, u₂}}

/-- **Roadmap 2.3.** Every geometric theory has a classifying site, its syntactic site, in the
universe of the language and of the theory's disjunctions. -/
theorem exists_isClassifyingSite (T : GeometricTheory.{max u₁ u₂ u} L) :
    ∃ (C : Type (max u₁ u₂ u)) (_ : SmallCategory C) (J : GrothendieckTopology C)
      (U : CatStructure L (Sheaf J (Type (max u₁ u₂ u)))), IsClassifyingSite T J U :=
  ⟨Syntactic.HornCat.{u} L, inferInstance, _, _,
    Syntactic.HornCat.isClassifyingSite_genericModel.{u} L T⟩

/-- Every geometric theory is Morita-equivalent to itself. -/
theorem moritaEquivalent_refl (T : GeometricTheory.{max u₁ u₂ u} L) : MoritaEquivalent T T :=
  (Syntactic.HornCat.isClassifyingSite_genericModel.{u} L T).moritaEquivalent_refl

namespace IsClassifyingSite

variable {T : GeometricTheory.{max u₁ u₂ u} L} {C : Type (max u₁ u₂ u)} [SmallCategory C]
  {J : GrothendieckTopology C} {U : CatStructure L (Sheaf J (Type (max u₁ u₂ u)))}

/-- **Roadmap 2.4.** In a classifying topos, every subobject of a power of the generic model is
the interpretation of a geometric formula. -/
theorem exists_interp_eq_of_subobject (hU : IsClassifyingSite T J U) {n : ℕ}
    (S : Subobject (U.pow n)) : ∃ ψ : GeometricFormula.{max u₁ u₂ u} L n, U.interp ψ = S := by
  obtain ⟨e, he⟩ := (Syntactic.HornCat.isClassifyingSite_genericModel.{u} L T).exists_equivalence hU
  refine he.exists_interp_eq (fun {m} S' => ?_) S
  obtain ⟨Q, hQ⟩ := Syntactic.exists_mapSubobject_eq e.toAdjunction
    (piComparison e.functor fun _ : Fin m =>
      (Syntactic.HornCat.genericModel (quotientTopology (Syntactic.HornCat.genericSheaf.{u} L)
        T)).carrier) S'
  obtain ⟨ψ, hψ⟩ := Syntactic.HornCat.exists_interp_genericModel_eq.{u} _ Q
  exact ⟨ψ, by rw [CatStructure.interp_map, hψ, hQ]⟩

/-- **Roadmap 2.5, both directions.** On every classifying site, the quotients of the theory
correspond to the topologies finer than the classifying topology, each classifying the
corresponding quotient with the sheafified generic model. -/
theorem hasQuotientTopologies_of_univ (hU : IsClassifyingSite T J U) :
    HasQuotientTopologies T J U :=
  hU.hasQuotientTopologies_of_isClassifyingSite
    (Syntactic.HornCat.isClassifyingSite_genericModel.{u} L T)
    (Syntactic.HornCat.hasQuotientTopologies.{u} T)

/-- **Roadmap 2.5, converse.** Every topology finer than the topology of a classifying site
classifies a quotient of the theory, with the sheafified generic model. -/
theorem exists_quotient_theory {J' : GrothendieckTopology C} (hU : IsClassifyingSite T J U)
    (hJ : J ≤ J') :
    ∃ T' : GeometricTheory.{max u₁ u₂ u} L, T ⊆ T' ∧
      IsClassifyingSite T' J'
        (U.map (sheafToPresheaf J (Type (max u₁ u₂ u)) ⋙
          presheafToSheaf J' (Type (max u₁ u₂ u)))) :=
  (IsClassifyingSite.hasQuotientTopologies_of_univ.{u₁, u₂, u} hU).2 J' hJ

end IsClassifyingSite

/-- **Bridges between theories.** The quotients of two Morita-equivalent theories are order
isomorphic, by an isomorphism carrying each quotient of the first theory to a Morita-equivalent
quotient of the second. -/
theorem MoritaEquivalent.exists_orderIso_quotients {L' : Language.{u₃, u₄}}
    {T : GeometricTheory.{max u₁ u₂ u₃ u₄ u} L} {T' : GeometricTheory.{max u₁ u₂ u₃ u₄ u} L'}
    (h : MoritaEquivalent T T') :
    ∃ Ψ : T.Quotients ≃o T'.Quotients, ∀ (T₁ : T.QuotientTheory) (T₂ : T'.QuotientTheory),
      Ψ (toAntisymmetrization _ T₁) = toAntisymmetrization _ T₂ →
        MoritaEquivalent T₁.1 T₂.1 := by
  obtain ⟨C, C', _, _, J, J', U, U', hU, hU', -⟩ := id h
  exact hU.exists_orderIso_quotients hU'
    (IsClassifyingSite.hasQuotientTopologies_of_univ.{u₁, u₂, max u₃ u₄ u} hU)
    (IsClassifyingSite.hasQuotientTopologies_of_univ.{u₃, u₄, max u₁ u₂ u} hU') h

end LeanPool.ClassifyingTopoi
