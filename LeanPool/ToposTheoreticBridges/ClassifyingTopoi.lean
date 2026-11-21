/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntax
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Semantics
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.CatSemantics
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.TypeSemantics
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.InverseImage
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Morleyization
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Homomorphisms
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.ClassifyingSite
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.NormalForm
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.NormalFormSemantics
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Bridges
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Diaconescu
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Quotients
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Horn
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Fiber
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.HornStructure
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Presheaf
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Generic
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Extension
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.NatTrans
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Universal
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Definability
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.SyntacticSite
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Transport
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.QuotientTransport
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Substitution
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Provability
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Unconditional
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Examples.PresheafType
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Examples.ObjectClassifier
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Examples.Torsors
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Examples.Interval
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Examples.FinitelyPresentable
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Examples.Homogeneous

/-!
# Classifying topoi of geometric theories

Layer 1 of the roadmap: geometric logic and its semantics.

* `LeanPool.ClassifyingTopoi.GeometricFormula`, `Sequent`, `GeometricTheory`: the syntax of
  geometric logic over a first-order language of Mathlib;
* `LeanPool.ClassifyingTopoi.GeometricFormula.realize_hom`: homomorphisms of structures preserve
  geometric formulas;
* `LeanPool.ClassifyingTopoi.CatStructure.interp`: the interpretation of geometric formulas as
  subobjects in a category with finite limits, images and coproducts;
* `LeanPool.ClassifyingTopoi.CatStructure.isModel_ofStructure_iff`: in the category `Type u`, the
  categorical semantics is the set-theoretic one;
* `LeanPool.ClassifyingTopoi.CatStructure.IsModel.map`: the inverse image of a geometric morphism
  between sheaf topoi maps models to models;
* `LeanPool.ClassifyingTopoi.exists_morleyization`: every first-order theory has a coherent
  Morleyization with the same models in sets.

Layer 2 of the roadmap: classifying topoi.

* `LeanPool.ClassifyingTopoi.IsClassifyingSite`: the universal property of a classifying site;
  `LeanPool.ClassifyingTopoi.MoritaEquivalent`: Morita equivalence of geometric theories;
* `LeanPool.ClassifyingTopoi.GeometricFormula.exists_interp_eq_iSup_exs`: in every sheaf topos,
  a geometric formula is interpreted as a disjunction of existential quantifications of Horn
  formulas;
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_equivalence`: two classifying sites of
  the same theory have equivalent topoi of sheaves;
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_orderIso_quotients`: bridges between
  Morita-equivalent theories, an order isomorphism between their quotients, assuming the
  correspondence between quotients and finer topologies (roadmap 2.5) on the classifying sites;
* `LeanPool.ClassifyingTopoi.exists_iso_sheafify_comp_iff`,
  `LeanPool.ClassifyingTopoi.nonempty_iso_of_yoneda_comp_iso`: the localisation and uniqueness
  halves of Diaconescu's theorem;
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_quotient_topology` (roadmap 2.5): every
  quotient of `T` is classified by a topology finer than `J`, with the sheafified generic model;
  the converse `IsClassifyingSite.exists_quotient_theory_of_definable` and the bridges theorem
  `IsClassifyingSite.exists_orderIso_quotients'` assume the definability of sieves
  (`SievesDefinable`).

Layer 2, unconditional results (`LeanPool.ClassifyingTopoi.Syntactic`,
`LeanPool.ClassifyingTopoi.Unconditional`), in the universe `max u₁ u₂ u` of the language and of
the theory's disjunctions:

* `LeanPool.ClassifyingTopoi.Syntactic.HornCat.isClassifyingSite_hornCat`: the presheaf topos on
  the Horn category of `L` (Horn formulas in context, tuples of terms) classifies the empty
  theory; this is the existence half of Diaconescu's theorem for this site, through the points
  of the site given by the fibers of a structure (Mathlib's `GrothendieckTopology.Point`);
* `LeanPool.ClassifyingTopoi.exists_isClassifyingSite` (roadmap 2.3): every geometric theory has
  a classifying site, the Horn category with the topology classifying the theory as a quotient of
  the empty theory;
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_interp_eq_of_subobject` (roadmap 2.4): in
  a classifying topos every subobject of a power of the generic model is definable; on the Horn
  sites the covering sieves are definable (`Syntactic.HornCat.sievesDefinable_genericModel`);
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.exists_quotient_theory` (converse of roadmap 2.5)
  and `IsClassifyingSite.hasQuotientTopologies_of_univ`, for every classifying site;
* `LeanPool.ClassifyingTopoi.MoritaEquivalent.exists_orderIso_quotients`: bridges between
  Morita-equivalent theories without hypothesis; `moritaEquivalent_refl`.

Geometric sequent calculus (`LeanPool.ClassifyingTopoi.GeometricTheory.Provable`) is sound for
models in sheaf topoi (`GeometricTheory.Provable.sound`, using the substitution lemma
`CatStructure.interp_subst`), and the generic model of a classifying site satisfies exactly the
sequents valid in all models (`IsClassifyingSite.interp_le_iff`).

The classifying site constructed is the Horn category with a quotient topology, not the geometric
syntactic category of the theory (formulas in context and provably functional relations); the
two have equivalent topoi of sheaves. Not formalised: the syntactic category and its topology,
and the completeness of geometric sequent calculus (a sequent valid in the generic model is
provable).

Layer 3 of the roadmap: theories of presheaf type (the modules
`LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Examples.*`).

* `LeanPool.ClassifyingTopoi.isOfPresheafType_of_isHorn` (roadmap 3.1): Horn theories are of
  presheaf type, classified by the presheaves on their Horn category
  (`Syntactic.HornTheoryCat`), through the comparison lemma for the functor from the Horn category
  of the language, whose induced topology is the topology classifying the theory;
* `LeanPool.ClassifyingTopoi.isClassifyingSite_genericObject` (roadmap 3.2): the functors from
  finite sets to sets classify objects, with the inclusion as generic object;
* `LeanPool.ClassifyingTopoi.isModel_genericTorsor` and
  `LeanPool.ClassifyingTopoi.moritaEquivalent_torsorTheory_of_mulEquiv` (roadmap 3.3, partial):
  the generic torsor is a torsor, and isomorphic groups have Morita-equivalent theories of
  torsors;
* `LeanPool.ClassifyingTopoi.isModel_genericInterval` (roadmap 3.4, partial): the standard
  `1`-simplex is an interval in simplicial sets;
* the definitions of roadmap 3.5 (`GeometricFormula.IsIrreducible`, `SetModel`, `FPModel`,
  `SetModel.IsPresentedBy`, `irreducibleFormulaObjects`) and, for roadmap 3.6,
  `LeanPool.ClassifyingTopoi.isSetModel_iff_isIrreducibleObject`: a finitely presentable model is
  a model of a quotient whose models are the homogeneous ones iff it is irreducible.

Not formalised in layer 3: the classification of torsors by `SingleObj G` and the converse of
the Morita equivalence (roadmap 3.3), the classification of intervals by simplicial sets
(roadmap 3.4), and the theorems of roadmap 3.5 and the existence of quotients of 3.6, which need
the existence half of Diaconescu's theorem beyond the Horn sites and the identification of the
finitely presentable models with the irreducible objects of the classifying topos.

The translation of geometric formulas into infinitary logic `L_{∞ω}` (roadmap 1.2, `toInf` and
`realize_toInf`) is not formalised, since it is not available in Mathlib.
-/
