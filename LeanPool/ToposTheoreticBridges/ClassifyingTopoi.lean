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

The existence of classifying sites (roadmap 2.3, the syntactic site) and the definability of
subobjects of the generic model (2.4) are not formalised; hence neither is the converse of 2.5
without the definability hypothesis, nor the existence half of Diaconescu's theorem.

The translation of geometric formulas into infinitary logic `L_{∞ω}` (roadmap 1.2, `toInf` and
`realize_toInf`) is not formalised, since it is not available in Mathlib.
-/
