/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ClassifyingTopoi.Syntax
public import LeanPool.ClassifyingTopoi.Semantics
public import LeanPool.ClassifyingTopoi.CatSemantics
public import LeanPool.ClassifyingTopoi.TypeSemantics
public import LeanPool.ClassifyingTopoi.InverseImage
public import LeanPool.ClassifyingTopoi.Morleyization
public import LeanPool.ClassifyingTopoi.Homomorphisms
public import LeanPool.ClassifyingTopoi.ClassifyingSite
public import LeanPool.ClassifyingTopoi.NormalForm
public import LeanPool.ClassifyingTopoi.NormalFormSemantics
public import LeanPool.ClassifyingTopoi.Bridges

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
  correspondence between quotients and finer topologies (roadmap 2.5) on the classifying sites.

The existence of classifying sites (roadmap 2.3, the syntactic site), the definability of
subobjects of the generic model (2.4) and the correspondence between quotients and topologies
(2.5) are not formalised.

The translation of geometric formulas into infinitary logic `L_{∞ω}` (roadmap 1.2, `toInf` and
`realize_toInf`) is not formalised, since it is not available in Mathlib.
-/
