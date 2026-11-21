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

The translation of geometric formulas into infinitary logic `L_{∞ω}` (roadmap 1.2, `toInf` and
`realize_toInf`) is not formalised, since it is not available in Mathlib.
-/
