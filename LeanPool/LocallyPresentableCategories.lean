/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.LocallyPresentableCategories.Basic
public import LeanPool.LocallyPresentableCategories.Reflective
public import LeanPool.LocallyPresentableCategories.AdjointFunctor
public import LeanPool.LocallyPresentableCategories.Ind
public import LeanPool.LocallyPresentableCategories.Orthogonality
public import LeanPool.LocallyPresentableCategories.Models
public import LeanPool.LocallyPresentableCategories.GabrielUlmer
public import LeanPool.LocallyPresentableCategories.Theory
public import LeanPool.LocallyPresentableCategories.Restrict
public import LeanPool.LocallyPresentableCategories.InitialAlgebra
public import LeanPool.LocallyPresentableCategories.Generation

/-!
# Locally presentable categories and Gabriel–Ulmer duality

Source: doi:10.1017/CBO9780511600579, url:https://github.com/TauCetiProject/TauCetiRoadmap/pull/1926
Authors: Michel Hua
Status: verified
Main declarations:
  `LeanPool.LocallyPresentableCategories.hasLimitsOfSize_of_isCardinalLocallyPresentable`,
  `LeanPool.LocallyPresentableCategories.isCardinalLocallyPresentable_iff_exists_reflective`,
  `LeanPool.LocallyPresentableCategories.isRightAdjoint_iff`,
  `LeanPool.LocallyPresentableCategories.isLeftAdjoint_iff`,
  `LeanPool.LocallyPresentableCategories.isFinitelyAccessibleCategory_iff_exists_ind`,
  `LeanPool.LocallyPresentableCategories.isCardinalLocallyPresentable_iff_exists_isLocal`,
  `LeanPool.LocallyPresentableCategories.isCardinalLocallyPresentable_iff_exists_models`,
  `LeanPool.LocallyPresentableCategories.nonempty_isCardinalPresentable_models_equivalence`,
  `LeanPool.LocallyPresentableCategories.exists_iso_restrict`
Tags: locally-presentable, accessible-categories, gabriel-ulmer-duality, algebraic-theories
MSC: 18C35, 18C10, 18A40
-/

/-!
## Overview

Root module of the formalisation of the roadmap *Locally presentable categories* (proposed to
Tau Ceti in TauCetiProject/TauCetiRoadmap#1926, not merged), on Mathlib's carriers
(`IsCardinalPresentable`, `IsCardinalLocallyPresentable`, `IsLocallyPresentable`,
`IsCardinalAccessibleCategory`, `MorphismProperty.isLocal`, `Ind`). Target numbers such as 1.2
refer to that roadmap.

* `Basic`: `κ`-small limits (roadmap 0.1).
* `Reflective`: completeness (1.1) and reflective subcategories of presheaf categories (1.2).
* `AdjointFunctor`: accessible and complete (1.3), the adjoint functor theorems (1.4).
* `Ind`: finitely accessible categories are the categories `Ind A` (1.5).
* `Orthogonality`, `Models`: models of limit theories, algebras of finite-product theories and
  models of `D`-limit theories form locally presentable categories (3.1, 4.1, 4.2, 5.1).
* `GabrielUlmer`: Gabriel–Ulmer duality on objects (3.2) and small-orthogonality classes (2.1).
* `Theory`: the theory is recovered from its `κ`-presentable models (3.3).
* `Restrict`: algebraic functors are the `κ`-accessible right adjoints (3.4).
* `InitialAlgebra`: the colimit of the initial chain is an initial algebra (4.4, first part).
* `Generation`: generation under `D`-limits is detected by fully faithful `D`-functors (5.5).

Not formalised: roadmap 1.6, 1.7, 1.8, 4.3, the transfinite part of 4.4, 5.2 and 5.3.

## References

* J. Adámek, J. Rosický, *Locally presentable and accessible categories*, London Math. Soc.
  Lecture Note Ser. 189, Cambridge University Press, 1994.
* P. Gabriel, F. Ulmer, *Lokal präsentierbare Kategorien*, Lecture Notes in Math. 221, Springer,
  1971.
* G. M. Kelly, *Basic concepts of enriched category theory*, London Math. Soc. Lecture Note
  Ser. 64, Cambridge University Press, 1982; Repr. Theory Appl. Categ. 10 (2005).
* S. Lack, J. Rosický, « Notions of Lawvere theory », Appl. Categ. Structures 19 (2011), 363–391;
  arXiv:0810.2578.
* J. Adámek, « Free algebras and automata realizations in the language of categories », Comment.
  Math. Univ. Carolin. 15 (1974), 589–602.
-/
