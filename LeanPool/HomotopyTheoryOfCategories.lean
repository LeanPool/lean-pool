/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.HomotopyTheoryOfCategories.FundamentalGroupoid
public import LeanPool.HomotopyTheoryOfCategories.Fibration
public import LeanPool.HomotopyTheoryOfCategories.Localizer
public import LeanPool.HomotopyTheoryOfCategories.Presheaf
public import LeanPool.HomotopyTheoryOfCategories.Direct
public import LeanPool.HomotopyTheoryOfCategories.Nonsingular
public import LeanPool.HomotopyTheoryOfCategories.Derivator
public import LeanPool.HomotopyTheoryOfCategories.CofibrationCategory
public import LeanPool.HomotopyTheoryOfCategories.GrCategory

/-!
# Basic localizers and the homotopy theory of small categories

Source: url:https://github.com/TauCetiProject/TauCetiRoadmap/pull/1521
Authors: Michel Hua
Status: verified
Main declarations: `LeanPool.HomotopyTheoryOfCategories.Winfty_le`,
  `LeanPool.HomotopyTheoryOfCategories.isBasicLocalizer_Winfty`,
  `LeanPool.HomotopyTheoryOfCategories.isBasicLocalizer_W₀`,
  `LeanPool.HomotopyTheoryOfCategories.mem_of_isAsphericalFunctor`,
  `LeanPool.HomotopyTheoryOfCategories.mem_of_isLeftAdjoint`,
  `LeanPool.HomotopyTheoryOfCategories.mem_of_isRightAdjoint`,
  `LeanPool.HomotopyTheoryOfCategories.W₁_iff_isEquivalence`,
  `LeanPool.HomotopyTheoryOfCategories.isDirect_iff_nonempty_reedyStructure`,
  `LeanPool.HomotopyTheoryOfCategories.brown_factorization`
Tags: basic-localizers, homotopy-of-categories, quillen-theorem-a, reedy-categories, gr-categories
MSC: 55U35, 18N40, 18M05
-/

/-!
## Overview

Root module of the formalisation of the roadmap *Homotopy theory of small categories* (proposed
to Tau Ceti in TauCetiProject/TauCetiRoadmap#1521, not merged), after Grothendieck, *Pursuing
Stacks* and *Les Dérivateurs*, and Cisinski 2004. Layer and target numbers refer to that
roadmap. Its Layer 0 (idempotent adjunctions, additive functors on a Karoubi envelope, Beck's
theorem as a characterization) is already in the pool, in `CategoryTheoryToolkit`, and is not
repeated here. It imports:

* `FundamentalGroupoid`, `Fibration`: Layer 1 (`W₀`, `W₁`, fibrations of groupoids and their
  exact sequence);
* `Localizer`: Layer 2 (basic localizers, `W∞`, `W₀`, `W₋₁`, Theorem A, adjoints);
* `Presheaf`: Layers 3.1–3.2 and 6.1 (`i_A ⊣ i_A^*`, presheaf weak equivalences, the
  definitions of test categories);
* `Direct`: Layers 7–8 (direct and inverse categories and Reedy structures);
* `Nonsingular`: Layer 9 (non-singular presheaves, discrete fibrations);
* `Derivator`: Layer 10.1–10.2 (definitions);
* `CofibrationCategory`: Layer 11 (Brown's factorization lemma);
* `GrCategory`: Layer 12 (gr-categories, `π₀` and `π₁` of two-term complexes).

Not formalised: 4.3 (homology localizers), 4.4 and 4.6 (`W∞` and locally constant functors,
`W₁` as a basic localizer), 5.1 (Dwyer maps and pushouts in `Cat`), 6.4 (`Δ` is a strict test
category), and the rest of Layers 3–6, 10 and 12–13 beyond the statements listed above.

## References

* D.-C. Cisinski, « Le localisateur fondamental minimal », Cahiers Top. Géom. Diff. Catég. 45
  (2004), 109–140.
* D.-C. Cisinski, *Les préfaisceaux comme modèles des types d'homotopie*, Astérisque 308 (2006).
* G. Maltsiniotis, « La catégorie cubique avec connexions est une catégorie test stricte »,
  Homology Homotopy Appl. 11 (2009), 309–326.
* A. Grothendieck, *Pursuing Stacks*, arXiv:2111.01000.
* P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*, Springer, 1967.
* R. Brown, P. R. Heath, K. H. Kamps, « Groupoids and the Mayer–Vietoris sequence », J. Pure
  Appl. Algebra 30 (1983), 109–129.
* E. Riehl, D. Verity, « The theory and practice of Reedy categories », Theory Appl. Categ. 29
  (2014), 256–301.
* M. Groth, « Derivators, pointed derivators and stable derivators », Algebr. Geom. Topol. 13
  (2013), 313–374.
* K. S. Brown, « Abstract homotopy theory and generalized sheaf cohomology », Trans. AMS 186
  (1973), 419–458.
* P. Deligne, « La formule de dualité globale », SGA 4 III, Exposé XVIII, LNM 305 (1973).
-/
