/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.GrothendieckInfinityGroupoids.Basic
public import LeanPool.GrothendieckInfinityGroupoids.GlobularSum
public import LeanPool.GrothendieckInfinityGroupoids.Extension
public import LeanPool.GrothendieckInfinityGroupoids.Homotopy
public import LeanPool.GrothendieckInfinityGroupoids.Topological

/-!
# Grothendieck ∞-groupoids, globular sums and the degree-zero comparison

Source: arxiv:1206.2941
Authors: Michel Hua
Status: verified
Main declarations: `LeanPool.GrothendieckInfinityGroupoids.GlobularSums.nonempty_of_hasPushouts`,
  `LeanPool.GrothendieckInfinityGroupoids.PseudoCoherator.exists_inverse`,
  `LeanPool.GrothendieckInfinityGroupoids.PseudoCoherator.exists_comp`,
  `LeanPool.GrothendieckInfinityGroupoids.PseudoCoherator.cellJoined_equivalence`,
  `LeanPool.GrothendieckInfinityGroupoids.PseudoCoherator.IsWeakEquivalence.comp`,
  `LeanPool.GrothendieckInfinityGroupoids.isGlobularPresheaf_piPresheaf`,
  `LeanPool.GrothendieckInfinityGroupoids.cellJoined_zero_piPresheaf_iff`,
  `LeanPool.GrothendieckInfinityGroupoids.bijectiveOnComponents_piPresheaf_iff`
Tags: infinity-groupoids, globular-sets, coherators, homotopy-hypothesis
MSC: 18N65, 55U35, 18N50
-/

/-!
## Overview

Root module of the formalisation of the roadmap *Grothendieck ∞-groupoids: globular theories,
coherators and their models*. This project develops the same author's prototype in
`Suggested.lean` from the unmerged proposal TauCetiProject/TauCetiRoadmap#1060, after D. Ara,
« On the homotopy theory of Grothendieck ∞-groupoids », J. Pure Appl.
Algebra 217 (2013), 1237–1278, arXiv:1206.2941, with Maltsiniotis' form of the definitions of
*Pursuing Stacks*. Target numbers such as 3.2 refer to that roadmap.

* `Basic`: the globe category and globular sets (0.1), coglobular objects, the coglobular space of
  disks and hemisphere inclusions, and tables of dimensions (1.1).
* `GlobularSum`: globular sums, and their existence in every category with pushouts (1.2).
* `Extension`: globular extensions and globular functors (2.1), admissible pairs, contractibility
  and pseudo-coherators (2.2), and ∞-groupoids of type `C` with the terminal and representable
  examples (3.1).
* `Homotopy`: identities, inverses and composites from liftings (3.2); the homotopy relation is an
  equivalence relation on the cells of an ∞-groupoid of type `C` (4.1); weak equivalences, the
  identities and composites of weak equivalences, and a presheaf with two components (4.3).
* `Topological`: given a globular functor `R` from a pseudo-coherator `C` into the disks,
  `Π_∞^R` is an ∞-groupoid of type `C` (5.2). Its `0`-cells modulo homotopy are the path
  components of the space (5.3, `π₀` part), so `Π_∞^R f`
  is a bijection on `π₀` exactly when `f` is a bijection on path components (5.4, `π₀` part).

The explicit globular sets `GlobularSet` (0.1) and the class
`PseudoCoherator.weakEquivalences` are defined here. Topological weak homotopy equivalence
is available from Tau Ceti as `ContinuousMap.IsWeakHomotopyEquivalence`.

Not formalised:

* 0.1, the equivalence between globular presheaves and explicit globular sets; 0.2, spheres and
  disks of globular sets; 1.3, the category `Θ₀`; 2.1, `Θ₀` as the initial globular extension;
* 2.2, the contractibility of `TopCat` with the disks, which needs the contractibility of the
  globular sums of disks (Ara 2013, Examples 2.7.1, Proposition 5.11);
* 2.3–2.5, free extensions `C[A]`, cellular towers, coherators and globular functors out of a
  free globular extension (Ara 2013, 2.9–2.14);
* 3.2 beyond existence: the operations as chosen maps and the pregroupoidal structures;
* 4.1, the groupoids `ϖ_n` and the groups `π_n`; 4.2, their independence of choices; 4.3, Ara's
  Theorem 4.18 and two-out-of-three in full;
* 5.1, globular functors into `TopCat`; 5.3, the isomorphisms `π_n(Π_∞^R X, x) ≅ π_n(X, x)`
  (Ara 2013, Theorem 8.7) for `n ≥ 1`; 5.4, Corollaries 8.9–8.11 beyond `π₀`;
* 6.1, cellular ∞-groupoids; 7.1, the functor `Hot ⥤ Ho(∞-Gpd_C)`; 7.2, the independence of the
  homotopy invariants from `R`.

## References

* D. Ara, « On the homotopy theory of Grothendieck ∞-groupoids », J. Pure Appl. Algebra 217
  (2013), no. 7, 1237–1278; arXiv:1206.2941.
* G. Maltsiniotis, « Grothendieck ∞-groupoids, and still another definition of ∞-categories »,
  arXiv:1009.2331 (2010).
* A. Grothendieck, *Pursuing Stacks (À la poursuite des champs)*, vol. I, ed. G. Maltsiniotis,
  Documents Mathématiques 20, SMF, 2022; arXiv:2111.01000.
-/
