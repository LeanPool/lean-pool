/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PosetHomotopy.FiniteSpace.Fence
public import LeanPool.PosetHomotopy.FiniteSpace.BeatPoint
public import LeanPool.PosetHomotopy.FiniteSpace.Core
public import LeanPool.PosetHomotopy.OrderComplex.Prism
public import LeanPool.PosetHomotopy.OrderComplex.EulerChar
public import LeanPool.PosetHomotopy.OrderComplex.FixedPoints
public import LeanPool.PosetHomotopy.SubgroupComplex.Basic
public import LeanPool.PosetHomotopy.SubgroupComplex.Brown

/-!
# Homotopy of finite spaces, posets and subgroup complexes

Source: doi:10.1016/0001-8708(78)90058-0
Authors: Michel Hua
Status: verified
Main declarations: `LeanPool.PosetHomotopy.homotopic_iff_eqvGen`,
  `LeanPool.PosetHomotopy.exists_retraction_of_isBeatPoint`,
  `LeanPool.PosetHomotopy.exists_homeomorph_of_homotopyEquiv`,
  `LeanPool.PosetHomotopy.exists_fixedPoint_of_contractibleSpace`,
  `LeanPool.PosetHomotopy.homotopic_realizationMap_of_le`,
  `LeanPool.PosetHomotopy.contractibleSpace_of_conical`,
  `LeanPool.PosetHomotopy.chainEulerChar_modEq_of_fixedPoints`,
  `LeanPool.PosetHomotopy.contractibleSpace_of_normal`,
  `LeanPool.PosetHomotopy.contractibleSpace_withUpperSet_iff`,
  `LeanPool.PosetHomotopy.eulerChar_pSubgroupPoset_modEq`
Tags: finite-spaces, poset-homotopy, order-complexes, subgroup-complexes, euler-characteristic
MSC: 06A07, 55P10, 20D30, 55U10
-/

/-!
## Overview

Root module of the formalisation of the roadmap *Homotopy of posets, finite spaces and subgroup
complexes* (proposed to Tau Ceti in TauCetiProject/TauCetiRoadmap#2296, not merged), on Mathlib's
specialization order and upper-set topology and on Tau Ceti's order complexes and their weak
realizations. Target numbers such as 1.3 refer to that roadmap.

* `FiniteSpace.Fence`: continuity from specialization (1.1); homotopies between finite spaces are
  fences of pointwise comparable maps (1.2).
* `FiniteSpace.BeatPoint`: beat points and strong deformation retracts (1.3).
* `FiniteSpace.Core`: Stong's classification (1.4); invariant cores and fixed points (1.5).
* `OrderComplex.Prism`: the prism homotopy between the realizations of comparable monotone maps
  (3.2) and conical contractibility (3.3).
* `OrderComplex.EulerChar`: the alternating count of nonempty chains in a finite poset, its
  invariance under removing an up beat point, and its value in the presence of a least element
  or a closure operator (3.5).
* `OrderComplex.FixedPoints`: the congruence for a group action whose nontrivial subgroups fix
  subposets of Euler characteristic `1` (3.5).
* `SubgroupComplex.Basic`: the posets `S_p(G)` and `A_p(G)` and conjugation on `S_p(G)` (4.1).
  A nontrivial normal `p`-subgroup gives contractibility of the realization of `S_p(G)` (4.3),
  using Mathlib's elementwise `IsPGroup`. Stong's finite-space form concerns the upper-set
  topology (4.4).
* `SubgroupComplex.Brown`: Brown's congruence for the alternating chain count (4.7).

Not formalised:

* 2.1–2.3, McCord's theorems (weak homotopy equivalences from basis-like covers, from the
  realization of the order complex of a finite space, and from a simplicial complex to its face
  poset);
* 3.1, the homeomorphism between the realization of the order complex and that of the nerve;
* 3.4, Quillen's fibre lemma: part (a) needs Quillen's Theorem A for realized nerves, which
  neither Mathlib nor Tau Ceti has at the pinned versions, and part (b) needs the basic localizers
  of HomotopyTheoryOfCategories, which projects of the pool do not import;
* 4.1 (b) and (c), the conical structure of `A_p(P)` for a `p`-group and the dimension of
  `A_p(G)`; 4.2, the Brown–Quillen homotopy equivalence, which needs 3.4;
* 4.5, Quillen's connectivity criterion, which needs 2.2; 4.6, Quillen's theorem for solvable
  groups, which needs the homology of `A_p(G)`;
* the identification of `chainEulerChar` with the Euler characteristic of the realization. The
  congruences in 3.5 and 4.7 are stated and proved for the alternating count of nonempty chains.

## References

* D. Quillen, « Homotopy properties of the poset of nontrivial p-subgroups of a group », Adv.
  Math. 28 (1978), no. 2, 101–128.
* K. S. Brown, « Euler characteristics of groups: the p-fractional part », Invent. Math. 29
  (1975), 1–5.
* R. E. Stong, « Finite topological spaces », Trans. Amer. Math. Soc. 123 (1966), 325–340.
* R. E. Stong, « Group actions on finite spaces », Discrete Math. 49 (1984), 95–100.
* J. A. Barmak, *Algebraic Topology of Finite Topological Spaces and Applications*, Lecture Notes
  in Math. 2032, Springer, 2011.
* E. G. Minian, K. I. Piterman, « The homotopy types of the posets of p-subgroups of a finite
  group », Adv. Math. 328 (2018), 1217–1233.
-/
