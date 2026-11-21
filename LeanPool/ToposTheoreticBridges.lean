/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.Morita
public import LeanPool.ToposTheoreticBridges.Boolean
public import LeanPool.ToposTheoreticBridges.DeMorgan
public import LeanPool.ToposTheoreticBridges.Sites
public import LeanPool.ToposTheoreticBridges.Subtopos
public import LeanPool.ToposTheoreticBridges.EssentialPoints

/-!
# Topos-theoretic bridges for presheaf topoi

Source: arxiv:1006.3930
Authors: Michel Hua
Status: verified
Main declarations: `LeanPool.ToposTheoreticBridges.moritaEquivalentCat_iff_karoubi`,
  `LeanPool.ToposTheoreticBridges.isBooleanTopos_presheaf_iff_isGroupoid`,
  `LeanPool.ToposTheoreticBridges.isDeMorganTopos_presheaf_iff_rightOreCondition`,
  `LeanPool.ToposTheoreticBridges.exists_orderIso_ici_of_sheafEquiv`,
  `LeanPool.ToposTheoreticBridges.subtoposOrderIso`,
  `LeanPool.ToposTheoreticBridges.essentialPointEquivKaroubiOp`
Tags: topos-theory, morita-equivalence, karoubi-envelope, presheaf-topoi
MSC: 18F10, 18B25, 18E50
-/

/-!
## Overview

Morita equivalence of small categories, read through their presheaf topoi, and two invariants of
presheaf topoi with their characterisations on the site:

* `LeanPool.ToposTheoreticBridges.moritaEquivalentCat_iff_karoubi`: two small categories have
  equivalent presheaf topoi exactly when their Karoubi envelopes are equivalent;
* `LeanPool.ToposTheoreticBridges.isBooleanTopos_presheaf_iff_isGroupoid`: the presheaf topos of
  `C` is Boolean exactly when `C` is a groupoid;
* `LeanPool.ToposTheoreticBridges.isDeMorganTopos_presheaf_iff_rightOreCondition`: it is
  De Morgan exactly when `C` satisfies the right Ore condition;
* `LeanPool.ToposTheoreticBridges.exists_orderIso_ici_of_sheafEquiv`: an equivalence of the sheaf
  topoi of two small sites gives an order isomorphism between the topologies finer than the two
  given ones, under which the sheaf conditions correspond;
* `LeanPool.ToposTheoreticBridges.subtoposOrderIso`: the subtopoi of `Sheaf J (Type u)` correspond
  to the topologies finer than `J`, by an order isomorphism reversing the order;
* `LeanPool.ToposTheoreticBridges.essentialPointEquivKaroubiOp`: the essential points of the
  presheaf topos of `C` form a category equivalent to `(Karoubi C)ᵒᵖ`;
* the Morita invariance of being a groupoid and of the right Ore condition.

These are « bridges » in O. Caramello's sense: an invariant of the topos, read on two
presentations, gives an equivalence of properties of the presentations. The card's source,
Caramello's *The unification of Mathematics via Topos Theory* (arXiv:1006.3930), is background
for this method; each file cites the sources of its own results (for instance SGA 4 IV,
Exercise 7.6(c,e), for the essential points, and Johnstone's *Elephant*, Example D4.6.3(a), for De
Morgan presheaf topoi).
-/
