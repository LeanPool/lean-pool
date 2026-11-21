/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.Morita
public import LeanPool.ToposTheoreticBridges.Boolean
public import LeanPool.ToposTheoreticBridges.DeMorgan

/-!
# Topos-theoretic bridges

Morita equivalence of small categories, read through their presheaf topoi, and two invariants of
presheaf topoi with their characterisations on the site:

* `LeanPool.ToposTheoreticBridges.moritaEquivalentCat_iff_karoubi`: two small categories have
  equivalent presheaf topoi exactly when their Karoubi envelopes are equivalent;
* `LeanPool.ToposTheoreticBridges.isBooleanTopos_presheaf_iff_isGroupoid`: the presheaf topos of
  `C` is Boolean exactly when `C` is a groupoid;
* `LeanPool.ToposTheoreticBridges.isDeMorganTopos_presheaf_iff_rightOreCondition`: it is
  De Morgan exactly when `C` satisfies the right Ore condition;
* the Morita invariance of both properties, as « bridges » in O. Caramello's sense: an invariant
  of the topos, read on two presentations, gives an equivalence of properties of the
  presentations.
-/
