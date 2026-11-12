/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3723T1AllContactRouting

-- [TABLET NODE: P3861T1FacialDomains]

/-!
# P3861T1FacialDomains

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a periodic complex $P$ and an all-contact drawing
$D$ as in `P3723T1AllContactRouting`, put
$$
 \mathcal T=\{D(a):a\in\iota\}\ \cup\!
       \bigcup_{a\sim_P b}D.\mathrm{edgeArc}(a,b),\qquad
 J_f=D_{f_0f_1}\cup D_{f_1f_2}\cup D_{f_2f_0}.
$$
A facial-domain record consists of a set $U_f$ for every fixed face
label, closedness of $\mathcal T$, and the following laws: $U_f$ is
nonempty, open, connected and bounded, avoids $\mathcal T$, and has
frontier exactly $J_f$. The exterior $(\overline{U_f})^c$ is connected
and has the same frontier $J_f$. No face orientation, pairwise disjointness
between these domains, or extra-contact exclusion is part of this
record. The drawing and all three arcs are the supplied literal ones.
-/
structure P3861T1FacialDomains {ι : Type} (P : PeriodicTileComplex ι)
    (D : P3723T1AllContactRouting P) where
-- BODY
  /-- The bounded complementary region attached to each fixed face label. -/
  region : P.plane.Face → Set (Real × Real)
  trace_closed : IsClosed (Set.range D.position ∪
    {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ D.edgeArc a b})
  region_open : ∀ f, IsOpen (region f)
  region_connected : ∀ f, IsConnected (region f)
  region_bounded : ∀ f, Bornology.IsBounded (region f)
  region_avoids_trace : ∀ f, Disjoint (region f)
    (Set.range D.position ∪ {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ D.edgeArc a b})
  region_frontier : ∀ f, frontier (region f) =
    D.edgeArc (P.plane.faceVertex f 0) (P.plane.faceVertex f 1) ∪
      D.edgeArc (P.plane.faceVertex f 1) (P.plane.faceVertex f 2) ∪
      D.edgeArc (P.plane.faceVertex f 2) (P.plane.faceVertex f 0)
  exterior_connected : ∀ f, IsConnected (closure (region f))ᶜ
  exterior_frontier : ∀ f,
    frontier (closure (region f))ᶜ = frontier (region f)

end ApollonianSuperharmonic

end
