/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46LongEdges

/-!
# Central and linking edge sets in VII (4.6)

On pages 225–226, the open middle segment of each long old edge is
central. The two outer open segments are linking edges. These definitions
use the chosen cut parameters and no graph or topological conclusions.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- The central edges in VII (4.6), pages 225–226, are the open middle
parameter segments of long edges. -/
def centralEdges {S : Type*} [TopologicalSpace S] (G J : Drawing S) (μ w : ℕ)
    (γ : Set S → unitInterval → S) (s t : longSeamEdges G J μ w → unitInterval) : Set (Set S) :=
  range fun e => γ e.1 '' Ioo (s e) (t e)

/-- The linking edges in VII (4.6), page 225, are the two outer open
parameter segments of long edges. -/
def linkingEdges {S : Type*} [TopologicalSpace S] (G J : Drawing S) (μ w : ℕ)
    (γ : Set S → unitInterval → S) (s t : longSeamEdges G J μ w → unitInterval) : Set (Set S) :=
  (range fun e => γ e.1 '' Ioo 0 (s e)) ∪ (range fun e => γ e.1 '' Ioo (t e) 1)

/-- The edge set of `L` in VII (4.6), page 226, obtained by deleting the
central edges and the edges contained in the cuffs. -/
def forestSeamEdges {S : Type*} [TopologicalSpace S] (J' : Drawing S)
    (central : Set (Set S)) : Set (Set S) :=
  {e ∈ J'.E | e ∉ central ∧ ¬e ⊆ bd S}

end GraphMinor.GM07
