/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityCompactExhaustion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityInteriorCutoff
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Ginibre transition analytic local regularity compact exhaustion

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularityOpenSet_contains_compact`,
`ginibreLocalRegularityExhaustionCutoff_one`,
`ginibreLocalRegularityExhaustionCutoff_fderiv_zero`.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

local instance ginibreLocalRegularityCF_locallyCompact (n : ℕ) :
    LocallyCompactSpace {z : Configuration n // CollisionFree z} :=
  (isOpen_collisionFree n).locallyCompactSpace

/-- A chosen compact exhaustion of the locally compact space of collision-free
configurations. -/
def ginibreLocalRegularityCFCompactExhaustion (n : ℕ) :
    CompactExhaustion {z : Configuration n // CollisionFree z} := CompactExhaustion.choice _

/-- The `j`-th compact set of `ginibreLocalRegularityCFCompactExhaustion n`, as a set of
configurations. -/
def ginibreLocalRegularityCompactSet (n j : ℕ) : Set (Configuration n) :=
  Subtype.val '' (ginibreLocalRegularityCFCompactExhaustion n j)

/-- The interior of `ginibreLocalRegularityCompactSet n j`. -/
def ginibreLocalRegularityOpenSet (n j : ℕ) : Set (Configuration n) :=
  interior (ginibreLocalRegularityCompactSet n j)

theorem ginibreLocalRegularityCompactSet_isCompact (n j : ℕ) :
    IsCompact (ginibreLocalRegularityCompactSet n j) :=
  (ginibreLocalRegularityCFCompactExhaustion n).isCompact j |>.image continuous_subtype_val

theorem ginibreLocalRegularityCompactSet_subset (n j : ℕ) :
    ginibreLocalRegularityCompactSet n j ⊆ {z | CollisionFree z} := by
  rintro z ⟨x, hx, rfl⟩
  exact x.property

theorem ginibreLocalRegularityCompactSet_monotone (n : ℕ) :
    Monotone (ginibreLocalRegularityCompactSet n) := by
  intro i j hij
  exact image_mono ((ginibreLocalRegularityCFCompactExhaustion n).subset hij)

theorem ginibreLocalRegularityCompactSet_subset_open_succ (n j : ℕ) :
    ginibreLocalRegularityCompactSet n j ⊆ ginibreLocalRegularityOpenSet n (j+1) := by
  rintro z ⟨x, hx, rfl⟩
  exact (isOpen_collisionFree n).isOpenMap_subtype_val.image_interior_subset _
    ⟨x, (ginibreLocalRegularityCFCompactExhaustion n).subset_interior_succ j hx, rfl⟩

theorem ginibreLocalRegularityOpenSet_isOpen (n j : ℕ) :
    IsOpen (ginibreLocalRegularityOpenSet n j) := isOpen_interior

theorem ginibreLocalRegularityOpenSet_subset_compact (n j : ℕ) :
    ginibreLocalRegularityOpenSet n j ⊆ ginibreLocalRegularityCompactSet n j := interior_subset

theorem ginibreLocalRegularityOpenSet_monotone (n : ℕ) :
    Monotone (ginibreLocalRegularityOpenSet n) := by
  intro i j hij
  exact interior_mono (ginibreLocalRegularityCompactSet_monotone n hij)

theorem ginibreLocalRegularityOpenSet_iUnion (n : ℕ) :
    (⋃ j, ginibreLocalRegularityOpenSet n j) = {z | CollisionFree z} := by
  apply Subset.antisymm
  · exact iUnion_subset (fun j => (ginibreLocalRegularityOpenSet_subset_compact n j).trans
      (ginibreLocalRegularityCompactSet_subset n j))
  · intro z hz
    obtain ⟨j, hj⟩ := (ginibreLocalRegularityCFCompactExhaustion n).exists_mem ⟨z, hz⟩
    exact mem_iUnion.mpr ⟨j+1, ginibreLocalRegularityCompactSet_subset_open_succ n j ⟨⟨z, hz⟩, hj,
        rfl⟩⟩

theorem ginibreLocalRegularityOpenSet_contains_compact {n : ℕ}
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | CollisionFree z}) :
    ∃ j, K ⊆ ginibreLocalRegularityOpenSet n j := by
  apply hK.elim_directed_cover (ginibreLocalRegularityOpenSet n)
    (ginibreLocalRegularityOpenSet_isOpen n)
  · intro z hz
    rw [ginibreLocalRegularityOpenSet_iUnion]
    exact hs hz
  · exact (ginibreLocalRegularityOpenSet_monotone n).directed_le

/-- A chosen smooth compactly supported cutoff, supported in the collision-free set, that equals
`1` near every point of `ginibreLocalRegularityCompactSet n j`. -/
def ginibreLocalRegularityExhaustionCutoff (n : ℕ) (hn : 0 < n) (j : ℕ) : Configuration n → ℝ :=
  Classical.choose (ginibreLocalRegularity_exists_compact_interior_cutoff n hn
    (ginibreLocalRegularityCompactSet n j) (ginibreLocalRegularityCompactSet_isCompact n j)
    (ginibreLocalRegularityCompactSet_subset n j))

theorem ginibreLocalRegularityExhaustionCutoff_properties (n : ℕ) (hn : 0 < n) (j : ℕ) :
    ContDiff ℝ ∞ (ginibreLocalRegularityExhaustionCutoff n hn j) ∧
    HasCompactSupport (ginibreLocalRegularityExhaustionCutoff n hn j) ∧
    tsupport (ginibreLocalRegularityExhaustionCutoff n hn j) ⊆ {z | CollisionFree z} ∧
    ∀ z ∈ ginibreLocalRegularityCompactSet n j,
      ginibreLocalRegularityExhaustionCutoff n hn j =ᶠ[𝓝 z] 1 :=
  Classical.choose_spec (ginibreLocalRegularity_exists_compact_interior_cutoff n hn
    (ginibreLocalRegularityCompactSet n j) (ginibreLocalRegularityCompactSet_isCompact n j)
    (ginibreLocalRegularityCompactSet_subset n j))

theorem ginibreLocalRegularityExhaustionCutoff_one (n : ℕ) (hn : 0 < n) (j : ℕ)
    (z : Configuration n) (hz : z ∈ ginibreLocalRegularityCompactSet n j) :
    ginibreLocalRegularityExhaustionCutoff n hn j z = 1 :=
  ((ginibreLocalRegularityExhaustionCutoff_properties n hn j).2.2.2 z hz).eq_of_nhds

theorem ginibreLocalRegularityExhaustionCutoff_fderiv_zero (n : ℕ) (hn : 0 < n) (j : ℕ)
    (z : Configuration n) (hz : z ∈ ginibreLocalRegularityCompactSet n j) :
    fderiv ℝ (ginibreLocalRegularityExhaustionCutoff n hn j) z = 0 := by
  have he := ((ginibreLocalRegularityExhaustionCutoff_properties n hn j).2.2.2 z hz).fderiv_eq
    (𝕜 := ℝ)
  simpa using he

end
end GinibrePoincare
