/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2EntryConstruction
public import LeanPool.GraphMinor.GM12.Section2SectorHomotopy
import LeanPool.GraphMinor.Surface.Disc

/-!
# Entry witnesses and replacement across a parallel disc

In XII's entry definition on page 243, a normalized approach followed
by an edge parametrization gives the required entry curve. A path
homotopy in the region with its vertex added gives the stated curve
homotopy. The second lemma replaces a chord by a parallel spoke using
the disc between them.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Convert a relative-endpoint path comparison into the exact entry
witness required by the definition in XII, page 243. -/
theorem entersLike_of_path_comparison {S : Type*} [TopologicalSpace S]
    {f : ℝ → S} {a c h : ℝ} (hh : h ∈ Ioo a c)
    {e r : Set S} {v w : S} {x y z : (r ∪ {v} : Set S)}
    (hz : z.val = w) (p : Path x y) (q : Path y z) (ρ : Path x z)
    (hp : ∀ t : unitInterval, (p t).val = f (h + t.val * (c - h)))
    (hqinj : Function.Injective (fun t => (q t).val))
    (hqe : (fun t => (q t).val) '' Ioo (0 : unitInterval) 1 = e)
    (hρ : ∀ t, (ρ t).val ∈ r) (hhom : (p.trans q).Homotopic ρ) :
    EntersLike f a c e r v w := by
  let j : (r ∪ {v} : Set S) → S := Subtype.val
  let p' := p.map (show Continuous j from continuous_subtype_val)
  let q' := q.map (show Continuous j from continuous_subtype_val)
  let ξ : Curve S := ((p.trans q).map
    (show Continuous j from continuous_subtype_val)).toContinuousMap
  let σ : Curve S := (ρ.map (show Continuous j from continuous_subtype_val)).toContinuousMap
  refine ⟨h, hh, ξ, σ, ?_, ?_, curvesHomotopicIn_of_paths_homotopic hhom⟩
  · have hentry := isEntryCurve_trans p' q' hp hqinj hqe
    dsimp only [ξ]
    rw [Path.map_trans]
    exact hz ▸ hentry
  · rintro x ⟨t, rfl⟩
    exact hρ t

/-- The disc between a chord and a radial spoke gives a homotopy in the
region with the boundary vertex added. Prefixing by an approach preserves
any entry comparison already obtained for the chord. -/
theorem entry_comparison_replace_in_disc {S : Type*} [TopologicalSpace S]
    {Z Δ : Set S} (hΔ : IsClosedDisc Δ) (hΔZ : Δ ⊆ Z)
    {a v w : Z} (p : Path a v) (q β : Path v w) (ρ : Path a w)
    (hq : ∀ t, (q t).val ∈ Δ) (hβ : ∀ t, (β t).val ∈ Δ)
    (hentry : (p.trans q).Homotopic ρ) : (p.trans β).Homotopic ρ := by
  have hparallel : β.Homotopic q :=
    paths_homotopic_in_subspace_of_patch hΔ.isSimplyConnectedSet hΔZ β q hβ hq
  exact ((Path.Homotopic.refl p).hcomp hparallel).trans hentry

end GraphMinor.GM12
