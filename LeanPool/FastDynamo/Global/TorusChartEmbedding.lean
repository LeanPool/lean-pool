/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusCellPlacement
public import LeanPool.FastDynamo.Analysis.TransverseChart
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# The Euclidean placement chart inside the transverse torus

`TransverseTorus` is the coordinatewise quotient `(ℝ / ℤ)²`, and
`FastDynamo/Analysis/TransverseChart.lean` supplies the quotient map
`transverseTorusPoint : ℝ × ℝ → TransverseTorus`, which sends a point of the
Euclidean placement chart `placementChart = (0,1/4) × (1/4,3/4)` (the right half of the paper's
coordinate square of §3.3, which contains every buffer disc) to its two quotient coordinates.
Since that chart lies in `(0,1)²`, the standard `AddCircle` representative theorem
proves that the map is injective there.  This is enough to transport the placed
buffer and core discs into the actual transverse torus as pairwise-disjoint
image sets.

The module intentionally makes no metric identification claim for the
quotient torus: the API supplies exactly the representative equality
certificate needed for support placement.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Set

/-- The quotient map has unique representatives on the placement chart. -/
theorem transverseTorusPoint_injectiveOn_placementChart :
    Set.InjOn transverseTorusPoint ScaleFamily.placementChart := by
  intro x hx y hy hxy
  have hx1 : x.1 ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨hx.1.1.le, hx.1.2.trans_le (by norm_num)⟩
  have hy1 : y.1 ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨hy.1.1.le, hy.1.2.trans_le (by norm_num)⟩
  have hx2 : x.2 ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨by linarith [hx.2.1], hx.2.2.trans_le (by norm_num)⟩
  have hy2 : y.2 ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨by linarith [hy.2.1], hy.2.2.trans_le (by norm_num)⟩
  apply Prod.ext
  · exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
      (by simpa using hx1) (by simpa using hy1)).mp
      (congrFun hxy 0)
  · exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
      (by simpa using hx2) (by simpa using hy2)).mp
      (congrFun hxy 1)

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p} {supportRadius : ℝ}

/-- The actual transverse-torus image of one Euclidean buffer disc. -/
def torusBufferDisk (P : TorusCellPlacement (r := r) supportRadius)
    (n : ℕ) : Set TransverseTorus :=
  transverseTorusPoint '' P.scaleFamily.bufferDisk n

/-- The actual transverse-torus image of one local-flow core disc. -/
def torusLocalCoreDisk (P : TorusCellPlacement (r := r) supportRadius)
    (n : ℕ) : Set TransverseTorus :=
  transverseTorusPoint '' P.scaleFamily.localCoreDisk supportRadius n

/-- Pairwise disjoint Euclidean buffers remain pairwise disjoint after their
coordinatewise quotient into the transverse torus. -/
theorem disjoint_torusBufferDisk
    (P : TorusCellPlacement (r := r) supportRadius)
    {n m : ℕ} (hnm : n < m) :
    Disjoint (P.torusBufferDisk n) (P.torusBufferDisk m) := by
  rw [Set.disjoint_left]
  intro q hq_n hq_m
  obtain ⟨x, hx, hxq⟩ := hq_n
  obtain ⟨y, hy, hyq⟩ := hq_m
  have hxy_torus : transverseTorusPoint x = transverseTorusPoint y :=
    hxq.trans hyq.symm
  have hxchart : x ∈ placementChart := P.bufferDisk_subset_chart n hx
  have hychart : y ∈ placementChart := P.bufferDisk_subset_chart m hy
  have hxy : x = y :=
    transverseTorusPoint_injectiveOn_placementChart hxchart hychart hxy_torus
  exact (Set.disjoint_left.mp (P.disjoint_bufferDisk hnm)) hx (hxy ▸ hy)

/-- Every local-flow core image is contained in its actual torus buffer
image. -/
theorem torusLocalCoreDisk_subset_torusBufferDisk
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    P.torusLocalCoreDisk n ⊆ P.torusBufferDisk n :=
  Set.image_mono (P.localCoreDisk_subset_bufferDisk n)

/-- Matching a physical diffusivity selects a core and buffer whose torus
images have the certified placement relation. -/
theorem exists_matchingCell_with_torusPlacedCore
    (P : TorusCellPlacement (r := r) supportRadius) {epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hupper : epsilon ≤ P.scaleFamily.epsilon0) :
    ∃ c : MatchingCell P.scaleFamily epsilon,
      P.torusLocalCoreDisk c.index ⊆ P.torusBufferDisk c.index := by
  obtain ⟨c, -, -⟩ := P.exists_matchingCell_with_placedCore hepsilon hupper
  exact ⟨c, P.torusLocalCoreDisk_subset_torusBufferDisk c.index⟩

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
