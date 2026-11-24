/-
Copyright (c) 2026 Mike Lady. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Lady
-/

-- Modified for Lean Pool.

module

public import LeanPool.TetrahedronPacking.RecordDensity

/-!
# Chen–Engel–Glotzer periodic tetrahedron packing

Source: arxiv:1001.0586v3, doi:10.1007/s00454-010-9273-0, url:https://github.com/michaellady/tetrahedron-packing-lean/tree/2049dec1e3eba85d9621f04a5fa76131946549c5
Authors: Mike Lady
Status: verified
Main declarations: `PackingCertificate.packing_density`,
  `TetrahedronPacking.periodic_convex_density`
Tags: discrete-geometry, lattice-packing, convex-geometry, exact-certificates
MSC: 52C17, 52C07, 68V15
-/

@[expose] public section

/-!
# The Chen–Engel–Glotzer regular tetrahedron packing

Coordinates are from Definition 2 and Theorem 1, equations (15)–(16),
of arXiv:1001.0586v3. All lengths are scaled by 160.
-/

namespace PackingCertificate

open Filter MeasureTheory Set TetrahedronPacking
open scoped BigOperators Pointwise Topology

/-- The four published tetrahedra in integer coordinates, at scale 160. -/
def motifVertex : Fin 4 → Fin 4 → Fin 3 → ℤ := TetrahedronPacking.recordVertex

/-- The primitive periods corresponding to the paper's a+b, b+c and c+a, at scale 160. -/
def periodVector : Fin 3 → Fin 3 → ℤ := TetrahedronPacking.recordPeriod

/-- Cartesian shift indexed by the three integer lattice coordinates. -/
def periodShift (k : Fin 3 → ℤ) (r : Fin 3) : ℝ :=
  ∑ j : Fin 3, (k j : ℝ) * (periodVector j r : ℝ)

/-- One translated tetrahedron in the periodic packing. -/
def piece (p : Fin 4 × (Fin 3 → ℤ)) : Set (Fin 3 → ℝ) :=
  convexHull ℝ (range fun a => (fun r => (motifVertex p.1 a r : ℝ)) + periodShift p.2)

/-- The motif has a common positive squared length for every edge.
The pieces have disjoint interiors and cover a fraction tending to
`4000/4671` in expanding, origin-centered coordinate cubes. -/
theorem packing_density :
    (∀ i a b : Fin 4, a ≠ b →
      ∑ r : Fin 3, ((motifVertex i a r : ℝ) - (motifVertex i b r : ℝ)) ^ 2 = 460800) ∧
    (Pairwise fun p q => Disjoint (interior (piece p)) (interior (piece q))) ∧
    Tendsto (fun R : ℝ =>
      volume.real ((⋃ p, piece p) ∩ Metric.closedBall 0 R) /
        volume.real (Metric.closedBall (0 : Fin 3 → ℝ) R))
      atTop (𝓝 (4000 / 4671 : ℝ)) := by
  classical
  have hs (k : Fin 3 → ℤ) :
      periodShift k = recordRealShift k := by
    ext r
    simp [periodShift, periodVector, recordRealShift, recordCoordinates_symm_apply, mul_comm]
  have hp (p : Fin 4 × (Fin 3 → ℤ)) : piece p = periodShift p.2 +ᵥ recordHull p.1 := by
    rw [recordHull_translate]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · exact record_squared_edge_lengths
  · simpa only [hp, hs] using record_pairwise_disjoint_interiors
  · let e := (Equiv.refl (Fin 4)).prodCongr recordLatticeEquiv
    have hu : (⋃ p, piece p) =
        (⋃ p : Fin 4 × recordLattice, (p.2 : Fin 3 → ℝ) +ᵥ recordHull p.1) := by
      simpa [e, hp, hs, recordLatticeEquiv_apply] using e.surjective.iUnion_comp
        (fun p => (p.2 : Fin 3 → ℝ) +ᵥ recordHull p.1)
    rw [hu]
    exact record_spatial_density

end PackingCertificate
