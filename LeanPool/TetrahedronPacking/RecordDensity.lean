/-
Copyright (c) 2026 Mike Lady. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Lady
-/

-- Modified for Lean Pool.

module

public import LeanPool.TetrahedronPacking.PeriodicDensity
public import LeanPool.TetrahedronPacking.RecordGeometry
public import LeanPool.TetrahedronPacking.SimplexVolume
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Tactic.NormNum

/-!
# Spatial density of the Chen–Engel–Glotzer cell

Use the four checked tetrahedra as the motif for the span of the checked
period basis over the integers. Their volume follows from the edge
determinant. The periodic density theorem divides the total motif volume
by the lattice covolume and gives the limit in ordinary coordinate cubes.
-/

@[expose] public section

namespace TetrahedronPacking

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped Pointwise Topology

/-- Covered volume fraction in expanding axis-aligned cubes for the exact
Chen–Engel–Glotzer cell. The data use a common length scale of 160. -/
theorem record_spatial_density :
    Tendsto (fun R : ℝ =>
      volume.real ((⋃ p : Fin 4 × recordLattice, (p.2 : Fin 3 → ℝ) +ᵥ recordHull p.1) ∩
        Metric.closedBall 0 R) / volume.real (Metric.closedBall (0 : Fin 3 → ℝ) R))
      atTop (𝓝 (4000 / 4671 : ℝ)) := by
  classical
  have hd : Pairwise fun p q : Fin 4 × recordLattice =>
      Disjoint (interior ((p.2 : Fin 3 → ℝ) +ᵥ recordHull p.1))
        (interior ((q.2 : Fin 3 → ℝ) +ᵥ recordHull q.1)) := by
    let e := (Equiv.refl (Fin 4)).prodCongr recordLatticeEquiv
    intro p q hpq
    simpa [e, ← recordLatticeEquiv_apply] using
      record_pairwise_disjoint_interiors (e.symm.injective.ne hpq)
  have hbounded : Bornology.IsBounded (⋃ i, recordHull i) :=
    Bornology.isBounded_iUnion.mpr fun i =>
      ((finite_range (recordRealVertex i)).isCompact_convexHull ℝ).isBounded
  obtain ⟨d, hd_bound⟩ := hbounded.exists_norm_le
  have h := periodic_convex_density recordLattice recordHull d (fun i => convex_convexHull ℝ _)
    (fun i x hx => hd_bound x (mem_iUnion.mpr ⟨i, hx⟩)) hd
  have hv (i : Fin 4) : volume.real (recordHull i) = 36864000 := by
    change volume.real (convexHull ℝ (range (recordRealVertex i))) = 36864000
    rw [tetrahedron_volume, record_edge_determinant]
    norm_num
  have hL : ZLattice.covolume recordLattice = 172191744 := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain recordLattice volume
      (ZSpan.isAddFundamentalDomain recordBasis volume)]
    exact record_period_cell_volume
  rw [hL] at h
  simp only [hv, Fin.sum_univ_four] at h
  convert h using 1
  norm_num

end TetrahedronPacking
