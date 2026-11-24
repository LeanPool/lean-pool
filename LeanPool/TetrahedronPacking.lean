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

open Filter MeasureTheory Set
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
  have hv : motifVertex = TetrahedronPacking.recordVertex := rfl
  have hp : periodVector = TetrahedronPacking.recordPeriod := rfl
  have hvertex (i a : Fin 4) :
      (fun r => (motifVertex i a r : ℝ)) = TetrahedronPacking.recordRealVertex i a := by
    rw [hv]
    rfl
  have hs (k : Fin 3 → ℤ) :
      periodShift k = TetrahedronPacking.recordCoordinates.symm (fun r => (k r : ℝ)) := by
    ext r
    simp [periodShift, hp, TetrahedronPacking.recordCoordinates_symm_apply, mul_comm]
  have he (p : Fin 4 × (Fin 3 → ℤ)) :
      piece p = convexHull ℝ (range fun a =>
        TetrahedronPacking.recordRealVertex p.1 a +
          TetrahedronPacking.recordCoordinates.symm (fun r => (p.2 r : ℝ))) := by
    simp only [piece, hvertex, hs]
  refine ⟨?_, ?_, ?_⟩
  · intro i a b h
    simpa only [hv, TetrahedronPacking.recordRealVertex] using
      TetrahedronPacking.record_squared_edge_lengths i a b h
  · simpa only [he] using TetrahedronPacking.record_pairwise_disjoint_interiors
  · let b := (Pi.basisFun ℝ (Fin 3)).map TetrahedronPacking.recordCoordinates.symm
    let L := Submodule.span ℤ (range b)
    let s (i : Fin 4) := convexHull ℝ (range (TetrahedronPacking.recordRealVertex i))
    have hcoord (p : Fin 3 → ℝ) :
        p ∈ L ↔ ∃ k : Fin 3 → ℤ, periodShift k = p := by
      constructor
      · intro hin
        choose k hk using (b.mem_span_iff_repr_mem ℤ _).mp hin
        refine ⟨k, ?_⟩
        rw [hs]
        apply TetrahedronPacking.recordCoordinates.injective
        ext r
        have hr := (hk r).symm
        change (Pi.basisFun ℝ (Fin 3)).repr (TetrahedronPacking.recordCoordinates p) r =
          (k r : ℝ) at hr
        simpa using hr.symm
      · rintro ⟨k, rfl⟩
        change periodShift k ∈ Submodule.span ℤ (range b)
        rw [b.mem_span_iff_repr_mem ℤ]
        intro r
        refine ⟨k r, ?_⟩
        simp [b, hs]
    have hpiece (i : Fin 4) (k : Fin 3 → ℤ) : piece (i, k) = periodShift k +ᵥ s i := by
      change _ = periodShift k +ᵥ convexHull ℝ (range (TetrahedronPacking.recordRealVertex i))
      rw [← convexHull_vadd, piece]
      congr 1
      change range (fun a => (fun r => (motifVertex i a r : ℝ)) + periodShift k) =
        (fun y : Fin 3 → ℝ => periodShift k + y) '' range (TetrahedronPacking.recordRealVertex i)
      rw [← range_comp]
      simp only [hvertex, Function.comp_def, add_comm]
    have hu : (⋃ p, piece p) =
        (⋃ p : Fin 4 × L, (p.2 : Fin 3 → ℝ) +ᵥ s p.1) := by
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨⟨i,k⟩, hx⟩
        exact ⟨⟨i, ⟨periodShift k, (hcoord _).2 ⟨k, rfl⟩⟩⟩, hpiece i k ▸ hx⟩
      · rintro ⟨⟨i,p⟩, hx⟩
        obtain ⟨k,hk⟩ := (hcoord _).1 p.property
        refine ⟨(i,k), ?_⟩
        rw [hpiece, hk]
        exact hx
    rw [hu]
    exact TetrahedronPacking.record_spatial_density

end PackingCertificate
