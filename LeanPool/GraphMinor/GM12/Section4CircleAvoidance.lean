/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CircleMove
public import Mathlib.Geometry.Euclidean.Sphere.SecondInter

/-!
# Choosing circle ports off finitely many lines

For the crossing drawing in XII (4.5), page 253, a new circle port
must avoid the lines through old ports and old crossing points.
A line through a point of a sphere meets that sphere in at most two
points. Every open circle arc of length less than a turn is infinite,
so finitely many such lines cannot cover it.
-/

public section

namespace GraphMinor.GM12

open Set Metric Surface EuclideanGeometry

/-- A line through a unit circle point has only finitely many unit
circle points. This is the finite exclusion used in the crossing
construction for XII (4.5), page 253. -/
theorem finite_unit_circle_inter_line {a q : ℂ} (ha : ‖a‖ = 1) :
    (sphere (0 : ℂ) 1 ∩ (line[ℝ, a, q] : Set ℂ)).Finite := by
  let s : EuclideanGeometry.Sphere ℂ := ⟨0, 1⟩
  have ha' : a ∈ s := by simpa [s, EuclideanGeometry.mem_sphere, dist_zero_right] using ha
  refine (toFinite ({a, s.secondInter a (q - a)} : Set ℂ)).subset ?_
  intro z hz
  have hz' : z ∈ s := by
    simpa [s, EuclideanGeometry.mem_sphere] using hz.1
  exact (s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair ha' hz.2).mpr hz'

/-- The circle parametrization is injective on an interval shorter
than one full turn. -/
theorem ee_injOn_short_interval {a b : ℝ} (hab : b ≤ a + 1) :
    InjOn ee (Ioo a b) := by
  intro x hx y hy hxy
  obtain ⟨m, hm⟩ := ee_eq_iff.mp hxy
  have hmlo : (-1 : ℝ) < (m : ℝ) := by linarith [hx.1, hy.2]
  have hmhi : (m : ℝ) < 1 := by linarith [hx.2, hy.1]
  have hlo : (-1 : ℤ) < m := by exact_mod_cast hmlo
  have hhi : m < (1 : ℤ) := by exact_mod_cast hmhi
  have hm0 : m = 0 := by omega
  simpa [hm0] using hm

/-- A short open circle arc contains a point outside any finite
set, including a finite set of old ports. -/
theorem exists_circle_port_avoiding_finite_set {B : Set ℂ} (hB : B.Finite)
    {u v : ℝ} (huv : u < v) (hlen : v ≤ u + 1) :
    ∃ t ∈ Ioo u v, (ee t : ℂ) ∉ B := by
  have hi : InjOn (fun t : ℝ => (ee t : ℂ)) (Ioo u v) := by
    intro x hx y hy hxy
    exact ee_injOn_short_interval hlen hx hy (Subtype.ext hxy)
  obtain ⟨z, ⟨t, ht, rfl⟩, hz⟩ :=
    (Set.Infinite.image hi (Ioo_infinite huv)).exists_notMem_finite hB
  exact ⟨t, ht, hz⟩

/-- Choose a port in any prescribed short open circle arc while
avoiding finitely many lines through existing circle ports. This
supplies the finite avoidance step in XII (4.5), page 253. -/
theorem exists_circle_port_avoiding_lines {ι : Type*} [Finite ι]
    (a q : ι → ℂ) (ha : ∀ i, ‖a i‖ = 1)
    {u v : ℝ} (huv : u < v) (hlen : v ≤ u + 1) :
    ∃ t ∈ Ioo u v, ∀ i, (ee t : ℂ) ∉ (line[ℝ, a i, q i] : Set ℂ) := by
  classical
  let B : Set ℂ := ⋃ i, sphere (0 : ℂ) 1 ∩ (line[ℝ, a i, q i] : Set ℂ)
  have hB : B.Finite := finite_iUnion fun i => finite_unit_circle_inter_line (ha i)
  have hi : InjOn (fun t : ℝ => (ee t : ℂ)) (Ioo u v) := by
    intro x hx y hy hxy
    exact ee_injOn_short_interval hlen hx hy (Subtype.ext hxy)
  have hinf := Set.Infinite.image hi (Ioo_infinite huv)
  obtain ⟨z, ⟨t, ht, rfl⟩, hz⟩ := hinf.exists_notMem_finite hB
  refine ⟨t, ht, fun i hi => hz ?_⟩
  exact mem_iUnion.mpr ⟨i, ⟨by simp, hi⟩⟩

end GraphMinor.GM12
