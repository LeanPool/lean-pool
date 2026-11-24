/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4ChordGeometry
public import Mathlib.Analysis.Complex.Basic
import LeanPool.GraphMinor.Surface.Lunes

/-!
# Joining a circle port to an outer vertex

For the crossing drawing of XII (4.5), page 253, join the ports
near each vertex by straight outer pieces. The tangent line to the
unit circle at a port gives a simple test: if the vertex lies
strictly beyond that tangent, the connecting segment meets the
unit disc only at its port. Thus these pieces cannot meet the
interior chords.
-/

public section

namespace GraphMinor.GM12

open Set Metric Surface

/-- An outer segment from a unit circle port to a point beyond
its tangent line meets the unit disc exactly at the port. This
keeps the vertex pieces away from the chords in XII (4.5), page 253. -/
theorem outer_port_segment_inter_disc {a v : ℂ} (ha : ‖a‖ = 1)
    (hv : 1 < ((starRingEnd ℂ) a * v).re) :
    segment ℝ a v ∩ closedBall 0 1 = {a} := by
  have haa : ((starRingEnd ℂ) a * a).re = 1 := by
    rw [RCLike.conj_mul, ha]
    norm_num
  ext x
  constructor
  · rintro ⟨hx, hxD⟩
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hx
    by_cases ht0 : t = 0
    · have hs1 : s = 1 := by simpa [ht0] using hst
      simp [ht0, hs1]
    · have htp : 0 < t := lt_of_le_of_ne ht (fun h => ht0 h.symm)
      have hlin : ((starRingEnd ℂ) a * (s • a + t • v)).re =
          s + t * ((starRingEnd ℂ) a * v).re := by
        simp only [mul_add, mul_smul_comm, Complex.add_re, Complex.smul_re, smul_eq_mul, haa,
          mul_one]
      have hbig : 1 < ((starRingEnd ℂ) a * (s • a + t • v)).re := by
        rw [hlin]
        have hmul := mul_lt_mul_of_pos_left hv htp
        nlinarith
      have hbound := Complex.re_le_norm ((starRingEnd ℂ) a * (s • a + t • v))
      rw [norm_mul, Complex.norm_conj, ha, one_mul] at hbound
      have hnorm := mem_closedBall_zero_iff.mp hxD
      exact False.elim ((not_lt_of_ge (hbound.trans hnorm)) hbig)
  · rintro rfl
    exact ⟨left_mem_segment _ _ _, by simp [ha]⟩

/-- An outer port segment is a simple arc. The strict tangent
inequality also proves its two ends are distinct. -/
theorem outer_port_segment_isLine {a v : ℂ} (ha : ‖a‖ = 1)
    (hv : 1 < ((starRingEnd ℂ) a * v).re) :
    IsLineWithEnds (segment ℝ a v) a v := by
  apply isLineWithEnds_segment
  intro h
  rw [← h, RCLike.conj_mul, ha] at hv
  norm_num at hv

/-- An outer vertex piece cannot meet a chord with two other
ports. Thus all crossings between different edges in the source
drawing of XII (4.5), page 253, occur between their inner chords. -/
theorem outer_port_segment_disjoint_chord {a v b c : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hv : 1 < ((starRingEnd ℂ) a * v).re)
    (hbc : b ≠ c) (hab : a ≠ b) (hac : a ≠ c) :
    Disjoint (segment ℝ a v) (segment ℝ b c) := by
  apply disjoint_left.mpr
  intro x hx hx'
  have hgeom := unit_chord_geometry hb hc hbc
  have hxa : x = a := show x ∈ ({a} : Set ℂ) from
    outer_port_segment_inter_disc ha hv ▸ And.intro hx (hgeom.2.1 hx')
  subst x
  have hport : a = b ∨ a = c := show a ∈ ({b, c} : Set ℂ) from
    hgeom.2.2 ▸ And.intro hx' (by simp [ha])
  exact hport.elim hab hac

private theorem outer_point_not_on_port_line {a b v : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hva : 1 < ((starRingEnd ℂ) a * v).re)
    (hvb : 1 < ((starRingEnd ℂ) b * v).re) :
    v ∉ line[ℝ, a, b] := by
  intro hvline
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hvline
  have haa : ((starRingEnd ℂ) a * a).re = 1 := by
    rw [RCLike.conj_mul, ha]; norm_num
  have hbb : ((starRingEnd ℂ) b * b).re = 1 := by
    rw [RCLike.conj_mul, hb]; norm_num
  have hab : ((starRingEnd ℂ) a * b).re = ((starRingEnd ℂ) b * a).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hsum : ((starRingEnd ℂ) a * v).re + ((starRingEnd ℂ) b * v).re =
      1 + ((starRingEnd ℂ) a * b).re := by
    rw [← ht, AffineMap.lineMap_apply_module]
    simp only [mul_add, mul_smul_comm, Complex.add_re, Complex.smul_re, smul_eq_mul,
      haa, hbb, ← hab]
    ring
  have hbound := Complex.re_le_norm ((starRingEnd ℂ) a * b)
  rw [norm_mul, Complex.norm_conj, ha, hb, one_mul] at hbound
  linarith

/-- Outer pieces joining distinct visible ports to one vertex
meet exactly at that vertex. This proves the vertex-star part of
the crossing construction in XII (4.5), page 253. -/
theorem outer_port_segments_inter {a b v : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b)
    (hva : 1 < ((starRingEnd ℂ) a * v).re)
    (hvb : 1 < ((starRingEnd ℂ) b * v).re) :
    segment ℝ a v ∩ segment ℝ b v = {v} := by
  ext x
  constructor
  · rintro ⟨hxa, hxb⟩
    by_cases hxv : x = v
    · exact hxv
    have hxlinea : x ∈ line[ℝ, a, v] :=
      (line[ℝ, a, v]).convex.segment_subset
        (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _) hxa
    have hxlineb : x ∈ line[ℝ, b, v] :=
      (line[ℝ, b, v]).convex.segment_subset
        (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _) hxb
    have hea := affineSpan_pair_eq_of_mem_of_mem_of_ne hxlinea
      (right_mem_affineSpan_pair ℝ a v) hxv
    have heb := affineSpan_pair_eq_of_mem_of_mem_of_ne hxlineb
      (right_mem_affineSpan_pair ℝ b v) hxv
    have hbline : b ∈ line[ℝ, a, v] := by
      rw [← hea, heb]
      exact left_mem_affineSpan_pair _ _ _
    have heq := affineSpan_pair_eq_of_right_mem_of_ne hbline (fun h => hab h.symm)
    have hvline : v ∈ line[ℝ, a, b] := by
      rw [heq]
      exact right_mem_affineSpan_pair _ _ _
    exact False.elim (outer_point_not_on_port_line ha hb hva hvb hvline)
  · rintro rfl
    exact ⟨right_mem_segment _ _ _, right_mem_segment _ _ _⟩

end GraphMinor.GM12
