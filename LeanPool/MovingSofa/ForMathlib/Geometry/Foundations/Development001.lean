/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Moving sofa: related mathematical developments

* `ForMathlib.Geometry.Euclidean.Segment`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Geometry / Euclidean / Segment
-/

@[expose] public section

open MeasureTheory

namespace EuclideanGeometry

/-- Two unit vectors perpendicular to the same nonzero planar vector agree up to sign. -/
theorem eq_or_eq_neg_of_unit_orthogonal
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2))
    {v n m : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0)
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hvn : inner ℝ v n = 0) (hvm : inner ℝ v m = 0) : n = m ∨ n = -m := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
    ⟨by simp [finrank_euclideanSpace]⟩
  obtain ⟨r, hr⟩ :=
    ((o.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two).mp hvn).resolve_left hv
  obtain ⟨s, hs⟩ :=
    ((o.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two).mp hvm).resolve_left hv
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hrabs : |r| * ‖v‖ = 1 := by
    calc
      |r| * ‖v‖ = ‖r • o.rotation (Real.pi / 2 : ℝ) v‖ := by simp [norm_smul]
      _ = ‖n‖ := congrArg norm hr
      _ = 1 := hn
  have hsabs : |s| * ‖v‖ = 1 := by
    calc
      |s| * ‖v‖ = ‖s • o.rotation (Real.pi / 2 : ℝ) v‖ := by simp [norm_smul]
      _ = ‖m‖ := congrArg norm hs
      _ = 1 := hm
  have habs : |r| = |s| := mul_right_cancel₀ (ne_of_gt hvnorm) (hrabs.trans hsabs.symm)
  rcases (abs_eq_abs.mp habs) with hrs | hrs
  · left
    rw [← hr, ← hs, hrs]
  · right
    rw [← hr, ← hs, hrs, neg_smul]

/-- Equal segments have the same orthogonal directions. -/
theorem inner_direction_eq_zero_of_segment_eq
    {a b c d n : (EuclideanSpace ℝ (Fin 2))} (hseg : segment ℝ a b = segment ℝ c d)
    (hcdn : inner ℝ (d - c) n = 0) : inner ℝ (b - a) n = 0 := by
  have ha : a ∈ segment ℝ c d := hseg ▸ left_mem_segment ℝ a b
  have hb : b ∈ segment ℝ c d := hseg ▸ right_mem_segment ℝ a b
  rw [segment_eq_image'] at ha hb
  obtain ⟨r, _, hr⟩ := ha
  obtain ⟨s, _, hs⟩ := hb
  rw [← hr, ← hs]
  have heq : c + s • (d - c) - (c + r • (d - c)) = (s - r) • (d - c) := by
    module
  rw [heq]
  rw [inner_smul_left, hcdn, mul_zero]

/-- Equal segments have equal endpoint distances. -/
theorem dist_eq_of_segment_eq {a b c d : (EuclideanSpace ℝ (Fin 2))}
    (hseg : segment ℝ a b = segment ℝ c d) : dist a b = dist c d := by
  have h := congrArg (Measure.hausdorffMeasure 1) hseg
  simpa only [MeasureTheory.hausdorffMeasure_segment, edist_dist,
    ENNReal.ofReal_eq_ofReal_iff, dist_nonneg] using h

/-- A segment transverse to a hyperplane meets it in at most one point. -/
lemma segment_inter_hyperplane_subsingleton {a b n : EuclideanSpace ℝ (Fin 2)} {c : ℝ}
    (h : inner ℝ (b - a) n ≠ 0) :
    (segment ℝ a b ∩ {q | inner ℝ q n = c}).Subsingleton := by
  rintro x ⟨hx, hxc⟩ y ⟨hy, hyc⟩
  rw [segment_eq_image'] at hx hy
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨s, hs, rfl⟩ := hy
  have heq : r * inner ℝ (b - a) n = s * inner ℝ (b - a) n := by
    have hx : inner ℝ a n + r * inner ℝ (b - a) n = c := by
      simpa only [Set.mem_ofPred_eq, inner_add_left, real_inner_smul_left] using hxc
    have hy : inner ℝ a n + s * inner ℝ (b - a) n = c := by
      simpa only [Set.mem_ofPred_eq, inner_add_left, real_inner_smul_left] using hyc
    linarith
  rw [mul_right_cancel₀ h heq]

/-- A transverse segment has zero length on a hyperplane. -/
lemma hausdorffMeasure_segment_inter_hyperplane_eq_zero {a b n : EuclideanSpace ℝ (Fin 2)} {c : ℝ}
    (h : inner ℝ (b - a) n ≠ 0) :
    Measure.hausdorffMeasure 1 (segment ℝ a b ∩ {q | inner ℝ q n = c}) = 0 := by
  have := Measure.nullSingletonClass_hausdorff (EuclideanSpace ℝ (Fin 2)) (by norm_num : (0 : ℝ) <
    1)
  exact (segment_inter_hyperplane_subsingleton h).countable.measure_zero _

/-- A segment not contained in a hyperplane meets it in at most one point. -/
lemma segment_inter_hyperplane_subsingleton_of_not_subset {a b n : EuclideanSpace ℝ (Fin 2)} {c : ℝ}
    (hnot : ¬ segment ℝ a b ⊆ {q | inner ℝ q n = c}) :
    (segment ℝ a b ∩ {q | inner ℝ q n = c}).Subsingleton := by
  by_cases hdir : inner ℝ (b - a) n = 0
  · intro x hx y hy
    exfalso
    apply hnot
    have hconstant {q : EuclideanSpace ℝ (Fin 2)} (hq : q ∈ segment ℝ a b) :
        inner ℝ q n = inner ℝ a n := by
      rw [segment_eq_image'] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      simp only [inner_add_left, real_inner_smul_left, hdir, mul_zero, add_zero]
    intro q hq
    exact (hconstant hq).trans ((hconstant hx.1).symm.trans hx.2)
  · exact segment_inter_hyperplane_subsingleton hdir

/-- A nondegenerate segment covered by finitely many hyperplanes lies in one of them. -/
lemma exists_segment_subset_hyperplane_of_finite_cover {ι : Type*}
    (I : Finset ι) (n : ι → EuclideanSpace ℝ (Fin 2)) (c : ι → ℝ) {a b : EuclideanSpace ℝ (Fin 2)}
      (hab : a ≠ b)
    (hcover : segment ℝ a b ⊆ ⋃ i ∈ I, {q | inner ℝ q (n i) = c i}) :
    ∃ i ∈ I, segment ℝ a b ⊆ {q | inner ℝ q (n i) = c i} := by
  classical
  have := Measure.nullSingletonClass_hausdorff (EuclideanSpace ℝ (Fin 2)) (by norm_num : (0 : ℝ) <
    1)
  by_contra hnot
  push Not at hnot
  have hnull (i : ι) (hi : i ∈ I) :
      Measure.hausdorffMeasure 1 (segment ℝ a b ∩ {q | inner ℝ q (n i) = c i}) = 0 :=
    (segment_inter_hyperplane_subsingleton_of_not_subset (hnot i hi)).countable.measure_zero _
  have hsub : segment ℝ a b ⊆
      ⋃ i ∈ I, segment ℝ a b ∩ {q | inner ℝ q (n i) = c i} := by
    intro q hq
    obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.mp (hcover hq)
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hq, hqi⟩
  have hm := measure_mono_null hsub
    ((measure_biUnion_null_iff I.finite_toSet.countable).mpr hnull)
  rw [hausdorffMeasure_segment] at hm
  exact hab (edist_eq_zero.mp hm)

end EuclideanGeometry

end

end
