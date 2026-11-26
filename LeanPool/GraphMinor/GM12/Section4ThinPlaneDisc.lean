/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM12.Section4PinchedDisc
import LeanPool.GraphMinor.Surface.PlaneDisc
import LeanPool.GraphMinor.Surface.Wedge
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# A thin disc avoiding a closed set except at its ends

For the empty-disc construction in XII (4.3), page 250,
straighten a normal arc to a real segment. The distance from each
interior point of the segment to the forbidden closed set gives
a positive width. This width tends to zero at the ends. Shrinking
the vertical fibres of the unit disc by that width produces the
required disc within the prescribed open chart.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface Metric Complex

/-- A real segment whose interior misses a closed set can be thickened
into a disc meeting that set only at its ends, within any open set
containing the segment. -/
theorem exists_thin_plane_disc
    {O B : Set ℂ} (hO : IsOpen O) (hB : IsClosed B)
    (hsegO : Complex.ofReal '' Icc (-1 : ℝ) 1 ⊆ O)
    (hBseg : B ∩ (Complex.ofReal '' Icc (-1 : ℝ) 1) ⊆ {-1, 1})
    (hleft : (-1 : ℂ) ∈ B) (hright : (1 : ℂ) ∈ B) :
    ∃ D : Set ℂ, IsClosedDisc D ∧ D ⊆ O ∧ D ∩ B = {-1, 1} ∧
      ({-1, 1} : Set ℂ) ⊆ discBd D ∧
      Complex.ofReal '' Icc (-1 : ℝ) 1 ⊆ D := by
  let F : Set ℂ := Oᶜ ∪ B
  have hF : IsClosed F := hO.isClosed_compl.union hB
  have hFne : F.Nonempty := ⟨-1, Or.inr hleft⟩
  let ε : ℝ → ℝ := fun x => min 1 (infDist (x : ℂ) F / 2)
  have hεc : Continuous ε := continuous_const.min
    (((continuous_infDist_pt F).comp continuous_ofReal).div_const 2)
  have hεnn : ∀ x, 0 ≤ ε x := fun x => le_min (by norm_num)
    (div_nonneg infDist_nonneg (by norm_num))
  have hεpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ε x := by
    intro x hx
    have hxseg : (x : ℂ) ∈ Complex.ofReal '' Icc (-1 : ℝ) 1 :=
      ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩
    have hxF : (x : ℂ) ∉ F := by
      rintro (hxO | hxB)
      · exact hxO (hsegO hxseg)
      · have hend := hBseg ⟨hxB, hxseg⟩
        rcases hend with h | h
        · have h' := congrArg Complex.re h
          simp only [ofReal_re, neg_re, one_re] at h'
          linarith [hx.1]
        · have h' := congrArg Complex.re (Set.mem_singleton_iff.mp h)
          simp only [ofReal_re, one_re] at h'
          linarith [hx.2]
    have hdist : 0 < infDist (x : ℂ) F :=
      (infDist_pos_iff_notMem_closure hFne).mp (by rw [hF.closure_eq]; exact hxF)
    exact lt_min (by norm_num) (half_pos hdist)
  have hzero₀ : infDist (-1 : ℂ) F = 0 := Metric.infDist_zero_of_mem (s := F) (x := -1)
    (Or.inr hleft)
  have hzero₁ : infDist (1 : ℂ) F = 0 := Metric.infDist_zero_of_mem (s := F) (x := 1)
    (Or.inr hright)
  have hεends : ε (-1) = 0 ∧ ε 1 = 0 := by
    constructor <;> simp [ε, hzero₀, hzero₁]
  let f : ℂ → ℂ := fun z => (z.re : ℂ) + (ε z.re * z.im : ℝ) * I
  have hfc : Continuous f := (continuous_ofReal.comp continuous_re).add
    ((continuous_ofReal.comp ((hεc.comp continuous_re).mul continuous_im)).mul_const I)
  have hfi := pinched_disc_injOn ε (fun x hx => (hεpos x hx).ne')
  have hdisc := isClosedDisc_image_injOn isClosedDisc_closedBall.1
    (isCompact_closedBall (0 : ℂ) 1) hfc.continuousOn hfi
  have hendf : f (-1) = -1 ∧ f 1 = 1 := by
    constructor <;> simp [f, hεends.1, hεends.2]
  have hloc : ∀ z ∈ closedBall (0 : ℂ) 1,
      f z ∈ O ∧ (f z ∈ B → f z ∈ ({-1, 1} : Set ℂ)) := by
    intro z hz
    have hzN : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have hre := abs_le.mp ((abs_re_le_norm z).trans hzN)
    have him := (abs_im_le_norm z).trans hzN
    by_cases hmid : z.re ∈ Ioo (-1 : ℝ) 1
    · have hdist : dist (f z) (z.re : ℂ) ≤ ε z.re := by
        have heq : f z - (z.re : ℂ) = (ε z.re * z.im : ℝ) * I := by
          dsimp only [f]; ring
        rw [dist_eq_norm, heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_mul, abs_of_nonneg (hεnn _)]
        exact mul_le_of_le_one_right (hεnn _) him
      have hsmall : ε z.re < infDist (z.re : ℂ) F :=
        (min_le_right _ _).trans_lt (half_lt_self (by
          have hpos := hεpos z.re hmid
          have hle : ε z.re ≤ infDist (z.re : ℂ) F / 2 := min_le_right _ _
          linarith))
      have hnot : f z ∉ F := by
        intro hmem
        have hle := infDist_le_dist_of_mem (x := (z.re : ℂ)) hmem
        rw [dist_comm] at hle
        exact (hdist.trans_lt hsmall).not_ge hle
      exact ⟨not_not.mp (fun hn => hnot (Or.inl hn)), fun hb => False.elim (hnot (Or.inr hb))⟩
    · have hext : z.re = -1 ∨ z.re = 1 := by
        simp only [mem_Ioo] at hmid
        rcases le_or_gt z.re (-1) with h | h
        · exact Or.inl (le_antisymm h hre.1)
        · exact Or.inr (le_antisymm hre.2 (not_lt.mp (fun h' => hmid ⟨h, h'⟩)))
      have hfend : f z ∈ ({-1, 1} : Set ℂ) := by
        rcases hext with he | he
        · simp [f, he, hεends.1]
        · simp [f, he, hεends.2]
      have hOend : ({-1, 1} : Set ℂ) ⊆ O := by
        intro w hw
        apply hsegO
        rcases hw with rfl | hw
        · exact ⟨-1, by norm_num, by simp⟩
        · have hw' := Set.mem_singleton_iff.mp hw
          exact hw' ▸ ⟨1, by norm_num, by simp⟩
      exact ⟨hOend hfend, fun _ => hfend⟩
  refine ⟨f '' closedBall 0 1, hdisc.1, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hloc z hz).1
  · apply Set.Subset.antisymm
    · rintro w ⟨⟨z, hz, rfl⟩, hwB⟩
      exact (hloc z hz).2 hwB
    · intro w hw
      rcases hw with rfl | hw
      · exact ⟨⟨-1, by norm_num, hendf.1⟩, hleft⟩
      · have hw' := Set.mem_singleton_iff.mp hw
        subst w
        exact ⟨⟨1, by norm_num, hendf.2⟩, hright⟩
  · rw [hdisc.2, isClosedDisc_closedBall.2]
    intro w hw
    rcases hw with rfl | hw
    · exact ⟨-1, by norm_num, hendf.1⟩
    · have hw' := Set.mem_singleton_iff.mp hw
      subst w
      exact ⟨1, by norm_num, hendf.2⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨(x : ℂ), ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr hx
    · simp [f]

end GraphMinor.GM12
