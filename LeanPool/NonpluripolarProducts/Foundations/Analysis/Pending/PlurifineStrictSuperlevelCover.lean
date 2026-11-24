/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlurifineEuclideanComparison
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorExistence

/-! # Actual countable compact coverage of one genuine singular PSH superlevel -/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.PlurifineStrictSuperlevelCover

open FirstPass FirstPass.MongeAmpere PlurifinePshTopology PlurifineEuclideanComparison

noncomputable section

variable {n : ℕ}

/-- An actual ordinary compact exhaustion and genuine PSH positive margins produce a countable
    plurifine-open cover whose Euclidean closures stay in the same strict superlevel. -/
theorem exists_countable_superlevel_cover {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω) (c : ℝ) :
    ∃ V : ℕ × ℕ → Set (ComplexModel n),
      (⋃ i, V i) = {z | z ∈ Ω ∧ (c : EReal) < u z} ∧
      ∀ i, MeasurableSet (V i) ∧ IsOpen[topology Ω] (Subtype.val ⁻¹' V i) ∧
        IsCompact (closure (V i)) ∧ closure (V i) ⊆ {z | z ∈ Ω ∧ (c : EReal) < u z} := by
  obtain ⟨U, _, hUc, hUabsorb⟩ := BedfordTaylor.exists_exhaustion Ω
  let V : ℕ × ℕ → Set (ComplexModel n) := fun i =>
    (U i.1 : Set (ComplexModel n)) ∩ {z | ((c + 1 / (i.2 + 1) : ℝ) : EReal) < u z}
  have hUΩ : ∀ j, (U j : Set (ComplexModel n)) ⊆ Ω :=
    fun j => subset_closure.trans (hUc j).2
  have hcl : ∀ i, closure (V i) ⊆ closure (U i.1 : Set (ComplexModel n)) :=
    fun _ => closure_mono inter_subset_left
  refine ⟨V, ?_, ?_⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      have hpos : (0 : ℝ) < 1 / (i.2 + 1) := by positivity
      exact ⟨hUΩ i.1 hi.1,
        (EReal.coe_lt_coe_iff.mpr (by linarith : c < c + 1 / (i.2 + 1))).trans hi.2⟩
    · intro hz
      obtain ⟨d, hcd, hdu⟩ := EReal.exists_rat_btwn_of_lt hz.2
      have hgap : 0 < (d : ℝ) - c := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hcd)
      obtain ⟨l, hl⟩ := exists_nat_one_div_lt hgap
      obtain ⟨j, hj⟩ := hUabsorb {z} isCompact_singleton (singleton_subset_iff.mpr hz.1)
      apply mem_iUnion.mpr
      refine ⟨(j, l), hj (mem_singleton z), ?_⟩
      exact (EReal.coe_lt_coe_iff.mpr (by linarith : c + 1 / (l + 1) < (d : ℝ))).trans hdu
  · intro i
    have hmeas : MeasurableSet (V i) := by
      have heq : V i = (U i.1 : Set (ComplexModel n)) ∩
          {z | z ∈ Ω ∧ ((c + 1 / (i.2 + 1) : ℝ) : EReal) < u z} := by
        ext z
        exact and_congr_right fun hz => (and_iff_right (hUΩ i.1 hz)).symm
      rw [heq]
      exact (U i.1).isOpen.measurableSet.inter (measurableSet_psh_superlevel hu _)
    have hfine : IsOpen[topology Ω] (Subtype.val ⁻¹' V i) := by
      let : TopologicalSpace Ω := topology Ω
      exact (isOpen_euclidean (U i.1).isOpen).inter (isOpen_psh_superlevel hu _)
    have hc : IsCompact (closure (V i)) :=
      (hUc i.1).1.of_isClosed_subset isClosed_closure (hcl i)
    refine ⟨hmeas, hfine, hc, ?_⟩
    intro z hz
    have hzΩ := (hUc i.1).2 (hcl i hz)
    have hge : ((c + 1 / (i.2 + 1) : ℝ) : EReal) ≤ u z :=
      (hu z hzΩ).upperSemicontinuousAt.frequently _
        ((mem_closure_iff_frequently.mp hz).mono fun y hy => hy.2.le)
    have hpos : (0 : ℝ) < 1 / (i.2 + 1) := by positivity
    exact ⟨hzΩ, (EReal.coe_lt_coe_iff.mpr
      (by linarith : c < c + 1 / (i.2 + 1))).trans_le hge⟩

end

end SGPT.Foundations.Analysis.Pending.PlurifineStrictSuperlevelCover
