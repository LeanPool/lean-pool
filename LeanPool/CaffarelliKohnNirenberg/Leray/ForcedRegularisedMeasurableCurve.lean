/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedJointRep
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Measurable curves of `L²` classes from jointly measurable fields

A jointly measurable field `Γ(x, s)` with square-integrable slices defines a
curve `s ↦ [Γ(·, s)]` of `L²` classes. Its distance to any fixed class is a
measurable function of `s` by Tonelli, and in a separable metric space this
already makes the curve measurable. This is the measurability used for the
force and Stokes Duhamel integrands of `lem:regularised-forced`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

/-- In a separable pseudometric Borel space, a map whose distances to all
points are measurable is measurable. -/
theorem measurable_of_measurable_dist {β Y : Type*} [MeasurableSpace β]
    [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace.SeparableSpace Y] {f : β → Y}
    (hf : ∀ y : Y, Measurable fun s => dist (f s) y) : Measurable f := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact measurable_of_subsingleton_codomain f
  let D : ℕ → Y := TopologicalSpace.denseSeq Y
  have hD : DenseRange D := TopologicalSpace.denseRange_denseSeq Y
  refine measurable_of_isOpen fun U hU => ?_
  classical
  let S : ℕ → ℚ → Set β := fun n q =>
    if 0 < q ∧ Metric.ball (D n) q ⊆ U then {s | dist (f s) (D n) < q} else ∅
  have hS : ∀ n q, MeasurableSet (S n q) := by
    intro n q
    simp only [S]
    split_ifs
    · exact measurableSet_lt (hf (D n)) measurable_const
    · exact MeasurableSet.empty
  have heq : f ⁻¹' U = ⋃ n, ⋃ q, S n q := by
    ext s
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro hs
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU (f s) hs
      obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (half_pos hε)
      obtain ⟨n, hn⟩ := hD.exists_dist_lt (f s) (by exact_mod_cast hq0 : (0 : ℝ) < q)
      refine ⟨n, q, ?_⟩
      have hsub : Metric.ball (D n) q ⊆ U := by
        intro z hz
        apply hball
        rw [Metric.mem_ball] at hz ⊢
        calc dist z (f s) ≤ dist z (D n) + dist (D n) (f s) := dist_triangle _ _ _
          _ < q + q := add_lt_add hz (by rw [dist_comm]; exact hn)
          _ < ε := by linarith only [hq]
      have hpos : (0 : ℚ) < q := by exact_mod_cast hq0
      simp only [S, hpos, hsub, and_self, ↓reduceIte]
      exact hn
    · rintro ⟨n, q, hs⟩
      simp only [S] at hs
      split_ifs at hs with hcond
      · exact hcond.2 (by simpa [Metric.mem_ball] using hs)
      · exact absurd hs (Set.notMem_empty s)
  rw [heq]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun q => hS n q

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  [NormedAddCommGroup E]

/-- The `L²` distance from the slices of a jointly measurable field to a fixed
class is measurable in the slice variable. -/
theorem measurable_dist_slice_class [SFinite μ] (Γ : α × β → E) (hΓ : StronglyMeasurable Γ)
    (γ : β → Lp E 2 μ) (hrep : ∀ s, (fun x => Γ (x, s)) =ᵐ[μ] γ s) (c : Lp E 2 μ) :
    Measurable fun s => dist (γ s) c := by
  have heq : (fun s => dist (γ s) c) = fun s =>
      ((∫⁻ x, ‖Γ (x, s) - (c : α → E) x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))).toReal := by
    funext s
    rw [Lp.dist_def]
    congr 1
    have hae : ((γ s : α → E) - (c : α → E)) =ᵐ[μ] fun x => Γ (x, s) - (c : α → E) x := by
      filter_upwards [hrep s] with x hx
      simp [hx]
    have hm : AEStronglyMeasurable (fun x => Γ (x, s) - (c : α → E) x) μ :=
      ((hΓ.comp_measurable (measurable_id.prodMk measurable_const)).sub
        (Lp.stronglyMeasurable c)).aestronglyMeasurable
    rw [eLpNorm_congr_ae hae, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm]
    simp
  rw [heq]
  refine ENNReal.measurable_toReal.comp (Measurable.pow_const ?_ _)
  exact Measurable.lintegral_prod_left'
    (f := fun q : α × β => ‖Γ q - (c : α → E) q.1‖ₑ ^ (2 : ℝ))
    ((hΓ.sub ((Lp.stronglyMeasurable c).comp_measurable measurable_fst)).enorm.pow_const _)

/-- A curve of `L²` classes represented slice by slice by a jointly measurable
field is strongly measurable. -/
theorem stronglyMeasurable_of_jointRep [SFinite μ] [MeasurableSpace.CountablyGenerated α]
     [SecondCountableTopology E]
    (Γ : α × β → E) (hΓ : StronglyMeasurable Γ)
    (γ : β → Lp E 2 μ) (hrep : ∀ s, (fun x => Γ (x, s)) =ᵐ[μ] γ s) :
    StronglyMeasurable γ := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  borelize (↥(Lp E 2 μ))
  exact (measurable_of_measurable_dist fun c =>
    measurable_dist_slice_class Γ hΓ γ hrep c).stronglyMeasurable

end CKN.Leray

end
