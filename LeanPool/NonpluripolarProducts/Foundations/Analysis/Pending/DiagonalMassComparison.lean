/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BoundedDifferenceMass
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalDiagonalScaling

/-!
# Diagonal mass comparison in a semipositive background

For a semipositive closed real `(1,1)`-form `θ` on a compact Kähler manifold, the
diagonal global mixed measure `c ↦ μ(c, …, c)` satisfies the hypotheses of
`BoundedDifferenceMass.mass_le_of_le_add` with `N = n`:

* locality of maxima is `GlobalMaxLocality.globalMixedMeasure_restrict_max_eq`;
* poles are null (`GlobalSlotComparison.globalMixedMeasure_pole_null`);
* bounded diagonal tuples all have the same mass (`oneSlotMassInvariance`);
* scaling is `GlobalDiagonalScaling.globalMixedMeasure_diagonal_scale`.

Hence potentials with bounded difference have the same diagonal mass.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.DiagonalMassComparison

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
open GlobalNonPluripolar BoundedGlobalProduct GlobalMaxLocality UniformBoundedGlobalMass
open GlobalSlotComparison GlobalDiagonalScaling BoundedDifferenceMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Diagonal mass is monotone along `a ≤ b ≤ a + t` in a semipositive background. -/
theorem diagonal_univ_le_of_le_add (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} (hθ : θ.val.IsSemipositive) {a b : M → EReal}
    (ha : ThetaPlurisubharmonic θ.val a) (hb : ThetaPlurisubharmonic θ.val b)
    {t : ℝ} (ht : 0 ≤ t) (hab : ∀ p, a p ≤ b p) (hba : ∀ p, b p ≤ a p + (t : EReal)) :
    globalMixedMeasure (fun _ => θ) (fun _ => a) (fun _ => ha) univ ≤
      globalMixedMeasure (fun _ => θ) (fun _ => b) (fun _ => hb) univ := by
  rcases isEmpty_or_nonempty M with hM | hM
  · simp [Set.univ_eq_empty_iff.mpr hM]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (congrArg (fun μ : Measure M => μ univ)
      (globalMixedMeasure_congr_tuple (Subsingleton.elim _ _) _ _)).le
  have h0 : ThetaPlurisubharmonic θ.val (fun _ => ((0 : ℝ) : EReal)) :=
    thetaPlurisubharmonic_const θ hθ 0
  refine mass_le_of_le_add (fun c => ThetaPlurisubharmonic θ.val c)
    (fun c hc => globalMixedMeasure (fun _ => θ) (fun _ => c) (fun _ => hc))
    (fun c hc => ThetaPlurisubharmonic.measurable hc)
    (fun c hc S => globalMixedMeasure_apply_lt_top omega _ S)
    (fun c hc => globalMixedMeasure_pole_null (fun _ => hc) ⟨0, hn⟩)
    (fun r => thetaPlurisubharmonic_const θ hθ r)
    (fun c hc r => thetaPlurisubharmonic_max_const hθ hc r)
    (fun c hc r => isBoundedPotential_max_const hc r)
    (fun c d hc hd => ThetaPlurisubharmonic.max hc hd)
    (fun a c ha hc hm => ?_)
    (globalMixedMeasure (fun _ => θ) (fun _ => fun _ => ((0 : ℝ) : EReal)) (fun _ => h0) univ)
    (fun c hc hcb => globalMixedMeasure_univ_eq_of_bounded (oneSlotMassInvariance omega _)
      _ _ (fun _ => hcb) (fun _ => ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩))
    n (fun c hc hcb ε hε0 hε1 K => globalMixedMeasure_diagonal_scale hθ hc hcb hε0 hε1 K)
    ht ha hb hab hba
  have hS : {p | c p < a p} = {p | ∀ _ : Fin n, c p < a p} := by
    ext p
    simp only [mem_ofPred_eq]
    exact ⟨fun h _ => h, fun h => h ⟨0, hn⟩⟩
  rw [hS]
  exact globalMixedMeasure_restrict_max_eq (fun _ => ha) (fun _ => hc) (fun _ => hm)

/-- **Same diagonal mass for a bounded difference** in a semipositive background. -/
theorem diagonal_univ_eq_of_le_add (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} (hθ : θ.val.IsSemipositive) {a b : M → EReal}
    (ha : ThetaPlurisubharmonic θ.val a) (hb : ThetaPlurisubharmonic θ.val b)
    {t : ℝ} (ht : 0 ≤ t) (hab : ∀ p, a p ≤ b p) (hba : ∀ p, b p ≤ a p + (t : EReal)) :
    globalMixedMeasure (fun _ => θ) (fun _ => a) (fun _ => ha) univ =
      globalMixedMeasure (fun _ => θ) (fun _ => b) (fun _ => hb) univ := by
  refine le_antisymm (diagonal_univ_le_of_le_add omega hθ ha hb ht hab hba) ?_
  have hb' := GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const hb t
  have hsub := GlobalMeasureInvariance.globalMixedMeasure_sub_const (θ := fun _ => θ)
    (u := fun _ => b) (fun _ => hb) (fun _ => t)
  have hle := diagonal_univ_le_of_le_add omega hθ hb' ha ht
    (fun p => EReal.sub_le_of_le_add (hba p))
    (fun p => (hab p).trans (by rw [EReal.sub_add_cancel]))
  calc globalMixedMeasure (fun _ => θ) (fun _ => b) (fun _ => hb) univ
      = globalMixedMeasure (fun _ => θ) (fun _ => fun x => b x - (t : EReal)) (fun _ => hb')
          univ :=
        (congrArg (fun μ : Measure M => μ univ) hsub).symm
    _ ≤ _ := hle

end

end SGPT.Foundations.Analysis.Pending.DiagonalMassComparison
