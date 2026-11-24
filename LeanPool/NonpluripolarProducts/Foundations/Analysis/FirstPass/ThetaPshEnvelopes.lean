/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialIndependence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshSupremumRegularization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ThetaPshCompactBounds
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.UscRegularizationContinuous

/-!
# Theta-PSH upper envelopes

On a compact nonempty complex manifold, normalized theta-PSH competitors are
nonempty and uniformly bounded above by zero.  In a fixed chart and relative
to one fixed smooth local potential, their corrected representatives form a
locally uniformly bounded family of ordinary PSH functions.  The local PSH
supremum theorem therefore applies to their upper-semicontinuous regularized
supremum.

Naturality of regularization under charts and finite continuous corrections
then gives the global theta-PSH envelope.  The regularized normalized supremum
is itself a normalized competitor, which proves that the raw pointwise
supremum was already upper semicontinuous.  The same local argument proves the
singularity-type envelope theorem.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- Translation by a finite real value commutes with an arbitrary supremum in
`EReal`, including empty suprema and values at either infinity. -/
theorem iSup_add_coe {ι : Type*} (f : ι → EReal) (c : ℝ) :
    (⨆ i, f i + (c : EReal)) = (⨆ i, f i) + (c : EReal) := by
  apply le_antisymm
  · exact iSup_le fun i ↦ add_le_add (le_iSup f i) le_rfl
  · rw [← (EReal.addLECancellable_coe (-c)).add_le_add_iff_right]
    rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
    apply iSup_le
    intro i
    calc
      f i = (f i + (c : EReal)) + ((-c : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
      _ ≤ (⨆ j, f j + (c : EReal)) + ((-c : ℝ) : EReal) :=
        add_le_add (le_iSup (fun j ↦ f j + (c : EReal)) i) le_rfl

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Correct a family of manifold potentials by one fixed chart potential. -/
def chartCorrectedFamily (F : Set (M → EReal)) (e : ComplexChart n M)
    (ρ : ComplexModel n → ℝ) : Set (ComplexModel n → EReal) :=
  (fun u z ↦ chartFunction u e z + (ρ z : EReal)) '' F

omit [IsComplexManifold n M] in
/-- A corrected chart family is nonempty when the original family is. -/
theorem chartCorrectedFamily_nonempty {F : Set (M → EReal)}
    (hF : F.Nonempty) (e : ComplexChart n M) (ρ : ComplexModel n → ℝ) :
    (chartCorrectedFamily F e ρ).Nonempty := hF.image _

omit [IsComplexManifold n M] in
/-- Pointwise supremum commutes with the fixed finite chart correction. -/
theorem sSup_chartCorrectedFamily_apply (F : Set (M → EReal))
    (e : ComplexChart n M) (ρ : ComplexModel n → ℝ) (z : ComplexModel n) :
    sSup (chartCorrectedFamily F e ρ) z =
      chartFunction (sSup F) e z + (ρ z : EReal) := by
  simp only [chartCorrectedFamily, sSup_apply, iSup_subtype, iSup_image,
    chartFunction]
  change (⨆ b ∈ F, b (e.val.symm z) + (ρ z : EReal)) =
    (⨆ b ∈ F, b (e.val.symm z)) + (ρ z : EReal)
  rw [← iSup_subtype'' F (fun b ↦ b (e.val.symm z) + (ρ z : EReal)),
    ← iSup_subtype'' F (fun b ↦ b (e.val.symm z))]
  exact iSup_add_coe (fun b : F ↦ b.1 (e.val.symm z)) (ρ z)

/-- Change-of-potential independence puts every competitor into the same
ordinary PSH chart family. -/
theorem chartCorrectedFamily_plurisubharmonicOn
    {θ : SmoothRealForm n M 2} {F : Set (M → EReal)}
    (hF : ∀ u ∈ F, IsThetaPshPotential θ u)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ) :
    ∀ f ∈ chartCorrectedFamily F e ρ, PlurisubharmonicOn f W := by
  rintro f ⟨u, huF, rfl⟩
  intro x hx
  obtain ⟨V, σ, hxV, hσ, hpσ⟩ := (hF u huF).1 e x (hρ.2.1 hx)
  have hWV : IsOpen (W ∩ V) := hρ.1.inter hσ.1
  have hρ' := hρ.mono hWV inter_subset_left
  have hσ' := hσ.mono hWV inter_subset_right
  have hpρ : PlurisubharmonicOn
      (fun y ↦ chartFunction u e y + (ρ y : EReal)) (W ∩ V) :=
    (smoothLocalPotential_psh_iff θ e (W ∩ V) ρ σ hρ' hσ' (chartFunction u e)).mpr
      (hpσ.mono inter_subset_right)
  exact hpρ x ⟨hx, hxV⟩

omit [IsComplexManifold n M] in
/-- Nonpositive global competitors remain locally uniformly bounded after a
fixed smooth chart correction. -/
theorem chartCorrectedFamily_locallyUniformlyBoundedAbove
    {F : Set (M → EReal)} (hF0 : ∀ u ∈ F, u ≤ 0)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hW : IsOpen W) (hρ : ContDiffOn ℝ ∞ ρ W) :
    LocallyUniformlyBoundedAbove (chartCorrectedFamily F e ρ) W := by
  intro x hx
  have hρc : ContinuousAt ρ x :=
    ((hρ x hx).contDiffAt (hW.mem_nhds hx)).continuousAt
  have hU : {y | ρ y < ρ x + 1} ∈ 𝓝 x :=
    hρc (isOpen_Iio.mem_nhds (lt_add_one (ρ x)))
  refine ⟨{y | ρ y < ρ x + 1}, mem_nhdsWithin_of_mem_nhds hU, ρ x + 1, ?_⟩
  rintro f ⟨u, huF, rfl⟩ y ⟨hy, _hyW⟩
  calc
    chartFunction u e y + (ρ y : EReal) ≤ 0 + (ρ y : EReal) :=
      add_le_add (hF0 u huF (e.val.symm y)) le_rfl
    _ = (ρ y : EReal) := zero_add _
    _ ≤ ((ρ x + 1 : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hy.le

/-- The regularized supremum of a nonempty normalized theta-PSH family is
theta-PSH. -/
theorem thetaPlurisubharmonic_uscRegularization_sSup
    {θ : SmoothRealForm n M 2} {F : Set (M → EReal)}
    (hlocal : HasSmoothLocalPotentials θ) (hne : F.Nonempty)
    (hF : ∀ u ∈ F, IsThetaPshPotential θ u) (hF0 : ∀ u ∈ F, u ≤ 0) :
    ThetaPlurisubharmonic θ (uscRegularization (sSup F)) := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ⟩ := hlocal e z hz
  refine ⟨W, ρ, hzW, hρ, ?_⟩
  let G := chartCorrectedFamily F e ρ
  have hGne : G.Nonempty := chartCorrectedFamily_nonempty hne e ρ
  have hGpsh : ∀ g ∈ G, PlurisubharmonicOn g W :=
    chartCorrectedFamily_plurisubharmonicOn hF e hρ
  have hGbound : LocallyUniformlyBoundedAbove G W :=
    chartCorrectedFamily_locallyUniformlyBoundedAbove hF0 e hρ.1 hρ.2.2.1
  have hp := plurisubharmonicOn_uscRegularization_sSup hρ.1 hGne hGpsh hGbound
  intro x hx
  apply (hp x hx).congr
  filter_upwards [hρ.1.mem_nhds hx] with y hy
  change uscRegularization (sSup (chartCorrectedFamily F e ρ)) y = _
  rw [show sSup (chartCorrectedFamily F e ρ) =
      (fun t ↦ chartFunction (sSup F) e t + (ρ t : EReal)) by
    funext t
    exact sSup_chartCorrectedFamily_apply F e ρ t]
  rw [uscRegularization_add_coe_continuousAt_apply _
    (((hρ.2.2.1 y hy).contDiffAt (hρ.1.mem_nhds hy)).continuousAt)]
  rw [uscRegularization_chartFunction_apply _ e (hρ.2.1 hy)]

/-- The raw normalized pointwise supremum is already an actual theta-PSH
potential. -/
theorem thetaPshSupremum_isThetaPshPotential
    [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2)
    (hlocal : HasSmoothLocalPotentials θ) (hne : ∃ u, IsThetaPshPotential θ u) :
    IsThetaPshPotential θ (thetaPshSupremum θ) := by
  have hcomp : (thetaPshCompetitors θ).Nonempty := thetaPshCompetitors_nonempty θ hne
  have hstar : IsThetaPshPotential θ
      (uscRegularization (thetaPshSupremum θ)) := by
    refine ⟨?_, ?_⟩
    · simpa only [thetaPshSupremum] using
        thetaPlurisubharmonic_uscRegularization_sSup hlocal hcomp
          (fun _ hu ↦ hu.1) (fun _ hu ↦ hu.2)
    · exact (thetaPshSupremum_locallyNondegenerate hcomp).mono
        (le_uscRegularization (thetaPshSupremum θ))
  have hstar0 : uscRegularization (thetaPshSupremum θ) ≤ 0 :=
    uscRegularization_le upperSemicontinuous_const (thetaPshSupremum_le_zero θ)
  have hstarV : uscRegularization (thetaPshSupremum θ) ≤ thetaPshSupremum θ :=
    le_thetaPshSupremum hstar hstar0
  have heq : uscRegularization (thetaPshSupremum θ) = thetaPshSupremum θ :=
    le_antisymm hstarV (le_uscRegularization _)
  simpa only [heq] using hstar

/-- Every theta-PSH potential is more singular than the normalized supremum. -/
theorem thetaPshSupremum_minimalSingularities
    [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2)
    (u : M → EReal) (hu : IsThetaPshPotential θ u) :
    MoreSingularOn u (thetaPshSupremum θ) univ := by
  obtain ⟨C, hC⟩ := hu.exists_normalized_sub_const
  exact (sameSingularityTypeOn_add_const u univ (-C)).2.trans <|
    MoreSingularOn.of_le fun x _ ↦ by
      simpa only [sub_eq_add_neg, EReal.coe_neg] using
        le_thetaPshSupremum hC.1 hC.2 x

/-- The upper-semicontinuous singularity-type envelope of an actual theta-PSH
potential is again an actual theta-PSH potential. -/
theorem singularityEnvelope_isThetaPshPotential
    [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal)
    (hφ : IsThetaPshPotential θ φ) :
    IsThetaPshPotential θ (singularityEnvelope θ φ) := by
  have hcomp : (singularityCompetitors θ φ).Nonempty :=
    singularityCompetitors_nonempty hφ
  refine ⟨?_, singularityEnvelope_locallyNondegenerate hcomp⟩
  simpa only [singularityEnvelope, singularitySupremum] using
    thetaPlurisubharmonic_uscRegularization_sSup hlocal hcomp
      (fun _ hu ↦ hu.1.1) (fun _ hu ↦ hu.1.2)

end

end SGPT.Foundations.Analysis.FirstPass
