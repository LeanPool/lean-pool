/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BoundedGlobalProduct
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalPotentials
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ThetaPshCompactBounds
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PositiveClasses

/-!
# Bounded global truncations in a semipositive background

In a semipositive background the constants are `θ`-PSH, so the truncation
`max(u, c)` of a raw `θ`-PSH potential is again raw `θ`-PSH; on a nonempty
compact manifold it is moreover globally bounded, the upper bound coming from
upper semicontinuity of `u` and the lower bound from the truncation level
itself. Combined with `Pending.BoundedGlobalProduct` this produces, for every
truncation level, a global mixed non-pluripolar measure of finite total mass.

This is `gnpp:bounded-global-truncation` with the semipositivity supplied as a
hypothesis rather than obtained from a Kähler background: the passage from an
arbitrary closed real `(1,1)`-form to `θ + Aω` (`gnpp:kahler-domination`) is a
separate geometric statement and is not proved here.
-/

@[expose] public section

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct

open FirstPass FirstPass.GlobalPotentialPatches
open GlobalNonPluripolar

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The chart correction of a raw `θ`-PSH potential by *any* smooth local
potential of `θ` is PSH, not only by the one produced with it. This is the
single-function form of `chartCorrectedFamily_plurisubharmonicOn`, and needs no
nondegeneracy. -/
theorem ThetaPlurisubharmonic.corrected_plurisubharmonicOn
    {θ : SmoothRealForm n M 2} {u : M → EReal} (hu : ThetaPlurisubharmonic θ u)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ) :
    PlurisubharmonicOn (fun y => chartFunction u e y + (ρ y : EReal)) W := by
  intro x hx
  obtain ⟨V, σ, hxV, hσ, hpσ⟩ := hu e x (hρ.2.1 hx)
  have hWV : IsOpen (W ∩ V) := hρ.1.inter hσ.1
  have hpρ : PlurisubharmonicOn (fun y => chartFunction u e y + (ρ y : EReal)) (W ∩ V) :=
    (smoothLocalPotential_psh_iff θ e (W ∩ V) ρ σ (hρ.mono hWV inter_subset_left)
      (hσ.mono hWV inter_subset_right) (chartFunction u e)).mpr
      (hpσ.mono inter_subset_right)
  exact hpρ x ⟨hx, hxV⟩

/-- **The pointwise maximum of two raw theta-PSH potentials is raw theta-PSH.**
The corresponding statement for nondegenerate potentials is
`Pending.IsThetaPshPotential.max`; here neither factor is assumed
nondegenerate, which is what the truncation `max(u, c)` needs. -/
theorem ThetaPlurisubharmonic.max {θ : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) (hv : ThetaPlurisubharmonic θ v) :
    ThetaPlurisubharmonic θ (fun x => Max.max (u x) (v x)) := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ, _⟩ := hu e z hz
  refine ⟨W, ρ, hzW, hρ, ?_⟩
  have h1 := ThetaPlurisubharmonic.corrected_plurisubharmonicOn hu e hρ
  have h2 := ThetaPlurisubharmonic.corrected_plurisubharmonicOn hv e hρ
  convert h1.max h2 using 2 with y
  exact (max_add_add_right _ _ _).symm

/-- In a semipositive background every finite constant is raw theta-PSH. -/
theorem thetaPlurisubharmonic_const (a : ClosedRealOneOneForm n M)
    (ha : a.val.IsSemipositive) (c : ℝ) :
    ThetaPlurisubharmonic a.val (fun _ : M => (c : EReal)) := by
  have h0 : ThetaPlurisubharmonic a.val (fun _ : M => (0 : EReal)) :=
    (LocalPotentials.thetaPlurisubharmonic_zero_iff a).mpr ha
  have h := PositiveClasses.thetaPlurisubharmonic_sub_const h0 (-c)
  simpa using h

/-- **Truncation preserves raw theta-PSH in a semipositive background.** -/
theorem thetaPlurisubharmonic_max_const {a : ClosedRealOneOneForm n M} {u : M → EReal}
    (ha : a.val.IsSemipositive) (hu : ThetaPlurisubharmonic a.val u) (c : ℝ) :
    ThetaPlurisubharmonic a.val (fun x => Max.max (u x) ((c : ℝ) : EReal)) :=
  ThetaPlurisubharmonic.max hu (thetaPlurisubharmonic_const a ha c)

variable [CompactSpace M] [Nonempty M]

/-- **Truncations of a raw theta-PSH potential are globally bounded** on a
nonempty compact manifold: below by the truncation level, above by the global
upper bound coming from upper semicontinuity. No semipositivity is used. -/
theorem isBoundedPotential_max_const {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) (c : ℝ) :
    IsBoundedPotential (fun x => Max.max (u x) ((c : ℝ) : EReal)) := by
  obtain ⟨C, hC⟩ := FirstPass.ThetaPlurisubharmonic.exists_global_upper_bound hu
  refine ⟨c, Max.max C c, fun x => ⟨le_max_right _ _, ?_⟩⟩
  have hC' : ((C : ℝ) : EReal) ≤ ((Max.max C c : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr (le_max_left C c)
  have hc' : ((c : ℝ) : EReal) ≤ ((Max.max C c : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr (le_max_right C c)
  exact max_le ((hC x).trans hC') hc'

end

end SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct

namespace SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct

open FirstPass FirstPass.GlobalPotentialPatches GlobalNonPluripolar

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

/-- The truncated tuple is raw theta-PSH for the same semipositive backgrounds. -/
theorem thetaPlurisubharmonic_truncation
    (ha : ∀ i, (θ i).val.IsSemipositive) (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (c : Fin n → ℝ) (i : Fin n) :
    ThetaPlurisubharmonic (θ i).val (fun x => Max.max (u i x) ((c i : ℝ) : EReal)) :=
  thetaPlurisubharmonic_max_const (ha i) (hu i) (c i)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

/-- **The global mixed measure of a truncated tuple has finite total mass.**
This is the measure `ν_l` of the BEGZ uniform-mass argument: it exists, is
glued from genuine bounded local Bedford–Taylor products, and is finite. Its
independence of the truncation levels is a separate integration-by-parts
statement and is not asserted here. -/
theorem globalMixedMeasure_truncation_isFiniteMeasure
    (ha : ∀ i, (θ i).val.IsSemipositive) (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (c : Fin n → ℝ) :
    IsFiniteMeasure (globalMixedMeasure θ (fun i x => Max.max (u i x) ((c i : ℝ) : EReal))
      (thetaPlurisubharmonic_truncation ha hu c)) :=
  globalMixedMeasure_isFiniteMeasure_of_bounded _
    (fun i => isBoundedPotential_max_const (hu i) (c i))

theorem globalMixedMeasure_truncation_apply_lt_top
    (ha : ∀ i, (θ i).val.IsSemipositive) (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (c : Fin n → ℝ) (S : Set M) :
    globalMixedMeasure θ (fun i x => Max.max (u i x) ((c i : ℝ) : EReal))
      (thetaPlurisubharmonic_truncation ha hu c) S < ⊤ :=
  globalMixedMeasure_apply_lt_top_of_bounded _
    (fun i => isBoundedPotential_max_const (hu i) (c i)) S

end

end SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
