/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ThetaCapacityChart
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PatchLocalBoundedMeasure

/-!
# The chart bridge for the global capacity, from a bound on one chart only

`Pending.ThetaCapacityChart.thetaCapacity_le_relCapacity` compares Xia's
`Cap_theta(-, V)` with Blocki's relative capacity in a chart, but only for a
reference `V` that is bounded on **all** of `M`.  I-0282 records why that is
not a technicality: `V_theta` is unbounded below exactly when
`nK({theta}) != emptyset`, and then *every* `theta`-PSH potential is unbounded
below (`Pending.ThetaCapacityBoundedDegeneracy`), so the hypothesis
`IsBoundedPotential` is unsatisfiable and the whole Section 2.3 stack is
vacuous in the only case Nakamaye's theorem is about.

`Pending.PatchLocalBoundedMeasure` removed the same global bound from the
*measure* half: a bound on the source of a single patch already puts
`globalMixedMeasure` in honest Bedford--Taylor form there.  This module carries
that through the *capacity* half, which is what its own header says was left
open.  Every statement below is the corresponding statement of
`Pending.ThetaCapacityChart` with `IsBoundedPotential` replaced by a bound on
the slot-chart source.

Why that is enough for Xia.  His Theorem 2.4.4 runs on open sets
`G' <<- G <<- X \ nK({theta})`, and there both `V_theta` and `P_theta(f)` are
locally bounded by his Lemma 2.4.1 -- available here as
`Pending.BigClassEnvelopeContact.exists_isBoundedPotentialOn_offNonKahlerLocus`.
Local boundedness is exactly the hypothesis below.

No new analysis is introduced: the Bedford--Taylor / Blocki estimate
`canonicalBedfordTaylorMeasure_le_relCapacity_of_bounds` is used unchanged, and
the only genuinely new step is that the local model of the global measure is
taken from `PatchLocalBoundedMeasure` rather than from
`GlobalSlotStokes.SlotChart.exists_isBTLimit`.
-/

@[expose] public section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ThetaCapacityChartLocal

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
open FirstPass.MongeAmpere
open GlobalNonPluripolar BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacityChart

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- **The corrected chart potential is real locally bounded plurisubharmonic,
from a bound on the chart domain only.**  This is
`ThetaCapacityChart.correctedChartReal_isLocallyBoundedPshOn` with the global
bound on `u` replaced by a bound at the points `e⁻¹(D)`. -/
theorem correctedChartReal_isLocallyBoundedPshOn_of_boundedOn
    {theta : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : ThetaPlurisubharmonic theta.val u) {e : ComplexChart n M}
    {D : Opens (ComplexModel n)} {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential theta.val e D rho) {c d L : ℝ}
    (hbd : ∀ z ∈ (D : Set (ComplexModel n)),
      (c : EReal) ≤ u (e.val.symm z) ∧ u (e.val.symm z) ≤ (d : EReal))
    (hL : ∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L) :
    IsLocallyBoundedPshOn D (correctedChartReal u e rho) := by
  have hcoe : ∀ z ∈ (D : Set (ComplexModel n)),
      ((u (e.val.symm z)).toReal : EReal) = u (e.val.symm z) := by
    intro z hz
    exact EReal.coe_toReal (ne_of_lt ((hbd z hz).2.trans_lt (EReal.coe_lt_top d)))
      (ne_of_gt ((EReal.bot_lt_coe c).trans_le (hbd z hz).1))
  have hpsh0 := ThetaPlurisubharmonic.corrected_plurisubharmonicOn hu e hrho
  have heq : EqOn (fun z => chartFunction u e z + ((rho z : ℝ) : EReal))
      (fun z => ((correctedChartReal u e rho z : ℝ) : EReal))
      (D : Set (ComplexModel n)) := by
    intro z hz
    change chartFunction u e z + ((rho z : ℝ) : EReal) =
      ((((u (e.val.symm z)).toReal + rho z : ℝ)) : EReal)
    rw [EReal.coe_add, hcoe z hz]
    rfl
  have hpsh : PlurisubharmonicOn
      (fun z => ((correctedChartReal u e rho z : ℝ) : EReal))
      (D : Set (ComplexModel n)) :=
    SGPT.Foundations.Analysis.plurisubharmonicOn_congr D.isOpen hpsh0 heq
  refine isLocallyBoundedPshOn_of_abs_le hpsh (C := |c - L| + |d + L|) ?_
  intro z hz
  obtain ⟨h1, h2⟩ := hbd z hz
  have hr : ((u (e.val.symm z)).toReal : EReal) = u (e.val.symm z) := hcoe z hz
  have hc1 : c ≤ (u (e.val.symm z)).toReal := EReal.coe_le_coe_iff.mp (hr ▸ h1)
  have hc2 : (u (e.val.symm z)).toReal ≤ d := EReal.coe_le_coe_iff.mp (hr ▸ h2)
  have h3 := abs_le.mp (hL z hz)
  have hval : correctedChartReal u e rho z = (u (e.val.symm z)).toReal + rho z := rfl
  refine abs_le.mpr ⟨?_, ?_⟩
  · have := neg_abs_le (c - L); have := abs_nonneg (d + L); rw [hval]; linarith
  · have := le_abs_self (d + L); have := abs_nonneg (c - L); rw [hval]; linarith

/-- **The local Bedford--Taylor model of the global measure on a slot chart,
from a bound on the slot-chart source only.**  Compare
`GlobalSlotStokes.SlotChart.exists_isBTLimit`. -/
theorem exists_isBTLimit_of_boundedOn
    {η : Fin n → ClosedRealOneOneForm n M} {κ : ClosedRealOneOneForm n M}
    (J : SlotChart η κ) {u : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (η i).val (u i))
    (hb : ∀ i, IsBoundedPotentialOn (u i) (J.source : Set M)) :
    ∃ μ : Measure (ComplexModel n),
      IsBTLimit J.domain
        (fun i z => (u i (J.chart.val.symm z)).toReal + J.potential i z) μ ∧
      (globalMixedMeasure η u hu).restrict (J.source : Set M) =
        (J.patch u hu).pushMeasure μ := by
  set P := J.patch u hu with hP
  have hb' : ∀ i, IsBoundedPotentialOn (u i) (P.source : Set M) := hb
  refine ⟨canonicalMixedBedfordTaylorMeasure P.domain (correctedReal P)
    (correctedReal_isLocallyBoundedMixedPshOn_of_boundedOn P hb'), ?_,
    globalMixedMeasure_restrict_patch_eq_canonical_of_boundedOn hu P hb'⟩
  have h := IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (canonicalMixedBedfordTaylorMeasure_spec P.domain (correctedReal P)
      (correctedReal_isLocallyBoundedMixedPshOn_of_boundedOn P hb'))
  exact h.congr fun i z hz => correctedReal_eq_of_boundedOn (hb' i) hz

/-- **One competitor, from a bound on the chart source only.**  The diagonal
non-pluripolar measure of a `theta`-PSH potential bounded on the slot-chart
source is dominated there by Blocki's relative capacity of the coordinate
image. -/
theorem diagonalPotentialMeasure_le_relCapacity_of_boundedOn
    {theta : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (e : ComplexChart n M) (D : Opens (ComplexModel n))
    (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (rho : ComplexModel n → ℝ)
    (hrho : IsSmoothLocalPotential theta.val e D rho)
    {c d L : ℝ} (hcd : c ≤ d) (hL0 : 0 ≤ L)
    (hbd : ∀ x ∈ ((diagSlotChart theta e D hD rho hrho).source : Set M),
      (c : EReal) ≤ u x ∧ u x ≤ (d : EReal))
    (hL : ∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L)
    (E : Set M)
    (hE : E ⊆ (diagSlotChart theta e D hD rho hrho).source) :
    diagonalPotentialMeasure theta u hu E ≤
      ENNReal.ofReal ((d - c + 2 * L + 1) ^ n) * relCapacity D (e.val '' E) := by
  classical
  set J := diagSlotChart theta e D hD rho hrho with hJ
  have hbsrc : IsBoundedPotentialOn u (J.source : Set M) := ⟨c, d, hbd⟩
  have hbD : ∀ z ∈ (D : Set (ComplexModel n)),
      (c : EReal) ≤ u (e.val.symm z) ∧ u (e.val.symm z) ≤ (d : EReal) := by
    intro z hz
    exact hbd _ ((J.patch (fun _ => u) (fun _ => hu.1)).map_target hz)
  set g : ComplexModel n → ℝ := correctedChartReal u e rho with hg_def
  have hg : IsLocallyBoundedPshOn D g :=
    correctedChartReal_isLocallyBoundedPshOn_of_boundedOn hu.1 hrho hbD hL
  have hgbd : ∀ z ∈ (D : Set (ComplexModel n)), c - L ≤ g z ∧ g z ≤ d + L + 1 := by
    intro z hz
    obtain ⟨h1, h2⟩ := hbD z hz
    have hr : ((u (e.val.symm z)).toReal : EReal) = u (e.val.symm z) :=
      EReal.coe_toReal (ne_of_lt (h2.trans_lt (EReal.coe_lt_top d)))
        (ne_of_gt ((EReal.bot_lt_coe c).trans_le h1))
    have hc1 : c ≤ (u (e.val.symm z)).toReal := EReal.coe_le_coe_iff.mp (hr ▸ h1)
    have hc2 : (u (e.val.symm z)).toReal ≤ d := EReal.coe_le_coe_iff.mp (hr ▸ h2)
    have h3 := abs_le.mp (hL z hz)
    have hval : g z = (u (e.val.symm z)).toReal + rho z := rfl
    constructor <;> rw [hval] <;> linarith
  obtain ⟨mu, hmuBT, hmueq⟩ :=
    exists_isBTLimit_of_boundedOn J (u := fun _ => u) (fun _ => hu.1) (fun _ => hbsrc)
  have hfam : (fun (i : Fin n) (z : ComplexModel n) =>
      (u (J.chart.val.symm z)).toReal + J.potential i z) = fun _ => g := rfl
  rw [hfam] at hmuBT
  have hmu : mu = Pending.MongeAmpere.canonicalBedfordTaylorMeasure D g hg :=
    hmuBT.unique (isBTLimit_canonicalBedfordTaylorMeasure hg)
  have hsrc : E ⊆ ((J.patch (fun _ => u) (fun _ => hu.1)).source : Set M) := hE
  have hrestr : diagonalPotentialMeasure theta u hu E =
      ((diagonalPotentialMeasure theta u hu).restrict (J.source : Set M)) E := by
    rw [Measure.restrict_apply' J.source.isOpen.measurableSet,
      inter_eq_self_of_subset_left hE]
  have hval : diagonalPotentialMeasure theta u hu E = mu (e.val '' E) := by
    rw [hrestr]
    change ((globalMixedMeasure (fun _ : Fin n => theta) (fun _ => u)
      (fun _ => hu.1)).restrict (J.source : Set M)) E = _
    rw [hmueq, Patch.pushMeasure_apply_image, inter_eq_self_of_subset_left hsrc]
    rfl
  rw [hval, hmu]
  have hfin := canonicalBedfordTaylorMeasure_le_relCapacity_of_bounds hg
    (show c - L < d + L + 1 by linarith) hgbd (e.val '' E)
  have harith : d + L + 1 - (c - L) = d - c + 2 * L + 1 := by ring
  rwa [harith] at hfin

/-- **The chart bridge, from a bound on the chart source only.**  Xia's
`Cap_theta(-, V)` is dominated on a slot chart by Blocki's relative capacity,
assuming only that the reference `V` is bounded on the slot-chart source.  This
is `ThetaCapacityChart.thetaCapacity_le_relCapacity` with the global hypothesis
on `V` localized, which is what makes it applicable to `V_theta` away from
`nK({theta})`. -/
theorem thetaCapacity_le_relCapacity_of_boundedOn
    {theta : ClosedRealOneOneForm n M} {V : M → EReal}
    (e : ComplexChart n M) (D : Opens (ComplexModel n))
    (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (rho : ComplexModel n → ℝ)
    (hrho : IsSmoothLocalPotential theta.val e D rho)
    {c d L : ℝ} (hcd : c ≤ d) (hL0 : 0 ≤ L)
    (hVbd : ∀ x ∈ ((diagSlotChart theta e D hD rho hrho).source : Set M),
      (c : EReal) ≤ V x ∧ V x ≤ (d : EReal))
    (hL : ∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L)
    (E : Set M)
    (hE : E ⊆ (diagSlotChart theta e D hD rho hrho).source) :
    thetaCapacity theta V E ≤
      ENNReal.ofReal ((d - c + 2 * L + 2) ^ n) * relCapacity D (e.val '' E) := by
  refine thetaCapacity_le_of_forall fun u hu h1 h2 => ?_
  have hbd : ∀ x ∈ ((diagSlotChart theta e D hD rho hrho).source : Set M),
      ((c - 1 : ℝ) : EReal) ≤ u x ∧ u x ≤ (d : EReal) := by
    intro x hx
    refine ⟨?_, (h1 x).trans (hVbd x hx).2⟩
    have hchain : (c : EReal) ≤ u x + 1 := (hVbd x hx).1.trans (h2 x)
    have hne : u x ≠ ⊥ := by
      intro hbot
      rw [hbot] at hchain
      simp at hchain
    have hnt : u x ≠ ⊤ :=
      SGPT.Foundations.Analysis.Pending.DominationPrincipleBarrier.ne_top_of_isThetaPshPotential
        hu x
    obtain ⟨r, hr⟩ : ∃ r : ℝ, u x = (r : EReal) :=
      ⟨(u x).toReal, (EReal.coe_toReal hnt hne).symm⟩
    rw [hr] at hchain ⊢
    rw [← EReal.coe_one, ← EReal.coe_add, EReal.coe_le_coe_iff] at hchain
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  have hmain := diagonalPotentialMeasure_le_relCapacity_of_boundedOn hu e D hD rho hrho
    (c := c - 1) (d := d) (L := L) (by linarith) hL0 hbd hL E hE
  have harith : d - (c - 1) + 2 * L + 1 = d - c + 2 * L + 2 := by ring
  rwa [harith] at hmain

end

end SGPT.Foundations.Analysis.Pending.ThetaCapacityChartLocal
