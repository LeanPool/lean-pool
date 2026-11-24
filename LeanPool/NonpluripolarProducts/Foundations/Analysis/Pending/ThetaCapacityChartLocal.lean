/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ThetaCapacity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalSlotStokes
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorCapacity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PatchLocalBoundedMeasure

/-!
# Comparing global non-pluripolar and local Bedford–Taylor capacity

On a coordinate chart, a two-sided bound on the reference potential and a
bound on the chart potential yield a uniform oscillation estimate for every
competitor. The local model from `PatchLocalBoundedMeasure` identifies each
competitor's diagonal non-pluripolar measure with its Bedford–Taylor measure
on the chart. The capacity comparison then follows from Błocki's estimate
`canonicalBedfordTaylorMeasure_le_relCapacity_of_bounds`.

The chart-local comparison applies off the non-Kähler locus, where the
reference and envelope are locally bounded in Xia's Theorem 2.4.4. The
corollaries for globally bounded references use the same comparison.
-/

@[expose] public section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
open FirstPass.MongeAmpere
open GlobalNonPluripolar BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.ThetaCapacity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

namespace ThetaCapacityChart

/-- The slot chart in which every slot carries the same background `theta` and
the same smooth local potential `rho`. -/
def diagSlotChart (theta : ClosedRealOneOneForm n M) (e : ComplexChart n M)
    (D : Opens (ComplexModel n)) (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (rho : ComplexModel n → ℝ)
    (hrho : IsSmoothLocalPotential theta.val e D rho) :
    SlotChart (fun _ : Fin n => theta) theta where
  chart := e
  domain := D
  domain_le_target := hD
  potential := fun _ => rho
  localPotential := fun _ => hrho
  kahler := rho
  kahlerLocal := hrho

/-- The real corrected chart potential of a bounded potential: the potential
read in the chart plus a smooth local potential of the background.

This is the same function as `BoundedGlobalProduct.correctedReal` for the
patch of `diagSlotChart`, and the proof of
`diagonalPotentialMeasure_le_relCapacity` uses that identification (`hfam`,
by `rfl`).  It is kept as a separate chart-level definition only because
`correctedReal` is indexed by a `Patch`, which the quasi-continuity arguments
downstream would otherwise have to build merely to name this function. -/
def correctedChartReal (u : M → EReal) (e : ComplexChart n M)
    (rho : ComplexModel n → ℝ) : ComplexModel n → ℝ :=
  fun z => (u (e.val.symm z)).toReal + rho z

end ThetaCapacityChart

namespace ThetaCapacityChartLocal

open ThetaCapacityChart

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

end ThetaCapacityChartLocal

namespace ThetaCapacityChart

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [IsComplexManifold n M] in
theorem coe_correctedChartReal {u : M → EReal} (hub : IsBoundedPotential u)
    (e : ComplexChart n M) (rho : ComplexModel n → ℝ) (z : ComplexModel n) :
    ((correctedChartReal u e rho z : ℝ) : EReal) =
      chartFunction u e z + (rho z : EReal) := by
  change ((((u (e.val.symm z)).toReal + rho z : ℝ)) : EReal) = _
  rw [EReal.coe_add, EReal.coe_toReal (hub.ne_top _) (hub.ne_bot _)]
  rfl

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [IsComplexManifold n M] in
/-- Two-sided bounds for the corrected chart potential. -/
theorem correctedChartReal_bounds {u : M → EReal} (hub : IsBoundedPotential u)
    {e : ComplexChart n M} {rho : ComplexModel n → ℝ} {c d L : ℝ}
    (hbd : ∀ x, (c : EReal) ≤ u x ∧ u x ≤ (d : EReal))
    {S : Set (ComplexModel n)} (hL : ∀ z ∈ S, |rho z| ≤ L) (z : ComplexModel n)
    (hz : z ∈ S) :
    c - L ≤ correctedChartReal u e rho z ∧
      correctedChartReal u e rho z ≤ d + L := by
  have hru : ((u (e.val.symm z)).toReal : EReal) = u (e.val.symm z) :=
    EReal.coe_toReal (hub.ne_top _) (hub.ne_bot _)
  have h1 : c ≤ (u (e.val.symm z)).toReal :=
    EReal.coe_le_coe_iff.mp (hru ▸ (hbd (e.val.symm z)).1)
  have h2 : (u (e.val.symm z)).toReal ≤ d :=
    EReal.coe_le_coe_iff.mp (hru ▸ (hbd (e.val.symm z)).2)
  have h3 := abs_le.mp (hL z hz)
  constructor <;> simp only [correctedChartReal] <;> linarith

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- **The corrected chart potential is real locally bounded plurisubharmonic.**
Plurisubharmonicity is the `theta`-PSH property read in the chart; the bound
combines the global bound on `u` with the assumed bound on `rho`. -/
theorem correctedChartReal_isLocallyBoundedPshOn {theta : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : ThetaPlurisubharmonic theta.val u)
    {e : ComplexChart n M}
    {D : Opens (ComplexModel n)} {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential theta.val e D rho) {c d L : ℝ}
    (hbd : ∀ x, (c : EReal) ≤ u x ∧ u x ≤ (d : EReal))
    (hL : ∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L) :
    IsLocallyBoundedPshOn D (correctedChartReal u e rho) :=
  ThetaCapacityChartLocal.correctedChartReal_isLocallyBoundedPshOn_of_boundedOn hu hrho
    (fun z _ => hbd (e.val.symm z)) hL

/-- **One competitor.**  The diagonal non-pluripolar measure of a globally
bounded `theta`-PSH potential is dominated on a chart neighbourhood by the
relative Monge--Ampere capacity of the coordinate image. -/
theorem diagonalPotentialMeasure_le_relCapacity
    {theta : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (e : ComplexChart n M) (D : Opens (ComplexModel n))
    (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (rho : ComplexModel n → ℝ)
    (hrho : IsSmoothLocalPotential theta.val e D rho)
    {c d L : ℝ} (hcd : c ≤ d) (hL0 : 0 ≤ L)
    (hbd : ∀ x, (c : EReal) ≤ u x ∧ u x ≤ (d : EReal))
    (hL : ∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L)
    (E : Set M)
    (hE : E ⊆ (diagSlotChart theta e D hD rho hrho).source) :
    diagonalPotentialMeasure theta u hu E ≤
      ENNReal.ofReal ((d - c + 2 * L + 1) ^ n) * relCapacity D (e.val '' E) :=
  ThetaCapacityChartLocal.diagonalPotentialMeasure_le_relCapacity_of_boundedOn hu e D hD rho hrho
    hcd hL0 (fun x _ => hbd x) hL E hE

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Every competitor of the capacity relative to `V` inherits the lower bound
of `V`, shifted by one.  The pole case is excluded: `V x <= u x + 1` with
`c <= V x` forces `u x` finite. -/
theorem competitor_ge_of_reference_ge {theta : ClosedRealOneOneForm n M}
    {V u : M → EReal} (hu : IsThetaPshPotential theta.val u) {c : ℝ}
    (hc : ∀ x, (c : EReal) ≤ V x) (h2 : ∀ x, V x ≤ u x + 1) (x : M) :
    ((c - 1 : ℝ) : EReal) ≤ u x := by
  have hchain : (c : EReal) ≤ u x + 1 := (hc x).trans (h2 x)
  have hne : u x ≠ ⊥ := by
    intro hbot
    rw [hbot] at hchain
    simp at hchain
  have hnt : u x ≠ ⊤ :=
    SGPT.Foundations.Analysis.Pending.DominationPrincipleBarrier.ne_top_of_isThetaPshPotential hu x
  obtain ⟨r, hr⟩ : ∃ r : ℝ, u x = (r : EReal) :=
    ⟨(u x).toReal, (EReal.coe_toReal hnt hne).symm⟩
  rw [hr] at hchain ⊢
  rw [← EReal.coe_one, ← EReal.coe_add, EReal.coe_le_coe_iff] at hchain
  exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- **The global capacity is controlled by the chart capacity.**  On a chart
neighbourhood carrying a bounded smooth local potential of `theta`, and for a
globally bounded reference `V`, Xia's `Cap_theta(-, V)` is dominated by a
constant multiple of the relative Monge--Ampere capacity of the coordinate
image.  The constant depends only on the oscillation bound of `V` and the
bound on the local potential, not on the competitor. -/
theorem thetaCapacity_le_relCapacity
    {theta : ClosedRealOneOneForm n M} {V : M → EReal}
    (e : ComplexChart n M) (D : Opens (ComplexModel n))
    (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (rho : ComplexModel n → ℝ)
    (hrho : IsSmoothLocalPotential theta.val e D rho)
    {c d L : ℝ} (hcd : c ≤ d) (hL0 : 0 ≤ L)
    (hVbd : ∀ x, (c : EReal) ≤ V x ∧ V x ≤ (d : EReal))
    (hL : ∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L)
    (E : Set M)
    (hE : E ⊆ (diagSlotChart theta e D hD rho hrho).source) :
    thetaCapacity theta V E ≤
      ENNReal.ofReal ((d - c + 2 * L + 2) ^ n) * relCapacity D (e.val '' E) :=
  ThetaCapacityChartLocal.thetaCapacity_le_relCapacity_of_boundedOn e D hD rho hrho
    hcd hL0 (fun x _ => hVbd x) hL E hE

/-- A set inside a chart neighbourhood whose coordinate image has zero relative
capacity has zero global capacity. -/
theorem thetaCapacity_eq_zero_of_relCapacity_eq_zero
    {theta : ClosedRealOneOneForm n M} {V : M → EReal}
    (e : ComplexChart n M) (D : Opens (ComplexModel n))
    (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (rho : ComplexModel n → ℝ)
    (hrho : IsSmoothLocalPotential theta.val e D rho)
    {c d L : ℝ} (hcd : c ≤ d) (hL0 : 0 ≤ L)
    (hVbd : ∀ x, (c : EReal) ≤ V x ∧ V x ≤ (d : EReal))
    (hL : ∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L)
    (E : Set M)
    (hE : E ⊆ (diagSlotChart theta e D hD rho hrho).source)
    (hzero : relCapacity D (e.val '' E) = 0) :
    thetaCapacity theta V E = 0 := by
  refine le_antisymm ?_ zero_le
  simpa [hzero] using
    thetaCapacity_le_relCapacity e D hD rho hrho hcd hL0 hVbd hL E hE

end ThetaCapacityChart

end

end SGPT.Foundations.Analysis.Pending
