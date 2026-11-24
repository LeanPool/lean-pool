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

/-!
# The global capacity is controlled by the chart capacity

This is the bridge that makes the local Bedford--Taylor / Blocki stack of
`Pending.BedfordTaylorCapacity` and `Pending.BedfordTaylorQuasiContinuity`
usable for Xia's global `Cap_theta` (`Pending.ThetaCapacity`).

Fix a chart `e`, a coordinate domain `D` on which `theta` has a smooth local
potential `rho`, and assume `|rho| <= L` on `D` (always achievable after
shrinking `D`, since `rho` is smooth hence continuous).  Let `V` be a
*globally bounded* `theta`-PSH potential, say `c <= V <= d`.  Then every
competitor `u` of `Cap_theta(-, V)` satisfies `c - 1 <= u <= d`, so its
corrected chart potential `u o e^{-1} + rho` is a real plurisubharmonic
function on `D` with oscillation at most `d - c + 1 + 2 L`, and the global
non-pluripolar measure `theta^n_u` restricted to the chart neighbourhood is
its Bedford--Taylor measure
(`Pending.GlobalSlotStokes.SlotChart.exists_isBTLimit`).  Blocki's domination
of the Bedford--Taylor measure by the relative capacity
(`canonicalBedfordTaylorMeasure_le_relCapacity_of_bounds`) then gives, for
every `E` inside the chart neighbourhood,

  `Cap_theta(E, V) <= (d - c + 2 L + 2)^n * c(e(E), D)`.

The constant is uniform in the competitor, which is the whole point: the
supremum defining the capacity can be taken after the estimate.

**What the boundedness of `V` costs.**  The hypothesis is a genuine
restriction, not a technicality.  Xia's own reference is `V_theta`, which is
bounded above by `0` but is unbounded below exactly when
`nK({theta}) != emptyset` -- the case this project is about.  So
`ThetaCapacity.thetaCapacityV` cannot be substituted here, and what is proved
is Section 2.3 *relative to a globally bounded reference*.  Xia avoids the
issue by working on open sets relatively compact in `X \ nK({theta})`, where
Lemma 2.4.1 makes `V_theta` locally bounded; that is a different architecture
from the global, `[CompactSpace M]`-wide statements here, and the global bound
is forced by `GlobalSlotStokes.SlotChart.exists_isBTLimit`, which identifies
the global measure with a chart Bedford--Taylor measure only for a globally
bounded potential.  Lifting the restriction means restating the whole stack
relative to an open subset, not adding a lemma.
-/

@[expose] public section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ThetaCapacityChart

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
open FirstPass.MongeAmpere
open GlobalNonPluripolar BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
open SGPT.Foundations.Analysis.Pending.ThetaCapacity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

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
    (hub : IsBoundedPotential u) {e : ComplexChart n M}
    {D : Opens (ComplexModel n)} {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential theta.val e D rho) {c d L : ℝ}
    (hbd : ∀ x, (c : EReal) ≤ u x ∧ u x ≤ (d : EReal))
    (hL : ∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L) :
    IsLocallyBoundedPshOn D (correctedChartReal u e rho) := by
  have hpsh : PlurisubharmonicOn
      (fun z => ((correctedChartReal u e rho z : ℝ) : EReal))
      (D : Set (ComplexModel n)) := by
    have h := ThetaPlurisubharmonic.corrected_plurisubharmonicOn hu e hrho
    simpa only [funext (coe_correctedChartReal hub e rho)] using h
  refine isLocallyBoundedPshOn_of_abs_le hpsh (C := |c - L| + |d + L|) ?_
  intro z hz
  obtain ⟨h1, h2⟩ := correctedChartReal_bounds hub hbd hL z hz
  refine abs_le.mpr ⟨?_, ?_⟩
  · have := neg_abs_le (c - L); have := abs_nonneg (d + L); linarith
  · have := le_abs_self (d + L); have := abs_nonneg (c - L); linarith

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
      ENNReal.ofReal ((d - c + 2 * L + 1) ^ n) * relCapacity D (e.val '' E) := by
  classical
  set J := diagSlotChart theta e D hD rho hrho with hJ
  have hub : IsBoundedPotential u := ⟨c, d, hbd⟩
  -- the corrected chart potential
  set g : ComplexModel n → ℝ := correctedChartReal u e rho with hg_def
  have hg : IsLocallyBoundedPshOn D g :=
    correctedChartReal_isLocallyBoundedPshOn hu.1 hub hrho hbd hL
  have hgbd : ∀ z ∈ (D : Set (ComplexModel n)), c - L ≤ g z ∧ g z ≤ d + L + 1 := by
    intro z hz
    obtain ⟨h1, h2⟩ := correctedChartReal_bounds hub hbd hL z hz
    exact ⟨h1, by linarith⟩
  -- the local model of the global measure
  obtain ⟨mu, hmuBT, hmueq⟩ :=
    SlotChart.exists_isBTLimit J (u := fun _ => u) (fun _ => hu.1) (fun _ => hub)
  have hfam : (fun (i : Fin n) (z : ComplexModel n) =>
      (u (J.chart.val.symm z)).toReal + J.potential i z) = fun _ => g := rfl
  rw [hfam] at hmuBT
  have hmu : mu = Pending.MongeAmpere.canonicalBedfordTaylorMeasure D g hg :=
    hmuBT.unique (isBTLimit_canonicalBedfordTaylorMeasure hg)
  -- read the global measure through the patch
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
      ENNReal.ofReal ((d - c + 2 * L + 2) ^ n) * relCapacity D (e.val '' E) := by
  refine thetaCapacity_le_of_forall fun u hu h1 h2 => ?_
  have hlow : ∀ x, ((c - 1 : ℝ) : EReal) ≤ u x :=
    competitor_ge_of_reference_ge hu (fun x => (hVbd x).1) h2
  have hhigh : ∀ x, u x ≤ (d : EReal) := fun x => (h1 x).trans (hVbd x).2
  have hmain := diagonalPotentialMeasure_le_relCapacity hu e D hD rho hrho
    (c := c - 1) (d := d) (L := L) (by linarith) hL0
    (fun x => ⟨hlow x, hhigh x⟩) hL E hE
  have harith : d - (c - 1) + 2 * L + 1 = d - c + 2 * L + 2 := by ring
  rwa [harith] at hmain

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

end

end SGPT.Foundations.Analysis.Pending.ThetaCapacityChart
