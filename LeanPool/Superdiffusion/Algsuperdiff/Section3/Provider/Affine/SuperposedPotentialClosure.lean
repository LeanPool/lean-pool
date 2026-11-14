/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.SuperposedPotentialL2

/-!
# SuperposedPotentialClosure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A closed-`L²` representative for the superposed potential field

This file passes from the Cauchy sequence of finite bad-component prefixes to
the full superposed slope defect.  The limit is kept in the canonical closed
zero-trace potential subspace, identified almost everywhere with the raw
superposition, and then represented using CoarseGraining's closed-range theorem
on open cubes.
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport Set MeasureTheory
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

private theorem badFamilyPotentialApproximationL2_mem_potentialZeroTrace
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (N : ℕ) (p : Vec d) :
    badFamilyPotentialApproximationL2 hb0 hb hk₀ hne N p ∈
      (PotentialSolenoidalL2Data.ofSubmoduleClosures
        (openCubeSet (originCube d m))).potentialZeroTrace := by
  let hprefix := potentialZeroTraceFieldOn_badFamily_activeComponentPrefix
    hb0 hb hk₀ hne N p
  rcases hprefix.2 with ⟨u, hu⟩
  apply (PotentialSolenoidalL2Data.ofSubmoduleClosures
    (openCubeSet (originCube d m))).mem_potentialZeroTrace hprefix.1
  exact IsPotentialZeroTraceOn.congr_ae hu.symm u.isPotentialZeroTraceOn

/-- Almost every point of the open root cube eventually sees the exact full
superposed slope defect in the finite Whitney-layer prefixes. -/
theorem ae_tendsto_badFamilyPotentialApproximation
    [NeZero d] {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (p : Vec d) :
    ∀ᵐ x ∂volumeMeasureOn (openCubeSet (originCube d m)),
      Filter.Tendsto
        (fun N => badFamilyPotentialApproximation M m E b k₀ omega N p x)
        Filter.atTop
        (nhds (superposedCompetitorSlope m
          (whitneyScale M m E b k₀ omega)
          (badFamily M m (whitneyScale M m E b k₀ omega) omega) p x - p)) := by
  let hn := whitneyScale M m E b k₀ omega
  let U := openCubeSet (originCube d m)
  have hmono : Monotone hn := by
    change Monotone (whitneyScaleSeq b (hsep M m E b omega) k₀)
    exact whitneyScaleSeq_mono hb0.le (by linarith) _ _
  have hstep : ∀ k, hn k ≤ hn (k + 1) + 1 := step_of_monotone hmono
  have hI : badFamily M m hn omega ⊆ whitneyPartition m hn := fun _ hR => hR.1
  have hwin := badComponents_window_badFamily hb0 hb hk₀ hne
  have hUnionSub :
      (⋃ T : ↑(simplexPartition (d := d) m hn), T.1.openCarrier) ⊆ U := by
    intro x hx
    obtain ⟨T, hxT⟩ := Set.mem_iUnion.mp hx
    have hxCarrier : x ∈ T.1.carrier := T.1.openCarrier_subset_carrier hxT
    dsimp [U]
    rw [← iUnion_carrier_simplexPartition_eq_openCubeSet hstep]
    exact Set.mem_iUnion.mpr ⟨T.1, Set.mem_iUnion.mpr ⟨T.2, hxCarrier⟩⟩
  have haeSet : U =ᵐ[volume]
      ⋃ T : ↑(simplexPartition (d := d) m hn), T.1.openCarrier := by
    apply MeasureTheory.ae_eq_set.mpr
    constructor
    · dsimp [U]
      simpa only [Set.iUnion_subtype] using
        volume_openCubeSet_diff_iUnion_openCarrier hstep
    · rw [Set.sdiff_eq_empty.mpr hUnionSub]
      exact measure_empty
  have hcover : ∀ᵐ x ∂volumeMeasureOn U,
      x ∈ ⋃ T : ↑(simplexPartition (d := d) m hn), T.1.openCarrier := by
    filter_upwards
        [MeasureTheory.ae_restrict_of_ae haeSet,
         MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet (originCube d m))]
      with x hxEq hxU
    exact hxEq.mp hxU
  filter_upwards [hcover] with x hx
  obtain ⟨T, hxT⟩ := Set.mem_iUnion.mp hx
  obtain ⟨k, Q, hQ, hTQ⟩ := T.2
  exact tendsto_const_nhds.congr' <| by
    filter_upwards [Filter.eventually_ge_atTop (k + 1)] with N hN
    have hkN : k < N := by omega
    have hfull := (superposedCompetitorSlope_eq_cellSlope
      hmono hI hwin p T.2).1 x hxT
    have hpref := badFamilyPotentialApproximation_eq_cell
      hb0 hb hk₀ hne (N := N) p T.2 x hxT
    have hcell := superposedCompetitorCellSlope_sub_eq_activeComponentPrefix_sum
      hb0 hb hk₀ hne hkN p hQ hTQ
    calc
      superposedCompetitorSlope m hn (badFamily M m hn omega) p x - p =
          superposedCompetitorCellSlope m hn (badFamily M m hn omega) p T.1 - p :=
        congrArg (fun v => v - p) hfull
      _ = badFamilyPotentialApproximationCell M m E b k₀ omega N p T.1 := by
        simpa only [hn, badFamilyPotentialApproximationCell] using hcell
      _ = badFamilyPotentialApproximation M m E b k₀ omega N p x := hpref.symm

/-! ## The full zero-trace potential theorem -/

/-- The full bad-family superposed slope defect is a zero-trace potential
field on the open root cube.  The nonzero-dimension instance is derived from
the model and is not exposed in the statement. -/
theorem potentialZeroTraceFieldOn_superposedCompetitorSlope_sub_badFamily
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (p : Vec d) :
    HCPolySupport.Book.Ch01.PotentialZeroTraceFieldOn
      (openCubeSet (originCube d m))
      (fun x => superposedCompetitorSlope m
        (whitneyScale M m E b k₀ omega)
        (badFamily M m (whitneyScale M m E b k₀ omega) omega) p x - p) := by
  let U := openCubeSet (originCube d m)
  let target : Vec d → Vec d := fun x => superposedCompetitorSlope m
    (whitneyScale M m E b k₀ omega)
    (badFamily M m (whitneyScale M m E b k₀ omega) omega) p x - p
  let P := PotentialSolenoidalL2Data.ofSubmoduleClosures U
  have : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).isFiniteMeasure_restrict_volume
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_badFamilyPotentialApproximationL2 hb0 hb hk₀ hne p)
  have hprefixMem : ∀ N,
      badFamilyPotentialApproximationL2 hb0 hb hk₀ hne N p ∈
        P.potentialZeroTrace := by
    intro N
    exact badFamilyPotentialApproximationL2_mem_potentialZeroTrace
      hb0 hb hk₀ hne N p
  have hFmem : F ∈ P.potentialZeroTrace :=
    P.potentialZeroTrace.isClosed.mem_of_tendsto hF
      (Filter.Eventually.of_forall hprefixMem)
  have hLpMeasure : MeasureTheory.TendstoInMeasure (volumeMeasureOn U)
      (fun N : ℕ => ⇑(badFamilyPotentialApproximationL2 hb0 hb hk₀ hne N p))
      Filter.atTop ⇑F :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hF
  have hrawMeasure : MeasureTheory.TendstoInMeasure (volumeMeasureOn U)
      (fun N : ℕ => badFamilyPotentialApproximation M m E b k₀ omega N p)
      Filter.atTop ⇑F := by
    refine hLpMeasure.congr_left fun N => ?_
    simpa only [U, badFamilyPotentialApproximationL2,
      badFamilyPotentialApproximation] using!
      coeFn_toVectorL2
        (potentialZeroTraceFieldOn_badFamily_activeComponentPrefix
          hb0 hb hk₀ hne N p).1
  have htargetMeasure : MeasureTheory.TendstoInMeasure (volumeMeasureOn U)
      (fun N : ℕ => badFamilyPotentialApproximation M m E b k₀ omega N p)
      Filter.atTop target := by
    apply MeasureTheory.tendstoInMeasure_of_tendsto_ae
    · intro N
      exact (potentialZeroTraceFieldOn_badFamily_activeComponentPrefix
        hb0 hb hk₀ hne N p).1.aestronglyMeasurable
    · simpa only [U, target] using
        ae_tendsto_badFamilyPotentialApproximation hb0 hb hk₀ hne p
  have hcoe : (⇑F : Vec d → Vec d) =ᵐ[volumeMeasureOn U] target :=
    MeasureTheory.tendstoInMeasure_ae_unique hrawMeasure htargetMeasure
  have htargetMem : MemVectorL2 U target :=
    MeasureTheory.MemLp.ae_eq hcoe (MeasureTheory.Lp.memLp F)
  have hrealize : PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
      (isOpenBoundedConvexDomain_openCubeSet (originCube d m))
  have hFpot : IsPotentialZeroTraceOn U (⇑F) := hrealize F hFmem
  have htargetPot : IsPotentialZeroTraceOn U target :=
    IsPotentialZeroTraceOn.congr_ae hcoe hFpot
  rcases htargetPot with ⟨u, hu⟩
  refine ⟨htargetMem, u, ?_⟩
  exact Filter.Eventually.of_forall fun x => (congrFun hu x).symm

end

end Algsuperdiff.Section3.Provider.Affine
