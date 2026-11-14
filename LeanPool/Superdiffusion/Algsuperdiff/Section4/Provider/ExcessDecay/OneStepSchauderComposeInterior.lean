/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepWeylRepresentative

/-!
# OneStepSchauderComposeInterior

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior-branch excess-decay endpoint, conditional only on the anchor

`OneStepSchauderChain.excessDecay_oneStep_interior_of_harmonicApprox` closed the
Schauder slot of the interior branch, but it still *assumed* that the
competitor is **classically** harmonic on the replacement window
(`hharmclass`).  What the competitor producer
(`ResidualCorrectorExistence.exists_weaklyHarmonicOn_of_datum`) delivers is the
**variational** `Support.IsWeaklyHarmonicOn`.  Weyl's lemma
(`OneStepWeylRepresentative.exists_harmonicRepresentative_full`) bridges the two,
and this module performs the composition.

The result, `excessDecay_oneStep_interior_of_weaklyHarmonic`, carries exactly **one**
derived-result hypothesis, `hharm`, transcribed verbatim from
`OneStepConditional` (the anchor's conclusion), plus the standing frame and
the variational harmonicity of the competitor.  The four Schauder
slots and `hharmclass` are gone.

## Why the competitor lives on the moved replacement cube

The anchor states its `L²` bound on the **moved replacement cube**
`R = y + □_{n-2}` with `y = wellPlacedCentre x m (n-2)` — a full open cube — and
`OneStepWindows.truncatedWindow_subset_image_add_windowChoice` puts the
replacement window `(x + □_{n-2}) ∩ □_m` inside it.  Weyl's lemma is therefore
applied at `U := R`, where it yields harmonicity on **all** of `R` (the full
form, obtained in `OneStepWeylRepresentative` by gluing the fixed-radius
representatives), hence on the replacement window; and the same statement gives
`v = w` almost everywhere on `R`, which is exactly what makes `hharm` transfer
from `w` to `v` — `eLpNorm` is an almost-everywhere invariant.  Both `MemLp`
slots come free: the representative agrees almost everywhere with the zero
extension `𝟙_R w`, hence is globally square integrable.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The moved replacement cube as a domain -/

theorem isOpen_movedReplacementCube (x : Vec d) (m n : ℤ) :
    IsOpen (movedReplacementCube x m n) := by
  rw [movedReplacementCube]
  exact (Homeomorph.addLeft (wellPlacedCentre x m (n - 2))).isOpenMap _
    (HCPolySupport.isOpen_openCubeSet _)

theorem measurableSet_movedReplacementCube (x : Vec d) (m n : ℤ) :
    MeasurableSet (movedReplacementCube x m n) :=
  (isOpen_movedReplacementCube x m n).measurableSet

theorem truncatedWindow_subset_movedReplacementCube (x : Vec d) {m n : ℤ} (hnm : n - 2 ≤ m) :
    truncatedWindow x m (n - 2) ⊆ movedReplacementCube x m n :=
  truncatedWindow_subset_image_add_windowChoice x hnm

theorem movedReplacementCube_subset_truncatedWindow {x : Vec d} {m n : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 2 ≤ m) :
    movedReplacementCube x m n ⊆ truncatedWindow x m n :=
  subset_trans
    (image_add_wellPlacedCentre_subset_windowChoice
      (z := x) (mem_truncatedWindow_self (n - 3) hx) hnm)
    (truncatedWindow_mono x m (by omega : n - 1 ≤ n))

/-! ## 2. The competitor's smooth harmonic representative -/

/-- **The classical competitor.**  From a variationally harmonic `H¹` function on the anchor's
moved replacement cube, Weyl's lemma produces a globally square-integrable representative which is
classically harmonic on the whole cube and agrees with it almost everywhere there. -/
theorem exists_classicalCompetitor_movedReplacementCube [NeZero d] (x : Vec d) (m n : ℤ)
    {w : H1Function (movedReplacementCube x m n)}
    (hw : IsWeaklyHarmonicOn (movedReplacementCube x m n) w) :
    ∃ v : Vec d → ℝ,
      HarmonicOnNhd (v ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' movedReplacementCube x m n) ∧
      MemLp v 2 (volume : Measure (Vec d)) ∧
      v =ᵐ[volume.restrict (movedReplacementCube x m n)] w.toFun := by
  obtain ⟨v, hharm, hmem, hae⟩ :=
    exists_harmonicRepresentative_memLp (isOpen_movedReplacementCube x m n) hw
  refine ⟨v, hharm, hmem, ?_⟩
  have h1 : v =ᵐ[volume.restrict (movedReplacementCube x m n)]
      Set.indicator (movedReplacementCube x m n) w.toFun :=
    MeasureTheory.ae_restrict_of_ae hae
  filter_upwards [h1,
    MeasureTheory.self_mem_ae_restrict (measurableSet_movedReplacementCube x m n)] with p hp hpR
  rw [hp, Set.indicator_of_mem hpR]

/-! ## 3. The composed interior endpoint -/

/-- **The one-step excess-decay contraction on the interior branch, conditional only on the
harmonic-approximation anchor.**

Identical to `OneStepConditional.excessDecay_oneStep_of_harmonicApprox` with
`Csch = schauderWindowConst d` and `K_h = 0`, and with the four Schauder slots *and*
the classical-harmonicity slot of `OneStepSchauderChain` all discharged: the competitor enters
only through the **variational** condition `Support.IsWeaklyHarmonicOn` on the anchor's own moved
replacement cube, which is what `ResidualCorrectorExistence.exists_weaklyHarmonicOn_of_datum`
produces.

The `hharm` binder is transcribed **verbatim** from `OneStepConditional`, with the competitor read
as `w.toFun`; `eLpNorm` is an almost-everywhere invariant, so the smooth representative may be
substituted inside the proof without touching the statement. -/
theorem excessDecay_oneStep_interior_of_weaklyHarmonic [NeZero d] (hd : d ≠ 0) {m n : ℤ}
    {k : ℕ} (hk : 3 ≤ k) {M : ABKModel d} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {delta : ℝ}
    (hdelta1 : delta ≤ 1) {x z : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m)
    (hcube : (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
      openCubeSet (originCube d m))
    {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
    {w : H1Function ((fun y => wellPlacedCentre x m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2)))}
    (hw : IsWeaklyHarmonicOn ((fun y => wellPlacedCentre x m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2))) w)
    {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
      (Support.cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
      (s / 8 * Real.sqrt delta))
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hharm : Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
          (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
        (fun _omega' =>
          MeasureTheory.eLpNorm (fun y => u y - w.toFun y) 2
            (Support.normalizedVolumeMeasureOn
              ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                openCubeSet (originCube d (n - 2)))))
        omega ≤ B) :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u
      ≤ taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m n) u
        + triangleRemainderConst d (schauderWindowConst d) k
            * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal))
        + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * 0 := by
  have hnm2 : n - 2 ≤ m := by omega
  set R : Set (Vec d) := movedReplacementCube x m n with hRdef
  -- Weyl's lemma at the anchor's replacement cube
  obtain ⟨v, hvharm, hvmem, hvae⟩ := exists_classicalCompetitor_movedReplacementCube x m n hw
  -- the two `MemLp` slots
  have hRsub : R ⊆ truncatedWindow x m n := movedReplacementCube_subset_truncatedWindow hx hnm2
  have hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)) := hvmem.restrict _
  have huR : MemLp u 2 (volume.restrict R) :=
    hu.mono_measure (Measure.restrict_mono hRsub le_rfl)
  have hvR : MemLp v 2 (volume.restrict R) := hvmem.restrict _
  have huv : MemLp (fun y => u y - v y) 2 (volume.restrict R) := huR.sub hvR
  -- the classical harmonicity slot, on the replacement window inside the cube
  have hharmclass : HarmonicOnNhd (v ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m (n - 2)) :=
    hvharm.mono (Set.image_mono (truncatedWindow_subset_movedReplacementCube x hnm2))
  -- transfer `hharm` from the variational competitor to its representative
  have hN : (fun y => u y - v y)
      =ᵐ[Support.normalizedVolumeMeasureOn R] (fun y => u y - w.toFun y) := by
    rw [Support.normalizedVolumeMeasureOn_def]
    refine MeasureTheory.Measure.ae_smul_measure ?_ _
    filter_upwards [hvae] with p hp
    rw [hp]
  have heLp : MeasureTheory.eLpNorm (fun y => u y - v y) 2
        (Support.normalizedVolumeMeasureOn R)
      = MeasureTheory.eLpNorm (fun y => u y - w.toFun y) 2
        (Support.normalizedVolumeMeasureOn R) :=
    MeasureTheory.eLpNorm_congr_ae hN
  have hharm' : Set.indicator
      (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
        (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
      (fun _omega' =>
        MeasureTheory.eLpNorm (fun y => u y - v y) 2
          (Support.normalizedVolumeMeasureOn
            ((fun y => wellPlacedCentre x m (n - 2) + y) ''
              openCubeSet (originCube d (n - 2)))))
      omega ≤ B := by
    rw [show ((fun y => wellPlacedCentre x m (n - 2) + y) ''
        openCubeSet (originCube d (n - 2))) = R from hRdef.symm, heLp]
    rw [hRdef]
    exact hharm
  exact excessDecay_oneStep_interior_of_harmonicApprox hd hk hs hs1 hdelta1 hx hnm hcube hu hv
    huv hharmclass hmem hB hharm'

end

end Algsuperdiff.Section4.Provider.ExcessDecay
