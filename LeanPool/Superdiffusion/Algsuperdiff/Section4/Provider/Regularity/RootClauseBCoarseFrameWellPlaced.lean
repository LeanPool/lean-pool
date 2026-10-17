/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBGateGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringGeometry

/-!
# RootClauseBCoarseFrameWellPlaced

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The two printed inclusions, with no geometry binder -/

/-- **The printed sandwich, upper half.**  The well-placed coarse cube lies in
`□_m` for every centre, at the single scale comparison `k ≤ m`.  A restatement
of `BoundaryCoveringGeometry.image_add_wellPlacedCentre_subset_openCubeSet`
under the name the Step-7 chain reads. -/
theorem coarseFrame_subset_openCubeSet {m k : ℤ} (z : Vec d) (hkm : k ≤ m) :
    (fun y => wellPlacedCentre z m k + y) '' openCubeSet (originCube d k) ⊆
      openCubeSet (originCube d m) :=
  image_add_wellPlacedCentre_subset_openCubeSet z hkm

/-- **The printed sandwich, lower half.**  The Step-7 chain's coarse-window
inclusion `truncatedWindow z m k ⊆ c + □_k`, at no geometry binder. -/
theorem truncatedWindow_subset_coarseFrame {m k : ℤ} (z : Vec d) (hkm : k ≤ m) :
    truncatedWindow z m k ⊆
      (fun y => wellPlacedCentre z m k + y) '' openCubeSet (originCube d k) :=
  truncatedWindow_subset_image_add_wellPlacedCentre z hkm le_rfl

/-- The well-placed coarse cube has finite volume. -/
theorem volume_coarseFrame_ne_top {m k : ℤ} (z : Vec d) (hkm : k ≤ m) :
    volume ((fun y => wellPlacedCentre z m k + y) '' openCubeSet (originCube d k)) ≠
      ⊤ :=
  ne_top_of_le_ne_top (volume_openCubeSet_ne_top (originCube d m))
    (measure_mono (coarseFrame_subset_openCubeSet z hkm))

/-! ## 2. The five `IntegrableOn` slots at the well-placed cube -/

/-- **The chain's two window integrability slots**, at no geometry binder. -/
theorem integrableOn_truncatedWindow_pack {m k : ℤ} (z : Vec d)
    (u : H1Function (openCubeSet (originCube d m))) :
    IntegrableOn u.toFun (truncatedWindow z m k) volume ∧
      IntegrableOn (fun x => u.toFun x ^ 2) (truncatedWindow z m k) volume :=
  ⟨integrableOn_toFun_subset u (truncatedWindow_subset_domain z m k)
      (volume_truncatedWindow_lt_top z m k).ne,
    integrableOn_sq_toFun_subset u (truncatedWindow_subset_domain z m k)
      (volume_truncatedWindow_lt_top z m k).ne⟩

/-- **The chain's three covering-cube integrability slots**, at no geometry binder. -/
theorem integrableOn_coarseFrame_pack {m k : ℤ} (z : Vec d) (hkm : k ≤ m)
    (u : H1Function (openCubeSet (originCube d m))) (b : ℝ) :
    IntegrableOn u.toFun
        ((fun y => wellPlacedCentre z m k + y) '' openCubeSet (originCube d k))
        volume ∧
      IntegrableOn (fun x => u.toFun x ^ 2)
        ((fun y => wellPlacedCentre z m k + y) '' openCubeSet (originCube d k))
        volume ∧
      IntegrableOn (fun x => (u.toFun x - b) ^ 2)
        ((fun y => wellPlacedCentre z m k + y) '' openCubeSet (originCube d k))
        volume :=
  ⟨integrableOn_toFun_subset u (coarseFrame_subset_openCubeSet z hkm)
      (volume_coarseFrame_ne_top z hkm),
    integrableOn_sq_toFun_subset u (coarseFrame_subset_openCubeSet z hkm)
      (volume_coarseFrame_ne_top z hkm),
    integrableOn_sub_sq_toFun_subset u (coarseFrame_subset_openCubeSet z hkm)
      (volume_coarseFrame_ne_top z hkm) b⟩

/-! ## 5. The force's Besov regularity and the `dataB` leg at the well-placed cube -/

theorem forceBesovRegularity_coarseFrame [NeZero d] {m k : ℤ} {z : Vec d}
    {gsrc : Vec d → Vec d} (hkm : k ≤ m)
    (hgL2 : MemLp gsrc 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m)))) :
    ForceBesovRegularity (originCube d k) stepOneS
      (fun x => -gsrc (x + wellPlacedCentre z m k)) :=
  forceBesovRegularity_stepSevenCacc_gate (coarseFrame_subset_openCubeSet z hkm) hgL2
    hgW

/-- **The `dataB` leg at the print's own coarse frame, at no geometry binder.**

`RootClauseBGateGeometry.rootClauseB_dataB_gate` at `z:= wellPlacedCentre z m
k`.  The printed `3^{k/2} ≤ 3^{m/2}` step is the same scale comparison `k ≤ m`
that discharges the gate, so the statement carries exactly one integer
hypothesis. -/
theorem rootClauseB_dataB_coarseFrame [NeZero d] {m k : ℤ} {z : Vec d}
    {gsrc : Vec d → Vec d} {Khol : ℝ} (hkm : k ≤ m) (hKhol : 0 ≤ Khol)
    (hgHol : Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
      (1 / 2) Khol gsrc)
    (hgL2 : MemLp gsrc 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m)))) :
    scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k) stepSevenCgS
        (fun y => -gsrc (y + wellPlacedCentre z m k)) ≤
      rootClauseBDataBConst d * edFinalDataOscG Khol m :=
  rootClauseB_dataB_gate (coarseFrame_subset_openCubeSet z hkm) hkm hKhol hgHol hgL2
    hgW

end

end Algsuperdiff.Section4.Provider.Regularity
