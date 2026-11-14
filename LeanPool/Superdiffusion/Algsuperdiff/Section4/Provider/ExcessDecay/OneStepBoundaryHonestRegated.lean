/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryHonest
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseEpsilon

/-!
# OneStepBoundaryHonestRegated

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The re-gated sibling of the re-cut boundary one-step

`OneStepBoundaryHonest.excessDecay_oneStep_boundary_metSet_datumSplit` re-gated
at the frozen threshold `C_v⁻¹ s⁴`, exactly as the re-gated sibling of the
proved boundary endpoint re-gates it.  This is the shape the anchored join
consumes on the boundary branch, so it is the interface an honest join must be
built against.

The statement is transcribed byte-for-byte from the re-cut endpoint, with
`_hharm` re-gated and the reachability hypothesis `_hrep` inserted; the
conclusion — including the printed `K_h` leg — is unchanged.  The printed supply
event sits below both thresholds, so the re-gating is free
(`RebaseEpsilon.indicator_goodEventAt_transfer`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open scoped ENNReal

noncomputable section

/-- **The re-gated sibling of the re-cut boundary one-step.** -/
theorem excessDecay_oneStep_boundary_metSet_datumSplit_regated (d : ℕ) [NeZero d]
    (hd : d ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m n : ℤ} {k : ℕ} (_hk : 3 ≤ k) {M : ABKModel d} {s : ℝ}
      (hs : 0 < s) (_hs1 : s ≤ 1) {delta : ℝ} (_hdelta1 : delta ≤ 1) {x z : Vec d}
      {i : Fin d} (_hx : x ∈ openCubeSet (originCube d m)) (_hnm : n - 1 ≤ m)
      (_hmn : n - 2 < m)
      (_hmet : MeetsUpperFace x m (n - 2) i ∨ MeetsLowerFace x m (n - 2) i)
      {u v v₁ V : Vec d → ℝ} {cl : ℝ} {Al : Vec d} {Kh : ℝ} (_hKh : 0 ≤ Kh)
      (_hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
      (_hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
      (_hvR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))))
      (_huv : MemLp (fun y => u y - v y) 2
        (volume.restrict (movedReplacementCube x m n)))
      (_hVae : V =ᵐ[volume.restrict (truncatedWindow x m (n - 2))]
        (fun y => v y - affineLift x cl Al y - v₁ y))
      (_hv₁ : ∀ᵐ y ∂(volume.restrict (truncatedWindow x m (n - 2))),
        |v₁ y| ≤ datumResidualBound d n Kh)
      (_hupv : ∀ l : Fin d, MeetsUpperFace x m (n - 2) l →
        ∀ y ∈ reflectedWindow x m (n - 2),
          V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y)
      (_hlowv : ∀ l : Fin d, MeetsLowerFace x m (n - 2) l →
        ∀ y ∈ reflectedWindow x m (n - 2),
          V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y)
      (_hharmclass : HarmonicOnNhd
        (V ∘ (Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
          reflectedWindow x m (n - 2)))
      {omega : Cutoff.CutoffSample d}
      (_hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
        (Support.cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
        (s / 8 * Real.sqrt delta))
      {B : ℝ≥0∞} (_hB : B ≠ ⊤)
      {Cv : ℝ}
      (_hrep : s / 8 * Real.sqrt delta ≤ Cv⁻¹ * s ^ (4 : ℕ))
      (_hharm : Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
          (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (Cv⁻¹ * s ^ (4 : ℕ)))
        (fun _omega' =>
          MeasureTheory.eLpNorm (fun y => u y - v y) 2
            (Support.normalizedVolumeMeasureOn
              ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                openCubeSet (originCube d (n - 2)))))
        omega ≤ B),
      affineExcess (truncatedWindow x m (n - (k : ℤ))) u
        ≤ taylorContractionConst d * C * windowRatioConst d 2
              * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
              * affineExcess (truncatedWindow x m n) u
          + triangleRemainderConst d C k
              * ((3 : ℝ) ^ (-n)
                * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal))
          + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
              * (boundaryDatumLegConst d C k * Kh) := by
  obtain ⟨C, hC0, hC⟩ := excessDecay_oneStep_boundary_metSet_datumSplit d hd
  refine ⟨C, hC0, ?_⟩
  intro m n k hk M s hs hs1 delta hdelta1 x z i hx hnm hmn hmet u v v₁ V cl Al Kh hKh hu
    hv hvR huv hVae hv₁ hupv hlowv hharmclass omega hmem B hB Cv hrep hharm
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsqrtle : Real.sqrt delta ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hdelta1
  have hep0 : (0 : ℝ) ≤ s / 8 * Real.sqrt delta :=
    mul_nonneg (by linarith only [hs]) hsqrtnn
  have hhalf : s / 8 * Real.sqrt delta ≤ 1 / 2 := by
    have h1 : s / 8 ≤ 1 / 8 := by linarith only [hs1]
    calc s / 8 * Real.sqrt delta ≤ (1 / 8 : ℝ) * 1 :=
          mul_le_mul h1 hsqrtle hsqrtnn (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  exact hC hk hs hs1 hdelta1 hx hnm hmn hmet hKh hu hv hvR huv hVae hv₁ hupv hlowv
    hharmclass hmem hB (indicator_goodEventAt_transfer hep0 hrep hhalf hmem hharm)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
