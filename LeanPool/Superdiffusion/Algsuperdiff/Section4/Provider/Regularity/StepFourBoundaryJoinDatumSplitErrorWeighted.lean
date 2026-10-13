/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourBoundaryJoinDatumSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourCollapseErrorWeighted
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeStepFourDatumSplitErrorWeighted

/-!
# StepFourBoundaryJoinDatumSplitErrorWeighted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The error-weighted Step-4 slot at every centre, and its budget seam

Nothing here imports the frozen file, nothing here claims the anchor, and nothing
here is a frozen statement.

## What this module proves

* `excessDecay_stepFour_slot_allCentres_datumSplit_errorWeighted` —
  `excessDecay_stepFour_slot_allCentres_datumSplit` at the error-weighted
  clause: the Step-4 slot with **no geometric hypothesis at all**, at every
  centre including the boundary lattice centres where the cube gate fails, with
  the printed datum leg and with the `𝓔`-multiplied flat `∇h` leg in the `δ`
  slot.  The disjunction is discharged by
  `RootInterfaceGate.gate_or_exists_meetsFace`.
* `edBridgeDeltaErrorWeighted_le_stepFourDeltaOutErrorWeighted` — the seam: the
  excess-decay lane's own `δ` is bounded by `stepFourDeltaOutErrorWeighted`'s own
  dominations.  The proof is
  `edBracket_le_errorWeighted` read at `Osc = 0` — the bridge's `δ` is precisely the
  collapse's bracket with the oscillation half already spent against the excess
  (that is what residue 2 does inside the slot), so no leg is double-counted.
* `edBridgeDatumLeg_at_flatIndex` — the datum leg at the budget's own `3^{n/2}` weight:
  `edBridgeDatumLeg d Cs k n K_h = (C_leg · 3^{1/2}) · (3^{n/2} · K_h)`.  The slot is
  delivered at `j = n+1` while the collapse's `δ` is indexed at `n`; the single `3^{1/2}`
  is that one-scale offset, and it moves only the `A^h` constant.
* `edBridgeDeltaErrorWeighted_add_datumLeg_le_boundaryThreeLegs` — the two composed: the
  slot's whole `δ`-side proves the three-leg grouping `A^g_n
  + (A^h_n + ε_j H)` with the `A^h` constant widened from `C_bd` to `C_bd +
  C_leg·3^{1/2}` and **no** `ε`-free flat summand at all.

## References

* ABK26, `l.excess.decay.good.scales`; `t.regularity` Steps 4--5.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The error-weighted Step-4 slot at every centre, geometric half discharged -/

/-- **The Step-4 decay slot at every printed centre, at the error-weighted clause.**

`EdBridgeStepFourDatumSplitErrorWeighted.excessDecay_stepFour_slot_general_datumSplit_errorWeighted` with the
join's window disjunction discharged by `RootInterfaceGate.gate_or_exists_meetsFace`: at
every centre and every scale either the interior gate holds outright, or some coordinate
face of `∂□_m` is met and the carried competitor package supplies the second disjunct.  No
interiority, no lattice-centre condition, no gate.

The carried package is asked of the shifted competitor's Weyl representative `V`,
so it is not forced to vanish on the met face and is chain-satisfiable at a
general Dirichlet datum; the price is the printed datum leg `edBridgeDatumLeg`
in the `δ` slot. -/
theorem excessDecay_stepFour_slot_allCentres_datumSplit_errorWeighted (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C Ccap Cb : ℝ, 0 < C ∧ 0 < Ccap ∧ 0 ≤ Cb ∧ ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
          M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          ∀ hs : 0 < s,
          ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) 1 →
            delta ≤ 64 * (C ^ (2 : ℕ))⁻¹ * s ^ (6 : ℕ) →
            M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                  (s / 8 * Real.sqrt delta) →
            edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k * Ccap *
                  Real.rpow s (-(3 : ℝ)) * Real.sqrt delta ≤
                (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) →
            ∀ L m : ℤ, m ≤ L →
              ∀ z : Vec d, z ∈ openCubeSet (originCube d m) →
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  ∀ n : ℤ, n + 1 ≤ m →
                    omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                        (cgEllipLowerConstant d) (n + 1) z ⟨s / 8, by linarith only [hs]⟩
                        (s / 8 * Real.sqrt delta) →
                    ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                      (gflux : Vec d → Vec d),
                      IsDirichletSolutionOn
                          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                          (originCube d m) u hdat gflux →
                      MemLp gflux 2
                          (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                      MemLp (Gagliardo.gagliardoKernel s 2 gflux) 2
                          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                      MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
                          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                      ∀ (v : H1Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
                              openCubeSet (originCube d (n - 2))))
                        (w : H10Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
                              openCubeSet (originCube d (n - 2)))),
                        IsWeaklyHarmonicOn ((fun y => wellPlacedCentre z m (n - 2) + y) ''
                          openCubeSet (originCube d (n - 2))) v →
                        (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                        (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                        ∀ (V v₁ : Vec d → ℝ) (cl : ℝ) (Al : Vec d) (Kh : ℝ), 0 ≤ Kh →
                        MemLp v.toFun 2 (volume.restrict (truncatedWindow z m n)) →
                        MemLp V 2 (volume.restrict (reflectedWindow z m (n - 2))) →
                        V =ᵐ[volume.restrict (truncatedWindow z m (n - 2))]
                          (fun y => v.toFun y - affineLift z cl Al y - v₁ y) →
                        (∀ᵐ y ∂(volume.restrict (truncatedWindow z m (n - 2))),
                          |v₁ y| ≤ datumResidualBound d n Kh) →
                        (∀ l : Fin d, MeetsUpperFace z m (n - 2) l →
                          ∀ y ∈ reflectedWindow z m (n - 2),
                            V (coordFaceReflection
                              ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) →
                        (∀ l : Fin d, MeetsLowerFace z m (n - 2) l →
                          ∀ y ∈ reflectedWindow z m (n - 2),
                            V (coordFaceReflection
                              (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) →
                        HarmonicOnNhd
                          (V ∘
                            (Schauder.toEuc.symm :
                              EuclideanSpace ℝ (Fin d) → Vec d))
                          ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
                            reflectedWindow z m (n - 2)) →
                        ∀ (c : ℝ) (gmin : Vec d),
                          IsAffineMinimizer (truncatedWindow z m (n + 1)) u.toFun c gmin →
                          affineExcess (truncatedWindow z m (n + 1 - ((k + 1 : ℕ) : ℤ)))
                              u.toFun ≤
                            (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) *
                                affineExcess (truncatedWindow z m (n + 1)) u.toFun +
                              edBridgeEps M
                                    (edBridgeEpsConstGen d
                                      (max (schauderWindowConst d) Cb) C k) L s
                                    ⟨s / 8, by linarith only [hs]⟩ z omega n *
                                  slopeMagnitude gmin +
                              (edBridgeDeltaErrorWeighted M C
                                  (edBridgeRemWeightGen d
                                    (max (schauderWindowConst d) Cb) k) L m s
                                  ⟨s / 8, by linarith only [hs]⟩ z gflux hdat.grad omega n
                                + edBridgeDatumLeg d
                                    (max (schauderWindowConst d) Cb) k n Kh) := by
  classical
  obtain ⟨C, Ccap, Cb, hC, hCcap, hCb, k₀, hk₀, hslot⟩ :=
    excessDecay_stepFour_slot_general_datumSplit_errorWeighted d hd
  refine ⟨C, Ccap, Cb, hC, hCcap, hCb, k₀, hk₀, ?_⟩
  intro k hk M s hsrange hregime hregimecap hs delta hdelta hprice hfundcap hgate L m hmL z hz
  filter_upwards [hslot k hk M s hsrange hregime hregimecap hs delta hdelta hprice hfundcap
    hgate L m hmL z hz] with omega hom
  intro n hnm hmem u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv V v₁ cl Al Kh hKh
    hvn hvR hVae hv₁ hupv hlowv hharmclass c gmin hmin
  refine hom n hnm hmem u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv Kh hKh ?_ c gmin
    hmin
  rcases gate_or_exists_meetsFace z m (n - 2) with hcube | ⟨i, hmet⟩
  · exact Or.inl hcube
  · exact Or.inr ⟨i, V, v₁, cl, Al, hmet, hvn, hvR, hVae, hv₁, hupv, hlowv, hharmclass⟩

/-! ## 2. The consumption seam: the bridge's `δ` is the collapse's `δ` -/

/-- **THE CONSUMPTION SEAM FOR THE ERROR-WEIGHTED `δ`.**

The excess-decay bridge's own `δ_j` at the error-weighted clause is bounded by
`stepFourDeltaOutErrorWeighted` — the object the collapse produces and the
`α`-free boundary budget consumes — through its own dominations and nothing more.

The proof is `edBracket_le_errorWeighted` read at `Osc = 0`: the bridge's bracket is
the collapse's bracket with the oscillation half already spent inside the slot
(residue 2 folds it into the contraction and the `ε |∇ℓ|` leg), so setting the
oscillation slot to zero is not a weakening — it is the exact accounting, and
no leg is counted twice. -/
theorem edBridgeDeltaErrorWeighted_le_stepFourDeltaOutErrorWeighted {M : ABKModel d}
    {C Crem Vd s epsj Khinf SigInvN Kg Kh : ℝ} {L m n : ℤ} {t : {t : ℝ // 0 < t}}
    {z : Vec d} {gflux gradh : Vec d → Vec d} {omega : Cutoff.CutoffSample d}
    (hCV : 0 ≤ Crem * Vd) (hCst : 0 ≤ C) (hs : 0 < s) (heps0 : 0 ≤ epsj)
    (hEfl : fluxCorrectedErrorRepresentative M L (n + 1) t
      (Cutoff.translateCutoffSample z omega) ≤ epsj)
    (hGav : ‖volumeAverageVec (truncatedWindow z m n) gradh‖ ≤ Khinf)
    (hSig : (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ ≤ 8 * SigInvN) (hSigN0 : 0 ≤ SigInvN)
    (hKg0 : 0 ≤ Kg)
    (hGsem : (normalizedGagliardoESeminormOn (truncatedWindow z m (n + 1)) s gflux).toReal ≤
      Kg * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)))
    (hKh0 : 0 ≤ Kh)
    (hHsem : (normalizedGagliardoESeminormOn (truncatedWindow z m (n + 1)) s gradh).toReal ≤
      Kh * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s))) :
    edBridgeDeltaErrorWeighted M C (Crem * Vd) L m s t z gflux gradh omega n ≤
      stepFourDeltaOutErrorWeighted Crem Vd C s epsj Khinf SigInvN Kg Kh n := by
  have hcoef4 : (0 : ℝ) ≤ C * s ^ (-(4 : ℝ)) := mul_nonneg hCst (Real.rpow_nonneg hs.le _)
  have hcoef6 : (0 : ℝ) ≤ C * s ^ (-(6 : ℝ)) := mul_nonneg hCst (Real.rpow_nonneg hs.le _)
  have hcoef7 : (0 : ℝ) ≤ C * s ^ (-(7 : ℝ)) := mul_nonneg hCst (Real.rpow_nonneg hs.le _)
  have hw : (0 : ℝ) ≤ s ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have h := edBracket_le_errorWeighted (n := n) (Crem := Crem) (Vd := Vd) (Cst := C) (s := s)
    (Efl := fluxCorrectedErrorRepresentative M L (n + 1) t
      (Cutoff.translateCutoffSample z omega))
    (Osc := 0)
    (Gav := ‖volumeAverageVec (truncatedWindow z m n) gradh‖)
    (Gsem := (normalizedGagliardoESeminormOn (truncatedWindow z m (n + 1)) s gflux).toReal)
    (Hsem := (normalizedGagliardoESeminormOn (truncatedWindow z m (n + 1)) s gradh).toReal)
    (Hl2 := ‖volumeAverageVec (truncatedWindow z m n) gradh‖)
    (SigInv := (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹) (SigInvN := SigInvN)
    (epsj := epsj) (Kg := Kg) (Kh := Kh) (Khinf := Khinf) (Cosc := 0) (E0 := 0) (S0 := 0)
    hCV hs.le hcoef4 hcoef6 hcoef7 hw
    (fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _) hEfl heps0
    (by simp) (by simp) (norm_nonneg _) hGav hSig hSigN0 ENNReal.toReal_nonneg hKg0 hGsem
    hKh0 hHsem hGav
  rw [edBridgeDeltaErrorWeighted, edBridgeDeltaBracketErrorWeighted]
  simp only [Real.rpow_eq_pow]
  linarith only [h]

/-! ## 3. The datum leg at the budget's own index, and the composed budget -/

/-- **The slot's datum leg at the collapse's `3^{n/2}` weight.**

The slot is delivered at `j = n+1` while the collapse's `δ` is indexed at `n`;
the single factor `3^{1/2}` is exactly that one-scale offset.  So as a summand
of the collapse's budget the leg is `(C_leg · 3^{1/2}) · (3^{n/2} · K_h)` —'s
`A^h_n` shape verbatim, with only the constant moving. -/
theorem edBridgeDatumLeg_at_flatIndex (d : ℕ) (Cs : ℝ) (k : ℕ) (n : ℤ) (Kh : ℝ) :
    edBridgeDatumLeg d Cs k n Kh
      = edBridgeDatumLegConst d Cs k * (3 : ℝ) ^ ((1 : ℝ) / 2) *
        ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) := by
  have hsplit : (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) / 2)
      = (3 : ℝ) ^ ((n : ℝ) / 2) * (3 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [edBridgeDatumLeg_eq, hsplit]
  ring

/-- **THE BOUNDARY BUDGET AT THE SLOT'S OWN `δ`-SIDE.**

The whole `δ`-side of the error-weighted Step-4 slot — the bridge's `δ` plus the
printed datum leg — sits inside the three-leg grouping

```text
   A^g_n + ( A^h_n + ε_j · H ) ,     H = 2 C_bd K_{h,∞} ,
```

with the `A^h` constant widened from `C_bd` to `C_bd + C_leg·3^{1/2}` and
**no** `ε`-free flat summand: the leg priced at `Θ(γ^{-1/2})` is gone, and the
datum leg costs a constant factor on `A^h` alone. -/
theorem edBridgeDeltaErrorWeighted_add_datumLeg_le_boundaryThreeLegs {M : ABKModel d}
    {C Crem Vd s epsj Khinf SigInvN Kg Kh Cs : ℝ} {k : ℕ} {L m n : ℤ}
    {t : {t : ℝ // 0 < t}} {z : Vec d} {gflux gradh : Vec d → Vec d}
    {omega : Cutoff.CutoffSample d}
    (hCV : 0 ≤ Crem * Vd) (hCst : 0 ≤ C) (hs : 0 < s) (heps0 : 0 ≤ epsj)
    (hEfl : fluxCorrectedErrorRepresentative M L (n + 1) t
      (Cutoff.translateCutoffSample z omega) ≤ epsj)
    (hGav : ‖volumeAverageVec (truncatedWindow z m n) gradh‖ ≤ Khinf)
    (hSig : (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ ≤ 8 * SigInvN) (hSigN0 : 0 ≤ SigInvN)
    (hKg0 : 0 ≤ Kg)
    (hGsem : (normalizedGagliardoESeminormOn (truncatedWindow z m (n + 1)) s gflux).toReal ≤
      Kg * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)))
    (hKh0 : 0 ≤ Kh)
    (hHsem : (normalizedGagliardoESeminormOn (truncatedWindow z m (n + 1)) s gradh).toReal ≤
      Kh * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s))) :
    edBridgeDeltaErrorWeighted M C (Crem * Vd) L m s t z gflux gradh omega n
        + edBridgeDatumLeg d Cs k n Kh ≤
      stepFourBoundaryDeltaConst Crem Vd C s *
          ((3 : ℝ) ^ ((n : ℝ) / 2) * SigInvN * Kg) +
        ((stepFourBoundaryDeltaConst Crem Vd C s
              + edBridgeDatumLegConst d Cs k * (3 : ℝ) ^ ((1 : ℝ) / 2)) *
            ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) +
          epsj * (2 * stepFourBoundaryDeltaConst Crem Vd C s * Khinf)) := by
  have hKhinf : (0 : ℝ) ≤ Khinf := le_trans (norm_nonneg _) hGav
  have hdel := edBridgeDeltaErrorWeighted_le_stepFourDeltaOutErrorWeighted (M := M) (C := C) (Crem := Crem)
    (Vd := Vd) (s := s) (epsj := epsj) (Khinf := Khinf) (SigInvN := SigInvN) (Kg := Kg)
    (Kh := Kh) (L := L) (m := m) (n := n) (t := t) (z := z) (gflux := gflux)
    (gradh := gradh) (omega := omega) hCV hCst hs heps0 hEfl hGav hSig hSigN0 hKg0 hGsem
    hKh0 hHsem
  have hbud := stepFourDeltaOutErrorWeighted_add_datumLeg_le_boundaryThreeLegs (Crem := Crem)
    (Vd := Vd) (Cst := C) (s := s) (epsj := epsj) (Khinf := Khinf) (SigInvN := SigInvN)
    (Kg := Kg) (Kh := Kh) (Cleg := edBridgeDatumLegConst d Cs k * (3 : ℝ) ^ ((1 : ℝ) / 2))
    (n := n) hCV hCst hs heps0 hKhinf hSigN0 hKg0 hKh0
  rw [edBridgeDatumLeg_at_flatIndex]
  linarith only [hdel, hbud]

end

end Algsuperdiff.Section4.Provider.Regularity
