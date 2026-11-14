/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AssemblyBoundaryClause
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseEpsilon
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.StitchDisplayLegs

/-!
# ProviderBoundary

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary obligation, discharged

## The stitch, in one paragraph

Feeding `S := |(u − h)_{V₁}|` itself,
`StitchDisplayLegs.exists_scalarLeg_le_displayLegs_of_epsPin` prices that
summand on the display's own four legs — **provided** the pin `A·𝓔 ≤ s⁴` holds.
And the pin is exactly what the re-gating bought: on the clause event `𝒢(n+3, z;
s/8, C⁻¹s⁴)` the proved caps step
`GoodEventCaps.ae_errorRepresentative_le_of_mem_goodEventAt` — whose `ε`-slot
is universally quantified — gives `𝓔 ≤ C₀·C⁻¹·s⁴`, so `A·𝓔 ≤ s⁴` as soon as the
statement's own existential constant satisfies `C ≥ A·C₀`.  That is legitimate
because `C` is chosen **last**, after the `d`-only constants `C₀` and `A`.

## The final constant

`C:= max (max (max C_asm C_disp) (max C₀ C_σ)) (max (max 2 (A·C₀)) (C_asm·(1 +
4·C_out)))`, where every entry is a `d`-only constant produced before `C`:

* `C_disp` — the display-legs pricing;
* `C₀` — the caps step;
* `C_σ` — the `σ` gap-3 conversion;
* `2` — makes `C⁻¹s⁴ ≤ 1/2`, keeping the clause event inside the annular
  anchor's admissible `ε`-window and funding the `(1/2)`-form hypotheses of the
  two proved inputs a fortiori;
* `A·C₀` — **the pin**;
* `C_asm·(1 + 4·C_out)` — the conclusion's absorption.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the frozen block of
  `Algsuperdiff/Section4/Provider/ExcessDecay/ProviderEpsFree.lean` (read for
  the byte-verification, never imported).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. The absorption arithmetic -/

/-- **The scalar leg, absorbed into the display.**

Everything below is free-real arithmetic on nonnegative data. -/
theorem boundaryScalarLeg_absorb {LHS CA Cout Ctot L1 L1' L2 L2' L3 L4 P : ℝ}
    (hmain : LHS ≤ CA * (L1 + L2 + L3 + L4) + CA * P)
    (hP : P ≤ Cout * (L1' + L4 + L3 + L2'))
    (hL1' : L1' ≤ L1) (hL2' : L2' ≤ 4 * L2)
    (hCA : 0 ≤ CA) (hCout : 0 ≤ Cout) (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2)
    (hL3 : 0 ≤ L3) (hL4 : 0 ≤ L4)
    (hC : CA * (1 + 4 * Cout) ≤ Ctot) :
    LHS ≤ Ctot * (L1 + L2 + L3 + L4) := by
  have hsum : (0 : ℝ) ≤ L1 + L2 + L3 + L4 := by
    linarith only [hL1, hL2, hL3, hL4]
  have hP2 : L1' + L4 + L3 + L2' ≤ 4 * (L1 + L2 + L3 + L4) := by
    linarith only [hL1', hL2', hL1, hL2, hL3, hL4]
  have hP4 : CA * P ≤ CA * (Cout * (4 * (L1 + L2 + L3 + L4))) :=
    mul_le_mul_of_nonneg_left (hP.trans (mul_le_mul_of_nonneg_left hP2 hCout)) hCA
  have hfin : CA * (1 + 4 * Cout) * (L1 + L2 + L3 + L4) ≤
      Ctot * (L1 + L2 + L3 + L4) := mul_le_mul_of_nonneg_right hC hsum
  linarith only [hmain, hP4, hfin]

/-- **The pin, from the clause threshold.**

`A·𝓔 ≤ s⁴` whenever the caps step gives `𝓔 ≤ C₀·(C⁻¹·s⁴)` and the statement's
own constant was chosen with `A·C₀ ≤ C`. -/
theorem epsPin_of_caps {A C0 Ct E s : ℝ} (hA : 0 ≤ A) (hCt : 0 < Ct)
    (hpin : A * C0 ≤ Ct) (hs : 0 ≤ s)
    (hcap : E ≤ C0 * (Ct⁻¹ * s ^ (4 : ℕ))) :
    A * E ≤ s ^ (4 : ℕ) := by
  have h1 : A * E ≤ A * (C0 * (Ct⁻¹ * s ^ (4 : ℕ))) :=
    mul_le_mul_of_nonneg_left hcap hA
  have h3 : A * C0 * Ct⁻¹ ≤ 1 := by
    have h4 : A * C0 * Ct⁻¹ ≤ Ct * Ct⁻¹ :=
      mul_le_mul_of_nonneg_right hpin (inv_nonneg.mpr hCt.le)
    rwa [mul_inv_cancel₀ (ne_of_gt hCt)] at h4
  have h5 : A * C0 * Ct⁻¹ * s ^ (4 : ℕ) ≤ 1 * s ^ (4 : ℕ) :=
    mul_le_mul_of_nonneg_right h3 (pow_nonneg hs 4)
  rw [one_mul] at h5
  linarith only [h1, h5]

/-- A single boundary-provider constant controls all source thresholds and absorptions. -/
theorem exists_boundary_provider_constant (CA CD C0 CS A Cout : ℝ) :
    ∃ Ct : ℝ, CA ≤ Ct ∧ CD ≤ Ct ∧ C0 ≤ Ct ∧ CS ≤ Ct ∧ (2 : ℝ) ≤ Ct ∧
      A * C0 ≤ Ct ∧ CA * (1 + 4 * Cout) ≤ Ct := by
  refine ⟨max (max (max CA CD) (max C0 CS))
      (max (max 2 (A * C0)) (CA * (1 + 4 * Cout))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((le_max_left CA CD).trans (le_max_left _ _)).trans (le_max_left _ _)
  · exact ((le_max_right CA CD).trans (le_max_left _ _)).trans (le_max_left _ _)
  · exact ((le_max_left C0 CS).trans (le_max_right _ _)).trans (le_max_left _ _)
  · exact ((le_max_right C0 CS).trans (le_max_right _ _)).trans (le_max_left _ _)
  · exact ((le_max_left 2 (A * C0)).trans (le_max_left _ _)).trans (le_max_right _ _)
  · exact ((le_max_right 2 (A * C0)).trans (le_max_left _ _)).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- The boundary clause epsilon lies in the half-event range and inherits funding. -/
theorem boundary_clause_epsilon_data {d : ℕ} {M : ABKModel d} {s Ct : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hCt2 : (2 : ℝ) ≤ Ct)
    (hfund : M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
        (Ct⁻¹ * s ^ (4 : ℕ))) :
    0 < Ct⁻¹ * s ^ (4 : ℕ) ∧ Ct⁻¹ * s ^ (4 : ℕ) ≤ 1 / 2 ∧
      M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
        Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) := by
  have hCt : 0 < Ct := lt_of_lt_of_le (by norm_num) hCt2
  have hhalf := clauseEpsilon_le_half hCt2 hs.le hs1
  exact ⟨mul_pos (inv_pos.mpr hCt) (pow_pos hs 4), hhalf,
    funding_le_of_epsilon_le hs hhalf hfund⟩

/-! ## 2. The boundary obligation -/

/-- The boundary-provider estimate retaining its final gradient error weight. -/
theorem exists_boundaryClauseReal_errorWeighted (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (C⁻¹ * s ^ (4 : ℕ)) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m →
          ∀ x z : HCPolySupport.Vec d,
            x ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
            z ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
            (fun y => x + y) '' HCPolySupport.openCubeSet (HCPolySupport.originCube d n) ⊆
              ((fun y => z + y) ''
                  HCPolySupport.openCubeSet (HCPolySupport.originCube d (n + 1))) ∩
                HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
            (((fun y' => z + y') ''
                    HCPolySupport.openCubeSet (HCPolySupport.originCube d (n + 2))) ∩
                  frontier (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) ≠
                ∅) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (C⁻¹ * s ^ (4 : ℕ)) →
                ∀ (u h : HCPolySupport.H1Function
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)))
                  (g : HCPolySupport.Vec d → HCPolySupport.Vec d),
                  Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (HCPolySupport.originCube d m) u h g →
                  MeasureTheory.MemLp g 2
                      (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                        (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) →
                  MeasureTheory.MemLp (HCPolySupport.Gagliardo.gagliardoKernel s 2 g) 2
                      (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                        (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) →
                  MeasureTheory.MemLp (HCPolySupport.Gagliardo.gagliardoKernel s 2 h.grad) 2
                      (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                        (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) →
                  ∀ (v : HCPolySupport.H1Function
                        ((fun y => x + y) ''
                          HCPolySupport.openCubeSet (HCPolySupport.originCube d n)))
                    (w : HCPolySupport.H10Function
                        ((fun y => x + y) ''
                          HCPolySupport.openCubeSet (HCPolySupport.originCube d n))),
                    Algsuperdiff.Section4.Support.IsWeaklyHarmonicOn
                        ((fun y => x + y) ''
                          HCPolySupport.openCubeSet (HCPolySupport.originCube d n)) v →
                    (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                    (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                      (MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                          (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                            ((fun y => x + y) ''
                              HCPolySupport.openCubeSet
                                (HCPolySupport.originCube d n)))).toReal ≤
                        C *
                          (Real.rpow s (-(4 : ℝ)) *
                                Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative
                                  M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
                                  (Cutoff.translateCutoffSample z omega) *
                                ((MeasureTheory.eLpNorm
                                    (fun y =>
                                      u.toFun y -
                                        HCPolySupport.volumeAverage
                                          (((fun y' => z + y') ''
                                              HCPolySupport.openCubeSet
                                                (HCPolySupport.originCube d (n + 3))) ∩
                                            HCPolySupport.openCubeSet
                                              (HCPolySupport.originCube d m))
                                          u.toFun)
                                    2
                                    (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                      (((fun y' => z + y') ''
                                          HCPolySupport.openCubeSet
                                            (HCPolySupport.originCube d (n + 3))) ∩
                                        HCPolySupport.openCubeSet
                                          (HCPolySupport.originCube d m)))).toReal +
                                  Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                                    ‖HCPolySupport.volumeAverageVec
                                        (((fun y' => z + y') ''
                                            HCPolySupport.openCubeSet
                                              (HCPolySupport.originCube d (n + 2))) ∩
                                          HCPolySupport.openCubeSet
                                            (HCPolySupport.originCube d m))
                                        h.grad‖) +
                            Real.rpow s (-(7 : ℝ)) * (Annealed.sigmaBar M n : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d (n + 3))) ∩
                                    HCPolySupport.openCubeSet
                                      (HCPolySupport.originCube d m)) s g).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d (n + 3))) ∩
                                    HCPolySupport.openCubeSet
                                      (HCPolySupport.originCube d m)) s h.grad).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                                Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative
                                  M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
                                  (Cutoff.translateCutoffSample z omega) *
                                Real.rpow (3 : ℝ) (n : ℝ) *
                                (MeasureTheory.eLpNorm h.grad 2
                                  (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                    (((fun y' => z + y') ''
                                        HCPolySupport.openCubeSet
                                          (HCPolySupport.originCube d (n + 3))) ∩
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d m)))).toReal) := by
  classical
  by_cases hd : d = 0
  · refine ⟨1, one_pos, ?_⟩
    intro M
    exact absurd M.shellPrefix.dimension (by omega)
  have : NeZero d := ⟨hd⟩
  obtain ⟨CA, hCA, hasm⟩ := hbdryOfScalarCoarse_errorWeighted d
  obtain ⟨CD, A, Cout, hCD, hA, hCout, hdisp⟩ :=
    exists_scalarLeg_le_displayLegs_of_epsPin_errorWeighted d
  obtain ⟨C0, hC0, hcaps⟩ := ae_errorRepresentative_le_of_mem_goodEventAt d
  obtain ⟨CS, hCS, hsig⟩ := exists_inv_sigmaBar_add_three_le d
  obtain ⟨Ct, hleA, hleD, hle0, hleS, hle2, hlepin, hleout⟩ :=
    exists_boundary_provider_constant CA CD C0 CS A Cout
  have hCtpos : (0 : ℝ) < Ct := lt_of_lt_of_le (by norm_num) hle2
  refine ⟨Ct, hCtpos, ?_⟩
  intro M s hsrange hregime hfund hs L m n hmL hnm x z hx hz hgeom hgate
  have hs1 : s ≤ 1 := hsrange.2
  obtain ⟨hep0, hephalf, hfund2⟩ := boundary_clause_epsilon_data hs hs1 hle2 hfund
  obtain ⟨i, sigma, hsigma, hover⟩ := overhang_of_boundaryBranch hgate
  have hsigconv := hsig M (regime_le_of_const_le hCS hleS hregime) n
  filter_upwards [hasm M s hsrange (regime_le_of_const_le hCA hleA hregime) hfund2 hs
      L m n hmL hnm x z hx hz hgeom hgate,
    hdisp M s hsrange (regime_le_of_const_le hCD hleD hregime) hfund2 hs
      L m n hmL hnm x z hx hz hgeom i sigma hsigma hover,
    hcaps M (regime_le_of_const_le hC0 hle0 hregime) ⟨s / 8, by linarith only [hs]⟩
      (annularSlot_mem_Icc M.gamma s hsrange) (Ct⁻¹ * s ^ (4 : ℕ))
      ⟨hep0, hephalf⟩ hfund (n + 3) z]
    with omega hasmw hdispw hcapsw
  intro hmem u h g hsol hgL2 hgW hhW v w hharm hval hgrad
  have hmemhalf := Algsuperdiff.Section4.Provider.GoodEvents.goodEventAt_mono_ep M
    (Support.cgEllipLowerConstant d) (n + 3) z ⟨s / 8, by linarith only [hs]⟩
    hep0.le hephalf hmem
  have hpin := epsPin_of_caps hA.le hCtpos hlepin hs.le
    (hcapsw hmem L (by omega))
  have hmain := hasmw hmemhalf u h g hsol hgL2 hgW hhW _ (le_refl
    |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2))) (fun y => u.toFun y - h.toFun y)|)
    v w hharm hval hgrad
  have hpriced := hdispw hmemhalf hpin u h g hsol hgL2 hgW hhW
  have hErep0 : (0 : ℝ) ≤ Support.fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hS4 : (0 : ℝ) ≤ Real.rpow s (-(4 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS7 : (0 : ℝ) ≤ Real.rpow s (-(7 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS6 : (0 : ℝ) ≤ Real.rpow s (-(6 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS32 : (0 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have h3n : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (n : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h3sn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsgn : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M n).2.le
  have hcompanion : (0 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
      ‖volumeAverageVec
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
          openCubeSet (originCube d m))) h.grad‖ :=
    mul_nonneg (mul_nonneg hS32 h3n) (norm_nonneg _)
  -- the force leg, converted from `σ_{n+3}` to `σ_n`
  have hforce : Real.rpow s (-(7 : ℝ)) * ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
      Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
      (Support.normalizedGagliardoESeminormOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))) s g).toReal ≤
      4 * (Real.rpow s (-(7 : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
        Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
        (Support.normalizedGagliardoESeminormOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))) s g).toReal) :=
    sigma_leg_move hS7 h3sn ENNReal.toReal_nonneg hsigconv
  exact boundaryScalarLeg_absorb hmain hpriced
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hcompanion)
      (mul_nonneg hS4 hErep0)) hforce hCA.le hCout
    (mul_nonneg (mul_nonneg hS4 hErep0)
      (add_nonneg ENNReal.toReal_nonneg hcompanion))
    (mul_nonneg (mul_nonneg (mul_nonneg hS7 hsgn) h3sn) ENNReal.toReal_nonneg)
    (mul_nonneg (mul_nonneg hS6 h3sn) ENNReal.toReal_nonneg)
    (mul_nonneg (mul_nonneg (mul_nonneg hS6 hErep0) h3n) ENNReal.toReal_nonneg) hleout

/-- The frozen general clause in real form, restricted to the boundary regime
`(z+□_{n+2}) ∩ ∂□_m ≠ ∅` — `RebaseSealDistance`'s `hbdry` — with **no**
hypothesis beyond the frozen statement's own binders. -/
theorem exists_boundaryClauseReal (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (C⁻¹ * s ^ (4 : ℕ)) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m →
          ∀ x z : HCPolySupport.Vec d,
            x ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
            z ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
            (fun y => x + y) '' HCPolySupport.openCubeSet (HCPolySupport.originCube d n) ⊆
              ((fun y => z + y) ''
                  HCPolySupport.openCubeSet (HCPolySupport.originCube d (n + 1))) ∩
                HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
            (((fun y' => z + y') ''
                    HCPolySupport.openCubeSet (HCPolySupport.originCube d (n + 2))) ∩
                  frontier (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) ≠
                ∅) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (C⁻¹ * s ^ (4 : ℕ)) →
                ∀ (u h : HCPolySupport.H1Function
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)))
                  (g : HCPolySupport.Vec d → HCPolySupport.Vec d),
                  Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (HCPolySupport.originCube d m) u h g →
                  MeasureTheory.MemLp g 2
                      (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                        (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) →
                  MeasureTheory.MemLp (HCPolySupport.Gagliardo.gagliardoKernel s 2 g) 2
                      (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                        (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) →
                  MeasureTheory.MemLp (HCPolySupport.Gagliardo.gagliardoKernel s 2 h.grad) 2
                      (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                        (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) →
                  ∀ (v : HCPolySupport.H1Function
                        ((fun y => x + y) ''
                          HCPolySupport.openCubeSet (HCPolySupport.originCube d n)))
                    (w : HCPolySupport.H10Function
                        ((fun y => x + y) ''
                          HCPolySupport.openCubeSet (HCPolySupport.originCube d n))),
                    Algsuperdiff.Section4.Support.IsWeaklyHarmonicOn
                        ((fun y => x + y) ''
                          HCPolySupport.openCubeSet (HCPolySupport.originCube d n)) v →
                    (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                    (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                      (MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                          (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                            ((fun y => x + y) ''
                              HCPolySupport.openCubeSet
                                (HCPolySupport.originCube d n)))).toReal ≤
                        C *
                          (Real.rpow s (-(4 : ℝ)) *
                                Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative
                                  M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
                                  (Cutoff.translateCutoffSample z omega) *
                                ((MeasureTheory.eLpNorm
                                    (fun y =>
                                      u.toFun y -
                                        HCPolySupport.volumeAverage
                                          (((fun y' => z + y') ''
                                              HCPolySupport.openCubeSet
                                                (HCPolySupport.originCube d (n + 3))) ∩
                                            HCPolySupport.openCubeSet
                                              (HCPolySupport.originCube d m))
                                          u.toFun)
                                    2
                                    (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                      (((fun y' => z + y') ''
                                          HCPolySupport.openCubeSet
                                            (HCPolySupport.originCube d (n + 3))) ∩
                                        HCPolySupport.openCubeSet
                                          (HCPolySupport.originCube d m)))).toReal +
                                  Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                                    ‖HCPolySupport.volumeAverageVec
                                        (((fun y' => z + y') ''
                                            HCPolySupport.openCubeSet
                                              (HCPolySupport.originCube d (n + 2))) ∩
                                          HCPolySupport.openCubeSet
                                            (HCPolySupport.originCube d m))
                                        h.grad‖) +
                            Real.rpow s (-(7 : ℝ)) * (Annealed.sigmaBar M n : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d (n + 3))) ∩
                                    HCPolySupport.openCubeSet
                                      (HCPolySupport.originCube d m)) s g).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d (n + 3))) ∩
                                    HCPolySupport.openCubeSet
                                      (HCPolySupport.originCube d m)) s h.grad).toReal +
                            Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                                (MeasureTheory.eLpNorm h.grad 2
                                  (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                    (((fun y' => z + y') ''
                                        HCPolySupport.openCubeSet
                                          (HCPolySupport.originCube d (n + 3))) ∩
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d m)))).toReal) := by
  classical
  obtain ⟨CW, hCW, hweighted⟩ := exists_boundaryClauseReal_errorWeighted d
  obtain ⟨C0, hC0, hcaps⟩ := ae_errorRepresentative_le_of_mem_goodEventAt d
  let Ct := max (max CW C0) 2
  have hleW : CW ≤ Ct := (le_max_left _ _).trans (le_max_left _ _)
  have hle0 : C0 ≤ Ct := (le_max_right _ _).trans (le_max_left _ _)
  have hle2 : (2 : ℝ) ≤ Ct := le_max_right _ _
  have hCt : 0 < Ct := lt_of_lt_of_le (by norm_num) hle2
  refine ⟨Ct, hCt, ?_⟩
  intro M s hsrange hregime hfund hs L m n hmL hnm x z hx hz hgeom hgate
  obtain ⟨hep0, hephalf, _⟩ := boundary_clause_epsilon_data hs hsrange.2 hle2 hfund
  have hepW := clauseEpsilon_anti hCW hleW hs.le
  filter_upwards [hweighted M s hsrange (regime_le_of_const_le hCW hleW hregime)
      (funding_le_of_epsilon_le hs hepW hfund) hs L m n hmL hnm x z hx hz hgeom hgate,
    hcaps M (regime_le_of_const_le hC0 hle0 hregime) ⟨s / 8, by linarith only [hs]⟩
      (annularSlot_mem_Icc M.gamma s hsrange) (Ct⁻¹ * s ^ (4 : ℕ))
      ⟨hep0, hephalf⟩ hfund (n + 3) z] with omega hom hcap
  intro hmem u hdat g hsol hgL2 hgW hhW v w hharm hval hgrad
  have hmemW := Algsuperdiff.Section4.Provider.GoodEvents.goodEventAt_mono_ep M
    (Support.cgEllipLowerConstant d) (n + 3) z ⟨s / 8, by linarith only [hs]⟩
    hep0.le hepW hmem
  have hreal := hom hmemW u hdat g hsol hgL2 hgW hhW v w hharm hval hgrad
  let window := ((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
    openCubeSet (originCube d m)
  let companionWindow := ((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
    openCubeSet (originCube d m)
  let E := Support.fluxCorrectedErrorRepresentative M L (n + 3)
    ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega)
  have hE0 : 0 ≤ E := Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hsig0 : 0 ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M n).2.le
  let oscillationLeg := Real.rpow s (-(4 : ℝ)) * E *
    ((eLpNorm (fun y => u.toFun y - volumeAverage window u.toFun) 2
      (Support.normalizedVolumeMeasureOn window)).toReal +
      Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
        ‖volumeAverageVec companionWindow hdat.grad‖)
  let forceLeg := Real.rpow s (-(7 : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
    Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
      (Support.normalizedGagliardoESeminormOn window s g).toReal
  let fractionalGradientLeg := Real.rpow s (-(6 : ℝ)) *
    Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
      (Support.normalizedGagliardoESeminormOn window s hdat.grad).toReal
  let gradientLeg := Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
    (eLpNorm hdat.grad 2 (Support.normalizedVolumeMeasureOn window)).toReal
  have hoscillation : 0 ≤ oscillationLeg :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) hE0)
      (add_nonneg ENNReal.toReal_nonneg
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
          (Real.rpow_nonneg (by norm_num) _)) (norm_nonneg _)))
  have hforce : 0 ≤ forceLeg :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) hsig0)
      (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
  have hfractional : 0 ≤ fractionalGradientLeg :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
      (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
  have hgradient : 0 ≤ gradientLeg :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
      (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
  have hE1 : E ≤ 1 := by
    have hpin := epsPin_of_caps (A := 1) zero_le_one hCt
      (by simpa only [one_mul] using hle0) hs.le (hcap hmem L (by omega))
    have hEpow : E ≤ s ^ (4 : ℕ) := by simpa only [one_mul, E] using hpin
    exact hEpow.trans (pow_le_one₀ hs.le hsrange.2)
  let scalarLeg : ℝ := 0
  have hscalar : 0 ≤ scalarLeg := le_refl 0
  have hbound := five_leg_bound_errorWeighted
    (K := CW) (C := 1) (L1 := oscillationLeg) (L2 := forceLeg)
    (L3 := fractionalGradientLeg) (L4 := gradientLeg) (L5 := scalarLeg)
    hCW.le hE1
    hoscillation hforce hfractional hgradient
    (le_refl 0)
    (by
      convert hreal using 1
      dsimp only [oscillationLeg, forceLeg, fractionalGradientLeg, gradientLeg, scalarLeg, E,
        window, companionWindow]
      ring)
  simp only [max_self, mul_one] at hbound
  refine hbound.trans ?_
  calc _ ≤ Ct * (oscillationLeg + forceLeg + fractionalGradientLeg + gradientLeg + scalarLeg) :=
      mul_le_mul_of_nonneg_right hleW
        (add_nonneg (add_nonneg (add_nonneg (add_nonneg hoscillation hforce) hfractional)
          hgradient) hscalar)
    _ = _ := by
      dsimp only [oscillationLeg, forceLeg, fractionalGradientLeg, gradientLeg, scalarLeg, E,
        window, companionWindow]
      ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
