/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourBoundaryDatumPackage

/-!
# StepFourBoundaryPairTrim

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The trimmed harmonic replacement pair, and the `hvn` residue produced

## The residue

Every statement of the boundary lane carries

```text
   hvn : MemLp v.toFun 2 (volume.restrict (truncatedWindow z m n))
```

as a hypothesis — a standing residue.  It has no producer, and for a good
reason: `v = u - w` with `w ∈ H¹₀(moved cube)`, and an `H¹₀` witness constrains
its function only on its own domain (`H10Function`'s `memL2`, `gradMemL2`, `hasWeakGradient`
and `tendsto_approx` are all read on `volume.restrict U`), so `w.toFun` is
unconstrained off the cube and `v.toFun` need not be in `L²` of any larger
window.

## The fix, and why it is not a cheat

Re-read the pair with `w` replaced by `1_U · w`.  So
`exists_harmonicReplacementPair_movedCube_memLp` delivers the pair with `hvn`
included, and `excessDecay_stepFour_decay_allCentres_datumSplit_trimmed` is the
Step-4 slot with both the competitor disjunction and `hvn` gone.

## What remains

Exactly one carried input: `hgradh: HasGradientOn (truncatedWindow z m (n-2))
h.toFun h.grad`, the classical `C¹` half of the print's `h ∈ C^{1,1/2}(□_m)`,
which the frozen root's binder block does not carry.

## References

* ABK26, `l.excess.decay.good.scales`; `t.regularity` Step 4.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory InnerProductSpace
open Algsuperdiff.Section3
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem hasWeakGradientOn_congr_on {U : Set (Vec d)} (hU : MeasurableSet U)
    {f g : Vec d → ℝ} {Du : Vec d → Vec d} (hfg : ∀ y ∈ U, f y = g y)
    (hf : HasWeakGradientOn U f Du) : HasWeakGradientOn U g Du := by
  intro i phi hphi hphic hphiU
  have h := hf i phi hphi hphic hphiU
  rw [← h]
  exact setIntegral_congr_fun hU (fun x hx => by rw [hfg x hx])

theorem ae_eq_of_forall_mem {U : Set (Vec d)} (hU : MeasurableSet U)
    {f g : Vec d → ℝ} (hfg : ∀ y ∈ U, f y = g y) :
    f =ᵐ[volume.restrict U] g :=
  Filter.eventuallyEq_of_mem (self_mem_ae_restrict hU) hfg

/-- Re-reading an `H¹(U)` function as `1_U · f`: the `H¹` structure sees only `U`. -/
def h1Trim {U : Set (Vec d)} (hU : MeasurableSet U) (v : H1Function U) :
    H1Function U where
  toFun := Set.indicator U v.toFun
  grad := v.grad
  memL2 := by
    refine (memLp_congr_ae (ae_eq_of_forall_mem hU (f := v.toFun) ?_)).mp v.memL2
    intro y hy
    rw [Set.indicator_of_mem hy]
  gradMemL2 := v.gradMemL2
  hasWeakGradient :=
    hasWeakGradientOn_congr_on hU (fun y hy => (Set.indicator_of_mem hy v.toFun).symm)
      v.hasWeakGradient

@[simp] theorem h1Trim_toFun {U : Set (Vec d)} (hU : MeasurableSet U)
    (v : H1Function U) : (h1Trim hU v).toFun = Set.indicator U v.toFun := rfl

@[simp] theorem h1Trim_grad {U : Set (Vec d)} (hU : MeasurableSet U)
    (v : H1Function U) : (h1Trim hU v).grad = v.grad := rfl

/-- The same re-reading for an `H¹₀(U)` function. -/
def h10Trim {U : Set (Vec d)} (hU : MeasurableSet U) (w : H10Function U) :
    H10Function U where
  toH1Function := h1Trim hU w.toH1Function
  approx := w.approx
  approx_smooth := w.approx_smooth
  approx_hasCompactSupport := w.approx_hasCompactSupport
  approx_support_subset := w.approx_support_subset
  tendsto_approx := by
    refine w.tendsto_approx.congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    refine ae_eq_of_forall_mem hU ?_
    intro y hy
    show w.approx n y - w.toH1Function.toFun y
      = w.approx n y - Set.indicator U w.toH1Function.toFun y
    rw [Set.indicator_of_mem hy]
  tendsto_approx_grad := fun i => w.tendsto_approx_grad i

@[simp] theorem h10Trim_toFun {U : Set (Vec d)} (hU : MeasurableSet U)
    (w : H10Function U) :
    (h10Trim hU w).toH1Function.toFun = Set.indicator U w.toH1Function.toFun := rfl

/-- Membership in `L²` of the trimmed corrector, on ANY window. -/
theorem memLp_indicator_of_memL2 {U W : Set (Vec d)} (hU : MeasurableSet U)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    MemLp (Set.indicator U f) 2 (volume.restrict W) := by
  have h1 : MemLp (Set.indicator U f) 2 (volume : Measure (Vec d)) := by
    have h := (memLp_indicator_iff_restrict hU (μ := (volume : Measure (Vec d)))
      (p := 2) (f := f)).mpr hf
    exact h
  exact h1.restrict W

/-- **The trimmed harmonic replacement pair.**

The pair at the moved cube, re-read so that the `H¹₀` corrector vanishes off its
own cube.  Every clause of the original is preserved and the pair now also
carries `MemLp v.toFun 2` on every window — the standing residue `hvn` of the
boundary Step-4 slot. -/
theorem exists_harmonicReplacementPair_movedCube_memLp [NeZero d] {m n : ℤ}
    {z : Vec d} (hnm : n - 2 ≤ m) (u : H1Function (openCubeSet (originCube d m))) :
    ∃ (v : H1Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
          openCubeSet (originCube d (n - 2))))
      (w : H10Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
          openCubeSet (originCube d (n - 2)))),
      IsWeaklyHarmonicOn ((fun y => wellPlacedCentre z m (n - 2) + y) ''
          openCubeSet (originCube d (n - 2))) v ∧
        (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) ∧
        (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) ∧
        ∀ W : Set (Vec d), MemLp u.toFun 2 (volume.restrict W) →
          MemLp v.toFun 2 (volume.restrict W) := by
  classical
  obtain ⟨v, w, hharm, hval, hgrad⟩ :=
    exists_harmonicReplacementPair_movedCube (m := m) (n := n) (z := z) hnm u
  have hUmeas : MeasurableSet ((fun y => wellPlacedCentre z m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2))) :=
    (isOpen_image_add_openCubeSet_originCube _ _).measurableSet
  refine ⟨{ toFun := fun y => u.toFun y -
              Set.indicator ((fun y => wellPlacedCentre z m (n - 2) + y) ''
                openCubeSet (originCube d (n - 2))) w.toH1Function.toFun y
            grad := v.grad
            memL2 := ?_
            gradMemL2 := v.gradMemL2
            hasWeakGradient := ?_ }, h10Trim hUmeas w, ?_, ?_, ?_, ?_⟩
  · refine (memLp_congr_ae (ae_eq_of_forall_mem hUmeas (f := v.toFun) ?_)).mp v.memL2
    intro y hy
    rw [Set.indicator_of_mem hy, hval y]
  · refine hasWeakGradientOn_congr_on hUmeas (f := v.toFun) ?_ v.hasWeakGradient
    intro y hy
    rw [Set.indicator_of_mem hy, hval y]
  · exact hharm
  · intro y; rfl
  · intro y; exact hgrad y
  · intro W hu
    have hw2 : MemLp (Set.indicator ((fun y => wellPlacedCentre z m (n - 2) + y) ''
        openCubeSet (originCube d (n - 2))) w.toH1Function.toFun) 2
        (volume.restrict W) :=
      memLp_indicator_of_memL2 hUmeas w.toH1Function.memL2
    exact hu.sub hw2

/-! ## 3. The slot with the disjunction AND `hvn` discharged -/

/-- **The Step-4 decay at every centre, both boundary residues gone.**

The slot of `StepFourBoundaryDatumPackage` with the harmonic replacement pair
produced internally in its trimmed form, so that `hvn` disappears from the
binder block.  What is left is the slot's
own data plus the single input `hgradh` — the classical `C¹` half of the
printed datum hypothesis `h ∈ C^{1,1/2}(□_m)`, which the frozen root does
not carry. -/
theorem excessDecay_stepFour_decay_allCentres_datumSplit_trimmed (d : ℕ) [NeZero d]
    (hd : d ≠ 0) :
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
                        ∀ Kh : ℝ, 0 ≤ Kh →
                        HolderSeminormBoundOn (truncatedWindow z m (n - 2)) (1 / 2 : ℝ)
                          Kh hdat.grad →
                        -- `h ∈ C^{1,1/2}(□_m)`
                        HasGradientOn (truncatedWindow z m (n - 2)) hdat.toFun
                          hdat.grad →
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
    excessDecay_stepFour_decay_allCentres_datumSplit d hd
  refine ⟨C, Ccap, Cb, hC, hCcap, hCb, k₀, hk₀, ?_⟩
  intro k hk M s hsrange hregime hregimecap hs delta hdelta hprice hfundcap hgate L m hmL
    z hz
  filter_upwards [hslot k hk M s hsrange hregime hregimecap hs delta hdelta hprice hfundcap
    hgate L m hmL z hz] with omega hom
  intro n hnm hmem u hdat gflux hsol hgL2 hgW hhW Kh hKh hHol hgradh c gmin hmin
  obtain ⟨v, w, hharmv, hval, hgradv, hmem2⟩ :=
    exists_harmonicReplacementPair_movedCube_memLp (m := m) (n := n) (z := z)
      (by omega) u
  have hu : MemLp u.toFun 2 (volume.restrict (truncatedWindow z m n)) :=
    u.memL2.mono_measure (Measure.restrict_mono (truncatedWindow_subset_domain z m n) le_rfl)
  exact hom n hnm hmem u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv
    (hmem2 _ hu) Kh hKh hHol hgradh c gmin hmin

end

end Algsuperdiff.Section4.Provider.Regularity
