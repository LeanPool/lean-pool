/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourBoundaryJoinDatumSplitErrorWeighted
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourHarmonicWindowSeam
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringTrace
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CorrectorComposed
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryComposeGlue
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepDatumZeroTrace

/-!
# StepFourBoundaryDatumPackage

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary competitor package, and the Step-4 decay at every centre

## What is delivered

`excessDecay_stepFour_slot_allCentres_datumSplit_errorWeighted` carries a
disjunction at
every scale: either the interior cube gate `z + □_{n-2} ⊆ □_m`, or a met face
together with the manuscript's datum-split competitor package `(V, v₁, ℓ)`.  At
a boundary lattice centre the gate holds at no scale of the Step-4 chain (a
lattice centre `z = 3^n v ∉ □_{m-1}` sits at distance `≥ 3^n/2` from `∂□_m`, so
the gate fails for every `j > n+2` while the chain needs `j` up to `m-1`), so
the package branch is the only one available.

This module produces that package from the slot's own moved-cube replacement
pair:

* `truncatedWindow_subset_movedCube_self` — the `U₂` carrier identification at
  equal index.  The inclusion is not "one scale down":
  `truncatedWindow_subset_image_add_wellPlacedCentre` takes `j ≤ k`, so at `j =
  k` the §4.4 window sits inside the anchor's moved cube of the same index.
  The harmonic domain therefore does transfer, by `H1Function.restrict` (which
  shares `toFun` definitionally) and `isWeaklyHarmonicOn_restrict`.
* `localizedZeroTrace_movedCubeCorrector` — the `H¹₀` corrector of the
  replacement pair lives on the moved cube, which is strictly larger than the
  §4.4 window, so it is *not* an `H¹₀(U₂)` function; but the odd-reflection glue
  only ever reads its face-only localized zero trace, and
  `localizedZeroTraceFunctionOn_of_memH10_of_inter_subset` supplies exactly that
  (`reflectedWindow ∩ movedCube ⊆ reflectedWindow ∩ □_m = U₂`).
* `exists_datumSplitPackage_movedCubePair` — the four package clauses (`MemLp
  V`, the packaging identity, the corrector's `L^∞` bound, the two face
  identities, the harmonic class) from `CorrectorComposed`'s
  `exists_residualCorrector_affineLift`, the affine-split odd competitor, the
  partial reflection and the harmonic representative.
* `excessDecay_stepFour_decay_allCentres_datumSplit` — the slot with the
  disjunction discharged at every centre.

## The one carried input, named exactly

`hgradh : HasGradientOn (truncatedWindow z m (n-2)) h.toFun h.grad`.

This is the **classical `C¹` half** of the print's `h ∈ C^{1,\nicefrac12}(□_m)`
(ABK26 for `t.regularity`; for `l.excess.decay.good.scales`), i.e. that
`h.grad` is the gradient of `h` and not merely a weak gradient.
`AffineSplitLift` already treats the pair `(HasGradientOn,
HolderSeminormBoundOn)` as the two halves of `h ∈ C^{1,1/2}` and carries both.
It is a genuine premise of the printed statement, not a proof step
promoted to a hypothesis.

## References

* ABK26, `t.regularity`, (the datum `h ∈ C^{1,1/2}(□_m)`);
  `l.excess.decay.good.scales`, (the datum); Steps 4--5.
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

/-- **The `U₂` carrier identification, at equal index.**

The inclusion is not "one scale down".  The proved
`truncatedWindow_subset_image_add_wellPlacedCentre` takes `j <= k`, so at `j =
k` the truncated window sits inside the moved cube of the same index. -/
theorem truncatedWindow_subset_movedCube_self {m k : ℤ} (z : Vec d) (hkm : k ≤ m) :
    truncatedWindow z m k ⊆
      (fun y => wellPlacedCentre z m k + y) '' openCubeSet (originCube d k) :=
  truncatedWindow_subset_image_add_wellPlacedCentre z hkm le_rfl

/-- The reflected window meets the moved cube only inside the truncated window. -/
theorem reflectedWindow_inter_movedCube_subset {m k : ℤ} (z : Vec d) (hkm : k ≤ m) :
    reflectedWindow z m k ∩
        ((fun y => wellPlacedCentre z m k + y) '' openCubeSet (originCube d k)) ⊆
      truncatedWindow z m k := by
  intro p hp
  have hpm : p ∈ openCubeSet (originCube d m) :=
    image_add_wellPlacedCentre_subset_openCubeSet z hkm hp.2
  have h : p ∈ reflectedWindow z m k ∩ openCubeSet (originCube d m) := ⟨hp.1, hpm⟩
  rwa [reflectedWindow_inter_openCubeSet z m k] at h

/-- The moved-cube corrector has the zero trace on the truncated window. -/
theorem localizedZeroTrace_movedCubeCorrector {m k : ℤ} {z : Vec d} (hkm : k ≤ m)
    (w : H10Function
      ((fun y => wellPlacedCentre z m k + y) '' openCubeSet (originCube d k))) :
    LocalizedZeroTraceFunctionOn (truncatedWindow z m k) (reflectedWindow z m k)
      w.toH1Function.toFun :=
  localizedZeroTraceFunctionOn_of_memH10_of_inter_subset
    (isOpen_truncatedWindow z m k) (truncatedWindow_subset_movedCube_self z hkm)
    (reflectedWindow_inter_movedCube_subset z hkm) w

/-- **The datum-split competitor package.**

Every clause of the second disjunct of
`excessDecay_stepFour_slot_allCentres_datumSplit_errorWeighted`,
produced at a boundary centre from the slot's OWN moved-cube replacement pair.
The only input beyond the slot's binders is `hgradh`, the classical `C¹` half
of the printed datum hypothesis `h ∈ C^{1,1/2}(□_m)`. -/
theorem exists_datumSplitPackage_movedCubePair [NeZero d] {m n : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m)
    (u hdat : H1Function (openCubeSet (originCube d m)))
    (hDir : MemH10 (openCubeSet (originCube d m))
      (fun y => u.toFun y - hdat.toFun y))
    {v : H1Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
        openCubeSet (originCube d (n - 2)))}
    {w : H10Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
        openCubeSet (originCube d (n - 2)))}
    (hvharm : IsWeaklyHarmonicOn ((fun y => wellPlacedCentre z m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2))) v)
    (hval : ∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y)
    {Kh : ℝ} (hKh : 0 ≤ Kh)
    (hgradh : HasGradientOn (truncatedWindow z m (n - 2)) hdat.toFun hdat.grad)
    (hHol : HolderSeminormBoundOn (truncatedWindow z m (n - 2)) (1 / 2 : ℝ) Kh
      hdat.grad) :
    ∃ (V v₁ : Vec d → ℝ) (cl : ℝ) (Al : Vec d),
      MemLp V 2 (volume.restrict (reflectedWindow z m (n - 2))) ∧
      V =ᵐ[volume.restrict (truncatedWindow z m (n - 2))]
        (fun y => v.toFun y - affineLift z cl Al y - v₁ y) ∧
      (∀ᵐ y ∂(volume.restrict (truncatedWindow z m (n - 2))),
        |v₁ y| ≤ datumResidualBound d n Kh) ∧
      (∀ l : Fin d, MeetsUpperFace z m (n - 2) l →
        ∀ y ∈ reflectedWindow z m (n - 2),
          V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) ∧
      (∀ l : Fin d, MeetsLowerFace z m (n - 2) l →
        ∀ y ∈ reflectedWindow z m (n - 2),
          V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) ∧
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
          reflectedWindow z m (n - 2)) := by
  classical
  have hkm : n - 2 ≤ m := le_of_lt hmn
  have hopen : IsOpen (truncatedWindow z m (n - 2)) := isOpen_truncatedWindow z m (n - 2)
  have hsub : truncatedWindow z m (n - 2) ⊆
      (fun y => wellPlacedCentre z m (n - 2) + y) ''
        openCubeSet (originCube d (n - 2)) :=
    truncatedWindow_subset_movedCube_self z hkm
  -- the replacement, read on the §4.4 window (SAME `toFun`)
  set v' : H1Function (truncatedWindow z m (n - 2)) := v.restrict hopen hsub with hv'def
  have hv'harm : IsWeaklyHarmonicOn (truncatedWindow z m (n - 2)) v' :=
    isWeaklyHarmonicOn_restrict hopen hsub hvharm
  have hv'val : ∀ y, v'.toFun y = v.toFun y := fun _ => rfl
  -- the datum corrector
  have hzU : z ∈ truncatedWindow z m (n - 2) := mem_truncatedWindow_self (n - 2) hz
  have hdiam : ∀ p ∈ truncatedWindow z m (n - 2), ‖p - z‖ ≤ (3 : ℝ) ^ (n - 2) / 2 :=
    fun p hp => norm_sub_le_of_mem_truncatedWindow hp
  have hint : ∀ i, IntegrableOn (fun p => hdat.grad p i)
      (truncatedWindow z m (n - 2)) volume :=
    fun i => integrableOn_coord_of_holderSeminormBoundOn hopen.measurableSet
      (ne_of_lt (volume_truncatedWindow_lt_top z m (n - 2))) hzU hKh hHol hdiam i
  obtain ⟨Psi, v₁, hPsi, hv₁harm, hv₁Psi, hv₁bd⟩ :=
    exists_residualCorrector_affineLift (k := n - 2) hz hdat hKh hint hgradh hHol
  set cl : ℝ := hdat.toFun z with hcldef
  set Al : Vec d := volumeAverageVec (truncatedWindow z m (n - 2)) hdat.grad with hAldef
  -- the face-only zero trace of the odd competitor
  have h1 : LocalizedZeroTraceFunctionOn (truncatedWindow z m (n - 2))
      (reflectedWindow z m (n - 2)) (fun y => v'.toFun y - u.toFun y) := by
    have hw := localizedZeroTrace_movedCubeCorrector (z := z) hkm w
    have hneg := localizedZeroTraceFunctionOn_neg hw
    refine localizedZeroTraceFunctionOn_congr (fun y => ?_) hneg
    rw [hv'val y, hval y]
    ring
  have h2 : LocalizedZeroTraceFunctionOn (truncatedWindow z m (n - 2))
      (reflectedWindow z m (n - 2)) (fun y => u.toFun y - hdat.toFun y) :=
    localizedZeroTraceFunctionOn_truncatedWindow_of_memH10_cube z hDir
  have h3 : LocalizedZeroTraceFunctionOn (truncatedWindow z m (n - 2))
      (reflectedWindow z m (n - 2))
      (fun y => hdat.toFun y - affineLift z cl Al y - Psi.toFun y) :=
    localizedZeroTraceFunctionOn_of_forall_eq_zero hopen.measurableSet
      (fun y hy => by rw [hPsi y hy]; ring)
  have h4 : LocalizedZeroTraceFunctionOn (truncatedWindow z m (n - 2))
      (reflectedWindow z m (n - 2)) (fun y => Psi.toFun y - v₁.toFun y) := by
    have hneg := memH10_neg hv₁Psi
    refine localizedZeroTraceFunctionOn_of_memH10 ?_
    have hfun : (fun y => -(v₁.toFun y - Psi.toFun y))
        = fun y => Psi.toFun y - v₁.toFun y := by
      funext y; ring
    rwa [hfun] at hneg
  have h12 := localizedZeroTraceFunctionOn_add h1 h2
  have h34 := localizedZeroTraceFunctionOn_add h3 h4
  have hzt : LocalizedZeroTraceFunctionOn (truncatedWindow z m (n - 2))
      (reflectedWindow z m (n - 2))
      (fun y => v'.toFun y - affineLift z cl Al y - v₁.toFun y) :=
    localizedZeroTraceFunctionOn_congr (fun y => by ring)
      (localizedZeroTraceFunctionOn_add h12 h34)
  -- the odd competitor and its reflection
  obtain ⟨vodd, hvoddharm, heq⟩ :=
    exists_h1_oddCompetitor_affineSplit hv'harm hv₁harm cl Al
  have hzt' : LocalizedZeroTraceFunctionOn (truncatedWindow z m (n - 2))
      (reflectedWindow z m (n - 2)) vodd.toFun :=
    localizedZeroTraceFunctionOn_congr (fun y => (heq y).symm) hzt
  obtain ⟨W, hWharm, hWpin, hWodd⟩ :=
    exists_h1_oddReflection_reflectedWindow hmn vodd hvoddharm hzt'
  obtain ⟨V, hVharm, hVmem, hVae⟩ :=
    exists_classicalCompetitor_reflectedWindow z m (n - 2) hWharm
  obtain ⟨hup, hlow⟩ :=
    faceOdd_eqOn_reflectedWindow_of_ae hmn hVharm hVae
      (fun i hi => (hWodd i).1 hi) (fun i hi => (hWodd i).2 hi)
  refine ⟨V, v₁.toFun, cl, Al, hVmem.restrict _, ?_, ?_, hup, hlow, hVharm⟩
  · have hWae : V =ᵐ[volume.restrict (truncatedWindow z m (n - 2))] W.toFun :=
      hVae.filter_mono (MeasureTheory.ae_mono (Measure.restrict_mono
        (truncatedWindow_subset_reflectedWindow z m (n - 2)) le_rfl))
    filter_upwards [hWae, MeasureTheory.self_mem_ae_restrict
      (measurableSet_truncatedWindow z m (n - 2))] with y hy hymem
    rw [hy, hWpin y hymem, heq y, hv'val y]
  · exact hv₁bd

/-! ## 2. The slot with the competitor disjunction discharged -/

/-- **The Step-4 decay at every centre, the disjunction discharged.**

The slot with its competitor disjunction produced rather than carried, so the
boundary branch is available at a centre where the interior cube gate holds at
no scale.  The binder block is the slot's own, plus the classical `C¹` half
`hgradh` of the printed datum hypothesis `h ∈ C^{1,1/2}(□_m)`; see the module
docstring. -/
theorem excessDecay_stepFour_decay_allCentres_datumSplit (d : ℕ) [NeZero d] (hd : d ≠ 0) :
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
                        MemLp v.toFun 2 (volume.restrict (truncatedWindow z m n)) →
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
    excessDecay_stepFour_slot_allCentres_datumSplit_errorWeighted d hd
  refine ⟨C, Ccap, Cb, hC, hCcap, hCb, k₀, hk₀, ?_⟩
  intro k hk M s hsrange hregime hregimecap hs delta hdelta hprice hfundcap hgate L m hmL
    z hz
  filter_upwards [hslot k hk M s hsrange hregime hregimecap hs delta hdelta hprice hfundcap
    hgate L m hmL z hz] with omega hom
  intro n hnm hmem u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv hvn Kh hKh hHol
    hgradh c gmin hmin
  obtain ⟨V, v₁, cl, Al, hVmem, hVae, hv₁bd, hup, hlow, hharmclass⟩ :=
    exists_datumSplitPackage_movedCubePair (n := n) hz (by omega) u hdat
      (by
        obtain ⟨wd, hwval, _⟩ := hsol.1
        exact ⟨wd, funext fun y => by rw [hwval y]; ring⟩)
      hharmv hval hKh hgradh hHol
  exact hom n hnm hmem u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv V v₁ cl Al
    Kh hKh hvn hVmem hVae hv₁bd hup hlow hharmclass c gmin hmin


end

end Algsuperdiff.Section4.Provider.Regularity
