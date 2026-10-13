/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenGaugeScalarCap
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripEnvelopeTwoLeg
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitProducerFold

/-!
# GammaTenInteriorGaugedEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior Besov envelope of the **gauged** `bfF_z`, at one localization cube

ABK26, Step 2 of `l.approximate.recurrence.formula`,
`e.lower.bound.oscillations`, `e.Fz.def`, `e.shom.h.bounds`.

## What this module does

`Closure.GammaTenStripEnvelopeTwoLeg.exists_besovEnvelope_two_legs_interiorMesoCubeGrid`
produces one envelope dominating `|c_1|` times the Besov tower of a first raw
field and `|c_2|` times that of a second.  The body of
`Closure.ClosureInteriorSplit.ClosureInteriorBesovEnvelopeInput` asks instead for
an envelope dominating the towers of the **two gauged legs** of `bfF_z`.  By

* `Closure.GammaTenEnvelopeInputGauge.cubeBesovPositiveVectorPartialSeminormTwo_gauged_localizationFz_potential`
  and `..._flux` --- each gauged tower **is** the corresponding scalar multiple of
  the raw tower, and
* `Closure.GammaTenGaugeScalarCap.abs_gaugeScalar_potential_le` / `..._flux_le`
  --- both scalars are capped by the absolute `4 . 3^9`,

the two statements are the same statement, and this module performs the
substitution at one fixed localization cube.  Nothing analytic happens here: the
per-cell typing data and the two per-depth grid roots are binders.

## What is proved

* `exists_besovEnvelope_gaugedLocalizationFz_interiorMesoCubeGrid` --- the body of
  `ClosureInteriorBesovEnvelopeInput` at one `(M, n, h, K, e, e')` and one mesh
  scale `nmesh`, from the scale bookkeeping, the boundary gate, the numerical
  threshold `hthr`, the gauge-ratio cap `hgauge`, the six cellwise typing binders
  and the two per-depth inputs at the common constant `2 d`.

## Binders

Those of the two-leg envelope, re-read at the closure's own two raw fields (the
Dirichlet corrector gradient and the Neumann flux field of the closure's
families), together with `hgauge` and the descendant-wise `L^2` memberships the
two gauge identities need.  No smallness gate beyond `hthr`, no model estimate
and no stationarity occurs.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.oscillations`, `e.Fz.def`, `e.shom.h.bounds`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The interior grid sits inside the localization cube -/

/-- Every cell of the interior meso grid at a scale below the localization scale
lies in the localization cube: it is a descendant of it. -/
theorem openCubeSet_subset_originCube_of_mem_interiorMesoCubeGrid {K nmesh outer : ℤ}
    (hn : nmesh ≤ K) {R : TriadicCube d}
    (hR : R ∈ interiorMesoCubeGrid d K nmesh outer) :
    openCubeSet R ⊆ openCubeSet (originCube d K) := by
  have hmem := interiorMesoCubeGrid_subset hR
  rw [mesoCubeGrid_eq_descendantsAtDepth hn] at hmem
  exact openCubeSet_subset_of_mem_descendantsAtDepth hmem

/-! ## The gauged two-leg envelope at one localization cube -/

/-- **The body of `ClosureInteriorBesovEnvelopeInput` at one localization cube.**

The two raw fields are the closure's own Dirichlet corrector gradient and Neumann
flux field; the two gauged legs of `bfF_z` are their fixed scalar multiples, and
the two scalars are capped by `4 . 3^9` under `hgauge`.  So the two-leg envelope
of `Closure.GammaTenStripEnvelopeTwoLeg` at `A = 2 d`, `C_g = 4 . 3^9` is exactly
what is wanted.

on the scale bookkeeping `hKp`, `houter`, `hgp`, `hno`, the boundary gate
`hsmall`, `hgamma0`, the numerical threshold `hthr`, the gauge-ratio cap
`hgauge`, the descendant-wise `L^2` memberships `hmemD`, `hmemN`, the six
cellwise typing binders and the two per-depth inputs. -/
theorem exists_besovEnvelope_gaugedLocalizationFz_interiorMesoCubeGrid [NeZero d]
    (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e e' : Vec d)
    {nmesh : ℤ} {p g : ℕ}
    (hKp : (K : ℤ) = nmesh + (p : ℤ)) (houter : n + 1 = nmesh + (g : ℤ)) (hgp : g ≤ p)
    (hno : nmesh ≤ n)
    (hsmall : (d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p) ≤ 1 / 2)
    (hgamma0 : 0 < M.gamma)
    (hthr : 200 * (4 * (2 * (d : ℝ)) * (4 * (3 : ℝ) ^ (9 : ℕ))) ^ (4 : ℕ) *
      M.gamma ^ (4 : ℕ) ≤ 1)
    (hgauge : gaugeRatio (Annealed.sigmaBar M n)
      (Annealed.sigmaBar M (n + (h : ℤ) - 1)) ≤ 4 * (3 : ℝ) ^ (9 : ℕ))
    (hmemD : ∀ (omega : CutoffSample d) (S : TriadicCube d),
      openCubeSet S ⊆ openCubeSet (originCube d (K : ℤ)) →
      MemLp (closureDirichletAlong M n h K e omega.val).toH1Function.grad (2 : ℝ≥0∞)
        (normalizedCubeMeasure S))
    (hmemN : ∀ (omega : CutoffSample d) (S : TriadicCube d),
      openCubeSet S ⊆ openCubeSet (originCube d (K : ℤ)) →
      MemLp (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
          (closureNeumannAlong M n h K e' omega.val)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure S))
    (hmeasD : ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1),
      Measurable fun omega : CutoffSample d => meshOscillationCell (nmesh - (i : ℤ))
        (closureDirichletAlong M n h K e omega.val).toH1Function.grad R')
    (hintD : ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1),
      Integrable (fun omega : CutoffSample d => meshOscillationCell (nmesh - (i : ℤ))
        (closureDirichletAlong M n h K e omega.val).toH1Function.grad R' ^ (4 : ℕ))
        (cutoffSampleLaw M).toMeasure)
    (hmeasN : ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1),
      Measurable fun omega : CutoffSample d => meshOscillationCell (nmesh - (i : ℤ))
        (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
          (closureNeumannAlong M n h K e' omega.val)) R')
    (hintN : ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1),
      Integrable (fun omega : CutoffSample d => meshOscillationCell (nmesh - (i : ℤ))
        (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
          (closureNeumannAlong M n h K e' omega.val)) R' ^ (4 : ℕ))
        (cutoffSampleLaw M).toMeasure)
    (hdepthD : ∀ i : ℕ,
      gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
          (interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1))
          (fun R' omega => meshOscillationCell (nmesh - (i : ℤ))
            (closureDirichletAlong M n h K e omega.val).toH1Function.grad R') ≤
        2 * (d : ℝ) * (M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)))))
    (hdepthN : ∀ i : ℕ,
      gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
          (interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1))
          (fun R' omega => meshOscillationCell (nmesh - (i : ℤ))
            (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
              (closureNeumannAlong M n h K e' omega.val)) R') ≤
        2 * (d : ℝ) * (M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))))) :
    ∃ Bg : TriadicCube d → CutoffSample d → ℝ,
      (∀ R omega, 0 ≤ Bg R omega) ∧
      (∀ R ∈ interiorMesoCubeGrid d (K : ℤ) nmesh n,
        MemLp (Bg R) 4 (cutoffSampleLaw M).toMeasure) ∧
      gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
          (interiorMesoCubeGrid d (K : ℤ) nmesh n) Bg ≤ M.gamma ^ (15 : ℕ) ∧
      (∀ R ∈ interiorMesoCubeGrid d (K : ℤ) nmesh n,
        ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
          (∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R gammaTenBesovExponent N
              (fun x => (blockGaugeUp (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ)
                ((localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
                  (closureDirichletAlong M n h K e omega.val)
                  (closureNeumannAlong M n h K e' omega.val)).eval x)).1) ≤
                Bg R omega) ∧
          (∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R gammaTenBesovExponent N
              (fun x => (blockGaugeUp (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ)
                ((localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
                  (closureDirichletAlong M n h K e omega.val)
                  (closureNeumannAlong M n h K e' omega.val)).eval x)).2) ≤
                Bg R omega)) := by
  classical
  have hnK : nmesh ≤ (K : ℤ) := by omega
  have hc1 : |Real.sqrt (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ) *
      (Real.sqrt (Annealed.sigmaBar M n : ℝ))⁻¹| ≤ 4 * (3 : ℝ) ^ (9 : ℕ) :=
    abs_gaugeScalar_potential_le M n h hgauge
  have hc2 : |(Real.sqrt (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ))⁻¹ *
      Real.sqrt (Annealed.sigmaBar M n : ℝ)| ≤ 4 * (3 : ℝ) ^ (9 : ℕ) :=
    abs_gaugeScalar_flux_le M n h hgauge
  have hA1 : (1 : ℝ) ≤ 2 * (d : ℝ) := by
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
      have hpos := NeZero.pos d
      exact_mod_cast hpos
    linarith
  have hCg1 : (1 : ℝ) ≤ 4 * (3 : ℝ) ^ (9 : ℕ) := by norm_num
  have hmem2D : ∀ (omega : CutoffSample d) (i : ℕ),
      ∀ R' ∈ interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1),
      MemLp (closureDirichletAlong M n h K e omega.val).toH1Function.grad (2 : ℝ≥0∞)
        (normalizedCubeMeasure R') := by
    intro omega i R' hR'
    exact hmemD omega R'
      (openCubeSet_subset_originCube_of_mem_interiorMesoCubeGrid (by omega) hR')
  have hmem2N : ∀ (omega : CutoffSample d) (i : ℕ),
      ∀ R' ∈ interiorMesoCubeGrid d (K : ℤ) (nmesh - (i : ℤ)) (n - 1),
      MemLp (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
          (closureNeumannAlong M n h K e' omega.val)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure R') := by
    intro omega i R' hR'
    exact hmemN omega R'
      (openCubeSet_subset_originCube_of_mem_interiorMesoCubeGrid (by omega) hR')
  obtain ⟨B, hB0, hBmem, hBroot, hBdom⟩ :=
    exists_besovEnvelope_two_legs_interiorMesoCubeGrid (cutoffSampleLaw M).toMeasure
      hKp houter hgp hno hsmall
      (fun omega : CutoffSample d =>
        (closureDirichletAlong M n h K e omega.val).toH1Function.grad)
      (fun omega : CutoffSample d =>
        neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
          (closureNeumannAlong M n h K e' omega.val))
      hgamma0 hA1 hCg1 hthr hc1 hc2
      hmeasD hintD hmem2D hmeasN hintN hmem2N hdepthD hdepthN
  refine ⟨B, hB0, hBmem, hBroot, ?_⟩
  intro R hR
  have hRsub : openCubeSet R ⊆ openCubeSet (originCube d (K : ℤ)) :=
    openCubeSet_subset_originCube_of_mem_interiorMesoCubeGrid hnK hR
  filter_upwards [hBdom R hR] with omega hom
  constructor
  · intro N
    have hid := cubeBesovPositiveVectorPartialSeminormTwo_gauged_localizationFz_potential
      (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ) (Annealed.sigmaBar M n) omega.val n
      (n + (h : ℤ)) e' R (closureDirichletAlong M n h K e omega.val)
      (closureNeumannAlong M n h K e' omega.val) gammaTenBesovExponent N
      (fun _ _ S hS => hmemD omega S
        (subset_trans (openCubeSet_subset_of_mem_descendantsAtDepth hS) hRsub))
    rw [hid]
    exact (hom N).1
  · intro N
    have hid := cubeBesovPositiveVectorPartialSeminormTwo_gauged_localizationFz_flux
      (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ) (Annealed.sigmaBar M n) omega.val n
      (n + (h : ℤ)) e' R (closureDirichletAlong M n h K e omega.val)
      (closureNeumannAlong M n h K e' omega.val) gammaTenBesovExponent N
      (fun _ _ S hS => hmemN omega S
        (subset_trans (openCubeSet_subset_of_mem_descendantsAtDepth hS) hRsub))
    rw [hid]
    exact (hom N).2

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
