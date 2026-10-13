/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationEnvelopeHenv
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationEnvelopeMesh
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CorrectorMeasurableQuartic

/-!
# LocalizationEnvelopeWire

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
NOTE: this module is an ordinary Provider helper / conditional A.  The binder
descriptions below are an informal inventory only.

# The oscillation grid fourth moment with the sample-space binders gone

Source displays in ABK26:

* `e.lower.bound.oscillations` (label; display);
* `e.nablaw.in.L.eight` (label; display);
* `e.def.w` (label);
* `e.recurrence.params` (label).

## What this module is

`LocalizationEnvelopeGrid` proves the grid fourth-moment bound with the
envelope derived, but its own inventory lists three sample-space hypotheses it
must assume:

* `hTm : A Tfluct mu`;
* `hcellInt`, integrability in the sample of the window fourth energies;
* `hglobInt`, integrability in the sample of the global fourth energy.

This module removes all three, using the quartic measurability of
`Corrector.CorrectorMeasurableQuartic`.  Two observations do the work.

1. **A measurable fluctuation dominated by the given one.**  Write
   `G(omega) = fint_{cu_K} |u(omega)|^4` for the global fourth energy.  This is
   a measurable function of the sample, by the quartic layer.  Put

   ```
     T'(omega) = max( sqrt(G(omega)) - Chead , 0 ) .
   ```

   Then `T'` is measurable and nonnegative by construction; it satisfies
   `G <= (Chead + T')^2` by construction; and `T' <= T` pointwise, because the
   spatial `L^4 <= L^8` bridge turns the caller's `L^8` bound into
   `G <= (Chead + T)^2`.  A pointwise-smaller variable inherits the
   stretched-exponential tail (`IsBigOWith.of_le`), so `T'` is an
   `O_{Gamma_1}(A)` variable with the *same* amplitude.  The whole envelope
   derivation now runs on `T'`, whose measurability is a theorem rather than a
   hypothesis.

2. **Integrability by domination.**  `G` is measurable and squeezed between `0`
   and `2 Chead^2 + 2 T'^2`, whose second moment is finite by the tail; and each
   window fourth energy is measurable and at most a fixed volume ratio times
   `G`, the window being contained in `cu_K`.

## What is proved

* `gridFourthMoment_mesoWindowEnergy_le_of_measurable_fourthEnergy` -- the
  generic form: the grid fourth-moment bound with `hTm`, `hcellInt` and
  `hglobInt` replaced by measurability of the two fourth-energy observables.
* `exists_freshShell_gridFourthMoment_mesoWindowEnergy_le_wired` -- the same at
  the **actual** correctors of `e.def.w`, where the two measurability
  hypotheses are themselves theorems, so that no sample-space binder of any
  kind survives.

## Which binders die and which survive

Relative to `exists_freshShell_gridFourthMoment_mesoWindowEnergy_le`, the three
sample-space binders `A Tfluct`, `hcellInt` and `hglobInt` are **gone**.  What
survives, and is disclosed below, is exactly:

* the model and parameter gates of `e.recurrence.params` and the two direction
  bounds -- unchanged;
* the two interior-grid scale gates `n <= K - 1`, `n + N <= K - 1` -- unchanged;
* the caller's family of weak solutions of `e.def.w` -- unchanged;
* the **spatial** binders `hmem` (`L^8` membership on `cu_K`), `hcoord`, `hsq`,
  `hfour` (integrability on `cu_K` of the coordinate squares, of `|u|^2` and of
  `|u|^4`).  These are statements about a single sample point; nothing in the
  measurability layer bears on them and none of them is assumed away.

In the generic form one further binder appears that the source form did not
need: `hChead : 0 <= Chead`.  It is used to compare `sqrt(G)` with `Chead + T`,
and at the actual correctors it is supplied by the positivity of `Chead` that
`e.nablaw.in.L.eight` produces.

## What is not proved here

* **The second inequality, `<= cgamma^{15}`, is untouched.**
* **The forcing term of the display is untouched.**
* **The per-site estimate `e.nablaw.oscillations` is not inserted here.**
* **No measurable selection of correctors is used.**  The corrector families
  are arbitrary weak-solution families; their gradients are measurable because
  the solution operator is continuous, not because a selection was made.

## Scope

It records no availability status.

## Divergences from the printed statement

The divergences of `LocalizationEnvelopeGrid` carry over unchanged:, and the
two added interior scale gates.  No new divergence is introduced.

## References

* ABK26, `e.lower.bound.oscillations`; `e.nablaw.in.L.eight`; `e.def.w`, display
  (label); `e.recurrence.params`, display (label), with the `h` gate.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book.Ch03
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## The window is dominated by the cube -/

/-- The window fourth energy is at most the volume ratio times the global
fourth energy, for any window contained in `cu_K`.

: the caller supplies `hsub` (the containment) and `hfour` (integrability of
`|u|^4` on `cu_K`). -/
private theorem mesoWindowFourthEnergy_le_ratio_mul_originCubeFourthEnergy
    {K ell : ℤ} {R : TriadicCube d} (u : Vec d → Vec d)
    (hsub : openCubeAtScale (triadicCubeShift R) ell ⊆ openCubeSet (originCube d K))
    (hfour : IntegrableOn (fun x => vecNormSq (u x) ^ 2)
      (openCubeSet (originCube d K)) volume) :
    mesoWindowFourthEnergy ell u R ≤
      (volume (openCubeAtScale (triadicCubeShift R) ell)).toReal⁻¹ *
          (volume (openCubeSet (originCube d K))).toReal *
        originCubeFourthEnergy K u := by
  have hWpos : (0 : ℝ) < (volume (openCubeSet (originCube d K))).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos _
  have hVnn : (0 : ℝ) ≤
      (volume (openCubeAtScale (triadicCubeShift R) ell)).toReal⁻¹ := by
    positivity
  have hmono : ∫ x in openCubeAtScale (triadicCubeShift R) ell,
        vecNormSq (u x) ^ 2 ∂volume ≤
      ∫ x in openCubeSet (originCube d K), vecNormSq (u x) ^ 2 ∂volume :=
    setIntegral_mono_set hfour
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) hsub.eventuallyLE
  have hcancel : (volume (openCubeSet (originCube d K))).toReal *
      originCubeFourthEnergy K u =
        ∫ x in openCubeSet (originCube d K), vecNormSq (u x) ^ 2 ∂volume := by
    unfold originCubeFourthEnergy volumeAverage
    field_simp
  show (volume (openCubeAtScale (triadicCubeShift R) ell)).toReal⁻¹ *
      ∫ x in openCubeAtScale (triadicCubeShift R) ell,
        vecNormSq (u x) ^ 2 ∂volume ≤ _
  calc (volume (openCubeAtScale (triadicCubeShift R) ell)).toReal⁻¹ *
        ∫ x in openCubeAtScale (triadicCubeShift R) ell, vecNormSq (u x) ^ 2 ∂volume
      ≤ (volume (openCubeAtScale (triadicCubeShift R) ell)).toReal⁻¹ *
          ∫ x in openCubeSet (originCube d K), vecNormSq (u x) ^ 2 ∂volume :=
        mul_le_mul_of_nonneg_left hmono hVnn
    _ = (volume (openCubeAtScale (triadicCubeShift R) ell)).toReal⁻¹ *
          (volume (openCubeSet (originCube d K))).toReal *
            originCubeFourthEnergy K u := by rw [← hcancel]; ring

/-! ## The generic wired form -/

/-- **The grid fourth-moment bound with the three sample-space binders gone.**

The hypotheses `hTm : A T mu`, `hcellInt` and `hglobInt` of
`gridFourthMoment_mesoWindowEnergy_le_of_cubeEuclideanL8_pathwise` are replaced
by measurability of the two fourth-energy observables, which the quartic layer
proves outright at the correctors.  The fluctuation `T` itself is still allowed
to be an arbitrary nonnegative `O_{Gamma_1}(A)` variable with no measurability
property: the proof never uses `T` except through the pointwise-smaller
measurable variable `T'` built from the global fourth energy.

Complete binder census, beyond the typing binders `d, Omega, its
MeasurableSpace instance, mu, K, n, N, u, Chead, A, T`:

* `[IsProbabilityMeasure mu]` -- instance binder;
* `hn : n <= K - 1`, `hN : n + N <= K - 1` -- the interior-grid scale gates;
* `hChead : 0 <= Chead`, `hA : 0 < A`;
* `hT0 : forall omega, 0 <= T omega`;
* `hT : IsBigOWith mu (gammaSigma 1) T A`;
* `hmem`, `hpath` -- the spatial `L^8` membership and the pathwise `L^8` bound;
* `hcoord`, `hsq`, `hfour` -- the three spatial integrability families on
  `cu_K`;
* `hglobMeas`, `hcellMeas` -- measurability in the sample of the global and of
  the window fourth energies.

No a.e.-measurability of `T` and no integrability in the sample is assumed. -/
theorem gridFourthMoment_mesoWindowEnergy_le_of_measurable_fourthEnergy
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {K n : ℤ} {N : ℕ} (hn : n ≤ K - 1) (hN : n + (N : ℤ) ≤ K - 1)
    (u : Ω → Vec d → Vec d) {Chead A : ℝ} (hChead : 0 ≤ Chead) (hA : 0 < A)
    {T : Ω → ℝ} (hT0 : ∀ ω, 0 ≤ T ω)
    (hT : IndependentSums.IsBigOWith μ (IndependentSums.gammaSigma 1) T A)
    (hmem : ∀ ω, MemLp (fun x => Book.Ch02.vecNorm (u ω x)) 8
      (normalizedCubeMeasure (originCube d K)))
    (hpath : ∀ ω, Corrector.cubeEuclideanLpNorm (originCube d K) 8 (u ω) ^ (2 : ℕ) ≤
      Chead + T ω)
    (hcoord : ∀ (ω : Ω) (k : Fin d), IntegrableOn (fun x => (u ω x k) ^ 2)
      (openCubeSet (originCube d K)) volume)
    (hsq : ∀ ω, IntegrableOn (fun x => vecNormSq (u ω x))
      (openCubeSet (originCube d K)) volume)
    (hfour : ∀ ω, IntegrableOn (fun x => vecNormSq (u ω x) ^ 2)
      (openCubeSet (originCube d K)) volume)
    (hglobMeas : Measurable fun ω => originCubeFourthEnergy K (u ω))
    (hcellMeas : ∀ R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1),
      Measurable fun ω => mesoWindowFourthEnergy (n + (N : ℤ)) (u ω) R) :
    gridFourthMoment μ (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
        (fun R ω => mesoWindowEnergy (n + (N : ℤ)) (u ω) R) ≤
      (3 : ℝ) ^ d * freshShellFourthEnergyConst Chead A := by
  classical
  set G : Ω → ℝ := fun ω => originCubeFourthEnergy K (u ω) with hGdef
  have hG0 : ∀ ω, 0 ≤ G ω := fun ω => originCubeFourthEnergy_nonneg K (u ω)
  set T' : Ω → ℝ := fun ω => max (Real.sqrt (G ω) - Chead) 0 with hT'def
  have hT'0 : ∀ ω, 0 ≤ T' ω := fun ω => le_max_right _ _
  have hT'meas : Measurable T' :=
    ((hglobMeas.sqrt).sub measurable_const).max measurable_const
  -- the caller's `L^8` bound, read on the fourth energy
  have hGT : ∀ ω, G ω ≤ (Chead + T ω) ^ (2 : ℕ) := fun ω =>
    originCubeFourthEnergy_le_sq_of_cubeEuclideanLpNorm_sq_le K (u ω) (hmem ω) (hpath ω)
  have hT'le : ∀ ω, T' ω ≤ T ω := by
    intro ω
    have hnn : (0 : ℝ) ≤ Chead + T ω := by linarith [hT0 ω]
    have hsqrt : Real.sqrt (G ω) ≤ Chead + T ω := by
      have h := Real.sqrt_le_sqrt (hGT ω)
      rwa [Real.sqrt_sq hnn] at h
    exact max_le (by linarith) (hT0 ω)
  have hT'tail : IndependentSums.IsBigOWith μ (IndependentSums.gammaSigma 1) T' A :=
    hT.of_le hT'le
  -- the envelope, rebuilt on the measurable fluctuation
  have hGT' : ∀ ω, G ω ≤ (Chead + T' ω) ^ (2 : ℕ) := by
    intro ω
    have hle : Real.sqrt (G ω) ≤ Chead + T' ω := by
      have := le_max_left (Real.sqrt (G ω) - Chead) 0
      linarith
    have hsq : Real.sqrt (G ω) ^ (2 : ℕ) = G ω := Real.sq_sqrt (hG0 ω)
    calc G ω = Real.sqrt (G ω) ^ (2 : ℕ) := hsq.symm
      _ ≤ (Chead + T' ω) ^ (2 : ℕ) := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  have hmaj : ∀ ω, G ω ≤ 2 * Chead ^ (2 : ℕ) + 2 * T' ω ^ (2 : ℕ) := by
    intro ω
    have h := hGT' ω
    nlinarith [sq_nonneg (Chead - T' ω)]
  have hT'sqInt : Integrable (fun ω => T' ω ^ (2 : ℕ)) μ :=
    integrable_sq_of_isBigOWith_gammaSigma_one hA hT'0 hT'meas.aemeasurable hT'tail
  have hmajInt : Integrable (fun ω => 2 * Chead ^ (2 : ℕ) + 2 * T' ω ^ (2 : ℕ)) μ :=
    (integrable_const _).add (hT'sqInt.const_mul 2)
  have hglobInt : Integrable G μ := by
    refine hmajInt.mono' hglobMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (hG0 ω)]
    exact hmaj ω
  -- the window integrability, by the volume-ratio domination
  have hcellInt : ∀ R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1),
      Integrable (fun ω => mesoWindowFourthEnergy (n + (N : ℤ)) (u ω) R) μ := by
    intro R hR
    have hsub := openCubeAtScale_subset_openCubeSet_of_mem_interiorMesoCubeGrid hR
    have hratio : (0 : ℝ) ≤
        (volume (openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)))).toReal⁻¹ *
          (volume (openCubeSet (originCube d K))).toReal := by positivity
    refine (hglobInt.const_mul
      ((volume (openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)))).toReal⁻¹ *
        (volume (openCubeSet (originCube d K))).toReal)).mono'
      (hcellMeas R hR).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (mesoWindowFourthEnergy_nonneg _ _ _)]
    exact mesoWindowFourthEnergy_le_ratio_mul_originCubeFourthEnergy (u ω) hsub (hfour ω)
  -- the envelope bound itself
  have henv : ∫ ω, G ω ∂μ ≤ freshShellFourthEnergyConst Chead A := by
    have hsplit : ∫ ω, (2 * Chead ^ (2 : ℕ) + 2 * T' ω ^ (2 : ℕ)) ∂μ =
        2 * Chead ^ (2 : ℕ) + 2 * ∫ ω, T' ω ^ (2 : ℕ) ∂μ := by
      rw [integral_add (integrable_const _) (hT'sqInt.const_mul 2), integral_const,
        integral_const_mul]
      simp
    have hsecond : ∫ ω, T' ω ^ (2 : ℕ) ∂μ ≤ 16 * Real.exp 1 ^ (2 : ℕ) * A ^ (2 : ℕ) :=
      integral_sq_le_of_isBigOWith_gammaSigma_one' hA hT'0 hT'meas.aemeasurable hT'tail
    calc ∫ ω, G ω ∂μ
        ≤ ∫ ω, (2 * Chead ^ (2 : ℕ) + 2 * T' ω ^ (2 : ℕ)) ∂μ :=
          integral_mono hglobInt hmajInt hmaj
      _ = 2 * Chead ^ (2 : ℕ) + 2 * ∫ ω, T' ω ^ (2 : ℕ) ∂μ := hsplit
      _ ≤ 2 * Chead ^ (2 : ℕ) + 2 * (16 * Real.exp 1 ^ (2 : ℕ) * A ^ (2 : ℕ)) := by
          linarith
      _ = freshShellFourthEnergyConst Chead A := by
          unfold freshShellFourthEnergyConst
          ring
  exact gridFourthMoment_mesoWindowEnergy_le μ hn hN u hcoord hsq hfour hcellInt
    hglobInt henv

/-! ## The consumer at the actual fresh-shell correctors -/

/-- **`e.lower.bound.oscillations`, first term, at the actual correctors of
`e.def.w`, with every sample-space binder gone.**

```
  3^d ( 2 Chead^2 + 32 e^2 (cgamma^100)^2 ) .
```

Relative to `exists_freshShell_gridFourthMoment_mesoWindowEnergy_le` the three
sample-space hypotheses -- `A Tfluct M.P.toMeasure`, the window fourth-energy
integrability `hcellInt`, and the global fourth-energy integrability `hglobInt`
-- do **not** appear.  The first is bypassed by the measurable dominating
fluctuation described in the module docstring; the other two follow from
measurability of the fourth-energy observables together with the `L^8` bound.
`Tfluct` is still chosen before the sample point, before the scales and before
the correctors, so no measurable selection of correctors is claimed or used.

Complete surviving binder census:

* `hd : 2 <= d`;
* under the leading quantifiers, `M.gamma <= gamma0`, the induction state
  `Algsuperdiff.Frozen.Section3.inductionState M m0 Eind`, and the parameter
  gates `0 < hh`, `m - hh <= m0`, `hh <= 6 cstar M gamma^{-1}`,
  `10^10 gamma^{-1} <= K - m` of `e.recurrence.params`, together with the two
  direction bounds `vecNorm e <= 1` and `vecNorm e' <= 1`;
* then, per leg, the interior-grid gates `hn : n <= K - 1` and
  `hNle : n + N <= K - 1`; the caller's sample family of solutions together
  with its weak-solution property `hsol`; the spatial `L^8` membership family
  `hmem`; and the three spatial integrability families `hcoord`, `hsq`,
  `hfour` on `cu_K`.

Every one of the surviving per-leg binders is a statement about a single sample
point.  No hypothesis about the sample space remains. -/
theorem exists_freshShell_gridFourthMoment_mesoWindowEnergy_le_wired
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ Chead : ℝ, 0 < Chead ∧
      ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
        ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
          ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
            Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
            ∀ (m K : ℤ) (hh : ℕ), 0 < hh → m - (hh : ℤ) ≤ m0 →
              (hh : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
              (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
              ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 →
                Book.Ch02.vecNorm e' ≤ 1 →
                ∃ Tfluct : Cutoff.ShellSeq d → ℝ,
                  (∀ omega, 0 ≤ Tfluct omega) ∧
                  IndependentSums.IsBigOWith M.P.toMeasure
                      (IndependentSums.gammaSigma 1) Tfluct
                      (M.gamma ^ (100 : ℕ)) ∧
                  (∀ (n : ℤ) (N : ℕ), n ≤ K - 1 → n + (N : ℤ) ≤ K - 1 →
                    ∀ wD : Cutoff.ShellSeq d →
                        H10Function (openCubeSet (originCube d K)),
                      (∀ omega, IsZeroTraceDirichletRhsWeakSolution
                          (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                          (openCubeSet (originCube d K)) (wD omega)
                          (fun x => -Corrector.streamForcing
                            ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹ omega
                            (m - (hh : ℤ)) m e x)) →
                      (∀ omega, MemLp (fun x => Book.Ch02.vecNorm
                          ((wD omega).toH1Function.grad x)) 8
                          (normalizedCubeMeasure (originCube d K))) →
                      (∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
                        IntegrableOn
                          (fun x => ((wD omega).toH1Function.grad x k) ^ 2)
                          (openCubeSet (originCube d K)) volume) →
                      (∀ omega, IntegrableOn
                        (fun x => vecNormSq ((wD omega).toH1Function.grad x))
                        (openCubeSet (originCube d K)) volume) →
                      (∀ omega, IntegrableOn
                        (fun x => vecNormSq ((wD omega).toH1Function.grad x) ^ 2)
                        (openCubeSet (originCube d K)) volume) →
                      gridFourthMoment M.P.toMeasure
                          (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
                          (fun R omega => mesoWindowEnergy (n + (N : ℤ))
                            ((wD omega).toH1Function.grad) R) ≤
                        (3 : ℝ) ^ d *
                          freshShellFourthEnergyConst Chead (M.gamma ^ (100 : ℕ))) ∧
                  (∀ (n : ℤ) (N : ℕ), n ≤ K - 1 → n + (N : ℤ) ≤ K - 1 →
                    ∀ wN : Cutoff.ShellSeq d →
                        H1MeanZeroFunction (openCubeSet (originCube d K)),
                      (∀ omega, IsMeanZeroNeumannRhsWeakSolution
                          (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                          (openCubeSet (originCube d K)) (wN omega)
                          (fun x => -Corrector.streamForcing
                            ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹ omega
                            (m - (hh : ℤ)) m e' x)) →
                      (∀ omega, MemLp (fun x => Book.Ch02.vecNorm
                          ((wN omega).toH1Function.grad x)) 8
                          (normalizedCubeMeasure (originCube d K))) →
                      (∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
                        IntegrableOn
                          (fun x => ((wN omega).toH1Function.grad x k) ^ 2)
                          (openCubeSet (originCube d K)) volume) →
                      (∀ omega, IntegrableOn
                        (fun x => vecNormSq ((wN omega).toH1Function.grad x))
                        (openCubeSet (originCube d K)) volume) →
                      (∀ omega, IntegrableOn
                        (fun x => vecNormSq ((wN omega).toH1Function.grad x) ^ 2)
                        (openCubeSet (originCube d K)) volume) →
                      gridFourthMoment M.P.toMeasure
                          (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
                          (fun R omega => mesoWindowEnergy (n + (N : ℤ))
                            ((wN omega).toH1Function.grad) R) ≤
                        (3 : ℝ) ^ d *
                          freshShellFourthEnergyConst Chead (M.gamma ^ (100 : ℕ))) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Chead, hCheadpos, gamma0, hg0pos, hg0quarter, hleg⟩ :=
    exists_freshShell_cubeEuclideanL8_leg_bound d hd
  refine ⟨Chead, hCheadpos, gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he'
  obtain ⟨Tfluct, hTnn, hTtail, hD, hNleg⟩ :=
    hleg M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he'
  have hApos : (0 : ℝ) < M.gamma ^ (100 : ℕ) := pow_pos M.shellPrefix.gamma_pos _
  refine ⟨Tfluct, hTnn, hTtail, ?_, ?_⟩
  · intro n N hn hNle wD hsol hmem hcoord hsq hfour
    refine gridFourthMoment_mesoWindowEnergy_le_of_measurable_fourthEnergy hn hNle
      (fun omega => (wD omega).toH1Function.grad) hCheadpos.le hApos hTnn hTtail hmem
      (fun omega => hD omega (wD omega) (hsol omega)) hcoord hsq hfour
      (Corrector.measurable_volumeAverage_vecNormSq_sq_freshShellDirichletGrad
        (originCube d K) _ (m - (hh : ℤ)) m e
        (measurableSet_openCubeSet _) subset_rfl wD hsol) ?_
    intro R hR
    exact Corrector.measurable_volumeAverage_vecNormSq_sq_freshShellDirichletGrad
      (originCube d K) _ (m - (hh : ℤ)) m e
      (measurableSet_openCubeAtScale _ _)
      (openCubeAtScale_subset_openCubeSet_of_mem_interiorMesoCubeGrid hR) wD hsol
  · intro n N hn hNle wN hsol hmem hcoord hsq hfour
    refine gridFourthMoment_mesoWindowEnergy_le_of_measurable_fourthEnergy hn hNle
      (fun omega => (wN omega).toH1Function.grad) hCheadpos.le hApos hTnn hTtail hmem
      (fun omega => hNleg omega (wN omega) (hsol omega)) hcoord hsq hfour
      (Corrector.measurable_volumeAverage_vecNormSq_sq_freshShellNeumannGrad
        (originCube d K) _ (m - (hh : ℤ)) m e'
        (measurableSet_openCubeSet _) subset_rfl wN hsol) ?_
    intro R hR
    exact Corrector.measurable_volumeAverage_vecNormSq_sq_freshShellNeumannGrad
      (originCube d K) _ (m - (hh : ℤ)) m e'
      (measurableSet_openCubeAtScale _ _)
      (openCubeAtScale_subset_openCubeSet_of_mem_interiorMesoCubeGrid hR) wN hsol

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
