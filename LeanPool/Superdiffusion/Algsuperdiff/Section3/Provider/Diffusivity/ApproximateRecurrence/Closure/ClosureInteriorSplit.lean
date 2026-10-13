/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenCloserMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenInteriorArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripAssembly

/-!
# ClosureInteriorSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `ClosureSplitInput` from an **interior**-mesh oscillation envelope plus the strip

ABK26, Step 2 of `l.approximate.recurrence.formula`, target
`e.lower.bound.localization.terms`.

## What this module composes

Step 2 at the closure's own corrector families runs off a Besov envelope on the
**full** mesh `descendantsAtDepth (cu_K) j`.  The interior route of
`Closure.GammaTenInterior*` and `Closure.GammaTenStripEnvelope` produces the
envelope only on the **interior** mesh `interiorMesoCubeGrid d K (K - j) n` ---
the carrier forces --- and
`Closure.GammaTenStripAssembly.fluctuationEnergyAverage_le_of_interior_cell_fold_grid_load`
is the bridge from the one to the other, at the price of two exposed binders:
the strip second moment and its absorption gate.

This module runs Step 2 through that bridge, so the envelope may be read on the
interior mesh throughout.  The two carrier-facing points are:

* the load leg's grid fourth-moment root, which
  `Closure.GammaTenLoad.exists_gammaTenLoadConst_root` delivers on the full mesh,
  is moved to the interior mesh by `gridFourthMomentRoot_interiorMesoCubeGrid_le`
  at the cost of the absolute factor `3^d`;
* the numerical gate is produced at the **doubled** absolute constants, so that
  the folded interior average is below `cgamma^{10} / 2` and the strip remainder
  has the other half to live in.

## The window scale, and the two parameters the bridge needs

The bridge's scale bookkeeping is `K = (K - j) + p`, `outer + 1 = (K - j) + g`,
`g <= p`.  At the closure's own data these are forced:

```
  K - j = recurrenceMesoScale 32 cgamma (n + h) h = n - recurrenceGap 32 cgamma ,
  p = j ,   outer = n ,   g = closureStripGap M = recurrenceGap 32 cgamma + 1 ,
```

`outer = n` being exactly the window scale at which
`Closure.GammaTenStripEnvelopeConst.exists_besovEnvelope_interiorMesoCubeGrid_of_depth_gridRoot_const`
produces the interior envelope, one larger than the depth endpoints' own
`n - 1`.  `g <= p` and the two largeness gates hold for every sufficiently large
localization cube.

## What is proved

* `gridFourthMomentRoot_interiorMesoCubeGrid_le` --- the full-mesh to
  interior-mesh transfer of a grid fourth-moment root, at the factor `3^d` of
  `LocalizationGrid.cubeFamilyAverage_interior_le_of_full`.
* `gammaTenBound_of_interiorEnvelope` --- Step 2 at the closure's families, i.e.
  the verbatim antecedent of
  `Closure.SplitFoldIntegrability.closureSplitInput_of_gammaTenBound`, from the
  two named inputs below.
* `closureSplitInput_of_interiorEnvelope` --- `Closure.ClosureFinal.ClosureSplitInput`
  from the same two inputs.

## The two named inputs, and their status

`ClosureInteriorBesovEnvelopeInput` and `ClosureStripRemainder` are
**conditional A obligations** of this module; neither is proved here.

* `ClosureInteriorBesovEnvelopeInput` is the manuscript's own
  `e.lower.bound.oscillations`, read at the Besov tower of the gauged `bfF_z`
  on the interior mesh at window scale `n`.  The depth-indexed interior
  endpoints
  `Closure.GammaTenDepthOscillation.exists_gamma0_freshShell{Dirichlet,Neumann}_meshOscillationDepth_le_gamma_pow_sixteen`
  and the envelope device
  `Closure.GammaTenStripEnvelopeConst.exists_besovEnvelope_interiorMesoCubeGrid_of_depth_gridRoot_const`
  are the route to it, taken downstream in
  `Closure.GammaTenInteriorHosc.closureInteriorBesovEnvelopeInput_proved`; that
  composition is not performed here and the input is carried explicitly.
* `ClosureStripRemainder` is the boundary-strip residual that
  `Closure.GammaTenStripAssembly` isolates and does not prove (its module
  header, "The residual this module isolates"): a second-moment bound on the
  full mesh together with the absorption of `sqrt(d 3^{g-p})` times its square
  root into half of `cgamma^{10}`.

## Binders

The two named inputs and the standing `2 <= d`.  No smallness gate on `cgamma`,
no measurability of the cell integrand and no integrability of the Step-2
integrand is assumed; every threshold is produced.

## Scope

Internal Provider infrastructure.  There is no `sorry`, no `admit`, no custom
axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.localization.terms`, `e.lower.bound.oscillations`,
  `e.recurrence.params`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

/-! ## The full-mesh to interior-mesh transfer of a grid fourth-moment root -/

/-- **A grid fourth-moment root survives the passage to the interior mesh**, at
the absolute factor `3^d`.

The interior mesh is a subfamily of the full mesh whose cardinality is at least
`3^{-d}` of it (`LocalizationGrid.card_mesoCubeGrid_le_three_pow_mul_card_interior`),
so the interior average of the nonnegative cell fourth moments is at most `3^d`
times the full one.  Unconditional beyond the two scale gates and `0 <= C`. -/
theorem gridFourthMomentRoot_interiorMesoCubeGrid_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (d : ℕ) {K nmesh outer : ℤ}
    (hn : nmesh ≤ K - 1) (houter : outer + 1 ≤ K - 1)
    (F : TriadicCube d → Omega → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hroot : gridFourthMomentRoot mu (mesoCubeGrid d K nmesh) F ≤ C) :
    gridFourthMomentRoot mu (interiorMesoCubeGrid d K nmesh outer) F ≤ (3 : ℝ) ^ d * C := by
  have hmom : gridFourthMoment mu (mesoCubeGrid d K nmesh) F ≤ C ^ (4 : ℕ) :=
    gridFourthMoment_le_pow_four_of_root_le mu _ F hroot
  have hnn : ∀ R ∈ mesoCubeGrid d K nmesh, (0 : ℝ) ≤ ∫ w, F R w ^ (4 : ℝ) ∂mu := by
    intro R _
    refine integral_nonneg fun w => ?_
    rw [rpow_four_eq_pow_four]
    positivity
  have hint : gridFourthMoment mu (interiorMesoCubeGrid d K nmesh outer) F ≤
      (3 : ℝ) ^ d * gridFourthMoment mu (mesoCubeGrid d K nmesh) F := by
    unfold gridFourthMoment
    exact cubeFamilyAverage_interior_le_of_full hn houter hnn
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have h30 : (0 : ℝ) < (3 : ℝ) ^ d := by positivity
  refine gridFourthMomentRoot_le_of_le mu _ F (mul_nonneg h30.le hC) ?_
  have hstep : (3 : ℝ) ^ d * gridFourthMoment mu (mesoCubeGrid d K nmesh) F ≤
      (3 : ℝ) ^ d * C ^ (4 : ℕ) := mul_le_mul_of_nonneg_left hmom h30.le
  have h4 : (3 : ℝ) ^ d ≤ ((3 : ℝ) ^ d) ^ (4 : ℕ) := by
    calc (3 : ℝ) ^ d = ((3 : ℝ) ^ d) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ ((3 : ℝ) ^ d) ^ (4 : ℕ) := pow_le_pow_right₀ h3 (by norm_num)
  have hC4 : (0 : ℝ) ≤ C ^ (4 : ℕ) := by positivity
  have hbig : (3 : ℝ) ^ d * C ^ (4 : ℕ) ≤ ((3 : ℝ) ^ d) ^ (4 : ℕ) * C ^ (4 : ℕ) :=
    mul_le_mul_of_nonneg_right h4 hC4
  rw [mul_pow]
  linarith only [hint, hstep, hbig]

/-! ## The two named inputs of the interior route -/

/-- The boundary-strip gap of the closure's own mesh: with the mesh scale
`K - j = n - recurrenceGap 32 cgamma` and window scale `outer = n`, the bridge's
`outer + 1 = (K - j) + g` forces `g = recurrenceGap 32 cgamma + 1`. -/
def closureStripGap {d : ℕ} (M : ABKModel d) : ℕ :=
  recurrenceGap recurrenceGapMultiplier M.gamma + 1

/-- **The residual oscillation input of Step 2, on the interior mesh.**

The residual oscillation obligation of Step 2, stated not on the full mesh
`descendantsAtDepth (cu_K) (closureMeshDepth M n h K)` but on the interior
mesh `interiorMesoCubeGrid d K (K - closureMeshDepth M n h K) n` at window scale
`n`, which is the carrier the interior route of `Closure.GammaTenInterior*` and
`Closure.GammaTenStripEnvelope` produces.  Everything else --- the exponent
`gammaTenBesovExponent = 1/2`, the gauge `shom_{n+h-1}`, the two legs of the
gauged `bfF_z`, the `L^4` membership and the `cgamma^{15}` root --- is unchanged.

It is a **conditional A obligation** of this module and is *not* proved here. -/
def ClosureInteriorBesovEnvelopeInput (d : ℕ) [NeZero d] : Prop :=
  ∃ Cosc : ℝ, 0 < Cosc ∧
    ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}) (e e' : Vec d),
      vecNorm e ≤ 1 → vecNorm e' ≤ 1 → ClosureRegime Cosc M n h Ec →
      ∀ᶠ K : ℕ in Filter.atTop,
        ∃ Bg : TriadicCube d → CutoffSample d → ℝ,
          (∀ R omega, 0 ≤ Bg R omega) ∧
          (∀ R ∈ interiorMesoCubeGrid d (K : ℤ)
              ((K : ℤ) - ((closureMeshDepth M n h K : ℕ) : ℤ)) n,
            MemLp (Bg R) 4 (cutoffSampleLaw M).toMeasure) ∧
          gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
              (interiorMesoCubeGrid d (K : ℤ)
                ((K : ℤ) - ((closureMeshDepth M n h K : ℕ) : ℤ)) n) Bg ≤
            M.gamma ^ (15 : ℕ) ∧
          (∀ R ∈ interiorMesoCubeGrid d (K : ℤ)
              ((K : ℤ) - ((closureMeshDepth M n h K : ℕ) : ℤ)) n,
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
                    Bg R omega))

/-- **The boundary-strip residual of the interior route.**

At the closure's own families, for all sufficiently large localization cubes, a
bound `Cstrip` on the full-mesh average of the *squared* cell expectations of the
Step-2 integrand, together with the absorption of the signed Cauchy--Schwarz
remainder `sqrt(d 3^{g-p}) sqrt(Cstrip)` into half of `cgamma^{10}`.  The
`Filter.atTop` quantifier is exactly the one the consumer uses, so nothing is
asked for at a cube the consumer does not reach.

This is exactly what `Closure.GammaTenStripAssembly` isolates as `hstrip` and
`hgate` and does not prove; see that module's header.  It is a **conditional A
obligation** of this module and is *not* proved here. -/
def ClosureStripRemainder (d : ℕ) [NeZero d] : Prop :=
  ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (e e' : Vec d),
    ∀ᶠ K : ℕ in Filter.atTop,
    ∃ Cstrip : ℝ,
      cubeFamilyAverage
          (mesoCubeGrid d (K : ℤ) ((K : ℤ) - ((closureMeshDepth M n h K : ℕ) : ℤ)))
          (fun R => (∫ omega, meshFluctuationCellIntegrand M n h (K : ℤ) e e'
              (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega
            ∂(cutoffSampleLaw M).toMeasure) ^ 2) ≤ Cstrip ∧
        Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ closureStripGap M /
              (3 : ℝ) ^ closureMeshDepth M n h K)) * Real.sqrt Cstrip ≤
          M.gamma ^ (10 : ℕ) / 2

/-! ## Step 2 from the two inputs -/

/-- **Step 2 at the closure's own corrector families, through the strip bridge**,
i.e. the verbatim antecedent of
`Closure.SplitFoldIntegrability.closureSplitInput_of_gammaTenBound`.

exactly on `ClosureInteriorBesovEnvelopeInput d`, `ClosureStripRemainder d` and
the standing `2 <= d`. -/
theorem gammaTenBound_of_interiorEnvelope (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hosc : ClosureInteriorBesovEnvelopeInput d) (hstrip : ClosureStripRemainder d) :
    ∃ Cfl : ℝ, 0 < Cfl ∧
      ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}) (e e' : Vec d),
        vecNorm e ≤ 1 → vecNorm e' ≤ 1 → ClosureRegime Cfl M n h Ec →
        ∀ᶠ K : ℕ in Filter.atTop,
          fluctuationEnergyAverage M n h (K : ℤ) (closureMeshDepth M n h K) e e'
              (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') ≤
            M.gamma ^ (10 : ℕ) := by
  classical
  obtain ⟨Cosc, -, hoscmain⟩ := hosc
  obtain ⟨Cell, gell, hCell0, hgell0, -, hellbd⟩ :=
    exists_regime_gaugedEllipticitySum_pow_four_le d
  obtain ⟨Cmem, gmem, hCmem0, hgmem0, -, hmembd⟩ :=
    exists_regime_memLp_four_gaugedEllipticitySum_ancestorAtScale d
  obtain ⟨Cload, hCload0, hloadbd⟩ := exists_gammaTenLoadConst_root d hd
  have hCload3 : (0 : ℝ) ≤ (3 : ℝ) ^ d * Cload := mul_nonneg (by positivity) hCload0.le
  obtain ⟨gthr, hgthr0, -, hthrbd⟩ := exists_gamma_threshold_gridFold
    (2 * (gammaTenCrossConst d * ((3 : ℝ) ^ d * Cload))) (2 * gammaTenQuadConst d)
    (mul_nonneg (by norm_num) (mul_nonneg (gammaTenCrossConst_nonneg d) hCload3))
    (mul_nonneg (by norm_num) (gammaTenQuadConst_nonneg d))
  set gcov : ℝ := ((((recurrenceGapMultiplier : ℕ) : ℝ) + 1) ^ 2)⁻¹ with hgcov
  have hgcov0 : (0 : ℝ) < gcov := by
    rw [hgcov]
    have hbase : (0 : ℝ) < (((recurrenceGapMultiplier : ℕ) : ℝ) + 1) ^ 2 := by positivity
    exact inv_pos.2 hbase
  set Cfl : ℝ := max (max Cell Cmem) (max Cosc (max (3 / 2 * gell⁻¹)
    (max (3 / 2 * gmem⁻¹) (max (3 / 2 * gthr⁻¹) (3 / 2 * gcov⁻¹))))) with hCfl
  have hCflpos : 0 < Cfl := lt_of_lt_of_le hCell0
    (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨Cfl, hCflpos, ?_⟩
  intro M n h Ec e e' he he' hreg
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  obtain ⟨hstate, hhpos, -, -, hhcap, -⟩ := id hreg
  -- the four `cgamma` thresholds
  have hgell : M.gamma ≤ gell := gamma_le_of_closureRegime hgell0
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hreg
  have hgmem : M.gamma ≤ gmem := gamma_le_of_closureRegime hgmem0
    (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) hreg
  have hgthr : M.gamma ≤ gthr := gamma_le_of_closureRegime hgthr0
    (le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) hreg
  have hgcovle : M.gamma ≤ gcov := gamma_le_of_closureRegime hgcov0
    (le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) hreg
  have hcover : (((recurrenceGapMultiplier : ℕ) : ℝ) + 1) ^ 2 ≤ M.gamma⁻¹ := by
    calc (((recurrenceGapMultiplier : ℕ) : ℝ) + 1) ^ 2 = gcov⁻¹ := by
          rw [hgcov, inv_inv]
      _ ≤ M.gamma⁻¹ := inv_anti₀ hgamma0 hgcovle
  -- the ellipticity regime premises
  have hregCell : ClosureRegime Cell M n h Ec :=
    closureRegime_mono (le_trans (le_max_left _ _) (le_max_left _ _)) hreg
  have hregCmem : ClosureRegime Cmem M n h Ec :=
    closureRegime_mono (le_trans (le_max_right _ _) (le_max_left _ _)) hreg
  have hregCosc : ClosureRegime Cosc M n h Ec :=
    closureRegime_mono (le_trans (le_max_left _ _) (le_max_right _ _)) hreg
  obtain ⟨-, -, hCellE, hgammaE, -, -⟩ := hregCell
  obtain ⟨-, -, hCmemE, -, -, -⟩ := hregCmem
  -- the gauge ratio
  have hnhh : n + (h : ℤ) - (h : ℤ) = n := by ring
  have hgauge : gaugeRatio (Annealed.sigmaBar M n)
      (Annealed.sigmaBar M (n + (h : ℤ) - 1)) ≤ 4 * (3 : ℝ) ^ (9 : ℕ) := by
    have hb := gaugeRatio_sigmaBar_le_readingConst M hstate (m := n + (h : ℤ)) (h := h)
      hhpos (le_refl _) hhcap
    rwa [hnhh] at hb
  have hKge : ∀ᶠ K : ℕ in Filter.atTop, n + (h : ℤ) + 2 ≤ (K : ℤ) := by
    filter_upwards [Filter.eventually_ge_atTop (n + (h : ℤ) + 2).toNat] with K hK
    have hself := Int.self_le_toNat (n + (h : ℤ) + 2)
    have hKcast : ((n + (h : ℤ) + 2).toNat : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK
    omega
  filter_upwards [hoscmain M n h Ec e e' he he' hregCosc,
    eventually_recurrenceParams_largeCube M n h,
    eventually_closureMeshDepth_scale M n h, hKge, hstrip M n h e e']
    with K hBgK hK10 hscale hKn hstripK
  obtain ⟨Bg, hBg0, hBgmem, hBgroot, hBgdom⟩ := hBgK
  set j : ℕ := closureMeshDepth M n h K with hj
  set mu : Measure (CutoffSample d) := (cutoffSampleLaw M).toMeasure with hmu
  set F : TriadicCube d → CutoffSample d → ℝ := fun R omega =>
    gaugedEllipticitySum (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ)
      (ancestorAtScale R (n + (h : ℤ))) M.gamma
      (coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega) with hF
  set G : TriadicCube d → CutoffSample d → ℝ := fun R omega =>
    Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M n)
      (meshCellLoad M n h (K : ℤ) e e' (closureDirichletAlong M n h K e)
        (closureNeumannAlong M n h K e') R omega)) with hG
  have hsig0 : (0 : ℝ) < (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ) :=
    (Annealed.sigmaBar M (n + (h : ℤ) - 1)).2
  have hF0 : ∀ R omega, 0 ≤ F R omega := fun R omega =>
    gaugedEllipticitySum_nonneg _ _ hsig0.le hgamma0
  have hG0 : ∀ R omega, 0 ≤ G R omega := fun R omega => Real.sqrt_nonneg _
  -- the scale bookkeeping of the two meshes
  have hscale' : (K : ℤ) - (j : ℤ) =
      recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ) := hscale
  have hgapEq : (K : ℤ) - (j : ℤ) =
      n - ((recurrenceGap recurrenceGapMultiplier M.gamma : ℕ) : ℤ) := by
    rw [hscale']
    unfold recurrenceMesoScale
    ring
  have hgp : closureStripGap M ≤ j := by
    unfold closureStripGap
    omega
  have houter : n + 1 = ((K : ℤ) - (j : ℤ)) + ((closureStripGap M : ℕ) : ℤ) := by
    unfold closureStripGap
    omega
  have hKp : (K : ℤ) = ((K : ℤ) - (j : ℤ)) + ((j : ℕ) : ℤ) := by omega
  have hmeshEq : mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)) =
      descendantsAtDepth (originCube d (K : ℤ)) j := by
    rw [mesoCubeGrid_eq_descendantsAtDepth (by omega : (K : ℤ) - (j : ℤ) ≤ (K : ℤ))]
    congr 1
    omega
  have hsub : ∀ R ∈ interiorMesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)) n,
      R ∈ descendantsAtDepth (originCube d (K : ℤ)) j := by
    intro R hR
    rw [← hmeshEq]
    exact interiorMesoCubeGrid_subset hR
  -- the scale gate on the mesh cells
  have hscaleR : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      R.scale ≤ n + (h : ℤ) := by
    intro R hR
    have h1 : R.scale =
        recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ) := by
      have hsc := scale_eq_sub_of_mem_descendantsAtDepth hR
      rw [hsc]; exact hscale
    have h2 := recurrenceMesoScale_le recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ)
    omega
  -- the three `L^4` legs and the two moments, on the full mesh
  have hF4 : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j, MemLp (F R) 4 mu :=
    fun R hR => hmembd M (n + (h : ℤ)) Ec hgmem hstate hCmemE hgammaE R (hscaleR R hR)
  have hG4 : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j, MemLp (G R) 4 mu :=
    fun R hR => memLp_four_gammaTenLoadLeg hd M n h K e e' he he' hhpos (by omega) hR
  have hell : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      ∫ w, F R w ^ (4 : ℝ) ∂mu ≤ (M.gamma ^ (8 : ℕ))⁻¹ := by
    intro R hR
    simp only [rpow_four_eq_pow_four]
    exact hellbd M (n + (h : ℤ)) Ec hgell hstate hCellE hgammaE R (hscaleR R hR)
  have hnm0 : n ≤ n + (h : ℤ) - 1 := by
    have h1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hhpos
    omega
  have hload : gridFourthMomentRoot mu (descendantsAtDepth (originCube d (K : ℤ)) j) G ≤
      Cload :=
    hloadbd M (n + (h : ℤ) - 1) Ec hstate n h K j e e' hhpos hnm0 hhcap (by omega) he he'
  -- the load leg on the interior mesh
  have hloadMesh : gridFourthMomentRoot mu (mesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ))) G ≤
      Cload := by
    rw [hmeshEq]
    exact hload
  have hloadI : gridFourthMomentRoot mu
      (interiorMesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)) n) G ≤ (3 : ℝ) ^ d * Cload :=
    gridFourthMomentRoot_interiorMesoCubeGrid_le mu d (by omega) (by omega) G hCload0.le
      hloadMesh
  -- the numerical gate, at half of the target
  have hthr : ∀ Bosc : ℝ, 0 ≤ Bosc → Bosc ≤ M.gamma ^ (15 : ℕ) →
      gammaTenCrossConst d * ((3 : ℝ) ^ d * Cload) * ((M.gamma ^ (2 : ℕ))⁻¹ * Bosc) +
          gammaTenQuadConst d * ((M.gamma ^ (2 : ℕ))⁻¹ * Bosc ^ (2 : ℕ)) ≤
        M.gamma ^ (10 : ℕ) / 2 := by
    intro Bosc hB0 hB
    have hbase := hthrbd M.gamma hgamma0 hgthr Bosc hB0 hB
    linarith only [hbase]
  -- the cell bound, on the interior mesh
  have hcell : ∀ R ∈ interiorMesoCubeGrid d (K : ℤ) ((K : ℤ) - (j : ℤ)) n,
      ∀ᵐ omega ∂mu,
        meshFluctuationCellIntegrand M n h (K : ℤ) e e'
            (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega ≤
          gammaTenCrossConst d * (F R omega * G R omega * Bg R omega) +
            gammaTenQuadConst d * (F R omega * Bg R omega * Bg R omega) := by
    intro R hR
    filter_upwards [hBgdom R hR] with omega hdom
    exact meshFluctuationCellIntegrand_le_closureFold M n h K hK10 hscale hcover hhcap
      hgauge e e' omega (hsub R hR) (hBg0 R omega) hdom.1 hdom.2
  -- the strip residual
  obtain ⟨Cstrip, hstripbd, hstripgate⟩ := hstripK
  have hgate : M.gamma ^ (10 : ℕ) / 2 +
      Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ closureStripGap M / (3 : ℝ) ^ j)) *
        Real.sqrt Cstrip ≤ M.gamma ^ (10 : ℕ) := by
    linarith only [hstripgate]
  exact fluctuationEnergyAverage_le_of_interior_cell_fold_grid_load M n h (K : ℤ) j e e'
    (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
    hKp houter hgp F G Bg hF0 hG0 hBg0
    (fun R hR => hF4 R (hsub R hR)) (fun R hR => hG4 R (hsub R hR)) hBgmem
    (gammaTenCrossConst_nonneg d) (gammaTenQuadConst_nonneg d) (by positivity)
    (fun R hR => hell R (hsub R hR)) hloadI hBgroot hthr hcell hstripbd hgate

/-- **`Closure.ClosureFinal.ClosureSplitInput` from the interior-mesh envelope and
the strip residual.** -/
theorem closureSplitInput_of_interiorEnvelope (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hosc : ClosureInteriorBesovEnvelopeInput d) (hstrip : ClosureStripRemainder d) :
    ClosureSplitInput d := by
  obtain ⟨Cfl, -, hfluct⟩ := gammaTenBound_of_interiorEnvelope d hd hosc hstrip
  exact closureSplitInput_of_gammaTenBound d hd hfluct

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
