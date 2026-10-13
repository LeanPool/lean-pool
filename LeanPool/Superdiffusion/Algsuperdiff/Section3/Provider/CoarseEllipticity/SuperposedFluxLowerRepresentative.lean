/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4Bounds

/-!
# SuperposedFluxLowerRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3.Cutoff
  (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_le_cutoffCoercivity)

/-!
# Pointwise representative for the sharp lower coarse-ellipticity lane

The sharp superposed-flux estimate is initially simultaneous in the cutoff
index only almost everywhere.  This file intersects those events over the
countable depth family, encloses the exceptional set in one measurable null
set, and caps the random remainder by the unconditional cutoff-coercivity
bound.  The resulting representative is measurable, has the same weak-Orlicz
tail, is uniformly bounded at every sample point, and gives the depth estimate
pointwise for every cutoff index.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open Filter MeasureTheory Topology
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Affine

noncomputable section



variable {d : ℕ}

/-- The deterministic sharp prefactor at the positive-depth grid indexed by
`k`. -/
def superposedFluxSharpDepthConst (M : ABKModel d) (m : ℤ) (E : ℝ)
    (k : ℕ) : ℝ :=
  superposedFluxSharpConst M (m - 1 - (k : ℤ)) (m - 1)
    (superposedFluxRateEps M) (superposedFluxRateBeta M)
    (superposedFluxPrimaryDepth M E) (superposedFluxRareDepth M E)

/-- The retained rare slot for the rate-compatible integer parameters. -/
def superposedFluxSharpDepthRare (M : ABKModel d) (E : ℝ) : ℝ :=
  superposedFluxSharpRare (superposedFluxRateBeta M)
    (superposedFluxPrimaryDepth M E) (superposedFluxRareDepth M E)

/-- The raw finite-grid random remainder at positive-depth grid index `k`. -/
def superposedFluxSharpDepthRandom (M : ABKModel d) (m : ℤ) (E : ℝ)
    (k : ℕ) (omega : CutoffSample d) : ℝ :=
  bfaLocalGridSup M m k E bfaProfileB
    (superposedFluxLocalExponent M bfaProfileB
      (superposedFluxRateEps M) (superposedFluxRateBeta M))
    (superposedFluxSharpDepthConst M m E k)
    (superposedFluxSharpDepthRare M E) omega

/-- The exact finite-grid weak-Orlicz amplitude of the raw remainder. -/
def superposedFluxSharpDepthAmp (M : ABKModel d) (m : ℤ) (E sigma : ℝ)
    (k : ℕ) : ℝ :=
  gridBlockAmp d
    (bfaTau (bfaProfileSigma sigma)
      (superposedFluxLocalExponent M bfaProfileB
        (superposedFluxRateEps M) (superposedFluxRateBeta M)) bfaProfileB)
    (bfaLaneScale (bfaProfileSigma sigma) bfaProfileB
      (superposedFluxLocalExponent M bfaProfileB
        (superposedFluxRateEps M) (superposedFluxRateBeta M))
      (superposedFluxSharpDepthConst M m E k)
      (superposedFluxSharpDepthRare M E)) k

/-- An everywhere-valid deterministic cap for the normalized inverse coarse
matrix at any depth and cutoff index. -/
def superposedFluxCutoffCap (M : ABKModel d) (m : ℤ) : ℝ :=
  (Annealed.sigmaBar M (m - 1) : ℝ) * (4 * (d : ℝ) * M.nu⁻¹)

theorem superposedFluxCutoffCap_pos (hd : 2 ≤ d) (M : ABKModel d) (m : ℤ) :
    0 < superposedFluxCutoffCap M m := by
  unfold superposedFluxCutoffCap
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  exact mul_pos (Annealed.sigmaBar M (m - 1)).2
    (mul_pos (mul_pos (by norm_num) hdR) (inv_pos.mpr M.nu_pos))

private theorem measurable_superposedFluxSharpDepthRandom
    (M : ABKModel d) (m : ℤ) (E : ℝ) (k : ℕ) :
    Measurable (superposedFluxSharpDepthRandom M m E k) := by
  unfold superposedFluxSharpDepthRandom bfaLocalGridSup
  exact measurable_blockGridSup d m k fun R => measurable_bfaLocalLane M R _ _ _ _ _

private theorem superposedFluxSharpDepthRandom_nonneg
    (M : ABKModel d) (m : ℤ) (E : ℝ) (k : ℕ)
    (omega : CutoffSample d) :
    0 ≤ superposedFluxSharpDepthRandom M m E k omega := by
  unfold superposedFluxSharpDepthRandom
  exact bfaLocalGridSup_nonneg M m k _ _ _ _ _ omega

/-- One measurable representative simultaneously serves every depth and every
cutoff index.  The last clause is the everywhere cap that later discharges all
pointwise summability requirements; it is not exported by the frozen theorem.
-/
theorem exists_superposedFluxLowerPointwiseRepresentative
    [NeZero d] (hd : 2 ≤ d) (M : ABKModel d) (m : ℤ)
    (E : {E : ℝ // 1 ≤ E})
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    ∃ U : ℕ → CutoffSample d → ℝ,
      (∀ n omega, 0 ≤ U n omega) ∧
      (∀ n, Measurable (U n)) ∧
      (∀ n, IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma ((1 - sigma) / 2)) (U n)
        (superposedFluxSharpDepthAmp M m E sigma n.pred)) ∧
      (∀ omega, ∀ L : ℤ, m - 1 ≤ L → ∀ n : ℕ,
        (Annealed.sigmaBar M (m - 1) : ℝ) *
            Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              (originCube d m) (m - (n : ℤ))
              (coefficientCutoff M.nu L omega) ≤
          finiteQGeometricProfile (2 * superposedFluxSharpDetConst d)
            M.gamma n + U n omega) ∧
      (∀ n omega, U n omega ≤ superposedFluxCutoffCap M m) := by
  classical
  obtain ⟨heps, hbeta, hbeta9, hbetab, hgammaWin, hk₀three, _hk₀,
      hcap, _hlocalEq, hlocalb, htau⟩ :=
    superposedFluxRateCompatible_allParameterGates_of_profileAuxiliaryMaxGate
      hd M E.property hsigma hsigmaHalf hmax hEgamma
  obtain ⟨hE4, hunit, hgamma20, hinvSq, hgammaZ⟩ :=
    badEventGates_of_profileAuxiliaryMaxGate M E.property hsigma hsigmaHalf hmax hEgamma
  have hexp : Real.exp (profileAuxiliaryConst d / sigma) ≤ (E : ℝ) :=
    (le_max_left _ _).trans hmax
  have hEexp : Real.exp (badClustersConst d / bfaProfileSigma sigma) ≤ (E : ℝ) :=
    exp_badClustersConst_div_bfaProfileSigma_le_of_profileAuxiliaryGate hsigma hexp
  have hEb : badClustersConst d / bfaProfileB ≤ (E : ℝ) :=
    badClustersConst_div_bfaProfileB_le_of_profileAuxiliaryGate
      hsigma hsigmaHalf hexp
  let P : CutoffSample d → Prop := fun omega =>
    ∀ k : ℕ,
      ∀ R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)),
        ∀ (L : ℤ), m - 1 ≤ L →
          cutoffSigmaStarInvBlockFamily M L
              (Annealed.sigmaBar M (m - 1) : ℝ) R omega ≤
            2 * superposedFluxSharpDepthConst M m E k +
              superposedFluxSharpDepthRandom M m E k omega
  have hae : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, P omega := by
    rw [ae_all_iff]
    intro k
    have hsharp := slstar_descendantGrid_allL_ae_sharp_of_gates hd M k hS
      (bfaProfileSigma_pos hsigma) (bfaProfileSigma_le_one_half hsigmaHalf)
      bfaProfileB_pos bfaProfileB_le_one_eighth hEexp hE4 hunit hgamma20
      hinvSq hEb hgammaZ hk₀three heps hbeta hbeta9 hbetab hgammaWin hcap
    simpa [P, superposedFluxSharpDepthConst, superposedFluxSharpDepthRandom] using! hsharp
  obtain ⟨N, hsubN, hNmeas, hN0⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hae)
  let H : ℝ := superposedFluxCutoffCap M m
  let capped : ℕ → CutoffSample d → ℝ := fun n omega =>
    min H (superposedFluxSharpDepthRandom M m E n.pred omega)
  let U : ℕ → CutoffSample d → ℝ := fun n =>
    N.piecewise (fun _ => H) (capped n)
  have hHpos : 0 < H := superposedFluxCutoffCap_pos hd M m
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · intro n omega
    by_cases homega : omega ∈ N
    · change 0 ≤ N.piecewise (fun _ => H) (capped n) omega
      rw [N.piecewise_eq_of_mem _ _ homega]
      exact hHpos.le
    · have hraw := superposedFluxSharpDepthRandom_nonneg M m E n.pred omega
      change 0 ≤ N.piecewise (fun _ => H) (capped n) omega
      rw [N.piecewise_eq_of_notMem _ _ homega]
      change 0 ≤ min H (superposedFluxSharpDepthRandom M m E n.pred omega)
      exact le_min hHpos.le hraw
  · intro n
    have hraw : Measurable (superposedFluxSharpDepthRandom M m E n.pred) :=
      measurable_superposedFluxSharpDepthRandom M m E n.pred
    exact Measurable.piecewise hNmeas measurable_const (measurable_const.min hraw)
  · intro n
    have hsharp := slstar_descendantGrid_allL_ae_and_isBigOWith_sharp_of_gates
      hd M n.pred hS
      (bfaProfileSigma_pos hsigma) (bfaProfileSigma_le_one_half hsigmaHalf)
      bfaProfileB_pos bfaProfileB_le_one_eighth hEexp hE4 hunit hgamma20
      hinvSq hEb hgammaZ hk₀three heps hbeta hbeta9 hbetab hgammaWin hcap hlocalb
    have hrawO : IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma ((1 - sigma) / 2))
        (superposedFluxSharpDepthRandom M m E n.pred)
        (superposedFluxSharpDepthAmp M m E sigma n.pred) := by
      refine HCPolySupport.Book.Ch04.IsBigOWith.gammaSigma_mono_exponent htau ?_
      simpa [superposedFluxSharpDepthRandom, superposedFluxSharpDepthAmp,
        superposedFluxSharpDepthConst, superposedFluxSharpDepthRare] using! hsharp.2
    have hcappedO : IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma ((1 - sigma) / 2)) (capped n)
        (superposedFluxSharpDepthAmp M m E sigma n.pred) :=
      isBigOWith_gammaSigma_of_le (fun omega => min_le_right _ _) hrawO
    refine Provider.Tail.isBigOWith_of_ae_eq ?_ hcappedO
    have hnmem : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, omega ∉ N :=
      measure_eq_zero_iff_ae_notMem.mp hN0
    filter_upwards [hnmem] with omega homega
    change capped n omega = N.piecewise (fun _ => H) (capped n) omega
    rw [N.piecewise_eq_of_notMem _ _ homega]
  · intro omega L hL n
    have hcutoff :
        (Annealed.sigmaBar M (m - 1) : ℝ) *
            Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              (originCube d m) (m - (n : ℤ))
              (coefficientCutoff M.nu L omega) ≤ H := by
      have hbase :=
        maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_le_cutoffCoercivity
          M L omega (originCube d m) n
      exact mul_le_mul_of_nonneg_left hbase
        (Annealed.sigmaBar M (m - 1)).2.le
    have hdet :
        2 * superposedFluxSharpDepthConst M m E n.pred ≤
          finiteQGeometricProfile (2 * superposedFluxSharpDetConst d) M.gamma n := by
      have hprof := superposedFluxSharpConst_le_profile hd M m n.pred E.property
        hgamma20 hbeta9 (by
          simpa [superposedFluxRate] using _hk₀)
      have hpred : n.pred ≤ n := Nat.pred_le n
      have hexpMono : (3 : ℝ) ^ (M.gamma * (n.pred : ℝ)) ≤
          (3 : ℝ) ^ (M.gamma * (n : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hpred)
            M.shellPrefix.gamma_pos.le)
      unfold superposedFluxSharpDepthConst finiteQGeometricProfile
      calc
        2 * superposedFluxSharpConst M (m - 1 - (n.pred : ℤ)) (m - 1)
              (superposedFluxRateEps M) (superposedFluxRateBeta M)
              (superposedFluxPrimaryDepth M E) (superposedFluxRareDepth M E) ≤
            2 * (superposedFluxSharpDetConst d *
              (3 : ℝ) ^ (M.gamma * (n.pred : ℝ))) :=
          mul_le_mul_of_nonneg_left hprof (by norm_num)
        _ ≤ 2 * (superposedFluxSharpDetConst d *
              (3 : ℝ) ^ (M.gamma * (n : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexpMono
              (superposedFluxSharpDetConst_pos hd).le) (by norm_num)
        _ = _ := by ring
    by_cases hmem : omega ∈ N
    · have hU : U n omega = H := by
        change N.piecewise (fun _ => H) (capped n) omega = H
        rw [N.piecewise_eq_of_mem _ _ hmem]
      rw [hU]
      exact hcutoff.trans (le_add_of_nonneg_left
        (finiteQGeometricProfile_nonneg
          (mul_nonneg (by norm_num) (superposedFluxSharpDetConst_pos hd).le)
          M.gamma n))
    · have hgood : P omega := by
        by_contra hbad
        exact hmem (hsubN hbad)
      have hgrid (k : ℕ) :
          (Annealed.sigmaBar M (m - 1) : ℝ) *
              Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                (originCube d m) (m - 1 - (k : ℤ))
                (coefficientCutoff M.nu L omega) ≤
            2 * superposedFluxSharpDepthConst M m E k +
              superposedFluxSharpDepthRandom M m E k omega := by
        rw [maxDescendantSigmaStarInvCoeffField_eq_blockGridSup m k,
          ← blockGridSup_const_mul d m k (Annealed.sigmaBar M (m - 1)).2.le]
        apply blockGridSup_le
        intro R hR
        rw [abs_of_nonneg (mul_nonneg (Annealed.sigmaBar M (m - 1)).2.le
          (coarseSigmaStarInvNormCoeffField_nonneg _ _))]
        exact hgood k R hR L hL
      have hraw :
          (Annealed.sigmaBar M (m - 1) : ℝ) *
              Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                (originCube d m) (m - (n : ℤ))
                (coefficientCutoff M.nu L omega) ≤
            2 * superposedFluxSharpDepthConst M m E n.pred +
              superposedFluxSharpDepthRandom M m E n.pred omega := by
        cases n with
        | zero =>
            have htop := maxDescendantSigmaStarInvCoeffField_top_le m
              (coefficientCutoff M.nu L omega)
            simpa only [Nat.pred_zero, Nat.cast_zero, sub_zero] using
              (mul_le_mul_of_nonneg_left htop
                (Annealed.sigmaBar M (m - 1)).2.le).trans (hgrid 0)
        | succ k =>
            rw [show m - ((Nat.succ k : ℕ) : ℤ) = m - 1 - (k : ℤ) by
              push_cast
              ring]
            simpa only [Nat.pred_succ] using hgrid k
      by_cases hrawCap : superposedFluxSharpDepthRandom M m E n.pred omega ≤ H
      · have hU : U n omega =
            superposedFluxSharpDepthRandom M m E n.pred omega := by
          change N.piecewise (fun _ => H) (capped n) omega = _
          rw [N.piecewise_eq_of_notMem _ _ hmem]
          change min H (superposedFluxSharpDepthRandom M m E n.pred omega) = _
          exact min_eq_right hrawCap
        rw [hU]
        exact hraw.trans (add_le_add hdet le_rfl)
      · have hU : U n omega = H := by
          have hHraw : H ≤ superposedFluxSharpDepthRandom M m E n.pred omega :=
            le_of_not_ge hrawCap
          change N.piecewise (fun _ => H) (capped n) omega = H
          rw [N.piecewise_eq_of_notMem _ _ hmem]
          change min H (superposedFluxSharpDepthRandom M m E n.pred omega) = H
          exact min_eq_left hHraw
        rw [hU]
        exact hcutoff.trans (le_add_of_nonneg_left
          (finiteQGeometricProfile_nonneg
            (mul_nonneg (by norm_num) (superposedFluxSharpDetConst_pos hd).le)
            M.gamma n))
  · intro n omega
    by_cases homega : omega ∈ N
    · change N.piecewise (fun _ => H) (capped n) omega ≤
          superposedFluxCutoffCap M m
      rw [N.piecewise_eq_of_mem _ _ homega]
    · change N.piecewise (fun _ => H) (capped n) omega ≤
          superposedFluxCutoffCap M m
      rw [N.piecewise_eq_of_notMem _ _ homega]
      exact min_le_left _ _

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
