/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreDefinitions
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationHarmonicComparison
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationHarmonicAffineDecay

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedGenerationOneStepAffineExcess

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rounded one-step affine-excess recurrence at the common scale

This file combines the rounded harmonic comparison on the first child with
direct regularity for the rounded constant operator.  It implements the
printed step at HC (5.65)--(5.66).
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set Book.Ch03
open scoped ENNReal

noncomputable section

open FiniteLipschitzCoreInternal

private theorem isWeakSolutionOn_mono_roundStep
    {d : ℕ} {b : CoeffField d} {U V : Set (Vec d)} {F : Vec d → Vec d}
    (hUV : U ⊆ V) (h : IsWeakSolutionOn b V F) :
    IsWeakSolutionOn b U F := by
  intro phi hphi
  have hphiV : IsLocalTest V phi :=
    ⟨hphi.contDiff, hphi.hasCompactSupport, hphi.tsupport_subset.trans hUV⟩
  obtain ⟨hint, hzero⟩ := h phi hphiV
  let f : Vec d → ℝ := fun x ↦
    vecDot (smoothGrad phi x) (matVecMul (b x) (F x))
  have hfzero : ∀ x, x ∉ U → f x = 0 := by
    intro x hx
    have hxnot : x ∉ tsupport phi := fun hmem ↦ hx (hphi.tsupport_subset hmem)
    simp only [f, smoothGrad_eq_zero_of_notMem_tsupport hxnot,
      vecDot_zero_left]
  refine ⟨hint.mono_set hUV, ?_⟩
  have hUint : ∫ x in U, f x ∂volume = ∫ x, f x ∂volume :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hfzero
  have hVzero : ∀ x, x ∉ V → f x = 0 :=
    fun x hx ↦ hfzero x (fun hxU ↦ hx (hUV hxU))
  have hVint : ∫ x in V, f x ∂volume = ∫ x, f x ∂volume :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hVzero
  change ∫ x in U, f x ∂volume = 0
  calc
    ∫ x in U, f x ∂volume = ∫ x, f x ∂volume := hUint
    _ = ∫ x in V, f x ∂volume := hVint.symm
    _ = 0 := hzero

private theorem isWeakSolutionOn_of_constantCoeffForcedEquation_zero
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a₀ : Book.Ch03.ConstantCoeffMatrix d)
    (v : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d)))
    (hv : Book.Ch03.IsConstantCoeffForcedEquation Q a₀ v
      (0 : Vec d → Vec d)) :
    IsWeakSolutionOn (constantCoeffField a₀.matrix)
      (Book.Ch02.cubeDomain Q : Set (Vec d)) v.grad := by
  have hEll : IsEllipticFieldOn a₀.lam a₀.Lam
      (Book.Ch02.cubeDomain Q : Set (Vec d))
      (constantCoeffField a₀.matrix) :=
    Book.Ch03.constantCoeffMatrix_isEllipticFieldOn_constantCoeffField
      a₀ (Book.Ch02.cubeDomain Q).measurableSet
  have hflux : MemVectorL2 (Book.Ch02.cubeDomain Q : Set (Vec d))
      (fun x ↦ matVecMul a₀.matrix (v.grad x)) := by
    simpa only [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll v.grad_memVectorL2
  intro phi hphi
  let psi : H10Function (Book.Ch02.cubeDomain Q : Set (Vec d)) :=
    H10Function.ofContDiff (Book.Ch02.cubeDomain Q).isOpen
      hphi.contDiff hphi.hasCompactSupport hphi.tsupport_subset
  have hpsiGrad : psi.toH1Function.grad = smoothGrad phi := rfl
  have htest : MemVectorL2 (Book.Ch02.cubeDomain Q : Set (Vec d))
      (smoothGrad phi) := by
    simpa only [← hpsiGrad] using psi.toH1Function.grad_memVectorL2
  refine ⟨integrableOn_vecDot_of_memVectorL2 htest hflux, ?_⟩
  have hzero := hv psi
  simpa only [constantCoeffField, hpsiGrad, Pi.zero_apply, vecDot_comm,
    vecDot_zero_left, vecDot_zero_right, integral_zero] using hzero

private theorem normalizedChildDistance_le_comparison
    {d : ℕ} (k : ℤ) (u v : Vec d → ℝ) {bound : ℝ}
    (hcomparison : cubeBesovScaleWeight 1 (originCube d k) *
      cubeLpNorm (originCube d (k - 1)) 2 (fun x ↦ u x - v x) ≤ bound) :
    normalizedCubeL2Distance (originCube d (k - 1)) u v ≤ 3 * bound := by
  have hweight : cubeBesovScaleWeight 1 (originCube d (k - 1)) =
      3 * cubeBesovScaleWeight 1 (originCube d k) := by
    simpa only [Nat.cast_one, pow_one] using
      cubeBesovScaleWeight_one_originCube_sub_nat (d := d) k 1
  unfold normalizedCubeL2Distance
  rw [hweight]
  calc
    _ = 3 * (cubeBesovScaleWeight 1 (originCube d k) *
        cubeLpNorm (originCube d (k - 1)) 2 (fun x ↦ u x - v x)) := by ring
    _ ≤ 3 * bound := mul_le_mul_of_nonneg_left hcomparison (by norm_num)

private theorem exists_roundedOneStepAffineExcessConstants_of_comparison
    (d : ℕ) [NeZero d] (geom : RoundedGenerationAnalyticGeometry d)
    (s Ccomparison : ℝ) (hCcomparison : 0 ≤ Ccomparison) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : CoeffSpace d) (abar : Mat d)
        (hS : (symmPart abar).PosDef)
        (aRounded : Book.Ch03.CoeffFamily d),
        (∀ (k : ℤ)
          (u : H1Function
            (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)))
          (hu : IsWeakSolutionOn
            (aRounded.coeffOn (originCube d k)).toCoeffField
            (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) u.grad),
          let W := geom.harmonicReplacementDatum
            abar hS aRounded k u hu
          Book.Ch03.IsConstantCoeffForcedEquation (originCube d k)
              (geom.referenceConstantCoeffMatrix abar hS)
              W.v (0 : Vec d → Vec d) ∧
            cubeBesovScaleWeight 1 (originCube d k) *
                cubeLpNorm (originCube d (k - 1)) 2
                  (fun x ↦ u.toFun x - W.v.toFun x) ≤
              Ccomparison * geom.spatialWeakError a abar hS s k *
                Book.Ch03.h1EnergyNormOnCube
                  (originCube d k) aRounded u) →
        ∀ (m : ℤ) (u : Book.Ch03.CubeSolution
          (originCube d m) aRounded) (k : ℤ) (hkm : k ≤ m),
          finiteCenteredCubeBestFitErrorAt aRounded m u
              (k - (N : ℤ)) (by omega) ≤
            (1 / 8 : ℝ) *
                finiteCenteredCubeBestFitErrorAt aRounded m u k hkm +
              C * geom.spatialWeakError a abar hS s k *
                finiteCenteredCubeSolutionEnergy aRounded m u k := by
  let R₁ : ℝ := 3 * (((3 ^ d : ℕ) : ℝ))
  have hR₁ : 0 < R₁ := by dsimp [R₁]; positivity
  let theta : ℝ := 1 / (8 * R₁)
  have htheta : 0 < theta := by dsimp [theta]; positivity
  obtain ⟨N₀, hN₀, hdecay⟩ :=
    exists_printOrderRoundedReference_harmonic_normalized_affine_candidate_error_decay
      d geom theta htheta
  let A₀ : ℝ := (3 : ℝ) ^ N₀ * ((((3 ^ d) ^ N₀ : ℕ) : ℝ))
  let N : ℕ := N₀ + 1
  let C : ℝ := (A₀ + theta) * 3 * Ccomparison
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hN : 0 < N := by dsimp [N]; omega
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨N, hN, C, hC, ?_⟩
  intro a abar hS aRounded hcomparison m u k hkm
  let uk : Book.Ch03.CubeSolution (originCube d k) aRounded :=
    finiteCubeSolutionRestriction aRounded hkm u
  have huk : IsWeakSolutionOn
      (aRounded.coeffOn (originCube d k)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) uk.toH1.grad :=
    cubeSolution_isWeakSolutionOn uk
  let W := geom.harmonicReplacementDatum abar hS aRounded k uk.toH1 huk
  obtain ⟨hWeq, hcomparisonL2⟩ := hcomparison k uk.toH1 huk
  let c : ℝ := finiteLipschitzBestIntercept aRounded m u k
  let e : Vec d := finiteLipschitzBestSlope aRounded m u k
  let E : ℝ := finiteLipschitzAffineErrorRow aRounded m u k
  let D : ℝ := finiteLipschitzEnergyRow aRounded m u k
  let H : ℝ := normalizedCubeL2Distance (originCube d (k - 1))
    uk.toH1.toFun W.v.toFun
  have hsub₁ : openCubeSet (originCube d (k - 1)) ⊆
      openCubeSet (originCube d k) :=
    openCubeSet_originCube_subset_of_le (by omega)
  let v₁ : H1Function (openCubeSet (originCube d (k - 1))) :=
    W.v.restrict (isOpen_openCubeSet _) hsub₁
  have hWweak : IsWeakSolutionOn
      (constantCoeffField (geom.referenceMatrix abar hS))
      (openCubeSet (originCube d k)) W.v.grad := by
    simpa only [geom.referenceConstantCoeffMatrix_matrix] using!
      isWeakSolutionOn_of_constantCoeffForcedEquation_zero
        (originCube d k) (geom.referenceConstantCoeffMatrix abar hS) W.v hWeq
  have hv₁weak : IsWeakSolutionOn
      (constantCoeffField (geom.referenceMatrix abar hS))
      (openCubeSet (originCube d (k - 1))) v₁.grad := by
    simpa only [v₁, H1Function.restrict] using
      isWeakSolutionOn_mono_roundStep hsub₁ hWweak
  obtain ⟨c', e', hdec⟩ := hdecay abar hS (k - 1) v₁ hv₁weak c e
  have hchildScale : k - (N : ℤ) = (k - 1) - (N₀ : ℤ) := by
    dsimp [N]
    omega
  have hdec' : normalizedAffineCandidateError
      (originCube d (k - (N : ℤ))) W.v.toFun c' e' ≤
        theta * normalizedAffineCandidateError
          (originCube d (k - 1)) W.v.toFun c e := by
    rw [hchildScale]
    simpa only [v₁, H1Function.restrict] using hdec
  have hdiff : MemLp (fun x ↦ uk.toH1.toFun x - W.v.toFun x) 2
      (normalizedCubeMeasure (originCube d k)) :=
    uk.toH1.memL2_normalizedCubeMeasure.sub W.v.memL2_normalizedCubeMeasure
  have hdiff₁ : MemLp (fun x ↦ uk.toH1.toFun x - W.v.toFun x) 2
      (normalizedCubeMeasure (originCube d (k - 1))) := by
    have h := CubeCalderonZygmund.memLp_centralDescendant_of_memLp
      (Q := originCube d k) 1 hdiff
    rw [centralDescendant_originCube_eq_originCube_sub] at h
    simpa only [Nat.cast_one] using h
  have hdiffChild : MemLp
      (fun x ↦ uk.toH1.toFun x - W.v.toFun x) 2
      (normalizedCubeMeasure (originCube d (k - (N : ℤ)))) := by
    have h := CubeCalderonZygmund.memLp_centralDescendant_of_memLp
      (Q := originCube d (k - 1)) N₀ hdiff₁
    rw [centralDescendant_originCube_eq_originCube_sub, ← hchildScale] at h
    exact h
  have hbestMem : MemLp (fun x ↦ uk.toH1.toFun x - (c + vecDot e x)) 2
      (normalizedCubeMeasure (originCube d k)) := by
    simpa only [uk, c, e, finiteCubeSolutionRestriction_toFun] using
      finiteLipschitzBestResidual_memLp aRounded m u hkm
  have hbestMem₁ : MemLp (fun x ↦ uk.toH1.toFun x - (c + vecDot e x)) 2
      (normalizedCubeMeasure (originCube d (k - 1))) := by
    have h := CubeCalderonZygmund.memLp_centralDescendant_of_memLp
      (Q := originCube d k) 1 hbestMem
    rw [centralDescendant_originCube_eq_originCube_sub] at h
    simpa only [Nat.cast_one] using h
  have hrestrictE : normalizedAffineCandidateError
      (originCube d (k - 1)) uk.toH1.toFun c e ≤ R₁ * E := by
    have h := normalizedAffineCandidateError_originCube_sub_nat_le
      k 1 uk.toH1.toFun c e hbestMem
    simpa only [Nat.cast_one, pow_one, R₁, E,
      finiteLipschitzAffineErrorRow, finiteLipschitzRestriction_toFun,
      min_eq_left hkm, finiteCubeSolutionRestriction_toFun] using! h
  have hWcandidate : normalizedAffineCandidateError
      (originCube d (k - 1)) W.v.toFun c e ≤ H + R₁ * E := by
    have h := normalizedAffineCandidateError_le_distance_add
      (originCube d (k - 1)) W.v.toFun uk.toH1.toFun c e
      (W.v.memL2_normalizedCubeMeasure.sub
        uk.toH1.memL2_normalizedCubeMeasure |> fun hmem ↦ by
          have h := CubeCalderonZygmund.memLp_centralDescendant_of_memLp
            (Q := originCube d k) 1 hmem
          rw [centralDescendant_originCube_eq_originCube_sub] at h
          simpa only [Nat.cast_one] using! h)
      hbestMem₁
    rw [normalizedCubeL2Distance_comm] at h
    exact h.trans (add_le_add_right hrestrictE H)
  have hdecBound : normalizedAffineCandidateError
      (originCube d (k - (N : ℤ))) W.v.toFun c' e' ≤
        theta * (H + R₁ * E) :=
    hdec'.trans (mul_le_mul_of_nonneg_left hWcandidate htheta.le)
  let vChild : H1Function (openCubeSet (originCube d (k - (N : ℤ)))) :=
    W.v.restrict (isOpen_openCubeSet _)
      (openCubeSet_originCube_subset_of_le (by dsimp [N]; omega))
  let ellChild : H1Function
      (openCubeSet (originCube d (k - (N : ℤ)))) :=
    originCubeAffineH1LinearMap d (k - (N : ℤ)) (c', e')
  have hcandMem : MemLp (fun x ↦ W.v.toFun x - (c' + vecDot e' x)) 2
      (normalizedCubeMeasure (originCube d (k - (N : ℤ)))) := by
    have hraw := (vChild - ellChild).memL2_normalizedCubeMeasure
    rw [H1Function.sub_toFun] at hraw
    rw [originCubeAffineH1LinearMap_toFun] at hraw
    exact hraw
  have htransfer := normalizedAffineCandidateError_le_distance_add
    (originCube d (k - (N : ℤ))) uk.toH1.toFun W.v.toFun c' e'
      hdiffChild hcandMem
  have hHchild : normalizedCubeL2Distance (originCube d (k - (N : ℤ)))
      uk.toH1.toFun W.v.toFun ≤ A₀ * H := by
    have h := normalizedCubeL2Distance_originCube_sub_nat_le
      (k - 1) N₀ uk.toH1.toFun W.v.toFun hdiff₁
    rw [← hchildScale] at h
    simpa only [A₀, H] using h
  have hchildCandidate : normalizedAffineCandidateError
      (originCube d (k - (N : ℤ))) uk.toH1.toFun c' e' ≤
        A₀ * H + theta * (H + R₁ * E) :=
    htransfer.trans (add_le_add hHchild hdecBound)
  have hH : H ≤ 3 * Ccomparison *
      geom.spatialWeakError a abar hS s k * D := by
    have henergy : Book.Ch03.h1EnergyNormOnCube
        (originCube d k) aRounded uk.toH1 = D := by
      simpa only [D, uk] using
        (finiteLipschitzEnergyRow_eq_h1EnergyNormOnCube_of_le
          aRounded m u k hkm).symm
    have hbound := normalizedChildDistance_le_comparison k
      uk.toH1.toFun W.v.toFun (by simpa only [W] using hcomparisonL2)
    rw [henergy] at hbound
    simpa only [H, mul_assoc] using hbound
  have hthetaR₁ : theta * R₁ = (1 / 8 : ℝ) := by
    dsimp [theta]
    field_simp [hR₁.ne']
  have hchildBest := finiteLipschitzAffineErrorRow_best_le aRounded m u
    (by dsimp [N]; omega : k - (N : ℤ) ≤ m) c' e'
  calc
    finiteCenteredCubeBestFitErrorAt aRounded m u (k - (N : ℤ)) (by omega) =
        finiteLipschitzAffineErrorRow aRounded m u (k - (N : ℤ)) := rfl
    _ ≤ normalizedAffineCandidateError (originCube d (k - (N : ℤ)))
          u.toH1.toFun c' e' := hchildBest
    _ = normalizedAffineCandidateError (originCube d (k - (N : ℤ)))
          uk.toH1.toFun c' e' := by rw [finiteCubeSolutionRestriction_toFun]
    _ ≤ A₀ * H + theta * (H + R₁ * E) := hchildCandidate
    _ = theta * R₁ * E + (A₀ + theta) * H := by ring
    _ ≤ theta * R₁ * E + (A₀ + theta) *
          (3 * Ccomparison * geom.spatialWeakError
            a abar hS s k * D) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hH (add_nonneg hA₀ htheta.le)) _
    _ = (1 / 8 : ℝ) * finiteCenteredCubeBestFitErrorAt
          aRounded m u k hkm +
        C * geom.spatialWeakError a abar hS s k *
          finiteCenteredCubeSolutionEnergy aRounded m u k := by
      rw [hthetaR₁]
      have henergy : finiteCenteredCubeSolutionEnergy aRounded m u k = D := by
        calc
          finiteCenteredCubeSolutionEnergy aRounded m u k =
              Book.Ch03.h1EnergyNormOnCube (originCube d k) aRounded uk.toH1 := by
            simpa only [uk] using
              finiteCenteredCubeSolutionEnergy_eq_of_le aRounded m u k hkm
          _ = D := by
            simpa only [D, uk] using
              (finiteLipschitzEnergyRow_eq_h1EnergyNormOnCube_of_le
                aRounded m u k hkm).symm
      rw [henergy]
      rw [show finiteCenteredCubeBestFitErrorAt aRounded m u k hkm = E from rfl]
      dsimp [C, E]
      ring

/-- At every order below one half, the selected-generation dual comparison
supplies the complete affine-excess one-step estimate. -/
theorem exists_printOrderRoundedGenerationOneStepAffineExcess
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : CoeffSpace d) (abar : Mat d)
        (hS : (symmPart abar).PosDef)
        (aRounded : Book.Ch03.CoeffFamily d),
        (∀ R : TriadicCube d,
          (aRounded.coeffOn R).toCoeffField =
            (⇑(geom.centeredCoeffSpace abar hS a).1 : CoeffField d)) →
        ∀ (m : ℤ) (u : Book.Ch03.CubeSolution
          (originCube d m) aRounded) (k : ℤ) (hkm : k ≤ m),
          finiteCenteredCubeBestFitErrorAt aRounded m u
              (k - (N : ℤ)) (by omega) ≤
            (1 / 8 : ℝ) *
                finiteCenteredCubeBestFitErrorAt aRounded m u k hkm +
              C * geom.spatialWeakError a abar hS
                  (printCertificateOrder g) k *
                finiteCenteredCubeSolutionEnergy aRounded m u k := by
  obtain ⟨Cdual, hCdual, hregularity⟩ := hdual
  have hs : 0 < printCertificateOrder g := (printOrder_margins hg).1
  have hsHalf : printCertificateOrder g < (1 : ℝ) / 2 :=
    (printOrder_margins hg).2.1
  obtain ⟨Ccomparison, hCcomparison, hcomparison⟩ :=
    exists_roundedGenerationHarmonicComparisonSpecializationConstant
      d geom (printCertificateOrder g) Cdual hs hsHalf hCdual
  obtain ⟨N, hN, C, hC, hstep⟩ :=
    exists_roundedOneStepAffineExcessConstants_of_comparison
      d geom (printCertificateOrder g) Ccomparison hCcomparison
  refine ⟨N, hN, C, hC, ?_⟩
  intro a abar hS aRounded hRounded
  apply hstep a abar hS aRounded
  intro k u hu
  let W := geom.harmonicReplacementDatum abar hS aRounded k u hu
  have hspecial := hcomparison a abar hS aRounded hRounded k u hu
    (hregularity abar hS k)
  refine ⟨?_, hspecial.2.2⟩
  simpa only [W] using!
    (geom.harmonicReplacementDatum abar hS aRounded k u hu).vWeakSolution

end

end HighContrast
end HCPolySupport
