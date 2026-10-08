/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorAffineCubeGrowth
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalEquation

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorLiouvilleForward

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Forward Liouville inclusion for intrinsic affine correctors

This module assembles the local Sobolev representative, global weak equation,
and best-fit-normalized growth chain into the forward inclusion of the frozen
Liouville classification.  Only the local Sobolev clause reads the coefficient
field.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set _root_.Filter
open scoped ENNReal Topology

noncomputable section

/-- Correction-only cube growth implies the exact frozen sublinear limit for
every affine-plus-corrector representative and every additive constant. -/
theorem NormalizedLocalH1Carrier.tendsto_affineAdd_normalizedL2Norm_sublinear_of_cubeGrowth
    {d : ℕ} [NeZero d] (z : NormalizedLocalH1Carrier d)
    (q₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hcube : ∀ q : ℕ, q₀ ≤ q →
      cubeLpNorm (originCube d (q : ℤ)) 2 z.globalValueRepresentative ≤
        C * (3 : ℝ) ^ q)
    (e : Vec d) (c : ℝ) {ϑ : ℝ} (hϑ : 0 < ϑ) :
    Tendsto
      (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + ϑ))) *
        normalizedL2Norm (euclideanBall d r)
          (fun x => vecDot e x + z.globalValueRepresentative x + c))
      atTop (nhds 0) := by
  obtain ⟨Cfull, hCfull, hfull⟩ :=
    z.exists_affineAdd_cubeLpNorm_le_three_pow
      q₀ C hC hcube e c
  let f : Vec d → ℝ :=
    fun x => vecDot e x + z.globalValueRepresentative x + c
  have hmem : ∀ q : ℕ, MemLp f 2
      (normalizedCubeMeasure (originCube d (q : ℤ))) := by
    intro q
    let Q : TriadicCube d := originCube d (q : ℤ)
    have haffine : MemLp (fun x => vecDot e x) 2
        (normalizedCubeMeasure Q) := by
      let u : H1Function (openCubeSet Q) := by
        simpa only [Q, Book.Ch02.cubeDomain_coe] using
          finiteAffineBoundaryH1 (q : ℤ) e
      have hfun : u.toFun = fun x => vecDot e x := by
        simpa only [u] using! finiteAffineBoundaryH1_toFun (m := (q : ℤ)) e
      rw [← hfun]
      exact u.memL2_normalizedCubeMeasure
    have hcorrector : MemLp z.globalValueRepresentative 2
        (normalizedCubeMeasure Q) := by
      simpa only [Q] using
        z.memLp_globalValueRepresentative_normalizedCubeMeasure q
    exact (haffine.add hcorrector).add (memLp_const c)
  apply _root_.HCPolySupport.HighContrast.tendsto_normalizedL2Norm_sublinear_of_cubeGrowth
    f q₀ Cfull hCfull hmem hfull hϑ

/-- A scalar intrinsic good tail therefore gives the frozen sublinear-growth
condition for every affine-plus-corrector representative. -/
theorem exists_scalarIdentityGoodTailAffineCorrectorSublinearGrowthConstant
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ K c : ℝ, 0 < K ∧ c ∈ Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a)
          (e : Vec d) (c₀ : ℝ) (ϑ : ℝ), 0 < ϑ →
          Tendsto
            (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + ϑ))) *
              normalizedL2Norm (euclideanBall d r)
                (fun x => vecDot e x +
                  (finiteAffineCorrectionJointLocalLimit a hCauchy e).globalValueRepresentative
                    x + c₀))
            atTop (nhds 0) := by
  obtain ⟨K, c, hK, hc, hcube⟩ :=
    exists_scalarIdentityGoodTailCorrectorCubeGrowthConstant d s hs hs_lt
  refine ⟨K, c, hK, hc, ?_⟩
  intro a delta n hdelta hgood hCauchy e c₀ ϑ hϑ
  obtain ⟨C, hC, hgrowth⟩ :=
    hcube a delta n hdelta hgood hCauchy e
  exact NormalizedLocalH1Carrier.tendsto_affineAdd_normalizedL2Norm_sublinear_of_cubeGrowth
    (finiteAffineCorrectionJointLocalLimit a hCauchy e)
    n.toNat C hC hgrowth e c₀ hϑ

/-- The intrinsic affine corrector belongs to the exact frozen Liouville
class.  This is the forward inclusion, including arbitrary additive constants. -/
theorem exists_scalarIdentityGoodTailAffineCorrectorMemLiouvilleConstant
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ K c : ℝ, 0 < K ∧ c ∈ Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ {b : CoeffField d}, IsAELocallyUniformlyElliptic b →
        (∀ q : ℕ,
          Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a
            =ᵐ[volumeMeasureOn (localGradientCube d q)] b) →
        ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a)
          (e : Vec d) (c₀ : ℝ) (ϑ : ℝ), 0 < ϑ →
          MemLiouvilleClass b ϑ
            (fun x => vecDot e x +
              (finiteAffineCorrectionJointLocalLimit a hCauchy e).globalValueRepresentative x + c₀)
            (fun x => e +
              (finiteAffineCorrectionJointLocalLimit a hCauchy e).globalGradientRepresentative
                x) := by
  obtain ⟨K, c, hK, hc, hgrowth⟩ :=
    exists_scalarIdentityGoodTailAffineCorrectorSublinearGrowthConstant
      d s hs hs_lt
  refine ⟨K, c, hK, hc, ?_⟩
  intro a delta n hdelta hgood b hb hcoeff hCauchy e c₀ ϑ hϑ
  let z : NormalizedLocalH1Carrier d :=
    finiteAffineCorrectionJointLocalLimit a hCauchy e
  have hlocalEquation : IsFiniteAffineCorrectionJointLocalEquation a
      (finiteAffineCorrectionJointLocalLimit a hCauchy) := by
    constructor
    · intro e'
      exact finiteAffineCorrectionJointLocalLimit_isLimit a hCauchy e'
    · intro e' q
      simpa only [finiteAffineCorrectionJointLocalH1] using
        finiteAffineCorrectionJointLocalH1_isHarmonic a hCauchy e' q
  refine ⟨?_, ?_, ?_⟩
  · exact z.memH1sLoc_affineAdd_globalRepresentatives hb e c₀
  · apply hlocalEquation.isWeakSolutionOn_global (b := b) (e := e)
    intro q
    simpa only [volumeMeasureOn] using hcoeff q
  · exact hgrowth a delta n hdelta hgood hCauchy e c₀ ϑ hϑ

end

end HighContrast
end HCPolySupport
