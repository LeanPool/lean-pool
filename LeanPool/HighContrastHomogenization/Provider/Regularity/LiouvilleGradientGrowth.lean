/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleOriginCubeBallBridge

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleGradientGrowth

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Gradient growth of finite realizations of a Liouville solution

This module completes the function-to-gradient Caccioppoli step in the reverse
Liouville argument.  It chooses the exact finite-cube realizations of a frozen
Liouville pair and proves that their two-scale-inner weighted energies are
`o(R^theta)`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

/-- The Liouville-growth output: finite realizations preserving `(v,Dv)` pointwise
have inner weighted energy `o(R^theta)` along scale-matched triadic radii. -/
theorem exists_scalarIdentityLiouvilleFiniteGradientGrowth
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2)
    (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ)
    (hdelta : delta ≤ 1) (hgood : ScalarIdentityGoodTail a s delta n)
    {b : CoeffField d} {theta : ℝ} (hb : IsAELocallyUniformlyElliptic b)
    (hcoeff : ∀ q : ℕ,
      Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a
        =ᵐ[volumeMeasureOn (openCubeSet (originCube d (q : ℤ)))] b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (hv : MemLiouvilleClass b theta v Dv) :
    ∃ C : ℝ, 0 < C ∧
      ∃ u : ∀ q : ℕ, Book.Ch03.CubeSolution (originCube d (q : ℤ)) a,
        (∀ q, (u q).toH1.toFun = v ∧ (u q).toH1.grad = Dv) ∧
          Tendsto
            (fun q : ℕ => ENNReal.ofReal
              ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-theta) *
                finiteCenteredCubeSolutionEnergy a (q : ℤ) (u q)
                  ((q : ℤ) - 2)))
            atTop (nhds 0) := by
  obtain ⟨C, hC, hcacc⟩ :=
    exists_scalarIdentityFiniteCaccioppoliAffineConstant d s hs hs_lt
  have hexists : ∀ q : ℕ,
      ∃ uq : Book.Ch03.CubeSolution (originCube d (q : ℤ)) a,
        uq.toH1.toFun = v ∧ uq.toH1.grad = Dv := by
    intro q
    have hactual : (a.coeffOn (originCube d (q : ℤ))).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (originCube d (q : ℤ)))] b :=
      (Book.Ch03.publicCoeffField_ae_eq_openCubeSet
        (originCube d (q : ℤ)) a).symm.trans (hcoeff q)
    exact exists_cubeSolution_eq_representatives_of_memLiouvilleClass
      a (q : ℤ) hb hv hactual
  let u : ∀ q : ℕ, Book.Ch03.CubeSolution (originCube d (q : ℤ)) a :=
    fun q => Classical.choose (hexists q)
  have hu : ∀ q, (u q).toH1.toFun = v ∧ (u q).toH1.grad = Dv :=
    fun q => Classical.choose_spec (hexists q)
  refine ⟨C, hC, u, hu, ?_⟩
  have herrorLimit :=
    tendsto_scaleMatchedRadius_zeroAffineError_of_memLiouvilleClass hv
  have hright : Tendsto
      (fun q : ℕ => ENNReal.ofReal C * ENNReal.ofReal
        ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-theta) *
          normalizedAffineCandidateError
            (originCube d (q : ℤ)) v 0 0))
      atTop (nhds 0) := by
    have hmul := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) herrorLimit
      (Or.inr ENNReal.ofReal_ne_top)
    simpa only [mul_zero] using hmul
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hright
  · filter_upwards with q
    exact bot_le
  · filter_upwards [eventually_atTop.2 ⟨n.toNat, fun q hq => by omega⟩]
      with q hnq
    have hnq' : n ≤ (q : ℤ) := by omega
    have hweak : scalarIdentityWeakError a s (q : ℤ) ≤ 1 :=
      (hgood.weakError_le hnq').trans hdelta
    have hbound := hcacc a (q : ℤ) (u q) 0 0 hweak
    have hbound' : finiteCenteredCubeSolutionEnergy a (q : ℤ) (u q)
        ((q : ℤ) - 2) ≤ C * normalizedAffineCandidateError
          (originCube d (q : ℤ)) v 0 0 := by
      simpa only [(hu q).1, euclideanNorm_zero, add_zero] using hbound
    let R : ℝ := Real.sqrt d * (3 : ℝ) ^ q
    have hR : 0 < R := by
      dsimp only [R]
      have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
      positivity
    have hreal : R ^ (-theta) *
        finiteCenteredCubeSolutionEnergy a (q : ℤ) (u q) ((q : ℤ) - 2) ≤
      C * (R ^ (-theta) * normalizedAffineCandidateError
        (originCube d (q : ℤ)) v 0 0) := by
      calc
        R ^ (-theta) * finiteCenteredCubeSolutionEnergy a (q : ℤ) (u q)
              ((q : ℤ) - 2) ≤ R ^ (-theta) *
              (C * normalizedAffineCandidateError
                (originCube d (q : ℤ)) v 0 0) :=
          mul_le_mul_of_nonneg_left hbound' (Real.rpow_nonneg hR.le _)
        _ = C * (R ^ (-theta) * normalizedAffineCandidateError
              (originCube d (q : ℤ)) v 0 0) := by ring
    have hofReal := ENNReal.ofReal_mono hreal
    rw [ENNReal.ofReal_mul hC.le] at hofReal
    simpa only [R] using hofReal

end

end HighContrast
end HCPolySupport
