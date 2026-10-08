/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalCauchy
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalEquation

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorJointGoodTailEquation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fixed-cube equations for joint corrector limits

A sufficiently small scalar good tail gives a unique family of normalized
local finite-corrector limits.  On every fixed centered cube, adding the
affine boundary function to the corresponding local representative gives a
coefficient-harmonic gradient.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- Below a dimension-and-exponent threshold, a scalar good tail determines
one unique joint normalized local limit whose affine extensions are
coefficient-harmonic on every fixed centered cube. -/
theorem exists_finiteAffineCorrectionJointLocalEquationGoodTailThreshold
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∃! Phi : Vec d → NormalizedLocalH1Carrier d,
          (∀ e : Vec d,
            IsNormalizedLocalLimit
              (finiteAffineCorrectionLocalSequence a e) (Phi e)) ∧
          ∀ (e : Vec d) (q : ℕ),
            IsAHarmonicGradient
              (a.coeffOn (originCube d (q : ℤ))).toCoeffField
              (localGradientCube d q)
              ((show H1Function (localGradientCube d q) from by
                simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
                  finiteAffineBoundaryH1 (q : ℤ) e) +
                (Phi e).localH1Function q).grad := by
  obtain ⟨c, hc, hCauchy⟩ :=
    exists_finiteAffineCorrectionLocalCauchyThreshold d s hs hs_lt
  refine ⟨c, hc, ?_⟩
  intro a delta n hdelta hgood
  have hLocalCauchy : FiniteAffineCorrectionLocalCauchy a :=
    hCauchy a delta n hdelta hgood
  obtain ⟨Phi, hPhi, hPhiUnique⟩ :=
    existsUnique_finiteAffineCorrectionJointLocalLimit a hLocalCauchy
  refine ⟨Phi, ⟨?_, ?_⟩, ?_⟩
  · simpa only [IsFiniteAffineCorrectionJointLocalLimit] using hPhi
  · intro e q
    have hPhiEq :
        Phi = finiteAffineCorrectionJointLocalLimit a hLocalCauchy :=
      (isFiniteAffineCorrectionJointLocalLimit_iff_eq
        a hLocalCauchy Phi).mp hPhi
    rw [hPhiEq]
    simpa only [finiteAffineCorrectionJointLocalH1] using
      finiteAffineCorrectionJointLocalH1_isHarmonic a hLocalCauchy e q
  · intro Psi hPsi
    have hPsiLimit : IsFiniteAffineCorrectionJointLocalLimit a Psi := by
      simpa only [IsFiniteAffineCorrectionJointLocalLimit] using hPsi.1
    exact hPhiUnique Psi hPsiLimit

end

end HighContrast
end HCPolySupport
