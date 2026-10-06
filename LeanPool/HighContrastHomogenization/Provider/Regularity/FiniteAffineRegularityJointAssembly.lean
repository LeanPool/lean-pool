/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineGradientExcessRateSelection
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorJointGoodTailEquation

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineRegularityJointAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Joint finite-excess decay and infinite corrector assembly

One small good-tail threshold supplies both the finite-volume real-rate excess
estimate and the unique joint normalized local corrector family with its local
equations.
-/

namespace HCPolySupport
namespace HighContrast

open scoped ENNReal

noncomputable section

/-- Joint normalized local-limit and fixed-cube equation property. -/
@[expose]
def IsFiniteAffineCorrectionJointLocalEquation
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d) : Prop :=
  (∀ e : Vec d,
    IsNormalizedLocalLimit (finiteAffineCorrectionLocalSequence a e) (Phi e)) ∧
  ∀ (e : Vec d) (q : ℕ),
    IsAHarmonicGradient
      (a.coeffOn (originCube d (q : ℤ))).toCoeffField
      (localGradientCube d q)
      ((show H1Function (localGradientCube d q) from by
        simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
          finiteAffineBoundaryH1 (q : ℤ) e) +
        (Phi e).localH1Function q).grad

/-- A single scalar good tail produces both sides of the regularity interface:
real-rate finite excess decay on every later interval and the unique joint
normalized local corrector family satisfying every fixed-cube equation. -/
theorem exists_scalarIdentityFiniteExcessDecayAndJointLocalEquationConstants
    (d : ℕ) [NeZero d] (s eta : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    ∃ Cfamily c Cdec : ℝ,
      1 ≤ Cfamily ∧ c ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < Cdec ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodTail a s delta n →
          (∃! Phi : Vec d → NormalizedLocalH1Carrier d,
            IsFiniteAffineCorrectionJointLocalEquation a Phi) ∧
          ∀ m : ℤ, n < m →
            ∃ Q : ℤ → Mat d,
              IsFiniteAffineSlopeFamily a delta Cfamily n m Q ∧
              ∀ u : Book.Ch03.CubeSolution (originCube d m) a,
                finiteAffineGradientExcess a n m u ≤
                  ENNReal.ofReal
                      (Cdec * Real.rpow 3 (-eta * ((m - n : ℤ) : ℝ))) *
                    finiteAffineGradientExcess a m m u := by
  obtain ⟨Cfamily, cB, Cdec, hCfamily, hcB, hCdec, hdecay⟩ :=
    exists_scalarIdentityFiniteAffineGradientExcessRealRateDecayConstants
      d s eta hs hs_lt heta0 heta1
  obtain ⟨cC, hcC, hlimit⟩ :=
    exists_finiteAffineCorrectionJointLocalEquationGoodTailThreshold
      d s hs hs_lt
  let c : ℝ := min cB cC
  have hc0 : 0 < c := lt_min hcB hcC.1
  have hc1 : c < 1 := (min_le_right cB cC).trans_lt hcC.2
  refine ⟨Cfamily, c, Cdec, hCfamily, ⟨hc0, hc1⟩, hCdec, ?_⟩
  intro a delta n hdelta hgood
  have hdeltaB : delta ∈ Set.Ioc (0 : ℝ) cB :=
    ⟨(Set.mem_Ioc.mp hdelta).1,
      (Set.mem_Ioc.mp hdelta).2.trans (min_le_left _ _)⟩
  have hdeltaC : delta ∈ Set.Ioc (0 : ℝ) cC :=
    ⟨(Set.mem_Ioc.mp hdelta).1,
      (Set.mem_Ioc.mp hdelta).2.trans (min_le_right _ _)⟩
  refine ⟨?_, ?_⟩
  · simpa only [IsFiniteAffineCorrectionJointLocalEquation] using
      hlimit a delta n hdeltaC hgood
  intro m hnm
  exact hdecay a delta n m hnm hdeltaB (hgood.goodMaxOnInterval hnm.le)

end
end HighContrast
end HCPolySupport
