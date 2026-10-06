/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.RootOfBallTriangle
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.BallTriangle

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.RootTheorem

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The root at the frozen signature, with no hypothesis

`HCPoly.Provider.PolynomialHomogenization.Root.CorrectorComposition.RootOfBallTriangle`
inhabits the frozen statement on one named analytic hypothesis,
`ExactRootBallTriangle`, and
`HCPoly.Provider.PolynomialHomogenization.Root.CorrectorComposition.BallTriangle`
proves that hypothesis.  This module composes the two, so the frozen statement
is inhabited
at the frozen signature `(d : ℕ) (hd : 2 ≤ d)` with **no** hypothesis and no
`NeZero d` binder — the instance is derived from `hd` inside, exactly as the
frozen declaration's own signature requires.

The type below is the frozen statement's type, taken from
`HCPoly.Provider.PolynomialHomogenization.Root.CorrectorComposition.RootOfBallTriangle`; nothing
here restates it.
-/

open HCPolySupport HCPolySupport.HighContrast
open HCPolySupport.HighContrast.CorrectorComposition

namespace HCPolySupport.HighContrast.CorrectorComposition

/-- **The frozen root statement, inhabited unconditionally.** -/
theorem polynomial_homogenization_root (d : ℕ) (hd : 2 ≤ d) :
    ∃ (cd : ℝ) (C₀ : ℝ → ℝ → ℝ → ℝ), 0 < cd ∧
      (∀ s₀ ρ Rad : ℝ, 0 < C₀ s₀ ρ Rad) ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ (C cSrc κ : ℝ) (C₁ : ℝ → ℝ),
          0 < C ∧ 0 < cSrc ∧ 0 < κ ∧ (∀ ϑ : ℝ, 0 < C₁ ϑ) ∧
          ∀ (P : MeasureTheory.Measure (HCPolySupport.HighContrast.CoeffSpace d)) (E :
            HCPolySupport.BlockMat d) (Ψ : ℝ → ℝ)
            (K : ℝ) (S : HCPolySupport.HighContrast.CoeffSpace d → ℝ),
            MeasureTheory.IsProbabilityMeasure P →
            HCPoly.Frozen.IsStationaryLaw P →
            HCPoly.Frozen.IsUnitRangeLaw P →
            HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
            ∃ (abar : HCPolySupport.Mat d) (Lpoly : ℝ) (X :
              HCPolySupport.HighContrast.CoeffSpace d → ℝ)
              (Phi : HCPolySupport.Vec d → HCPolySupport.HighContrast.CoeffSpace d →
                HCPolySupport.Vec d → ℝ)
              (gradPhi : HCPolySupport.Vec d → HCPolySupport.HighContrast.CoeffSpace d
                → HCPolySupport.Vec d → HCPolySupport.Vec d),
              1 ≤ Lpoly ∧
              Measurable X ∧
              (∀ a, 1 ≤ X a) ∧
              -- the family is linear in the slope
              (∀ (c : ℝ) (e e' : HCPolySupport.Vec d) (a :
                HCPolySupport.HighContrast.CoeffSpace d),
                gradPhi (c • e + e') a
                  =ᵐ[MeasureTheory.volume] fun x => c • gradPhi e a x + gradPhi e' a x)
                    ∧
              -- and stationary under integer translations
              (∀ (z : Fin d → ℤ) (e : HCPolySupport.Vec d) (a :
                HCPolySupport.HighContrast.CoeffSpace d),
                gradPhi e (HCPolySupport.HighContrast.translateCoeff z a)
                  =ᵐ[MeasureTheory.volume] fun x =>
                    gradPhi e a (x + HCPolySupport.Source.AKL.intTranslation z)) ∧
              -- ...length
              Lpoly ≤ (2 + HCPolySupport.HighContrast.aspectRatio E * K) ^ C ∧
              -- ...tail
              (∀ t : ℝ, 1 ≤ t →
                P.real {a | C * Lpoly * t ≤ X a} ≤
                  Real.exp (-cd * t ^ ((d : ℝ) - 2 * g)) + (Ψ (cSrc * t))⁻¹) ∧
              -- the symmetric part of the homogenized matrix is positive definite
              (∀ x : HCPolySupport.Vec d, x ≠ 0 → 0 < HCPolySupport.vecDot x
                (HCPolySupport.matVecMul (HCPolySupport.symmPart abar) x)) ∧
              ∃ Ωend : Set (HCPolySupport.HighContrast.CoeffSpace d),
                MeasurableSet Ωend ∧
                P.real Ωend = 1 ∧
                (∀ z : Fin d → ℤ, HCPolySupport.HighContrast.translateCoeff z ⁻¹' Ωend
                  = Ωend) ∧
                -- (1) ...dirichlet
                (∀ s₀ : ℝ, s₀ ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ) →
                    ∀ (ρ Rad : ℝ) (U : Set (HCPolySupport.Vec d)),
                      (∃ j : ℤ, ∃ z : HCPolySupport.Vec d,
                        U = (fun x : HCPolySupport.Vec d =>
                          z + HCPolySupport.matVecMul
                            (HCPolySupport.HighContrast.matSqrt
                              (HCPolySupport.symmPart abar)) x) ''
                            HCPolySupport.openCubeSet
                              (HCPolySupport.originCube d j)) →
                      HCPolySupport.HighContrast.HasBallSandwich
                        (HCPolySupport.HighContrast.matImage
                          ((HCPolySupport.HighContrast.matSqrt (HCPolySupport.symmPart
                          abar))⁻¹) U) ρ Rad →
                      U ⊆ HCPolySupport.HighContrast.ellipsoid abar 1 →
                      HCPolySupport.HighContrast.ellipsoid abar
                          (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U →
                        ∀ a ∈ Ωend, ∀ ε : ℝ, 0 < ε → X a ≤ ε⁻¹ →
                          ∀ g₀ : HCPolySupport.H1Function U,
                            (∃ Lg : ℝ, ∀ᵐ x ∂MeasureTheory.volume.restrict U,
                              |g₀.toFun x| +
                                Real.sqrt (HCPolySupport.vecNormSq (g₀.grad x)) ≤ Lg) →
                            HCPolySupport.HighContrast.hsNormSq U s₀ g₀.grad ≠ ⊤ →
                            ∀ h : HCPolySupport.H1Function U,
                              HCPolySupport.HighContrast.MemAffineH10 U g₀ h →
                              HCPolySupport.HighContrast.IsWeakSolutionOn (fun _ =>
                                abar) U h.grad →
                              ∀ (uFun : HCPolySupport.Vec d → ℝ) (uGrad :
                                HCPolySupport.Vec d → HCPolySupport.Vec d),
                                HCPolySupport.HighContrast.MemH1a0
                                  (HCPolySupport.HighContrast.scaledCoeff ε a) U
                                  (fun x => uFun x - g₀.toFun x)
                                  (fun x => uGrad x - g₀.grad x) →
                                HCPolySupport.HighContrast.IsWeakSolutionOn
                                  (HCPolySupport.HighContrast.scaledCoeff ε a) U uGrad
                                  →
                                HCPolySupport.HighContrast.negSobolevNorm U s₀
                                    (fun x => HCPolySupport.matVecMul
                                      (HCPolySupport.HighContrast.matSqrt
                                      (HCPolySupport.symmPart abar))
                                      (uGrad x - h.grad x)) +
                                  HCPolySupport.HighContrast.negSobolevNorm U s₀
                                    (fun x => HCPolySupport.matVecMul
                                      (HCPolySupport.HighContrast.matSqrt
                                      (HCPolySupport.symmPart abar))⁻¹
                                      (HCPolySupport.matVecMul
                                          (HCPolySupport.HighContrast.scaledCoeff ε a x
                                            - HCPolySupport.skewPart abar)
                                          (uGrad x) -
                                        HCPolySupport.matVecMul
                                          (HCPolySupport.symmPart abar)
                                          (h.grad x))) ≤
                                  ENNReal.ofReal
                                      (C₀ s₀ ρ Rad * (ε * X a) ^ κ) *
                                    HCPolySupport.HighContrast.hsNormSq U s₀
                                        (fun x => HCPolySupport.matVecMul
                                          (HCPolySupport.HighContrast.matSqrt
                                            (HCPolySupport.symmPart abar)) (g₀.grad x))
                                            ^
                                      (1 / 2 : ℝ)) ∧
                -- (2a) ...corrector.equation
                (∀ a ∈ Ωend, ∀ e : HCPolySupport.Vec d,
                  HCPolySupport.HasWeakGradientOn Set.univ (Phi e a) (gradPhi e a) ∧
                    HCPolySupport.HighContrast.IsWeakSolutionOn (fun x => a.1 x)
                      Set.univ
                      (fun x => e + gradPhi e a x)) ∧
                -- (2b) ...corrector: the inverse-radius factor is written on
                -- each summand rather than absorbed into the constant
                (∀ a ∈ Ωend, ∀ e : HCPolySupport.Vec d, ∀ r : ℝ, X a ≤ r →
                  ENNReal.ofReal r⁻¹ *
                      HCPolySupport.HighContrast.negOneNorm
                        (HCPolySupport.HighContrast.ellipsoid abar r)
                        (fun x => HCPolySupport.matVecMul
                          (HCPolySupport.HighContrast.matSqrt (HCPolySupport.symmPart
                          abar))
                          (gradPhi e a x)) +
                    ENNReal.ofReal r⁻¹ *
                      HCPolySupport.HighContrast.negOneNorm
                        (HCPolySupport.HighContrast.ellipsoid abar r)
                        (fun x => HCPolySupport.matVecMul
                          (HCPolySupport.HighContrast.matSqrt (HCPolySupport.symmPart
                          abar))⁻¹
                          (HCPolySupport.matVecMul (a.1 x - HCPolySupport.skewPart abar)
                              (e + gradPhi e a x) -
                            HCPolySupport.matVecMul (HCPolySupport.symmPart abar) e)) ≤
                    ENNReal.ofReal
                      (C * Real.sqrt (HCPolySupport.vecDot e (HCPolySupport.matVecMul
                        (HCPolySupport.symmPart abar) e)) *
                        (r / X a) ^ (-κ))) ∧
                -- (3) ...liouville (double inclusion)
                (∀ a ∈ Ωend, ∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                  (∀ (v : HCPolySupport.Vec d → ℝ) (Dv : HCPolySupport.Vec d →
                    HCPolySupport.Vec d),
                    HCPolySupport.HighContrast.MemLiouvilleClass (fun x => a.1 x) ϑ v
                      Dv →
                    ∃ (e : HCPolySupport.Vec d) (c : ℝ),
                      v =ᵐ[MeasureTheory.volume] fun x => HCPolySupport.vecDot e x +
                        Phi e a x + c) ∧
                  (∀ (e : HCPolySupport.Vec d) (c : ℝ),
                    HCPolySupport.HighContrast.MemLiouvilleClass (fun x => a.1 x) ϑ
                      (fun x => HCPolySupport.vecDot e x + Phi e a x + c)
                      (fun x => e + gradPhi e a x))) ∧
                -- (4) ...lipschitz and (5) ...C1
                (∀ a ∈ Ωend, ∀ R : ℝ, X a ≤ R →
                  ∀ (u : HCPolySupport.Vec d → ℝ) (Du : HCPolySupport.Vec d →
                    HCPolySupport.Vec d),
                    HCPolySupport.HighContrast.MemH1a (fun x => a.1 x)
                      (HCPolySupport.HighContrast.ellipsoid abar R) u Du →
                    HCPolySupport.HighContrast.IsWeakSolutionOn (fun x => a.1 x)
                      (HCPolySupport.HighContrast.ellipsoid abar R) Du →
                    (∀ r : ℝ, r ∈ Set.Icc (X a) R →
                      HCPolySupport.HighContrast.weightedGradNorm (fun x => a.1 x)
                        (HCPolySupport.HighContrast.ellipsoid abar r) Du ≤
                        ENNReal.ofReal C *
                          HCPolySupport.HighContrast.weightedGradNorm (fun x => a.1 x)
                            (HCPolySupport.HighContrast.ellipsoid abar R) Du) ∧
                    (∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                      ∃ e : HCPolySupport.Vec d, ∀ r : ℝ, r ∈ Set.Icc (X a) R →
                        HCPolySupport.HighContrast.weightedGradNorm (fun x => a.1 x)
                          (HCPolySupport.HighContrast.ellipsoid abar r)
                            (fun x => Du x - (e + gradPhi e a x)) ≤
                          ENNReal.ofReal (C₁ ϑ * (r / R) ^ ϑ) *
                            HCPolySupport.HighContrast.weightedGradNorm (fun x => a.1
                              x)
                              (HCPolySupport.HighContrast.ellipsoid abar R) Du)) :=
  polynomial_homogenization_root_of_ballTriangle d hd
    (@CorrectorComposition.exactRootBallTriangle d ⟨by omega⟩)

end HCPolySupport.HighContrast.CorrectorComposition
