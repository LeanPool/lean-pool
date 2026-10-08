/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.DirichletHoleBridge
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.LargeScaleC1AtCertificate
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootAssembly

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.RootOfBallTriangle

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The root at the frozen signature, on one analytic hypothesis

The large-scale C¹ slope approximation clause terminal
`exactRootGaugeTerminal_onReconciled_of_ballTriangle` follows from one
named analytic hypothesis, the weighted-energy triangle inequality on the
exact-root pullback ball.  The frozen statement is therefore inhabited here with
**that** as its only hypothesis, at the frozen signature `(d : ℕ) (hd : 2 ≤ d)`,
the `NeZero d` instance being derived from `hd` inside rather than taken as a
binder.

The remaining binders are supplied unchanged: the coupled providers,
`hhomogenized`, the negative-Sobolev Dirichlet error clause bridge, the unconditional the
stationary corrector family clause, the decay, Liouville and Lipschitz clauses, and the
assembly.

## Where the corrector constant is quantified

The statement selects `C₁ : ℝ → ℝ` after `g` and before the coefficient sample and
the point.  A corrector family whose delay and whose starting index are chosen after
the sample cannot supply it: those two data would have to appear in `C₁`, which is
already fixed by then.

The route taken avoids the delay rather than accommodating it.  The certificate's own
power tail is read at order `printCertificateOrder g` and at the starting index
`triadicCeilingIndex x`, with no delay and no restart, so every constant the
simultaneous-slope row needs depends on `d`, `g` and the tolerance alone, provided the
corrector smallness stays below a threshold free of the coefficient law.
`polynomial_homogenization_root_of_ballTriangle` below is stated at that binder order.
-/

/-! ## The root, at the frozen statement's own signature -/

open HCPolySupport HCPolySupport.HighContrast
open HCPolySupport.HighContrast.CorrectorComposition

namespace HCPolySupport.HighContrast.CorrectorComposition

/-- **The frozen root statement, inhabited conditionally on the
weighted-energy triangle inequality on the exact-root pullback ball alone.**
The type below is the frozen statement's type, unchanged, and the
signature is the frozen one — `(d : ℕ) (hd : 2 ≤ d)` — with the `NeZero d`
instance *derived* from `hd` rather than taken as a binder. -/
theorem polynomial_homogenization_root_of_ballTriangle (d : ℕ) (hd : 2 ≤ d)
    (htri : @CorrectorComposition.ExactRootBallTriangle d ⟨by omega⟩) :
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
                              (HCPolySupport.HighContrast.ellipsoid abar R) Du)) := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨cStar, hcStar⟩ := CorrectorComposition.exists_commonCeiling
      (fun _ _ => True) _
      (fun g c => ∀ hg : g ∈ Set.Ico (0 : ℝ) 1,
        c ≤ canonicalCorrectorSmallness d g hg)
      (fun _ _ => True) (fun _ _ => True)
    (fun _g _hg => ⟨1 / 2, ⟨by norm_num, by norm_num⟩, fun _c _ _ => trivial⟩)
    (CorrectorComposition.exists_largeScaleLipschitz_of_reconciledRootGoodScale d)
    (fun g hg => ⟨canonicalCorrectorSmallness d g hg,
      canonicalCorrectorSmallness_mem d g hg,
      fun _c _hc hcc _hg => hcc⟩)
    (fun _g _hg => ⟨1 / 2, ⟨by norm_num, by norm_num⟩, fun _c _ _ => trivial⟩)
    (fun _g _hg => ⟨1 / 2, ⟨by norm_num, by norm_num⟩, fun _c _ _ => trivial⟩)
  have hceil : ∀ (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1),
      cStar g ∈ Set.Ioo (0 : ℝ) 1 ∧
      cStar g ≤ canonicalCorrectorSmallness d g hg :=
    fun g hg => ⟨(hcStar g hg).1, (hcStar g hg).2.2.2.1 hg⟩
  have hcore : ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
      ∃ cSc : ℝ, 0 < cSc ∧
        ∃ alpha Cdelay : ℝ, 0 < alpha ∧ 0 ≤ Cdelay ∧
          ∀ (cStar' gBase : ℝ) (Pbase : MeasureTheory.Measure (CoeffSpace d))
            (Ebase : BlockMat d) (PsiBase : ℝ → ℝ) (Kbase : ℝ)
            (Sbase : CoeffSpace d → ℝ),
            cStar' ∈ Set.Ioo 0 cSc →
            gBase = (1 + g) / 2 →
            MeasureTheory.IsProbabilityMeasure Pbase →
            HCPoly.Frozen.IsStationaryLaw Pbase →
            HCPoly.Frozen.IsUnitRangeLaw Pbase →
            HCPoly.Frozen.CoarseEllipticityDagger
              Pbase gBase Ebase PsiBase Kbase Sbase →
            annealedContrast Pbase 0 - 1 ≤ cStar' →
            blockContrast Ebase ≤ 1 + cSc →
            ∃ m0 : ℕ,
              (3 : ℝ) ^ m0 ≤ (2 + aspectRatio Ebase * Kbase) ^ Cdelay ∧
              ∀ j : ℕ,
                annealedContrast Pbase ((m0 + j : ℕ) : ℤ) - 1 ≤
                  (3 : ℝ) ^ (-alpha * (j : ℝ)) := by
    intro g hg
    obtain ⟨cSc, hcSc, alpha, Cdelay, halpha, hCdelay, hbody⟩ :=
      endpoint_hcore_body_corrected d hd g hg
    exact ⟨cSc, hcSc, alpha, Cdelay, halpha, hCdelay,
      fun cStar' gBase Pbase Ebase PsiBase Kbase Sbase hcStar' =>
        hbody cStar' gBase Pbase Ebase PsiBase Kbase Sbase
          ⟨hcStar'.1, hcStar'.2.le⟩⟩
  refine RootInterface.polynomial_homogenization_of_quenched_scale d hd
    (CorrectorComposition.reconciledRootGoodScaleOn d cStar)
    (Root.RootPushCorrectorFamilyPredicate d)
    (Quenched.exists_quenched_minimal_scale_of_coupled_providers d hd hcore
      (Quenched.exists_prop211_rebase_provider d hd)
      (Quenched.exists_coupledWitnessAssembly d hd
        (Quenched.exists_coupledWitnessEngineData_of_endpoint d hd)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hhomogenized, at the event-retaining certificate
    exact fun g hg kappa delta hkappa hdelta =>
      CorrectorComposition.exists_rootGoodScaleOn_of_quenchedEventRow d hg (hceil g hg).1
        hkappa hdelta
  · -- the negative-Sobolev Dirichlet error clause, the Dirichlet module's inhabitant, bridged
    exact CorrectorComposition.dirichletHole_reconciledRootGoodScaleOn d cStar
  · -- the stationary corrector family clause
    exact fun g hg κ _hκ =>
      CorrectorComposition.correctorFamilyHole_of_reconciledRootGoodScaleOn d cStar hg κ
  · -- the corrector-and-flux decay clause
    exact CorrectorComposition.exists_correctorDecay_of_reconciledRootGoodScaleOn d cStar hceil
  · -- the Liouville characterization clause
    exact fun g hg κc _hκc abar Phi gradPhi hmarker a x hgood =>
      (Root.canonicalPullbackFamily_of_pushforwardMarker
          (CorrectorComposition.rootPushCanonicalFamily_of_rootGoodScaleOn d (g := g) (c := cStar g)
            (kappaRate := κc) hg)
          abar Phi gradPhi hmarker).physicalLiouvilleDoubleInclusion a x hgood
  · -- the large-scale Lipschitz estimate clause
    intro g hg κc hκc
    obtain ⟨C, hC, hbody⟩ := (hcStar g hg).2.2.1 κc hκc
    exact ⟨C, hC, fun abar a x hx hgood =>
      hbody abar a x hx
        (CorrectorComposition.reconciledRootGoodScale_of_reconciledRootGoodScaleOn cStar hgood)⟩
  · -- the large-scale C¹ slope approximation clause, now conditional on the ball triangle
    -- inequality alone
    intro g hg κc hκc
    exact CorrectorComposition.largeScaleC1_of_terminal_atCertificate d
      (CorrectorComposition.reconciledRootGoodScaleOn d cStar g κc)
      (Root.RootPushCorrectorFamilyPredicate d)
      (fun abar a x h => CorrectorComposition.rootGoodScaleAt_posDef h.1)
      (CorrectorComposition.pushforwardMarker_linear d)
      (fun eta heta =>
        CorrectorComposition.exactRootGaugeTerminal_onReconciled_of_ballTriangle d htri cStar hg
          (hceil g hg).1.1 hκc heta)

end HCPolySupport.HighContrast.CorrectorComposition
