/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootInterfaceArithmetic
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.HomogenizedBlockIdentification
public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledQuenchedMinimalScale
public import LeanPool.HighContrastHomogenization.Analytic.EllipsoidGeometry
public import LeanPool.HighContrastHomogenization.Setup.AnalyticCarriers
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootInterface.ScaleFactorArithmetic

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RootAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The homogenization root from the quenched scale and the deterministic package

The root theorem splits in two.  The random side produces the
homogenized block, the polynomial length, the measurable scale with its
two-part tail, and one integer-translation-invariant full-measure event on
which the weighted block row decays past that scale.  The deterministic side
turns the block-row certificate at a sample into the homogenized matrix, one
corrector family, and the five estimates.

This module composes the two sides.  It proves no estimate: every
deterministic input is carried as one hypothesis, and the two abstract
predicates below name the interfaces along which the deterministic modules
communicate.  The first is the normalized weak-error certificate that the
block row is converted into; the second is the characterization of the
corrector family that its estimates are read against.

The reconciliation of the shared constant and the shared error exponent is
performed here, since every clause is weakened by enlarging the constant and
by shrinking the exponent.

## Why the certificate interface is threaded, folded and law-free

Three conventions fix the shape of the interface below; Lean checks none of
them, so they are recorded here.

* **The certificate is per `g` and per rate.**  `GoodScale` takes two leading
  real arguments, the stochastic exponent `g` and the certificate's own decay
  rate `κ`, and every deterministic input reads `GoodScale g κ abar a x` under
  its own `∀ g ∈ Ico 0 1, ∀ κ, 0 < κ`; an input that does not use them may
  ignore them.  The rate is threaded rather than existentially hidden because
  the Dirichlet estimate's exponent *is* the certificate's rate, so it cannot
  be chosen before the certificate is seen.  The Dirichlet input therefore
  takes the rate as a parameter together with the order constraint
  `κ ≤ (1 + g) / 4` that the window `s₀ ∈ Ico ((1 + g) / 4) (1 / 2)` of the
  root statement forces.

* **The provider's constants are law-free but `g`-dependent, while `C₀` sits
  before `g`.**  The Dirichlet input carries a law-free amplitude `Lg ≥ 1`,
  chosen together with the eccentricity power after `g`, which multiplies the
  scale in both the `ε`-premise and the rate factor.  A `g`-dependent constant
  is paid by `Lg ^ κ` and never by `C₀`.

* **The certificate does not live at the raw quenched scale.**  The
  printed-order certificate is produced at the *common affine scale*, a
  positive multiple of the quenched scale depending on the homogenized matrix
  through its witness eccentricity, so `hhomogenized` exports its own factor
  `Lcert * eccentricityFoldFactor abar pCert` and concludes at the enlarged
  scale.  Both factors are law-free times an eccentricity power, so their
  product is again polynomial in the printed length base.

The exported length is `X a * rootLengthFactor abar Lcert pCert Lg pEcc` and
the polynomial exponent is enlarged by `rootLengthExponent Lcert pCert Lg pEcc`.
-/

namespace HCPolySupport
namespace HighContrast
namespace RootInterface

open MeasureTheory
open RootInterface
open RowSupply (eccentricityFoldFactor one_le_eccentricityFoldFactor
  eccentricityFoldFactor_pos measureReal_foldedThreshold_le corrector_factor_mono
  witnessEccentricity_symmPart_le_rpow_aspectRatio)

/-- The homogenization root, given the quenched minimal scale and the
deterministic package, at the threaded and folded certificate interface.

`GoodScale g κ abar a x` is the certificate the deterministic modules read: the
normalized weak-error condition of stochastic exponent `g` and decay rate `κ`
satisfied by the sample `a` above the scale `x`, relative to the homogenized
matrix `abar`.  `CorrectorFamily abar Phi gradPhi` is the characterization of
the corrector family against which the corrector, Liouville and regularity
estimates are stated. -/
theorem polynomial_homogenization_of_quenched_scale
    (d : ℕ) (hd : 2 ≤ d)
    (GoodScale : ℝ → ℝ → HCPolySupport.Mat d →
      HCPolySupport.HighContrast.CoeffSpace d → ℝ → Prop)
    (CorrectorFamily : HCPolySupport.Mat d →
      (HCPolySupport.Vec d → HCPolySupport.HighContrast.CoeffSpace d →
        HCPolySupport.Vec d → ℝ) →
      (HCPolySupport.Vec d → HCPolySupport.HighContrast.CoeffSpace d →
        HCPolySupport.Vec d → HCPolySupport.Vec d) → Prop)
    -- the quenched minimal scale, in the coupled window's shape
    (hquenched : ∃ cd : ℝ, 0 < cd ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ C cSrc kappa delta : ℝ,
          0 < C ∧ 0 < cSrc ∧ 0 < kappa ∧
          delta ∈ Set.Ioo (0 : ℝ) 1 ∧
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d)
            (Psi : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
            IsProbabilityMeasure P →
            HCPoly.Frozen.IsStationaryLaw P →
            HCPoly.Frozen.IsUnitRangeLaw P →
            HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S →
            ∃ (Abar : BlockMat d) (Nann : ℕ) (alpha Lpoly : ℝ)
              (Ssrc X : CoeffSpace d → ℝ),
              0 < alpha ∧
              IsSymmetricBlockMat Abar ∧
              Book.Ch02.BlockPosDef Abar ∧
              (∀ m : ℕ,
                BlockMatLoewnerLE Abar
                  (annealedBlock P (centeredCube d (m : ℤ)))) ∧
              (∀ m : ℕ,
                BlockMatLoewnerLE
                  (blockSharp (annealedBlock P (centeredCube d (m : ℤ))))
                  Abar) ∧
              (∀ j : ℕ,
                annealedContrast P ((Nann + j : ℕ) : ℤ) - 1 ≤
                  (3 : ℝ) ^ (-alpha * (j : ℝ))) ∧
              (∀ a, Ssrc a = max 1 (S a / (3 : ℝ) ^ Nann)) ∧
              1 ≤ Lpoly ∧
              Lpoly ≤ (2 + aspectRatio E * K) ^ C ∧
              Measurable Ssrc ∧
              (∀ a, 1 ≤ Ssrc a) ∧
              Measurable X ∧
              (∀ a, 1 ≤ X a) ∧
              (∀ a, S a ≤ X a) ∧
              (∀ t : ℝ, 1 ≤ t →
                P.real {a | C * Lpoly * t ≤ X a} ≤
                  Real.exp (-cd * t ^ ((d : ℝ) - 2 * g)) +
                    (Psi (cSrc * t))⁻¹) ∧
              ∃ OmegaEnd : Set (CoeffSpace d),
                MeasurableSet OmegaEnd ∧
                P.real OmegaEnd = 1 ∧
                (∀ z : Fin d → ℤ,
                  translateCoeff z ⁻¹' OmegaEnd = OmegaEnd) ∧
                ∀ a ∈ OmegaEnd,
                  Quenched.HasAllLaterPhysicalBlockRow ((1 + 3 * g) / 4)
                    kappa delta Abar S X a)
    -- the normalized weak-error certificate at the identified coefficient
    -- matrix, at its own rate and at its own enlarged scale   [S-1, S-4]
    (hhomogenized : ∀ (g : ℝ), g ∈ Set.Ico (0 : ℝ) 1 →
      ∀ (kappa delta : ℝ), 0 < kappa → delta ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ kappaRate Lcert pCert : ℝ,
          0 < kappaRate ∧ kappaRate ≤ (1 + g) / 4 ∧
          1 ≤ Lcert ∧ 0 ≤ pCert ∧
          ∀ (abar : Mat d), (symmPart abar).PosDef →
            ∀ (Omega : Set (CoeffSpace d)) (S X : CoeffSpace d → ℝ),
              (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Omega = Omega) →
              (∀ b ∈ Omega, 1 ≤ X b) →
              (∀ b ∈ Omega, S b ≤ X b) →
              (∀ b ∈ Omega, Quenched.HasAllLaterPhysicalBlockRow
                ((1 + 3 * g) / 4) kappa delta
                (Book.Ch02.constantBlockMatrix abar) S X b) →
              ∀ a ∈ Omega,
                GoodScale g kappaRate abar a
                  (X a * (Lcert * eccentricityFoldFactor abar pCert)))
    -- the negative-Sobolev Dirichlet error: its constant is fixed before
    -- the exponent, its rate is taken from the certificate, and its own
    -- law-free amplitude and eccentricity power are chosen after `g`
    (hdirichlet : ∃ C₀ : ℝ → ℝ → ℝ → ℝ, (∀ s₀ ρ Rad : ℝ, 0 < C₀ s₀ ρ Rad) ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∀ κ : ℝ, 0 < κ → κ ≤ (1 + g) / 4 →
          ∃ Lg pEcc : ℝ, 1 ≤ Lg ∧ 0 ≤ pEcc ∧
            ∀ (abar : Mat d) (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
              GoodScale g κ abar a x →
              ∀ s₀ : ℝ, s₀ ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ) →
                ∀ (ρ Rad : ℝ) (U : Set (Vec d)),
                  (∃ j : ℤ, ∃ z : Vec d,
                    U = (fun y : Vec d =>
                      z + matVecMul (matSqrt (symmPart abar)) y) ''
                      HCPolySupport.openCubeSet
                        (HCPolySupport.originCube d j)) →
                  HasBallSandwich
                    (matImage ((matSqrt (symmPart abar))⁻¹) U) ρ Rad →
                  U ⊆ ellipsoid abar 1 →
                  ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U →
                    ∀ ε : ℝ, 0 < ε →
                      x * (Lg * eccentricityFoldFactor abar pEcc) ≤ ε⁻¹ →
                      ∀ g₀ : H1Function U,
                        (∃ Lb : ℝ, ∀ᵐ y ∂volume.restrict U,
                          |g₀.toFun y| +
                            Real.sqrt (vecNormSq (g₀.grad y)) ≤ Lb) →
                        hsNormSq U s₀ g₀.grad ≠ ⊤ →
                        ∀ h : H1Function U,
                          MemAffineH10 U g₀ h →
                          IsWeakSolutionOn (fun _ => abar) U h.grad →
                          ∀ (uFun : Vec d → ℝ) (uGrad : Vec d → Vec d),
                            MemH1a0 (scaledCoeff ε a) U
                              (fun y => uFun y - g₀.toFun y)
                              (fun y => uGrad y - g₀.grad y) →
                            IsWeakSolutionOn (scaledCoeff ε a) U uGrad →
                            negSobolevNorm U s₀
                                (fun y => matVecMul (matSqrt (symmPart abar))
                                  (uGrad y - h.grad y)) +
                              negSobolevNorm U s₀
                                (fun y => matVecMul (matSqrt (symmPart abar))⁻¹
                                  (matVecMul (scaledCoeff ε a y - skewPart abar)
                                      (uGrad y) -
                                    matVecMul (symmPart abar) (h.grad y))) ≤
                              ENNReal.ofReal
                                  (C₀ s₀ ρ Rad *
                                    (ε * (x *
                                      (Lg * eccentricityFoldFactor abar pEcc)))
                                        ^ κ) *
                                hsNormSq U s₀
                                    (fun y => matVecMul
                                      (matSqrt (symmPart abar)) (g₀.grad y)) ^
                                  (1 / 2 : ℝ))
    -- the stationary corrector family: its equation, its linearity in the
    -- slope, and its stationarity under integer translation
    (hcorrector : ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
      ∀ κ : ℝ, 0 < κ →
        ∀ abar : Mat d, (symmPart abar).PosDef →
          ∃ (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
            (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
            CorrectorFamily abar Phi gradPhi ∧
            (∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
              gradPhi (c • e + e') a
                =ᵐ[volume] fun x => c • gradPhi e a x + gradPhi e' a x) ∧
            (∀ (z : Fin d → ℤ) (e : Vec d) (a : CoeffSpace d),
              gradPhi e (translateCoeff z a)
                =ᵐ[volume] fun x =>
                  gradPhi e a (x + Source.AKL.intTranslation z)) ∧
            ∀ (a : CoeffSpace d) (x : ℝ), GoodScale g κ abar a x →
              ∀ e : Vec d,
                HasWeakGradientOn Set.univ (Phi e a) (gradPhi e a) ∧
                  IsWeakSolutionOn (fun y => a.1 y) Set.univ
                    (fun y => e + gradPhi e a y))
    -- the corrector-and-flux decay: a visible inverse-radius factor on
    -- each summand, mirroring the frozen clause (2b)
    (hcorrectorDecay : ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
      ∀ κc : ℝ, 0 < κc →
        ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
          ∀ (abar : Mat d) (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
            (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
            CorrectorFamily abar Phi gradPhi →
            ∀ (a : CoeffSpace d) (x : ℝ), 1 ≤ x → GoodScale g κc abar a x →
              ∀ (e : Vec d) (r : ℝ), x ≤ r →
                ENNReal.ofReal r⁻¹ *
                    negOneNorm (ellipsoid abar r)
                      (fun y => matVecMul (matSqrt (symmPart abar))
                        (gradPhi e a y)) +
                  ENNReal.ofReal r⁻¹ *
                    negOneNorm (ellipsoid abar r)
                      (fun y => matVecMul (matSqrt (symmPart abar))⁻¹
                        (matVecMul (a.1 y - skewPart abar) (e + gradPhi e a y) -
                          matVecMul (symmPart abar) e)) ≤
                  ENNReal.ofReal
                    (C * Real.sqrt (vecDot e (matVecMul (symmPart abar) e)) *
                      (r / x) ^ (-κ)))
    -- the Liouville characterization, as a double inclusion
    (hliouville : ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
      ∀ κc : ℝ, 0 < κc →
        ∀ (abar : Mat d) (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
          (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
          CorrectorFamily abar Phi gradPhi →
          ∀ (a : CoeffSpace d) (x : ℝ), GoodScale g κc abar a x →
            ∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
              (∀ (v : Vec d → ℝ) (Dv : Vec d → Vec d),
                MemLiouvilleClass (fun y => a.1 y) ϑ v Dv →
                ∃ (e : Vec d) (c : ℝ),
                  v =ᵐ[volume] fun y => vecDot e y + Phi e a y + c) ∧
              (∀ (e : Vec d) (c : ℝ),
                MemLiouvilleClass (fun y => a.1 y) ϑ
                  (fun y => vecDot e y + Phi e a y + c)
                  (fun y => e + gradPhi e a y)))
    -- the large-scale Lipschitz estimate
    (hlipschitz : ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
      ∀ κc : ℝ, 0 < κc →
        ∃ C : ℝ, 0 < C ∧
          ∀ (abar : Mat d) (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
            GoodScale g κc abar a x →
            ∀ R : ℝ, x ≤ R →
              ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
                MemH1a (fun y => a.1 y) (ellipsoid abar R) u Du →
                IsWeakSolutionOn (fun y => a.1 y) (ellipsoid abar R) Du →
                  ∀ r : ℝ, r ∈ Set.Icc x R →
                    weightedGradNorm (fun y => a.1 y) (ellipsoid abar r) Du ≤
                      ENNReal.ofReal C *
                        weightedGradNorm (fun y => a.1 y)
                          (ellipsoid abar R) Du)
    -- the large-scale C¹ slope approximation: one slope at every radius
    (hC1 : ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
      ∀ κc : ℝ, 0 < κc →
        ∃ C₁ : ℝ → ℝ, (∀ ϑ : ℝ, 0 < C₁ ϑ) ∧
          ∀ (abar : Mat d) (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
            (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
            CorrectorFamily abar Phi gradPhi →
            ∀ (a : CoeffSpace d) (x : ℝ), 1 ≤ x → GoodScale g κc abar a x →
              ∀ R : ℝ, x ≤ R →
                ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
                  MemH1a (fun y => a.1 y) (ellipsoid abar R) u Du →
                  IsWeakSolutionOn (fun y => a.1 y) (ellipsoid abar R) Du →
                    ∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                      ∃ e : Vec d, ∀ r : ℝ, r ∈ Set.Icc x R →
                        weightedGradNorm (fun y => a.1 y) (ellipsoid abar r)
                            (fun y => Du y - (e + gradPhi e a y)) ≤
                          ENNReal.ofReal (C₁ ϑ * (r / R) ^ ϑ) *
                            weightedGradNorm (fun y => a.1 y)
                              (ellipsoid abar R) Du) :
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
  have : NeZero d := ⟨by omega⟩
  obtain ⟨cd, hcd, hquenched⟩ := hquenched
  obtain ⟨C₀, hC₀, hdirichlet⟩ := hdirichlet
  refine ⟨cd, C₀, hcd, hC₀, ?_⟩
  intro g hg
  obtain ⟨Cq, cSrc, kappaRow, deltaRow, hCq, hcSrc, hkappaRow, hdeltaRow,
    hquenched⟩ :=
    hquenched g hg
  obtain ⟨kappaRate, Lcert, pCert, hkappaRate, hkappaRateLe, hLcert, hpCert,
    hhomogenized⟩ :=
    hhomogenized g hg kappaRow deltaRow hkappaRow hdeltaRow
  obtain ⟨Lg, pEcc, hLg, hpEcc, hdirichlet⟩ :=
    hdirichlet g hg kappaRate hkappaRate hkappaRateLe
  obtain ⟨Ccor, κcor, hCcor, hκcor, hcorrectorDecay⟩ :=
    hcorrectorDecay g hg kappaRate hkappaRate
  obtain ⟨Clip, hClip, hlipschitz⟩ := hlipschitz g hg kappaRate hkappaRate
  obtain ⟨C₁, hC₁, hC1⟩ := hC1 g hg kappaRate hkappaRate
  have hexp : (0 : ℝ) ≤ rootLengthExponent Lcert pCert Lg pEcc :=
    rootLengthExponent_nonneg hLcert hpCert hLg hpEcc
  refine ⟨max Cq (max Ccor Clip) + rootLengthExponent Lcert pCert Lg pEcc,
    cSrc, min kappaRate κcor, C₁,
    lt_of_lt_of_le (lt_of_lt_of_le hCq (le_max_left _ _))
      (le_add_of_nonneg_right hexp),
    hcSrc, lt_min hkappaRate hκcor, hC₁, ?_⟩
  intro P E Ψ K S hP hstationary hunit hdagger
  let : MeasureTheory.IsProbabilityMeasure P := hP
  obtain ⟨Abar, Nann, alpha, Lpoly, -, X, halpha, hAbarSymm, hAbarPos,
    hlower, hupper, hcontrast, -, hLpolyOne,
    hLpolyBound, -, -, hXMeasurable, hXOne, hburn, htail,
    Ωend, hΩmeasurable, hΩfull, hΩinvariant, hΩrow⟩ :=
    hquenched P E Ψ K S hP hstationary hunit hdagger
  obtain ⟨abar, habar, hAbarEq⟩ :=
    exists_homogenizedCoeffMatrix_of_annealedBlock_sandwich
      hAbarSymm hAbarPos hlower hupper halpha hcontrast
  obtain ⟨Phi, gradPhi, hfamily, hlinear, hstationaryFamily, hequation⟩ :=
    hcorrector g hg kappaRate hkappaRate abar habar
  have hproduct : (1 : ℝ) ≤ aspectRatio E * K := by
    have hAspect : 1 ≤ aspectRatio E :=
      one_le_aspectRatio_of_coarseEllipticityDagger hdagger
    exact one_le_mul_of_one_le_of_one_le hAspect
      hdagger.one_lt_growthWitness.le
  have hbase2 : (2 : ℝ) ≤ 2 + aspectRatio E * K :=
    le_add_of_nonneg_right (zero_le_one.trans hproduct)
  have hbase : (1 : ℝ) ≤ 2 + aspectRatio E * K := le_trans (by norm_num) hbase2
  have hecc :
      witnessEccentricity (symmPart abar) ≤ (2 + aspectRatio E * K) ^ (5 : ℝ) :=
    witnessEccentricity_symmPart_le_rpow_aspectRatio hdagger habar hAbarSymm
      hlower hAbarEq
  -- the two enlargement factors, and the composite root factor
  have hcertFactor : (1 : ℝ) ≤ Lcert * eccentricityFoldFactor abar pCert :=
    one_le_mul_of_one_le_of_one_le hLcert
      (one_le_eccentricityFoldFactor abar pCert)
  have hprovFactor : (1 : ℝ) ≤ Lg * eccentricityFoldFactor abar pEcc :=
    one_le_mul_of_one_le_of_one_le hLg (one_le_eccentricityFoldFactor abar pEcc)
  have hF1 : (1 : ℝ) ≤ rootLengthFactor abar Lcert pCert Lg pEcc :=
    one_le_rootLengthFactor hLcert hLg
  have hF0 : (0 : ℝ) < rootLengthFactor abar Lcert pCert Lg pEcc :=
    rootLengthFactor_pos hLcert hLg
  have hFbound : rootLengthFactor abar Lcert pCert Lg pEcc ≤
      (2 + aspectRatio E * K) ^ rootLengthExponent Lcert pCert Lg pEcc :=
    rootLengthFactor_le_rpow hbase2 hLcert hpCert hLg hpEcc hecc
  have hLpolyBound' : Lpoly ≤
      (2 + aspectRatio E * K) ^ max Cq (max Ccor Clip) :=
    le_rpow_of_le_rpow_of_exponent_le hbase (le_max_left _ _) hLpolyBound
  have hlength : Lpoly * rootLengthFactor abar Lcert pCert Lg pEcc ≤
      (2 + aspectRatio E * K) ^
        (max Cq (max Ccor Clip) + rootLengthExponent Lcert pCert Lg pEcc) :=
    RowSupply.mul_le_rpow_add hbase (le_trans zero_le_one hF1) hLpolyBound'
      hFbound
  have hsplit : ∀ a : CoeffSpace d,
      X a * rootLengthFactor abar Lcert pCert Lg pEcc =
        X a * (Lcert * eccentricityFoldFactor abar pCert) *
          (Lg * eccentricityFoldFactor abar pEcc) := by
    intro a
    unfold rootLengthFactor
    ring
  -- the certificate, at the scale the printed-order producer supplies it
  have hcert : ∀ a ∈ Ωend,
      GoodScale g kappaRate abar a
        (X a * (Lcert * eccentricityFoldFactor abar pCert)) :=
    hhomogenized abar habar Ωend S X hΩinvariant
      (fun b _ => hXOne b) (fun b _ => hburn b)
      (fun b hb => by simpa only [hAbarEq] using hΩrow b hb)
  have hcertOne : ∀ a : CoeffSpace d,
      (1 : ℝ) ≤ X a * (Lcert * eccentricityFoldFactor abar pCert) := fun a =>
    one_le_mul_factor (hXOne a) hcertFactor
  have hcertLe : ∀ a : CoeffSpace d,
      X a * (Lcert * eccentricityFoldFactor abar pCert) ≤
        X a * rootLengthFactor abar Lcert pCert Lg pEcc := fun a => by
    rw [hsplit a]
    exact le_mul_factor (le_trans zero_le_one (hcertOne a)) hprovFactor
  refine ⟨abar, Lpoly * rootLengthFactor abar Lcert pCert Lg pEcc,
    fun a => X a * rootLengthFactor abar Lcert pCert Lg pEcc, Phi, gradPhi,
    one_le_mul_factor hLpolyOne hF1,
    measurable_mul_factor hXMeasurable,
    fun a => one_le_mul_factor (hXOne a) hF1,
    hlinear, hstationaryFamily, hlength,
    ?_, fun x hx => vecDot_matVecMul_pos_of_posDef habar hx,
    Ωend, hΩmeasurable, hΩfull, hΩinvariant, ?_, ?_, ?_, ?_, ?_⟩
  · -- the two-part tail, at the reconciled constant; the factor cancels
    intro t ht
    refine le_trans ?_ (htail t ht)
    exact measureReal_foldedThreshold_le (zero_le_one.trans hLpolyOne)
      (zero_le_one.trans ht) hF0
      ((le_max_left _ _).trans (le_add_of_nonneg_right hexp))
  · -- (1) the Dirichlet estimate, at the reconciled exponent
    intro s₀ hs₀ ρ Rad U hU hsandwich hUsub hinner a ha ε hε hXε g₀ hg₀ hg₀norm
      h hh hhsol uFun uGrad huH1 husol
    simp only [hsplit] at hXε ⊢
    refine le_trans
      (hdirichlet abar a (X a * (Lcert * eccentricityFoldFactor abar pCert))
        (hcertOne a) (hcert a ha) s₀ hs₀ ρ Rad U hU hsandwich hUsub hinner ε hε
        hXε g₀ hg₀ hg₀norm h hh hhsol uFun uGrad huH1 husol) ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    refine mul_le_mul_of_nonneg_left ?_ (hC₀ s₀ ρ Rad).le
    refine rpow_le_rpow_of_exponent_ge_of_le_one
      (mul_pos hε (lt_of_lt_of_le zero_lt_one
        (one_le_mul_factor (hcertOne a) hprovFactor))) ?_ (min_le_left _ _)
    calc ε * (X a * (Lcert * eccentricityFoldFactor abar pCert) *
            (Lg * eccentricityFoldFactor abar pEcc)) ≤ ε * ε⁻¹ :=
          mul_le_mul_of_nonneg_left hXε hε.le
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hε)
  · -- (2a) the corrector equation
    exact fun a ha => hequation a
      (X a * (Lcert * eccentricityFoldFactor abar pCert)) (hcert a ha)
  · -- (2b) the corrector estimate, at the reconciled constant and exponent
    intro a ha e r hr
    have hcertPos : (0 : ℝ) <
        X a * (Lcert * eccentricityFoldFactor abar pCert) :=
      lt_of_lt_of_le zero_lt_one (hcertOne a)
    have hr' : X a * (Lcert * eccentricityFoldFactor abar pCert) ≤ r :=
      (hcertLe a).trans hr
    refine le_trans
      (hcorrectorDecay abar Phi gradPhi hfamily a
        (X a * (Lcert * eccentricityFoldFactor abar pCert)) (hcertOne a)
        (hcert a ha) e r hr') (ENNReal.ofReal_le_ofReal ?_)
    have hrpos : (0 : ℝ) < r := lt_of_lt_of_le hcertPos hr'
    have hratio : (1 : ℝ) ≤ r / (X a * rootLengthFactor abar Lcert pCert Lg pEcc) :=
      (one_le_div (lt_of_lt_of_le hcertPos (hcertLe a))).mpr hr
    have hsqrt : 0 ≤ Real.sqrt (vecDot e (matVecMul (symmPart abar) e)) :=
      Real.sqrt_nonneg _
    refine mul_le_mul
      (mul_le_mul_of_nonneg_right
        (((le_max_left Ccor Clip).trans (le_max_right Cq _)).trans
          (le_add_of_nonneg_right hexp)) hsqrt)
      (le_trans
        (corrector_factor_mono hcertPos (hcertLe a) hrpos hκcor)
        (rpow_neg_le_rpow_neg_of_exponent_ge hratio (min_le_right _ _)))
      (Real.rpow_nonneg (by positivity) _)
      (by positivity)
  · -- (3) the Liouville double inclusion
    exact fun a ha => hliouville g hg kappaRate hkappaRate abar Phi gradPhi
      hfamily a (X a * (Lcert * eccentricityFoldFactor abar pCert))
      (hcert a ha)
  · -- (4) and (5), the two large-scale regularity estimates
    intro a ha R hR u Du hu husol
    have hR' : X a * (Lcert * eccentricityFoldFactor abar pCert) ≤ R :=
      (hcertLe a).trans hR
    refine ⟨fun r hr => ?_, fun ϑ hϑ => ?_⟩
    swap
    · -- (5) the C¹ estimate: the slope of the wider window serves the narrower
      obtain ⟨e, he⟩ :=
        hC1 abar Phi gradPhi hfamily a
          (X a * (Lcert * eccentricityFoldFactor abar pCert)) (hcertOne a)
          (hcert a ha) R hR' u Du hu husol ϑ hϑ
      exact ⟨e, fun r hr =>
        he r (RowSupply.Icc_foldedScale_subset (hcertLe a) hr)⟩
    refine le_trans
      (hlipschitz abar a (X a * (Lcert * eccentricityFoldFactor abar pCert))
        (hcertOne a) (hcert a ha) R hR' u Du hu husol r
        (RowSupply.Icc_foldedScale_subset (hcertLe a) hr))
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (((le_max_right Ccor Clip).trans (le_max_right Cq _)).trans
          (le_add_of_nonneg_right hexp))) _)

end RootInterface
end HighContrast
end HCPolySupport
