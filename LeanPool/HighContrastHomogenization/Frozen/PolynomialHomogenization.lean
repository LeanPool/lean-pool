/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup
public import LeanPool.HighContrastHomogenization.Setup.AnalyticCarriers
public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange
public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.RootTheorem

/-!
# High-contrast homogenization: Frozen.PolynomialHomogenization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Theorem `t.random.homogenization`

Polynomial homogenization with a random microscopic source scale: one
homogenized matrix, one polynomially bounded length, one homogenization scale
with a two-part tail, and one full-probability event on which the Dirichlet
estimate, the corrector equation and estimate, the Liouville classification and
the two large-scale regularity estimates all hold for a single corrector family.
-/

/-- **Theorem `t.random.homogenization`**: the polynomial
homogenization scale for a random microscopic source scale.

**Scope.**  Two deviations from the reference text, neither of which touches any
quantitative content.  The coefficient fields are uniformly elliptic almost
everywhere, with ellipticity constants belonging to the field and entering no
estimate; `e.qualitative.ellipticity` follows from this.  The domains
carrying the Dirichlet estimate are the adapted cells of the homogenized
matrix — translates of the image of a centred triadic cube under the symmetric
square root of `s̄` — normalized to sit between two concentric adapted
ellipsoids, rather than the bounded Lipschitz domains of the reference text.
Every domain the development uses is such a cell; the normalization fixes the
domain's size relative to `s̄`, which is the scale the endpoint constant would
otherwise have to carry, and it is satisfiable at every dimension because the
window between the two ellipsoids has triadic ratio three.
Every quantitative object below — `Π`, the gauge and its growth witness, the
homogenized matrix, the homogenization length and its tail, and every
dimensional constant and exponent — is unchanged by either.

**The centering convention of the flux displays.**  The two flux differences
below — in the Dirichlet estimate and in the corrector estimate — are written
for the skew-centered field: the constant skew part of the homogenized matrix is
subtracted from the coefficient field, and the homogenized matrix enters through
its symmetric part.  This is the standing convention under which a coefficient
field and its antisymmetric part are read modulo a constant antisymmetric
matrix.  It is the form the argument establishes, a constant skew part changing
neither the solutions nor the coarse-grained blocks; and it is the form that is
invariant under that recentering, which the displays written with the full
homogenized matrix are not.

**Valuation.**  All norms and energies are valued in `ℝ≥0∞`, so that each
estimate is an assertion about the quantity the reference text writes rather
than about a totalized integral that vanishes when that quantity is infinite.

**Constants.**  The endpoint constant of the Dirichlet estimate depends on
nothing but the dimension, the regularity exponent, and the shape of the adapted
domain `s̄^{-1/2}U` — the radii of concentric balls trapping it.  That is the
dependence the reference text records for it, and its binder accordingly stands
outside the exponent and outside the law.

Two separate things stand behind that reading, and they should not be confused.
Writing the flux difference for the skew-centered field removes one obstruction
to it: a constant skew part of the homogenized matrix is seen by no other datum
of the statement, and it moves the difference written with the full homogenized
matrix while leaving the centered one fixed.  That is what makes the printed
dependence list available to write down; it is not what makes it true.  What a
proof must use for the rest is the bound on the length below.  A law that is
badly conditioned — of large contrast, strongly anisotropic, or carrying a large
source scale — pays for it in the reference aspect ratio and the growth witness,
and the length bound lets the homogenization scale, and with it the largest
admissible microscale, absorb exactly that; the estimate is read only below that
scale.  A proof of this theorem has to honour that dependency, and the statement
is what expresses it.

The two radii enter only through their ratio.  Dilating the coefficient field
and the homogenized matrix together leaves the domain condition exactly fixed,
slides both radii along a common ray, and multiplies both sides of the estimate
by the same factor; so a constant depending on the two radii separately carries
no more than one depending on their ratio, which is the dimensionless datum the
reference text's own condition on the domain records.

The constants `C`, `C_0` and `C_1` are asserted positive; the reference text
asserts only their finiteness, and positivity is a normalization, every
occurrence of each being weakened by increasing it.

**Measurability.**  The three membership classes below carry the measurability
of the function and of its gradient field that their printed counterparts —
completions of smooth functions in a norm — presuppose.  Without it the relation
that ties a function to its weak gradient compares integrals that may each fail
to converge, and a pair on which they both fail satisfies it for no reason;
whether the wider class actually contains such a pair is a question about sets
of inner measure zero, and is not settled here.  Two
consequences are worth stating.  The second inclusion of the Liouville clause is
the only place this statement says anything about the measurability of the
corrector family.  And the corrector equation, read on its own, does not exclude
such a pair: what excludes it is that same inclusion, which puts the corrector
in the local class.

**Approximants.**  The coefficient-weighted spaces are closures under globally
smooth approximants, where the reference text closes the functions smooth on the
domain.  The two readings are recorded as distinct because the Liouville clause
states a double inclusion, in which the class occurs in both directions.  On a
bounded convex domain a function smooth on the domain agrees, after a dilation
towards an interior point, with a globally smooth function on the whole closure,
so the two readings are separated only by the continuity of that dilation in the
norm.

The invariance of `Ω_end` under integer translations is proved with the theorem
and is carried in the conclusion. -/

theorem HCPoly.Frozen.polynomial_homogenization_random_source
    (d : ℕ) (hd : 2 ≤ d) :
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
                              (HCPolySupport.HighContrast.ellipsoid abar R) Du))
    := by
  exact HCPolySupport.HighContrast.CorrectorComposition.polynomial_homogenization_root d hd
