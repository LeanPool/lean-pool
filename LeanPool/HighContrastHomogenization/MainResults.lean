/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.PolynomialEntry
public import LeanPool.HighContrastHomogenization.Frozen.PolynomialHomogenization
public import LeanPool.HighContrastHomogenization.Frozen.QuenchedConvergence
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AlgebraicConvergenceAssembly
public import LeanPool.HighContrastHomogenization.Provider.UniformEllipticity.UniformHomogenization

/-!
# High-contrast homogenization: MainResults

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Main results

The headline theorems of the formalization of the paper *HCPolySupport at a
polynomial scale in high contrast* (Armstrong--Kuusi--Loher), stated here
in full.  Each is proved by direct application of the theorem it restates, so
the statement displayed in this file is the one that has been checked.

* `HCPoly.polynomial_entry` -- Theorem A of the paper, `t.polynomial.entry`:
  entry into the small-contrast regime at every generation beyond a multiple of
  the base-three logarithm of `2 + Π K`, hence at a length polynomial in the
  reference aspect ratio and in the growth constant of the source tail.
* `HCPoly.algebraic_convergence` -- Theorem B of the paper,
  `t.algebraic.convergence`: beyond a generation bounded by a multiple of the
  base-three logarithm of `2 + Π K`, the annealed contrast decays geometrically
  and the annealed blocks converge, in the Loewner order and at the same rate,
  to a deterministic self-dual positive definite limit block.
* `HCPoly.uniform_homogenization` -- Theorem C of the paper,
  `t.uniform.homogenization`: the uniformly elliptic model, obtained as the
  instance of Theorem D at exponent zero with a vanishing source scale, with a
  homogenization scale whose tail is `exp(-t^d)` beyond a length polynomial in
  the ellipticity ratio.
* `HCPoly.polynomial_homogenization` -- Theorem D of the paper,
  `t.random.homogenization`: quantitative homogenization, first-order
  correctors, a Liouville theorem and large-scale regularity above a single
  random radius whose tail has a stretched-exponential term and a rescaled copy
  of the source tail.
* `HCPoly.quenched_convergence` -- quenched convergence of the coarse-grained
  matrices: the estimate used in the proof of Theorem D in the subsection
  `ss.random.dirichlet`.  It is not one of the theorems of the introduction.

All five reduce to the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).
-/

open HCPolySupport MeasureTheory
open HCPolySupport.HighContrast

/-! ## Theorem A: polynomial entry into small contrast -/

/-- **Theorem A, `t.polynomial.entry`: polynomial entry into small contrast.**
Fix a dimension `d ≥ 2`, a coarse ellipticity exponent `g ∈ [0, 1)` and a
tolerance `σ ∈ (0, 1]`.  There is a constant `C`, depending on these three data
alone -- in particular independent of the reference block, of the coefficient
law, of the reference aspect ratio `e.reference.aspect.ratio` and of the growth
constant of the source tail -- such that for every stationary law of unit range
of dependence which is coarsely elliptic above its random source scale the
annealed contrast `e.Theta.m` is at most `1 + σ` at every generation beyond the
entry generation `⌈C log₃(2 + Π K)⌉` of `e.polynomial.entry`.  The length of that
entry generation is polynomial in the reference aspect ratio and in the growth
constant of the source tail.

No bound uniform as `g` increases to one is asserted. -/
theorem HCPoly.polynomial_entry (d : ℕ) (hd : 2 ≤ d) (g : ℝ)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (σ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P g E Ψ K S →
        (∀ m : ℤ, ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ≤ m →
            annealedContrast P m ≤ 1 + σ) ∧
          ∃ mEnt : ℕ,
            (mEnt : ℤ) = ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ∧
            (3 : ℝ) ^ (mEnt : ℕ) ≤ 3 * (2 + aspectRatio E * K) ^ C := by
  obtain ⟨C, hC, hbody⟩ := HCPolySupport.HighContrast.polynomial_entry d hd g hg σ hσ
  refine ⟨C, hC, ?_⟩
  intro P E Ψ K S hP hstat hrange hdagger
  refine ⟨hbody P E Ψ K S hP hstat hrange hdagger, ?_⟩
  exact HCPoly.Frozen.exists_entry_generation hC
    (HCPoly.Frozen.one_lt_two_add_aspectRatio_mul E hdagger.one_lt_growthWitness)

/-! ## Theorem B: algebraic convergence at a polynomial scale -/

/-- **Theorem B, `t.algebraic.convergence`: algebraic convergence at a
polynomial scale.**  Fix a dimension `d ≥ 2` and a coarse ellipticity exponent
`g ∈ [0, 1)`.  There are constants `C` and `κ`, depending on these two data
alone, such that every stationary law of unit range of dependence which is
coarsely elliptic above its random source scale admits a deterministic
generation `m₀` subject to the bound `e.algebraic.entry`, beyond which the
annealed contrast `e.Theta.m` decays geometrically at rate `κ`
(`e.algebraic.contrast.decay`), and a deterministic symmetric positive definite
limit block `Abar` which the annealed blocks of the centred cubes approach from
above in the Loewner order at the same rate, with the constant six of
`e.algebraic.block.decay`.

The Schur coefficients of the limit block, in the parametrization
`e.annealed.schur`, satisfy `s̄_* = s̄`, with `s̄` positive definite and `k̄`
antisymmetric; `ā = s̄ + k̄` is the coefficient matrix associated with the law.

The coefficient fields are locally uniformly elliptic almost everywhere, with
ellipticity constants belonging to the field and entering no estimate; the
paper's standing condition `e.qualitative.ellipticity` expresses this through
local essential bounds on the symmetric and skew parts, and every quantitative
object below is independent of the local ellipticity constants. -/
theorem HCPoly.algebraic_convergence (d : ℕ) (hd : 2 ≤ d) (g : ℝ)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P g E Ψ K S →
        ∃ (m₀ : ℕ) (Abar : BlockMat d),
          -- the entry generation, `e.algebraic.entry`
          (m₀ : ℤ) ≤ ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ∧
          -- the geometric decay of the contrast, `e.algebraic.contrast.decay`
          (∀ j : ℕ,
            annealedContrast P ((m₀ + j : ℕ) : ℤ) - 1 ≤
              (3 : ℝ) ^ (-κ * (j : ℝ))) ∧
          IsSymmetricBlockMat Abar ∧
          Book.Ch02.BlockPosDef Abar ∧
          -- the convergence of the annealed blocks, `e.algebraic.block.decay`
          (∀ j : ℕ,
            BlockMatLoewnerLE Abar
              (annealedBlock P (centeredCube d ((m₀ + j : ℕ) : ℤ))) ∧
            BlockMatLoewnerLE
              (annealedBlock P (centeredCube d ((m₀ + j : ℕ) : ℤ)))
              (blockScale (1 + 6 * (3 : ℝ) ^ (-κ * (j : ℝ))) Abar)) ∧
          -- the Schur coefficients of the limit, `e.annealed.schur`
          schurSigmaStar Abar = schurSigma Abar ∧
          (schurSigma Abar).PosDef ∧
          IsSkewMat (schurSkew Abar) :=
  Quenched.algebraic_convergence_assembly d hd g hg

/-! ## Theorem C: quantitative homogenization under uniform ellipticity -/

/-- **Theorem C, `t.uniform.homogenization`: quantitative homogenization under
uniform ellipticity.**  For a `ℤ^d`-stationary law of unit range whose fields
satisfy `e.uniform.ellipticity` with `0 < λ ≤ 1 ≤ Λ` there are a homogenized
matrix with positive definite symmetric part, a corrector family, and a
homogenization scale `X ≥ 1` whose tail is `e.uniform.scale.tail`: the exponent
is the dimension, and the deterministic factor in front of `t` is a power of
`2 + Λ/λ` with a dimensional exponent.  On one translation invariant event of
full probability the Dirichlet estimate and the large-scale energy estimate
`e.uniform.energy` hold. The Lean theorem also exports the corrector equation
and estimate, the Liouville classification and the first-order approximation
from its specialization of Theorem D; these are not clauses of the paper's
printed Theorem C.

This is the instance of Theorem D, `t.random.homogenization`, for uniformly
elliptic laws: the coarse ellipticity condition holds at the exponent `g = 0`
with a vanishing source scale and the reference block `diag(2Λ, 2λ⁻¹)`, whose
reference aspect ratio is at most `4Λ/λ`, so the two-part tail collapses to
`exp(-t^d)` and the length `(2 + Π K)^C` becomes `(2 + Λ/λ)^C`.

**Differences from the printed statement.**  The Dirichlet clause is the
homogeneous negative-Sobolev estimate of Theorem D on the adapted cells of the
homogenized matrix, not the `L²` estimate `e.uniform.dirichlet` with a forcing
term on the ellipsoids `e.homogenized.ellipsoids`; the paper deduces the latter
from the former by a separate duality argument, which is not formalized.  The
tolerance `δ` of that estimate is accordingly absent, and the endpoint constant
is the shape constant of Theorem D.  The large-scale energy estimate and the
first-order approximation are stated on the ellipsoids of
`e.homogenized.ellipsoids`, with the constant `C` of the tail; the other
differences listed for Theorem D apply unchanged. -/
theorem HCPoly.uniform_homogenization (d : ℕ) (hd : 2 ≤ d) :
    ∃ (κ C : ℝ) (C₀ : ℝ → ℝ → ℝ → ℝ) (C₁ : ℝ → ℝ),
      0 < κ ∧ 0 < C ∧ (∀ s₀ ρ Rad : ℝ, 0 < C₀ s₀ ρ Rad) ∧ (∀ ϑ : ℝ, 0 < C₁ ϑ) ∧
      ∀ lam Lam : ℝ, 0 < lam → lam ≤ 1 → 1 ≤ Lam →
        ∀ P : Measure (CoeffSpace d), IsProbabilityMeasure P →
          IsStationaryLaw P → IsUnitRangeLaw P →
          (∀ᵐ a ∂P, ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (a.1 x)) →
          ∃ (abar : Mat d) (X : CoeffSpace d → ℝ)
            (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
            (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
            Measurable X ∧
            (∀ a, 1 ≤ X a) ∧
            (∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
              gradPhi (c • e + e') a
                =ᵐ[volume] fun x => c • gradPhi e a x + gradPhi e' a x) ∧
            (∀ (z : Fin d → ℤ) (e : Vec d) (a : CoeffSpace d),
              gradPhi e (translateCoeff z a)
                =ᵐ[volume] fun x => gradPhi e a (x + Source.AKL.intTranslation z)) ∧
            (∀ t : ℝ, 1 ≤ t →
              P.real {a | C * (2 + Lam / lam) ^ C * t ≤ X a} ≤
                Real.exp (-(t ^ (d : ℝ)))) ∧
            (∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x)) ∧
            ∃ Ωend : Set (CoeffSpace d),
              MeasurableSet Ωend ∧
              P.real Ωend = 1 ∧
              (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Ωend = Ωend) ∧
              (∀ s₀ : ℝ, s₀ ∈ Set.Ico (1 / 4 : ℝ) (1 / 2 : ℝ) →
                  ∀ (ρ Rad : ℝ) (U : Set (Vec d)),
                    (∃ j : ℤ, ∃ z : Vec d,
                      U = (fun x : Vec d =>
                        z + matVecMul (matSqrt (symmPart abar)) x) ''
                          openCubeSet (originCube d j)) →
                    HasBallSandwich (matImage ((matSqrt (symmPart abar))⁻¹) U) ρ Rad →
                    U ⊆ ellipsoid abar 1 →
                    ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U →
                      ∀ a ∈ Ωend, ∀ ε : ℝ, 0 < ε → X a ≤ ε⁻¹ →
                        ∀ g₀ : H1Function U,
                          (∃ Lg : ℝ, ∀ᵐ x ∂volume.restrict U,
                            |g₀.toFun x| + Real.sqrt (vecNormSq (g₀.grad x)) ≤ Lg) →
                          hsNormSq U s₀ g₀.grad ≠ ⊤ →
                          ∀ h : H1Function U,
                            MemAffineH10 U g₀ h →
                            IsWeakSolutionOn (fun _ => abar) U h.grad →
                            ∀ (uFun : Vec d → ℝ) (uGrad : Vec d → Vec d),
                              MemH1a0 (scaledCoeff ε a) U
                                (fun x => uFun x - g₀.toFun x)
                                (fun x => uGrad x - g₀.grad x) →
                              IsWeakSolutionOn (scaledCoeff ε a) U uGrad →
                              negSobolevNorm U s₀
                                  (fun x => matVecMul (matSqrt (symmPart abar))
                                    (uGrad x - h.grad x)) +
                                negSobolevNorm U s₀
                                  (fun x => matVecMul (matSqrt (symmPart abar))⁻¹
                                    (matVecMul (scaledCoeff ε a x - skewPart abar)
                                        (uGrad x) -
                                      matVecMul (symmPart abar) (h.grad x))) ≤
                                ENNReal.ofReal (C₀ s₀ ρ Rad * (ε * X a) ^ κ) *
                                  hsNormSq U s₀
                                    (fun x => matVecMul (matSqrt (symmPart abar))
                                      (g₀.grad x)) ^ (1 / 2 : ℝ)) ∧
              (∀ a ∈ Ωend, ∀ e : Vec d,
                HasWeakGradientOn Set.univ (Phi e a) (gradPhi e a) ∧
                  IsWeakSolutionOn (fun x => a.1 x) Set.univ
                    (fun x => e + gradPhi e a x)) ∧
              (∀ a ∈ Ωend, ∀ e : Vec d, ∀ r : ℝ, X a ≤ r →
                ENNReal.ofReal r⁻¹ *
                    negOneNorm (ellipsoid abar r)
                      (fun x => matVecMul (matSqrt (symmPart abar)) (gradPhi e a x)) +
                  ENNReal.ofReal r⁻¹ *
                    negOneNorm (ellipsoid abar r)
                      (fun x => matVecMul (matSqrt (symmPart abar))⁻¹
                        (matVecMul (a.1 x - skewPart abar) (e + gradPhi e a x) -
                          matVecMul (symmPart abar) e)) ≤
                  ENNReal.ofReal
                    (C * Real.sqrt (vecDot e (matVecMul (symmPart abar) e)) *
                      (r / X a) ^ (-κ))) ∧
              (∀ a ∈ Ωend, ∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                (∀ (v : Vec d → ℝ) (Dv : Vec d → Vec d),
                  MemLiouvilleClass (fun x => a.1 x) ϑ v Dv →
                  ∃ (e : Vec d) (c : ℝ),
                    v =ᵐ[volume] fun x => vecDot e x + Phi e a x + c) ∧
                (∀ (e : Vec d) (c : ℝ),
                  MemLiouvilleClass (fun x => a.1 x) ϑ
                    (fun x => vecDot e x + Phi e a x + c)
                    (fun x => e + gradPhi e a x))) ∧
              (∀ a ∈ Ωend, ∀ R : ℝ, X a ≤ R →
                ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
                  MemH1a (fun x => a.1 x) (ellipsoid abar R) u Du →
                  IsWeakSolutionOn (fun x => a.1 x) (ellipsoid abar R) Du →
                  (∀ r : ℝ, r ∈ Set.Icc (X a) R →
                    weightedGradNorm (fun x => a.1 x) (ellipsoid abar r) Du ≤
                      ENNReal.ofReal C *
                        weightedGradNorm (fun x => a.1 x) (ellipsoid abar R) Du) ∧
                  (∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                    ∃ e : Vec d, ∀ r : ℝ, r ∈ Set.Icc (X a) R →
                      weightedGradNorm (fun x => a.1 x) (ellipsoid abar r)
                          (fun x => Du x - (e + gradPhi e a x)) ≤
                        ENNReal.ofReal (C₁ ϑ * (r / R) ^ ϑ) *
                          weightedGradNorm (fun x => a.1 x) (ellipsoid abar R) Du)) :=
  uniform_homogenization_of_polynomial_homogenization d hd

/-! ## Theorem D: homogenization with a random source scale -/

/-- **Theorem D, `t.random.homogenization`: homogenization with a random source
scale.**  Under the standing assumptions there are a homogenized matrix with
positive definite symmetric part, a length bounded by a power of `2 + Π K`, and
a measurable random radius whose tail is the two-part bound
`e.random.scale.tail`, together with a slope-linear family of stationary
corrector gradients, such that almost surely and simultaneously: the Dirichlet
estimate `e.random.dirichlet` holds for every microscale below the radius; the
correctors solve the corrector equation and obey `e.random.corrector`; the
entire solutions of the growth condition `e.random.liouville.growth` are exactly
the affine functions corrected by the family; and the large-scale energy and
excess-decay estimates `e.random.energy` and `e.random.regularity` hold above
the radius.

**The coefficient class.**  The coefficient fields are locally uniformly
elliptic almost everywhere, with ellipticity constants belonging to the field
and entering no estimate below; the paper's standing condition
`e.qualitative.ellipticity` expresses this through local essential bounds on
the symmetric and skew parts.  Every quantitative object below -- the
reference aspect ratio, the gauge and its growth witness, the homogenized
matrix, the length and its tail, and every dimensional constant and exponent --
is independent of those constants.

**Differences from the printed statement.**

* The random radius satisfies `1 ≤ X`, where the paper states
  `X ≥ max {1, S}`.
* The homogenized matrix is produced existentially, rather than identified with
  the matrix of Theorem B, `t.algebraic.convergence`.
* The domains carrying the Dirichlet estimate are the adapted cells of the
  homogenized matrix -- translates of the image of a centred triadic cube under
  the symmetric square root of its symmetric part -- normalized to sit between
  two concentric adapted ellipsoids, rather than the bounded Lipschitz domains
  of the paper.  Every domain the development uses is such a cell; the
  normalization fixes the size of the domain relative to the homogenized matrix,
  which is the scale the endpoint constant would otherwise have to carry, and it
  is satisfiable at every dimension because the window between the two
  ellipsoids has triadic ratio three.
* The two flux differences -- in the Dirichlet estimate and in the corrector
  estimate -- are written for the skew-centered field: the constant skew part of
  the homogenized matrix is subtracted from the coefficient field, and the
  homogenized matrix enters through its symmetric part.  This is the standing
  convention under which a coefficient field and its antisymmetric part are read
  modulo a constant antisymmetric matrix; it is the form the argument
  establishes, a constant skew part changing neither the solutions nor the
  coarse-grained blocks, and it is the form invariant under that recentering,
  which the displays written with the full homogenized matrix are not.
* All norms and energies are valued in `ℝ≥0∞`, so that each estimate is an
  assertion about the quantity the paper writes rather than about a totalized
  integral that vanishes when that quantity is infinite.
* The endpoint constant of the Dirichlet estimate depends on nothing but the
  dimension, the regularity exponent and the shape of the adapted domain -- the
  radii of concentric balls trapping it -- so its binder stands outside the
  exponent and outside the law.  The two radii enter only through their ratio:
  dilating the coefficient field and the homogenized matrix together leaves the
  condition on the domain fixed, slides both radii along a common ray, and
  multiplies both sides of the estimate by the same factor.
* The constants `C`, `C₀` and `C₁` are asserted positive, where the paper
  asserts only their finiteness; positivity is a normalization, every occurrence
  of each being weakened by increasing it.
* The three membership classes carry the measurability of the function and of
  its gradient field that their printed counterparts -- completions of smooth
  functions in a norm -- presuppose.  The second inclusion of the Liouville
  clause is the only place this statement says anything about the measurability
  of the corrector family, and it is what puts the correctors in the local
  class.
* The coefficient-weighted spaces are closures under globally smooth
  approximants, where the paper closes the functions smooth on the domain.  On a
  bounded convex domain a function smooth on the domain agrees, after a dilation
  towards an interior point, with a globally smooth function on the whole
  closure, so the two readings are separated only by the continuity of that
  dilation in the norm.
* The invariance of the full-probability event under integer translations is
  carried in the conclusion; the paper does not state it. -/
theorem HCPoly.polynomial_homogenization (d : ℕ) (hd : 2 ≤ d) :
    ∃ (cd : ℝ) (C₀ : ℝ → ℝ → ℝ → ℝ), 0 < cd ∧
      (∀ s₀ ρ Rad : ℝ, 0 < C₀ s₀ ρ Rad) ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ (C cSrc κ : ℝ) (C₁ : ℝ → ℝ),
          0 < C ∧ 0 < cSrc ∧ 0 < κ ∧ (∀ ϑ : ℝ, 0 < C₁ ϑ) ∧
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (S : CoeffSpace d → ℝ),
            IsProbabilityMeasure P →
            IsStationaryLaw P →
            IsUnitRangeLaw P →
            CoarseEllipticityDagger P g E Ψ K S →
            ∃ (abar : Mat d) (Lpoly : ℝ) (X : CoeffSpace d → ℝ)
              (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
              (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
              1 ≤ Lpoly ∧
              Measurable X ∧
              (∀ a, 1 ≤ X a) ∧
              -- the family is linear in the slope
              (∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
                gradPhi (c • e + e') a
                  =ᵐ[volume] fun x => c • gradPhi e a x + gradPhi e' a x) ∧
              -- and stationary under integer translations
              (∀ (z : Fin d → ℤ) (e : Vec d) (a : CoeffSpace d),
                gradPhi e (translateCoeff z a)
                  =ᵐ[volume] fun x =>
                    gradPhi e a (x + Source.AKL.intTranslation z)) ∧
              -- the polynomial length of `e.random.scale.tail`
              Lpoly ≤ (2 + aspectRatio E * K) ^ C ∧
              -- and its two-part tail `e.random.scale.tail`
              (∀ t : ℝ, 1 ≤ t →
                P.real {a | C * Lpoly * t ≤ X a} ≤
                  Real.exp (-cd * t ^ ((d : ℝ) - 2 * g)) + (Ψ (cSrc * t))⁻¹) ∧
              -- the symmetric part of the homogenized matrix is positive definite
              (∀ x : Vec d, x ≠ 0 →
                0 < vecDot x (matVecMul (symmPart abar) x)) ∧
              ∃ Ωend : Set (CoeffSpace d),
                MeasurableSet Ωend ∧
                P.real Ωend = 1 ∧
                (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Ωend = Ωend) ∧
                -- (1) Dirichlet homogenization, `e.random.dirichlet`
                (∀ s₀ : ℝ, s₀ ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ) →
                    ∀ (ρ Rad : ℝ) (U : Set (Vec d)),
                      (∃ j : ℤ, ∃ z : Vec d,
                        U = (fun x : Vec d =>
                          z + matVecMul (matSqrt (symmPart abar)) x) ''
                            openCubeSet (originCube d j)) →
                      HasBallSandwich
                        (matImage ((matSqrt (symmPart abar))⁻¹) U) ρ Rad →
                      U ⊆ ellipsoid abar 1 →
                      ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U →
                        ∀ a ∈ Ωend, ∀ ε : ℝ, 0 < ε → X a ≤ ε⁻¹ →
                          ∀ g₀ : H1Function U,
                            (∃ Lg : ℝ, ∀ᵐ x ∂volume.restrict U,
                              |g₀.toFun x| +
                                Real.sqrt (vecNormSq (g₀.grad x)) ≤ Lg) →
                            hsNormSq U s₀ g₀.grad ≠ ⊤ →
                            ∀ h : H1Function U,
                              MemAffineH10 U g₀ h →
                              IsWeakSolutionOn (fun _ => abar) U h.grad →
                              ∀ (uFun : Vec d → ℝ) (uGrad : Vec d → Vec d),
                                MemH1a0 (scaledCoeff ε a) U
                                  (fun x => uFun x - g₀.toFun x)
                                  (fun x => uGrad x - g₀.grad x) →
                                IsWeakSolutionOn (scaledCoeff ε a) U uGrad →
                                negSobolevNorm U s₀
                                    (fun x => matVecMul (matSqrt (symmPart abar))
                                      (uGrad x - h.grad x)) +
                                  negSobolevNorm U s₀
                                    (fun x => matVecMul (matSqrt (symmPart abar))⁻¹
                                      (matVecMul (scaledCoeff ε a x - skewPart abar)
                                          (uGrad x) -
                                        matVecMul (symmPart abar) (h.grad x))) ≤
                                  ENNReal.ofReal (C₀ s₀ ρ Rad * (ε * X a) ^ κ) *
                                    hsNormSq U s₀
                                        (fun x => matVecMul
                                          (matSqrt (symmPart abar)) (g₀.grad x)) ^
                                      (1 / 2 : ℝ)) ∧
                -- (2a) the corrector equation of `e.random.corrector`
                (∀ a ∈ Ωend, ∀ e : Vec d,
                  HasWeakGradientOn Set.univ (Phi e a) (gradPhi e a) ∧
                    IsWeakSolutionOn (fun x => a.1 x) Set.univ
                      (fun x => e + gradPhi e a x)) ∧
                -- (2b) the corrector estimate `e.random.corrector`, with the
                -- inverse-radius factor written on each summand rather than
                -- absorbed into the constant
                (∀ a ∈ Ωend, ∀ e : Vec d, ∀ r : ℝ, X a ≤ r →
                  ENNReal.ofReal r⁻¹ *
                      negOneNorm (ellipsoid abar r)
                        (fun x => matVecMul (matSqrt (symmPart abar))
                          (gradPhi e a x)) +
                    ENNReal.ofReal r⁻¹ *
                      negOneNorm (ellipsoid abar r)
                        (fun x => matVecMul (matSqrt (symmPart abar))⁻¹
                          (matVecMul (a.1 x - skewPart abar)
                              (e + gradPhi e a x) -
                            matVecMul (symmPart abar) e)) ≤
                    ENNReal.ofReal
                      (C * Real.sqrt (vecDot e (matVecMul (symmPart abar) e)) *
                        (r / X a) ^ (-κ))) ∧
                -- (3) the Liouville classification for the growth condition
                -- `e.random.liouville.growth`, as a double inclusion
                (∀ a ∈ Ωend, ∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                  (∀ (v : Vec d → ℝ) (Dv : Vec d → Vec d),
                    MemLiouvilleClass (fun x => a.1 x) ϑ v Dv →
                    ∃ (e : Vec d) (c : ℝ),
                      v =ᵐ[volume] fun x => vecDot e x + Phi e a x + c) ∧
                  (∀ (e : Vec d) (c : ℝ),
                    MemLiouvilleClass (fun x => a.1 x) ϑ
                      (fun x => vecDot e x + Phi e a x + c)
                      (fun x => e + gradPhi e a x))) ∧
                -- (4) the large-scale energy estimate `e.random.energy` and
                -- (5) the large-scale regularity estimate `e.random.regularity`
                (∀ a ∈ Ωend, ∀ R : ℝ, X a ≤ R →
                  ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
                    MemH1a (fun x => a.1 x) (ellipsoid abar R) u Du →
                    IsWeakSolutionOn (fun x => a.1 x) (ellipsoid abar R) Du →
                    (∀ r : ℝ, r ∈ Set.Icc (X a) R →
                      weightedGradNorm (fun x => a.1 x) (ellipsoid abar r) Du ≤
                        ENNReal.ofReal C *
                          weightedGradNorm (fun x => a.1 x)
                            (ellipsoid abar R) Du) ∧
                    (∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                      ∃ e : Vec d, ∀ r : ℝ, r ∈ Set.Icc (X a) R →
                        weightedGradNorm (fun x => a.1 x) (ellipsoid abar r)
                            (fun x => Du x - (e + gradPhi e a x)) ≤
                          ENNReal.ofReal (C₁ ϑ * (r / R) ^ ϑ) *
                            weightedGradNorm (fun x => a.1 x)
                              (ellipsoid abar R) Du)) :=
  HCPoly.Frozen.polynomial_homogenization_random_source d hd

/-! ## Quenched convergence of the coarse-grained matrices -/

/-- **Quenched convergence of the coarse-grained matrices.**  The estimate the
proof of Theorem D uses in the subsection `ss.random.dirichlet`; it is not one
of the theorems of the introduction.

There are a deterministic symmetric positive definite limit block pinning the
annealed blocks of the centred cubes from both sides, a length bounded by a
power of `2 + Π K`, and a measurable random scale whose tail is the two-part
bound `e.random.scale.tail`, such that on one translation-invariant event of
full probability the weighted sum over depths of the largest normalized excess
of a coarse-grained block over the limit block, taken over the cells of that
depth inside the outer cube and restricted to the event that the source has
burned at the outer scale, decays algebraically in the ratio of the outer scale
to the random scale, below any prescribed tolerance.

The coefficient fields are locally uniformly elliptic almost everywhere, with
ellipticity constants belonging to the field and entering no estimate; the
paper's standing condition `e.qualitative.ellipticity` expresses this through
local essential bounds on the symmetric and skew parts, and every
quantitative object below -- the reference aspect ratio, the gauge and its
growth witness, the limit block, the length, the tail, and every dimensional
constant -- is independent of those constants. -/
theorem HCPoly.quenched_convergence (d : ℕ) (hd : 2 ≤ d) :
    ∃ cd : ℝ, 0 < cd ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ C κ cSrc : ℝ, 1 < C ∧ 0 < κ ∧ 0 < cSrc ∧
          ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) 1 →
            ∃ Cδ : ℝ, 1 ≤ Cδ ∧
              ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ)
                (K : ℝ) (S : CoeffSpace d → ℝ),
                IsProbabilityMeasure P →
                IsStationaryLaw P →
                IsUnitRangeLaw P →
                CoarseEllipticityDagger P g E Ψ K S →
                ∃ (Abar : BlockMat d) (Lpoly : ℝ) (X : CoeffSpace d → ℝ),
                  IsSymmetricBlockMat Abar ∧
                  Book.Ch02.BlockPosDef Abar ∧
                  (∀ m : ℕ,
                    BlockMatLoewnerLE Abar
                      (annealedBlock P (centeredCube d (m : ℤ)))) ∧
                  (∀ m : ℕ,
                    BlockMatLoewnerLE
                      (blockSharp (annealedBlock P (centeredCube d (m : ℤ))))
                      Abar) ∧
                  1 ≤ Lpoly ∧
                  Lpoly ≤ (2 + aspectRatio E * K) ^ Cδ ∧
                  Measurable X ∧
                  (∀ a, 1 ≤ X a) ∧
                  (∀ t : ℝ, 1 ≤ t →
                    P.real {a | C * Lpoly * t ≤ X a} ≤
                      Real.exp (-cd * t ^ ((d : ℝ) - 2 * g)) +
                        (Ψ (cSrc * t))⁻¹) ∧
                  ∃ Ωend : Set (CoeffSpace d),
                    MeasurableSet Ωend ∧
                    P.real Ωend = 1 ∧
                    (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Ωend = Ωend) ∧
                    ∀ a ∈ Ωend, ∀ m : ℤ, X a ≤ (3 : ℝ) ^ m →
                      (if S a ≤ (3 : ℝ) ^ m then
                          ∑' n : ℕ, (3 : ℝ) ^ (-((1 + 3 * g) / 4) * (n : ℝ)) *
                            sSup {r : ℝ | ∃ w : Fin d → ℤ,
                              standardCellCenter (m - (n : ℤ)) w ∈
                                centeredCube d m ∧
                              r =
                                blockExcess
                                  (coarseBlock
                                    (standardCell d (m - (n : ℤ)) w) a)
                                  Abar}
                        else 0) ≤ δ * ((3 : ℝ) ^ m / X a) ^ (-κ) :=
  HCPoly.Frozen.quenched_convergence_random_source d hd
