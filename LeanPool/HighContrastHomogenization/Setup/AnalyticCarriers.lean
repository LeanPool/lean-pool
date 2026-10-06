/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.Definitions
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# High-contrast homogenization: Setup.AnalyticCarriers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Analytic carriers for the homogenization theorem

The volume-normalized and coefficient-weighted spaces of `s.introduction`,
the weak equation, the Liouville class, and the domain data carried by the
Dirichlet estimate of `t.random.homogenization`.

This module carries definitions only.  Every norm and energy is valued in
`ℝ≥0∞`: the integrands are nonnegative, so the Lebesgue integral is defined for
every argument and is infinite exactly where the quantity the reference text
writes is infinite, whereas a totalized Bochner integral would return zero there
and let an estimate be satisfied by the failure of the membership it
presupposes.  The two dual norms and the weak equation carry the absolute
convergence of their pairings for the same reason: it is the well-formedness of
a printed distributional display, not an additional claim.  The membership
classes carry the measurability of their pairs, which their printed
counterparts — completions of smooth functions in a norm — presuppose.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-! ## Elementary geometry and pointwise operations -/

/-- The open Euclidean ball of radius `r` centered at `c`.  The ambient norm of
`Vec d` is the supremum norm, so the Euclidean radius is written through
`vecNormSq`. -/
@[expose]
def euclideanBallAt (c : Vec d) (r : ℝ) : Set (Vec d) :=
  {x | vecNormSq (x - c) < r ^ 2}

/-- The open Euclidean ball `B_r` centered at the origin. -/
@[expose]
def euclideanBall (d : ℕ) (r : ℝ) : Set (Vec d) :=
  euclideanBallAt (0 : Vec d) r

/-- The coordinate gradient of a smooth scalar function, through `fderiv`. -/
@[expose]
def smoothGrad (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => fderiv ℝ f x (basisVec i)

/-- The rescaled sample coefficient `a^ε(x) = a(x/ε)`. -/
@[expose]
def scaledCoeff (ε : ℝ) (a : CoeffSpace d) : CoeffField d :=
  fun x => a.1 (ε⁻¹ • x)

/-- A vector-valued test function on `U`: smooth, compactly supported inside
`U`. -/
structure IsLocalVecTest (U : Set (Vec d)) (ψ : Vec d → Vec d) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) ψ
  hasCompactSupport : HasCompactSupport ψ
  tsupport_subset : tsupport ψ ⊆ U

/-! ## Normalized norms (the volume-normalized function spaces)

All norms and energies below are valued in `ℝ≥0∞`.  Their integrands are
nonnegative, so the Lebesgue integral is defined for every argument and takes
the value `∞` exactly when the quantity the reference text writes is infinite;
a Bochner integral would instead return `0` there, which would make each
estimate satisfiable by the failure of the very membership it presupposes. -/

/-- The volume-normalized integral `⨍_V f` of a nonnegative quantity. -/
@[expose]
def eVolumeAverage (V : Set (Vec d)) (f : Vec d → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ x in V, f x ∂volume) / volume V

/-- The normalized norm `‖v‖_{L̲²(V)}` (the volume-normalized L^p norm at `p = 2`). -/
@[expose]
def normalizedL2Norm (V : Set (Vec d)) (v : Vec d → ℝ) : ℝ≥0∞ :=
  (eVolumeAverage V fun x => ENNReal.ofReal (v x ^ 2)) ^ (1 / 2 : ℝ)

/-- The value `‖s^{1/2} F‖_{L̲²(V)}` for the symmetric part `s` of a coefficient
field, written through the quadratic form (an exact identity, not a
re-encoding). -/
@[expose]
def weightedGradNorm (b : CoeffField d) (V : Set (Vec d)) (F : Vec d → Vec d) :
    ℝ≥0∞ :=
  (eVolumeAverage V fun x =>
    ENNReal.ofReal (vecDot (F x) (matVecMul (symmPart (b x)) (F x)))) ^ (1 / 2 : ℝ)

/-- The Gagliardo double-integral seminorm square of a vector field
(`e.physical.fractional.norm`), with Euclidean distances. -/
@[expose]
def fracSeminormSq (V : Set (Vec d)) (s : ℝ) (F : Vec d → Vec d) : ℝ≥0∞ :=
  eVolumeAverage V fun x =>
    ∫⁻ y in V, ENNReal.ofReal
      (vecNormSq (F x - F y) /
        Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume

/-- The volume-normalized `H^s(V)` norm square of a vector field
(`e.physical.fractional.norm`). -/
@[expose]
def hsNormSq (V : Set (Vec d)) (s : ℝ) (F : Vec d → Vec d) : ℝ≥0∞ :=
  volume V ^ (-(2 * s) / (d : ℝ)) *
      eVolumeAverage V (fun x => ENNReal.ofReal (vecNormSq (F x))) +
    fracSeminormSq V s F

/-- The volume-normalized `H¹(V)` norm square of a smooth vector test function
(the `s = 1` display of the volume-normalized function spaces), with componentwise
gradients. -/
@[expose]
def h1NormSq (V : Set (Vec d)) (ψ : Vec d → Vec d) : ℝ≥0∞ :=
  volume V ^ (-(2 : ℝ) / (d : ℝ)) *
      eVolumeAverage V (fun x => ENNReal.ofReal (vecNormSq (ψ x))) +
    eVolumeAverage V fun x =>
      ENNReal.ofReal (∑ j, vecNormSq (smoothGrad (fun y => ψ y j) x))

/-- The normalized pairing `⨍_V F · ψ` of a vector field against a test field,
valued in `ℝ≥0∞`.  A pairing that is not absolutely convergent is `∞`: the
reference text reads the pairing of a locally integrable field against a smooth
compactly supported test, and a totalized Bochner integral would silently value
a divergent pairing at `0`, dropping that test from the supremum below. -/
@[expose]
def dualPairing (V : Set (Vec d)) (F ψ : Vec d → Vec d) : ℝ≥0∞ :=
  if IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume then
    ENNReal.ofReal (volumeAverage V fun x => vecDot (F x) (ψ x))
  else ⊤

/-- The dual norm `‖F‖_{H^{-s}(V)}` (`e.physical.negative.norm`). -/
@[expose]
def negSobolevNorm (V : Set (Vec d)) (s : ℝ) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ⨆ ψ : {ψ : Vec d → Vec d // IsLocalVecTest V ψ ∧ hsNormSq V s ψ ≤ 1},
    dualPairing V F ψ.1

/-- The dual norm `‖F‖_{H̲^{-1}(V)}` (the `s = 1` display of
the volume-normalized function spaces). -/
@[expose]
def negOneNorm (V : Set (Vec d)) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ⨆ ψ : {ψ : Vec d → Vec d // IsLocalVecTest V ψ ∧ h1NormSq V ψ ≤ 1},
    dualPairing V F ψ.1

/-! ## Coefficient-weighted Sobolev classes
(the coefficient Sobolev space) -/

/-- The `s`-weighted Dirichlet energy `∫_V F · s F`. -/
@[expose]
def sEnergyOn (b : CoeffField d) (V : Set (Vec d)) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ∫⁻ x in V, ENNReal.ofReal (vecDot (F x) (matVecMul (symmPart (b x)) (F x)))
    ∂volume

/-- The `H¹_s(V)` norm square `‖u‖_{L¹(V)}² + ∫_V ∇u · s ∇u`. -/
@[expose]
def h1sNormSqOn (b : CoeffField d) (V : Set (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) : ℝ≥0∞ :=
  (∫⁻ x in V, ENNReal.ofReal |u x| ∂volume) ^ 2 + sEnergyOn b V Du

/-- The pairing `∫_V ∇φ · k F` of the skew flux against a test gradient, valued
in `ℝ≥0∞` and infinite on a pairing that is not absolutely convergent. -/
@[expose]
def skewFluxPairing (b : CoeffField d) (V : Set (Vec d)) (F : Vec d → Vec d)
    (φ : Vec d → ℝ) : ℝ≥0∞ :=
  if IntegrableOn
      (fun x => vecDot (smoothGrad φ x) (matVecMul (skewPart (b x)) (F x))) V
      volume then
    ENNReal.ofReal
      (∫ x in V, vecDot (smoothGrad φ x) (matVecMul (skewPart (b x)) (F x))
        ∂volume)
  else ⊤

/-- The `H^{-1}_s(V)` norm of the skew flux divergence `∇·(k F)`, through smooth
compactly supported tests of unit `H¹_s` norm. -/
@[expose]
def skewFluxDualNorm (b : CoeffField d) (V : Set (Vec d)) (F : Vec d → Vec d) :
    ℝ≥0∞ :=
  ⨆ φ : {φ : Vec d → ℝ //
      IsLocalTest V φ ∧ h1sNormSqOn b V φ (smoothGrad φ) ≤ 1},
    skewFluxPairing b V F φ.1

/-- A function and a candidate gradient field for it, both measurable.

The reference text's coefficient-weighted spaces are completions of smooth
functions in a norm, so each of their elements is an equivalence class of
measurable functions carrying a measurable gradient field; the classes below
record that.  The condition is what makes the relation tying a function to its
weak gradient an identity between convergent integrals: with it, and with the
coefficient field elliptic almost everywhere, both pairings of that relation
converge absolutely.  Without it the relation compares two integrals that may
each fail to converge, and a pair on which they both fail satisfies it for no
reason; whether the wider class actually contains such a pair is a question
about sets of inner measure zero, and is not settled here.

The condition is faithful in both directions.  Where a membership class stands
as a hypothesis, the narrower class makes the statement assert less; where it
stands as a conclusion, as in the second inclusion of the Liouville clause, the
narrower class makes it assert more, and that inclusion is the only place the
measurability of the corrector family is asserted at all. -/
@[expose]
def IsMeasurableGradientPair (μ : Measure (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) : Prop :=
  AEStronglyMeasurable u μ ∧ ∀ i, AEStronglyMeasurable (fun x => Du x i) μ

/-- Membership in `H¹_a(V)`: a weak-gradient pair approximated by globally
smooth functions in the `H¹_a` norm (`H¹_s` part and skew-flux dual part). -/
@[expose]
def MemH1a (b : CoeffField d) (V : Set (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) : Prop :=
  IsMeasurableGradientPair (volume.restrict V) u Du ∧
    HasWeakGradientOn V u Du ∧
    ∃ v : ℕ → Vec d → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n)) ∧
      Filter.Tendsto
        (fun n => h1sNormSqOn b V (fun x => v n x - u x)
          (fun x => smoothGrad (v n) x - Du x)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun n => skewFluxDualNorm b V (fun x => smoothGrad (v n) x - Du x))
        Filter.atTop (nhds 0)

/-- Membership in `H¹_{a,0}(V)`: as `MemH1a`, with the approximants compactly
supported inside `V`. -/
@[expose]
def MemH1a0 (b : CoeffField d) (V : Set (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) : Prop :=
  IsMeasurableGradientPair (volume.restrict V) u Du ∧
    HasWeakGradientOn V u Du ∧
    ∃ v : ℕ → Vec d → ℝ,
      (∀ n, IsLocalTest V (v n)) ∧
      Filter.Tendsto
        (fun n => h1sNormSqOn b V (fun x => v n x - u x)
          (fun x => smoothGrad (v n) x - Du x)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun n => skewFluxDualNorm b V (fun x => smoothGrad (v n) x - Du x))
        Filter.atTop (nhds 0)

/-- Membership in `H¹_{s,loc}(ℝ^d)`: on every centered Euclidean ball, a
weak-gradient pair approximated by smooth functions in the `H¹_s` norm. -/
@[expose]
def MemH1sLoc (b : CoeffField d) (v : Vec d → ℝ) (Dv : Vec d → Vec d) : Prop :=
  IsMeasurableGradientPair volume v Dv ∧
    ∀ R : ℝ, 0 < R →
      HasWeakGradientOn (euclideanBall d R) v Dv ∧
        ∃ w : ℕ → Vec d → ℝ,
          (∀ n, ContDiff ℝ (⊤ : ℕ∞) (w n)) ∧
          Filter.Tendsto
            (fun n => h1sNormSqOn b (euclideanBall d R) (fun x => w n x - v x)
              (fun x => smoothGrad (w n) x - Dv x)) Filter.atTop (nhds 0)

/-! ## Weak solutions and the Liouville class -/

/-- The weak interior equation `-∇·(b F) = 0` in `V`: against every smooth
compactly supported test the flux pairing is absolutely convergent and
vanishes.  Absolute convergence is the well-formedness of the printed
distributional display, and it is what keeps the equation from holding by the
failure of the pairing. -/
@[expose]
def IsWeakSolutionOn (b : CoeffField d) (V : Set (Vec d))
    (F : Vec d → Vec d) : Prop :=
  ∀ φ : Vec d → ℝ, IsLocalTest V φ →
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (F x))) V
        volume ∧
      ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (b x) (F x)) ∂volume = 0

/-- The Liouville class `𝒜_{1,ϑ}(ℝ^d)` of
`e.random.liouville.growth`.  The growth
condition is the vanishing-limit form of the `limsup` display, equivalent for
the nonnegative normalized averages. -/
@[expose]
def MemLiouvilleClass (b : CoeffField d) (ϑ : ℝ) (v : Vec d → ℝ)
    (Dv : Vec d → Vec d) : Prop :=
  MemH1sLoc b v Dv ∧
    IsWeakSolutionOn b Set.univ Dv ∧
      Filter.Tendsto
        (fun r : ℝ =>
          ENNReal.ofReal (r ^ (-(1 + ϑ))) * normalizedL2Norm (euclideanBall d r) v)
        Filter.atTop (nhds 0)

/-- Membership of `h` in the affine class `g₀ + H¹₀(U)`, through an
`H10Function` witness matching function and gradient a.e. on `U`. -/
@[expose]
def MemAffineH10 (U : Set (Vec d)) (g₀ h : H1Function U) : Prop :=
  ∃ w : H10Function U,
    (w.toH1Function.toFun =ᵐ[volume.restrict U]
      fun x => h.toFun x - g₀.toFun x) ∧
    (w.toH1Function.grad =ᵐ[volume.restrict U]
      fun x => h.grad x - g₀.grad x)

/-! ## Domains and their shape data

The domains carrying the Dirichlet estimate are the bounded convex domains of
`IsOpenBoundedConvexDomain`, the domain class of the coarse-graining library.
The geometric datum through which the endpoint constant is allowed to depend on
the domain is the concentric ball sandwich of the adapted domain: an inner
radius and an outer radius.  For a convex body this pair plays exactly the role
that the Lipschitz character plays for a Lipschitz domain — it controls the
trace, extension and fractional Poincaré constants — and it is the convex
reading of the domain dependence recorded at
`e.random.dirichlet`. -/

/-- The image of a set under a linear map, used for the adapted domain
`s̄^{-1/2}U` whose shape governs the endpoint constant. -/
@[expose]
def matImage (M : Mat d) (U : Set (Vec d)) : Set (Vec d) :=
  matVecMul M '' U

/-- `U` contains, and is contained in, concentric Euclidean balls of radii `ρ`
and `Rad`.  The pair `(ρ, Rad)` is the shape datum of a convex domain: an
estimate whose constant depends on the domain only through `(ρ, Rad)` is
uniform over every domain admitting that sandwich.  The radii are signed
constraints on the shape, so their sign is fixed here: a ball is read through
the square of its radius, and without the sign conditions the same domain would
be indexed by both a radius and its negative. -/
@[expose]
def HasBallSandwich (U : Set (Vec d)) (ρ Rad : ℝ) : Prop :=
  0 < ρ ∧ 0 ≤ Rad ∧
    ∃ c : Vec d, euclideanBallAt c ρ ⊆ U ∧ U ⊆ euclideanBallAt c Rad

end

end HighContrast
end HCPolySupport
