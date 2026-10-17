/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.NormalizedL2
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import LeanPool.HighContrastHomogenization.Support.Ambient.CoefficientFieldHilbert
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.Cutoff.Euclidean

/-!
# Carrier

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Carriers for the small-contrast Schauder estimate

The analytic core is stated on the explicit Euclidean balls
`Homogenization.euclideanBall`.  This choice is substantive: normalized
Dirichlet energy of a harmonic function is monotone on concentric Euclidean
balls, giving the coefficient `1` in the contraction.  Replacing the balls by
sup-norm cubes at this point would spend a dimension factor before the
perturbative term and destroy the contraction as `alpha` tends to one.

The eventual coefficient-sigma-field consumer uses scalar coefficients on
cubes.  It is reached by a separate scalar and ball/cube wrapper; the theorem
family here keeps the source's matrix-valued coefficient and ball geometry.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- The normalized Euclidean `L²` seminorm of a vector field. -/
def vectorNormalizedL2On (W : Set (Vec d)) (f : Vec d → Vec d) : ℝ :=
  normalizedL2On W (fun x => HCPolySupport.euclideanNorm (f x))

/-- The paper-side unit-coefficient weak harmonicity predicate. -/
abbrev IsUnitWeaklyHarmonicOn (W : Set (Vec d)) (u : H1Function W) : Prop :=
  IsWeaklyHarmonicOn W u

/-- The source's `L^infinity` distance of the coefficient from the identity,
written as an a.e. operator-norm bound. -/
def CoefficientIdentityDistanceLE (W : Set (Vec d)) (a : CoeffField d)
    (delta : ℝ) : Prop :=
  ∀ᵐ x ∂volume.restrict W,
    ‖HilbertVec.applyMat (a x - (1 : Mat d))‖ ≤ delta

/-- The real-valued Euclidean `L^p` size of a vector field. -/
def vectorLpSizeOn (W : Set (Vec d)) (p : ℝ) (f : Vec d → Vec d) : ℝ :=
  (eLpNorm (fun x => euclideanNorm (f x)) (ENNReal.ofReal p)
    (volume.restrict W)).toReal

/-- Membership in the vector `L^p` carrier used by the source. -/
def MemVectorLpOn (W : Set (Vec d)) (p : ℝ) (f : Vec d → Vec d) : Prop :=
  MemLp (fun x => HilbertVec.ofVec (f x)) (ENNReal.ofReal p)
    (volume.restrict W)

/-- Euclidean Hölder control of a scalar representative. -/
def EuclideanHolderBoundOn (W : Set (Vec d)) (alpha K : ℝ)
    (v : Vec d → ℝ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W,
    |v x - v y| ≤ K * euclideanNorm (x - y) ^ alpha

/-- The source exponent `p = d/(1-alpha)`. -/
def schauderSourceExponent (d : ℕ) (alpha : ℝ) : ℝ :=
  (d : ℝ) / (1 - alpha)

/-- The unit Euclidean ball in the project carrier. -/
def smallContrastUnitBall (d : ℕ) : Set (Vec d) :=
  euclideanBall 0 1

/-- The concentric Euclidean ball of radius `r`. -/
def smallContrastBall (d : ℕ) (r : ℝ) : Set (Vec d) :=
  euclideanBall 0 r

/-- The right-hand side of the Schauder estimate, with the sole
`(1-alpha)^{-1}` price exposed. -/
def smallContrastDataSize (d : ℕ) (alpha : ℝ)
    (u : H1Function (smallContrastUnitBall d)) (f : Vec d → Vec d) : ℝ :=
  vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad +
    (1 - alpha)⁻¹ *
      vectorLpSizeOn (smallContrastUnitBall d) (schauderSourceExponent d alpha) f

/-- Scale-invariant gradient control on every concentric sub-ball. -/
def HasSmallContrastGradientScaleBound (alpha K : ℝ)
    (u : H1Function (smallContrastUnitBall d)) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 →
    r ^ (1 - alpha) * vectorNormalizedL2On (smallContrastBall d r) u.grad ≤ K

/-- Quotient-safe conclusion of the small-contrast Schauder theorem.  The
continuous representative is explicit, preventing any pointwise claim about
the arbitrary raw representative stored in `H1Function`. -/
def SmallContrastSchauderConclusion (alpha K : ℝ)
    (u : H1Function (smallContrastUnitBall d)) : Prop :=
  HasSmallContrastGradientScaleBound alpha K u ∧
    ∃ uRep : Vec d → ℝ,
      ContinuousOn uRep (smallContrastBall d (1 / 2)) ∧
      uRep =ᵐ[volume.restrict (smallContrastUnitBall d)] u.toFun ∧
      EuclideanHolderBoundOn (smallContrastBall d (1 / 2)) alpha K uRep

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
