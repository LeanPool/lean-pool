/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ProjectiveSection
public import LeanPool.CCDN.Height.ProjectiveZeroLocus
public import LeanPool.CCDN.Hilbert.AffineCurveDegree
public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial

/-!
# Statements of the main results

The counting statements of Theorems 1–4, as propositions, together with the plane case of
Theorem 3 and the hypersurface case of Theorem 1 that the proofs use as intermediate targets.
This module imports only the foundation directories (the counting functions of `Height/`, the
zero loci and degree predicates of `Algebra/`, and the Hilbert-function degrees of `Hilbert/`),
so each statement can be read without the proof infrastructure.

* `PlaneCurveBound`: Theorem 3 for plane curves, proved in `CCDN.Plane.CurveCount`;
* `AffineCurveBound`: Theorem 3, proved in `CCDN.AffineCurveBound`;
* `ProjectiveCurveBound`: Theorem 2, proved in `CCDN.ProjectiveCurveBound`;
* `AffineHypersurfaceGrowth` and `RationalAffineHypersurfaceGrowth`: Theorem 4 with a given
  degree exponent, proved in `CCDN.AffineHypersurfaceDimensionGrowth`;
* `ProjectiveHypersurfaceGrowth`: Theorem 1 for hypersurfaces, proved in
  `CCDN.Hypersurface.ProjectiveHypersurfaceDimensionGrowth`;
* `ProjectiveGrowth`: Theorem 1 with a given degree exponent, proved in
  `CCDN.ProjectiveDimensionGrowth`.

Theorem 6 and Proposition 5 are stated directly by their endpoint theorems
`classGroup_two_torsion_bound` and `projective_integral_curve_lower_bound`.
-/

@[expose] public section

namespace CCDN

noncomputable section

/-! ### Theorem 3: affine curves -/

/-- The bound `d³ B^(1/d) (log B + d)` of Theorem 3. -/
noncomputable def curveBound (d : ℕ) (B : ℝ) : ℝ :=
  (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) * (Real.log B + d)

/-- The `n = 2` case of CCDN (2020), Theorem 3, expressed using rational defining
polynomials. The proof (`planeCurveBound`, in
`CCDN.Plane.CurveCount`) includes denominator clearing and content removal.
Irreducibility is over `ℚ`, not absolute irreducibility. The one constant is uniform in the
polynomial, its degree, its coefficients, and the real radius. -/
def PlaneCurveBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : MvPolynomial (Fin 2) ℚ, Irreducible f →
    0 < f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus f) B : ℝ) ≤ C * curveBound f.totalDegree B

/-- CCDN (2020), Theorem 3, using the affine Hilbert function to specify degree.
The constant is chosen before the ideal, degree, and real box radius. -/
def AffineCurveBound : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ I : Ideal (CoordinatePolynomial n), I.IsPrime →
      ∀ d : ℕ, 0 < d → HasAffineCurveDegree I d →
        ∀ B : ℝ, 1 ≤ B → (count (idealZeroLocus I) B : ℝ) ≤ C * curveBound d B

/-! ### Theorem 2: projective curves -/

/-- The bound `d⁴ B^(2/d)` of Theorem 2. -/
def projectiveCurveEstimate (d : ℕ) (B : ℝ) : ℝ :=
  (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ))

/-- CCDN (2020), Theorem 2, with projective degree specified by the
homogeneous Hilbert function. The constant precedes the ideal, degree and radius. -/
def ProjectiveCurveBound : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ I : Ideal (CoordinatePolynomial (n + 1)), I.IsPrime →
      ∀ d : ℕ, 0 < d → HasProjectiveCurveDegree I d →
        ∀ B : ℝ, 1 ≤ B →
          (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤ C * projectiveCurveEstimate d B

/-! ### Theorem 4: affine hypersurfaces -/

/-- Affine dimension growth with degree exponent `e` for integer equations in `n + 3`
variables of degree at least five whose top-degree form is absolutely irreducible. The
constant depends only on `n` and `e`. -/
def AffineHypersurfaceGrowth (n e : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ f : MvPolynomial (Fin (n + 3)) ℤ, HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
        (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) f)) B : ℝ) ≤
          C * (f.totalDegree : ℝ) ^ e * B ^ (n + 1)

/-- The rational-equation form of `AffineHypersurfaceGrowth`. -/
def RationalAffineHypersurfaceGrowth (n e : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ f : MvPolynomial (Fin (n + 3)) ℚ, HasAbsIrreducibleTopFormRat f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
        (count (zeroLocus f) B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ e * B ^ (n + 1)

/-! ### Theorem 1: projective varieties -/

/-- Dimension growth with degree exponent `e` for rationally irreducible projective
hypersurfaces of degree at least five in `ℙ^(n+2)`. The height exponent is the
hypersurface dimension `n + 1`. -/
def ProjectiveHypersurfaceGrowth (n e : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ f : MvPolynomial (Fin (n + 3)) ℚ, f.IsHomogeneous f.totalDegree → Irreducible f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
        (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
          C * (f.totalDegree : ℝ) ^ e * B ^ (n + 1)

/-- CCDN Theorem 1 in `ℙⁿ` with degree exponent `E`. A homogeneous prime ideal whose
Hilbert polynomial has degree `r` and leading coefficient `d / r!`, with `d ≥ 5`, has at
most `C d^E B^(r-1)` rational points of height at most `B`. The constant depends only on
`n` and `E`. -/
def ProjectiveGrowth (n E : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime → IsHomogeneousIdeal I →
      ∀ d : ℕ, 5 ≤ d →
      (filteredHilbertPolynomial I).leadingCoeff =
        (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ E * B ^ ((filteredHilbertPolynomial I).natDegree - 1)

end

end CCDN
