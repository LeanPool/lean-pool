/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-poincare/GinibrePoincare/Concrete/Generator.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Concrete.SmoothTarget

/-!
# The concrete Ginibre pregenerator

This is the speed `αₙ = n` realization used in Theorem 1.9 of the paper.
It is defined on representatives; its closed `L²` realization is a later
milestone.
-/


@[expose] public section


open scoped BigOperators ContDiff

namespace GinibrePoincare

noncomputable section

/-- The real symmetric test-function core used in Theorem 1.9: smooth,
compactly supported, and supported away from particle collisions. -/
def IsTheoremOneNineCore {n : ℕ} (f : Configuration n → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    tsupport f ⊆ (collisionSet n)ᶜ ∧ IsSymmetric f

/-- The collision-free core refines the smooth compact symmetric core used by
the Poincaré reduction. -/
theorem IsTheoremOneNineCore.isSmoothCompactSymmetric {n : ℕ}
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) :
    IsSmoothCompactSymmetric f :=
  ⟨hf.1, hf.2.1, hf.2.2.2⟩

/-- Every point in the support of a Theorem 1.9 core function is
collision-free. -/
theorem IsTheoremOneNineCore.support_collisionFree {n : ℕ}
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f)
    {z : Configuration n} (hz : z ∈ Function.support f) :
    CollisionFree z := by
  rw [collisionFree_iff_not_mem_collisionSet]
  exact hf.2.2.1 (subset_tsupport _ hz)

/-- Second real directional derivative, expressed using Fréchet derivatives. -/
def secondDirectionalDerivative {n : ℕ}
    (f : Configuration n → ℝ) (v : Configuration n)
    (z : Configuration n) : ℝ :=
  fderiv ℝ (fun x => fderiv ℝ f x v) z v

theorem secondDirectionalDerivative_sub_const {n : ℕ}
    (f : Configuration n → ℝ) (c : ℝ) (v : Configuration n)
    (z : Configuration n) :
    secondDirectionalDerivative (fun x => f x - c) v z =
      secondDirectionalDerivative f v z := by
  unfold secondDirectionalDerivative
  have hfun :
      (fun x => fderiv ℝ (fun y => f y - c) x v) =
        fun x => fderiv ℝ f x v := by
    funext x
    rw [fderiv_sub_const]
  rw [hfun]

theorem fderiv_apply_sub_const {n : ℕ}
    (f : Configuration n → ℝ) (c : ℝ) (z v : Configuration n) :
    fderiv ℝ (fun x => f x - c) z v = fderiv ℝ f z v := by
  rw [fderiv_sub_const]

/-- Euclidean Laplacian on `ℂⁿ ≃ ℝ²ⁿ`. -/
def configurationLaplacian {n : ℕ}
    (f : Configuration n → ℝ) (z : Configuration n) : ℝ :=
  ∑ j : Fin n,
    (secondDirectionalDerivative f (realCoordinateDirection j) z +
      secondDirectionalDerivative f (imaginaryCoordinateDirection j) z)

/-- Direction of the pairwise Coulomb drift for a pair of particles.  Its
value on the collision set is immaterial for compactly supported core
functions whose support avoids collisions. -/
def coulombPairDirection {n : ℕ} (j k : Fin n)
    (z : Configuration n) : Configuration n :=
  coordinateDirection j
      ((z j - z k) / Complex.normSq (z j - z k)) -
    coordinateDirection k
      ((z j - z k) / Complex.normSq (z j - z k))

/-- The Ginibre Langevin pregenerator at speed `αₙ = n` and inverse
temperature `βₙ = n²`.

The three terms are respectively `(1/n) Δ`, the quadratic confinement
drift, and the symmetrized Coulomb drift. -/
def ginibrePregenerator (n : ℕ)
    (f : Configuration n → ℝ) (z : Configuration n) : ℝ :=
  (1 / (n : ℝ)) * configurationLaplacian f z -
    2 * ∑ j : Fin n,
      fderiv ℝ f z (coordinateDirection j (z j)) +
    (2 / (n : ℝ)) * ∑ j : Fin n, ∑ k ∈ Finset.Ioi j,
      fderiv ℝ f z (coulombPairDirection j k z)

/-- The pregenerator kills constants. -/
@[simp] theorem ginibrePregenerator_const (n : ℕ) (c : ℝ) (z : Configuration n) :
    ginibrePregenerator n (fun _ => c) z = 0 := by
  simp [ginibrePregenerator, configurationLaplacian,
    secondDirectionalDerivative]

/-- Centering an observable does not change its pregenerator. -/
theorem ginibrePregenerator_sub_const (n : ℕ)
    (f : Configuration n → ℝ) (c : ℝ) (z : Configuration n) :
    ginibrePregenerator n (fun x => f x - c) z =
      ginibrePregenerator n f z := by
  simp [ginibrePregenerator, configurationLaplacian,
    secondDirectionalDerivative_sub_const, fderiv_apply_sub_const]

/-- Squared `L²(μₙ)` norm of the concrete pregenerator. -/
def ginibreGeneratorNormSq (n : ℕ)
    (f : Configuration n → ℝ) : ℝ :=
  ∫ z, (ginibrePregenerator n f z) ^ 2 ∂ginibreMeasure n

/-- Centering does not change the squared generator norm. -/
theorem ginibreGeneratorNormSq_sub_const (n : ℕ)
    (f : Configuration n → ℝ) (c : ℝ) :
    ginibreGeneratorNormSq n (fun z => f z - c) =
      ginibreGeneratorNormSq n f := by
  simp [ginibreGeneratorNormSq, ginibrePregenerator_sub_const]

/-- Squared norm of `(Aₙ + 2)f`. -/
def shiftedGinibreGeneratorNormSq (n : ℕ)
    (f : Configuration n → ℝ) : ℝ :=
  ∫ z, (ginibrePregenerator n f z + 2 * f z) ^ 2 ∂ginibreMeasure n

end

end GinibrePoincare
