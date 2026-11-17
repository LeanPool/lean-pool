/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousChart
public import LeanPool.CCDN.Determinant.HypersurfaceLocalDeterminant
public import LeanPool.CCDN.Determinant.PlaneMultiplicity
public import LeanPool.CCDN.Determinant.ProjectiveLocalDeterminant

/-!
Projective hypersurface determinants in all positive dimensions.
Unit normalization modulo prime powers transfers the local affine
bound to homogeneous evaluation matrices of a common degree.

Singular local determinant bounds at a residue point in arbitrary
dimension. Multiplicity is obtained from the first nonzero translated homogeneous
component.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Translation carries the finite-precision determinant theorem to any
residue class. Its divisor and its precision use the same explicit exponent. -/
theorem hypersurface_residue_pow_dvd_det_mod {p n μ s : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 2)) ℤ) (a : Fin (n + 2) → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a f) ∈
      idealOfVars (Fin (n + 2)) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) (originShift a f)) ≠ 0)
    (x : Fin s → Fin (n + 2) → ℤ) (hx : ∀ i j, (p : ℤ) ∣ x i j - a j)
    (hfx : ∀ i, (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣ eval (x i) f)
    (F : Fin s → MvPolynomial (Fin (n + 2)) ℤ) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
      (Matrix.of fun i j => eval (x i) (F j)).det := by
  have h := hypersurface_pow_dvd_det_mod (originShift a f) hf hμ
    (fun i j => x i j - a j) hx
    (fun i => by simpa only [eval_sub_originShift] using hfx i)
    (fun j => originShift a (F j))
  simpa only [eval_sub_originShift] using h

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- Unit normalization in the first homogeneous coordinate preserves the
evaluation of a degree-M form, up to the corresponding unit row factor. -/
lemma projective_hypersurface_chart_eval_congr {n M : ℕ} {q u : ℤ}
    (z : Fin (n + 3) → ℤ) (hu : q ∣ u * z 0 - 1)
    (F : MvPolynomial (Fin (n + 3)) ℤ) (hF : F.IsHomogeneous M) :
    q ∣ eval (fun j : Fin (n + 2) => u * z j.succ) (affineChart (n + 2) F) -
      u ^ M * eval z F := by
  exact projective_chart_eval_congr z hu F hF

/-- Projective local determinant estimate in a chart whose first coordinate
is a p-adic unit. The affine multiplicity belongs to the chart equation. -/
theorem projective_hypersurface_chart_det_divisibility {p n μ s d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin s → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin (n + 3) → ℤ) (a : Fin (n + 2) → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a (affineChart (n + 2) f)) ∈
      idealOfVars (Fin (n + 2)) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ
      (map (Int.castRingHom (ZMod p)) (originShift a (affineChart (n + 2) f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i 0))
    (hres : ∀ i j, (p : ℤ) ∣ z i j.succ - a j * z i 0)
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
      (Matrix.of fun i j => eval (z i) (F j)).det := by
  apply projective_chart_det_divisibility_of_affine f hfhom F hF z a hunit hres hz
  intro x hx hxf G
  exact hypersurface_residue_pow_dvd_det_mod (affineChart (n + 2) f) a hf hμ x hx hxf G

/-- Move coordinate `k` to the first position before taking the affine chart. -/
def projectiveHypersurfaceChart {n : ℕ} (k : Fin (n + 3)) (f : MvPolynomial (Fin (n + 3)) ℤ) :
    MvPolynomial (Fin (n + 2)) ℤ :=
  projectiveChart k f

/-- The local projective divisor is available in every coordinate chart. -/
theorem projective_hypersurface_local_det_divisibility {p n μ s d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin s → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin (n + 3) → ℤ) (k : Fin (n + 3)) (a : Fin (n + 2) → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a (projectiveHypersurfaceChart k f)) ∈
      idealOfVars (Fin (n + 2)) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ
      (map (Int.castRingHom (ZMod p)) (originShift a (projectiveHypersurfaceChart k f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i k))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 k j.succ) - a j * z i k)
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
      (Matrix.of fun i j => eval (z i) (F j)).det := by
  apply projective_local_det_divisibility_of_affine f hfhom F hF z k a hunit hres hz
  intro x hx hxf G
  exact hypersurface_residue_pow_dvd_det_mod (projectiveHypersurfaceChart k f)
    a hf hμ x hx hxf G

/-- Assemble local projective residue classes in their own coordinate charts.
Every maximal minor acquires the sum of their local multiplicity exponents. -/
theorem projective_hypersurface_residue_minorGcd {p n c s N d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin (n + 3) → ℤ) (label : Fin s → Fin c)
    (k : Fin c → Fin (n + 3)) (a : Fin c → Fin (n + 2) → ℤ) (μ : Fin c → ℕ)
    (hf : ∀ i, map (Int.castRingHom (ZMod p))
      (originShift (a i) (projectiveHypersurfaceChart (k i) f)) ∈
        idealOfVars (Fin (n + 2)) (ZMod p) ^ μ i)
    (hμ : ∀ i, homogeneousComponent (μ i) (map (Int.castRingHom (ZMod p))
      (originShift (a i) (projectiveHypersurfaceChart (k i) f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i (k (label i))))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 (k (label i)) j.succ) -
      a (label i) j * z i (k (label i)))
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ (∑ i : Fin c, hypersurfaceMultiplicityExponent (n + 1) (μ i)
      (Fintype.card {j : Fin s // label j = i})) ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  apply projective_residue_minorGcd_of_affine f hfhom F hF z label k a
    (fun i => hypersurfaceMultiplicityExponent (n + 1) (μ i)
      (Fintype.card {j : Fin s // label j = i})) hunit hres hz
  intro i x hx hxf G
  exact hypersurface_residue_pow_dvd_det_mod (projectiveHypersurfaceChart (k i) f)
    (a i) (hf i) (hμ i) x hx hxf G

end
end CCDN
