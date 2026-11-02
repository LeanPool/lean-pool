/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.BombieriVaaler
public import LeanPool.CCDN.Algebra.OriginShift
public import LeanPool.CCDN.Determinant.LocalDeterminant
public import Mathlib.RingTheory.MvPolynomial.Ideal
import LeanPool.CCDN.Determinant.BlockDeterminant
import LeanPool.CCDN.Determinant.SingularLocalDeterminant

/-! Translation and residue-block assembly for the singular local
plane-curve determinant theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Singular local divisibility at an arbitrary integral representative of a
residue point; multiplicity is measured on the translated reduction. -/
theorem singular_plane_chart_det_divisibility_mod {p μ s : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ) (F : Fin s → MvPolynomial (Fin 2) ℤ)
    (x : Fin s → Fin 2 → ℤ) (a : Fin 2 → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a f) ∈
      idealOfVars (Fin 2) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) (originShift a f)) ≠ 0)
    (hx : ∀ i j, (p : ℤ) ∣ x i j - a j)
    (hfx : ∀ i, (p : ℤ) ^ multiplicityExponent s μ ∣ eval (x i) f) :
    (p : ℤ) ^ multiplicityExponent s μ ∣
      (Matrix.of fun i j => eval (x i) (F j)).det := by
  have he (i : Fin s) (u : MvPolynomial (Fin 2) ℤ) :
      eval (fun j => x i j - a j) (originShift a u) = eval (x i) u := by
    exact eval_sub_originShift a (x i) u
  have h := singular_plane_pow_dvd_det_mod (originShift a f) hf hμ
    (fun i j => x i j - a j) hx (fun i => by rw [he]; exact hfx i)
    (fun j => originShift a (F j))
  simpa only [he] using h

/-- Exact integral zeros satisfy the finite-precision version at every precision. -/
private theorem singular_plane_chart_det_divisibility {p μ s : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ) (F : Fin s → MvPolynomial (Fin 2) ℤ)
    (x : Fin s → Fin 2 → ℤ) (a : Fin 2 → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a f) ∈
      idealOfVars (Fin 2) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) (originShift a f)) ≠ 0)
    (hx : ∀ i j, (p : ℤ) ∣ x i j - a j) (hfx : ∀ i, eval (x i) f = 0) :
    (p : ℤ) ^ multiplicityExponent s μ ∣
      (Matrix.of fun i j => eval (x i) (F j)).det := by
  have he (i : Fin s) (u : MvPolynomial (Fin 2) ℤ) :
      eval (fun j => x i j - a j) (originShift a u) = eval (x i) u := by
    exact eval_sub_originShift a (x i) u
  have h := singular_plane_pow_dvd_det (originShift a f) hf hμ
    (fun i j => x i j - a j) hx (fun i => by rw [he]; exact hfx i)
    (fun j => originShift a (F j))
  simpa only [he] using h

/-- Summed multiplicity exponents for arbitrary residue blocks, including
singular blocks. Each local hypothesis describes the reduced equation. -/
theorem singular_plane_residue_minorGcd {p c s N : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ) (F : Fin N → MvPolynomial (Fin 2) ℤ)
    (x : Fin s → Fin 2 → ℤ) (label : Fin s → Fin c)
    (a : Fin c → Fin 2 → ℤ) (μ : Fin c → ℕ)
    (hf : ∀ i, map (Int.castRingHom (ZMod p)) (originShift (a i) f) ∈
      idealOfVars (Fin 2) (ZMod p) ^ μ i)
    (hμ : ∀ i, homogeneousComponent (μ i)
      (map (Int.castRingHom (ZMod p)) (originShift (a i) f)) ≠ 0)
    (hx : ∀ i j, (p : ℤ) ∣ x i j - a (label i) j) (hfx : ∀ i, eval (x i) f = 0) :
    (p : ℤ) ^ (∑ i : Fin c, multiplicityExponent
      (Fintype.card {k : Fin s // label k = i}) (μ i)) ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (x i) (F j)) := by
  apply residue_prime_powers_dvd_minorGcd _ label
  intro i cols
  apply singular_plane_chart_det_divisibility f (fun j => F (cols j))
    (fun k => x (residueRows label i k)) (a i) (hf i) (hμ i)
  · intro k j
    simpa only [residueRows_label] using hx (residueRows label i k) j
  · intro k
    exact hfx _

end
end CCDN
