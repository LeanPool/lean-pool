/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.SingularTangent
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.MvPolynomial
import LeanPool.CCDN.Algebra.ModularPolynomialLift
import LeanPool.CCDN.Determinant.OriginTruncationGenerators
import Mathlib.FieldTheory.Finite.Polynomial

/-! Lift singular local generators from the reduction modulo p. The
remaining error is an explicit multiple of p, with a separate high-order term. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Lift a whole homogeneous generating family without changing its size at
any weight. The error separates the equation, the origin power and a multiple of p. -/
private theorem lift_origin_truncation_generators {σ : Type*} {p : ℕ} [Fact p.Prime]
    (f : MvPolynomial σ ℤ) (r : ℕ → ℕ)
    (g : (k : ℕ) → Fin (r k) → MvPolynomial σ (ZMod p))
    (hg : ∀ k j, (g k j).IsHomogeneous k)
    (hspan : ∀ N u, ∃ c : (k : Fin N) → Fin (r k.val) → ZMod p,
      u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈
        Ideal.span {map (Int.castRingHom (ZMod p)) f} ⊔ idealOfVars σ (ZMod p) ^ N) :
    ∃ G : (k : ℕ) → Fin (r k) → MvPolynomial σ ℤ,
      (∀ k j, (G k j).IsHomogeneous k) ∧
      ∀ N u, ∃ (c : (k : Fin N) → Fin (r k.val) → ℤ) (h v w : MvPolynomial σ ℤ),
        v ∈ idealOfVars σ ℤ ^ N ∧
        u - ∑ k : Fin N, ∑ j, c k j • G k.val j = f * h + v + C (p : ℤ) * w := by
  classical
  let π := Int.castRingHom (ZMod p)
  refine ⟨(fun k j => modularPolynomialLift (g k j)),
    (fun k j => modularPolynomialLift_homogeneous _ (hg k j)), ?_⟩
  intro N u
  obtain ⟨c, hc⟩ := hspan N (map π u)
  obtain ⟨h', hh', v, hv, he⟩ := Submodule.mem_sup.mp hc
  obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton.mp hh'
  let cZ : (k : Fin N) → Fin (r k.val) → ℤ := fun k j => (c k j).val
  let S := ∑ k : Fin N, ∑ j, cZ k j • modularPolynomialLift (g k.val j)
  have hS : map π S = ∑ k : Fin N, ∑ j, c k j • g k.val j := by
    simp only [S, cZ, smul_eq_C_mul, map_sum, map_mul, map_C, map_modularPolynomialLift,
      π, Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_zmod_val]
  let D := u - S - f * modularPolynomialLift h - modularPolynomialLift v
  have hlift (q : MvPolynomial σ (ZMod p)) : map π (modularPolynomialLift q) = q :=
    map_modularPolynomialLift q
  have hD : map π D = 0 := by
    simp only [D, map_sub, map_mul, hlift, hS]
    linear_combination -he
  obtain ⟨w, hw⟩ := (C_dvd_iff_zmod p D).mpr hD
  refine ⟨cZ, modularPolynomialLift h, modularPolynomialLift v, w,
    modularPolynomialLift_mem_origin_power v hv, ?_⟩
  change u - S = _
  dsimp only [D] at hw
  linear_combination hw


/-- Integer generators in arbitrary dimension, with the residue-layer
Hilbert function as their weight profile. -/
theorem exists_integer_hypersurface_generators {p n : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 1)) ℤ) :
    ∃ (r : ℕ → ℕ) (g : (k : ℕ) → Fin (r k) → MvPolynomial (Fin (n + 1)) ℤ),
      (∀ k, r k = Module.finrank (ZMod p)
        (originLayer (map (Int.castRingHom (ZMod p)) f) k)) ∧
      (∀ k j, (g k j).IsHomogeneous k) ∧
      ∀ N u, ∃ (c : (k : Fin N) → Fin (r k.val) → ℤ)
        (h v w : MvPolynomial (Fin (n + 1)) ℤ),
        v ∈ idealOfVars (Fin (n + 1)) ℤ ^ N ∧
        u - ∑ k : Fin N, ∑ j, c k j • g k.val j = f * h + v + C (p : ℤ) * w := by
  obtain ⟨r, g, hr, hg, hs⟩ :=
    exists_origin_truncation_generators (map (Int.castRingHom (ZMod p)) f)
  obtain ⟨G, hG, hrep⟩ := lift_origin_truncation_generators f r g hg hs
  exact ⟨r, G, hr, hG, hrep⟩

/-- The local generators are homogeneous integer polynomials. Their
uniform reduction formula separates the defining equation, the origin-adic
error, and the p-divisible error. -/
theorem exists_integer_origin_generators {p μ : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ)
    (hf : map (Int.castRingHom (ZMod p)) f ∈ idealOfVars (Fin 2) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) f) ≠ 0) :
    ∃ (r : ℕ → ℕ) (g : (k : ℕ) → Fin (r k) → MvPolynomial (Fin 2) ℤ),
      (∀ k, r k ≤ μ) ∧ (∀ k j, (g k j).IsHomogeneous k) ∧
      ∀ N u, ∃ (c : (k : Fin N) → Fin (r k.val) → ℤ) (h v w : MvPolynomial (Fin 2) ℤ),
        v ∈ idealOfVars (Fin 2) ℤ ^ N ∧
        u - ∑ k : Fin N, ∑ j, c k j • g k.val j = f * h + v + C (p : ℤ) * w := by
  obtain ⟨r, g, hr, hg, hs⟩ :=
    exists_plane_truncation_generators (map (Int.castRingHom (ZMod p)) f) hf hμ
  obtain ⟨G, hG, hrep⟩ := lift_origin_truncation_generators f r g hg hs
  exact ⟨r, G, hr, hG, hrep⟩

end
end CCDN
