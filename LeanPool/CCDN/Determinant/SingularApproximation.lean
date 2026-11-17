/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.MvPolynomial.Ideal
import LeanPool.CCDN.Determinant.ModularOriginGenerators
import Mathlib.Tactic.LinearCombination

/-! Uniform finite p-adic approximation by weighted local generators
at a possibly singular plane-curve residue point. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- If every coordinate of `x` is divisible by `p`, then `p ^ N` divides `u(x)` for every integer
polynomial `u` in the `N`-th power of the ideal of the origin. -/
lemma origin_power_eval_dvd {σ : Type*} (p : ℤ) (x : σ → ℤ) (hx : ∀ j, p ∣ x j)
    {N : ℕ} {u : MvPolynomial σ ℤ} (hu : u ∈ idealOfVars σ ℤ ^ N) :
    p ^ N ∣ eval x u := by
  have hI : idealOfVars σ ℤ ≤ (Ideal.span {p}).comap (eval x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change eval x (X j) ∈ Ideal.span {p}
    rw [eval_X]
    exact Ideal.mem_span_singleton.mpr (hx j)
  have hpow := (pow_le_pow_left' hI N).trans (Ideal.le_comap_pow (eval x) N)
  have hmem := hpow hu
  change eval x u ∈ (Ideal.span {p}) ^ N at hmem
  rw [Ideal.span_singleton_pow] at hmem
  exact Ideal.mem_span_singleton.mp hmem

/-- Iterating the explicit p-divisible error yields a representation to any
fixed precision, uniformly over every integral zero in the origin residue class. -/
lemma integer_generators_approximate_mod {σ : Type*} {p N : ℕ} (f : MvPolynomial σ ℤ)
    (r : ℕ → ℕ) (g : (k : ℕ) → Fin (r k) → MvPolynomial σ ℤ)
    (hrep : ∀ u, ∃ (c : (k : Fin N) → Fin (r k.val) → ℤ) (h v w : MvPolynomial σ ℤ),
      v ∈ idealOfVars σ ℤ ^ N ∧
      u - ∑ k : Fin N, ∑ j, c k j • g k.val j = f * h + v + C (p : ℤ) * w)
    (u : MvPolynomial σ ℤ) :
    ∃ c : (k : Fin N) → Fin (r k.val) → ℤ, ∀ x : σ → ℤ,
      (p : ℤ) ^ N ∣ eval x f → (∀ j, (p : ℤ) ∣ x j) →
      (p : ℤ) ^ N ∣ eval x u - ∑ k : Fin N, ∑ j, c k j * eval x (g k.val j) := by
  have hprec : ∀ k ≤ N, ∀ u : MvPolynomial σ ℤ,
      ∃ c : (j : Fin N) → Fin (r j.val) → ℤ, ∀ x : σ → ℤ,
        (p : ℤ) ^ N ∣ eval x f → (∀ j, (p : ℤ) ∣ x j) →
        (p : ℤ) ^ k ∣ eval x u - ∑ j : Fin N, ∑ l, c j l * eval x (g j.val l) := by
    intro k
    induction k with
    | zero =>
      intro _ u
      exact ⟨fun _ _ => 0, fun _ _ _ => by simp only [pow_zero, one_dvd]⟩
    | succ k ih =>
      intro hk u
      obtain ⟨c, h, v, w, hv, he⟩ := hrep u
      obtain ⟨b, hb⟩ := ih (by omega) w
      refine ⟨fun j l => c j l + (p : ℤ) * b j l, ?_⟩
      intro x hfx hx
      have hvdiv := origin_power_eval_dvd (p : ℤ) x hx hv
      have hbdiv := hb x hfx hx
      have heval := congrArg (eval x) he
      simp only [eval_sub, eval_add, map_sum, smul_eq_C_mul, eval_mul, eval_C] at heval
      have heq : eval x u - ∑ j : Fin N, ∑ l, (c j l + (p : ℤ) * b j l) * eval x (g j.val l) =
          eval x f * eval x h + eval x v +
            (p : ℤ) * (eval x w - ∑ j : Fin N, ∑ l, b j l * eval x (g j.val l)) := by
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        linear_combination heval
      rw [heq]
      apply dvd_add (dvd_add
        ((pow_dvd_pow (p : ℤ) hk).trans (dvd_mul_of_dvd_left hfx _))
        ((pow_dvd_pow (p : ℤ) hk).trans hvdiv))
      simpa only [pow_succ, mul_comm (p : ℤ)] using mul_dvd_mul_left (p : ℤ) hbdiv
  exact hprec N le_rfl u

/-- For a plane equation of multiplicity `μ` at the origin modulo `p`, a family of at most `μ`
integer homogeneous generators in each degree approximates every polynomial modulo `p^N` at all
zeros of `f` modulo `p^N` divisible by `p`, with one choice of coefficients for all such zeros.
This permits normalization of projective points modulo prime powers. -/
theorem exists_singular_plane_approximation_mod {p μ : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ)
    (hf : map (Int.castRingHom (ZMod p)) f ∈ idealOfVars (Fin 2) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) f) ≠ 0) :
    ∃ (r : ℕ → ℕ) (g : (k : ℕ) → Fin (r k) → MvPolynomial (Fin 2) ℤ),
      (∀ k, r k ≤ μ) ∧ (∀ k j, (g k j).IsHomogeneous k) ∧
      ∀ N u, ∃ c : (k : Fin N) → Fin (r k.val) → ℤ, ∀ x : Fin 2 → ℤ,
        (p : ℤ) ^ N ∣ eval x f → (∀ j, (p : ℤ) ∣ x j) →
        (p : ℤ) ^ N ∣ eval x u - ∑ k : Fin N, ∑ j, c k j * eval x (g k.val j) := by
  obtain ⟨r, g, hr, hg, hrep⟩ := exists_integer_origin_generators f hf hμ
  exact ⟨r, g, hr, hg, fun N u => integer_generators_approximate_mod f r g (hrep N) u⟩

end
end CCDN
