/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The question of Kazhdan and Polishchuk about formula (3) has a negative answer

arXiv 2107.08085, end of section 3: for a finite group `G`, a linear subspace `A` of a
representation `V` with
`dim A / (A ∩ gA) ≤ r` for all `g`, and `A₀ = ∑_{|S| > |G|/2} ⋂_{g ∈ S} gA`, is `A` close to `A₀`,
with a bound that depends on `r` only?

Here `V = K^n`, a finite group `H` of at least `2n - 1` nonzero scalars `t` acts by `(t, t^2, ...,
t^n)`, and `A` is the hyperplane
of the vectors with coordinate sum `0`. Then `r = 1`, but `A₀ = 0` and `dim A = n - 1`.
-/

@[expose] public section

open Submodule Module

namespace AlmostInvariant

variable {K : Type*} [Field K]

/-- `t` acts on `K^n` by multiplication of coordinate `i` by `t^(i+1)`. -/
def powAct (n : ℕ) : Kˣ →* ((Fin n → K) ≃ₗ[K] (Fin n → K)) where
  toFun t := LinearEquiv.piCongrRight fun i : Fin n => LinearEquiv.smulOfUnit (t ^ ((i : ℕ) + 1))
  map_one' := by
    ext x i
    simp [LinearEquiv.smulOfUnit]
  map_mul' s t := by
    ext x i
    simp [LinearEquiv.smulOfUnit, Units.smul_def, mul_pow, mul_assoc]

theorem powAct_apply (n : ℕ) (t : Kˣ) (x : Fin n → K) (i : Fin n) : powAct n t x i = (t : K)
    ^ ((i : ℕ) + 1) * x i := by
  simp [powAct, LinearEquiv.smulOfUnit, Units.smul_def]

/-- The functional whose kernel is the translate of the hyperplane. -/
def tr (n : ℕ) (t : Kˣ) : (Fin n → K) →ₗ[K] K := ∑ i : Fin n, ((t⁻¹ : Kˣ) : K) ^ ((i : ℕ) + 1)
    • LinearMap.proj i

theorem tr_apply (n : ℕ) (t : Kˣ) (x : Fin n → K) : tr n t x = ∑ i : Fin n, ((t⁻¹ : Kˣ) : K)
    ^ ((i : ℕ) + 1) * x i := by
  simp [tr]

/-- The hyperplane of the vectors with coordinate sum `0`. -/
def hyp (K : Type*) [Field K] (n : ℕ) : Submodule K (Fin n → K) := LinearMap.ker (tr n (1 : Kˣ))

theorem map_hyp (n : ℕ) (t : Kˣ) : (hyp K n).map (powAct n t : (Fin n → K) →ₗ[K] (Fin n → K))
    = LinearMap.ker (tr n t) := by
  ext y
  simp only [Submodule.mem_map, hyp, LinearMap.mem_ker, tr_apply, inv_one, Units.val_one, one_pow,
      one_mul]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearEquiv.coe_coe, powAct_apply, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow,
        one_mul]
  · intro hy
    refine ⟨(powAct n t).symm y, ?_, by simp⟩
    rw [← hy]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : powAct n t ((powAct n t).symm y) i = y i := by simp
    rw [powAct_apply] at h
    rw [← h, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]

/-- Every two translates differ by at most one dimension. -/
theorem rank_le_one (n : ℕ) (t : Kˣ) (A N : Submodule K (Fin n → K)) (hN : N
    = LinearMap.ker (tr n t)) :
    Module.rank K (A ⧸ N.submoduleOf A) ≤ 1 := by
  subst hN
  have e : (LinearMap.ker (tr n t)).submoduleOf A = LinearMap.ker ((tr n t).comp A.subtype) := by
    ext x; simp [Submodule.submoduleOf]
  rw [e, (LinearMap.quotKerEquivRange ((tr n t).comp A.subtype)).rank_eq]
  calc Module.rank K (LinearMap.range ((tr n t).comp A.subtype)) ≤ Module.rank K K :=
      Submodule.rank_le _
    _ = 1 := rank_self K

/-- At least `n` translates meet in `0`. -/
theorem inf_eq_bot (n : ℕ) (S : Finset Kˣ) (hS : n ≤ S.card) : (⨅ t ∈ S, LinearMap.ker (tr n t))
    = (⊥ : Submodule K (Fin n → K)) := by
  classical
  rw [eq_bot_iff]
  intro y hy
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, tr_apply] at hy
  -- the polynomial with coefficients `y`
  let q : Polynomial K := ∑ i : Fin n, Polynomial.monomial (i : ℕ) (y i)
  have hcoef : ∀ i : Fin n, q.coeff i = y i := by
    intro i
    simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      exact Finsupp.single_eq_of_ne fun h => hj (Fin.ext h.symm)
    · simp
  have hdeg : q.degree < n := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact WithBot.bot_lt_coe n)]
    intro i _
    exact lt_of_le_of_lt (Polynomial.degree_monomial_le _ _) (by exact_mod_cast i.2)
  have hq : q = 0 := by
    let f : Kˣ → K := fun t => ((t⁻¹ : Kˣ) : K)
    have hf : Function.Injective f := fun s t h => inv_injective (Units.ext h)
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (S.image f) ?_ ?_
    · rw [Finset.card_image_of_injective _ hf]
      exact lt_of_lt_of_le hdeg (by exact_mod_cast hS)
    · intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      have h := hy t ht
      have h2 : ((t⁻¹ : Kˣ) : K) * q.eval ((t⁻¹ : Kˣ) : K) = 0 := by
        rw [← h]
        simp only [q, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      exact (mul_eq_zero.mp h2).resolve_left (Units.ne_zero _)
  rw [Submodule.mem_bot]
  ext i
  rw [← hcoef i, hq]
  simp

/-- The dimension of the hyperplane. -/
theorem finrank_hyp (n : ℕ) (hn : 0 < n) : finrank K (hyp K n) = n - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (tr n (1 : Kˣ))
  have hr : LinearMap.range (tr n (1 : Kˣ)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨Pi.single ⟨0, hn⟩ c, ?_⟩
    rw [tr_apply, Finset.sum_eq_single ⟨0, hn⟩]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  rw [hr, finrank_top, finrank_self, finrank_fin_fun] at h
  have : finrank K (hyp K n) = finrank K (LinearMap.ker (tr n (1 : Kˣ))) := rfl
  omega

/-- **The answer is no**, over every field that has a finite group of at least `2n - 1` nonzero
elements. -/
theorem question_negative (n : ℕ) (hn : 0 < n) (H : Subgroup Kˣ) (hH : 2 * n
    ≤ Nat.card H + 1) :
    ∃ (ρ : H →* ((Fin n → K) ≃ₗ[K] (Fin n → K))) (A : Submodule K (Fin n → K)),
      (∀ g, Module.rank K (A ⧸ (A.map (ρ g : (Fin n → K) →ₗ[K] (Fin n → K))).submoduleOf A) ≤ 1) ∧
      (⨆ S : {S : Finset H // Nat.card H < 2 * S.card}, ⨅ g ∈ S.1, A.map (ρ g : (Fin n → K)
          →ₗ[K] (Fin n → K))) = ⊥ ∧
      finrank K A = n - 1 := by
  classical
  refine ⟨(powAct n).comp H.subtype, hyp K n, ?_, ?_, finrank_hyp n hn⟩
  · intro g
    exact rank_le_one n (g : Kˣ) _ _ (map_hyp (K := K) n (g : Kˣ))
  · rw [eq_bot_iff]
    refine iSup_le fun S => ?_
    have hc : n ≤ (S.1.map ⟨fun g : H => (g : Kˣ), Subtype.val_injective⟩).card := by
      rw [Finset.card_map]
      have := S.2
      omega
    rw [← inf_eq_bot (K := K) n _ hc]
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, iInf_exists, iInf_and]
    refine le_iInf fun t => le_iInf fun g => le_iInf fun hg => le_iInf fun hgt => ?_
    subst hgt
    refine (iInf₂_le g hg).trans (le_of_eq ?_)
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply]
    exact map_hyp n (g : Kˣ)

/-- Over the complex numbers there is no bound that depends on `r` only, already for `r = 1`. -/
theorem question_negative_complex (c : ℕ) :
    ∃ (n : ℕ) (H : Type) (_ : Group H) (_ : Finite H) (ρ : H →* ((Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)))
        (A : Submodule ℂ (Fin n → ℂ)),
      (∀ g, Module.rank ℂ (A ⧸ (A.map (ρ g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))).submoduleOf A) ≤ 1) ∧
      ∀ A₀ : Submodule ℂ (Fin n → ℂ),
        A₀ = (⨆ S : {S : Finset H // Nat.card H < 2 * S.card}, ⨅ g ∈ S.1, A.map (ρ g : (Fin n → ℂ)
            →ₗ[ℂ] (Fin n → ℂ))) →
          c < finrank ℂ (A ⧸ A₀.submoduleOf A) := by
  have : NeZero (2 * (c + 2)) := ⟨by omega⟩
  have hcard : Nat.card (rootsOfUnity (2 * (c + 2)) ℂ) = 2 * (c + 2) := Complex.card_rootsOfUnity _
  obtain ⟨ρ, A, h1, h2, h3⟩ := question_negative (K := ℂ) (c + 2) (by omega) (rootsOfUnity (2 * (c
      + 2)) ℂ) (by omega)
  refine ⟨c + 2, rootsOfUnity (2 * (c + 2)) ℂ, inferInstance, inferInstance, ρ, A, h1, ?_⟩
  rintro A₀ rfl
  rw [h2]
  have e : (⊥ : Submodule ℂ (Fin (c + 2) → ℂ)).submoduleOf A = ⊥ := by
    ext x; simp [Submodule.submoduleOf]
  rw [e, (Submodule.quotEquivOfEqBot _ rfl).finrank_eq, h3]
  omega

end AlmostInvariant
