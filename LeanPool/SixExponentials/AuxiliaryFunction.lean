/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SixExponentials.Defs
public import Mathlib.NumberTheory.NumberField.House
import LeanPool.SixExponentials.HouseBounds
import LeanPool.SixExponentials.SiegelLemma
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

/-!
# The auxiliary function

Siegel's lemma over a number field with rational integer unknowns, and the exponential polynomial
with integer coefficients, not all zero, vanishing on a box of lattice points.

From `SixExponentials/Basic/exists_aux_expSum.lean` of `carlok/six-exponentials-lean`;
see `LeanPool.SixExponentials` for provenance.
-/

@[expose] public section

namespace SixExponentials.SX

/-!
# The auxiliary function of the six exponentials theorem

Let `K` be the number field containing the numbers `exp (x i * y j)`, and `n = [K : ℚ]`.
For each `M`, let `L` be least with `2 n M ^ l ≤ L ^ d`. We look for integers `p λ`, one for each
`λ` in the box `[0, L) ^ d`, not all zero, such that for every `m` in `[0, M) ^ l`
`∑_λ p λ ∏_{i,j} exp (x i * y j) ^ (λ i * m j) = 0`.
These are `M ^ l` linear equations in `L ^ d` unknowns, with coefficients in `K`.

A common denominator `b` of the numbers `exp (x i * y j)` makes each coefficient
`b ^ T ∏ exp (x i * y j) ^ (λ i * m j)`, with `T = d l L M`, an algebraic integer of house at most
`H ^ T`. Written in an integral basis of `K`, each equation becomes `n` equations over `ℤ` whose
entries are bounded by a constant times `H ^ T`, and there are still at least twice as many
unknowns as equations. Siegel's lemma gives a nonzero solution of size at most `L ^ d` times that
bound, which is `exp (O (L M))`. Finally
`exp (⟨λ, x⟩ ∑_j m j y j) = ∏_{i,j} exp (x i * y j) ^ (λ i * m j)`,
so the equations say that the exponential sum `SX.expSum x L p` vanishes at `SX.latticeSum y m`.
-/

open Complex

namespace AuxSiegel

open NumberField Transcendence

/-- Siegel's lemma over a number field, with rational integer unknowns. A system of linear
equations with algebraic integer coefficients of house at most `A`, with at least `2 [K : ℚ]`
times as many unknowns as equations, has a nonzero integer solution whose entries are at most
the number of unknowns times `max 1 (c_K A)`. The constant `c_K` is `[K : ℚ]` times the largest
entry of the inverse transpose of the matrix `(σ ω)`, `σ` running over the complex embeddings and
`ω` over an integral basis: it bounds the integer coordinates of an algebraic integer by its
house. The proof writes each equation in that basis and applies Siegel's lemma over `ℤ`. -/
theorem exists_int_kernel {K : Type*} [Field K] [NumberField K] [DecidableEq (K →+* ℂ)]
    {ρ κ : Type*} [Fintype ρ] [Fintype κ] (a : ρ → κ → K) (ha : ∀ k l, IsIntegral ℤ (a k l))
    {A : ℝ} (hA : ∀ k l, house (a k l) ≤ A) (hκ : 0 < Fintype.card κ)
    (hcard : 2 * (Fintype.card ρ * Module.finrank ℚ K) ≤ Fintype.card κ) :
    ∃ t : κ → ℤ, t ≠ 0 ∧ (∀ k, ∑ l, (t l : K) * a k l = 0) ∧
      ∀ l, |(t l : ℝ)| ≤ Fintype.card κ *
        max 1 (Module.finrank ℚ K * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖ * A) := by
  classical
  set c : ℝ := Module.finrank ℚ K * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖ with hc
  set bas := (RingOfIntegers.basis K).reindex (equivReindex K).symm with hbas
  -- the integer coordinates of an algebraic integer are bounded by `c` times its house
  have hrepr : ∀ (x : 𝓞 K) r, |((bas.repr x r : ℤ) : ℝ)| ≤ c * house (algebraMap (𝓞 K) K x) := by
    intro x r
    have h := house.basis_repr_norm_le_const_mul_house K x r
    simp only [Module.Basis.repr_reindex_apply, integralBasis_repr_apply,
      eq_intCast, Rat.cast_intCast, Complex.norm_intCast] at h
    simp only [hbas, Module.Basis.repr_reindex_apply]
    exact_mod_cast h
  have hc0 : 0 ≤ c := by positivity
  let a' : ρ → κ → 𝓞 K := fun k l => ⟨a k l, ha k l⟩
  -- one equation over `ℤ` for each equation and each coordinate
  obtain ⟨t, ht0, hker, hbd⟩ := siegel_entrywise
    (fun (kr : ρ × (K →+* ℂ)) l => bas.repr (a' kr.1 l) kr.2) hκ
    (by rw [Fintype.card_prod, Embeddings.card]; exact hcard) (le_max_left 1 (c * A))
    (fun kr l => (hrepr _ _).trans <|
      (mul_le_mul_of_nonneg_left (hA _ _) hc0).trans (le_max_right _ _))
  refine ⟨t, ht0, fun k => ?_, hbd⟩
  -- each equation holds coordinatewise, hence in `𝓞 K`, hence in `K`
  have h0 : bas.repr (∑ l, t l • a' k l) = 0 := by
    ext r
    simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
    rw [← hker (k, r)]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have h1 := congrArg (algebraMap (𝓞 K) K) (bas.repr.map_eq_zero_iff.mp h0)
  rw [map_sum, map_zero] at h1
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) h1
  rw [map_zsmul, zsmul_eq_mul]; rfl

end AuxSiegel

open NumberField Transcendence AuxSiegel in
open SX in
theorem exists_aux_expSum
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ i j, Complex.exp (x i * y j) ∈ K) :
    ∃ c : ℝ, 0 < c ∧ ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M →
      ∃ L : ℕ, 0 < L ∧ (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l ∧
        ∃ p : (Fin d → ℕ) → ℤ,
          (∃ lam ∈ SX.box d L, p lam ≠ 0) ∧
          (∀ lam, |(p lam : ℝ)| ≤ Real.exp (c * L * M)) ∧
          (∀ m : Fin l → ℕ, (∀ j, m j < M) → SX.expSum x L p (SX.latticeSum y m) = 0) := by
  classical
  have : NumberField K := ⟨⟩
  obtain ⟨hd, hl⟩ : 0 < d ∧ 0 < l := by
    constructor <;> (apply Nat.pos_of_ne_zero; rintro rfl; simp at hdl)
  set n := Module.finrank ℚ K with hn
  have hn1 : 1 ≤ n := Module.finrank_pos
  -- the numbers `exp (x i * y j)` in `K`: a denominator `b` and a house bound `H` for monomials
  set V : K →+* ℂ := (IntermediateField.val K).toRingHom
  set θ : Fin d × Fin l → K := fun ij => ⟨Complex.exp (x ij.1 * y ij.2), hK ij.1 ij.2⟩
  obtain ⟨b, hb0, -, H, hH1, hbH⟩ := exists_denom_house_monomial_le θ
  -- the constant of Siegel's lemma over `K`, and the constant `c`
  set W : ℝ := max 1 ((n : ℝ) * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖)
  have hWH : 1 ≤ W * H := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hH1
  have hlog : 0 ≤ Real.log (W * H) := Real.log_nonneg hWH
  set c : ℝ := 2 ^ d * (2 * n) + d + d * l * Real.log (W * H) with hc
  refine ⟨c, by positivity, 1, fun M hM => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  -- `L` is least with `2 n M ^ l ≤ L ^ d`
  have hex : ∃ L : ℕ, 2 * n * M ^ l ≤ L ^ d := ⟨2 * n * M ^ l, Nat.le_self_pow hd.ne' _⟩
  set L := Nat.find hex
  have hL : 2 * n * M ^ l ≤ L ^ d := Nat.find_spec hex
  have hMl : 1 ≤ M ^ l := Nat.one_le_pow _ _ hM
  have hL0 : 0 < L := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_pow hd.ne'] at hL; nlinarith
  have hLub : L ^ d ≤ 2 ^ d * (2 * n * M ^ l) := by
    rcases Nat.lt_or_ge L 2 with h | h
    · rw [show L = 1 by omega, one_pow]
      exact le_trans (by nlinarith) (Nat.le_mul_of_pos_left _ (by positivity))
    · have hmin : ¬ 2 * n * M ^ l ≤ (L - 1) ^ d := Nat.find_min hex (by omega)
      calc L ^ d ≤ (2 * (L - 1)) ^ d := Nat.pow_le_pow_left (by omega) d
        _ = 2 ^ d * (L - 1) ^ d := mul_pow _ _ _
        _ ≤ 2 ^ d * (2 * n * M ^ l) := Nat.mul_le_mul_left _ (by omega)
  have hLc : (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l := by
    have h1 : ((L ^ d : ℕ) : ℝ) ≤ ((2 ^ d * (2 * n * M ^ l) : ℕ) : ℝ) := by exact_mod_cast hLub
    push_cast at h1
    calc (L : ℝ) ^ d ≤ 2 ^ d * (2 * n) * (M : ℝ) ^ l := by linarith
      _ ≤ c * (M : ℝ) ^ l := by
        gcongr; rw [hc]; have := mul_nonneg (by positivity : (0 : ℝ) ≤ d * l) hlog; linarith
  -- the system: one equation for each `m`, one unknown for each `λ` in the box
  set T := d * l * L * M with hT
  have hE : ∀ (m : Fin l → Fin M) (lam : ↥(SX.box d L)),
      ∑ ij : Fin d × Fin l, lam.1 ij.1 * (m ij.2 : ℕ) ≤ T := fun m lam => by
    calc _ ≤ ∑ _ij : Fin d × Fin l, L * M := Finset.sum_le_sum fun ij _ =>
          Nat.mul_le_mul (SX.mem_box.1 lam.2 ij.1).le (m ij.2).2.le
      _ = T := by simp [hT, Fintype.card_prod]; ring
  have hcardρ : Fintype.card (Fin l → Fin M) = M ^ l := by simp
  have hcardκ : Fintype.card ↥(SX.box d L) = L ^ d := by
    rw [Fintype.card_coe]; simp [SX.box]
  obtain ⟨t, ht0, hker, hbd⟩ := exists_int_kernel
    (fun (m : Fin l → Fin M) (lam : ↥(SX.box d L)) =>
      b ^ T * ∏ ij : Fin d × Fin l, θ ij ^ (lam.1 ij.1 * (m ij.2 : ℕ)))
    (fun m lam => (hbH _ T (hE m lam)).1) (fun m lam => (hbH _ T (hE m lam)).2)
    (by rw [hcardκ]; positivity) (by rw [hcardρ, hcardκ, ← hn]; linarith [hL])
  -- the height: `L ^ d max 1 (c_K H ^ T) ≤ exp (d L) (W H) ^ T ≤ exp (c L M)`
  have hT1 : T ≠ 0 := by positivity
  have hheight : ∀ lam, |(t lam : ℝ)| ≤ Real.exp (c * L * M) := by
    intro lam
    refine (hbd lam).trans ?_
    rw [hcardκ, ← hn]
    push_cast
    have h1 : max 1 ((n : ℝ) * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖ * H ^ T)
        ≤ (W * H) ^ T := by
      rw [mul_pow]
      refine max_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_left _ _))
        (one_le_pow₀ hH1)) ?_
      exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans
        (le_self_pow₀ (le_max_left _ _) hT1)) (by positivity)
    have h2 : (L : ℝ) ^ d ≤ Real.exp (d * L) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith [Real.add_one_le_exp (L : ℝ)]) d
    have h3 : (W * H) ^ T = Real.exp (T * Real.log (W * H)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    have h4 : (d : ℝ) * L + T * Real.log (W * H) ≤ c * L * M := by
      have hL1 : (0 : ℝ) ≤ L := L.cast_nonneg
      have h5 : (d : ℝ) * L ≤ d * L * M := le_mul_of_one_le_right (by positivity) hM1
      have h6 : (0 : ℝ) ≤ 2 ^ d * (2 * n) * L * M := by positivity
      rw [hc, hT]; push_cast; nlinarith
    calc (L : ℝ) ^ d * max 1 ((n : ℝ) * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖ * H ^ T)
        ≤ Real.exp (d * L) * Real.exp (T * Real.log (W * H)) :=
          h3 ▸ mul_le_mul h2 h1 (by positivity) (by positivity)
      _ ≤ Real.exp (c * L * M) := by rw [← Real.exp_add]; exact Real.exp_le_exp.2 h4
  -- `p` is `t` on the box and zero outside it
  set p : (Fin d → ℕ) → ℤ := fun lam => if h : lam ∈ SX.box d L then t ⟨lam, h⟩ else 0
  have hpt : ∀ lam : ↥(SX.box d L), p lam.1 = t lam := fun lam => dite_eq_left lam.2
  refine ⟨L, hL0, hLc, p, ?_, fun lam => ?_, fun m hm => ?_⟩
  · obtain ⟨lam, hlam⟩ := Function.ne_iff.1 ht0
    exact ⟨lam.1, lam.2, by rw [hpt]; simpa using hlam⟩
  · by_cases h : lam ∈ SX.box d L
    · simpa only [hpt ⟨lam, h⟩] using hheight ⟨lam, h⟩
    · rw [show p lam = 0 from dite_eq_right h, Int.cast_zero, abs_zero]; exact (Real.exp_pos _).le
  · -- the equation of index `m`, divided by `b ^ T` and read in `ℂ`
    have h2 : ∑ lam : ↥(SX.box d L), (t lam : K) * ∏ ij : Fin d × Fin l,
        θ ij ^ (lam.1 ij.1 * m ij.2) = 0 := by
      have h1 := hker (fun j => ⟨m j, hm j⟩)
      simp_rw [mul_left_comm _ (b ^ T), ← Finset.mul_sum] at h1
      exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hb0)
    have h3 := congrArg V h2
    simp only [map_sum, map_mul, map_intCast, map_prod, map_pow, map_zero] at h3
    rw [SX.expSum, ← Finset.sum_coe_sort (SX.box d L)]
    refine Eq.trans (Finset.sum_congr rfl fun lam _ => ?_) h3
    rw [hpt, SX.exp_expExponent_mul_latticeSum, Fintype.prod_prod_type]
    rfl

end SixExponentials.SX
