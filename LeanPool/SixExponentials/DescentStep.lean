/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SixExponentials.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import LeanPool.SixExponentials.GridEstimate
import LeanPool.SixExponentials.HouseBounds
import LeanPool.SixExponentials.Liouville
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

/-!
# Extending the zeros

If the auxiliary function vanishes on one box of lattice points, the Cauchy estimate played against
Liouville's inequality in the number field makes it vanish on the next box.

From `SixExponentials/Basic/descent_step.lean` of `carlok/six-exponentials-lean`;
see `LeanPool.SixExponentials` for provenance.
-/

@[expose] public section

namespace SixExponentials.SX

open Complex

open NumberField

/-!
The descent step of the six exponentials theorem.

Suppose `F = expSum x L p` vanishes at the lattice points `∑ m j • y j` with every `m j < N`,
but not at some `w = ∑ m j • y j` with every `m j ≤ N`.
* Upper bound. `F` is an exponential polynomial with coefficients `p λ` and frequencies
  `⟨λ, x⟩` of modulus `≤ L X`, `X = ∑ |x i|`. The `N ^ l` zeros are distinct because the `y j` are
  ℚ-linearly independent, and the grid estimate with radius parameter `u = 3` gives
  `|F w| ≤ 2 · 2^(-N^l) · B e^{4 X (2Y + 1) L N}`, `Y = ∑ |y j|`, where `B = L^d e^{c L M}`
  bounds `∑ |p λ|`.
* Lower bound. `F w` is the image of `β = ∑ p λ ∏ θ_ij ^ (λ i m j)`, `θ_ij = exp (x i y j) ∈ K`.
  With a common denominator `b` of the `θ_ij`, `b^E β` (`E = d l L N`) is a nonzero algebraic
  integer of house `≤ B G^E`, and Liouville's inequality gives
  `1 ≤ G^E |F w| (B G^E)^([K:ℚ] - 1)`.
* Together, `2^(N^l) ≤ exp (C L N)`. With `L^d ≤ c M^l ≤ c N^l` and `d l ≥ d + l + 1` this forces
  `N (log 2)^d ≤ C^d c`, which fails once `N ≥ M ≥ M₀`.
-/

theorem descent_step
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ i j, Complex.exp (x i * y j) ∈ K)
    (c : ℝ) (hc : 0 < c) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ L : ℕ, 0 < L → (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l →
      ∀ p : (Fin d → ℕ) → ℤ, (∀ lam, |(p lam : ℝ)| ≤ Real.exp (c * L * M)) →
        ∀ N : ℕ, M ≤ N →
          (∀ m : Fin l → ℕ, (∀ j, m j < N) → SX.expSum x L p (SX.latticeSum y m) = 0) →
          (∀ m : Fin l → ℕ, (∀ j, m j < N + 1) → SX.expSum x L p (SX.latticeSum y m) = 0) := by
  classical
  have : NumberField K := {}
  set rk := Module.finrank ℚ K with hrk
  have hrk1 : 1 ≤ rk := Module.finrank_pos
  set σ : K →+* ℂ := K.val.toRingHom
  -- the numbers `exp (x i * y j)` as elements of `K`, a common denominator `b` and a house bound
  set θ : Fin d × Fin l → K := fun ij => ⟨Complex.exp (x ij.1 * y ij.2), hK ij.1 ij.2⟩ 
  obtain ⟨b, hb0, -, H, hH1, hbH⟩ := Transcendence.exists_denom_house_monomial_le θ
  set G : ℝ := max 1 (house b) * H
  have hHG : H ≤ G := le_mul_of_one_le_left (by positivity) (le_max_left 1 (house b))
  have hbG : house b ≤ G :=
    (le_max_right 1 (house b)).trans (le_mul_of_one_le_right (by positivity) hH1)
  have hG1 : 1 ≤ G := hH1.trans hHG
  set X := ∑ i, ‖x i‖
  set Y := ∑ j, ‖y j‖
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  set C : ℝ := 1 + rk * (d + c) + 4 * X * (2 * Y + 1) + d * l * rk * Real.log G with hC
  have hC0 : 0 ≤ C := by have := Real.log_nonneg hG1; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨⌈C ^ d * c / Real.log 2 ^ d⌉₊ + 1, fun M hM L hL hLc p hp N hMN hvan m hm => ?_⟩
  by_contra hne
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_pos _).trans_le (hM.trans hMN)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set B : ℝ := (L : ℝ) ^ d * Real.exp (c * L * M) with hB
  have hB1 : 1 ≤ B :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (Real.one_le_exp (by positivity))
  have hpB : ∑ lam ∈ SX.box d L, |(p lam : ℝ)| ≤ B := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun lam _ => hp lam).trans_eq ?_
    simp [SX.box, Fintype.card_piFinset, hB]
  -- the analytic upper bound: the grid estimate with `u = 3`
  have hup : ‖SX.expSum x L p (SX.latticeSum y m)‖
      ≤ 2 * (1 / 2) ^ (N ^ l) * (B * Real.exp (L * X * (4 * N * (2 * Y + 1)))) := by
    have h := Transcendence.expPoly_grid_estimate y hy (SX.box d L) (fun lam => (p lam : ℂ))
      (SX.expExponent x) (fun _ => 0) (SX.expSum x L p) (fun z => by simp [SX.expSum]) (L * X) 0
      (fun lam hlam => ?_) (fun _ _ => le_rfl) (fun _ => N) (fun _ => N + 1) (fun _ => N.le_succ) 1
      (fun m' hm' i hi => ?_) 3 (4 * N * (2 * Y + 1)) (by norm_num) ?_ m hm 0
    · simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, mul_one,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, Complex.norm_intCast] at h
      norm_num at h
      refine h.trans ?_
      gcongr
    · rw [SX.mem_box] at hlam
      refine (norm_sum_le _ _).trans
        ((Finset.sum_le_sum fun i _ => ?_).trans_eq (Finset.mul_sum _ _ _).symm)
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (hlam i).le) (norm_nonneg _)
    · rw [Nat.lt_one_iff.1 hi, iteratedDeriv_zero]; exact hvan m' hm'
    · rw [← Finset.mul_sum]; push_cast; nlinarith
  -- the arithmetic lower bound: the value lies in `K` and Liouville's inequality applies
  set E : ℕ := d * l * L * N with hE
  set β : K := ∑ lam ∈ SX.box d L, (p lam : K) * ∏ ij, θ ij ^ (lam ij.1 * m ij.2) with hβ
  have heE : ∀ lam ∈ SX.box d L, ∑ ij : Fin d × Fin l, lam ij.1 * m ij.2 ≤ E := fun lam hlam =>
    (Finset.sum_le_card_nsmul _ _ (L * N) fun ij _ => Nat.mul_le_mul ((SX.mem_box.1 hlam) ij.1).le
      (Nat.lt_succ_iff.1 (hm ij.2))).trans_eq (by simp [hE]; ring)
  have hσβ : σ β = SX.expSum x L p (SX.latticeSum y m) := by
    rw [hβ, SX.expSum, map_sum]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [map_mul, map_intCast, map_prod, SX.exp_expExponent_mul_latticeSum, Fintype.prod_prod_type]
    rfl
  have hβ0 : β ≠ 0 := fun h => hne (by rw [← hσβ, h, map_zero])
  have hδ : b ^ E * β =
      ∑ lam ∈ SX.box d L, (p lam : K) * (b ^ E * ∏ ij, θ ij ^ (lam ij.1 * m ij.2)) := by
    rw [hβ, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hint : IsIntegral ℤ (((1 : ℤ) : K) * (b ^ E * β)) := by
    rw [Int.cast_one, one_mul, hδ]
    exact IsIntegral.sum _ fun lam hlam =>
      (isIntegral_algebraMap (x := p lam)).mul (hbH _ E (heE lam hlam)).1
  have hhouse : house (b ^ E * β) ≤ B * G ^ E := by
    rw [hδ]
    refine (house_sum_le_sum_house _ _).trans
      ((Finset.sum_le_sum (g := fun lam => |(p lam : ℝ)| * G ^ E)
      fun lam hlam => (house_mul_le _ _).trans ?_).trans ?_)
    · rw [house_intCast, Int.cast_abs]
      exact mul_le_mul_of_nonneg_left ((hbH _ E (heE lam hlam)).2.trans (by gcongr)) (abs_nonneg _)
    · rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hpB (by positivity)
  have hliou :=
    Transcendence.liouville_house (mul_ne_zero (pow_ne_zero E hb0) hβ0) one_ne_zero hint σ
  rw [Int.cast_one, abs_one, one_pow, one_mul, map_mul, map_pow, norm_mul, norm_pow, hσβ] at hliou
  -- combining the two bounds: `2 ^ (N ^ l) ≤ exp (C L N)`
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hrk1
  have hLN : (1 : ℝ) ≤ L * N := one_le_mul_of_one_le_of_one_le hL1 hN1
  have hBexp : B ≤ Real.exp ((d + c) * (L * N)) := by
    have h1 : (L : ℝ) ≤ Real.exp (L * N) :=
      (by linarith [Real.add_one_le_exp ((L : ℝ) - 1)] : (L : ℝ) ≤ Real.exp (L - 1)).trans
        (Real.exp_le_exp.2 (by nlinarith))
    have h2 : c * L * M ≤ c * (L * N) := by
      rw [mul_assoc]; gcongr
    rw [add_mul, Real.exp_add, hB, Real.exp_nat_mul]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) h1 d) (Real.exp_le_exp.2 h2) (by positivity)
      (by positivity)
  have hkey : (2 : ℝ) ^ (N ^ l) ≤ Real.exp (C * (L * N)) := by
    have hσb : ‖σ b‖ ^ E ≤ G ^ E :=
      pow_le_pow_left₀ (norm_nonneg _) ((norm_embedding_le_house b σ).trans hbG) E
    have hG0 : 0 ≤ G := by linarith
    have hB0 : 0 ≤ B := by linarith
    have h1 := hliou.trans (mul_le_mul (mul_le_mul hσb hup (norm_nonneg _) (pow_nonneg hG0 E))
      (pow_le_pow_left₀ (house_nonneg _) hhouse _) (pow_nonneg (house_nonneg _) _) (by positivity))
    rw [← hrk, hk, Nat.add_sub_cancel_left] at h1
    calc (2 : ℝ) ^ (N ^ l) ≤ 2 ^ (N ^ l) * (G ^ E * (2 * (1 / 2) ^ (N ^ l) *
          (B * Real.exp (L * X * (4 * N * (2 * Y + 1))))) * (B * G ^ E) ^ k) := by
          simpa using mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 ^ (N ^ l))
      _ = 2 * B ^ (1 + k) * G ^ (E * (1 + k)) * Real.exp (L * X * (4 * N * (2 * Y + 1))) := by
          rw [mul_pow B (G ^ E) k, ← pow_mul G E k, one_div, inv_pow]; field_simp; ring
      _ ≤ Real.exp (L * N) * Real.exp ((d + c) * (L * N)) ^ (1 + k) *
          Real.exp (G.log) ^ (E * (1 + k)) * Real.exp (L * X * (4 * N * (2 * Y + 1))) := by
          rw [Real.exp_log (by positivity)]
          gcongr
          exact (by linarith [Real.add_one_le_exp 1] : (2 : ℝ) ≤ Real.exp 1).trans
            (Real.exp_le_exp.2 hLN)
      _ = Real.exp (C * (L * N)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add,
            ← Real.exp_add,
            hC, hk, hE]
          push_cast; ring_nf
  -- the endgame: `N ^ l log 2 ≤ C L N` and `L ^ d ≤ c N ^ l` force `N (log 2) ^ d ≤ C ^ d c`
  have h2 : (N : ℝ) ^ l * Real.log 2 ≤ C * (L * N) := by
    have := Real.log_le_log (by positivity) hkey
    rwa [Real.log_pow, Real.log_exp, Nat.cast_pow] at this
  have hLc' : (L : ℝ) ^ d ≤ c * N ^ l := hLc.trans (by gcongr)
  have hNd : (N : ℝ) ^ (l + d) * N ≤ N ^ (l * d) := by
    rw [← pow_succ]; exact pow_le_pow_right₀ hN1 (by rw [Nat.mul_comm]; omega)
  have hend : (N : ℝ) * Real.log 2 ^ d ≤ C ^ d * c := by
    refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < N ^ (l + d))
    calc (N : ℝ) ^ (l + d) * (N * Real.log 2 ^ d) = (N ^ (l + d) * N) * Real.log 2 ^ d := by ring
      _ ≤ N ^ (l * d) * Real.log 2 ^ d := by gcongr
      _ = ((N : ℝ) ^ l * Real.log 2) ^ d := by rw [mul_pow, ← pow_mul]
      _ ≤ (C * (L * N)) ^ d := by gcongr
      _ = C ^ d * (L : ℝ) ^ d * (N : ℝ) ^ d := by rw [mul_pow, mul_pow, ← mul_assoc]
      _ ≤ C ^ d * (c * (N : ℝ) ^ l) * (N : ℝ) ^ d := by gcongr
      _ = (N : ℝ) ^ (l + d) * (C ^ d * c) := by ring
  have hlt : C ^ d * c / Real.log 2 ^ d < N := by
    have h3 : ((⌈C ^ d * c / Real.log 2 ^ d⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hM.trans hMN
    push_cast at h3
    linarith [Nat.le_ceil (C ^ d * c / Real.log 2 ^ d)]
  rw [div_lt_iff₀ (by positivity)] at hlt
  linarith

end SixExponentials.SX
