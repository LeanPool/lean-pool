/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FoldUniversal
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.LaurentSeries

import LeanPool.HyperellipticCurves.ForMathlib.HahnSeries
import Mathlib.Tactic.Ring

/-!
# The cusp descent: separation and the correction budget at the common rates

The content of `lem:cusp-descent`, in its common-rate form: fix a degree bound `D` for the finitely
many cuspidal numerators and a digit base `B > D`, and use the *one* rate vector
`ñᵢ = D·B^(g+1) + B^(i+1)` (`ChabautyColeman.descRate`) for every fold quantity.

* **Separation** (`ChabautyColeman.orderTop_aeval_descRate_le`, with the digit lemma
  `ChabautyColeman.digits_eq_of_sum_eq` at its core): a nonzero homogeneous polynomial of
  degree `d ≤ D` evaluated at `tᵢ = s^(-ñᵢ)` is nonzero of valuation at most `-d·M`
  (`M = D·B^(g+1)`) — homogeneity makes the `M`-part of all monomial valuations common,
  and the base-`B` digits below `B` land distinct monomials on distinct valuations.
* **The correction budget** (`ChabautyColeman.aeval_family_ne_zero`): at the
  all-at-infinity family — `x`-coordinates exactly `s^(-2ñᵢ)`, `y`-coordinates
  `s^(-Nñᵢ)` times one-units of depth `2ñᵢ` (the shape delivered by
  `ChabautyColeman.exists_infinityPoint`), curve coefficients of nonnegative order — the
  value of a universal weighted-homogeneous quantity deviates from its cuspidal value by
  terms of valuation at least `-d·M + M`, strictly above the separation window. Hence a
  nonzero cuspidal numerator forces a nonzero family value; no atom certificates and no
  leading-coefficient analysis enter.

The one-unit toolkit (`ChabautyColeman.le_orderTop_mul_sub_one` and friends) and the
elementary order bounds (`ChabautyColeman.le_orderTop_mul`,
`ChabautyColeman.le_orderTop_pow_of_le`) support the budget.
-/

@[expose] public section

open MvPolynomial HahnSeries

namespace ChabautyColeman

/-! ### Digit arithmetic -/

/-- **Bounded-digit base-`B` expansions are unique**: on digit vectors below `B`, the
base-`B` sum is injective. Mathlib proves this for lists (`Nat.ofDigits_inj_of_len_eq`), but
only for `1 < b`, and transporting it to `Fin`-tuples through `Nat.ofDigits_eq_sum_mapIdx`
costs more bookkeeping than the induction below. -/
theorem digits_eq_of_sum_eq {B g : ℕ} {c c' : Fin g → ℕ} (hc : ∀ i, c i < B)
    (hc' : ∀ i, c' i < B)
    (h : ∑ i, c i * B ^ (i : ℕ) = ∑ i, c' i * B ^ (i : ℕ)) : c = c' := by
  induction g with
  | zero => exact funext fun i ↦ i.elim0
  | succ g ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
    have hfac : ∀ b : Fin g → ℕ,
        (∑ i : Fin g, b i * B ^ (i.succ : ℕ)) = B * ∑ i : Fin g, b i * B ^ (i : ℕ) := by
      intro b
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [Fin.val_succ, pow_succ]; ring
    rw [hfac, hfac] at h
    simp only [Fin.val_zero, pow_zero, mul_one] at h
    have hB : 0 < B := (c 0).zero_le.trans_lt (hc 0)
    -- extract the lowest digit by reduction mod `B`
    have h0 : c 0 = c' 0 := by
      have hm := congrArg (· % B) h
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hc 0), Nat.mod_eq_of_lt (hc' 0)]
        using hm
    rw [h0] at h
    have hS := Nat.eq_of_mul_eq_mul_left hB (Nat.add_left_cancel h)
    have htail := ih (c := fun i ↦ c i.succ) (c' := fun i ↦ c' i.succ)
      (fun i ↦ hc i.succ) (fun i ↦ hc' i.succ) hS
    exact funext fun i ↦ Fin.cases h0 (fun j ↦ congrFun htail j) i

/-! ### The common rates -/

/-- **The common descent rates** of `lem:cusp-descent`: `ñᵢ = D·B^(g+1) + B^(i+1)`, where
`D` bounds the degrees of the cuspidal numerators and `B > D` is the digit base. The
`M = D·B^(g+1)` part is common to all rates; the `B`-power part separates the variables. -/
def descRate (D B g i : ℕ) : ℕ := D * B ^ (g + 1) + B ^ (i + 1)

theorem le_descRate (D B g i : ℕ) : D * B ^ (g + 1) ≤ descRate D B g i :=
  Nat.le_add_right ..

theorem descRate_le {B i g : ℕ} (hB : 1 ≤ B) (hi : i < g) (D : ℕ) :
    descRate D B g i ≤ D * B ^ (g + 1) + B ^ g :=
  Nat.add_le_add_left (Nat.pow_le_pow_right hB hi) _

section Weights

variable {K : Type*} [Field K] {g : ℕ}

/-- The all-`1` weight of a monomial is the sum of its digits. -/
private theorem weight_one_apply (m : Fin g →₀ ℕ) :
    Finsupp.weight (fun _ ↦ (1 : ℤ)) m = ∑ i, (m i : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp

/-- The universal weight of a monomial, split by variable class. -/
private theorem weight_univWt_apply (m : (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) →₀ ℕ) :
    Finsupp.weight (univWt g) m
      = ∑ i, (m (.inl i) : ℤ) * 2
        + (∑ i, (m (.inr (.inl i)) : ℤ) * (2 * g + 1)
          + ∑ r : Fin (2 * g + 1),
              (m (.inr (.inr r)) : ℤ) * (2 * (2 * g + 1 - ((r : ℕ) : ℤ)))) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  simp only [univWt_inl, univWt_inr_inl, univWt_inr_inr, nsmul_eq_mul]

end Weights

/-! ### Separation: the cuspidal value at the common rates -/

section Separation

variable {K : Type*} [Field K] {g : ℕ}

private theorem prod_single_one {ι : Type*} (s : Finset ι) (b : ι → ℤ) :
    ∏ i ∈ s, (single (b i) 1 : LaurentSeries K) = single (∑ i ∈ s, b i) 1 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s his ih =>
    rw [Finset.prod_cons, Finset.sum_cons, ih, single_mul_single, one_mul]

private theorem pow_single_one (b : ℤ) (k : ℕ) :
    (single b 1 : LaurentSeries K) ^ k = single (k * b) 1 := by
  rw [single_pow, one_pow, nsmul_eq_mul]

private theorem prod_pow_single_one {ι : Type*} (s : Finset ι) (b : ι → ℤ) (k : ι → ℕ) :
    ∏ i ∈ s, (single (b i) 1 : LaurentSeries K) ^ k i
      = single (∑ i ∈ s, (k i : ℤ) * b i) 1 := by
  rw [← prod_single_one]
  exact Finset.prod_congr rfl fun i _ ↦ pow_single_one ..

/-- Weighted sums against a common negated rate factor out that factor. -/
private theorem sum_mul_neg_mul (C : ℤ) (k : Fin g → ℕ) (r : Fin g → ℤ) :
    ∑ i, (k i : ℤ) * -(C * r i) = -(C * ∑ i, (k i : ℤ) * r i) := by
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The value of a multivariate polynomial at Laurent monomials, as a sum of monomials. -/
private theorem aeval_single_eq (n : Fin g → ℤ) (P : MvPolynomial (Fin g) K) :
    MvPolynomial.aeval (fun i ↦ (single (n i) 1 : LaurentSeries K)) P
      = ∑ m ∈ P.support, single (∑ i, (m i : ℤ) * n i) (P.coeff m) := by
  conv_lhs => rw [P.as_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    prod_pow_single_one, LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
    single_mul_single, zero_add, mul_one]

/-- **Separation** (`lem:cusp-descent`(a)): the value of a nonzero homogeneous polynomial
of degree `d ≤ D` at the common-rate Laurent monomials `t_i = s^(-ñ_i)` is nonzero of
valuation at most `-d·M` — by homogeneity the `M`-part of the valuations is common to all
monomials, and bounded-digit base-`B` expansions separate the rest. -/
theorem orderTop_aeval_descRate_le {P : MvPolynomial (Fin g) K} {d : ℤ} {D B : ℕ}
    (hP : P.IsWeightedHomogeneous (fun _ ↦ 1) d) (hP0 : P ≠ 0) (hdD : d ≤ D) (hDB : D < B) :
    (MvPolynomial.aeval (fun i : Fin g ↦ (single (-(descRate D B g i : ℤ)) 1
      : LaurentSeries K)) P).orderTop ≤ ((-(d * (D * B ^ (g + 1))) : ℤ) : WithTop ℤ) := by
  classical
  set M : ℕ := D * B ^ (g + 1) with hM
  have hwt : ∀ m ∈ P.support, ∑ i, (m i : ℤ) = d := fun m hm ↦ by
    rw [← weight_one_apply]
    exact hP (mem_support_iff.mp hm)
  have hdig : ∀ m ∈ P.support, ∀ i, m i < B := by
    intro m hm i
    lia [hwt m hm ▸ Finset.single_le_sum (f := fun i ↦ (m i : ℤ)) (fun _ _ ↦ by positivity)
      (Finset.mem_univ i)]
  set S : (Fin g →₀ ℕ) → ℕ := fun m ↦ ∑ i, m i * B ^ ((i : ℕ) + 1) with hS
  have hinj : ∀ m ∈ P.support, ∀ m' ∈ P.support, S m = S m' → m = m' := by
    intro m hm m' hm' hSS
    have h2 : ∀ c : Fin g →₀ ℕ, S c = (∑ i, c i * B ^ (i : ℕ)) * B := fun c ↦ by
      rw [hS, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [pow_succ]; ring
    rw [h2, h2] at hSS
    have h3 := digits_eq_of_sum_eq (hdig m hm) (hdig m' hm')
      (Nat.eq_of_mul_eq_mul_right (by lia) hSS)
    exact DFunLike.coe_injective h3
  have hexp : ∀ m ∈ P.support,
      ∑ i, (m i : ℤ) * -(descRate D B g i : ℤ) = -(d * M + S m) := by
    intro m hm
    have h2 : ∀ i : Fin g, (m i : ℤ) * -(descRate D B g i : ℤ)
        = -((m i : ℤ) * M) + -((m i : ℤ) * B ^ ((i : ℕ) + 1)) := fun i ↦ by
      rw [descRate, hM]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun i _ ↦ h2 i, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul, hwt m hm]
    simp only [hS]
    push_cast
    ring
  rw [aeval_single_eq, Finset.sum_congr rfl fun m hm ↦ by rw [hexp m hm]]
  obtain ⟨m₀, hm₀, hmax⟩ := P.support.exists_max_image S (support_nonempty.mpr hP0)
  rw [← Finset.add_sum_erase _ _ hm₀,
    orderTop_add_sum_eq (V := -(d * M + S m₀)) (orderTop_single (mem_support_iff.mp hm₀))
      fun m hm ↦ ?_]
  · rw [WithTop.coe_le_coe]
    lia
  · rw [orderTop_single (mem_support_iff.mp (Finset.mem_of_mem_erase hm))]
    rw [WithTop.coe_lt_coe]
    lia [lt_of_le_of_ne (hmax m (Finset.mem_of_mem_erase hm)) fun he ↦
      Finset.ne_of_mem_erase hm (hinj m (Finset.mem_of_mem_erase hm) m₀ hm₀ he)]

end Separation

/-! ### One-unit bounds -/

section OneUnit

variable {K : Type*} [CommRing K] {μ : ℤ}

/-- A product of one-units is a one-unit at the smaller depth. -/
theorem le_orderTop_mul_sub_one {u v : LaurentSeries K} (hμ : 0 ≤ μ)
    (hu : (μ : WithTop ℤ) ≤ (u - 1).orderTop) (hv : (μ : WithTop ℤ) ≤ (v - 1).orderTop) :
    (μ : WithTop ℤ) ≤ (u * v - 1).orderTop := by
  have hid : u * v - 1 = (u - 1) * (v - 1) + ((u - 1) + (v - 1)) := by ring
  rw [hid]
  refine le_trans (le_min ?_ (le_trans (le_min hu hv) min_orderTop_le_orderTop_add))
    min_orderTop_le_orderTop_add
  refine le_trans ?_ orderTop_add_le_mul
  calc (μ : WithTop ℤ) = μ + (0 : ℤ) := by rw [WithTop.coe_zero, add_zero]
    _ ≤ (u - 1).orderTop + (v - 1).orderTop :=
        add_le_add hu (le_trans (mod_cast hμ) hv)

theorem le_orderTop_pow_sub_one {u : LaurentSeries K} (hμ : 0 ≤ μ)
    (hu : (μ : WithTop ℤ) ≤ (u - 1).orderTop) (k : ℕ) :
    (μ : WithTop ℤ) ≤ (u ^ k - 1).orderTop := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; exact le_orderTop_mul_sub_one hμ ih hu

theorem le_orderTop_prod_sub_one {ι : Type*} {s : Finset ι} {u : ι → LaurentSeries K}
    (hμ : 0 ≤ μ) (hu : ∀ i ∈ s, (μ : WithTop ℤ) ≤ (u i - 1).orderTop) :
    (μ : WithTop ℤ) ≤ (∏ i ∈ s, u i - 1).orderTop := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s his ih =>
    rw [Finset.prod_cons]
    exact le_orderTop_mul_sub_one hμ (hu i (Finset.mem_cons_self ..))
      (ih fun j hj ↦ hu j (Finset.mem_cons_of_mem hj))

end OneUnit

/-! ### Elementary order bounds -/

section OrderBounds

variable {K : Type*} [CommRing K]

/-- Order bounds on factors add up. -/
theorem le_orderTop_mul {x y : LaurentSeries K} {a b : ℤ}
    (hx : (a : WithTop ℤ) ≤ x.orderTop) (hy : (b : WithTop ℤ) ≤ y.orderTop) :
    ((a + b : ℤ) : WithTop ℤ) ≤ (x * y).orderTop := by
  rw [WithTop.coe_add]
  exact le_trans (add_le_add hx hy) orderTop_add_le_mul

/-- Order bounds on a base persist under powers. -/
theorem le_orderTop_pow_of_le [Nontrivial K] {x : LaurentSeries K} {a : ℤ}
    (h : (a : WithTop ℤ) ≤ x.orderTop) (k : ℕ) :
    ((k * a : ℤ) : WithTop ℤ) ≤ (x ^ k).orderTop := by
  induction k with
  | zero => simp [orderTop_one]
  | succ k ih =>
    rw [pow_succ]
    exact (WithTop.coe_inj.mpr (by push_cast; ring)).le.trans (le_orderTop_mul ih h)

end OrderBounds

/-! ### The correction budget and the family value -/

section Budget

variable {K : Type*} [Field K] {g : ℕ}

/-- Composing the cuspidal specialization with the common-rate Laurent monomials gives
the all-at-infinity cusp values of the coordinates. -/
private theorem aeval_cuspSpec_descRate (D B : ℕ)
    (P : MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) K) :
    MvPolynomial.aeval (fun i : Fin g ↦
        (single (-(descRate D B g i : ℤ)) 1 : LaurentSeries K))
      (MvPolynomial.aeval (cuspSpec K g) P)
      = MvPolynomial.aeval (Sum.elim (fun i : Fin g ↦
            (single (-(2 * (descRate D B g i : ℤ))) 1 : LaurentSeries K))
          (Sum.elim (fun i : Fin g ↦ single (-((2 * g + 1) * (descRate D B g i : ℤ))) 1)
            fun _ : Fin (2 * g + 1) ↦ 0)) P := by
  refine (aeval_bind₁ _ (cuspSpec K g) P).trans ?_
  have hfun : (fun s ↦ MvPolynomial.aeval (fun i : Fin g ↦
        (single (-(descRate D B g i : ℤ)) 1 : LaurentSeries K)) (cuspSpec K g s))
      = Sum.elim (fun i : Fin g ↦
          (single (-(2 * (descRate D B g i : ℤ))) 1 : LaurentSeries K))
        (Sum.elim (fun i : Fin g ↦ single (-((2 * g + 1) * (descRate D B g i : ℤ))) 1)
          fun _ : Fin (2 * g + 1) ↦ 0) := by
    funext s
    rcases s with i | i | r
    · simp only [cuspSpec, Sum.elim_inl, map_pow, aeval_X]
      rw [pow_single_one]
      exact congrArg (fun e ↦ single e (1 : K)) (by push_cast; ring)
    · simp only [cuspSpec, Sum.elim_inr, Sum.elim_inl, map_pow, aeval_X]
      rw [pow_single_one]
      exact congrArg (fun e ↦ single e (1 : K)) (by push_cast; ring)
    · simp only [cuspSpec, Sum.elim_inr, map_zero]
  rw [hfun]

/-- The `ℤ`-sum of `ℕ`-coefficients against the common rates is bounded by the coefficient
sum times `M` plus the coefficient sum times `B^g`. -/
private theorem sum_mul_descRate_le {D B : ℕ} (hB : 1 ≤ B) (c : Fin g → ℕ) :
    ∑ i, (c i : ℤ) * descRate D B g i
      ≤ (∑ i, (c i : ℤ)) * (D * B ^ (g + 1)) + (∑ i, (c i : ℤ)) * B ^ g := by
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have h1 : (descRate D B g i : ℤ) ≤ (D * B ^ (g + 1) + B ^ g : ℕ) :=
    Int.ofNat_le.mpr (descRate_le hB i.isLt D)
  have h2 : (c i : ℤ) * descRate D B g i
      ≤ (c i : ℤ) * ((D * B ^ (g + 1) + B ^ g : ℕ) : ℤ) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  push_cast at h2 ⊢
  lia

/-- The numeric core of the `a`-free budget case. -/
private theorem budget_numeric₁ {g : ℕ} {M Bg d Sb Sc Xb Xc D : ℤ}
    (hw : d = Sb * 2 + Sc * (2 * g + 1)) (h3 : Xb ≤ Sb * M + Sb * Bg)
    (h4 : Xc ≤ Sc * M + Sc * Bg) (hd : d ≤ D) (hDBg : D * Bg ≤ M) (hBg : 0 ≤ Bg) :
    2 * Xb + (2 * g + 1) * Xc ≤ d * M + M := by
  have f3 : d * M = 2 * (Sb * M) + (2 * g + 1) * (Sc * M) := by rw [hw]; ring
  have f4 : d * Bg = 2 * (Sb * Bg) + (2 * g + 1) * (Sc * Bg) := by rw [hw]; ring
  lia [mul_le_mul_of_nonneg_left h4 (show (0 : ℤ) ≤ 2 * g + 1 by positivity),
    mul_le_mul_of_nonneg_right hd hBg]

/-- The numeric core of the `a`-carrying budget case. -/
private theorem budget_numeric₂ {g : ℕ} {M Bg d Sb Sc Sd Xb Xc D : ℤ}
    (hw : d = Sb * 2 + (Sc * (2 * g + 1) + Sd)) (hSd : 2 ≤ Sd)
    (h3 : Xb ≤ Sb * M + Sb * Bg) (h4 : Xc ≤ Sc * M + Sc * Bg) (hd : d ≤ D)
    (hDBg : D * Bg ≤ M) (hBg : 0 ≤ Bg) (hM : 0 ≤ M) :
    2 * Xb + (2 * g + 1) * Xc ≤ d * M - M := by
  have f5 : (Sb * 2 + Sc * (2 * g + 1)) * Bg ≤ D * Bg := by
    have f5a : Sb * 2 + Sc * (2 * g + 1) ≤ D := by nlinarith
    exact mul_le_mul_of_nonneg_right f5a hBg
  have f6 : (Sb * 2 + Sc * (2 * g + 1)) * M ≤ (d - 2) * M := by
    have f6a : Sb * 2 + Sc * (2 * g + 1) ≤ d - 2 := by lia
    exact mul_le_mul_of_nonneg_right f6a hM
  lia [mul_le_mul_of_nonneg_left h4 (show (0 : ℤ) ≤ 2 * g + 1 by positivity)]

section Master

/-- The value of a monomial at a family split over the three variable blocks. -/
private theorem aeval_monomial_blocks (x y : Fin g → LaurentSeries K)
    (z : Fin (2 * g + 1) → LaurentSeries K) (m : (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) →₀ ℕ)
    (c : K) :
    MvPolynomial.aeval (Sum.elim x (Sum.elim y z)) (monomial m c)
      = algebraMap K (LaurentSeries K) c * (∏ i, x i ^ m (.inl i))
        * (∏ i, y i ^ m (.inr (.inl i))) * ∏ r, z r ^ m (.inr (.inr r)) := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  ring

/-- The deviation of one universal monomial between the all-at-infinity family and the
cusp is beyond the window: the correction budget of `lem:cusp-descent`(c). -/
private theorem mono_dev_le {D B M : ℕ} (hDB : D < B) (hM : M = D * B ^ (g + 1)) {d : ℤ}
    (hdD : d ≤ (D : ℤ)) {η : Fin g → LaurentSeries K}
    {α : Fin (2 * g + 1) → LaurentSeries K} {u : Fin g → LaurentSeries K}
    (hηu : ∀ i : Fin g, η i = single (-((2 * g + 1) * (descRate D B g i : ℤ))) 1 * u i)
    (hu0 : ∀ i, (0 : WithTop ℤ) ≤ (u i).orderTop)
    (hu1 : ∀ i, (((2 * M : ℕ) : ℤ) : WithTop ℤ) ≤ (u i - 1).orderTop)
    (hα : ∀ r, (0 : WithTop ℤ) ≤ (α r).orderTop)
    {m : (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) →₀ ℕ} (c : K)
    (hwt : Finsupp.weight (univWt g) m = d) :
    ((-(d * M) + M : ℤ) : WithTop ℤ)
      ≤ (MvPolynomial.aeval (Sum.elim (fun i : Fin g ↦
            (single (-(2 * (descRate D B g i : ℤ))) 1 : LaurentSeries K))
          (Sum.elim η α)) (monomial m c)
        - MvPolynomial.aeval (Sum.elim (fun i : Fin g ↦
            (single (-(2 * (descRate D B g i : ℤ))) 1 : LaurentSeries K))
            (Sum.elim (fun i : Fin g ↦ single (-((2 * g + 1) * (descRate D B g i : ℤ))) 1)
              fun _ : Fin (2 * g + 1) ↦ 0)) (monomial m c)).orderTop := by
  classical
  have hB : 1 ≤ B := by lia
  rw [aeval_monomial_blocks, aeval_monomial_blocks]
  set A := algebraMap K (LaurentSeries K) c with hA
  set Xp := ∏ i : Fin g, (single (-(2 * (descRate D B g i : ℤ))) 1 : LaurentSeries K) ^ m (.inl i)
    with hXp
  set Sp := ∏ i : Fin g, (single (-((2 * g + 1) * (descRate D B g i : ℤ))) 1
    : LaurentSeries K) ^ m (.inr (.inl i)) with hSp
  set Ep := ∏ i, η i ^ m (.inr (.inl i)) with hEp
  set Ap := ∏ r, α r ^ m (.inr (.inr r)) with hAp
  set Zp := ∏ r, (0 : LaurentSeries K) ^ m (.inr (.inr r))
  have hXpv : Xp = single (∑ i, (m (.inl i) : ℤ) * -(2 * (descRate D B g i : ℤ))) 1 :=
    hXp.trans (prod_pow_single_one ..)
  have hSpv : Sp
      = single (∑ i, (m (.inr (.inl i)) : ℤ) * -((2 * g + 1) * (descRate D B g i : ℤ))) 1 :=
    hSp.trans (prod_pow_single_one ..)
  have hw := weight_univWt_apply (g := g) m
  rw [hwt] at hw
  have hxe := sum_mul_neg_mul 2 (fun i ↦ m (.inl i)) fun i ↦ (descRate D B g i : ℤ)
  have hse := sum_mul_neg_mul (2 * g + 1) (fun i ↦ m (.inr (.inl i)))
    fun i ↦ (descRate D B g i : ℤ)
  have hMz : ((D : ℤ) * (B : ℤ) ^ (g + 1)) = (M : ℤ) := by rw [hM]; push_cast; ring
  have h3 : ∑ i, (m (.inl i) : ℤ) * descRate D B g i
      ≤ (∑ i, (m (.inl i) : ℤ)) * M + (∑ i, (m (.inl i) : ℤ)) * B ^ g := by
    have := sum_mul_descRate_le (g := g) (D := D) hB fun i ↦ m (.inl i)
    rwa [hMz] at this
  have h4 : ∑ i, (m (.inr (.inl i)) : ℤ) * descRate D B g i
      ≤ (∑ i, (m (.inr (.inl i)) : ℤ)) * M
        + (∑ i, (m (.inr (.inl i)) : ℤ)) * B ^ g := by
    have := sum_mul_descRate_le (g := g) (D := D) hB fun i ↦ m (.inr (.inl i))
    rwa [hMz] at this
  have hBg : (0 : ℤ) ≤ (B : ℤ) ^ g := by positivity
  have hDBg : (D : ℤ) * (B : ℤ) ^ g ≤ (M : ℤ) := by
    rw [hM]
    push_cast [pow_succ]
    rw [← mul_assoc]
    exact le_mul_of_one_le_right (by positivity) (mod_cast hB)
  by_cases ha : ∀ r, m (.inr (.inr r)) = 0
  · -- the `a`-free case: the deviation is a one-unit defect at the cusp monomial
    have hZ1 : Zp = 1 := Finset.prod_eq_one fun r _ ↦ by rw [ha r, pow_zero]
    have hA1 : Ap = 1 := Finset.prod_eq_one fun r _ ↦ by rw [ha r, pow_zero]
    have hEs : Ep = Sp * ∏ i, u i ^ m (.inr (.inl i)) := by
      rw [hEp, hSp, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ by rw [hηu i, mul_pow]
    rw [hZ1, hA1, hEs, mul_one, mul_one,
      show A * Xp * (Sp * ∏ i, u i ^ m (.inr (.inl i))) - A * Xp * Sp
        = A * (Xp * Sp) * ((∏ i, u i ^ m (.inr (.inl i))) - 1) by ring, hXpv, hSpv,
      single_mul_single, hxe, hse]
    refine le_trans ?_ (le_orderTop_mul (le_orderTop_mul (a := 0)
      (by rw [hA, LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
          exact orderTop_single_le)
      orderTop_single_le)
      (le_orderTop_prod_sub_one (by positivity) fun i _ ↦
        le_orderTop_pow_sub_one (by positivity) (hu1 i) _))
    rw [WithTop.coe_le_coe]
    have h5 : ∑ r, (m (.inr (.inr r)) : ℤ) * (2 * (2 * g + 1 - ((r : ℕ) : ℤ))) = 0 :=
      Finset.sum_eq_zero fun r _ ↦ by rw [ha r]; push_cast; ring
    rw [h5, add_zero, ← Finset.sum_mul, ← Finset.sum_mul] at hw
    have hcore := budget_numeric₁ (Bg := (B : ℤ) ^ g) hw h3 h4 hdD hDBg hBg
    push_cast
    lia
  · -- the `a`-carrying case: the cusp value vanishes, the family value is deep
    push Not at ha
    obtain ⟨r₀, hr₀⟩ := ha
    have hZ0 : Zp = 0 := Finset.prod_eq_zero (Finset.mem_univ r₀) (zero_pow hr₀)
    rw [hZ0, mul_zero, sub_zero]
    have hηO : ∀ i : Fin g, ((-((2 * g + 1) * (descRate D B g i : ℤ)) : ℤ) : WithTop ℤ)
        ≤ (η i).orderTop := fun i ↦ by
      rw [hηu i]
      exact le_trans (le_of_eq (congrArg (fun z : ℤ ↦ (z : WithTop ℤ)) (add_zero _).symm))
        (le_orderTop_mul (le_of_eq (orderTop_single one_ne_zero).symm) (hu0 i))
    have hEb : ((∑ i, (m (.inr (.inl i)) : ℤ)
        * -((2 * g + 1) * (descRate D B g i : ℤ)) : ℤ) : WithTop ℤ) ≤ Ep.orderTop := by
      rw [hEp]
      exact sum_le_orderTop_prod fun i _ ↦ le_orderTop_pow_of_le (hηO i) _
    have hAb : ((0 : ℤ) : WithTop ℤ) ≤ Ap.orderTop := by
      rw [hAp]
      refine le_trans (le_of_eq (by rw [Finset.sum_const_zero]))
        (sum_le_orderTop_prod (a := fun _ ↦ (0 : ℤ)) fun r _ ↦ ?_)
      exact le_trans (le_of_eq (congrArg (fun z : ℤ ↦ (z : WithTop ℤ)) (mul_zero _).symm))
        (le_orderTop_pow_of_le (hα r) _)
    have hXb : ((∑ i, (m (.inl i) : ℤ) * -(2 * (descRate D B g i : ℤ)) : ℤ) : WithTop ℤ)
        ≤ Xp.orderTop := by
      rw [hXpv]
      exact orderTop_single_le
    have hAb0 : ((0 : ℤ) : WithTop ℤ) ≤ A.orderTop := by
      rw [hA, LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
      exact orderTop_single_le
    refine le_trans ?_ (le_orderTop_mul (le_orderTop_mul (le_orderTop_mul hAb0 hXb) hEb) hAb)
    rw [WithTop.coe_le_coe, hxe, hse]
    have hSd : (2 : ℤ) ≤ ∑ r, (m (.inr (.inr r)) : ℤ) * (2 * (2 * g + 1 - ((r : ℕ) : ℤ))) := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun r ↦ (m (.inr (.inr r)) : ℤ)
        * (2 * (2 * g + 1 - ((r : ℕ) : ℤ)))) (fun r _ ↦ ?_) (Finset.mem_univ r₀))
      · have h6 : 1 ≤ (m (.inr (.inr r₀)) : ℤ) := mod_cast Nat.one_le_iff_ne_zero.mpr hr₀
        have h7 : 1 ≤ 2 * (g : ℤ) + 1 - ((r₀ : ℕ) : ℤ) := by lia
        nlinarith
      · have h8 : ((r : ℕ) : ℤ) ≤ 2 * g := by lia
        exact mul_nonneg (by positivity) (by lia)
    rw [← Finset.sum_mul, ← Finset.sum_mul] at hw
    lia [budget_numeric₂ (Bg := (B : ℤ) ^ g) hw hSd h3 h4 hdD hDBg hBg (by positivity)]

/-- **The cusp descent** (`lem:cusp-descent`): at the all-at-infinity family with the
common rates `ñᵢ = D·B^(g+1) + B^(i+1)` — `x`-coordinates exactly `s^(-2ñᵢ)`,
`y`-coordinates `s^(-Nñᵢ)` times one-units of depth `2ñᵢ`, curve coefficients of
nonnegative order — every universal weighted-homogeneous quantity whose cuspidal
specialization is nonzero takes a *nonzero* Laurent-series value: the cuspidal value is
separated by bounded-digit base-`B` expansions inside the window of width `< 2M` below
`-d·M`, and the correction budget keeps every deviation above `-d·M + M`. -/
theorem aeval_family_ne_zero {P : MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) K}
    {d : ℤ} {D B : ℕ} (hP : P.IsWeightedHomogeneous (univWt g) d)
    (hcusp : MvPolynomial.aeval (cuspSpec K g) P ≠ 0)
    (hdD : d ≤ (D : ℤ)) (hD : 0 < D) (hDB : D < B)
    {η : Fin g → LaurentSeries K}
    (hη : ∀ i : Fin g, ((2 * (descRate D B g i : ℤ)) : WithTop ℤ)
      ≤ (single ((2 * g + 1) * (descRate D B g i : ℤ)) 1 * η i - 1).orderTop)
    {α : Fin (2 * g + 1) → LaurentSeries K}
    (hα : ∀ r, (0 : WithTop ℤ) ≤ (α r).orderTop) :
    MvPolynomial.aeval (Sum.elim (fun i : Fin g ↦
        (single (-(2 * (descRate D B g i : ℤ))) 1 : LaurentSeries K))
      (Sum.elim η α)) P ≠ 0 := by
  classical
  set M : ℕ := D * B ^ (g + 1) with hM
  set u : Fin g → LaurentSeries K :=
    fun i ↦ single ((2 * g + 1) * (descRate D B g i : ℤ)) 1 * η i with hu
  have hηu : ∀ i : Fin g, η i
      = single (-((2 * g + 1) * (descRate D B g i : ℤ))) 1 * u i := fun i ↦ by
    rw [hu, ← mul_assoc, single_mul_single, neg_add_cancel, mul_one]
    change η i = single 0 1 * η i
    rw [single_zero_one, one_mul]
  have hu1 : ∀ i : Fin g, (((2 * M : ℕ) : ℤ) : WithTop ℤ) ≤ (u i - 1).orderTop := fun i ↦ by
    refine le_trans (WithTop.coe_le_coe.mpr ?_) (hη i)
    have h1 := le_descRate D B g i
    push_cast
    lia
  have hu0 : ∀ i : Fin g, (0 : WithTop ℤ) ≤ (u i).orderTop := fun i ↦ by
    rw [show u i = 1 + (u i - 1) by ring]
    refine le_trans (le_min ?_ ?_) min_orderTop_le_orderTop_add
    · rw [orderTop_one]
    · exact le_trans (mod_cast Int.natCast_nonneg (2 * M)) (hu1 i)
  have hsep := orderTop_aeval_descRate_le (isWeightedHomogeneous_aeval_cuspSpec hP)
    hcusp hdD hDB
  rw [aeval_cuspSpec_descRate] at hsep
  set xv := MvPolynomial.aeval (Sum.elim (fun i : Fin g ↦
      (single (-(2 * (descRate D B g i : ℤ))) 1 : LaurentSeries K))
    (Sum.elim η α)) P with hxv
  set yv := MvPolynomial.aeval (Sum.elim (fun i : Fin g ↦
      (single (-(2 * (descRate D B g i : ℤ))) 1 : LaurentSeries K))
    (Sum.elim (fun i : Fin g ↦ single (-((2 * g + 1) * (descRate D B g i : ℤ))) 1)
      fun _ : Fin (2 * g + 1) ↦ 0)) P with hyv
  have hdev : ((-(d * M) + M : ℤ) : WithTop ℤ) ≤ (xv - yv).orderTop := by
    rw [show xv - yv
        = ∑ m ∈ P.support, (MvPolynomial.aeval (Sum.elim (fun i : Fin g ↦
            (single (-(2 * (descRate D B g i : ℤ))) 1 : LaurentSeries K))
            (Sum.elim η α)) (monomial m (P.coeff m))
          - MvPolynomial.aeval (Sum.elim (fun i : Fin g ↦
              (single (-(2 * (descRate D B g i : ℤ))) 1 : LaurentSeries K))
              (Sum.elim (fun i : Fin g ↦
                single (-((2 * g + 1) * (descRate D B g i : ℤ))) 1)
                fun _ : Fin (2 * g + 1) ↦ 0)) (monomial m (P.coeff m))) by
      rw [hxv, hyv, Finset.sum_sub_distrib, ← map_sum, ← map_sum, ← P.as_sum]]
    exact le_orderTop_sum fun m hm ↦ mono_dev_le hDB hM hdD hηu hu0 hu1 hα (P.coeff m)
      (hP (mem_support_iff.mp hm))
  have hMz : ((M : ℕ) : ℤ) = (D : ℤ) * (B : ℤ) ^ (g + 1) := by rw [hM]; push_cast; ring
  rw [show ((-(d * ((D : ℤ) * (B : ℤ) ^ (g + 1))) : ℤ) : WithTop ℤ)
      = ((-(d * (M : ℕ)) : ℤ) : WithTop ℤ) by rw [hMz]] at hsep
  have hM1 : (1 : ℤ) ≤ ((M : ℕ) : ℤ) := by
    have h1 : 0 < M := hM ▸ Nat.mul_pos hD (pow_pos (by lia) (g + 1))
    exact_mod_cast h1
  intro h0
  have hlt : yv.orderTop < (xv - yv).orderTop :=
    lt_of_le_of_lt hsep (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by lia)) hdev)
  have heq := orderTop_add_eq_left hlt
  rw [show yv + (xv - yv) = xv by ring, h0, orderTop_zero] at heq
  rw [← heq] at hsep
  exact WithTop.not_top_le_coe _ hsep

end Master

end Budget

end ChabautyColeman

end
