/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.RingTheory.Polynomial.Pochhammer

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.Hilbert

/-!
# The Hilbert polynomial

* `hilb_colon_hom`: for any homogeneous `f ≠ 0` of degree `e`,
  `hilb J (k+e) = hilb (J + (f)) (k+e) + hilb (J : f) k`.
* `evPoly_poly`: an eventually polynomial `ℕ → ℤ` (some `Δⁿ` eventually zero) agrees for large `k`
  with an honest polynomial `P ∈ ℚ[X]`. This is the Gregory–Newton formula.
* `hpoly J`: the Hilbert polynomial of a homogeneous ideal, unique by `poly_unique`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule

namespace StrongSix.M2

variable {K : Type*} [Field K] {m : ℕ}

local notation "A" => MvPolynomial (Fin m) K

/-! ### Products with a homogeneous element -/

theorem homogeneousComponent_mul_hom {f : A} {e : ℕ} (hf : f.IsHomogeneous e) (n : ℕ) (q : A) :
    homogeneousComponent (n + e) (f * q) = f * homogeneousComponent n q := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent q, Finset.mul_sum, map_sum]
  have hterm : ∀ j, homogeneousComponent (n + e) (f * homogeneousComponent j q) =
      if j = n then f * homogeneousComponent n q else 0 := by
    intro j
    rw [homogeneousComponent_of_mem (hf.mul (homogeneousComponent_isHomogeneous j q))]
    by_cases h : j = n
    · subst h; simp [add_comm]
    · simp only [h, show n + e ≠ e + j by omega, ↓reduceIte]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by omega), mul_zero]

theorem homogeneousComponent_mul_hom_lt {f : A} {e : ℕ} (hf : f.IsHomogeneous e) {N : ℕ}
    (hN : N < e) (q : A) : homogeneousComponent N (f * q) = 0 := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent q, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [homogeneousComponent_of_mem (hf.mul (homogeneousComponent_isHomogeneous j q))]
  simp only [show N ≠ e + j by omega, ↓reduceIte]

theorem HomIdeal.sup_hom {J : Ideal A} (hJ : HomIdeal J) {f : A} {e : ℕ} (hf : f.IsHomogeneous e) :
    HomIdeal (J ⊔ Ideal.span {f}) := by
  intro p hp n
  obtain ⟨j, hj, r, hr, rfl⟩ := Submodule.mem_sup.mp hp
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  rw [map_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left (hJ j hj n)) (Submodule.mem_sup_right ?_)
  rw [mul_comm]
  by_cases hn : n < e
  · rw [homogeneousComponent_mul_hom_lt hf hn]; exact zero_mem _
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hn)
    rw [add_comm, homogeneousComponent_mul_hom hf]
    exact Ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩

theorem HomIdeal.colon_hom {J : Ideal A} (hJ : HomIdeal J) {f : A} {e : ℕ} (hf : f.IsHomogeneous
  e) :
    HomIdeal (M2.colonX J f) := by
  intro q hq n
  rw [mem_colonX, ← homogeneousComponent_mul_hom hf]
  exact hJ _ hq _

theorem mz_injective_of_ne {f : A} (hf : f ≠ 0) : Function.Injective (mz (K := K) f) :=
  fun a b h => mul_left_cancel₀ hf (show f * a = f * b from h)

theorem mem_Adeg_mul {f : A} {e k : ℕ} (hf : f.IsHomogeneous e) {a : A} (ha : a ∈ Adeg K m k) :
    f * a ∈ Adeg K m (k + e) := by
  have := hf.mul ha
  rw [add_comm] at this
  exact this

theorem Jdeg_sup_hom {J : Ideal A} (hJ : HomIdeal J) {f : A} {e : ℕ} (hf : f.IsHomogeneous e)
    (k : ℕ) :
    Jdeg (J ⊔ Ideal.span {f}) (k + e) = Jdeg J (k + e) ⊔ (Adeg K m k).map (mz f) := by
  apply le_antisymm
  · rintro p ⟨hp, hpk⟩
    obtain ⟨j, hj, r, hr, hsum⟩ := Submodule.mem_sup.mp hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have hpe : homogeneousComponent (k + e) p = p := homogeneousComponent_eq_self hpk
    rw [← hpe, ← hsum, map_add, mul_comm q, homogeneousComponent_mul_hom hf]
    refine Submodule.add_mem_sup ⟨hJ j hj (k + e), homogeneousComponent_isHomogeneous _ _⟩ ?_
    exact ⟨_, homogeneousComponent_isHomogeneous _ _, rfl⟩
  · refine sup_le (inf_le_inf_right _ (Submodule.restrictScalars_mono _ le_sup_left)) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨a, mul_comm _ _⟩),
      mem_Adeg_mul hf ha⟩

theorem Jdeg_inf_hom {J : Ideal A} {f : A} {e : ℕ} (hf : f.IsHomogeneous e) (k : ℕ) :
    Jdeg J (k + e) ⊓ (Adeg K m k).map (mz f) = (Jdeg (colonX J f) k).map (mz f) := by
  apply le_antisymm
  · rintro p ⟨⟨hpJ, -⟩, a, ha, rfl⟩
    exact ⟨a, ⟨hpJ, ha⟩, rfl⟩
  · rintro _ ⟨a, ⟨haJ, ha⟩, rfl⟩
    exact ⟨⟨haJ, mem_Adeg_mul hf ha⟩, a, ha, rfl⟩

/-- **The colon identity for a homogeneous element of degree `e`.** -/
theorem hilb_colon_hom {J : Ideal A} (hJ : HomIdeal J) {f : A} {e : ℕ} (hf : f.IsHomogeneous e)
    (hf0 : f ≠ 0) (k : ℕ) :
    hilb J (k + e) = hilb (J ⊔ Ideal.span {f}) (k + e) + hilb (colonX J f) k := by
  unfold hilb
  have hinj := mz_injective_of_ne (K := K) hf0
  have e1 : ∀ (U : Submodule K A) [FiniteDimensional K U], finrank K (U.map (mz f)) = finrank K U :=
    fun U _ => LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj U).symm
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Jdeg J (k + e)) ((Adeg K m k).map (mz f))
  rw [← Jdeg_sup_hom hJ hf k, Jdeg_inf_hom hf k, e1, e1] at h1
  have h2 := finrank_Jdeg_le (J ⊔ Ideal.span {f}) (k + e)
  have h3 := finrank_Jdeg_le (colonX J f) k
  have h4 := finrank_Jdeg_le J (k + e)
  omega

/-! ### From eventual polynomiality to a polynomial -/

theorem iter_Δ_zero_from {f : ℕ → ℤ} {N k0 : ℕ} (h : ∀ k ≥ k0, (Δ^[N] f) k = 0) :
    ∀ i, ∀ k ≥ k0, (Δ^[N + i] f) k = 0 := by
  intro i
  induction i with
  | zero => exact h
  | succ i ih =>
    intro k hk
    rw [← add_assoc, Function.iterate_succ_apply']
    change (Δ^[N + i] f) (k + 1) - (Δ^[N + i] f) k = 0
    rw [ih k hk, ih (k + 1) (by omega), sub_zero]

/-- **Gregory–Newton**: an eventually polynomial function is eventually a polynomial. -/
theorem evPoly_poly {f : ℕ → ℤ} (h : EvPoly f) :
    ∃ P : Polynomial ℚ, ∀ᶠ k in Filter.atTop, (f k : ℚ) = P.eval (k : ℚ) := by
  classical
  obtain ⟨N, hN⟩ := h
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp hN
  have hzero : ∀ j, N ≤ j → (Δ^[j] f) k0 = 0 := fun j hj => by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact iter_Δ_zero_from hk0 i k0 le_rfl
  refine ⟨∑ j ∈ Finset.range N, Polynomial.C (((Δ^[j] f) k0 : ℚ) / j.factorial) *
      (descPochhammer ℚ j).comp (Polynomial.X - Polynomial.C (k0 : ℚ)), ?_⟩
  refine Filter.eventually_atTop.mpr ⟨k0, fun k hk => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  -- Newton's formula
  have hnewton := shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) f n k0
  rw [smul_eq_mul, mul_one] at hnewton
  have hsum : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ) * (Δ^[j] f) k0 =
      ∑ j ∈ Finset.range N, (n.choose j : ℤ) * (Δ^[j] f) k0 := by
    have hA : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ) * (Δ^[j] f) k0 =
        ∑ j ∈ Finset.range (n + 1 + N), (n.choose j : ℤ) * (Δ^[j] f) k0 :=
      Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j _ hj => by
        rw [Finset.mem_range] at hj
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    have hB : ∑ j ∈ Finset.range N, (n.choose j : ℤ) * (Δ^[j] f) k0 =
        ∑ j ∈ Finset.range (n + 1 + N), (n.choose j : ℤ) * (Δ^[j] f) k0 :=
      Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j _ hj => by
        rw [Finset.mem_range] at hj
        rw [hzero j (by omega), mul_zero]
    rw [hA, hB]
  simp only [nsmul_eq_mul] at hnewton
  rw [hnewton, hsum]
  push_cast
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, show ((k0 : ℚ) + (n : ℚ) - k0) = ((n : ℕ) : ℚ) by ring,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  push_cast
  field_simp

/-- Two polynomials eventually equal on `ℕ` are equal. -/
theorem poly_unique {P Q : Polynomial ℚ} {f : ℕ → ℤ}
    (hP : ∀ᶠ k in Filter.atTop, (f k : ℚ) = P.eval (k : ℚ))
    (hQ : ∀ᶠ k in Filter.atTop, (f k : ℚ) = Q.eval (k : ℚ)) : P = Q := by
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp (hP.and hQ)
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((k0 + n : ℕ) : ℚ))
  · intro a b h; simpa using h
  · intro n
    have := hk0 (k0 + n) (by omega)
    change Polynomial.eval _ P = Polynomial.eval _ Q
    rw [← this.1, ← this.2]

/-- **The Hilbert polynomial** of a homogeneous ideal. -/
noncomputable def hpoly (J : Ideal A) (hJ : HomIdeal J) : Polynomial ℚ :=
  Classical.choose (evPoly_poly (hilb_evPoly J hJ))

theorem hpoly_spec (J : Ideal A) (hJ : HomIdeal J) :
    ∀ᶠ k in Filter.atTop, (hilb J k : ℚ) = (hpoly J hJ).eval (k : ℚ) := by
  filter_upwards [Classical.choose_spec (evPoly_poly (hilb_evPoly J hJ))] with k hk
  rw [hpoly, ← hk]
  simp

end StrongSix.M2

end LeanPool
