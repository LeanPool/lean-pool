/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.PeelAlphabet

/-!
# The peel stages as exact top-coefficient identities

The stage identities of `LeanPool.HyperellipticCurves.Log.Fold.PeelStage` split the pattern
determinant of
`q·F` — `F` the factor carrying the peeled node `u`, `q` the `u`-free rest of the alphabet
— into a surviving weight times the peeled determinant plus junk of smaller `u`-degree.
Read in the polynomial ring `A[u]` (the node `u` the polynomial variable, `q` over `A`),
this is an **exact coefficient statement**: the coefficient of `u^N` at the survivor
degree `N` is the survivor's scalar times the peeled determinant, since no junk term
reaches degree `N` (`ChabautyColeman.coeff_momentDet_of_stage`,
`ChabautyColeman.degree_prod_coeff_lt`). No valuation, rate spread or gap hypothesis is
needed: a term of strictly smaller `u`-degree cannot contribute to the top coefficient.

The five stage shapes, in coefficient form:

* `ChabautyColeman.coeff_momentDet_single`: the single peel `c_(r+1) → c_r`, coefficient `1`
  at `u^r`;
* `ChabautyColeman.coeff_momentDet_double`: the doubled peel `c_(r+2) → c_r`
  (`r + 2 ≤ g`), coefficient `2` at `u^(2r+1)`;
* `ChabautyColeman.coeff_momentDet_id`: any factor of `u`-weight `D` at the identity
  pattern of size `g + 1`, coefficient `a₀^g·a₁` at `u^(Dg + D - 1)` — the doubled peel
  (`D = 2`, `2`) and the signed trio (`D = 3`, `(-1)^(g+1)`);
* `ChabautyColeman.coeff_momentDet_triple_id`: the tripled peel at the identity pattern of
  size `g + 2`, coefficient `8` at `u^(3g+3)`;
* `ChabautyColeman.coeff_momentDet_lead`: any factor of `u`-weight `D` at any pattern,
  coefficient `a₀^g` at `u^(Dg)` — the leads of the doubled, signed-pair, trio and tripled
  factors.

The cascades of `LeanPool.HyperellipticCurves.Log.Fold.PeelCascade` iterate these along the generic
nodes.
-/
@[expose] public section

open Polynomial

namespace ChabautyColeman

section Coeff

variable {A : Type*} [CommRing A] {g : ℕ}

/-- **The top-coefficient principle of a peel stage**: if the stage identity exhibits the
pattern determinant of `q·F` (the node `u` the polynomial variable of `A[u]`, `q` free of
`u`) as `a·u^N` times the peeled determinant plus junk of `u`-degree below `N`, then the
coefficient at `u^N` is exactly `a` times the peeled determinant. -/
theorem coeff_momentDet_of_stage {ρ N : ℕ} {q : A[X]} {F : (A[X])[X]} {c c' : Fin g → ℕ}
    {a : A} {S : Finset (Fin g → Fin ρ)} {w : (Fin g → Fin ρ) → A[X]}
    (h : momentDet g (q.map C * F) c
      = C a * X ^ N * momentDet g (q.map C) c'
        + ∑ σ ∈ S, w σ * momentDet g (q.map C) (fun m ↦ c m + (σ m : ℕ)))
    (hS : ∀ σ ∈ S, (w σ).degree < N) :
    (momentDet g (q.map C * F) c).coeff N = a * momentDet g q c' := by
  rw [h, coeff_add, momentDet_map, show C a * X ^ N * C (momentDet g q c')
      = C (a * momentDet g q c') * X ^ N by rw [map_mul]; ring,
    coeff_C_mul_X_pow, ite_eq_left rfl, finsetSum_coeff, Finset.sum_eq_zero fun σ hσ ↦ ?_, add_zero]
  rw [momentDet_map]
  refine coeff_eq_zero_of_degree_lt ((degree_mul_le ..).trans_lt ?_)
  refine (add_le_add_right (degree_C_le (a := momentDet g q _)) _).trans_lt ?_
  rw [add_zero]
  exact hS σ hσ

/-- The junk weights of a peel with a factor of `u`-weight `D` — each coefficient of `F`
has `u`-degree at most `D` minus its index — have `u`-degree at most `D·g - shiftSum σ`, so a
shift choice `σ` with `D·g < N + shiftSum σ` contributes nothing at `u^N`. -/
theorem degree_prod_coeff_lt {ρ D N : ℕ} {F : (A[X])[X]} (hFD : F.natDegree ≤ D)
    (hFk : ∀ k, (F.coeff k).natDegree ≤ D - k) {σ : Fin g → Fin ρ}
    (h : D * g < N + shiftSum σ) :
    (∏ m, F.coeff (σ m : ℕ)).degree < N := by
  by_cases hσ : ∃ m, D < (σ m : ℕ)
  · obtain ⟨m, hm⟩ := hσ
    rw [Finset.prod_eq_zero (Finset.mem_univ m)
      (coeff_eq_zero_of_natDegree_lt (hFD.trans_lt hm)), degree_zero]
    exact WithBot.bot_lt_coe _
  · push Not at hσ
    refine degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr ?_)
    refine ((natDegree_prod_le ..).trans (Finset.sum_le_sum fun m _ ↦ hFk (σ m : ℕ))).trans_lt ?_
    have hs : shiftSum σ ≤ g * D := by
      rw [shiftSum]
      refine (Finset.sum_le_sum fun m _ ↦ hσ m).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [Finset.sum_tsub_distrib _ fun m _ ↦ hσ m, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, ← shiftSum]
    lia

/-! ### The factor profiles: coefficient degrees and leading coefficients at the node `u` -/

/-- The coefficient degrees of the linear node factor `u + X`. -/
theorem natDegree_coeff_C_add_X_le (k : ℕ) :
    ((C X + X : (A[X])[X]).coeff k).natDegree ≤ 1 - k := by
  rcases k with _ | _ | k
  · simpa using natDegree_X_le
  · simp
  · simp [coeff_X]

/-- The coefficient degrees of the squared node factor `(u + X)²`. -/
theorem natDegree_coeff_C_add_X_sq_le (k : ℕ) :
    (((C X + X) ^ 2 : (A[X])[X]).coeff k).natDegree ≤ 2 - k := by
  rw [coeff_C_add_X_sq]
  split_ifs with h0 h1 h2
  · subst h0; exact natDegree_X_pow_le _
  · subst h1
    exact (natDegree_mul_le ..).trans (by rw [natDegree_ofNat, zero_add]; exact natDegree_X_le)
  · subst h2; simp
  · simp

/-- The coefficient degrees of the signed-pair factor `X² - u²`. -/
theorem natDegree_coeff_X_sq_sub_C_le (k : ℕ) :
    ((X ^ 2 - C (X ^ 2) : (A[X])[X]).coeff k).natDegree ≤ 2 - k := by
  rw [coeff_X_sq_sub_C]
  split_ifs with h0 h2
  · subst h0; rw [natDegree_neg]; exact natDegree_X_pow_le _
  · subst h2; simp
  · simp

/-- The coefficient degrees of the signed-trio factor `(u + X)²(X - u)`. -/
theorem natDegree_coeff_trio_le (k : ℕ) :
    (((C X + X) ^ 2 * (X - C X) : (A[X])[X]).coeff k).natDegree ≤ 3 - k := by
  rw [coeff_trio]
  split_ifs with h0 h1 h2 h3
  · subst h0; rw [natDegree_neg]; exact natDegree_X_pow_le _
  · subst h1; rw [natDegree_neg]; exact natDegree_X_pow_le _
  · subst h2; exact natDegree_X_le
  · subst h3; simp
  · simp

/-- The coefficient degrees of the tripled node factor `(u + X)³`. -/
theorem natDegree_coeff_tripled_le (k : ℕ) :
    (((C X + X) ^ 3 : (A[X])[X]).coeff k).natDegree ≤ 3 - k := by
  rw [coeff_tripled]
  split_ifs with h0 h1 h2 h3
  · subst h0; exact natDegree_X_pow_le _
  · subst h1
    exact (natDegree_mul_le ..).trans
      (by rw [natDegree_ofNat, zero_add]; exact natDegree_X_pow_le _)
  · subst h2
    exact (natDegree_mul_le ..).trans (by rw [natDegree_ofNat, zero_add]; exact natDegree_X_le)
  · subst h3; simp
  · simp

/-! The stage coefficients in the `C a₀ * X ^ D` / `C a₁ * X ^ (D - 1)` shape that
`ChabautyColeman.coeff_momentDet_lead` and `ChabautyColeman.coeff_momentDet_id` consume; the
exponents are deliberately left unreduced. -/

theorem coeff_zero_C_add_X : (C X + X : (A[X])[X]).coeff 0 = C 1 * X ^ 1 := by simp

theorem coeff_zero_C_add_X_sq : ((C X + X) ^ 2 : (A[X])[X]).coeff 0 = C 1 * X ^ 2 := by
  rw [coeff_C_add_X_sq]; simp

theorem coeff_one_C_add_X_sq : ((C X + X) ^ 2 : (A[X])[X]).coeff 1 = C 2 * X ^ (2 - 1) := by
  rw [coeff_C_add_X_sq, ← map_ofNat C 2]; simp

theorem coeff_zero_X_sq_sub_C : (X ^ 2 - C (X ^ 2) : (A[X])[X]).coeff 0 = C (-1) * X ^ 2 := by
  rw [coeff_X_sq_sub_C, ite_eq_left rfl, map_neg, map_one]
  ring

theorem coeff_zero_trio : ((C X + X) ^ 2 * (X - C X) : (A[X])[X]).coeff 0 = C (-1) * X ^ 3 := by
  rw [coeff_trio, ite_eq_left rfl, map_neg, map_one]
  ring

theorem coeff_one_trio :
    ((C X + X) ^ 2 * (X - C X) : (A[X])[X]).coeff 1 = C (-1) * X ^ (3 - 1) := by
  rw [coeff_trio, ite_eq_right one_ne_zero, ite_eq_left rfl, map_neg, map_one]
  ring

theorem coeff_zero_tripled : ((C X + X) ^ 3 : (A[X])[X]).coeff 0 = C 1 * X ^ 3 := by
  rw [coeff_tripled, ite_eq_left rfl, map_one, one_mul]

/-! ### The five stage shapes -/

variable {q : A[X]} {r : ℕ}

/-- **The single peel, coefficient form**: the `u^r`-coefficient of the stage-`(r+1)`
determinant of `q·(u + X)` is the stage-`r` determinant of `q`. -/
theorem coeff_momentDet_single (hq : q.natDegree ≤ r) (hr : r < g) :
    (momentDet g (q.map C * (C X + X)) (peelPattern g (r + 1))).coeff r
      = momentDet g q (peelPattern g r) := by
  refine (coeff_momentDet_of_stage (q := q) (a := 1)
    (w := fun σ : Fin g → Fin 2 ↦ (X : A[X]) ^ (g - shiftSum σ))
    (by rw [peelStage_single (natDegree_map_le.trans hq) hr, map_one, one_mul])
    fun σ hσ ↦ ?_).trans (one_mul _)
  have h1 := (Finset.mem_filter.mp hσ).2
  have h2 := shiftSum_le σ
  exact (degree_X_pow_le _).trans_lt (WithBot.coe_lt_coe.mpr (by lia))

/-- **The doubled peel, coefficient form** (`r + 2 ≤ g`): the `u^(2r+1)`-coefficient of the
stage-`(r+2)` determinant of `q·(u + X)²` is twice the stage-`r` determinant of `q`. -/
theorem coeff_momentDet_double (hq : q.natDegree ≤ r) (hr : r + 2 ≤ g) :
    (momentDet g (q.map C * (C X + X) ^ 2) (peelPattern g (r + 2))).coeff (2 * r + 1)
      = 2 * momentDet g q (peelPattern g r) := by
  refine coeff_momentDet_of_stage (q := q) (a := 2)
    (w := fun σ : Fin g → Fin 3 ↦ ∏ m, ((C X + X) ^ 2 : (A[X])[X]).coeff (σ m : ℕ))
    (by
      have hc0 : ((C X + X) ^ 2 : (A[X])[X]).coeff 0 = X ^ 2 := by rw [coeff_C_add_X_sq]; simp
      have hc1 : ((C X + X) ^ 2 : (A[X])[X]).coeff 1 = 2 * X := by rw [coeff_C_add_X_sq]; simp
      have hc2 : ((C X + X) ^ 2 : (A[X])[X]).coeff 2 = 1 := by rw [coeff_C_add_X_sq]; simp
      rw [peelStage_double (natDegree_C_add_X_sq_lt _) (natDegree_map_le.trans hq) hr, hc0, hc1,
        hc2, map_ofNat]
      ring_nf)
    fun σ hσ ↦ ?_
  have := (Finset.mem_filter.mp hσ).2
  exact degree_prod_coeff_lt (Nat.lt_add_one_iff.mp (natDegree_C_add_X_sq_lt _))
    natDegree_coeff_C_add_X_sq_le (by lia)

variable (q) in
/-- **The lead peel, coefficient form**: for a factor of `u`-weight `D` with leading
coefficient `a₀·u^D` at `X^0`, the `u^(D·g)`-coefficient of the determinant of `q·F` at any
pattern is `a₀^g` times the determinant of `q`. -/
theorem coeff_momentDet_lead {ρ D : ℕ} [NeZero ρ] {F : (A[X])[X]} (hF : F.natDegree < ρ)
    (hFD : F.natDegree ≤ D) (hFk : ∀ k, (F.coeff k).natDegree ≤ D - k) {a₀ : A}
    (hF0 : F.coeff 0 = C a₀ * X ^ D) (c : Fin g → ℕ) :
    (momentDet g (q.map C * F) c).coeff (D * g) = a₀ ^ g * momentDet g q c := by
  refine coeff_momentDet_of_stage (q := q) (a := a₀ ^ g)
    (w := fun σ : Fin g → Fin ρ ↦ ∏ m, F.coeff (σ m : ℕ))
    (by rw [peelStage_lead hF, hF0, mul_pow, ← map_pow, ← pow_mul])
    fun σ hσ ↦ ?_
  have h1 := one_le_shiftSum_of_ne_zero (Finset.mem_filter.mp hσ).2
  exact degree_prod_coeff_lt hFD hFk (by lia)

/-- **The identity-pattern peel, coefficient form**: for a factor of `u`-weight `D ≥ 1` with
`F.coeff 0 = a₀·u^D` and `F.coeff 1 = a₁·u^(D-1)`, the `u^(Dg + D - 1)`-coefficient of the
identity-pattern determinant of size `g + 1` of `q·F` (`deg q ≤ g`) is `a₀^g·a₁` times the
determinant of `q` at `peelPattern (g+1) g`. -/
theorem coeff_momentDet_id {ρ D : ℕ} [NeZero ρ] (hρ : 2 ≤ ρ) {F : (A[X])[X]}
    (hF : F.natDegree < ρ) (hFD : F.natDegree ≤ D) (hFk : ∀ k, (F.coeff k).natDegree ≤ D - k)
    {a₀ a₁ : A} (hF0 : F.coeff 0 = C a₀ * X ^ D) (hF1 : F.coeff 1 = C a₁ * X ^ (D - 1))
    (hD : 1 ≤ D) (hq : q.natDegree ≤ g) :
    (momentDet (g + 1) (q.map C * F) (fun m ↦ (m : ℕ))).coeff (D * g + (D - 1))
      = a₀ ^ g * a₁ * momentDet (g + 1) q (peelPattern (g + 1) g) := by
  refine coeff_momentDet_of_stage (q := q) (a := a₀ ^ g * a₁)
    (w := fun σ : Fin (g + 1) → Fin ρ ↦ ∏ m, F.coeff (σ m : ℕ))
    (by
      rw [peelStage_id hρ hF (natDegree_map_le.trans hq), hF0, hF1, mul_pow, ← map_pow,
        ← pow_mul, map_mul, pow_add]
      ring)
    fun σ hσ ↦ ?_
  have h1 := (Finset.mem_filter.mp hσ).2
  have h2 : D * (g + 1) = D * g + D := by ring
  exact degree_prod_coeff_lt hFD hFk (by lia)

/-- **The tripled peel at the identity pattern, coefficient form**: the
`u^(3g+3)`-coefficient of the identity-pattern determinant of size `g + 2` of `q·(u + X)³`
(`deg q ≤ g`) is `8` times the determinant of `q` at `peelPattern (g+2) g`. -/
theorem coeff_momentDet_triple_id (hq : q.natDegree ≤ g) :
    (momentDet (g + 2) (q.map C * (C X + X) ^ 3) (fun m ↦ (m : ℕ))).coeff (3 * g + 3)
      = 8 * momentDet (g + 2) q (peelPattern (g + 2) g) := by
  refine coeff_momentDet_of_stage (q := q) (a := 8)
    (w := fun σ : Fin (g + 2) → Fin 4 ↦ ∏ m, ((C X + X) ^ 3 : (A[X])[X]).coeff (σ m : ℕ))
    (by
      have hc0 : ((C X + X) ^ 3 : (A[X])[X]).coeff 0 = X ^ 3 := by rw [coeff_tripled]; simp
      have hc1 : ((C X + X) ^ 3 : (A[X])[X]).coeff 1 = 3 * X ^ 2 := by rw [coeff_tripled]; simp
      have hc2 : ((C X + X) ^ 3 : (A[X])[X]).coeff 2 = 3 * X := by rw [coeff_tripled]; simp
      have hc3 : ((C X + X) ^ 3 : (A[X])[X]).coeff 3 = 1 := by rw [coeff_tripled]; simp
      rw [peelStage_triple_id (natDegree_tripled_lt _) (natDegree_map_le.trans hq), hc0, hc1,
        hc2, hc3, map_ofNat]
      ring_nf)
    fun σ hσ ↦ ?_
  have := (Finset.mem_filter.mp hσ).2
  exact degree_prod_coeff_lt (Nat.lt_add_one_iff.mp (natDegree_tripled_lt _))
    natDegree_coeff_tripled_le (by lia)

end Coeff

end ChabautyColeman

end
