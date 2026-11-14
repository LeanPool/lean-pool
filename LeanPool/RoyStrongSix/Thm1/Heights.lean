/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Arith.Liouville
public import LeanPool.RoyStrongSix.Arith.House
public import LeanPool.RoyStrongSix.Thm1.Deriv

/-!
# Heights of the interpolation-determinant entries, and Liouville's lower bound

The entries of the interpolation determinant are `eval_g (D_{w₁} ⋯ D_{w_r} (X^a Y^b))` with points
`g` and directions `w` over a number field `K`. We track each polynomial as an explicit sum of
monomials (`Good`). The predicate records:
* bidegree `≤ (D₀, D₁)`;
* coefficients that become integral after multiplying by `δ^r` (`δ` a denominator of the
  directions);
* a bound `B` on the sum of the houses of the coefficients.

* `good_invDers`: one derivation `D_w` with `δ w` integral and `house w ≤ A` turns `(r, B)` into
  `(r + 1, A (D₀ + D₁) B)`.
* `norm_eval_map_le`: for every embedding `φ` and complex `x` with `|x_X| ≤ X` and `|x_Y| ≤ Y`
  (`X, Y ≥ 1`), `‖eval x (φ P)‖ ≤ B X^{D₀} Y^{D₁}`. This gives both the analytic bound on the
  circle and the house bound.
* `isIntegral_eval`: `δ^r δ_X^{D₀} δ_Y^{D₁} eval_g P` is integral when `δ_X g_X`, `δ_Y g_Y` are.
* `liouville_det`: for a non-zero determinant with integral `E·A_{ij}` and `house A_{ij} ≤ H`,
  `1 ≤ ‖φ Δ‖ · E^N · (N! (E H)^N)^{[K:ℚ] - 1}`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Finset NumberField

namespace StrongSix.Thm1

variable {K : Type*} [Field K] [NumberField K] {d0 d1 : ℕ}

/-- `∏_v g_v^{s_v}`. -/
def monVal {R : Type*} [CommMonoid R] (g : Var d0 d1 → R) (s : Var d0 d1 →₀ ℕ) : R :=
  ∏ v, g v ^ s v

theorem eval_monomial' {R : Type*} [CommSemiring R] (g : Var d0 d1 → R) (s : Var d0 d1 →₀ ℕ)
    (c : R) : eval g (monomial s c) = c * monVal g s := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

/-- `P = Σ_k monomial (s k) (c k)` with bidegrees `≤ (D₀, D₁)`, `δ^r c_k` integral, and
`Σ house c_k ≤ B`. -/
def Good (P : MvPolynomial (Var d0 d1) K) (D0 D1 r δ : ℕ) (B : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (s : ι → Var d0 d1 →₀ ℕ) (c : ι → K),
    P = ∑ k, monomial (s k) (c k) ∧
    (∀ k, (∑ i, s k (Sum.inl i)) ≤ D0 ∧ (∑ j, s k (Sum.inr j)) ≤ D1) ∧
    (∀ k, IsIntegral ℤ ((δ : K) ^ r * c k)) ∧ ∑ k, house (c k) ≤ B

omit [NumberField K] in
theorem isIntegral_natCast' (m : ℕ) : IsIntegral ℤ (m : K) := by
  simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K m))

omit [NumberField K] in
theorem isIntegral_intCast' (m : ℤ) : IsIntegral ℤ (m : K) := by
  simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K m))

theorem good_monomial (s : Var d0 d1 →₀ ℕ) {D0 D1 : ℕ} (h0 : (∑ i, s (Sum.inl i)) ≤ D0)
    (h1 : (∑ j, s (Sum.inr j)) ≤ D1) (δ : ℕ) : Good (monomial s (1 : K)) D0 D1 0 δ 1 :=
  ⟨Unit, inferInstance, fun _ => s, fun _ => 1, by simp, fun _ => ⟨h0, h1⟩,
    fun _ => by simpa using isIntegral_one, by simp [house_one']⟩

omit [NumberField K] in
theorem invDer_zero (w : LieG K d0 d1) : invDer w (0 : MvPolynomial (Var d0 d1) K) = 0 := by
  simp [invDer]

omit [NumberField K] in
theorem invDer_sum {ι : Type*} (w : LieG K d0 d1) (t : Finset ι)
    (f : ι → MvPolynomial (Var d0 d1) K) : invDer w (∑ k ∈ t, f k) = ∑ k ∈ t, invDer w (f k) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [invDer_zero]
  | insert a t ha ih => rw [sum_insert ha, sum_insert ha, invDer_add, ih]

theorem X_mul_monomial_sub (v : Var d0 d1) (s : Var d0 d1 →₀ ℕ) (c : K) :
    X v * monomial (s - Finsupp.single v 1) (c * s v) = monomial s (c * s v) := by
  by_cases h : s v = 0
  · simp [h]
  · have hle : Finsupp.single v 1 ≤ s := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h)
    rw [X, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le hle]

/-- `D_w` of a monomial. -/
theorem invDer_monomial (w : LieG K d0 d1) (s : Var d0 d1 →₀ ℕ) (c : K) :
    invDer w (monomial s c) =
      ∑ i, monomial (s - Finsupp.single (Sum.inl i) 1) (w.1 i * (c * s (Sum.inl i))) +
        ∑ j, monomial s (w.2 j * (c * s (Sum.inr j))) := by
  simp only [invDer, pderiv_monomial, X_mul_monomial_sub, smul_monomial, smul_eq_mul]

/-- **One derivation.** -/
theorem good_invDer {P : MvPolynomial (Var d0 d1) K} {D0 D1 r δ : ℕ} {B : ℝ}
    (hP : Good P D0 D1 r δ B) (w : LieG K d0 d1) {A : ℝ} (hA : 0 ≤ A)
    (hwi : ∀ i, IsIntegral ℤ ((δ : K) * w.1 i)) (hwj : ∀ j, IsIntegral ℤ ((δ : K) * w.2 j))
    (hAi : ∀ i, house (w.1 i) ≤ A) (hAj : ∀ j, house (w.2 j) ≤ A) :
    Good (invDer w P) D0 D1 (r + 1) δ (A * (D0 + D1) * B) := by
  classical
  obtain ⟨ι, _, s, c, rfl, hdeg, hint, hB⟩ := hP
  let s' : ι × Var d0 d1 → Var d0 d1 →₀ ℕ := fun p => match p.2 with
    | Sum.inl i => s p.1 - Finsupp.single (Sum.inl i) 1
    | Sum.inr _ => s p.1
  let c' : ι × Var d0 d1 → K := fun p => match p.2 with
    | Sum.inl i => w.1 i * (c p.1 * s p.1 (Sum.inl i))
    | Sum.inr j => w.2 j * (c p.1 * s p.1 (Sum.inr j))
  refine ⟨ι × Var d0 d1, inferInstance, s', c', ?_, ?_, ?_, ?_⟩
  · rw [invDer_sum, Fintype.sum_prod_type]
    refine sum_congr rfl fun k _ => ?_
    rw [invDer_monomial, Fintype.sum_sum_type]
  · rintro ⟨k, v⟩
    obtain ⟨h0, h1⟩ := hdeg k
    cases v with
    | inl i =>
      refine ⟨le_trans (sum_le_sum fun i' _ => ?_) h0, le_trans (sum_le_sum fun j' _ => ?_) h1⟩ <;>
        simp only [s', Finsupp.coe_tsub, Pi.sub_apply] <;> omega
    | inr j => exact ⟨h0, h1⟩
  · rintro ⟨k, v⟩
    cases v with
    | inl i =>
      change IsIntegral ℤ ((δ : K) ^ (r + 1) * (w.1 i * (c k * (s k (Sum.inl i) : K))))
      rw [show (δ : K) ^ (r + 1) * (w.1 i * (c k * (s k (Sum.inl i) : K))) =
        ((δ : K) ^ r * c k) * ((δ : K) * w.1 i) * (s k (Sum.inl i) : K) by ring]
      exact ((hint k).mul (hwi i)).mul (isIntegral_natCast' _)
    | inr j =>
      change IsIntegral ℤ ((δ : K) ^ (r + 1) * (w.2 j * (c k * (s k (Sum.inr j) : K))))
      rw [show (δ : K) ^ (r + 1) * (w.2 j * (c k * (s k (Sum.inr j) : K))) =
        ((δ : K) ^ r * c k) * ((δ : K) * w.2 j) * (s k (Sum.inr j) : K) by ring]
      exact ((hint k).mul (hwj j)).mul (isIntegral_natCast' _)
  · have hterm : ∀ k (x : K) (m : ℕ), house x ≤ A →
        house (x * (c k * m)) ≤ A * (m * house (c k)) := fun k x m hx =>
      calc house (x * (c k * m)) ≤ house x * house (c k * m) := house_mul_le _ _
        _ = house x * (m * house (c k)) := by rw [mul_comm (c k), house_nat_mul]
        _ ≤ A * (m * house (c k)) :=
            mul_le_mul_of_nonneg_right hx (mul_nonneg (Nat.cast_nonneg _) (house_nonneg _))
    have hk : ∀ k, (∑ i, house (c' (k, Sum.inl i))) + ∑ j, house (c' (k, Sum.inr j)) ≤
        A * (D0 + D1) * house (c k) := by
      intro k
      obtain ⟨h0, h1⟩ := hdeg k
      have h0' : (∑ i, (s k (Sum.inl i) : ℝ)) ≤ D0 := by exact_mod_cast h0
      have h1' : (∑ j, (s k (Sum.inr j) : ℝ)) ≤ D1 := by exact_mod_cast h1
      have e0 : (∑ i, house (c' (k, Sum.inl i))) ≤
          A * house (c k) * ∑ i, (s k (Sum.inl i) : ℝ) := by
        rw [mul_sum]
        exact sum_le_sum fun i _ => (hterm k _ _ (hAi i)).trans_eq (by ring)
      have e1 : (∑ j, house (c' (k, Sum.inr j))) ≤
          A * house (c k) * ∑ j, (s k (Sum.inr j) : ℝ) := by
        rw [mul_sum]
        exact sum_le_sum fun j _ => (hterm k _ _ (hAj j)).trans_eq (by ring)
      have hAc : 0 ≤ A * house (c k) := mul_nonneg hA (house_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_left h0' hAc, mul_le_mul_of_nonneg_left h1' hAc]
    calc ∑ p, house (c' p) = ∑ k, ((∑ i, house (c' (k, Sum.inl i))) +
          ∑ j, house (c' (k, Sum.inr j))) := by
          rw [Fintype.sum_prod_type]
          exact sum_congr rfl fun k _ => Fintype.sum_sum_type _
      _ ≤ ∑ k, A * (D0 + D1) * house (c k) := sum_le_sum fun k _ => hk k
      _ = A * (D0 + D1) * ∑ k, house (c k) := by rw [mul_sum]
      _ ≤ A * (D0 + D1) * B := mul_le_mul_of_nonneg_left hB (by positivity)

/-- **Many derivations.** -/
theorem good_invDers {P : MvPolynomial (Var d0 d1) K} {D0 D1 r δ : ℕ} {B : ℝ}
    (hP : Good P D0 D1 r δ B) (l : List (LieG K d0 d1)) {A : ℝ} (hA : 0 ≤ A)
    (hwi : ∀ w ∈ l, ∀ i, IsIntegral ℤ ((δ : K) * w.1 i))
    (hwj : ∀ w ∈ l, ∀ j, IsIntegral ℤ ((δ : K) * w.2 j))
    (hAi : ∀ w ∈ l, ∀ i, house (w.1 i) ≤ A) (hAj : ∀ w ∈ l, ∀ j, house (w.2 j) ≤ A) :
    Good (invDers l P) D0 D1 (r + l.length) δ ((A * (D0 + D1)) ^ l.length * B) := by
  induction l with
  | nil => simpa [invDers_nil] using hP
  | cons w l ih =>
    have h := good_invDer (ih (fun w' hw' => hwi w' (List.mem_cons_of_mem _ hw'))
      (fun w' hw' => hwj w' (List.mem_cons_of_mem _ hw'))
      (fun w' hw' => hAi w' (List.mem_cons_of_mem _ hw'))
      (fun w' hw' => hAj w' (List.mem_cons_of_mem _ hw'))) w hA
      (hwi w List.mem_cons_self) (hwj w List.mem_cons_self)
      (hAi w List.mem_cons_self) (hAj w List.mem_cons_self)
    rw [invDers_cons, List.length_cons]
    convert h using 1
    · ring

/-! ### Evaluation bounds -/

theorem norm_monVal_le (x : Var d0 d1 → ℂ) (s : Var d0 d1 →₀ ℕ) {D0 D1 : ℕ}
    (h0 : (∑ i, s (Sum.inl i)) ≤ D0) (h1 : (∑ j, s (Sum.inr j)) ≤ D1) {X Y : ℝ} (hX : 1 ≤ X)
    (hY : 1 ≤ Y) (hx : ∀ i, ‖x (Sum.inl i)‖ ≤ X) (hy : ∀ j, ‖x (Sum.inr j)‖ ≤ Y) :
    ‖monVal x s‖ ≤ X ^ D0 * Y ^ D1 := by
  rw [monVal, norm_prod, Fintype.prod_sum_type]
  simp only [norm_pow]
  refine mul_le_mul ?_ ?_ (prod_nonneg fun _ _ => by positivity) (by positivity)
  · calc ∏ i, ‖x (Sum.inl i)‖ ^ s (Sum.inl i) ≤ ∏ i, X ^ s (Sum.inl i) :=
          prod_le_prod₀ (fun _ _ => by positivity) fun i _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hx i) _
      _ = X ^ (∑ i, s (Sum.inl i)) := prod_pow_eq_pow_sum _ _ _
      _ ≤ X ^ D0 := pow_le_pow_right₀ hX h0
  · calc ∏ j, ‖x (Sum.inr j)‖ ^ s (Sum.inr j) ≤ ∏ j, Y ^ s (Sum.inr j) :=
          prod_le_prod₀ (fun _ _ => by positivity) fun j _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hy j) _
      _ = Y ^ (∑ j, s (Sum.inr j)) := prod_pow_eq_pow_sum _ _ _
      _ ≤ Y ^ D1 := pow_le_pow_right₀ hY h1

/-- **Evaluation bound** at complex points, through any embedding. -/
theorem norm_eval_map_le {P : MvPolynomial (Var d0 d1) K} {D0 D1 r δ : ℕ} {B : ℝ}
    (hP : Good P D0 D1 r δ B) (φ : K →+* ℂ) (x : Var d0 d1 → ℂ) {X Y : ℝ} (hX : 1 ≤ X)
    (hY : 1 ≤ Y) (hx : ∀ i, ‖x (Sum.inl i)‖ ≤ X) (hy : ∀ j, ‖x (Sum.inr j)‖ ≤ Y) :
    ‖eval x (map φ P)‖ ≤ B * X ^ D0 * Y ^ D1 := by
  obtain ⟨ι, _, s, c, rfl, hdeg, -, hB⟩ := hP
  simp only [map_sum, map_monomial, eval_monomial']
  calc ‖∑ k, φ (c k) * monVal x (s k)‖ ≤ ∑ k, house (c k) * (X ^ D0 * Y ^ D1) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
        rw [norm_mul]
        exact mul_le_mul (norm_embedding_le_house _ _)
          (norm_monVal_le x (s k) (hdeg k).1 (hdeg k).2 hX hY hx hy) (norm_nonneg _)
          (house_nonneg _)
    _ = (∑ k, house (c k)) * (X ^ D0 * Y ^ D1) := by rw [sum_mul]
    _ ≤ B * (X ^ D0 * Y ^ D1) := mul_le_mul_of_nonneg_right hB (by positivity)
    _ = B * X ^ D0 * Y ^ D1 := by ring

omit [NumberField K] in
/-- `φ (eval g P) = eval (φ ∘ g) (map φ P)`. -/
theorem map_eval_eq (φ : K →+* ℂ) (g : Var d0 d1 → K) (P : MvPolynomial (Var d0 d1) K) :
    φ (eval g P) = eval (fun v => φ (g v)) (map φ P) := by
  rw [eval_map]
  change φ (eval₂ (RingHom.id K) g P) = _
  rw [hom_eval₂, RingHom.comp_id]

/-- **House bound** for evaluations. -/
theorem house_eval_le {P : MvPolynomial (Var d0 d1) K} {D0 D1 r δ : ℕ} {B : ℝ}
    (hP : Good P D0 D1 r δ B) (g : Var d0 d1 → K) {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hx : ∀ i, house (g (Sum.inl i)) ≤ X) (hy : ∀ j, house (g (Sum.inr j)) ≤ Y) :
    house (eval g P) ≤ B * X ^ D0 * Y ^ D1 := by
  rw [house, canonicalEmbedding.norm_le_iff]
  intro φ
  rw [map_eval_eq]
  exact norm_eval_map_le hP φ _ hX hY (fun i => (norm_embedding_le_house _ φ).trans (hx i))
    (fun j => (norm_embedding_le_house _ φ).trans (hy j))

/-- **Integrality** of evaluations. -/
theorem isIntegral_eval {P : MvPolynomial (Var d0 d1) K} {D0 D1 r δ : ℕ} {B : ℝ}
    (hP : Good P D0 D1 r δ B) (g : Var d0 d1 → K) (δx δy : ℕ)
    (hx : ∀ i, IsIntegral ℤ ((δx : K) * g (Sum.inl i)))
    (hy : ∀ j, IsIntegral ℤ ((δy : K) * g (Sum.inr j))) :
    IsIntegral ℤ ((δ : K) ^ r * (δx : K) ^ D0 * (δy : K) ^ D1 * eval g P) := by
  obtain ⟨ι, _, s, c, rfl, hdeg, hint, -⟩ := hP
  simp only [map_sum, eval_monomial', mul_sum]
  refine IsIntegral.sum _ fun k _ => ?_
  obtain ⟨h0, h1⟩ := hdeg k
  have hmon : (δx : K) ^ D0 * (δy : K) ^ D1 * monVal g (s k) =
      (δx : K) ^ (D0 - ∑ i, s k (Sum.inl i)) * (δy : K) ^ (D1 - ∑ j, s k (Sum.inr j)) *
        ((∏ i, ((δx : K) * g (Sum.inl i)) ^ s k (Sum.inl i)) *
          ∏ j, ((δy : K) * g (Sum.inr j)) ^ s k (Sum.inr j)) := by
    simp only [monVal, Fintype.prod_sum_type, mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum]
    conv_lhs => rw [show D0 = (D0 - ∑ i, s k (Sum.inl i)) + ∑ i, s k (Sum.inl i) by omega,
      show D1 = (D1 - ∑ j, s k (Sum.inr j)) + ∑ j, s k (Sum.inr j) by omega]
    rw [pow_add, pow_add]
    ring
  have hrw : (δ : K) ^ r * (δx : K) ^ D0 * (δy : K) ^ D1 * (c k * monVal g (s k)) =
      ((δ : K) ^ r * c k) * ((δx : K) ^ D0 * (δy : K) ^ D1 * monVal g (s k)) := by ring
  rw [hrw, hmon]
  exact (hint k).mul ((((isIntegral_natCast' _).pow _).mul ((isIntegral_natCast' _).pow _)).mul
    ((IsIntegral.prod _ fun i _ => (hx i).pow _).mul (IsIntegral.prod _ fun j _ => (hy j).pow _)))

/-! ### Liouville for determinants -/

theorem house_sign (σ : Equiv.Perm (Fin N)) : house (Equiv.Perm.sign σ : K) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · simp [h1, house_one']
  · have : house (-1 : K) = house (1 : K) := by simp [house, map_neg, norm_neg]
    simp [h1, this, house_one']

theorem house_det_le {N : ℕ} (A : Matrix (Fin N) (Fin N) K) {H : ℝ}
    (hH : ∀ i j, house (A i j) ≤ H) : house A.det ≤ N.factorial * H ^ N := by
  rw [Matrix.det_apply']
  refine (house_sum_le_sum_house _ _).trans ?_
  calc ∑ σ : Equiv.Perm (Fin N), house ((Equiv.Perm.sign σ : K) * ∏ i, A (σ i) i)
      ≤ ∑ _σ : Equiv.Perm (Fin N), H ^ N := by
        refine sum_le_sum fun σ _ => (house_mul_le _ _).trans ?_
        rw [house_sign, one_mul]
        calc house (∏ i, A (σ i) i) ≤ ∏ i, house (A (σ i) i) := house_prod_le' _ _
          _ ≤ ∏ _i : Fin N, H := prod_le_prod₀ (fun _ _ => house_nonneg _) fun i _ => hH _ _
          _ = H ^ N := by simp
    _ = N.factorial * H ^ N := by
        rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- **Liouville's inequality for an interpolation determinant.** If `E · A_{ij}` is integral and
`house A_{ij} ≤ H`, a non-zero `Δ = det A` satisfies
`1 ≤ ‖φ Δ‖ · E^N · (N! (E H)^N)^{[K:ℚ] - 1}`. -/
theorem liouville_det {N : ℕ} (φ : K →+* ℂ) (A : Matrix (Fin N) (Fin N) K) (E : ℕ) {H : ℝ}
    (hE : ∀ i j, IsIntegral ℤ ((E : K) * A i j)) (hH : ∀ i j, house (A i j) ≤ H)
    (hΔ : A.det ≠ 0) (hE0 : E ≠ 0) :
    1 ≤ ‖φ A.det‖ * (E : ℝ) ^ N * (N.factorial * (E * H) ^ N) ^ (Module.finrank ℚ K - 1) := by
  set B : Matrix (Fin N) (Fin N) K := Matrix.of fun i j => (E : K) * A i j with hBdef
  have hBdet : B.det = (E : K) ^ N * A.det := by
    have := Matrix.det_mul_column (fun _ : Fin N => (E : K)) A
    rw [prod_const, card_univ, Fintype.card_fin] at this
    rw [← this]
  have hint : IsIntegral ℤ B.det := by
    rw [Matrix.det_apply']
    exact IsIntegral.sum _ fun σ _ =>
      (isIntegral_intCast' _).mul (IsIntegral.prod _ fun i _ => hE _ _)
  have hBne : B.det ≠ 0 := by
    rw [hBdet]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr hE0)) hΔ
  have hL := one_le_norm_mul_house_pow hint hBne φ
  have hhB : house B.det ≤ N.factorial * (E * H) ^ N := by
    refine house_det_le B fun i j => ?_
    change house ((E : K) * A i j) ≤ E * H
    rw [house_nat_mul]
    exact mul_le_mul_of_nonneg_left (hH i j) (Nat.cast_nonneg _)
  have hφ : ‖φ B.det‖ = (E : ℝ) ^ N * ‖φ A.det‖ := by
    rw [hBdet, map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
  calc (1 : ℝ) ≤ ‖φ B.det‖ * house B.det ^ (Module.finrank ℚ K - 1) := hL
    _ ≤ ‖φ B.det‖ * (N.factorial * (E * H) ^ N) ^ (Module.finrank ℚ K - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (house_nonneg _) hhB _) (norm_nonneg _)
    _ = ‖φ A.det‖ * (E : ℝ) ^ N * (N.factorial * (E * H) ^ N) ^ (Module.finrank ℚ K - 1) := by
        rw [hφ]; ring

end StrongSix.Thm1

end LeanPool
