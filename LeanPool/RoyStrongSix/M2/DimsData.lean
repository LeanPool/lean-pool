/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.BridgeLow
public import LeanPool.RoyStrongSix.M2.Dims

/-!
# Dimensions and degrees of `h₀ × T_U` and of `I_G`

* `hasData_poly`: an integer polynomial `P ≠ 0` gives `t ↦ P(t)` the data `(deg P, lc P · (deg
P)!)`.
* **`hdata_prodSet`**: `hdim I(h₀ × T_U) = dim h₀ + (d₁ − dim U)`, and
  `(h+r)! D₀^h D₁^r ≤ h^h r^r · deg I(h₀ × T_U)`.
* **`hdata_IG`**: `hdim I_G = d₀ + d₁` and `deg I_G ≤ (d₀+d₁)! D₀^{d₀} (2D₁)^{d₁}`.
* **`height_IG`**: `ht I_G = d₁`, so `I_G` is a complete intersection.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule StrongSix.Thm1

namespace StrongSix.M2

/-! ### Data of polynomial functions -/

theorem hasData_poly {P : Polynomial ℤ} (hP : P ≠ 0) :
    HasData (fun t : ℕ => P.eval (t : ℤ)) P.natDegree (P.leadingCoeff * P.natDegree.factorial) := by
  refine ⟨mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP) (by exact_mod_cast
    (Nat.factorial_pos _).ne'), Filter.Eventually.of_forall fun t => ?_⟩
  rw [iter_Δ_comp_cast (fun x => P.eval x), Polynomial.fwdDiff_iter_degree_eq_factorial]
  simp []

theorem HasData.smul {f : ℕ → ℤ} {a : ℕ} {c κ : ℤ} (h : HasData f a c) (hκ : κ ≠ 0) :
    HasData (fun t => κ * f t) a (κ * c) := by
  refine ⟨mul_ne_zero hκ h.1, ?_⟩
  have hlin : ∀ n (g : ℕ → ℤ), (Δ^[n] fun t => κ * g t) = fun t => κ * (Δ^[n] g) t := by
    intro n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        show Δ (fun t => κ * g t) = fun t => κ * Δ g t from by funext t; simp [fwdDiff]; ring, ih]
  rw [hlin]
  filter_upwards [h.2] with t ht
  rw [ht]

/-- `(a t + 1)^h (b t + 1)^r` as an integer polynomial. -/
noncomputable def linProd (a b h r : ℕ) : Polynomial ℤ :=
  (Polynomial.C (a : ℤ) * Polynomial.X + Polynomial.C 1) ^ h *
    (Polynomial.C (b : ℤ) * Polynomial.X + Polynomial.C 1) ^ r

theorem linProd_eval (a b h r t : ℕ) :
    (linProd a b h r).eval (t : ℤ) = (((a * t + 1) ^ h * (b * t + 1) ^ r : ℕ) : ℤ) := by
  simp [linProd]

theorem lin_data {c : ℕ} (hc : 1 ≤ c) :
    (Polynomial.C (c : ℤ) * Polynomial.X + Polynomial.C 1).natDegree = 1 ∧
      (Polynomial.C (c : ℤ) * Polynomial.X + Polynomial.C 1).leadingCoeff = (c : ℤ) ∧
      Polynomial.C (c : ℤ) * Polynomial.X + Polynomial.C 1 ≠ 0 := by
  have hc0 : (c : ℤ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  have h1 := Polynomial.natDegree_linear (b := (1 : ℤ)) hc0
  refine ⟨h1, Polynomial.leadingCoeff_linear hc0, fun h0 => ?_⟩
  rw [h0, Polynomial.natDegree_zero] at h1
  omega

theorem linProd_ne_zero {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h r : ℕ) : linProd a b h r ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (lin_data ha).2.2) (pow_ne_zero _ (lin_data hb).2.2)

theorem linProd_data {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h r : ℕ) :
    (linProd a b h r).natDegree = h + r ∧ (linProd a b h r).leadingCoeff = (a : ℤ) ^ h * b ^ r := by
  obtain ⟨ha1, ha2, ha3⟩ := lin_data ha
  obtain ⟨hb1, hb2, hb3⟩ := lin_data hb
  unfold linProd
  constructor
  · rw [Polynomial.natDegree_mul (pow_ne_zero _ ha3) (pow_ne_zero _ hb3), Polynomial.natDegree_pow,
      Polynomial.natDegree_pow, ha1, hb1]
    ring
  · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_pow, ha2,
      hb2]

theorem pow_div_bound (x h : ℕ) : (x + 1) ^ h ≤ (h * (x / h + 1)) ^ h := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp
  · apply Nat.pow_le_pow_left
    have := Nat.div_add_mod x h
    have := Nat.mod_lt x hpos
    nlinarith

variable {K : Type*} [Field K] [CharZero K] {d0 d1 : ℕ}

omit [CharZero K] in
theorem one_notMem_vanish {E : Set (GPt K d0 d1)} (hE : E.Nonempty) : vanish E ≠ ⊤ := by
  intro h
  obtain ⟨g, hg⟩ := hE
  have : (1 : MvPolynomial (V3 d0 d1) K) ∈ vanish E := h ▸ Submodule.mem_top
  simpa using this g hg

omit [CharZero K] in
theorem zero_mem_prodSet (V : Submodule K (Fin d0 → K)) (Λ : AddSubgroup (Fin d1 → ℤ)) :
    GPt.zero ∈ prodSet V Λ := ⟨V.zero_mem, fun l _ => by simp [GPt.zero, chr]⟩

/-- **Dimension and degree of `h₀ × T_U`.** -/
theorem hdata_prodSet (h0 : Submodule K (Fin d0 → K)) (U : Submodule ℚ (Fin d1 → ℚ))
    {D0 D1 : ℕ} (hD0 : 1 ≤ D0) (hD1 : 1 ≤ D1) :
    (hdata blk ![D0, D1] K (vanish (prodSet h0 (lsat U)))).1 = finrank K h0 + (d1 - finrank ℚ U) ∧
    (((finrank K h0 + (d1 - finrank ℚ U)).factorial * D0 ^ finrank K h0 *
        D1 ^ (d1 - finrank ℚ U) : ℕ) : ℤ) ≤
      ((finrank K h0) ^ finrank K h0 * (d1 - finrank ℚ U) ^ (d1 - finrank ℚ U) : ℕ) *
        (hdata blk ![D0, D1] K (vanish (prodSet h0 (lsat U)))).2 := by
  set h := finrank K h0
  set r := d1 - finrank ℚ U
  set G0 := prodSet h0 (lsat U)
  have hne : vanish G0 ≠ ⊤ := one_notMem_vanish ⟨_, zero_mem_prodSet h0 (lsat U)⟩
  have hspec := hdata_spec blk ![D0, D1] K hne
  set a := (hdata blk ![D0, D1] K (vanish G0)).1
  set c := (hdata blk ![D0, D1] K (vanish G0)).2
  -- upper bound on the dimension
  obtain ⟨M, hM⟩ := hfun_prodSet_le h0 U D0 D1
  set B := D0 + 2 * M * D1
  have hup : a ≤ h + r := by
    apply hspec.dim_le (Filter.Eventually.of_forall fun _ => by positivity)
      (g := fun t : ℕ => ((B * t + 1 : ℕ) : ℤ) ^ (h + r))
    · refine Filter.Eventually.of_forall fun t => ?_
      have h1 := hM t
      have h2 : (t * D0 + 1) ^ h * (2 * M * (t * D1) + 1) ^ r ≤ (B * t + 1) ^ (h + r) := by
        rw [pow_add]
        have hB : B * t = D0 * t + 2 * M * D1 * t := by simp only [B]; ring
        apply Nat.mul_le_mul <;> apply Nat.pow_le_pow_left
        · rw [hB, mul_comm t D0]; omega
        · rw [hB, show 2 * M * (t * D1) = 2 * M * D1 * t by ring]; omega
      exact_mod_cast h1.trans h2
    · exact Filter.Eventually.of_forall fun t => by rw [iter_Δ_pow_zero]; rfl
  -- lower bound
  set κ : ℕ := h ^ h * r ^ r
  have hκ : (κ : ℤ) ≠ 0 := by
    have hpow : ∀ n : ℕ, 0 < n ^ n := fun n => by
      rcases Nat.eq_zero_or_pos n with h' | h'
      · rw [h']; simp
      · exact Nat.pow_pos h'
    have : 0 < κ := Nat.mul_pos (hpow h) (hpow r)
    exact_mod_cast this.ne'
  have hlow : ∀ t : ℕ, (linProd D0 D1 h r).eval (t : ℤ) ≤
      κ * (hfun blk ![D0, D1] K (vanish G0) t : ℤ) := by
    intro t
    rw [linProd_eval]
    have h1 := hfun_prodSet_ge h0 U D0 D1 t
    have h2 : (D0 * t + 1) ^ h * (D1 * t + 1) ^ r ≤
        κ * ((t * D0 / h + 1) ^ h * (t * D1 / r + 1) ^ r) := by
      have e1 := pow_div_bound (t * D0) h
      have e2 := pow_div_bound (t * D1) r
      rw [mul_pow] at e1 e2
      calc (D0 * t + 1) ^ h * (D1 * t + 1) ^ r = (t * D0 + 1) ^ h * (t * D1 + 1) ^ r := by ring
        _ ≤ (h ^ h * (t * D0 / h + 1) ^ h) * (r ^ r * (t * D1 / r + 1) ^ r) :=
          Nat.mul_le_mul e1 e2
        _ = κ * ((t * D0 / h + 1) ^ h * (t * D1 / r + 1) ^ r) := by ring
    exact_mod_cast h2.trans (Nat.mul_le_mul_left _ h1)
  obtain ⟨hdeg, hlc⟩ := linProd_data hD0 hD1 h r
  have hg := hasData_poly (linProd_ne_zero hD0 hD1 h r)
  rw [hdeg, hlc] at hg
  have hκf := hspec.smul hκ
  have hcmp := hg.compare hκf (Filter.Eventually.of_forall hlow)
    (Filter.Eventually.of_forall fun t => by rw [linProd_eval]; positivity)
  rcases hcmp with hlt | ⟨heq, hle⟩
  · omega
  · refine ⟨heq.symm, ?_⟩
    push_cast
    calc ((h + r).factorial : ℤ) * D0 ^ h * D1 ^ r = (D0 : ℤ) ^ h * D1 ^ r * (h + r).factorial := by
          ring
      _ ≤ κ * c := hle
      _ = _ := by push_cast [κ]; ring

omit [CharZero K] in
/-- `I_G ⊆ I(G)`. -/
theorem IG_le_vanish : (IG : Ideal (MvPolynomial (V3 d0 d1) K)) ≤ vanish Set.univ := by
  rw [IG, Ideal.ofList, Ideal.span_le]
  intro P hP g _
  simp only [lG, List.mem_ofFn, Set.mem_ofPred_eq] at hP
  obtain ⟨j, rfl⟩ := hP
  simp [pt]

omit [CharZero K] in
theorem prodSet_top_bot :
    prodSet (⊤ : Submodule K (Fin d0 → K)) (lsat (⊥ : Submodule ℚ (Fin d1 → ℚ))) = Set.univ := by
  ext g
  simp only [prodSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  refine ⟨Submodule.mem_top, fun l hl => ?_⟩
  have : (fun j => (l j : ℚ)) = 0 := hl
  have hl0 : l = 0 := by funext j; have := congrFun this j; simpa using this
  simp [hl0, chr]

/-- **Dimension and degree of `I_G`.** -/
theorem hdata_IG {D0 D1 : ℕ} (hD0 : 1 ≤ D0) (hD1 : 1 ≤ D1) :
    IG (K := K) (d0 := d0) (d1 := d1) ≠ ⊤ ∧
    (hdata blk ![D0, D1] K (IG (K := K) (d0 := d0) (d1 := d1))).1 = d0 + d1 ∧
    (hdata blk ![D0, D1] K (IG (K := K) (d0 := d0) (d1 := d1))).2 ≤
      ((d0 + d1).factorial * D0 ^ d0 * (2 * D1) ^ d1 : ℕ) := by
  have hGne : vanish (Set.univ : Set (GPt K d0 d1)) ≠ ⊤ :=
    one_notMem_vanish ⟨GPt.zero, Set.mem_univ _⟩
  have hne : IG (K := K) (d0 := d0) (d1 := d1) ≠ ⊤ := ne_top_of_le_ne_top hGne IG_le_vanish
  refine ⟨hne, ?_⟩
  have hspec := hdata_spec blk ![D0, D1] K hne
  -- lower bound on the dimension, from `I(G)`
  have hG := hdata_prodSet (K := K) (⊤ : Submodule K (Fin d0 → K)) (⊥ : Submodule ℚ (Fin d1 → ℚ))
    hD0 hD1
  rw [prodSet_top_bot, finrank_top, finrank_bot, Module.finrank_fin_fun, Nat.sub_zero] at hG
  have hlow := hdata_le_of_le blk ![D0, D1] K IG_le_vanish hGne
  -- upper bound
  have h2D1 : 1 ≤ 2 * D1 := by omega
  obtain ⟨hdeg, hlc⟩ := linProd_data hD0 h2D1 d0 d1
  have hg := hasData_poly (linProd_ne_zero hD0 h2D1 d0 d1)
  rw [hdeg, hlc] at hg
  have hcmp := hspec.compare hg (Filter.Eventually.of_forall fun t => by
      rw [linProd_eval]
      have := hfun_IG_le (K := K) (d0 := d0) (d1 := d1) D0 D1 t
      have e : (t * D0 + 1) ^ d0 * (2 * (t * D1) + 1) ^ d1 =
          (D0 * t + 1) ^ d0 * (2 * D1 * t + 1) ^ d1 := by ring
      rw [e] at this
      exact_mod_cast this)
    (Filter.Eventually.of_forall fun _ => by positivity)
  rcases hcmp with hlt | ⟨heq, hle⟩
  · omega
  · refine ⟨heq, ?_⟩
    push_cast
    calc (hdata blk ![D0, D1] K IG).2 ≤ (D0 : ℤ) ^ d0 * (2 * D1 : ℕ) ^ d1 * (d0 + d1).factorial
      := hle
      _ = _ := by push_cast; ring

/-- **`I_G` is a complete intersection**: its height is `d₁`. -/
theorem height_IG : (IG (K := K) (d0 := d0) (d1 := d1)).height = d1 := by
  obtain ⟨hne, hdim, -⟩ := hdata_IG (K := K) (d0 := d0) (d1 := d1) (le_refl 1) (le_refl 1)
  have hb := hdim_add_height_eq blk ![1, 1] (K := K) (σ := V3 d0 d1)
    (fun i => by fin_cases i <;> simp) hne
  rw [hdim] at hb
  have hcard : Fintype.card (V3 d0 d1) = d0 + d1 + d1 := by simp [V3]; ring
  rw [hcard] at hb
  have hfin := Ideal.height_ne_top hne
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn] at hb ⊢
  have : (d0 + d1 : ℕ) + n = d0 + d1 + d1 := by exact_mod_cast hb
  norm_cast
  omega

end StrongSix.M2

end LeanPool
