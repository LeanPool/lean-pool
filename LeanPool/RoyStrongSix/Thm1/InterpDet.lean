/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.Analysis.Complex.AbsMax

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Thm1.Lines
public import LeanPool.RoyStrongSix.Thm1.Rank
public import LeanPool.RoyStrongSix.Thm1.Taylor

/-!
# Laurent's interpolation determinants: the analytic upper bound

Let `f₁, …, f_N` be analytic on `ℂ^n`. For each row `ν` take a *jet*: an order `t_ν`, directions
`w_ν : Fin t_ν → ℂ^n` and a point `ζ_ν`. Put

  `Ψ(z) = det ( D^{t_ν} f_λ (z ζ_ν) (w_ν) )_{ν, λ}`,   so that `Ψ(1)` is the interpolation
  determinant.

**Theorem** (`interpDet_bound`). For `n ≥ 1`, every `M`, `R ≥ 1`, and `B` bounding all entries on
`|z| = R`,

  `‖Ψ(1)‖ ≤ N! · B^N / R^{M(N − Mⁿ) − Σ t_ν}`.

The exponent comes from `Ψ(z) = z^K G(z)` with `G` entire and `K = M(N − Mⁿ) − Σ t_ν`
(`exists_pow_mul`). This is the several-variable zero-order estimate of Laurent's method: the
`Θ_n(N) ≫ N^{1+1/n}` count, here with `n` the dimension of the space the functions live on (for
Theorem 1, `n = dim V`).

Proof: expand every entry by the exact Taylor split `g = Σ_{k<K} tc_k z^k + z^K · rest`
(`Taylor.lean`). Expand the determinant multilinearly in the rows. A term built only from Taylor
coefficients, with total degree `< K`, has a determinant of rows of symmetric forms. Its rows of
total order `m` lie in a space of dimension `≤ (m+1)^{n-1}` (`Rank.lean`), so if the
determinant were non-zero, `Σ (t_ν + k_ν) ≥ M(N − Mⁿ)`, which contradicts degree `< K`.
-/

@[expose] public section

namespace LeanPool

open Complex Finset Matrix Function Module
open scoped ContDiff

namespace StrongSix.Thm1

variable {n N : ℕ}

/-- A jet functional on functions on `ℂ^n`: the derivative of order `t` along the directions `w`,
at the point `ζ`. -/
structure Jet (n : ℕ) where
  /-- The order of differentiation. -/
  t : ℕ
  /-- The ordered list of differentiation directions. -/
  w : Fin t → Fin n → ℂ
  /-- The point at which the jet is evaluated. -/
  ζ : Fin n → ℂ

/-- The entry `z ↦ D^t f (z ζ) (w)`. -/
noncomputable def entry (f : (Fin n → ℂ) → ℂ) (J : Jet n) (z : ℂ) : ℂ :=
  iteratedFDeriv ℂ J.t f (z • J.ζ) J.w

/-- `Ψ(z) = det (D^{t_ν} f_λ (z ζ_ν)(w_ν))`. -/
noncomputable def Ψ (f : Fin N → (Fin n → ℂ) → ℂ) (J : Fin N → Jet n) (z : ℂ) : ℂ :=
  (Matrix.of fun ν l => entry (f l) (J ν) z).det

/-! ### Elementary bounds -/

theorem norm_det_le (A : Matrix (Fin N) (Fin N) ℂ) {B : ℝ}
    (h : ∀ i j, ‖A i j‖ ≤ B) : ‖A.det‖ ≤ N.factorial * B ^ N := by
  rw [Matrix.det_apply']
  calc ‖∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : ℂ) * ∏ i, A (σ i) i‖
      ≤ ∑ σ : Equiv.Perm (Fin N), ‖(Equiv.Perm.sign σ : ℂ) * ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin N), B ^ N := by
        refine sum_le_sum fun σ _ => ?_
        rw [norm_mul, norm_prod]
        have hs : ‖(Equiv.Perm.sign σ : ℂ)‖ = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
        rw [hs, one_mul]
        calc ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : Fin N, B :=
              prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h _ _)
          _ = B ^ N := by simp
    _ = N.factorial * B ^ N := by
        rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem norm_le_of_sphere {G : ℂ → ℂ} (hG : Differentiable ℂ G) {R C : ℝ} (hR : 0 < R)
    (hC : ∀ z : ℂ, ‖z‖ = R → ‖G z‖ ≤ C) {z₀ : ℂ} (hz₀ : ‖z₀‖ ≤ R) : ‖G z₀‖ ≤ C := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball 0 R)
    Metric.isBounded_ball hG.diffContOnCl (fun z hz => hC z ?_) ?_
  · rw [frontier_ball 0 hR.ne'] at hz
    simpa using hz
  · rw [closure_ball 0 hR.ne']
    simpa using hz₀

theorem differentiable_det {q : Fin N → Fin N → ℂ → ℂ} (hq : ∀ i j, Differentiable ℂ (q i j)) :
    Differentiable ℂ (fun z => detRowAlternating (fun i j => q i j z)) := by
  change Differentiable ℂ (fun z => (Matrix.of fun i j => q i j z).det)
  simp only [Matrix.det_apply', Matrix.of_apply]
  fun_prop

/-! ### The zero-order lemma -/

/-- The Taylor coefficients of an entry are values of symmetric forms. -/
theorem tc_entry {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℂ ω f) (J : Jet n) (k : ℕ) :
    tc k (entry f J) = (k.factorial : ℂ)⁻¹ *
      iteratedFDeriv ℂ (J.t + k) f 0 (ext J.w J.ζ k) := by
  have h := tc_mul_factorial (differentiable_line hf J.w J.ζ) k
  have hl := congrFun (iteratedDeriv_line hf J.w J.ζ k) 0
  simp only [zero_smul] at hl
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  unfold entry
  rw [← hl, ← h]
  field_simp

/-- **Rank lemma.** A non-zero determinant of Taylor-coefficient rows has total order
`≥ M (N − Mⁿ)`. -/
theorem sum_order_ge (hn : 1 ≤ n) {f : Fin N → (Fin n → ℂ) → ℂ} (hf : ∀ l, ContDiff ℂ ω (f l))
    (J : Fin N → Jet n) (κ : Fin N → ℕ)
    (hdet : (Matrix.of fun ν l => tc (κ ν) (entry (f l) (J ν))).det ≠ 0) (M : ℕ) :
    M * (N - M ^ n) ≤ ∑ ν, ((J ν).t + κ ν) := by
  classical
  set C := Matrix.of fun ν l => tc (κ ν) (entry (f l) (J ν)) with hC
  have hind : LinearIndependent ℂ (fun ν => C ν) := Matrix.linearIndependent_rows_of_det_ne_zero
    hdet
  -- the spanning rows of order `m`
  let b : (m : ℕ) → {j : Fin m → Fin n // Monotone j} → Fin N → ℂ :=
    fun m j l => iteratedFDeriv ℂ m (f l) 0 (fun a => e (j.1 a))
  have hrow : ∀ ν, C ν ∈ Submodule.span ℂ (Set.range (b ((J ν).t + κ ν))) := by
    intro ν
    have hCν : C ν = ((κ ν).factorial : ℂ)⁻¹ •
        fun l => iteratedFDeriv ℂ ((J ν).t + κ ν) (f l) 0 (ext (J ν).w (J ν).ζ (κ ν)) := by
      funext l
      simp [hC, tc_entry (hf l)]
    rw [hCν]
    refine Submodule.smul_mem _ _ ?_
    exact row_mem_span (fun l => iteratedFDeriv ℂ ((J ν).t + κ ν) (f l) 0)
      (fun l v σ => (hf l).contDiffAt.iteratedFDeriv_comp_perm v σ) _
  refine mul_sub_le_sum hn (fun ν => (J ν).t + κ ν) (fun k => ?_) M
  calc (univ.filter fun ν => (J ν).t + κ ν = k).card
      ≤ Fintype.card {j : Fin k → Fin n // Monotone j} :=
        card_fiber_le hind (fun ν => (J ν).t + κ ν) k (b k) (fun ν hν => hν ▸ hrow ν)
    _ ≤ (k + 1) ^ (n - 1) := card_monotone_le hn

/-- **Zero of high order.** `Ψ(z) = z^K G(z)` with `G` entire and `K = M(N − Mⁿ) − Σ t_ν`. -/
theorem exists_pow_mul (hn : 1 ≤ n) {f : Fin N → (Fin n → ℂ) → ℂ} (hf : ∀ l, ContDiff ℂ ω (f l))
    (J : Fin N → Jet n) (M : ℕ) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ z, Ψ f J z = z ^ (M * (N - M ^ n) - ∑ ν, (J ν).t) * G z := by
  classical
  set K := M * (N - M ^ n) - ∑ ν, (J ν).t with hK
  set g : Fin N → Fin N → ℂ → ℂ := fun ν l => entry (f l) (J ν) with hg
  have hgd : ∀ ν l, Differentiable ℂ (g ν l) := fun ν l => differentiable_line (hf l) _ _
  set rest : Fin N → Fin N → ℂ → ℂ := fun ν l => (swap dslope (0 : ℂ))^[K] (g ν l) with hrest
  have hrd : ∀ ν l, Differentiable ℂ (rest ν l) := fun ν l => differentiable_iterate_dslope (hgd
    ν l) K
  -- the rescaled rows
  let Q : (Fin N → ℕ) → Fin N → ℂ → Fin N → ℂ := fun κ ν z l =>
    if κ ν < K then tc (κ ν) (g ν l) else rest ν l z
  let G : ℂ → ℂ := fun z => ∑ κ ∈ Fintype.piFinset (fun _ : Fin N => range (K + 1)),
    if K ≤ ∑ ν, κ ν then z ^ (∑ ν, κ ν - K) * detRowAlternating (fun ν => Q κ ν z) else 0
  refine ⟨G, ?_, fun z => ?_⟩
  · refine Differentiable.fun_sum fun κ _ => ?_
    split_ifs
    · refine (differentiable_pow _).mul ?_
      exact differentiable_det (N := N) (q := fun ν l z => Q κ ν z l) (fun ν l => by
        by_cases h : κ ν < K
        · simp only [Q, h, ↓reduceIte]; exact differentiable_const _
        · simp only [Q, h, ↓reduceIte]; exact hrd ν l)
    · exact differentiable_const _
  -- expand
  have hrow : ∀ ν, (fun l => g ν l z) = ∑ k ∈ range (K + 1),
      (z ^ k) • (fun l => if k < K then tc k (g ν l) else rest ν l z) := by
    intro ν
    funext l
    rw [taylor_split (g ν l) K z]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_range_succ, lt_irrefl, ↓reduceIte]
    congr 1
    · refine sum_congr rfl fun k hk => ?_
      simp only [mem_range.mp hk, ↓reduceIte]; ring
  have hΨ : Ψ f J z = ∑ κ ∈ Fintype.piFinset (fun _ : Fin N => range (K + 1)),
      z ^ (∑ ν, κ ν) * detRowAlternating (fun ν => Q κ ν z) := by
    have h1 : Ψ f J z = detRowAlternating (fun ν => ∑ k ∈ range (K + 1),
        (z ^ k) • (fun l => if k < K then tc k (g ν l) else rest ν l z)) := by
      rw [← funext hrow]; rfl
    have hs := (detRowAlternating (R := ℂ) (n := Fin N)).toMultilinearMap.map_sum_finset
      (g := fun ν k => (z ^ k) • (fun l => if k < K then tc k (g ν l) else rest ν l z))
      (A := fun _ => range (K + 1))
    simp only [AlternatingMap.coe_multilinearMap] at hs
    rw [h1, hs]
    refine sum_congr rfl fun κ hκ => ?_
    have hQ : (fun ν => (z ^ κ ν) • (fun l => if κ ν < K then tc (κ ν) (g ν l) else rest ν l z)) =
        fun ν => (z ^ κ ν) • Q κ ν z := rfl
    rw [hQ, (detRowAlternating (R := ℂ) (n := Fin N)).map_smul_univ, smul_eq_mul,
      prod_pow_eq_pow_sum]
  rw [hΨ, Finset.mul_sum]
  refine sum_congr rfl fun κ hκ => ?_
  split_ifs with hle
  · rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
  · -- low total degree: the term vanishes by the rank lemma
    push Not at hle
    have hlt : ∀ ν, κ ν < K := fun ν =>
      lt_of_le_of_lt (single_le_sum (fun i _ => Nat.zero_le (κ i)) (mem_univ ν)) hle
    have hQc : (fun ν => Q κ ν z) = fun ν l => tc (κ ν) (g ν l) := by
      funext ν l; simp [Q, hlt ν]
    have hdet0 : detRowAlternating (fun ν => Q κ ν z) = 0 := by
      rw [hQc]
      by_contra hne
      have := sum_order_ge hn hf J κ (fun h => hne h) M
      rw [sum_add_distrib] at this
      omega
    rw [hdet0, mul_zero, mul_zero]

/-- **The interpolation-determinant upper bound.** -/
theorem interpDet_bound (hn : 1 ≤ n) {f : Fin N → (Fin n → ℂ) → ℂ} (hf : ∀ l, ContDiff ℂ ω (f l))
    (J : Fin N → Jet n) (M : ℕ) {R B : ℝ} (hR : 1 ≤ R)
    (hB : ∀ ν l (z : ℂ), ‖z‖ = R → ‖entry (f l) (J ν) z‖ ≤ B) :
    ‖Ψ f J 1‖ ≤ N.factorial * B ^ N / R ^ (M * (N - M ^ n) - ∑ ν, (J ν).t) := by
  obtain ⟨G, hG, hΨG⟩ := exists_pow_mul hn hf J M
  set K := M * (N - M ^ n) - ∑ ν, (J ν).t
  have hR0 : 0 < R := by linarith
  have hRK : 0 < R ^ K := pow_pos hR0 K
  have hsphere : ∀ z : ℂ, ‖z‖ = R → ‖G z‖ ≤ N.factorial * B ^ N / R ^ K := by
    intro z hz
    rw [le_div_iff₀ hRK]
    have hdet := norm_det_le (Matrix.of fun ν l => entry (f l) (J ν) z)
      (fun ν l => hB ν l z hz)
    have : ‖Ψ f J z‖ = R ^ K * ‖G z‖ := by rw [hΨG z, norm_mul, norm_pow, hz]
    rw [Ψ] at this
    linarith [this ▸ hdet]
  have h1 := norm_le_of_sphere hG hR0 hsphere (z₀ := 1) (by simpa using hR)
  rw [hΨG 1, one_pow, one_mul]
  exact h1

end StrongSix.Thm1

end LeanPool
