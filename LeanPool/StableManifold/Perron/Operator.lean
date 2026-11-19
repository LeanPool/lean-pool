/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.Linear.HyperbolicSplitting
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# The linear Lyapunov–Perron operator

Let `S` be a hyperbolic splitting of `A` (projection `P`, unstable inverse `B`, constants `C`,
`λ`), on a real Banach space `E`. The bounded solutions `z` of the inhomogeneous linear equation

  `z (n + 1) = A (z n) + y n`

with a bounded right-hand side `y` are exactly the sequences `z = stableOrbit ξ + perronOp y`
(variation of constants), with

* `S.stableOrbit ξ n = Aⁿ (P ξ)` (`stableOrbit`, a bounded linear map `E → ℕ →ᵇ E`), and
* `S.perronOp y n = ∑_{k < n} A^(n-1-k) P (y k) - ∑_{j ≥ 0} B^(j+1) (y (n + j))` (`perronOp`, a
  bounded linear operator of `ℕ →ᵇ E`, the linear Lyapunov–Perron operator).

`ξ` fixes the stable component `P (z 0) = P ξ`. Main statements:

* `stableOrbit_add_perronOp_succ`, `proj_stableOrbit_add_perronOp_zero`:
  `stableOrbit ξ + perronOp y` solves the equation, with stable component `P ξ` at time `0`;
* `eq_stableOrbit_add_perronOp`: every bounded solution has this form, with `ξ = z 0`;
* `norm_perronOp_le`: `‖perronOp‖ ≤ S.bound = 3 C / (1 - λ)`;
* `norm_perronOp_apply_le_of_le`: the same bound in the weighted sup norm with weights
  `θⁿ`, `θ = S.decayRate = (1 + λ) / 2`: if `‖y n‖ ≤ M θⁿ` then
  `‖perronOp y n‖ ≤ S.bound * M * θⁿ`.

## Proofs

* `summable_unstableInv_pow_apply`: `‖B^(j+1) (y (n + j))‖ ≤ C λ^(j+1) ‖y‖`
  (`norm_unstableInv_pow_succ_le`), the terms of a geometric series (`Summable.of_norm_bounded`,
  `summable_geometric_of_lt_one`).
* `norm_perronTerm_le`: the finite sum has norm `≤ ∑_{k < n} C λ^(n-1-k) ‖y‖ ≤ C ‖y‖ / (1 - λ)`
  (`Finset.sum_range_reflect`, `Summable.sum_le_tsum`, `tsum_geometric_of_lt_one`), and the
  series has norm `≤ C λ ‖y‖ / (1 - λ) ≤ C ‖y‖ / (1 - λ)` (`tsum_of_norm_bounded`); the total
  `2 C ‖y‖ / (1 - λ)` is at most `S.bound ‖y‖ = 3 C ‖y‖ / (1 - λ)`.
* `perronTerm_add`, `perronTerm_smul`: `Finset.sum_add_distrib`, `Summable.tsum_add`,
  `Summable.tsum_const_smul`, with the summability above. `perronOp` is then
  `LinearMap.mkContinuous` with the constant `S.bound`, so `norm_perronOp_le` is
  `LinearMap.mkContinuous_norm_le`.
* `norm_perronOp_apply_le_of_le`: with `θ - λ = (1 - λ) / 2`, `geom_sum₂_mul` gives
  `∑_{k < n} θ^k λ^(n-1-k) ≤ θⁿ / (θ - λ) = 2 θⁿ / (1 - λ)`, so the finite sum has norm
  `≤ 2 C M θⁿ / (1 - λ)`; the series has norm `≤ C M θⁿ / (1 - λ)`, as `‖y (n + j)‖ ≤ M θⁿ`.
  The total is `3 C M θⁿ / (1 - λ) = S.bound M θⁿ`.
* `proj_perronOp_apply_zero`: at time `0` only the series remains, and `P B^(j+1) = 0` term by
  term (`ContinuousLinearMap.map_tsum`).
* `stableOrbit_add_perronOp_succ`: the stable orbit gives `A^(n+1) P ξ = A (Aⁿ P ξ)`; the finite
  sums, `∑_{k ≤ n} A^(n-k) P y k = A (∑_{k < n} A^(n-1-k) P y k) + P y n`
  (`Finset.sum_range_succ`); the series,
  `A (∑_j B^(j+1) y (n + j)) = (1 - P) y n + ∑_j B^(j+1) y (n + 1 + j)`, from
  `A B^(j+1) = (1 - P) B^j` and `P B^(j+1) = 0` (`mul_unstableInv_pow_succ`,
  `ContinuousLinearMap.map_tsum`, `Summable.tsum_eq_zero_add`). The three combine to the
  equation.
* `proj_stableOrbit_add_perronOp_zero`: `proj_perronOp_apply_zero` and `P² = P`.
* `eq_stableOrbit_add_perronOp`: the difference `d` of `z` and `stableOrbit (z 0) + perronOp y`
  solves `d (n + 1) = A (d n)` with `P (d 0) = 0`, so `P (d n) = 0` for all `n` (`A P = P A`),
  `B (d (n + 1)) = d n` (`B A = 1 - P`), and `d n = Bᵐ (1 - P) (d (n + m))`, of norm
  `≤ C λᵐ ‖d‖ → 0`; hence `d = 0`.
-/

@[expose] public section

open Filter Topology
open scoped BoundedContinuousFunction

namespace ContinuousLinearMap.HyperbolicSplitting

open BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : E →L[ℝ] E}
  (S : A.HyperbolicSplitting)

/-- `‖Aⁿ P x‖ ≤ C λⁿ ‖x‖`. -/
private theorem norm_pow_proj_apply_le (n : ℕ) (x : E) :
    ‖(A ^ n) (S.proj x)‖ ≤ S.const * S.rate ^ n * ‖x‖ := by
  rw [← mul_apply_eq_comp]
  exact ((A ^ n * S.proj).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (S.norm_pow_mul_proj_le n) (norm_nonneg _))

/-- `‖Aⁿ P ξ‖ ≤ C λⁿ ‖P ξ‖`. -/
theorem norm_pow_apply_proj_le (n : ℕ) (ξ : E) :
    ‖(A ^ n) (S.proj ξ)‖ ≤ S.const * S.rate ^ n * ‖S.proj ξ‖ := by
  simpa only [← mul_apply_eq_comp S.proj S.proj, S.proj_mul_proj] using
    S.norm_pow_proj_apply_le n (S.proj ξ)

/-- `‖Aⁿ P ξ‖ ≤ C ‖ξ‖`. -/
theorem norm_pow_apply_proj_le_const (n : ℕ) (ξ : E) :
    ‖(A ^ n) (S.proj ξ)‖ ≤ S.const * ‖ξ‖ := by
  exact (S.norm_pow_proj_apply_le n ξ).trans (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right S.const_pos.le (pow_le_one₀ S.rate_pos.le S.rate_lt_one.le))
    (norm_nonneg _))

/-- The **stable orbits** `ξ ↦ (n ↦ Aⁿ (P ξ))`, a bounded linear map into bounded sequences. -/
noncomputable def stableOrbit : E →L[ℝ] (ℕ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun ξ ↦ ofNormedAddCommGroupDiscrete (fun n ↦ (A ^ n) (S.proj ξ)) (S.const * ‖ξ‖)
        fun n ↦ S.norm_pow_apply_proj_le_const n ξ
      map_add' := fun ξ η ↦ by ext n; simp
      map_smul' := fun c ξ ↦ by ext n; simp }
    S.const fun ξ ↦ norm_ofNormedAddCommGroup_le _ (by positivity [S.const_pos])
      fun n ↦ S.norm_pow_apply_proj_le_const n ξ

@[simp]
theorem stableOrbit_apply (ξ : E) (n : ℕ) : S.stableOrbit ξ n = (A ^ n) (S.proj ξ) :=
  rfl

theorem stableOrbit_proj (ξ : E) : S.stableOrbit (S.proj ξ) = S.stableOrbit ξ := by
  ext n
  simp only [stableOrbit_apply, ← mul_apply_eq_comp S.proj S.proj, S.proj_mul_proj]

/-- The `n`-th term of the linear Lyapunov–Perron operator:
`∑_{k < n} A^(n-1-k) P (y k) - ∑_{j ≥ 0} B^(j+1) (y (n + j))`. -/
private noncomputable def perronTerm (y : ℕ →ᵇ E) (n : ℕ) : E :=
  ∑ k ∈ Finset.range n, (A ^ (n - 1 - k)) (S.proj (y k)) -
    ∑' j : ℕ, (S.unstableInv ^ (j + 1)) (y (n + j))

/-- `‖Bⁿ⁺¹ x‖ ≤ C λⁿ⁺¹ ‖x‖`. -/
private theorem norm_unstableInv_pow_succ_apply_le (n : ℕ) (x : E) :
    ‖(S.unstableInv ^ (n + 1)) x‖ ≤ S.const * S.rate ^ (n + 1) * ‖x‖ :=
  ((S.unstableInv ^ (n + 1)).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (S.norm_unstableInv_pow_succ_le n) (norm_nonneg _))

/-- `A Bⁿ⁺¹ x = Bⁿ x - P Bⁿ x`. -/
private theorem apply_unstableInv_pow_succ_apply (n : ℕ) (x : E) :
    A ((S.unstableInv ^ (n + 1)) x) =
      (S.unstableInv ^ n) x - S.proj ((S.unstableInv ^ n) x) := by
  rw [← mul_apply_eq_comp A, S.mul_unstableInv_pow_succ, mul_apply_eq_comp, _root_.sub_apply,
    one_apply_eq_self]

/-- `P Bⁿ⁺¹ x = 0`. -/
private theorem proj_unstableInv_pow_succ_apply (n : ℕ) (x : E) :
    S.proj ((S.unstableInv ^ (n + 1)) x) = 0 := by
  rw [← mul_apply_eq_comp S.proj, S.proj_mul_unstableInv_pow_succ, zero_apply]

/-- Bound the geometric convolution for any weight at least the decay rate. -/
private theorem sum_weight_pow_mul_rate_pow_le {weight : ℝ} (hweight : S.decayRate ≤ weight)
    (n : ℕ) :
    ∑ k ∈ Finset.range n, weight ^ k * S.rate ^ (n - 1 - k) ≤
      2 * (1 - S.rate)⁻¹ * weight ^ n := by
  have h := geom_sum₂_mul weight S.rate n
  have hd : (1 - S.rate) / 2 ≤ weight - S.rate := by
    unfold decayRate at hweight
    linarith
  have hrate : 0 < 1 - S.rate := sub_pos.2 S.rate_lt_one
  have hw : 0 ≤ weight := S.decayRate_pos.le.trans hweight
  set s := ∑ k ∈ Finset.range n, weight ^ k * S.rate ^ (n - 1 - k)
  have hs : 0 ≤ s := Finset.sum_nonneg fun k _ ↦
    mul_nonneg (pow_nonneg hw k) (pow_nonneg S.rate_pos.le _)
  have hscaled : s * (1 - S.rate) ≤ 2 * weight ^ n := by
    nlinarith [mul_le_mul_of_nonneg_left hd hs, pow_nonneg S.rate_pos.le n]
  calc s = s * (1 - S.rate) * (1 - S.rate)⁻¹ := by field_simp
    _ ≤ 2 * weight ^ n * (1 - S.rate)⁻¹ :=
      mul_le_mul_of_nonneg_right hscaled (inv_nonneg.mpr hrate.le)
    _ = 2 * (1 - S.rate)⁻¹ * weight ^ n := by ring

/-- `‖∑_{k < n} A^(n-1-k) P (x k)‖ ≤ ∑_{k < n} C λ^(n-1-k) ‖x k‖`. -/
private theorem norm_sum_pow_proj_apply_le (x : ℕ → E) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, (A ^ (n - 1 - k)) (S.proj (x k))‖ ≤
      ∑ k ∈ Finset.range n, S.const * S.rate ^ (n - 1 - k) * ‖x k‖ :=
  (norm_sum_le _ _).trans <| Finset.sum_le_sum fun _ _ ↦ S.norm_pow_proj_apply_le _ _

/-- `‖∑_j B^(j+1) (x j)‖ ≤ C / (1 - λ) * a` when `‖x j‖ ≤ a` for all `j`. -/
private theorem norm_tsum_unstableInv_pow_apply_le {x : ℕ → E} {a : ℝ} (hx : ∀ j, ‖x j‖ ≤ a) :
    ‖∑' j : ℕ, (S.unstableInv ^ (j + 1)) (x j)‖ ≤ S.const * (1 - S.rate)⁻¹ * a := by
  have ha : 0 ≤ a := (norm_nonneg _).trans (hx 0)
  have h1 : 0 < 1 - S.rate := sub_pos.2 S.rate_lt_one
  have hg : HasSum (fun j : ℕ ↦ S.const * S.rate ^ (j + 1) * a)
      (S.const * S.rate * (1 - S.rate)⁻¹ * a) := by
    convert ((hasSum_geometric_of_lt_one S.rate_pos.le S.rate_lt_one).mul_left
      (S.const * S.rate)).mul_right a using 1
    ext j
    ring
  refine (tsum_of_norm_bounded hg fun j ↦ (S.norm_unstableInv_pow_succ_apply_le j _).trans
    (mul_le_mul_of_nonneg_left (hx j) (by positivity [S.const_pos, S.rate_pos]))).trans ?_
  have : S.const * S.rate ≤ S.const :=
    mul_le_of_le_one_right S.const_pos.le S.rate_lt_one.le
  gcongr

variable [CompleteSpace E] in
/-- The unstable series converges: `‖B^(j+1) (y (n + j))‖ ≤ C λ^(j+1) ‖y‖`. -/
theorem summable_unstableInv_pow_apply (y : ℕ →ᵇ E) (n : ℕ) :
    Summable fun j : ℕ ↦ (S.unstableInv ^ (j + 1)) (y (n + j)) := by
  refine .of_norm_bounded (g := fun j ↦ S.const * S.rate ^ (j + 1) * ‖y‖) ?_ fun j ↦ ?_
  · exact (((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one S.rate_pos.le
      S.rate_lt_one)).mul_left S.const).mul_right ‖y‖
  · exact (S.norm_unstableInv_pow_succ_apply_le j _).trans
      (mul_le_mul_of_nonneg_left (y.norm_coe_le_norm _) (by positivity [S.const_pos, S.rate_pos]))

/-- Estimate a Perron term on a sequence bounded by a geometric weight. -/
private theorem norm_perronTerm_le_of_le {y : ℕ →ᵇ E} {M weight : ℝ}
    (hweightOne : weight ≤ 1) (hweight : S.decayRate ≤ weight)
    (hy : ∀ n, ‖y n‖ ≤ M * weight ^ n) (n : ℕ) :
    ‖perronTerm S y n‖ ≤ S.bound * M * weight ^ n := by
  have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hy 0)
  have h1 : 0 < 1 - S.rate := sub_pos.2 S.rate_lt_one
  have hw : 0 ≤ weight := S.decayRate_pos.le.trans hweight
  have hs : ‖∑ k ∈ Finset.range n, (A ^ (n - 1 - k)) (S.proj (y k))‖ ≤
      S.const * M * (2 * (1 - S.rate)⁻¹ * weight ^ n) := by
    refine (S.norm_sum_pow_proj_apply_le y n).trans ?_
    calc ∑ k ∈ Finset.range n, S.const * S.rate ^ (n - 1 - k) * ‖y k‖
        ≤ ∑ k ∈ Finset.range n, S.const * S.rate ^ (n - 1 - k) * (M * weight ^ k) := by
          gcongr with k
          · exact mul_nonneg S.const_pos.le (pow_nonneg S.rate_pos.le _)
          · exact hy k
      _ = S.const * M * ∑ k ∈ Finset.range n, weight ^ k * S.rate ^ (n - 1 - k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ ↦ by ring
      _ ≤ S.const * M * (2 * (1 - S.rate)⁻¹ * weight ^ n) := by
          gcongr
          · exact mul_nonneg S.const_pos.le hM
          · exact S.sum_weight_pow_mul_rate_pow_le hweight n
  have ht := S.norm_tsum_unstableInv_pow_apply_le (x := fun j ↦ y (n + j))
    (a := M * weight ^ n) fun j ↦ (hy (n + j)).trans <| by
      rw [pow_add]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (pow_nonneg hw n) (pow_le_one₀ hw hweightOne))
        hM
  have hb : S.bound * M * weight ^ n =
      3 * (S.const * (1 - S.rate)⁻¹ * (M * weight ^ n)) := by unfold bound; ring
  rw [hb, perronTerm]
  exact (norm_sub_le _ _).trans (by nlinarith)

private theorem norm_perronTerm_le (y : ℕ →ᵇ E) (n : ℕ) :
    ‖perronTerm S y n‖ ≤ S.bound * ‖y‖ := by
  simpa using norm_perronTerm_le_of_le S le_rfl S.decayRate_lt_one.le
    (fun k ↦ by simpa using y.norm_coe_le_norm k) n

variable [CompleteSpace E]

private theorem perronTerm_add (y z : ℕ →ᵇ E) (n : ℕ) :
    perronTerm S (y + z) n = perronTerm S y n + perronTerm S z n := by
  simp only [perronTerm, BoundedContinuousFunction.add_apply, map_add, Finset.sum_add_distrib]
  rw [(S.summable_unstableInv_pow_apply y n).tsum_add (S.summable_unstableInv_pow_apply z n)]
  abel

private theorem perronTerm_smul (c : ℝ) (y : ℕ →ᵇ E) (n : ℕ) :
    perronTerm S (c • y) n = c • perronTerm S y n := by
  simp only [perronTerm, BoundedContinuousFunction.smul_apply, map_smul, ← Finset.smul_sum]
  rw [(S.summable_unstableInv_pow_apply y n).tsum_const_smul c, smul_sub]

/-- The **linear Lyapunov–Perron operator** on bounded sequences:
`perronOp y n = ∑_{k < n} A^(n-1-k) P (y k) - ∑_{j ≥ 0} B^(j+1) (y (n + j))`. -/
@[no_expose]
noncomputable def perronOp : (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun y ↦ ofNormedAddCommGroupDiscrete (perronTerm S y) (S.bound * ‖y‖)
        (norm_perronTerm_le S y)
      map_add' := fun y z ↦ by ext n; exact perronTerm_add S y z n
      map_smul' := fun c y ↦ by ext n; exact perronTerm_smul S c y n }
    S.bound fun y ↦ norm_ofNormedAddCommGroup_le _ (by positivity [S.bound_pos])
      (norm_perronTerm_le S y)

theorem perronOp_apply (y : ℕ →ᵇ E) (n : ℕ) :
    S.perronOp y n = ∑ k ∈ Finset.range n, (A ^ (n - 1 - k)) (S.proj (y k)) -
      ∑' j : ℕ, (S.unstableInv ^ (j + 1)) (y (n + j)) := by
  unfold perronOp
  rfl

/-- At time `0` only the unstable series remains. -/
theorem perronOp_apply_zero (y : ℕ →ᵇ E) :
    S.perronOp y 0 = -∑' j : ℕ, (S.unstableInv ^ (j + 1)) (y j) := by
  simp [perronOp_apply]

/-- The operator norm of the linear Lyapunov–Perron operator is at most `S.bound`. -/
theorem norm_perronOp_le : ‖S.perronOp‖ ≤ S.bound :=
  LinearMap.mkContinuous_norm_le _ S.bound_pos.le _

/-- **The weighted estimate**: if `‖y n‖ ≤ M θⁿ` with `θ = S.decayRate = (1 + λ) / 2`, then
`‖perronOp y n‖ ≤ S.bound * M * θⁿ`.

Proof: `∑_{k<n} C λ^(n-1-k) M θ^k ≤ 2 C M θⁿ / (1 - λ)` and
`∑_j C λ^(j+1) M θ^(n+j) ≤ C M θⁿ / (1 - λ)`. -/
theorem norm_perronOp_apply_le_of_le {y : ℕ →ᵇ E} {M : ℝ}
    (hy : ∀ n, ‖y n‖ ≤ M * S.decayRate ^ n) (n : ℕ) :
    ‖S.perronOp y n‖ ≤ S.bound * M * S.decayRate ^ n := by
  exact norm_perronTerm_le_of_le S S.decayRate_lt_one.le le_rfl hy n

/-- The Lyapunov–Perron term vanishes on the stable component at time `0`. -/
theorem proj_perronOp_apply_zero (y : ℕ →ᵇ E) : S.proj (S.perronOp y 0) = 0 := by
  have hs := S.summable_unstableInv_pow_apply y 0
  simp only [zero_add] at hs
  rw [perronOp_apply_zero, map_neg, S.proj.map_tsum hs]
  simp only [proj_unstableInv_pow_succ_apply, tsum_zero, neg_zero]

/-- `A (∑_j B^(j+1) (y (n + j))) = (1 - P) (y n) + ∑_j B^(j+1) (y (n + 1 + j))`. -/
private theorem apply_tsum_unstableInv_pow_apply (y : ℕ →ᵇ E) (n : ℕ) :
    A (∑' j : ℕ, (S.unstableInv ^ (j + 1)) (y (n + j))) =
      (y n - S.proj (y n)) + ∑' j : ℕ, (S.unstableInv ^ (j + 1)) (y (n + 1 + j)) := by
  have hs := S.summable_unstableInv_pow_apply y n
  have hs' := hs.mapL A
  simp only [apply_unstableInv_pow_succ_apply] at hs'
  rw [A.map_tsum hs]
  simp only [apply_unstableInv_pow_succ_apply]
  rw [hs'.tsum_eq_zero_add]
  simp only [pow_zero, one_apply_eq_self, add_zero, proj_unstableInv_pow_succ_apply, sub_zero]
  congr 2
  ext j
  rw [add_comm j 1, add_assoc]

/-- `stableOrbit ξ + perronOp y` **solves** `z (n + 1) = A (z n) + y n`.

Proof: split into the stable component (finite sums) and the unstable one (the series, with
`A B^(j+1) = (1 - P) B^j`). -/
theorem stableOrbit_add_perronOp_succ (ξ : E) (y : ℕ →ᵇ E) (n : ℕ) :
    (S.stableOrbit ξ + S.perronOp y) (n + 1) =
      A ((S.stableOrbit ξ + S.perronOp y) n) + y n := by
  simp only [BoundedContinuousFunction.add_apply, stableOrbit_apply, perronOp_apply,
    map_add, map_sub, apply_tsum_unstableInv_pow_apply, map_sum]
  rw [Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_apply_eq_self,
    ← mul_apply_eq_comp A (A ^ n), ← pow_succ']
  have h : ∀ k ∈ Finset.range n, A ((A ^ (n - 1 - k)) (S.proj (y k))) =
      (A ^ (n - k)) (S.proj (y k)) := fun k hk ↦ by
    rw [← mul_apply_eq_comp, ← pow_succ', show n - 1 - k + 1 = n - k by
      have := Finset.mem_range.1 hk; omega]
  simp only [Finset.sum_congr rfl h]
  abel

/-- The solution `stableOrbit ξ + perronOp y` has stable component `P ξ` at time `0`. -/
theorem proj_stableOrbit_add_perronOp_zero (ξ : E) (y : ℕ →ᵇ E) :
    S.proj ((S.stableOrbit ξ + S.perronOp y) 0) = S.proj ξ := by
  rw [BoundedContinuousFunction.add_apply, map_add, proj_perronOp_apply_zero, add_zero,
    stableOrbit_apply, pow_zero, one_apply_eq_self, ← mul_apply_eq_comp S.proj S.proj,
    S.proj_mul_proj]

/-- **Every bounded solution** of `z (n + 1) = A (z n) + y n` is `stableOrbit (z 0) + perronOp y`.

Proof: the difference `d` solves `d (n + 1) = A (d n)` with `P (d 0) = 0`; so `P (d n) = 0` and
`(1 - P) (d n) = Bᵐ (1 - P) (d (n + m))` has norm `≤ C λᵐ ‖d‖ → 0`. -/
theorem eq_stableOrbit_add_perronOp {z y : ℕ →ᵇ E} (hz : ∀ n, z (n + 1) = A (z n) + y n) :
    z = S.stableOrbit (z 0) + S.perronOp y := by
  set w := S.stableOrbit (z 0) + S.perronOp y
  set d := z - w
  have hd : ∀ n, d (n + 1) = A (d n) := fun n ↦ by
    simp only [d, BoundedContinuousFunction.sub_apply, hz, w,
      S.stableOrbit_add_perronOp_succ, map_sub]
    abel
  have hP : ∀ n, S.proj (d n) = 0 := by
    intro n
    induction n with
    | zero =>
      simp only [d, BoundedContinuousFunction.sub_apply, map_sub, w,
        S.proj_stableOrbit_add_perronOp_zero, sub_self]
    | succ n ih => rw [hd, ← mul_apply_eq_comp, ← S.mul_proj_comm, mul_apply_eq_comp, ih,
        map_zero]
  have hB : ∀ n, S.unstableInv (d (n + 1)) = d n := fun n ↦ by
    rw [hd, ← mul_apply_eq_comp, S.unstableInv_mul, _root_.sub_apply, one_apply_eq_self, hP,
      sub_zero]
  have hBm (m n : ℕ) : (S.unstableInv ^ m) (d (n + m)) = d n := by
    refine pow_apply_of_backwardOrbit (w := fun k ↦ d (n + k)) (by simp) ?_ m
    intro k
    simpa only [Nat.add_assoc] using hB (n + k)
  have hle : ∀ n m, ‖d n‖ ≤ S.const * S.rate ^ m * ‖d‖ := by
    intro n m
    have h : d n = (S.unstableInv ^ m * (1 - S.proj)) (d (n + m)) := by
      rw [mul_apply_eq_comp, _root_.sub_apply (1 : E →L[ℝ] E) S.proj, one_apply_eq_self,
        hP, sub_zero, hBm]
    rw [h]
    exact (le_opNorm _ _).trans (mul_le_mul (S.norm_unstableInv_pow_mul_le m)
      (d.norm_coe_le_norm _) (norm_nonneg _) (by positivity [S.const_pos, S.rate_pos]))
  have ht : Tendsto (fun m ↦ S.const * S.rate ^ m * ‖d‖) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one S.rate_pos.le
      S.rate_lt_one).const_mul S.const).mul_const ‖d‖
  ext n
  have : d n = 0 := norm_le_zero_iff.1 (ge_of_tendsto' ht (hle n))
  rwa [BoundedContinuousFunction.sub_apply, sub_eq_zero] at this

end ContinuousLinearMap.HyperbolicSplitting
