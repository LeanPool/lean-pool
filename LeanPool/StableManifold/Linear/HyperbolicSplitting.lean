/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.Linear.Subspaces

/-!
# Hyperbolic splittings with exponential estimates

`ContinuousLinearMap.HyperbolicSplitting A` bundles what the Lyapunov–Perron method needs about a
linear map `A` (an exponential dichotomy): the projection `P = S.proj` onto the stable subspace
along the unstable one, the inverse `B = S.unstableInv` of `A` on the unstable subspace (extended
by `0` on the stable subspace), and constants `C ≥ 1`, `0 < λ < 1` with

  `‖Aⁿ P‖ ≤ C λⁿ`, `‖Bⁿ (1 - P)‖ ≤ C λⁿ` for all `n`.

Everything is stated with endomorphisms of `E` (`*` is composition), so that the analysis never
meets subtypes.

* `HyperbolicSplitting.range_proj`, `HyperbolicSplitting.ker_proj`: the range of `P` is the
  stable subspace and its kernel the unstable one; so the splitting determines `P` and
  `IsCompl Eₛ Eᵤ` (`HyperbolicSplitting.isCompl`);
* `HyperbolicSplitting.bound = 3 C / (1 - λ)` and `HyperbolicSplitting.decayRate = (1 + λ) / 2`:
  the constants of the Lyapunov–Perron estimates (`StableManifold.Perron.Operator`).

## Proofs

The algebraic identities between `A`, `P` and `B` (`unstableInv_mul_one_sub_proj`,
`mul_unstableInv_pow_succ`, `proj_mul_unstableInv_pow_succ`, …) and the bounds `‖P‖ ≤ C`,
`‖1 - P‖ ≤ C` are short rewrites with the fields of the structure.

* `proj_apply_eq_self_iff`: if `P x = x`, then `‖Aⁿ x‖ = ‖(Aⁿ P) x‖ ≤ C λⁿ ‖x‖ → 0`. Conversely,
  `Bⁿ (1 - P) Aⁿ = 1 - P` (induction on `n`, from `B (1 - P) = B` and `B A = 1 - P`), so for
  `x ∈ Eₛ`, `‖(1 - P) x‖ = ‖Bⁿ (1 - P) (Aⁿ x)‖ ≤ C ‖Aⁿ x‖ → 0`.
* `proj_apply_eq_zero_iff`: if `P x = 0`, then `n ↦ Bⁿ x` is a backward orbit of `x`
  (`A Bⁿ⁺¹ = (1 - P) Bⁿ` and `P Bⁿ⁺¹ = 0`) with `‖Bⁿ x‖ = ‖Bⁿ (1 - P) x‖ ≤ C λⁿ ‖x‖`.
  Conversely, a backward orbit `w` of `x` has `Aⁿ (w n) = x`, so `P x = (Aⁿ P) (w n)`
  (`pow_mul_proj_comm`), of norm `≤ C ‖w n‖ → 0`.
* `range_proj`, `ker_proj`: the two characterizations and `P² = P`. `isCompl`: the range and the
  kernel of an idempotent are complementary (`LinearMap.IsIdempotentElem.isCompl`).
-/

@[expose] public section

open Filter Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A **hyperbolic splitting** of `A` (an exponential dichotomy): a projection `P = proj`
commuting with `A`, a map `B = unstableInv` inverting `A` on the range of `1 - P` and vanishing on
the range of `P`, and exponential estimates `‖Aⁿ P‖ ≤ C λⁿ`, `‖Bⁿ (1 - P)‖ ≤ C λⁿ` with `C ≥ 1`
and `0 < λ < 1`. The range of `P` is then the stable subspace of `A` and its kernel the unstable
subspace (`HyperbolicSplitting.range_proj`, `HyperbolicSplitting.ker_proj`). -/
structure HyperbolicSplitting (A : E →L[ℝ] E) where
  /-- The projection onto the stable subspace along the unstable subspace. -/
  proj : E →L[ℝ] E
  /-- The inverse of `A` on the unstable subspace, extended by `0` on the stable subspace. -/
  unstableInv : E →L[ℝ] E
  /-- The constant `C` of the exponential estimates. -/
  const : ℝ
  /-- The rate `λ` of the exponential estimates. -/
  rate : ℝ
  unstableInv_mul_proj : unstableInv * proj = 0
  mul_unstableInv : A * unstableInv = 1 - proj
  unstableInv_mul : unstableInv * A = 1 - proj
  one_le_const : 1 ≤ const
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  norm_pow_mul_proj_le : ∀ n : ℕ, ‖A ^ n * proj‖ ≤ const * rate ^ n
  norm_unstableInv_pow_mul_le : ∀ n : ℕ, ‖unstableInv ^ n * (1 - proj)‖ ≤ const * rate ^ n

namespace HyperbolicSplitting

variable {A : E →L[ℝ] E} (S : A.HyperbolicSplitting)

/-- The constant `3 C / (1 - λ)` of the Lyapunov–Perron estimates: it bounds the norm of the
linear Lyapunov–Perron operator, also in the weighted norm with weights `decayRate ^ n`. -/
noncomputable def bound : ℝ := 3 * S.const / (1 - S.rate)

/-- The decay rate `(1 + λ) / 2 ∈ (λ, 1)` of the orbits on the stable manifold. -/
noncomputable def decayRate : ℝ := (1 + S.rate) / 2

theorem const_pos : 0 < S.const := zero_lt_one.trans_le S.one_le_const

theorem bound_pos : 0 < S.bound :=
  div_pos (by linarith [S.one_le_const]) (by linarith [S.rate_lt_one])

theorem rate_lt_decayRate : S.rate < S.decayRate := by
  unfold decayRate; linarith [S.rate_lt_one]

theorem decayRate_lt_one : S.decayRate < 1 := by
  unfold decayRate; linarith [S.rate_lt_one]

theorem decayRate_pos : 0 < S.decayRate := S.rate_pos.trans S.rate_lt_decayRate

theorem norm_proj_le : ‖S.proj‖ ≤ S.const := by
  simpa using S.norm_pow_mul_proj_le 0

theorem norm_one_sub_proj_le : ‖1 - S.proj‖ ≤ S.const := by
  simpa using S.norm_unstableInv_pow_mul_le 0

/-- The stable projection is idempotent. -/
theorem proj_mul_proj : S.proj * S.proj = S.proj := by
  have h : (1 - S.proj) * S.proj = 0 := by
    rw [← S.mul_unstableInv, mul_assoc, S.unstableInv_mul_proj, mul_zero]
  rw [sub_mul, one_mul] at h
  exact (sub_eq_zero.mp h).symm

/-- The stable projection commutes with the original map. -/
theorem mul_proj_comm : A * S.proj = S.proj * A := by
  have h : A * (1 - S.proj) = (1 - S.proj) * A := calc
    _ = A * (S.unstableInv * A) := congrArg (A * ·) S.unstableInv_mul.symm
    _ = (A * S.unstableInv) * A := (mul_assoc _ _ _).symm
    _ = _ := congrArg (· * A) S.mul_unstableInv
  simpa [mul_sub, sub_mul] using h

theorem unstableInv_mul_one_sub_proj : S.unstableInv * (1 - S.proj) = S.unstableInv := by
  rw [mul_sub, mul_one, S.unstableInv_mul_proj, sub_zero]

theorem one_sub_proj_mul_unstableInv : (1 - S.proj) * S.unstableInv = S.unstableInv := calc
  _ = (S.unstableInv * A) * S.unstableInv := congrArg (· * S.unstableInv) S.unstableInv_mul.symm
  _ = S.unstableInv * (A * S.unstableInv) := mul_assoc _ _ _
  _ = S.unstableInv * (1 - S.proj) := congrArg (S.unstableInv * ·) S.mul_unstableInv
  _ = _ := S.unstableInv_mul_one_sub_proj

/-- The image of the unstable inverse lies in the kernel of the stable projection. -/
theorem proj_mul_unstableInv : S.proj * S.unstableInv = 0 := by
  simpa [sub_mul] using S.one_sub_proj_mul_unstableInv

theorem proj_mul_one_sub_proj : S.proj * (1 - S.proj) = 0 := by
  rw [mul_sub, mul_one, S.proj_mul_proj, sub_self]

theorem one_sub_proj_mul_proj : (1 - S.proj) * S.proj = 0 := by
  rw [sub_mul, one_mul, S.proj_mul_proj, sub_self]

/-- `Aⁿ` commutes with `P`. -/
theorem pow_mul_proj_comm (n : ℕ) : A ^ n * S.proj = S.proj * A ^ n :=
  (Commute.pow_left S.mul_proj_comm n).eq

/-- `B Bⁿ⁺¹ = Bⁿ⁺¹ (1 - P)`, so `‖Bⁿ⁺¹‖ ≤ C λⁿ⁺¹`. -/
theorem norm_unstableInv_pow_succ_le (n : ℕ) :
    ‖S.unstableInv ^ (n + 1)‖ ≤ S.const * S.rate ^ (n + 1) := by
  have h : S.unstableInv ^ (n + 1) = S.unstableInv ^ (n + 1) * (1 - S.proj) := by
    rw [pow_succ, mul_assoc, S.unstableInv_mul_one_sub_proj]
  rw [h]
  exact S.norm_unstableInv_pow_mul_le (n + 1)

/-- `A Bⁿ⁺¹ = (1 - P) Bⁿ`: `n ↦ Bⁿ x` is a backward orbit of `(1 - P) x`. -/
theorem mul_unstableInv_pow_succ (n : ℕ) :
    A * S.unstableInv ^ (n + 1) = (1 - S.proj) * S.unstableInv ^ n := by
  rw [pow_succ', ← mul_assoc, S.mul_unstableInv]

/-- `P Bⁿ⁺¹ = 0`: the range of `B` lies in the kernel of `P`. -/
theorem proj_mul_unstableInv_pow_succ (n : ℕ) : S.proj * S.unstableInv ^ (n + 1) = 0 := by
  rw [pow_succ', ← mul_assoc, S.proj_mul_unstableInv, zero_mul]

/-- `C λⁿ ≤ C`. -/
theorem const_mul_rate_pow_le (n : ℕ) : S.const * S.rate ^ n ≤ S.const :=
  mul_le_of_le_one_right S.const_pos.le (pow_le_one₀ S.rate_pos.le S.rate_lt_one.le)

/-- `C λⁿ a → 0`. -/
private lemma tendsto_const_mul_rate_pow_mul (a : ℝ) :
    Tendsto (fun n : ℕ ↦ S.const * S.rate ^ n * a) atTop (𝓝 0) := by
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one S.rate_pos.le S.rate_lt_one).const_mul
    S.const).mul_const a

/-- `Bⁿ (1 - P) Aⁿ = 1 - P`, by induction from `B (1 - P) A = B A = 1 - P`. -/
private lemma unstableInv_pow_mul_one_sub_proj_mul_pow (n : ℕ) :
    S.unstableInv ^ n * (1 - S.proj) * A ^ n = 1 - S.proj := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc S.unstableInv ^ (n + 1) * (1 - S.proj) * A ^ (n + 1)
        = S.unstableInv ^ n * (S.unstableInv * (1 - S.proj) * A) * A ^ n := by
          rw [pow_succ, pow_succ']; simp only [mul_assoc]
      _ = 1 - S.proj := by rw [S.unstableInv_mul_one_sub_proj, S.unstableInv_mul, ih]

/-- The fixed points of `P` are the vectors of the stable subspace.

Proof: `Aⁿ x = Aⁿ P x` decays; conversely `(1 - P) x = Bⁿ (1 - P) Aⁿ x → 0`. -/
theorem proj_apply_eq_self_iff {x : E} : S.proj x = x ↔ x ∈ A.stableSubspace := by
  constructor
  · intro hx
    refine squeeze_zero_norm (fun n ↦ ?_) (S.tendsto_const_mul_rate_pow_mul ‖x‖)
    calc ‖(A ^ n) x‖ = ‖(A ^ n * S.proj) x‖ := by rw [mul_apply_eq_comp, hx]
      _ ≤ ‖A ^ n * S.proj‖ * ‖x‖ := le_opNorm _ _
      _ ≤ S.const * S.rate ^ n * ‖x‖ := by gcongr; exact S.norm_pow_mul_proj_le n
  · intro hx
    have hle (n : ℕ) : ‖(1 - S.proj) x‖ ≤ S.const * ‖(A ^ n) x‖ := by
      calc ‖(1 - S.proj) x‖ = ‖(S.unstableInv ^ n * (1 - S.proj)) ((A ^ n) x)‖ := by
            rw [← mul_apply_eq_comp, S.unstableInv_pow_mul_one_sub_proj_mul_pow]
        _ ≤ ‖S.unstableInv ^ n * (1 - S.proj)‖ * ‖(A ^ n) x‖ := le_opNorm _ _
        _ ≤ S.const * S.rate ^ n * ‖(A ^ n) x‖ := by
            gcongr; exact S.norm_unstableInv_pow_mul_le n
        _ ≤ S.const * ‖(A ^ n) x‖ := by gcongr; exact S.const_mul_rate_pow_le n
    have h0 : ‖(1 - S.proj) x‖ ≤ 0 :=
      ge_of_tendsto' (by simpa using (mem_stableSubspace.1 hx).norm.const_mul S.const) hle
    rw [norm_le_zero_iff, sub_apply, one_apply_eq_self, sub_eq_zero] at h0
    exact h0.symm

/-- The kernel of `P` is the unstable subspace.

Proof: if `P x = 0`, `n ↦ Bⁿ x` is a backward orbit tending to `0`; conversely
`P x = Aⁿ P (w n)` for a backward orbit `w` of `x`. -/
theorem proj_apply_eq_zero_iff {x : E} : S.proj x = 0 ↔ x ∈ A.unstableSubspace := by
  constructor
  · intro hx
    have hx' : (1 - S.proj) x = x := by rw [sub_apply, one_apply_eq_self, hx, sub_zero]
    refine ⟨fun n ↦ (S.unstableInv ^ n) x, by simp, fun n ↦ ?_, ?_⟩
    · rw [← mul_apply_eq_comp, S.mul_unstableInv_pow_succ, mul_apply_eq_comp]
      cases n with
      | zero => simpa using hx'
      | succ n =>
        rw [sub_apply, one_apply_eq_self, ← mul_apply_eq_comp S.proj,
          S.proj_mul_unstableInv_pow_succ, zero_apply, sub_zero]
    · refine squeeze_zero_norm (fun n ↦ ?_) (S.tendsto_const_mul_rate_pow_mul ‖x‖)
      calc ‖(S.unstableInv ^ n) x‖ = ‖(S.unstableInv ^ n * (1 - S.proj)) x‖ := by
            rw [mul_apply_eq_comp, hx']
        _ ≤ ‖S.unstableInv ^ n * (1 - S.proj)‖ * ‖x‖ := le_opNorm _ _
        _ ≤ S.const * S.rate ^ n * ‖x‖ := by gcongr; exact S.norm_unstableInv_pow_mul_le n
  · rintro ⟨w, hw0, hwA, hwt⟩
    have hpow := pow_apply_of_backwardOrbit hw0 hwA
    have hle (n : ℕ) : ‖S.proj x‖ ≤ S.const * ‖w n‖ := by
      calc ‖S.proj x‖ = ‖(A ^ n * S.proj) (w n)‖ := by
            rw [S.pow_mul_proj_comm, mul_apply_eq_comp, hpow]
        _ ≤ ‖A ^ n * S.proj‖ * ‖w n‖ := le_opNorm _ _
        _ ≤ S.const * S.rate ^ n * ‖w n‖ := by gcongr; exact S.norm_pow_mul_proj_le n
        _ ≤ S.const * ‖w n‖ := by gcongr; exact S.const_mul_rate_pow_le n
    have h0 : ‖S.proj x‖ ≤ 0 := ge_of_tendsto' (by simpa using hwt.norm.const_mul S.const) hle
    exact norm_le_zero_iff.1 h0

/-- The range of `P` is the stable subspace. -/
theorem range_proj : LinearMap.range (S.proj : E →ₗ[ℝ] E) = A.stableSubspace := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [coe_coe, ← S.proj_apply_eq_self_iff, ← mul_apply_eq_comp, S.proj_mul_proj]
  · exact fun hx ↦ ⟨x, S.proj_apply_eq_self_iff.2 hx⟩

/-- The kernel of `P` is the unstable subspace. -/
theorem ker_proj : LinearMap.ker (S.proj : E →ₗ[ℝ] E) = A.unstableSubspace := by
  ext x
  rw [LinearMap.mem_ker, coe_coe]
  exact S.proj_apply_eq_zero_iff

include S in
/-- A hyperbolic splitting makes the stable and unstable subspaces complementary. -/
theorem isCompl : IsCompl A.stableSubspace A.unstableSubspace := by
  have h : IsIdempotentElem (S.proj : E →ₗ[ℝ] E) := by
    ext x
    exact congr($(S.proj_mul_proj) x)
  rw [← S.range_proj, ← S.ker_proj]
  exact LinearMap.IsIdempotentElem.isCompl h

end HyperbolicSplitting

end ContinuousLinearMap
