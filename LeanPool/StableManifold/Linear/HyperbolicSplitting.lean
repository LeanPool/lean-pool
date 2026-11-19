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
* `ContinuousLinearMap.nonempty_hyperbolicSplitting`: in finite dimension, a hyperbolic splitting
  exists as soon as `Eₛ` and `Eᵤ` are complementary (for instance when `A` is hyperbolic,
  `isCompl_stableSubspace_unstableSubspace`);
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
* `nonempty_hyperbolicSplitting`: `P` is the projection onto `Eₛ` along `Eᵤ`
  (`Submodule.projection`), continuous in finite dimension (`LinearMap.toContinuousLinearMap`),
  and `A P = P A` since `A` preserves both subspaces (`map_mem_stableSubspace`,
  `map_mem_unstableSubspace`). No restriction to the subspaces is needed: `T = A (1 - P) + P`
  (`A` on `Eᵤ`, the identity on `Eₛ`) has `T P = P T = P` and is injective
  (`injOn_unstableSubspace`), hence a continuous linear equivalence
  (`LinearEquiv.ofInjectiveEndo`, `LinearEquiv.toContinuousLinearEquiv`). Then
  `B = T⁻¹ (1 - P) = (1 - P) T⁻¹`, and `B A = A B = 1 - P`, `B P = P B = 0` follow from
  `A (1 - P) = T (1 - P) = (1 - P) T`. Every orbit of `A P` tends to `0`, as
  `(A P)ⁿ⁺¹ v = Aⁿ⁺¹ (P v)` with `P v ∈ Eₛ`; so does every orbit of `B`, as `B v ∈ Eᵤ` and, for
  `u ∈ Eᵤ` with backward orbit `w`, `Bⁿ u = w n`. So `exists_norm_pow_le_mul_pow_of_tendsto`
  gives `‖(A P)ⁿ‖ ≤ C₁ λ₁ⁿ` and `‖Bⁿ‖ ≤ C₂ λ₂ⁿ`; as `Aⁿ P = (A P)ⁿ P`, the constants
  `C = max C₁ C₂ · max 1 (max ‖P‖ ‖1 - P‖)` and `λ = max λ₁ λ₂` work.
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
  proj_mul_proj : proj * proj = proj
  mul_proj_comm : A * proj = proj * A
  unstableInv_mul_proj : unstableInv * proj = 0
  proj_mul_unstableInv : proj * unstableInv = 0
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

theorem unstableInv_mul_one_sub_proj : S.unstableInv * (1 - S.proj) = S.unstableInv := by
  rw [mul_sub, mul_one, S.unstableInv_mul_proj, sub_zero]

theorem one_sub_proj_mul_unstableInv : (1 - S.proj) * S.unstableInv = S.unstableInv := by
  rw [sub_mul, one_mul, S.proj_mul_unstableInv, sub_zero]

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
private lemma const_mul_rate_pow_le (n : ℕ) : S.const * S.rate ^ n ≤ S.const :=
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

/-- **A hyperbolic splitting exists** in finite dimension when the stable and unstable subspaces
are complementary.

Proof: `P` is the projection onto `Eₛ` along `Eᵤ`; `T = A (1 - P) + P` is invertible, and
`B = T⁻¹ (1 - P)`. The orbits of `A P` and of `B` tend to `0`, so their powers decay
geometrically (`exists_norm_pow_le_mul_pow_of_tendsto`), and `Aⁿ P = (A P)ⁿ P`. -/
theorem nonempty_hyperbolicSplitting [FiniteDimensional ℝ E] {A : E →L[ℝ] E}
    (h : IsCompl A.stableSubspace A.unstableSubspace) : Nonempty A.HyperbolicSplitting := by
  -- The projection `P` onto `Eₛ` along `Eᵤ`, continuous in finite dimension.
  let P : E →L[ℝ] E :=
    LinearMap.toContinuousLinearMap (A.stableSubspace.projection A.unstableSubspace h)
  have hPs (x : E) : P x ∈ A.stableSubspace := Submodule.projection_apply_mem h x
  have hPu (x : E) : x - P x ∈ A.unstableSubspace := Submodule.sub_projection_mem h x
  have hPself {x : E} (hx : x ∈ A.stableSubspace) : P x = x :=
    Submodule.projection_apply_of_mem_left h hx
  have hPzero {x : E} : P x = 0 ↔ x ∈ A.unstableSubspace :=
    Submodule.projection_apply_eq_zero_iff h
  have hPP : P * P = P := by
    ext x
    exact hPself (hPs x)
  -- `A` commutes with `P`, since it preserves `Eₛ` and `Eᵤ`.
  have hAP : A * P = P * A := by
    ext x
    have e : A x = A (P x) + A (x - P x) := by rw [← map_add, add_sub_cancel]
    change A (P x) = P (A x)
    rw [e, map_add, hPself (map_mem_stableSubspace (hPs x)),
      hPzero.2 (map_mem_unstableSubspace (hPu x)), add_zero]
  have hP1 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
  have hP2 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  -- `T = A (1 - P) + P` (`A` on `Eᵤ`, the identity on `Eₛ`) is injective, hence invertible.
  set T : E →L[ℝ] E := A * (1 - P) + P with hT
  have hTP : T * P = P := by rw [hT, add_mul, mul_assoc, hP1, mul_zero, zero_add, hPP]
  have hPT : P * T = P := by
    rw [hT, mul_add, ← mul_assoc, ← hAP, mul_assoc, hP2, mul_zero, zero_add, hPP]
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hPx : P x = 0 := by rw [← hPT, mul_apply_eq_comp, hx, map_zero]
    have hAx : A x = A 0 := by
      rw [map_zero, ← hx, hT, add_apply, hPx, add_zero, mul_apply_eq_comp, sub_apply,
        one_apply_eq_self, hPx, sub_zero]
    exact injOn_unstableSubspace A (hPzero.1 hPx) A.unstableSubspace.zero_mem hAx
  let e : E ≃L[ℝ] E :=
    (LinearEquiv.ofInjectiveEndo (T : E →ₗ[ℝ] E) hTinj).toContinuousLinearEquiv
  have he (x : E) : e x = T x := rfl
  set R : E →L[ℝ] E := (e.symm : E →L[ℝ] E)
  have hTR : T * R = 1 := by
    ext x
    rw [mul_apply_eq_comp, ← he]
    exact e.apply_symm_apply x
  have hRT : R * T = 1 := by
    ext x
    rw [mul_apply_eq_comp, ← he]
    exact e.symm_apply_apply x
  have hRP : R * P = P := calc
    R * P = R * (T * P) := by rw [hTP]
    _ = P := by rw [← mul_assoc, hRT, one_mul]
  have hPR : P * R = P := calc
    P * R = P * T * R := by rw [hPT]
    _ = P := by rw [mul_assoc, hTR, mul_one]
  -- `B = T⁻¹ (1 - P) = (1 - P) T⁻¹` inverts `A` on `Eᵤ`.
  set B : E →L[ℝ] E := R * (1 - P) with hB
  have hB' : B = (1 - P) * R := by rw [hB, mul_sub, sub_mul, mul_one, one_mul, hRP, hPR]
  have hA1 : (1 - P) * A = A * (1 - P) := by rw [sub_mul, mul_sub, one_mul, mul_one, hAP]
  have hA2 : A * (1 - P) = T * (1 - P) := by
    rw [mul_sub T, mul_one, hTP, hT, add_sub_cancel_right]
  have hA3 : A * (1 - P) = (1 - P) * T := by
    rw [sub_mul, one_mul, hPT, hT, add_sub_cancel_right]
  have hBA : B * A = 1 - P := by
    rw [hB, mul_assoc, hA1, hA2, ← mul_assoc, hRT, one_mul]
  have hAB : A * B = 1 - P := by
    rw [hB', ← mul_assoc, hA3, mul_assoc, hTR, mul_one]
  have hBP : B * P = 0 := by rw [hB, mul_assoc, hP1, mul_zero]
  have hPB : P * B = 0 := by rw [hB, ← mul_assoc, hPR, hP2]
  -- Geometric decay on `Eₛ`: the orbits of `A P` tend to `0`.
  have hc : Commute A P := hAP
  have hQ (n : ℕ) : (A * P) ^ n * P = A ^ n * P := by
    rw [hc.mul_pow, mul_assoc, ← pow_succ, IsIdempotentElem.pow_succ_eq n hPP]
  have hQt (v : E) : Tendsto (fun n : ℕ ↦ ((A * P) ^ n) v) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have hv (n : ℕ) : ((A * P) ^ (n + 1)) v = (A ^ (n + 1)) (P v) := by
      rw [hc.mul_pow, mul_apply_eq_comp, IsIdempotentElem.pow_succ_eq n hPP]
    simp_rw [hv]
    exact (tendsto_add_atTop_iff_nat 1).2 (mem_stableSubspace.1 (hPs v))
  obtain ⟨C₁, r₁, hC₁, hr₁, hr₁', hCr₁⟩ := exists_norm_pow_le_mul_pow_of_tendsto (A * P) hQt
  -- Geometric decay on `Eᵤ`: the orbits of `B` tend to `0`, being backward orbits of `A`.
  have hBu {u : E} (hu : u ∈ A.unstableSubspace) :
      Tendsto (fun n : ℕ ↦ (B ^ n) u) atTop (𝓝 0) := by
    obtain ⟨w, hw0, hwA, hwt⟩ := hu
    have hwmem (n : ℕ) : w n ∈ A.unstableSubspace :=
      ⟨fun k ↦ w (k + n), by simp, fun k ↦ by
        change A (w (k + 1 + n)) = w (k + n); rw [Nat.add_right_comm]; exact hwA _,
        (tendsto_add_atTop_iff_nat n).2 hwt⟩
    have hBw (n : ℕ) : B (w n) = w (n + 1) := by
      rw [← hwA n, ← mul_apply_eq_comp B A, hBA, sub_apply, one_apply_eq_self,
        hPzero.2 (hwmem (n + 1)), sub_zero]
    have hBpow (n : ℕ) : (B ^ n) u = w n := by
      induction n with
      | zero => rw [pow_zero, one_apply_eq_self, hw0]
      | succ n ih => rw [pow_succ', mul_apply_eq_comp, ih, hBw]
    exact hwt.congr fun n ↦ (hBpow n).symm
  have hBt (v : E) : Tendsto (fun n : ℕ ↦ (B ^ n) v) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have hBv : B v ∈ A.unstableSubspace := by
      rw [← hPzero, ← mul_apply_eq_comp P B, hPB, zero_apply]
    simp_rw [pow_succ, mul_apply_eq_comp]
    exact hBu hBv
  obtain ⟨C₂, r₂, hC₂, hr₂, hr₂', hCr₂⟩ := exists_norm_pow_le_mul_pow_of_tendsto B hBt
  -- The constants.
  have hK : 1 ≤ max 1 (max ‖P‖ ‖1 - P‖) := le_max_left _ _
  have hCr (n : ℕ) {C r a : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (ha : 0 ≤ a) (hCm : C ≤ max C₁ C₂)
      (hrm : r ≤ max r₁ r₂) (ham : a ≤ max 1 (max ‖P‖ ‖1 - P‖)) :
      C * r ^ n * a ≤ max C₁ C₂ * max 1 (max ‖P‖ ‖1 - P‖) * max r₁ r₂ ^ n := by
    have hpow : r ^ n ≤ max r₁ r₂ ^ n := pow_le_pow_left₀ hr hrm n
    have hproduct : C * r ^ n ≤ max C₁ C₂ * max r₁ r₂ ^ n :=
      mul_le_mul hCm hpow (pow_nonneg hr n) (hC.trans hCm)
    calc
      C * r ^ n * a ≤ max C₁ C₂ * max r₁ r₂ ^ n * max 1 (max ‖P‖ ‖1 - P‖) :=
        mul_le_mul hproduct ham ha (mul_nonneg (hC.trans hCm) ((pow_nonneg hr n).trans hpow))
      _ = _ := mul_right_comm _ _ _
  refine ⟨{
    proj := P
    unstableInv := B
    const := max C₁ C₂ * max 1 (max ‖P‖ ‖1 - P‖)
    rate := max r₁ r₂
    proj_mul_proj := hPP
    mul_proj_comm := hAP
    unstableInv_mul_proj := hBP
    proj_mul_unstableInv := hPB
    mul_unstableInv := hAB
    unstableInv_mul := hBA
    one_le_const := one_le_mul_of_one_le_of_one_le (hC₁.trans (le_max_left _ _)) hK
    rate_pos := hr₁.trans_le (le_max_left _ _)
    rate_lt_one := max_lt hr₁' hr₂'
    norm_pow_mul_proj_le := fun n ↦ ?_
    norm_unstableInv_pow_mul_le := fun n ↦ ?_ }⟩
  · calc ‖A ^ n * P‖ = ‖(A * P) ^ n * P‖ := by rw [hQ]
      _ ≤ ‖(A * P) ^ n‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ C₁ * r₁ ^ n * ‖P‖ := mul_le_mul_of_nonneg_right (hCr₁ n) (norm_nonneg _)
      _ ≤ _ := hCr n (zero_le_one.trans hC₁) hr₁.le (norm_nonneg _)
          (le_max_left _ _) (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
  · calc ‖B ^ n * (1 - P)‖ ≤ ‖B ^ n‖ * ‖1 - P‖ := norm_mul_le _ _
      _ ≤ C₂ * r₂ ^ n * ‖1 - P‖ := mul_le_mul_of_nonneg_right (hCr₂ n) (norm_nonneg _)
      _ ≤ _ := hCr n (zero_le_one.trans hC₂) hr₂.le (norm_nonneg _)
          (le_max_right _ _) (le_max_right _ _) ((le_max_right _ _).trans (le_max_right _ _))

end ContinuousLinearMap
