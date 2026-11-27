/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.MeasureSpaces.Spectral.Basic
public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Projection

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Coefficient characterisation of Besov spaces for spectral schemes

For a spectral scheme `(e_i, lvl)` in a Hilbert space `H`, the truncation
`P n f = ∑_{lvl i < n} ⟨e_i, f⟩ e_i` is the orthogonal projection onto the approximants, so
the scheme is a projection scheme with bound `1` (`SpectralScheme.projectionScheme`), and the
union of the approximants is dense.  The dyadic block

`Δ_k f = P (2^(k+1)) f - P (2^k) f = ∑_{2^k ≤ lvl i < 2^(k+1)} ⟨e_i, f⟩ e_i`

has `‖Δ_k f‖² = ∑_{2^k ≤ lvl i < 2^(k+1)} |⟨e_i, f⟩|²`.  The general block characterisation
of `ApproximationSpaces.Decompositions.Projection` then gives, for `s > 0`:

* **the coefficient characterisation of `A^s_q`** (`memApprox_iff_blockNorm_lt_top`):
  `f ∈ A^s_q` iff `(2^(ks) (∑_{2^k ≤ lvl i < 2^(k+1)} |⟨e_i, f⟩|²)^(1/2))_k ∈ ℓ_q`; on the
  torus with the Fourier basis this is the Littlewood–Paley description of `B^s_{2,q}` with
  sharp dyadic cut-offs;
* **`H^s = A^s_2`** (`memApprox_two_iff`): the Sobolev space of order `s` is the approximation
  space with fine index `2`, i.e. `H^s = B^s_{2,2}`.
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal InnerProductSpace lp

namespace SpectralScheme

open ApproximationScheme ENNReal

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : SpectralScheme ι H)

/-- Truncation is additive. -/
theorem truncate_add (n : ℕ) (f g : H) : S.truncate n (f + g) = S.truncate n f + S.truncate n g :=
by
  simp only [truncate, map_add, lp.coeFn_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Truncation is homogeneous. -/
theorem truncate_smul (n : ℕ) (c : ℂ) (f : H) : S.truncate n (c • f) = c • S.truncate n f := by
  simp only [truncate, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
    Finset.smul_sum]

/-- Truncation does not increase the norm, by Bessel's inequality. -/
theorem norm_truncate_le (n : ℕ) (f : H) : ‖S.truncate n f‖ ≤ ‖f‖ := by
  rw [← S.basis.repr.norm_map, ← S.basis.repr.norm_map f]
  refine lp.norm_mono (by norm_num) fun i => ?_
  rw [repr_truncate]
  split_ifs <;> simp

/-- The truncation as a bounded linear operator of norm at most `1`. -/
noncomputable def truncateCLM (n : ℕ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := S.truncate n
      map_add' := S.truncate_add n
      map_smul' := S.truncate_smul n }
    1 fun f => by rw [one_mul]; exact S.norm_truncate_le n f

/-- The bounded linear truncation is the truncation. -/
theorem truncateCLM_apply (n : ℕ) (f : H) : S.truncateCLM n f = S.truncate n f := rfl

/-- The truncation fixes the approximants. -/
theorem truncate_of_mem {n : ℕ} {a : H} (ha : a ∈ S.span n) : S.truncate n a = a := by
  refine S.basis.repr.injective (lp.ext (funext fun i => ?_))
  rw [repr_truncate]
  split_ifs with hi
  · rfl
  · exact (S.repr_eq_zero_of_mem_span ha (not_lt.1 hi)).symm

/-- **The spectral scheme as a projection scheme**, with the truncations as projections of
norm at most `1`. -/
noncomputable def projectionScheme : S.toScheme.ProjectionScheme where
  P n := (S.truncateCLM n).restrictScalars ℝ
  mem n f := S.truncate_mem_span n f
  proj n a ha := S.truncate_of_mem ha
  bound := 1
  norm_le n := by
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The projections of the spectral projection scheme are the truncations. -/
theorem projectionScheme_P (n : ℕ) (f : H) : S.projectionScheme.P n f = S.truncate n f := rfl

/-- The approximants of all complexities span the span of the basis. -/
theorem iUnion_span : (⋃ n, (S.span n : Set H)) = Submodule.span ℂ (Set.range S.basis) := by
  apply le_antisymm
  · exact Set.iUnion_subset fun n => Submodule.span_mono (Set.image_subset_range _ _)
  · have hdir : Directed (· ≤ ·) S.span := S.span_mono.directed_le
    have h : Submodule.span ℂ (Set.range S.basis) ≤ ⨆ n, S.span n := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.mem_iSup_of_mem (S.level i + 1)
        (Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩)
    intro x hx
    have := h hx
    rw [Submodule.mem_iSup_of_directed _ hdir] at this
    exact Set.mem_iUnion.2 this

/-- The union of the approximants is dense. -/
theorem closure_iUnion_toScheme : closure (⋃ n, S.toScheme n) = Set.univ := by
  have h : (⋃ n, S.toScheme n) = (Submodule.span ℂ (Set.range S.basis) : Set H) := S.iUnion_span
  rw [h, ← Submodule.topologicalClosure_coe, S.basis.dense_span, Submodule.top_coe]

/-- The coefficients of a dyadic block are those of `f` with `2^k ≤ lvl i < 2^(k+1)`. -/
theorem repr_block (k : ℕ) (f : H) (i : ι) :
    S.basis.repr (S.projectionScheme.block k f) i =
      if 2 ^ k ≤ S.level i ∧ S.level i < 2 ^ (k + 1) then S.basis.repr f i else 0 := by
  rw [ProjectionScheme.block, S.projectionScheme_P, S.projectionScheme_P, map_sub, lp.coeFn_sub,
    Pi.sub_apply, repr_truncate, repr_truncate]
  by_cases h1 : S.level i < 2 ^ k
  · have h2 : S.level i < 2 ^ (k + 1) := h1.trans (Nat.pow_lt_pow_right one_lt_two
    (Nat.lt_succ_self k))
    simp [h1, h2, not_le.2 h1]
  · by_cases h2 : S.level i < 2 ^ (k + 1)
    · simp [h1, h2, not_lt.1 h1]
    · simp [h1, h2]

/-- `‖Δ_k f‖² = ∑_{2^k ≤ lvl i < 2^(k+1)} |⟨e_i, f⟩|²`. -/
theorem enorm_block_sq (k : ℕ) (f : H) :
    ‖S.projectionScheme.block k f‖ₑ ^ 2 = ∑' i,
      if 2 ^ k ≤ S.level i ∧ S.level i < 2 ^ (k + 1) then ‖S.basis.repr f i‖ₑ ^ 2 else 0 := by
  rw [← S.basis.repr.eNorm_map, lp.enorm_sq_eq_tsum]
  congr 1; funext i
  rw [repr_block]
  split_ifs <;> simp

/-- **Coefficient characterisation of `A^s_q`** for a spectral scheme in a Hilbert space: for
`s > 0`, `f ∈ A^s_q` iff `‖P 1 f‖ + ‖(2^(ks) ‖Δ_k f‖)_k‖_q < ∞`, where
`‖Δ_k f‖² = ∑_{2^k ≤ lvl i < 2^(k+1)} |⟨e_i, f⟩|²` (`enorm_block_sq`). -/
theorem memApprox_iff_blockNorm_lt_top {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : H} : S.toScheme.MemApprox s q f ↔ S.projectionScheme.blockNorm s q f < ∞ :=
  S.projectionScheme.memApprox_iff_blockNorm_lt_top S.closure_iUnion_toScheme hs hq

/-- Membership in `ℓ²` through the series of squares in `ℝ≥0∞`. -/
theorem mem_l2_iff (g : ι → ℂ) : Memℓp g 2 ↔ ∑' i, ‖g i‖ₑ ^ 2 ≠ ∞ := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  have h : ∀ i, ‖g i‖ₑ ^ 2 = ((‖g i‖₊ ^ 2 : NNReal) : ℝ≥0∞) := fun i => by
    rw [ENNReal.coe_pow]; rfl
  simp_rw [h, ENNReal.tsum_coe_ne_top_iff_summable_coe]
  simp

/-- The squared Sobolev weight `(1 + lvl i)^(2s)` in `ℝ≥0∞`. -/
theorem enorm_weight_mul_sq (s : ℝ) (i : ι) (z : ℂ) :
    ‖(S.weight s i : ℂ) * z‖ₑ ^ 2 = ((1 + S.level i : ℕ) : ℝ≥0∞) ^ (2 * s) * ‖z‖ₑ ^ 2 := by
  rw [eNorm_mul, mul_pow, ← ofReal_norm, S.norm_ofReal_weight, weight,
    ← ENNReal.ofReal_rpow_of_pos (by positivity), ENNReal.ofReal_natCast, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  congr 2
  push_cast; ring

/-- The dyadic block containing a level `m ≥ 1` is the one with `k = ⌊log₂ m⌋`. -/
theorem tsum_ite_block_eq (s : ℝ) (m : ℕ) :
    (∑' k : ℕ, if 2 ^ k ≤ m ∧ m < 2 ^ (k + 1) then dyadicWeight (2 * s) k else 0) =
      if m = 0 then 0 else dyadicWeight (2 * s) (Nat.log 2 m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hk0 : 2 ^ Nat.log 2 m ≤ m ∧ m < 2 ^ (Nat.log 2 m + 1) :=
    ⟨Nat.pow_log_le_self 2 hm.ne', Nat.lt_pow_succ_log_self Nat.one_lt_two m⟩
  rw [tsum_eq_single (Nat.log 2 m) fun k hk => ite_eq_right_iff.2 fun h =>
    absurd (Nat.log_eq_of_pow_le_of_lt_pow h.1 h.2).symm hk]
  simp [hk0, hm.ne']

/-- **`H^s = B^s_{2,2}`** for a spectral scheme: for `s > 0`, `f ∈ A^s_2` if and only if
`∑_i (1 + lvl i)^(2s) |⟨e_i, f⟩|² < ∞`, i.e. `f` lies in the Sobolev space of order `s`. -/
theorem memApprox_two_iff {s : ℝ} (hs : 0 < s) (f : H) :
    S.toScheme.MemApprox s 2 f ↔ Memℓp (fun i => (S.weight s i : ℂ) * S.basis.repr f i) 2 := by
  set e : ι → ℝ≥0∞ := fun i => ‖S.basis.repr f i‖ₑ ^ 2
  set Wt : ι → ℝ≥0∞ := fun i => ((1 + S.level i : ℕ) : ℝ≥0∞) ^ (2 * s)
  set blk : ℕ → ι → Prop := fun k i => 2 ^ k ≤ S.level i ∧ S.level i < 2 ^ (k + 1)
  set B : ℝ≥0∞ := ∑' k, dyadicWeight (2 * s) k * ‖S.projectionScheme.block k f‖ₑ ^ 2
  set T : ℝ≥0∞ := ∑' i, Wt i * e i
  -- the block sum as a sum over the coefficients
  have hB : B = ∑' i, (∑' k : ℕ, if blk k i then dyadicWeight (2 * s) k else 0) * e i := by
    simp only [B, enorm_block_sq]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [tsum_comm]
    congr 1; funext i
    rw [← ENNReal.tsum_mul_right]
    congr 1; funext k
    simp only [blk, e]
    split_ifs <;> simp
  -- the block weight against the Sobolev weight
  have hle : ∀ i, (∑' k : ℕ, if blk k i then dyadicWeight (2 * s) k else 0) ≤ Wt i := fun i => by
    simp only [blk, Wt]
    rw [tsum_ite_block_eq]
    split_ifs with h0
    · exact bot_le
    · rw [← ENNReal.natCast_two_pow_rpow]
      gcongr
      exact (Nat.pow_log_le_self 2 h0).trans (Nat.le_add_left _ _)
  have hge : ∀ i, Wt i ≤ (if S.level i = 0 then 1 else 0) +
      2 ^ (2 * s) * ∑' k : ℕ, if blk k i then dyadicWeight (2 * s) k else 0 := fun i => by
    simp only [blk, Wt]
    rw [tsum_ite_block_eq]
    split_ifs with h0
    · simp [h0]
    · rw [zero_add]
      calc ((1 + S.level i : ℕ) : ℝ≥0∞) ^ (2 * s)
          ≤ ((2 ^ (Nat.log 2 (S.level i) + 1) : ℕ) : ℝ≥0∞) ^ (2 * s) := by
            gcongr
            have := Nat.lt_pow_succ_log_self Nat.one_lt_two (S.level i)
            omega
        _ = 2 ^ (2 * s) * dyadicWeight (2 * s) (Nat.log 2 (S.level i)) := by
            rw [ENNReal.natCast_two_pow_rpow, ENNReal.dyadicWeight_succ]
  have hBT : B ≤ T := by
    rw [hB]; exact tsum_le_tsum fun i => by gcongr; exact hle i
  have hTB : T ≤ ‖f‖ₑ ^ 2 + 2 ^ (2 * s) * B := by
    calc T ≤ ∑' i, ((if S.level i = 0 then 1 else 0) * e i +
          2 ^ (2 * s) * ((∑' k : ℕ, if blk k i then dyadicWeight (2 * s) k else 0) * e i)) :=
          tsum_le_tsum fun i => by
            calc Wt i * e i ≤ ((if S.level i = 0 then 1 else 0) +
                2 ^ (2 * s) * ∑' k : ℕ, if blk k i then dyadicWeight (2 * s) k else 0) * e i := by
                  gcongr; exact hge i
              _ = _ := by ring
      _ = ∑' i, (if S.level i = 0 then 1 else 0) * e i + 2 ^ (2 * s) * B := by
          rw [tsum_add, ENNReal.tsum_mul_left, hB]
      _ ≤ ‖f‖ₑ ^ 2 + 2 ^ (2 * s) * B := by
          gcongr
          calc ∑' i, (if S.level i = 0 then 1 else 0) * e i ≤ ∑' i, e i :=
                tsum_le_tsum fun i => by split_ifs <;> simp
            _ = ‖f‖ₑ ^ 2 := by rw [← S.basis.repr.eNorm_map, lp.enorm_sq_eq_tsum]
  -- the block norm is finite iff `B` is
  have hblk : S.projectionScheme.blockNorm s 2 f < ∞ ↔ B ≠ ∞ := by
    rw [ProjectionScheme.blockNorm, ENNReal.add_lt_top, and_iff_right eNorm_lt_top]
    have h2 := lqNorm_rpow (q := 2) (by norm_num) (by norm_num)
      (fun k => dyadicWeight s k * ‖S.projectionScheme.block k f‖ₑ)
    have hB' : (∑' k, (dyadicWeight s k * ‖S.projectionScheme.block k f‖ₑ) ^ (2 : ℝ≥0∞).toReal) =
      B := by
      simp only [B, ENNReal.toReal_ofNat]
      congr 1; funext k
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.dyadicWeight_rpow, mul_comm s,
        ENNReal.rpow_two]
    rw [hB'] at h2
    rw [← h2, ← lt_top_iff_ne_top, ENNReal.rpow_lt_top_iff_of_pos (by norm_num)]
  rw [memApprox_iff_blockNorm_lt_top S hs one_le_two, hblk, mem_l2_iff]
  simp_rw [S.enorm_weight_mul_sq]
  change B ≠ ∞ ↔ T ≠ ∞
  constructor
  · intro h
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top eNorm_ne_top,
      ENNReal.mul_ne_top (ENNReal.two_rpow_ne_top _) h⟩)
      hTB
  · intro h
    exact ne_top_of_le_ne_top h hBT

end SpectralScheme
