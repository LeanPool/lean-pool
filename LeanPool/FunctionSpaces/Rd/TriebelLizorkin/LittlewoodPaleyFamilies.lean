/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinDistributions
public import LeanPool.FunctionSpaces.Rd.FourierMultipliers.SymbolKernels
public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinLocalMeans

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Independence of the Littlewood–Paley family

The blocks of an admissible Littlewood–Paley kernel (`Rd.LPKernel`, with `𝓕Φ' = 1` on the ball
`{‖ξ‖ ≤ a}` and `𝓕Φ' = 0` outside the ball of radius `b`) are `ψ'_0 = Φ'` and
`ψ'_j = (Φ' - δ_{1/2} Φ')_{2^j}`, with the dilation `G_c(x) = c^n G(c x)`, so that
`𝓕ψ'_j(ξ) = 𝓕Φ'(2^{-j} ξ) - 𝓕Φ'(2^{1-j} ξ)` for `j ≥ 1` (`Rd.LPKernel.fourier_psiS_succ`), as in
Triebel's example of a Littlewood–Paley system (Triebel 1983, §2.3.1). The bases `Φ'` and
`Φ' - δ_{1/2} Φ'` are uniformly Schwartz with the seminorm bounds `Rd.LPKernel.baseBound`
(`Rd.LPKernel.isUniformSchwartz_base`).

Any two admissible kernels give equivalent Triebel–Lizorkin quasi-norms on tempered distributions,
for every real `s`, `1 < p < ∞` and `1 < q ≤ ∞`, with the explicit constant
`Rd.LPKernel.comparisonConst N c s` times the Fefferman–Stein constant
(`Rd.LPKernel.triebelLizorkinNormDistr_le_of_blocks`,
`Rd.LPKernel.triebelLizorkinNormDistr_le_mul`), for every window `c ∈ ℕ` with `b ≤ 2^c a'` and
`b' ≤ 2^c a`, that is `2^c ≥ max(b/a', b'/a)`; such a window exists (`Rd.LPKernel.exists_window`).
Hence they give the same spaces, also on `L_p` (`Rd.LPKernel.memTriebelLizorkinDistr_iff`,
`Rd.LPKernel.memTriebelLizorkin_iff`).

The proof is a finite identity on the Fourier side. With `2^c ≥ max(b/a', b'/a)`,
`∑_{|k - j| ≤ c} 𝓕ψ'_k = 1` wherever `𝓕ψ_j ≠ 0` (`Rd.LPKernel.fourier_psiS_mul_sum_Icc`), so
`Δ_j u = ∑_{|k - j| ≤ c} ψ_j ⋆ Δ'_k u` (`Rd.LPKernel.distribBlock_eq_sum`). The convolutions with
`ψ_j` lie below the maximal function, uniformly in `j`, the weights change by at most `2^{c|s|}`
inside the window, the window sums cost the factor `2c + 1` in `ℓ_q`
(`ENNReal.lqNorm_sum_Icc_le`), and the Fefferman–Stein inequality finishes.
-/

@[expose] public section

open MeasureTheory Filter Module
open scoped ENNReal SchwartzMap FourierTransform

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

namespace LPKernel

variable (K K' : LPKernel V)

/-! ### The blocks of an admissible kernel -/

/-- The seminorm bounds of the bases: the larger of the seminorms of `Φ'` and `Φ' - δ_{1/2} Φ'`. -/
noncomputable def baseBound (k l : ℕ) : ℝ :=
  max (SchwartzMap.seminorm ℝ k l K.kernel)
    (SchwartzMap.seminorm ℝ k l (K.kernel - schwartzDilate (1 / 2) (by norm_num) K.kernel))

/-- The bases form a uniformly Schwartz family with bounds `K.baseBound`, since they take only two
values (`Rd.IsUniformSchwartz.of_forall_eq_or_eq`). -/
theorem isUniformSchwartz_base : IsUniformSchwartz K.base K.baseBound :=
  IsUniformSchwartz.of_forall_eq_or_eq fun j => by
    cases j with
    | zero => exact Or.inl rfl
    | succ j => exact Or.inr rfl

/-- `𝓕ψ'_0 = 𝓕Φ'`. -/
theorem fourier_psiS_zero (ξ : V) :
    (𝓕 (K.psiS 0) : 𝓢(V, ℂ)) ξ = (𝓕 K.kernel : 𝓢(V, ℂ)) ξ := by
  rw [psiS, fourier_schwartzDilate_apply (by norm_num : (0 : ℝ) < 2 ^ 0), pow_zero, inv_one,
    one_smul]
  rfl

/-- `𝓕ψ'_{j+1}(ξ) = 𝓕Φ'(2^{-(j+1)} ξ) - 𝓕Φ'(2^{-j} ξ)` (`Rd.fourier_schwartzDilate_apply`). -/
theorem fourier_psiS_succ (j : ℕ) (ξ : V) :
    (𝓕 (K.psiS (j + 1)) : 𝓢(V, ℂ)) ξ =
      (𝓕 K.kernel : 𝓢(V, ℂ)) (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
        (𝓕 K.kernel : 𝓢(V, ℂ)) (((2 : ℝ) ^ j)⁻¹ • ξ) := by
  rw [psiS, fourier_schwartzDilate_apply (by positivity : (0 : ℝ) < 2 ^ (j + 1)), base,
    sub_eq_add_neg, FourierAdd.fourier_add, FourierTransform.fourier_neg, add_apply,
    neg_apply, ← sub_eq_add_neg,
    fourier_schwartzDilate_apply (by norm_num : (0 : ℝ) < 1 / 2), smul_smul]
  congr 2
  rw [pow_succ]
  field_simp

/-- **The blocks telescope**: `∑_{j ≤ J} 𝓕ψ'_j(ξ) = 𝓕Φ'(2^{-J} ξ)`. -/
theorem sum_range_fourier_psiS (J : ℕ) (ξ : V) :
    ∑ j ∈ Finset.range (J + 1), (𝓕 (K.psiS j) : 𝓢(V, ℂ)) ξ =
      (𝓕 K.kernel : 𝓢(V, ℂ)) (((2 : ℝ) ^ J)⁻¹ • ξ) := by
  induction J with
  | zero => rw [zero_add, Finset.sum_range_one, fourier_psiS_zero, pow_zero, inv_one, one_smul]
  | succ J ih => rw [Finset.sum_range_succ, ih, fourier_psiS_succ]; ring

/-- `𝓕Φ'(c⁻¹ ξ) = 1` for `‖ξ‖ ≤ c a`, `c > 0`. -/
theorem fourier_kernel_inv_smul_eq_one {c : ℝ} (hc : 0 < c) {ξ : V} (h : ‖ξ‖ ≤ c * K.a) :
    (𝓕 K.kernel : 𝓢(V, ℂ)) (c⁻¹ • ξ) = 1 := by
  refine K.fourier_eq_one _ ?_
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le, inv_mul_le_iff₀ hc]
  exact h

/-- `𝓕Φ'(c⁻¹ ξ) = 0` for `‖ξ‖ ≥ c b`, `c > 0`. -/
theorem fourier_kernel_inv_smul_eq_zero {c : ℝ} (hc : 0 < c) {ξ : V} (h : c * K.b ≤ ‖ξ‖) :
    (𝓕 K.kernel : 𝓢(V, ℂ)) (c⁻¹ • ξ) = 0 := by
  refine K.fourier_eq_zero _ ?_
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le, le_inv_mul_iff₀ hc]
  exact h

/-- **The Fourier support of the blocks, outer radius**: where `𝓕ψ'_j(ξ) ≠ 0`, `‖ξ‖ < 2^j b`. -/
theorem norm_lt_of_fourier_psiS_ne_zero {j : ℕ} {ξ : V}
    (h : (𝓕 (K.psiS j) : 𝓢(V, ℂ)) ξ ≠ 0) : ‖ξ‖ < 2 ^ j * K.b := by
  by_contra hξ
  rw [not_lt] at hξ
  cases j with
  | zero =>
    rw [fourier_psiS_zero] at h
    exact h (by simpa using K.fourier_kernel_inv_smul_eq_zero one_pos (by simpa using hξ))
  | succ j =>
    rw [fourier_psiS_succ, K.fourier_kernel_inv_smul_eq_zero (by positivity) hξ,
      K.fourier_kernel_inv_smul_eq_zero (by positivity) (le_trans (by
        rw [pow_succ]; nlinarith [K.a_pos, K.a_lt_b, pow_pos (two_pos (α := ℝ)) j]) hξ),
      sub_zero] at h
    exact h rfl

/-- **The Fourier support of the blocks, inner radius**: where `𝓕ψ'_{j+1}(ξ) ≠ 0`,
`2^j a < ‖ξ‖`. -/
theorem lt_norm_of_fourier_psiS_succ_ne_zero {j : ℕ} {ξ : V}
    (h : (𝓕 (K.psiS (j + 1)) : 𝓢(V, ℂ)) ξ ≠ 0) : 2 ^ j * K.a < ‖ξ‖ := by
  by_contra hξ
  rw [not_lt] at hξ
  rw [fourier_psiS_succ, K.fourier_kernel_inv_smul_eq_one (by positivity) hξ,
    K.fourier_kernel_inv_smul_eq_one (by positivity) (hξ.trans (by
      rw [pow_succ]; nlinarith [K.a_pos, pow_pos (two_pos (α := ℝ)) j])), sub_self] at h
  exact h rfl

/-! ### The finite identity -/

/-- **A window for two kernels**: for admissible kernels `K`, `K'` there is `c ∈ ℕ` with
`b ≤ 2^c a'` and `b' ≤ 2^c a` (Mathlib's `pow_unbounded_of_one_lt`). -/
theorem exists_window : ∃ c : ℕ, K.b ≤ 2 ^ c * K'.a ∧ K'.b ≤ 2 ^ c * K.a := by
  obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt (max (K.b / K'.a) (K'.b / K.a)) one_lt_two
  refine ⟨c, ?_, ?_⟩
  · exact ((div_lt_iff₀ K'.a_pos).1 ((le_max_left _ _).trans_lt hc)).le
  · exact ((div_lt_iff₀ K.a_pos).1 ((le_max_right _ _).trans_lt hc)).le

/-- **The window sums are `1` on the Fourier support of a block**: if `b ≤ 2^c a'` and
`b' ≤ 2^c a`, then `∑_{k = j - c}^{j + c} 𝓕ψ'_k(ξ) = 1` wherever `𝓕ψ_j(ξ) ≠ 0`. The sum is
`𝓕Φ'(2^{-(j+c)} ξ) - 𝓕Φ'(2^{-(j-c-1)} ξ)` (`Rd.LPKernel.sum_range_fourier_psiS`, the second term
absent for `j ≤ c`), and `2^{j-1} a < ‖ξ‖ < 2^j b` (`Rd.LPKernel.norm_lt_of_fourier_psiS_ne_zero`,
`Rd.LPKernel.lt_norm_of_fourier_psiS_succ_ne_zero`). -/
theorem sum_Icc_fourier_psiS_eq_one {c : ℕ} (hb : K.b ≤ 2 ^ c * K'.a) (hb' : K'.b ≤ 2 ^ c * K.a)
    {j : ℕ} {ξ : V} (h : (𝓕 (K.psiS j) : 𝓢(V, ℂ)) ξ ≠ 0) :
    ∑ k ∈ Finset.Icc (j - c) (j + c), (𝓕 (K'.psiS k) : 𝓢(V, ℂ)) ξ = 1 := by
  have hup : ∑ k ∈ Finset.range (j + c + 1), (𝓕 (K'.psiS k) : 𝓢(V, ℂ)) ξ = 1 := by
    rw [K'.sum_range_fourier_psiS]
    refine K'.fourier_kernel_inv_smul_eq_one (by positivity) ?_
    have h1 := K.norm_lt_of_fourier_psiS_ne_zero h
    calc ‖ξ‖ ≤ 2 ^ j * K.b := h1.le
      _ ≤ 2 ^ j * (2 ^ c * K'.a) := by gcongr
      _ = 2 ^ (j + c) * K'.a := by rw [pow_add, mul_assoc]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ (by omega), hup]
  rcases Nat.lt_or_ge c j with hcj | hcj
  · obtain ⟨i, rfl⟩ : ∃ i, j = c + i + 1 := ⟨j - c - 1, by omega⟩
    rw [show c + i + 1 - c = i + 1 by omega, K'.sum_range_fourier_psiS,
      K'.fourier_kernel_inv_smul_eq_zero (by positivity), sub_zero]
    have h1 := K.lt_norm_of_fourier_psiS_succ_ne_zero h
    calc 2 ^ i * K'.b ≤ 2 ^ i * (2 ^ c * K.a) := by gcongr
      _ = 2 ^ (c + i) * K.a := by rw [pow_add]; ring
      _ ≤ ‖ξ‖ := h1.le
  · rw [Nat.sub_eq_zero_of_le hcj, Finset.sum_range_zero, sub_zero]

/-- **The finite identity on the Fourier side**: `𝓕ψ_j · ∑_{k = j - c}^{j + c} 𝓕ψ'_k = 𝓕ψ_j`
under the hypotheses of `Rd.LPKernel.sum_Icc_fourier_psiS_eq_one`. -/
theorem fourier_psiS_mul_sum_Icc {c : ℕ} (hb : K.b ≤ 2 ^ c * K'.a) (hb' : K'.b ≤ 2 ^ c * K.a)
    (j : ℕ) (ξ : V) :
    (𝓕 (K.psiS j) : 𝓢(V, ℂ)) ξ *
        ∑ k ∈ Finset.Icc (j - c) (j + c), (𝓕 (K'.psiS k) : 𝓢(V, ℂ)) ξ =
      (𝓕 (K.psiS j) : 𝓢(V, ℂ)) ξ := by
  by_cases h : (𝓕 (K.psiS j) : 𝓢(V, ℂ)) ξ = 0
  · rw [h, zero_mul]
  · rw [K.sum_Icc_fourier_psiS_eq_one K' hb hb' h, mul_one]

/-! ### The finite identity for tempered distributions -/

/-- **The finite identity for tempered distributions**: under the hypotheses of
`Rd.LPKernel.sum_Icc_fourier_psiS_eq_one`, for every tempered distribution `u` and every `j`,
`Δ_j u = ∑_{k = j - c}^{j + c} (𝓕ψ_j)(D) Δ'_k u`, with the blocks `Δ_j` of `K` and `Δ'_k` of
`K'`. Both sides are Fourier multipliers of `u` (Mathlib's
`TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply`,
`TemperedDistribution.fourierMultiplierCLM_sum`), with the same symbol by
`Rd.LPKernel.fourier_psiS_mul_sum_Icc`. -/
theorem distribBlock_eq_sum {c : ℕ} (hb : K.b ≤ 2 ^ c * K'.a) (hb' : K'.b ≤ 2 ^ c * K.a)
    (u : 𝓢'(V, ℂ)) (j : ℕ) :
    K.distribBlock j u = ∑ k ∈ Finset.Icc (j - c) (j + c),
      TemperedDistribution.fourierMultiplierCLM ℂ (𝓕 (K.psiS j) : 𝓢(V, ℂ))
        (K'.distribBlock k u) := by
  simp only [distribBlock]
  simp_rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (𝓕 (K'.psiS _)).hasTemperateGrowth (𝓕 (K.psiS j)).hasTemperateGrowth]
  rw [← sum_apply, ← TemperedDistribution.fourierMultiplierCLM_sum ℂ
    fun k _ => (𝓕 (K'.psiS k)).hasTemperateGrowth.mul (𝓕 (K.psiS j)).hasTemperateGrowth]
  refine congrArg (fun f => TemperedDistribution.fourierMultiplierCLM ℂ f u) (funext fun ξ => ?_)
  simp only [Pi.mul_apply]
  rw [← Finset.sum_mul, mul_comm, K.fourier_psiS_mul_sum_Icc K' hb hb' j ξ]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The blocks of `K` from those of `K'`**: under the hypotheses of
`Rd.LPKernel.distribBlock_eq_sum`, `1 ≤ p < ∞`, if the blocks `Δ'_k u` are `L_p` functions `g_k`,
then `Δ_j u` is the `L_p` function `∑_{k = j - c}^{j + c} ψ_j ⋆ g_k`
(`Rd.fourierMultiplierCLM_fourier_toLp_eq_conv`). -/
theorem distribBlock_eq_sum_convLp (hp : p ≠ ∞) {c : ℕ} (hb : K.b ≤ 2 ^ c * K'.a)
    (hb' : K'.b ≤ 2 ^ c * K.a) {u : 𝓢'(V, ℂ)} {g : ℕ → Lp ℂ p (volume : Measure V)}
    (hg : ∀ k, K'.distribBlock k u = (g k : 𝓢'(V, ℂ))) (j : ℕ) :
    K.distribBlock j u = ((∑ k ∈ Finset.Icc (j - c) (j + c),
      convLp hp (K.psiS j).integrable (g k) : Lp ℂ p (volume : Measure V)) : 𝓢'(V, ℂ)) := by
  rw [K.distribBlock_eq_sum K' hb hb', ← Lp.toTemperedDistributionCLM_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hg, fourierMultiplierCLM_fourier_toLp_eq_conv hp, Lp.toTemperedDistributionCLM_apply]

/-! ### The comparison of two kernels -/

/-- **The pointwise bound**: let `N > n`, `c, j ∈ ℕ` and `s` real. For every family
`g_k : V → ℂ` and every `x`,
`2^{js} |∑_{k = j - c}^{j + c} (ψ_j ⋆ g_k)(x)| ≤ 2^{c|s|} C_{n,N} C_{A,0,N} ∑_k M(2^{ks} |g_k|)(x)`
with the bounds `A = K.baseBound` of the bases of `K`: the convolutions lie below the maximal
function (`Rd.IsUniformSchwartz.enorm_conv_dilate_le_maximal`), and every `k` in the window has
`|j - k| ≤ c`, so `2^{js} ≤ 2^{c|s|} 2^{ks}` (`ENNReal.dyadicWeight_le_of_mem_Icc`). -/
theorem dyadicWeight_mul_enorm_sum_conv_le {N : ℕ} (hN : finrank ℝ V < N) (c : ℕ) (s : ℝ)
    (j : ℕ) (g : ℕ → V → ℂ) (x : V) :
    dyadicWeight s j * ‖∑ k ∈ Finset.Icc (j - c) (j + c), conv (K.psiS j) (g k) volume x‖ₑ ≤
      dyadicWeight |s| c * (decayMaximalConst V N * familyDecayConst K.baseBound 0 N) *
        ∑ k ∈ Finset.Icc (j - c) (j + c),
          maximal (fun y => dyadicWeight s k * ‖g k y‖ₑ) x := by
  set D := decayMaximalConst V N * familyDecayConst K.baseBound 0 N
  calc dyadicWeight s j * ‖∑ k ∈ Finset.Icc (j - c) (j + c), conv (K.psiS j) (g k) volume x‖ₑ
      ≤ ∑ k ∈ Finset.Icc (j - c) (j + c),
          dyadicWeight s j * (D * maximal (fun y => ‖g k y‖ₑ) x) := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ((eNorm_sum_le _ _).trans
          (Finset.sum_le_sum fun k _ => ?_)) (zero_le (a := dyadicWeight s j))
        rw [K.coe_psiS]
        exact K.isUniformSchwartz_base.enorm_conv_dilate_le_maximal hN j _ x
    _ ≤ ∑ k ∈ Finset.Icc (j - c) (j + c),
          dyadicWeight |s| c * dyadicWeight s k * (D * maximal (fun y => ‖g k y‖ₑ) x) :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right
          (ENNReal.dyadicWeight_le_of_mem_Icc s hk) (zero_le (a := D * _))
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← dyadicWeight_mul_maximal]
        ring

/-- The **comparison constant** `2^{c|s|} C_{n,N} C_{A,0,N} (2c + 1)` of two kernels, with the
window `c`, `N > n` and the bounds `A = K.baseBound` of the bases of `K`. -/
noncomputable def comparisonConst (N c : ℕ) (s : ℝ) : ℝ≥0∞ :=
  dyadicWeight |s| c * (decayMaximalConst V N * familyDecayConst K.baseBound 0 N) * (2 * c + 1)

/-- The comparison constant is finite for `N > n`. -/
theorem comparisonConst_ne_top {N : ℕ} (hN : finrank ℝ V < N) (c : ℕ) (s : ℝ) :
    K.comparisonConst N c s ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.dyadicWeight_ne_top _ _)
    (decayMaximalConst_mul_familyDecayConst_ne_top hN _)) (by finiteness)

/-- **The comparison for one family of blocks**: let `1 < p < ∞`, `1 < q ≤ ∞`, `N > n` and
`b ≤ 2^c a'`, `b' ≤ 2^c a`. If the blocks of `u` for `K'` are `L_p` functions `g_k`, then
`‖u‖_{F^s_{p,q}, K} ≤ C C_{FS} ‖ x ↦ ‖(2^{ks} |g_k(x)|)_k‖_{ℓ_q} ‖_p` with the comparison constant
`C = K.comparisonConst N c s` and the Fefferman–Stein constant `C_{FS}`. The blocks of `u` for `K`
are window sums of convolutions of the `g_k` (`Rd.LPKernel.distribBlock_eq_sum_convLp`), bounded
pointwise by maximal functions (`Rd.LPKernel.dyadicWeight_mul_enorm_sum_conv_le`); the window
sums cost `2c + 1` in `ℓ_q` (`ENNReal.lqNorm_sum_Icc_le`), and
`Rd.eLpNorm_le_of_le_lqNorm_maximal` finishes. -/
theorem triebelLizorkinNormDistr_le_of_blocks (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞}
    (hq1 : 1 < q) {N : ℕ} (hN : finrank ℝ V < N) {c : ℕ} (hb : K.b ≤ 2 ^ c * K'.a)
    (hb' : K'.b ≤ 2 ^ c * K.a) (s : ℝ) {u : 𝓢'(V, ℂ)} {g : ℕ → Lp ℂ p (volume : Measure V)}
    (hg : ∀ k, K'.distribBlock k u = (g k : 𝓢'(V, ℂ))) :
    K.triebelLizorkinNormDistr p s q u ≤ K.comparisonConst N c s * feffermanSteinConst V p q *
      eLpNorm (fun x => lqNorm q fun k => dyadicWeight s k * ‖g k x‖ₑ) p volume := by
  set h : ℕ → Lp ℂ p (volume : Measure V) := fun j =>
    ∑ k ∈ Finset.Icc (j - c) (j + c), convLp hp (K.psiS j).integrable (g k) with hh
  have hae : ∀ j, ⇑(h j) =ᵐ[volume]
      fun x => ∑ k ∈ Finset.Icc (j - c) (j + c), conv (K.psiS j) (g k) volume x := fun j =>
    coeFn_sum_convLp_ae hp (fun _ => K.psiS j) g _
  refine (K.triebelLizorkinNormDistr_le (g := h)
    (K.distribBlock_eq_sum_convLp K' hp hb hb' hg)).trans ?_
  refine eLpNorm_le_of_le_lqNorm_maximal hp1 hp hq1 (aemeasurable_lqNorm_dyadicWeight_Lp _ q _)
    (fun k => ((Lp.aestronglyMeasurable (g k)).eNorm.const_mul _)) ?_
  filter_upwards [ae_all_iff.2 hae] with x hx
  simp_rw [hx]
  calc lqNorm q (fun j => dyadicWeight s j *
        ‖∑ k ∈ Finset.Icc (j - c) (j + c), conv (K.psiS j) (g k) volume x‖ₑ)
      ≤ lqNorm q (fun j => dyadicWeight |s| c *
          (decayMaximalConst V N * familyDecayConst K.baseBound 0 N) *
          ∑ k ∈ Finset.Icc (j - c) (j + c),
            maximal (fun y => dyadicWeight s k * ‖g k y‖ₑ) x) :=
        ENNReal.lqNorm_mono fun j => K.dyadicWeight_mul_enorm_sum_conv_le hN c s j _ x
    _ ≤ dyadicWeight |s| c * (decayMaximalConst V N * familyDecayConst K.baseBound 0 N) *
          ((2 * c + 1) * lqNorm q (fun k => maximal (fun y => dyadicWeight s k * ‖g k y‖ₑ) x)) := by
        rw [ENNReal.lqNorm_const_mul]
        exact mul_le_mul_of_nonneg_left (ENNReal.lqNorm_sum_Icc_le hq1.le c _) (zero_le (a := _))
    _ = _ := by rw [comparisonConst, mul_assoc _ (2 * c + 1 : ℝ≥0∞)]

/-- **Any two admissible kernels give equivalent quasi-norms, with explicit constant**: let
`1 < p < ∞`, `1 < q ≤ ∞`, `N > n` and `b ≤ 2^c a'`, `b' ≤ 2^c a`. For every tempered distribution
`u`, `‖u‖_{F^s_{p,q}, K} ≤ max(1, C C_{FS}) ‖u‖_{F^s_{p,q}, K'}` with the comparison constant
`C = K.comparisonConst N c s` and the Fefferman–Stein constant `C_{FS}`
(`Rd.LPKernel.triebelLizorkinNormDistr_le_of_blocks` for every family of `L_p` functions
representing the blocks of `u` for `K'`, and `Rd.LPKernel.le_mul_triebelLizorkinNormDistr`). -/
theorem triebelLizorkinNormDistr_le_mul (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞} (hq1 : 1 < q)
    {N : ℕ} (hN : finrank ℝ V < N) {c : ℕ} (hb : K.b ≤ 2 ^ c * K'.a) (hb' : K'.b ≤ 2 ^ c * K.a)
    (s : ℝ) (u : 𝓢'(V, ℂ)) :
    K.triebelLizorkinNormDistr p s q u ≤
      max 1 (K.comparisonConst N c s * feffermanSteinConst V p q) *
        K'.triebelLizorkinNormDistr p s q u := by
  refine K'.le_mul_triebelLizorkinNormDistr (zero_lt_one.trans_le (le_max_left _ _)).ne'
    fun g hg => ?_
  refine (K.triebelLizorkinNormDistr_le_of_blocks K' hp1 hp hq1 hN hb hb' s hg).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le (a := _))

/-- **Any two admissible kernels give equivalent quasi-norms**: for admissible kernels `K`, `K'`,
`1 < p < ∞`, `1 < q ≤ ∞` and every real `s` there is a finite constant `C` with
`‖u‖_{F^s_{p,q}, K} ≤ C ‖u‖_{F^s_{p,q}, K'}` for every tempered distribution `u`
(`Rd.LPKernel.triebelLizorkinNormDistr_le_mul` with a window from `Rd.LPKernel.exists_window` and
`N = n + 1`). Exchanging `K` and `K'` gives the converse. -/
theorem exists_triebelLizorkinNormDistr_le (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞} (hq1 : 1 < q)
    (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ u : 𝓢'(V, ℂ),
      K.triebelLizorkinNormDistr p s q u ≤ C * K'.triebelLizorkinNormDistr p s q u := by
  obtain ⟨c, hb, hb'⟩ := K.exists_window K'
  have hN : finrank ℝ V < finrank ℝ V + 1 := Nat.lt_succ_self _
  exact ⟨max 1 (K.comparisonConst (finrank ℝ V + 1) c s * feffermanSteinConst V p q),
    max_ne_top ENNReal.one_ne_top (ENNReal.mul_ne_top (K.comparisonConst_ne_top hN c s)
      (feffermanSteinConst_ne_top hp1 hp hq1)),
    K.triebelLizorkinNormDistr_le_mul K' hp1 hp hq1 hN hb hb' s⟩

/-- **Every admissible kernel gives the same spaces of tempered distributions**: for `1 < p < ∞`,
`1 < q ≤ ∞` and every real `s`, a tempered distribution has finite quasi-norm for the kernel `K`
iff it lies in `F^s_{p,q}` of the project (`Rd.LPKernel.exists_triebelLizorkinNormDistr_le` for
`K` and `Rd.LPKernel.standard` in both orders). -/
theorem memTriebelLizorkinDistr_iff (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞} (hq1 : 1 < q)
    (s : ℝ) (u : 𝓢'(V, ℂ)) :
    K.triebelLizorkinNormDistr p s q u < ∞ ↔ MemTriebelLizorkinDistr p s q u := by
  rw [MemTriebelLizorkinDistr, ← standard_triebelLizorkinNormDistr]
  obtain ⟨C, hC, h⟩ := K.exists_triebelLizorkinNormDistr_le (standard V) hp1 hp hq1 s
  obtain ⟨C', hC', h'⟩ := (standard V).exists_triebelLizorkinNormDistr_le K hp1 hp hq1 s
  exact ⟨fun hu => (h' u).trans_lt (ENNReal.mul_lt_top hC'.lt_top hu),
    fun hu => (h u).trans_lt (ENNReal.mul_lt_top hC.lt_top hu)⟩

/-- **Every admissible kernel gives the same spaces of `L_p` functions**: for `1 < p < ∞`,
`1 < q ≤ ∞`, every real `s` and `f ∈ L_p(V)`,
`‖ x ↦ ‖(2^{js} |(ψ'_j ⋆ f)(x)|)_j‖_{ℓ_q} ‖_p < ∞` iff `f ∈ F^s_{p,q}`
(`Rd.LPKernel.memTriebelLizorkinDistr_iff`,
`Rd.LPKernel.triebelLizorkinNormDistr_toTemperedDistribution`,
`Rd.memTriebelLizorkinDistr_toTemperedDistribution_iff`). -/
theorem memTriebelLizorkin_iff (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞} (hq1 : 1 < q) (s : ℝ)
    (f : Lp ℂ p (volume : Measure V)) :
    K.triebelLizorkinNorm s q f < ∞ ↔ MemTriebelLizorkin s q f := by
  rw [← K.triebelLizorkinNormDistr_toTemperedDistribution hp, K.memTriebelLizorkinDistr_iff hp1 hp
    hq1, memTriebelLizorkinDistr_toTemperedDistribution_iff hp]

/-- **Equivalent quasi-norms on `L_p`**: for admissible kernels `K`, `K'`, `1 < p < ∞`,
`1 < q ≤ ∞` and every real `s` there is a finite constant `C` with
`‖f‖_{F^s_{p,q}, K} ≤ C ‖f‖_{F^s_{p,q}, K'}` for every `f ∈ L_p(V)`
(`Rd.LPKernel.exists_triebelLizorkinNormDistr_le`). For `K' = Rd.LPKernel.standard` the right side
is the quasi-norm `Rd.triebelLizorkinNorm` of the project
(`Rd.LPKernel.standard_triebelLizorkinNorm`). -/
theorem exists_triebelLizorkinNorm_le (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞} (hq1 : 1 < q)
    (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      K.triebelLizorkinNorm s q f ≤ C * K'.triebelLizorkinNorm s q f := by
  obtain ⟨C, hC, h⟩ := K.exists_triebelLizorkinNormDistr_le K' hp1 hp hq1 s
  refine ⟨C, hC, fun f => ?_⟩
  have hf := h f
  rwa [K.triebelLizorkinNormDistr_toTemperedDistribution hp,
    K'.triebelLizorkinNormDistr_toTemperedDistribution hp] at hf

end LPKernel

end Rd
