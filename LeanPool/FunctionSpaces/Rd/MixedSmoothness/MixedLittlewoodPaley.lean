/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.MixedSmoothness.MixedLocalMeans
public import LeanPool.FunctionSpaces.Rd.Approximation.BandJackson
public import LeanPool.FunctionSpaces.Rd.Approximation.BandInverse

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Tensor Littlewood–Paley blocks

On `ℝ^d = Fin d → ℝ` the **tensor Littlewood–Paley blocks** of `f ∈ L_p` are `δ_k ⋆ f` with the
tensor kernels `δ_k = ⊗_i ψ_{k_i}` of the one-dimensional blocks `ψ_j` (`Rd.psi` on `ℝ`),
`k ∈ ℕ^d` (`Rd.mixedPsi`, `Rd.mixedBlock`). In Fourier terms `δ_k ⋆ f = 𝓕⁻¹(φ_k 𝓕f)` for the
tensor product `φ_k = ⊗_i 𝓕ψ_{k_i}` of the one-dimensional dyadic decomposition of unity, and
**Vybíral's quasi-norm** of the Besov spaces of dominating mixed smoothness is
`‖(2^(s|k|_1) ‖δ_k ⋆ f‖_p)_{k ∈ ℕ^d}‖_{ℓ_q(ℕ^d)}` (`Rd.mixedLPNorm`). Over the boxes
`{k : k_i ≤ J}` the blocks sum to the dilation `(⊗Φ)_{2^J}` of an approximate identity, so
`∑_k δ_k ⋆ f = f` in `L_p` (`Rd.tendsto_sum_mixedBlock`).

**Littlewood–Paley blocks, local means and differences** (`Rd.mixedBesov_iff_mixedLP`): for
`1 ≤ p < ∞`, `0 < s < L` and `1 ≤ q ≤ ∞` the three quasi-norms are finite together. Both
comparisons with the mixed local means use a reproducing formula, a one-dimensional bound in
`L_1` in each coordinate, and the almost diagonal lemma on `ℕ^d`:

* `‖ψ_m ⋆ η_k‖_1 ≤ C 2^(-(m-k)L)` for `k ≤ m`
  (`Rd.LocalMeansBump.exists_eLpNorm_conv_psi_dual_le`): `ψ_m` annihilates the band-limited
  Jackson approximant `J_{m-3} η_k` (`Rd.conv_psi_Theta`), and
  `‖η_k - J_{m-3} η_k‖_1 ≤ C ω_L(η_k, 2^(-(m-3)))_1` (`Rd.enorm_sub_jacksonApprox_le`);
* `‖k_m ⋆ Θ_k‖_1 ≤ C 2^(-(m-k)L)` for `k < m`
  (`Rd.LocalMeansBump.exists_eLpNorm_conv_kernel_Theta_le`): local means are bounded by the
  modulus (`Rd.LocalMeansBump.enorm_localMean_succ_le`), and `Θ_k` is smooth at the scale `2^(-k)`
  (`Rd.eLpNorm_higherDiff_Theta_le`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

open ENNReal (dyadicWeight lqNorm)

namespace Rd

variable {d : ℕ}

/-! ### Tensor Littlewood–Paley blocks -/

/-- The **tensor Littlewood–Paley kernels** `δ_k = ⊗_i ψ_{k_i}`. -/
noncomputable def mixedPsi (k : Fin d → ℕ) : (Fin d → ℝ) → ℂ :=
  tensorKernel fun i => psi (V := ℝ) (k i)

/-- The **tensor band-limiting kernels** `⊗_i Θ_{k_i}`. -/
noncomputable def mixedTheta (k : Fin d → ℕ) : (Fin d → ℝ) → ℂ :=
  tensorKernel fun i => Theta (V := ℝ) (k i)

/-- The tensor Littlewood–Paley kernels are integrable. -/
theorem integrable_mixedPsi (k : Fin d → ℕ) : Integrable (mixedPsi k) :=
  integrable_tensorKernel fun i => integrable_psi (k i)

/-- The tensor band-limiting kernels are integrable. -/
theorem integrable_mixedTheta (k : Fin d → ℕ) : Integrable (mixedTheta k) :=
  integrable_tensorKernel fun i => integrable_Theta (k i)

/-- **The blocks are band-limited**: `(⊗Θ_{k_i}) ⋆ δ_k = δ_k` (`Rd.conv_Theta_psi` in every
coordinate). -/
theorem conv_mixedTheta_mixedPsi (k : Fin d → ℕ) :
    conv (mixedTheta k) (mixedPsi k) volume = mixedPsi k := by
  rw [mixedTheta, mixedPsi, conv_tensorKernel]
  congr 1
  funext i
  exact conv_Theta_psi (k i)

/-- **The blocks sum to an approximate identity**: over the boxes `{k : k_i ≤ J}`,
`∑_k δ_k = (⊗Φ)_{2^J}`. -/
theorem sum_mixedPsi (J : ℕ) :
    (fun x => ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (J + 1)), mixedPsi k x) =
      dilate ((2 : ℝ) ^ J) (tensorKernel fun _ : Fin d => lpKernel (V := ℝ)) := by
  have h := sum_tensorKernel_piFinset (fun _ : Fin d => Finset.range (J + 1))
    (fun _ j => psi (V := ℝ) j)
  rw [dilate_tensorKernel]
  funext x
  rw [← Finset.sum_apply]
  change (∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (J + 1)),
    tensorKernel fun i => psi (V := ℝ) (k i)) x = _
  rw [h]
  simp only [sum_psi]
  rfl

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **tensor Littlewood–Paley blocks** `f ↦ δ_k ⋆ f` on `L_p(ℝ^d)`. -/
noncomputable def mixedBlock (hp : p ≠ ∞) (k : Fin d → ℕ) :
    Lp ℂ p (volume : Measure (Fin d → ℝ)) →L[ℂ] Lp ℂ p (volume : Measure (Fin d → ℝ)) :=
  convLp hp (integrable_mixedPsi k)

/-- **Vybíral's quasi-norm** of the Besov spaces of dominating mixed smoothness,
`‖(2^(s|k|_1) ‖δ_k ⋆ f‖_p)_{k ∈ ℕ^d}‖_{ℓ_q(ℕ^d)}`. -/
noncomputable def mixedLPNorm (hp : p ≠ ∞) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) : ℝ≥0∞ :=
  lqNorm q fun k => mixedWeight s k * ‖mixedBlock hp k f‖ₑ

/-- **The tensor Littlewood–Paley decomposition**: `∑_{k ≤ J} δ_k ⋆ f → f` in `L_p` over the boxes
`{k : k_i ≤ J}`. -/
theorem tendsto_sum_mixedBlock (hp : p ≠ ∞) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    Tendsto (fun J => ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (J + 1)),
      mixedBlock hp k f) atTop (𝓝 f) := by
  have hΦ : Integrable (tensorKernel fun _ : Fin d => lpKernel (V := ℝ)) :=
    integrable_tensorKernel fun _ => integrable_lpKernel
  have hΦ1 : ∫ x, tensorKernel (fun _ : Fin d => lpKernel (V := ℝ)) x = 1 := by
    rw [integral_tensorKernel]
    simp [integral_lpKernel]
  have hlim := tendsto_convLp_dilate hp hΦ hΦ1 (c := fun J : ℕ => (2 : ℝ) ^ J)
    (fun J => pow_ne_zero J two_ne_zero) (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) f
  refine hlim.congr fun J => ?_
  symm
  simp only [mixedBlock]
  rw [convLp_finsetSum_kernel]
  exact convLp_congr hp _ _ (sum_mixedPsi J) f

/-! ### One-dimensional estimates in `L_1` -/

/-- The `L_1` norm of a convolution with `G` through the operator on `L_1`. -/
theorem eLpNorm_conv_eq_enorm_convLp {K G : ℝ → ℂ} (hK : Integrable K) (hG : Integrable G) :
    eLpNorm (conv K G volume) 1 volume =
      ‖convLp ENNReal.one_ne_top hK ((memLp_one_iff_integrable.2 hG).toLp G)‖ₑ := by
  rw [Lp.eNorm_def]
  refine eLpNorm_congr_ae ?_
  exact ((convLp_apply_ae ENNReal.one_ne_top hK _).trans
    (Filter.EventuallyEq.of_eq (conv_congr_ae (MemLp.coeFn_toLp _)))).symm

/-- `1 ≤ 2^(3L) c(m, k)` for `m < k + 3`. -/
theorem one_le_dyadicWeight_mul_almostDiagCoeff (L : ℕ) {m k : ℕ} (hmk : m < k + 3) :
    1 ≤ dyadicWeight L 3 * almostDiagCoeff L m k := by
  rw [almostDiagCoeff]
  split_ifs with hkm
  · rw [mul_comm, ← ENNReal.dyadicWeight_neg_mul_self (L : ℝ) (m - k)]
    exact mul_le_mul' le_rfl (ENNReal.dyadicWeight_mono (Nat.cast_nonneg L) (by omega))
  · rw [mul_one]
    exact ENNReal.one_le_dyadicWeight (Nat.cast_nonneg L) 3

namespace LocalMeansBump

variable (b : LocalMeansBump ℝ)

/-- **Littlewood–Paley blocks against the dual kernels**: there is `C < ∞` with
`‖ψ_m ⋆ η_k‖_1 ≤ C c(m, k)`, `c(m, k) = 2^(-(m-k)L)` for `k ≤ m` and `1` for `k > m`. For
`k + 3 ≤ m`, `ψ_m` annihilates the band-limited Jackson approximant `J_{m-3} η_k`, and
`‖η_k - J_{m-3} η_k‖_1 ≤ C ω_L(η_k, 2^(-(m-3)))_1 ≤ C 2^(-(m-3-k)L)`. -/
theorem exists_eLpNorm_conv_psi_dual_le (L : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ m k : ℕ,
      eLpNorm (conv (psi (V := ℝ) m) (b.dual L k) volume) 1 volume ≤
        C * almostDiagCoeff L m k := by
  have h1 : (1 : ℝ≥0∞) ≠ ∞ := ENNReal.one_ne_top
  set Φ₁ := 2 * eLpNorm (lpKernel (V := ℝ)) 1 volume
  set C₀ := Φ₁ * (2 * eLpNorm (momentKernel b.toFun L) 1 volume)
  set C₁ := Φ₁ * (jacksonConst ℝ L 1 * b.dualConst L)
  have hΦ₁ : Φ₁ ≠ ∞ := ENNReal.mul_ne_top (by norm_num) eLpNorm_lpKernel_ne_top
  have hC₀ : C₀ ≠ ∞ := ENNReal.mul_ne_top hΦ₁ (ENNReal.mul_ne_top (by norm_num)
    (eLpNorm_momentKernel_ne_top b.integrable L))
  have hC₁ : C₁ ≠ ∞ := ENNReal.mul_ne_top hΦ₁ (ENNReal.mul_ne_top
    (jacksonConst_ne_top le_rfl h1 L) (b.dualConst_ne_top L))
  refine ⟨(C₀ + C₁) * dyadicWeight L 3, ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hC₀, hC₁⟩)
    (ENNReal.dyadicWeight_ne_top _ _), fun m k => ?_⟩
  have htriv : eLpNorm (conv (psi (V := ℝ) m) (b.dual L k) volume) 1 volume ≤ C₀ :=
    (eLpNorm_conv_le le_rfl (integrable_psi m).aestronglyMeasurable
      (b.integrable_dual L k).aestronglyMeasurable).trans
      (mul_le_mul' (eLpNorm_psi_one_le m) (b.eLpNorm_dual_one_le L k))
  by_cases hkm : k + 3 ≤ m
  · -- the Jackson approximant of `η_k` at the level `m - 3`
    set η : Lp ℂ 1 (volume : Measure ℝ) := (memLp_one_iff_integrable.2 (b.integrable_dual L
      k)).toLp _
    set P := jacksonApprox h1 L (m - 3) η
    have hP : convLp h1 (integrable_psi (V := ℝ) m) P = 0 := by
      have hmem : convLp h1 (integrable_Theta (V := ℝ) (m - 3)) P = P :=
        mem_bandSpace.1 (jacksonApprox_mem_bandSpace h1 L (m - 3) η)
      rw [← hmem, convLp_convLp]
      exact convLp_of_eq_zero h1 _ (conv_psi_Theta (by omega)) P
    have hmod : lpModulus 1 L η (m - 3) ≤ b.dualConst L * almostDiagCoeff L (m - 3) k := by
      rw [lpModulus, modulus_congr_ae (MemLp.coeFn_toLp _)]
      exact iSup₂_le fun v hv => b.eLpNorm_higherDiff_dual_le L hv
    have hc : almostDiagCoeff L (m - 3) k = almostDiagCoeff L m k * dyadicWeight L 3 := by
      have hk : k ≤ m - 3 := by omega
      have hk' : k ≤ m := by omega
      simp only [almostDiagCoeff, hk, hk', ↓reduceIte]
      rw [show m - k = (m - 3 - k) + 3 by omega, ENNReal.dyadicWeight_add_nat, mul_assoc,
        ENNReal.dyadicWeight_neg_mul_self, mul_one]
    rw [eLpNorm_conv_eq_enorm_convLp (integrable_psi m) (b.integrable_dual L k)]
    have hsplit : convLp h1 (integrable_psi (V := ℝ) m) η =
        convLp h1 (integrable_psi (V := ℝ) m) (η - P) := by
      rw [map_sub, hP, sub_zero]
    rw [hsplit]
    calc ‖convLp h1 (integrable_psi (V := ℝ) m) (η - P)‖ₑ
        ≤ eLpNorm (psi (V := ℝ) m) 1 volume * ‖η - P‖ₑ := enorm_convLp_le h1 _ _
      _ ≤ Φ₁ * (jacksonConst ℝ L 1 * lpModulus 1 L η (m - 3)) :=
          mul_le_mul' (eLpNorm_psi_one_le m) (enorm_sub_jacksonApprox_le h1 L (m - 3) η)
      _ ≤ Φ₁ * (jacksonConst ℝ L 1 * (b.dualConst L * almostDiagCoeff L (m - 3) k)) := by
          gcongr
      _ = C₁ * (almostDiagCoeff L m k * dyadicWeight L 3) := by rw [hc]; ring
      _ ≤ (C₀ + C₁) * dyadicWeight L 3 * almostDiagCoeff L m k := by
          rw [mul_comm (almostDiagCoeff _ _ _), ← mul_assoc]
          exact mul_le_mul' (mul_le_mul' le_add_self le_rfl) le_rfl
  · calc eLpNorm (conv (psi (V := ℝ) m) (b.dual L k) volume) 1 volume
        ≤ C₀ * (dyadicWeight L 3 * almostDiagCoeff L m k) :=
          htriv.trans (le_mul_of_one_le_right' (one_le_dyadicWeight_mul_almostDiagCoeff L
            (by omega)))
      _ ≤ (C₀ + C₁) * dyadicWeight L 3 * almostDiagCoeff L m k := by
          rw [← mul_assoc]
          exact mul_le_mul' (mul_le_mul' le_self_add le_rfl) le_rfl

/-- **Local means kernels against the band-limiting kernels**: there is `C < ∞` with
`‖k_m ⋆ Θ_k‖_1 ≤ C c(m, k)`. For `k < m`, `‖k_m ⋆ Θ_k‖_1 ≤ C ω_L(Θ_k, 2^(1-m))_1` and the
differences of `Θ_k` give `2^(-(m-1-k)L)`. -/
theorem exists_eLpNorm_conv_kernel_Theta_le (L : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ m k : ℕ,
      eLpNorm (conv (b.kernel L m) (Theta (V := ℝ) k) volume) 1 volume ≤
        C * almostDiagCoeff L m k := by
  have h1 : (1 : ℝ≥0∞) ≠ ∞ := ENNReal.one_ne_top
  set C₀ := 2 * eLpNorm (momentKernel b.toFun L) 1 volume * eLpNorm (bandKernel (V := ℝ)) 1 volume
  set D := ∫⁻ x, ‖iteratedFDeriv ℝ L (bandKernelS (V := ℝ) : ℝ → ℂ) x‖ₑ
  set C₂ := 2 * (∫⁻ z, ‖b.toFun z‖ₑ) * ENNReal.ofReal (1 + b.radius) ^ L * (D * dyadicWeight L 1)
  have hC₀ : C₀ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
    (eLpNorm_momentKernel_ne_top b.integrable L))
    eLpNorm_bandKernel_ne_top
  have hC₂ : C₂ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
    b.integrable.2.ne) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    (ENNReal.mul_ne_top (lintegral_enorm_iteratedFDeriv_ne_top L _)
      (ENNReal.dyadicWeight_ne_top _ _))
  refine ⟨C₀ + C₂, ENNReal.add_ne_top.2 ⟨hC₀, hC₂⟩, fun m k => ?_⟩
  by_cases hkm : k < m
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hkj : k ≤ j := by omega
    set Θ : Lp ℂ 1 (volume : Measure ℝ) :=
      (memLp_one_iff_integrable.2 (integrable_Theta (V := ℝ) k)).toLp _
    have hmod : lpModulus 1 L Θ j ≤ dyadicWeight (-(L : ℝ)) (j - k) * D := by
      rw [lpModulus, modulus_congr_ae (MemLp.coeFn_toLp _)]
      refine iSup₂_le fun v hv => ?_
      refine (eLpNorm_higherDiff_Theta_le L k v).trans (mul_le_mul' ?_ le_rfl)
      rw [← ENNReal.rpow_natCast]
      exact ENNReal.ofReal_two_pow_mul_rpow_le hkj hv (Nat.cast_nonneg L)
    have hc : dyadicWeight (-(L : ℝ)) (j - k) = almostDiagCoeff L (j + 1) k * dyadicWeight L 1 := by
      have hk' : k ≤ j + 1 := by omega
      simp only [almostDiagCoeff, hk', ↓reduceIte]
      rw [show j + 1 - k = (j - k) + 1 by omega, ENNReal.dyadicWeight_add_nat, mul_assoc,
        ENNReal.dyadicWeight_neg_mul_self, mul_one]
    rw [eLpNorm_conv_eq_enorm_convLp (b.integrable_kernel L (j + 1)) (integrable_Theta k)]
    calc ‖convLp h1 (b.integrable_kernel L (j + 1)) Θ‖ₑ
        ≤ 2 * (∫⁻ z, ‖b.toFun z‖ₑ) * ENNReal.ofReal (1 + b.radius) ^ L * lpModulus 1 L Θ j :=
          b.enorm_localMean_succ_le h1 L j Θ
      _ ≤ 2 * (∫⁻ z, ‖b.toFun z‖ₑ) * ENNReal.ofReal (1 + b.radius) ^ L *
            (dyadicWeight (-(L : ℝ)) (j - k) * D) := mul_le_mul' le_rfl hmod
      _ = C₂ * almostDiagCoeff L (j + 1) k := by rw [hc]; ring
      _ ≤ (C₀ + C₂) * almostDiagCoeff L (j + 1) k := mul_le_mul' le_add_self le_rfl
  · have hc : almostDiagCoeff L m k = 1 := by
      rw [almostDiagCoeff]
      split_ifs with h
      · rw [show m - k = 0 by omega, ENNReal.dyadicWeight_zero_right]
      · rfl
    rw [hc, mul_one]
    refine (eLpNorm_conv_le le_rfl (b.integrable_kernel L m).aestronglyMeasurable
      (integrable_Theta k).aestronglyMeasurable).trans ?_
    rw [eLpNorm_Theta_one]
    exact (mul_le_mul' (b.eLpNorm_kernel_one_le L m) le_rfl).trans le_self_add

end LocalMeansBump

/-! ### Littlewood–Paley blocks and mixed local means -/

namespace LocalMeansBump

variable (b : LocalMeansBump ℝ)

/-- One term of the comparison: `‖δ_m ⋆ η_k ⋆ h‖_p ≤ C^d ∏_i c(m_i, k_i) ‖h‖_p` if
`‖ψ_m ⋆ η_k‖_1 ≤ C c(m, k)` in one variable. -/
theorem enorm_mixedBlock_convLp_mixedDual_le (hp : p ≠ ∞) (L : ℕ) {C : ℝ≥0∞}
    (hC : ∀ m k : ℕ, eLpNorm (conv (psi (V := ℝ) m) (b.dual L k) volume) 1 volume ≤
      C * almostDiagCoeff L m k)
    (m k : Fin d → ℕ) (h : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖mixedBlock hp m (convLp hp (b.integrable_mixedDual L k) h)‖ₑ ≤
      C ^ d * (∏ i, almostDiagCoeff L (m i) (k i)) * ‖h‖ₑ := by
  rw [mixedBlock, convLp_convLp]
  refine (enorm_convLp_le hp _ h).trans (mul_le_mul' ?_ le_rfl)
  rw [mixedPsi, mixedDual, conv_tensorKernel,
    eLpNorm_tensorKernel_one fun i => integrable_conv (integrable_psi _) (b.integrable_dual L _),
    ← Fin.prod_const d C, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod fun i _ => hC (m i) (k i)

/-- One term of the comparison: `‖k_m ⋆ δ_k ⋆ f‖_p ≤ C^d ∏_i c(m_i, k_i) ‖δ_k ⋆ f‖_p` if
`‖k_m ⋆ Θ_k‖_1 ≤ C c(m, k)` in one variable, since `δ_k = (⊗Θ_{k_i}) ⋆ δ_k`. -/
theorem enorm_mixedLocalMean_mixedBlock_le (hp : p ≠ ∞) (L : ℕ) {C : ℝ≥0∞}
    (hC : ∀ m k : ℕ, eLpNorm (conv (b.kernel L m) (Theta (V := ℝ) k) volume) 1 volume ≤
      C * almostDiagCoeff L m k)
    (m k : Fin d → ℕ) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖b.mixedLocalMean hp L m (mixedBlock hp k f)‖ₑ ≤
      C ^ d * (∏ i, almostDiagCoeff L (m i) (k i)) * ‖mixedBlock hp k f‖ₑ := by
  have hΘ : mixedBlock hp k f = convLp hp (integrable_mixedTheta k) (mixedBlock hp k f) := by
    rw [mixedBlock, convLp_convLp]
    exact (convLp_congr hp _ _ (conv_mixedTheta_mixedPsi k) f).symm
  conv_lhs => rw [hΘ, mixedLocalMean, convLp_convLp]
  refine (enorm_convLp_le hp _ _).trans (mul_le_mul' ?_ le_rfl)
  rw [mixedKernel, mixedTheta, conv_tensorKernel,
    eLpNorm_tensorKernel_one fun i => integrable_conv (b.integrable_kernel L _)
      (integrable_Theta _),
    ← Fin.prod_const d C, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod fun i _ => hC (m i) (k i)

/-- **Littlewood–Paley blocks are bounded by the mixed local means**: there is `C < ∞` with
`‖(2^(s|m|_1) ‖δ_m ⋆ f‖_p)_m‖_{ℓ_q} ≤ (C C_s)^d ‖(2^(s|k|_1) ‖k_k ⋆ f‖_p)_k‖_{ℓ_q}` for `0 ≤ s`,
`C_s` the constant of the almost diagonal lemma (`Rd.lqNorm_le_of_le_almostDiagonal_pi`). -/
theorem exists_mixedLPNorm_le (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {s : ℝ}, 0 ≤ s → ∀ {q : ℝ≥0∞}, 1 ≤ q →
      ∀ f : Lp ℂ p (volume : Measure (Fin d → ℝ)),
        mixedLPNorm hp s q f ≤
          (C * ENNReal.almostDiagonalConst s L) ^ d * b.mixedLocalMeansNorm hp L s q f := by
  obtain ⟨C, hC, hE⟩ := b.exists_eLpNorm_conv_psi_dual_le L
  refine ⟨C, hC, fun {s} hs {q} hq f => ?_⟩
  set h : (Fin d → ℕ) → Lp ℂ p (volume : Measure (Fin d → ℝ)) := fun k => b.mixedLocalMean hp L k f
  have hblock : ∀ m, ‖mixedBlock hp m f‖ₑ ≤
      C ^ d * ∑' k, (∏ i, almostDiagCoeff L (m i) (k i)) * ‖h k‖ₑ := fun m => by
    have hrep := ((mixedBlock hp m).continuous.tendsto f).comp
      (b.tendsto_sum_mixedDual_mixedLocalMean hp hL f)
    simp only [Function.comp_def, map_sum] at hrep
    have h1 := ENNReal.le_tsum_of_tendsto_finsetSum (Q := fun x : Lp ℂ p (volume : Measure (Fin
      d → ℝ)) =>
      ‖x‖ₑ) (C := 1) ENNReal.one_ne_top (fun x y => eNorm_add_le x y) (fun x => (one_mul _).ge)
      hrep
    refine h1.trans ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun k => ?_
    rw [← mul_assoc]
    exact b.enorm_mixedBlock_convLp_mixedDual_le hp L hE m k (h k)
  exact lqNorm_le_of_le_almostDiagonal_pi hq hs hblock

/-- **The mixed local means are bounded by the Littlewood–Paley blocks**: there is `C < ∞` with
`‖(2^(s|m|_1) ‖k_m ⋆ f‖_p)_m‖_{ℓ_q} ≤ (C C_s)^d ‖(2^(s|k|_1) ‖δ_k ⋆ f‖_p)_k‖_{ℓ_q}` for `0 ≤ s`
(`Rd.lqNorm_le_of_le_almostDiagonal_pi`). -/
theorem exists_mixedLocalMeansNorm_le (hp : p ≠ ∞) (L : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {s : ℝ}, 0 ≤ s → ∀ {q : ℝ≥0∞}, 1 ≤ q →
      ∀ f : Lp ℂ p (volume : Measure (Fin d → ℝ)),
        b.mixedLocalMeansNorm hp L s q f ≤
          (C * ENNReal.almostDiagonalConst s L) ^ d * mixedLPNorm hp s q f := by
  obtain ⟨C, hC, hE⟩ := b.exists_eLpNorm_conv_kernel_Theta_le L
  refine ⟨C, hC, fun {s} hs {q} hq f => ?_⟩
  set h : (Fin d → ℕ) → Lp ℂ p (volume : Measure (Fin d → ℝ)) := fun k => mixedBlock hp k f
  have hmean : ∀ m, ‖b.mixedLocalMean hp L m f‖ₑ ≤
      C ^ d * ∑' k, (∏ i, almostDiagCoeff L (m i) (k i)) * ‖h k‖ₑ := fun m => by
    have hrep := ((b.mixedLocalMean hp L m).continuous.tendsto f).comp
      (tendsto_sum_mixedBlock hp f)
    simp only [Function.comp_def, map_sum] at hrep
    have h1 := ENNReal.le_tsum_of_tendsto_finsetSum (Q := fun x : Lp ℂ p (volume : Measure (Fin
      d → ℝ)) =>
      ‖x‖ₑ) (C := 1) ENNReal.one_ne_top (fun x y => eNorm_add_le x y) (fun x => (one_mul _).ge)
      hrep
    refine h1.trans ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun k => ?_
    rw [← mul_assoc]
    exact b.enorm_mixedLocalMean_mixedBlock_le hp L hE m k f
  exact lqNorm_le_of_le_almostDiagonal_pi hq hs hmean

end LocalMeansBump

/-- **Littlewood–Paley blocks, local means and differences** (Vybíral; T. Ullrich): for
`1 ≤ p < ∞`, `0 < s < L` and `1 ≤ q ≤ ∞`,
`‖(2^(s|k|_1) Ω^{e(k)}_L(f, 2^(-k))_p)_k‖_{ℓ_q(ℕ^d)} < ∞` iff
`‖(2^(s|k|_1) ‖δ_k ⋆ f‖_p)_k‖_{ℓ_q(ℕ^d)} < ∞`, through the mixed local means of the centred bump of
radius `1`. -/
theorem mixedBesov_iff_mixedLP (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s < L) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    mixedModNorm p L s q f < ∞ ↔ mixedLPNorm hp s q f < ∞ := by
  set b := LocalMeansBump.centered (V := ℝ) one_pos
  have hR : b.radius ≤ 1 := (LocalMeansBump.centered_radius (V := ℝ) one_pos).le
  rw [b.mixedBesov_iff_mixedLocalMeans hp hL hR hs hsL hq f]
  obtain ⟨C₁, hC₁, h1⟩ := b.exists_mixedLPNorm_le (d := d) hp hL
  obtain ⟨C₂, hC₂, h2⟩ := b.exists_mixedLocalMeansNorm_le (d := d) hp L
  have hA := ENNReal.almostDiagonalConst_ne_top hs hsL
  constructor
  · intro h
    exact (h1 hs.le hq f).trans_lt (ENNReal.mul_lt_top
      (ENNReal.pow_lt_top (ENNReal.mul_lt_top hC₁.lt_top hA.lt_top)) h)
  · intro h
    exact (h2 hs.le hq f).trans_lt (ENNReal.mul_lt_top
      (ENNReal.pow_lt_top (ENNReal.mul_lt_top hC₂.lt_top hA.lt_top)) h)

end Rd
