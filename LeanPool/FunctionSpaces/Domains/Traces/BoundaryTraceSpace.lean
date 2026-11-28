/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Sobolev.LipschitzDomainH1
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The trace space of a bounded Lipschitz domain

Let `Ω` be a bounded Lipschitz domain with boundary `Γ` in a finite-dimensional real inner
product space `V`, such as `ℝ^d`, with Lebesgue measure, and `H^1(Ω)` the Hilbert space
`Rd.RestrictionSpace 1 Ω` (`Rd.BoundedLipschitzDomain.SobolevOne`). The trace space
`H^{1/2}(Γ)` is defined as the orthogonal complement of the trace kernel in `H^1(Ω)`, a Hilbert
space; the trace, the extension and the quotient isometry below hold by this definition. Its
norm is equivalent to the norm of `B^{1/2}_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`).

* **`H^1(V)` in Besov spaces, with constants**: for `U ∈ H^1(V)` with `L_2` function `ι U`
  (`Rd.toL2`), `‖ι U‖_2 + ‖(2^k ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2} ≤ C ‖U‖` with an explicit `C`
  (`Rd.modNorm_two_le_norm`), and the `B^{1/2}_{2,1}` quantity is at most `√2` times the
  `B^1_{2,2}` quantity (`Rd.modNorm_half_one_le`, by the Cauchy–Schwarz inequality
  `ENNReal.lqNorm_one_mul_le` and `‖(2^(-k/2))_k‖_{ℓ_2} = √2`,
  `ENNReal.lqNorm_two_dyadicWeight_neg_half`); together `H^1(V) ⊆ B^{1/2}_{2,1}(V)` with
  constant `√2 C` (`Rd.modNorm_half_one_le_norm`). Conversely
  `‖U‖ ≤ C' (‖ι U‖_2 + ‖(2^k ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2})` with an explicit `C'`
  (`Rd.enorm_le_modNorm_two`). The trace of `H^1(V)` on one Lipschitz
  graph is bounded (`Rd.LipschitzGraph.exists_enorm_trace_toL2_le`): a bounded operator
  `H^1(V) → L_2(H)` (`Rd.LipschitzGraph.traceH1`), equal to `w ∘ γ` for Schwartz functions `w`
  (`Rd.LipschitzGraph.traceH1_ofSchwartz_ae`).
* **Chart traces**: `u ↦ Tr_j(ψ_j u)` is a bounded operator from `H^1(Ω)` to `L_2` of the
  hyperplane of the chart `j` (`Rd.BoundedLipschitzDomain.chartTrace`), for the canonical
  resolution of unity `Rd.BoundedLipschitzDomain.boundaryPartition`.
* **The trace kernel**: `Rd.BoundedLipschitzDomain.traceKer` is the closed subspace of the
  `u ∈ H^1(Ω)` whose boundary trace vanishes almost everywhere on `Γ`, for every resolution of
  unity (`Rd.BoundedLipschitzDomain.mem_traceKer_iff`).
* **The trace space** `H^{1/2}(Γ)` is its orthogonal complement
  (`Rd.BoundedLipschitzDomain.TraceSpace`), with the trace `Rd.BoundedLipschitzDomain.trace`, the
  orthogonal projection, and the extension `Rd.BoundedLipschitzDomain.extend`, the inclusion:
  `trace ∘ extend = id`, both have norm at most `1`, the kernel of the trace is the trace kernel,
  and `H^1(Ω) ⧸ traceKer ≅ H^{1/2}(Γ)` isometrically
  (`Rd.BoundedLipschitzDomain.quotientEquivTraceSpace`). Two elements of `H^1(Ω)` have the same
  trace iff their boundary traces agree almost everywhere on `Γ`
  (`Rd.BoundedLipschitzDomain.trace_eq_iff`), and the boundary traces of the elements of the trace
  space are the functions of `B^{1/2}_{2,2}(Γ)`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_extend`,
  `Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov`).
* **`H^{-1/2}(Γ)`** is the dual of the trace space (`Rd.BoundedLipschitzDomain.DualTraceSpace`),
  conjugate-linearly isometric to it by Riesz (`Rd.BoundedLipschitzDomain.dualTraceEquiv`), and
  the adjoint of the trace is the extension (`Rd.BoundedLipschitzDomain.adjoint_trace`).
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace Metric
open scoped ENNReal SchwartzMap BesselPotentialSpace InnerProductSpace
open TemperedDistribution (besselPotential)
open ENNReal (lqNorm dyadicWeight)

/-! ### A sum of dyadic weights -/

namespace ENNReal

/-- `‖(2^(-k/2))_k‖_{ℓ_2} = √2`, since `∑_k 2^(-k) = 2`. -/
theorem lqNorm_two_dyadicWeight_neg_half :
    lqNorm 2 (dyadicWeight (-(1 / 2))) = 2 ^ (1 / 2 : ℝ) := by
  rw [ENNReal.lqNorm_eq_tsum two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
  simp_rw [ENNReal.dyadicWeight_rpow]
  norm_num [ENNReal.tsum_dyadicWeight_neg_one]

end ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### `H^1(V)` in Besov spaces, with constants -/

/-- **`B^1_{2,2}(V) ⊆ B^{1/2}_{2,1}(V)` with constant `√2`**: for every `F ∈ L_2(V)`,
`‖F‖_2 + ∑_k 2^(k/2) ω_2(F, 2^(-k))_2 ≤ √2 (‖F‖_2 + ‖(2^k ω_2(F, 2^(-k))_2)_k‖_{ℓ_2})`, by the
Cauchy–Schwarz inequality `∑_k 2^(-k/2) (2^k ω_k) ≤ ‖(2^(-k/2))_k‖_{ℓ_2} ‖(2^k ω_k)_k‖_{ℓ_2}`. The
left side is the norm in which the trace on a Lipschitz graph domain is bounded
(`Rd.LipschitzGraph.enorm_trace_le`). -/
theorem modNorm_half_one_le (F : Lp ℂ 2 (volume : Measure V)) :
    ‖F‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / 2) k * lpModulus 2 2 F k) ≤
      2 ^ (1 / 2 : ℝ) * (‖F‖ₑ + lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 2 F k)) := by
  have hw : ∀ k, dyadicWeight (1 / 2) k * lpModulus 2 2 F k =
      dyadicWeight (-(1 / 2)) k * (dyadicWeight 1 k * lpModulus 2 2 F k) := fun k => by
    rw [← mul_assoc, ← ENNReal.dyadicWeight_add]
    norm_num
  have hcs : lqNorm 1 (fun k => dyadicWeight (1 / 2) k * lpModulus 2 2 F k) ≤
      2 ^ (1 / 2 : ℝ) * lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 2 F k) := by
    simp_rw [hw]
    exact (ENNReal.lqNorm_one_mul_le _ _).trans_eq
      (by rw [ENNReal.lqNorm_two_dyadicWeight_neg_half])
  have h1 : (1 : ℝ≥0∞) ≤ 2 ^ (1 / 2 : ℝ) := ENNReal.one_le_rpow (by norm_num) (by norm_num)
  rw [mul_add]
  exact add_le_add (le_mul_of_one_le_left bot_le h1) hcs

variable (V) in
/-- **The constant of `H^1(V) ⊆ B^1_{2,2}(V)`**: `C_inv · 2 (1 - 2^(-1))⁻¹ · (2 · 4)^{1/2}`, the
product of the constants of the three inclusions behind `Rd.modNorm_two_le_norm`: the inverse
inequality for the moduli of order `2` (`ApproximationScheme.ModulusData.inverseConst` of
`Rd.bandModulusData`), `F^1_{2,2} ⊆ B^1_{2,2}` (`Rd.approxNormDyadic_le_triebelLizorkinNorm`) and
`H^1 ⊆ F^1_{2,2}` (`Rd.triebelLizorkinNorm_le_of_besselPotential_eq`). -/
noncomputable def sobolevOneBesovConst : ℝ≥0∞ :=
  (bandModulusData (V := V) two_ne_top 2).inverseConst 1 *
    (2 * (1 - (2 : ℝ≥0∞) ^ (-1 : ℝ))⁻¹) * (2 * 4 ^ (1 : ℝ)) ^ (1 / 2 : ℝ)

/-- The constant of `H^1(V) ⊆ B^1_{2,2}(V)` is finite. -/
theorem sobolevOneBesovConst_ne_top : sobolevOneBesovConst V ≠ ∞ := by
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ((bandModulusData two_ne_top 2).inverseConst_ne_top (by norm_num))
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.one_sub_two_rpow_neg_inv_ne_top one_pos)))
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.rpow_ne_top_of_nonneg zero_le_one (by norm_num))))

/-- **`H^1(V) ⊆ B^1_{2,2}(V)` with an explicit constant**: for every `U ∈ H^1(V)` with `L_2`
function `ι U`, `‖ι U‖_2 + ‖(2^k ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2} ≤ C ‖U‖` with
`C = Rd.sobolevOneBesovConst V`: the moduli are bounded by the band-limited approximation norm
(`ApproximationScheme.ModulusData.modNorm_le_approxNormDyadic`), which is bounded by the norm of
`F^1_{2,2}` (`Rd.approxNormDyadic_le_triebelLizorkinNorm`), which is at most
`(2 · 4)^{1/2} ‖J_1 ι U‖_2` (`Rd.triebelLizorkinNorm_le_of_besselPotential_eq`), and
`‖J_1 ι U‖_2 = ‖U‖` (`BesselPotentialSpace.enorm_toLp_eq`). -/
theorem modNorm_two_le_norm (U : H^{1}(V)) :
    ‖toL2 U‖ₑ + lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 2 (toL2 U) k) ≤
      sobolevOneBesovConst V * ‖U‖ₑ := by
  have hfh : besselPotential V ℂ 1 ((toL2 U : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) =
      (U.toLp : 𝓢'(V, ℂ)) := by
    rw [toTemperedDistribution_toL2]
    exact U.bessel_toDistr_eq_toLp
  have h1 := (bandModulusData (V := V) two_ne_top 2).modNorm_le_approxNormDyadic one_le_two
    zero_le_one (by norm_num) (toL2 U)
  have h2 := approxNormDyadic_le_triebelLizorkinNorm two_ne_top one_pos one_le_two (toL2 U)
  rw [max_self] at h2
  have h3 := triebelLizorkinNorm_le_of_besselPotential_eq zero_le_one hfh
  rw [U.enorm_toLp_eq] at h3
  calc ‖toL2 U‖ₑ + lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 2 (toL2 U) k)
      ≤ (bandModulusData (V := V) two_ne_top 2).inverseConst 1 *
          (bandScheme two_ne_top).approxNormDyadic 1 2 (toL2 U) := h1
    _ ≤ (bandModulusData (V := V) two_ne_top 2).inverseConst 1 *
          (2 * (1 - (2 : ℝ≥0∞) ^ (-1 : ℝ))⁻¹ * triebelLizorkinNorm 1 2 (toL2 U)) := by gcongr
    _ ≤ (bandModulusData (V := V) two_ne_top 2).inverseConst 1 *
          (2 * (1 - (2 : ℝ≥0∞) ^ (-1 : ℝ))⁻¹ * ((2 * 4 ^ (1 : ℝ)) ^ (1 / 2 : ℝ) * ‖U‖ₑ)) := by
        gcongr
    _ = sobolevOneBesovConst V * ‖U‖ₑ := by
        rw [sobolevOneBesovConst]
        ring

variable (V) in
/-- **The constant of the bound of `H^1(V)` by `B^1_{2,2}(V)`**:
`(2 · 5)^{1/2} · 8 · 8 ‖Φ‖_1 · D`, the product of the constants of the three inclusions behind
`Rd.enorm_le_modNorm_two`: `F^1_{2,2} ⊆ H^1` (`Rd.enorm_besselPotential_le_triebelLizorkinNorm`),
`A^1_2 ⊆ F^1_{2,2}` for the band-limited approximation spaces, with the Littlewood–Paley kernel
`Φ = Rd.lpKernel` (`Rd.triebelLizorkinNorm_le_approxNormDyadic`), and Jackson's direction for the
moduli of order `2` (`ApproximationScheme.ModulusData.directConst` of `Rd.bandModulusData`). -/
noncomputable def sobolevOneInvConst : ℝ≥0∞ :=
  (2 * 5 ^ (1 : ℝ)) ^ (1 / 2 : ℝ) *
    (8 * dyadicWeight 1 3 * eLpNorm (lpKernel (V := V)) 1 volume) *
      (bandModulusData (V := V) two_ne_top 2).directConst 1

/-- The constant of the bound of `H^1(V)` by `B^1_{2,2}(V)` is finite. -/
theorem sobolevOneInvConst_ne_top : sobolevOneInvConst V ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.rpow_ne_top_of_nonneg zero_le_one (by norm_num))))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.dyadicWeight_ne_top 1 3))
      eLpNorm_lpKernel_ne_top))
    ((bandModulusData two_ne_top 2).directConst_ne_top 1)

/-- **The norm of `H^1(V)` by the `B^1_{2,2}(V)` quantity, with an explicit constant**, the
converse of `Rd.modNorm_two_le_norm`: for every `U ∈ H^1(V)` with `L_2` function `ι U`,
`‖U‖ ≤ C (‖ι U‖_2 + ‖(2^k ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2})` with `C = Rd.sobolevOneInvConst V`:
`‖U‖ = ‖J_1 ι U‖_2` (`BesselPotentialSpace.enorm_toLp_eq`) is at most `(2 · 5)^{1/2}` times the
norm of `F^1_{2,2}` (`Rd.enorm_besselPotential_le_triebelLizorkinNorm`), which is bounded by the
band-limited approximation norm (`Rd.triebelLizorkinNorm_le_approxNormDyadic`), which is bounded by
the moduli (`ApproximationScheme.ModulusData.approxNormDyadic_le_modNorm`). -/
theorem enorm_le_modNorm_two (U : H^{1}(V)) :
    ‖U‖ₑ ≤ sobolevOneInvConst V *
      (‖toL2 U‖ₑ + lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 2 (toL2 U) k)) := by
  have hfh : besselPotential V ℂ 1 ((toL2 U : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) =
      (U.toLp : 𝓢'(V, ℂ)) := by
    rw [toTemperedDistribution_toL2]
    exact U.bessel_toDistr_eq_toLp
  have h1 := enorm_besselPotential_le_triebelLizorkinNorm zero_le_one hfh
  rw [U.enorm_toLp_eq] at h1
  have h2 := triebelLizorkinNorm_le_approxNormDyadic two_ne_top zero_le_one one_le_two (toL2 U)
  rw [min_self] at h2
  have h3 := (bandModulusData (V := V) two_ne_top 2).approxNormDyadic_le_modNorm (s := 1)
    one_le_two (toL2 U)
  calc ‖U‖ₑ ≤ (2 * 5 ^ (1 : ℝ)) ^ (1 / 2 : ℝ) * triebelLizorkinNorm 1 2 (toL2 U) := h1
    _ ≤ (2 * 5 ^ (1 : ℝ)) ^ (1 / 2 : ℝ) *
        (8 * dyadicWeight 1 3 * eLpNorm (lpKernel (V := V)) 1 volume *
          (bandScheme two_ne_top).approxNormDyadic 1 2 (toL2 U)) := by gcongr
    _ ≤ (2 * 5 ^ (1 : ℝ)) ^ (1 / 2 : ℝ) *
        (8 * dyadicWeight 1 3 * eLpNorm (lpKernel (V := V)) 1 volume *
          ((bandModulusData (V := V) two_ne_top 2).directConst 1 *
            (‖toL2 U‖ₑ + lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 2 (toL2 U) k)))) := by
        gcongr
        exact h3
    _ = _ := by
        rw [sobolevOneInvConst]
        ring

/-- **`H^1(V) ⊆ B^{1/2}_{2,1}(V)` with an explicit constant**: for every `U ∈ H^1(V)` with `L_2`
function `ι U`, `‖ι U‖_2 + ∑_k 2^(k/2) ω_2(ι U, 2^(-k))_2 ≤ √2 C ‖U‖` with
`C = Rd.sobolevOneBesovConst V` (`Rd.modNorm_half_one_le`, `Rd.modNorm_two_le_norm`). The left
side bounds the traces on Lipschitz graph domains (`Rd.LipschitzGraph.enorm_trace_le`). -/
theorem modNorm_half_one_le_norm (U : H^{1}(V)) :
    ‖toL2 U‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / 2) k * lpModulus 2 2 (toL2 U) k) ≤
      2 ^ (1 / 2 : ℝ) * sobolevOneBesovConst V * ‖U‖ₑ := by
  rw [mul_assoc]
  exact (modNorm_half_one_le _).trans (mul_le_mul' le_rfl (modNorm_two_le_norm U))

/-- **The hypothesis of the trace theorems for `H^1(V)`**: for every `U ∈ H^1(V)`,
`‖ι U‖_2 + ‖(2^(k(1/2 + 1/2)) ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2} < ∞`, the finiteness that the boundary
traces at `s = 1/2`, `p = q = 2` and order `L = 2` ask for (`Rd.modNorm_two_le_norm`). -/
theorem modNorm_toL2_lt_top (U : H^{1}(V)) :
    ‖toL2 U‖ₑ + lqNorm 2 (fun k => dyadicWeight (1 / 2 + 1 / (2 : ℝ≥0∞).toReal) k *
      lpModulus 2 2 (toL2 U) k) < ∞ := by
  have hσ : (1 / 2 : ℝ) + 1 / (2 : ℝ≥0∞).toReal = 1 := by norm_num
  rw [hσ]
  exact (modNorm_two_le_norm U).trans_lt
    (ENNReal.mul_lt_top sobolevOneBesovConst_ne_top.lt_top eNorm_lt_top)

/-- **The trace of `H^1(V)` on a Lipschitz graph is bounded**: `‖Tr ι U‖_{L_2(H)} ≤ C ‖U‖` for every
`U ∈ H^1(V)` with `L_2` function `ι U` (`Rd.toL2`), with `C = K √2 Rd.sobolevOneBesovConst V` for
the constant `K` of the trace bound in the `B^{1/2}_{2,1}` quantity
(`Rd.LipschitzGraph.enorm_trace_le`, `Rd.modNorm_half_one_le_norm`). -/
theorem LipschitzGraph.exists_enorm_trace_toL2_le (Ω : LipschitzGraph V) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ U : H^{1}(V), ‖Ω.trace two_ne_top 2 (toL2 U)‖ₑ ≤ C * ‖U‖ₑ := by
  obtain ⟨K, hK, hle⟩ := Ω.enorm_trace_le two_ne_top 2
  refine ⟨K * (2 ^ (1 / 2 : ℝ) * sobolevOneBesovConst V), ENNReal.mul_ne_top hK
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num))
      sobolevOneBesovConst_ne_top), fun U => ?_⟩
  have hw : 1 / (2 : ℝ≥0∞).toReal = 1 / 2 := by norm_num
  have h1 := hle (toL2 U)
  rw [hw] at h1
  rw [mul_assoc]
  exact h1.trans (mul_le_mul' le_rfl (modNorm_half_one_le_norm U))

/-! ### The trace of `H^1(V)` on a Lipschitz graph as an operator -/

namespace LipschitzGraph

variable (Ω : LipschitzGraph V)

/-- The `L_2` functions of `H^1(V)` satisfy the hypothesis of the trace theorem on `Ω` at
`s = 1/2`, `p = q = 2` and order `2` (`Rd.modNorm_toL2_lt_top`). -/
theorem intrinsicNorm_toL2_lt_top (U : H^{1}(V)) :
    Ω.intrinsicNorm two_ne_top 2 (1 / 2 + 1 / (2 : ℝ≥0∞).toReal) 2 (toL2 U) < ∞ :=
  (Ω.intrinsicNorm_lt_top_of_modNorm two_ne_top 2 one_le_two (modNorm_toL2_lt_top U)).2

/-- The trace of `H^1(V)` on the graph as a linear map, `U ↦ Tr(ι U)` for the `L_2` function
`ι U` (`Rd.LipschitzGraph.trace_sub`, `Rd.LipschitzGraph.trace_smul`). -/
noncomputable def traceH1Linear : H^{1}(V) →ₗ[ℂ] Lp ℂ 2 (volume : Measure Ω.hyperplane) where
  toFun U := Ω.trace two_ne_top 2 (toL2 U)
  map_add' U W := by
    have h := Ω.trace_sub two_ne_top 2 (s := 1 / 2) (by norm_num) one_le_two
      (Ω.intrinsicNorm_toL2_lt_top (U + W)) (Ω.intrinsicNorm_toL2_lt_top W)
    rw [map_add, add_sub_cancel_right] at h
    rw [map_add, h, sub_add_cancel]
  map_smul' c U := by
    simp only [map_smul, RingHom.id_apply, LipschitzGraph.trace_smul]

/-- **The trace of `H^1(V)` on a Lipschitz graph** as a bounded operator `H^1(V) → L_2(H)`,
`U ↦ Tr(ι U)` (`Rd.LipschitzGraph.exists_enorm_trace_toL2_le`). -/
noncomputable def traceH1 : H^{1}(V) →L[ℂ] Lp ℂ 2 (volume : Measure Ω.hyperplane) :=
  (Ω.traceH1Linear).mkContinuousOfExistsBound (by
    obtain ⟨C, hC, hle⟩ := Ω.exists_enorm_trace_toL2_le
    refine ⟨C.toReal, fun U => ?_⟩
    rw [← toReal_eNorm, ← toReal_eNorm U, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC eNorm_ne_top) (hle U))

/-- `traceH1 U = Tr(ι U)`. -/
theorem traceH1_apply (U : H^{1}(V)) : Ω.traceH1 U = Ω.trace two_ne_top 2 (toL2 U) :=
  rfl

/-- **The trace of a Schwartz function** is its restriction to the graph: `Tr w = w ∘ γ` almost
everywhere on `H` (`Rd.LipschitzGraph.trace_ae_eq_comp_graphMap`). -/
theorem traceH1_ofSchwartz_ae (w : 𝓢(V, ℂ)) :
    (Ω.traceH1 (ofSchwartz 1 w) : Ω.hyperplane → ℂ) =ᵐ[volume] fun x' => w (Ω.graphMap x') := by
  rw [traceH1_apply]
  refine Ω.trace_ae_eq_comp_graphMap two_ne_top (L := 2) one_le_two (s := 1 / 2) (by norm_num)
    one_le_two (Ω.intrinsicNorm_lt_top_of_modNorm two_ne_top 2 one_le_two
      (modNorm_toL2_lt_top (ofSchwartz 1 w))).1 w.continuous ?_
  rw [toL2_ofSchwartz]
  exact w.coeFn_toLp 2 volume

end LipschitzGraph

/-! ### The chart traces of `H^1(Ω)` -/

namespace BoundedLipschitzDomain

/-- **The Sobolev space `H^1(Ω)`** of a bounded Lipschitz domain, as a Hilbert space: the
restriction space `Rd.RestrictionSpace 1 Ω` of the open set `Ω`. `Rd.restrictL2` identifies its
elements with the restrictions to `Ω` of the functions of `Rd.BoundedLipschitzDomain.MemSobolevOn`
(`Rd.BoundedLipschitzDomain.memSobolevOn_iff_exists_restrictL2`). -/
abbrev SobolevOne (Ω : BoundedLipschitzDomain V) := RestrictionSpace 1 Ω.toOpens

/-- **The canonical resolution of unity** on the boundary of `Ω`, a fixed choice among the
nonnegative resolutions of `Rd.BoundedLipschitzDomain.exists_boundaryPartition_nonneg`: `ψ_j ≥ 0`
and `∑_j ψ_j ≤ 1` everywhere. The trace kernel uses it and does not depend on it
(`Rd.BoundedLipschitzDomain.mem_traceKer_iff`); the surface measure and the unit normal use its
nonnegativity. -/
noncomputable def boundaryPartition (Ω : BoundedLipschitzDomain V) : Ω.BoundaryPartition :=
  Ω.exists_boundaryPartition_nonneg.choose

omit [MeasurableSpace V] [BorelSpace V] in
/-- The functions of the canonical resolution of unity are nonnegative. -/
theorem boundaryPartition_nonneg (Ω : BoundedLipschitzDomain V) (j : Fin Ω.N) (y : V) :
    0 ≤ Ω.boundaryPartition.toFun j y :=
  Ω.exists_boundaryPartition_nonneg.choose_spec.1 j y

omit [MeasurableSpace V] [BorelSpace V] in
/-- The functions of the canonical resolution of unity sum to at most `1` everywhere. -/
theorem sum_boundaryPartition_le_one (Ω : BoundedLipschitzDomain V) (y : V) :
    ∑ j, Ω.boundaryPartition.toFun j y ≤ 1 :=
  Ω.exists_boundaryPartition_nonneg.choose_spec.2 y

namespace BoundaryPartition

variable {Ω : BoundedLipschitzDomain V} (ψ : Ω.BoundaryPartition)

/-- **A bound of the derivatives of `ψ_j`** up to order `2`, a choice among the bounds of
`Rd.exists_iteratedFDeriv_bound` (smooth functions with compact support). -/
noncomputable def derivBound (j : Fin Ω.N) : ℝ :=
  (exists_iteratedFDeriv_bound (ψ.contDiff_toComplex j) (ψ.hasCompactSupport_toComplex j) 2).choose

omit [MeasurableSpace V] [BorelSpace V] in
/-- The derivatives of `ψ_j` of order at most `2` are bounded by `ψ.derivBound j`. -/
theorem derivBound_spec (j : Fin Ω.N) :
    ∀ l ≤ 2, ∀ x, ‖iteratedFDeriv ℝ l (ψ.toComplex j) x‖ ≤ ψ.derivBound j :=
  (exists_iteratedFDeriv_bound (ψ.contDiff_toComplex j) (ψ.hasCompactSupport_toComplex j)
    2).choose_spec

omit [MeasurableSpace V] [BorelSpace V] in
/-- `|ψ_j| ≤ D_j` for the derivative bound `D_j = ψ.derivBound j`. -/
theorem enorm_toComplex_le (j : Fin Ω.N) (y : V) :
    ‖ψ.toComplex j y‖ₑ ≤ ENNReal.ofReal (ψ.derivBound j) := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_le_of_iteratedFDeriv_le (ψ.derivBound_spec j) y)

omit [MeasurableSpace V] [BorelSpace V] in
/-- `ψ_j` is Lipschitz: `|ψ_j(x) - ψ_j(y)| ≤ D_j |x - y|` for the derivative bound
`D_j = ψ.derivBound j` (`Rd.norm_higherDiff_le_of_iteratedFDeriv` with differences of order
`1`). -/
theorem enorm_toComplex_sub_le (j : Fin Ω.N) (x y : V) :
    ‖ψ.toComplex j x - ψ.toComplex j y‖ₑ ≤ ENNReal.ofReal (ψ.derivBound j) * ‖x - y‖ₑ := by
  have h := norm_higherDiff_le_of_iteratedFDeriv (ψ.contDiff_toComplex j) (l := 1)
    (fun z => ψ.derivBound_spec j 1 (by norm_num) z) (x - y) y
  simp only [Function.iterate_one, fwdDiff, add_sub_cancel, pow_one] at h
  have hD : 0 ≤ ψ.derivBound j :=
    (norm_nonneg _).trans (norm_le_of_iteratedFDeriv_le (ψ.derivBound_spec j) y)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hD]
  exact ENNReal.ofReal_le_ofReal h

/-- **Localisation to the chart `j`**: `F ↦ ψ_j F` on `L_2(V)` (`Rd.mulLp`). -/
noncomputable def localize (j : Fin Ω.N) (F : Lp ℂ 2 (volume : Measure V)) :
    Lp ℂ 2 (volume : Measure V) :=
  mulLp (ψ.contDiff_toComplex j).continuous
    (norm_le_of_iteratedFDeriv_le (ψ.derivBound_spec j)) F

/-- **Localisations of `H^1(V)` functions satisfy the trace hypothesis**: for every resolution of
unity `ψ` and `U ∈ H^1(V)`, the intrinsic norm of `ψ_j ι U` of smoothness `1/2 + 1/2` on the graph
domain of every chart `k` is finite (`Rd.modNorm_mulLp_lt_top`, `Rd.modNorm_toL2_lt_top`). -/
theorem intrinsicNorm_localize_lt_top (j k : Fin Ω.N) (U : H^{1}(V)) :
    (Ω.graph k).intrinsicNorm two_ne_top 2 (1 / 2 + 1 / (2 : ℝ≥0∞).toReal) 2
      (ψ.localize j (toL2 U)) < ∞ :=
  ((Ω.graph k).intrinsicNorm_lt_top_of_modNorm two_ne_top 2 one_le_two
    (modNorm_mulLp_lt_top two_ne_top (ψ.contDiff_toComplex j)
      (ψ.derivBound_spec j) (by norm_num) one_le_two
      (modNorm_toL2_lt_top U))).2

end BoundaryPartition

variable (Ω : BoundedLipschitzDomain V)

/-- **The chart trace as a linear map**: `u ↦ Tr_j(ψ_j u)` from `H^1(Ω)` to `L_2(H_j)`, with the
trace of the graph domain of the chart `j` and the canonical resolution of unity. It is additive by
`Rd.LipschitzGraph.trace_sub` on the localised `H^1(V)` functions and homogeneous by
`Rd.LipschitzGraph.trace_smul` and `Rd.mulLp_smul`. -/
noncomputable def chartTraceLinear (j : Fin Ω.N) :
    Ω.SobolevOne →ₗ[ℂ] Lp ℂ 2 (volume : Measure (Ω.graph j).hyperplane) where
  toFun u := (Ω.graph j).trace two_ne_top 2
    (Ω.boundaryPartition.localize j (toL2 (u : H^{1}(V))))
  map_add' u w := by
    have h := (Ω.graph j).trace_sub two_ne_top 2 (s := 1 / 2) (by norm_num) one_le_two
      (Ω.boundaryPartition.intrinsicNorm_localize_lt_top j j ((u : H^{1}(V)) + w))
      (Ω.boundaryPartition.intrinsicNorm_localize_lt_top j j w)
    have he : Ω.boundaryPartition.localize j (toL2 ((u : H^{1}(V)) + w)) -
        Ω.boundaryPartition.localize j (toL2 (w : H^{1}(V))) =
          Ω.boundaryPartition.localize j (toL2 (u : H^{1}(V))) := by
      rw [BoundaryPartition.localize, BoundaryPartition.localize, ← mulLp_sub, map_add,
        add_sub_cancel_right]
      rfl
    rw [he] at h
    rw [Submodule.coe_add, h, sub_add_cancel]
  map_smul' c u := by
    simp only [Submodule.coe_smul, map_smul, RingHom.id_apply, BoundaryPartition.localize,
      mulLp_smul, LipschitzGraph.trace_smul]

/-- `chartTraceLinear Ω j u = Tr_j(ψ_j u)`. -/
theorem chartTraceLinear_apply (j : Fin Ω.N) (u : Ω.SobolevOne) :
    Ω.chartTraceLinear j u = (Ω.graph j).trace two_ne_top 2
      (Ω.boundaryPartition.localize j (toL2 (u : H^{1}(V)))) :=
  rfl

/-- **The chart traces are bounded**: `‖Tr_j(ψ_j U)‖_{L_2(H_j)} ≤ C ‖U‖` for every `U ∈ H^1(V)`, for
every resolution of unity `ψ`, with `C = K M √2 Rd.sobolevOneBesovConst V`. The trace is at most
`K` times the `B^{1/2}_{2,1}` quantity of `ψ_j U` (`Rd.LipschitzGraph.enorm_trace_le`), which is at
most `M` times that of `U` (`Rd.modNorm_mulLp_le`, with the multiplier constant `M` of `ψ_j` for
differences of order `2` and smoothness `1/2`), and that is at most
`√2 Rd.sobolevOneBesovConst V ‖U‖` (`Rd.modNorm_half_one_le_norm`). -/
theorem exists_enorm_trace_localize_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ U : H^{1}(V),
      ‖(Ω.graph j).trace two_ne_top 2 (ψ.localize j (toL2 U))‖ₑ ≤ C * ‖U‖ₑ := by
  obtain ⟨K, hK, hle⟩ := (Ω.graph j).enorm_trace_le two_ne_top 2
  -- the multiplier constant of `ψ_j` (`Rd.modNorm_mulLp_le` with `r = 2`, `s = 1/2`)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ≥0∞, M = ENNReal.ofReal (ψ.derivBound j) +
      ∑ l ∈ Finset.range (2 + 1), ((2 : ℕ).choose l : ℝ≥0∞) * ENNReal.ofReal (ψ.derivBound j) *
        multiplierConst (V := V) two_ne_top 2 (1 / 2) l := ⟨_, rfl⟩
  have hM : M ≠ ∞ := hMdef ▸ multiplierTotal_ne_top two_ne_top (by norm_num) (ψ.derivBound j)
  refine ⟨K * M * 2 ^ (1 / 2 : ℝ) * sobolevOneBesovConst V, ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK hM)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num))) sobolevOneBesovConst_ne_top,
    fun U => ?_⟩
  have hw : 1 / (2 : ℝ≥0∞).toReal = 1 / 2 := by norm_num
  have h1 := hle (ψ.localize j (toL2 U))
  rw [hw] at h1
  have h2 : ‖ψ.localize j (toL2 U)‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / 2) k *
      lpModulus 2 2 (ψ.localize j (toL2 U)) k) ≤
        M * (‖toL2 U‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / 2) k * lpModulus 2 2 (toL2 U) k)) :=
    hMdef ▸ modNorm_mulLp_le two_ne_top (ψ.contDiff_toComplex j)
      (ψ.derivBound_spec j) (s := 1 / 2) (by norm_num) le_rfl (toL2 U)
  calc ‖(Ω.graph j).trace two_ne_top 2 (ψ.localize j (toL2 U))‖ₑ
      ≤ K * (‖ψ.localize j (toL2 U)‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / 2) k *
          lpModulus 2 2 (ψ.localize j (toL2 U)) k)) := h1
    _ ≤ K * (M * (‖toL2 U‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / 2) k *
          lpModulus 2 2 (toL2 U) k))) := mul_le_mul' le_rfl h2
    _ ≤ K * (M * (2 ^ (1 / 2 : ℝ) * sobolevOneBesovConst V * ‖U‖ₑ)) := by
        gcongr; exact modNorm_half_one_le_norm U
    _ = K * M * 2 ^ (1 / 2 : ℝ) * sobolevOneBesovConst V * ‖U‖ₑ := by ring

/-- **The chart traces are bounded operators**: `u ↦ Tr_j(ψ_j u)` from `H^1(Ω)` to `L_2(H_j)`, with
the canonical resolution of unity (`Rd.BoundedLipschitzDomain.exists_enorm_trace_localize_le`). -/
noncomputable def chartTrace (j : Fin Ω.N) :
    Ω.SobolevOne →L[ℂ] Lp ℂ 2 (volume : Measure (Ω.graph j).hyperplane) :=
  (Ω.chartTraceLinear j).mkContinuousOfExistsBound (by
    obtain ⟨C, hC, hle⟩ := Ω.exists_enorm_trace_localize_le Ω.boundaryPartition j
    refine ⟨C.toReal, fun u => ?_⟩
    rw [← toReal_eNorm, ← toReal_eNorm u, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC eNorm_ne_top) (hle (u : H^{1}(V))))

/-- `chartTrace Ω j u = Tr_j(ψ_j u)`. -/
theorem chartTrace_apply (j : Fin Ω.N) (u : Ω.SobolevOne) :
    Ω.chartTrace j u = (Ω.graph j).trace two_ne_top 2
      (Ω.boundaryPartition.localize j (toL2 (u : H^{1}(V)))) :=
  rfl

/-- **The chart trace is the localised boundary trace**: `Tr_j(ψ_j u) = (ψ_j Tr_Γ u) ∘ γ_j`
almost everywhere on `H_j`, with the canonical resolution of unity
(`Rd.BoundedLipschitzDomain.trace_mulLp_ae_boundaryTrace`). -/
theorem chartTrace_ae_eq (j : Fin Ω.N) (u : Ω.SobolevOne) :
    (Ω.chartTrace j u : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume] fun x' =>
      Ω.boundaryPartition.toComplex j ((Ω.graph j).graphMap x') *
        Ω.boundaryTrace Ω.boundaryPartition two_ne_top 2 (toL2 (u : H^{1}(V)))
          ((Ω.graph j).graphMap x') :=
  Ω.trace_mulLp_ae_boundaryTrace Ω.boundaryPartition two_ne_top one_le_two (s := 1 / 2)
    (by norm_num) (by norm_num) one_le_two (modNorm_toL2_lt_top _) j
    (Ω.boundaryPartition.derivBound_spec j)

/-! ### The trace kernel -/

/-- **Vanishing on the boundary, chart by chart**: for every resolution of unity `ψ`, a function
`T` vanishes almost everywhere on `Γ` iff `(ψ_j T) ∘ γ_j = 0` almost everywhere on `H_j` for every
`j`. `⇐`: the localised statements hold almost everywhere on `Γ ∩ B_j`
(`Rd.BoundedLipschitzDomain.eventually_aeBoundary_of_chart`), and `T = ∑_j ψ_j T` on `Γ`. -/
theorem eventuallyEq_zero_iff_forall_chart (ψ : Ω.BoundaryPartition) (T : V → ℂ) :
    T =ᶠ[Ω.aeBoundary] 0 ↔ ∀ j, (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') *
      T ((Ω.graph j).graphMap x')) =ᵐ[(volume : Measure (Ω.graph j).hyperplane)] 0 := by
  constructor
  · intro h j
    filter_upwards [Ω.eventually_aeBoundary_iff.1 h j] with x' hx
    by_cases hψ : ψ.toFun j ((Ω.graph j).graphMap x') = 0
    · simp [ψ.toComplex_of_eq_zero hψ]
    · simp [hx (ψ.mem_ball_of_ne_zero hψ)]
  · intro h
    have hk : ∀ k, ∀ᶠ y in Ω.aeBoundary,
        y ∈ ball (Ω.center k) (Ω.radius k) → ψ.toComplex k y * T y = 0 := fun k =>
      Ω.eventually_aeBoundary_of_chart k ((h k).mono fun x' hx _ => hx)
    have hΓ : ∀ᶠ y in Ω.aeBoundary, y ∈ frontier Ω.carrier :=
      Ω.eventually_aeBoundary_iff.2 fun j =>
        Eventually.of_forall fun x' hx => Ω.graphMap_mem_frontier j hx
    filter_upwards [eventually_all.2 hk, hΓ] with y hy hyΓ
    calc T y = ∑ k, ψ.toComplex k y * T y := by
          rw [← Finset.sum_mul, ψ.sum_toComplex_eq_one hyΓ, one_mul]
      _ = 0 := Finset.sum_eq_zero fun k _ => by
          by_cases hψ : ψ.toFun k y = 0
          · rw [ψ.toComplex_of_eq_zero hψ, zero_mul]
          · exact hy k (ψ.mem_ball_of_ne_zero hψ)

/-- **The trace kernel** `ker γ ⊆ H^1(Ω)`: the `u` whose chart traces `Tr_j(ψ_j u)` all vanish, for
the canonical resolution of unity; equivalently, the `u` whose boundary trace vanishes almost
everywhere on `Γ`, for every resolution of unity (`Rd.BoundedLipschitzDomain.mem_traceKer_iff`). -/
noncomputable def traceKer : Submodule ℂ Ω.SobolevOne :=
  ⨅ j, (Ω.chartTrace j).ker

/-- The trace kernel is closed, an intersection of kernels of bounded operators. -/
theorem isClosed_traceKer : IsClosed (Ω.traceKer : Set Ω.SobolevOne) := by
  rw [traceKer, Submodule.coe_iInf]
  exact isClosed_iInter fun j => ContinuousLinearMap.isClosed_ker _

/-- The trace kernel is complete, as a closed subspace of the Hilbert space `H^1(Ω)`; hence it
has an orthogonal projection. -/
instance completeSpace_traceKer : CompleteSpace Ω.traceKer :=
  Ω.isClosed_traceKer.completeSpace_coe

/-- **The trace kernel by the boundary trace**: for every resolution of unity `ψ`, `u ∈ H^1(Ω)`
lies in the trace kernel iff its boundary trace `Tr_Γ u` vanishes almost everywhere on `Γ`. In
particular the trace kernel does not depend on the resolution of unity in its definition. The
chart traces are the localised boundary traces (`Rd.BoundedLipschitzDomain.chartTrace_ae_eq`),
`Rd.BoundedLipschitzDomain.eventuallyEq_zero_iff_forall_chart` collects them, and the boundary
traces of two resolutions agree almost everywhere on `Γ`
(`Rd.BoundedLipschitzDomain.boundaryTrace_eventuallyEq`). -/
theorem mem_traceKer_iff (ψ : Ω.BoundaryPartition) (u : Ω.SobolevOne) :
    u ∈ Ω.traceKer ↔
      Ω.boundaryTrace ψ two_ne_top 2 (toL2 (u : H^{1}(V))) =ᶠ[Ω.aeBoundary] 0 := by
  have hψ := Ω.boundaryTrace_eventuallyEq Ω.boundaryPartition ψ two_ne_top one_le_two
    (s := 1 / 2) (by norm_num) (by norm_num) one_le_two (modNorm_toL2_lt_top (u : H^{1}(V)))
  rw [traceKer, Submodule.mem_iInf, ← (Filter.EventuallyEq.congr_left hψ),
    eventuallyEq_zero_iff_forall_chart Ω Ω.boundaryPartition]
  refine forall_congr' fun j => ?_
  rw [LinearMap.mem_ker, Lp.eq_zero_iff_ae_eq_zero]
  exact ⟨fun h => (Ω.chartTrace_ae_eq j u).symm.trans h,
    fun h => (Ω.chartTrace_ae_eq j u).trans h⟩

/-- **The boundary trace of `H^1(V)` functions is linear**: for every resolution of unity `ψ` and
`U, W ∈ H^1(V)`, `Tr_Γ(U - W) = Tr_Γ U - Tr_Γ W` almost everywhere on `Γ`: in each chart the
boundary traces are traces of the graph domain (`Rd.BoundedLipschitzDomain.boundaryTrace_graphMap`),
which are linear (`Rd.LipschitzGraph.trace_sub`). -/
theorem boundaryTrace_toL2_sub (ψ : Ω.BoundaryPartition) (U W : H^{1}(V)) :
    Ω.boundaryTrace ψ two_ne_top 2 (toL2 (U - W)) =ᶠ[Ω.aeBoundary]
      Ω.boundaryTrace ψ two_ne_top 2 (toL2 U) - Ω.boundaryTrace ψ two_ne_top 2 (toL2 W) := by
  refine Ω.eventually_aeBoundary_iff.2 fun j => ?_
  have hG := fun G : H^{1}(V) => Ω.boundaryTrace_graphMap ψ two_ne_top one_le_two (s := 1 / 2)
    (by norm_num) (by norm_num) one_le_two (modNorm_toL2_lt_top G) j
  have hI := fun G : H^{1}(V) => ((Ω.graph j).intrinsicNorm_lt_top_of_modNorm two_ne_top 2
    one_le_two (modNorm_toL2_lt_top G)).2
  have hsub := (Ω.graph j).trace_sub two_ne_top 2 (s := 1 / 2) (by norm_num) one_le_two (hI U)
    (hI W)
  filter_upwards [hG (U - W), hG U, hG W, Lp.coeFn_sub ((Ω.graph j).trace two_ne_top 2 (toL2 U))
    ((Ω.graph j).trace two_ne_top 2 (toL2 W))] with x' h1 h2 h3 h4 hj
  rw [Pi.sub_apply, h1 hj, h2 hj, h3 hj, map_sub, hsub, h4, Pi.sub_apply]

/-! ### The trace space `H^{1/2}(Γ)` -/

/-- **The trace space `H^{1/2}(Γ)`** of a bounded Lipschitz domain, as a Hilbert space, defined
as the orthogonal complement of the trace kernel in `H^1(Ω)`. By the trace theorem of `H^1(Ω)`,
the boundary traces of its elements are the functions of `B^{1/2}_{2,2}(Γ)`, up to null sets of
`Γ` (`Rd.BoundedLipschitzDomain.memBoundaryBesov_extend`,
`Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov`,
`Rd.BoundedLipschitzDomain.boundaryTrace_extend_eventuallyEq_iff`), with equivalent norms
(`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`). -/
abbrev TraceSpace := ↥(Ω.traceKer)ᗮ

/-- **The trace** `γ : H^1(Ω) → H^{1/2}(Γ)`, the orthogonal projection onto the trace space. Two
elements of `H^1(Ω)` have the same trace iff their boundary traces agree almost everywhere on `Γ`
(`Rd.BoundedLipschitzDomain.trace_eq_iff`). -/
noncomputable def trace : Ω.SobolevOne →L[ℂ] Ω.TraceSpace :=
  (Ω.traceKer)ᗮ.orthogonalProjectionOnto

/-- **The extension** `H^{1/2}(Γ) → H^1(Ω)`, the inclusion of the trace space: a right inverse of
the trace (`Rd.BoundedLipschitzDomain.trace_extend`) and an isometry
(`Rd.BoundedLipschitzDomain.norm_extend_apply`). -/
noncomputable def extend : Ω.TraceSpace →L[ℂ] Ω.SobolevOne :=
  (Ω.traceKer)ᗮ.subtypeL

/-- **The extension is a right inverse of the trace**: `γ (E t) = t`. -/
@[simp]
theorem trace_extend (t : Ω.TraceSpace) : Ω.trace (Ω.extend t) = t :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self t

/-- The trace has norm at most `1`: `‖γ u‖ ≤ ‖u‖`. -/
theorem norm_trace_apply_le (u : Ω.SobolevOne) : ‖Ω.trace u‖ ≤ ‖u‖ :=
  Submodule.norm_orthogonalProjectionOnto_apply_le _ u

/-- The extension is an isometry: `‖E t‖ = ‖t‖`. -/
theorem norm_extend_apply (t : Ω.TraceSpace) : ‖Ω.extend t‖ = ‖t‖ :=
  rfl

/-- `γ u = 0` iff `u` lies in the trace kernel (Mathlib's
`Submodule.orthogonalProjectionOnto_eq_zero_iff`, `Submodule.orthogonal_orthogonal`). -/
theorem trace_eq_zero_iff (u : Ω.SobolevOne) : Ω.trace u = 0 ↔ u ∈ Ω.traceKer := by
  rw [trace, Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal]

/-- **The kernel of the trace is the trace kernel**: the kernel of the orthogonal projection onto
`Kᗮ` is `Kᗮᗮ = K` (Mathlib's `Submodule.ker_orthogonalProjectionOnto`,
`Submodule.orthogonal_orthogonal`). -/
theorem ker_trace : (Ω.trace).ker = Ω.traceKer := by
  rw [trace, Submodule.ker_orthogonalProjectionOnto, Submodule.orthogonal_orthogonal]

/-- `u` and the extension of its trace differ by an element of the trace kernel. -/
theorem sub_extend_trace_mem (u : Ω.SobolevOne) : u - Ω.extend (Ω.trace u) ∈ Ω.traceKer := by
  have h := Submodule.sub_starProjection_mem_orthogonal (K := (Ω.traceKer)ᗮ) u
  rwa [Submodule.orthogonal_orthogonal] at h

/-- **`H^{1/2}(Γ)` as a quotient**: `H^1(Ω) ⧸ ker γ` is isometrically isomorphic to the trace
space, by the definition of the trace space as an orthogonal complement (Mathlib's
`Submodule.quotientEquivOrthogonal`); the class of `u` corresponds to `γ u`
(`Rd.BoundedLipschitzDomain.quotientEquivTraceSpace_mk`). -/
noncomputable def quotientEquivTraceSpace : (Ω.SobolevOne ⧸ Ω.traceKer) ≃ₗᵢ[ℂ] Ω.TraceSpace :=
  Submodule.quotientEquivOrthogonal _

/-- The class of `u` corresponds to its trace. -/
theorem quotientEquivTraceSpace_mk (u : Ω.SobolevOne) :
    Ω.quotientEquivTraceSpace (Submodule.Quotient.mk u) = Ω.trace u := by
  have h : (Submodule.Quotient.mk u : Ω.SobolevOne ⧸ Ω.traceKer) =
      Submodule.Quotient.mk (Ω.extend (Ω.trace u)) :=
    (Submodule.Quotient.eq _).2 (Ω.sub_extend_trace_mem u)
  rw [quotientEquivTraceSpace, h]
  exact Submodule.quotientEquivOrthogonal_mk _ _ (Ω.trace u).2

/-! ### The functions of `H^{1/2}(Γ)` -/

/-- **Equal traces are equal boundary traces**: for every resolution of unity `ψ`, `γ u = γ u'`
iff `Tr_Γ u = Tr_Γ u'` almost everywhere on `Γ` (`Rd.BoundedLipschitzDomain.mem_traceKer_iff` for
`u - u'`, `Rd.BoundedLipschitzDomain.boundaryTrace_toL2_sub`). -/
theorem trace_eq_iff (ψ : Ω.BoundaryPartition) (u u' : Ω.SobolevOne) :
    Ω.trace u = Ω.trace u' ↔ Ω.boundaryTrace ψ two_ne_top 2 (toL2 (u : H^{1}(V))) =ᶠ[Ω.aeBoundary]
      Ω.boundaryTrace ψ two_ne_top 2 (toL2 (u' : H^{1}(V))) := by
  rw [← sub_eq_zero, ← map_sub, trace_eq_zero_iff, mem_traceKer_iff Ω ψ, Submodule.coe_sub]
  exact ⟨fun h => Filter.eventuallyEq_iff_sub.2 ((Ω.boundaryTrace_toL2_sub ψ _ _).symm.trans h),
    fun h => (Ω.boundaryTrace_toL2_sub ψ _ _).trans (Filter.eventuallyEq_iff_sub.1 h)⟩

/-- **The extension of the trace has the same boundary trace**: `Tr_Γ (E γ u) = Tr_Γ u` almost
everywhere on `Γ`, for every resolution of unity. -/
theorem boundaryTrace_extend_trace (ψ : Ω.BoundaryPartition) (u : Ω.SobolevOne) :
    Ω.boundaryTrace ψ two_ne_top 2 (toL2 ((Ω.extend (Ω.trace u) : Ω.SobolevOne) : H^{1}(V)))
      =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ two_ne_top 2 (toL2 (u : H^{1}(V))) :=
  (Ω.trace_eq_iff ψ _ _).1 (Ω.trace_extend _)

/-- **Elements of the trace space are determined by their boundary traces**: `Tr_Γ (E t)` and
`Tr_Γ (E t')` agree almost everywhere on `Γ` iff `t = t'`. -/
theorem boundaryTrace_extend_eventuallyEq_iff (ψ : Ω.BoundaryPartition) (t t' : Ω.TraceSpace) :
    Ω.boundaryTrace ψ two_ne_top 2 (toL2 ((Ω.extend t : Ω.SobolevOne) : H^{1}(V)))
      =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ two_ne_top 2
        (toL2 ((Ω.extend t' : Ω.SobolevOne) : H^{1}(V))) ↔ t = t' := by
  rw [← Ω.trace_eq_iff ψ, trace_extend, trace_extend]

/-- **The boundary trace of `H^1(V)` functions lies in `B^{1/2}_{2,2}(Γ)`**: for every resolution of
unity `ψ` and `U ∈ H^1(V)` (`Rd.BoundedLipschitzDomain.memBoundaryBesov_boundaryTrace` at
`s = 1/2`, `p = q = 2`, `L = 2`). -/
theorem memBoundaryBesov_toL2 (ψ : Ω.BoundaryPartition) (U : H^{1}(V)) :
    Ω.MemBoundaryBesov 2 ψ (1 / 2) 2 (Ω.boundaryTrace ψ two_ne_top 2 (toL2 U)) :=
  Ω.memBoundaryBesov_boundaryTrace ψ two_ne_top one_le_two (by norm_num) (by norm_num)
    (by norm_num) one_le_two (modNorm_toL2_lt_top U)

/-- **The boundary traces of the trace space lie in `B^{1/2}_{2,2}(Γ)`**: for every resolution of
unity `ψ` and `t ∈ H^{1/2}(Γ)`, `Tr_Γ (E t) ∈ B^{1/2}_{2,2}(Γ)`. -/
theorem memBoundaryBesov_extend (ψ : Ω.BoundaryPartition) (t : Ω.TraceSpace) :
    Ω.MemBoundaryBesov 2 ψ (1 / 2) 2
      (Ω.boundaryTrace ψ two_ne_top 2 (toL2 ((Ω.extend t : Ω.SobolevOne) : H^{1}(V)))) :=
  Ω.memBoundaryBesov_toL2 ψ _

/-- **Every function of `B^{1/2}_{2,2}(Γ)` is the boundary trace of an element of the trace
space**: for every resolution of unity `ψ` and `g ∈ B^{1/2}_{2,2}(Γ)` there is `t ∈ H^{1/2}(Γ)`
with `Tr_Γ (E t) = g` almost everywhere on `Γ`. The trace theorem of `H^1(Ω)`
(`Rd.BoundedLipschitzDomain.exists_memSobolevOn_of_memBoundaryBesov`) gives `f ∈ H^1(Ω)` with
boundary trace `g`, `f` is the restriction of some `u` in the Hilbert space `H^1(Ω)`
(`Rd.BoundedLipschitzDomain.memSobolevOn_iff_exists_restrictL2`), and `t = γ u`. -/
theorem exists_traceSpace_of_memBoundaryBesov (ψ : Ω.BoundaryPartition) {g : V → ℂ}
    (hg : Ω.MemBoundaryBesov 2 ψ (1 / 2) 2 g) :
    ∃ t : Ω.TraceSpace, Ω.boundaryTrace ψ two_ne_top 2
      (toL2 ((Ω.extend t : Ω.SobolevOne) : H^{1}(V))) =ᶠ[Ω.aeBoundary] g := by
  obtain ⟨f, hf, hfg⟩ := Ω.exists_memSobolevOn_of_memBoundaryBesov ψ hg
  obtain ⟨u, hu⟩ := (Ω.memSobolevOn_iff_exists_restrictL2 f).1 hf
  refine ⟨Ω.trace u, (Ω.boundaryTrace_extend_trace ψ u).trans ?_⟩
  exact (Ω.isBoundaryTrace_iff_forall_memSobolev ψ f g).1 hfg _ (memSobolev_toL2 _)
    ((restrictL2_eq_iff_ae_eq u f).1 hu)

/-! ### `H^{-1/2}(Γ)` -/

/-- **The space `H^{-1/2}(Γ)`**: the bounded linear functionals on the trace space `H^{1/2}(Γ)`.
Normal traces of vector fields on `Ω` pair with `H^{1/2}(Γ)` through this space. -/
abbrev DualTraceSpace := StrongDual ℂ Ω.TraceSpace

/-- **Riesz for `H^{-1/2}(Γ)`**: the conjugate-linear isometric isomorphism of `H^{-1/2}(Γ)` onto
`H^{1/2}(Γ)` that represents a functional by an element (Mathlib's `InnerProductSpace.toDual`):
`ℓ t = ⟪dualTraceEquiv Ω ℓ, t⟫` (`Rd.BoundedLipschitzDomain.dualTraceEquiv_apply`), and this
element is the only one with this property
(`Rd.BoundedLipschitzDomain.eq_dualTraceEquiv_of_forall`). -/
noncomputable def dualTraceEquiv : Ω.DualTraceSpace ≃ₗᵢ⋆[ℂ] Ω.TraceSpace :=
  (InnerProductSpace.toDual ℂ Ω.TraceSpace).symm

/-- Every functional of `H^{-1/2}(Γ)` is the inner product with its representing element. -/
theorem dualTraceEquiv_apply (ℓ : Ω.DualTraceSpace) (t : Ω.TraceSpace) :
    ℓ t = ⟪Ω.dualTraceEquiv ℓ, t⟫_ℂ := by
  rw [dualTraceEquiv, InnerProductSpace.toDual_symm_apply]

/-- **The representing element is unique**: if `ℓ t = ⟪t₀, t⟫` for every `t ∈ H^{1/2}(Γ)`, then
`t₀ = dualTraceEquiv Ω ℓ` (Mathlib's `ext_inner_right`). -/
theorem eq_dualTraceEquiv_of_forall (ℓ : Ω.DualTraceSpace) {t₀ : Ω.TraceSpace}
    (h : ∀ t, ℓ t = ⟪t₀, t⟫_ℂ) : t₀ = Ω.dualTraceEquiv ℓ :=
  ext_inner_right ℂ fun t => by rw [← h, dualTraceEquiv_apply]

/-- **The adjoint of the trace is the extension**: `γ* = E`, the adjoint of an orthogonal
projection onto a closed subspace is its inclusion (Mathlib's
`Submodule.adjoint_orthogonalProjectionOnto`). -/
theorem adjoint_trace : ContinuousLinearMap.adjoint Ω.trace = Ω.extend :=
  Submodule.adjoint_orthogonalProjectionOnto _

end BoundedLipschitzDomain

end Rd
