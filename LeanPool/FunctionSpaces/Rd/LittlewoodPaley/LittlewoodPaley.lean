/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Approximation.BandLimited
public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Blocks

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Littlewood–Paley decomposition and band-limited approximation

For `f ∈ L_p(V)`, `1 ≤ p < ∞`, the **Littlewood–Paley blocks** are `Δ_j f = ψ_j ⋆ f`
(`Rd.lpBlock`), with `ψ_0 = Φ_0` and `ψ_j = Φ_j - Φ_{j-1}` (`Rd.psi`). They are bounded uniformly,
`‖Δ_j f‖_p ≤ 2 ‖Φ‖_1 ‖f‖_p` (`Rd.enorm_lpBlock_le`), their partial sums are `Φ_J ⋆ f`
(`Rd.sum_lpBlock`), and these converge to `f` in `L_p` (`Rd.tendsto_sum_lpBlock`, an approximate
identity). The **Littlewood–Paley quasi-norm** is `‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}`
(`Rd.littlewoodPaleyNorm`).

**Band-limited approximation and Littlewood–Paley blocks** (`Rd.memApprox_bandScheme_iff`): for
`s > 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q(L_p, (E_k))` iff its Littlewood–Paley quasi-norm is finite,
and the two quasi-norms are equivalent (`Rd.approxNormDyadic_bandScheme_le`,
`Rd.littlewoodPaleyNorm_le_approxNormDyadic`). Both directions come from the kernel identities:

* the blocks are band-limited, `Δ_j f ∈ E_j`, since `Θ_j ⋆ ψ_j = ψ_j`
  (`Rd.lpBlock_mem_bandSpace`); a finite quasi-norm makes `f = ∑ Δ_j f` absolutely convergent
  (`Rd.hasSum_lpBlock`), a block decomposition in the sense of
  `ApproximationScheme.blockDecompNorm`;
* high blocks of band-limited functions vanish, `Δ_j g = 0` for `g ∈ E_i` and `j ≥ i + 3`, since
  `ψ_j ⋆ Θ_i = 0` (`Rd.lpBlock_eq_zero_of_mem`); hence `Δ_j f = Δ_j (f - g)` and
  `‖Δ_j f‖_p ≤ 2 ‖Φ‖_1 E(f, E_i)_p` (`Rd.enorm_lpBlock_le_approxError`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Rd

open ENNReal (lqNorm dyadicWeight)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The blocks -/

/-- The **Littlewood–Paley block** `Δ_j f = ψ_j ⋆ f` of `f ∈ L_p`. -/
noncomputable def lpBlock (hp : p ≠ ∞) (j : ℕ) :
    Lp ℂ p (volume : Measure V) →L[ℂ] Lp ℂ p (volume : Measure V) :=
  convLp hp (integrable_psi j)

/-- **The blocks are bounded uniformly**: `‖Δ_j f‖_p ≤ 2 ‖Φ‖_1 ‖f‖_p`. -/
theorem enorm_lpBlock_le (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ‖lpBlock hp j f‖ₑ ≤ 2 * eLpNorm (lpKernel (V := V)) 1 volume * ‖f‖ₑ :=
  (enorm_convLp_le hp (integrable_psi j) f).trans (by gcongr; exact eLpNorm_psi_one_le j)

/-- `Δ_{j+1} f = Φ_{j+1} ⋆ f - Φ_j ⋆ f`. -/
theorem lpBlock_succ (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    lpBlock hp (j + 1) f =
      convLp hp (integrable_Phi (j + 1)) f - convLp hp (integrable_Phi j) f :=
  convLp_sub_kernel hp (integrable_Phi (j + 1)) (integrable_Phi j) f

/-- **The blocks telescope**: `∑_{j ≤ J} Δ_j f = Φ_J ⋆ f`. -/
theorem sum_lpBlock (hp : p ≠ ∞) (J : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ∑ j ∈ Finset.range (J + 1), lpBlock hp j f = convLp hp (integrable_Phi J) f := by
  induction J with
  | zero =>
    rw [Finset.sum_range_one]
    rfl
  | succ J ih => rw [Finset.sum_range_succ, ih, lpBlock_succ, add_sub_cancel]

/-- **Reconstruction**: the partial sums of the blocks converge to `f` in `L_p`, since
`Φ_J ⋆ f → f` (`Rd.tendsto_convLp_dilate` with `∫ Φ = 1`). -/
theorem tendsto_sum_lpBlock (hp : p ≠ ∞) (f : Lp ℂ p (volume : Measure V)) :
    Tendsto (fun J => ∑ j ∈ Finset.range J, lpBlock hp j f) atTop (𝓝 f) := by
  have h : Tendsto (fun J => convLp hp (integrable_Phi (V := V) J) f) atTop (𝓝 f) :=
    tendsto_convLp_dilate hp integrable_lpKernel integral_lpKernel
      (c := fun J : ℕ => (2 : ℝ) ^ J) (fun J => pow_ne_zero J two_ne_zero)
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) f
  rw [← tendsto_add_atTop_iff_nat 1]
  simpa only [sum_lpBlock] using h

/-! ### Blocks and band-limited functions -/

/-- **The blocks are band-limited**: `Δ_j f ∈ E_j`, since `Θ_j ⋆ ψ_j = ψ_j`. -/
theorem lpBlock_mem_bandSpace (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    lpBlock hp j f ∈ bandSpace hp j := by
  rw [mem_bandSpace, lpBlock]
  exact convLp_convLp_of_eq hp _ _ _ (conv_Theta_psi j) f

/-- **High blocks of band-limited functions vanish**: `Δ_j g = 0` for `g ∈ E_i` and `j ≥ i + 3`,
since `ψ_j ⋆ Θ_i = 0`. -/
theorem lpBlock_eq_zero_of_mem (hp : p ≠ ∞) {i j : ℕ} (hij : i + 3 ≤ j)
    {g : Lp ℂ p (volume : Measure V)} (hg : g ∈ bandSpace hp i) : lpBlock hp j g = 0 := by
  rw [mem_bandSpace] at hg
  rw [lpBlock, ← hg, convLp_convLp_of_eq hp _ _ (integrable_zero _ _ _) (conv_psi_Theta hij) g]
  exact convLp_of_eq_zero hp _ rfl g

/-- **Blocks see only the error of band-limited approximation**: for `j ≥ i + 3`,
`‖Δ_j f‖_p ≤ 2 ‖Φ‖_1 E(f, E_i)_p`. -/
theorem enorm_lpBlock_le_approxError (hp : p ≠ ∞) {i j : ℕ} (hij : i + 3 ≤ j)
    (f : Lp ℂ p (volume : Measure V)) :
    ‖lpBlock hp j f‖ₑ ≤
      2 * eLpNorm (lpKernel (V := V)) 1 volume * (bandScheme hp).approxError f (2 ^ i) := by
  refine ApproximationScheme.le_mul_approxError_of_forall_mem
    (ENNReal.mul_ne_top (by norm_num) eLpNorm_lpKernel_ne_top) fun a ha => ?_
  have h0 : lpBlock hp j a = 0 := lpBlock_eq_zero_of_mem hp hij (mem_bandScheme_two_pow.1 ha)
  rw [show lpBlock hp j f = lpBlock hp j (f - a) by rw [map_sub, h0, sub_zero]]
  exact enorm_lpBlock_le hp j (f - a)

/-! ### The Littlewood–Paley quasi-norm -/

/-- The **Littlewood–Paley quasi-norm** `‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}`. -/
noncomputable def littlewoodPaleyNorm (hp : p ≠ ∞) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) : ℝ≥0∞ :=
  lqNorm q (fun j => dyadicWeight s j * ‖lpBlock hp j f‖ₑ)

/-- **A finite Littlewood–Paley quasi-norm gives an absolutely convergent decomposition**: for
`s > 0`, `‖Δ_j f‖_p ≤ 2^(-js) ‖f‖_{LP}`, so `f = ∑_j Δ_j f` converges absolutely in `L_p`. -/
theorem hasSum_lpBlock (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} (hf : littlewoodPaleyNorm hp s q f < ∞) :
    HasSum (fun j => lpBlock hp j f) f :=
  HasSum.of_tendsto_of_lqNorm_dyadicWeight_lt_top hs hq (tendsto_sum_lpBlock hp f) hf

/-! ### Band-limited approximation and Littlewood–Paley blocks -/

/-- **The approximation norm is controlled by the Littlewood–Paley quasi-norm**: for `s > 0`,
`‖f‖^dyadic ≤ 2 (1 - 2^(-s))⁻¹ ‖(2^(js) ‖Δ_j f‖_p)_j‖_q`, with the band-limited scheme. The
blocks form a block decomposition (`ApproximationScheme.approxNormDyadic_le_of_hasSum`). -/
theorem approxNormDyadic_bandScheme_le (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    (bandScheme hp).approxNormDyadic s q f ≤
      2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * littlewoodPaleyNorm hp s q f := by
  rcases eq_or_ne (littlewoodPaleyNorm hp s q f) ∞ with h | h
  · rw [h, ENNReal.mul_top (mul_ne_zero two_ne_zero
      (zero_lt_one.trans_le (ENNReal.one_le_one_sub_two_rpow_neg_inv s)).ne')]
    exact le_top
  · exact ApproximationScheme.approxNormDyadic_le_of_hasSum hq
      (fun j => mem_bandScheme_two_pow.2 (lpBlock_mem_bandSpace hp j f))
      (hasSum_lpBlock hp hs hq h.lt_top)

/-- **The Littlewood–Paley quasi-norm is controlled by the approximation norm**: for `s ≥ 0`,
`‖(2^(js) ‖Δ_j f‖_p)_j‖_q ≤ 8 · 2^(3s) ‖Φ‖_1 ‖f‖^dyadic`, with the band-limited scheme. The first
three blocks are bounded by `‖f‖`, the block `Δ_{j+3} f` by `E(f, E_j)`. -/
theorem littlewoodPaleyNorm_le_approxNormDyadic (hp : p ≠ ∞) {s : ℝ} (hs : 0 ≤ s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    littlewoodPaleyNorm hp s q f ≤
      8 * dyadicWeight s 3 * eLpNorm (lpKernel (V := V)) 1 volume *
        (bandScheme hp).approxNormDyadic s q f := by
  calc littlewoodPaleyNorm hp s q f
      ≤ ((3 : ℕ) : ℝ≥0∞) * dyadicWeight s 3 * (2 * eLpNorm (lpKernel (V := V)) 1 volume) *
          (bandScheme hp).approxNormDyadic s q f :=
        ApproximationScheme.lqNorm_dyadicWeight_mul_enorm_le_approxNormDyadic hs hq (by norm_num)
          (fun j _ => enorm_lpBlock_le hp j f) fun n => enorm_lpBlock_le_approxError hp le_rfl f
    _ = 6 * (dyadicWeight s 3 * eLpNorm (lpKernel (V := V)) 1 volume *
          (bandScheme hp).approxNormDyadic s q f) := by push_cast; ring
    _ ≤ 8 * (dyadicWeight s 3 * eLpNorm (lpKernel (V := V)) 1 volume *
          (bandScheme hp).approxNormDyadic s q f) := by gcongr; norm_num
    _ = _ := by ring

/-- **Band-limited approximation and Littlewood–Paley blocks**: for `s > 0` and `1 ≤ q ≤ ∞`,
`f ∈ A^s_q(L_p, (E_k))` iff `(2^(js) ‖Δ_j f‖_p)_j ∈ ℓ_q`. -/
theorem memApprox_bandScheme_iff (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} :
    (bandScheme hp).MemApprox s q f ↔ littlewoodPaleyNorm hp s q f < ∞ := by
  rw [ApproximationScheme.memApprox_iff_approxNormDyadic_lt_top hq hs.le]
  constructor
  · intro h
    refine (littlewoodPaleyNorm_le_approxNormDyadic hp hs.le hq f).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num)
        (ENNReal.dyadicWeight_lt_top s 3)) eLpNorm_lpKernel_lt_top) h)
  · intro h
    exact (approxNormDyadic_bandScheme_le hp hs hq f).trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by norm_num) (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs).lt_top) h)

end Rd
