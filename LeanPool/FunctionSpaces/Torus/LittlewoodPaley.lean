/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.EuclideanConvolutionIdentities
public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Blocks

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Littlewood–Paley blocks on the torus

For `f ∈ L_p(𝕋^d)`, `1 ≤ p < ∞`, the **Littlewood–Paley blocks** are `Δ_j f = ψ_j ⋆ f`
(`Torus.lpBlock`), with the kernels `ψ_j` of `Rd.psi` on `ℝ^d` acting by `Torus.econvLp`. They
are bounded uniformly, `‖Δ_j f‖_p ≤ 2 ‖Φ‖_1 ‖f‖_p` (`Torus.enorm_lpBlock_le`), their partial
sums are `Φ_J ⋆ f` (`Torus.sum_lpBlock`), and these converge to `f`
(`Torus.tendsto_sum_lpBlock`). The **Littlewood–Paley quasi-norm** is
`‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}` (`Torus.littlewoodPaleyNorm`).

**Besov spaces on the torus by Littlewood–Paley blocks**
(`Torus.memBesov_iff_littlewoodPaleyNorm_lt_top`): for `s > 0`, `1 ≤ q ≤ ∞` and every
`1 ≤ p < ∞`, `f ∈ B^s_{p,q}(𝕋^d)` iff its Littlewood–Paley quasi-norm is finite, with explicit
constants in both directions (`Torus.approxNormDyadic_trigScheme_le`,
`Torus.littlewoodPaleyNorm_le_approxNormDyadic_trigScheme`). Both come from the Fourier
multipliers at the lattice points:

* the blocks are trigonometric polynomials, `Δ_j f ∈ 𝒯_{2^(j+1)}`, since `𝓕ψ_j(m) = 0` for
  `|m| ≥ 2^(j+1)` (`Torus.lpBlock_mem_trigPolyLp`);
* high blocks of trigonometric polynomials vanish, `Δ_j a = 0` for `a ∈ 𝒯_{2^i}` and
  `j ≥ i + #d + 1`, since `|m| ≤ #d deg m < 2^(i + #d)` (`Torus.lpBlock_eq_zero_of_mem`); hence
  `‖Δ_j f‖_p ≤ 2 ‖Φ‖_1 E_{2^i}(f)_p` (`Torus.enorm_lpBlock_le_approxError`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus Set Filter Topology
open scoped ENNReal FourierTransform TorusHaar

open ENNReal (lqNorm dyadicWeight)

namespace Torus

variable {d : Type*} [Fintype d] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The blocks -/

/-- The **Littlewood–Paley block** `Δ_j f = ψ_j ⋆ f` of `f ∈ L_p(𝕋^d)`, with the kernel `ψ_j` of
`Rd.psi` on `ℝ^d`. -/
noncomputable def lpBlock (hp : p ≠ ∞) (j : ℕ) :
    Lp ℂ p (volume : Measure (UnitAddTorus d)) →L[ℂ] Lp ℂ p (volume : Measure (UnitAddTorus d)) :=
  econvLp hp (Rd.integrable_psi (V := EuclideanSpace ℝ d) j)

/-- **The blocks are bounded uniformly**: `‖Δ_j f‖_p ≤ 2 ‖Φ‖_1 ‖f‖_p`. -/
theorem enorm_lpBlock_le (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ‖lpBlock hp j f‖ₑ ≤ 2 * eLpNorm (Rd.lpKernel (V := EuclideanSpace ℝ d)) 1 volume * ‖f‖ₑ := by
  refine (enorm_econvLp_le hp _ f).trans ?_
  rw [← eLpNorm_one_eq_lintegral_eNorm (Rd.integrable_psi j).1]
  gcongr
  exact Rd.eLpNorm_psi_one_le j

/-- `Δ_{j+1} f = Φ_{j+1} ⋆ f - Φ_j ⋆ f`. -/
theorem lpBlock_succ (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    lpBlock hp (j + 1) f =
      econvLp hp (Rd.integrable_Phi (V := EuclideanSpace ℝ d) (j + 1)) f -
        econvLp hp (Rd.integrable_Phi (V := EuclideanSpace ℝ d) j) f :=
  econvLp_sub_kernel hp (Rd.integrable_Phi (j + 1)) (Rd.integrable_Phi j) f

/-- **The blocks telescope**: `∑_{j ≤ J} Δ_j f = Φ_J ⋆ f`. -/
theorem sum_lpBlock (hp : p ≠ ∞) (J : ℕ) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∑ j ∈ Finset.range (J + 1), lpBlock hp j f =
      econvLp hp (Rd.integrable_Phi (V := EuclideanSpace ℝ d) J) f := by
  induction J with
  | zero =>
    rw [Finset.sum_range_one]
    rfl
  | succ J ih => rw [Finset.sum_range_succ, ih, lpBlock_succ, add_sub_cancel]

/-- **Reconstruction**: the partial sums of the blocks converge to `f` in `L_p(𝕋^d)`, since
`Φ_J ⋆ f → f` (`Torus.tendsto_econvLp_Phi`). -/
theorem tendsto_sum_lpBlock (hp : p ≠ ∞) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    Tendsto (fun J => ∑ j ∈ Finset.range J, lpBlock hp j f) atTop (𝓝 f) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  simpa only [sum_lpBlock] using tendsto_econvLp_Phi hp f

/-! ### Blocks and trigonometric polynomials -/

/-- **The blocks are trigonometric polynomials**: `Δ_j f` has degree `< 2^(j+1)`, since
`𝓕ψ_j(m) ≠ 0` forces `deg m ≤ |m| < 2^(j+1)`. -/
theorem lpBlock_mem_trigPolyLp (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    lpBlock hp j f ∈ trigPolyLp p (2 ^ (j + 1)) := by
  refine econvLp_mem_trigPolyLp hp _ (fun m hm => ?_) f
  by_contra h
  have h1 := Rd.norm_lt_of_fourier_psi_ne_zero h
  have h2 := deg_le_norm_latticeVec m
  have h3 : ((2 : ℝ) ^ (j + 1)) ≤ deg m := by exact_mod_cast hm
  linarith

/-- **High blocks of trigonometric polynomials vanish**: `Δ_j a = 0` for a trigonometric
polynomial `a` of degree `< 2^i` and `j ≥ i + #d + 1`, since `𝓕ψ_j = 0` on the ball of radius
`2^(j-1)` and `|m| ≤ #d deg m < 2^(i + #d)`. -/
theorem lpBlock_eq_zero_of_mem (hp : p ≠ ∞) {i j : ℕ} (hij : i + Fintype.card d + 1 ≤ j)
    {a : Lp ℂ p (volume : Measure (UnitAddTorus d))} (ha : a ∈ trigPolyLp p (2 ^ i)) :
    lpBlock hp j a = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  refine econvLp_eq_zero_of_mem hp _ (fun m hm => Rd.fourier_psi_succ_eq_zero ?_) ha
  have hcard : (Fintype.card d : ℝ) ≤ 2 ^ Fintype.card d := by
    exact_mod_cast (Fintype.card d).lt_two_pow_self.le
  have hdeg : (deg m : ℝ) ≤ 2 ^ i := by exact_mod_cast hm.le
  calc ‖latticeVec m‖ ≤ Fintype.card d * deg m := norm_latticeVec_le m
    _ ≤ 2 ^ Fintype.card d * 2 ^ i := by gcongr
    _ = 2 ^ (i + Fintype.card d) := by rw [pow_add, mul_comm]
    _ ≤ 2 ^ k := pow_le_pow_right₀ one_le_two (by omega)

/-- **Blocks see only the error of trigonometric approximation**: for `j ≥ i + #d + 1`,
`‖Δ_j f‖_p ≤ 2 ‖Φ‖_1 E_{2^i}(f)_p`. -/
theorem enorm_lpBlock_le_approxError (hp : p ≠ ∞) {i j : ℕ} (hij : i + Fintype.card d + 1 ≤ j)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ‖lpBlock hp j f‖ₑ ≤ 2 * eLpNorm (Rd.lpKernel (V := EuclideanSpace ℝ d)) 1 volume *
      ((trigScheme d).toLp volume p).approxError f (2 ^ i) := by
  refine ApproximationScheme.le_mul_approxError_of_forall_mem
    (ENNReal.mul_ne_top (by norm_num) Rd.eLpNorm_lpKernel_ne_top) fun a ha => ?_
  have h0 : lpBlock hp j a = 0 := lpBlock_eq_zero_of_mem hp hij (mem_toLp_trigScheme_iff.1 ha)
  rw [show lpBlock hp j f = lpBlock hp j (f - a) by rw [map_sub, h0, sub_zero]]
  exact enorm_lpBlock_le hp j (f - a)

/-! ### The Littlewood–Paley quasi-norm -/

/-- The **Littlewood–Paley quasi-norm** `‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}` on `L_p(𝕋^d)`. -/
noncomputable def littlewoodPaleyNorm (hp : p ≠ ∞) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) : ℝ≥0∞ :=
  lqNorm q (fun j => dyadicWeight s j * ‖lpBlock hp j f‖ₑ)

/-- **A finite Littlewood–Paley quasi-norm gives an absolutely convergent decomposition**: for
`s > 0`, `‖Δ_j f‖_p ≤ 2^(-js) ‖f‖_{LP}`, so `f = ∑_j Δ_j f` converges absolutely in
`L_p(𝕋^d)`. -/
theorem hasSum_lpBlock (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : littlewoodPaleyNorm hp s q f < ∞) :
    HasSum (fun j => lpBlock hp j f) f :=
  HasSum.of_tendsto_of_lqNorm_dyadicWeight_lt_top hs hq (tendsto_sum_lpBlock hp f) hf

/-! ### Trigonometric approximation and Littlewood–Paley blocks -/

/-- **The approximation norm is controlled by the Littlewood–Paley quasi-norm**: for `s > 0`,
`‖f‖^dyadic ≤ 2 · 2^s (1 - 2^(-s))⁻¹ ‖(2^(js) ‖Δ_j f‖_p)_j‖_q` for every `f ∈ L_p(𝕋^d)`, with
the scheme of trigonometric polynomials. The blocks moved up by one level,
`0, Δ_0 f, Δ_1 f, …` (`ApproximationScheme.shiftSeq 1`), lie in `𝒯_{2^k}` and form a block
decomposition (`ApproximationScheme.approxNormDyadic_le_of_hasSum`). -/
theorem approxNormDyadic_trigScheme_le (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ((trigScheme d).toLp volume p).approxNormDyadic s q f ≤
      2 * dyadicWeight s 1 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * littlewoodPaleyNorm hp s q f := by
  rcases eq_or_ne (littlewoodPaleyNorm hp s q f) ∞ with h | h
  · rw [h, ENNReal.mul_top (mul_ne_zero (mul_ne_zero two_ne_zero
      (ENNReal.dyadicWeight_pos s 1).ne')
      (zero_lt_one.trans_le (ENNReal.one_le_one_sub_two_rpow_neg_inv s)).ne')]
    exact le_top
  set g := ApproximationScheme.shiftSeq 1 fun j => lpBlock hp j f
  calc ((trigScheme d).toLp volume p).approxNormDyadic s q f
      ≤ 2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * lqNorm q (fun k => dyadicWeight s k * ‖g k‖ₑ) :=
        ApproximationScheme.approxNormDyadic_le_of_hasSum hq
          (ApproximationScheme.shiftSeq_mem fun j =>
            mem_toLp_trigScheme_iff.2 (lpBlock_mem_trigPolyLp hp j f))
          (ApproximationScheme.hasSum_shiftSeq (hasSum_lpBlock hp hs hq h.lt_top))
    _ ≤ 2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ *
          lqNorm q (fun j => dyadicWeight s 1 * (dyadicWeight s j * ‖lpBlock hp j f‖ₑ)) := by
        gcongr
        refine (ApproximationScheme.lqNorm_shiftSeq_le 1 _ s q).trans_eq ?_
        congr 1; funext j; rw [ENNReal.dyadicWeight_add_nat]; ring
    _ = 2 * dyadicWeight s 1 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * littlewoodPaleyNorm hp s q f := by
        rw [ENNReal.lqNorm_const_mul, littlewoodPaleyNorm]; ring

/-- **The Littlewood–Paley quasi-norm is controlled by the approximation norm**: for `s ≥ 0`,
`‖(2^(js) ‖Δ_j f‖_p)_j‖_q ≤ 2 (#d + 1) 2^((#d + 1) s) ‖Φ‖_1 ‖f‖^dyadic` for every
`f ∈ L_p(𝕋^d)`, with the scheme of trigonometric polynomials. The first `#d + 1` blocks are
bounded by `‖f‖`, the block `Δ_{j + #d + 1} f` by `E_{2^j}(f)`. -/
theorem littlewoodPaleyNorm_le_approxNormDyadic_trigScheme (hp : p ≠ ∞) {s : ℝ} (hs : 0 ≤ s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    littlewoodPaleyNorm hp s q f ≤
      2 * ((Fintype.card d : ℝ≥0∞) + 1) * dyadicWeight s (Fintype.card d + 1) *
        eLpNorm (Rd.lpKernel (V := EuclideanSpace ℝ d)) 1 volume *
          ((trigScheme d).toLp volume p).approxNormDyadic s q f := by
  refine (ApproximationScheme.lqNorm_dyadicWeight_mul_enorm_le_approxNormDyadic
    (M := Fintype.card d + 1) hs hq (by omega) (fun j _ => enorm_lpBlock_le hp j f)
    fun n => enorm_lpBlock_le_approxError hp le_rfl f).trans_eq ?_
  push_cast
  ring

/-- **Besov spaces on the torus by Littlewood–Paley blocks**: for every `1 ≤ p < ∞`, `s > 0` and
`1 ≤ q ≤ ∞`, `f ∈ B^s_{p,q}(𝕋^d)` (the approximation space of the trigonometric polynomials in
`L_p`) iff `(2^(js) ‖ψ_j ⋆ f‖_p)_j ∈ ℓ_q`. -/
theorem memBesov_iff_littlewoodPaleyNorm_lt_top (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    (trigScheme d).MemBesov volume p s q f ↔ littlewoodPaleyNorm hp s q f < ∞ := by
  rw [FunctionScheme.MemBesov, ApproximationScheme.memApprox_iff_approxNormDyadic_lt_top hq hs.le]
  have hK : eLpNorm (Rd.lpKernel (V := EuclideanSpace ℝ d)) 1 volume < ∞ :=
    Rd.eLpNorm_lpKernel_lt_top
  constructor
  · intro h
    refine (littlewoodPaleyNorm_le_approxNormDyadic_trigScheme hp hs.le hq f).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top
        (by norm_num) ?_) (ENNReal.dyadicWeight_lt_top s _)) hK) h)
    exact ENNReal.add_lt_top.2 ⟨ENNReal.natCast_lt_top _, ENNReal.one_lt_top⟩
  · intro h
    exact (approxNormDyadic_trigScheme_le hp hs hq f).trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (ENNReal.dyadicWeight_lt_top s 1))
        (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs).lt_top) h)

end Torus
