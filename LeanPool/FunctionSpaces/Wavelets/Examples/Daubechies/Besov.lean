/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Moduli
public import LeanPool.FunctionSpaces.Rd.Differences.BesovDifferences
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Bernstein
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Jackson
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Wavelet

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov spaces by Daubechies coefficients

For a Daubechies mask of order `N ≥ 2` with scaling function `φ` (`Daubechies.scalingFun`),
wavelet `ψ` (`Daubechies.wavelet`) and `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, this file characterises the
Besov spaces `B^s_{p,q}(ℝ)` by the coefficients `⟨f, φ(· - k)⟩` and `⟨f, ψ_{j,k}⟩`, where
`ψ_{j,k}(x) = 2^(j/2) ψ(2^j x - k)` and `⟨f, g⟩ = ∫ f(x) conj g(x) dx`
(`Daubechies.coeffFun`). With the **coefficient quasi-norm**

`‖f‖_coef = ‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q}`

(`Daubechies.coeffNorm`), the main theorem (`Daubechies.besov_iff_coeff`) reads: if `φ` has a
Bernstein bound `ω_N(φ, t)_p ≤ K t^θ` for `0 < t ≤ 1` (`Daubechies.BernsteinBound`), then for
`0 < s < θ` and every `f ∈ L_p(ℝ)`

`‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞  ↔  ‖f‖_coef < ∞`.

* **Approximation and moduli.** Jackson's inequality `E_{2^k}(f)_p ≤ C_J ω_N(f, 2^(-k))_p`
  (`Daubechies.approxError_scheme_le`) and the inverse inequality
  `ω_N(a, 2^(-k))_p ≤ C_B 2^(-(k-j)θ) ‖a‖_p` for `a ∈ V_j` (`Daubechies.inverse_scheme`) make
  the modulus of smoothness compatible with the Daubechies scheme (`Daubechies.modulusData`), so
  the coincidence theorem `ApproximationScheme.ModulusData.memApprox_iff_modNorm_lt_top` gives
  `f ∈ A^s_q ↔ ‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` for `0 ≤ s < θ`
  (`Daubechies.memApprox_scheme_iff_modulus`).
* **Approximation and coefficients.** The projections `P_j` form a projection scheme with dense
  union (`Daubechies.projectionScheme`, `Daubechies.closure_iUnion_scheme`), so `f ∈ A^s_q` iff
  `‖P_0 f‖_p + ‖(2^(js) ‖P_{j+1} f - P_j f‖_p)_j‖_{ℓ_q} < ∞` for `s > 0`
  (`ApproximationScheme.ProjectionScheme.memApprox_iff_blockNorm_lt_top`). The blocks are the
  wavelet expansions of level `j` (`Daubechies.proj_succ_sub_proj`), and their norms are
  comparable with `2^(j(1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p}` (`Daubechies.enorm_block_equiv`);
  likewise `‖P_0 f‖_p` with `‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p}` (`Daubechies.enorm_proj_zero_equiv`).
  Hence `f ∈ A^s_q ↔ ‖f‖_coef < ∞` for `s > 0` (`Daubechies.memApprox_scheme_iff_coeff`).
* **Littlewood–Paley.** For `0 < s < min(θ, N)` the coefficient condition is also equivalent
  to the finiteness of the Littlewood–Paley quasi-norm `‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}`
  (`Daubechies.littlewoodPaleyNorm_lt_top_iff_coeff`, through
  `Rd.littlewoodPaleyNorm_lt_top_iff_modulus`).
* **The regularity of `φ`.** Let `T^n 1 ≤ C λ^n` be a growth bound for the transfer operator
  (`Daubechies.TransferGrowth`); then `λ ≥ 1` (`Daubechies.TransferGrowth.one_le_lam`). For
  `p ≤ 2` the characterisation holds for `0 < s < N - log₄ λ`
  (`Daubechies.besov_iff_coeff_of_le_two`); for `p ≥ 2` it holds for
  `0 < s < (2/p) s' + (1 - 2/p) a` with `s' < N - log₄ λ` and either `a < N - log₄ λ - 1/2`
  (`Daubechies.besov_iff_coeff_of_two_le`) or a Hölder exponent `a` of `φ`
  (`Daubechies.besov_iff_coeff_of_two_le_of_holder`).
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped ENNReal
open ENNReal (dyadicWeight)

namespace Daubechies

/-! ### Growth bounds for the transfer operator -/

/-- **The iterates of the transfer operator on `1` are at least `1`**: for `N ≥ 1`, every
`n ∈ ℕ` and every `ξ ∈ ℝ`, `(T^n 1)(ξ) ≥ 1`. By induction on `n`: since `P ≥ 1`
(`Daubechies.one_le_daubFun`), for `g ≥ 1` the first summand of
`(T g)(ξ) = P(ξ/2) g(ξ/2) + P((ξ + 1)/2) g((ξ + 1)/2)` is at least `1` and the second is
nonnegative. -/
theorem one_le_iterate_transfer_one {N : ℕ} (hN : 1 ≤ N) (n : ℕ) (ξ : ℝ) :
    1 ≤ (transfer N)^[n] (fun _ => 1) ξ := by
  induction n generalizing ξ with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h1 : 1 ≤ daubFun N (ξ / 2) * (transfer N)^[n] (fun _ => 1) (ξ / 2) :=
      one_le_mul_of_one_le_of_one_le (one_le_daubFun hN _) (ih _)
    have h2 : 0 ≤ daubFun N ((ξ + 1) / 2) * (transfer N)^[n] (fun _ => 1) ((ξ + 1) / 2) :=
      mul_nonneg (daubFun_nonneg N _) (iterate_transfer_one_nonneg N n _)
    exact le_add_of_le_of_nonneg h1 h2

/-- **The rate of a growth bound is at least `1`**: for `N ≥ 1`, every growth bound
`T^n 1 ≤ C λ^n` for the transfer operator (`Daubechies.TransferGrowth`) has `λ ≥ 1`. Otherwise
`C λ^n → 0`, while `(T^n 1)(0) ≥ 1` for every `n` (`Daubechies.one_le_iterate_transfer_one`). -/
theorem TransferGrowth.one_le_lam {N : ℕ} {lam C : ℝ} (hN : 1 ≤ N)
    (hg : TransferGrowth N lam C) : 1 ≤ lam := by
  by_contra h
  push Not at h
  have ht : Tendsto (fun n : ℕ => C * lam ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hg.1.le h).const_mul C
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds one_pos)).exists
  linarith [hg.2 n 0, one_le_iterate_transfer_one hN n 0]

/-- **The Sobolev exponent of a growth bound is at most `N`**: for `N ≥ 1` and every growth
bound `T^n 1 ≤ C λ^n` for the transfer operator, `N - log₄ λ ≤ N`, since `λ ≥ 1`
(`Daubechies.TransferGrowth.one_le_lam`). -/
theorem TransferGrowth.sub_logb_le {N : ℕ} {lam C : ℝ} (hN : 1 ≤ N)
    (hg : TransferGrowth N lam C) : (N : ℝ) - Real.logb 4 lam ≤ N :=
  sub_le_self _ (Real.logb_nonneg (by norm_num) (hg.one_le_lam hN))

variable {N : ℕ} (m : Mask N)

/-! ### The coefficient quasi-norm -/

/-- **The Daubechies coefficient quasi-norm** of `f : ℝ → ℂ`, for the exponents `p, q` and the
smoothness `s`:
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q}`, with the
coefficients `⟨f, g_{j,k}⟩ = ∫ f(x) conj g_{j,k}(x) dx` (`Daubechies.coeffFun`) of the scaling
function `φ` at level `0` and of the wavelet `ψ` at the levels `j ∈ ℕ`. Its finiteness describes
`B^s_{p,q}(ℝ)` (`Daubechies.besov_iff_coeff`). -/
noncomputable def coeffNorm (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) (f : ℝ → ℂ) : ℝ≥0∞ :=
  ENNReal.lqNorm p (fun k : ℤ => ‖coeffFun (scalingFun m) 0 f k‖ₑ) +
    ENNReal.lqNorm q (fun j => dyadicWeight (s + (1 / 2 - 1 / p.toReal)) j *
      ENNReal.lqNorm p (fun k : ℤ => ‖coeffFun (wavelet m) j f k‖ₑ))

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The modulus of smoothness and the Daubechies scheme -/

variable (p) in
/-- **The modulus of smoothness is compatible with the Daubechies scheme**: for `N ≥ 2`,
`1 ≤ p < ∞` and a Bernstein bound `ω_N(φ, t)_p ≤ K t^θ` for `0 < t ≤ 1`
(`Daubechies.BernsteinBound` with differences of order `N`), the modulus
`ω_N(f, 2^(-k))_p` (`Rd.lpModulus p N`) is compatible with the Daubechies scheme with inverse
order `θ` (`ApproximationScheme.ModulusData`). Jackson's inequality
`E_{2^k}(f)_p ≤ C_J ω_N(f, 2^(-k))_p` holds from level `0` on
(`Daubechies.approxError_scheme_le_jacksonConst_mul`), and the inverse inequality
`ω_N(a, 2^(-k))_p ≤ C_B 2^(-(k-j)θ) ‖a‖_p` for the approximants `a` of complexity `2^j` is
`Daubechies.inverse_scheme`. -/
noncomputable def modulusData (hN : 2 ≤ N) (hp : p ≠ ∞) {θ : ℝ} (hB : BernsteinBound m p θ N) :
    ApproximationScheme.ModulusData (scheme m p hN hp) θ where
  modulus := Rd.lpModulus p N
  add_le := Rd.lpModulus_add_le N
  C0 := 2 ^ N
  C0_ne_top := by simp
  le_enorm := Rd.lpModulus_le N
  jacksonStart := 0
  CJ := jacksonConst m p
  CJ_ne_top := jacksonConst_ne_top m hN p
  jackson f k _ := approxError_scheme_le_jacksonConst_mul m hN hp f k
  CB := (inverse_scheme m hN hp hB).choose
  CB_ne_top := (inverse_scheme m hN hp hB).choose_spec.1
  inverse := (inverse_scheme m hN hp hB).choose_spec.2

/-- **Approximation by the Daubechies scaling spaces and moduli of smoothness**: for `N ≥ 2`,
`1 ≤ p < ∞`, a Bernstein bound of order `θ` for `φ` with differences of order `N`,
`1 ≤ q ≤ ∞` and `0 ≤ s < θ`, an `f ∈ L_p(ℝ)` lies in the approximation space `A^s_q` of the
Daubechies scheme iff `‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. This is the coincidence
theorem `ApproximationScheme.ModulusData.memApprox_iff_modNorm_lt_top` for
`Daubechies.modulusData`. -/
theorem memApprox_scheme_iff_modulus (hN : 2 ≤ N) (hp : p ≠ ∞) {θ : ℝ}
    (hB : BernsteinBound m p θ N) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 ≤ s) (hsθ : s < θ)
    (f : Lp ℂ p (volume : Measure ℝ)) :
    (scheme m p hN hp).MemApprox s q f ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p N f k) < ∞ :=
  (modulusData m p hN hp hB).memApprox_iff_modNorm_lt_top hq hs hsθ f

/-! ### Approximation and coefficients -/

/-- **The projection of complexity `1` of the Daubechies projection scheme is `P_0`**: the
case `k = 0` of `Daubechies.projectionScheme_two_pow`. -/
theorem projectionScheme_one (hN : 2 ≤ N) (hp : p ≠ ∞) :
    (projectionScheme m p hN hp).P 1 = proj m p hN hp 0 := by
  simpa using projectionScheme_two_pow m hN hp 0

/-- **The dyadic blocks of the Daubechies projection scheme**: for every `f ∈ L_p` and level `j`,
the block `P(2^(j+1)) f - P(2^j) f` of the projection scheme is `P_{j+1} f - P_j f`, since the
projection of complexity `2^j` is `P_j` (`Daubechies.projectionScheme_two_pow`). -/
theorem projectionScheme_block (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure ℝ)) :
    (projectionScheme m p hN hp).block j f = proj m p hN hp (j + 1) f - proj m p hN hp j f := by
  rw [ApproximationScheme.ProjectionScheme.block, projectionScheme_two_pow,
    projectionScheme_two_pow]

/-- **Approximation by the Daubechies scaling spaces through coefficients**: for `N ≥ 2`,
`1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞`, an `f ∈ L_p(ℝ)` lies in the approximation space `A^s_q`
of the Daubechies scheme iff its coefficient quasi-norm
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q}`
(`Daubechies.coeffNorm`) is finite.

The projections form a projection scheme with dense union, so `f ∈ A^s_q` iff
`‖P_0 f‖_p + ‖(2^(js) ‖P_{j+1} f - P_j f‖_p)_j‖_{ℓ_q} < ∞`
(`ApproximationScheme.ProjectionScheme.memApprox_iff_blockNorm_lt_top`). The first summand
`‖P_0 f‖_p` and `‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p}` are both finite (`Daubechies.enorm_proj_zero_equiv`),
and
`2^(js) ‖P_{j+1} f - P_j f‖_p` is comparable with
`2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p}` uniformly in `j` (`Daubechies.enorm_block_equiv`),
so the two `ℓ_q` norms are finite together (`ENNReal.lqNorm_lt_top_iff_of_le_mul`). -/
theorem memApprox_scheme_iff_coeff (hN : 2 ≤ N) (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure ℝ)) :
    (scheme m p hN hp).MemApprox s q f ↔ coeffNorm m p s q f < ∞ := by
  obtain ⟨K₀, _, hK₀, _, hKM₀⟩ := enorm_proj_zero_equiv m hN hp
  obtain ⟨K, M, hK, hM, hKM⟩ := enorm_block_equiv m hN hp
  rw [(projectionScheme m p hN hp).memApprox_iff_blockNorm_lt_top
    (closure_iUnion_scheme m hN hp) hs hq, ApproximationScheme.ProjectionScheme.blockNorm,
    projectionScheme_one, coeffNorm]
  simp only [projectionScheme_block, ENNReal.add_lt_top]
  refine and_congr ⟨fun _ => (hKM₀ f).1.trans_lt (ENNReal.mul_lt_top hK₀.lt_top eNorm_lt_top),
    fun _ => eNorm_lt_top⟩
    (ENNReal.lqNorm_lt_top_iff_of_le_mul hK hM (fun j => ?_) fun j => ?_)
  · rw [ENNReal.dyadicWeight_add, mul_assoc, mul_left_comm M]
    exact mul_le_mul' le_rfl (hKM f j).2
  · rw [ENNReal.dyadicWeight_add, mul_assoc, mul_left_comm K]
    exact mul_le_mul' le_rfl (hKM f j).1

/-! ### Besov spaces by Daubechies coefficients -/

/-- **Besov spaces by Daubechies coefficients**: let `N ≥ 2`, `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, and let
`φ` have a Bernstein bound `ω_N(φ, t)_p ≤ K t^θ` for `0 < t ≤ 1` (`Daubechies.BernsteinBound`).
Then for `0 < s < θ` and every `f ∈ L_p(ℝ)`,
`‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
(`Daubechies.coeffNorm`). Both conditions describe the approximation space `A^s_q` of the
Daubechies scheme (`Daubechies.memApprox_scheme_iff_modulus`,
`Daubechies.memApprox_scheme_iff_coeff`). -/
theorem besov_iff_coeff (hN : 2 ≤ N) (hp : p ≠ ∞) {θ : ℝ} (hB : BernsteinBound m p θ N)
    {s : ℝ} (hs : 0 < s) (hsθ : s < θ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p N f k) < ∞ ↔
      coeffNorm m p s q f < ∞ :=
  (memApprox_scheme_iff_modulus m hN hp hB hq hs.le hsθ f).symm.trans
    (memApprox_scheme_iff_coeff m hN hp hs hq f)

/-- **Littlewood–Paley blocks and Daubechies coefficients**: let `N ≥ 2`, `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞`, and let `φ` have a Bernstein bound of order `θ` with differences of order `N`
(`Daubechies.BernsteinBound`). Then for `0 < s` with `s < θ` and `s < N`, and every
`f ∈ L_p(ℝ)`, the Littlewood–Paley quasi-norm `‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}` with the
Littlewood–Paley blocks `Δ_j f` (`Rd.littlewoodPaleyNorm`, `Rd.lpBlock`) is finite iff the
coefficient quasi-norm
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q}`
(`Daubechies.coeffNorm`) is: both are equivalent to the finiteness of the Besov quasi-norm by
differences of order `N` (`Rd.littlewoodPaleyNorm_lt_top_iff_modulus`,
`Daubechies.besov_iff_coeff`). -/
theorem littlewoodPaleyNorm_lt_top_iff_coeff (hN : 2 ≤ N) (hp : p ≠ ∞) {θ : ℝ}
    (hB : BernsteinBound m p θ N) {s : ℝ} (hs : 0 < s) (hsθ : s < θ) (hsN : s < N) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure ℝ)) :
    Rd.littlewoodPaleyNorm hp s q f < ∞ ↔ coeffNorm m p s q f < ∞ :=
  (Rd.littlewoodPaleyNorm_lt_top_iff_modulus hp hs hsN hq f).trans
    (besov_iff_coeff m hN hp hB hs hsθ hq f)

end Lp

/-! ### The regularity of the scaling function -/

/-- **Bernstein bounds above a given order, `p ≤ 2`**: let `N ≥ 2`, `p ≤ 2`, let `T^n 1 ≤ C λ^n`
be a growth bound for the transfer operator (`Daubechies.TransferGrowth`), and let
`0 ≤ s < N - log₄ λ`. Then `φ` has a Bernstein bound of some order `θ > s` in `L_p` with
differences of order `N`: the order `θ = (s + N - log₄ λ)/2` lies in `(s, N - log₄ λ)` and is at
most `N` (`Daubechies.TransferGrowth.sub_logb_le`), so `Daubechies.bernsteinBound_of_le_two`
applies. -/
theorem exists_bernsteinBound_of_le_two (hN : 2 ≤ N) {p : ℝ≥0∞} (hp2 : p ≤ 2) {lam C s : ℝ}
    (hg : TransferGrowth N lam C) (hs0 : 0 ≤ s) (hs : s < N - Real.logb 4 lam) :
    ∃ θ : ℝ, s < θ ∧ BernsteinBound m p θ N := by
  have hle := hg.sub_logb_le (by omega)
  exact ⟨(s + (N - Real.logb 4 lam)) / 2, by linarith,
    bernsteinBound_of_le_two m hN hp2 hg (by linarith) (by linarith) (by linarith)⟩

/-- **The interpolation weight**: for `2 ≤ p < ∞`, the weight `2/p` of the interpolated order
`(2/p) s + (1 - 2/p) a` lies in `[0, 1]`. -/
theorem two_div_toReal_mem_Icc {p : ℝ≥0∞} (hp : p ≠ ∞) (hp2 : 2 ≤ p) :
    2 / p.toReal ∈ Set.Icc (0 : ℝ) 1 := by
  have h2 : (2 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hp hp2
  exact ⟨by positivity, (div_le_one (by linarith)).2 h2⟩

/-- **Interpolated orders stay below a common bound**: for every weight `w ∈ [0, 1]` and all real
`s, a, b` with `s ≤ b` and `a ≤ b`, `w s + (1 - w) a ≤ b`, since a convex combination is at most
the larger of the two numbers (Mathlib's `Convex.combo_le_max`). -/
theorem mul_add_one_sub_mul_le {w s a b : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) (hs : s ≤ b)
    (ha : a ≤ b) : w * s + (1 - w) * a ≤ b :=
  (Convex.combo_le_max s a hw.1 (sub_nonneg.2 hw.2) (by ring)).trans (max_le hs ha)

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Besov spaces by Daubechies coefficients, `p ≤ 2`**: let `N ≥ 2`, `1 ≤ p ≤ 2`,
`1 ≤ q ≤ ∞`, and let `T^n 1 ≤ C λ^n` be a growth bound for the transfer operator
(`Daubechies.TransferGrowth`). Then for `0 < s < N - log₄ λ` and every `f ∈ L_p(ℝ)`,
`‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
(`Daubechies.besov_iff_coeff` with the Bernstein bound of
`Daubechies.exists_bernsteinBound_of_le_two`). -/
theorem besov_iff_coeff_of_le_two (hN : 2 ≤ N) (hp : p ≠ ∞) (hp2 : p ≤ 2) {lam C : ℝ}
    (hg : TransferGrowth N lam C) {s : ℝ} (hs : 0 < s) (hsl : s < N - Real.logb 4 lam)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p N f k) < ∞ ↔
      coeffNorm m p s q f < ∞ := by
  obtain ⟨θ, hsθ, hB⟩ := exists_bernsteinBound_of_le_two m hN hp2 hg hs.le hsl
  exact besov_iff_coeff m hN hp hB hs hsθ hq f

/-- **Littlewood–Paley blocks and Daubechies coefficients, `p ≤ 2`**: let `N ≥ 2`,
`1 ≤ p ≤ 2`, `1 ≤ q ≤ ∞`, and let `T^n 1 ≤ C λ^n` be a growth bound for the transfer operator.
Then for `0 < s < N - log₄ λ` and every `f ∈ L_p(ℝ)`, the Littlewood–Paley quasi-norm
`‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}` (`Rd.littlewoodPaleyNorm`) is finite iff the coefficient
quasi-norm `Daubechies.coeffNorm` is (`Daubechies.littlewoodPaleyNorm_lt_top_iff_coeff`; here
`s < N` since `λ ≥ 1`, `Daubechies.TransferGrowth.sub_logb_le`). -/
theorem littlewoodPaleyNorm_lt_top_iff_coeff_of_le_two (hN : 2 ≤ N) (hp : p ≠ ∞) (hp2 : p ≤ 2)
    {lam C : ℝ} (hg : TransferGrowth N lam C) {s : ℝ} (hs : 0 < s)
    (hsl : s < N - Real.logb 4 lam) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure ℝ)) :
    Rd.littlewoodPaleyNorm hp s q f < ∞ ↔ coeffNorm m p s q f < ∞ := by
  obtain ⟨θ, hsθ, hB⟩ := exists_bernsteinBound_of_le_two m hN hp2 hg hs.le hsl
  exact littlewoodPaleyNorm_lt_top_iff_coeff m hN hp hB hs hsθ
    (hsl.trans_le (hg.sub_logb_le (by omega))) hq f

/-- **Besov spaces by Daubechies coefficients, `p ≥ 2`**: let `N ≥ 2`, `2 ≤ p < ∞`,
`1 ≤ q ≤ ∞`, let `T^n 1 ≤ C λ^n` be a growth bound for the transfer operator
(`Daubechies.TransferGrowth`), and let `s', a` be real with `0 ≤ s' < N - log₄ λ` and
`0 ≤ a < N - log₄ λ - 1/2`. Then for `0 < s < (2/p) s' + (1 - 2/p) a` and every `f ∈ L_p(ℝ)`,
`‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
(`Daubechies.besov_iff_coeff` with the interpolated Bernstein bound
`Daubechies.bernsteinBound_interp`; `s', a ≤ N` since `λ ≥ 1`). -/
theorem besov_iff_coeff_of_two_le (hN : 2 ≤ N) (hp : p ≠ ∞) (hp2 : 2 ≤ p) {lam C : ℝ}
    (hg : TransferGrowth N lam C) {s' a : ℝ} (hs'0 : 0 ≤ s') (hs' : s' < N - Real.logb 4 lam)
    (ha0 : 0 ≤ a) (ha : a < N - Real.logb 4 lam - 1 / 2) {s : ℝ} (hs : 0 < s)
    (hsθ : s < 2 / p.toReal * s' + (1 - 2 / p.toReal) * a) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p N f k) < ∞ ↔
      coeffNorm m p s q f < ∞ := by
  have hle := hg.sub_logb_le (by omega)
  exact besov_iff_coeff m hN hp (bernsteinBound_interp m hN hp2 hg hs'0 hs' (by linarith) ha0
    (by linarith) ha) hs hsθ hq f

/-- **Littlewood–Paley blocks and Daubechies coefficients, `p ≥ 2`**: under the hypotheses of
`Daubechies.besov_iff_coeff_of_two_le`, for `0 < s < (2/p) s' + (1 - 2/p) a` and every
`f ∈ L_p(ℝ)`, the Littlewood–Paley quasi-norm `‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}`
(`Rd.littlewoodPaleyNorm`) is finite iff the coefficient quasi-norm `Daubechies.coeffNorm` is.
The interpolated order is at most `N`, since `s', a ≤ N` and `2/p ∈ [0, 1]`
(`Daubechies.mul_add_one_sub_mul_le`), so `s < N`. -/
theorem littlewoodPaleyNorm_lt_top_iff_coeff_of_two_le (hN : 2 ≤ N) (hp : p ≠ ∞)
    (hp2 : 2 ≤ p) {lam C : ℝ} (hg : TransferGrowth N lam C) {s' a : ℝ} (hs'0 : 0 ≤ s')
    (hs' : s' < N - Real.logb 4 lam) (ha0 : 0 ≤ a) (ha : a < N - Real.logb 4 lam - 1 / 2)
    {s : ℝ} (hs : 0 < s) (hsθ : s < 2 / p.toReal * s' + (1 - 2 / p.toReal) * a) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure ℝ)) :
    Rd.littlewoodPaleyNorm hp s q f < ∞ ↔ coeffNorm m p s q f < ∞ := by
  have hle := hg.sub_logb_le (by omega)
  exact littlewoodPaleyNorm_lt_top_iff_coeff m hN hp (bernsteinBound_interp m hN hp2 hg hs'0 hs'
    (by linarith) ha0 (by linarith) ha) hs hsθ
    (hsθ.trans_le (mul_add_one_sub_mul_le (two_div_toReal_mem_Icc hp hp2) (by linarith)
      (by linarith))) hq f

/-- **Besov spaces by Daubechies coefficients, `p ≥ 2`, from a Hölder estimate**: let `N ≥ 2`,
`2 ≤ p < ∞`, `1 ≤ q ≤ ∞`, let `T^n 1 ≤ C λ^n` be a growth bound for the transfer operator
(`Daubechies.TransferGrowth`), let `0 ≤ s' < N - log₄ λ`, and let
`|φ(x) - φ(y)| ≤ K₀ |x - y|^a` for all `x, y ∈ ℝ`, with `a ≥ 0`. Then for
`0 < s < (2/p) s' + (1 - 2/p) a` and every `f ∈ L_p(ℝ)`,
`‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
(`Daubechies.besov_iff_coeff` with the Bernstein bound
`Daubechies.bernsteinBound_interp_of_holder`). -/
theorem besov_iff_coeff_of_two_le_of_holder (hN : 2 ≤ N) (hp : p ≠ ∞) (hp2 : 2 ≤ p)
    {lam C : ℝ} (hg : TransferGrowth N lam C) {s' a K₀ : ℝ} (hs'0 : 0 ≤ s')
    (hs' : s' < N - Real.logb 4 lam) (ha0 : 0 ≤ a)
    (hK : ∀ x y : ℝ, ‖scalingFun m x - scalingFun m y‖ ≤ K₀ * |x - y| ^ a) {s : ℝ} (hs : 0 < s)
    (hsθ : s < 2 / p.toReal * s' + (1 - 2 / p.toReal) * a) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p N f k) < ∞ ↔
      coeffNorm m p s q f < ∞ := by
  have hle := hg.sub_logb_le (by omega)
  exact besov_iff_coeff m hN hp (bernsteinBound_interp_of_holder m hN hp2 (by omega) hg hs'0 hs'
    (by linarith) ha0 hK) hs hsθ hq f

end Lp

end Daubechies
