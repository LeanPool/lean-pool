/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.FilterIdentities
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Projections

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Daubechies wavelet

For a Daubechies mask of order `N ≥ 2` with filter coefficients `c_k` (`Daubechies.coeff`), dual
filter `g_k = (-1)^k c_{1-k}` (`Daubechies.dualCoeff`) and scaling function `φ`
(`Daubechies.scalingFun`), the **Daubechies wavelet** is

`ψ(x) = ∑_{k = 2 - 2N}^{1} g_k φ(2x - k)` (`Daubechies.wavelet`),

a real continuous function vanishing outside `[1 - N, N]` (`Daubechies.wavelet_eq_zero`). Its
dilates and translates `ψ_{j,k}(x) = 2^(j/2) ψ(2^j x - k)` (`Daubechies.waveletScaled`) complete
the multiresolution analysis of `FunctionSpaces.Wavelets.Examples.Daubechies.Projections`, with the
projections `P_j f = ∑_k ⟨f, φ_{j,k}⟩ φ_{j,k}`.

* **Refinement.** `ψ_{j,k} = ∑_n (g_{n-2k}/√2) φ_{j+1,n}` (`Daubechies.waveletScaled_eq_expand`),
  as `φ_{j,k} = ∑_n (c_{n-2k}/√2) φ_{j+1,n}`.
* **Orthonormality.** `⟨ψ_{j,k}, ψ_{j,l}⟩ = δ_{kl}` and `⟨ψ_{j,k}, φ_{j,l}⟩ = 0` at every level
  (`Daubechies.integral_waveletScaled_mul_conj`,
  `Daubechies.integral_waveletScaled_mul_conj_scaled`), in particular for the integer translates.
  Both functions are expansions of level `j + 1`, so Parseval's identity for finite expansions
  (`Daubechies.integral_expand_mul_conj_expand`) reduces the integrals to the filter identities
  `∑_k g_k g_{k+2i} = 2 δ_{i0}` and `∑_k c_k g_{k+2i} = 0`.
* **The block identity.** `P_{j+1} f - P_j f = ∑_k ⟨f, ψ_{j,k}⟩ ψ_{j,k}` for locally integrable
  `f` (`Daubechies.projFun_succ_eq_add`, with the wavelet part `Daubechies.detailFun`) and on
  `L_p` (`Daubechies.proj_succ_sub_proj`). The coefficients of level `j` are
  `⟨f, φ_{j,k}⟩ = ∑_n (c_{n-2k}/√2) ⟨f, φ_{j+1,n}⟩` and
  `⟨f, ψ_{j,k}⟩ = ∑_n (g_{n-2k}/√2) ⟨f, φ_{j+1,n}⟩`, both expansions of level `j` are expansions
  of level `j + 1` (`Daubechies.expand_eq_expand_succ`,
  `Daubechies.expand_wavelet_eq_expand_succ`, `Daubechies.coeffFun_eq_tsum_of_filter`), and the
  filter identity
  `∑_k (c_{a-2k} c_{b-2k} + g_{a-2k} g_{b-2k}) = 2 δ_{ab}` gives perfect reconstruction
  (`Daubechies.refineCoeff_add_waveletRefineCoeff`).
* **The kernel identity.**
  `∑_n φ_{j+1,n}(x) φ_{j+1,n}(y) = ∑_k φ_{j,k}(x) φ_{j,k}(y) + ∑_k ψ_{j,k}(x) ψ_{j,k}(y)`
  (`Daubechies.tsum_scaled_mul_scaled_succ`), by perfect reconstruction with
  `a_n = φ_{j+1,n}(y)`; at level `0` it reads `2 K(2x, 2y) = K(x, y) + ∑_k ψ(x - k) ψ(y - k)` for
  the kernel `K(x, y) = ∑_k φ(x - k) φ(y - k)` of `P_0` (`Daubechies.kernel_succ`).
* **Norms of the blocks.** For `1 ≤ p < ∞` there are constants `K, M < ∞` with
  `2^(j(1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p} ≤ K ‖P_{j+1} f - P_j f‖_p` and
  `‖P_{j+1} f - P_j f‖_p ≤ M 2^(j(1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p}` for all `f` and `j`
  (`Daubechies.enorm_block_equiv`), and the same for `‖P_j f‖_p` and the coefficients
  `⟨f, φ_{j,k}⟩` (`Daubechies.enorm_proj_equiv`, `Daubechies.enorm_proj_zero_equiv`): the
  stability of the expansions (`FunctionSpaces.Wavelets.Examples.Daubechies.Expansion`).
* **Vanishing moments.** `∫ x^l ψ(x) dx = 0` for `l < N` (`Daubechies.vanishing_moments`): the
  substitution `y = 2x - k` and the binomial theorem reduce it to `∑_k g_k k^i = 0` for `i < N`.
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped ENNReal ComplexConjugate
open ENNReal (dyadicWeight)

namespace Daubechies

variable {N : ℕ} (m : Mask N)

/-! ### The wavelet -/

/-- **The Daubechies wavelet** `ψ(x) = ∑_{k = 2 - 2N}^{1} g_k φ(2x - k)` of a mask of order `N`,
with the dual filter `g_k = (-1)^k c_{1-k}` (`Daubechies.dualCoeff`) and the scaling function `φ`
(`Daubechies.scalingFun`). The dual filter vanishes outside `2 - 2N ≤ k ≤ 1`
(`Daubechies.dualCoeff_eq_zero`), so this is the sum over all `k ∈ ℤ`. -/
noncomputable def wavelet (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (2 - 2 * (N : ℤ)) 1, (dualCoeff m k : ℂ) * scalingFun m (2 * x - k)

/-- **Support of the wavelet**: for `N ≥ 2`, `ψ(x) = 0` for every `x` outside `[1 - N, N]`. A term
`g_k φ(2x - k)` with `2 - 2N ≤ k ≤ 1` is nonzero only if `0 ≤ 2x - k ≤ 2N - 1`
(`Daubechies.scalingFun_eq_zero`), which forces `2 - 2N ≤ 2x ≤ 2N`. -/
theorem wavelet_eq_zero (hN : 2 ≤ N) {x : ℝ} (hx : x ∉ Set.Icc (1 - N : ℝ) N) :
    wavelet m x = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
  have hk1' : (2 - 2 * N : ℝ) ≤ k := by exact_mod_cast hk1
  have hk2' : (k : ℝ) ≤ 1 := by exact_mod_cast hk2
  rw [scalingFun_eq_zero m hN fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩, mul_zero]

/-- **The wavelet is continuous**, for `N ≥ 2`: a finite sum of dilated and translated copies of
the continuous scaling function (`Daubechies.continuous_scalingFun`). -/
theorem continuous_wavelet (hN : 2 ≤ N) : Continuous (wavelet m) := by
  have hφ := continuous_scalingFun m hN
  unfold wavelet
  fun_prop

/-- **The wavelet has compact support**, for `N ≥ 2`: it vanishes outside `[1 - N, N]`
(`Daubechies.wavelet_eq_zero`). -/
theorem hasCompactSupport_wavelet (hN : 2 ≤ N) : HasCompactSupport (wavelet m) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => wavelet_eq_zero m hN hx

/-- **The wavelet lies in every `L_p`**, `p ∈ [0, ∞]`, for `N ≥ 2`: it is continuous with compact
support (Mathlib's `Continuous.memLp_of_hasCompactSupport`). -/
theorem memLp_wavelet (hN : 2 ≤ N) (p : ℝ≥0∞) : MemLp (wavelet m) p :=
  (continuous_wavelet m hN).memLp_of_hasCompactSupport (hasCompactSupport_wavelet m hN)

/-- **The wavelet is real**: `conj ψ(x) = ψ(x)` for every `x ∈ ℝ`, since the dual filter and the
scaling function are real (`Daubechies.conj_scalingFun`). -/
theorem conj_wavelet (x : ℝ) : conj (wavelet m x) = wavelet m x := by
  simp only [wavelet, map_sum, map_mul, Complex.conj_ofReal, conj_scalingFun]

/-! ### The wavelets of every level -/

/-- **The wavelets of level `j`**: `ψ_{j,k}(x) = 2^(j/2) ψ(2^j x - k)` for the level `j ∈ ℕ` and
the position `k ∈ ℤ`; this is the generic `Daubechies.scaledFun` for `g = ψ`. -/
noncomputable abbrev waveletScaled (j : ℕ) (k : ℤ) : ℝ → ℂ := scaledFun (wavelet m) j k

/-- **The wavelets through the scaling functions of the next level**: for every level `j`,
position `k` and point `x`, `ψ_{j,k}(x) = ∑_{i = 2 - 2N}^{1} (g_i/√2) φ_{j+1,2k+i}(x)`. This is the
definition `ψ(y) = ∑_i g_i φ(2y - i)` at `y = 2^j x - k`, with
`2(2^j x - k) - i = 2^(j+1) x - (2k + i)` and `2^(j/2) = 2^((j+1)/2)/√2`
(`Daubechies.two_rpow_succ_div_two`). -/
theorem waveletScaled_refine (j : ℕ) (k : ℤ) (x : ℝ) :
    waveletScaled m j k x = ∑ i ∈ Finset.Icc (2 - 2 * (N : ℤ)) 1,
      ((dualCoeff m i / √2 : ℝ) : ℂ) * scaled m (j + 1) (2 * k + i) x := by
  simp only [waveletScaled, scaled, scaledFun, wavelet]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : (2 : ℝ) * ((2 : ℝ) ^ j * x - k) - i = 2 ^ (j + 1) * x - ((2 * k + i : ℤ) : ℝ) := by
    push_cast
    ring
  have hs : (√2 : ℝ) ≠ 0 := by positivity
  have hc : (2 : ℝ) ^ ((j : ℝ) / 2) * dualCoeff m i =
      dualCoeff m i / √2 * ((2 : ℝ) ^ ((j : ℝ) / 2) * √2) := by
    field_simp
  rw [h2, two_rpow_succ_div_two, ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, hc]

/-- **`ψ_{j,k}` is an expansion of level `j + 1`**: for every level `j`, position `k` and point
`x`, `ψ_{j,k}(x) = ∑_{n ∈ ℤ} (g_{n-2k}/√2) φ_{j+1,n}(x)`. This is
`Daubechies.waveletScaled_refine` after the substitution `n = 2k + i`; the dual filter vanishes
outside `2 - 2N ≤ i ≤ 1` (`Daubechies.dualCoeff_eq_zero`). -/
theorem waveletScaled_eq_expand (j : ℕ) (k : ℤ) (x : ℝ) :
    waveletScaled m j k x =
      expand (scalingFun m) (j + 1) (fun n => ((dualCoeff m (n - 2 * k) / √2 : ℝ) : ℂ)) x := by
  rw [waveletScaled_refine m, expand, ← (Equiv.addLeft (2 * k)).tsum_eq]
  simp only [Equiv.coe_addLeft, add_sub_cancel_left]
  rw [tsum_eq_sum (s := Finset.Icc (2 - 2 * (N : ℤ)) 1) ?_]
  intro i hi
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hi
  rw [dualCoeff_eq_zero m hi, zero_div, Complex.ofReal_zero, zero_mul]

/-! ### Inner products with finite expansions -/

/-- **Coefficients against a finite expansion**: let `N ≥ 2`, let `f` be locally integrable and
let the coefficients `v : ℤ → ℂ` vanish outside a finite set `T`. Then for every level `j`,
`∫ f conj(∑_n v_n φ_{j,n}) = ∑_{n ∈ T} conj(v_n) ⟨f, φ_{j,n}⟩`: the expansion is a finite sum, and
the integral is linear on the integrable terms (`Daubechies.integrable_mul_conj_scaled`). -/
theorem integral_mul_conj_expand (hN : 2 ≤ N) {f : ℝ → ℂ} (hf : LocallyIntegrable f volume)
    (j : ℕ) {v : ℤ → ℂ} {T : Finset ℤ} (hv : ∀ n ∉ T, v n = 0) :
    ∫ y, f y * conj (expand (scalingFun m) j v y) =
      ∑ n ∈ T, conj (v n) * coeffFun (scalingFun m) j f n := by
  have h : ∀ y, f y * conj (expand (scalingFun m) j v y) =
      ∑ n ∈ T, conj (v n) * (f y * conj (scaled m j n y)) := fun y => by
    rw [expand, tsum_eq_sum (s := T) fun n hn => by rw [hv n hn, zero_mul], map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul]
    ring
  simp_rw [h]
  rw [integral_finsetSum _ fun n _ => (integrable_mul_conj_scaled m hN hf j n).const_mul _]
  simp_rw [integral_const_mul]
  rfl

/-- **Parseval's identity for a finite expansion**: for `N ≥ 2`, every level `j`, all coefficients
`u : ℤ → ℂ` and all coefficients `v` vanishing outside a finite set `T`,
`∫ (∑_n u_n φ_{j,n}) conj(∑_n v_n φ_{j,n}) = ∑_{n ∈ T} u_n conj(v_n)`, by
`Daubechies.integral_mul_conj_expand` and coefficient recovery
(`Daubechies.coeffFun_expand_scalingFun`). -/
theorem integral_expand_mul_conj_expand (hN : 2 ≤ N) (j : ℕ) (u : ℤ → ℂ) {v : ℤ → ℂ}
    {T : Finset ℤ} (hv : ∀ n ∉ T, v n = 0) :
    ∫ y, expand (scalingFun m) j u y * conj (expand (scalingFun m) j v y) =
      ∑ n ∈ T, u n * conj (v n) := by
  rw [integral_mul_conj_expand m hN (continuous_expand (continuous_scalingFun m hN)
    (fun _ hx => scalingFun_eq_zero m hN hx) j u).locallyIntegrable j hv]
  exact Finset.sum_congr rfl fun n _ => by rw [coeffFun_expand_scalingFun m hN, mul_comm]

/-! ### Sums of products of filters -/

/-- **Support of the dual filter**: if `g_i ≠ 0`, then `2 - 2N ≤ i ≤ 1`
(`Daubechies.dualCoeff_eq_zero`). -/
theorem mem_Icc_of_dualCoeff_ne_zero {i : ℤ} (h : dualCoeff m i ≠ 0) :
    2 - 2 * (N : ℤ) ≤ i ∧ i ≤ 1 := by
  by_contra h'
  exact h (dualCoeff_eq_zero m (by omega))

/-- The shifted filter `n ↦ c_{n-2l}` vanishes outside `[2l, 2l + 2N - 1]`
(`Daubechies.coeff_eq_zero`). -/
theorem coeff_sub_eq_zero {l n : ℤ} (hn : n ∉ Finset.Icc (2 * l) (2 * l + (2 * N - 1))) :
    coeff m (n - 2 * l) = 0 := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  exact coeff_eq_zero m (by omega)

/-- The shifted dual filter `n ↦ g_{n-2l}` vanishes outside `[2l + 2 - 2N, 2l + 1]`
(`Daubechies.dualCoeff_eq_zero`). -/
theorem dualCoeff_sub_eq_zero {l n : ℤ} (hn : n ∉ Finset.Icc (2 * l + (2 - 2 * N)) (2 * l + 1)) :
    dualCoeff m (n - 2 * l) = 0 := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  exact dualCoeff_eq_zero m (by omega)

/-- **A sum of products of shifted filters**: let `h, h' : ℤ → ℝ`, `k, l ∈ ℤ`, and let
`h'(n - 2l) = 0` for every `n` outside a finite set `T`. Then
`∑_{n ∈ T} (h_{n-2k}/√2) conj(h'_{n-2l}/√2) = (1/2) ∑_{n ∈ ℤ} h_{n-2k} h'_{n-2l}`, since
`√2 √2 = 2` and the sequences are real. -/
theorem sum_mul_conj_filter {h h' : ℤ → ℝ} {T : Finset ℤ} {k l : ℤ}
    (hT : ∀ n ∉ T, h' (n - 2 * l) = 0) :
    ∑ n ∈ T, ((h (n - 2 * k) / √2 : ℝ) : ℂ) * conj ((h' (n - 2 * l) / √2 : ℝ) : ℂ) =
      ((1 / 2 * ∑ᶠ n : ℤ, h (n - 2 * k) * h' (n - 2 * l) : ℝ) : ℂ) := by
  rw [finsum_eq_sum_of_support_subset (s := T) _ fun n hn =>
    by_contra fun hnT => hn (by rw [hT n hnT, mul_zero]), Finset.mul_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hr : h (n - 2 * k) / √2 * (h' (n - 2 * l) / √2) =
      1 / 2 * (h (n - 2 * k) * h' (n - 2 * l)) := by
    rw [div_mul_div_comm, Real.mul_self_sqrt zero_le_two]
    ring
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, hr]

/-- **Reindexing a sum of products of shifted sequences**: for all `h, h' : ℤ → ℝ` and
`k, l ∈ ℤ`, `∑_n h_{n-2k} h'_{n-2l} = ∑_a h_a h'_{a+2(k-l)}`, by the substitution `n = a + 2k`. -/
theorem finsum_mul_sub_two_mul (h h' : ℤ → ℝ) (k l : ℤ) :
    ∑ᶠ n : ℤ, h (n - 2 * k) * h' (n - 2 * l) = ∑ᶠ a : ℤ, h a * h' (a + 2 * (k - l)) := by
  rw [← finsum_comp_equiv (Equiv.addRight (2 * k))]
  refine finsum_congr fun a => ?_
  simp only [Equiv.coe_addRight]
  rw [add_sub_cancel_right, show a + 2 * k - 2 * l = a + 2 * (k - l) by ring]

/-! ### Orthonormality -/

/-- **Orthonormality of the wavelets at every level**: for `N ≥ 2`, every level `j` and all
positions `k, l`, `∫ ψ_{j,k}(x) conj ψ_{j,l}(x) dx` is `1` for `k = l` and `0` otherwise. Both
wavelets are expansions of level `j + 1` with the coefficients `g_{n-2k}/√2` and `g_{n-2l}/√2`
(`Daubechies.waveletScaled_eq_expand`), so by Parseval's identity
(`Daubechies.integral_expand_mul_conj_expand`) the integral is
`(1/2) ∑_n g_{n-2k} g_{n-2l} = (1/2) ∑_a g_a g_{a+2(k-l)} = δ_{kl}`
(`Daubechies.sum_dualCoeff_mul_dualCoeff_add`). -/
theorem integral_waveletScaled_mul_conj (hN : 2 ≤ N) (j : ℕ) (k l : ℤ) :
    ∫ x, waveletScaled m j k x * conj (waveletScaled m j l x) = if k = l then 1 else 0 := by
  simp_rw [waveletScaled_eq_expand m j]
  rw [integral_expand_mul_conj_expand m hN (j + 1) _
      (T := Finset.Icc (2 * l + (2 - 2 * N)) (2 * l + 1)) fun n hn => by
        simp only [dualCoeff_sub_eq_zero m hn, zero_div, Complex.ofReal_zero],
    sum_mul_conj_filter fun n hn => dualCoeff_sub_eq_zero m hn, finsum_mul_sub_two_mul,
    sum_dualCoeff_mul_dualCoeff_add]
  simp only [sub_eq_zero]
  split_ifs <;> norm_num

/-- **The wavelets are orthogonal to the scaling functions of the same level**: for `N ≥ 2`,
every level `j` and all positions `k, l`, `∫ ψ_{j,k}(x) conj φ_{j,l}(x) dx = 0`. As expansions of
level `j + 1` (`Daubechies.waveletScaled_eq_expand`, `Daubechies.scaled_eq_expand`), Parseval's
identity gives `(1/2) ∑_n g_{n-2k} c_{n-2l} = (1/2) ∑_a c_a g_{a+2(l-k)} = 0`
(`Daubechies.sum_coeff_mul_dualCoeff_add`). -/
theorem integral_waveletScaled_mul_conj_scaled (hN : 2 ≤ N) (j : ℕ) (k l : ℤ) :
    ∫ x, waveletScaled m j k x * conj (scaled m j l x) = 0 := by
  simp_rw [waveletScaled_eq_expand m j, scaled_eq_expand m hN j]
  rw [integral_expand_mul_conj_expand m hN (j + 1) _
      (T := Finset.Icc (2 * l) (2 * l + (2 * N - 1))) fun n hn => by
        simp only [coeff_sub_eq_zero m hn, zero_div, Complex.ofReal_zero],
    sum_mul_conj_filter fun n hn => coeff_sub_eq_zero m hn,
    finsum_congr fun n => mul_comm (dualCoeff m (n - 2 * k)) (coeff m (n - 2 * l)),
    finsum_mul_sub_two_mul, sum_coeff_mul_dualCoeff_add, mul_zero, Complex.ofReal_zero]

/-- **Orthonormality of the integer translates of the wavelet**: for `N ≥ 2` and all `k, l ∈ ℤ`,
`∫ ψ(x - k) conj ψ(x - l) dx` is `1` for `k = l` and `0` otherwise: the level `j = 0` of
`Daubechies.integral_waveletScaled_mul_conj` (`Daubechies.scaledFun_zero`). -/
theorem integral_wavelet_translate_mul_conj_translate (hN : 2 ≤ N) (k l : ℤ) :
    ∫ x, wavelet m (x - k) * conj (wavelet m (x - l)) = if k = l then 1 else 0 := by
  simpa only [waveletScaled, scaledFun_zero] using integral_waveletScaled_mul_conj m hN 0 k l

/-- **The integer translates of the wavelet and of the scaling function are orthogonal**: for
`N ≥ 2` and all `k, l ∈ ℤ`, `∫ ψ(x - k) conj φ(x - l) dx = 0`: the level `j = 0` of
`Daubechies.integral_waveletScaled_mul_conj_scaled` (`Daubechies.scaledFun_zero`). -/
theorem integral_wavelet_translate_mul_conj_scalingFun_translate (hN : 2 ≤ N) (k l : ℤ) :
    ∫ x, wavelet m (x - k) * conj (scalingFun m (x - l)) = 0 := by
  simpa only [waveletScaled, scaled, scaledFun_zero] using
    integral_waveletScaled_mul_conj_scaled m hN 0 k l

/-! ### The coefficients of two consecutive levels -/

/-- **The coefficients of a refinable generator through those of the next level**: if `N ≥ 2`,
the real filter `h` vanishes outside `[a, b]`, `f` is locally integrable and
`g_{j,k} = ∑_n (h_{n-2k}/√2) φ_{j+1,n}`, then `⟨f, g_{j,k}⟩ = ∑_n (h_{n-2k}/√2) ⟨f, φ_{j+1,n}⟩`
(`Daubechies.integral_mul_conj_expand` for the finite expansion; the filter is real). -/
theorem coeffFun_eq_tsum_of_filter (hN : 2 ≤ N) {g : ℝ → ℂ} {h : ℤ → ℝ} {a b : ℤ}
    (hh : ∀ i, h i ≠ 0 → a ≤ i ∧ i ≤ b) {f : ℝ → ℂ} (hf : LocallyIntegrable f volume)
    (j : ℕ) (k : ℤ)
    (hg : ∀ x, scaledFun g j k x =
      expand (scalingFun m) (j + 1) (fun n => ((h (n - 2 * k) / √2 : ℝ) : ℂ)) x) :
    coeffFun g j f k =
      ∑' n : ℤ, ((h (n - 2 * k) / √2 : ℝ) : ℂ) * coeffFun (scalingFun m) (j + 1) f n := by
  have hT : ∀ n ∉ Finset.Icc (2 * k + a) (2 * k + b), ((h (n - 2 * k) / √2 : ℝ) : ℂ) = 0 :=
    fun n hn => by
      have h0 : h (n - 2 * k) = 0 := by
        by_contra hne
        obtain ⟨h1, h2⟩ := hh _ hne
        exact hn (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      rw [h0, zero_div, Complex.ofReal_zero]
  rw [coeffFun, show scaledFun g j k = expand (scalingFun m) (j + 1)
      (fun n => ((h (n - 2 * k) / √2 : ℝ) : ℂ)) from funext hg,
    integral_mul_conj_expand m hN hf (j + 1) hT,
    tsum_eq_sum (s := Finset.Icc (2 * k + a) (2 * k + b)) fun n hn => by rw [hT n hn, zero_mul]]
  simp only [Complex.conj_ofReal]

/-- **The scaling coefficients of level `j` through those of level `j + 1`**: for `N ≥ 2` and
locally integrable `f`, `⟨f, φ_{j,k}⟩ = ∑_n (c_{n-2k}/√2) ⟨f, φ_{j+1,n}⟩`
(`Daubechies.coeffFun_eq_tsum_of_filter`, `Daubechies.scaled_eq_expand`). -/
theorem coeffFun_scalingFun_eq_tsum (hN : 2 ≤ N) {f : ℝ → ℂ} (hf : LocallyIntegrable f volume)
    (j : ℕ) (k : ℤ) :
    coeffFun (scalingFun m) j f k =
      ∑' n : ℤ, ((coeff m (n - 2 * k) / √2 : ℝ) : ℂ) * coeffFun (scalingFun m) (j + 1) f n :=
  coeffFun_eq_tsum_of_filter m hN (h := coeff m) (fun _ hi => mem_Icc_of_coeff_ne_zero m hi) hf
    j k (scaled_eq_expand m hN j k)

/-- **The wavelet coefficients of level `j` through the scaling coefficients of level `j + 1`**:
for `N ≥ 2` and locally integrable `f`, `⟨f, ψ_{j,k}⟩ = ∑_n (g_{n-2k}/√2) ⟨f, φ_{j+1,n}⟩`
(`Daubechies.coeffFun_eq_tsum_of_filter`, `Daubechies.waveletScaled_eq_expand`). -/
theorem coeffFun_wavelet_eq_tsum (hN : 2 ≤ N) {f : ℝ → ℂ} (hf : LocallyIntegrable f volume)
    (j : ℕ) (k : ℤ) :
    coeffFun (wavelet m) j f k =
      ∑' n : ℤ, ((dualCoeff m (n - 2 * k) / √2 : ℝ) : ℂ) * coeffFun (scalingFun m) (j + 1) f n :=
  coeffFun_eq_tsum_of_filter m hN (h := dualCoeff m)
    (fun _ hi => mem_Icc_of_dualCoeff_ne_zero m hi) hf j k (waveletScaled_eq_expand m j k)

/-- **The refined wavelet coefficients**: for coefficients `b : ℤ → ℂ` of level `j`, the
coefficients `b'_n = ∑_{k ∈ ℤ} b_k g_{n-2k}/√2` of level `j + 1`, with the dual filter `g`
(`Daubechies.dualCoeff`); only the `k` with `2 - 2N ≤ n - 2k ≤ 1` contribute. They express a
wavelet expansion of level `j` as an expansion in the scaling functions of level `j + 1`,
`∑_k b_k ψ_{j,k} = ∑_n b'_n φ_{j+1,n}` (`Daubechies.expand_wavelet_eq_expand_succ`). -/
noncomputable def waveletRefineCoeff (b : ℤ → ℂ) (n : ℤ) : ℂ :=
  ∑' k : ℤ, b k * ((dualCoeff m (n - 2 * k) / √2 : ℝ) : ℂ)

/-- **The double sum of the wavelet refinement has finitely many terms**: for `N ≥ 2` the family
`(k, n) ↦ b_k (g_{n-2k}/√2) φ_{j+1,n}(x)` is summable over `ℤ × ℤ`
(`Daubechies.summable_refine_of_filter`, `Daubechies.mem_Icc_of_dualCoeff_ne_zero`). -/
theorem summable_waveletRefine (hN : 2 ≤ N) (j : ℕ) (b : ℤ → ℂ) (x : ℝ) :
    Summable (Function.uncurry fun k n : ℤ =>
      b k * (((dualCoeff m (n - 2 * k) / √2 : ℝ) : ℂ) * scaled m (j + 1) n x)) :=
  summable_refine_of_filter m hN (h := dualCoeff m)
    (fun _ hi => mem_Icc_of_dualCoeff_ne_zero m hi) j b x

/-- **Wavelet expansions of level `j` are expansions of level `j + 1`**: for `N ≥ 2`, every level
`j`, coefficients `b : ℤ → ℂ` and point `x`, `∑_k b_k ψ_{j,k}(x) = ∑_n b'_n φ_{j+1,n}(x)` with the
refined coefficients `b'_n = ∑_k b_k g_{n-2k}/√2` (`Daubechies.waveletRefineCoeff`), by
`Daubechies.expand_eq_tsum_refine_of_filter` and `Daubechies.waveletScaled_eq_expand`. -/
theorem expand_wavelet_eq_expand_succ (hN : 2 ≤ N) (j : ℕ) (b : ℤ → ℂ) (x : ℝ) :
    expand (wavelet m) j b x = expand (scalingFun m) (j + 1) (waveletRefineCoeff m b) x :=
  expand_eq_tsum_refine_of_filter m hN (h := dualCoeff m)
    (fun _ hi => mem_Icc_of_dualCoeff_ne_zero m hi) j (waveletScaled_eq_expand m j) b x

/-! ### Perfect reconstruction -/

/-- **Combining and exchanging two double sums**: for families `X, Y : ℤ → ℤ → ℂ` that are
summable over `ℤ × ℤ`, `∑_k ∑_n X_{k,n} + ∑_k ∑_n Y_{k,n} = ∑_n ∑_k (X_{k,n} + Y_{k,n})` (Mathlib's
`Summable.tsum_comm`, `Summable.prod`, `Summable.prod_factor`). -/
theorem tsum_tsum_add_tsum_tsum {X Y : ℤ → ℤ → ℂ} (hX : Summable (Function.uncurry X))
    (hY : Summable (Function.uncurry Y)) :
    ∑' k, ∑' n, X k n + ∑' k, ∑' n, Y k n = ∑' n, ∑' k, (X k n + Y k n) := by
  have hX1 : Summable fun k => ∑' n, X k n := hX.prod
  have hY1 : Summable fun k => ∑' n, Y k n := hY.prod
  have hXY : Summable (Function.uncurry fun k n => X k n + Y k n) := hX.add hY
  calc ∑' k, ∑' n, X k n + ∑' k, ∑' n, Y k n
      = ∑' k, (∑' n, X k n + ∑' n, Y k n) := (hX1.tsum_add hY1).symm
    _ = ∑' k, ∑' n, (X k n + Y k n) :=
        tsum_congr fun k => ((hX.prod_factor k).tsum_add (hY.prod_factor k)).symm
    _ = ∑' n, ∑' k, (X k n + Y k n) := hXY.tsum_comm.symm

/-- **The double sum of the filter identity has finitely many terms**: let `h, h' : ℤ → ℝ` vanish
outside `[-B, B]`. Then for every `a : ℤ → ℂ` and `n' ∈ ℤ` the family
`(k, n) ↦ (h_{n-2k}/√2)(h'_{n'-2k}/√2) a_n` is summable over `ℤ × ℤ`: a nonzero term needs
`|n' - 2k| ≤ B` and `|n - 2k| ≤ B`, which leaves finitely many pairs. -/
theorem summable_filter_mul_filter {h h' : ℤ → ℝ} {B : ℤ}
    (hh : ∀ i, h i ≠ 0 → -B ≤ i ∧ i ≤ B) (hh' : ∀ i, h' i ≠ 0 → -B ≤ i ∧ i ≤ B)
    (a : ℤ → ℂ) (n' : ℤ) :
    Summable (Function.uncurry fun k n : ℤ =>
      ((h (n - 2 * k) / √2 : ℝ) : ℂ) * ((h' (n' - 2 * k) / √2 : ℝ) : ℂ) * a n) := by
  refine summable_of_ne_finset_zero (s := Finset.Icc (n' / 2 - B) (n' / 2 + B) ×ˢ
    Finset.Icc (n' - 4 * B - 1) (n' + 4 * B + 1)) fun kn hkn => ?_
  obtain ⟨k, n⟩ := kn
  by_contra hne
  simp only [Function.uncurry_apply_pair] at hne
  obtain ⟨h1, -⟩ := mul_ne_zero_iff.1 hne
  obtain ⟨h3, h4⟩ := mul_ne_zero_iff.1 h1
  have h3' : h (n - 2 * k) ≠ 0 := fun h0 => h3 (by rw [h0, zero_div, Complex.ofReal_zero])
  have h4' : h' (n' - 2 * k) ≠ 0 := fun h0 => h4 (by rw [h0, zero_div, Complex.ofReal_zero])
  obtain ⟨h5, h6⟩ := hh _ h3'
  obtain ⟨h7, h8⟩ := hh' _ h4'
  exact hkn (Finset.mem_product.2
    ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩)

/-- **The filter identity with normalised filters**: for all `n, n' ∈ ℤ`,
`∑_{k ∈ ℤ} ((c_{n-2k}/√2)(c_{n'-2k}/√2) + (g_{n-2k}/√2)(g_{n'-2k}/√2))` is `1` for `n = n'` and
`0` otherwise (`Daubechies.sum_coeff_mul_add_dual`); only finitely many terms are nonzero. -/
theorem tsum_coeff_mul_add_dual (n n' : ℤ) :
    ∑' k : ℤ, (((coeff m (n - 2 * k) / √2 : ℝ) : ℂ) * ((coeff m (n' - 2 * k) / √2 : ℝ) : ℂ) +
      ((dualCoeff m (n - 2 * k) / √2 : ℝ) : ℂ) * ((dualCoeff m (n' - 2 * k) / √2 : ℝ) : ℂ)) =
    if n = n' then 1 else 0 := by
  have hinj : Function.Injective fun k : ℤ => n' - 2 * k := fun i i' hii' => by
    simp only at hii'
    omega
  have hfin : Function.HasFiniteSupport fun k : ℤ =>
      coeff m (n - 2 * k) * coeff m (n' - 2 * k) +
        dualCoeff m (n - 2 * k) * dualCoeff m (n' - 2 * k) :=
    Set.Finite.subset (Set.Finite.union
      (Set.Finite.subset (Function.HasFiniteSupport.fun_comp_of_injective hinj
        (finite_support_coeff m)) (Function.support_mul_subset_right _ _))
      (Set.Finite.subset (Function.HasFiniteSupport.fun_comp_of_injective hinj
        (finite_support_dualCoeff m)) (Function.support_mul_subset_right _ _)))
      (Function.support_add _ _)
  have h : ∀ k : ℤ,
      ((coeff m (n - 2 * k) / √2 : ℝ) : ℂ) * ((coeff m (n' - 2 * k) / √2 : ℝ) : ℂ) +
        ((dualCoeff m (n - 2 * k) / √2 : ℝ) : ℂ) * ((dualCoeff m (n' - 2 * k) / √2 : ℝ) : ℂ) =
      ((1 / 2 * (coeff m (n - 2 * k) * coeff m (n' - 2 * k) +
        dualCoeff m (n - 2 * k) * dualCoeff m (n' - 2 * k)) : ℝ) : ℂ) := fun k => by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, div_mul_div_comm,
      div_mul_div_comm, Real.mul_self_sqrt zero_le_two]
    congr 1
    ring
  simp_rw [h]
  rw [← Complex.ofReal_tsum, tsum_mul_left, tsum_eq_finsum hfin, sum_coeff_mul_add_dual]
  split_ifs <;> norm_num

/-- **Perfect reconstruction**: for every `a : ℤ → ℂ` and `n' ∈ ℤ`,
`∑_k (∑_n (c_{n-2k}/√2) a_n)(c_{n'-2k}/√2) + ∑_k (∑_n (g_{n-2k}/√2) a_n)(g_{n'-2k}/√2) = a_{n'}`:
the left side is `∑_n a_n ∑_k ((c_{n-2k}/√2)(c_{n'-2k}/√2) + (g_{n-2k}/√2)(g_{n'-2k}/√2))` after
exchanging the sums (`Daubechies.summable_filter_mul_filter`,
`Daubechies.tsum_tsum_add_tsum_tsum`), and the inner sum is `δ_{nn'}`
(`Daubechies.tsum_coeff_mul_add_dual`). In terms of the refined coefficients
(`Daubechies.refineCoeff`, `Daubechies.waveletRefineCoeff`) this reads `H* H a + G* G a = a`. -/
theorem refineCoeff_add_waveletRefineCoeff (a : ℤ → ℂ) (n' : ℤ) :
    refineCoeff m (fun k => ∑' n, ((coeff m (n - 2 * k) / √2 : ℝ) : ℂ) * a n) n' +
      waveletRefineCoeff m (fun k => ∑' n, ((dualCoeff m (n - 2 * k) / √2 : ℝ) : ℂ) * a n) n' =
    a n' := by
  have hc : ∀ i, coeff m i ≠ 0 → -(2 * N : ℤ) ≤ i ∧ i ≤ 2 * N := fun i hi => by
    have := mem_Icc_of_coeff_ne_zero m hi
    omega
  have hg : ∀ i, dualCoeff m i ≠ 0 → -(2 * N : ℤ) ≤ i ∧ i ≤ 2 * N := fun i hi => by
    have := mem_Icc_of_dualCoeff_ne_zero m hi
    omega
  have e1 : refineCoeff m (fun k => ∑' n, ((coeff m (n - 2 * k) / √2 : ℝ) : ℂ) * a n) n' =
      ∑' k : ℤ, ∑' n : ℤ,
        ((coeff m (n - 2 * k) / √2 : ℝ) : ℂ) * ((coeff m (n' - 2 * k) / √2 : ℝ) : ℂ) * a n := by
    rw [refineCoeff]
    refine tsum_congr fun k => ?_
    rw [← tsum_mul_right]
    exact tsum_congr fun n => by ring
  have e2 : waveletRefineCoeff m
      (fun k => ∑' n, ((dualCoeff m (n - 2 * k) / √2 : ℝ) : ℂ) * a n) n' =
      ∑' k : ℤ, ∑' n : ℤ, ((dualCoeff m (n - 2 * k) / √2 : ℝ) : ℂ) *
        ((dualCoeff m (n' - 2 * k) / √2 : ℝ) : ℂ) * a n := by
    rw [waveletRefineCoeff]
    refine tsum_congr fun k => ?_
    rw [← tsum_mul_right]
    exact tsum_congr fun n => by ring
  have e3 : ∀ n : ℤ, ∑' k : ℤ,
      (((coeff m (n - 2 * k) / √2 : ℝ) : ℂ) * ((coeff m (n' - 2 * k) / √2 : ℝ) : ℂ) * a n +
        ((dualCoeff m (n - 2 * k) / √2 : ℝ) : ℂ) * ((dualCoeff m (n' - 2 * k) / √2 : ℝ) : ℂ) *
          a n) = if n = n' then a n else 0 := fun n => by
    rw [tsum_congr fun k => (add_mul _ _ (a n)).symm, tsum_mul_right, tsum_coeff_mul_add_dual]
    split_ifs <;> simp
  rw [e1, e2, tsum_tsum_add_tsum_tsum (summable_filter_mul_filter hc hc a n')
    (summable_filter_mul_filter hg hg a n'), tsum_congr e3]
  exact tsum_ite_eq n' a

/-! ### The block identity -/

/-- **The wavelet part of level `j`, pointwise**: `Q_j f(x) = ∑_{k ∈ ℤ} ⟨f, ψ_{j,k}⟩ ψ_{j,k}(x)`
for every `f : ℝ → ℂ`, the expansion of level `j` in the wavelets with the coefficients
`⟨f, ψ_{j,k}⟩ = ∫ f(y) conj ψ_{j,k}(y) dy` (`Daubechies.coeffFun`). It is the difference
`P_{j+1} f - P_j f` of two consecutive projections (`Daubechies.projFun_succ_eq_add`). -/
noncomputable def detailFun (j : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  expand (wavelet m) j (coeffFun (wavelet m) j f)

/-- **The block identity, pointwise**: for `N ≥ 2`, locally integrable `f`, every level `j` and
point `x`, `P_{j+1} f(x) = P_j f(x) + ∑_k ⟨f, ψ_{j,k}⟩ ψ_{j,k}(x)`. Both terms on the right are
expansions of level `j + 1` (`Daubechies.expand_eq_expand_succ`,
`Daubechies.expand_wavelet_eq_expand_succ`) whose coefficients, written through
`a_n = ⟨f, φ_{j+1,n}⟩` (`Daubechies.coeffFun_scalingFun_eq_tsum`,
`Daubechies.coeffFun_wavelet_eq_tsum`), add up to `a` (perfect reconstruction,
`Daubechies.refineCoeff_add_waveletRefineCoeff`). -/
theorem projFun_succ_eq_add (hN : 2 ≤ N) {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) (j : ℕ)
    (x : ℝ) : projFun m (j + 1) f x = projFun m j f x + detailFun m j f x := by
  have hc : coeffFun (scalingFun m) (j + 1) f = fun n =>
      refineCoeff m (coeffFun (scalingFun m) j f) n +
        waveletRefineCoeff m (coeffFun (wavelet m) j f) n := by
    funext n
    rw [funext (coeffFun_scalingFun_eq_tsum m hN hf j), funext (coeffFun_wavelet_eq_tsum m hN hf j),
      refineCoeff_add_waveletRefineCoeff m (coeffFun (scalingFun m) (j + 1) f) n]
  rw [projFun, projFun, detailFun, expand_eq_expand_succ m hN j (coeffFun (scalingFun m) j f) x,
    expand_wavelet_eq_expand_succ m hN j (coeffFun (wavelet m) j f) x,
    ← expand_add (fun _ hy => scalingFun_eq_zero m hN hy), ← hc]

/-- **The wavelet part of an `L_p` function lies in `L_p`**: for `N ≥ 2`, `1 ≤ p < ∞`, `f ∈ L_p`
and every level `j` (`Daubechies.memLp_expand_coeffFun` for `g = ψ`). -/
theorem memLp_detailFun (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : ℝ → ℂ}
    (hf : MemLp f p volume) (j : ℕ) : MemLp (detailFun m j f) p volume :=
  memLp_expand_coeffFun (continuous_wavelet m hN) (fun _ hx => wavelet_eq_zero m hN hx) hp1 hp hf j

/-! ### The kernel identity -/

/-- **The kernel identity at level `j`**: for `N ≥ 2`, every level `j` and all points `x, y`,
`∑_n φ_{j+1,n}(x) φ_{j+1,n}(y) = ∑_k φ_{j,k}(x) φ_{j,k}(y) + ∑_k ψ_{j,k}(x) ψ_{j,k}(y)`: the kernel
of `P_{j+1}` is the kernel of `P_j` plus the kernel of the wavelets of level `j`. As functions of
`x`, the two sums on the right are expansions of level `j` with the coefficients
`φ_{j,k}(y) = ∑_n (c_{n-2k}/√2) φ_{j+1,n}(y)` and `ψ_{j,k}(y) = ∑_n (g_{n-2k}/√2) φ_{j+1,n}(y)`
(`Daubechies.scaled_eq_expand`, `Daubechies.waveletScaled_eq_expand`), hence expansions of level
`j + 1`, and perfect reconstruction (`Daubechies.refineCoeff_add_waveletRefineCoeff`) with
`a_n = φ_{j+1,n}(y)` adds their coefficients up to `a`. -/
theorem tsum_scaled_mul_scaled_succ (hN : 2 ≤ N) (j : ℕ) (x y : ℝ) :
    ∑' n : ℤ, scaled m (j + 1) n x * scaled m (j + 1) n y =
      ∑' k : ℤ, scaled m j k x * scaled m j k y +
        ∑' k : ℤ, waveletScaled m j k x * waveletScaled m j k y := by
  have hc : (fun n => scaled m (j + 1) n y) = fun n =>
      refineCoeff m (fun k => scaled m j k y) n +
        waveletRefineCoeff m (fun k => waveletScaled m j k y) n := by
    funext n
    have hb : (fun k => scaled m j k y) = fun k =>
        ∑' i, ((coeff m (i - 2 * k) / √2 : ℝ) : ℂ) * scaled m (j + 1) i y :=
      funext fun k => scaled_eq_expand m hN j k y
    have hb' : (fun k => waveletScaled m j k y) = fun k =>
        ∑' i, ((dualCoeff m (i - 2 * k) / √2 : ℝ) : ℂ) * scaled m (j + 1) i y :=
      funext fun k => waveletScaled_eq_expand m j k y
    rw [hb, hb']
    exact (refineCoeff_add_waveletRefineCoeff m (fun i => scaled m (j + 1) i y) n).symm
  have h1 : ∑' k : ℤ, scaled m j k x * scaled m j k y =
      expand (scalingFun m) j (fun k => scaled m j k y) x :=
    tsum_congr fun k => mul_comm _ _
  have h2 : ∑' k : ℤ, waveletScaled m j k x * waveletScaled m j k y =
      expand (wavelet m) j (fun k => waveletScaled m j k y) x :=
    tsum_congr fun k => mul_comm _ _
  rw [h1, h2, expand_eq_expand_succ m hN j _ x, expand_wavelet_eq_expand_succ m hN j _ x,
    ← expand_add (fun _ hz => scalingFun_eq_zero m hN hz), ← hc]
  exact tsum_congr fun n => mul_comm _ _

/-- **Products of generators of level `1`**: `g_{1,n}(x) g_{1,n}(y) = 2 g(2x - n) g(2y - n)` for
every `g : ℝ → ℂ`, `n ∈ ℤ` and `x, y ∈ ℝ`, since `2^(1/2) 2^(1/2) = 2`
(`ofReal_two_rpow_half_mul_self`). -/
theorem scaledFun_one_mul_scaledFun_one (g : ℝ → ℂ) (n : ℤ) (x y : ℝ) :
    scaledFun g 1 n x * scaledFun g 1 n y = 2 * (g (2 * x - n) * g (2 * y - n)) := by
  have h := ofReal_two_rpow_half_mul_self 1
  rw [pow_one] at h
  calc scaledFun g 1 n x * scaledFun g 1 n y
      = ((((2 : ℝ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) * (((2 : ℝ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ)) *
          (g (2 ^ 1 * x - n) * g (2 ^ 1 * y - n)) := by
        rw [scaledFun, scaledFun]
        ring
    _ = 2 * (g (2 * x - n) * g (2 * y - n)) := by rw [h, pow_one]

/-- **The kernel identity**: for `N ≥ 2` and all `x, y ∈ ℝ`, the kernel
`K(x, y) = ∑_k φ(x - k) φ(y - k)` of the projection `P_0` satisfies
`2 K(2x, 2y) = K(x, y) + ∑_k ψ(x - k) ψ(y - k)`. This is the level `j = 0` of
`Daubechies.tsum_scaled_mul_scaled_succ`, with `φ_{0,k} = φ(· - k)` (`Daubechies.scaledFun_zero`)
and `φ_{1,n}(x) φ_{1,n}(y) = 2 φ(2x - n) φ(2y - n)`
(`Daubechies.scaledFun_one_mul_scaledFun_one`). -/
theorem kernel_succ (hN : 2 ≤ N) (x y : ℝ) :
    2 * ∑' n : ℤ, scalingFun m (2 * x - n) * scalingFun m (2 * y - n) =
      ∑' k : ℤ, scalingFun m (x - k) * scalingFun m (y - k) +
        ∑' k : ℤ, wavelet m (x - k) * wavelet m (y - k) := by
  have h := tsum_scaled_mul_scaled_succ m hN 0 x y
  simp only [scaled, waveletScaled, zero_add, scaledFun_zero, scaledFun_one_mul_scaledFun_one,
    tsum_mul_left] at h
  exact h

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The block identity on `L_p`**: for `N ≥ 2`, `1 ≤ p < ∞`, every level `j` and every
`f ∈ L_p`, `P_{j+1} f - P_j f` is the class of the wavelet part
`∑_k ⟨f, ψ_{j,k}⟩ ψ_{j,k}` (`Daubechies.detailFun`, `Daubechies.projFun_succ_eq_add`). -/
theorem proj_succ_sub_proj (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure ℝ)) :
    proj m p hN hp (j + 1) f - proj m p hN hp j f =
      (memLp_detailFun m hN Fact.out hp (Lp.memLp f) j).toLp _ := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (proj m p hN hp (j + 1) f) (proj m p hN hp j f),
    proj_apply_ae m hN hp (j + 1) f, proj_apply_ae m hN hp j f,
    MemLp.coeFn_toLp (memLp_detailFun m hN Fact.out hp (Lp.memLp f) j)] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4,
    projFun_succ_eq_add m hN ((Lp.memLp f).locallyIntegrable Fact.out) j x, add_sub_cancel_left]

/-- **The norm of a block**: `‖P_{j+1} f - P_j f‖_p = ‖∑_k ⟨f, ψ_{j,k}⟩ ψ_{j,k}‖_p` for every
`f ∈ L_p` and every level `j` (`Daubechies.proj_succ_sub_proj`). -/
theorem enorm_proj_succ_sub_proj (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖proj m p hN hp (j + 1) f - proj m p hN hp j f‖ₑ = eLpNorm (detailFun m j f) p volume := by
  rw [proj_succ_sub_proj, Lp.eNorm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]

/-- **The norm of a projection**: `‖P_j f‖_p = ‖∑_k ⟨f, φ_{j,k}⟩ φ_{j,k}‖_p` for every
`f ∈ L_p` and every level `j` (`Daubechies.proj_apply_ae`). -/
theorem enorm_proj_eq (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖proj m p hN hp j f‖ₑ = eLpNorm (projFun m j f) p volume := by
  rw [Lp.eNorm_def, eLpNorm_congr_ae (proj_apply_ae m hN hp j f)]

/-- **The norms of the blocks through the wavelet coefficients**: for `N ≥ 2` and `1 ≤ p < ∞`
there are constants `K, M < ∞` such that for every `f ∈ L_p` and every level `j`
`2^(j(1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p} ≤ K ‖P_{j+1} f - P_j f‖_p` and
`‖P_{j+1} f - P_j f‖_p ≤ M 2^(j(1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p}`. The block is the wavelet
expansion with the coefficients `⟨f, ψ_{j,k}⟩` (`Daubechies.enorm_proj_succ_sub_proj`), so the
lower and the upper stability of the expansions (`Daubechies.lqNorm_le_eLpNorm_expand`, which
uses the orthonormality of the translates of `ψ`, and `Daubechies.eLpNorm_expand_le`) give the
constants `K = Daubechies.coeffConst` and `M = Daubechies.expandConst` for `g = ψ`. -/
theorem enorm_block_equiv (hN : 2 ≤ N) (hp : p ≠ ∞) :
    ∃ K M : ℝ≥0∞, K ≠ ∞ ∧ M ≠ ∞ ∧ ∀ (f : Lp ℂ p (volume : Measure ℝ)) (j : ℕ),
      dyadicWeight (1 / 2 - 1 / p.toReal) j *
          ENNReal.lqNorm p (fun k : ℤ => ‖coeffFun (wavelet m) j f k‖ₑ) ≤
        K * ‖proj m p hN hp (j + 1) f - proj m p hN hp j f‖ₑ ∧
      ‖proj m p hN hp (j + 1) f - proj m p hN hp j f‖ₑ ≤
        M * (dyadicWeight (1 / 2 - 1 / p.toReal) j *
          ENNReal.lqNorm p (fun k : ℤ => ‖coeffFun (wavelet m) j f k‖ₑ)) := by
  refine ⟨coeffConst (wavelet m) (1 - N) N p, expandConst (wavelet m) (1 - N) N p,
    coeffConst_ne_top _ _ (memLp_wavelet m hN _), expandConst_ne_top _ _ (memLp_wavelet m hN p),
    fun f j => ⟨?_, ?_⟩⟩
  · rw [enorm_proj_succ_sub_proj]
    exact lqNorm_le_eLpNorm_expand (continuous_wavelet m hN) (fun _ hx => wavelet_eq_zero m hN hx)
      (integral_wavelet_translate_mul_conj_translate m hN) Fact.out hp j _
  · rw [enorm_proj_succ_sub_proj, expandConst, ← mul_assoc]
    exact eLpNorm_expand_le (continuous_wavelet m hN).aestronglyMeasurable
      (fun _ hx => wavelet_eq_zero m hN hx) Fact.out hp j _

/-- **The norms of the projections through the scaling coefficients**: for `N ≥ 2` and
`1 ≤ p < ∞` there are constants `K, M < ∞` such that for every `f ∈ L_p` and every level `j`
`2^(j(1/2 - 1/p)) ‖(⟨f, φ_{j,k}⟩)_k‖_{ℓ_p} ≤ K ‖P_j f‖_p` and
`‖P_j f‖_p ≤ M 2^(j(1/2 - 1/p)) ‖(⟨f, φ_{j,k}⟩)_k‖_{ℓ_p}`, by the stability of the expansions
(`Daubechies.lqNorm_le_eLpNorm_expand`, `Daubechies.eLpNorm_expand_le`) for `g = φ`. -/
theorem enorm_proj_equiv (hN : 2 ≤ N) (hp : p ≠ ∞) :
    ∃ K M : ℝ≥0∞, K ≠ ∞ ∧ M ≠ ∞ ∧ ∀ (f : Lp ℂ p (volume : Measure ℝ)) (j : ℕ),
      dyadicWeight (1 / 2 - 1 / p.toReal) j *
          ENNReal.lqNorm p (fun k : ℤ => ‖coeffFun (scalingFun m) j f k‖ₑ) ≤
        K * ‖proj m p hN hp j f‖ₑ ∧
      ‖proj m p hN hp j f‖ₑ ≤
        M * (dyadicWeight (1 / 2 - 1 / p.toReal) j *
          ENNReal.lqNorm p (fun k : ℤ => ‖coeffFun (scalingFun m) j f k‖ₑ)) := by
  refine ⟨coeffConst (scalingFun m) 0 (2 * N - 1) p, expandConst (scalingFun m) 0 (2 * N - 1) p,
    coeffConst_ne_top _ _ (memLp_scalingFun m hN _),
    expandConst_ne_top _ _ (memLp_scalingFun m hN p), fun f j => ⟨?_, ?_⟩⟩
  · rw [enorm_proj_eq]
    exact lqNorm_le_eLpNorm_expand (continuous_scalingFun m hN)
      (fun _ hx => scalingFun_eq_zero m hN hx)
      (integral_scalingFun_translate_mul_conj_translate m hN) Fact.out hp j _
  · rw [enorm_proj_eq, expandConst, ← mul_assoc]
    exact eLpNorm_expand_le (continuous_scalingFun m hN).aestronglyMeasurable
      (fun _ hx => scalingFun_eq_zero m hN hx) Fact.out hp j _

/-- **The norm of the projection of level `0` through the scaling coefficients**: for `N ≥ 2` and
`1 ≤ p < ∞` there are constants `K, M < ∞` with `‖(⟨f, φ_{0,k}⟩)_k‖_{ℓ_p} ≤ K ‖P_0 f‖_p` and
`‖P_0 f‖_p ≤ M ‖(⟨f, φ_{0,k}⟩)_k‖_{ℓ_p}` for every `f ∈ L_p`, where `φ_{0,k} = φ(· - k)`: the level
`j = 0` of `Daubechies.enorm_proj_equiv`. -/
theorem enorm_proj_zero_equiv (hN : 2 ≤ N) (hp : p ≠ ∞) :
    ∃ K M : ℝ≥0∞, K ≠ ∞ ∧ M ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure ℝ),
      ENNReal.lqNorm p (fun k : ℤ => ‖coeffFun (scalingFun m) 0 f k‖ₑ) ≤
        K * ‖proj m p hN hp 0 f‖ₑ ∧
      ‖proj m p hN hp 0 f‖ₑ ≤
        M * ENNReal.lqNorm p (fun k : ℤ => ‖coeffFun (scalingFun m) 0 f k‖ₑ) := by
  obtain ⟨K, M, hK, hM, hKM⟩ := enorm_proj_equiv m hN hp
  refine ⟨K, M, hK, hM, fun f => ?_⟩
  simpa only [ENNReal.dyadicWeight_zero_right, one_mul] using hKM f 0

end Lp

/-! ### Vanishing moments -/

/-- For `N ≥ 2`, `l ∈ ℕ` and `k ∈ ℤ`, the function `x ↦ x^l φ(2x - k)` is integrable: it is
continuous and vanishes outside `[k/2, (k + 2N - 1)/2]` (`Daubechies.scalingFun_eq_zero`). -/
theorem integrable_pow_mul_scalingFun_two_mul_sub (hN : 2 ≤ N) (l : ℕ) (k : ℤ) :
    Integrable fun x : ℝ => (x : ℂ) ^ l * scalingFun m (2 * x - k) := by
  have hφ := continuous_scalingFun m hN
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop)
    (HasCompactSupport.intro (isCompact_Icc (a := (k : ℝ) / 2) (b := (k + (2 * N - 1)) / 2))
      fun x hx => ?_)
  rw [scalingFun_eq_zero m hN fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩, mul_zero]

/-- For `N ≥ 2` and `i ∈ ℕ`, the function `y ↦ y^i φ(y)` is integrable: it is continuous with
compact support (`Daubechies.hasCompactSupport_scalingFun`). -/
theorem integrable_pow_mul_scalingFun (hN : 2 ≤ N) (i : ℕ) :
    Integrable fun y : ℝ => (y : ℂ) ^ i * scalingFun m y := by
  have hφ := continuous_scalingFun m hN
  exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
    (hasCompactSupport_scalingFun m hN).mul_left

/-- **The moments of a dilated translate of the scaling function**: for `N ≥ 2`, `l ∈ ℕ` and
`k ∈ ℤ`, `∫ x^l φ(2x - k) dx = 2^(-(l+1)) ∑_{i=0}^{l} k^(l-i) C(l, i) ∫ y^i φ(y) dy`. The
substitution `u = 2x` (Mathlib's `MeasureTheory.Measure.integral_comp_mul_left`) and the
translation `u = y + k` give `(1/2) ∫ ((y + k)/2)^l φ(y) dy`, and the binomial theorem (Mathlib's
`add_pow`) expands `(y + k)^l`. -/
theorem integral_pow_mul_scalingFun_two_mul_sub (hN : 2 ≤ N) (l : ℕ) (k : ℤ) :
    ∫ x : ℝ, (x : ℂ) ^ l * scalingFun m (2 * x - k) =
      (1 / 2) ^ (l + 1) * ∑ i ∈ Finset.range (l + 1),
        (k : ℂ) ^ (l - i) * (l.choose i : ℂ) * ∫ y : ℝ, (y : ℂ) ^ i * scalingFun m y := by
  have h1 : ∫ x : ℝ, (x : ℂ) ^ l * scalingFun m (2 * x - k) =
      1 / 2 * ∫ u : ℝ, ((u / 2 : ℝ) : ℂ) ^ l * scalingFun m (u - k) := by
    have h := Measure.integral_comp_mul_left
      (fun u : ℝ => ((u / 2 : ℝ) : ℂ) ^ l * scalingFun m (u - k)) 2
    simp only [mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] at h
    rw [h, abs_of_pos (by norm_num), Complex.real_smul]
    norm_num
  have h2 : ∫ u : ℝ, ((u / 2 : ℝ) : ℂ) ^ l * scalingFun m (u - k) =
      ∫ y : ℝ, (((y + k) / 2 : ℝ) : ℂ) ^ l * scalingFun m y := by
    rw [← integral_add_right_eq_self _ (k : ℝ)]
    simp only [add_sub_cancel_right]
  have h3 : ∀ y : ℝ, (((y + k) / 2 : ℝ) : ℂ) ^ l * scalingFun m y =
      ∑ i ∈ Finset.range (l + 1), (1 / 2) ^ l * ((k : ℂ) ^ (l - i) * (l.choose i : ℂ)) *
        ((y : ℂ) ^ i * scalingFun m y) := fun y => by
    rw [show (((y + k) / 2 : ℝ) : ℂ) = (1 / 2) * ((y : ℂ) + (k : ℂ)) by push_cast; ring, mul_pow,
      add_pow, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2]
  simp_rw [h3]
  rw [integral_finsetSum _ fun i _ => (integrable_pow_mul_scalingFun m hN i).const_mul _]
  simp_rw [integral_const_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The moments of the dual filter, as complex numbers**: for `s < N`,
`∑_{k = 2 - 2N}^{1} g_k k^s = 0` (`Daubechies.sum_dualCoeff_mul_pow`,
`Daubechies.finsum_eq_sum_Icc_of_dualCoeff`). -/
theorem sum_dualCoeff_mul_pow_eq_zero {s : ℕ} (hs : s < N) :
    ∑ k ∈ Finset.Icc (2 - 2 * (N : ℤ)) 1, (dualCoeff m k : ℂ) * (k : ℂ) ^ s = 0 := by
  have h := sum_dualCoeff_mul_pow m hs
  rw [finsum_eq_sum_Icc_of_dualCoeff m _ fun k hk => by rw [hk, zero_mul]] at h
  exact_mod_cast h

/-- **Vanishing moments of the wavelet**: for `N ≥ 2` and `l < N`, `∫ x^l ψ(x) dx = 0`. By
`Daubechies.integral_pow_mul_scalingFun_two_mul_sub`,
`∫ x^l ψ(x) dx = 2^(-(l+1)) ∑_{i ≤ l} C(l, i) (∫ y^i φ(y) dy) ∑_k g_k k^(l-i)`, and every inner sum
vanishes since `l - i < N` (`Daubechies.sum_dualCoeff_mul_pow_eq_zero`). -/
theorem vanishing_moments (hN : 2 ≤ N) {l : ℕ} (hl : l < N) :
    ∫ x : ℝ, (x : ℂ) ^ l * wavelet m x = 0 := by
  have h1 : ∀ x : ℝ, (x : ℂ) ^ l * wavelet m x = ∑ k ∈ Finset.Icc (2 - 2 * (N : ℤ)) 1,
      (dualCoeff m k : ℂ) * ((x : ℂ) ^ l * scalingFun m (2 * x - k)) := fun x => by
    rw [wavelet, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [h1]
  rw [integral_finsetSum _ fun k _ =>
    (integrable_pow_mul_scalingFun_two_mul_sub m hN l k).const_mul _]
  simp_rw [integral_const_mul, integral_pow_mul_scalingFun_two_mul_sub m hN, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hs : l - i < N := by omega
  calc ∑ k ∈ Finset.Icc (2 - 2 * (N : ℤ)) 1, (dualCoeff m k : ℂ) * ((1 / 2) ^ (l + 1) *
        ((k : ℂ) ^ (l - i) * (l.choose i : ℂ) * ∫ y : ℝ, (y : ℂ) ^ i * scalingFun m y))
      = (1 / 2) ^ (l + 1) * (l.choose i : ℂ) * (∫ y : ℝ, (y : ℂ) ^ i * scalingFun m y) *
          ∑ k ∈ Finset.Icc (2 - 2 * (N : ℤ)) 1, (dualCoeff m k : ℂ) * (k : ℂ) ^ (l - i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by rw [sum_dualCoeff_mul_pow_eq_zero m hs, mul_zero]

end Daubechies
