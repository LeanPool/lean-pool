/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Expansion
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Orthonormality

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The scaling functions of every level

For a Daubechies mask of order `N ≥ 2` with filter coefficients `c_k` (`Daubechies.coeff`) and
scaling function `φ` (`Daubechies.scalingFun`), the functions of the multiresolution analysis are

`φ_{j,k}(x) = 2^(j/2) φ(2^j x - k)`, `j ∈ ℕ`, `k ∈ ℤ` (`Daubechies.scaled`),

the generic generators `Daubechies.scaledFun` of
`FunctionSpaces.Wavelets.Examples.Daubechies.Expansion` for `g = φ`. The scaling function is
continuous and vanishes outside `[0, 2N - 1]` (`Daubechies.continuous_scalingFun`,
`Daubechies.scalingFun_eq_zero`), so every result of that file applies with `a = 0` and
`b = 2N - 1`. This file adds what is particular to `φ`:

* `φ_{j,k}` vanishes outside `[k/2^j, (k + 2N - 1)/2^j]` (`Daubechies.scaled_eq_zero`);
* **orthonormality at every level**, `∫ φ_{j,k} conj φ_{j,l} = δ_{kl}`
  (`Daubechies.integral_scaled_mul_conj`), from the orthonormality of the integer translates
  (`Daubechies.integral_scalingFun_translate_mul_conj_translate`), and with it coefficient
  recovery `⟨∑_l c_l φ_{j,l}, φ_{j,k}⟩ = c_k` (`Daubechies.coeffFun_expand_scalingFun`);
* **the refinement relation between levels**,
  `φ_{j,k} = ∑_{i=0}^{2N-1} (c_i/√2) φ_{j+1,2k+i}` (`Daubechies.scaled_refine`), the refinement
  equation `φ(y) = ∑_i c_i φ(2y - i)` (`Daubechies.scalingFun_refine`) at `y = 2^j x - k`; as an
  expansion of level `j + 1` it reads `φ_{j,k} = ∑_{n ∈ ℤ} (c_{n-2k}/√2) φ_{j+1,n}`
  (`Daubechies.scaled_eq_expand`).
-/

@[expose] public section

open MeasureTheory
open scoped ComplexConjugate

namespace Daubechies

variable {N : ℕ} (m : Mask N)

/-- **The functions `φ_{j,k}` of the multiresolution analysis**:
`φ_{j,k}(x) = 2^(j/2) φ(2^j x - k)` for the scaling function `φ` (`Daubechies.scalingFun`), the
level `j ∈ ℕ` and the position `k ∈ ℤ`; this is the generic `Daubechies.scaledFun` for `g = φ`.
-/
noncomputable abbrev scaled (j : ℕ) (k : ℤ) : ℝ → ℂ := scaledFun (scalingFun m) j k

/-- **Support of `φ_{j,k}`**: for `N ≥ 2`, `φ_{j,k}(x) = 0` for every `x` outside
`[k/2^j, (k + 2N - 1)/2^j]`, since `φ` vanishes outside `[0, 2N - 1]`
(`Daubechies.scalingFun_eq_zero`, `Daubechies.supportWindow_eq_Icc`). -/
theorem scaled_eq_zero (hN : 2 ≤ N) {j : ℕ} {k : ℤ} {x : ℝ}
    (hx : x ∉ Set.Icc ((k : ℝ) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j)) : scaled m j k x = 0 :=
  scaledFun_eq_zero (fun _ hy => scalingFun_eq_zero m hN hy)
    (by rwa [supportWindow_eq_Icc, add_zero])

/-- **Orthonormality at every level**: for `N ≥ 2`, every level `j` and all positions `k, l`,
`∫ φ_{j,k}(x) conj φ_{j,l}(x) dx` is `1` for `k = l` and `0` otherwise
(`Daubechies.integral_scaledFun_mul_conj` and the orthonormality of the integer translates,
`Daubechies.integral_scalingFun_translate_mul_conj_translate`). -/
theorem integral_scaled_mul_conj (hN : 2 ≤ N) (j : ℕ) (k l : ℤ) :
    ∫ x, scaled m j k x * conj (scaled m j l x) = if k = l then 1 else 0 :=
  integral_scaledFun_mul_conj (integral_scalingFun_translate_mul_conj_translate m hN) j k l

/-- **Coefficient recovery for the scaling function**: for `N ≥ 2`, every level `j`, every
coefficient sequence `c : ℤ → ℂ` and every `k ∈ ℤ`, `⟨∑_l c_l φ_{j,l}, φ_{j,k}⟩ = c_k`
(`Daubechies.coeffFun_expand` for `g = φ`, with `a = 0` and `b = 2N - 1`). -/
theorem coeffFun_expand_scalingFun (hN : 2 ≤ N) (j : ℕ) (c : ℤ → ℂ) (k : ℤ) :
    coeffFun (scalingFun m) j (expand (scalingFun m) j c) k = c k :=
  coeffFun_expand (continuous_scalingFun m hN) (fun _ hx => scalingFun_eq_zero m hN hx)
    (integral_scalingFun_translate_mul_conj_translate m hN) j c k

/-- `2^((j+1)/2) = 2^(j/2) √2` for every `j ∈ ℕ`: the normalising factors of two consecutive
levels differ by the factor `√2`. -/
theorem two_rpow_succ_div_two (j : ℕ) :
    (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) / 2) = (2 : ℝ) ^ ((j : ℝ) / 2) * √2 := by
  rw [Nat.cast_succ, add_div, Real.rpow_add two_pos, Real.sqrt_eq_rpow]

/-- **The refinement relation between levels**: for `N ≥ 2`, every level `j`, position `k` and
point `x`, `φ_{j,k}(x) = ∑_{i=0}^{2N-1} (c_i/√2) φ_{j+1,2k+i}(x)`. This is the refinement
equation `φ(y) = ∑_i c_i φ(2y - i)` (`Daubechies.scalingFun_refine`) at `y = 2^j x - k`, with
`2(2^j x - k) - i = 2^(j+1) x - (2k + i)` and `2^(j/2) = 2^((j+1)/2)/√2`
(`Daubechies.two_rpow_succ_div_two`). -/
theorem scaled_refine (hN : 2 ≤ N) (j : ℕ) (k : ℤ) (x : ℝ) :
    scaled m j k x = ∑ i ∈ Finset.range (2 * N),
      ((coeff m i / √2 : ℝ) : ℂ) * scaled m (j + 1) (2 * k + i) x := by
  simp only [scaled, scaledFun]
  rw [scalingFun_refine m hN (2 ^ j * x - k), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : (2 : ℝ) * ((2 : ℝ) ^ j * x - k) - i = 2 ^ (j + 1) * x - ((2 * k + i : ℤ) : ℝ) := by
    push_cast
    ring
  have hs : (√2 : ℝ) ≠ 0 := by positivity
  have hc : (2 : ℝ) ^ ((j : ℝ) / 2) * coeff m i =
      coeff m i / √2 * ((2 : ℝ) ^ ((j : ℝ) / 2) * √2) := by
    field_simp
  rw [h2, two_rpow_succ_div_two, ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, hc]

/-- **`φ_{j,k}` is an expansion of level `j + 1`**: for `N ≥ 2`, every level `j`, position `k`
and point `x`, `φ_{j,k}(x) = ∑_{n ∈ ℤ} (c_{n-2k}/√2) φ_{j+1,n}(x)`. This is the refinement
relation `Daubechies.scaled_refine` after the substitution `n = 2k + i`; the filter coefficients
`c_i` vanish outside `0 ≤ i ≤ 2N - 1` (`Daubechies.coeff_eq_zero`). -/
theorem scaled_eq_expand (hN : 2 ≤ N) (j : ℕ) (k : ℤ) (x : ℝ) :
    scaled m j k x =
      expand (scalingFun m) (j + 1) (fun n => ((coeff m (n - 2 * k) / √2 : ℝ) : ℂ)) x := by
  rw [scaled_refine m hN, expand, ← (Equiv.addLeft (2 * k)).tsum_eq]
  simp only [Equiv.coe_addLeft, add_sub_cancel_left]
  rw [tsum_eq_sum (s := (Finset.range (2 * N)).map Nat.castEmbedding) ?_, Finset.sum_map]
  · rfl
  · intro i hi
    have h0 : coeff m i = 0 := by
      refine coeff_eq_zero m ?_
      by_contra h
      push Not at h
      exact hi (Finset.mem_map.2 ⟨i.toNat, Finset.mem_range.2 (by omega), by simp [h.1]⟩)
    rw [h0, zero_div, Complex.ofReal_zero, zero_mul]

end Daubechies
