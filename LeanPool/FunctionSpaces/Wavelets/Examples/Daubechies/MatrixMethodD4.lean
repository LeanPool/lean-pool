/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.D4
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.MatrixMethod
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.ScalingMoments

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Hölder exponent of D4 by the matrix method

The scaling function `φ` of the Daubechies mask D4 (`Daubechies.d4`, filter coefficients
`c_0, …, c_3 = (1 + √3)/4, (3 + √3)/4, (3 - √3)/4, (1 - √3)/4`) is Hölder continuous with every
exponent `0 ≤ a ≤ α = 2 - log₂(1 + √3)`: there is `K` with `‖φ(x) - φ(y)‖ ≤ K |x - y|^a` for all
`x, y ∈ ℝ` (`Daubechies.holder_d4`), and `α > 0.55`
(`Daubechies.two_sub_logb_two_one_add_sqrt_three_gt`). The exponent `α ≈ 0.5500` is the Hölder
exponent of D4 determined by Daubechies–Lagarias; the proof is their matrix method in a scalar
form, with the dyadic descent of `FunctionSpaces.Wavelets.Examples.Daubechies.MatrixMethod`.

* **The vector of translates.** `φ` vanishes outside `(0, 3)` (`Daubechies.scalingFun_d4_eq_zero`),
  so for `x ∈ [0, 1)` the vector `v(x) = (φ(x), φ(x + 1), φ(x + 2))` carries all values of `φ`.
  On the half `[d/2, (d+1)/2)` the refinement equation `φ(x) = ∑_k c_k φ(2x - k)` reads
  `v(x) = T_d v(2x - d)` with `(T_d)_{ij} = c_{2i+d-j}` (`Daubechies.scalingFun_d4_left`,
  `Daubechies.scalingFun_d4_add_one_left`, `Daubechies.scalingFun_d4_add_two_left` for `d = 0`,
  `Daubechies.scalingFun_d4_right`, `Daubechies.scalingFun_d4_add_one_right`,
  `Daubechies.scalingFun_d4_add_two_right` for `d = 1`), and the partition of unity gives
  `φ(x) + φ(x + 1) + φ(x + 2) = 1` (`Daubechies.scalingFun_d4_add_add_eq_one`), that is
  `ℓ_0(v(x)) = 1` for the functional `ℓ_0 = (1, 1, 1)`.
* **Two scalar recursions.** The functions `A(x) = φ(x + 1) + 2 φ(x + 2)` (`Daubechies.d4A`, the
  functional `ℓ_1 = (0, 1, 2)` applied to `v(x)`) and `B(x) = φ(x) + A(x)` (`Daubechies.d4B`)
  satisfy, with `u = 2x - d`,
  `A(x) = A(u)/2 + (μ - d)/2` for `μ = (3 - √3)/2` (`Daubechies.d4A_left`, `Daubechies.d4A_right`),
  `B(x) = a_0 + β_0 A(u) + λ_0 B(u)` for `d = 0` and `B(x) = a_1 + λ_1 B(u)` for `d = 1`, where
  `a_0 = (3 - √3)/4`, `a_1 = (3 + √3)/4`, `β_0 = λ_1 = (1 - √3)/4` and `λ_0 = (1 + √3)/4`
  (`Daubechies.d4B_left`, `Daubechies.d4B_right`). In matrix terms, `ℓ_0` is a common left
  eigenvector of `T_0` and `T_1` for the eigenvalue `1`, and on differences, which lie in the
  kernel of `ℓ_0`, both matrices act triangularly with diagonal `(1/2, λ_d)`.
* **Dyadic descent.** The differences of `A` and `B` satisfy the halving and the triangular
  recursion with `ρ = (1 + √3)/4` and `β = ρ - 1/2 = (√3 - 1)/4` (`Daubechies.norm_d4A_sub_le`,
  `Daubechies.norm_d4B_sub_le`). For a bound `‖φ‖ ≤ M`, the descent gives
  `‖A(x) - A(y)‖ ≤ 6M/2^n` and `‖B(x) - B(y)‖ ≤ 14 M ρ^n` on every dyadic interval of level `n`
  in `[0, 1)`. Since `φ(x + i)` is affine in `(A(x), B(x))`
  (`Daubechies.norm_scalingFun_d4_sub_le`), `‖φ(x + i) - φ(y + i)‖ ≤ 28 M ρ^n` there
  (`Daubechies.norm_scalingFun_d4_sub_le_dyadic`), and `ρ = 2^(-α)` turns these bounds into the
  Hölder estimate.
-/

@[expose] public section

open Set
open scoped Real

namespace Daubechies

/-! ### The scaling function of D4 on the unit interval -/

section D4

/-- `1 < √3`, since `1² < 3` (Mathlib's `Real.lt_sqrt`). -/
theorem one_lt_sqrt_three : 1 < √3 := by
  rw [Real.lt_sqrt zero_le_one]
  norm_num

/-- **The support of the D4 scaling function**: `φ(x) = 0` for every `x ∉ (0, 3)`
(`Daubechies.scalingFun_eq_zero_of_notMem_Ioo` with `2N - 1 = 3`). -/
theorem scalingFun_d4_eq_zero {x : ℝ} (hx : x ∉ Ioo (0 : ℝ) 3) : scalingFun d4 x = 0 :=
  scalingFun_eq_zero_of_notMem_Ioo d4 le_rfl
    (by rwa [show (2 : ℝ) * ((2 : ℕ) : ℝ) - 1 = 3 by norm_num])

/-- **The partition of unity for D4 on `[0, 1)`**: `φ(x) + φ(x + 1) + φ(x + 2) = 1` for every
`x ∈ [0, 1)`. In `∑_{k ∈ ℤ} φ(x - k) = 1` (`Daubechies.sum_scalingFun_translate`) only the
indices `k = 0, -1, -2` contribute, since `φ` vanishes outside `(0, 3)`. -/
theorem scalingFun_d4_add_add_eq_one {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    scalingFun d4 x + scalingFun d4 (x + 1) + scalingFun d4 (x + 2) = 1 := by
  have h := sum_scalingFun_translate d4 le_rfl x
  rw [tsum_eq_sum (s := ({0, -1, -2} : Finset ℤ)) fun k hk => scalingFun_d4_eq_zero fun hk' =>
    hk ?_] at h
  · simpa [add_assoc] using h
  · have h1 : (k : ℝ) < 1 := by linarith [hk'.1, hx.2]
    have h2 : (-3 : ℝ) < k := by linarith [hk'.2, hx.1]
    have h1' : k < 1 := by exact_mod_cast h1
    have h2' : -3 < k := by exact_mod_cast h2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- **The refinement equation of D4**, written out:
`φ(x) = c_0 φ(2x) + c_1 φ(2x - 1) + c_2 φ(2x - 2) + c_3 φ(2x - 3)` for every `x ∈ ℝ`
(`Daubechies.scalingFun_refine` with `2N = 4`). -/
theorem scalingFun_d4_refine (x : ℝ) :
    scalingFun d4 x = (coeff d4 0 : ℂ) * scalingFun d4 (2 * x) +
      (coeff d4 1 : ℂ) * scalingFun d4 (2 * x - 1) + (coeff d4 2 : ℂ) * scalingFun d4 (2 * x - 2) +
      (coeff d4 3 : ℂ) * scalingFun d4 (2 * x - 3) := by
  rw [scalingFun_refine d4 le_rfl x]
  simp [Finset.sum_range_succ]

/-- **The refinement equation on the left half**: for `x ∈ [0, 1/2)`, `φ(x) = c_0 φ(2x)`; the
other terms of `Daubechies.scalingFun_d4_refine` vanish since `2x - j < 0` for `j ≥ 1`. -/
theorem scalingFun_d4_left {x : ℝ} (hx : x ∈ Ico (0 : ℝ) (1 / 2)) :
    scalingFun d4 x = (coeff d4 0 : ℂ) * scalingFun d4 (2 * x) := by
  rw [scalingFun_d4_refine, scalingFun_d4_eq_zero (x := 2 * x - 1) fun h => by linarith [h.1, hx.2],
    scalingFun_d4_eq_zero (x := 2 * x - 2) fun h => by linarith [h.1, hx.2],
    scalingFun_d4_eq_zero (x := 2 * x - 3) fun h => by linarith [h.1, hx.2]]
  ring

/-- **The refinement equation on the left half**, second translate: for `x ∈ [0, 1/2)`,
`φ(x + 1) = c_2 φ(2x) + c_1 φ(2x + 1) + c_0 φ(2x + 2)`; the term `c_3 φ(2x - 1)` vanishes. -/
theorem scalingFun_d4_add_one_left {x : ℝ} (hx : x ∈ Ico (0 : ℝ) (1 / 2)) :
    scalingFun d4 (x + 1) = (coeff d4 2 : ℂ) * scalingFun d4 (2 * x) +
      (coeff d4 1 : ℂ) * scalingFun d4 (2 * x + 1) +
      (coeff d4 0 : ℂ) * scalingFun d4 (2 * x + 2) := by
  rw [scalingFun_d4_refine, show 2 * (x + 1) = 2 * x + 2 by ring,
    show 2 * x + 2 - 1 = 2 * x + 1 by ring, show 2 * x + 2 - 2 = 2 * x by ring,
    show 2 * x + 2 - 3 = 2 * x - 1 by ring,
    scalingFun_d4_eq_zero (x := 2 * x - 1) fun h => by linarith [h.1, hx.2]]
  ring

/-- **The refinement equation on the left half**, third translate: for `x ∈ [0, 1/2)`,
`φ(x + 2) = c_3 φ(2x + 1) + c_2 φ(2x + 2)`; the terms with `φ(2x + 3)` and `φ(2x + 4)` vanish. -/
theorem scalingFun_d4_add_two_left {x : ℝ} (hx : x ∈ Ico (0 : ℝ) (1 / 2)) :
    scalingFun d4 (x + 2) = (coeff d4 3 : ℂ) * scalingFun d4 (2 * x + 1) +
      (coeff d4 2 : ℂ) * scalingFun d4 (2 * x + 2) := by
  rw [scalingFun_d4_refine, show 2 * (x + 2) = 2 * x + 4 by ring,
    show 2 * x + 4 - 1 = 2 * x + 3 by ring, show 2 * x + 4 - 2 = 2 * x + 2 by ring,
    show 2 * x + 4 - 3 = 2 * x + 1 by ring,
    scalingFun_d4_eq_zero (x := 2 * x + 4) fun h => by linarith [h.2, hx.1],
    scalingFun_d4_eq_zero (x := 2 * x + 3) fun h => by linarith [h.2, hx.1]]
  ring

/-- **The refinement equation on the right half**: for `x ∈ [1/2, 1)`,
`φ(x) = c_1 φ(2x - 1) + c_0 φ(2x)`; the terms with `φ(2x - 2)` and `φ(2x - 3)` vanish. -/
theorem scalingFun_d4_right {x : ℝ} (hx : x ∈ Ico (1 / 2 : ℝ) 1) :
    scalingFun d4 x = (coeff d4 1 : ℂ) * scalingFun d4 (2 * x - 1) +
      (coeff d4 0 : ℂ) * scalingFun d4 (2 * x) := by
  rw [scalingFun_d4_refine, scalingFun_d4_eq_zero (x := 2 * x - 2) fun h => by linarith [h.1, hx.2],
    scalingFun_d4_eq_zero (x := 2 * x - 3) fun h => by linarith [h.1, hx.2]]
  ring

/-- **The refinement equation on the right half**, second translate: for `x ∈ [1/2, 1)`,
`φ(x + 1) = c_3 φ(2x - 1) + c_2 φ(2x) + c_1 φ(2x + 1)`; the term `c_0 φ(2x + 2)` vanishes. -/
theorem scalingFun_d4_add_one_right {x : ℝ} (hx : x ∈ Ico (1 / 2 : ℝ) 1) :
    scalingFun d4 (x + 1) = (coeff d4 3 : ℂ) * scalingFun d4 (2 * x - 1) +
      (coeff d4 2 : ℂ) * scalingFun d4 (2 * x) +
      (coeff d4 1 : ℂ) * scalingFun d4 (2 * x + 1) := by
  rw [scalingFun_d4_refine, show 2 * (x + 1) = 2 * x + 2 by ring,
    show 2 * x + 2 - 1 = 2 * x + 1 by ring, show 2 * x + 2 - 2 = 2 * x by ring,
    show 2 * x + 2 - 3 = 2 * x - 1 by ring,
    scalingFun_d4_eq_zero (x := 2 * x + 2) fun h => by linarith [h.2, hx.1]]
  ring

/-- **The refinement equation on the right half**, third translate: for `x ∈ [1/2, 1)`,
`φ(x + 2) = c_3 φ(2x + 1)`; the other terms vanish since `2x + j ≥ 3` for `j ≥ 2`. -/
theorem scalingFun_d4_add_two_right {x : ℝ} (hx : x ∈ Ico (1 / 2 : ℝ) 1) :
    scalingFun d4 (x + 2) = (coeff d4 3 : ℂ) * scalingFun d4 (2 * x + 1) := by
  rw [scalingFun_d4_refine, show 2 * (x + 2) = 2 * x + 4 by ring,
    show 2 * x + 4 - 1 = 2 * x + 3 by ring, show 2 * x + 4 - 2 = 2 * x + 2 by ring,
    show 2 * x + 4 - 3 = 2 * x + 1 by ring,
    scalingFun_d4_eq_zero (x := 2 * x + 4) fun h => by linarith [h.2, hx.1],
    scalingFun_d4_eq_zero (x := 2 * x + 3) fun h => by linarith [h.2, hx.1],
    scalingFun_d4_eq_zero (x := 2 * x + 2) fun h => by linarith [h.2, hx.1]]
  ring

/-! ### The two scalar recursions -/

/-- **The first auxiliary function of the matrix method for D4**: `A(x) = φ(x + 1) + 2 φ(x + 2)`.
For `x ∈ [0, 1)` it is the functional `ℓ_1 = (0, 1, 2)` applied to the vector
`v(x) = (φ(x), φ(x + 1), φ(x + 2))` of Daubechies–Lagarias. -/
noncomputable def d4A (x : ℝ) : ℂ := scalingFun d4 (x + 1) + 2 * scalingFun d4 (x + 2)

/-- **The second auxiliary function of the matrix method for D4**:
`B(x) = φ(x) + A(x) = φ(x) + φ(x + 1) + 2 φ(x + 2)`, the functional `(1, 1, 2)` applied to the
vector `v(x) = (φ(x), φ(x + 1), φ(x + 2))`. -/
noncomputable def d4B (x : ℝ) : ℂ := scalingFun d4 x + d4A x

/-- **The recursion of `A` on the left half**: for `x ∈ [0, 1/2)`,
`A(x) = A(2x)/2 + (3 - √3)/4`. By the refinement equation (`Daubechies.scalingFun_d4_add_one_left`,
`Daubechies.scalingFun_d4_add_two_left`), `A(x) = c_2 φ(u) + (c_1 + 2c_3) φ(u + 1) +
(c_0 + 2c_2) φ(u + 2)` with `u = 2x ∈ [0, 1)`, and the coefficients are
`(3 - √3)/4 + (0, 1/2, 1)`; the partition of unity `φ(u) + φ(u + 1) + φ(u + 2) = 1`
(`Daubechies.scalingFun_d4_add_add_eq_one`) turns the first part into the constant `(3 - √3)/4`. In
matrix language: `ℓ_1 T_0 = ℓ_1/2 + (μ/2) ℓ_0` with `μ = (3 - √3)/2`. -/
theorem d4A_left {x : ℝ} (hx : x ∈ Ico (0 : ℝ) (1 / 2)) :
    d4A x = d4A (2 * x) / 2 + (((3 - √3) / 4 : ℝ) : ℂ) := by
  have hp := scalingFun_d4_add_add_eq_one (x := 2 * x) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  simp only [d4A]
  rw [scalingFun_d4_add_one_left hx, scalingFun_d4_add_two_left hx, coeff_d4_zero, coeff_d4_one,
    coeff_d4_two, coeff_d4_three]
  push_cast
  linear_combination ((3 - (√3 : ℂ)) / 4) * hp

/-- **The recursion of `A` on the right half**: for `x ∈ [1/2, 1)`,
`A(x) = A(2x - 1)/2 + (1 - √3)/4`. With `u = 2x - 1 ∈ [0, 1)`, the refinement equation
(`Daubechies.scalingFun_d4_add_one_right`, `Daubechies.scalingFun_d4_add_two_right`) gives
`A(x) = c_3 φ(u) + c_2 φ(u + 1) + (c_1 + 2c_3) φ(u + 2)` with coefficients
`(1 - √3)/4 + (0, 1/2, 1)`, and the partition of unity gives the constant. In matrix language:
`ℓ_1 T_1 = ℓ_1/2 + ((μ - 1)/2) ℓ_0`. -/
theorem d4A_right {x : ℝ} (hx : x ∈ Ico (1 / 2 : ℝ) 1) :
    d4A x = d4A (2 * x - 1) / 2 + (((1 - √3) / 4 : ℝ) : ℂ) := by
  have hp := scalingFun_d4_add_add_eq_one (x := 2 * x - 1) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [show 2 * x - 1 + 1 = 2 * x by ring, show 2 * x - 1 + 2 = 2 * x + 1 by ring] at hp
  simp only [d4A]
  rw [show 2 * x - 1 + 1 = 2 * x by ring, show 2 * x - 1 + 2 = 2 * x + 1 by ring,
    scalingFun_d4_add_one_right hx, scalingFun_d4_add_two_right hx, coeff_d4_one, coeff_d4_two,
    coeff_d4_three]
  push_cast
  linear_combination ((1 - (√3 : ℂ)) / 4) * hp

/-- **The recursion of `B` on the left half**: for `x ∈ [0, 1/2)`,
`B(x) = (3 - √3)/4 + ((1 - √3)/4) A(2x) + ((1 + √3)/4) B(2x)`. With `u = 2x`, the refinement
equation gives `B(x) = φ(u) + ((5 - √3)/4) φ(u + 1) + ((7 - √3)/4) φ(u + 2)`, and this row vector
is `a_0 ℓ_0 + β_0 ℓ_1 + λ_0 (1, 1, 2)` with `a_0 = (3 - √3)/4`, `β_0 = (1 - √3)/4`,
`λ_0 = (1 + √3)/4`; the partition of unity turns `a_0 ℓ_0` into the constant `a_0`. -/
theorem d4B_left {x : ℝ} (hx : x ∈ Ico (0 : ℝ) (1 / 2)) :
    d4B x = (((3 - √3) / 4 : ℝ) : ℂ) + (((1 - √3) / 4 : ℝ) : ℂ) * d4A (2 * x) +
      (((1 + √3) / 4 : ℝ) : ℂ) * d4B (2 * x) := by
  have hp := scalingFun_d4_add_add_eq_one (x := 2 * x) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  simp only [d4B, d4A]
  rw [scalingFun_d4_left hx, scalingFun_d4_add_one_left hx, scalingFun_d4_add_two_left hx,
    coeff_d4_zero, coeff_d4_one, coeff_d4_two, coeff_d4_three]
  push_cast
  linear_combination ((3 - (√3 : ℂ)) / 4) * hp

/-- **The recursion of `B` on the right half**: for `x ∈ [1/2, 1)`,
`B(x) = (3 + √3)/4 + ((1 - √3)/4) B(2x - 1)`. With `u = 2x - 1`, the refinement equation gives
`B(x) = φ(u) + φ(u + 1) + ((5 - √3)/4) φ(u + 2)`, the row vector
`a_1 ℓ_0 + λ_1 (1, 1, 2)` with `a_1 = (3 + √3)/4` and `λ_1 = (1 - √3)/4`, whose `A`-coordinate
is `0`. -/
theorem d4B_right {x : ℝ} (hx : x ∈ Ico (1 / 2 : ℝ) 1) :
    d4B x = (((3 + √3) / 4 : ℝ) : ℂ) + (((1 - √3) / 4 : ℝ) : ℂ) * d4B (2 * x - 1) := by
  have hp := scalingFun_d4_add_add_eq_one (x := 2 * x - 1) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [show 2 * x - 1 + 1 = 2 * x by ring, show 2 * x - 1 + 2 = 2 * x + 1 by ring] at hp
  simp only [d4B, d4A]
  rw [show 2 * x - 1 + 1 = 2 * x by ring, show 2 * x - 1 + 2 = 2 * x + 1 by ring,
    scalingFun_d4_right hx, scalingFun_d4_add_one_right hx, scalingFun_d4_add_two_right hx,
    coeff_d4_zero, coeff_d4_one, coeff_d4_two, coeff_d4_three]
  push_cast
  linear_combination ((3 + (√3 : ℂ)) / 4) * hp

/-- **The halving recursion of `A` for differences**: for `d ∈ {0, 1}` and
`x, y ∈ [d/2, (d+1)/2)`, `‖A(x) - A(y)‖ ≤ ‖A(2x - d) - A(2y - d)‖ / 2` (in fact with equality):
the additive constants of `Daubechies.d4A_left` and `Daubechies.d4A_right` cancel. This is the
hypothesis of `Daubechies.norm_sub_le_of_halving`. -/
theorem norm_d4A_sub_le (d : ℕ) (hd : d < 2) {x y : ℝ}
    (hx : x ∈ Ico ((d : ℝ) / 2) ((d + 1) / 2)) (hy : y ∈ Ico ((d : ℝ) / 2) ((d + 1) / 2)) :
    ‖d4A x - d4A y‖ ≤ ‖d4A (2 * x - d) - d4A (2 * y - d)‖ / 2 := by
  obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
  · have hx' : x ∈ Ico (0 : ℝ) (1 / 2) := by simpa using hx
    have hy' : y ∈ Ico (0 : ℝ) (1 / 2) := by simpa using hy
    have h : d4A x - d4A y = (d4A (2 * x) - d4A (2 * y)) / 2 := by
      rw [d4A_left hx', d4A_left hy']
      ring
    rw [h, Nat.cast_zero, sub_zero, sub_zero, norm_div, Complex.norm_two]
  · have hx' : x ∈ Ico (1 / 2 : ℝ) 1 := by norm_num at hx ⊢; exact hx
    have hy' : y ∈ Ico (1 / 2 : ℝ) 1 := by norm_num at hy ⊢; exact hy
    have h : d4A x - d4A y = (d4A (2 * x - 1) - d4A (2 * y - 1)) / 2 := by
      rw [d4A_right hx', d4A_right hy']
      ring
    rw [h, Nat.cast_one, norm_div, Complex.norm_two]

/-- **The triangular recursion of `B` for differences**: for `d ∈ {0, 1}` and
`x, y ∈ [d/2, (d+1)/2)`,
`‖B(x) - B(y)‖ ≤ ((√3 - 1)/4) ‖A(2x - d) - A(2y - d)‖ + ((1 + √3)/4) ‖B(2x - d) - B(2y - d)‖`.
For `d = 0` this is the triangle inequality in `Daubechies.d4B_left` with
`|β_0| = (√3 - 1)/4` and `λ_0 = (1 + √3)/4`; for `d = 1` (`Daubechies.d4B_right`) the factor
`|λ_1| = (√3 - 1)/4` is at most `(1 + √3)/4`. This is the hypothesis of
`Daubechies.norm_sub_le_of_triangular` with `β = (√3 - 1)/4` and `ρ = (1 + √3)/4`. -/
theorem norm_d4B_sub_le (d : ℕ) (hd : d < 2) {x y : ℝ}
    (hx : x ∈ Ico ((d : ℝ) / 2) ((d + 1) / 2)) (hy : y ∈ Ico ((d : ℝ) / 2) ((d + 1) / 2)) :
    ‖d4B x - d4B y‖ ≤ (√3 - 1) / 4 * ‖d4A (2 * x - d) - d4A (2 * y - d)‖ +
      (1 + √3) / 4 * ‖d4B (2 * x - d) - d4B (2 * y - d)‖ := by
  have h3 := one_lt_sqrt_three
  obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
  · have hx' : x ∈ Ico (0 : ℝ) (1 / 2) := by simpa using hx
    have hy' : y ∈ Ico (0 : ℝ) (1 / 2) := by simpa using hy
    have h : d4B x - d4B y = (((1 - √3) / 4 : ℝ) : ℂ) * (d4A (2 * x) - d4A (2 * y)) +
        (((1 + √3) / 4 : ℝ) : ℂ) * (d4B (2 * x) - d4B (2 * y)) := by
      rw [d4B_left hx', d4B_left hy']
      ring
    rw [h, Nat.cast_zero, sub_zero, sub_zero]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_neg (by linarith), abs_of_pos (by positivity)]
    ring
  · have hx' : x ∈ Ico (1 / 2 : ℝ) 1 := by norm_num at hx ⊢; exact hx
    have hy' : y ∈ Ico (1 / 2 : ℝ) 1 := by norm_num at hy ⊢; exact hy
    have h : d4B x - d4B y = (((1 - √3) / 4 : ℝ) : ℂ) * (d4B (2 * x - 1) - d4B (2 * y - 1)) := by
      rw [d4B_right hx', d4B_right hy']
      ring
    rw [h, Nat.cast_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.2 h3.le) (norm_nonneg (d4A (2 * x - 1) - d4A (2 * y - 1))),
      norm_nonneg (d4B (2 * x - 1) - d4B (2 * y - 1))]

/-! ### Back from the auxiliary functions to the scaling function -/

/-- `φ = B - A` (the definition of `B`). -/
theorem scalingFun_d4_eq_d4B_sub_d4A (x : ℝ) : scalingFun d4 x = d4B x - d4A x := by
  simp [d4B]

/-- `φ(x + 2) = B(x) - 1` for `x ∈ [0, 1)`: `B(x) = (φ(x) + φ(x + 1) + φ(x + 2)) + φ(x + 2)`
and the partition of unity (`Daubechies.scalingFun_d4_add_add_eq_one`). -/
theorem scalingFun_d4_add_two_eq {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    scalingFun d4 (x + 2) = d4B x - 1 := by
  have hp := scalingFun_d4_add_add_eq_one hx
  simp only [d4B, d4A]
  linear_combination -hp

/-- `φ(x + 1) = A(x) - 2 (B(x) - 1)` for `x ∈ [0, 1)`: `A(x) = φ(x + 1) + 2 φ(x + 2)` and
`φ(x + 2) = B(x) - 1` (`Daubechies.scalingFun_d4_add_two_eq`). -/
theorem scalingFun_d4_add_one_eq {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    scalingFun d4 (x + 1) = d4A x - 2 * (d4B x - 1) := by
  have hp := scalingFun_d4_add_add_eq_one hx
  simp only [d4B, d4A]
  linear_combination 2 * hp

/-- For `x ∈ [0, 1)` and an integer `i ∉ {0, 1, 2}`, `φ(x + i) = 0`, since `x + i ∉ (0, 3)`
(`Daubechies.scalingFun_d4_eq_zero`). -/
theorem scalingFun_d4_add_int_eq_zero {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) {i : ℤ}
    (hi : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2) : scalingFun d4 (x + i) = 0 := by
  refine scalingFun_d4_eq_zero fun h => ?_
  have h1 : (-1 : ℝ) < i := by linarith [h.1, hx.2]
  have h2 : (i : ℝ) < 3 := by linarith [h.2, hx.1]
  have h1' : -1 < i := by exact_mod_cast h1
  have h2' : i < 3 := by exact_mod_cast h2
  omega

/-- **The translates of `φ` are controlled by `A` and `B`**: for `x, y ∈ [0, 1)` and every
integer `i`,
`‖φ(x + i) - φ(y + i)‖ ≤ ‖A(x) - A(y)‖ + 2 ‖B(x) - B(y)‖`.
On `[0, 1)` the values `φ(x) = B(x) - A(x)`, `φ(x + 1) = A(x) - 2 (B(x) - 1)` and
`φ(x + 2) = B(x) - 1` are affine in `(A(x), B(x))`, and `φ(x + i) = 0` for the other `i`. -/
theorem norm_scalingFun_d4_sub_le {x y : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) (hy : y ∈ Ico (0 : ℝ) 1)
    (i : ℤ) : ‖scalingFun d4 (x + i) - scalingFun d4 (y + i)‖ ≤
      ‖d4A x - d4A y‖ + 2 * ‖d4B x - d4B y‖ := by
  have hA := norm_nonneg (d4A x - d4A y)
  have hB := norm_nonneg (d4B x - d4B y)
  by_cases h0 : i = 0
  · subst h0
    rw [Int.cast_zero, add_zero, add_zero, scalingFun_d4_eq_d4B_sub_d4A,
      scalingFun_d4_eq_d4B_sub_d4A,
      show d4B x - d4A x - (d4B y - d4A y) = (d4B x - d4B y) - (d4A x - d4A y) by ring]
    linarith [norm_sub_le (d4B x - d4B y) (d4A x - d4A y)]
  by_cases h1 : i = 1
  · subst h1
    rw [Int.cast_one, scalingFun_d4_add_one_eq hx, scalingFun_d4_add_one_eq hy,
      show d4A x - 2 * (d4B x - 1) - (d4A y - 2 * (d4B y - 1)) =
        (d4A x - d4A y) - 2 * (d4B x - d4B y) by ring]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_two]
  by_cases h2 : i = 2
  · subst h2
    rw [Int.cast_ofNat, scalingFun_d4_add_two_eq hx, scalingFun_d4_add_two_eq hy,
      sub_sub_sub_cancel_right]
    linarith
  · rw [scalingFun_d4_add_int_eq_zero hx ⟨h0, h1, h2⟩,
      scalingFun_d4_add_int_eq_zero hy ⟨h0, h1, h2⟩, sub_zero, norm_zero]
    positivity

/-! ### The Hölder exponent -/

/-- A bound `‖φ‖ ≤ M` gives `‖A(x)‖ ≤ 3M` for every `x ∈ ℝ`. -/
theorem norm_d4A_le {M : ℝ} (hM : ∀ x, ‖scalingFun d4 x‖ ≤ M) (x : ℝ) : ‖d4A x‖ ≤ 3 * M := by
  calc ‖d4A x‖ ≤ ‖scalingFun d4 (x + 1)‖ + ‖2 * scalingFun d4 (x + 2)‖ := norm_add_le _ _
    _ ≤ 3 * M := by rw [norm_mul, Complex.norm_two]; linarith [hM (x + 1), hM (x + 2)]

/-- A bound `‖φ‖ ≤ M` gives `‖B(x)‖ ≤ 4M` for every `x ∈ ℝ`. -/
theorem norm_d4B_le {M : ℝ} (hM : ∀ x, ‖scalingFun d4 x‖ ≤ M) (x : ℝ) : ‖d4B x‖ ≤ 4 * M := by
  calc ‖d4B x‖ ≤ ‖scalingFun d4 x‖ + ‖d4A x‖ := norm_add_le _ _
    _ ≤ 4 * M := by linarith [hM x, norm_d4A_le hM x]

/-- A bound `‖φ‖ ≤ M` gives `‖A(x) - A(y)‖ ≤ 6M` for all `x, y ∈ ℝ`
(`Daubechies.norm_d4A_le`). -/
theorem norm_d4A_sub_d4A_le {M : ℝ} (hM : ∀ x, ‖scalingFun d4 x‖ ≤ M) (x y : ℝ) :
    ‖d4A x - d4A y‖ ≤ 6 * M := by
  linarith [norm_sub_le (d4A x) (d4A y), norm_d4A_le hM x, norm_d4A_le hM y]

/-- A bound `‖φ‖ ≤ M` gives `‖B(x) - B(y)‖ ≤ 8M` for all `x, y ∈ ℝ`
(`Daubechies.norm_d4B_le`). -/
theorem norm_d4B_sub_d4B_le {M : ℝ} (hM : ∀ x, ‖scalingFun d4 x‖ ≤ M) (x y : ℝ) :
    ‖d4B x - d4B y‖ ≤ 8 * M := by
  linarith [norm_sub_le (d4B x) (d4B y), norm_d4B_le hM x, norm_d4B_le hM y]

/-- **The oscillation of D4 on dyadic intervals**: let `‖φ‖ ≤ M` and `ρ = (1 + √3)/4`. For every
`n ∈ ℕ`, every integer `i` and all `x, y` in one dyadic interval `[k/2^n, (k+1)/2^n)` with
`k < 2^n`,
`‖φ(x + i) - φ(y + i)‖ ≤ 28 M ρ^n`.
The dyadic descent gives `‖A(x) - A(y)‖ ≤ 6M / 2^n` (`Daubechies.norm_sub_le_of_halving`) and
`‖B(x) - B(y)‖ ≤ 14 M ρ^n - 6M / 2^n` (`Daubechies.norm_sub_le_of_triangular` with
`β = ρ - 1/2 = (√3 - 1)/4` and `C = E_A = 6M`), and
`Daubechies.norm_scalingFun_d4_sub_le` combines them. -/
theorem norm_scalingFun_d4_sub_le_dyadic {M : ℝ} (hM : ∀ x, ‖scalingFun d4 x‖ ≤ M) (n : ℕ)
    (i : ℤ) {k : ℕ} (hk : k < 2 ^ n) {x y : ℝ}
    (hx : x ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n))
    (hy : y ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n)) :
    ‖scalingFun d4 (x + i) - scalingFun d4 (y + i)‖ ≤ 28 * M * ((1 + √3) / 4) ^ n := by
  have h3 := one_lt_sqrt_three
  have hA : ∀ (n k : ℕ), k < 2 ^ n → ∀ x ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n),
      ∀ y ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n), ‖d4A x - d4A y‖ ≤ 6 * M / 2 ^ n :=
    fun n k hk x hx y hy => norm_sub_le_of_halving (fun x _ y _ => norm_d4A_sub_d4A_le hM x y)
      (fun d hd x hx y hy => norm_d4A_sub_le d hd hx hy) n hk hx hy
  have hB := norm_sub_le_of_triangular (C := 6 * M) (by linarith) (by positivity)
    (le_of_eq (by ring)) hA (fun x _ y _ => norm_d4B_sub_d4B_le hM x y)
    (fun d hd x hx y hy => norm_d4B_sub_le d hd hx hy) n hk hx hy
  have hφ := norm_scalingFun_d4_sub_le (mem_Ico_zero_one_of_mem_dyadic hk hx)
    (mem_Ico_zero_one_of_mem_dyadic hk hy) i
  have hA' := hA n k hk x hx y hy
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h2 : 0 ≤ 6 * M / 2 ^ n := by positivity
  linarith

/-- `ρ = (1 + √3)/4 ≤ 2^(-a)` for every `a ≤ 2 - log₂(1 + √3)`, since
`2^(log₂(1 + √3) - 2) = (1 + √3)/4`. -/
theorem one_add_sqrt_three_div_four_le {a : ℝ} (ha : a ≤ 2 - Real.logb 2 (1 + √3)) :
    (1 + √3) / 4 ≤ (2 : ℝ) ^ (-a) := by
  have h3 : (0 : ℝ) < 1 + √3 := by positivity
  calc (1 + √3) / 4 = (2 : ℝ) ^ (Real.logb 2 (1 + √3) - 2) := by
        rw [Real.rpow_sub two_pos, Real.rpow_logb two_pos (by norm_num) h3, Real.rpow_two]
        norm_num
    _ ≤ 2 ^ (-a) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- **The Hölder exponent of D4** (Daubechies–Lagarias): the scaling function `φ` of the
Daubechies mask D4 is Hölder continuous with every exponent `0 ≤ a ≤ 2 - log₂(1 + √3)`
(`≈ 0.5500`): there is `K` with `‖φ(x) - φ(y)‖ ≤ K |x - y|^a` for all `x, y ∈ ℝ`. The exponent is
`-log₂ ρ` for the rate `ρ = (1 + √3)/4` of `Daubechies.norm_scalingFun_d4_sub_le_dyadic`, and
`Daubechies.exists_holder_of_unit_dyadic` turns the dyadic bounds `28 M ρ^n` into the Hölder
estimate (`M = ∫ ‖Φ‖ ≥ sup ‖φ‖`, `Daubechies.norm_scalingFun_le`). -/
theorem holder_d4 {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 2 - Real.logb 2 (1 + √3)) :
    ∃ K, ∀ x y, ‖scalingFun d4 x - scalingFun d4 y‖ ≤ K * |x - y| ^ a := by
  have hM := norm_scalingFun_le d4
  have hM0 : 0 ≤ ∫ ξ, ‖symbolProduct d4 ξ‖ := (norm_nonneg _).trans (hM 0)
  exact exists_holder_of_unit_dyadic (continuous_scalingFun d4 le_rfl) hM (by positivity)
    (by positivity) (one_add_sqrt_three_div_four_le ha) ha0
    fun n i k hk x hx y hy => norm_scalingFun_d4_sub_le_dyadic hM n i hk hx hy

/-- `(1 + √3)^20 = 268377088 + 154947584 √3`, by repeated squaring with `(√3)² = 3`:
`(1 + √3)² = 4 + 2√3`, `(1 + √3)^4 = 28 + 16√3`, `(1 + √3)^8 = 1552 + 896√3`,
`(1 + √3)^16 = 4817152 + 2781184√3`. -/
theorem one_add_sqrt_three_pow_twenty : (1 + √3) ^ 20 = 268377088 + 154947584 * √3 := by
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : (1 + √3) ^ 2 = 4 + 2 * √3 := by linear_combination hs
  have h4 : (1 + √3) ^ 4 = 28 + 16 * √3 := by
    rw [show (1 + √3) ^ 4 = ((1 + √3) ^ 2) ^ 2 by ring, h2]
    linear_combination 4 * hs
  have h8 : (1 + √3) ^ 8 = 1552 + 896 * √3 := by
    rw [show (1 + √3) ^ 8 = ((1 + √3) ^ 4) ^ 2 by ring, h4]
    linear_combination 256 * hs
  have h16 : (1 + √3) ^ 16 = 4817152 + 2781184 * √3 := by
    rw [show (1 + √3) ^ 16 = ((1 + √3) ^ 8) ^ 2 by ring, h8]
    linear_combination 802816 * hs
  rw [show (1 + √3) ^ 20 = (1 + √3) ^ 16 * (1 + √3) ^ 4 by ring, h16, h4]
  linear_combination 44498944 * hs

/-- **The Hölder exponent of D4 exceeds `0.55`**: `2 - log₂(1 + √3) > 0.55`. Equivalently
`1 + √3 < 2^(29/20)`, that is `(1 + √3)^20 < 2^29 = 536870912`; by
`Daubechies.one_add_sqrt_three_pow_twenty` this is `154947584 √3 < 268493824`, which holds since
`√3 < 1.7321`. -/
theorem two_sub_logb_two_one_add_sqrt_three_gt : (0.55 : ℝ) < 2 - Real.logb 2 (1 + √3) := by
  have hs : √3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hlt : (1 + √3) ^ 20 < ((2 : ℝ) ^ (1.45 : ℝ)) ^ 20 := by
    rw [one_add_sqrt_three_pow_twenty, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
    linarith
  have hlog : Real.logb 2 (1 + √3) < 1.45 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity)]
    exact lt_of_pow_lt_pow_left₀ 20 (by positivity) hlt
  linarith

end D4

end Daubechies
