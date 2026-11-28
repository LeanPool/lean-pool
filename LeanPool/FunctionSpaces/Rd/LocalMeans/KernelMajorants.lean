/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Atoms.SmoothAtoms
public import LeanPool.FunctionSpaces.Rd.Approximation.BandInverse
public import LeanPool.FunctionSpaces.Analysis.Maximal.HardyLittlewoodMaximal

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Kernel majorants

Pointwise bounds of convolution kernels by Peetre weights `2^(kn) (1 + 2^k ‖y‖)^(-N)`, the input
of the maximal function bounds behind the local means characterisation of Triebel–Lizorkin
spaces. Every constant is explicit.

* **Decay of Schwartz functions**: the segment bound for differences
  (`Rd.norm_higherDiff_le_of_segment`) and Peetre's inequality along a segment
  (`Rd.one_add_norm_le_mul_of_mem_Icc`) give the decay of differences of Schwartz functions
  (`Rd.enorm_higherDiff_schwartz_le`, constant `Rd.schwartzDecayConst`), their tails
  (`Rd.lintegral_tail_schwartz_le`, constant `Rd.tailConst`), and the convolution of two Peetre
  bumps (`Rd.lintegral_peetre_mul_le`, with the mass `Rd.peetreIntegral` of the weight and the
  change of scale `Rd.lintegral_comp_smul`).
* **The cross kernel `k_j ⋆ Θ_i`** of the local means kernels and the band-limiting kernels
  (`Rd.LocalMeansBump.enorm_conv_kernel_Theta_le`): for `i < j` the averaged differences of the
  moment kernels act on the smooth `Θ_i`, one scale at a time
  (`Rd.LocalMeansBump.ae_enorm_conv_kernel_le_of_scaled`); for `i ≥ j` the kernel `k_j` is
  bounded and of small support (`Rd.LocalMeansBump.norm_kernel_le`,
  `Rd.LocalMeansBump.kernel_eq_zero_of_lt`).
* **The cross kernel `ψ_j ⋆ η_i`** of the Littlewood–Paley blocks and the dual kernels
  (`Rd.LocalMeansBump.enorm_conv_psi_dual_le`): for `i ≤ j` and `j ≥ 2` the block `ψ_j`
  annihilates the moment kernel `μ_{2^(j-2)}` of `Φ` (`Rd.conv_psi_lpMomentScaled`, through the
  Fourier transforms `Rd.fourier_dilate_momentKernel`), so
  `ψ_j ⋆ η_i = ψ_j ⋆ (η_i - μ_{2^(j-2)} ⋆ η_i)`, and `η_i - μ_{2^(j-2)} ⋆ η_i` averages
  differences of `η_i` with short steps; the remaining cases use the small support of `η_i`.

Both bounds have the shape `|K(y)| ≤ C c_{ji} 2^(mn) (1 + 2^m ‖y‖)^(-N)` with `m = min(i, j)` and
`c_{ji} = 1` for `i > j`; for `i ≤ j`, `c_{ji} = 2^(-(j-i)L)` for `k_j ⋆ Θ_i` and
`c_{ji} = 2^(-(j-i)L')` for `ψ_j ⋆ η_i`, with the free order `L'` of the moment kernel of `Φ`.
Such kernels act below the Hardy–Littlewood maximal function: `|K ⋆ h(x)| ≤ C_{n,N} C M|h|(x)`
for every function `h` (`Rd.enorm_conv_le_maximal_of_decay`).
-/

@[expose] public section

open MeasureTheory Module Metric Filter Set
open scoped ENNReal SchwartzMap Pointwise FourierTransform

open ENNReal (dyadicWeight)

namespace ENNReal

/-! ### Peetre weights in `[0, ∞]` -/

/-- `X⁻¹ ≤ c Y⁻¹` in `[0, ∞]` whenever `Y ≤ c X` with `0 < c < ∞`. -/
theorem inv_le_mul_inv_of_le {X Y c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    (h : Y ≤ c * X) : X⁻¹ ≤ c * Y⁻¹ := by
  calc X⁻¹ = c * (c * X)⁻¹ := by
        rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hc), ← mul_assoc, ENNReal.mul_inv_cancel hc0 hc,
          one_mul]
    _ ≤ c * Y⁻¹ := by gcongr

/-- `1 + a ≠ 0` in `[0, ∞]`. -/
theorem one_add_ne_zero (a : ℝ≥0∞) : 1 + a ≠ 0 :=
  (lt_of_lt_of_le one_pos le_self_add).ne'

/-- **Peetre's inequality** for the weights `(1 + a ‖·‖)^(-N)` in `[0, ∞]`: if `u ≤ v + w` and
`a, w < ∞`, then `(1 + a v)^(-N) ≤ (1 + a w)^N (1 + a u)^(-N)`, from
`1 + a u ≤ (1 + a w)(1 + a v)`. -/
theorem inv_one_add_mul_pow_le {a u v w : ℝ≥0∞} (ha : a ≠ ∞) (hw : w ≠ ∞) (h : u ≤ v + w)
    (N : ℕ) : ((1 + a * v) ^ N)⁻¹ ≤ (1 + a * w) ^ N * ((1 + a * u) ^ N)⁻¹ := by
  refine ENNReal.inv_le_mul_inv_of_le (pow_ne_zero _ (one_add_ne_zero _))
    (ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top ha hw⟩)) ?_
  rw [← mul_pow]
  refine pow_le_pow_left' ?_ N
  calc 1 + a * u ≤ 1 + (a * v + a * w) := by rw [← mul_add]; gcongr
    _ ≤ 1 + (a * v + a * w) + a * w * (a * v) := le_self_add
    _ = (1 + a * w) * (1 + a * v) := by ring

/-- The Peetre weights decrease with the scale: `(1 + b u)^(-N) ≤ (1 + a u)^(-N)` for `a ≤ b`. -/
theorem inv_one_add_mul_pow_anti {a b : ℝ≥0∞} (hab : a ≤ b) (u : ℝ≥0∞) (N : ℕ) :
    ((1 + b * u) ^ N)⁻¹ ≤ ((1 + a * u) ^ N)⁻¹ :=
  ENNReal.inv_le_inv.2 (by gcongr)

/-- Halving the scale costs `2^N`: `(1 + a u)^(-N) ≤ 2^N (1 + 2 a u)^(-N)`. -/
theorem inv_one_add_mul_pow_le_two_pow (a u : ℝ≥0∞) (N : ℕ) :
    ((1 + a * u) ^ N)⁻¹ ≤ 2 ^ N * ((1 + 2 * a * u) ^ N)⁻¹ := by
  refine ENNReal.inv_le_mul_inv_of_le (pow_ne_zero _ two_ne_zero)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ?_
  rw [← mul_pow]
  refine pow_le_pow_left' ?_ N
  calc 1 + 2 * a * u ≤ 2 + 2 * a * u := by gcongr; exact one_le_two
    _ = 2 * (1 + a * u) := by ring

/-- `(1 + a)^(-(k + r + m)) a^r ≤ (1 + a)^(-k) (1 + a)^(-m)` for `a < ∞`. -/
theorem inv_one_add_pow_mul_pow_le {a : ℝ≥0∞} (ha : a ≠ ∞) (k r m : ℕ) :
    ((1 + a) ^ (k + r + m))⁻¹ * a ^ r ≤ ((1 + a) ^ k)⁻¹ * ((1 + a) ^ m)⁻¹ := by
  have hX0 : 1 + a ≠ 0 := one_add_ne_zero a
  have hXt : 1 + a ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ha⟩
  have h1 : (1 + a)⁻¹ * a ≤ 1 := by
    calc (1 + a)⁻¹ * a ≤ (1 + a)⁻¹ * (1 + a) := by gcongr; exact le_add_self
      _ = 1 := ENNReal.inv_mul_cancel hX0 hXt
  rw [ENNReal.inv_pow, ENNReal.inv_pow, ENNReal.inv_pow]
  calc (1 + a)⁻¹ ^ (k + r + m) * a ^ r = (1 + a)⁻¹ ^ k * (1 + a)⁻¹ ^ m * ((1 + a)⁻¹ * a) ^ r := by
        ring
    _ ≤ (1 + a)⁻¹ ^ k * (1 + a)⁻¹ ^ m * 1 := by gcongr; exact pow_le_one₀ zero_le h1
    _ = (1 + a)⁻¹ ^ k * (1 + a)⁻¹ ^ m := mul_one _

/-- `(1 + a)^(-2N) (1 + a)^N = (1 + a)^(-N)` for `a < ∞`. -/
theorem inv_one_add_pow_two_mul_mul_pow {a : ℝ≥0∞} (ha : a ≠ ∞) (N : ℕ) :
    ((1 + a) ^ (2 * N))⁻¹ * (1 + a) ^ N = ((1 + a) ^ N)⁻¹ := by
  have h0 : (1 + a) ^ N ≠ 0 := pow_ne_zero _ (one_add_ne_zero a)
  have ht : (1 + a) ^ N ≠ ∞ := ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ha⟩)
  rw [two_mul, pow_add, ENNReal.mul_inv (Or.inl h0) (Or.inl ht), mul_assoc,
    ENNReal.inv_mul_cancel h0 ht, mul_one]

/-- Near the origin the Peetre weight is bounded below: if `a ≤ t` with `0 ≤ t`, then
`1 ≤ (1 + t)^N (1 + a)^(-N)`. -/
theorem one_le_ofReal_mul_inv_of_le {a : ℝ≥0∞} {t : ℝ} (ht : 0 ≤ t) (h : a ≤ ENNReal.ofReal t)
    (N : ℕ) : 1 ≤ ENNReal.ofReal ((1 + t) ^ N) * ((1 + a) ^ N)⁻¹ := by
  have ha : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hX0 : (1 + a) ^ N ≠ 0 := pow_ne_zero _ (one_add_ne_zero a)
  have hXt : (1 + a) ^ N ≠ ∞ := ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ha⟩)
  calc 1 = (1 + a) ^ N * ((1 + a) ^ N)⁻¹ := (ENNReal.mul_inv_cancel hX0 hXt).symm
    _ ≤ ENNReal.ofReal ((1 + t) ^ N) * ((1 + a) ^ N)⁻¹ := by
        rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add zero_le_one ht,
          ENNReal.ofReal_one]
        gcongr

end ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Peetre weights -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Peetre's inequality for norms: `(1 + a ‖y - w‖)^(-N) ≤ (1 + a ‖w‖)^N (1 + a ‖y‖)^(-N)` for
`a < ∞`. -/
theorem inv_one_add_mul_enorm_sub_pow_le {a : ℝ≥0∞} (ha : a ≠ ∞) (y w : V) (N : ℕ) :
    ((1 + a * ‖y - w‖ₑ) ^ N)⁻¹ ≤ (1 + a * ‖w‖ₑ) ^ N * ((1 + a * ‖y‖ₑ) ^ N)⁻¹ := by
  refine ENNReal.inv_one_add_mul_pow_le ha eNorm_ne_top ?_ N
  calc ‖y‖ₑ = ‖(y - w) + w‖ₑ := by rw [sub_add_cancel]
    _ ≤ ‖y - w‖ₑ + ‖w‖ₑ := eNorm_add_le _ _

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The bridge to Mathlib's `finite_integral_one_add_norm`:
`ofReal ((1 + ‖x‖)^(-N)) = (1 + ‖x‖)^(-N)` in `[0, ∞]`. -/
theorem ofReal_one_add_norm_rpow_neg (x : V) (N : ℕ) :
    ENNReal.ofReal ((1 + ‖x‖) ^ (-(N : ℝ))) = ((1 + ‖x‖ₑ) ^ N)⁻¹ := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add zero_le_one (norm_nonneg _),
    ENNReal.ofReal_one, ofReal_norm]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `ofReal ((1 + a ‖x‖)^(-N)) = (1 + a ‖x‖)^(-N)` in `[0, ∞]` for `a ≥ 0`. -/
theorem ofReal_inv_one_add_mul_norm_pow {a : ℝ} (ha : 0 ≤ a) (x : V) (N : ℕ) :
    ENNReal.ofReal (((1 + a * ‖x‖) ^ N)⁻¹) = ((1 + ENNReal.ofReal a * ‖x‖ₑ) ^ N)⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_mul ha,
    ofReal_norm]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A point of norm at most `ρ 2^(-k)` has `2^k ‖w‖ ≤ ρ`, in `[0, ∞]`. -/
theorem two_pow_mul_enorm_le_ofReal {k : ℕ} {ρ : ℝ} {w : V} (h : ‖w‖ ≤ ρ / 2 ^ k) :
    2 ^ k * ‖w‖ₑ ≤ ENNReal.ofReal ρ := by
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow zero_le_two, ← ofReal_norm,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (by positivity)] at h
  linarith

/-! ### Decay of Schwartz functions and of their differences -/

/-- The constant `2^N (sup ‖D^r G‖ + sup ‖x‖^N ‖D^r G(x)‖)` of the decay of the derivatives of
order `r` of a Schwartz function `G`, through two of its seminorms. -/
noncomputable def schwartzDecayConst (G : 𝓢(V, ℂ)) (r N : ℕ) : ℝ≥0∞ :=
  2 ^ N * ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 r G + SchwartzMap.seminorm ℝ N r G)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The decay constant of a Schwartz function is finite. -/
theorem schwartzDecayConst_ne_top (G : 𝓢(V, ℂ)) (r N : ℕ) : schwartzDecayConst G r N ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ENNReal.ofReal_ne_top

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `(1 + ‖x‖)^N ‖D^r G(x)‖ ≤ 2^N (sup ‖D^r G‖ + sup ‖x‖^N ‖D^r G(x)‖)` for a Schwartz function
`G`, from `(1 + t)^N ≤ 2^N (1 + t^N)`. Mathlib's `SchwartzMap.one_add_le_sup_seminorm_apply` is
the same kind of bound with the supremum over a range of seminorms. -/
theorem one_add_norm_pow_mul_le_schwartz (G : 𝓢(V, ℂ)) (r N : ℕ) (x : V) :
    (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ r G x‖ ≤
      2 ^ N * (SchwartzMap.seminorm ℝ 0 r G + SchwartzMap.seminorm ℝ N r G) := by
  have h0 := SchwartzMap.le_seminorm ℝ 0 r G x
  have hN := SchwartzMap.le_seminorm ℝ N r G x
  rw [pow_zero, one_mul] at h0
  calc (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ r G x‖
      ≤ 2 ^ N * (1 + ‖x‖ ^ N) * ‖iteratedFDeriv ℝ r G x‖ :=
        mul_le_mul_of_nonneg_right (one_add_pow_le_two_pow_mul (norm_nonneg x) N)
          (norm_nonneg _)
    _ = 2 ^ N * (‖iteratedFDeriv ℝ r G x‖ + ‖x‖ ^ N * ‖iteratedFDeriv ℝ r G x‖) := by ring
    _ ≤ _ := by gcongr

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Peetre's inequality along a segment**: `1 + ‖y‖ ≤ (1 + ‖y + t v‖)(1 + r ‖v‖)` for
`0 ≤ t ≤ r`. -/
theorem one_add_norm_le_mul_of_mem_Icc {r t : ℝ} (ht : t ∈ Set.Icc 0 r) (v y : V) :
    1 + ‖y‖ ≤ (1 + ‖y + t • v‖) * (1 + r * ‖v‖) := by
  have h1 : ‖y‖ ≤ ‖y + t • v‖ + t * ‖v‖ := by
    calc ‖y‖ = ‖(y + t • v) - t • v‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖y + t • v‖ + ‖t • v‖ := norm_sub_le _ _
      _ = ‖y + t • v‖ + t * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg ht.1]
  have h2 : t * ‖v‖ ≤ r * ‖v‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)
  have h3 : 0 ≤ ‖y + t • v‖ * (r * ‖v‖) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (ht.1.trans ht.2) (norm_nonneg v))
  nlinarith

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The derivatives of order `r` of a Schwartz function along the segment from `y` to `y + r v`
are at most `2^N (sup ‖D^r G‖ + sup ‖x‖^N ‖D^r G(x)‖) (1 + r ‖v‖)^N (1 + ‖y‖)^(-N)`. -/
theorem norm_iteratedFDeriv_schwartz_le_of_mem_Icc (G : 𝓢(V, ℂ)) (r N : ℕ) (v y : V) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) r) :
    ‖iteratedFDeriv ℝ r G (y + t • v)‖ ≤
      2 ^ N * (SchwartzMap.seminorm ℝ 0 r G + SchwartzMap.seminorm ℝ N r G) *
        (1 + r * ‖v‖) ^ N / (1 + ‖y‖) ^ N := by
  have hz := one_add_norm_pow_mul_le_schwartz G r N (y + t • v)
  have hpeetre : (1 + ‖y‖) ^ N ≤ (1 + ‖y + t • v‖) ^ N * (1 + r * ‖v‖) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (one_add_norm_le_mul_of_mem_Icc ht v y) N
  rw [le_div_iff₀ (by positivity)]
  calc ‖iteratedFDeriv ℝ r G (y + t • v)‖ * (1 + ‖y‖) ^ N
      ≤ ‖iteratedFDeriv ℝ r G (y + t • v)‖ * ((1 + ‖y + t • v‖) ^ N * (1 + r * ‖v‖) ^ N) := by
        gcongr
    _ = (1 + ‖y + t • v‖) ^ N * ‖iteratedFDeriv ℝ r G (y + t • v)‖ * (1 + r * ‖v‖) ^ N := by
        ring
    _ ≤ _ := by gcongr

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Differences of Schwartz functions with decay**: for a Schwartz function `G`,
`|Δ_v^r G(y)| ≤ C ‖v‖^r (1 + r ‖v‖)^N (1 + ‖y‖)^(-N)` with
`C = Rd.schwartzDecayConst G r N`, by the segment bound for differences and Peetre's
inequality. -/
theorem enorm_higherDiff_schwartz_le (G : 𝓢(V, ℂ)) (r N : ℕ) (v y : V) :
    ‖(fwdDiff v)^[r] (G : V → ℂ) y‖ₑ ≤
      schwartzDecayConst G r N * ‖v‖ₑ ^ r * (1 + r * ‖v‖ₑ) ^ N * ((1 + ‖y‖ₑ) ^ N)⁻¹ := by
  set S := 2 ^ N * (SchwartzMap.seminorm ℝ 0 r G + SchwartzMap.seminorm ℝ N r G) with hS
  have hS0 : 0 ≤ S := by positivity
  have hreal := norm_higherDiff_le_of_segment r (G.smooth r) v y
    (C := S * (1 + r * ‖v‖) ^ N / (1 + ‖y‖) ^ N)
    fun t ht => norm_iteratedFDeriv_schwartz_le_of_mem_Icc G r N v y ht
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
  have e1 : ENNReal.ofReal S = schwartzDecayConst G r N := by
    rw [hS, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat, schwartzDecayConst]
  have e2 : ENNReal.ofReal ((1 + r * ‖v‖) ^ N) = (1 + r * ‖v‖ₑ) ^ N := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add zero_le_one (by positivity),
      ENNReal.ofReal_one, ENNReal.ofReal_mul (Nat.cast_nonneg r), ENNReal.ofReal_natCast,
      ofReal_norm]
  have e3 : ENNReal.ofReal (((1 + ‖y‖) ^ N)⁻¹) = ((1 + ‖y‖ₑ) ^ N)⁻¹ := by
    have h := ofReal_inv_one_add_mul_norm_pow zero_le_one y N
    rwa [one_mul, ENNReal.ofReal_one, one_mul] at h
  have e4 : ENNReal.ofReal (‖v‖ ^ r) = ‖v‖ₑ ^ r := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hS0, e1, e2, e3, e4]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Decay of Schwartz functions**: `|G(y)| ≤ C (1 + ‖y‖)^(-N)` with
`C = Rd.schwartzDecayConst G 0 N`. -/
theorem enorm_schwartz_le (G : 𝓢(V, ℂ)) (N : ℕ) (y : V) :
    ‖G y‖ₑ ≤ schwartzDecayConst G 0 N * ((1 + ‖y‖ₑ) ^ N)⁻¹ := by
  simpa using enorm_higherDiff_schwartz_le G 0 N 0 y

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `‖2^j v‖ = 2^j ‖v‖` in `[0, ∞]`. -/
theorem enorm_two_pow_smul [NormedSpace ℝ V] (j : ℕ) (v : V) :
    ‖((2 : ℝ) ^ j) • v‖ₑ = 2 ^ j * ‖v‖ₑ := by
  rw [eNorm_smul, ← ofReal_norm, Real.norm_of_nonneg (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `|Φ_{2^j}(y)| = 2^(jn) |Φ(2^j y)|`. -/
theorem enorm_dilate_two_pow (Φ : V → ℂ) (j : ℕ) (y : V) :
    ‖dilate (2 ^ j) Φ y‖ₑ = 2 ^ (j * finrank ℝ V) * ‖Φ (((2 : ℝ) ^ j) • y)‖ₑ := by
  have hc : ‖(((((2 : ℝ) ^ j) ^ finrank ℝ V : ℝ)) : ℂ)‖ₑ = 2 ^ (j * finrank ℝ V) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← pow_mul,
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  rw [dilate, eNorm_mul, hc]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Decay of dilated Schwartz functions**:
`|G_{2^j}(y)| ≤ C 2^(jn) (1 + 2^j ‖y‖)^(-N)` with `C = Rd.schwartzDecayConst G 0 N`. -/
theorem enorm_dilate_schwartz_le (G : 𝓢(V, ℂ)) (N j : ℕ) (y : V) :
    ‖dilate (2 ^ j) G y‖ₑ ≤
      schwartzDecayConst G 0 N * 2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹ := by
  have h := enorm_schwartz_le G N (((2 : ℝ) ^ j) • y)
  rw [enorm_two_pow_smul] at h
  rw [enorm_dilate_two_pow]
  calc 2 ^ (j * finrank ℝ V) * ‖G (((2 : ℝ) ^ j) • y)‖ₑ
      ≤ 2 ^ (j * finrank ℝ V) * (schwartzDecayConst G 0 N * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹) := by
        gcongr
    _ = _ := by ring

/-! ### Tails -/

variable (V) in
/-- The integral `∫ (1 + ‖u‖)^(-M) du` of the Peetre weight, finite for `M > n`. -/
noncomputable def peetreIntegral (M : ℕ) : ℝ≥0∞ := ∫⁻ u : V, ((1 + ‖u‖ₑ) ^ M)⁻¹

/-- The integral of the Peetre weight is finite for `M > n` (Mathlib's
`finite_integral_one_add_norm`). -/
theorem peetreIntegral_ne_top {M : ℕ} (hM : finrank ℝ V < M) : peetreIntegral V M ≠ ∞ := by
  have h := finite_integral_one_add_norm (E := V) (μ := (volume : Measure V)) (r := (M : ℝ))
    (by exact_mod_cast hM)
  simp only [ofReal_one_add_norm_rpow_neg] at h
  exact h.ne

/-- The constant `schwartzDecayConst G 0 (N + r + n + 1) · ∫ (1 + ‖u‖)^(-(n+1)) du` of the
tails of a Schwartz function. -/
noncomputable def tailConst (G : 𝓢(V, ℂ)) (r N : ℕ) : ℝ≥0∞ :=
  schwartzDecayConst G 0 (N + r + finrank ℝ V + 1) * peetreIntegral V (finrank ℝ V + 1)

/-- The tail constant of a Schwartz function is finite. -/
theorem tailConst_ne_top (G : 𝓢(V, ℂ)) (r N : ℕ) : tailConst G r N ≠ ∞ :=
  ENNReal.mul_ne_top (schwartzDecayConst_ne_top _ _ _)
    (peetreIntegral_ne_top (Nat.lt_succ_self _))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The integrand of the tails: for `‖z‖ ≥ ρ`,
`|G(z)| ‖z‖^r ≤ C (1 + max(ρ, 0))^(-N) (1 + ‖z‖)^(-(n+1))` with
`C = Rd.schwartzDecayConst G 0 (N + r + n + 1)`. -/
theorem enorm_mul_enorm_pow_le_of_le (G : 𝓢(V, ℂ)) (r N : ℕ) {ρ : ℝ} {z : V}
    (hz : ρ ≤ ‖z‖) :
    ‖G z‖ₑ * ‖z‖ₑ ^ r ≤ schwartzDecayConst G 0 (N + r + finrank ℝ V + 1) *
      ((1 + ENNReal.ofReal ρ) ^ N)⁻¹ * ((1 + ‖z‖ₑ) ^ (finrank ℝ V + 1))⁻¹ := by
  have h1 := enorm_schwartz_le G (N + r + finrank ℝ V + 1) z
  have h2 := ENNReal.inv_one_add_pow_mul_pow_le (a := ‖z‖ₑ) eNorm_ne_top N r (finrank ℝ V + 1)
  have h3 : ((1 + ‖z‖ₑ) ^ N)⁻¹ ≤ ((1 + ENNReal.ofReal ρ) ^ N)⁻¹ := by
    have hρz : ENNReal.ofReal ρ ≤ ‖z‖ₑ := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hz
    exact ENNReal.inv_le_inv.2 (by gcongr)
  rw [← add_assoc] at h2
  calc ‖G z‖ₑ * ‖z‖ₑ ^ r
      ≤ schwartzDecayConst G 0 (N + r + finrank ℝ V + 1) *
          ((1 + ‖z‖ₑ) ^ (N + r + finrank ℝ V + 1))⁻¹ * ‖z‖ₑ ^ r := by gcongr
    _ ≤ schwartzDecayConst G 0 (N + r + finrank ℝ V + 1) *
          (((1 + ‖z‖ₑ) ^ N)⁻¹ * ((1 + ‖z‖ₑ) ^ (finrank ℝ V + 1))⁻¹) := by
        rw [mul_assoc]; gcongr
    _ ≤ schwartzDecayConst G 0 (N + r + finrank ℝ V + 1) *
          (((1 + ENNReal.ofReal ρ) ^ N)⁻¹ * ((1 + ‖z‖ₑ) ^ (finrank ℝ V + 1))⁻¹) := by gcongr
    _ = _ := by ring

/-- **Tails of Schwartz functions**: for every real `ρ`,
`∫_{‖z‖ ≥ ρ} |G(z)| ‖z‖^r dz ≤ C (1 + max(ρ, 0))^(-N)` with `C = Rd.tailConst G r N`. -/
theorem lintegral_tail_schwartz_le (G : 𝓢(V, ℂ)) (r N : ℕ) (ρ : ℝ) :
    ∫⁻ z in {z : V | ρ ≤ ‖z‖}, ‖G z‖ₑ * ‖z‖ₑ ^ r ≤
      tailConst G r N * ((1 + ENNReal.ofReal ρ) ^ N)⁻¹ := by
  have hs : MeasurableSet {z : V | ρ ≤ ‖z‖} := measurableSet_le measurable_const measurable_norm
  have hρ : ((1 + ENNReal.ofReal ρ) ^ N)⁻¹ ≠ ∞ := by
    refine ENNReal.inv_ne_top.2 (pow_ne_zero _ ?_)
    simp
  have hc : schwartzDecayConst G 0 (N + r + finrank ℝ V + 1) *
      ((1 + ENNReal.ofReal ρ) ^ N)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (schwartzDecayConst_ne_top _ _ _) hρ
  calc ∫⁻ z in {z : V | ρ ≤ ‖z‖}, ‖G z‖ₑ * ‖z‖ₑ ^ r
      ≤ ∫⁻ z in {z : V | ρ ≤ ‖z‖}, schwartzDecayConst G 0 (N + r + finrank ℝ V + 1) *
          ((1 + ENNReal.ofReal ρ) ^ N)⁻¹ * ((1 + ‖z‖ₑ) ^ (finrank ℝ V + 1))⁻¹ :=
        setLIntegral_mono' hs fun z hz => enorm_mul_enorm_pow_le_of_le G r N hz
    _ ≤ ∫⁻ z, schwartzDecayConst G 0 (N + r + finrank ℝ V + 1) *
          ((1 + ENNReal.ofReal ρ) ^ N)⁻¹ * ((1 + ‖z‖ₑ) ^ (finrank ℝ V + 1))⁻¹ :=
        setLIntegral_le_lintegral _ _
    _ = schwartzDecayConst G 0 (N + r + finrank ℝ V + 1) * ((1 + ENNReal.ofReal ρ) ^ N)⁻¹ *
          peetreIntegral V (finrank ℝ V + 1) := lintegral_const_mul' _ _ hc
    _ = tailConst G r N * ((1 + ENNReal.ofReal ρ) ^ N)⁻¹ := by rw [tailConst]; ring

/-- The mass of the dilated Peetre weight:
`∫ 2^(jn) (1 + 2^j ‖u‖)^(-N) du = ∫ (1 + ‖u‖)^(-N) du`. -/
theorem lintegral_dilate_peetre (j N : ℕ) :
    ∫⁻ u : V, 2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖u‖ₑ) ^ N)⁻¹ = peetreIntegral V N := by
  have h := lintegral_comp_two_pow_smul (V := V) (μ := volume) (fun u => ((1 + ‖u‖ₑ) ^ N)⁻¹) j
  simp only [enorm_two_pow_smul] at h
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), h, peetreIntegral,
    ← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), one_mul]

/-! ### Convolution of two Peetre bumps -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The integrand of the convolution of two Peetre bumps, pointwise: for `i ≤ j`,
`2^(jn) (1 + 2^j ‖y - w‖)^(-2N) 2^(in) (1 + 2^i ‖w‖)^(-N)` is at most
`2^(jn) (1 + 2^j ‖y - w‖)^(-N) 2^(in) (1 + 2^i ‖y‖)^(-N)`. -/
theorem peetre_mul_peetre_le {i j : ℕ} (hij : i ≤ j) (N n : ℕ) (y w : V) :
    2 ^ (j * n) * ((1 + 2 ^ j * ‖y - w‖ₑ) ^ (2 * N))⁻¹ *
        (2 ^ (i * n) * ((1 + 2 ^ i * ‖w‖ₑ) ^ N)⁻¹) ≤
      2 ^ (j * n) * ((1 + 2 ^ j * ‖y - w‖ₑ) ^ N)⁻¹ *
        (2 ^ (i * n) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹) := by
  have h2 : (2 : ℝ≥0∞) ^ i ≤ 2 ^ j := pow_le_pow_right₀ one_le_two hij
  have hP : ((1 + 2 ^ i * ‖w‖ₑ) ^ N)⁻¹ ≤
      (1 + 2 ^ j * ‖y - w‖ₑ) ^ N * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹ := by
    have hyw : ‖y‖ₑ ≤ ‖w‖ₑ + ‖y - w‖ₑ := by
      calc ‖y‖ₑ = ‖w + (y - w)‖ₑ := by rw [add_sub_cancel]
        _ ≤ ‖w‖ₑ + ‖y - w‖ₑ := eNorm_add_le _ _
    refine (ENNReal.inv_one_add_mul_pow_le (a := (2 : ℝ≥0∞) ^ i)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) eNorm_ne_top hyw N).trans ?_
    gcongr
  have hX := ENNReal.inv_one_add_pow_two_mul_mul_pow (a := (2 : ℝ≥0∞) ^ j * ‖y - w‖ₑ)
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) eNorm_ne_top) N
  calc 2 ^ (j * n) * ((1 + 2 ^ j * ‖y - w‖ₑ) ^ (2 * N))⁻¹ *
        (2 ^ (i * n) * ((1 + 2 ^ i * ‖w‖ₑ) ^ N)⁻¹)
      ≤ 2 ^ (j * n) * ((1 + 2 ^ j * ‖y - w‖ₑ) ^ (2 * N))⁻¹ *
          (2 ^ (i * n) * ((1 + 2 ^ j * ‖y - w‖ₑ) ^ N * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹)) := by
        gcongr
    _ = 2 ^ (j * n) * (((1 + 2 ^ j * ‖y - w‖ₑ) ^ (2 * N))⁻¹ * (1 + 2 ^ j * ‖y - w‖ₑ) ^ N) *
          (2 ^ (i * n) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹) := by ring
    _ = _ := by rw [hX]

/-- **Convolution of two Peetre bumps**: for `i ≤ j`, the integral
`∫ 2^(jn) (1 + 2^j ‖y - w‖)^(-2N) 2^(in) (1 + 2^i ‖w‖)^(-N) dw` is at most
`(∫ (1 + ‖u‖)^(-N) du) 2^(in) (1 + 2^i ‖y‖)^(-N)`, by Peetre's inequality and the substitution
`u = 2^j (y - w)`. -/
theorem lintegral_peetre_mul_le {i j : ℕ} (hij : i ≤ j) (N : ℕ) (y : V) :
    ∫⁻ w, 2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖y - w‖ₑ) ^ (2 * N))⁻¹ *
        (2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖w‖ₑ) ^ N)⁻¹) ≤
      peetreIntegral V N * 2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹ := by
  have hc : 2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      (ENNReal.inv_ne_top.2 (pow_ne_zero _ (ENNReal.one_add_ne_zero _)))
  calc _ ≤ ∫⁻ w, 2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖y - w‖ₑ) ^ N)⁻¹ *
          (2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹) :=
        lintegral_mono fun w => peetre_mul_peetre_le hij N _ y w
    _ = (∫⁻ w, 2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖y - w‖ₑ) ^ N)⁻¹) *
          (2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹) := lintegral_mul_const' _ _ hc
    _ = _ := by
        rw [lintegral_sub_left_eq_self
          (fun u => 2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖u‖ₑ) ^ N)⁻¹) y,
          lintegral_dilate_peetre, mul_assoc]

/-! ### Dilations of Schwartz functions -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Differences of dilated Schwartz functions**:
`|Δ_h^r G_{2^j}(y)| ≤ C ‖2^j h‖^r (1 + r ‖2^j h‖)^N 2^(jn) (1 + 2^j ‖y‖)^(-N)` with
`C = Rd.schwartzDecayConst G r N`, since `Δ_h^r G_{2^j} = (Δ_{2^j h}^r G)_{2^j}`. -/
theorem enorm_higherDiff_dilate_schwartz_le (G : 𝓢(V, ℂ)) (r N j : ℕ) (h y : V) :
    ‖(fwdDiff h)^[r] (dilate (2 ^ j) G) y‖ₑ ≤
      schwartzDecayConst G r N * ‖((2 : ℝ) ^ j) • h‖ₑ ^ r *
        (1 + r * ‖((2 : ℝ) ^ j) • h‖ₑ) ^ N *
          (2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹) := by
  rw [higherDiff_dilate, enorm_dilate_two_pow]
  have h1 := enorm_higherDiff_schwartz_le G r N (((2 : ℝ) ^ j) • h) (((2 : ℝ) ^ j) • y)
  rw [enorm_two_pow_smul j y] at h1
  calc 2 ^ (j * finrank ℝ V) *
        ‖(fwdDiff (((2 : ℝ) ^ j) • h))^[r] (G : V → ℂ) (((2 : ℝ) ^ j) • y)‖ₑ
      ≤ 2 ^ (j * finrank ℝ V) * (schwartzDecayConst G r N * ‖((2 : ℝ) ^ j) • h‖ₑ ^ r *
          (1 + r * ‖((2 : ℝ) ^ j) • h‖ₑ) ^ N * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹) := by gcongr
    _ = _ := by ring

/-- **Tails of dilated Schwartz functions**: for every real `a`,
`∫_{‖z‖ ≥ a} |G_{2^j}(z)| dz ≤ C (1 + max(2^j a, 0))^(-N)` with `C = Rd.tailConst G 0 N`, by the
substitution `u = 2^j z`. -/
theorem setLIntegral_enorm_dilate_schwartz_le (G : 𝓢(V, ℂ)) (N j : ℕ) (a : ℝ) :
    ∫⁻ z in {z : V | a ≤ ‖z‖}, ‖dilate (2 ^ j) G z‖ₑ ≤
      tailConst G 0 N * ((1 + ENNReal.ofReal (2 ^ j * a)) ^ N)⁻¹ := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have h2 := lintegral_tail_schwartz_le G 0 N (2 ^ j * a)
  simp only [pow_zero, mul_one] at h2
  simp_rw [enorm_dilate_two_pow]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
    setLIntegral_comp_smul (fun u => ‖G u‖ₑ) hpos.ne', smul_setOf_le_norm hpos,
    abs_of_pos (by positivity), ← pow_mul, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
    one_mul]
  exact h2

/-! ### Explicit bounds for the local means kernels -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- The constant `2 sup |m|` of the local means kernels, with the supremum of the moment kernel
`m` as its Schwartz seminorm. -/
noncomputable def kernelSupConst (L : ℕ) : ℝ :=
  2 * SchwartzMap.seminorm ℝ 0 0 (b.momentSchwartz L)

/-- The constant of the local means kernels is nonnegative. -/
theorem kernelSupConst_nonneg (L : ℕ) : 0 ≤ b.kernelSupConst L :=
  mul_nonneg zero_le_two (apply_nonneg _ _)

/-- `|m_{2^j}(y)| ≤ 2^(jn) sup |m|`. -/
theorem norm_scaled_le (L j : ℕ) (y : V) :
    ‖b.scaled L j y‖ ≤ SchwartzMap.seminorm ℝ 0 0 (b.momentSchwartz L) * 2 ^ (j * finrank ℝ V) := by
  have h := SchwartzMap.norm_le_seminorm ℝ (b.momentSchwartz L) (((2 : ℝ) ^ j) • y)
  rw [scaled, dilate, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← pow_mul,
    mul_comm]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- **The local means kernels are bounded**: `|k_j(y)| ≤ C 2^(jn)` with
`C = Rd.LocalMeansBump.kernelSupConst L`. -/
theorem norm_kernel_le (L j : ℕ) (y : V) :
    ‖b.kernel L j y‖ ≤ b.kernelSupConst L * 2 ^ (j * finrank ℝ V) := by
  have hS : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (b.momentSchwartz L) := apply_nonneg _ _
  cases j with
  | zero =>
    have h := b.norm_scaled_le L 0 y
    change ‖b.scaled L 0 y‖ ≤ 2 * SchwartzMap.seminorm ℝ 0 0 (b.momentSchwartz L) *
      2 ^ (0 * finrank ℝ V)
    simp only [zero_mul, pow_zero, mul_one] at h ⊢
    linarith
  | succ j =>
    change ‖b.scaled L (j + 1) y - b.scaled L j y‖ ≤
      2 * SchwartzMap.seminorm ℝ 0 0 (b.momentSchwartz L) * 2 ^ ((j + 1) * finrank ℝ V)
    have h1 := b.norm_scaled_le L (j + 1) y
    have h2 := b.norm_scaled_le L j y
    have hmono : (2 : ℝ) ^ (j * finrank ℝ V) ≤ 2 ^ ((j + 1) * finrank ℝ V) :=
      pow_le_pow_right₀ one_le_two (Nat.mul_le_mul_right _ (Nat.le_succ j))
    refine (norm_sub_le _ _).trans ?_
    nlinarith

/-- The local means kernels vanish outside `closedBall(0, 2 L R 2^(-j))`. -/
theorem kernel_eq_zero_of_lt (L j : ℕ) {y : V} (hy : 2 * L * b.radius / 2 ^ j < ‖y‖) :
    b.kernel L j y = 0 := by
  have hLR : 0 ≤ (L : ℝ) * b.radius := mul_nonneg (Nat.cast_nonneg L) b.radius_nonneg
  cases j with
  | zero =>
    refine b.scaled_eq_zero_of_lt L 0 (lt_of_le_of_lt ?_ hy)
    simp only [pow_zero, div_one]
    linarith
  | succ j =>
    change b.scaled L (j + 1) y - b.scaled L j y = 0
    have h1 : (L : ℝ) * b.radius / 2 ^ (j + 1) ≤ 2 * L * b.radius / 2 ^ (j + 1) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : 2 * (L : ℝ) * b.radius / 2 ^ (j + 1) = L * b.radius / 2 ^ j := by
      rw [pow_succ, mul_comm ((2 : ℝ) ^ j) 2, mul_assoc, mul_div_mul_left _ _ two_ne_zero]
    rw [b.scaled_eq_zero_of_lt L (j + 1) (h1.trans_lt hy),
      b.scaled_eq_zero_of_lt L j (h2 ▸ hy), sub_zero]

/-- `|k_j(y)| ≤ C 2^(jn)` in `[0, ∞]`, with `C = Rd.LocalMeansBump.kernelSupConst L`. -/
theorem enorm_kernel_le (L j : ℕ) (y : V) :
    ‖b.kernel L j y‖ₑ ≤ ENNReal.ofReal (b.kernelSupConst L) * 2 ^ (j * finrank ℝ V) := by
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal (b.norm_kernel_le L j y)).trans_eq ?_
  rw [ENNReal.ofReal_mul (b.kernelSupConst_nonneg L), ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat]

end LocalMeansBump

/-! ### Peetre weights at a dyadic scale -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `ofReal (1 + 2^j ‖y‖) = 1 + 2^j ‖y‖` in `[0, ∞]`. -/
theorem ofReal_one_add_two_pow_mul_norm (j : ℕ) (y : V) :
    ENNReal.ofReal (1 + 2 ^ j * ‖y‖) = 1 + 2 ^ j * ‖y‖ₑ := by
  rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat,
    ofReal_norm]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Far from the origin, for `j ≤ i`:
`(1 + 2^i ‖y‖ / 2)^(-N) ≤ 2^N (1 + 2^j ‖y‖)^(-N)`, from `1 + 2^j ‖y‖ ≤ 2 (1 + 2^i ‖y‖ / 2)`. -/
theorem inv_one_add_ofReal_half_pow_le {i j : ℕ} (hji : j ≤ i) (y : V) (N : ℕ) :
    ((1 + ENNReal.ofReal (2 ^ i * (‖y‖ / 2))) ^ N)⁻¹ ≤ 2 ^ N * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹ := by
  refine ENNReal.inv_le_mul_inv_of_le (pow_ne_zero _ two_ne_zero)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ?_
  rw [← mul_pow]
  refine pow_le_pow_left' ?_ N
  have h2 : (2 : ℝ) ^ j ≤ 2 ^ i := pow_le_pow_right₀ one_le_two hji
  have hy := norm_nonneg y
  rw [← ofReal_one_add_two_pow_mul_norm, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (by positivity), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul zero_le_two]
  exact ENNReal.ofReal_le_ofReal (by nlinarith)

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-! ### Local means kernels from one scale -/

/-- **Local means kernels from one scale**: for levels `j < i`, `f ∈ L_1` and a bound
`|f(x) - (m_{2^k} ⋆ f)(x)| ≤ C 2^(-(k-j)L) u(x)` almost everywhere at every scale `k ≥ j`,
almost everywhere `|k_i ⋆ f(x)| ≤ 2 · 2^L C 2^(-(i-j)L) u(x)`. The kernel
`k_i = m_{2^i} - m_{2^(i-1)}` is a difference of two moment kernels, so
`k_i ⋆ f = (f - m_{2^(i-1)} ⋆ f) - (f - m_{2^i} ⋆ f)`. -/
theorem ae_enorm_conv_kernel_le_of_scaled (L : ℕ) {f : V → ℂ} (hf : MemLp f 1 volume)
    {C : ℝ≥0∞} {u : V → ℝ≥0∞} {j : ℕ}
    (hB : ∀ k, j ≤ k → ∀ᵐ x ∂volume, ‖f x - conv (b.scaled L k) f volume x‖ₑ ≤
      C * dyadicWeight (-(L : ℝ)) (k - j) * u x) {i : ℕ} (hji : j < i) :
    ∀ᵐ x ∂volume, ‖conv (b.kernel L i) f volume x‖ₑ ≤
      2 * 2 ^ L * C * dyadicWeight (-(L : ℝ)) (i - j) * u x := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hji' : j ≤ i' := by omega
  filter_upwards [sub_conv_ae le_rfl ENNReal.one_ne_top (b.integrable_scaled L (i' + 1))
    (b.integrable_scaled L i') hf, hB i' hji', hB (i' + 1) (hji'.trans (Nat.le_succ i'))]
    with x h0 h1 h2
  have hsplit : conv (b.kernel L (i' + 1)) f volume x =
      (f x - conv (b.scaled L i') f volume x) - (f x - conv (b.scaled L (i' + 1)) f volume x) := by
    change conv (b.scaled L (i' + 1) - b.scaled L i') f volume x = _
    rw [h0, Pi.sub_apply]
    ring
  rw [hsplit]
  refine eNorm_sub_le.trans ((add_le_add h1 h2).trans ?_)
  have hw1 := ENNReal.dyadicWeight_neg_sub_le L hji' le_rfl
  have hw2 := ENNReal.dyadicWeight_neg_sub_le L hji' (Nat.le_succ i')
  calc C * dyadicWeight (-(L : ℝ)) (i' - j) * u x +
        C * dyadicWeight (-(L : ℝ)) (i' + 1 - j) * u x
      ≤ C * (2 ^ L * dyadicWeight (-(L : ℝ)) (i' + 1 - j)) * u x +
        C * (2 ^ L * dyadicWeight (-(L : ℝ)) (i' + 1 - j)) * u x := by gcongr
    _ = _ := by ring

/-! ### The cross kernel `k_j ⋆ Θ_i` -/

/-- One step of the moment case, pointwise in `z`: for `i ≤ k`,
`|g(z)| |Δ^L_{-2^(-k) z} Θ_i(y)| ≤ |g(z)| C R^L 2^(-(k-i)L) (1 + L R)^N 2^(in) (1 + 2^i ‖y‖)^(-N)`
with `C = Rd.schwartzDecayConst bandKernelS L N`, since the step of the dilated difference has
length `2^(i-k) ‖z‖ ≤ 2^(i-k) R` on the support of the bump `g`. -/
theorem enorm_mul_higherDiff_Theta_le (L N : ℕ) {i k : ℕ} (hik : i ≤ k) (z y : V) :
    ‖b.toFun z‖ₑ * ‖(fwdDiff (-((2 : ℝ) ^ k)⁻¹ • z))^[L] (Theta i) y‖ₑ ≤
      ‖b.toFun z‖ₑ * (schwartzDecayConst (bandKernelS (V := V)) L N *
        ENNReal.ofReal (b.radius ^ L) * dyadicWeight (-(L : ℝ)) (k - i) *
          ENNReal.ofReal ((1 + L * b.radius) ^ N) *
            (2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹)) := by
  by_cases hz : b.radius < ‖z‖
  · rw [b.eq_zero z hz, eNorm_zero, zero_mul, zero_mul]
  push Not at hz
  refine mul_le_mul_right ?_ _
  have hk : (2 : ℝ) ^ k = 2 ^ (k - i) * 2 ^ i := by rw [← pow_add, Nat.sub_add_cancel hik]
  have hv : ‖((2 : ℝ) ^ i) • (-((2 : ℝ) ^ k)⁻¹ • z)‖ ≤ b.radius / 2 ^ (k - i) := by
    rw [smul_smul, norm_smul, Real.norm_eq_abs, hk]
    rw [show (2 : ℝ) ^ i * -(2 ^ (k - i) * 2 ^ i)⁻¹ = -(2 ^ (k - i))⁻¹ by field_simp, abs_neg,
      abs_of_pos (by positivity), inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hz (by positivity)
  have hvR : b.radius / 2 ^ (k - i) ≤ b.radius :=
    div_le_self b.radius_nonneg (one_le_pow₀ one_le_two)
  have hve : ‖((2 : ℝ) ^ i) • (-((2 : ℝ) ^ k)⁻¹ • z)‖ₑ ≤
      ENNReal.ofReal b.radius * ((2 : ℝ≥0∞) ^ (k - i))⁻¹ := by
    rw [← ofReal_norm, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow zero_le_two,
      ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul b.radius_nonneg,
      ← div_eq_mul_inv]
    exact ENNReal.ofReal_le_ofReal hv
  have e1 : ‖((2 : ℝ) ^ i) • (-((2 : ℝ) ^ k)⁻¹ • z)‖ₑ ^ L ≤
      ENNReal.ofReal (b.radius ^ L) * dyadicWeight (-(L : ℝ)) (k - i) := by
    rw [ENNReal.dyadicWeight_neg_natCast, ENNReal.ofReal_pow b.radius_nonneg, ← mul_pow]
    gcongr
  have e2 : (1 + L * ‖((2 : ℝ) ^ i) • (-((2 : ℝ) ^ k)⁻¹ • z)‖ₑ) ^ N ≤
      ENNReal.ofReal ((1 + L * b.radius) ^ N) := by
    rw [ENNReal.ofReal_pow (by have := b.radius_nonneg; positivity),
      ENNReal.ofReal_add zero_le_one (by have := b.radius_nonneg; positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_mul (Nat.cast_nonneg L), ENNReal.ofReal_natCast, ← ofReal_norm]
    gcongr
    exact hv.trans hvR
  refine (enorm_higherDiff_dilate_schwartz_le (bandKernelS (V := V)) L N i _ y).trans ?_
  calc schwartzDecayConst (bandKernelS (V := V)) L N *
        ‖((2 : ℝ) ^ i) • (-((2 : ℝ) ^ k)⁻¹ • z)‖ₑ ^ L *
          (1 + L * ‖((2 : ℝ) ^ i) • (-((2 : ℝ) ^ k)⁻¹ • z)‖ₑ) ^ N *
            (2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹)
      ≤ schwartzDecayConst (bandKernelS (V := V)) L N *
        (ENNReal.ofReal (b.radius ^ L) * dyadicWeight (-(L : ℝ)) (k - i)) *
          ENNReal.ofReal ((1 + L * b.radius) ^ N) *
            (2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹) := by gcongr
    _ = _ := by ring

/-- **One scale of the moment case**: for `i ≤ k` and almost every `y`,
`|Θ_i(y) - (m_{2^k} ⋆ Θ_i)(y)| ≤ ‖g‖_1 C R^L 2^(-(k-i)L) (1 + L R)^N 2^(in)
(1 + 2^i ‖y‖)^(-N)` with `C = Rd.schwartzDecayConst bandKernelS L N`, by the averaged
differences of the moment kernel. -/
theorem ae_enorm_Theta_sub_conv_scaled_le (L N : ℕ) {i k : ℕ} (hik : i ≤ k) :
    ∀ᵐ y ∂volume, ‖Theta i y - conv (b.scaled L k) (Theta i) volume y‖ₑ ≤
      (∫⁻ z, ‖b.toFun z‖ₑ) * (schwartzDecayConst (bandKernelS (V := V)) L N *
        ENNReal.ofReal (b.radius ^ L) * dyadicWeight (-(L : ℝ)) (k - i) *
          ENNReal.ofReal ((1 + L * b.radius) ^ N) *
            (2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹)) := by
  filter_upwards [ae_enorm_sub_conv_dilate_momentKernel_le le_rfl ENNReal.one_ne_top b.integrable
    b.integral_eq_one (memLp_one_iff_integrable.2 (integrable_Theta (V := V) i)) L
    (c := (2 : ℝ) ^ k) (by positivity)] with y hy
  refine hy.trans ((lintegral_mono fun z => b.enorm_mul_higherDiff_Theta_le L N hik z y).trans ?_)
  rw [lintegral_mul_const'' _ b.contDiff.continuous.aestronglyMeasurable.eNorm]

/-- The constant `2 ‖g‖_1 (2R)^L (1 + 2LR)^N C` of the moment case of `k_j ⋆ Θ_i`, with
`C = Rd.schwartzDecayConst bandKernelS L N`. -/
noncomputable def kernelThetaMomentConst (L N : ℕ) : ℝ≥0∞ :=
  2 * (∫⁻ z, ‖b.toFun z‖ₑ) * ENNReal.ofReal ((2 * b.radius) ^ L) *
    ENNReal.ofReal ((1 + 2 * L * b.radius) ^ N) * schwartzDecayConst (bandKernelS (V := V)) L N

/-- The constant of the moment case of `k_j ⋆ Θ_i` is finite. -/
theorem kernelThetaMomentConst_ne_top (L N : ℕ) : b.kernelThetaMomentConst L N ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top b.integrable.hasFiniteIntegral.ne)
    ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) (schwartzDecayConst_ne_top _ _ _)

/-- **The moment case**: for `i < j` and almost every `y`,
`|(k_j ⋆ Θ_i)(y)| ≤ C 2^(-(j-i)L) 2^(in) (1 + 2^i ‖y‖)^(-N)` with
`C = Rd.LocalMeansBump.kernelThetaMomentConst L N`. The kernel `k_j = m_{2^j} - m_{2^(j-1)}` is
a difference of two moment kernels (`Rd.LocalMeansBump.ae_enorm_conv_kernel_le_of_scaled`), and
`Θ_i - m_{2^k} ⋆ Θ_i` averages differences of order `L` of `Θ_i` with steps of length at most
`2^(-k) R`. -/
theorem ae_enorm_conv_kernel_Theta_le_of_lt (L N : ℕ) {i j : ℕ} (hij : i < j) :
    ∀ᵐ y ∂volume, ‖conv (b.kernel L j) (Theta i) volume y‖ₑ ≤
      b.kernelThetaMomentConst L N * dyadicWeight (-(L : ℝ)) (j - i) *
        2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹ := by
  have hR0 := b.radius_nonneg
  have hR : ENNReal.ofReal ((1 + L * b.radius) ^ N) ≤
      ENNReal.ofReal ((1 + 2 * L * b.radius) ^ N) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity)
      (by nlinarith [mul_nonneg (Nat.cast_nonneg L : (0 : ℝ) ≤ L) hR0]) N)
  have h2R : ENNReal.ofReal ((2 * b.radius) ^ L) = 2 ^ L * ENNReal.ofReal (b.radius ^ L) := by
    rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat]
  filter_upwards [b.ae_enorm_conv_kernel_le_of_scaled L
    (memLp_one_iff_integrable.2 (integrable_Theta (V := V) i))
    (C := (∫⁻ z, ‖b.toFun z‖ₑ) * (schwartzDecayConst (bandKernelS (V := V)) L N *
      ENNReal.ofReal (b.radius ^ L) * ENNReal.ofReal ((1 + L * b.radius) ^ N)))
    (u := fun y => 2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹)
    (fun k hik => (b.ae_enorm_Theta_sub_conv_scaled_le L N hik).mono fun y hy =>
      hy.trans_eq (by ring)) hij] with y hy
  refine hy.trans ?_
  calc 2 * 2 ^ L * ((∫⁻ z, ‖b.toFun z‖ₑ) * (schwartzDecayConst (bandKernelS (V := V)) L N *
        ENNReal.ofReal (b.radius ^ L) * ENNReal.ofReal ((1 + L * b.radius) ^ N))) *
          dyadicWeight (-(L : ℝ)) (j - i) *
            (2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹)
      ≤ 2 * 2 ^ L * ((∫⁻ z, ‖b.toFun z‖ₑ) * (schwartzDecayConst (bandKernelS (V := V)) L N *
        ENNReal.ofReal (b.radius ^ L) * ENNReal.ofReal ((1 + 2 * L * b.radius) ^ N))) *
          dyadicWeight (-(L : ℝ)) (j - i) *
            (2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹) := by gcongr
    _ = _ := by rw [kernelThetaMomentConst, h2R]; ring

/-- The constant `C (‖Θ‖_1 (1 + 4LR)^N + 2^N T)` of the support case of `k_j ⋆ Θ_i`, with
`C = Rd.LocalMeansBump.kernelSupConst L` and `T = Rd.tailConst bandKernelS 0 N`. -/
noncomputable def kernelThetaSupportConst (L N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (b.kernelSupConst L) * (eLpNorm (bandKernel (V := V)) 1 volume *
    ENNReal.ofReal ((1 + 4 * L * b.radius) ^ N) + 2 ^ N * tailConst (bandKernelS (V := V)) 0 N)

/-- The constant of the support case of `k_j ⋆ Θ_i` is finite. -/
theorem kernelThetaSupportConst_ne_top (L N : ℕ) : b.kernelThetaSupportConst L N ≠ ∞ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top eLpNorm_bandKernel_ne_top
      ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) (tailConst_ne_top _ _ _)⟩)

/-- The support case near the origin: for `‖y‖ ≤ 4LR 2^(-j)`,
`∫ |Θ_i(z)| |k_j(y - z)| dz ≤ C ‖Θ‖_1 (1 + 4LR)^N 2^(jn) (1 + 2^j ‖y‖)^(-N)` with
`C = Rd.LocalMeansBump.kernelSupConst L`. -/
theorem lintegral_Theta_mul_kernel_le_near (L N i j : ℕ) {y : V}
    (hy : ‖y‖ ≤ 4 * L * b.radius / 2 ^ j) :
    ∫⁻ z, ‖Theta i z‖ₑ * ‖b.kernel L j (y - z)‖ₑ ≤
      ENNReal.ofReal (b.kernelSupConst L) * (eLpNorm (bandKernel (V := V)) 1 volume *
        ENNReal.ofReal ((1 + 4 * L * b.radius) ^ N)) *
          2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹ := by
  have hR0 := b.radius_nonneg
  have h4 : 2 ^ j * ‖y‖ₑ ≤ ENNReal.ofReal (4 * L * b.radius) := two_pow_mul_enorm_le_ofReal hy
  have h1 := ENNReal.one_le_ofReal_mul_inv_of_le (by positivity) h4 N
  calc ∫⁻ z, ‖Theta i z‖ₑ * ‖b.kernel L j (y - z)‖ₑ
      ≤ ∫⁻ z, ‖Theta i z‖ₑ * (ENNReal.ofReal (b.kernelSupConst L) * 2 ^ (j * finrank ℝ V)) :=
        lintegral_mono fun z => mul_le_mul_right (b.enorm_kernel_le L j (y - z)) _
    _ = eLpNorm (bandKernel (V := V)) 1 volume *
          (ENNReal.ofReal (b.kernelSupConst L) * 2 ^ (j * finrank ℝ V)) := by
        rw [lintegral_mul_const'' _ (continuous_Theta (V := V) i).measurable.eNorm.aemeasurable,
          ← eLpNorm_one_eq_lintegral_eNorm (continuous_Theta (V := V) i).aestronglyMeasurable,
          eLpNorm_Theta_one]
    _ = eLpNorm (bandKernel (V := V)) 1 volume *
          (ENNReal.ofReal (b.kernelSupConst L) * 2 ^ (j * finrank ℝ V)) * 1 := (mul_one _).symm
    _ ≤ eLpNorm (bandKernel (V := V)) 1 volume *
          (ENNReal.ofReal (b.kernelSupConst L) * 2 ^ (j * finrank ℝ V)) *
            (ENNReal.ofReal ((1 + 4 * L * b.radius) ^ N) * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹) := by
        gcongr
    _ = _ := by ring

/-- The support case far from the origin: for `j ≤ i` and `‖y‖ > 4LR 2^(-j)`,
`∫ |Θ_i(z)| |k_j(y - z)| dz ≤ C 2^N T 2^(jn) (1 + 2^j ‖y‖)^(-N)` with
`C = Rd.LocalMeansBump.kernelSupConst L` and `T = Rd.tailConst bandKernelS 0 N`: the integrand
vanishes unless `‖z‖ ≥ ‖y‖ / 2`, where the tail of `Θ_i` is small. -/
theorem lintegral_Theta_mul_kernel_le_far (L N : ℕ) {i j : ℕ} (hji : j ≤ i) {y : V}
    (hy : 4 * L * b.radius / 2 ^ j < ‖y‖) :
    ∫⁻ z, ‖Theta i z‖ₑ * ‖b.kernel L j (y - z)‖ₑ ≤
      ENNReal.ofReal (b.kernelSupConst L) * (2 ^ N * tailConst (bandKernelS (V := V)) 0 N) *
        2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹ := by
  have hs : MeasurableSet {z : V | ‖y‖ / 2 ≤ ‖z‖} :=
    measurableSet_le measurable_const measurable_norm
  have hc : ENNReal.ofReal (b.kernelSupConst L) * 2 ^ (j * finrank ℝ V) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hpt : ∀ z, ‖Theta i z‖ₑ * ‖b.kernel L j (y - z)‖ₑ ≤
      {z : V | ‖y‖ / 2 ≤ ‖z‖}.indicator (fun z => ‖Theta i z‖ₑ) z *
        (ENNReal.ofReal (b.kernelSupConst L) * 2 ^ (j * finrank ℝ V)) := fun z => by
    by_cases hz : ‖y‖ / 2 ≤ ‖z‖
    · rw [Set.indicator_of_mem (show z ∈ {z : V | ‖y‖ / 2 ≤ ‖z‖} from hz)]
      exact mul_le_mul_right (b.enorm_kernel_le L j (y - z)) _
    · have hyz : 2 * L * b.radius / 2 ^ j < ‖y - z‖ := by
        have h1 := norm_sub_norm_le y z
        have h2 : 2 * L * b.radius / 2 ^ j = (4 * L * b.radius / 2 ^ j) / 2 := by ring
        push Not at hz
        linarith
      rw [b.kernel_eq_zero_of_lt L j hyz, eNorm_zero, mul_zero]
      exact zero_le
  have htail := setLIntegral_enorm_dilate_schwartz_le (bandKernelS (V := V)) N i (‖y‖ / 2)
  calc ∫⁻ z, ‖Theta i z‖ₑ * ‖b.kernel L j (y - z)‖ₑ
      ≤ ∫⁻ z, {z : V | ‖y‖ / 2 ≤ ‖z‖}.indicator (fun z => ‖Theta i z‖ₑ) z *
          (ENNReal.ofReal (b.kernelSupConst L) * 2 ^ (j * finrank ℝ V)) := lintegral_mono hpt
    _ = (∫⁻ z in {z : V | ‖y‖ / 2 ≤ ‖z‖}, ‖Theta i z‖ₑ) *
          (ENNReal.ofReal (b.kernelSupConst L) * 2 ^ (j * finrank ℝ V)) := by
        rw [lintegral_mul_const' _ _ hc, lintegral_indicator hs]
    _ ≤ tailConst (bandKernelS (V := V)) 0 N * (2 ^ N * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹) *
          (ENNReal.ofReal (b.kernelSupConst L) * 2 ^ (j * finrank ℝ V)) := by
        gcongr
        exact htail.trans (mul_le_mul_right (inv_one_add_ofReal_half_pow_le hji y N) _)
    _ = _ := by ring

/-- **The support case**: for `j ≤ i` and every `y`,
`|(k_j ⋆ Θ_i)(y)| ≤ C 2^(jn) (1 + 2^j ‖y‖)^(-N)` with
`C = Rd.LocalMeansBump.kernelThetaSupportConst L N`: `k_j` is bounded by `2^(jn)` and supported
in `closedBall(0, 2LR 2^(-j))`, and `Θ_i` has small tails. -/
theorem enorm_conv_kernel_Theta_le_of_le (L N : ℕ) {i j : ℕ} (hji : j ≤ i) (y : V) :
    ‖conv (b.kernel L j) (Theta i) volume y‖ₑ ≤
      b.kernelThetaSupportConst L N * 2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹ := by
  rw [conv_comm]
  refine (enorm_conv_le_lintegral _ _ y).trans ?_
  rw [kernelThetaSupportConst]
  by_cases hy : ‖y‖ ≤ 4 * L * b.radius / 2 ^ j
  · refine (b.lintegral_Theta_mul_kernel_le_near L N i j hy).trans ?_
    gcongr
    exact le_self_add
  · refine (b.lintegral_Theta_mul_kernel_le_far L N hji (not_le.1 hy)).trans ?_
    gcongr
    exact le_add_self

/-- The constant of the cross kernel `k_j ⋆ Θ_i`: the sum of the constants of the moment case
and of the support case. -/
noncomputable def kernelThetaConst (L N : ℕ) : ℝ≥0∞ :=
  b.kernelThetaMomentConst L N + b.kernelThetaSupportConst L N

/-- The constant of the cross kernel `k_j ⋆ Θ_i` is finite. -/
theorem kernelThetaConst_ne_top (L N : ℕ) : b.kernelThetaConst L N ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨b.kernelThetaMomentConst_ne_top L N, b.kernelThetaSupportConst_ne_top L N⟩

/-- **The cross kernel `k_j ⋆ Θ_i`**: for all levels `i, j` and almost every `y`,
`|(k_j ⋆ Θ_i)(y)| ≤ C c_{ji} 2^(min(i,j) n) (1 + 2^min(i,j) ‖y‖)^(-N)` with
`c_{ji} = 2^(-(j-i)L)` for `i ≤ j`, `c_{ji} = 1` for `i > j`, and
`C = Rd.LocalMeansBump.kernelThetaConst L N`. -/
theorem enorm_conv_kernel_Theta_le (L N i j : ℕ) :
    ∀ᵐ y ∂volume, ‖conv (b.kernel L j) (Theta i) volume y‖ₑ ≤
      b.kernelThetaConst L N * (if i ≤ j then dyadicWeight (-(L : ℝ)) (j - i) else 1) *
        2 ^ (min i j * finrank ℝ V) * ((1 + 2 ^ (min i j) * ‖y‖ₑ) ^ N)⁻¹ := by
  rcases lt_or_ge i j with hij | hji
  · filter_upwards [b.ae_enorm_conv_kernel_Theta_le_of_lt L N hij] with y hy
    simp only [hij.le, ↓reduceIte, min_eq_left hij.le]
    refine hy.trans ?_
    gcongr
    exact le_self_add
  · refine Filter.Eventually.of_forall fun y =>
      (b.enorm_conv_kernel_Theta_le_of_le L N hji y).trans ?_
    rw [min_eq_right hji]
    have hw : 1 ≤ (if i ≤ j then dyadicWeight (-(L : ℝ)) (j - i) else 1) := by
      split_ifs with h
      · rw [show j - i = 0 by omega, ENNReal.dyadicWeight_zero_right]
      · exact le_rfl
    calc b.kernelThetaSupportConst L N * 2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹
        = b.kernelThetaSupportConst L N * 1 * 2 ^ (j * finrank ℝ V) *
            ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹ := by rw [mul_one]
      _ ≤ _ := by
          gcongr
          exact le_add_self

end LocalMeansBump

/-! ### The vanishing of `ψ_j ⋆ μ_{2^(j-2)}` -/

/-- **The Fourier transform of a dilated moment kernel**: for an integrable `g` and `c > 0`,
`𝓕(m_c)(ξ) = ∑_{l < L} a_l 𝓕g(((l + 1)/c) ξ)` with the coefficients `a_l = Rd.jacksonCoeff L l`. -/
theorem fourier_dilate_momentKernel {g : V → ℂ} (hg : Integrable g) (L : ℕ) {c : ℝ} (hc : 0 < c)
    (ξ : V) :
    𝓕 (dilate c (momentKernel g L)) ξ =
      ∑ l ∈ Finset.range L, jacksonCoeff L l * 𝓕 g ((((l : ℝ) + 1) / c) • ξ) := by
  have hcl : ∀ l : ℕ, 0 < c / ((l : ℝ) + 1) := fun l => by positivity
  have hint : ∀ l ∈ Finset.range L, Integrable (fun v : V =>
      𝐞 (-inner ℝ v ξ) • (jacksonCoeff L l * dilate (c / ((l : ℝ) + 1)) g v)) := fun l _ =>
    (Real.fourierIntegral_convergent_iff ξ).2 ((integrable_dilate hg (hcl l).ne').const_mul _)
  rw [dilate_momentKernel, Real.fourier_eq]
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h : ∀ v : V, 𝐞 (-inner ℝ v ξ) • (jacksonCoeff L l * dilate (c / ((l : ℝ) + 1)) g v) =
      jacksonCoeff L l * (𝐞 (-inner ℝ v ξ) • dilate (c / ((l : ℝ) + 1)) g v) := fun v => by
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  simp_rw [h]
  rw [integral_const_mul, ← Real.fourier_eq, fourier_dilate g (hcl l), inv_div]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Moment kernels of continuous functions are continuous. -/
theorem continuous_momentKernel {g : V → ℂ} (hg : Continuous g) (L : ℕ) :
    Continuous (momentKernel g L) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_dilate hg _)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Moment kernels of bounded functions are bounded. -/
theorem bddAbove_momentKernel {g : V → ℂ} (hg : BddAbove (Set.range fun x => ‖g x‖)) (L : ℕ) :
    BddAbove (Set.range fun x => ‖momentKernel g L x‖) := by
  choose B hB using fun l : ℕ => bddAbove_dilate hg (1 / ((l : ℝ) + 1))
  refine ⟨∑ l ∈ Finset.range L, ‖jacksonCoeff L l‖ * B l, Set.forall_mem_range.2 fun x => ?_⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB l (Set.mem_range_self x)) (norm_nonneg _)

/-- The moment kernel `μ = ∑_{l<L} a_l Φ_{1/(l+1)}` of order `L` built from the
Littlewood–Paley kernel `Φ = Rd.lpKernel`. -/
noncomputable def lpMoment (L : ℕ) : V → ℂ := momentKernel lpKernel L

/-- The dilations `μ_{2^k} = 2^(kn) μ(2^k ·)` of `Rd.lpMoment`. -/
noncomputable def lpMomentScaled (L k : ℕ) : V → ℂ := dilate (2 ^ k) (lpMoment L)

/-- The dilated moment kernels of `Φ` are integrable. -/
theorem integrable_lpMomentScaled (L k : ℕ) : Integrable (lpMomentScaled (V := V) L k) :=
  integrable_dilate (integrable_momentKernel integrable_lpKernel L) (by positivity)

/-- The dilated moment kernels of `Φ` are continuous. -/
theorem continuous_lpMomentScaled (L k : ℕ) : Continuous (lpMomentScaled (V := V) L k) :=
  continuous_dilate (continuous_momentKernel continuous_lpKernel L) _

/-- The dilated moment kernels of `Φ` are bounded. -/
theorem bddAbove_lpMomentScaled (L k : ℕ) :
    BddAbove (Set.range fun x => ‖lpMomentScaled (V := V) L k x‖) :=
  bddAbove_dilate (bddAbove_momentKernel bddAbove_lpKernel L) _

/-- `𝓕μ_{2^j}` vanishes outside the ball of radius `2^(j+1)`: every term has
`‖((l + 1)/2^j) ξ‖ ≥ 2`, where `𝓕Φ = χ_{1,2}` vanishes. -/
theorem fourier_lpMomentScaled_eq_zero (L : ℕ) {j : ℕ} {ξ : V} (h : 2 ^ (j + 1) ≤ ‖ξ‖) :
    𝓕 (lpMomentScaled (V := V) L j) ξ = 0 := by
  rw [lpMomentScaled, lpMoment,
    fourier_dilate_momentKernel integrable_lpKernel L (by positivity : (0 : ℝ) < 2 ^ j)]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [fourier_lpKernel, cutoff_eq_zero _ _ ?_, mul_zero]
  rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div,
    le_div_iff₀ (by positivity)]
  have h1 : (1 : ℝ) ≤ (l : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg l)
  calc (2 : ℝ) * 2 ^ j = 2 ^ (j + 1) := by ring
    _ ≤ ‖ξ‖ := h
    _ ≤ ((l : ℝ) + 1) * ‖ξ‖ := le_mul_of_one_le_left (norm_nonneg _) h1

/-- **High blocks annihilate the moment kernels of `Φ`**: `ψ_{j+2} ⋆ μ_{2^j} = 0`, since
`𝓕ψ_{j+2}` vanishes on the ball of radius `2^(j+1)` and `𝓕μ_{2^j}` outside it. -/
theorem conv_psi_lpMomentScaled (L j : ℕ) :
    conv (psi (V := V) (j + 2)) (lpMomentScaled L j) volume = 0 := by
  have h0 : 𝓕 (0 : V → ℂ) = 0 := funext fun ξ => by simp [Real.fourier_eq]
  refine conv_eq_of_fourier (integrable_psi _) (integrable_lpMomentScaled L j)
    (continuous_lpMomentScaled L j) (bddAbove_lpMomentScaled L j) (integrable_zero _ _ _)
    continuous_zero ?_ fun ξ => ?_
  · rw [h0]
    exact integrable_zero _ _ _
  · rw [h0, Pi.zero_apply]
    by_cases hξ : ‖ξ‖ ≤ 2 ^ (j + 1)
    · rw [show j + 2 = j + 1 + 1 from rfl, fourier_psi_succ_eq_zero hξ, zero_mul]
    · rw [fourier_lpMomentScaled_eq_zero L (not_le.1 hξ).le, mul_zero]

/-! ### Decay of the Littlewood–Paley blocks -/

variable (V) in
/-- The constant `(1 + 2^N) C` of the decay of the blocks `ψ_j`, with
`C = Rd.schwartzDecayConst lpKernelS 0 N`. -/
noncomputable def psiDecayConst (N : ℕ) : ℝ≥0∞ :=
  (1 + 2 ^ N) * schwartzDecayConst (lpKernelS (V := V)) 0 N

/-- The decay constant of the blocks is finite. -/
theorem psiDecayConst_ne_top (N : ℕ) : psiDecayConst V N ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.pow_ne_top ENNReal.ofNat_ne_top⟩) (schwartzDecayConst_ne_top _ _ _)

/-- **Decay of the Littlewood–Paley blocks**:
`|ψ_j(y)| ≤ C 2^(jn) (1 + 2^j ‖y‖)^(-N)` with `C = Rd.psiDecayConst V N`; `ψ_j` is the
difference of the dilations of `Φ` at the scales `2^j` and `2^(j-1)`. -/
theorem enorm_psi_le (j N : ℕ) (y : V) :
    ‖psi j y‖ₑ ≤ psiDecayConst V N * 2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹ := by
  have hPhi : ∀ k, ‖Phi (V := V) k y‖ₑ ≤ schwartzDecayConst (lpKernelS (V := V)) 0 N *
      2 ^ (k * finrank ℝ V) * ((1 + 2 ^ k * ‖y‖ₑ) ^ N)⁻¹ := fun k =>
    enorm_dilate_schwartz_le (lpKernelS (V := V)) N k y
  have hS : schwartzDecayConst (lpKernelS (V := V)) 0 N ≤ psiDecayConst V N :=
    le_mul_of_one_le_left zero_le le_self_add
  cases j with
  | zero =>
    refine (hPhi 0).trans ?_
    gcongr
  | succ j =>
    change ‖Phi (V := V) (j + 1) y - Phi j y‖ₑ ≤ _
    have hW : ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹ ≤ 2 ^ N * ((1 + 2 ^ (j + 1) * ‖y‖ₑ) ^ N)⁻¹ := by
      have h := ENNReal.inv_one_add_mul_pow_le_two_pow (2 ^ j) ‖y‖ₑ N
      rwa [← pow_succ'] at h
    have hX : (2 : ℝ≥0∞) ^ (j * finrank ℝ V) ≤ 2 ^ ((j + 1) * finrank ℝ V) :=
      pow_le_pow_right₀ one_le_two (Nat.mul_le_mul_right _ (Nat.le_succ j))
    calc ‖Phi (V := V) (j + 1) y - Phi j y‖ₑ ≤ ‖Phi (V := V) (j + 1) y‖ₑ + ‖Phi (V := V) j y‖ₑ :=
          eNorm_sub_le
      _ ≤ schwartzDecayConst (lpKernelS (V := V)) 0 N * 2 ^ ((j + 1) * finrank ℝ V) *
            ((1 + 2 ^ (j + 1) * ‖y‖ₑ) ^ N)⁻¹ +
          schwartzDecayConst (lpKernelS (V := V)) 0 N * 2 ^ ((j + 1) * finrank ℝ V) *
            (2 ^ N * ((1 + 2 ^ (j + 1) * ‖y‖ₑ) ^ N)⁻¹) := by
          gcongr
          · exact hPhi (j + 1)
          · exact (hPhi j).trans (by gcongr)
      _ = psiDecayConst V N * 2 ^ ((j + 1) * finrank ℝ V) *
            ((1 + 2 ^ (j + 1) * ‖y‖ₑ) ^ N)⁻¹ := by rw [psiDecayConst]; ring

/-! ### The cross kernel `ψ_j ⋆ η_i` -/

/-- **Integrals against a kernel of small support**: if `η` vanishes outside
`closedBall(0, ρ 2^(-k))` and `|ψ(z)| ≤ C 2^(kn) (1 + 2^k ‖z‖)^(-N)`, then
`∫ |η(w)| |ψ(y - w)| dw ≤ ‖η‖_1 C (1 + ρ)^N 2^(kn) (1 + 2^k ‖y‖)^(-N)`, by Peetre's inequality
`(1 + 2^k ‖y - w‖)^(-N) ≤ (1 + 2^k ‖w‖)^N (1 + 2^k ‖y‖)^(-N)`. -/
theorem lintegral_mul_peetre_le_of_support {η ψ : V → ℂ} (hη : AEStronglyMeasurable η volume)
    {k N : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hηs : ∀ w, ρ / 2 ^ k < ‖w‖ → η w = 0) {C : ℝ≥0∞}
    (hψ : ∀ z, ‖ψ z‖ₑ ≤ C * 2 ^ (k * finrank ℝ V) * ((1 + 2 ^ k * ‖z‖ₑ) ^ N)⁻¹) (y : V) :
    ∫⁻ w, ‖η w‖ₑ * ‖ψ (y - w)‖ₑ ≤ (∫⁻ w, ‖η w‖ₑ) * (C * ENNReal.ofReal ((1 + ρ) ^ N) *
      2 ^ (k * finrank ℝ V) * ((1 + 2 ^ k * ‖y‖ₑ) ^ N)⁻¹) := by
  rw [← lintegral_mul_const'' _ hη.eNorm]
  refine lintegral_mono fun w => ?_
  by_cases hw : ρ / 2 ^ k < ‖w‖
  · rw [hηs w hw, eNorm_zero, zero_mul, zero_mul]
  push Not at hw
  refine mul_le_mul_right ((hψ (y - w)).trans ?_) _
  have hkw : 2 ^ k * ‖w‖ₑ ≤ ENNReal.ofReal ρ := two_pow_mul_enorm_le_ofReal hw
  have hP := inv_one_add_mul_enorm_sub_pow_le (a := (2 : ℝ≥0∞) ^ k)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) y w N
  have hρ' : (1 + 2 ^ k * ‖w‖ₑ) ^ N ≤ ENNReal.ofReal ((1 + ρ) ^ N) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add zero_le_one hρ, ENNReal.ofReal_one]
    gcongr
  calc C * 2 ^ (k * finrank ℝ V) * ((1 + 2 ^ k * ‖y - w‖ₑ) ^ N)⁻¹
      ≤ C * 2 ^ (k * finrank ℝ V) * ((1 + 2 ^ k * ‖w‖ₑ) ^ N * ((1 + 2 ^ k * ‖y‖ₑ) ^ N)⁻¹) := by
        gcongr
    _ ≤ C * 2 ^ (k * finrank ℝ V) * (ENNReal.ofReal ((1 + ρ) ^ N) *
          ((1 + 2 ^ k * ‖y‖ₑ) ^ N)⁻¹) := by gcongr
    _ = _ := by ring

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- The constant `C (1 + 2LR)^N 2 ‖m‖_1` of the support cases of `ψ_j ⋆ η_i`, with
`C = Rd.psiDecayConst V N`. -/
noncomputable def psiDualSupportConst (L N : ℕ) : ℝ≥0∞ :=
  psiDecayConst V N * ENNReal.ofReal ((1 + 2 * L * b.radius) ^ N) *
    (2 * eLpNorm (momentKernel b.toFun L) 1 volume)

/-- The constant of the support cases of `ψ_j ⋆ η_i` is finite. -/
theorem psiDualSupportConst_ne_top (L N : ℕ) : b.psiDualSupportConst L N ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (psiDecayConst_ne_top N) ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (eLpNorm_momentKernel_ne_top b.integrable L))

/-- `∫ |η_i| ≤ 2 ‖m‖_1`. -/
theorem lintegral_enorm_dual_le (L i : ℕ) :
    ∫⁻ w, ‖b.dual L i w‖ₑ ≤ 2 * eLpNorm (momentKernel b.toFun L) 1 volume := by
  rw [← eLpNorm_one_eq_lintegral_eNorm (b.continuous_dual L i).aestronglyMeasurable]
  exact b.eLpNorm_dual_one_le L i

/-- **The case `i > j`**: `|(ψ_j ⋆ η_i)(y)| ≤ C 2^(jn) (1 + 2^j ‖y‖)^(-N)` with
`C = Rd.LocalMeansBump.psiDualSupportConst L N`: `η_i` is supported in `closedBall(0, 2LR
2^(-i))`, where
the Peetre weight at the scale `2^j` changes by at most `(1 + 2LR)^N`. -/
theorem enorm_conv_psi_dual_le_of_lt (L N : ℕ) {i j : ℕ} (hji : j < i) (y : V) :
    ‖conv (psi j) (b.dual L i) volume y‖ₑ ≤
      b.psiDualSupportConst L N * 2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹ := by
  rw [conv_comm]
  refine (enorm_conv_le_lintegral _ _ y).trans ?_
  have hρ : 0 ≤ 2 * (L : ℝ) * b.radius := by have := b.radius_nonneg; positivity
  have hs : ∀ w, 2 * L * b.radius / 2 ^ j < ‖w‖ → b.dual L i w = 0 := fun w hw =>
    b.dual_eq_zero_of_lt L i (lt_of_le_of_lt (div_le_div_of_nonneg_left hρ (by positivity)
      (pow_le_pow_right₀ one_le_two hji.le)) hw)
  refine (lintegral_mul_peetre_le_of_support (b.continuous_dual L i).aestronglyMeasurable hρ hs
    (fun z => enorm_psi_le j N z) y).trans ?_
  calc (∫⁻ w, ‖b.dual L i w‖ₑ) * (psiDecayConst V N *
        ENNReal.ofReal ((1 + 2 * L * b.radius) ^ N) * 2 ^ (j * finrank ℝ V) *
          ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹)
      ≤ (2 * eLpNorm (momentKernel b.toFun L) 1 volume) * (psiDecayConst V N *
        ENNReal.ofReal ((1 + 2 * L * b.radius) ^ N) * 2 ^ (j * finrank ℝ V) *
          ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹) := by gcongr; exact b.lintegral_enorm_dual_le L i
    _ = _ := by rw [psiDualSupportConst]; ring

/-- **The case `i ≤ j ≤ 1`**: `|(ψ_j ⋆ η_i)(y)| ≤ 2^(n+L') C 2^(-(j-i)L') 2^(in)
(1 + 2^i ‖y‖)^(-N)` with `C = Rd.LocalMeansBump.psiDualSupportConst L N`, as in the case `i > j`
with the Peetre weight at the scale `2^i`. -/
theorem enorm_conv_psi_dual_le_of_le_one (L N L' : ℕ) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 1)
    (y : V) :
    ‖conv (psi j) (b.dual L i) volume y‖ₑ ≤
      2 ^ (finrank ℝ V + L') * b.psiDualSupportConst L N * dyadicWeight (-(L' : ℝ)) (j - i) *
        2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹ := by
  rw [conv_comm]
  refine (enorm_conv_le_lintegral _ _ y).trans ?_
  have hρ : 0 ≤ 2 * (L : ℝ) * b.radius := by have := b.radius_nonneg; positivity
  have hs : ∀ w, 2 * L * b.radius / 2 ^ i < ‖w‖ → b.dual L i w = 0 := fun w hw =>
    b.dual_eq_zero_of_lt L i hw
  have hψ : ∀ z : V, ‖psi j z‖ₑ ≤ 2 ^ finrank ℝ V * psiDecayConst V N * 2 ^ (i * finrank ℝ V) *
      ((1 + 2 ^ i * ‖z‖ₑ) ^ N)⁻¹ := fun z => by
    have h2 : (2 : ℝ≥0∞) ^ (j * finrank ℝ V) ≤ 2 ^ finrank ℝ V * 2 ^ (i * finrank ℝ V) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ one_le_two (by nlinarith)
    refine (enorm_psi_le j N z).trans ?_
    calc psiDecayConst V N * 2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖z‖ₑ) ^ N)⁻¹
        ≤ psiDecayConst V N * (2 ^ finrank ℝ V * 2 ^ (i * finrank ℝ V)) *
            ((1 + 2 ^ i * ‖z‖ₑ) ^ N)⁻¹ :=
          mul_le_mul' (mul_le_mul_right h2 _)
            (ENNReal.inv_one_add_mul_pow_anti (pow_le_pow_right₀ one_le_two hij) _ N)
      _ = _ := by ring
  refine (lintegral_mul_peetre_le_of_support (b.continuous_dual L i).aestronglyMeasurable hρ hs
    hψ y).trans ?_
  have hw := ENNReal.one_le_two_pow_mul_dyadicWeight_neg L' (m := j - i) (by omega)
  calc (∫⁻ w, ‖b.dual L i w‖ₑ) * (2 ^ finrank ℝ V * psiDecayConst V N *
        ENNReal.ofReal ((1 + 2 * L * b.radius) ^ N) * 2 ^ (i * finrank ℝ V) *
          ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹)
      ≤ (2 * eLpNorm (momentKernel b.toFun L) 1 volume) * (2 ^ finrank ℝ V *
        psiDecayConst V N * ENNReal.ofReal ((1 + 2 * L * b.radius) ^ N) *
          2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹) * 1 := by
        rw [mul_one]; gcongr; exact b.lintegral_enorm_dual_le L i
    _ ≤ (2 * eLpNorm (momentKernel b.toFun L) 1 volume) * (2 ^ finrank ℝ V *
        psiDecayConst V N * ENNReal.ofReal ((1 + 2 * L * b.radius) ^ N) *
          2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹) *
            (2 ^ L' * dyadicWeight (-(L' : ℝ)) (j - i)) := by gcongr
    _ = _ := by rw [psiDualSupportConst, pow_add]; ring

end LocalMeansBump

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- For `L ≥ 1` and `i ≤ j' + 2`: `(1 + 2^j' ‖w‖ / (2L))^(-N) ≤ (8L)^N (1 + 2^i ‖w‖)^(-N)`,
from `1 + 2^i ‖w‖ ≤ 8L + 4 · 2^j' ‖w‖`. -/
theorem inv_one_add_ofReal_div_pow_le {L i j' : ℕ} (hL : 1 ≤ L) (hij : i ≤ j' + 2) (w : V)
    (N : ℕ) :
    ((1 + ENNReal.ofReal (2 ^ j' * ‖w‖ / (2 * L))) ^ N)⁻¹ ≤
      (8 * (L : ℝ≥0∞)) ^ N * ((1 + 2 ^ i * ‖w‖ₑ) ^ N)⁻¹ := by
  have hL0 : (8 * (L : ℝ≥0∞)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.2 (by omega))
  refine ENNReal.inv_le_mul_inv_of_le (pow_ne_zero _ hL0)
    (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top L))) ?_
  rw [← mul_pow]
  refine pow_le_pow_left' ?_ N
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h2 : (2 : ℝ) ^ i ≤ 4 * 2 ^ j' := by
    calc (2 : ℝ) ^ i ≤ 2 ^ (j' + 2) := pow_le_pow_right₀ one_le_two hij
      _ = 4 * 2 ^ j' := by ring
  have hw := norm_nonneg w
  rw [← ofReal_one_add_two_pow_mul_norm, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have he : 8 * (L : ℝ) * (1 + 2 ^ j' * ‖w‖ / (2 * L)) = 8 * L + 4 * (2 ^ j' * ‖w‖) := by
    field_simp
    ring
  rw [he]
  nlinarith

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- **Differences of the dual kernels**, one step of the moment identity of `Φ`:
`|Δ^L'_{-2^(-j') z} η_i(w)| ≤ A 2^(in) 2^(iL') 2^(-j'L') ‖z‖^L'` with
`A = Rd.LocalMeansBump.dualDerivConst L L'`, by the bound of differences through derivatives. -/
theorem enorm_higherDiff_dual_le (L L' i j' : ℕ) (z w : V) :
    ‖(fwdDiff (-((2 : ℝ) ^ j')⁻¹ • z))^[L'] (b.dual L i) w‖ₑ ≤
      ENNReal.ofReal (b.dualDerivConst L L') * 2 ^ (i * finrank ℝ V) * dyadicWeight (L' : ℝ) i *
        dyadicWeight (-(L' : ℝ)) j' * ‖z‖ₑ ^ L' := by
  have hA := b.dualDerivConst_nonneg L L'
  have h := norm_higherDiff_le_of_iteratedFDeriv (b.contDiff_dual L i)
    (fun x => b.norm_iteratedFDeriv_dual_le L L' le_rfl i x) (-((2 : ℝ) ^ j')⁻¹ • z) w
  have hh : ‖-((2 : ℝ) ^ j')⁻¹ • z‖ = ((2 : ℝ) ^ j')⁻¹ * ‖z‖ := by
    rw [norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg (by positivity)]
  rw [hh, Nat.mul_add, pow_add, mul_pow] at h
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal h).trans_eq ?_
  rw [mul_assoc (b.dualDerivConst L L'), ENNReal.ofReal_mul hA,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ofReal_two_pow_mul i L',
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ j')⁻¹),
    ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < 2 ^ j'),
    ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm, ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← ENNReal.dyadicWeight_neg_natCast]
  ring

/-- **Support of the differences of the dual kernels**: `Δ^L'_h η_i(w) = 0` for
`‖w‖ > 2LR 2^(-i) + L' ‖h‖`, since all points `w + l h`, `l ≤ L'`, lie outside the support of
`η_i`. -/
theorem higherDiff_dual_eq_zero (L L' i : ℕ) {h w : V}
    (hw : 2 * L * b.radius / 2 ^ i + L' * ‖h‖ < ‖w‖) :
    (fwdDiff h)^[L'] (b.dual L i) w = 0 := by
  rw [higherDiff_apply]
  refine Finset.sum_eq_zero fun l hl => ?_
  have hl' : (l : ℝ) ≤ L' := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  rw [b.dual_eq_zero_of_lt L i, mul_zero]
  have h1 : ‖w‖ ≤ ‖w + (l : ℝ) • h‖ + l * ‖h‖ := by
    calc ‖w‖ = ‖(w + (l : ℝ) • h) - (l : ℝ) • h‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖w + (l : ℝ) • h‖ + ‖(l : ℝ) • h‖ := norm_sub_le _ _
      _ = ‖w + (l : ℝ) • h‖ + l * ‖h‖ := by rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg l)]
  have h2 : (l : ℝ) * ‖h‖ ≤ L' * ‖h‖ := mul_le_mul_of_nonneg_right hl' (norm_nonneg h)
  linarith

/-- **The averaged differences of `η_i`**, integrated: if the differences
`Δ^L'_{-2^(-j') z} η_i(w)` vanish for `‖z‖ < ρ`, then
`∫ |Φ(z)| |Δ^L'_{-2^(-j') z} η_i(w)| dz ≤ A 2^(in) 2^(iL') 2^(-j'L') T (1 + ρ)^(-N)` with
`A = Rd.LocalMeansBump.dualDerivConst L L'` and `T = Rd.tailConst lpKernelS L' N`. -/
theorem lintegral_lpKernel_mul_higherDiff_dual_le (L L' i j' N : ℕ) (w : V) {ρ : ℝ}
    (hsupp : ∀ z : V, ‖z‖ < ρ → (fwdDiff (-((2 : ℝ) ^ j')⁻¹ • z))^[L'] (b.dual L i) w = 0) :
    ∫⁻ z, ‖lpKernel z‖ₑ * ‖(fwdDiff (-((2 : ℝ) ^ j')⁻¹ • z))^[L'] (b.dual L i) w‖ₑ ≤
      ENNReal.ofReal (b.dualDerivConst L L') * 2 ^ (i * finrank ℝ V) *
        dyadicWeight (L' : ℝ) i * dyadicWeight (-(L' : ℝ)) j' *
          tailConst (lpKernelS (V := V)) L' N * ((1 + ENNReal.ofReal ρ) ^ N)⁻¹ := by
  set K0 := ENNReal.ofReal (b.dualDerivConst L L') * 2 ^ (i * finrank ℝ V) *
    dyadicWeight (L' : ℝ) i * dyadicWeight (-(L' : ℝ)) j' with hK0def
  have hK0 : K0 ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
    (ENNReal.dyadicWeight_ne_top _ _)) (ENNReal.dyadicWeight_ne_top _ _)
  have hs : MeasurableSet {z : V | ρ ≤ ‖z‖} := measurableSet_le measurable_const measurable_norm
  have hpt : ∀ z, ‖lpKernel z‖ₑ * ‖(fwdDiff (-((2 : ℝ) ^ j')⁻¹ • z))^[L'] (b.dual L i) w‖ₑ ≤
      {z : V | ρ ≤ ‖z‖}.indicator (fun z => ‖lpKernel z‖ₑ * ‖z‖ₑ ^ L') z * K0 := fun z => by
    by_cases hz : ρ ≤ ‖z‖
    · rw [Set.indicator_of_mem (show z ∈ {z : V | ρ ≤ ‖z‖} from hz)]
      calc ‖lpKernel z‖ₑ * ‖(fwdDiff (-((2 : ℝ) ^ j')⁻¹ • z))^[L'] (b.dual L i) w‖ₑ
          ≤ ‖lpKernel z‖ₑ * (K0 * ‖z‖ₑ ^ L') :=
            mul_le_mul_right (b.enorm_higherDiff_dual_le L L' i j' z w) _
        _ = _ := by ring
    · rw [hsupp z (not_le.1 hz), eNorm_zero, mul_zero]
      exact zero_le
  calc ∫⁻ z, ‖lpKernel z‖ₑ * ‖(fwdDiff (-((2 : ℝ) ^ j')⁻¹ • z))^[L'] (b.dual L i) w‖ₑ
      ≤ ∫⁻ z, {z : V | ρ ≤ ‖z‖}.indicator (fun z => ‖lpKernel z‖ₑ * ‖z‖ₑ ^ L') z * K0 :=
        lintegral_mono hpt
    _ = (∫⁻ z in {z : V | ρ ≤ ‖z‖}, ‖lpKernel z‖ₑ * ‖z‖ₑ ^ L') * K0 := by
        rw [lintegral_mul_const' _ _ hK0, lintegral_indicator hs]
    _ ≤ (tailConst (lpKernelS (V := V)) L' N * ((1 + ENNReal.ofReal ρ) ^ N)⁻¹) * K0 := by
        gcongr
        exact lintegral_tail_schwartz_le (lpKernelS (V := V)) L' N ρ
    _ = _ := by rw [hK0def]; ring

/-- The constant `A 4^L' (8L')^N (1 + 4LR)^N T` of the averaged differences of the dual kernels,
with `A = Rd.LocalMeansBump.dualDerivConst L L'` and `T = Rd.tailConst lpKernelS L' N`. -/
noncomputable def dualTailConst (L L' N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (b.dualDerivConst L L') * 4 ^ L' * (8 * (L' : ℝ≥0∞)) ^ N *
    ENNReal.ofReal ((1 + 4 * L * b.radius) ^ N) * tailConst (lpKernelS (V := V)) L' N

/-- The constant of the averaged differences of the dual kernels is finite. -/
theorem dualTailConst_ne_top (L L' N : ℕ) : b.dualTailConst L L' N ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (by norm_num)))
    (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top L'))))
    ENNReal.ofReal_ne_top) (tailConst_ne_top _ _ _)

/-- For `L' ≥ 1` and `‖w‖ > 4LR 2^(-i)`, the difference `Δ^L'_{-2^(-j') z} η_i(w)` vanishes
whenever `‖z‖ < 2^j' ‖w‖ / (2L')`: all points `w - l 2^(-j') z`, `l ≤ L'`, then lie outside
`closedBall(0, 2LR 2^(-i))`, where `η_i` vanishes. -/
theorem higherDiff_dual_eq_zero_of_norm_lt (L L' i j' : ℕ) (hL' : 1 ≤ L') {w : V}
    (hw : 4 * L * b.radius / 2 ^ i < ‖w‖) {z : V} (hz : ‖z‖ < 2 ^ j' * ‖w‖ / (2 * L')) :
    (fwdDiff (-((2 : ℝ) ^ j')⁻¹ • z))^[L'] (b.dual L i) w = 0 := by
  refine b.higherDiff_dual_eq_zero L L' i ?_
  have hLr : (0 : ℝ) < L' := by exact_mod_cast hL'
  have hh : ‖-((2 : ℝ) ^ j')⁻¹ • z‖ = ‖z‖ / 2 ^ j' := by
    rw [norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg (by positivity), inv_mul_eq_div]
  rw [hh]
  have hz' : ‖z‖ * (2 * L') < 2 ^ j' * ‖w‖ := by rwa [lt_div_iff₀ (by positivity)] at hz
  have h1 : L' * (‖z‖ / 2 ^ j') < ‖w‖ / 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith
  have h2 : 2 * L * b.radius / 2 ^ i = (4 * L * b.radius / 2 ^ i) / 2 := by ring
  linarith

/-- **The averaged differences of the dual kernels**: for `L' ≥ 1`, `i ≤ j' + 2` and almost
every `w`, `|η_i(w) - (μ_{2^j'} ⋆ η_i)(w)| ≤ C 2^(-(j'+2-i)L') 2^(in) (1 + 2^i ‖w‖)^(-N)` with
`C = Rd.LocalMeansBump.dualTailConst L L' N`, where `μ` is the moment kernel of order `L'` of
`Φ`. -/
theorem ae_enorm_dual_sub_conv_lpMomentScaled_le (L N : ℕ) {L' : ℕ} (hL' : 1 ≤ L')
    {i j' : ℕ} (hij : i ≤ j' + 2) :
    ∀ᵐ w ∂volume, ‖b.dual L i w - conv (lpMomentScaled L' j') (b.dual L i) volume w‖ₑ ≤
      b.dualTailConst L L' N * dyadicWeight (-(L' : ℝ)) (j' + 2 - i) *
        2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖w‖ₑ) ^ N)⁻¹ := by
  filter_upwards [ae_enorm_sub_conv_dilate_momentKernel_le le_rfl ENNReal.one_ne_top
    integrable_lpKernel integral_lpKernel (memLp_one_iff_integrable.2 (b.integrable_dual L i)) L'
    (c := (2 : ℝ) ^ j') (by positivity)] with w hw
  refine hw.trans ?_
  have hR0 := b.radius_nonneg
  have hfac := ENNReal.dyadicWeight_mul_dyadicWeight_neg_eq L' hij
  have h8 : 1 ≤ (8 * (L' : ℝ≥0∞)) ^ N :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ 8 * L' by omega))
  by_cases hsmall : ‖w‖ ≤ 4 * L * b.radius / 2 ^ i
  · refine (b.lintegral_lpKernel_mul_higherDiff_dual_le L L' i j' N w (ρ := 0)
      fun z hz => absurd hz (not_lt.2 (norm_nonneg z))).trans ?_
    have h4 : 2 ^ i * ‖w‖ₑ ≤ ENNReal.ofReal (4 * L * b.radius) :=
      two_pow_mul_enorm_le_ofReal hsmall
    have h1 := ENNReal.one_le_ofReal_mul_inv_of_le (by positivity) h4 N
    rw [ENNReal.ofReal_zero, add_zero, one_pow, inv_one, mul_one, mul_assoc _ (dyadicWeight _ i),
      hfac, dualTailConst]
    calc ENNReal.ofReal (b.dualDerivConst L L') * 2 ^ (i * finrank ℝ V) *
          (4 ^ L' * dyadicWeight (-(L' : ℝ)) (j' + 2 - i)) * tailConst (lpKernelS (V := V)) L' N
        = ENNReal.ofReal (b.dualDerivConst L L') * 2 ^ (i * finrank ℝ V) *
          (4 ^ L' * dyadicWeight (-(L' : ℝ)) (j' + 2 - i)) * tailConst (lpKernelS (V := V)) L' N *
            (1 * 1) := by rw [mul_one, mul_one]
      _ ≤ ENNReal.ofReal (b.dualDerivConst L L') * 2 ^ (i * finrank ℝ V) *
          (4 ^ L' * dyadicWeight (-(L' : ℝ)) (j' + 2 - i)) * tailConst (lpKernelS (V := V)) L' N *
            ((8 * (L' : ℝ≥0∞)) ^ N * (ENNReal.ofReal ((1 + 4 * L * b.radius) ^ N) *
              ((1 + 2 ^ i * ‖w‖ₑ) ^ N)⁻¹)) := by gcongr
      _ = _ := by ring
  · push Not at hsmall
    refine (b.lintegral_lpKernel_mul_higherDiff_dual_le L L' i j' N w
      (ρ := 2 ^ j' * ‖w‖ / (2 * L'))
      fun z hz => b.higherDiff_dual_eq_zero_of_norm_lt L L' i j' hL' hsmall hz).trans ?_
    have hW := inv_one_add_ofReal_div_pow_le hL' hij w N
    have h1 : 1 ≤ ENNReal.ofReal ((1 + 4 * L * b.radius) ^ N) := by
      rw [← ENNReal.ofReal_one]
      have hLR : 0 ≤ (L : ℝ) * b.radius := mul_nonneg (Nat.cast_nonneg L) hR0
      exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by nlinarith))
    rw [mul_assoc _ (dyadicWeight _ i), hfac, dualTailConst]
    calc ENNReal.ofReal (b.dualDerivConst L L') * 2 ^ (i * finrank ℝ V) *
          (4 ^ L' * dyadicWeight (-(L' : ℝ)) (j' + 2 - i)) * tailConst (lpKernelS (V := V)) L' N *
            ((1 + ENNReal.ofReal (2 ^ j' * ‖w‖ / (2 * L'))) ^ N)⁻¹
        ≤ ENNReal.ofReal (b.dualDerivConst L L') * 2 ^ (i * finrank ℝ V) *
          (4 ^ L' * dyadicWeight (-(L' : ℝ)) (j' + 2 - i)) * tailConst (lpKernelS (V := V)) L' N *
            ((8 * (L' : ℝ≥0∞)) ^ N * (ENNReal.ofReal ((1 + 4 * L * b.radius) ^ N) *
              ((1 + 2 ^ i * ‖w‖ₑ) ^ N)⁻¹)) := by
          gcongr
          refine hW.trans ?_
          gcongr
          exact le_mul_of_one_le_left zero_le h1
      _ = _ := by ring

/-- **The moment identity of `Φ` in the blocks**:
`ψ_{j'+2} ⋆ η_i = ψ_{j'+2} ⋆ (η_i - μ_{2^j'} ⋆ η_i)` almost everywhere, since
`ψ_{j'+2} ⋆ μ_{2^j'} = 0`. -/
theorem conv_psi_dual_ae_eq (L L' i j' : ℕ) :
    conv (psi (V := V) (j' + 2)) (b.dual L i) volume =ᵐ[volume]
      conv (psi (j' + 2)) (b.dual L i - conv (lpMomentScaled L' j') (b.dual L i) volume)
        volume := by
  have hη : MemLp (b.dual L i) 1 volume := memLp_one_iff_integrable.2 (b.integrable_dual L i)
  have hμη : MemLp (conv (lpMomentScaled L' j') (b.dual L i) volume) 1 volume :=
    memLp_one_iff_integrable.2 (integrable_conv (integrable_lpMomentScaled L' j')
      (b.integrable_dual L i))
  have h0 : conv (psi (V := V) (j' + 2)) (conv (lpMomentScaled L' j') (b.dual L i) volume)
      volume =ᵐ[volume] 0 := by
    have h := conv_conv_ae le_rfl ENNReal.one_ne_top (integrable_psi (V := V) (j' + 2))
      (integrable_lpMomentScaled L' j') hη
    rw [conv_psi_lpMomentScaled] at h
    filter_upwards [h] with w hw
    rw [← hw]
    simp [conv_apply]
  filter_upwards [conv_sub_ae le_rfl ENNReal.one_ne_top (integrable_psi (V := V) (j' + 2)) hη
    hμη, h0] with y h1 h2
  rw [h1, Pi.sub_apply, h2, Pi.zero_apply, sub_zero]

/-- **The case `i ≤ j`, `j ≥ 2`**: for `L' ≥ 1` and almost every `y`,
`|(ψ_j ⋆ η_i)(y)| ≤ C P I 2^(-(j-i)L') 2^(in) (1 + 2^i ‖y‖)^(-N)` with
`C = Rd.LocalMeansBump.dualTailConst L L' N`, `P = Rd.psiDecayConst V (2N)` and
`I = Rd.peetreIntegral V N`: by the moment identity of `Φ`, the averaged differences of `η_i`
and the convolution of two Peetre bumps. -/
theorem ae_enorm_conv_psi_dual_le_of_two_le (L N : ℕ) {L' : ℕ} (hL' : 1 ≤ L') {i j : ℕ}
    (hij : i ≤ j) (hj : 2 ≤ j) :
    ∀ᵐ y ∂volume, ‖conv (psi j) (b.dual L i) volume y‖ₑ ≤
      b.dualTailConst L L' N * psiDecayConst V (2 * N) * peetreIntegral V N *
        dyadicWeight (-(L' : ℝ)) (j - i) * 2 ^ (i * finrank ℝ V) *
          ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹ := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
  have hD := b.ae_enorm_dual_sub_conv_lpMomentScaled_le L N hL' hij
  have hc : b.dualTailConst L L' N * dyadicWeight (-(L' : ℝ)) (j' + 2 - i) *
      psiDecayConst V (2 * N) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (b.dualTailConst_ne_top L L' N)
      (ENNReal.dyadicWeight_ne_top _ _)) (psiDecayConst_ne_top _)
  filter_upwards [b.conv_psi_dual_ae_eq L L' i j'] with y hy
  rw [hy, conv_comm]
  refine (enorm_conv_le_lintegral _ _ y).trans ?_
  calc ∫⁻ w, ‖(b.dual L i - conv (lpMomentScaled L' j') (b.dual L i) volume) w‖ₑ *
        ‖psi (j' + 2) (y - w)‖ₑ
      ≤ ∫⁻ w, b.dualTailConst L L' N * dyadicWeight (-(L' : ℝ)) (j' + 2 - i) *
          psiDecayConst V (2 * N) * (2 ^ ((j' + 2) * finrank ℝ V) *
            ((1 + 2 ^ (j' + 2) * ‖y - w‖ₑ) ^ (2 * N))⁻¹ *
              (2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖w‖ₑ) ^ N)⁻¹)) := by
        refine lintegral_mono_ae (hD.mono fun w hw => ?_)
        calc ‖(b.dual L i - conv (lpMomentScaled L' j') (b.dual L i) volume) w‖ₑ *
              ‖psi (j' + 2) (y - w)‖ₑ
            ≤ (b.dualTailConst L L' N * dyadicWeight (-(L' : ℝ)) (j' + 2 - i) *
                2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖w‖ₑ) ^ N)⁻¹) *
              (psiDecayConst V (2 * N) * 2 ^ ((j' + 2) * finrank ℝ V) *
                ((1 + 2 ^ (j' + 2) * ‖y - w‖ₑ) ^ (2 * N))⁻¹) :=
              mul_le_mul' hw (enorm_psi_le _ _ _)
          _ = _ := by ring
    _ = b.dualTailConst L L' N * dyadicWeight (-(L' : ℝ)) (j' + 2 - i) *
          psiDecayConst V (2 * N) * ∫⁻ w, 2 ^ ((j' + 2) * finrank ℝ V) *
            ((1 + 2 ^ (j' + 2) * ‖y - w‖ₑ) ^ (2 * N))⁻¹ *
              (2 ^ (i * finrank ℝ V) * ((1 + 2 ^ i * ‖w‖ₑ) ^ N)⁻¹) :=
        lintegral_const_mul' _ _ hc
    _ ≤ b.dualTailConst L L' N * dyadicWeight (-(L' : ℝ)) (j' + 2 - i) *
          psiDecayConst V (2 * N) * (peetreIntegral V N * 2 ^ (i * finrank ℝ V) *
            ((1 + 2 ^ i * ‖y‖ₑ) ^ N)⁻¹) := by
        gcongr
        exact lintegral_peetre_mul_le hij N y
    _ = _ := by ring

/-- The constant of the cross kernel `ψ_j ⋆ η_i`: the sum of the constants of the three cases,
`(1 + 2^(n+L')) C_s + C P I` with `C_s = Rd.LocalMeansBump.psiDualSupportConst L N`,
`C = Rd.LocalMeansBump.dualTailConst L L' N`, `P = Rd.psiDecayConst V (2N)` and
`I = Rd.peetreIntegral V N`. -/
noncomputable def psiDualConst (L L' N : ℕ) : ℝ≥0∞ :=
  (1 + 2 ^ (finrank ℝ V + L')) * b.psiDualSupportConst L N +
    b.dualTailConst L L' N * psiDecayConst V (2 * N) * peetreIntegral V N

/-- The constant of the cross kernel `ψ_j ⋆ η_i` is finite for `N > n`. -/
theorem psiDualConst_ne_top (L L' : ℕ) {N : ℕ} (hN : finrank ℝ V < N) :
    b.psiDualConst L L' N ≠ ∞ := by
  refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.pow_ne_top ENNReal.ofNat_ne_top⟩) (b.psiDualSupportConst_ne_top L N), ?_⟩
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (b.dualTailConst_ne_top L L' N)
    (psiDecayConst_ne_top _)) (peetreIntegral_ne_top hN)

/-- **The cross kernel `ψ_j ⋆ η_i`**: for every order `L`, every `L' ≥ 1`, all levels `i, j` and
almost every `y`, `|(ψ_j ⋆ η_i)(y)| ≤ C c_{ji} 2^(min(i,j) n) (1 + 2^min(i,j) ‖y‖)^(-N)` with
`c_{ji} = 2^(-(j-i)L')` for `i ≤ j`, `c_{ji} = 1` for `i > j`, and
`C = Rd.LocalMeansBump.psiDualConst L L' N`. -/
theorem enorm_conv_psi_dual_le (L : ℕ) {L' : ℕ} (hL' : 1 ≤ L') (N i j : ℕ) :
    ∀ᵐ y ∂volume, ‖conv (psi j) (b.dual L i) volume y‖ₑ ≤
      b.psiDualConst L L' N * (if i ≤ j then dyadicWeight (-(L' : ℝ)) (j - i) else 1) *
        2 ^ (min i j * finrank ℝ V) * ((1 + 2 ^ (min i j) * ‖y‖ₑ) ^ N)⁻¹ := by
  have h1 : b.psiDualSupportConst L N ≤ b.psiDualConst L L' N :=
    (le_mul_of_one_le_left zero_le le_self_add).trans le_self_add
  have h2 : 2 ^ (finrank ℝ V + L') * b.psiDualSupportConst L N ≤ b.psiDualConst L L' N :=
    (mul_le_mul_left le_add_self _).trans le_self_add
  have h3 : b.dualTailConst L L' N * psiDecayConst V (2 * N) * peetreIntegral V N ≤
      b.psiDualConst L L' N := le_add_self
  rcases lt_or_ge j i with hji | hij
  · refine Filter.Eventually.of_forall fun y => (b.enorm_conv_psi_dual_le_of_lt L N hji y).trans ?_
    simp only [not_le.2 hji, ↓reduceIte, min_eq_right hji.le, mul_one]
    gcongr
  · simp only [hij, ↓reduceIte, min_eq_left hij]
    rcases le_or_gt j 1 with hj | hj
    · refine Filter.Eventually.of_forall fun y =>
        (b.enorm_conv_psi_dual_le_of_le_one L N L' hij hj y).trans ?_
      gcongr
    · filter_upwards [b.ae_enorm_conv_psi_dual_le_of_two_le L N hL' hij hj] with y hy
      refine hy.trans ?_
      gcongr

end LocalMeansBump

/-! ### Maximal function bounds of convolutions -/

/-- **Convolutions under a Peetre majorant**: if `|K(y)| ≤ C 2^(mn) (1 + 2^m ‖y‖)^(-N)` almost
everywhere with `C < ∞` and `N > n`, then `|K ⋆ h(x)| ≤ C_{n,N} C M|h|(x)` for every function
`h` and every `x`, with `C_{n,N} = Rd.decayMaximalConst V N`. -/
theorem enorm_conv_le_maximal_of_decay {N m : ℕ} (hN : finrank ℝ V < N) {C : ℝ≥0∞}
    (hC : C ≠ ∞) {K : V → ℂ}
    (hK : ∀ᵐ y ∂volume, ‖K y‖ₑ ≤ C * 2 ^ (m * finrank ℝ V) * ((1 + 2 ^ m * ‖y‖ₑ) ^ N)⁻¹)
    (h : V → ℂ) (x : V) :
    ‖conv K h volume x‖ₑ ≤ decayMaximalConst V N * C * maximal (fun y => ‖h y‖ₑ) x :=
  (enorm_conv_le_lintegral K h x).trans ((lintegral_mono_ae (hK.mono fun _ hy =>
    mul_le_mul_left hy _)).trans
      (lintegral_mul_le_maximal_of_one_add_norm (j := m) hN hC (fun _ => le_rfl)
        (fun y => ‖h y‖ₑ) x))

end Rd
