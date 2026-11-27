/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Differences.MomentKernels
public import LeanPool.FunctionSpaces.Rd.Differences.BesovDifferences
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Local means

A **bump for local means** is a smooth `g : V → ℂ` with `∫ g = 1` that vanishes outside the ball
of radius `R` (`Rd.LocalMeansBump`). With the moment kernel `m` of order `L`
(`Rd.momentKernel`) and its dilations `m_{2^j}` (`Rd.LocalMeansBump.scaled`), the **local means**
of `f ∈ L_p(V)` are `k_j ⋆ f` (`Rd.LocalMeansBump.localMean`) with the kernels

`k_0 = m`,  `k_j = m_{2^j} - m_{2^(j-1)}`   (`Rd.LocalMeansBump.kernel`),

and the **local means quasi-norm** is `‖(2^(js) ‖k_j ⋆ f‖_p)_j‖_{ℓ_q}`
(`Rd.LocalMeansBump.localMeansNorm`). With the dual kernels `η_0 = m`,
`η_j = m_{2^j} + m_{2^(j-1)}` (`Rd.LocalMeansBump.dual`), the identity `a² - b² = (a - b)(a + b)`
in the commutative convolution algebra gives the **reproducing formula**
`∑_{j ≤ J} η_j ⋆ k_j ⋆ f = m_{2^J} ⋆ m_{2^J} ⋆ f → f` in `L_p`
(`Rd.LocalMeansBump.sum_dual_localMean`, `Rd.LocalMeansBump.tendsto_sum_dual_localMean`).

**Local means and differences** (`Rd.LocalMeansBump.besov_iff_localMeans`): for `1 ≤ p < ∞`,
`0 < s < L` and `1 ≤ q ≤ ∞`, `‖f‖_p + ‖(2^(ks) ω_L(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff the local means
quasi-norm is finite, with equivalent quasi-norms:

* `‖k_j ⋆ f‖_p ≤ 2 ‖g‖_1 (1 + R)^L ω_L(f, 2^(1-j))_p`, since `f - m_c ⋆ f` averages differences
  of order `L` (`Rd.LocalMeansBump.localMeansNorm_le`);
* `ω_L(η_j ⋆ h, 2^(-i))_p ≤ C min(1, 2^((j-i)L)) ‖h‖_p` by the differences of the smooth kernels
  in `L_1`; the reproducing formula and Hardy's inequalities in both directions
  (`ENNReal.lqNorm_almostDiagonal_le`) bound the moduli by the local means
  (`Rd.LocalMeansBump.modNorm_le_localMeansNorm`).

Local means therefore describe the same spaces as band-limited approximation, Littlewood–Paley
blocks and differences (`Rd.LocalMeansBump.memApprox_bandScheme_iff_localMeans`).

**Bumps from smooth bump functions**: the normalised smooth bump function around `c` with outer
radius `r` (Mathlib's `ContDiffBump.normed`), with complex values (`Rd.bumpMollifier`), is a bump
of every radius `R ≥ ‖c‖ + r` (`Rd.LocalMeansBump.ofContDiffBump`). Hence every radius `R > 0` has
a bump, the one around `0` (`Rd.LocalMeansBump.centered`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal SchwartzMap

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Bumps and their kernels -/

variable (V) in
/-- A **bump for local means**: a smooth function with integral `1` that vanishes outside the
ball of radius `radius`. -/
structure LocalMeansBump where
  /-- The function. -/
  toFun : V → ℂ
  /-- The radius of the ball outside of which the bump vanishes. -/
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) toFun
  eq_zero : ∀ z, radius < ‖z‖ → toFun z = 0
  integral_eq_one : ∫ z, toFun z = 1

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- A bump has compact support. -/
theorem hasCompactSupport : HasCompactSupport b.toFun :=
  HasCompactSupport.intro (isCompact_closedBall 0 b.radius) fun x hx =>
    b.eq_zero x (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)

/-- A bump is integrable. -/
theorem integrable : Integrable b.toFun :=
  b.contDiff.continuous.integrable_of_hasCompactSupport b.hasCompactSupport

/-- The moment kernel of a bump is smooth. -/
theorem contDiff_momentKernel (L : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (momentKernel b.toFun L) :=
  ContDiff.sum fun _ _ => contDiff_const.mul
    (contDiff_const.mul (b.contDiff.comp (contDiff_const_smul _)))

/-- The moment kernel of a bump vanishes outside the ball of radius `L R`. -/
theorem momentKernel_eq_zero (L : ℕ) {x : V} (hx : L * b.radius < ‖x‖) :
    momentKernel b.toFun L x = 0 := by
  refine Finset.sum_eq_zero fun l hl => ?_
  have hl' : (l : ℝ) + 1 ≤ L := by exact_mod_cast Finset.mem_range.1 hl
  have hpos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  rw [dilate, b.eq_zero _ ?_, mul_zero, mul_zero]
  rw [norm_smul, Real.norm_of_nonneg (by positivity), one_div, inv_mul_eq_div, lt_div_iff₀ hpos]
  calc b.radius * ((l : ℝ) + 1) ≤ b.radius * L := mul_le_mul_of_nonneg_left hl' b.radius_nonneg
    _ = L * b.radius := mul_comm _ _
    _ < ‖x‖ := hx

/-- The moment kernel of a bump has compact support. -/
theorem hasCompactSupport_momentKernel (L : ℕ) : HasCompactSupport (momentKernel b.toFun L) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (L * b.radius)) fun x hx =>
    b.momentKernel_eq_zero L (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)

/-- The moment kernel of a bump as a Schwartz function. -/
noncomputable def momentSchwartz (L : ℕ) : 𝓢(V, ℂ) :=
  (b.hasCompactSupport_momentKernel L).toSchwartzMap (b.contDiff_momentKernel L)

/-- The `L_1` norm of the derivatives of order `L` of the moment kernel. -/
noncomputable def derivNorm (L : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, ‖iteratedFDeriv ℝ L (b.momentSchwartz L : V → ℂ) x‖ₑ

/-- The moment kernel at the dyadic scale `2^j`, `m_{2^j} = 2^(jn) m(2^j ·)`. -/
noncomputable def scaled (L j : ℕ) : V → ℂ := dilate (2 ^ j) (momentKernel b.toFun L)

/-- The **local means kernels** `k_0 = m`, `k_j = m_{2^j} - m_{2^(j-1)}`. -/
noncomputable def kernel (L : ℕ) : ℕ → V → ℂ
  | 0 => b.scaled L 0
  | j + 1 => b.scaled L (j + 1) - b.scaled L j

/-- The **dual kernels** `η_0 = m`, `η_j = m_{2^j} + m_{2^(j-1)}`. -/
noncomputable def dual (L : ℕ) : ℕ → V → ℂ
  | 0 => b.scaled L 0
  | j + 1 => b.scaled L (j + 1) + b.scaled L j

/-- The dilated moment kernels are integrable. -/
theorem integrable_scaled (L j : ℕ) : Integrable (b.scaled L j) :=
  integrable_dilate (integrable_momentKernel b.integrable L) (by positivity)

/-- The local means kernels are integrable. -/
theorem integrable_kernel (L j : ℕ) : Integrable (b.kernel L j) := by
  cases j with
  | zero => exact b.integrable_scaled L 0
  | succ j => exact (b.integrable_scaled L (j + 1)).sub (b.integrable_scaled L j)

/-- The dual kernels are integrable. -/
theorem integrable_dual (L j : ℕ) : Integrable (b.dual L j) := by
  cases j with
  | zero => exact b.integrable_scaled L 0
  | succ j => exact (b.integrable_scaled L (j + 1)).add (b.integrable_scaled L j)

/-- `‖m_{2^j}‖_1 = ‖m‖_1`. -/
theorem eLpNorm_scaled_one (L j : ℕ) :
    eLpNorm (b.scaled L j) 1 volume = eLpNorm (momentKernel b.toFun L) 1 volume :=
  eLpNorm_dilate_one (integrable_momentKernel b.integrable L) (by positivity)

/-- `‖η_j‖_1 ≤ 2 ‖m‖_1`. -/
theorem eLpNorm_dual_one_le (L j : ℕ) :
    eLpNorm (b.dual L j) 1 volume ≤ 2 * eLpNorm (momentKernel b.toFun L) 1 volume := by
  cases j with
  | zero =>
    rw [two_mul]
    exact (b.eLpNorm_scaled_one L 0).le.trans le_self_add
  | succ j =>
    change eLpNorm (b.scaled L (j + 1) + b.scaled L j) 1 volume ≤ _
    calc eLpNorm (b.scaled L (j + 1) + b.scaled L j) 1 volume
        ≤ eLpNorm (b.scaled L (j + 1)) 1 volume + eLpNorm (b.scaled L j) 1 volume :=
          eLpNorm_add_le le_rfl
      _ = 2 * eLpNorm (momentKernel b.toFun L) 1 volume := by
          rw [b.eLpNorm_scaled_one, b.eLpNorm_scaled_one, two_mul]

/-- `‖k_j‖_1 ≤ 2 ‖m‖_1`. -/
theorem eLpNorm_kernel_one_le (L j : ℕ) :
    eLpNorm (b.kernel L j) 1 volume ≤ 2 * eLpNorm (momentKernel b.toFun L) 1 volume := by
  cases j with
  | zero =>
    rw [two_mul]
    exact (b.eLpNorm_scaled_one L 0).le.trans le_self_add
  | succ j =>
    change eLpNorm (b.scaled L (j + 1) - b.scaled L j) 1 volume ≤ _
    calc eLpNorm (b.scaled L (j + 1) - b.scaled L j) 1 volume
        ≤ eLpNorm (b.scaled L (j + 1)) 1 volume + eLpNorm (b.scaled L j) 1 volume :=
          eLpNorm_sub_le le_rfl
      _ = 2 * eLpNorm (momentKernel b.toFun L) 1 volume := by
          rw [b.eLpNorm_scaled_one, b.eLpNorm_scaled_one, two_mul]

/-- The dilated moment kernels vanish outside `closedBall(0, L R 2^(-j))`. -/
theorem scaled_eq_zero_of_lt (L j : ℕ) {y : V} (hy : L * b.radius / 2 ^ j < ‖y‖) :
    b.scaled L j y = 0 := by
  rw [scaled, dilate, b.momentKernel_eq_zero L, mul_zero]
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [div_lt_iff₀ (by positivity)] at hy
  linarith

/-- The dual kernels vanish outside `closedBall(0, 2 L R 2^(-j))`. -/
theorem dual_eq_zero_of_lt (L j : ℕ) {y : V} (hy : 2 * L * b.radius / 2 ^ j < ‖y‖) :
    b.dual L j y = 0 := by
  have hLR : 0 ≤ (L : ℝ) * b.radius := mul_nonneg (Nat.cast_nonneg L) b.radius_nonneg
  cases j with
  | zero =>
    refine b.scaled_eq_zero_of_lt L 0 (lt_of_le_of_lt ?_ hy)
    simp only [pow_zero, div_one]
    linarith
  | succ j =>
    change b.scaled L (j + 1) y + b.scaled L j y = 0
    have h1 : (L : ℝ) * b.radius / 2 ^ (j + 1) ≤ 2 * L * b.radius / 2 ^ (j + 1) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : 2 * (L : ℝ) * b.radius / 2 ^ (j + 1) = L * b.radius / 2 ^ j := by
      rw [pow_succ, mul_comm ((2 : ℝ) ^ j) 2, mul_assoc, mul_div_mul_left _ _ two_ne_zero]
    rw [b.scaled_eq_zero_of_lt L (j + 1) (h1.trans_lt hy),
      b.scaled_eq_zero_of_lt L j (h2 ▸ hy), add_zero]

/-- The dual kernels have compact support. -/
theorem hasCompactSupport_dual (L j : ℕ) : HasCompactSupport (b.dual L j) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (2 * L * b.radius / 2 ^ j)) fun y hy =>
    b.dual_eq_zero_of_lt L j (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy)

/-- The dual kernels are continuous. -/
theorem continuous_dual (L j : ℕ) : Continuous (b.dual L j) := by
  have hm : Continuous (momentKernel b.toFun L) := (b.contDiff_momentKernel L).continuous
  cases j with
  | zero => exact continuous_dilate hm _
  | succ j => exact (continuous_dilate hm _).add (continuous_dilate hm _)

/-- The dilated moment kernels have compact support. -/
theorem hasCompactSupport_scaled (L j : ℕ) : HasCompactSupport (b.scaled L j) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (L * b.radius / 2 ^ j)) fun y hy =>
    b.scaled_eq_zero_of_lt L j (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy)

/-- The dilated moment kernels are continuous. -/
theorem continuous_scaled (L j : ℕ) : Continuous (b.scaled L j) :=
  continuous_dilate (b.contDiff_momentKernel L).continuous _

/-- The local means kernels have compact support. -/
theorem hasCompactSupport_kernel (L j : ℕ) : HasCompactSupport (b.kernel L j) := by
  cases j with
  | zero => exact b.hasCompactSupport_scaled L 0
  | succ j => exact (b.hasCompactSupport_scaled L (j + 1)).sub (b.hasCompactSupport_scaled L j)

/-- The local means kernels are continuous. -/
theorem continuous_kernel (L j : ℕ) : Continuous (b.kernel L j) := by
  cases j with
  | zero => exact b.continuous_scaled L 0
  | succ j => exact (b.continuous_scaled L (j + 1)).sub (b.continuous_scaled L j)

/-- **Differences of the dilated moment kernels in `L_1`**:
`‖Δ_v^L m_{2^j}‖_1 ≤ (2^j ‖v‖)^L ‖D^L m‖_1`. -/
theorem eLpNorm_higherDiff_scaled_le (L j : ℕ) (v : V) :
    eLpNorm ((fwdDiff v)^[L] (b.scaled L j)) 1 volume ≤
      ENNReal.ofReal (2 ^ j * ‖v‖) ^ L * b.derivNorm L := by
  have hint : Integrable ((fwdDiff ((2 : ℝ) ^ j • v))^[L] (momentKernel b.toFun L)) :=
    integrable_higherDiff (integrable_momentKernel b.integrable L) L _
  rw [scaled, higherDiff_dilate, eLpNorm_dilate_one hint (by positivity),
    eLpNorm_one_eq_lintegral_eNorm hint.aestronglyMeasurable]
  refine (lintegral_enorm_higherDiff_schwartz_le _ L (b.momentSchwartz L)).trans_eq ?_
  rw [← ofReal_norm, norm_smul, Real.norm_of_nonneg (by positivity)]
  rfl

/-- `‖Δ_v^L m_{2^j}‖_1 ≤ 2^L ‖m‖_1`. -/
theorem eLpNorm_higherDiff_scaled_le' (L j : ℕ) (v : V) :
    eLpNorm ((fwdDiff v)^[L] (b.scaled L j)) 1 volume ≤
      2 ^ L * eLpNorm (momentKernel b.toFun L) 1 volume := by
  rw [← b.eLpNorm_scaled_one L j]
  exact eLpNorm_higherDiff_le (b.integrable_scaled L j).aestronglyMeasurable le_rfl L v

/-- The constant `2 (‖D^L m‖_1 + 2^L ‖m‖_1)` of the differences of the dual kernels. -/
noncomputable def dualConst (L : ℕ) : ℝ≥0∞ :=
  2 * (b.derivNorm L + 2 ^ L * eLpNorm (momentKernel b.toFun L) 1 volume)

/-- The constant of the differences of the dual kernels is finite. -/
theorem dualConst_ne_top (L : ℕ) : b.dualConst L ≠ ∞ :=
  ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.2
    ⟨lintegral_enorm_iteratedFDeriv_ne_top L _, ENNReal.mul_ne_top (by simp)
      (eLpNorm_momentKernel_ne_top b.integrable L)⟩)

/-- One dilated kernel at a scale at most `2^j`: `‖Δ_v^L m_{2^l}‖_1 ≤ C 2^(-(i-j)L)` for
`l ≤ j ≤ i` and `‖v‖ ≤ 2^(-i)`, and `≤ C` always. -/
theorem eLpNorm_higherDiff_scaled_le_dyadic (L : ℕ) {i j l : ℕ} (hlj : l ≤ j) {v : V}
    (hv : ‖v‖ ≤ 1 / 2 ^ i) :
    eLpNorm ((fwdDiff v)^[L] (b.scaled L l)) 1 volume ≤
      (b.derivNorm L + 2 ^ L * eLpNorm (momentKernel b.toFun L) 1 volume) *
        (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) := by
  split_ifs with hji
  · have hw : ENNReal.ofReal (2 ^ l * ‖v‖) ^ L ≤ dyadicWeight (-(L : ℝ)) (i - j) := by
      rw [← ENNReal.rpow_natCast]
      exact (ENNReal.ofReal_two_pow_mul_rpow_le (hlj.trans hji) hv (Nat.cast_nonneg L)).trans
        (ENNReal.dyadicWeight_anti (by simp) (by omega))
    calc eLpNorm ((fwdDiff v)^[L] (b.scaled L l)) 1 volume
        ≤ ENNReal.ofReal (2 ^ l * ‖v‖) ^ L * b.derivNorm L := b.eLpNorm_higherDiff_scaled_le L l v
      _ ≤ dyadicWeight (-(L : ℝ)) (i - j) * b.derivNorm L := by gcongr
      _ ≤ (b.derivNorm L + 2 ^ L * eLpNorm (momentKernel b.toFun L) 1 volume) *
            dyadicWeight (-(L : ℝ)) (i - j) := by
          rw [mul_comm]
          gcongr
          exact le_self_add
  · rw [mul_one]
    exact (b.eLpNorm_higherDiff_scaled_le' L l v).trans le_add_self

/-- **Differences of the dual kernels in `L_1`**: for `‖v‖ ≤ 2^(-i)`,
`‖Δ_v^L η_j‖_1 ≤ C 2^(-(i-j)L)` if `j ≤ i`, and `‖Δ_v^L η_j‖_1 ≤ C` if `j > i`. -/
theorem eLpNorm_higherDiff_dual_le (L : ℕ) {i j : ℕ} {v : V} (hv : ‖v‖ ≤ 1 / 2 ^ i) :
    eLpNorm ((fwdDiff v)^[L] (b.dual L j)) 1 volume ≤
      b.dualConst L * (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) := by
  set B := (b.derivNorm L + 2 ^ L * eLpNorm (momentKernel b.toFun L) 1 volume) *
    (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1)
  have h2 : b.dualConst L * (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) = B + B := by
    rw [dualConst, ← two_mul, mul_assoc]
  rw [h2]
  cases j with
  | zero =>
    exact (b.eLpNorm_higherDiff_scaled_le_dyadic L le_rfl hv).trans le_self_add
  | succ j =>
    change eLpNorm ((fwdDiff v)^[L] (b.scaled L (j + 1) + b.scaled L j)) 1 volume ≤ B + B
    rw [fwdDiff_iter_add]
    exact (eLpNorm_add_le le_rfl).trans (add_le_add
      (b.eLpNorm_higherDiff_scaled_le_dyadic L le_rfl hv)
      (b.eLpNorm_higherDiff_scaled_le_dyadic L (Nat.le_succ j) hv))

/-! ### Local means and the reproducing formula -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **local means** `f ↦ k_j ⋆ f` on `L_p`. -/
noncomputable def localMean (hp : p ≠ ∞) (L j : ℕ) :
    Lp ℂ p (volume : Measure V) →L[ℂ] Lp ℂ p (volume : Measure V) :=
  convLp hp (b.integrable_kernel L j)

/-- **The reproducing formula, partial sums**: `∑_{j ≤ J} η_j ⋆ k_j ⋆ f = m_{2^J} ⋆ m_{2^J} ⋆ f`,
from `a² - b² = (a - b)(a + b)` for the commuting operators `a = m_{2^(J+1)} ⋆`,
`b = m_{2^J} ⋆`. -/
theorem sum_dual_localMean (hp : p ≠ ∞) (L J : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ∑ j ∈ Finset.range (J + 1), convLp hp (b.integrable_dual L j) (b.localMean hp L j f) =
      convLp hp (b.integrable_scaled L J) (convLp hp (b.integrable_scaled L J) f) := by
  induction J with
  | zero =>
    rw [Finset.sum_range_one]
    rfl
  | succ J ih =>
    have hk : b.localMean hp L (J + 1) f = convLp hp (b.integrable_scaled L (J + 1)) f -
        convLp hp (b.integrable_scaled L J) f :=
      convLp_sub_kernel hp (b.integrable_scaled L (J + 1)) (b.integrable_scaled L J) f
    have hd : convLp hp (b.integrable_dual L (J + 1)) (b.localMean hp L (J + 1) f) =
        convLp hp (b.integrable_scaled L (J + 1)) (b.localMean hp L (J + 1) f) +
          convLp hp (b.integrable_scaled L J) (b.localMean hp L (J + 1) f) :=
      convLp_add_kernel hp (b.integrable_scaled L (J + 1)) (b.integrable_scaled L J) _
    rw [Finset.sum_range_succ, ih, hd, hk, map_sub, map_sub,
      convLp_comm hp (b.integrable_scaled L (J + 1)) (b.integrable_scaled L J)]
    abel

/-- **The reproducing formula at every point**: `∑_{j ≤ J} (η_j ⋆ (k_j ⋆ f))(y) =
(m_{2^J} ⋆ (m_{2^J} ⋆ f))(y)` for all `y`, since both sides are continuous and agree almost
everywhere (`Rd.LocalMeansBump.sum_dual_localMean`). -/
theorem sum_conv_dual_localMean_apply (hp : p ≠ ∞) (L J : ℕ)
    (f : Lp ℂ p (volume : Measure V)) (y : V) :
    ∑ j ∈ Finset.range (J + 1), conv (b.dual L j) (b.localMean hp L j f) volume y =
      conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume y := by
  have hp1 : 1 ≤ p := Fact.out
  have hcont1 : Continuous fun y =>
      ∑ j ∈ Finset.range (J + 1), conv (b.dual L j) (b.localMean hp L j f) volume y :=
    continuous_finsetSum _ fun j _ => (b.hasCompactSupport_dual L j).continuous_convolution_left
      (ContinuousLinearMap.mul ℂ ℂ) (b.continuous_dual L j) ((Lp.memLp _).locallyIntegrable hp1)
  have hcont2 : Continuous (conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume) :=
    (b.hasCompactSupport_scaled L J).continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ)
      (b.continuous_scaled L J) ((Lp.memLp _).locallyIntegrable hp1)
  have hae : (fun y => ∑ j ∈ Finset.range (J + 1),
      conv (b.dual L j) (b.localMean hp L j f) volume y) =ᵐ[volume]
        conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume := by
    have h1 := Lp.coeFn_fun_finsetSum (Finset.range (J + 1))
      (fun j => convLp hp (b.integrable_dual L j) (b.localMean hp L j f))
    rw [b.sum_dual_localMean hp L J f] at h1
    have h2 := convLp_apply_ae hp (b.integrable_scaled L J)
      (convLp hp (b.integrable_scaled L J) f)
    have h3 : ∀ᵐ y ∂volume, ∀ j, convLp hp (b.integrable_dual L j) (b.localMean hp L j f) y =
        conv (b.dual L j) (b.localMean hp L j f) volume y :=
      ae_all_iff.2 fun j => convLp_apply_ae hp _ _
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    rw [← hy2, hy1]
    exact Finset.sum_congr rfl fun j _ => (hy3 j).symm
  exact congrFun ((Continuous.ae_eq_iff_eq volume hcont1 hcont2).1 hae) y

/-- **The reproducing formula**: `∑_j η_j ⋆ k_j ⋆ f = f` in `L_p`, since
`m_{2^J} ⋆ m_{2^J} ⋆ f → f` (`m` is an approximate identity, `Rd.tendsto_convLp_dilate`, and the
operators `m_{2^J} ⋆` are uniformly bounded, `Rd.tendsto_apply_apply_of_tendsto`). -/
theorem tendsto_sum_dual_localMean (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L)
    (f : Lp ℂ p (volume : Measure V)) :
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1),
      convLp hp (b.integrable_dual L j) (b.localMean hp L j f)) atTop (𝓝 f) := by
  simp_rw [b.sum_dual_localMean hp L]
  have h : Tendsto (fun J => convLp hp (b.integrable_scaled L J) f) atTop (𝓝 f) :=
    tendsto_convLp_dilate hp (integrable_momentKernel b.integrable L)
      (integral_momentKernel b.integrable b.integral_eq_one hL) (c := fun J : ℕ => (2 : ℝ) ^ J)
      (fun J => pow_ne_zero J two_ne_zero) (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) f
  refine tendsto_apply_apply_of_tendsto (T := fun J => convLp hp (b.integrable_scaled L J))
    (C := (eLpNorm (momentKernel b.toFun L) 1 volume).toReal) (fun J g => ?_) h
  have h1 := norm_convLp_le hp (b.integrable_scaled L J) g
  rwa [b.eLpNorm_scaled_one] at h1

/-- The **local means quasi-norm** `‖(2^(js) ‖k_j ⋆ f‖_p)_j‖_{ℓ_q}`. -/
noncomputable def localMeansNorm (hp : p ≠ ∞) (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) : ℝ≥0∞ :=
  lqNorm q (fun j => dyadicWeight s j * ‖b.localMean hp L j f‖ₑ)

/-! ### Local means are bounded by the modulus -/

/-- `‖k_0 ⋆ f‖_p ≤ ‖m‖_1 ‖f‖_p`. -/
theorem enorm_localMean_zero_le (hp : p ≠ ∞) (L : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ‖b.localMean hp L 0 f‖ₑ ≤ eLpNorm (momentKernel b.toFun L) 1 volume * ‖f‖ₑ :=
  (enorm_convLp_le hp (b.integrable_kernel L 0) f).trans_eq
    (congrArg (· * ‖f‖ₑ) (b.eLpNorm_scaled_one L 0))

/-- **Local means are bounded by the modulus**:
`‖k_{j+1} ⋆ f‖_p ≤ 2 ‖g‖_1 (1 + R)^L ω_L(f, 2^(-j))_p`, since
`k_{j+1} ⋆ f = (f - m_{2^j} ⋆ f) - (f - m_{2^(j+1)} ⋆ f)` and `f - m_c ⋆ f` averages differences
with steps of length at most `R/c`. -/
theorem enorm_localMean_succ_le (hp : p ≠ ∞) (L j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ‖b.localMean hp L (j + 1) f‖ₑ ≤
      2 * (∫⁻ z, ‖b.toFun z‖ₑ) * ENNReal.ofReal (1 + b.radius) ^ L * lpModulus p L f j := by
  set A := ∫⁻ z, ‖b.toFun z‖ₑ
  have hk : b.localMean hp L (j + 1) f = (f - convLp hp (b.integrable_scaled L j) f) -
      (f - convLp hp (b.integrable_scaled L (j + 1)) f) := by
    rw [show b.localMean hp L (j + 1) f = convLp hp (b.integrable_scaled L (j + 1)) f -
        convLp hp (b.integrable_scaled L j) f from
      convLp_sub_kernel hp (b.integrable_scaled L (j + 1)) (b.integrable_scaled L j) f]
    abel
  have hω : ∀ i, ‖f - convLp hp (b.integrable_scaled L i) f‖ₑ ≤
      A * modulus volume L p (f : V → ℂ) (b.radius / 2 ^ i) := fun i =>
    enorm_sub_convLp_momentKernel_le hp b.integrable b.integral_eq_one b.eq_zero L
      (by positivity) f
  have hmono : modulus volume L p (f : V → ℂ) (b.radius / 2 ^ (j + 1)) ≤
      modulus volume L p (f : V → ℂ) (b.radius / 2 ^ j) :=
    modulus_mono L p _ (div_le_div_of_nonneg_left b.radius_nonneg (by positivity)
      (pow_le_pow_right₀ one_le_two (Nat.le_succ j)))
  have hdil : modulus volume L p (f : V → ℂ) (b.radius / 2 ^ j) ≤
      ENNReal.ofReal (1 + b.radius) ^ L * lpModulus p L f j := by
    rw [lpModulus, show b.radius / 2 ^ j = b.radius * (1 / 2 ^ j) by ring]
    exact modulus_mul_le (Lp.aestronglyMeasurable f) Fact.out L b.radius_nonneg (by positivity)
  calc ‖b.localMean hp L (j + 1) f‖ₑ
      ≤ ‖f - convLp hp (b.integrable_scaled L j) f‖ₑ +
          ‖f - convLp hp (b.integrable_scaled L (j + 1)) f‖ₑ := by
        rw [hk]
        exact eNorm_sub_le
    _ ≤ A * modulus volume L p (f : V → ℂ) (b.radius / 2 ^ j) +
          A * modulus volume L p (f : V → ℂ) (b.radius / 2 ^ j) :=
        add_le_add (hω j) ((hω (j + 1)).trans (by gcongr))
    _ ≤ A * (ENNReal.ofReal (1 + b.radius) ^ L * lpModulus p L f j) +
          A * (ENNReal.ofReal (1 + b.radius) ^ L * lpModulus p L f j) := by gcongr
    _ = 2 * A * ENNReal.ofReal (1 + b.radius) ^ L * lpModulus p L f j := by ring

/-- The constant of the upper bound, `‖m‖_1 + 2^s · 2 ‖g‖_1 (1 + R)^L`. -/
noncomputable def upperConst (L : ℕ) (s : ℝ) : ℝ≥0∞ :=
  eLpNorm (momentKernel b.toFun L) 1 volume +
    2 ^ s * (2 * (∫⁻ z, ‖b.toFun z‖ₑ) * ENNReal.ofReal (1 + b.radius) ^ L)

/-- The constant of the upper bound is finite. -/
theorem upperConst_ne_top (L : ℕ) (s : ℝ) : b.upperConst L s ≠ ∞ :=
  ENNReal.add_ne_top.2
    ⟨(eLpNorm_momentKernel_ne_top b.integrable L),
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg' (by norm_num) (by simp))
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) b.integrable.2.ne)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))⟩

/-- **The local means quasi-norm is bounded by the modulus**:
`‖(2^(js) ‖k_j ⋆ f‖_p)_j‖_{ℓ_q} ≤ C (‖f‖_p + ‖(2^(js) ω_L(f, 2^(-j))_p)_j‖_{ℓ_q})`. -/
theorem localMeansNorm_le (hp : p ≠ ∞) (L : ℕ) (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure V)) :
    b.localMeansNorm hp L s q f ≤
      b.upperConst L s * (‖f‖ₑ + lqNorm q (fun j => dyadicWeight s j * lpModulus p L f j)) := by
  set C' := 2 * (∫⁻ z, ‖b.toFun z‖ₑ) * ENNReal.ofReal (1 + b.radius) ^ L
  set M := eLpNorm (momentKernel b.toFun L) 1 volume
  set Λ := lqNorm q (fun j => dyadicWeight s j * lpModulus p L f j)
  have htail : lqNorm q (fun j => dyadicWeight s (j + 1) * ‖b.localMean hp L (j + 1) f‖ₑ) ≤
      2 ^ s * C' * Λ := by
    rw [← ENNReal.lqNorm_const_mul]
    refine ENNReal.lqNorm_mono fun j => ?_
    rw [ENNReal.dyadicWeight_succ]
    calc 2 ^ s * dyadicWeight s j * ‖b.localMean hp L (j + 1) f‖ₑ
        ≤ 2 ^ s * dyadicWeight s j * (C' * lpModulus p L f j) :=
          mul_le_mul' le_rfl (b.enorm_localMean_succ_le hp L j f)
      _ = 2 ^ s * C' * (dyadicWeight s j * lpModulus p L f j) := by ring
  calc b.localMeansNorm hp L s q f
      ≤ dyadicWeight s 0 * ‖b.localMean hp L 0 f‖ₑ +
          lqNorm q (fun j => dyadicWeight s (j + 1) * ‖b.localMean hp L (j + 1) f‖ₑ) :=
        ENNReal.lqNorm_le_head_add_shift hq _
    _ ≤ M * ‖f‖ₑ + 2 ^ s * C' * Λ := by
        rw [ENNReal.dyadicWeight_zero_right, one_mul]
        exact add_le_add (b.enorm_localMean_zero_le hp L f) htail
    _ ≤ b.upperConst L s * ‖f‖ₑ + b.upperConst L s * Λ := by
        gcongr
        · exact le_self_add
        · exact le_add_self
    _ = b.upperConst L s * (‖f‖ₑ + Λ) := by ring

/-! ### The modulus is bounded by the local means -/

/-- **The moduli of the reproducing terms**: for `η_j ⋆ h`,
`ω_L(η_j ⋆ h, 2^(-i))_p ≤ C c_{ij} ‖h‖_p` with `c_{ij} = 2^(-(i-j)L)` for `j ≤ i` and `1` for
`j > i`. -/
theorem lpModulus_dual_le (hp : p ≠ ∞) (L i j : ℕ) (h : Lp ℂ p (volume : Measure V)) :
    lpModulus p L (convLp hp (b.integrable_dual L j) h) i ≤
      b.dualConst L * (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) * ‖h‖ₑ :=
  lpModulus_convLp_le hp (b.integrable_dual L j) L i
    (fun _ hv => b.eLpNorm_higherDiff_dual_le L hv) h

/-- The constant of the synthesis estimate,
`2 ‖m‖_1 (1 - 2^(-s))⁻¹ + C_η ((1 - 2^(-(L-s)))⁻¹ + (1 - 2^(-s))⁻¹)`. -/
noncomputable def synthConst (L : ℕ) (s : ℝ) : ℝ≥0∞ :=
  2 * eLpNorm (momentKernel b.toFun L) 1 volume * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ +
    b.dualConst L * ((1 - (2 : ℝ≥0∞) ^ (-((L : ℝ) - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹)

/-- The constant of the synthesis estimate is finite for `0 < s < L`. -/
theorem synthConst_ne_top {L : ℕ} {s : ℝ} (hs : 0 < s) (hsL : s < L) : b.synthConst L s ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      (eLpNorm_momentKernel_ne_top b.integrable L))
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs),
    ENNReal.mul_ne_top (b.dualConst_ne_top L) (ENNReal.add_ne_top.2
      ⟨ENNReal.one_sub_two_rpow_neg_inv_ne_top (by linarith),
        ENNReal.one_sub_two_rpow_neg_inv_ne_top hs⟩)⟩

/-- **Synthesis with the dual kernels**: if `F = ∑_j η_j ⋆ h_j` in `L_p` (as the limit of the
partial sums), then for `0 < s < L`,
`‖F‖_p + ‖(2^(is) ω_L(F, 2^(-i))_p)_i‖_{ℓ_q} ≤ C ‖(2^(js) ‖h_j‖_p)_j‖_{ℓ_q}`, by the bound of a
convergent series by its weighted terms (`ENNReal.enorm_le_of_tendsto_sum`), the moduli of the
terms (`Rd.LocalMeansBump.lpModulus_dual_le`) and Hardy's inequalities. -/
theorem modNorm_le_of_tendsto (hp : p ≠ ∞) (L : ℕ) (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {F : Lp ℂ p (volume : Measure V)} {h : ℕ → Lp ℂ p (volume : Measure V)}
    (hrep : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1),
      convLp hp (b.integrable_dual L j) (h j)) atTop (𝓝 F)) :
    ‖F‖ₑ + lqNorm q (fun i => dyadicWeight s i * lpModulus p L F i) ≤
      b.synthConst L s * lqNorm q (fun j => dyadicWeight s j * ‖h j‖ₑ) := by
  set a : ℕ → ℝ≥0∞ := fun j => ‖h j‖ₑ
  set X := lqNorm q (fun j => dyadicWeight s j * a j)
  set M := eLpNorm (momentKernel b.toFun L) 1 volume
  -- the norm of `f`
  have hnorm : ‖F‖ₑ ≤ 2 * M * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X :=
    ENNReal.enorm_le_of_tendsto_sum hrep (K := 2 * M) (b := a)
      (fun j => (enorm_convLp_le hp _ _).trans (mul_le_mul' (b.eLpNorm_dual_one_le L j) le_rfl))
      s hq
  -- the moduli
  have hmod : ∀ i, lpModulus p L F i ≤ b.dualConst L *
      ∑' j, (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) * a j := fun i => by
    have h1 : lpModulus p L F i ≤
        ∑' j, lpModulus p L (convLp hp (b.integrable_dual L j) (h j)) i :=
      ENNReal.le_tsum_of_tendsto_sum (C := 2 ^ L) (by simp) (fun x y => lpModulus_add_le L x y i)
        (fun x => lpModulus_le L x i) hrep
    refine h1.trans ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun j => ?_
    rw [← mul_assoc]
    exact b.lpModulus_dual_le hp L i j _
  have hlq : lqNorm q (fun i => dyadicWeight s i * lpModulus p L F i) ≤
      b.dualConst L * ENNReal.almostDiagonalConst s L * X :=
    ENNReal.lqNorm_le_almostDiagonalConst_mul_of_le hq s L hmod
  calc ‖F‖ₑ + lqNorm q (fun i => dyadicWeight s i * lpModulus p L F i)
      ≤ 2 * M * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X +
          b.dualConst L * ENNReal.almostDiagonalConst s L * X := add_le_add hnorm hlq
    _ = _ := by rw [synthConst, ENNReal.almostDiagonalConst]; ring

/-- **The modulus is bounded by the local means**: for `0 < s < L`,
`‖f‖_p + ‖(2^(is) ω_L(f, 2^(-i))_p)_i‖_{ℓ_q} ≤ C ‖(2^(js) ‖k_j ⋆ f‖_p)_j‖_{ℓ_q}`, by the
reproducing formula and the synthesis estimate. -/
theorem modNorm_le_localMeansNorm (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) (s : ℝ) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    ‖f‖ₑ + lqNorm q (fun i => dyadicWeight s i * lpModulus p L f i) ≤
      b.synthConst L s * b.localMeansNorm hp L s q f :=
  b.modNorm_le_of_tendsto hp L s hq (b.tendsto_sum_dual_localMean hp hL f)

/-! ### Local means and Besov spaces -/

/-- **Local means and differences**: for `1 ≤ p < ∞`, `0 < s < L` and `1 ≤ q ≤ ∞`,
`‖f‖_p + ‖(2^(ks) ω_L(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff `‖(2^(js) ‖k_j ⋆ f‖_p)_j‖_{ℓ_q} < ∞`. -/
theorem besov_iff_localMeans (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s < L) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p L f k) < ∞ ↔
      b.localMeansNorm hp L s q f < ∞ := by
  constructor
  · intro h
    exact (b.localMeansNorm_le hp L s hq f).trans_lt
      (ENNReal.mul_lt_top (b.upperConst_ne_top L s).lt_top h)
  · intro h
    exact (b.modNorm_le_localMeansNorm hp hL s hq f).trans_lt
      (ENNReal.mul_lt_top (b.synthConst_ne_top hs hsL).lt_top h)

/-- **Local means and band-limited approximation**: for `1 ≤ p < ∞`, `0 < s < L` and
`1 ≤ q ≤ ∞`, `f ∈ A^s_q(L_p, (E_k))` iff `‖(2^(js) ‖k_j ⋆ f‖_p)_j‖_{ℓ_q} < ∞`. -/
theorem memApprox_bandScheme_iff_localMeans (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ}
    (hs : 0 < s) (hsL : s < L) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    (bandScheme hp).MemApprox s q f ↔ b.localMeansNorm hp L s q f < ∞ := by
  rw [memApprox_bandScheme_iff_modulus hp hs.le hsL hq f, b.besov_iff_localMeans hp hL hs hsL hq f]

end LocalMeansBump

/-! ### Bumps from smooth bump functions -/

/-- **The mollifier of a bump function**: the normalised smooth bump `f` around `c` (Mathlib's
`ContDiffBump.normed`), with complex values; it is smooth with compact support in the closed ball
`closedBall(c, r_out)` and has integral `1`. -/
noncomputable def bumpMollifier {c : V} (f : ContDiffBump c) : V → ℂ :=
  fun z => ((f.normed volume z : ℝ) : ℂ)

/-- The mollifier of a bump function is smooth. -/
theorem contDiff_bumpMollifier {c : V} (f : ContDiffBump c) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bumpMollifier f) :=
  Complex.ofRealCLM.contDiff.comp (f.contDiff_normed (n := ⊤))

/-- The mollifier of a bump function has its closed support in `closedBall(c, r_out)`. -/
theorem tsupport_bumpMollifier_subset {c : V} (f : ContDiffBump c) :
    tsupport (bumpMollifier f) ⊆ Metric.closedBall c f.rOut :=
  (tsupport_comp_subset Complex.ofReal_zero _).trans (f.tsupport_normed_eq (μ := volume)).subset

/-- The mollifier of a bump function has compact support, since the normalised bump has
(Mathlib's `ContDiffBump.hasCompactSupport_normed`). -/
theorem hasCompactSupport_bumpMollifier {c : V} (f : ContDiffBump c) :
    HasCompactSupport (bumpMollifier f) :=
  (f.hasCompactSupport_normed (μ := volume)).comp_left Complex.ofReal_zero

/-- The mollifier of a bump function has integral `1` (Mathlib's `ContDiffBump.integral_normed`). -/
theorem integral_bumpMollifier {c : V} (f : ContDiffBump c) : ∫ z, bumpMollifier f z = 1 := by
  change ∫ z, ((f.normed volume z : ℝ) : ℂ) = 1
  rw [integral_complex_ofReal, f.integral_normed, Complex.ofReal_one]

/-- **The bump for local means of a smooth bump function**: the mollifier of a smooth bump `f`
around `c` with outer radius `r_out` vanishes outside `closedBall(c, r_out)`, hence outside the
ball of
every radius `R ≥ ‖c‖ + r_out` around `0`, since `‖z‖ ≤ ‖z - c‖ + ‖c‖`. -/
noncomputable def LocalMeansBump.ofContDiffBump {c : V} (f : ContDiffBump c) {R : ℝ}
    (hR : ‖c‖ + f.rOut ≤ R) : LocalMeansBump V where
  toFun := bumpMollifier f
  radius := R
  radius_nonneg := (add_nonneg (norm_nonneg c) f.rOut_pos.le).trans hR
  contDiff := contDiff_bumpMollifier f
  eq_zero z hz := image_eq_zero_of_notMem_tsupport fun h => by
    have := mem_closedBall_iff_norm.1 (tsupport_bumpMollifier_subset f h)
    linarith [norm_sub_norm_le z c]
  integral_eq_one := integral_bumpMollifier f

/-! ### The centred bump -/

section Centered

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The smooth bump around `0` with outer radius `R`. -/
noncomputable def centeredBumpBase {R : ℝ} (hR : 0 < R) : ContDiffBump (0 : V) :=
  ⟨R / 2, R, by positivity, by linarith⟩

/-- The **centred bump** of radius `R > 0`: the normalised smooth bump function around `0`. -/
noncomputable def LocalMeansBump.centered {R : ℝ} (hR : 0 < R) : LocalMeansBump V :=
  ofContDiffBump (centeredBumpBase hR) (R := R) (by simp [centeredBumpBase])

/-- The centred bump has radius `R`. -/
theorem LocalMeansBump.centered_radius {R : ℝ} (hR : 0 < R) :
    (LocalMeansBump.centered (V := V) hR).radius = R := rfl

end Centered

end Rd
