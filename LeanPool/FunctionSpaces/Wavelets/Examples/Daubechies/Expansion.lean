/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Maximal.DyadicGrid
public import LeanPool.FunctionSpaces.Wavelets.DyadicNormalisation
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Expansions in dilated and translated generators

Let `g : ℝ → ℂ` vanish outside a bounded interval `[a, b]`. Its dilated and translated copies
`g_{j,k}(x) = 2^(j/2) g(2^j x - k)` of level `j ∈ ℕ` and position `k ∈ ℤ`
(`Daubechies.scaledFun`) give the expansions and the coefficients

`∑_{k ∈ ℤ} c_k g_{j,k}(x)` (`Daubechies.expand`) and
`⟨f, g_{j,k}⟩ = ∫ f(y) conj g_{j,k}(y) dy` (`Daubechies.coeffFun`).

The file is generic in `g`, so that it serves the scaling function `φ` (support `[0, 2N - 1]`,
`FunctionSpaces.Wavelets.Examples.Daubechies.ExpansionScaling`) and the wavelet `ψ` alike.

* **Finitely many terms.** `g_{j,k}` vanishes outside the support window
  `{x : 2^j x - k ∈ [a, b]} = [(k + a)/2^j, (k + b)/2^j]` (`Daubechies.supportWindow`), and
  every point lies in at most `M = ⌈b - a⌉ + 1` windows of one level
  (`Daubechies.card_le_of_forall_mem_supportWindow`). Hence every expansion is a finite sum at
  each point (`Daubechies.expand_eq_sum`), continuous if `g` is continuous
  (`Daubechies.continuous_expand`), and a.e. strongly measurable if `g` is
  (`Daubechies.aestronglyMeasurable_expand`).
* **Orthonormality and coefficient recovery.** The generators of level `0` are the integer
  translates `g(· - k)` (`Daubechies.scaledFun_zero`). If these are orthonormal, then so are the
  `g_{j,k}` of every level (`Daubechies.integral_scaledFun_mul_conj`, by the substitution
  `u = 2^j x`, `Daubechies.integral_eq_two_pow_mul_integral_comp`), and
  `⟨∑_l c_l g_{j,l}, g_{j,k}⟩ = c_k` for every coefficient sequence `c`
  (`Daubechies.coeffFun_expand`).
* **Stability.** Let `1 ≤ p < ∞`, let `M = ⌈b - a⌉ + 1` be the overlap number and `p'` the
  conjugate exponent. The upper estimate
  `‖∑_k c_k g_{j,k}‖_p ≤ M^(1 - 1/p) ‖g‖_p 2^(j(1/2 - 1/p)) ‖c‖_{ℓ_p}`
  (`Daubechies.eLpNorm_expand_le`) follows from the bounded overlap inequality
  (`Rd.eLpNorm_rpow_le_of_overlap`) and `‖g_{j,k}‖_p = 2^(j(1/2 - 1/p)) ‖g‖_p`
  (`Daubechies.eLpNorm_scaledFun`). The coefficient estimate
  `‖(⟨f, g_{j,k}⟩)_k‖_{ℓ_p} ≤ M^(1/p) ‖g‖_{p'} 2^(-j(1/2 - 1/p)) ‖f‖_p`
  (`Daubechies.lqNorm_coeffFun_le`) follows from Hölder's inequality on each window and the
  window inequality `∑_k ∫_{W_k} F ≤ M ∫ F` (`MeasureTheory.tsum_setLIntegral_le_mul_lintegral`).
  Together with coefficient recovery it gives the lower estimate
  `2^(j(1/2 - 1/p)) ‖c‖_{ℓ_p} ≤ M^(1/p) ‖g‖_{p'} ‖∑_k c_k g_{j,k}‖_p` for orthonormal translates
  (`Daubechies.lqNorm_le_eLpNorm_expand`). The constants (`Daubechies.expandConst`,
  `Daubechies.coeffConst`) are the same for every level.
* **`L_p` membership and linearity.** Expansions with `ℓ_p` coefficients lie in `L_p`
  (`Daubechies.memLp_expand`), and so does the expansion of the coefficients of an `L_p`
  function (`Daubechies.memLp_expand_coeffFun`), with
  `‖∑_k ⟨f, g_{j,k}⟩ g_{j,k}‖_p ≤ C C' ‖f‖_p` uniformly in the level
  (`Daubechies.eLpNorm_expand_coeffFun_le`). Expansions are linear in the coefficients and the
  coefficients are linear in `f` (`Daubechies.expand_add`, `Daubechies.expand_const_mul`,
  `Daubechies.coeffFun_add`, `Daubechies.coeffFun_const_mul`).
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped ENNReal ComplexConjugate
open ENNReal (dyadicWeight)

namespace MeasureTheory

/-- **The window inequality**: let `I_i`, `i ∈ ι`, be countably many measurable sets such that
every point lies in at most `M` of them (every finite set `S` of indices with `x ∈ I_i` for all
`i ∈ S` has at most `M` elements). Then `∑_i ∫_{I_i} F ≤ M ∫ F` for every a.e. measurable
`F : α → [0, ∞]`. Indeed `∑_i 1_{I_i}(x) F(x) ≤ M F(x)` at every point, and the sum and the
integral may be exchanged (Mathlib's `MeasureTheory.lintegral_tsum`). -/
theorem tsum_setLIntegral_le_mul_lintegral {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {μ : Measure α} {I : ι → Set α} (hI : ∀ i, MeasurableSet (I i)) {M : ℕ}
    (hM : ∀ x (S : Finset ι), (∀ i ∈ S, x ∈ I i) → S.card ≤ M) {F : α → ℝ≥0∞}
    (hF : AEMeasurable F μ) :
    ∑' i, ∫⁻ x in I i, F x ∂μ ≤ M * ∫⁻ x, F x ∂μ := by
  have hpt : ∀ x, ∑' i, (I i).indicator F x ≤ M * F x := fun x => by
    obtain ⟨T, hT, hTM⟩ := Rd.exists_finset_of_card_le (P := fun i => x ∈ I i) (hM x)
    rw [tsum_eq_sum (s := T) fun i hi => Set.indicator_of_notMem (fun h => hi (hT i h)) _]
    calc ∑ i ∈ T, (I i).indicator F x ≤ ∑ _i ∈ T, F x :=
          Finset.sum_le_sum fun i _ => Set.indicator_le_self _ _ x
      _ = T.card * F x := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M * F x := by gcongr
  calc ∑' i, ∫⁻ x in I i, F x ∂μ = ∑' i, ∫⁻ x, (I i).indicator F x ∂μ := by
        congr 1
        funext i
        rw [lintegral_indicator (hI i)]
    _ = ∫⁻ x, ∑' i, (I i).indicator F x ∂μ :=
        (lintegral_tsum fun i => hF.indicator (hI i)).symm
    _ ≤ ∫⁻ x, M * F x ∂μ := lintegral_mono hpt
    _ = M * ∫⁻ x, F x ∂μ := lintegral_const_mul' _ _ (ENNReal.natCast_ne_top M)

end MeasureTheory

namespace Daubechies

/-! ### Dilated and translated generators -/

section Generic

variable {g : ℝ → ℂ} {a b : ℝ}

/-- **The dilated and translated generator** `g_{j,k}(x) = 2^(j/2) g(2^j x - k)` of level
`j ∈ ℕ` and position `k ∈ ℤ`. The factor `2^(j/2)` makes the `L_2` norm independent of `j` and
`k`. For the scaling function `g = φ` these are the functions `φ_{j,k}` of the multiresolution
analysis (`Daubechies.scaled`). -/
noncomputable def scaledFun (g : ℝ → ℂ) (j : ℕ) (k : ℤ) (x : ℝ) : ℂ :=
  (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * g (2 ^ j * x - k)

/-- **The expansion** `∑_{k ∈ ℤ} c_k g_{j,k}(x)` of level `j` with coefficients `c : ℤ → ℂ`. If
`g` vanishes outside a bounded interval, only finitely many terms are nonzero at each point
(`Daubechies.expand_eq_sum`), so the sum is meaningful for every coefficient sequence. -/
noncomputable def expand (g : ℝ → ℂ) (j : ℕ) (c : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑' k : ℤ, c k * scaledFun g j k x

/-- **The coefficient functional** `⟨f, g_{j,k}⟩ = ∫ f(y) conj g_{j,k}(y) dy` of level `j` and
position `k`. For an orthonormal system it recovers the coefficients of an expansion
(`Daubechies.coeffFun_expand`). -/
noncomputable def coeffFun (g : ℝ → ℂ) (j : ℕ) (f : ℝ → ℂ) (k : ℤ) : ℂ :=
  ∫ y, f y * conj (scaledFun g j k y)

/-- **The support window** `{x : 2^j x - k ∈ [a, b]}` of level `j` and position `k`: the
interval `[(k + a)/2^j, (k + b)/2^j]` (`Daubechies.supportWindow_eq_Icc`) outside which
`g_{j,k}` vanishes when `g` vanishes outside `[a, b]` (`Daubechies.scaledFun_eq_zero`). -/
def supportWindow (a b : ℝ) (j : ℕ) (k : ℤ) : Set ℝ := {x | (2 : ℝ) ^ j * x - k ∈ Set.Icc a b}

/-- The support window is the interval `[(k + a)/2^j, (k + b)/2^j]`. -/
theorem supportWindow_eq_Icc (a b : ℝ) (j : ℕ) (k : ℤ) :
    supportWindow a b j k = Set.Icc ((k + a) / 2 ^ j) ((k + b) / 2 ^ j) := by
  ext x
  have h : (0 : ℝ) < 2 ^ j := by positivity
  simp only [supportWindow, Set.mem_ofPred_eq, Set.mem_Icc, div_le_iff₀ h, le_div_iff₀ h]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The support windows are measurable (closed intervals). -/
theorem measurableSet_supportWindow (a b : ℝ) (j : ℕ) (k : ℤ) :
    MeasurableSet (supportWindow a b j k) := by
  rw [supportWindow_eq_Icc]
  exact measurableSet_Icc

/-- The support windows are compact (closed bounded intervals). -/
theorem isCompact_supportWindow (a b : ℝ) (j : ℕ) (k : ℤ) :
    IsCompact (supportWindow a b j k) := by
  rw [supportWindow_eq_Icc]
  exact isCompact_Icc

/-- **Support of `g_{j,k}`**: if `g` vanishes outside `[a, b]`, then `g_{j,k}(x) = 0` for every
`x` outside the support window `{x : 2^j x - k ∈ [a, b]}`. -/
theorem scaledFun_eq_zero (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) {j : ℕ} {k : ℤ} {x : ℝ}
    (hx : x ∉ supportWindow a b j k) : scaledFun g j k x = 0 := by
  rw [scaledFun, hsupp _ hx, mul_zero]

/-- If `g` vanishes outside `[a, b]` and `g_{j,k}(x) ≠ 0`, then `x` lies in the support window
`{x : 2^j x - k ∈ [a, b]}` (`Daubechies.scaledFun_eq_zero`). -/
theorem mem_supportWindow_of_scaledFun_ne_zero (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) {j : ℕ}
    {k : ℤ} {x : ℝ} (h : scaledFun g j k x ≠ 0) : x ∈ supportWindow a b j k :=
  by_contra fun hx => h (scaledFun_eq_zero hsupp hx)

/-- **`g_{j,k}` has compact support** if `g` vanishes outside `[a, b]`: it vanishes outside the
compact support window (`Daubechies.scaledFun_eq_zero`). -/
theorem hasCompactSupport_scaledFun (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) (j : ℕ) (k : ℤ) :
    HasCompactSupport (scaledFun g j k) :=
  HasCompactSupport.intro (isCompact_supportWindow a b j k) fun _ hx => scaledFun_eq_zero hsupp hx

/-- **`g_{j,k}` is continuous** if `g` is. -/
theorem continuous_scaledFun (hg : Continuous g) (j : ℕ) (k : ℤ) :
    Continuous (scaledFun g j k) :=
  continuous_const.mul (hg.comp ((continuous_const.mul continuous_id).sub continuous_const))

/-- **The generators of level `0` are the integer translates**: `g_{0,k}(x) = g(x - k)` for every
`g : ℝ → ℂ`, `k ∈ ℤ` and `x ∈ ℝ`, since `2^0 = 1`. -/
theorem scaledFun_zero (g : ℝ → ℂ) (k : ℤ) (x : ℝ) : scaledFun g 0 k x = g (x - k) := by
  simp [scaledFun]

/-! ### Finitely many terms at each point -/

/-- **The integers in an interval**: if `t - k ∈ [a, b]` for an integer `k`, then
`⌈t - b⌉ ≤ k ≤ ⌊t - a⌋`. -/
theorem mem_Icc_ceil_floor {t : ℝ} {k : ℤ} (h : t - k ∈ Set.Icc a b) :
    k ∈ Finset.Icc ⌈t - b⌉ ⌊t - a⌋ :=
  Finset.mem_Icc.2 ⟨Int.ceil_le.2 (by linarith [h.2]), Int.le_floor.2 (by linarith [h.1])⟩

/-- **Counting integers in an interval of length `b - a`**: the integers `k` with
`⌈t - b⌉ ≤ k ≤ ⌊t - a⌋` number at most `⌈b - a⌉ + 1`, for all real `t`, `a`, `b`. -/
theorem card_Icc_ceil_floor_le (t a b : ℝ) :
    (Finset.Icc ⌈t - b⌉ ⌊t - a⌋).card ≤ ⌈b - a⌉₊ + 1 := by
  rw [Int.card_Icc, Int.toNat_le]
  have h1 := Int.floor_le (t - a)
  have h2 := Int.le_ceil (t - b)
  have h3 := Nat.le_ceil (b - a)
  have h : ((⌊t - a⌋ + 1 - ⌈t - b⌉ : ℤ) : ℝ) ≤ ((⌈b - a⌉₊ + 1 : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast h

/-- **Bounded overlap of the support windows**: every point `x` lies in at most `⌈b - a⌉ + 1`
of the windows `{x : 2^j x - k ∈ [a, b]}`, `k ∈ ℤ`, of one level `j`: such `k` satisfy
`⌈2^j x - b⌉ ≤ k ≤ ⌊2^j x - a⌋` (`Daubechies.mem_Icc_ceil_floor`,
`Daubechies.card_Icc_ceil_floor_le`). -/
theorem card_le_of_forall_mem_supportWindow {j : ℕ} (x : ℝ) (S : Finset ℤ)
    (hS : ∀ k ∈ S, x ∈ supportWindow a b j k) : S.card ≤ ⌈b - a⌉₊ + 1 :=
  (Finset.card_le_card fun k hk => mem_Icc_ceil_floor (hS k hk)).trans
    (card_Icc_ceil_floor_le _ a b)

/-- **Expansions are finite sums**: if `g` vanishes outside `[a, b]`, then for every level `j`,
coefficients `c` and point `x`,
`∑_{k ∈ ℤ} c_k g_{j,k}(x) = ∑_{k = ⌈2^j x - b⌉}^{⌊2^j x - a⌋} c_k g_{j,k}(x)`. -/
theorem expand_eq_sum (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) (j : ℕ) (c : ℤ → ℂ) (x : ℝ) :
    expand g j c x =
      ∑ k ∈ Finset.Icc ⌈2 ^ j * x - b⌉ ⌊2 ^ j * x - a⌋, c k * scaledFun g j k x :=
  tsum_eq_sum fun _ hk => by
    rw [scaledFun_eq_zero hsupp (fun hx => hk (mem_Icc_ceil_floor hx)), mul_zero]

/-- The series `∑_k c_k g_{j,k}(x)` converges for every point `x`, if `g` vanishes outside
`[a, b]`: only finitely many terms are nonzero. -/
theorem summable_expand (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) (j : ℕ) (c : ℤ → ℂ) (x : ℝ) :
    Summable fun k => c k * scaledFun g j k x :=
  summable_of_ne_finset_zero (s := Finset.Icc ⌈2 ^ j * x - b⌉ ⌊2 ^ j * x - a⌋) fun _ hk => by
    rw [scaledFun_eq_zero hsupp (fun hx => hk (mem_Icc_ceil_floor hx)), mul_zero]

/-- **Expansions are continuous**: if `g` is continuous and vanishes outside `[a, b]`, then
`x ↦ ∑_k c_k g_{j,k}(x)` is continuous for every level `j` and all coefficients `c`. Near a point
`x`, at all `y` with `|2^j y - 2^j x| < 1`, the expansion is the same finite sum over
`⌈2^j x - b - 1⌉ ≤ k ≤ ⌊2^j x - a + 1⌋`, a continuous function. -/
theorem continuous_expand (hg : Continuous g) (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) (j : ℕ)
    (c : ℤ → ℂ) : Continuous (expand g j c) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hU : ∀ᶠ y in 𝓝 x, (2 : ℝ) ^ j * y ∈ Set.Ioo ((2 : ℝ) ^ j * x - 1) (2 ^ j * x + 1) :=
    (continuous_const_mul ((2 : ℝ) ^ j)).continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds (by linarith) (by linarith))
  have hev : (fun y => ∑ k ∈ Finset.Icc ⌈2 ^ j * x - (b + 1)⌉ ⌊2 ^ j * x - (a - 1)⌋,
      c k * scaledFun g j k y) =ᶠ[𝓝 x] expand g j c := by
    filter_upwards [hU] with y hy
    refine (tsum_eq_sum fun k hk => ?_).symm
    refine by_contra fun h => hk (mem_Icc_ceil_floor ?_)
    have hmem := mem_supportWindow_of_scaledFun_ne_zero hsupp (right_ne_zero_of_mul h)
    exact ⟨by linarith [hmem.1, hy.2], by linarith [hmem.2, hy.1]⟩
  exact ((continuous_finsetSum _ fun k _ =>
    continuous_const.mul (continuous_scaledFun hg j k)).continuousAt).congr hev

/-! ### Orthonormality at every level -/

/-- **The dyadic substitution**: `∫ g(u) du = 2^j ∫ g(2^j y) dy` for every `g : ℝ → ℂ` and every
`j ∈ ℕ`, by the substitution `u = 2^j y` (Mathlib's
`MeasureTheory.Measure.integral_comp_mul_left`). Both sides are `0` when `g` is not integrable. -/
theorem integral_eq_two_pow_mul_integral_comp (g : ℝ → ℂ) (j : ℕ) :
    ∫ u, g u = (2 : ℂ) ^ j * ∫ y, g (2 ^ j * y) := by
  rw [Measure.integral_comp_mul_left, abs_of_pos (by positivity), Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]

/-- **The product of two generators of one level**:
`g_{j,k}(x) conj g_{j,l}(x) = 2^j g(2^j x - k) conj g(2^j x - l)`, since the factor `2^(j/2)` is
real. -/
theorem scaledFun_mul_conj (j : ℕ) (k l : ℤ) (x : ℝ) :
    scaledFun g j k x * conj (scaledFun g j l x) =
      (2 : ℂ) ^ j * (g (2 ^ j * x - k) * conj (g (2 ^ j * x - l))) := by
  rw [scaledFun, scaledFun, map_mul, Complex.conj_ofReal, ← ofReal_two_rpow_half_mul_self j]
  ring

/-- **Orthonormality at every level**: if the integer translates of `g` are orthonormal,
`∫ g(x - k) conj g(x - l) dx = δ_{kl}` for all `k, l ∈ ℤ`, then so are the generators of every
level `j`: `∫ g_{j,k}(x) conj g_{j,l}(x) dx = δ_{kl}`. The substitution `u = 2^j x`
(`Daubechies.integral_eq_two_pow_mul_integral_comp`) cancels the factor `2^j` of
`Daubechies.scaledFun_mul_conj`. -/
theorem integral_scaledFun_mul_conj
    (horth : ∀ k l : ℤ, ∫ x, g (x - k) * conj (g (x - l)) = if k = l then 1 else 0)
    (j : ℕ) (k l : ℤ) :
    ∫ x, scaledFun g j k x * conj (scaledFun g j l x) = if k = l then 1 else 0 := by
  have h := integral_eq_two_pow_mul_integral_comp (fun u => g (u - k) * conj (g (u - l))) j
  simp_rw [scaledFun_mul_conj]
  rw [integral_const_mul, ← h, horth]

/-! ### Coefficient recovery -/

/-- **Generators of one level overlap only for nearby positions**: if `g` vanishes outside
`[a, b]`, then `g_{j,l}(y) conj g_{j,k}(y) = 0` for every `y` unless `|l - k| ≤ ⌈b - a⌉`. If both
factors are nonzero, then `2^j y - l` and `2^j y - k` lie in `[a, b]`, so `|l - k| ≤ b - a`. -/
theorem scaledFun_mul_conj_eq_zero (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) {j : ℕ} {k l : ℤ}
    (hl : l ∉ Finset.Icc (k - ⌈b - a⌉₊) (k + ⌈b - a⌉₊)) (y : ℝ) :
    scaledFun g j l y * conj (scaledFun g j k y) = 0 := by
  by_contra h
  obtain ⟨hl', hk'⟩ := mul_ne_zero_iff.1 h
  have h1 := mem_supportWindow_of_scaledFun_ne_zero hsupp hl'
  have h2 := mem_supportWindow_of_scaledFun_ne_zero hsupp fun h0 => hk' (by rw [h0, map_zero])
  have h3 := Nat.le_ceil (b - a)
  refine hl (Finset.mem_Icc.2 ⟨?_, ?_⟩)
  · have h4 : ((k - ⌈b - a⌉₊ : ℤ) : ℝ) ≤ l := by
      push_cast
      linarith [h1.2, h2.1]
    exact_mod_cast h4
  · have h4 : (l : ℝ) ≤ ((k + ⌈b - a⌉₊ : ℤ) : ℝ) := by
      push_cast
      linarith [h1.1, h2.2]
    exact_mod_cast h4

/-- If `g` is continuous and vanishes outside `[a, b]`, then `y ↦ g_{j,l}(y) conj g_{j,k}(y)` is
integrable: it is continuous with compact support. -/
theorem integrable_scaledFun_mul_conj (hg : Continuous g) (hsupp : ∀ x ∉ Set.Icc a b, g x = 0)
    (j : ℕ) (k l : ℤ) : Integrable fun y => scaledFun g j l y * conj (scaledFun g j k y) :=
  ((continuous_scaledFun hg j l).mul
    (Complex.continuous_conj.comp (continuous_scaledFun hg j k))).integrable_of_hasCompactSupport
    (hasCompactSupport_scaledFun hsupp j l).mul_right

/-- **Coefficient recovery**: let `g` be continuous, vanish outside `[a, b]`, and have
orthonormal integer translates. Then for every level `j`, every coefficient sequence
`c : ℤ → ℂ` and every `k ∈ ℤ`, `⟨∑_l c_l g_{j,l}, g_{j,k}⟩ = c_k`. Only the positions `l` with
`|l - k| ≤ ⌈b - a⌉` contribute to the integrand (`Daubechies.scaledFun_mul_conj_eq_zero`), so it
is a finite sum, and orthonormality at level `j` (`Daubechies.integral_scaledFun_mul_conj`) leaves
the term `l = k`. The sequence `c` is arbitrary: at each point the sum over `l` is finite. -/
theorem coeffFun_expand (hg : Continuous g) (hsupp : ∀ x ∉ Set.Icc a b, g x = 0)
    (horth : ∀ k l : ℤ, ∫ x, g (x - k) * conj (g (x - l)) = if k = l then 1 else 0)
    (j : ℕ) (c : ℤ → ℂ) (k : ℤ) : coeffFun g j (expand g j c) k = c k := by
  have h : ∀ y, expand g j c y * conj (scaledFun g j k y) =
      ∑ l ∈ Finset.Icc (k - ⌈b - a⌉₊) (k + ⌈b - a⌉₊),
        c l * (scaledFun g j l y * conj (scaledFun g j k y)) := fun y => by
    rw [expand, ← tsum_mul_right]
    refine (tsum_eq_sum fun l hl => ?_).trans (Finset.sum_congr rfl fun l _ => mul_assoc _ _ _)
    rw [mul_assoc, scaledFun_mul_conj_eq_zero hsupp hl, mul_zero]
  rw [coeffFun]
  simp_rw [h]
  rw [integral_finsetSum _ fun l _ => (integrable_scaledFun_mul_conj hg hsupp j k l).const_mul _]
  simp_rw [integral_const_mul, integral_scaledFun_mul_conj horth, mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq_of_mem' _ _ _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩)

/-! ### Measurability and `L_p` norms of the generators -/

/-- For every a.e. strongly measurable `F : ℝ → ℂ`, `j ∈ ℕ` and `t ∈ ℝ`, the translate
`u ↦ F(u - t)` is a.e. strongly measurable for the image of Lebesgue measure under `x ↦ 2^j x`.
That image is `2^(-j)` times Lebesgue measure (Mathlib's `Real.map_volume_mul_left`), and
translations preserve Lebesgue measure. -/
theorem aestronglyMeasurable_comp_sub_map {F : ℝ → ℂ} (hF : AEStronglyMeasurable F volume)
    (j : ℕ) (t : ℝ) :
    AEStronglyMeasurable (fun u => F (u - t)) (Measure.map (fun x => (2 : ℝ) ^ j * x) volume) := by
  rw [Real.map_volume_mul_left (pow_ne_zero j two_ne_zero)]
  exact (hF.comp_measurePreserving (measurePreserving_sub_right volume t)).smul_measure _

/-- **Dilation and translation preserve measurability**: for every a.e. strongly measurable
`F : ℝ → ℂ`, `j ∈ ℕ` and `t ∈ ℝ`, the function `x ↦ F(2^j x - t)` is a.e. strongly measurable
(`Daubechies.aestronglyMeasurable_comp_sub_map`). -/
theorem aestronglyMeasurable_comp_two_pow_mul_sub {F : ℝ → ℂ}
    (hF : AEStronglyMeasurable F volume) (j : ℕ) (t : ℝ) :
    AEStronglyMeasurable (fun x => F (2 ^ j * x - t)) volume :=
  (aestronglyMeasurable_comp_sub_map hF j t).comp_aemeasurable
    (measurable_const_mul _).aemeasurable

/-- The generators `g_{j,k}` of an a.e. strongly measurable `g` are a.e. strongly measurable
(`Daubechies.aestronglyMeasurable_comp_two_pow_mul_sub`). -/
theorem aestronglyMeasurable_scaledFun (hg : AEStronglyMeasurable g volume) (j : ℕ) (k : ℤ) :
    AEStronglyMeasurable (scaledFun g j k) volume :=
  (aestronglyMeasurable_comp_two_pow_mul_sub hg j k).const_mul _

/-- **Expansions are a.e. strongly measurable** for every a.e. strongly measurable `g` and all
coefficients `c`: a countable sum of a.e. strongly measurable functions (Mathlib's
`MeasureTheory.AEStronglyMeasurable.tsum`). -/
theorem aestronglyMeasurable_expand (hg : AEStronglyMeasurable g volume) (j : ℕ) (c : ℤ → ℂ) :
    AEStronglyMeasurable (expand g j c) volume :=
  AEStronglyMeasurable.tsum fun k => (aestronglyMeasurable_scaledFun hg j k).const_mul (c k)

/-- **Dilation and translation in `L_p`**: for every a.e. strongly measurable `F : ℝ → ℂ`, every
`j ∈ ℕ`, `t ∈ ℝ` and every exponent `p`, `‖F(2^j · - t)‖_p = 2^(-j/p) ‖F‖_p`. The image of
Lebesgue measure under `x ↦ 2^j x` is `2^(-j)` times Lebesgue measure (Mathlib's
`Real.map_volume_mul_left`), and translations preserve Lebesgue measure. For `p = ∞` the factor
is `1`, since then `1/p.toReal = 0` in Lean. -/
theorem eLpNorm_comp_two_pow_mul_sub {F : ℝ → ℂ} (hF : AEStronglyMeasurable F volume) (j : ℕ)
    (t : ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x => F (2 ^ j * x - t)) p volume =
      dyadicWeight (-(1 / p.toReal)) j * eLpNorm F p volume := by
  have hc : ENNReal.ofReal |((2 : ℝ) ^ j)⁻¹| ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  rw [show (fun x => F (2 ^ j * x - t)) = (fun u => F (u - t)) ∘ fun x => (2 : ℝ) ^ j * x from rfl,
    ← eLpNorm_map_measure (aestronglyMeasurable_comp_sub_map hF j t)
      (measurable_const_mul _).aemeasurable,
    Real.map_volume_mul_left (pow_ne_zero j two_ne_zero),
    eLpNorm_smul_measure_of_ne_zero hc, smul_eq_mul,
    show (fun u => F (u - t)) = F ∘ (fun u => u - t) from rfl,
    eLpNorm_comp_measurePreserving hF (measurePreserving_sub_right volume t)]
  congr 1
  rw [dyadicWeight, mul_neg, ENNReal.rpow_neg, ENNReal.rpow_mul, ENNReal.rpow_natCast,
    ← ENNReal.inv_rpow, abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ENNReal.toReal_div, ENNReal.toReal_one]

/-- **`L_p` norms of the generators**: for every a.e. strongly measurable `g`, every level `j`,
position `k` and exponent `p`, `‖g_{j,k}‖_p = 2^(j(1/2 - 1/p)) ‖g‖_p`
(`Daubechies.eLpNorm_comp_two_pow_mul_sub` and the factor `2^(j/2)`,
`enorm_two_rpow_half`). In particular
`‖g_{j,k}‖_2 = ‖g‖_2`. -/
theorem eLpNorm_scaledFun (hg : AEStronglyMeasurable g volume) (j : ℕ) (k : ℤ) (p : ℝ≥0∞) :
    eLpNorm (scaledFun g j k) p volume =
      dyadicWeight (1 / 2 - 1 / p.toReal) j * eLpNorm g p volume := by
  have h : scaledFun g j k = (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) • fun x => g (2 ^ j * x - k) :=
    rfl
  rw [h, eLpNorm_const_smul, eLpNorm_comp_two_pow_mul_sub hg, ← mul_assoc, sub_eq_add_neg,
    ENNReal.dyadicWeight_add]
  congr 2
  exact enorm_two_rpow_half j

/-- **`L_p` norm of a multiple of a generator**: `‖z g_{j,k}‖_p = |z| 2^(j(1/2 - 1/p)) ‖g‖_p` for
every `z ∈ ℂ` (`Daubechies.eLpNorm_scaledFun`). -/
theorem eLpNorm_const_mul_scaledFun (hg : AEStronglyMeasurable g volume) (z : ℂ) (j : ℕ)
    (k : ℤ) (p : ℝ≥0∞) :
    eLpNorm (fun x => z * scaledFun g j k x) p volume =
      ‖z‖ₑ * (dyadicWeight (1 / 2 - 1 / p.toReal) j * eLpNorm g p volume) := by
  rw [show (fun x => z * scaledFun g j k x) = z • scaledFun g j k from rfl, eLpNorm_const_smul,
    eLpNorm_scaledFun hg]

/-- A continuous `g` vanishing outside `[a, b]` lies in every `L_p`: it has compact support
(Mathlib's `Continuous.memLp_of_hasCompactSupport`). -/
theorem memLp_of_continuous_of_eq_zero (hg : Continuous g) (hsupp : ∀ x ∉ Set.Icc a b, g x = 0)
    (p : ℝ≥0∞) : MemLp g p volume :=
  hg.memLp_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hsupp)

/-! ### Upper stability of the expansions -/

/-- **Upper stability of the expansions**: let `g` be a.e. strongly measurable and vanish outside
`[a, b]`, and let `1 ≤ p < ∞`. Then for every level `j` and all coefficients `c : ℤ → ℂ`,
`‖∑_k c_k g_{j,k}‖_p ≤ M^(1 - 1/p) ‖g‖_p 2^(j(1/2 - 1/p)) ‖c‖_{ℓ_p}` with the overlap number
`M = ⌈b - a⌉ + 1`. The constant `M^(1 - 1/p) ‖g‖_p` (`Daubechies.expandConst`) is proportional to
`‖g‖_p`, depends on the support only through `b - a`, and is the same for every level `j` and
every `c`. At each point at most `M` terms are nonzero
(`Daubechies.card_le_of_forall_mem_supportWindow`), so
the bounded overlap inequality `‖∑_k F_k‖_p^p ≤ M^(p-1) ∑_k ‖F_k‖_p^p`
(`Rd.eLpNorm_rpow_le_of_overlap`) applies, and
`‖c_k g_{j,k}‖_p = |c_k| 2^(j(1/2 - 1/p)) ‖g‖_p` (`Daubechies.eLpNorm_const_mul_scaledFun`). -/
theorem eLpNorm_expand_le (hg : AEStronglyMeasurable g volume)
    (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (j : ℕ)
    (c : ℤ → ℂ) :
    eLpNorm (expand g j c) p volume ≤
      ((⌈b - a⌉₊ + 1 : ℕ) : ℝ≥0∞) ^ (1 - 1 / p.toReal) * eLpNorm g p volume *
        dyadicWeight (1 / 2 - 1 / p.toReal) j * ENNReal.lqNorm p (fun k => ‖c k‖ₑ) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have h := Rd.eLpNorm_rpow_le_of_overlap (μ := volume) hp1 hp
    (g := fun k x => c k * scaledFun g j k x)
    (fun k => (aestronglyMeasurable_scaledFun hg j k).const_mul (c k)) (N := ⌈b - a⌉₊ + 1)
    (fun x S hS => card_le_of_forall_mem_supportWindow x S fun k hk =>
      mem_supportWindow_of_scaledFun_ne_zero hsupp (right_ne_zero_of_mul (hS k hk)))
    (aestronglyMeasurable_expand hg j c) (Eventually.of_forall fun x => rfl)
  simp_rw [eLpNorm_const_mul_scaledFun hg] at h
  rw [← ENNReal.rpow_le_rpow_iff hr]
  refine h.trans (le_of_eq ?_)
  have he : (1 - 1 / p.toReal) * p.toReal = p.toReal - 1 := by field_simp
  simp only [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul, he]
  rw [ENNReal.tsum_mul_right, ← ENNReal.lqNorm_rpow hp0 hp (fun k => ‖c k‖ₑ)]
  ring

/-- **The constant of the upper estimate** `Daubechies.eLpNorm_expand_le`:
`M^(1 - 1/p) ‖g‖_p` with the overlap number `M = ⌈b - a⌉ + 1`, which bounds the number of
generators of one level that are nonzero at a point. It is the same for every level. -/
noncomputable def expandConst (g : ℝ → ℂ) (a b : ℝ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  ((⌈b - a⌉₊ + 1 : ℕ) : ℝ≥0∞) ^ (1 - 1 / p.toReal) * eLpNorm g p volume

/-- The constant `expandConst g a b p` is finite for every `g ∈ L_p`. -/
theorem expandConst_ne_top (a b : ℝ) {p : ℝ≥0∞} (hg : MemLp g p volume) :
    expandConst g a b p ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero (by simp) (ENNReal.natCast_ne_top _))
    hg.eLpNorm_ne_top

/-- **Expansions with `ℓ_p` coefficients lie in `L_p`**: if `g ∈ L_p` vanishes outside `[a, b]`,
`1 ≤ p < ∞` and `‖c‖_{ℓ_p} < ∞`, then `∑_k c_k g_{j,k} ∈ L_p` for every level `j`, since its norm
is finite by the upper estimate (`Daubechies.eLpNorm_expand_le`). -/
theorem memLp_expand {p : ℝ≥0∞} (hg : MemLp g p volume) (hsupp : ∀ x ∉ Set.Icc a b, g x = 0)
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) (j : ℕ) {c : ℤ → ℂ}
    (hc : ENNReal.lqNorm p (fun k => ‖c k‖ₑ) < ∞) : MemLp (expand g j c) p volume :=
  memLp_iff.2 ((eLpNorm_expand_le hg.aestronglyMeasurable hsupp hp1 hp j c).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (expandConst_ne_top a b hg).lt_top
      (ENNReal.dyadicWeight_lt_top _ _)) hc))

/-! ### The coefficient estimate -/

/-- **The conjugate exponent**: for `1 ≤ p ≤ ∞` and `p' = p/(p - 1)` (Mathlib's
`ENNReal.conjExponent`), the real exponents satisfy `1/p' = 1 - 1/p`, from `1/p + 1/p' = 1`; for
`p = 1` this reads `1/∞ = 0`, the value Lean assigns. -/
theorem one_div_toReal_conjExponent {p : ℝ≥0∞} (hp1 : 1 ≤ p) :
    1 / (ENNReal.conjExponent p).toReal = 1 - 1 / p.toReal := by
  have := ENNReal.HolderConjugate.conjExponent hp1
  have h := ENNReal.HolderConjugate.inv_add_inv_eq_one p (ENNReal.conjExponent p)
  have hp' : p⁻¹ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_self_add.trans_eq h)
  have hq' : (ENNReal.conjExponent p)⁻¹ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq h)
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add hp' hq', ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_one] at h2
  rw [one_div, one_div]
  linarith

/-- **`L_{p'}` norms of the generators**: for `1 ≤ p` and the conjugate exponent `p'`,
`‖g_{j,k}‖_{p'} = 2^(-j(1/2 - 1/p)) ‖g‖_{p'}`, since `1/2 - 1/p' = -(1/2 - 1/p)`
(`Daubechies.eLpNorm_scaledFun`, `Daubechies.one_div_toReal_conjExponent`). -/
theorem eLpNorm_scaledFun_conjExponent (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (j : ℕ) (k : ℤ) :
    eLpNorm (scaledFun g j k) (ENNReal.conjExponent p) volume =
      dyadicWeight (-(1 / 2 - 1 / p.toReal)) j * eLpNorm g (ENNReal.conjExponent p) volume := by
  rw [eLpNorm_scaledFun hg, one_div_toReal_conjExponent hp1]
  congr 2
  ring

/-- **Hölder's inequality on a support window**: let `g` be a.e. strongly measurable and vanish
outside `[a, b]`, let `1 ≤ p`, and let `f` be a.e. strongly measurable. Then
`‖f conj g_{j,k}‖_1 ≤ ‖1_W f‖_p ‖g_{j,k}‖_{p'}` with the support window
`W = {x : 2^j x - k ∈ [a, b]}` and the conjugate exponent `p'`. Outside `W` the factor `g_{j,k}`
vanishes, so `f` may be replaced by `1_W f`; then Hölder's inequality (Mathlib's
`MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm`) applies. -/
theorem eLpNorm_mul_conj_scaledFun_le (hg : AEStronglyMeasurable g volume)
    (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (j : ℕ) (k : ℤ) :
    eLpNorm (fun y => f y * conj (scaledFun g j k y)) 1 volume ≤
      eLpNorm ((supportWindow a b j k).indicator f) p volume *
        eLpNorm (scaledFun g j k) (ENNReal.conjExponent p) volume := by
  have := ENNReal.HolderConjugate.conjExponent hp1
  have heq : (fun y => f y * conj (scaledFun g j k y)) =
      fun y => (supportWindow a b j k).indicator f y * conj (scaledFun g j k y) := by
    funext y
    by_cases hy : y ∈ supportWindow a b j k
    · rw [Set.indicator_of_mem hy]
    · rw [scaledFun_eq_zero hsupp hy, map_zero, mul_zero, mul_zero]
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm (μ := volume) (p := p)
    (q := ENNReal.conjExponent p) (r := 1) (fun u v : ℂ => u * conj v) 1
    (continuous_fst.mul (Complex.continuous_conj.comp continuous_snd))
    (hf.indicator (measurableSet_supportWindow a b j k)) (aestronglyMeasurable_scaledFun hg j k)
    (Eventually.of_forall fun y => by simp)
  rw [ENNReal.coe_one, one_mul] at h
  rw [heq]
  exact h

/-- **A single coefficient**: under the hypotheses of `Daubechies.eLpNorm_mul_conj_scaledFun_le`,
`|⟨f, g_{j,k}⟩| ≤ ‖1_W f‖_p ‖g_{j,k}‖_{p'}` with the support window
`W = {x : 2^j x - k ∈ [a, b]}`, since `|∫ h| ≤ ‖h‖_1`. -/
theorem enorm_coeffFun_le (hg : AEStronglyMeasurable g volume)
    (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (j : ℕ) (k : ℤ) :
    ‖coeffFun g j f k‖ₑ ≤ eLpNorm ((supportWindow a b j k).indicator f) p volume *
      eLpNorm (scaledFun g j k) (ENNReal.conjExponent p) volume := by
  have hm : AEStronglyMeasurable (fun y => f y * conj (scaledFun g j k y)) volume :=
    hf.mul (Complex.continuous_conj.comp_aestronglyMeasurable
      (aestronglyMeasurable_scaledFun hg j k))
  refine (eNorm_integral_le_lintegral_eNorm _).trans
    (le_of_eq_of_le ?_ (eLpNorm_mul_conj_scaledFun_le hg hsupp hp1 hf j k))
  rw [eLpNorm_one_eq_lintegral_eNorm hm]

/-- **Summing local bounds over the support windows**: let `1 ≤ p < ∞`, let `f` be a.e. strongly
measurable, and let `d : ℤ → [0, ∞]` satisfy `d_k ≤ ‖1_{W_k} f‖_p B` for every `k`, where
`W_k = {x : 2^j x - k ∈ [a, b]}` are the support windows of level `j`. Then
`‖d‖_{ℓ_p} ≤ M^(1/p) B ‖f‖_p` with the overlap number `M = ⌈b - a⌉ + 1`: the `p`-th powers satisfy
`∑_k d_k^p ≤ B^p ∑_k ∫_{W_k} |f|^p ≤ M B^p ‖f‖_p^p` by the window inequality
(`MeasureTheory.tsum_setLIntegral_le_mul_lintegral`, with the overlap bound
`Daubechies.card_le_of_forall_mem_supportWindow`). -/
theorem lqNorm_le_of_le_eLpNorm_indicator {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (j : ℕ) {d : ℤ → ℝ≥0∞} {B : ℝ≥0∞}
    (hd : ∀ k, d k ≤ eLpNorm ((supportWindow a b j k).indicator f) p volume * B) :
    ENNReal.lqNorm p d ≤
      ((⌈b - a⌉₊ + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) * B * eLpNorm f p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hk : ∀ k, d k ^ p.toReal ≤
      B ^ p.toReal * ∫⁻ x in supportWindow a b j k, ‖f x‖ₑ ^ p.toReal := fun k => by
    calc d k ^ p.toReal
        ≤ (eLpNorm ((supportWindow a b j k).indicator f) p volume * B) ^ p.toReal :=
          ENNReal.rpow_le_rpow (hd k) hr.le
      _ = B ^ p.toReal * ∫⁻ x in supportWindow a b j k, ‖f x‖ₑ ^ p.toReal := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, mul_comm,
            eLpNorm_indicator_eq_eLpNorm_restrict
              (measurableSet_supportWindow a b j k).nullMeasurableSet,
            eLpNorm_rpow_eq hf.restrict hp0 hp]
  have hsum : ∑' k, d k ^ p.toReal ≤
      B ^ p.toReal * (((⌈b - a⌉₊ + 1 : ℕ) : ℝ≥0∞) * eLpNorm f p volume ^ p.toReal) := by
    calc ∑' k, d k ^ p.toReal
        ≤ ∑' k, B ^ p.toReal * ∫⁻ x in supportWindow a b j k, ‖f x‖ₑ ^ p.toReal :=
          tsum_le_tsum hk
      _ = B ^ p.toReal * ∑' k, ∫⁻ x in supportWindow a b j k, ‖f x‖ₑ ^ p.toReal :=
          ENNReal.tsum_mul_left
      _ ≤ B ^ p.toReal * (((⌈b - a⌉₊ + 1 : ℕ) : ℝ≥0∞) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal) := by
          gcongr
          exact tsum_setLIntegral_le_mul_lintegral (measurableSet_supportWindow a b j)
            (fun x S hS => card_le_of_forall_mem_supportWindow x S hS) (hf.eNorm.pow_const _)
      _ = B ^ p.toReal * (((⌈b - a⌉₊ + 1 : ℕ) : ℝ≥0∞) * eLpNorm f p volume ^ p.toReal) := by
          rw [eLpNorm_rpow_eq hf hp0 hp]
  rw [← ENNReal.rpow_le_rpow_iff hr, ENNReal.lqNorm_rpow hp0 hp]
  refine hsum.trans (le_of_eq ?_)
  simp only [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hr.ne', ENNReal.rpow_one]
  ring

/-- **The coefficient estimate**: let `g` be a.e. strongly measurable and vanish outside
`[a, b]`, and let `1 ≤ p < ∞`. Then for every a.e. strongly measurable `f` and every level `j`,
`‖(⟨f, g_{j,k}⟩)_k‖_{ℓ_p} ≤ M^(1/p) ‖g‖_{p'} 2^(-j(1/2 - 1/p)) ‖f‖_p` with the overlap number
`M = ⌈b - a⌉ + 1` and the conjugate exponent `p'`. The constant `M^(1/p) ‖g‖_{p'}`
(`Daubechies.coeffConst`) is the same for every `j` and `f`. Each coefficient is bounded by
Hölder's inequality on its support window, `|⟨f, g_{j,k}⟩| ≤ ‖1_{W_k} f‖_p ‖g_{j,k}‖_{p'}`
(`Daubechies.enorm_coeffFun_le`) with `‖g_{j,k}‖_{p'} = 2^(-j(1/2 - 1/p)) ‖g‖_{p'}`
(`Daubechies.eLpNorm_scaledFun_conjExponent`), and the windows overlap at most `M` times
(`Daubechies.lqNorm_le_of_le_eLpNorm_indicator`). -/
theorem lqNorm_coeffFun_le (hg : AEStronglyMeasurable g volume)
    (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (j : ℕ) :
    ENNReal.lqNorm p (fun k => ‖coeffFun g j f k‖ₑ) ≤
      ((⌈b - a⌉₊ + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) * eLpNorm g (ENNReal.conjExponent p) volume *
        dyadicWeight (-(1 / 2 - 1 / p.toReal)) j * eLpNorm f p volume := by
  have h := lqNorm_le_of_le_eLpNorm_indicator (a := a) (b := b) hp1 hp hf j
    (d := fun k => ‖coeffFun g j f k‖ₑ)
    (B := dyadicWeight (-(1 / 2 - 1 / p.toReal)) j * eLpNorm g (ENNReal.conjExponent p) volume)
    fun k => by
      rw [← eLpNorm_scaledFun_conjExponent hg hp1 j k]
      exact enorm_coeffFun_le hg hsupp hp1 hf j k
  refine h.trans (le_of_eq ?_)
  ring

/-- **The constant of the coefficient estimate** `Daubechies.lqNorm_coeffFun_le`:
`M^(1/p) ‖g‖_{p'}` with the overlap number `M = ⌈b - a⌉ + 1` and the conjugate exponent
`p' = p/(p - 1)` (Mathlib's `ENNReal.conjExponent`). It is the same for every level. -/
noncomputable def coeffConst (g : ℝ → ℂ) (a b : ℝ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  ((⌈b - a⌉₊ + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) * eLpNorm g (ENNReal.conjExponent p) volume

/-- The constant `coeffConst g a b p` is finite for every `g ∈ L_{p'}`, `p'` the conjugate
exponent. -/
theorem coeffConst_ne_top (a b : ℝ) {p : ℝ≥0∞} (hg : MemLp g (ENNReal.conjExponent p) volume) :
    coeffConst g a b p ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero (by simp) (ENNReal.natCast_ne_top _))
    hg.eLpNorm_ne_top

/-- **The coefficient estimate, weighted form**:
`2^(j(1/2 - 1/p)) ‖(⟨f, g_{j,k}⟩)_k‖_{ℓ_p} ≤ C' ‖f‖_p` with `C' = coeffConst g a b p`, under the
hypotheses of `Daubechies.lqNorm_coeffFun_le`, since `2^(j(1/2 - 1/p)) 2^(-j(1/2 - 1/p)) = 1`. -/
theorem dyadicWeight_mul_lqNorm_coeffFun_le (hg : AEStronglyMeasurable g volume)
    (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (j : ℕ) :
    dyadicWeight (1 / 2 - 1 / p.toReal) j * ENNReal.lqNorm p (fun k => ‖coeffFun g j f k‖ₑ) ≤
      coeffConst g a b p * eLpNorm f p volume := by
  calc dyadicWeight (1 / 2 - 1 / p.toReal) j * ENNReal.lqNorm p (fun k => ‖coeffFun g j f k‖ₑ)
      ≤ dyadicWeight (1 / 2 - 1 / p.toReal) j * (coeffConst g a b p *
          dyadicWeight (-(1 / 2 - 1 / p.toReal)) j * eLpNorm f p volume) :=
        mul_le_mul_right (lqNorm_coeffFun_le hg hsupp hp1 hp hf j) _
    _ = coeffConst g a b p * eLpNorm f p volume * (dyadicWeight (1 / 2 - 1 / p.toReal) j *
          dyadicWeight (-(1 / 2 - 1 / p.toReal)) j) := by ring
    _ = coeffConst g a b p * eLpNorm f p volume := by
        rw [ENNReal.dyadicWeight_mul_neg_self, mul_one]

/-- **Lower stability of the expansions**: let `g` be continuous, vanish outside `[a, b]`, and
have orthonormal integer translates, and let `1 ≤ p < ∞`. Then for every level `j` and all
coefficients `c : ℤ → ℂ`, `2^(j(1/2 - 1/p)) ‖c‖_{ℓ_p} ≤ C' ‖∑_k c_k g_{j,k}‖_p` with the constant
`C' = coeffConst g a b p`. The coefficients are recovered from the expansion,
`c_k = ⟨∑_l c_l g_{j,l}, g_{j,k}⟩` (`Daubechies.coeffFun_expand`), and the coefficient estimate
(`Daubechies.dyadicWeight_mul_lqNorm_coeffFun_le`) applies to the continuous expansion. -/
theorem lqNorm_le_eLpNorm_expand (hg : Continuous g) (hsupp : ∀ x ∉ Set.Icc a b, g x = 0)
    (horth : ∀ k l : ℤ, ∫ x, g (x - k) * conj (g (x - l)) = if k = l then 1 else 0)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (j : ℕ) (c : ℤ → ℂ) :
    dyadicWeight (1 / 2 - 1 / p.toReal) j * ENNReal.lqNorm p (fun k => ‖c k‖ₑ) ≤
      coeffConst g a b p * eLpNorm (expand g j c) p volume := by
  have h := dyadicWeight_mul_lqNorm_coeffFun_le hg.aestronglyMeasurable hsupp hp1 hp
    (continuous_expand hg hsupp j c).aestronglyMeasurable j
  simp only [coeffFun_expand hg hsupp horth] at h
  exact h

/-! ### Expansions of the coefficients of `L_p` functions -/

/-- **`L_p` functions have `ℓ_p` coefficients**: if `g` is continuous and vanishes outside
`[a, b]`, `1 ≤ p < ∞` and `f ∈ L_p`, then `‖(⟨f, g_{j,k}⟩)_k‖_{ℓ_p} < ∞` for every level `j`
(`Daubechies.lqNorm_coeffFun_le`). -/
theorem lqNorm_coeffFun_lt_top (hg : Continuous g) (hsupp : ∀ x ∉ Set.Icc a b, g x = 0)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : ℝ → ℂ} (hf : MemLp f p volume) (j : ℕ) :
    ENNReal.lqNorm p (fun k => ‖coeffFun g j f k‖ₑ) < ∞ :=
  (lqNorm_coeffFun_le hg.aestronglyMeasurable hsupp hp1 hp hf.aestronglyMeasurable j).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (coeffConst_ne_top a b (memLp_of_continuous_of_eq_zero hg hsupp _)).lt_top
      (ENNReal.dyadicWeight_lt_top _ _)) hf.eLpNorm_lt_top)

/-- **The expansion of the coefficients is bounded on `L_p`, uniformly in the level**: if `g` is
a.e. strongly measurable and vanishes outside `[a, b]` and `1 ≤ p < ∞`, then for every a.e.
strongly measurable `f` and every level `j`, `‖∑_k ⟨f, g_{j,k}⟩ g_{j,k}‖_p ≤ C C' ‖f‖_p` with the
constants `C = expandConst g a b p` and `C' = coeffConst g a b p`: the upper estimate
(`Daubechies.eLpNorm_expand_le`) and the coefficient estimate
(`Daubechies.dyadicWeight_mul_lqNorm_coeffFun_le`), whose dyadic weights cancel. -/
theorem eLpNorm_expand_coeffFun_le (hg : AEStronglyMeasurable g volume)
    (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (j : ℕ) :
    eLpNorm (expand g j (coeffFun g j f)) p volume ≤
      expandConst g a b p * coeffConst g a b p * eLpNorm f p volume := by
  calc eLpNorm (expand g j (coeffFun g j f)) p volume
      ≤ expandConst g a b p * (dyadicWeight (1 / 2 - 1 / p.toReal) j *
          ENNReal.lqNorm p (fun k => ‖coeffFun g j f k‖ₑ)) :=
        (eLpNorm_expand_le hg hsupp hp1 hp j _).trans_eq (by rw [expandConst, mul_assoc])
    _ ≤ expandConst g a b p * (coeffConst g a b p * eLpNorm f p volume) :=
        mul_le_mul_right (dyadicWeight_mul_lqNorm_coeffFun_le hg hsupp hp1 hp hf j) _
    _ = expandConst g a b p * coeffConst g a b p * eLpNorm f p volume := (mul_assoc _ _ _).symm

/-- **The expansion of the coefficients of an `L_p` function lies in `L_p`**: if `g` is
continuous and vanishes outside `[a, b]`, `1 ≤ p < ∞` and `f ∈ L_p`, then
`∑_k ⟨f, g_{j,k}⟩ g_{j,k} ∈ L_p` for every level `j` (`Daubechies.eLpNorm_expand_coeffFun_le`). -/
theorem memLp_expand_coeffFun (hg : Continuous g) (hsupp : ∀ x ∉ Set.Icc a b, g x = 0)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : ℝ → ℂ} (hf : MemLp f p volume) (j : ℕ) :
    MemLp (expand g j (coeffFun g j f)) p volume :=
  memLp_iff.2 ((eLpNorm_expand_coeffFun_le hg.aestronglyMeasurable hsupp hp1 hp
    hf.aestronglyMeasurable j).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (expandConst_ne_top a b (memLp_of_continuous_of_eq_zero hg hsupp p)).lt_top
      (coeffConst_ne_top a b (memLp_of_continuous_of_eq_zero hg hsupp _)).lt_top)
      hf.eLpNorm_lt_top))

/-! ### Linearity -/

/-- **Expansions are additive in the coefficients**: if `g` vanishes outside `[a, b]`, then
`∑_k (c_k + d_k) g_{j,k}(x) = ∑_k c_k g_{j,k}(x) + ∑_k d_k g_{j,k}(x)` at every point `x`; both
sums are finite (`Daubechies.summable_expand`). -/
theorem expand_add (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) (j : ℕ) (c d : ℤ → ℂ) (x : ℝ) :
    expand g j (fun k => c k + d k) x = expand g j c x + expand g j d x := by
  simp only [expand, add_mul]
  exact (summable_expand hsupp j c x).tsum_add (summable_expand hsupp j d x)

/-- **Expansions are homogeneous in the coefficients**:
`∑_k (z c_k) g_{j,k}(x) = z ∑_k c_k g_{j,k}(x)` for every `z ∈ ℂ` and every point `x`. -/
theorem expand_const_mul (j : ℕ) (z : ℂ) (c : ℤ → ℂ) (x : ℝ) :
    expand g j (fun k => z * c k) x = z * expand g j c x := by
  simp only [expand, mul_assoc]
  exact tsum_mul_left

/-- **The coefficients depend only on the class of `f` almost everywhere**: if `f = f'` almost
everywhere, then `⟨f, g_{j,k}⟩ = ⟨f', g_{j,k}⟩` (Mathlib's `MeasureTheory.integral_congr_ae`). -/
theorem coeffFun_congr_ae {f f' : ℝ → ℂ} (h : f =ᵐ[volume] f') (j : ℕ) (k : ℤ) :
    coeffFun g j f k = coeffFun g j f' k :=
  integral_congr_ae (h.mono fun y hy => by simp only [hy])

/-- **The integrands of the coefficients of `L_p` functions are integrable**: if `g` is continuous
and vanishes outside `[a, b]`, `1 ≤ p` and `f ∈ L_p`, then `f conj g_{j,k}` is integrable, by
Hölder's inequality with `conj g_{j,k} ∈ L_{p'}` (Mathlib's `MeasureTheory.MemLp.integrable_mul`).
-/
theorem integrable_mul_conj_scaledFun (hg : Continuous g) (hsupp : ∀ x ∉ Set.Icc a b, g x = 0)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) {f : ℝ → ℂ} (hf : MemLp f p volume) (j : ℕ) (k : ℤ) :
    Integrable fun y => f y * conj (scaledFun g j k y) := by
  have := ENNReal.HolderConjugate.conjExponent hp1
  exact hf.integrable_mul (q := ENNReal.conjExponent p)
    ((Complex.continuous_conj.comp (continuous_scaledFun hg j k)).memLp_of_hasCompactSupport
      ((hasCompactSupport_scaledFun hsupp j k).comp_left (map_zero _)))

/-- **The coefficients are additive in `f`**: `⟨f + f', g_{j,k}⟩ = ⟨f, g_{j,k}⟩ + ⟨f', g_{j,k}⟩`
when both integrands are integrable (for instance for `f, f' ∈ L_p`,
`Daubechies.integrable_mul_conj_scaledFun`). -/
theorem coeffFun_add {f f' : ℝ → ℂ} {j : ℕ} {k : ℤ}
    (hf : Integrable fun y => f y * conj (scaledFun g j k y))
    (hf' : Integrable fun y => f' y * conj (scaledFun g j k y)) :
    coeffFun g j (fun y => f y + f' y) k = coeffFun g j f k + coeffFun g j f' k := by
  simp only [coeffFun, add_mul]
  exact integral_add hf hf'

/-- **The coefficients are homogeneous in `f`**: `⟨z f, g_{j,k}⟩ = z ⟨f, g_{j,k}⟩` for every
`z ∈ ℂ` (Mathlib's `MeasureTheory.integral_const_mul`). -/
theorem coeffFun_const_mul (z : ℂ) (f : ℝ → ℂ) (j : ℕ) (k : ℤ) :
    coeffFun g j (fun y => z * f y) k = z * coeffFun g j f k := by
  simp only [coeffFun, mul_assoc]
  exact integral_const_mul z _

end Generic

end Daubechies
