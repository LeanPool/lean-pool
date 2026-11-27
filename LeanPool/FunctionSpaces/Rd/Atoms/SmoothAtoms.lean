/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Atoms.AtomAnalysis
public import LeanPool.FunctionSpaces.Rd.Differences.ConvexDifferences
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Smooth atoms

A **smooth atom on `Ω`** of level `j` and order `K` (`Rd.IsSmoothAtom`) vanishes outside
`B(c, d 2^(-j))`, is of class `C^K` within `Ω`, and satisfies `‖D^l a‖ ≤ A 2^(jl)` within `Ω` for
`l ≤ K` (Triebel's `K`-atoms, Schneider–Vybíral, Definition 1.3, on a set). On a convex set `Ω`
with nonempty interior, smooth atoms of order `K` are regular atoms on `Ω` of order and exponent
`r` for every `1 ≤ r ≤ K` (`Rd.isRegularAtomOn_of_isSmoothAtom`), by the bound of differences
through derivatives within `Ω` (`Rd.norm_higherDiff_le_of_iteratedFDerivWithin`).

**The cell atoms are smooth atoms of every order** (`Rd.LocalMeansBump.isSmoothAtom_cellAtom`).
Derivatives fall on the kernel: for a smooth kernel `K` with compact support and a locally
integrable `g`, `D^l (K ⋆ g)(x)(v_1, …, v_l) = ((D^l K)(v_1, …, v_l) ⋆ g)(x)`
(`Rd.iteratedFDeriv_conv_apply`, from Mathlib's `HasCompactSupport.hasFDerivAt_convolution_left`).
The dual kernels are dilations, `‖D^l η_j‖ ≤ A 2^(j(n+l))` (`Rd.norm_iteratedFDeriv_dilate_le`),
with the explicit constant `A = 2 ∑_{l ≤ K} sup ‖D^l m‖` of the moment kernel `m`
(`Rd.LocalMeansBump.dualDerivConst`, `Rd.LocalMeansBump.norm_iteratedFDeriv_dual_le`), and the
cell coefficients cancel the factor `2^(jn)` as for the atoms themselves
(`Rd.enorm_inv_cellCoef_mul_conv_le`). The standard bump `Rd.LocalMeansBump.std`, the normalised
smooth bump of radius `1`, has `L_1` norm `1` (`Rd.LocalMeansBump.eLpNorm_std_one`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric Set
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Derivatives of convolutions -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The convolution of complex functions, with the multiplication of `ℂ` as a real bilinear map. -/
theorem conv_eq_convolution_mul_real (K g : V → ℂ) (μ : Measure V) :
    conv K g μ = MeasureTheory.convolution K g (ContinuousLinearMap.mul ℝ ℂ) μ := by
  funext x
  rw [conv_apply, convolution_def]
  rfl

/-- The convolution with a smooth kernel of compact support is smooth. -/
theorem contDiff_conv {K g : V → ℂ} (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K)
    (hKs : HasCompactSupport K) (hg : LocallyIntegrable g volume) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (conv K g volume) := by
  rw [conv_eq_convolution_mul_real]
  exact hKs.contDiff_convolution_left _ hK hg

/-- **Directional derivatives of a convolution**: for a `C^1` kernel `K` of compact support and a
locally integrable `g`, `D_v (K ⋆ g)(x) = ((D_v K) ⋆ g)(x)`. -/
theorem fderiv_conv_apply {K g : V → ℂ} (hK : ContDiff ℝ 1 K) (hKs : HasCompactSupport K)
    (hg : LocallyIntegrable g volume) (x v : V) :
    fderiv ℝ (conv K g volume) x v = conv (fun y => fderiv ℝ K y v) g volume x := by
  rw [conv_eq_convolution_mul_real, (hKs.hasFDerivAt_convolution_left _ hK hg x).fderiv,
    conv_eq_convolution_mul_real, convolution_def, convolution_def,
    ContinuousLinearMap.integral_apply ((hKs.fderiv ℝ).convolutionExists_left
      ((ContinuousLinearMap.mul ℝ ℂ).precompL V) (hK.continuous_fderiv one_ne_zero) hg x)]
  rfl

/-- **Iterated derivatives of a convolution**: for a smooth kernel `K` of compact support and a
locally integrable `g`, `D^n (K ⋆ g)(x)(v) = ((D^n K)(·)(v) ⋆ g)(x)`. -/
theorem iteratedFDeriv_conv_apply {K g : V → ℂ} (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K)
    (hKs : HasCompactSupport K) (hg : LocallyIntegrable g volume) (n : ℕ) (x : V)
    (v : Fin n → V) :
    iteratedFDeriv ℝ n (conv K g volume) x v =
      conv (fun y => iteratedFDeriv ℝ n K y v) g volume x := by
  induction n generalizing x with
  | zero => simp [iteratedFDeriv_zero_apply, conv_apply]
  | succ n ih =>
    have hF := contDiff_conv hK hKs hg
    rw [DifferentiableAt.iteratedFDeriv_succ_apply_left'
      ((hF.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) x)]
    have hfun : (fun y => iteratedFDeriv ℝ n (conv K g volume) y (Fin.tail v)) =
        conv (fun z => iteratedFDeriv ℝ n K z (Fin.tail v)) g volume :=
      funext fun y => ih y (Fin.tail v)
    have hKn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z => iteratedFDeriv ℝ n K z (Fin.tail v) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => V) ℂ (Fin.tail v)).contDiff.comp
        (hK.iteratedFDeriv_right (by simp))
    have hKns : HasCompactSupport fun z => iteratedFDeriv ℝ n K z (Fin.tail v) :=
      HasCompactSupport.comp_left
        (g := fun M : ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ => M (Fin.tail v))
        (hKs.iteratedFDeriv n) (zero_apply _)
    rw [hfun, fderiv_conv_apply (hKn.of_le (by exact_mod_cast le_top)) hKns hg]
    congr 1
    funext y
    rw [DifferentiableAt.iteratedFDeriv_succ_apply_left'
      ((hK.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) y)]

/-- **Bounds for the derivatives of a convolution**: if `‖D^n K‖ ≤ M` and `K = 0` outside
`closedBall(0, ρ)`, the derivative of order `n` of `c (K ⋆ g)` is bounded through the
convolutions with the
directional derivatives `(D^n K)(·)(v)`, which satisfy `|(D^n K)(·)(v)| ≤ M ∏ ‖v_i‖`. -/
theorem norm_iteratedFDeriv_const_mul_conv_le {K g : V → ℂ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K) (hKs : HasCompactSupport K)
    (hg : LocallyIntegrable g volume) (c : ℂ) (n : ℕ) (x : V) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ v : Fin n → V, ‖c * conv (fun y => iteratedFDeriv ℝ n K y v) g volume x‖ ≤
      B * ∏ i, ‖v i‖) :
    ‖iteratedFDeriv ℝ n (fun z => c * conv K g volume z) x‖ ≤ B := by
  have hF := contDiff_conv hK hKs hg
  rw [show (fun z => c * conv K g volume z) = c • conv K g volume from rfl,
    iteratedFDeriv_const_smul_apply ((hF.of_le (by exact_mod_cast le_top)).contDiffAt)]
  refine ContinuousMultilinearMap.opNorm_le_bound hB fun v => ?_
  rw [smul_apply, iteratedFDeriv_conv_apply hK hKs hg, smul_eq_mul]
  exact hbound v

/-! ### Derivatives of dilations -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Dilations of smooth functions are smooth. -/
theorem contDiff_dilate {Φ : V → ℂ} {n : WithTop ℕ∞} (hΦ : ContDiff ℝ n Φ) (c : ℝ) :
    ContDiff ℝ n (dilate c Φ) :=
  contDiff_const.mul (hΦ.comp (contDiff_const_smul c))

/-- `2^(jn)` as an extended real is the dyadic weight `2^(jn)`, since `2^(jn) = (2^j)^n`
(`ENNReal.ofReal_two_pow_pow`). -/
theorem ofReal_two_pow_mul (j n : ℕ) :
    ENNReal.ofReal (2 ^ (j * n)) = dyadicWeight n j := by
  rw [pow_mul, ENNReal.ofReal_two_pow_pow]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Derivatives of a dilation**: `‖D^l (Φ_c)(x)‖ ≤ c^(n+l) ‖D^l Φ(c x)‖` for `c ≥ 0`, since
`Φ_c = c^n Φ(c ·)`. -/
theorem norm_iteratedFDeriv_dilate_le {Φ : V → ℂ} (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    {c : ℝ} (hc : 0 ≤ c) (l : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ l (dilate c Φ) x‖ ≤
      c ^ (finrank ℝ V + l) * ‖iteratedFDeriv ℝ l Φ (c • x)‖ := by
  set L : V →L[ℝ] V := c • ContinuousLinearMap.id ℝ V
  have hL : ‖L‖ ≤ c := by
    refine (norm_smul_le c (ContinuousLinearMap.id ℝ V)).trans ?_
    rw [Real.norm_of_nonneg hc]
    exact mul_le_of_le_one_right hc ContinuousLinearMap.norm_id_le
  have hd : dilate c Φ = ((c ^ finrank ℝ V : ℝ) : ℂ) • (Φ ∘ L) := by
    funext y
    simp [dilate, L]
  rw [hd, iteratedFDeriv_const_smul_apply ((hΦ.comp L.contDiff).of_le
    (by exact_mod_cast le_top)).contDiffAt, norm_smul,
    L.iteratedFDeriv_comp_right hΦ x (by exact_mod_cast le_top)]
  calc ‖((c ^ finrank ℝ V : ℝ) : ℂ)‖ *
        ‖(iteratedFDeriv ℝ l Φ (L x)).compContinuousLinearMap fun _ => L‖
      ≤ c ^ finrank ℝ V * (‖iteratedFDeriv ℝ l Φ (L x)‖ * ∏ _i : Fin l, ‖L‖) := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left
          (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) (by positivity)
    _ ≤ c ^ finrank ℝ V * (‖iteratedFDeriv ℝ l Φ (L x)‖ * c ^ l) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        gcongr
    _ = c ^ (finrank ℝ V + l) * ‖iteratedFDeriv ℝ l Φ (c • x)‖ := by
        simp only [L, smul_apply, ContinuousLinearMap.id_apply]
        ring

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- The dilated moment kernels are smooth. -/
theorem contDiff_scaled (L j : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b.scaled L j) := by
  rw [scaled]
  exact contDiff_dilate (b.contDiff_momentKernel L) _

/-- The dual kernels are smooth. -/
theorem contDiff_dual (L j : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b.dual L j) := by
  cases j with
  | zero => exact b.contDiff_scaled L 0
  | succ j => exact (b.contDiff_scaled L (j + 1)).add (b.contDiff_scaled L j)

/-- The constant `A = 2 ∑_{l ≤ K} sup ‖D^l m‖` of the derivatives of the dual kernels, where the
suprema of the derivatives of the moment kernel `m` are its Schwartz seminorms. -/
noncomputable def dualDerivConst (L K : ℕ) : ℝ :=
  2 * ∑ l ∈ Finset.range (K + 1), SchwartzMap.seminorm ℝ 0 l (b.momentSchwartz L)

/-- The constant of the derivatives of the dual kernels is nonnegative. -/
theorem dualDerivConst_nonneg (L K : ℕ) : 0 ≤ b.dualDerivConst L K :=
  mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)

/-- The derivatives of order `l ≤ K` of the moment kernel `m` are bounded by the sum of the
suprema `∑_{i ≤ K} sup ‖D^i m‖`, its Schwartz seminorms. -/
theorem norm_iteratedFDeriv_momentKernel_le (L K : ℕ) {l : ℕ} (hl : l ≤ K) (x : V) :
    ‖iteratedFDeriv ℝ l (momentKernel b.toFun L) x‖ ≤
      ∑ i ∈ Finset.range (K + 1), SchwartzMap.seminorm ℝ 0 i (b.momentSchwartz L) :=
  (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (b.momentSchwartz L) l x).trans
    (Finset.single_le_sum (f := fun i => SchwartzMap.seminorm ℝ 0 i (b.momentSchwartz L))
      (fun _ _ => apply_nonneg _ _) (Finset.mem_range.2 (Nat.lt_succ_of_le hl)))

/-- **Derivatives of the dual kernels**: `‖D^l η_j‖ ≤ A 2^(j(n+l))` for `l ≤ K` and every level
`j`, with the explicit constant `A = Rd.LocalMeansBump.dualDerivConst L K`. -/
theorem norm_iteratedFDeriv_dual_le (L K : ℕ) {l : ℕ} (hl : l ≤ K) (j : ℕ) (y : V) :
    ‖iteratedFDeriv ℝ l (b.dual L j) y‖ ≤
      b.dualDerivConst L K * 2 ^ (j * (finrank ℝ V + l)) := by
  set C := ∑ i ∈ Finset.range (K + 1), SchwartzMap.seminorm ℝ 0 i (b.momentSchwartz L)
  have hs : ∀ j y, ‖iteratedFDeriv ℝ l (b.scaled L j) y‖ ≤
      C * 2 ^ (j * (finrank ℝ V + l)) := fun j y => by
    refine (norm_iteratedFDeriv_dilate_le (b.contDiff_momentKernel L) (by positivity) l y).trans ?_
    rw [mul_comm C, ← pow_mul]
    exact mul_le_mul_of_nonneg_left (b.norm_iteratedFDeriv_momentKernel_le L K hl _)
      (by positivity)
  have hC : b.dualDerivConst L K = 2 * C := rfl
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (b.norm_iteratedFDeriv_momentKernel_le L K hl 0)
  rw [hC]
  cases j with
  | zero =>
    have h := hs 0 y
    simp only [zero_mul, pow_zero, mul_one] at h ⊢
    change ‖iteratedFDeriv ℝ l (b.scaled L 0) y‖ ≤ 2 * C
    linarith
  | succ j =>
    change ‖iteratedFDeriv ℝ l (b.scaled L (j + 1) + b.scaled L j) y‖ ≤ _
    rw [iteratedFDeriv_add_apply (i := l)
      (((b.contDiff_scaled L (j + 1)).of_le (by exact_mod_cast le_top)).contDiffAt)
      (((b.contDiff_scaled L j).of_le (by exact_mod_cast le_top)).contDiffAt)]
    refine (norm_add_le _ _).trans ?_
    have h1 := hs (j + 1) y
    have h2 := hs j y
    have hmono : (2 : ℝ) ^ (j * (finrank ℝ V + l)) ≤ 2 ^ ((j + 1) * (finrank ℝ V + l)) :=
      pow_le_pow_right₀ one_le_two (Nat.mul_le_mul_right _ (Nat.le_succ j))
    nlinarith

/-- **Derivatives of the dual kernels**: for every order `K` there is `A` with
`‖D^l η_j‖ ≤ A 2^(j(n+l))` for `l ≤ K` and every level `j`. -/
theorem exists_iteratedFDeriv_dual_bound (L K : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ l ≤ K, ∀ j y,
      ‖iteratedFDeriv ℝ l (b.dual L j) y‖ ≤ A * 2 ^ (j * (finrank ℝ V + l)) :=
  ⟨b.dualDerivConst L K, b.dualDerivConst_nonneg L K,
    fun _ hl j y => b.norm_iteratedFDeriv_dual_le L K hl j y⟩

end LocalMeansBump

/-! ### Smooth atoms -/

/-- A **smooth atom on `Ω`** of level `j` and order `K` with centre `c`, radius factor `d` and
constant `A`: `a = 0` outside `B(c, d 2^(-j))`, `a` is of class `C^K` within `Ω`, and
`‖D^l a‖ ≤ A 2^(jl)` within `Ω` for `l ≤ K`. -/
structure IsSmoothAtom (Ω : Set V) (K : ℕ) (d A : ℝ) (j : ℕ) (c : V) (a : V → ℂ) : Prop where
  aestronglyMeasurable : AEStronglyMeasurable a volume
  eq_zero : ∀ x, d / 2 ^ j < ‖x - c‖ → a x = 0
  contDiffOn : ContDiffOn ℝ K a Ω
  norm_iteratedFDerivWithin_le :
    ∀ l ≤ K, ∀ y ∈ Ω, ‖iteratedFDerivWithin ℝ l a Ω y‖ ≤ A * 2 ^ (j * l)

/-- **Differences of smooth atoms**: for a smooth atom on the convex set `Ω` of order `K ≥ r ≥ 1`,
`|Δ_h^r a(x)| ≤ 2^r r^(r+1) A min(1, (2^j ‖h‖)^r)` at the points whose steps stay in `Ω`. -/
theorem IsSmoothAtom.enorm_higherDiff_le {Ω : Set V} (hΩ : Convex ℝ Ω)
    (hint : (interior Ω).Nonempty) {K : ℕ} {d A : ℝ} (hA : 0 ≤ A) {j : ℕ} {c : V} {a : V → ℂ}
    (ha : IsSmoothAtom Ω K d A j c a) {r : ℕ} (hr : 1 ≤ r) (hrK : r ≤ K) {h x : V}
    (hx : x ∈ stepSet Ω r h) :
    ‖(fwdDiff h)^[r] a x‖ₑ ≤ ENNReal.ofReal (2 ^ r * (r : ℝ) ^ (r + 1) * A) *
      min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (r : ℝ)) := by
  have hK1 : (1 : ℝ) ≤ 2 ^ r * (r : ℝ) ^ (r + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two)
      (one_le_pow₀ (by exact_mod_cast hr))
  -- the bound through the derivatives
  have h1 : ‖(fwdDiff h)^[r] a x‖ ≤ 2 ^ r * (r : ℝ) ^ (r + 1) * A * (2 ^ j * ‖h‖) ^ r := by
    have hC : ∀ i ≤ r, ∀ y ∈ Ω, ‖iteratedFDerivWithin ℝ i a Ω y‖ ≤ A * 2 ^ (j * r) :=
      fun i hi y hy => (ha.norm_iteratedFDerivWithin_le i (hi.trans hrK) y hy).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_two (Nat.mul_le_mul_left j hi)) hA)
    refine (norm_higherDiff_le_of_iteratedFDerivWithin hΩ hint hr
      (ha.contDiffOn.of_le (by exact_mod_cast hrK)) hC hx).trans_eq ?_
    rw [mul_pow, pow_mul]
    ring
  -- the bound through the values
  have h2 : ‖(fwdDiff h)^[r] a x‖ₑ ≤ ENNReal.ofReal (2 ^ r * A) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
    refine enorm_higherDiff_le_of_bound_steps fun l hl => ?_
    have hy := ha.norm_iteratedFDerivWithin_le 0 (Nat.zero_le K) _ (hx l hl)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by simpa [norm_iteratedFDerivWithin_zero] using hy)
  rcases le_total 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (r : ℝ)) with hmin | hmin
  · rw [min_eq_left hmin, mul_one]
    refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    calc 2 ^ r * A = 1 * (2 ^ r * A) := (one_mul _).symm
      _ ≤ (r : ℝ) ^ (r + 1) * (2 ^ r * A) :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ (by exact_mod_cast hr)) (by positivity)
      _ = 2 ^ r * (r : ℝ) ^ (r + 1) * A := by ring
  · rw [min_eq_right hmin, ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (Nat.cast_nonneg r),
      Real.rpow_natCast, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h1

/-- **Differences of an atom vanish far from its centre**: for a smooth atom `a` with centre `c`
and radius factor `d` at level `j`, a step `h` with `‖h‖ ≤ ρ` and a point `x` with
`d 2^(-j) + r ρ < ‖x - c‖`, `Δ^r_h a(x) = 0`: every point `x + l h`, `l ≤ r`, has distance more
than `d 2^(-j)` from `c`, where `a` vanishes. -/
theorem IsSmoothAtom.higherDiff_eq_zero_of_lt {Ω : Set V} {K : ℕ} {d A : ℝ} {j : ℕ} {c : V}
    {a : V → ℂ} (ha : IsSmoothAtom Ω K d A j c a) (r : ℕ) {ρ : ℝ} {h x : V} (hh : ‖h‖ ≤ ρ)
    (hx : d / 2 ^ j + r * ρ < ‖x - c‖) :
    (fwdDiff h)^[r] a x = 0 := by
  rw [higherDiff_apply]
  refine Finset.sum_eq_zero fun l hl => ?_
  have hl' : (l : ℝ) ≤ r := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  have h2 : ‖(l : ℝ) • h‖ ≤ r * ρ := by
    rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg l)]
    exact mul_le_mul hl' hh (norm_nonneg _) (Nat.cast_nonneg r)
  have h3 : ‖x - c‖ - ‖(l : ℝ) • h‖ ≤ ‖x + (l : ℝ) • h - c‖ := by
    have hn := norm_sub_norm_le (x - c) (-((l : ℝ) • h))
    rwa [norm_neg, sub_neg_eq_add, sub_add_eq_add_sub] at hn
  rw [ha.eq_zero _ (by linarith), mul_zero]

/-- **Smooth atoms are regular atoms**: on a measurable convex set `Ω` with nonempty interior, a
smooth atom of order `K` is a regular atom on `Ω` of order and exponent `r` for `1 ≤ r ≤ K`, with
the constant `2^r r^(r+1) A ((r + 1) d^n |B_1|)^(1/p)`. -/
theorem isRegularAtomOn_of_isSmoothAtom {Ω : Set V} (hΩ : Convex ℝ Ω) (hΩm : MeasurableSet Ω)
    (hint : (interior Ω).Nonempty) {p : ℝ≥0∞} {K r : ℕ} (hr : 1 ≤ r) (hrK : r ≤ K) {d A : ℝ}
    (hd : 0 ≤ d) (hA : 0 ≤ A) {j : ℕ} {c : V} {a : V → ℂ} (ha : IsSmoothAtom Ω K d A j c a) :
    IsRegularAtomOn Ω p r r d (ENNReal.ofReal (2 ^ r * (r : ℝ) ^ (r + 1) * A) *
      (((r + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (d ^ finrank ℝ V) * volume (ball (0 : V) 1))) ^
        (1 / p.toReal)) j c a := by
  refine isRegularAtomOn_of_pointwise hd hΩm ha.aestronglyMeasurable ha.eq_zero (fun x hx => ?_)
    (fun h x hx => ha.enorm_higherDiff_le hΩ hint hA hr hrK hx)
  have h0 := ha.norm_iteratedFDerivWithin_le 0 (Nat.zero_le K) x hx
  rw [norm_iteratedFDerivWithin_zero, mul_zero, pow_zero, mul_one] at h0
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal (h0.trans ?_)
  have hK1 : (1 : ℝ) ≤ 2 ^ r * (r : ℝ) ^ (r + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) (one_le_pow₀ (by exact_mod_cast hr))
  nlinarith

/-- **Smooth atoms on `V` restrict to every set** of unique differentiability: the derivatives
within `Ω` are the derivatives. -/
theorem IsSmoothAtom.of_univ {Ω : Set V} (hΩ : UniqueDiffOn ℝ Ω) {K : ℕ} {d A : ℝ} {j : ℕ}
    {c : V} {a : V → ℂ} (ha : IsSmoothAtom Set.univ K d A j c a) : IsSmoothAtom Ω K d A j c a where
  aestronglyMeasurable := ha.aestronglyMeasurable
  eq_zero := ha.eq_zero
  contDiffOn := ha.contDiffOn.mono (Set.subset_univ _)
  norm_iteratedFDerivWithin_le l hl y hy := by
    have hc : ContDiff ℝ K a := contDiffOn_univ.1 ha.contDiffOn
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ (hc.contDiffAt.of_le (by exact_mod_cast hl)) hy,
      ← iteratedFDerivWithin_univ]
    exact ha.norm_iteratedFDerivWithin_le l hl y (Set.mem_univ y)

/-- The zero function is a smooth atom. -/
theorem isSmoothAtom_zero (Ω : Set V) (K : ℕ) (d : ℝ) {A : ℝ} (hA : 0 ≤ A) (j : ℕ) (c : V) :
    IsSmoothAtom Ω K d A j c 0 where
  aestronglyMeasurable := aestronglyMeasurable_zero
  eq_zero _ _ := rfl
  contDiffOn := contDiffOn_const
  norm_iteratedFDerivWithin_le l _ y _ := by
    rw [iteratedFDerivWithin_zero, Pi.zero_apply, norm_zero]
    positivity

/-! ### Smooth cell atoms -/

/-- **Derivatives of cell atoms**: if `K` is smooth, vanishes outside `closedBall(0, ρ 2^(-j))` and
`‖D^l K‖ ≤ A 2^(j(n+l))`, then `‖D^l a_{j,m}‖ ≤ A 2^(jl) (ρ^n |B_1|)^(1-1/p)`. -/
theorem norm_iteratedFDeriv_cellAtom_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K g : V → ℂ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K) (hg : MemLp g p volume) {j : ℕ}
    (m : Fin (finrank ℝ V) → ℤ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hKρ : ∀ y, ρ / 2 ^ j < ‖y‖ → K y = 0)
    {l : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (hKl : ∀ y, ‖iteratedFDeriv ℝ l K y‖ ≤ A * 2 ^ (j * (finrank ℝ V + l))) (x : V) :
    ‖iteratedFDeriv ℝ l (cellAtom p K j g m) x‖ ≤ A * 2 ^ (j * l) *
      ((ENNReal.ofReal (ρ ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^
        (1 - 1 / p.toReal)).toReal := by
  set X := (ENNReal.ofReal (ρ ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^ (1 - 1 / p.toReal)
  have hX : X ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (one_sub_one_div_toReal_nonneg hp1)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
  have hKs : HasCompactSupport K := HasCompactSupport.intro (isCompact_closedBall 0 (ρ / 2 ^ j))
    fun y hy => hKρ y (by simpa [mem_closedBall, dist_zero_right, not_le] using hy)
  have hgl : LocallyIntegrable ((cell j m).indicator g) volume :=
    (hg.indicator (measurableSet_cell j m).nullMeasurableSet).locallyIntegrable hp1
  refine norm_iteratedFDeriv_const_mul_conv_le hK hKs hgl _ l x (by positivity) fun v => ?_
  set K' : V → ℂ := fun y => iteratedFDeriv ℝ l K y v
  have hK'ρ : ∀ y, ρ / 2 ^ j < ‖y‖ → K' y = 0 := fun y hy => by
    have hy' : y ∉ tsupport (iteratedFDeriv ℝ l K) := fun hmem => by
      have hsub : tsupport K ⊆ closedBall 0 (ρ / 2 ^ j) :=
        closure_minimal (fun z hz => by
          by_contra hz'
          rw [mem_closedBall, dist_zero_right, not_le] at hz'
          exact hz (hKρ z hz')) isClosed_closedBall
      have := hsub (tsupport_iteratedFDeriv_subset l hmem)
      rw [mem_closedBall, dist_zero_right] at this
      linarith
    simp [K', image_eq_zero_of_notMem_tsupport hy']
  have hK' : ∀ y, ‖K' y‖ₑ ≤ ENNReal.ofReal (A * 2 ^ (j * l) * ∏ i, ‖v i‖) *
      dyadicWeight (finrank ℝ V) j := fun y => by
    rw [← ofReal_norm, ← ofReal_two_pow_mul, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (((iteratedFDeriv ℝ l K y).le_opNorm v).trans ?_)
    calc ‖iteratedFDeriv ℝ l K y‖ * ∏ i, ‖v i‖
        ≤ A * 2 ^ (j * (finrank ℝ V + l)) * ∏ i, ‖v i‖ :=
          mul_le_mul_of_nonneg_right (hKl y) (by positivity)
      _ = A * 2 ^ (j * l) * (∏ i, ‖v i‖) * 2 ^ (j * finrank ℝ V) := by
          rw [Nat.mul_add, pow_add]
          ring
  have h := enorm_inv_cellCoef_mul_conv_le hp1 hg m hK' hρ hK'ρ x
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hX) h
  rw [toReal_eNorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h'
  calc ‖(cellCoef p j g m)⁻¹ * conv K' ((cell j m).indicator g) volume x‖
      ≤ A * 2 ^ (j * l) * (∏ i, ‖v i‖) * X.toReal := h'
    _ = A * 2 ^ (j * l) * X.toReal * ∏ i, ‖v i‖ := by ring

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- **Cell atoms of the dual kernels are smooth atoms of every order**: every cell atom of
`η_j ⋆ g`, `g ∈ L_p`, is a smooth atom on `V` of order `K`, radius factor `2LR + n` and constant
`A ((2LR)^n |B_1|)^(1-1/p)` with `A = Rd.LocalMeansBump.dualDerivConst L K`. -/
theorem isSmoothAtom_cellAtom {p : ℝ≥0∞} (hp1 : 1 ≤ p) (L K j : ℕ) {g : V → ℂ}
    (hg : MemLp g p volume) (m : Fin (finrank ℝ V) → ℤ) :
    IsSmoothAtom Set.univ K (2 * L * b.radius + finrank ℝ V)
      (b.dualDerivConst L K * ((ENNReal.ofReal ((2 * L * b.radius) ^ finrank ℝ V) *
        volume (ball (0 : V) 1)) ^ (1 - 1 / p.toReal)).toReal) j (cellCenter j m)
      (cellAtom p (b.dual L j) j g m) := by
  have hρ : 0 ≤ 2 * (L : ℝ) * b.radius :=
    mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg L)) b.radius_nonneg
  have hKρ : ∀ y, 2 * L * b.radius / 2 ^ j < ‖y‖ → b.dual L j y = 0 := fun y hy =>
    b.dual_eq_zero_of_lt L j hy
  have hKs := b.hasCompactSupport_dual L j
  have hgl : LocallyIntegrable ((cell j m).indicator g) volume :=
    (hg.indicator (measurableSet_cell j m).nullMeasurableSet).locallyIntegrable hp1
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cellAtom p (b.dual L j) j g m) := by
    have := (contDiff_conv (b.contDiff_dual L j) hKs hgl).const_smul (cellCoef p j g m)⁻¹
    exact this
  refine ⟨hsmooth.continuous.aestronglyMeasurable, fun x hx => cellAtom_eq_zero hKρ m hx,
    (hsmooth.of_le (by exact_mod_cast le_top)).contDiffOn, fun l hl y _ => ?_⟩
  rw [iteratedFDerivWithin_univ]
  refine (norm_iteratedFDeriv_cellAtom_le hp1 (b.contDiff_dual L j) hg m hρ hKρ
    (b.dualDerivConst_nonneg L K) (fun z => b.norm_iteratedFDeriv_dual_le L K hl j z) y).trans_eq ?_
  ring

/-- **Cell atoms of the dual kernels are smooth atoms of every order**: for every order `K` there
is `A` such that every cell atom of `η_j ⋆ g`, `g ∈ L_p`, is a smooth atom on `V` of order `K`,
radius factor `2LR + n` and constant `A`. -/
theorem exists_isSmoothAtom_cellAtom {p : ℝ≥0∞} (hp1 : 1 ≤ p) (L K : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (j : ℕ) {g : V → ℂ}, MemLp g p volume → ∀ m,
      IsSmoothAtom Set.univ K (2 * L * b.radius + finrank ℝ V) A j (cellCenter j m)
        (cellAtom p (b.dual L j) j g m) :=
  ⟨_, mul_nonneg (b.dualDerivConst_nonneg L K) ENNReal.toReal_nonneg,
    fun j _ hg m => b.isSmoothAtom_cellAtom hp1 L K j hg m⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Atomic decomposition into smooth atoms**: for every order `K` there is `A` such that for
every `F ∈ L_p` the terms of the reproducing formula are `η_j ⋆ (k_j ⋆ F) = ∑_m λ_{j,m} a_{j,m}`
with cell atoms that are smooth atoms on `V` of order `K`, radius factor `2LR + n` and
constant `A`, and `‖λ‖_{b^s_{p,q}}` is the local means quasi-norm. -/
theorem atomic_decomposition_smooth (hp : p ≠ ∞) (L K : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ F : Lp ℂ p (volume : Measure V),
      (∀ j m, IsSmoothAtom Set.univ K (2 * L * b.radius + finrank ℝ V) A j (cellCenter j m)
        (cellAtom p (b.dual L j) j (b.localMean hp L j F) m)) ∧
      (∀ j, ∀ᵐ x ∂volume, convLp hp (b.integrable_dual L j) (b.localMean hp L j F) x =
        ∑' m, cellCoef p j (b.localMean hp L j F) m *
          cellAtom p (b.dual L j) j (b.localMean hp L j F) m x) ∧
      ∀ s q, coeffNorm p (finrank ℝ V) s q (fun j => cellCoef p j (b.localMean hp L j F)) =
        b.localMeansNorm hp L s q F := by
  obtain ⟨A, hA, ha⟩ := b.exists_isSmoothAtom_cellAtom (Fact.out : 1 ≤ p) L K
  obtain ⟨C, -, hdec⟩ := b.atomic_decomposition hp L K
  exact ⟨A, hA, fun F => ⟨fun j m => ha j (Lp.memLp _) m, (hdec F).2.1, (hdec F).2.2⟩⟩

end LocalMeansBump

/-- The smooth bump around `0` with radii `1/2` and `1` (`Rd.centeredBumpBase` for `R = 1`). -/
noncomputable def stdBumpBase : ContDiffBump (0 : V) := centeredBumpBase one_pos

/-- The **standard bump for local means**: the normalised `ContDiffBump` around `0` with outer
radius `1`, the centred bump `Rd.LocalMeansBump.centered` of radius `1`. -/
noncomputable def LocalMeansBump.std : LocalMeansBump V := LocalMeansBump.centered one_pos

/-- The standard bump `Rd.LocalMeansBump.std`, a nonnegative function of integral `1`, has `L_1`
norm `1`. -/
theorem LocalMeansBump.eLpNorm_std_one :
    eLpNorm (LocalMeansBump.std (V := V)).toFun 1 volume = 1 := by
  rw [eLpNorm_one_eq_lintegral_eNorm (LocalMeansBump.std (V := V)).integrable.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_eNorm (LocalMeansBump.std (V := V)).integrable]
  have hn : ∀ z, ‖(LocalMeansBump.std (V := V)).toFun z‖ =
      (stdBumpBase (V := V)).normed volume z := fun z => by
    change ‖(((stdBumpBase (V := V)).normed volume z : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg ((stdBumpBase (V := V)).nonneg_normed z)]
  simp_rw [hn, ContDiffBump.integral_normed, ENNReal.ofReal_one]

end Rd
