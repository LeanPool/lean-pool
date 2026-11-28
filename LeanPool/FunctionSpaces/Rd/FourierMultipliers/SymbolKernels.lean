/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.BesselPotentials.UniformSchwartzFamilies
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Symbols of order `σ` and their dilated kernel families

A smooth function `m` on a real normed space has **symbol growth of order `σ`**
(`Rd.HasSymbolGrowth σ m`, Hörmander's class `S^σ_{1,0}`) if every derivative satisfies
`‖D^k m(ξ)‖ ≤ C_k (1 + ‖ξ‖²)^{(σ - k)/2}`: each derivative gains one power of the Japanese bracket
`⟨ξ⟩ = (1 + ‖ξ‖²)^{1/2}`.

* **The class**: Schwartz functions have symbol growth of every order
  (`Rd.hasSymbolGrowth_schwartz`), and symbols have temperate growth
  (`Rd.HasSymbolGrowth.hasTemperateGrowth`), so they are Fourier multipliers of tempered
  distributions. The orders increase (`Rd.HasSymbolGrowth.mono`) and add under products
  (`Rd.HasSymbolGrowth.mul`).
* **Examples**: constants (order `0`), continuous linear maps (order `1`), the Bessel weight
  `⟨ξ⟩^s` (order `s`, `Rd.hasSymbolGrowth_besselWeight`), `⟪ξ, v⟫` (order `1`) and `‖ξ‖²`
  (order `2`). The Bessel weight is a symbol by the derivative bounds for powers of the Japanese
  bracket (`TauCeti.exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le`), mirrored from TauCeti.
* **Rescaled symbols**: `ζ ↦ 2^{-jσ} m(2^j ζ)` (`Rd.scaledSymbol`) has derivatives bounded on
  every annulus `{a ≤ ‖ζ‖ ≤ b}`, `a > 0`, uniformly in `j`
  (`Rd.HasSymbolGrowth.exists_norm_iteratedFDeriv_scaledSymbol_le`).
* **Kernel families**: if `ω̂` vanishes outside such an annulus, the families
  `j ↦ 2^{-jσ} m(2^j ·) ω̂` and their inverse Fourier transforms `K_j` are uniformly Schwartz
  (`Rd.HasSymbolGrowth.exists_isUniformSchwartz_symbolKernelFamily`), and
  `m(D) ω_{2^j} = 2^{jσ} (K_j)_{2^j}` with `ω = 𝓕⁻¹ ω̂` (`Rd.fourierMultiplierCLM_schwartzDilate`).
  For a family `(ω_j)` that is constant from some `M` on, with `𝓕ω_M` vanishing outside such an
  annulus, the kernels `K_j` of `𝓕ω_j` (`Rd.symbolBase`) are uniformly Schwartz
  (`Rd.HasSymbolGrowth.exists_isUniformSchwartz_symbolBase`); for the synthesis kernels `ψTilde_j`
  this gives `m(D) ψTilde_j = 2^{jσ} (G_j)_{2^j}` with a uniform family `(G_j)`
  (`Rd.HasSymbolGrowth.exists_isUniformSchwartz_psiDualS`).
* **The maximal bound**: convolutions with the dilates `(G_j)_{2^j}` of a uniform family are
  bounded by the Hardy–Littlewood maximal function, uniformly in `j`, with the finite constant
  `C_{n,N} C_{A,0,N}` (`Rd.IsUniformSchwartz.enorm_conv_dilate_le_maximal`,
  `Rd.decayMaximalConst_mul_familyDecayConst_ne_top`).
-/

@[expose] public section

open MeasureTheory Module Set
open scoped ENNReal SchwartzMap FourierTransform

/-! ### Derivatives of powers of the Japanese bracket -/

namespace Rd

section Bracket

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Bracket

/-! ### Symbols of order `σ` -/

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {σ τ : ℝ} {m m' : E → F}

/-- A function `m` has **symbol growth of order `σ`**, or is a **symbol of order `σ`**
(Hörmander's class `S^σ_{1,0}`), if it is smooth and every derivative satisfies
`‖D^k m(ξ)‖ ≤ C_k (1 + ‖ξ‖²)^{(σ - k)/2}`: each derivative gains one power of the Japanese
bracket `⟨ξ⟩ = (1 + ‖ξ‖²)^{1/2}`. It strengthens Mathlib's `Function.HasTemperateGrowth`
(`Rd.HasSymbolGrowth.hasTemperateGrowth`); for `σ = 0` it is Mihlin's condition with every
derivative and the inhomogeneous weight. -/
def HasSymbolGrowth (σ : ℝ) (m : E → F) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m ∧
    ∀ k : ℕ, ∃ C : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ k m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((σ - k) / 2)

/-- A symbol is smooth. -/
theorem HasSymbolGrowth.contDiff (h : HasSymbolGrowth σ m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m :=
  h.1

/-- The constants in the bounds of a symbol can be taken nonnegative. -/
theorem HasSymbolGrowth.exists_bound (h : HasSymbolGrowth σ m) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, ‖iteratedFDeriv ℝ k m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((σ - k) / 2) := by
  obtain ⟨C, hC⟩ := h.2 k
  exact ⟨max C 0, le_max_right _ _, fun ξ => (hC ξ).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩

omit [NormedSpace ℝ E] in
/-- **The bracket below a polynomial weight**: `(1 + ‖ξ‖²)^{a/2} ≤ (1 + ‖ξ‖)^N` for `a ≤ N`, since
`1 + ‖ξ‖² ≥ 1` and `√(1 + ‖ξ‖²) ≤ 1 + ‖ξ‖` (Mathlib's `sqrt_one_add_norm_sq_le`). -/
theorem one_add_norm_sq_rpow_le_one_add_norm_pow {a : ℝ} {N : ℕ} (h : a ≤ N) (ξ : E) :
    (1 + ‖ξ‖ ^ 2) ^ (a / 2) ≤ (1 + ‖ξ‖) ^ N := by
  have h1 : 1 ≤ 1 + ‖ξ‖ ^ 2 := le_add_of_nonneg_right (by positivity)
  calc (1 + ‖ξ‖ ^ 2) ^ (a / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ ((N : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = Real.sqrt (1 + ‖ξ‖ ^ 2) ^ N := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity)]
        congr 1
        ring
    _ ≤ (1 + ‖ξ‖) ^ N := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_one_add_norm_sq_le ξ) N

/-- **Symbols have temperate growth**: a symbol of any order is smooth with polynomially bounded
derivatives, `(1 + ‖ξ‖²)^{(σ-k)/2} ≤ (1 + ‖ξ‖)^N` for `N ≥ σ - k`
(`Rd.one_add_norm_sq_rpow_le_one_add_norm_pow`). Hence symbols are Fourier multipliers of
Schwartz functions and tempered distributions. -/
theorem HasSymbolGrowth.hasTemperateGrowth (h : HasSymbolGrowth σ m) : m.HasTemperateGrowth := by
  refine ⟨h.contDiff, fun k => ?_⟩
  obtain ⟨C, hC0, hC⟩ := h.exists_bound k
  exact ⟨⌈σ - k⌉₊, C, fun ξ => (hC ξ).trans (mul_le_mul_of_nonneg_left
    (one_add_norm_sq_rpow_le_one_add_norm_pow (Nat.le_ceil _) ξ) hC0)⟩

/-- **Schwartz functions are symbols of every order**: for a Schwartz function `φ` and every
real `σ`, `‖D^k φ(ξ)‖ ≤ C (1 + ‖ξ‖²)^{(σ-k)/2}`, since `(1 + ‖ξ‖)^N ‖D^k φ(ξ)‖` is bounded by
Schwartz seminorms (Mathlib's `SchwartzMap.one_add_le_sup_seminorm_apply`) and
`(1 + ‖ξ‖²)^{(k-σ)/2} ≤ (1 + ‖ξ‖)^N` for `N ≥ k - σ`. -/
theorem hasSymbolGrowth_schwartz (φ : 𝓢(E, F)) (σ : ℝ) : HasSymbolGrowth σ φ := by
  refine ⟨φ.smooth ⊤, fun k => ?_⟩
  set N := ⌈(k : ℝ) - σ⌉₊
  refine ⟨2 ^ N * (Finset.Iic (N, k)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ,
    fun ξ => ?_⟩
  have hw : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have h1 := one_add_norm_sq_rpow_le_one_add_norm_pow (Nat.le_ceil ((k : ℝ) - σ)) ξ
  have h2 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, k)) le_rfl le_rfl φ ξ
  have hinv : (1 + ‖ξ‖ ^ 2) ^ ((σ - k) / 2) * (1 + ‖ξ‖ ^ 2) ^ (((k : ℝ) - σ) / 2) = 1 := by
    rw [← Real.rpow_add hw, show (σ - k) / 2 + ((k : ℝ) - σ) / 2 = 0 by ring, Real.rpow_zero]
  calc ‖iteratedFDeriv ℝ k φ ξ‖
      = (1 + ‖ξ‖ ^ 2) ^ (((k : ℝ) - σ) / 2) * ‖iteratedFDeriv ℝ k φ ξ‖ *
          (1 + ‖ξ‖ ^ 2) ^ ((σ - k) / 2) := by
        rw [mul_comm _ ‖_‖, mul_assoc, mul_comm (_ ^ _), hinv, mul_one]
    _ ≤ (1 + ‖ξ‖) ^ N * ‖iteratedFDeriv ℝ k φ ξ‖ * (1 + ‖ξ‖ ^ 2) ^ ((σ - k) / 2) := by
        gcongr
    _ ≤ _ := by gcongr

/-- **The order of a symbol can be raised**: a symbol of order `σ` is a symbol of every order
`τ ≥ σ`, since `1 + ‖ξ‖² ≥ 1`. -/
theorem HasSymbolGrowth.mono (h : HasSymbolGrowth σ m) (hστ : σ ≤ τ) : HasSymbolGrowth τ m := by
  refine ⟨h.contDiff, fun k => ?_⟩
  obtain ⟨C, hC0, hC⟩ := h.exists_bound k
  refine ⟨C, fun ξ => (hC ξ).trans (mul_le_mul_of_nonneg_left ?_ hC0)⟩
  exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (by positivity)) (by linarith)

/-- **Sums of symbols**: the sum of two symbols of order `σ` is a symbol of order `σ`. -/
theorem HasSymbolGrowth.add (h : HasSymbolGrowth σ m) (h' : HasSymbolGrowth σ m') :
    HasSymbolGrowth σ (m + m') := by
  refine ⟨h.contDiff.add h'.contDiff, fun k => ?_⟩
  obtain ⟨C, hC⟩ := h.2 k
  obtain ⟨C', hC'⟩ := h'.2 k
  refine ⟨C + C', fun ξ => ?_⟩
  rw [iteratedFDeriv_add_apply (h.contDiff.contDiffAt.of_le (by exact_mod_cast le_top))
    (h'.contDiff.contDiffAt.of_le (by exact_mod_cast le_top)), add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC ξ) (hC' ξ))

/-- **Negatives of symbols**: the negative of a symbol of order `σ` is a symbol of order `σ`. -/
theorem HasSymbolGrowth.neg (h : HasSymbolGrowth σ m) : HasSymbolGrowth σ (-m) := by
  refine ⟨h.contDiff.neg, fun k => ?_⟩
  obtain ⟨C, hC⟩ := h.2 k
  refine ⟨C, fun ξ => ?_⟩
  rw [iteratedFDeriv_neg_apply, norm_neg]
  exact hC ξ

/-- **Differences of symbols**: the difference of two symbols of order `σ` is a symbol of order
`σ`. -/
theorem HasSymbolGrowth.sub (h : HasSymbolGrowth σ m) (h' : HasSymbolGrowth σ m') :
    HasSymbolGrowth σ (m - m') := by
  rw [sub_eq_add_neg]
  exact h.add h'.neg

/-- **Constants are symbols of order `0`**: their derivatives of positive order vanish. -/
theorem hasSymbolGrowth_const (c : F) : HasSymbolGrowth 0 (fun _ : E => c) := by
  refine ⟨contDiff_const, fun k => ⟨‖c‖, fun ξ => ?_⟩⟩
  rcases k with _ | k
  · rw [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero, zero_div, Real.rpow_zero, mul_one]
  · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k), Pi.zero_apply, norm_zero]
    positivity

/-- **Continuous linear maps are symbols of order `1`**
(`ContinuousLinearMap.norm_iteratedFDeriv_le_one_add_norm_sq_rpow`). -/
theorem hasSymbolGrowth_continuousLinearMap (L : E →L[ℝ] F) : HasSymbolGrowth 1 L :=
  ⟨L.contDiff, fun k => ⟨‖L‖, L.norm_iteratedFDeriv_le_one_add_norm_sq_rpow k⟩⟩

/-- **Products of symbols**: if `m` is a symbol of order `σ` and `m'` one of order `τ`, with
values in a normed algebra, then `m m'` is a symbol of order `σ + τ`. In the Leibniz rule
(Mathlib's `norm_iteratedFDeriv_mul_le`) the weights of `D^i m` and `D^{k-i} m'` multiply to
`(1 + ‖ξ‖²)^{(σ + τ - k)/2}`. -/
theorem HasSymbolGrowth.mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {m m' : E → A}
    (h : HasSymbolGrowth σ m) (h' : HasSymbolGrowth τ m') : HasSymbolGrowth (σ + τ) (m * m') := by
  refine ⟨h.contDiff.mul h'.contDiff, fun k => ?_⟩
  choose C hC0 hC using h.exists_bound
  choose C' hC'0 hC' using h'.exists_bound
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C i * C' (k - i), fun ξ => ?_⟩
  have hw : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  refine (norm_iteratedFDeriv_mul_le h.contDiff h'.contDiff ξ
    (by exact_mod_cast le_top)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hexp : (1 + ‖ξ‖ ^ 2) ^ ((σ - i) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((τ - (k - i : ℕ)) / 2) =
      (1 + ‖ξ‖ ^ 2) ^ ((σ + τ - k) / 2) := by
    rw [← Real.rpow_add hw, Nat.cast_sub hik]
    ring_nf
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i m ξ‖ * ‖iteratedFDeriv ℝ (k - i) m' ξ‖
      ≤ k.choose i * (C i * (1 + ‖ξ‖ ^ 2) ^ ((σ - i) / 2)) *
          (C' (k - i) * (1 + ‖ξ‖ ^ 2) ^ ((τ - (k - i : ℕ)) / 2)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hC i ξ) (Nat.cast_nonneg _)) (hC' (k - i) ξ)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC0 i) (by positivity)))
    _ = k.choose i * C i * C' (k - i) * (1 + ‖ξ‖ ^ 2) ^ ((σ + τ - k) / 2) := by
        rw [← hexp]
        ring

/-- **Constant multiples of symbols**: `c m` is a symbol of order `σ` with `m`
(`Rd.HasSymbolGrowth.mul` with the constant symbol of order `0`). -/
theorem HasSymbolGrowth.const_mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {m : E → A}
    (h : HasSymbolGrowth σ m) (c : A) : HasSymbolGrowth σ (fun ξ => c * m ξ) := by
  have h' := (hasSymbolGrowth_const (E := E) c).mul h
  rwa [zero_add] at h'

/-- **Real symbols as complex symbols**: if `m` is a real symbol of order `σ`, then so is
`ξ ↦ (m(ξ) : ℂ)`, since the embedding `ℝ → ℂ` is a linear isometry (Mathlib's
`LinearIsometry.norm_iteratedFDeriv_comp_left`). -/
theorem HasSymbolGrowth.ofReal {m : E → ℝ} (h : HasSymbolGrowth σ m) :
    HasSymbolGrowth σ (fun ξ => (m ξ : ℂ)) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp h.contDiff, fun k => ?_⟩
  obtain ⟨C, hC⟩ := h.2 k
  refine ⟨C, fun ξ => ?_⟩
  have he := Complex.ofRealLI.norm_iteratedFDeriv_comp_left h.contDiff.contDiffAt
    (x := ξ) (i := k) (by exact_mod_cast le_top)
  exact he.trans_le (hC ξ)

end General

section InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Powers of the Japanese bracket are symbols**: `ξ ↦ (1 + ‖ξ‖²)^r` is a symbol of order
`2r` (`TauCeti.exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le`). -/
theorem hasSymbolGrowth_one_add_norm_sq_rpow (r : ℝ) :
    HasSymbolGrowth (2 * r) (fun ξ : V => (1 + ‖ξ‖ ^ 2) ^ r) := by
  refine ⟨(contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne fun ξ => by positivity,
    fun k => ?_⟩
  obtain ⟨C, hC⟩ := TauCeti.exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le (E := V) r k
  refine ⟨C, fun ξ => (hC ξ).trans_eq ?_⟩
  congr 2
  ring

/-- **The Bessel weight is a symbol**: `⟨ξ⟩^s = (1 + ‖ξ‖²)^{s/2}` (`Rd.besselWeight`), as a
complex function, is a symbol of order `s` for every real `s`
(`Rd.hasSymbolGrowth_one_add_norm_sq_rpow`). -/
theorem hasSymbolGrowth_besselWeight (s : ℝ) :
    HasSymbolGrowth s (fun ξ : V => (besselWeight s ξ : ℂ)) := by
  have h := hasSymbolGrowth_one_add_norm_sq_rpow (V := V) (s / 2)
  rw [show 2 * (s / 2) = s by ring] at h
  exact h.ofReal

/-- **Linear symbols**: `ξ ↦ ⟪ξ, v⟫`, as a complex function, is a symbol of order `1`; it is the
symbol of the derivative in the direction `v` up to the factor `2πi` (Mathlib's
`TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM`). -/
theorem hasSymbolGrowth_inner (v : V) :
    HasSymbolGrowth 1 (fun ξ : V => ((inner ℝ ξ v : ℝ) : ℂ)) := by
  have h := hasSymbolGrowth_continuousLinearMap (innerSL ℝ v)
  have he : (fun ξ : V => inner ℝ ξ v) = ⇑(innerSL ℝ v) := by
    funext ξ
    rw [innerSL_apply_apply, real_inner_comm]
  rw [← he] at h
  exact h.ofReal

/-- **The symbol of the Laplacian**: `ξ ↦ ‖ξ‖²`, as a complex function, is a symbol of order
`2`, since `‖ξ‖² = ⟨ξ⟩^2 - 1` (`Rd.hasSymbolGrowth_besselWeight`, Mathlib's
`TemperedDistribution.laplacian_eq_fourierMultiplierCLM`). -/
theorem hasSymbolGrowth_norm_sq : HasSymbolGrowth 2 (fun ξ : V => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
  have h := (hasSymbolGrowth_besselWeight (V := V) 2).sub
    ((hasSymbolGrowth_const (E := V) (1 : ℂ)).mono zero_le_two)
  convert h using 1
  funext ξ
  rw [Pi.sub_apply, besselWeight, div_self two_ne_zero, Real.rpow_one]
  push_cast
  ring

end InnerProduct

/-! ### Rescaled symbols -/

section Scaled

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {σ : ℝ} {m : V → ℂ}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The **rescaled symbol** `ζ ↦ 2^{-jσ} m(2^j ζ)` of `m` at the dyadic level `j`. For a symbol
of order `σ` its derivatives are bounded on annuli uniformly in `j`
(`Rd.HasSymbolGrowth.exists_norm_iteratedFDeriv_scaledSymbol_le`). -/
noncomputable def scaledSymbol (m : V → ℂ) (σ : ℝ) (j : ℕ) (ζ : V) : ℂ :=
  ((((2 : ℝ) ^ j) ^ (-σ) : ℝ) : ℂ) * m (((2 : ℝ) ^ j) • ζ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- With `m`, every rescaled symbol has temperate growth: it is a constant times `m` composed
with the linear map `ζ ↦ 2^j ζ`. -/
theorem hasTemperateGrowth_scaledSymbol (hm : m.HasTemperateGrowth) (σ : ℝ) (j : ℕ) :
    (scaledSymbol m σ j).HasTemperateGrowth := by
  have h := (Function.HasTemperateGrowth.const ((((2 : ℝ) ^ j) ^ (-σ) : ℝ) : ℂ)).mul
    (hm.comp (((2 : ℝ) ^ j) • ContinuousLinearMap.id ℝ V).hasTemperateGrowth)
  convert h using 1
  funext ζ
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Derivatives of a rescaled symbol**:
`D^k (2^{-jσ} m(2^j ·))(ζ) = 2^{-jσ} 2^{jk} D^k m(2^j ζ)` (Mathlib's
`iteratedFDeriv_comp_const_smul` and `iteratedFDeriv_const_smul_apply'`). -/
theorem iteratedFDeriv_scaledSymbol (hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m) (σ : ℝ)
    (j k : ℕ) (ζ : V) :
    iteratedFDeriv ℝ k (scaledSymbol m σ j) ζ =
      ((((2 : ℝ) ^ j) ^ (-σ) : ℝ) : ℂ) •
        (((2 : ℝ) ^ j) ^ k • iteratedFDeriv ℝ k m (((2 : ℝ) ^ j) • ζ)) := by
  have hk : ContDiff ℝ k m := hm.of_le (by exact_mod_cast le_top)
  have hs : scaledSymbol m σ j =
      fun ζ => ((((2 : ℝ) ^ j) ^ (-σ) : ℝ) : ℂ) • m (((2 : ℝ) ^ j) • ζ) := rfl
  rw [hs, iteratedFDeriv_const_smul_apply' (f := fun z => m (((2 : ℝ) ^ j) • z))
    ((hk.comp (contDiff_const_smul _)).contDiffAt), iteratedFDeriv_comp_const_smul _ hk]

/-- **The dyadic weights of a rescaled symbol**: for `c > 0` and `x ≥ 0`,
`c^{-σ} c^k (1 + (c x)²)^{(σ-k)/2} = (c^{-2} + x²)^{(σ-k)/2}`, since
`c^{-2} + x² = c^{-2} (1 + (c x)²)` and `(c^{-2})^{(σ-k)/2} = c^{k-σ}`. -/
theorem rpow_neg_mul_pow_mul_one_add_sq_rpow {c : ℝ} (hc : 0 < c) (σ : ℝ) (k : ℕ) (x : ℝ) :
    c ^ (-σ) * c ^ k * (1 + (c * x) ^ 2) ^ ((σ - k) / 2) = (c⁻¹ ^ 2 + x ^ 2) ^ ((σ - k) / 2) := by
  have hY : 0 ≤ 1 + (c * x) ^ 2 := by positivity
  have hbase : c⁻¹ ^ 2 + x ^ 2 = c⁻¹ ^ 2 * (1 + (c * x) ^ 2) := by
    field_simp
  have hpow : (c⁻¹ ^ 2) ^ ((σ - k) / 2) = c ^ (-σ) * c ^ k := by
    rw [← Real.rpow_natCast c k, ← Real.rpow_add hc, inv_pow, Real.inv_rpow (sq_nonneg c),
      ← Real.rpow_natCast c 2, ← Real.rpow_mul hc.le, ← Real.rpow_neg hc.le]
    congr 1
    push_cast
    ring
  rw [hbase, Real.mul_rpow (sq_nonneg _) hY, hpow]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Bounds of a rescaled symbol**: if `‖D^k m(ξ)‖ ≤ C (1 + ‖ξ‖²)^{(σ-k)/2}`, then
`‖D^k (2^{-jσ} m(2^j ·))(ζ)‖ ≤ C (2^{-2j} + ‖ζ‖²)^{(σ-k)/2}`
(`Rd.iteratedFDeriv_scaledSymbol`, `Rd.rpow_neg_mul_pow_mul_one_add_sq_rpow`). -/
theorem norm_iteratedFDeriv_scaledSymbol_le (hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m) {k : ℕ}
    {C : ℝ}
    (hC : ∀ ξ, ‖iteratedFDeriv ℝ k m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((σ - k) / 2)) (j : ℕ) (ζ : V) :
    ‖iteratedFDeriv ℝ k (scaledSymbol m σ j) ζ‖ ≤
      C * (((2 : ℝ) ^ j)⁻¹ ^ 2 + ‖ζ‖ ^ 2) ^ ((σ - k) / 2) := by
  have hc : (0 : ℝ) < 2 ^ j := by positivity
  rw [iteratedFDeriv_scaledSymbol hm, norm_smul, norm_smul, Complex.norm_real, norm_pow,
    Real.norm_of_nonneg (Real.rpow_nonneg hc.le _), Real.norm_of_nonneg hc.le,
    ← rpow_neg_mul_pow_mul_one_add_sq_rpow hc σ k ‖ζ‖]
  have h := hC (((2 : ℝ) ^ j) • ζ)
  rw [norm_smul, Real.norm_of_nonneg hc.le] at h
  calc ((2 : ℝ) ^ j) ^ (-σ) * (((2 : ℝ) ^ j) ^ k * ‖iteratedFDeriv ℝ k m (((2 : ℝ) ^ j) • ζ)‖)
      ≤ ((2 : ℝ) ^ j) ^ (-σ) * (((2 : ℝ) ^ j) ^ k *
          (C * (1 + (2 ^ j * ‖ζ‖) ^ 2) ^ ((σ - k) / 2))) := by
        gcongr
    _ = _ := by ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Rescaled symbols on an annulus**: for a symbol `m` of order `σ`, `0 < a` and `b`, every
order `k` has a constant `C ≥ 0` with `‖D^k (2^{-jσ} m(2^j ·))(ζ)‖ ≤ C` for all levels `j` and all
`ζ` with `a ≤ ‖ζ‖ ≤ b`. The weight `(2^{-2j} + ‖ζ‖²)^{(σ-k)/2}` of
`Rd.norm_iteratedFDeriv_scaledSymbol_le` is at most `max((a²)^{(σ-k)/2}, (1 + b²)^{(σ-k)/2})`
(`Rd.norm_besselSymbol_le`). -/
theorem HasSymbolGrowth.exists_norm_iteratedFDeriv_scaledSymbol_le (hm : HasSymbolGrowth σ m)
    {a : ℝ} (ha : 0 < a) (b : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, ∀ ζ : V, a ≤ ‖ζ‖ → ‖ζ‖ ≤ b →
      ‖iteratedFDeriv ℝ k (scaledSymbol m σ j) ζ‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hm.exists_bound k
  refine ⟨C * besselSymbolBound a b (σ - k), mul_nonneg hC0 (besselSymbolBound_nonneg _ _ _),
    fun j ζ hζa hζb => (norm_iteratedFDeriv_scaledSymbol_le hm.contDiff hC j ζ).trans ?_⟩
  have hε : ((2 : ℝ) ^ j)⁻¹ ^ 2 ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))⟩
  have h := norm_besselSymbol_le (σ := σ - k) ha hε hζa hζb
  rw [besselSymbol, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    at h
  exact mul_le_mul_of_nonneg_left h hC0

/-! ### The symbol and kernel families -/

/-- The **symbol family** of a Schwartz function `ω̂`: `j ↦ (ζ ↦ 2^{-jσ} m(2^j ζ) ω̂(ζ))`, a
Schwartz function when `m` has temperate growth (Mathlib's `SchwartzMap.smulLeftCLM`). -/
noncomputable def symbolFamily (m : V → ℂ) (σ : ℝ) (ωhat : 𝓢(V, ℂ)) (j : ℕ) : 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (scaledSymbol m σ j) ωhat

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The symbol family is `ζ ↦ 2^{-jσ} m(2^j ζ) ω̂(ζ)`. -/
theorem coe_symbolFamily (hm : m.HasTemperateGrowth) (σ : ℝ) (ωhat : 𝓢(V, ℂ)) (j : ℕ) :
    (symbolFamily m σ ωhat j : V → ℂ) = fun ζ => scaledSymbol m σ j ζ * ωhat ζ := by
  rw [symbolFamily, SchwartzMap.smulLeftCLM_apply (hasTemperateGrowth_scaledSymbol hm σ j)]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The symbol families are uniformly Schwartz**: if `m` is a symbol of order `σ` and `ω̂`
vanishes outside the annulus `{a ≤ ‖ζ‖ ≤ b}` with `a > 0`, then
`j ↦ 2^{-jσ} m(2^j ·) ω̂` is uniformly Schwartz. On the annulus, `‖ζ‖^k ≤ |b|^k` and the Leibniz
bound (`Rd.norm_iteratedFDeriv_mul_schwartz_le`) combines the bounds of the rescaled symbols
(`Rd.HasSymbolGrowth.exists_norm_iteratedFDeriv_scaledSymbol_le`) with the seminorms of `ω̂`;
outside the support of `ω̂` all derivatives vanish. The bounds are existential. -/
theorem HasSymbolGrowth.exists_isUniformSchwartz_symbolFamily (hm : HasSymbolGrowth σ m)
    {ωhat : 𝓢(V, ℂ)} {a b : ℝ} (ha : 0 < a) (hω : ∀ ζ, ωhat ζ ≠ 0 → a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b) :
    ∃ A : ℕ → ℕ → ℝ, IsUniformSchwartz (symbolFamily m σ ωhat) A := by
  choose C hC0 hC using fun i => hm.exists_norm_iteratedFDeriv_scaledSymbol_le ha b i
  refine ⟨fun k l => |b| ^ k * ∑ i ∈ Finset.range (l + 1),
    (l.choose i : ℝ) * C i * SchwartzMap.seminorm ℝ 0 (l - i) ωhat, fun j k l => ?_⟩
  have hsum : 0 ≤ ∑ i ∈ Finset.range (l + 1),
      (l.choose i : ℝ) * C i * SchwartzMap.seminorm ℝ 0 (l - i) ωhat :=
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC0 i))
      (apply_nonneg _ _)
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scaledSymbol m σ j) :=
    (hasTemperateGrowth_scaledSymbol hm.hasTemperateGrowth σ j).1
  refine SchwartzMap.seminorm_le_bound ℝ k l _ (mul_nonneg (by positivity) hsum) fun x => ?_
  rw [coe_symbolFamily hm.hasTemperateGrowth]
  by_cases hx : x ∈ tsupport ωhat
  · obtain ⟨hxa, hxb⟩ := mem_annulus_of_mem_tsupport hω hx
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (hxb.trans (le_abs_self b)) k)
      (norm_iteratedFDeriv_mul_schwartz_le hcd ωhat fun i _ => hC i j x hxa hxb) (norm_nonneg _)
      (by positivity)
  · have hx' : x ∉ tsupport fun y => scaledSymbol m σ j y * ωhat y :=
      fun h => hx (tsupport_mul_subset_right h)
    rw [Function.notMem_support.1 fun h => hx' (support_iteratedFDeriv_subset l h), norm_zero,
      mul_zero]
    exact mul_nonneg (by positivity) hsum

/-- The **symbol kernel family** `K_j = 𝓕⁻¹[2^{-jσ} m(2^j ·) ω̂]` of a Schwartz function `ω̂`. -/
noncomputable def symbolKernelFamily (m : V → ℂ) (σ : ℝ) (ωhat : 𝓢(V, ℂ)) (j : ℕ) : 𝓢(V, ℂ) :=
  𝓕⁻ (symbolFamily m σ ωhat j)

/-- **The symbol kernels are uniformly Schwartz** when `m` is a symbol of order `σ` and `ω̂`
vanishes outside an annulus `{a ≤ ‖ζ‖ ≤ b}` with `a > 0`
(`Rd.HasSymbolGrowth.exists_isUniformSchwartz_symbolFamily`,
`Rd.exists_isUniformSchwartz_fourierInv`); the bounds are existential. -/
theorem HasSymbolGrowth.exists_isUniformSchwartz_symbolKernelFamily (hm : HasSymbolGrowth σ m)
    {ωhat : 𝓢(V, ℂ)} {a b : ℝ} (ha : 0 < a) (hω : ∀ ζ, ωhat ζ ≠ 0 → a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b) :
    ∃ A : ℕ → ℕ → ℝ, IsUniformSchwartz (symbolKernelFamily m σ ωhat) A := by
  obtain ⟨A, hA⟩ := hm.exists_isUniformSchwartz_symbolFamily ha hω
  exact exists_isUniformSchwartz_fourierInv hA

/-- `𝓕K_j(ζ) = 2^{-jσ} m(2^j ζ) ω̂(ζ)` for the symbol kernels. -/
theorem fourier_symbolKernelFamily (hm : m.HasTemperateGrowth) (σ : ℝ) (ωhat : 𝓢(V, ℂ))
    (j : ℕ) (ζ : V) :
    𝓕 (symbolKernelFamily m σ ωhat j : V → ℂ) ζ = scaledSymbol m σ j ζ * ωhat ζ := by
  rw [← SchwartzMap.fourier_coe, symbolKernelFamily, FourierInvPair.fourier_fourierInv_eq,
    coe_symbolFamily hm]

/-- **A Fourier multiplier of a dilate**: for a function `m` of temperate growth, a real `σ` and
a Schwartz function `ω`, `m(D) ω_{2^j} = 2^{jσ} (K_j)_{2^j}` with the symbol kernels `K_j` of
`ω̂ = 𝓕ω`. Both sides have the Fourier transform `m(ξ) ω̂(2^{-j} ξ)`, since
`2^{jσ} 2^{-jσ} m(2^j 2^{-j} ξ) = m(ξ)`. -/
theorem fourierMultiplierCLM_schwartzDilate (hm : m.HasTemperateGrowth) (σ : ℝ)
    (ω : 𝓢(V, ℂ)) (j : ℕ) :
    SchwartzMap.fourierMultiplierCLM ℂ m (schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) ω) =
      ((((2 : ℝ) ^ j) ^ σ : ℝ) : ℂ) •
        schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (symbolKernelFamily m σ (𝓕 ω) j) := by
  have hc : (0 : ℝ) < 2 ^ j := by positivity
  apply (FourierTransform.fourierCLE ℂ 𝓢(V, ℂ)).injective
  simp only [FourierTransform.fourierCLE_apply, FourierTransform.fourier_smul]
  ext ξ
  rw [fourier_fourierMultiplierCLM_apply hm, smul_apply, SchwartzMap.fourier_coe,
    SchwartzMap.fourier_coe, coe_schwartzDilate, coe_schwartzDilate, fourier_dilate _ hc,
    fourier_dilate _ hc, fourier_symbolKernelFamily hm, ← SchwartzMap.fourier_coe, smul_eq_mul,
    scaledSymbol, smul_inv_smul₀ hc.ne', ← mul_assoc, ← mul_assoc,
    ← Complex.ofReal_mul, ← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero, Complex.ofReal_one,
    one_mul]

/-- The **symbol kernels of a family** `(ω_j)` of Schwartz functions:
`K_j = 𝓕⁻¹[2^{-jσ} m(2^j ·) 𝓕ω_j]`, the symbol kernel of `𝓕ω_j` at the scale `j`
(`Rd.symbolKernelFamily`), so that `m(D) (ω_j)_{2^j} = 2^{jσ} (K_j)_{2^j}`
(`Rd.fourierMultiplierCLM_schwartzDilate`). -/
noncomputable def symbolBase (m : V → ℂ) (σ : ℝ) (ω : ℕ → 𝓢(V, ℂ)) (j : ℕ) : 𝓢(V, ℂ) :=
  symbolKernelFamily m σ (𝓕 (ω j)) j

/-- **Symbol kernels of a family that is constant from `M` on**: if `m` is a symbol of order
`σ`, `ω_j = ω_M` for `j ≥ M` and `𝓕ω_M` vanishes outside the annulus `{a ≤ ‖ζ‖ ≤ b}`, `a > 0`,
then the symbol kernels `j ↦ K_j` of the family (`Rd.symbolBase`) are uniformly Schwartz: from
`M` on they are the symbol kernels of `𝓕ω_M`
(`Rd.HasSymbolGrowth.exists_isUniformSchwartz_symbolKernelFamily`), and the first `M` are
exceptions (`Rd.IsUniformSchwartz.of_forall_ge_eq`). -/
theorem HasSymbolGrowth.exists_isUniformSchwartz_symbolBase (hm : HasSymbolGrowth σ m)
    {ω : ℕ → 𝓢(V, ℂ)} {M : ℕ} {a b : ℝ} (ha : 0 < a) (hω : ∀ j, M ≤ j → ω j = ω M)
    (hann : ∀ ζ, 𝓕 (ω M) ζ ≠ 0 → a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b) :
    ∃ A : ℕ → ℕ → ℝ, IsUniformSchwartz (symbolBase m σ ω) A := by
  obtain ⟨A, hA⟩ := hm.exists_isUniformSchwartz_symbolKernelFamily ha hann
  exact ⟨_, hA.of_forall_ge_eq (N := M) fun j hj => by rw [symbolBase, hω j hj]⟩

/-- **Symbols applied to the synthesis kernels**: for a symbol `m` of order `σ` there is a
uniformly Schwartz family `(G_j)` with `m(D) ψTilde_j = 2^{jσ} (G_j)_{2^j}` for every `j`, where
`ψTilde_j = (psiDualBase j)_{2^j}` (`Rd.psiDualS`). The family `psiDualBase` is constant from
`2` on,
with Fourier transform in `{1/4 ≤ ‖ζ‖ ≤ 4}` (`Rd.mem_annulus_of_fourier_psiDualBase_ne_zero`,
`Rd.HasSymbolGrowth.exists_isUniformSchwartz_symbolBase`,
`Rd.fourierMultiplierCLM_schwartzDilate`); the bounds are existential. -/
theorem HasSymbolGrowth.exists_isUniformSchwartz_psiDualS (hm : HasSymbolGrowth σ m) :
    ∃ (G : ℕ → 𝓢(V, ℂ)) (A : ℕ → ℕ → ℝ), IsUniformSchwartz G A ∧ ∀ j,
      SchwartzMap.fourierMultiplierCLM ℂ m (psiDualS j) =
        ((((2 : ℝ) ^ j) ^ σ : ℝ) : ℂ) •
          schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (G j) := by
  obtain ⟨A, hA⟩ := hm.exists_isUniformSchwartz_symbolBase (ω := psiDualBase (V := V)) (M := 2)
    (by norm_num : (0 : ℝ) < 4⁻¹)
    (fun j hj => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hj
      rfl)
    (fun _ h => mem_annulus_of_fourier_psiDualBase_ne_zero (j := 0) h)
  exact ⟨_, A, hA, fun j =>
    fourierMultiplierCLM_schwartzDilate hm.hasTemperateGrowth σ (psiDualBase j) j⟩

end Scaled

/-! ### The maximal bound -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Uniform families below the maximal function**: if `(G_j)` is uniformly Schwartz with
bounds `A` and `N > n`, then for every level `j`, function `g` and point `x`,
`|((G_j)_{2^j} ⋆ g)(x)| ≤ C_{n,N} C_{A,0,N} M|g|(x)` with `C_{n,N} = Rd.decayMaximalConst V N` and
`C_{A,0,N} = Rd.familyDecayConst A 0 N`, both finite, independent of `j`. The dilates obey the
Peetre bound `|(G_j)_{2^j}(y)| ≤ C_{A,0,N} 2^{jn} (1 + 2^j ‖y‖)^{-N}`
(`Rd.enorm_dilate_schwartz_le`, `Rd.schwartzDecayConst_le_familyDecayConst`), and such kernels
lie below the maximal function (`Rd.enorm_conv_le_maximal_of_decay`). -/
theorem IsUniformSchwartz.enorm_conv_dilate_le_maximal {G : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ}
    (h : IsUniformSchwartz G A) {N : ℕ} (hN : finrank ℝ V < N) (j : ℕ) (g : V → ℂ) (x : V) :
    ‖conv (dilate (2 ^ j) (G j : V → ℂ)) g volume x‖ₑ ≤
      decayMaximalConst V N * familyDecayConst A 0 N * maximal (fun y => ‖g y‖ₑ) x :=
  enorm_conv_le_maximal_of_decay hN (familyDecayConst_ne_top A 0 N)
    (Filter.Eventually.of_forall fun y => (enorm_dilate_schwartz_le (G j) N j y).trans (by
      gcongr
      exact schwartzDecayConst_le_familyDecayConst h j 0 N)) g x

/-- The constant `C_{n,N} C_{A,0,N}` of `Rd.IsUniformSchwartz.enorm_conv_dilate_le_maximal` is
finite for `N > n` (`Rd.decayMaximalConst_ne_top`, `Rd.familyDecayConst_ne_top`). -/
theorem decayMaximalConst_mul_familyDecayConst_ne_top {N : ℕ} (hN : finrank ℝ V < N)
    (A : ℕ → ℕ → ℝ) : decayMaximalConst V N * familyDecayConst A 0 N ≠ ∞ :=
  ENNReal.mul_ne_top (decayMaximalConst_ne_top hN) (familyDecayConst_ne_top A 0 N)

end Rd
