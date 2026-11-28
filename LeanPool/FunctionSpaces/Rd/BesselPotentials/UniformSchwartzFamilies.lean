/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.DerivativeKernels

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Uniform Schwartz families and the Bessel kernels

On a finite-dimensional real inner product space `V` with Lebesgue measure, let `J_σ` be the
Bessel potential on Schwartz functions, the Fourier multiplier with the Bessel weight
`⟨ξ⟩^σ = (1 + ‖ξ‖²)^{σ/2}` (`Rd.besselSchwartz`, the restriction of Mathlib's
`TemperedDistribution.besselPotential`). For every Schwartz function `ω` it maps the dilate
`ω_{2^j}`, `ω_c(x) = c^n ω(c x)`, to `2^{jσ} (K_j)_{2^j}` with the **Bessel kernels**
`K_j = 𝓕⁻¹[(2^{-2j} + ‖ζ‖²)^{σ/2} ω̂]` (`Rd.besselKernelFamily`,
`Rd.besselSchwartz_schwartzDilate`, and `Rd.besselPotential_schwartzDilate` for Mathlib's
`J_σ` on tempered distributions); the factor has size `|(2^j)^σ| = 2^{jσ}`
(`Rd.enorm_two_pow_rpow`).

* **Uniform families under continuous linear maps**: a family is uniformly Schwartz exactly
  when its range is bounded in the Schwartz space
  (`Rd.exists_isUniformSchwartz_iff_isVonNBounded`), so with `(G_j)` also `(T G_j)` is uniformly
  Schwartz for every continuous linear map `T` of the Schwartz space
  (`Rd.IsUniformSchwartz.exists_map`, from Mathlib's `Bornology.IsVonNBounded.image`); in
  particular for `𝓕⁻¹` (`Rd.exists_isUniformSchwartz_fourierInv`).
* **The shifted Bessel symbols** `(ε + ‖ζ‖²)^{σ/2}` (`Rd.besselSymbol`) have derivatives of every
  order bounded on an annulus `{a ≤ ‖ζ‖ ≤ b}`, `a > 0`, uniformly in `ε ∈ (0, 1]`
  (`Rd.exists_norm_iteratedFDeriv_besselSymbol_le`), by the Faà di Bruno bound for compositions
  and compactness (`ContDiffOn.exists_norm_iteratedFDerivWithin_le`).
* **The symbol and kernel families**: if `ω̂` vanishes outside such an annulus, then
  `j ↦ (2^{-2j} + ‖ζ‖²)^{σ/2} ω̂` and `j ↦ K_j` are uniformly Schwartz
  (`Rd.exists_isUniformSchwartz_besselSymbolFamily`,
  `Rd.exists_isUniformSchwartz_besselKernelFamily`); the bounds are existential.
* **The dilated Bessel kernels form a Calderón–Zygmund family** when `b = 2^N a`, with the
  explicit overlap `Rd.besselOverlap` and an existential Hörmander constant
  (`Rd.exists_isCZFamily_besselKernelFamily`). At most `N + 1` of them see a frequency
  (`ENNReal.tsum_le_of_dyadic_annulus`). The Fourier transforms of `ψ_1`,
  `Rd.psiBase (j+1)` and `Rd.psiDualBase (j+2)` vanish outside such annuli.
-/

@[expose] public section

open MeasureTheory Module Metric Filter Set
open scoped ENNReal SchwartzMap FourierTransform
open TemperedDistribution (besselPotential)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Uniform families under continuous linear maps -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Uniform families are the bounded families**: a family `(G_j)` of Schwartz functions is
uniformly Schwartz for some bounds exactly when its range is a bounded set of the Schwartz space
in the sense of topological vector spaces (von Neumann bounded). Both say that every Schwartz
seminorm is bounded on the family (Mathlib's `WithSeminorms.isVonNBounded_iff_seminorm_bddAbove`
with `schwartz_withSeminorms`). -/
theorem exists_isUniformSchwartz_iff_isVonNBounded (G : ℕ → 𝓢(V, ℂ)) :
    (∃ A, IsUniformSchwartz G A) ↔ Bornology.IsVonNBounded ℝ (Set.range G) := by
  rw [(schwartz_withSeminorms ℝ V ℂ).isVonNBounded_iff_seminorm_bddAbove]
  constructor
  · rintro ⟨A, hA⟩ ⟨k, l⟩
    refine ⟨A k l, ?_⟩
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact hA j k l
  · intro h
    choose A hA using h
    exact ⟨fun k l => A (k, l), fun j k l => hA (k, l) ⟨G j, ⟨j, rfl⟩, rfl⟩⟩

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Continuous linear maps preserve uniform families**: if `(G_j)` is uniformly Schwartz and
`T` is a continuous linear map of the Schwartz space, then `(T G_j)` is uniformly Schwartz. This
is the form for indexed families of Mathlib's `Bornology.IsVonNBounded.image`, since a family is
uniformly Schwartz exactly when its range is bounded in `𝓢(V, ℂ)`
(`Rd.exists_isUniformSchwartz_iff_isVonNBounded`). -/
theorem IsUniformSchwartz.exists_map {G : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ}
    (h : IsUniformSchwartz G A) (T : 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℂ)) :
    ∃ A' : ℕ → ℕ → ℝ, IsUniformSchwartz (fun j => T (G j)) A' := by
  rw [exists_isUniformSchwartz_iff_isVonNBounded, show Set.range (fun j => T (G j)) =
    T '' Set.range G from Set.range_comp T G]
  exact ((exists_isUniformSchwartz_iff_isVonNBounded G).1 ⟨A, h⟩).image T

/-- **The inverse Fourier transform preserves uniform families**: `𝓕⁻` is a continuous linear
map of the Schwartz space (`Rd.IsUniformSchwartz.exists_map`). -/
theorem exists_isUniformSchwartz_fourierInv {G : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ}
    (h : IsUniformSchwartz G A) : ∃ A' : ℕ → ℕ → ℝ, IsUniformSchwartz (fun j => 𝓕⁻ (G j)) A' :=
  h.exists_map (FourierTransform.fourierInvCLM ℝ 𝓢(V, ℂ))

/-! ### The shifted Bessel symbols -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The **shifted Bessel symbol** `ζ ↦ (ε + ‖ζ‖²)^{σ/2}`, as a complex-valued function. For
`ε = 1` it is the symbol of Mathlib's Bessel potential `TemperedDistribution.besselPotential`. -/
noncomputable def besselSymbol (ε σ : ℝ) (ζ : V) : ℂ := (((ε + ‖ζ‖ ^ 2) ^ (σ / 2) : ℝ) : ℂ)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The shifted Bessel symbol is `t ↦ t^{σ/2}` composed with `ζ ↦ ε + ‖ζ‖²`. -/
theorem besselSymbol_eq_comp (ε σ : ℝ) :
    besselSymbol (V := V) ε σ = (fun t : ℝ => ((t ^ (σ / 2) : ℝ) : ℂ)) ∘ fun ζ => ε + ‖ζ‖ ^ 2 :=
  rfl

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- For `ε = 1` the shifted Bessel symbol is the Bessel weight `⟨ξ⟩^σ = (1 + ‖ξ‖²)^{σ/2}`
(`Rd.besselWeight`), the symbol of Mathlib's Bessel potential. -/
theorem besselSymbol_one (σ : ℝ) : besselSymbol (V := V) 1 σ = fun ξ => (besselWeight σ ξ : ℂ) :=
  rfl

/-- The function `t ↦ t^τ`, as a complex-valued function, is smooth on `(0, ∞)`. -/
theorem _root_.Complex.contDiffOn_ofReal_rpow_const (τ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => ((t ^ τ : ℝ) : ℂ)) (Ioi 0) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_fun_id.rpow_const_of_ne fun _ ht => (ne_of_gt ht))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- For `ε > 0` the shifted Bessel symbol is smooth, since `ε + ‖ζ‖² > 0` everywhere. -/
theorem contDiff_besselSymbol {ε : ℝ} (hε : 0 < ε) (σ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (besselSymbol (V := V) ε σ) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne
    fun ζ => (add_pos_of_pos_of_nonneg hε (sq_nonneg ‖ζ‖)).ne')

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The scaling identity of the symbols**: for `c > 0`,
`⟨ξ⟩^σ = (1 + ‖ξ‖²)^{σ/2} = c^σ (c^{-2} + ‖c^{-1} ξ‖²)^{σ/2}`, since
`c^{-2} + ‖c^{-1} ξ‖² = c^{-2} (1 + ‖ξ‖²)`. -/
theorem besselWeight_eq_mul_besselSymbol {c : ℝ} (hc : 0 < c) (σ : ℝ) (ξ : V) :
    (besselWeight σ ξ : ℂ) = ((c ^ σ : ℝ) : ℂ) * besselSymbol (c⁻¹ ^ 2) σ (c⁻¹ • ξ) := by
  rw [besselWeight, besselSymbol, ← Complex.ofReal_mul]
  congr 1
  have hX : 0 ≤ 1 + ‖ξ‖ ^ 2 := by positivity
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le),
    show c⁻¹ ^ 2 + (c⁻¹ * ‖ξ‖) ^ 2 = c⁻¹ ^ 2 * (1 + ‖ξ‖ ^ 2) by ring,
    Real.mul_rpow (sq_nonneg _) hX, ← Real.rpow_natCast_mul (inv_nonneg.2 hc.le),
    show ((2 : ℕ) : ℝ) * (σ / 2) = σ by push_cast; ring, Real.inv_rpow hc.le, ← mul_assoc,
    mul_inv_cancel₀ (Real.rpow_pos_of_pos hc σ).ne', one_mul]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Rescaling the shift**: `(ε + ‖ζ‖²)^{σ/2} = ε^{σ/2} ⟨ε^{-1/2} ζ⟩^σ` for `ε > 0`, the scaling
identity `Rd.besselWeight_eq_mul_besselSymbol` with `c = ε^{-1/2}`. -/
theorem besselSymbol_eq_mul {ε : ℝ} (hε : 0 < ε) (σ : ℝ) (ζ : V) :
    besselSymbol ε σ ζ =
      ((ε ^ (σ / 2) : ℝ) : ℂ) * besselSymbol 1 σ ((Real.sqrt ε)⁻¹ • ζ) := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have h := besselWeight_eq_mul_besselSymbol (inv_pos.2 hs) σ ((Real.sqrt ε)⁻¹ • ζ)
  rw [inv_inv, Real.sq_sqrt hε.le, smul_inv_smul₀ hs.ne'] at h
  rw [besselSymbol_one]
  beta_reduce
  rw [h, ← mul_assoc, ← Complex.ofReal_mul, Real.inv_rpow hs.le,
    Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le, show 1 / 2 * σ = σ / 2 by ring,
    mul_inv_cancel₀ (Real.rpow_pos_of_pos hε _).ne', Complex.ofReal_one, one_mul]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- For `ε > 0` the shifted Bessel symbol has temperate growth: it is a constant times
Mathlib's Bessel symbol composed with a dilation (`Rd.besselSymbol_eq_mul`,
Mathlib's `Function.hasTemperateGrowth_one_add_norm_sq_rpow`). -/
theorem hasTemperateGrowth_besselSymbol {ε : ℝ} (hε : 0 < ε) (σ : ℝ) :
    (besselSymbol (V := V) ε σ).HasTemperateGrowth := by
  have h1 : (fun ζ : V => besselSymbol 1 σ ((Real.sqrt ε)⁻¹ • ζ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp
      ((Function.hasTemperateGrowth_one_add_norm_sq_rpow V (σ / 2)).comp
        ((Real.sqrt ε)⁻¹ • ContinuousLinearMap.id ℝ V).hasTemperateGrowth)
  have h2 := (Function.HasTemperateGrowth.const ((ε ^ (σ / 2) : ℝ) : ℂ)).mul h1
  convert h2 using 1
  funext ζ
  exact besselSymbol_eq_mul hε σ ζ

omit [MeasurableSpace V] [BorelSpace V] in
/-- The derivatives of `ζ ↦ ε + ‖ζ‖²` of the orders `1 ≤ i ≤ r` are those of `ζ ↦ ‖ζ‖²`, so on
the ball of radius `b` they are at most `D^i` for one `D`, uniformly in `ε`. -/
theorem exists_norm_iteratedFDeriv_add_norm_sq_le (b : ℝ) (r : ℕ) :
    ∃ D : ℝ, ∀ ε : ℝ, ∀ i, 1 ≤ i → i ≤ r → ∀ ζ : V, ‖ζ‖ ≤ b →
      ‖iteratedFDeriv ℝ i (fun ζ : V => ε + ‖ζ‖ ^ 2) ζ‖ ≤ D ^ i := by
  obtain ⟨C, hC⟩ := (contDiff_norm_sq ℝ (E := V)).contDiffOn.exists_norm_iteratedFDerivWithin_le
    uniqueDiffOn_univ (isCompact_closedBall (0 : V) b) (subset_univ _) r
  refine ⟨max 1 C, fun ε i hi1 hir ζ hζ => ?_⟩
  have h := hC i hir ζ (mem_closedBall_zero_iff.2 hζ)
  rw [iteratedFDerivWithin_univ] at h
  rw [show (fun ζ : V => ε + ‖ζ‖ ^ 2) = (fun _ : V => ε) + fun ζ : V => ‖ζ‖ ^ 2 from rfl,
    iteratedFDeriv_add_apply contDiffAt_const (contDiff_norm_sq ℝ).contDiffAt,
    iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, zero_add]
  calc _ ≤ C := h
    _ ≤ max 1 C := le_max_right _ _
    _ ≤ max 1 C ^ i := le_self_pow₀ (le_max_left _ _) (by omega)

omit [MeasurableSpace V] [BorelSpace V] in
/-- **Joint bounds for the shifted Bessel symbols**: for `0 < a`, `b`, `σ` and every order `r`
there is `C ≥ 0` with `‖D^r (ε + ‖·‖²)^{σ/2}(ζ)‖ ≤ C` for all `ε ∈ (0, 1]` and all `ζ` with
`a ≤ ‖ζ‖ ≤ b`. The symbol is `g ∘ f_ε` with `g(t) = t^{σ/2}`, smooth on `(0, ∞)`, and
`f_ε(ζ) = ε + ‖ζ‖² > 0`; the values `f_ε(ζ)` lie in the compact interval `[a², 1 + b²]`, where the
derivatives of `g` are bounded, the derivatives of `f_ε` of positive order are those of `‖·‖²`,
and Mathlib's Faà di Bruno bound `norm_iteratedFDeriv_comp_le'` combines the two. -/
theorem exists_norm_iteratedFDeriv_besselSymbol_le {a : ℝ} (ha : 0 < a) (b σ : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ζ : V, a ≤ ‖ζ‖ → ‖ζ‖ ≤ b →
      ‖iteratedFDeriv ℝ r (besselSymbol ε σ) ζ‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ :=
    (Complex.contDiffOn_ofReal_rpow_const (σ / 2)).exists_norm_iteratedFDerivWithin_le
    isOpen_Ioi.uniqueDiffOn (isCompact_Icc (a := a ^ 2) (b := 1 + b ^ 2))
    (fun t ht => lt_of_lt_of_le (pow_pos ha 2) ht.1) r
  obtain ⟨D, hD⟩ := exists_norm_iteratedFDeriv_add_norm_sq_le (V := V) b r
  refine ⟨max 0 (r.factorial * C₁ * D ^ r), le_max_left _ _, fun ε hε ζ hζa hζb => ?_⟩
  have h2a : a ^ 2 ≤ ‖ζ‖ ^ 2 := pow_le_pow_left₀ ha.le hζa 2
  have h2b : ‖ζ‖ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (norm_nonneg ζ) hζb 2
  rw [besselSymbol_eq_comp]
  refine le_max_of_le_right (norm_iteratedFDeriv_comp_le' (t := Ioi 0) ?_
    isOpen_Ioi.uniqueDiffOn (Complex.contDiffOn_ofReal_rpow_const (σ / 2))
    (contDiff_const.add (contDiff_norm_sq ℝ)) (WithTop.coe_le_coe.2 le_top) ζ
    (fun i hi => hC₁ i hi _ ⟨?_, ?_⟩) (fun i hi1 hir => hD ε i hi1 hir ζ hζb))
  · rintro _ ⟨y, rfl⟩
    exact add_pos_of_pos_of_nonneg hε.1 (sq_nonneg ‖y‖)
  · linarith [hε.1]
  · linarith [hε.2]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The bound `max((a²)^{σ/2}, (1 + b²)^{σ/2})` of the shifted Bessel symbols on the annulus
`{a ≤ ‖ζ‖ ≤ b}` for `ε ∈ [0, 1]` (`Rd.norm_besselSymbol_le`). -/
noncomputable def besselSymbolBound (a b σ : ℝ) : ℝ :=
  max ((a ^ 2) ^ (σ / 2)) ((1 + b ^ 2) ^ (σ / 2))

/-- The bound `max((a²)^{σ/2}, (1 + b²)^{σ/2})` is nonnegative. -/
theorem besselSymbolBound_nonneg (a b σ : ℝ) : 0 ≤ besselSymbolBound a b σ :=
  le_max_of_le_left (Real.rpow_nonneg (sq_nonneg a) _)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Size of the shifted Bessel symbols on the annulus**: for `0 < a ≤ ‖ζ‖ ≤ b` and
`ε ∈ [0, 1]`, `|(ε + ‖ζ‖²)^{σ/2}| ≤ max((a²)^{σ/2}, (1 + b²)^{σ/2})`, since
`ε + ‖ζ‖² ∈ [a², 1 + b²]` and `t ↦ t^{σ/2}` is monotone. -/
theorem norm_besselSymbol_le {a b ε σ : ℝ} (ha : 0 < a) (hε : ε ∈ Icc (0 : ℝ) 1) {ζ : V}
    (h1 : a ≤ ‖ζ‖) (h2 : ‖ζ‖ ≤ b) : ‖besselSymbol ε σ ζ‖ ≤ besselSymbolBound a b σ := by
  have h2a : a ^ 2 ≤ ε + ‖ζ‖ ^ 2 := by nlinarith [hε.1, pow_le_pow_left₀ ha.le h1 2]
  have h2b : ε + ‖ζ‖ ^ 2 ≤ 1 + b ^ 2 := by
    nlinarith [hε.2, pow_le_pow_left₀ (norm_nonneg ζ) h2 2]
  have hpos : 0 < ε + ‖ζ‖ ^ 2 := lt_of_lt_of_le (pow_pos ha 2) h2a
  rw [besselSymbol, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)]
  by_cases hσ : 0 ≤ σ / 2
  · exact le_max_of_le_right (Real.rpow_le_rpow hpos.le h2b hσ)
  · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos (pow_pos ha 2) h2a (not_le.1 hσ).le)

/-! ### The Bessel symbol and kernel families -/

/-- The **Bessel symbol family** of a Schwartz function `ω̂`:
`j ↦ (ζ ↦ (2^{-2j} + ‖ζ‖²)^{σ/2} ω̂(ζ))`, a Schwartz function since the symbol has temperate
growth (Mathlib's `SchwartzMap.smulLeftCLM`). -/
noncomputable def besselSymbolFamily (ωhat : 𝓢(V, ℂ)) (σ : ℝ) (j : ℕ) : 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (besselSymbol (((2 : ℝ) ^ j)⁻¹ ^ 2) σ) ωhat

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Bessel symbol family is `ζ ↦ (2^{-2j} + ‖ζ‖²)^{σ/2} ω̂(ζ)`. -/
theorem coe_besselSymbolFamily (ωhat : 𝓢(V, ℂ)) (σ : ℝ) (j : ℕ) :
    (besselSymbolFamily ωhat σ j : V → ℂ) =
      fun ζ => besselSymbol (((2 : ℝ) ^ j)⁻¹ ^ 2) σ ζ * ωhat ζ := by
  rw [besselSymbolFamily,
    SchwartzMap.smulLeftCLM_apply (hasTemperateGrowth_besselSymbol (by positivity) σ)]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The Leibniz bound against a Schwartz function**: if the derivatives of the smooth function
`g` at `x` of the orders `i ≤ l` are at most `C_i`, then
`‖D^l (g ω)(x)‖ ≤ ∑_{i ≤ l} C(l, i) C_i ‖ω‖_{0, l-i}` (Mathlib's `norm_iteratedFDeriv_mul_le`). -/
theorem norm_iteratedFDeriv_mul_schwartz_le {g : V → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (ω : 𝓢(V, ℂ)) {l : ℕ} {C : ℕ → ℝ} {x : V} (hC : ∀ i ≤ l, ‖iteratedFDeriv ℝ i g x‖ ≤ C i) :
    ‖iteratedFDeriv ℝ l (fun y => g y * ω y) x‖ ≤
      ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * C i * SchwartzMap.seminorm ℝ 0 (l - i) ω := by
  refine (norm_iteratedFDeriv_mul_le hg (ω.smooth ⊤) x (WithTop.coe_le_coe.2 le_top)).trans ?_
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hCi : 0 ≤ C i := (norm_nonneg _).trans (hC i hi')
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hC i hi') (Nat.cast_nonneg _))
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ ω (l - i) x) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hCi)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- If a function vanishes outside the closed annulus `{a ≤ ‖ζ‖ ≤ b}`, the closure of its support
lies in that annulus. -/
theorem mem_annulus_of_mem_tsupport {f : V → ℂ} {a b : ℝ}
    (hf : ∀ ζ, f ζ ≠ 0 → a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b) {x : V} (hx : x ∈ tsupport f) :
    a ≤ ‖x‖ ∧ ‖x‖ ≤ b := by
  have hclosed : IsClosed {ζ : V | a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b} :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  exact closure_minimal (fun ζ hζ => hf ζ hζ) hclosed hx

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The Bessel symbol families are uniformly Schwartz**: if `ω̂` vanishes outside the annulus
`{a ≤ ‖ζ‖ ≤ b}` with `a > 0`, then `j ↦ (2^{-2j} + ‖ζ‖²)^{σ/2} ω̂` is uniformly Schwartz. On the
annulus, `‖ζ‖^k ≤ |b|^k` and the Leibniz bound (`Rd.norm_iteratedFDeriv_mul_schwartz_le`)
combines the joint symbol bounds (`Rd.exists_norm_iteratedFDeriv_besselSymbol_le`) with the
seminorms of `ω̂`; outside the support of `ω̂` all derivatives vanish. The bounds are
existential. -/
theorem exists_isUniformSchwartz_besselSymbolFamily {ωhat : 𝓢(V, ℂ)} {a b : ℝ} (ha : 0 < a)
    (hω : ∀ ζ, ωhat ζ ≠ 0 → a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b) (σ : ℝ) :
    ∃ A : ℕ → ℕ → ℝ, IsUniformSchwartz (besselSymbolFamily ωhat σ) A := by
  choose C hC0 hC using fun i => exists_norm_iteratedFDeriv_besselSymbol_le (V := V) ha b σ i
  refine ⟨fun k l => |b| ^ k * ∑ i ∈ Finset.range (l + 1),
    (l.choose i : ℝ) * C i * SchwartzMap.seminorm ℝ 0 (l - i) ωhat, fun j k l => ?_⟩
  have hsum : 0 ≤ ∑ i ∈ Finset.range (l + 1),
      (l.choose i : ℝ) * C i * SchwartzMap.seminorm ℝ 0 (l - i) ωhat :=
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC0 i))
      (apply_nonneg _ _)
  refine SchwartzMap.seminorm_le_bound ℝ k l _ (mul_nonneg (by positivity) hsum) fun x => ?_
  rw [coe_besselSymbolFamily]
  have hε : ((2 : ℝ) ^ j)⁻¹ ^ 2 ∈ Ioc (0 : ℝ) 1 :=
    ⟨by positivity, pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))⟩
  by_cases hx : x ∈ tsupport ωhat
  · obtain ⟨hxa, hxb⟩ := mem_annulus_of_mem_tsupport hω hx
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (hxb.trans (le_abs_self b)) k)
      (norm_iteratedFDeriv_mul_schwartz_le (contDiff_besselSymbol hε.1 σ) ωhat fun i _ =>
        hC i _ hε x hxa hxb) (norm_nonneg _) (by positivity)
  · have hx' : x ∉ tsupport fun y => besselSymbol (((2 : ℝ) ^ j)⁻¹ ^ 2) σ y * ωhat y :=
      fun h => hx (tsupport_mul_subset_right h)
    rw [Function.notMem_support.1 fun h => hx' (support_iteratedFDeriv_subset l h), norm_zero,
      mul_zero]
    exact mul_nonneg (by positivity) hsum

/-- The **Bessel kernel family** `K_j = 𝓕⁻¹[(2^{-2j} + ‖ζ‖²)^{σ/2} ω̂]` of a Schwartz function
`ω̂`. -/
noncomputable def besselKernelFamily (ωhat : 𝓢(V, ℂ)) (σ : ℝ) (j : ℕ) : 𝓢(V, ℂ) :=
  𝓕⁻ (besselSymbolFamily ωhat σ j)

/-- **The Bessel kernels are uniformly Schwartz** when `ω̂` vanishes outside an annulus
`{a ≤ ‖ζ‖ ≤ b}` with `a > 0` (`Rd.exists_isUniformSchwartz_besselSymbolFamily` and
`Rd.exists_isUniformSchwartz_fourierInv`); the bounds are existential. -/
theorem exists_isUniformSchwartz_besselKernelFamily {ωhat : 𝓢(V, ℂ)} {a b : ℝ} (ha : 0 < a)
    (hω : ∀ ζ, ωhat ζ ≠ 0 → a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b) (σ : ℝ) :
    ∃ A : ℕ → ℕ → ℝ, IsUniformSchwartz (besselKernelFamily ωhat σ) A := by
  obtain ⟨A, hA⟩ := exists_isUniformSchwartz_besselSymbolFamily ha hω σ
  exact exists_isUniformSchwartz_fourierInv hA

/-- `𝓕K_j(ζ) = (2^{-2j} + ‖ζ‖²)^{σ/2} ω̂(ζ)`. -/
theorem fourier_besselKernelFamily (ωhat : 𝓢(V, ℂ)) (σ : ℝ) (j : ℕ) (ζ : V) :
    𝓕 (besselKernelFamily ωhat σ j : V → ℂ) ζ =
      besselSymbol (((2 : ℝ) ^ j)⁻¹ ^ 2) σ ζ * ωhat ζ := by
  rw [← SchwartzMap.fourier_coe, besselKernelFamily, FourierInvPair.fourier_fourierInv_eq,
    coe_besselSymbolFamily]

/-- **The Bessel potential of a dilate**: for every Schwartz function `ω`,
`J_σ ω_{2^j} = 2^{jσ} (K_j)_{2^j}` with the Bessel kernels `K_j` of `ω̂ = 𝓕ω`, where `J_σ` is the
Bessel potential on Schwartz functions (`Rd.besselSchwartz`). Both sides have the Fourier
transform `⟨ξ⟩^σ ω̂(2^{-j} ξ)` (`Rd.besselWeight_eq_mul_besselSymbol`). -/
theorem besselSchwartz_schwartzDilate (ω : 𝓢(V, ℂ)) (σ : ℝ) (j : ℕ) :
    besselSchwartz σ (schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) ω) =
      ((((2 : ℝ) ^ j) ^ σ : ℝ) : ℂ) •
        schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (besselKernelFamily (𝓕 ω) σ j) := by
  have hc : (0 : ℝ) < 2 ^ j := by positivity
  apply (FourierTransform.fourierCLE ℂ 𝓢(V, ℂ)).injective
  simp only [besselSchwartz, FourierTransform.fourierCLE_apply,
    SchwartzMap.fourierMultiplierCLM_apply, FourierInvPair.fourier_fourierInv_eq,
    FourierTransform.fourier_smul]
  ext ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_besselWeight σ),
    smul_apply, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, coe_schwartzDilate,
    coe_schwartzDilate, fourier_dilate _ hc, fourier_dilate _ hc, fourier_besselKernelFamily,
    ← SchwartzMap.fourier_coe, besselWeight_eq_mul_besselSymbol hc σ ξ, smul_eq_mul, smul_eq_mul,
    mul_assoc]

/-- **Mathlib's Bessel potential of a dilate**: for every Schwartz function `ω`, Mathlib's
`J_σ = TemperedDistribution.besselPotential V ℂ σ` maps the tempered distribution of `ω_{2^j}`
to that of `2^{jσ} (K_j)_{2^j}` (`Rd.besselPotential_schwartz`,
`Rd.besselSchwartz_schwartzDilate`). -/
theorem besselPotential_schwartzDilate (ω : 𝓢(V, ℂ)) (σ : ℝ) (j : ℕ) :
    besselPotential V ℂ σ (schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) ω : 𝓢'(V, ℂ)) =
      ((((2 : ℝ) ^ j) ^ σ : ℝ) : ℂ) •
        (schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (besselKernelFamily (𝓕 ω) σ j) :
          𝓢'(V, ℂ)) := by
  rw [besselPotential_schwartz, besselSchwartz_schwartzDilate]
  exact map_smul _ _ _

/-- The factor of a dilate has size `|(2^j)^σ| = 2^{jσ}`, the dyadic weight
`ENNReal.dyadicWeight σ j`. -/
theorem enorm_two_pow_rpow (j : ℕ) (σ : ℝ) :
    ‖((((2 : ℝ) ^ j) ^ σ : ℝ) : ℂ)‖ₑ = ENNReal.dyadicWeight σ j := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    ← ENNReal.ofReal_rpow_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat, ENNReal.dyadicWeight, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]

/-! ### The dilated Bessel kernels as a Calderón–Zygmund family -/

/-- `𝓕(K_j)_{2^j}(ξ) = (2^{-2j} + ‖ζ‖²)^{σ/2} ω̂(ζ)` with `ζ = 2^{-j} ξ`. -/
theorem fourier_dilate_besselKernelFamily (ωhat : 𝓢(V, ℂ)) (σ : ℝ) (j : ℕ) (ξ : V) :
    𝓕 (dilate (2 ^ j) (besselKernelFamily ωhat σ j : V → ℂ)) ξ =
      besselSymbol (((2 : ℝ) ^ j)⁻¹ ^ 2) σ (((2 : ℝ) ^ j)⁻¹ • ξ) *
        ωhat (((2 : ℝ) ^ j)⁻¹ • ξ) := by
  rw [fourier_dilate _ (by positivity), fourier_besselKernelFamily]

/-- Where `𝓕(K_j)_{2^j}(ξ) ≠ 0`, the frequency `2^{-j} ξ` lies in the annulus
`{a ≤ ‖ζ‖ ≤ b}` outside which `ω̂` vanishes. -/
theorem mem_annulus_of_fourier_dilate_besselKernelFamily_ne_zero {ωhat : 𝓢(V, ℂ)} {a b : ℝ}
    (hω : ∀ ζ, ωhat ζ ≠ 0 → a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b) {σ : ℝ} {j : ℕ} {ξ : V}
    (h : 𝓕 (dilate (2 ^ j) (besselKernelFamily ωhat σ j : V → ℂ)) ξ ≠ 0) :
    a ≤ ‖ξ‖ / 2 ^ j ∧ ‖ξ‖ / 2 ^ j ≤ b := by
  rw [fourier_dilate_besselKernelFamily] at h
  rw [← norm_two_pow_inv_smul]
  exact hω _ (right_ne_zero_of_mul h)

/-- **Size of the dilated Bessel kernels on the Fourier side**: if `ω̂` vanishes outside the
annulus `{a ≤ ‖ζ‖ ≤ b}`, `a > 0`, then
`|𝓕(K_j)_{2^j}(ξ)| ≤ max((a²)^{σ/2}, (1 + b²)^{σ/2}) sup |ω̂|` (`Rd.norm_besselSymbol_le`). -/
theorem enorm_fourier_dilate_besselKernelFamily_le {ωhat : 𝓢(V, ℂ)} {a b : ℝ} (ha : 0 < a)
    (hω : ∀ ζ, ωhat ζ ≠ 0 → a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b) (σ : ℝ) (j : ℕ) (ξ : V) :
    ‖𝓕 (dilate (2 ^ j) (besselKernelFamily ωhat σ j : V → ℂ)) ξ‖ₑ ≤
      ENNReal.ofReal (besselSymbolBound a b σ * SchwartzMap.seminorm ℝ 0 0 ωhat) := by
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [fourier_dilate_besselKernelFamily, norm_mul]
  by_cases h0 : ωhat (((2 : ℝ) ^ j)⁻¹ • ξ) = 0
  · rw [h0, norm_zero, mul_zero]
    exact mul_nonneg (besselSymbolBound_nonneg a b σ) (apply_nonneg _ _)
  · obtain ⟨h1, h2⟩ := hω _ h0
    have hε : ((2 : ℝ) ^ j)⁻¹ ^ 2 ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))⟩
    exact mul_le_mul (norm_besselSymbol_le ha hε h1 h2)
      (SchwartzMap.norm_le_seminorm ℝ ωhat _) (norm_nonneg _)
      ((norm_nonneg _).trans (norm_besselSymbol_le ha hε h1 h2))

/-- The **overlap of the dilated Bessel kernels**
`(N + 1) (max((a²)^{σ/2}, (1 + (2^N a)²)^{σ/2}) sup |ω̂|)²` for `ω̂` vanishing outside the annulus
`{a ≤ ‖ζ‖ ≤ 2^N a}`: at most `N + 1` kernels see a frequency
(`Rd.tsum_fourier_dilate_besselKernelFamily_sq_le`). -/
noncomputable def besselOverlap (a : ℝ) (N : ℕ) (σ : ℝ) (ωhat : 𝓢(V, ℂ)) : ℝ≥0∞ :=
  (N + 1) * ENNReal.ofReal (besselSymbolBound a (2 ^ N * a) σ *
    SchwartzMap.seminorm ℝ 0 0 ωhat) ^ 2

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The overlap of the dilated Bessel kernels is finite. -/
theorem besselOverlap_ne_top (a : ℝ) (N : ℕ) (σ : ℝ) (ωhat : 𝓢(V, ℂ)) :
    besselOverlap a N σ ωhat ≠ ∞ :=
  ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

/-- **At most `N + 1` dilated Bessel kernels see a frequency**: if `ω̂` vanishes outside the
annulus `{a ≤ ‖ζ‖ ≤ 2^N a}`, `a > 0`, and `i₀` is the least index with `‖ξ‖ ≤ 2^{i₀+N} a`, then
`𝓕(K_j)_{2^j}(ξ) ≠ 0` forces `i₀ ≤ j ≤ i₀ + N` (`Nat.le_add_of_dyadic_annulus`). -/
theorem mem_Icc_of_fourier_dilate_besselKernelFamily_ne_zero {ωhat : 𝓢(V, ℂ)} {a : ℝ} {N : ℕ}
    (ha : 0 < a) (hω : ∀ ζ, ωhat ζ ≠ 0 → a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 2 ^ N * a) {σ : ℝ} {ξ : V} {i₀ j : ℕ}
    (hi₀ : ‖ξ‖ ≤ 2 ^ i₀ * (2 ^ N * a)) (hmin : ∀ i < i₀, ¬ ‖ξ‖ ≤ 2 ^ i * (2 ^ N * a))
    (h : 𝓕 (dilate (2 ^ j) (besselKernelFamily ωhat σ j : V → ℂ)) ξ ≠ 0) :
    j ∈ Finset.Icc i₀ (i₀ + N) := by
  obtain ⟨h1, h2⟩ := mem_annulus_of_fourier_dilate_besselKernelFamily_ne_zero hω h
  rw [div_le_iff₀ (by positivity)] at h2
  have hlo : i₀ ≤ j := by
    by_contra hlt
    exact hmin j (not_le.1 hlt) (h2.trans_eq (by ring))
  have hi : ‖ξ‖ / 2 ^ i₀ ≤ 2 ^ N * a := by
    rw [div_le_iff₀ (by positivity)]
    exact hi₀.trans_eq (by ring)
  exact Finset.mem_Icc.2 ⟨hlo, Nat.le_add_of_dyadic_annulus ha h1 hi⟩

/-- **Overlap of the dilated Bessel kernels**: if `ω̂` vanishes outside the annulus
`{a ≤ ‖ζ‖ ≤ 2^N a}`, `a > 0`, then `∑_j |𝓕(K_j)_{2^j}(ξ)|² ≤ Rd.besselOverlap a N σ ω̂` for every
`ξ`: a nonzero term needs `‖ξ‖ / 2^j ∈ [a, 2^N a]`
(`Rd.mem_annulus_of_fourier_dilate_besselKernelFamily_ne_zero`), so at most `N + 1` terms are
nonzero (`ENNReal.tsum_le_of_dyadic_annulus`), each bounded by
`Rd.enorm_fourier_dilate_besselKernelFamily_le`. -/
theorem tsum_fourier_dilate_besselKernelFamily_sq_le {ωhat : 𝓢(V, ℂ)} {a : ℝ} {N : ℕ}
    (ha : 0 < a) (hω : ∀ ζ, ωhat ζ ≠ 0 → a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 2 ^ N * a) (σ : ℝ) (ξ : V) :
    ∑' j, ‖𝓕 (dilate (2 ^ j) (besselKernelFamily ωhat σ j : V → ℂ)) ξ‖ₑ ^ 2 ≤
      besselOverlap a N σ ωhat :=
  ENNReal.tsum_le_of_dyadic_annulus ha
    (fun j => by
      gcongr
      exact enorm_fourier_dilate_besselKernelFamily_le ha hω σ j ξ)
    fun j hj => mem_annulus_of_fourier_dilate_besselKernelFamily_ne_zero (σ := σ) (ξ := ξ) hω
      fun h => hj (by simp [h])

/-- **The dilated Bessel kernels form a Calderón–Zygmund family**: if `ω̂` is a Schwartz function
vanishing outside the annulus `{a ≤ ‖ζ‖ ≤ 2^N a}` with `a > 0`, then for every real `σ` the
family `j ↦ (K_j)_{2^j}`, `K_j = 𝓕⁻¹[(2^{-2j} + ‖ζ‖²)^{σ/2} ω̂]`, is a Calderón–Zygmund family
with the overlap `Rd.besselOverlap a N σ ω̂` and some finite Hörmander constant `H` (existential,
from the uniform Schwartz bounds of `Rd.exists_isUniformSchwartz_besselKernelFamily` and
`Rd.IsCZFamily.of_dilation`). -/
theorem exists_isCZFamily_besselKernelFamily {ωhat : 𝓢(V, ℂ)} {a : ℝ} {N : ℕ} (ha : 0 < a)
    (hω : ∀ ζ, ωhat ζ ≠ 0 → a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 2 ^ N * a) (σ : ℝ) :
    ∃ H : ℝ≥0∞, H ≠ ∞ ∧ IsCZFamily (fun j => dilate (2 ^ j) (besselKernelFamily ωhat σ j : V → ℂ))
      (besselOverlap a N σ ωhat) H := by
  obtain ⟨A, hA⟩ := exists_isUniformSchwartz_besselKernelFamily ha hω σ
  exact ⟨4 * familyHormanderConst V A,
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (familyHormanderConst_ne_top A),
    IsCZFamily.of_dilation hA (tsum_fourier_dilate_besselKernelFamily_sq_le ha hω σ)⟩

/-! ### Annuli of the Littlewood–Paley kernels -/

/-- `𝓕ψ_1` vanishes outside the annulus `{1 ≤ ‖ζ‖ ≤ 2^2 · 1}`. The bound is written as `2^2 · 1`
to match the hypothesis of `Rd.exists_isCZFamily_besselKernelFamily` with `a = 1`, `N = 2`. -/
theorem mem_annulus_of_fourier_psiOneS_ne_zero {ζ : V} (h : 𝓕 (psiOneS (V := V)) ζ ≠ 0) :
    1 ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 2 ^ 2 * 1 := by
  rw [fourier_psiOneS_apply] at h
  have h4 := norm_lt_of_fourier_psi_ne_zero h
  norm_num at h4 ⊢
  exact ⟨(one_lt_norm_of_fourier_psi_one_ne_zero h).le, h4.le⟩

/-- `𝓕(psiBase (j+1)) = 𝓕(Φ - δ_{1/2} Φ)` vanishes outside the annulus
`{1/2 ≤ ‖ζ‖ ≤ 2^2 · 1/2}`: `psiBase (j+1) = psiBase 1` and `ψ_1 = (psiBase 1)_2`, so
`𝓕(psiBase 1)(ζ) = 𝓕ψ_1(2ζ)` (`Rd.fourier_eq_fourier_dilate`) and `1 ≤ ‖2ζ‖ ≤ 4`. The bound is
written as `2^2 · 2⁻¹` to match the hypothesis of `Rd.exists_isCZFamily_besselKernelFamily` with
`a = 1/2`, `N = 2`. -/
theorem mem_annulus_of_fourier_psiBase_ne_zero {j : ℕ} {ζ : V}
    (h : 𝓕 (psiBase (V := V) (j + 1)) ζ ≠ 0) : 2⁻¹ ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 2 ^ 2 * 2⁻¹ := by
  change 𝓕 (psiBase (V := V) 1) ζ ≠ 0 at h
  have h' : 𝓕 (psiOneS (V := V)) ((2 : ℝ) • ζ) ≠ 0 := by
    rw [SchwartzMap.fourier_coe] at h ⊢
    rwa [psiOneS, coe_schwartzDilate, ← fourier_eq_fourier_dilate _ two_pos]
  obtain ⟨h1, h2⟩ := mem_annulus_of_fourier_psiOneS_ne_zero h'
  rw [norm_smul, Real.norm_two] at h1 h2
  constructor <;> linarith

/-- `𝓕(psiDualBase (j+2)) = 𝓕(δ_2 Φ - δ_{1/4} Φ)` vanishes outside the annulus
`{1/4 ≤ ‖ζ‖ ≤ 2^4 · 1/4}`: `psiDualBase (j+2) = psiDualBase 2` and
`psiDual_2 = (psiDualBase 2)_4`, whose Fourier transform vanishes outside `{1 < ‖ξ‖ < 16}`. The
bound is written as `2^4 · 4⁻¹` to match the hypothesis of
`Rd.exists_isCZFamily_besselKernelFamily` with `a = 1/4`, `N = 4`. -/
theorem mem_annulus_of_fourier_psiDualBase_ne_zero {j : ℕ} {ζ : V}
    (h : 𝓕 (psiDualBase (V := V) (j + 2)) ζ ≠ 0) : 4⁻¹ ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 2 ^ 4 * 4⁻¹ := by
  change 𝓕 (psiDualBase (V := V) 2) ζ ≠ 0 at h
  rw [SchwartzMap.fourier_coe, fourier_eq_fourier_dilate _ (pow_pos two_pos 2),
    dilate_psiDualBase] at h
  have h1 := lt_norm_of_fourier_psiDual_ne_zero (m := 0) h
  have h2 := norm_lt_of_fourier_psiDual_ne_zero h
  rw [norm_smul, Real.norm_of_nonneg (by positivity)] at h1 h2
  norm_num at h1 h2 ⊢
  constructor <;> linarith

end Rd
