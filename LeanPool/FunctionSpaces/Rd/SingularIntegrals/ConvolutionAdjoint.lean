/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.SingularIntegrals.DilationFamilies
public import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
public import LeanPool.FunctionSpaces.Rd.Sobolev.WeakDerivatives
public import LeanPool.FunctionSpaces.Analysis.Lp.Young

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The adjoint of a convolution and the transfer of derivatives

On a finite-dimensional real inner product space `V` with Lebesgue measure, `K ⋆ f` is the
convolution `(K ⋆ f)(x) = ∫ K(y) f(x - y) dy` (`Rd.conv`) and `K^∨(x) = K(-x)` the reflection
(`Rd.reflect`).

* **The adjoint identity** (`Rd.integral_conv_mul`): for integrable `K`, `f ∈ L_p`, `g ∈ L_q`
  with `1/p + 1/q = 1`, `p < ∞`, `∫ (K ⋆ f) g = ∫ f (K^∨ ⋆ g)`, by Fubini's theorem; the double
  integral converges absolutely by Young's and Hölder's inequalities
  (`Rd.integrable_kernel_mul_mul`). With conjugation it reads
  `∫ (K ⋆ f) conj g = ∫ f conj(K^* ⋆ g)` for the adjoint kernel `K^*(x) = conj K(-x)`
  (`Rd.integral_conv_mul_conj`).
* **Derivatives move to the Schwartz factor** (`Rd.integral_conv_iteratedLineDerivOp_mul`): for
  Schwartz functions `η`, `u` and `f ∈ L_p`, `1 ≤ p < ∞`,
  `∫ ((∂^w η) ⋆ f) u = (-1)^k ∫ (η ⋆ f) ∂^w u`, by the adjoint identity and integration by
  parts on the Schwartz space.
* **Reflected translates** (`Rd.shiftReflect`): the Schwartz function `y ↦ η(x - y)` tests
  `(η ⋆ f)(x) = ∫ η(x - y) f(y) dy`, and `∂^w` of it is `(-1)^k` times the reflected translate
  of `∂^w η` (`Rd.iteratedLineDerivOp_shiftReflect`).
* **Weak derivatives commute with convolution**: if `g ∈ L_r` is the weak derivative `∂^v f` of
  `f ∈ L_p` on `V`, `1 ≤ p, r ≤ ∞`, then `η ⋆ g = (∂^v η) ⋆ f` at every point
  (`Rd.conv_eq_conv_iteratedLineDerivOp`); locally, if `∂^v f = g` weakly on an open set `Ω`
  and `η` has compact support with `x - supp η ⊆ Ω`, then `(η ⋆ g)(x) = ((∂^v η) ⋆ f)(x)`
  (`Rd.conv_eq_conv_iteratedLineDerivOp_of_hasWeakLineDeriv`); and
  `∂^v (η ⋆ f) = (∂^v η) ⋆ f` weakly for
  `f ∈ L_p`, `1 ≤ p < ∞` (`Rd.hasWeakLineDeriv_conv`); for the operators of `Rd.convLp`,
  `η ⋆ g = ∂^v (η ⋆ f)` weakly (`Rd.hasWeakLineDeriv_convLp`).
-/

@[expose] public section

open MeasureTheory TopologicalSpace
open scoped ENNReal SchwartzMap FourierTransform LineDeriv ComplexConjugate

namespace SchwartzMap

/-! ### Translates of Schwartz functions -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Iterated derivatives commute with translations: `∂^w (η(· - y)) = (∂^w η)(· - y)`. -/
theorem iteratedLineDerivOp_compSubConstCLM {k : ℕ} (η : 𝓢(E, ℂ)) (y : E) (w : Fin k → E) :
    ∂^{w} (η.compSubConstCLM ℂ y) = (∂^{w} η).compSubConstCLM ℂ y := by
  induction k generalizing η with
  | zero => rfl
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left, ih,
      lineDerivOp_compSubConstCLM]

end SchwartzMap

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Reflection -/

/-- The **reflection** `K^∨(x) = K(-x)` of a function `K : V → ℂ`. -/
def reflect (K : V → ℂ) (x : V) : ℂ := K (-x)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The values of the reflection: `K^∨(x) = K(-x)`. -/
@[simp]
theorem reflect_apply (K : V → ℂ) (x : V) : reflect K x = K (-x) :=
  rfl

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The reflection is an involution. -/
@[simp]
theorem reflect_reflect (K : V → ℂ) : reflect (reflect K) = K := by
  funext x
  simp

/-- The reflection of an integrable function is integrable (Lebesgue measure is invariant under
`x ↦ -x`, Mathlib's `Integrable.comp_neg`). -/
theorem integrable_reflect {K : V → ℂ} (hK : Integrable K) : Integrable (reflect K) :=
  hK.comp_neg

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The reflection of a continuous function is continuous. -/
theorem continuous_reflect {K : V → ℂ} (hK : Continuous K) : Continuous (reflect K) :=
  hK.comp continuous_neg

/-- **Fourier transform of the reflection**: `𝓕(K^∨)(ξ) = 𝓕K(-ξ)` for every function `K`, from
Mathlib's `Real.fourierInv_eq_fourier_comp_neg` and `Real.fourierInv_eq_fourier_neg`. -/
theorem fourier_reflect (K : V → ℂ) (ξ : V) : 𝓕 (reflect K) ξ = 𝓕 K (-ξ) := by
  rw [show reflect K = fun x => K (-x) from rfl, ← Real.fourierInv_eq_fourier_comp_neg,
    Real.fourierInv_eq_fourier_neg]

/-! ### Convolution as an integral against translates -/

/-- **Convolution with the variable in the kernel**: `(K ⋆ f)(x) = ∫ K(x - y) f(y) dy`, the
symmetric form of the convolution integral (Mathlib's `MeasureTheory.convolution_mul_swap`). -/
theorem conv_apply_eq_integral_sub (K f : V → ℂ) (x : V) :
    conv K f volume x = ∫ y, K (x - y) * f y := by
  rw [conv]
  exact convolution_mul_swap

/-- **Convolution with a reflected kernel**: `(K^∨ ⋆ u)(y) = ∫ K(z - y) u(z) dz`. -/
theorem conv_reflect_apply (K u : V → ℂ) (y : V) :
    conv (reflect K) u volume y = ∫ z, K (z - y) * u z := by
  simp [conv_apply_eq_integral_sub, reflect_apply, neg_sub]

/-! ### The adjoint identity -/

/-- **The double integrand of the adjoint identity is integrable**: for integrable `K`,
`f ∈ L_p` and `g ∈ L_q` with `1/p + 1/q = 1`, `p < ∞`, the function
`(x, y) ↦ K(x - y) f(y) g(x)` is integrable on `V × V`. For almost every `x` the inner integral
converges (Young's inequality, `MeasureTheory.ae_convolutionExistsAt`), and
`x ↦ ∫ |K(x - y)| |f(y)| dy |g(x)|` is the product of the convolution `|K| ⋆ |f| ∈ L_p` with
`|g| ∈ L_q`, integrable by Hölder's inequality (Mathlib's `MemLp.integrable_mul`). -/
theorem integrable_kernel_mul_mul {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞)
    {K f g : V → ℂ} (hK : Integrable K) (hf : MemLp f p) (hg : MemLp g q) :
    Integrable (Function.uncurry fun x y => K (x - y) * f y * g x) (volume.prod volume) := by
  have hp1 : 1 ≤ p := ENNReal.HolderConjugate.one_le p q
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x y => K (x - y) * f y * g x)
      (volume.prod volume) :=
    ((hK.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)).mul
      hf.aestronglyMeasurable.comp_snd).mul hg.aestronglyMeasurable.comp_fst
  refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
  · filter_upwards [ae_convolutionExistsAt hp1 hp hK hf] with x hx
    have h := (Integrable.comp_sub_left hx x).mul_const (g x)
    simpa only [ContinuousLinearMap.mul_apply', sub_sub_cancel, Function.uncurry_apply_pair]
      using h
  · have hH : MemLp (conv (fun z => ((‖K z‖ : ℝ) : ℂ)) (fun z => ((‖f z‖ : ℝ) : ℂ)) volume) p
        volume := memLp_conv hp1 hK.norm.ofReal hf.norm.ofReal
    refine ((hH.integrable_mul hg).norm).congr (ae_of_all _ fun x => ?_)
    have hHx : conv (fun z => ((‖K z‖ : ℝ) : ℂ)) (fun z => ((‖f z‖ : ℝ) : ℂ)) volume x =
        ((∫ y, ‖K (x - y)‖ * ‖f y‖ : ℝ) : ℂ) := by
      rw [conv_apply_eq_integral_sub]
      simp only [← Complex.ofReal_mul]
      exact integral_ofReal
    have hnn : 0 ≤ ∫ y, ‖K (x - y)‖ * ‖f y‖ :=
      integral_nonneg fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    simp only [Pi.mul_apply, Function.uncurry_apply_pair, norm_mul, hHx, Complex.norm_real,
      Real.norm_of_nonneg hnn, integral_mul_const]

/-- **The adjoint identity for convolutions**: for integrable `K`, `f ∈ L_p` and `g ∈ L_q` with
`1/p + 1/q = 1`, `p < ∞`, and the reflection `K^∨(x) = K(-x)`,
`∫ (K ⋆ f)(x) g(x) dx = ∫ f(y) (K^∨ ⋆ g)(y) dy`. Both sides are the integral of
`K(x - y) f(y) g(x)` over `V × V` (`Rd.integrable_kernel_mul_mul`, Fubini's theorem in the form
of Mathlib's `integral_integral_swap`). -/
theorem integral_conv_mul {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞) {K f g : V → ℂ}
    (hK : Integrable K) (hf : MemLp f p) (hg : MemLp g q) :
    ∫ x, conv K f volume x * g x = ∫ y, f y * conv (reflect K) g volume y := by
  calc ∫ x, conv K f volume x * g x = ∫ x, ∫ y, K (x - y) * f y * g x := by
        congr 1
        funext x
        rw [conv_apply_eq_integral_sub, ← integral_mul_const]
    _ = ∫ y, ∫ x, K (x - y) * f y * g x :=
        integral_integral_swap (integrable_kernel_mul_mul hp hK hf hg)
    _ = ∫ y, f y * conv (reflect K) g volume y := by
        congr 1
        funext y
        rw [conv_reflect_apply, ← integral_const_mul]
        congr 1
        funext x
        ring

/-- **Reflection and conjugation**: `(K^∨ ⋆ conj u)(x) = conj((K^* ⋆ u)(x))` at every point, for
the adjoint kernel `K^*(z) = conj K(-z)` and the reflection `K^∨(z) = K(-z)`; both sides are
`∫ K(y - x) conj u(y) dy`. -/
theorem conv_reflect_conj (K u : V → ℂ) (x : V) :
    conv (reflect K) (fun y => conj (u y)) volume x =
      conj (conv (fun z => conj (K (-z))) u volume x) := by
  rw [conv_apply_eq_integral_sub, conv_apply_eq_integral_sub, ← integral_conj]
  congr 1
  funext y
  rw [map_mul, Complex.conj_conj, reflect_apply]

/-- **The adjoint identity with conjugation**: for integrable `K`, `f ∈ L_p` and `g ∈ L_q` with
`1/p + 1/q = 1`, `p < ∞`, `∫ (K ⋆ f) conj g = ∫ f conj(K^* ⋆ g)` with the adjoint kernel
`K^*(z) = conj K(-z)` (`Rd.integral_conv_mul` for `conj g` and `Rd.conv_reflect_conj`). -/
theorem integral_conv_mul_conj {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞) {K f g : V → ℂ}
    (hK : Integrable K) (hf : MemLp f p) (hg : MemLp g q) :
    ∫ x, conv K f volume x * conj (g x) =
      ∫ y, f y * conj (conv (fun z => conj (K (-z))) g volume y) := by
  rw [integral_conv_mul (g := fun x => conj (g x)) hp hK hf hg.star]
  congr 1
  funext y
  rw [conv_reflect_conj]

/-! ### Translates and reflections of Schwartz functions -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Derivatives of a reflection**: `∂_v (η(-·)) = -(∂_v η)(-·)` (Mathlib's
`SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv` and `LineDeriv.lineDerivOp_left_neg`). -/
theorem lineDerivOp_schwartzReflect (η : 𝓢(V, ℂ)) (v : V) :
    ∂_{v} (schwartzReflect η) = -schwartzReflect (∂_{v} η) := by
  rw [schwartzReflect, SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_neg, Pi.neg_apply, id_eq, LineDeriv.lineDerivOp_left_neg, map_neg,
    schwartzReflect]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Iterated derivatives of a reflection**: `∂^w (η(-·)) = (-1)^k (∂^w η)(-·)` for
`w ∈ V^k`. -/
theorem iteratedLineDerivOp_schwartzReflect {k : ℕ} (η : 𝓢(V, ℂ)) (w : Fin k → V) :
    ∂^{w} (schwartzReflect η) = ((-1 : ℂ) ^ k) • schwartzReflect (∂^{w} η) := by
  induction k generalizing η with
  | zero => simp
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left, ih,
      LineDeriv.lineDerivOp_smul, lineDerivOp_schwartzReflect, pow_succ, mul_neg_one, neg_smul,
      smul_neg]

/-- The **reflected translate** `y ↦ η(x - y)` of a Schwartz function `η`, the Schwartz function
that tests the convolution `(η ⋆ f)(x) = ∫ η(x - y) f(y) dy`. -/
noncomputable def shiftReflect (η : 𝓢(V, ℂ)) (x : V) : 𝓢(V, ℂ) :=
  (schwartzReflect η).compSubConstCLM ℂ x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The values of the reflected translate: `y ↦ η(x - y)`. -/
@[simp]
theorem shiftReflect_apply (η : 𝓢(V, ℂ)) (x y : V) : shiftReflect η x y = η (x - y) := by
  rw [shiftReflect, SchwartzMap.compSubConstCLM_apply, coe_schwartzReflect]
  simp only [neg_sub]

/-- **Convolution as a pairing**: `(η ⋆ f)(x) = ∫ η(x - y) f(y) dy` is the integral of `f`
against the reflected translate of `η`. -/
theorem conv_eq_integral_shiftReflect (η : 𝓢(V, ℂ)) (f : V → ℂ) (x : V) :
    conv η f volume x = ∫ y, shiftReflect η x y * f y := by
  simp only [conv_apply_eq_integral_sub, shiftReflect_apply]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Iterated derivatives of a reflected translate**: `∂^w` of `y ↦ η(x - y)` is `(-1)^k` times
`y ↦ (∂^w η)(x - y)`, for `w ∈ V^k`. -/
theorem iteratedLineDerivOp_shiftReflect {k : ℕ} (η : 𝓢(V, ℂ)) (x : V) (w : Fin k → V) :
    ∂^{w} (shiftReflect η x) = ((-1 : ℂ) ^ k) • shiftReflect (∂^{w} η) x := by
  rw [shiftReflect, SchwartzMap.iteratedLineDerivOp_compSubConstCLM,
    iteratedLineDerivOp_schwartzReflect,
    map_smul, shiftReflect]

/-! ### Derivatives move to the Schwartz factor -/

/-- **Integration by parts against a reflected kernel**: for Schwartz functions `η`, `u`,
`(∂_v η)^∨ ⋆ u = -(η^∨ ⋆ ∂_v u)` pointwise, by integration by parts on the Schwartz space
(Mathlib's `SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left`) applied to `η(· - y)` and
`u`. -/
theorem conv_reflect_lineDerivOp (η u : 𝓢(V, ℂ)) (v y : V) :
    conv (reflect (∂_{v} η : 𝓢(V, ℂ))) u volume y =
      -conv (reflect η) (∂_{v} u : 𝓢(V, ℂ)) volume y := by
  have h := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume)
    (η.compSubConstCLM ℂ y) u v
  rw [SchwartzMap.lineDerivOp_compSubConstCLM] at h
  simp only [SchwartzMap.compSubConstCLM_apply] at h
  rw [conv_reflect_apply, conv_reflect_apply, h, neg_neg]

/-- **A derivative moves from the kernel `η` to the Schwartz function `u`**: for Schwartz
functions `η`, `u`, `f ∈ L_p` with `1 ≤ p < ∞` and `v ∈ V`,
`∫ ((∂_v η) ⋆ f) u = -∫ (η ⋆ f) ∂_v u`. Both sides are pairings of `f` with reflected
convolutions (`Rd.integral_conv_mul`, with the conjugate exponent of `p` and Schwartz functions
in every `L_q`), and these agree up to the sign (`Rd.conv_reflect_lineDerivOp`). -/
theorem integral_conv_lineDerivOp_mul {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : V → ℂ}
    (hf : MemLp f p) (η u : 𝓢(V, ℂ)) (v : V) :
    ∫ x, conv (∂_{v} η : 𝓢(V, ℂ)) f volume x * u x =
      -∫ x, conv η f volume x * (∂_{v} u : 𝓢(V, ℂ)) x := by
  have := ENNReal.HolderConjugate.conjExponent hp1
  rw [integral_conv_mul (q := p.conjExponent) hp (∂_{v} η).integrable hf (u.memLp _),
    integral_conv_mul (q := p.conjExponent) hp η.integrable hf ((∂_{v} u).memLp _),
    ← integral_neg]
  congr 1
  funext y
  rw [conv_reflect_lineDerivOp, mul_neg]

/-- **Iterated derivatives move from the kernel `η` to the Schwartz function `u`**: for Schwartz
functions `η`, `u`, `f ∈ L_p` with `1 ≤ p < ∞` and `w ∈ V^k`,
`∫ ((∂^w η) ⋆ f) u = (-1)^k ∫ (η ⋆ f) ∂^w u`, by induction on `k` from
`Rd.integral_conv_lineDerivOp_mul`. -/
theorem integral_conv_iteratedLineDerivOp_mul {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : V → ℂ} (hf : MemLp f p) (η u : 𝓢(V, ℂ)) {k : ℕ} (w : Fin k → V) :
    ∫ x, conv (∂^{w} η : 𝓢(V, ℂ)) f volume x * u x =
      (-1 : ℂ) ^ k * ∫ x, conv η f volume x * (∂^{w} u : 𝓢(V, ℂ)) x := by
  induction k generalizing η u with
  | zero => simp
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left w η, integral_conv_lineDerivOp_mul hp1 hp hf,
      ih, LineDeriv.iteratedLineDerivOp_succ_left w u,
      SchwartzMap.lineDerivOp_iteratedLineDerivOp_comm, pow_succ]
    ring

/-! ### Weak derivatives and convolution -/

/-- **Weak derivatives commute with convolution**: if `g ∈ L_r(V)` is the weak derivative
`∂^v f` of `f ∈ L_p(V)` on `V`, `1 ≤ p, r ≤ ∞`, then `η ⋆ g = (∂^v η) ⋆ f` at every point, for
every Schwartz function `η`. The value `(η ⋆ g)(x)` is `g` tested with `y ↦ η(x - y)`; the
tempered derivative moves to this Schwartz function with the sign `(-1)^k`
(`TemperedDistribution.iteratedLineDerivOp_apply_apply`), which cancels against the sign of
`Rd.iteratedLineDerivOp_shiftReflect`. -/
theorem conv_eq_conv_iteratedLineDerivOp {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] {k : ℕ}
    {v : Fin k → V} {f : Lp ℂ p (volume : Measure V)} {g : Lp ℂ r (volume : Measure V)}
    (h : HasWeakLineDeriv ⊤ v f g) (η : 𝓢(V, ℂ)) (x : V) :
    conv η g volume x = conv (∂^{v} η : 𝓢(V, ℂ)) f volume x := by
  have h' := DFunLike.congr_fun (hasWeakLineDeriv_top_iff.1 h) (shiftReflect η x)
  rw [TemperedDistribution.iteratedLineDerivOp_apply_apply, iteratedLineDerivOp_shiftReflect,
    smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply] at h'
  rw [conv_eq_integral_shiftReflect, conv_eq_integral_shiftReflect]
  simpa only [smul_eq_mul] using h'.symm

/-- **Weak derivatives commute with convolution, for functions**: if `g ∈ L_r(V)` is the weak
derivative `∂^v f` of `f ∈ L_p(V)` on `V`, `1 ≤ p, r ≤ ∞`, then `η ⋆ g = (∂^v η) ⋆ f` at every
point, for every Schwartz function `η` (`Rd.conv_eq_conv_iteratedLineDerivOp` for the classes
of `f` and `g`). -/
theorem conv_eq_conv_iteratedLineDerivOp_of_memLp {p r : ℝ≥0∞} (hp1 : 1 ≤ p) (hr1 : 1 ≤ r)
    {k : ℕ} {v : Fin k → V} {f g : V → ℂ} (hf : MemLp f p) (hg : MemLp g r)
    (h : HasWeakLineDeriv ⊤ v f g) (η : 𝓢(V, ℂ)) (x : V) :
    conv η g volume x = conv (∂^{v} η : 𝓢(V, ℂ)) f volume x := by
  have := Fact.mk hp1
  have := Fact.mk hr1
  have h' : HasWeakLineDeriv ⊤ v (hf.toLp f) (hg.toLp g) := by
    refine h.congr_ae ?_ ?_ <;> rw [volume_restrict_top]
    exacts [hf.coeFn_toLp.symm, hg.coeFn_toLp.symm]
  rw [conv_congr_ae hg.coeFn_toLp.symm, conv_congr_ae hf.coeFn_toLp.symm]
  exact conv_eq_conv_iteratedLineDerivOp h' η x

/-- **The weak derivative of a convolution**: for `f ∈ L_p(V)`, `1 ≤ p < ∞`, a Schwartz function
`η` and `v ∈ V^k`, `(∂^v η) ⋆ f` is the weak derivative `∂^v (η ⋆ f)` on `V`. Tested with `φ`,
this is `∫ ((∂^v η) ⋆ f) φ = (-1)^k ∫ (η ⋆ f) ∂^v φ`
(`Rd.integral_conv_iteratedLineDerivOp_mul`); both convolutions lie in `L_p` by Young's
inequality and are locally integrable. -/
theorem hasWeakLineDeriv_conv {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : V → ℂ}
    (hf : MemLp f p) (η : 𝓢(V, ℂ)) {k : ℕ} (v : Fin k → V) :
    HasWeakLineDeriv ⊤ v (conv η f volume) (conv (∂^{v} η : 𝓢(V, ℂ)) f volume) := by
  have hloc : ∀ G : 𝓢(V, ℂ),
      LocallyIntegrableOn (conv G f volume) ((⊤ : Opens V) : Set V) volume := fun G =>
    locallyIntegrableOn_of_memLp hp1 (by
      rw [volume_restrict_top]
      exact memLp_conv hp1 G.integrable hf)
  refine (hasWeakLineDeriv_iff_integral (hloc η) (hloc _)).2 fun φ => ?_
  have hA := integral_conv_iteratedLineDerivOp_mul hp1 hp hf η (testSchwartz φ) v
  rw [iteratedLineDerivOp_testSchwartz] at hA
  simp only [testSchwartz_apply] at hA
  simp only [Complex.real_smul]
  rw [Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  simpa only [mul_comm] using hA

/-- **The weak derivative of a convolution, in `L_p`**: for `f ∈ L_p(V)`, `1 ≤ p < ∞`, a
Schwartz function `η` and `v ∈ V^k`, the class of `(∂^v η) ⋆ f` in `L_p` is the weak derivative
`∂^v` of the class of `η ⋆ f` (`Rd.hasWeakLineDeriv_conv`). -/
theorem hasWeakLineDeriv_toLp_conv {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : V → ℂ}
    (hf : MemLp f p) (η : 𝓢(V, ℂ)) {k : ℕ} (v : Fin k → V) :
    HasWeakLineDeriv ⊤ v (memLp_conv hp1 η.integrable hf).toLp
      (memLp_conv hp1 (∂^{v} η : 𝓢(V, ℂ)).integrable hf).toLp := by
  refine (hasWeakLineDeriv_conv hp1 hp hf η v).congr_ae ?_ ?_ <;> rw [volume_restrict_top]
  exacts [(MemLp.coeFn_toLp _).symm, (MemLp.coeFn_toLp _).symm]

/-- **Weak derivatives commute with convolution by Schwartz functions, in `L_p`**: if `g = ∂^v f`
weakly on `V` for `f ∈ L_p(V)`, `g ∈ L_r(V)`, `1 ≤ p, r < ∞`, `v ∈ V^k`, and the kernel `K` is
a Schwartz function `η`, then `K ⋆ g = ∂^v (K ⋆ f)` weakly on `V`, for the operators `Rd.convLp`.
The weak derivative of `η ⋆ f` is `(∂^v η) ⋆ f` (`Rd.hasWeakLineDeriv_conv`), which equals
`η ⋆ g` at every point (`Rd.conv_eq_conv_iteratedLineDerivOp`). -/
theorem hasWeakLineDeriv_convLp {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] (hp : p ≠ ∞)
    (hr : r ≠ ∞) (η : 𝓢(V, ℂ)) {K : V → ℂ} (hK : Integrable K) (hηK : (η : V → ℂ) = K) {k : ℕ}
    {v : Fin k → V} {f : Lp ℂ p (volume : Measure V)} {g : Lp ℂ r (volume : Measure V)}
    (h : HasWeakLineDeriv ⊤ v f g) :
    HasWeakLineDeriv ⊤ v (convLp hp hK f) (convLp hr hK g) := by
  subst hηK
  refine (hasWeakLineDeriv_conv Fact.out hp (Lp.memLp f) η v).congr_ae ?_ ?_ <;>
    rw [volume_restrict_top]
  · exact (convLp_apply_ae hp _ f).symm
  · filter_upwards [convLp_apply_ae hr η.integrable g] with x hx
    rw [hx, conv_eq_conv_iteratedLineDerivOp h η x]

/-! ### Weak derivatives on open sets and convolution -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The reflected translate `y ↦ η(x - y)` is `η` composed with the homeomorphism `y ↦ x - y`. -/
theorem coe_shiftReflect_eq_comp (η : 𝓢(V, ℂ)) (x : V) :
    (shiftReflect η x : V → ℂ) = (η : V → ℂ) ∘ Homeomorph.subLeft x :=
  funext fun y => by simp

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The reflected translate of a compactly supported Schwartz function has compact support. -/
theorem hasCompactSupport_shiftReflect {η : 𝓢(V, ℂ)} (hη : HasCompactSupport (η : V → ℂ))
    (x : V) : HasCompactSupport (shiftReflect η x : V → ℂ) := by
  rw [coe_shiftReflect_eq_comp]
  exact hη.comp_homeomorph _

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The support of the reflected translate `y ↦ η(x - y)` lies in `S` if `x - y ∈ S` for every
`y` in the support of `η`. -/
theorem tsupport_shiftReflect_subset {η : 𝓢(V, ℂ)} {x : V} {S : Set V}
    (hS : ∀ y ∈ tsupport (η : V → ℂ), x - y ∈ S) : tsupport (shiftReflect η x : V → ℂ) ⊆ S := by
  rw [coe_shiftReflect_eq_comp, tsupport_comp_eq_preimage]
  intro z hz
  simpa using hS _ hz

/-- **Weak derivatives commute with convolution, locally**: if `g = ∂^v f` weakly on an open set
`Ω` and `η` is a compactly supported Schwartz function with `x - y ∈ Ω` for every `y` in the
support of `η`, then `(η ⋆ g)(x) = ((∂^v η) ⋆ f)(x)`: the reflected translate `y ↦ η(x - y)` is a
complex test function on `Ω` (`Rd.HasWeakLineDeriv.integral_mul_eq`,
`Rd.iteratedLineDerivOp_shiftReflect`). -/
theorem conv_eq_conv_iteratedLineDerivOp_of_hasWeakLineDeriv {Ω : Opens V} {k : ℕ}
    {v : Fin k → V} {f g : V → ℂ} (h : HasWeakLineDeriv Ω v f g) {η : 𝓢(V, ℂ)}
    (hη : HasCompactSupport (η : V → ℂ)) {x : V} (hx : ∀ y ∈ tsupport (η : V → ℂ), x - y ∈ Ω) :
    conv η g volume x = conv (∂^{v} η : 𝓢(V, ℂ)) f volume x := by
  rw [conv_eq_integral_shiftReflect, conv_eq_integral_shiftReflect,
    h.integral_mul_eq _ (hasCompactSupport_shiftReflect hη x) (tsupport_shiftReflect_subset hx),
    iteratedLineDerivOp_shiftReflect]
  simp only [smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul, ← mul_assoc, ← mul_pow]
  simp

end Rd
