/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.LpWeakDerivatives
public import LeanPool.FunctionSpaces.Torus.PeriodicLift
public import LeanPool.FunctionSpaces.Rd.Sobolev.WeakDerivativeChangeOfVariables
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Weak derivatives on the torus as distributions of periodic lifts

A function `f` on `𝕋^d` lifts to the periodic function `f ∘ π` on `ℝ^d`, where
`π : ℝ^d → 𝕋^d` is the quotient map. For `f, g ∈ L_p(𝕋^d)`, `1 ≤ p ≤ ∞`, and directions
`v ∈ (ℝ^d)^k`, the weak derivative of `Torus.HasWeakLineDeriv` (the rule `ĝ(m) = σ_v(m) f̂(m)`)
is the distributional derivative of the lift: `g = ∂^v f` on the torus iff
`g ∘ π = ∂^v (f ∘ π)` in Mathlib's distributions `𝓓'(ℝ^d)`
(`Torus.hasWeakLineDeriv_iff_comp_proj`, `Rd.HasWeakLineDeriv ⊤`). The same holds for the
multi-index derivatives `∂^α` (`Torus.hasWeakDeriv_iff_comp_proj`), so `W^m_p(𝕋^d)` is described
through the lifts (`Torus.memSobolev_iff_comp_proj`).

* **The pairing** `h ↦ ∫ φ(x) h(π x) dx` with a test function `φ` on `ℝ^d` is a bounded linear
  functional on `L_p(𝕋^d)` (`Torus.periodicPairing`); on the character `e_m` it is the Fourier
  transform of `φ` at `-m`, and `∂^v φ` multiplies it by `(-1)^k σ_v(m)`.
* **From the torus to `ℝ^d`** (`Torus.HasWeakLineDeriv.comp_proj`): the integral identity
  `∫ φ (g ∘ π) = (-1)^k ∫ (∂^v φ) (f ∘ π)` holds for the Littlewood–Paley blocks, which are
  trigonometric polynomials, and passes to the limit of their partial sums.
* **From `ℝ^d` to the torus** (`Torus.HasWeakLineDeriv.of_comp_proj`): convolution with a
  compactly supported Schwartz kernel `η` moves the derivative onto `η`, so
  `η ⋆ g = (∂^v η) ⋆ f` on the torus; the modulated bump `η_m` with `𝓕η_m(m) = 1`
  (`Torus.modulatedBump`) reads off the coefficient at `m`.
* **Classical derivatives**: since the classical derivative of a `C^1` function on `ℝ^d` is its
  weak derivative (`FunctionSpaces.Rd.Sobolev.WeakDerivativeChangeOfVariables`), for `C^1` lifts
  the
  classes of the classical derivatives are the weak derivatives on the torus
  (`Torus.hasWeakLineDeriv_of_contDiff`, and `Torus.hasWeakLineDeriv_of_contDiff_chain` for a
  chain of derivatives of order `k`, whose coefficients multiply along the chain by
  `Fin.eq_prod_mul_of_succ_eq`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus Filter Topology TopologicalSpace Metric
open scoped ENNReal FourierTransform TorusHaar Real SchwartzMap LineDeriv Distributions

/-! ### A product along a chain -/

/-- **A product along a chain**: in a commutative monoid, if `a_{l+1} = c_l a_l` for every
`l < k`, then `a_k = (∏_{l<k} c_l) a_0`. -/
theorem Fin.eq_prod_mul_of_succ_eq {M : Type*} [CommMonoid M] {k : ℕ} (a : Fin (k + 1) → M)
    (c : Fin k → M) (h : ∀ l : Fin k, a l.succ = c l * a l.castSucc) :
    a (Fin.last k) = (∏ l, c l) * a 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (fun l => a l.castSucc) (fun l => c l.castSucc) fun l => by
      simpa only [Fin.succ_castSucc] using h l.castSucc
    rw [← Fin.succ_last, h (Fin.last k), ih', Fin.prod_univ_castSucc, Fin.castSucc_zero,
      mul_comm (∏ l : Fin k, c l.castSucc) (c (Fin.last k)), mul_assoc]

namespace Torus

variable {d : Type*} [Fintype d]

/-! ### The pairing of periodic lifts with test functions -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For a test function `φ` on `ℝ^d` and `h ∈ L_p(𝕋^d)`, `x ↦ φ(x) h(π x)` is integrable. -/
theorem integrable_mul_comp_proj (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ d)), ℝ))
    (h : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    Integrable (fun x => (φ x : ℂ) * h (proj x)) volume := by
  simpa only [Complex.real_smul, Function.comp_apply] using
    φ.integrable_smul ((locallyIntegrable_comp_proj_Lp h).locallyIntegrableOn _)

omit [Fact (1 ≤ p)] in
/-- **The pairing is bounded by the `L_1` norm**: if `|φ| ≤ M` and the support of `φ` lies in the
open ball `B(0, R)`, then `|∫ φ(x) h(π x) dx| ≤ M (2R + 2)^d ‖h‖_1` for `h ∈ L_p(𝕋^d)`, by
counting the period boxes that meet the ball (`Torus.setLIntegral_ball_comp_proj_le`). -/
theorem enorm_integral_mul_comp_proj_le (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ d)), ℝ)) {M R : ℝ}
    (hM : ∀ x, ‖φ x‖ ≤ M) (hR : tsupport φ ⊆ ball 0 R)
    (h : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ‖∫ x, (φ x : ℂ) * h (proj x)‖ₑ ≤
      ENNReal.ofReal M * ENNReal.ofReal (2 * R + 2) ^ Fintype.card d * eLpNorm h 1 volume := by
  calc ‖∫ x, (φ x : ℂ) * h (proj x)‖ₑ ≤ ∫⁻ x, ‖(φ x : ℂ) * h (proj x)‖ₑ :=
        eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ x in ball 0 R, ENNReal.ofReal M * ‖h (proj x)‖ₑ := by
        rw [← lintegral_indicator measurableSet_ball]
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ ball (0 : EuclideanSpace ℝ d) R
        · rw [Set.indicator_of_mem hx, eNorm_mul, ← ofReal_norm, Complex.norm_real]
          gcongr
          exact hM x
        · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport fun h' => hx (hR h'),
            Complex.ofReal_zero, zero_mul, eNorm_zero]
    _ = ENNReal.ofReal M * ∫⁻ x in ball 0 R, ‖h (proj x)‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal (2 * R + 2) ^ Fintype.card d * ∫⁻ t, ‖h t‖ₑ) := by
        gcongr
        exact setLIntegral_ball_comp_proj_le (fun t => ‖h t‖ₑ) 0 R
    _ = _ := by
        rw [mul_assoc, eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable h)]

/-- The pairing `h ↦ ∫ φ(x) h(π x) dx` has a bound `C ‖h‖_p` on `L_p(𝕋^d)`: a test function is
bounded and supported in a ball (`Torus.enorm_integral_mul_comp_proj_le`), and
`‖h‖_1 ≤ ‖h‖_p` on the probability space `𝕋^d`. -/
theorem exists_norm_integral_mul_comp_proj_le (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ d)), ℝ)) :
    ∃ C, ∀ h : Lp ℂ p (volume : Measure (UnitAddTorus d)),
      ‖∫ x, (φ x : ℂ) * h (proj x)‖ ≤ C * ‖h‖ := by
  obtain ⟨M, hM⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball 0
  refine ⟨(ENNReal.ofReal M * ENNReal.ofReal (2 * R + 2) ^ Fintype.card d).toReal, fun h => ?_⟩
  rw [← toReal_eNorm, ← toReal_eNorm h, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) eNorm_ne_top)
    ((enorm_integral_mul_comp_proj_le φ hM hR h).trans ?_)
  rw [Lp.eNorm_def]
  gcongr
  exact eLpNorm_le_eLpNorm_of_exponent_le Fact.out

/-- The pairing is additive in `h ∈ L_p(𝕋^d)`. -/
theorem integral_mul_comp_proj_add (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ d)), ℝ))
    (f g : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∫ x, (φ x : ℂ) * (f + g) (proj x) =
      (∫ x, (φ x : ℂ) * f (proj x)) + ∫ x, (φ x : ℂ) * g (proj x) := by
  rw [← integral_add (integrable_mul_comp_proj φ f) (integrable_mul_comp_proj φ g)]
  refine integral_congr_ae ((ae_comp_proj (Lp.coeFn_add f g)).mono fun x hx => ?_)
  simp only [hx, Pi.add_apply, mul_add]

omit [Fact (1 ≤ p)] in
/-- The pairing is homogeneous in `h ∈ L_p(𝕋^d)`. -/
theorem integral_mul_comp_proj_smul (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ d)), ℝ)) (c : ℂ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∫ x, (φ x : ℂ) * (c • f) (proj x) = c * ∫ x, (φ x : ℂ) * f (proj x) := by
  rw [← integral_const_mul]
  refine integral_congr_ae ((ae_comp_proj (Lp.coeFn_smul c f)).mono fun x hx => ?_)
  simp only [hx, Pi.smul_apply, smul_eq_mul]
  ring

variable (p) in
/-- The **periodic pairing** of a test function `φ` on `ℝ^d` with `L_p(𝕋^d)`, `1 ≤ p ≤ ∞`: the
bounded linear functional `h ↦ ∫ φ(x) h(π x) dx`, the lift `h ∘ π` as a distribution on `ℝ^d`
evaluated at `φ`. -/
noncomputable def periodicPairing (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ d)), ℝ)) :
    Lp ℂ p (volume : Measure (UnitAddTorus d)) →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun h => ∫ x, (φ x : ℂ) * h (proj x)
      map_add' := integral_mul_comp_proj_add φ
      map_smul' := integral_mul_comp_proj_smul φ }
    (exists_norm_integral_mul_comp_proj_le φ)

/-- The periodic pairing is the integral `∫ φ(x) h(π x) dx`. -/
theorem periodicPairing_apply (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ d)), ℝ))
    (h : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicPairing p φ h = ∫ x, (φ x : ℂ) * h (proj x) :=
  rfl

/-- **The pairing with a character** is a value of the Fourier transform:
`∫ φ(x) e_m(π x) dx = 𝓕φ(-m)`. -/
theorem periodicPairing_mFourierLp (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ d)), ℝ)) (m : d → ℤ) :
    periodicPairing p φ (mFourierLp p m) =
      𝓕 (Rd.testSchwartz φ : EuclideanSpace ℝ d → ℂ) (latticeVec (-m)) := by
  rw [periodicPairing_apply, ← integral_mul_mFourier_neg_proj]
  refine integral_congr_ae ((ae_comp_proj (coeFn_mFourierLp p m)).mono fun x hx => ?_)
  dsimp only
  rw [hx, ← mFourier_neg_neg m (proj x), Rd.testSchwartz_apply]

/-- **Derivatives of the test function on a character**: the pairing of `∂^v φ` with `e_m` is
`(-1)^k σ_v(m)` times the pairing of `φ`, since `𝓕(∂^v φ)(ξ) = ∏_l 2πi ⟪ξ, v_l⟫ 𝓕φ(ξ)` and
`σ_v(-m) = (-1)^k σ_v(m)`. -/
theorem periodicPairing_iteratedLineDerivOp_mFourierLp
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ d)), ℝ)) {k : ℕ} (v : Fin k → EuclideanSpace ℝ d)
    (m : d → ℤ) :
    periodicPairing p (∂^{v} φ) (mFourierLp p m) =
      (-1) ^ k * lineSymbol v m * periodicPairing p φ (mFourierLp p m) := by
  have h := SchwartzMap.fourier_iteratedLineDerivOp_apply (Rd.testSchwartz φ) v (latticeVec (-m))
  rw [Rd.iteratedLineDerivOp_testSchwartz] at h
  rw [periodicPairing_mFourierLp, periodicPairing_mFourierLp, ← SchwartzMap.fourier_coe, h,
    ← SchwartzMap.fourier_coe, smul_eq_mul]
  change lineSymbol v (-m) * _ = _
  rw [lineSymbol_neg]

/-! ### From the torus to `ℝ^d` -/

/-- **The integral identity for trigonometric polynomials**: if `a, b ∈ L_p(𝕋^d)` are
trigonometric polynomials of degree `< n` with `b = ∂^v a`, then
`∫ φ (b ∘ π) = (-1)^k ∫ (∂^v φ) (a ∘ π)` for every test function `φ` on `ℝ^d`. Both sides are
sums over the characters (`Torus.eq_sum_mFourierCoeff_of_mem_trigPolyLp`). -/
theorem periodicPairing_eq_of_mem_trigPolyLp {n k : ℕ} {v : Fin k → EuclideanSpace ℝ d}
    {a b : Lp ℂ p (volume : Measure (UnitAddTorus d))} (ha : a ∈ trigPolyLp p n)
    (hb : b ∈ trigPolyLp p n) (h : HasWeakLineDeriv v a b)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ d)), ℝ)) :
    periodicPairing p φ b = (-1) ^ k * periodicPairing p (∂^{v} φ) a := by
  rw [eq_sum_mFourierCoeff_of_mem_trigPolyLp ha, eq_sum_mFourierCoeff_of_mem_trigPolyLp hb,
    map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hsq : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, h m,
    periodicPairing_iteratedLineDerivOp_mFourierLp]
  linear_combination (-(lineSymbol v m * mFourierCoeff a m *
    periodicPairing p φ (mFourierLp p m))) * hsq

/-- **The integral identity for the Littlewood–Paley blocks**: if `g = ∂^v f` in `L_p(𝕋^d)`,
`1 ≤ p < ∞`, then `∫ φ (Δ_j g ∘ π) = (-1)^k ∫ (∂^v φ) (Δ_j f ∘ π)`, since `Δ_j g = ∂^v Δ_j f`
(`Torus.HasWeakLineDeriv.econvLp`) and both blocks are trigonometric polynomials
(`Torus.lpBlock_mem_trigPolyLp`). -/
theorem periodicPairing_lpBlock (hp : p ≠ ∞) {k : ℕ} {v : Fin k → EuclideanSpace ℝ d}
    {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))} (h : HasWeakLineDeriv v f g)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ d)), ℝ)) (j : ℕ) :
    periodicPairing p φ (lpBlock hp j g) =
      (-1) ^ k * periodicPairing p (∂^{v} φ) (lpBlock hp j f) :=
  periodicPairing_eq_of_mem_trigPolyLp (lpBlock_mem_trigPolyLp hp j f)
    (lpBlock_mem_trigPolyLp hp j g) (h.econvLp hp _) φ

/-- **The integral identity for the lifts**: if `g = ∂^v f` in `L_p(𝕋^d)`, `1 ≤ p < ∞`, then
`∫ φ (g ∘ π) = (-1)^k ∫ (∂^v φ) (f ∘ π)` for every test function `φ` on `ℝ^d`. The identity holds
for the partial sums `∑_{j<J} Δ_j` (`Torus.periodicPairing_lpBlock`), which converge to `f` and `g`
(`Torus.tendsto_sum_lpBlock`), and the pairings are continuous. -/
theorem HasWeakLineDeriv.periodicPairing_eq (hp : p ≠ ∞) {k : ℕ} {v : Fin k → EuclideanSpace ℝ d}
    {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))} (h : HasWeakLineDeriv v f g)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ d)), ℝ)) :
    periodicPairing p φ g = (-1) ^ k * periodicPairing p (∂^{v} φ) f := by
  have hg := ((periodicPairing p φ).continuous.tendsto g).comp (tendsto_sum_lpBlock hp g)
  have hf := (((periodicPairing p (∂^{v} φ)).continuous.tendsto f).comp
    (tendsto_sum_lpBlock hp f)).const_mul ((-1 : ℂ) ^ k)
  refine tendsto_nhds_unique hg (hf.congr fun J => ?_)
  simp only [Function.comp_apply, map_sum, Finset.mul_sum, periodicPairing_lpBlock hp h φ]

/-- **Weak derivatives on the torus are weak derivatives of the lifts**: if `g = ∂^v f` in
`L_p(𝕋^d)`, `1 ≤ p ≤ ∞`, then `g ∘ π = ∂^v (f ∘ π)` as distributions on `ℝ^d`. For `p < ∞` this is
`Torus.HasWeakLineDeriv.periodicPairing_eq`; every `p` reduces to `p = 1` through the inclusion
`L_p ⊆ L_1`, which keeps the classes of the lifts. -/
theorem HasWeakLineDeriv.comp_proj {k : ℕ} {v : Fin k → EuclideanSpace ℝ d}
    {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))} (h : HasWeakLineDeriv v f g) :
    Rd.HasWeakLineDeriv ⊤ v (⇑f ∘ proj) (⇑g ∘ proj) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hincl : ∀ (ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ d)), ℝ))
      (u : Lp ℂ p (volume : Measure (UnitAddTorus d))),
      periodicPairing 1 ψ (Lp.inclusionOfExponentLe (𝕜 := ℂ) volume hp1 u) =
        ∫ x, (ψ x : ℂ) * u (proj x) := fun ψ u =>
    integral_congr_ae ((ae_comp_proj (Lp.coeFn_inclusionOfExponentLe (𝕜 := ℂ) hp1 u)).mono
      fun x hx => by simp only [hx])
  refine (Rd.hasWeakLineDeriv_iff_integral
    ((locallyIntegrable_comp_proj_Lp f).locallyIntegrableOn _)
    ((locallyIntegrable_comp_proj_Lp g).locallyIntegrableOn _)).2 fun φ => ?_
  have h1 := (h.of_inclusion hp1).periodicPairing_eq ENNReal.one_ne_top φ
  rw [hincl, hincl] at h1
  simp only [Complex.real_smul, Function.comp_apply, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one]
  exact h1

/-! ### From `ℝ^d` to the torus -/

/-- **Weak derivatives of the lifts commute with convolution on the torus**: if
`g ∘ π = ∂^v (f ∘ π)` weakly on `ℝ^d` and `η` is a compactly supported Schwartz function, then
`η ⋆ g = (∂^v η) ⋆ f` at every point of the torus. At `π x` both sides are convolutions on `ℝ^d`
(`Torus.econv_proj`), equal by `Rd.conv_eq_conv_iteratedLineDerivOp_of_hasWeakLineDeriv`. -/
theorem econv_eq_of_comp_proj {k : ℕ} {v : Fin k → EuclideanSpace ℝ d}
    {f g : UnitAddTorus d → ℂ} (h : Rd.HasWeakLineDeriv ⊤ v (f ∘ proj) (g ∘ proj))
    {η : 𝓢(EuclideanSpace ℝ d, ℂ)} (hη : HasCompactSupport (η : EuclideanSpace ℝ d → ℂ)) :
    econv η g = econv (∂^{v} η : 𝓢(EuclideanSpace ℝ d, ℂ)) f := funext fun t => by
  obtain ⟨x, rfl, -⟩ := exists_proj_eq t
  rw [econv_proj, econv_proj]
  exact Rd.conv_eq_conv_iteratedLineDerivOp_of_hasWeakLineDeriv h hη fun y _ => by simp

/-- The **modulated bump** `η_m(x) = χ(x) e^{2πi ⟪x, m⟫}` for `m ∈ ℤ^d`, where `χ` is the
standard bump `Rd.LocalMeansBump.std` (smooth, supported in the unit ball, `∫ χ = 1`): a
compactly supported Schwartz function on `ℝ^d` with `𝓕η_m(m) = ∫ χ = 1`. -/
noncomputable def modulatedBump (m : d → ℤ) : 𝓢(EuclideanSpace ℝ d, ℂ) :=
  HasCompactSupport.toSchwartzMap
    (f := fun x => (Rd.LocalMeansBump.std (V := EuclideanSpace ℝ d)).toFun x *
      Complex.exp (↑(2 * π * inner ℝ x (latticeVec m)) * Complex.I))
    (Rd.LocalMeansBump.std (V := EuclideanSpace ℝ d)).hasCompactSupport.mul_right
    ((Rd.LocalMeansBump.std (V := EuclideanSpace ℝ d)).contDiff.mul
      (Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
        (contDiff_const.mul (contDiff_id.inner ℝ contDiff_const))).mul contDiff_const)))

/-- The values of the modulated bump: `η_m(x) = χ(x) e^{2πi ⟪x, m⟫}`. -/
theorem modulatedBump_apply (m : d → ℤ) (x : EuclideanSpace ℝ d) :
    modulatedBump m x = (Rd.LocalMeansBump.std (V := EuclideanSpace ℝ d)).toFun x *
      Complex.exp (↑(2 * π * inner ℝ x (latticeVec m)) * Complex.I) :=
  rfl

/-- The modulated bump has compact support. -/
theorem hasCompactSupport_modulatedBump (m : d → ℤ) :
    HasCompactSupport (modulatedBump m : EuclideanSpace ℝ d → ℂ) :=
  (Rd.LocalMeansBump.std (V := EuclideanSpace ℝ d)).hasCompactSupport.mul_right

/-- **The Fourier transform of the modulated bump at `m`** is `∫ χ = 1`: the modulation cancels
the character of the Fourier transform. -/
theorem fourier_modulatedBump (m : d → ℤ) :
    𝓕 (modulatedBump m : EuclideanSpace ℝ d → ℂ) (latticeVec m) = 1 := by
  rw [Real.fourier_eq']
  have h : ∀ x : EuclideanSpace ℝ d,
      Complex.exp (↑(-2 * π * inner ℝ x (latticeVec m)) * Complex.I) • modulatedBump m x =
        (Rd.LocalMeansBump.std (V := EuclideanSpace ℝ d)).toFun x := fun x => by
    rw [modulatedBump_apply, smul_eq_mul, mul_left_comm, ← Complex.exp_add]
    push_cast
    ring_nf
    rw [Complex.exp_zero, mul_one]
  exact (integral_congr_ae (Eventually.of_forall h)).trans
    (Rd.LocalMeansBump.std (V := EuclideanSpace ℝ d)).integral_eq_one

/-- **Weak derivatives of the lifts are weak derivatives on the torus**: if `f, g ∈ L_p(𝕋^d)`,
`1 ≤ p ≤ ∞`, and `g ∘ π = ∂^v (f ∘ π)` as distributions on `ℝ^d`, then `g = ∂^v f`. Convolution
with the modulated bump gives `η_m ⋆ g = (∂^v η_m) ⋆ f` (`Torus.econv_eq_of_comp_proj`); the
coefficients at `m` are `ĝ(m)` and `σ_v(m) f̂(m)`, since `𝓕η_m(m) = 1`. -/
theorem HasWeakLineDeriv.of_comp_proj {k : ℕ} {v : Fin k → EuclideanSpace ℝ d}
    {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (h : Rd.HasWeakLineDeriv ⊤ v (⇑f ∘ proj) (⇑g ∘ proj)) : HasWeakLineDeriv v f g := fun m => by
  have hc := congrArg (fun F => mFourierCoeff F m)
    (econv_eq_of_comp_proj h (hasCompactSupport_modulatedBump m))
  rw [mFourierCoeff_econv (modulatedBump m).integrable (Lp.stronglyMeasurable g).measurable
      ((Lp.memLp g).integrable Fact.out),
    mFourierCoeff_econv (∂^{v} (modulatedBump m)).integrable (Lp.stronglyMeasurable f).measurable
      ((Lp.memLp f).integrable Fact.out),
    ← SchwartzMap.fourier_coe (∂^{v} (modulatedBump m)),
    SchwartzMap.fourier_iteratedLineDerivOp_apply,
    SchwartzMap.fourier_coe, fourier_modulatedBump, smul_eq_mul, one_mul, mul_one] at hc
  exact hc

/-- **The torus derivative is the distributional derivative of the lift**: for
`f, g ∈ L_p(𝕋^d)`, `1 ≤ p ≤ ∞`, and directions `v ∈ (ℝ^d)^k`, `g = ∂^v f` (the rule
`ĝ(m) = σ_v(m) f̂(m)`) iff `g ∘ π = ∂^v (f ∘ π)` in `𝓓'(ℝ^d)`. -/
theorem hasWeakLineDeriv_iff_comp_proj {k : ℕ} {v : Fin k → EuclideanSpace ℝ d}
    {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    HasWeakLineDeriv v f g ↔ Rd.HasWeakLineDeriv ⊤ v (⇑f ∘ proj) (⇑g ∘ proj) :=
  ⟨HasWeakLineDeriv.comp_proj, HasWeakLineDeriv.of_comp_proj⟩

/-- **The multi-index derivative is the distributional derivative of the lift**: `g = ∂^α f` in
`L_p(𝕋^d)`, `1 ≤ p ≤ ∞`, iff `g ∘ π = ∂^α (f ∘ π)` in `𝓓'(ℝ^d)`, with `∂^α` along the coordinate
directions `Torus.coordDirs α`. -/
theorem hasWeakDeriv_iff_comp_proj [DecidableEq d] {α : d → ℕ}
    {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    HasWeakDeriv α f g ↔ Rd.HasWeakLineDeriv ⊤ (coordDirs α) (⇑f ∘ proj) (⇑g ∘ proj) := by
  rw [hasWeakDeriv_iff_hasWeakLineDeriv, hasWeakLineDeriv_iff_comp_proj]

/-- **`W^m_p(𝕋^d)` through the lifts**: `f ∈ W^m_p(𝕋^d)`, `1 ≤ p ≤ ∞`, iff for every order
`k ≤ m` and all directions `v ∈ (ℝ^d)^k` some `g ∈ L_p(𝕋^d)` has `g ∘ π = ∂^v (f ∘ π)` in
`𝓓'(ℝ^d)`. -/
theorem memSobolev_iff_comp_proj {m : ℕ} {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    MemSobolev m f ↔ ∀ k ≤ m, ∀ v : Fin k → EuclideanSpace ℝ d,
      ∃ g : Lp ℂ p (volume : Measure (UnitAddTorus d)),
        Rd.HasWeakLineDeriv ⊤ v (⇑f ∘ proj) (⇑g ∘ proj) := by
  simp only [memSobolev_iff_exists_hasWeakLineDeriv, hasWeakLineDeriv_iff_comp_proj]

/-! ### Classical derivatives -/

/-- **Classical derivatives are weak derivatives on the torus**: if the lift of `f ∈ L_p(𝕋^d)`,
`1 ≤ p ≤ ∞`, agrees almost everywhere with a `C^1` function `F` on `ℝ^d`, and the lift of
`g ∈ L_p(𝕋^d)` with its derivative `x ↦ DF(x) w`, then `g = ∂_w f`
(`Rd.hasWeakLineDeriv_of_contDiff`, `Torus.HasWeakLineDeriv.of_comp_proj`). -/
theorem hasWeakLineDeriv_of_contDiff {F : EuclideanSpace ℝ d → ℂ} (hF : ContDiff ℝ 1 F)
    (w : EuclideanSpace ℝ d) {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hf : ⇑f ∘ proj =ᵐ[volume] F) (hg : ⇑g ∘ proj =ᵐ[volume] fun x => fderiv ℝ F x w) :
    HasWeakLineDeriv (fun _ : Fin 1 => w) f g := by
  refine HasWeakLineDeriv.of_comp_proj ((Rd.hasWeakLineDeriv_of_contDiff hF ⊤ w).congr_ae ?_ ?_)
  · rw [Rd.volume_restrict_top]
    exact hf.symm
  · rw [Rd.volume_restrict_top]
    exact hg.symm

/-- **Classical derivatives of order `k`**: let `F_0, …, F_k` be functions on `ℝ^d` such that
`F_l` is `C^1` and `F_{l+1} = D F_l (·) v_l` for every `l < k`, and let `f_0, …, f_k ∈ L_p(𝕋^d)`,
`1 ≤ p ≤ ∞`, have lifts equal to `F_l` almost everywhere. Then `f_k = ∂^v f_0`: each step is
`Torus.hasWeakLineDeriv_of_contDiff`, and the symbols multiply. -/
theorem hasWeakLineDeriv_of_contDiff_chain {k : ℕ} (v : Fin k → EuclideanSpace ℝ d)
    {F : Fin (k + 1) → EuclideanSpace ℝ d → ℂ} (hF : ∀ l : Fin k, ContDiff ℝ 1 (F l.castSucc))
    (hstep : ∀ l : Fin k, F l.succ = fun x => fderiv ℝ (F l.castSucc) x (v l))
    {f : Fin (k + 1) → Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hf : ∀ l, ⇑(f l) ∘ proj =ᵐ[volume] F l) : HasWeakLineDeriv v (f 0) (f (Fin.last k)) :=
  fun m => Fin.eq_prod_mul_of_succ_eq (fun l => mFourierCoeff (f l) m)
    (fun l => 2 * π * Complex.I * (inner ℝ (latticeVec m) (v l) : ℂ)) fun l => by
      have h1 := hasWeakLineDeriv_of_contDiff (hF l) (v l) (hf l.castSucc)
        (by rw [← hstep l]; exact hf l.succ) m
      simpa only [lineSymbol, Finset.univ_unique, Finset.prod_singleton] using h1

end Torus
