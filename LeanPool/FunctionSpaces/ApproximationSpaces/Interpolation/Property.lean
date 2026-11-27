/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.Couple

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The interpolation property of the K-method

Bergh–Löfström, Theorems 3.1.2 and 3.11.2, give **exactness of exponent `θ`** in their
interpolation ranges for normed linear spaces and quasi-normed abelian groups, respectively.
Here the same bound holds for couples of extended-valued functions on additive groups and
arbitrary `θ` and `q`, including `q = 0`. If an additive map `T` satisfies
`N_i'(T a) ≤ M_i N_i(a)` with `0 < M_i < ∞`, then
`‖T u‖_{K,θ,q} ≤ M₀^(1-θ) M₁^θ ‖u‖_{K,θ,q}` (`InterpCouple.kMethodNorm_map_le`).

The proof has two steps.  The measure `dt/t` on `(0, ∞)` is invariant under every dilation
`t ↦ c t`, `c > 0` (`ApproximationScheme.measurePreserving_mul_left_kMethodMeasure`), so that
`Φ_{θ,q}(φ(c ·)) = c^θ Φ_{θ,q}(φ)` (`ApproximationScheme.phiFunctional_comp_mul`, Bergh–Löfström
(3.1.7)). The bound `K(t, T u) ≤ M₀ K((M₁/M₀) t, u)` (`InterpCouple.kFunctional_map_le`)
extends (3.1.8) to the extended-valued couples and endpoint scales. At positive scales, the
proof only needs additivity of `T` on decompositions into pieces of finite norm
(`InterpCouple.kFunctional_map_le_of_additiveOn`), as in the remark after Theorem 3.1.2.

Consequences: the discrete K-norms transform with the extra factor `2^(2ρθ)`
(`InterpCouple.discreteKMethodNorm_map_le`); couples with comparable norms have comparable
K-norms and the same interpolation spaces (`InterpCouple.kMethodNorm_le_of_le`,
`InterpCouple.memKMethod_congr`); the interpolation space of a retract is the image of the
interpolation space (`InterpCouple.memKMethod_iff_of_retract`,
`InterpCouple.memKMethod_iff_exists_map_eq`). This is the additive-couple version of the
real-interpolation part of Bergh–Löfström, Theorem 6.4.2, for compatible normed linear couples.
For bounded linear maps `T : X → X'`, `S : Y → Y'` with `T ι = ι' S`, the map `T` is bounded
between the spaces of `ApproximationSpaces.Interpolation.KMethod`
(`ApproximationScheme.kMethodNorm_map_le_of_comp_eq`, `ApproximationScheme.MemInterp.map`).
-/

@[expose] public section

open MeasureTheory Set Function
open scoped ENNReal

/-! ### Dilations of `dt/t` -/

namespace ApproximationScheme

variable {θ : ℝ} {q : ℝ≥0∞} {φ ψ : ℝ≥0∞ → ℝ≥0∞}

/-- The measure `dt/t` of a measurable set `s` is `∫ 1_{s ∩ (0, ∞)}(t) t⁻¹ dt`. -/
theorem kMethodMeasure_apply {s : Set ℝ} (hs : MeasurableSet s) :
    kMethodMeasure s = ∫⁻ t, (s ∩ Ioi 0).indicator (fun t => (ENNReal.ofReal t)⁻¹) t := by
  rw [kMethodMeasure, Measure.restrict_apply hs, withDensity_apply _ (hs.inter measurableSet_Ioi),
    lintegral_indicator (hs.inter measurableSet_Ioi)]
  rfl

/-- The density of `dt/t` under a dilation: for `c > 0`,
`1_{c⁻¹ s ∩ (0, ∞)}(t) t⁻¹ = c · 1_{s ∩ (0, ∞)}(c t) (c t)⁻¹`. -/
theorem indicator_preimage_mul_left_inv {c : ℝ} (hc : 0 < c) (s : Set ℝ) (t : ℝ) :
    (((c * ·) ⁻¹' s) ∩ Ioi 0).indicator (fun t => (ENNReal.ofReal t)⁻¹) t =
      ENNReal.ofReal c * (s ∩ Ioi 0).indicator (fun t => (ENNReal.ofReal t)⁻¹) (c * t) := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  by_cases ht : 0 < t
  · have hct : 0 < c * t := mul_pos hc ht
    by_cases hs : c * t ∈ s
    · rw [indicator_of_mem (show t ∈ (c * ·) ⁻¹' s ∩ Ioi 0 from ⟨hs, ht⟩),
        indicator_of_mem (show c * t ∈ s ∩ Ioi 0 from ⟨hs, hct⟩), ENNReal.ofReal_mul hc.le,
        ENNReal.mul_inv (Or.inl hc0) (Or.inl ENNReal.ofReal_ne_top), ← mul_assoc,
        ENNReal.mul_inv_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
    · rw [indicator_of_notMem (fun h : t ∈ (c * ·) ⁻¹' s ∩ Ioi 0 => hs h.1),
        indicator_of_notMem (fun h : c * t ∈ s ∩ Ioi 0 => hs h.1), mul_zero]
  · have hct : ¬ 0 < c * t := fun h => ht (pos_of_mul_pos_right h hc.le)
    rw [indicator_of_notMem (fun h : t ∈ (c * ·) ⁻¹' s ∩ Ioi 0 => ht h.2),
      indicator_of_notMem (fun h : c * t ∈ s ∩ Ioi 0 => hct h.2), mul_zero]

/-- **Dilations preserve `dt/t`**: for `c > 0`, `t ↦ c t` maps the measure `dt/t` on `(0, ∞)`
to itself, since Lebesgue measure scales by `c⁻¹` and the density `t⁻¹` by `c`. -/
theorem measurePreserving_mul_left_kMethodMeasure {c : ℝ} (hc : 0 < c) :
    MeasurePreserving (c * ·) kMethodMeasure kMethodMeasure := by
  have hm : Measurable (c * · : ℝ → ℝ) := measurable_const_mul c
  have hG : ∀ {s : Set ℝ}, MeasurableSet s →
      Measurable ((s ∩ Ioi 0).indicator fun t : ℝ => (ENNReal.ofReal t)⁻¹) := fun hs =>
    ENNReal.measurable_ofReal.inv.indicator (hs.inter measurableSet_Ioi)
  refine ⟨hm, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs, kMethodMeasure_apply (hm hs), kMethodMeasure_apply hs]
  simp_rw [indicator_preimage_mul_left_inv hc s]
  rw [lintegral_const_mul (ENNReal.ofReal c)
      (f := fun t => (s ∩ Ioi 0).indicator (fun t => (ENNReal.ofReal t)⁻¹) (c * t))
      ((hG hs).comp hm), ← lintegral_map (hG hs) hm,
    Real.map_volume_mul_left hc.ne', lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hc.le, abs_of_pos (inv_pos.2 hc), mul_inv_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]

/-- Almost every point for `dt/t` is positive, since `dt/t` is a restriction to `(0, ∞)`
(Mathlib's `MeasureTheory.ae_restrict_mem`). -/
theorem ae_pos_kMethodMeasure : ∀ᵐ t ∂kMethodMeasure, 0 < t := by
  rw [kMethodMeasure]
  exact ae_restrict_mem measurableSet_Ioi

/-- **Monotonicity of `Φ_{θ,q}`**: if `φ ≤ ψ` on `(0, ∞)` and `φ` is measurable, then
`Φ_{θ,q}(φ) ≤ Φ_{θ,q}(ψ)`. -/
theorem phiFunctional_mono (hφ : Measurable φ) (h : ∀ t, t ≠ 0 → t ≠ ∞ → φ t ≤ ψ t) :
    phiFunctional θ q φ ≤ phiFunctional θ q ψ := by
  rw [phiFunctional_eq, phiFunctional_eq]
  refine eLpNorm_mono_eNorm_ae (measurable_phiIntegrand_of_measurable hφ).aestronglyMeasurable
    (ae_pos_kMethodMeasure.mono fun t ht => ?_)
  simp only [eNorm_eq_self, phiIntegrand]
  gcongr
  exact h _ (ENNReal.ofReal_pos.2 ht).ne' ENNReal.ofReal_ne_top

/-- The integrand of `a φ` is `a` times the integrand of `φ`. -/
theorem phiIntegrand_const_mul (a : ℝ≥0∞) (φ : ℝ≥0∞ → ℝ≥0∞) :
    phiIntegrand θ (fun t => a * φ t) = fun t => a * phiIntegrand θ φ t := by
  funext t
  simp only [phiIntegrand]
  ring

/-- **Homogeneity of `Φ_{θ,q}`**: `Φ_{θ,q}(a φ) = a Φ_{θ,q}(φ)` for every `a ∈ [0, ∞]` and
measurable `φ`, by the homogeneity of `L_q` norms of `[0, ∞]`-valued functions
(Mathlib's `MeasureTheory.eLpNorm_const_mul_ennreal`). -/
theorem phiFunctional_const_mul (a : ℝ≥0∞) (hφ : Measurable φ) :
    phiFunctional θ q (fun t => a * φ t) = a * phiFunctional θ q φ := by
  rw [phiFunctional_eq, phiFunctional_eq, phiIntegrand_const_mul]
  exact eLpNorm_const_mul_ennreal (measurable_phiIntegrand_of_measurable hφ).aestronglyMeasurable

/-- The integrand of `φ(c ·)` at `t` is the integrand of `c^θ φ` at `c t`:
`t^(-θ) φ(c t) = (c t)^(-θ) c^θ φ(c t)`, for `0 < c < ∞`. -/
theorem phiIntegrand_comp_mul {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (t : ℝ) :
    phiIntegrand θ (fun s => φ (c * s)) t =
      phiIntegrand θ (fun s => c ^ θ * φ s) (c.toReal * t) := by
  have hct : ENNReal.ofReal (c.toReal * t) = c * ENNReal.ofReal t := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc]
  have h1 : c ^ (-θ) * c ^ θ = 1 := by
    rw [← ENNReal.rpow_add _ _ hc0 hc, neg_add_cancel, ENNReal.rpow_zero]
  rw [phiIntegrand, phiIntegrand, hct, ENNReal.mul_rpow_of_ne_top hc ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal t ^ (-θ) * φ (c * ENNReal.ofReal t)
      = (c ^ (-θ) * c ^ θ) * (ENNReal.ofReal t ^ (-θ) * φ (c * ENNReal.ofReal t)) := by
        rw [h1, one_mul]
    _ = _ := by ring

/-- **`Φ_{θ,q}` under a dilation** (Bergh–Löfström (3.1.7)): for `0 < c < ∞` and measurable `φ`,
`Φ_{θ,q}(φ(c ·)) = c^θ Φ_{θ,q}(φ)`, by the invariance of `dt/t` under `t ↦ c t`. -/
theorem phiFunctional_comp_mul {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (hφ : Measurable φ) :
    phiFunctional θ q (fun t => φ (c * t)) = c ^ θ * phiFunctional θ q φ := by
  have hc' : 0 < c.toReal := ENNReal.toReal_pos hc0 hc
  have hm : Measurable (phiIntegrand θ fun s => c ^ θ * φ s) :=
    measurable_phiIntegrand_of_measurable (hφ.const_mul _)
  calc phiFunctional θ q (fun t => φ (c * t))
      = eLpNorm ((phiIntegrand θ fun s => c ^ θ * φ s) ∘ (c.toReal * ·)) q kMethodMeasure := by
        rw [phiFunctional_eq]
        exact congrArg (eLpNorm · q kMethodMeasure) (funext (phiIntegrand_comp_mul hc0 hc))
    _ = phiFunctional θ q (fun s => c ^ θ * φ s) :=
        eLpNorm_comp_measurePreserving hm.aestronglyMeasurable
          (measurePreserving_mul_left_kMethodMeasure hc')
    _ = c ^ θ * phiFunctional θ q φ := phiFunctional_const_mul _ hφ

end ApproximationScheme

namespace InterpCouple

/-! ### The K-functional under a map -/

section Map

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V] {A : InterpCouple U}
  {B : InterpCouple V} {t M₀ M₁ : ℝ≥0∞} {θ ρ : ℝ} {q : ℝ≥0∞}

/-- **One decomposition under a map**: if `T u = T (u - b) + T b`,
`N₀'(T (u - b)) ≤ M₀ N₀(u - b)` and `N₁'(T b) ≤ M₁ N₁(b)`, then
`K'(t, T u) ≤ M₀ N₀(u - b) + t M₁ N₁(b)`. -/
theorem kFunctional_map_le_of_decomp {T : U → V} {u b : U} (hTu : T u = T (u - b) + T b)
    (h₀ : B.norm0 (T (u - b)) ≤ M₀ * A.norm0 (u - b)) (h₁ : B.norm1 (T b) ≤ M₁ * A.norm1 b) :
    B.kFunctional t (T u) ≤ M₀ * A.norm0 (u - b) + t * (M₁ * A.norm1 b) :=
  calc B.kFunctional t (T u) ≤ B.norm0 (T u - T b) + t * B.norm1 (T b) := kFunctional_le _ _
    _ = B.norm0 (T (u - b)) + t * B.norm1 (T b) := by rw [hTu, add_sub_cancel_right]
    _ ≤ M₀ * A.norm0 (u - b) + t * (M₁ * A.norm1 b) := by gcongr

/-- **The K-functional under an additive map**. This extends Bergh–Löfström (3.1.8) to
extended-valued couples and to endpoint scales. If `T : U → V` is additive with
`N₀'(T a) ≤ M₀ N₀(a)` and `N₁'(T a) ≤ M₁ N₁(a)` for every `a`, and `0 < M₀ < ∞`,
then `K'(t, T u) ≤ M₀ K((M₁/M₀) t, u)` for every `t` and `u`. -/
theorem kFunctional_map_le (T : U →+ V) (hM₀ : M₀ ≠ 0) (hM₀' : M₀ ≠ ∞)
    (h₀ : ∀ a, B.norm0 (T a) ≤ M₀ * A.norm0 a) (h₁ : ∀ a, B.norm1 (T a) ≤ M₁ * A.norm1 a)
    (t : ℝ≥0∞) (u : U) : B.kFunctional t (T u) ≤ M₀ * A.kFunctional (M₁ / M₀ * t) u := by
  rw [show M₀ * A.kFunctional (M₁ / M₀ * t) u =
      ⨅ b, M₀ * (A.norm0 (u - b) + M₁ / M₀ * t * A.norm1 b) from ENNReal.mul_iInf_of_ne hM₀ hM₀']
  refine le_iInf fun b => ?_
  rw [ENNReal.mul_add_div_mul_mul hM₀ hM₀']
  exact kFunctional_map_le_of_decomp (by rw [← map_add, sub_add_cancel]) (h₀ _) (h₁ _)

/-- **The K-functional under a map that is additive on pieces of finite norm**. The proof
uses the finite-piece argument as in the remark after Bergh–Löfström, Theorem 3.1.2.
If `T u = T (u - b) + T b` whenever `N₀(u - b) < ∞` and
`N₁(b) < ∞`, `N_i'(T a) ≤ M_i N_i(a)` for every `a`, `0 < M₀ < ∞`, `M₁ ≠ 0` and `t ≠ 0`, then
`K'(t, T u) ≤ M₀ K((M₁/M₀) t, u)`.  The decompositions with a piece of infinite norm give the
term `∞`. -/
theorem kFunctional_map_le_of_additiveOn {T : U → V} {u : U} (hM₀ : M₀ ≠ 0) (hM₀' : M₀ ≠ ∞)
    (hM₁ : M₁ ≠ 0) (ht : t ≠ 0)
    (hT : ∀ b, A.norm0 (u - b) ≠ ∞ → A.norm1 b ≠ ∞ → T u = T (u - b) + T b)
    (h₀ : ∀ a, B.norm0 (T a) ≤ M₀ * A.norm0 a) (h₁ : ∀ a, B.norm1 (T a) ≤ M₁ * A.norm1 a) :
    B.kFunctional t (T u) ≤ M₀ * A.kFunctional (M₁ / M₀ * t) u := by
  rw [show M₀ * A.kFunctional (M₁ / M₀ * t) u =
      ⨅ b, M₀ * (A.norm0 (u - b) + M₁ / M₀ * t * A.norm1 b) from ENNReal.mul_iInf_of_ne hM₀ hM₀']
  refine le_iInf fun b => ?_
  rw [ENNReal.mul_add_div_mul_mul hM₀ hM₀']
  rcases eq_or_ne (A.norm0 (u - b)) ∞ with h | h
  · rw [h, ENNReal.mul_top hM₀, top_add]
    exact le_top
  rcases eq_or_ne (A.norm1 b) ∞ with h' | h'
  · rw [h', ENNReal.mul_top hM₁, ENNReal.mul_top ht, add_top]
    exact le_top
  exact kFunctional_map_le_of_decomp (hT b h h') (h₀ _) (h₁ _)

/-! ### Exactness of exponent `θ` -/

/-- **The K-norm under a rescaled bound of the K-functional**: if `0 < M₀, M₁ < ∞` and
`K'(t, v) ≤ M₀ K((M₁/M₀) t, u)` for every `0 < t < ∞`, then
`‖v‖_{K,θ,q} ≤ M₀^(1-θ) M₁^θ ‖u‖_{K,θ,q}`, by the dilation formula for `Φ_{θ,q}`. -/
theorem kMethodNorm_le_of_kFunctional_le {v : V} {u : U} (hM₀ : M₀ ≠ 0) (hM₀' : M₀ ≠ ∞)
    (hM₁ : M₁ ≠ 0) (hM₁' : M₁ ≠ ∞)
    (h : ∀ t, t ≠ 0 → t ≠ ∞ → B.kFunctional t v ≤ M₀ * A.kFunctional (M₁ / M₀ * t) u) :
    B.kMethodNorm θ q v ≤ M₀ ^ (1 - θ) * M₁ ^ θ * A.kMethodNorm θ q u := by
  have hc0 : M₁ / M₀ ≠ 0 := ENNReal.div_ne_zero.2 ⟨hM₁, hM₀'⟩
  have hc : M₁ / M₀ ≠ ∞ := ENNReal.div_ne_top hM₁' hM₀
  have hK : Measurable fun t => A.kFunctional (M₁ / M₀ * t) u :=
    ((monotone_kFunctional u).comp fun _ _ hst => by gcongr).measurable
  calc B.kMethodNorm θ q v
      ≤ ApproximationScheme.phiFunctional θ q (fun t => M₀ * A.kFunctional (M₁ / M₀ * t) u) :=
        ApproximationScheme.phiFunctional_mono (monotone_kFunctional v).measurable h
    _ = M₀ * ((M₁ / M₀) ^ θ * A.kMethodNorm θ q u) := by
        rw [ApproximationScheme.phiFunctional_const_mul M₀ hK,
          ApproximationScheme.phiFunctional_comp_mul (φ := fun t => A.kFunctional t u) hc0 hc
            (monotone_kFunctional u).measurable]
        rfl
    _ = M₀ ^ (1 - θ) * M₁ ^ θ * A.kMethodNorm θ q u := by
        rw [← mul_assoc, ENNReal.mul_div_rpow_eq hM₀ hM₀']

/-- **The interpolation property of the K-method**. This extends the exactness estimate in
Bergh–Löfström, Theorems 3.1.2 and 3.11.2, to extended-valued couples and arbitrary parameters.
If `T : U → V` is additive with `N₀'(T a) ≤ M₀ N₀(a)`
and `N₁'(T a) ≤ M₁ N₁(a)` for every `a`, and `0 < M₀, M₁ < ∞`, then
`‖T u‖_{K,θ,q} ≤ M₀^(1-θ) M₁^θ ‖u‖_{K,θ,q}` for every `θ`, `q` and `u`.  Bounds with `M_i = 0`
can be enlarged. -/
theorem kMethodNorm_map_le (T : U →+ V) (hM₀ : M₀ ≠ 0) (hM₀' : M₀ ≠ ∞) (hM₁ : M₁ ≠ 0)
    (hM₁' : M₁ ≠ ∞) (h₀ : ∀ a, B.norm0 (T a) ≤ M₀ * A.norm0 a)
    (h₁ : ∀ a, B.norm1 (T a) ≤ M₁ * A.norm1 a) (u : U) :
    B.kMethodNorm θ q (T u) ≤ M₀ ^ (1 - θ) * M₁ ^ θ * A.kMethodNorm θ q u :=
  kMethodNorm_le_of_kFunctional_le hM₀ hM₀' hM₁ hM₁' fun t _ _ =>
    kFunctional_map_le T hM₀ hM₀' h₀ h₁ t u

/-- **The interpolation property for maps additive on pieces of finite norm**: if
`T u = T (u - b) + T b` whenever `N₀(u - b) < ∞` and `N₁(b) < ∞`, `N_i'(T a) ≤ M_i N_i(a)` for
every `a`, and `0 < M₀, M₁ < ∞`, then `‖T u‖_{K,θ,q} ≤ M₀^(1-θ) M₁^θ ‖u‖_{K,θ,q}`. -/
theorem kMethodNorm_map_le_of_additiveOn {T : U → V} {u : U} (hM₀ : M₀ ≠ 0) (hM₀' : M₀ ≠ ∞)
    (hM₁ : M₁ ≠ 0) (hM₁' : M₁ ≠ ∞)
    (hT : ∀ b, A.norm0 (u - b) ≠ ∞ → A.norm1 b ≠ ∞ → T u = T (u - b) + T b)
    (h₀ : ∀ a, B.norm0 (T a) ≤ M₀ * A.norm0 a) (h₁ : ∀ a, B.norm1 (T a) ≤ M₁ * A.norm1 a) :
    B.kMethodNorm θ q (T u) ≤ M₀ ^ (1 - θ) * M₁ ^ θ * A.kMethodNorm θ q u :=
  kMethodNorm_le_of_kFunctional_le hM₀ hM₀' hM₁ hM₁' fun _ ht _ =>
    kFunctional_map_le_of_additiveOn hM₀ hM₀' hM₁ ht hT h₀ h₁

/-- **Interpolation spaces are mapped into interpolation spaces**: if `T : U → V` is additive
with `N_i'(T a) ≤ M_i N_i(a)` for every `a` and finite `M₀, M₁`, then `T u ∈ (X₀', X₁')_{θ,q}`
for every `u ∈ (X₀, X₁)_{θ,q}`.  The bounds hold with the constants `max(1, M_i) ∈ (0, ∞)`
(Mathlib's `mul_le_mul_of_nonneg_right` and `le_max_right`), and `kMethodNorm_map_le` applies. -/
theorem MemKMethod.map (T : U →+ V) (hM₀ : M₀ ≠ ∞) (hM₁ : M₁ ≠ ∞)
    (h₀ : ∀ a, B.norm0 (T a) ≤ M₀ * A.norm0 a) (h₁ : ∀ a, B.norm1 (T a) ≤ M₁ * A.norm1 a)
    {u : U} (hu : A.MemKMethod θ q u) : B.MemKMethod θ q (T u) := by
  have hN₀ : max 1 M₀ ≠ ∞ := max_ne_top ENNReal.one_ne_top hM₀
  have hN₁ : max 1 M₁ ≠ ∞ := max_ne_top ENNReal.one_ne_top hM₁
  have hP₀ : max 1 M₀ ≠ 0 := (zero_lt_one.trans_le (le_max_left _ _)).ne'
  have hP₁ : max 1 M₁ ≠ 0 := (zero_lt_one.trans_le (le_max_left _ _)).ne'
  exact (kMethodNorm_map_le T hP₀ hN₀ hP₁ hN₁
    (fun a => (h₀ a).trans (mul_le_mul_of_nonneg_right (le_max_right 1 M₀) zero_le))
    (fun a => (h₁ a).trans (mul_le_mul_of_nonneg_right (le_max_right 1 M₁) zero_le)) u).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_mul_rpow_ne_top hP₀ hN₀ hP₁ hN₁ θ).lt_top hu)

/-- **The discrete K-norm under a bound of the continuous K-norms**: for `θ ≥ 0` and `ρ > 0`, if
`‖v‖_{K,θ,q} ≤ M ‖u‖_{K,θ,q}`, then the discrete K-norms on the grid `t = 2^(nρ)` satisfy
`‖v‖^ℤ_{θ,ρ,q} ≤ 2^(2ρθ) M ‖u‖^ℤ_{θ,ρ,q}`: the two comparisons of the discrete with the continuous
K-method lose `2^(ρθ)` each. -/
theorem discreteKMethodNorm_le_of_kMethodNorm_le {v : V} {u : U} {M : ℝ≥0∞} (hθ : 0 ≤ θ)
    (hρ : 0 < ρ) (h : B.kMethodNorm θ q v ≤ M * A.kMethodNorm θ q u) :
    B.discreteKMethodNorm θ ρ q v ≤ 2 ^ (2 * (ρ * θ)) * M * A.discreteKMethodNorm θ ρ q u := by
  have hL0 := ApproximationScheme.ofReal_mul_log_two_rpow_ne_zero hρ q
  have hLt : ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have h2 : (2 : ℝ≥0∞) ^ (-(ρ * θ)) ≠ 0 := (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'
  have h2t : (2 : ℝ≥0∞) ^ (-(ρ * θ)) ≠ ∞ := ENNReal.two_rpow_ne_top _
  have e : (2 : ℝ≥0∞) ^ (ρ * θ) = 2 ^ (-(ρ * θ)) * 2 ^ (2 * (ρ * θ)) := by
    rw [← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
    congr 1
    ring
  refine (ENNReal.mul_le_mul_iff_right (a := ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) *
    2 ^ (-(ρ * θ))) (mul_ne_zero hL0 h2) (ENNReal.mul_ne_top hLt h2t)).1 ?_
  calc ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) * 2 ^ (-(ρ * θ)) *
        B.discreteKMethodNorm θ ρ q v
      = ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) *
          (2 ^ (-(ρ * θ)) * B.discreteKMethodNorm θ ρ q v) := mul_assoc _ _ _
    _ ≤ M * A.kMethodNorm θ q u := (discreteKMethodNorm_le_kMethodNorm hθ hρ v).trans h
    _ ≤ M * (ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) *
          (2 ^ (ρ * θ) * A.discreteKMethodNorm θ ρ q u)) := by
        gcongr
        exact kMethodNorm_le_discreteKMethodNorm hθ hρ u
    _ = _ := by
        rw [e]
        ring

/-- **The interpolation property for the discrete K-method**: under the hypotheses of
`kMethodNorm_map_le`, for `θ ≥ 0` and `ρ > 0`, the discrete K-norms on the grid `t = 2^(nρ)`
satisfy `‖T u‖^ℤ_{θ,ρ,q} ≤ 2^(2ρθ) M₀^(1-θ) M₁^θ ‖u‖^ℤ_{θ,ρ,q}`. -/
theorem discreteKMethodNorm_map_le (T : U →+ V) (hM₀ : M₀ ≠ 0) (hM₀' : M₀ ≠ ∞) (hM₁ : M₁ ≠ 0)
    (hM₁' : M₁ ≠ ∞) (h₀ : ∀ a, B.norm0 (T a) ≤ M₀ * A.norm0 a)
    (h₁ : ∀ a, B.norm1 (T a) ≤ M₁ * A.norm1 a) (hθ : 0 ≤ θ) (hρ : 0 < ρ) (u : U) :
    B.discreteKMethodNorm θ ρ q (T u) ≤
      2 ^ (2 * (ρ * θ)) * (M₀ ^ (1 - θ) * M₁ ^ θ) * A.discreteKMethodNorm θ ρ q u :=
  discreteKMethodNorm_le_of_kMethodNorm_le hθ hρ (kMethodNorm_map_le T hM₀ hM₀' hM₁ hM₁' h₀ h₁ u)

/-! ### Retracts -/

/-- **The K-norm on a retract**: if `R : U → V` is additive with `N_i'(R a) ≤ M_i N_i(a)` and
`0 < M_i < ∞`, then for every map `E : V → U` with `R (E v) = v`,
`‖v‖_{K,θ,q} ≤ M₀^(1-θ) M₁^θ ‖E v‖_{K,θ,q}`; for additive `E` the reverse bound is
`kMethodNorm_map_le` for `E`. -/
theorem kMethodNorm_le_of_retract (R : U →+ V) (E : V → U) (hRE : ∀ v, R (E v) = v)
    (hM₀ : M₀ ≠ 0) (hM₀' : M₀ ≠ ∞) (hM₁ : M₁ ≠ 0) (hM₁' : M₁ ≠ ∞)
    (hR₀ : ∀ a, B.norm0 (R a) ≤ M₀ * A.norm0 a) (hR₁ : ∀ a, B.norm1 (R a) ≤ M₁ * A.norm1 a)
    (v : V) : B.kMethodNorm θ q v ≤ M₀ ^ (1 - θ) * M₁ ^ θ * A.kMethodNorm θ q (E v) := by
  simpa only [hRE] using kMethodNorm_map_le R hM₀ hM₀' hM₁ hM₁' hR₀ hR₁ (E v)

/-- **Interpolation of retracts on additive couples**. This is the real K-method
version of Bergh–Löfström, Theorem 6.4.2, with extended-valued norms and additive maps.
If `R : U → V` and `E : V → U` are additive with `R (E v) = v`, `N_i'(R a) ≤ M_i N_i(a)` and
`N_i(E v) ≤ L_i N_i'(v)` with finite `M_i, L_i`, then `v ∈ (X₀', X₁')_{θ,q}` if and only if
`E v ∈ (X₀, X₁)_{θ,q}`. -/
theorem memKMethod_iff_of_retract (R : U →+ V) (E : V →+ U) (hRE : ∀ v, R (E v) = v)
    {L₀ L₁ : ℝ≥0∞} (hM₀ : M₀ ≠ ∞) (hM₁ : M₁ ≠ ∞) (hL₀ : L₀ ≠ ∞) (hL₁ : L₁ ≠ ∞)
    (hR₀ : ∀ a, B.norm0 (R a) ≤ M₀ * A.norm0 a) (hR₁ : ∀ a, B.norm1 (R a) ≤ M₁ * A.norm1 a)
    (hE₀ : ∀ v, A.norm0 (E v) ≤ L₀ * B.norm0 v) (hE₁ : ∀ v, A.norm1 (E v) ≤ L₁ * B.norm1 v)
    {v : V} : B.MemKMethod θ q v ↔ A.MemKMethod θ q (E v) :=
  ⟨fun h => h.map E hL₀ hL₁ hE₀ hE₁,
    fun h => by simpa only [hRE] using h.map R hM₀ hM₁ hR₀ hR₁⟩

/-- **The K-method space of a retract is the image of the space**. Under
the hypotheses of `memKMethod_iff_of_retract`, `(X₀', X₁')_{θ,q} = R((X₀, X₁)_{θ,q})`, that is,
`v ∈ (X₀', X₁')_{θ,q}` if and only if `v = R u` for some `u ∈ (X₀, X₁)_{θ,q}`. -/
theorem memKMethod_iff_exists_map_eq (R : U →+ V) (E : V →+ U) (hRE : ∀ v, R (E v) = v)
    {L₀ L₁ : ℝ≥0∞} (hM₀ : M₀ ≠ ∞) (hM₁ : M₁ ≠ ∞) (hL₀ : L₀ ≠ ∞) (hL₁ : L₁ ≠ ∞)
    (hR₀ : ∀ a, B.norm0 (R a) ≤ M₀ * A.norm0 a) (hR₁ : ∀ a, B.norm1 (R a) ≤ M₁ * A.norm1 a)
    (hE₀ : ∀ v, A.norm0 (E v) ≤ L₀ * B.norm0 v) (hE₁ : ∀ v, A.norm1 (E v) ≤ L₁ * B.norm1 v)
    {v : V} : B.MemKMethod θ q v ↔ ∃ u, A.MemKMethod θ q u ∧ R u = v :=
  ⟨fun h => ⟨E v, h.map E hL₀ hL₁ hE₀ hE₁, hRE v⟩,
    fun ⟨_, hu, huv⟩ => huv ▸ hu.map R hM₀ hM₁ hR₀ hR₁⟩

end Map

/-! ### Comparable couples -/

section Compare

variable {U : Type*} [AddCommGroup U] {A B : InterpCouple U} {c₀ c₁ c₀' c₁' : ℝ≥0∞} {θ : ℝ}
  {q : ℝ≥0∞}

/-- **Monotonicity of the K-method in the couple**: if `N₀' ≤ c₀ N₀` and `N₁' ≤ c₁ N₁` with
`0 < c₀, c₁ < ∞`, then `‖u‖'_{K,θ,q} ≤ c₀^(1-θ) c₁^θ ‖u‖_{K,θ,q}` (the identity map in
`kMethodNorm_map_le`). -/
theorem kMethodNorm_le_of_le (hc₀ : c₀ ≠ 0) (hc₀' : c₀ ≠ ∞) (hc₁ : c₁ ≠ 0) (hc₁' : c₁ ≠ ∞)
    (h₀ : ∀ a, B.norm0 a ≤ c₀ * A.norm0 a) (h₁ : ∀ a, B.norm1 a ≤ c₁ * A.norm1 a) (u : U) :
    B.kMethodNorm θ q u ≤ c₀ ^ (1 - θ) * c₁ ^ θ * A.kMethodNorm θ q u :=
  kMethodNorm_map_le (AddMonoidHom.id U) hc₀ hc₀' hc₁ hc₁' h₀ h₁ u

/-- **Smaller norms give larger interpolation spaces**: if `N₀' ≤ c₀ N₀` and `N₁' ≤ c₁ N₁` with
finite `c₀, c₁`, then `(X₀, X₁)_{θ,q} ⊆ (X₀', X₁')_{θ,q}`. -/
theorem MemKMethod.of_le (hc₀ : c₀ ≠ ∞) (hc₁ : c₁ ≠ ∞) (h₀ : ∀ a, B.norm0 a ≤ c₀ * A.norm0 a)
    (h₁ : ∀ a, B.norm1 a ≤ c₁ * A.norm1 a) {u : U} (hu : A.MemKMethod θ q u) :
    B.MemKMethod θ q u :=
  hu.map (AddMonoidHom.id U) hc₀ hc₁ h₀ h₁

/-- **Equivalent couples give the same interpolation spaces**: if `N₀' ≤ c₀ N₀`, `N₁' ≤ c₁ N₁`,
`N₀ ≤ c₀' N₀'` and `N₁ ≤ c₁' N₁'` with finite constants, then
`(X₀, X₁)_{θ,q} = (X₀', X₁')_{θ,q}`. -/
theorem memKMethod_congr (hc₀ : c₀ ≠ ∞) (hc₁ : c₁ ≠ ∞) (hc₀' : c₀' ≠ ∞) (hc₁' : c₁' ≠ ∞)
    (h₀ : ∀ a, B.norm0 a ≤ c₀ * A.norm0 a) (h₁ : ∀ a, B.norm1 a ≤ c₁ * A.norm1 a)
    (h₀' : ∀ a, A.norm0 a ≤ c₀' * B.norm0 a) (h₁' : ∀ a, A.norm1 a ≤ c₁' * B.norm1 a) {u : U} :
    A.MemKMethod θ q u ↔ B.MemKMethod θ q u :=
  ⟨MemKMethod.of_le hc₀ hc₁ h₀ h₁, MemKMethod.of_le hc₀' hc₁' h₀' h₁'⟩

end Compare

/-! ### Couples of bounded linear maps -/

section OfMap

variable {X Y X' Y' : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup X'] [NormedSpace ℝ X']
  [NormedAddCommGroup Y'] [NormedSpace ℝ Y'] {ι : Y →L[ℝ] X} {ι' : Y' →L[ℝ] X'}

/-- A bounded linear map `T : X → X'` satisfies `‖T f‖ ≤ ‖T‖ ‖f‖` for the first norms of
`ofMap ι` and `ofMap ι'`. -/
theorem norm0_ofMap_apply_le (T : X →L[ℝ] X') (f : X) :
    (ofMap ι').norm0 (T f) ≤ ‖T‖ₑ * (ofMap ι).norm0 f :=
  T.le_opENorm f

/-- **The quotient norms under compatible maps**: if `T ι = ι' S` and `‖S‖ ≤ M` with
`0 < M < ∞`, then `N₁'(T f) ≤ M N₁(f)`, since `ι y = f` gives `ι' (S y) = T f`. -/
theorem norm1_ofMap_apply_le {T : X →L[ℝ] X'} {S : Y →L[ℝ] Y'} (hTS : T.comp ι = ι'.comp S)
    {M : ℝ≥0∞} (hM0 : M ≠ 0) (hM : M ≠ ∞) (hS : ‖S‖ₑ ≤ M) (f : X) :
    (ofMap ι').norm1 (T f) ≤ M * (ofMap ι).norm1 f := by
  rw [ofMap_norm1 (ι := ι) f, ENNReal.mul_iInf_of_ne hM0 hM]
  refine le_iInf fun y => ?_
  obtain ⟨y, rfl⟩ := y
  refine (norm1_ofMap_le (y := S y) ?_).trans ((S.le_opENorm y).trans (by gcongr))
  rw [← ContinuousLinearMap.comp_apply ι' S, ← hTS, ContinuousLinearMap.comp_apply]

end OfMap

end InterpCouple

/-! ### The interpolation property for the spaces of a bounded linear map -/

namespace ApproximationScheme

variable {X Y X' Y' : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup X'] [NormedSpace ℝ X']
  [NormedAddCommGroup Y'] [NormedSpace ℝ Y'] {ι : Y →L[ℝ] X} {ι' : Y' →L[ℝ] X'}
  {θ ρ : ℝ} {q M₀ M₁ : ℝ≥0∞}

/-- **The interpolation property for the couples `(X, ι(Y))`**: if `T : X → X'` and
`S : Y → Y'` are bounded linear maps with `T ι = ι' S`, `‖T‖ ≤ M₀`, `‖S‖ ≤ M₁` and
`0 < M₀, M₁ < ∞`, then `‖T f‖_{K,θ,q} ≤ M₀^(1-θ) M₁^θ ‖f‖_{K,θ,q}`. -/
theorem kMethodNorm_map_le_of_comp_eq (T : X →L[ℝ] X') (S : Y →L[ℝ] Y')
    (hTS : T.comp ι = ι'.comp S) (h₀ : ‖T‖ₑ ≤ M₀) (h₁ : ‖S‖ₑ ≤ M₁) (hM₀ : M₀ ≠ 0)
    (hM₀' : M₀ ≠ ∞) (hM₁ : M₁ ≠ 0) (hM₁' : M₁ ≠ ∞) (f : X) :
    kMethodNorm ι' θ q (T f) ≤ M₀ ^ (1 - θ) * M₁ ^ θ * kMethodNorm ι θ q f := by
  rw [← InterpCouple.kMethodNorm_ofMap, ← InterpCouple.kMethodNorm_ofMap]
  exact InterpCouple.kMethodNorm_map_le (T : X →+ X') hM₀ hM₀' hM₁ hM₁'
    (fun a => (InterpCouple.norm0_ofMap_apply_le T a).trans (by gcongr))
    (InterpCouple.norm1_ofMap_apply_le hTS hM₁ hM₁' h₁) f

/-- **The interpolation property on the grid `2^(-kρ)`**: under the hypotheses of
`kMethodNorm_map_le_of_comp_eq`, for `θ ≥ 0`, `ρ > 0` and `q ≠ 0`,
`‖T f‖_{θ,q} ≤ c' M₀^(1-θ) M₁^θ c ‖f‖_{θ,q}` with `c = kMethodUpperConst θ ρ q`, finite for
`θ > 0` (`kMethodUpperConst_ne_top`), and `c' = kMethodLowerConst ι' θ ρ q`, finite for `ρ > 0`
(`kMethodLowerConst_ne_top`). -/
theorem interpNorm_map_le_of_comp_eq (T : X →L[ℝ] X') (S : Y →L[ℝ] Y')
    (hTS : T.comp ι = ι'.comp S) (h₀ : ‖T‖ₑ ≤ M₀) (h₁ : ‖S‖ₑ ≤ M₁) (hM₀ : M₀ ≠ 0)
    (hM₀' : M₀ ≠ ∞) (hM₁ : M₁ ≠ 0) (hM₁' : M₁ ≠ ∞) (hθ : 0 ≤ θ) (hρ : 0 < ρ) (hq : q ≠ 0)
    (f : X) : interpNorm ι' θ ρ q (T f) ≤ kMethodLowerConst ι' θ ρ q *
      (M₀ ^ (1 - θ) * M₁ ^ θ) * kMethodUpperConst θ ρ q * interpNorm ι θ ρ q f :=
  calc interpNorm ι' θ ρ q (T f) ≤ kMethodLowerConst ι' θ ρ q * kMethodNorm ι' θ q (T f) :=
        interpNorm_le_kMethodNorm hθ hρ hq (T f)
    _ ≤ kMethodLowerConst ι' θ ρ q * (M₀ ^ (1 - θ) * M₁ ^ θ *
          (kMethodUpperConst θ ρ q * interpNorm ι θ ρ q f)) := by
        gcongr
        exact (kMethodNorm_map_le_of_comp_eq T S hTS h₀ h₁ hM₀ hM₀' hM₁ hM₁' f).trans
          (by gcongr; exact kMethodNorm_le_interpNorm hθ hρ f)
    _ = _ := by ring

/-- **The spaces of the continuous K-method under compatible maps**: if `T : X → X'` and
`S : Y → Y'` are bounded linear maps with `T ι = ι' S`, then `T` maps `(X, Y)_{θ,q}` into
`(X', Y')_{θ,q}`. -/
theorem MemKMethod.map (T : X →L[ℝ] X') (S : Y →L[ℝ] Y') (hTS : T.comp ι = ι'.comp S) {f : X}
    (hf : MemKMethod ι θ q f) : MemKMethod ι' θ q (T f) :=
  InterpCouple.memKMethod_ofMap_iff.1 ((InterpCouple.memKMethod_ofMap_iff.2 hf).map (T : X →+ X')
    eNorm_ne_top (max_ne_top ENNReal.one_ne_top eNorm_ne_top) (InterpCouple.norm0_ofMap_apply_le T)
    (InterpCouple.norm1_ofMap_apply_le hTS (zero_lt_one.trans_le (le_max_left _ _)).ne'
      (max_ne_top ENNReal.one_ne_top eNorm_ne_top) (le_max_right _ _)))

/-- **The spaces of the discrete K-method under compatible maps**: if `T : X → X'` and
`S : Y → Y'` are bounded linear maps with `T ι = ι' S`, then for `θ > 0` and `ρ > 0` the map `T`
sends the space of the discrete K-method on the grid `2^(-kρ)` for `ι` into that for `ι'`. -/
theorem MemInterp.map (T : X →L[ℝ] X') (S : Y →L[ℝ] Y') (hTS : T.comp ι = ι'.comp S)
    (hθ : 0 < θ) (hρ : 0 < ρ) {f : X} (hf : MemInterp ι θ ρ q f) : MemInterp ι' θ ρ q (T f) :=
  (memInterp_iff_memKMethod hθ hρ).2 (((memInterp_iff_memKMethod hθ hρ).1 hf).map T S hTS)

end ApproximationScheme
