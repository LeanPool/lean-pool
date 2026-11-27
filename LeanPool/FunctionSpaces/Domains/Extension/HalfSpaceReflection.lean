/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.WeakDerivativeChangeOfVariables
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Even reflection across a hyperplane

Let `e` be a unit vector of a finite-dimensional real inner product space `V`,
`H₊ = {y : ⟪y, e⟫ > 0}` the open half-space (`Rd.openHalfSpace`) and `σ y = y - 2⟪y, e⟫ e` the
reflection across `e^⊥` (`Rd.halfSpaceReflection`, Mathlib's `Submodule.reflection`), a linear
isometry that preserves Lebesgue measure.

* **Two general facts** (`Real.smoothTransition.exists_abs_deriv_le`,
  `MeasureTheory.locallyIntegrable_of_forall_integrableOn_ball`): the derivative of Mathlib's
  smooth step is bounded and vanishes outside `[0, 1]`, and a function integrable on every ball
  around a point is locally integrable.
* **The even reflection** (`Rd.evenReflection`): `E u = 1_{H₊} u + (1_{H₊} u) ∘ σ`, that is `u` on
  `H₊` and `u ∘ σ` on `σ(H₊)`, linear in `u` (`Rd.evenReflection_add`, `Rd.evenReflection_smul`),
  with `‖E u‖_{L_p(V)} ≤ 2 ‖u‖_{L_p(H₊)}` for `1 ≤ p` (`Rd.eLpNorm_evenReflection_le`).
* **Cutoffs near the hyperplane** (`Rd.halfSpaceCutoff`): `η_n(y) = s((n + 1)⟪y, e⟫ - 1)` with
  Mathlib's smooth step `s = Real.smoothTransition`; their derivatives have size `n + 1` on a
  strip of width `1/(n + 1)`.
* **Integration by parts on `H₊`** (`Rd.setIntegral_openHalfSpace_smul_add_eq`): for smooth
  compactly supported `χ_1`, `χ_2` with `|⟪w_1, e⟫ χ_1 + ⟪w_2, e⟫ χ_2| ≤ C ⟪y, e⟫` on `H₊`, weak
  derivatives `∂_{w_k} u` on `H₊` integrate by parts against them without a boundary term; the
  cutoffs and dominated convergence give the limit.
* **Weak derivatives of the even reflection** (`Rd.hasWeakLineDeriv_evenReflection`; Brezis 2011,
  Chapter 9): if `u` and its weak derivatives `h_i = ∂_{e_i} u` on `H₊` are integrable on the
  bounded parts of `H₊`, then `∂_v E u = 1_{H₊} ∑_i ⟪v, e_i⟫ h_i + (1_{H₊} ∑_i ⟪σ v, e_i⟫ h_i) ∘ σ`
  weakly on `V`.
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace Module Set Metric
open scoped ENNReal NNReal SchwartzMap LineDeriv Distributions

/-! ### The derivative of the smooth step, and local integrability from balls -/

namespace Real.smoothTransition

/-- The derivative of Mathlib's `Real.smoothTransition` vanishes for `x > 1`, where the function
is constantly `1`. -/
theorem deriv_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 :=
    eventually_of_mem (isOpen_Ioi.mem_nhds hx) fun y hy =>
      Real.smoothTransition.one_of_one_le (le_of_lt hy)
  rw [h.deriv_eq, deriv_const]

/-- The derivative of Mathlib's `Real.smoothTransition` vanishes for `x < 0`, where the function
is constantly `0`. -/
theorem deriv_eq_zero_of_neg {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 :=
    eventually_of_mem (isOpen_Iio.mem_nhds hx) fun y hy =>
      Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  rw [h.deriv_eq, deriv_const]

/-- **The derivative of `Real.smoothTransition` is bounded**: it is continuous and vanishes
outside `[0, 1]` (Mathlib's `Continuous.bounded_above_of_compact_support`). -/
theorem exists_abs_deriv_le : ∃ D : ℝ, 0 ≤ D ∧ ∀ x, |deriv Real.smoothTransition x| ≤ D := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hs : HasCompactSupport (deriv Real.smoothTransition) :=
    HasCompactSupport.intro isCompact_Icc fun x hx => by
      rcases not_and_or.1 (show ¬(0 ≤ x ∧ x ≤ 1) from hx) with h | h
      · exact deriv_eq_zero_of_neg (not_le.1 h)
      · exact deriv_eq_zero_of_one_lt (not_le.1 h)
  obtain ⟨D, hD⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨D, (abs_nonneg _).trans (hD 0), hD⟩

end Real.smoothTransition

namespace MeasureTheory

/-- **Local integrability from the balls**: a function integrable on every ball `B(x₀, R)` around
a fixed point `x₀` is locally integrable, since every point has the neighbourhood
`B(x₀, d(x, x₀) + 1)`. -/
theorem locallyIntegrable_of_forall_integrableOn_ball {X E : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup E] {f : X → E} (x₀ : X)
    (h : ∀ R, IntegrableOn f (ball x₀ R) μ) : LocallyIntegrable f μ := fun x =>
  ⟨ball x₀ (dist x x₀ + 1), isOpen_ball.mem_nhds (by simp), h _⟩

end MeasureTheory

namespace Rd

/-! ### The half-space, the reflection and the even reflection -/

section Reflection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (e : V)

/-- The **open half-space** `H₊ = {y : 0 < ⟪y, e⟫}`, an open set. -/
def openHalfSpace : Opens V :=
  ⟨{y | 0 < inner ℝ y e}, isOpen_lt continuous_const (continuous_id.inner continuous_const)⟩

variable {e} in
/-- Membership in the open half-space: `y ∈ H₊` iff `0 < ⟪y, e⟫`. -/
@[simp]
theorem mem_openHalfSpace {y : V} : y ∈ openHalfSpace e ↔ 0 < inner ℝ y e :=
  Iff.rfl

/-- The open half-space as a set. -/
theorem coe_openHalfSpace : (openHalfSpace e : Set V) = {y | 0 < inner ℝ y e} :=
  rfl

/-- The **reflection** `σ` across the hyperplane `e^⊥` (Mathlib's `Submodule.reflection` in
`(ℝ e)^⊥`), a linear isometry of `V`; for `‖e‖ = 1`, `σ y = y - 2⟪y, e⟫ e`
(`Rd.halfSpaceReflection_apply`). -/
noncomputable def halfSpaceReflection : V ≃ₗᵢ[ℝ] V :=
  (ℝ ∙ e)ᗮ.reflection

variable {e}

/-- **The reflection formula**: for a unit vector `e`, `σ y = y - 2⟪y, e⟫ e` (Mathlib's
`Submodule.reflection_orthogonal_apply` and `Submodule.reflection_singleton_apply`). -/
theorem halfSpaceReflection_apply (he : ‖e‖ = 1) (y : V) :
    halfSpaceReflection e y = y - (2 * inner ℝ y e) • e := by
  rw [halfSpaceReflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, he]
  simp only [RCLike.ofReal_real_eq_id, id, one_pow, div_one, real_inner_comm e y]
  module

/-- **The reflection reverses the height**: `⟪σ y, e⟫ = -⟪y, e⟫` for a unit vector `e`. -/
theorem inner_halfSpaceReflection (he : ‖e‖ = 1) (y : V) :
    inner ℝ (halfSpaceReflection e y) e = -inner ℝ y e := by
  rw [halfSpaceReflection_apply he, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, he]
  ring

/-- The reflection is an involution: `σ (σ y) = y` (Mathlib's
`Submodule.reflection_reflection`). -/
@[simp]
theorem halfSpaceReflection_halfSpaceReflection (y : V) :
    halfSpaceReflection e (halfSpaceReflection e y) = y :=
  Submodule.reflection_reflection _ y

/-- The reflection fixes the directions `w` with `⟪w, e⟫ = 0`. -/
theorem halfSpaceReflection_of_inner_eq_zero (he : ‖e‖ = 1) {w : V} (hw : inner ℝ w e = 0) :
    halfSpaceReflection e w = w := by
  rw [halfSpaceReflection_apply he, hw, mul_zero, zero_smul, sub_zero]

/-- The reflection maps `e` to `-e`. -/
theorem halfSpaceReflection_self (he : ‖e‖ = 1) : halfSpaceReflection e e = -e := by
  rw [halfSpaceReflection_apply he, real_inner_self_eq_norm_sq, he]
  rw [show (2 * (1 : ℝ) ^ 2) • e = e + e by rw [one_pow, mul_one, two_smul]]
  abel

/-- The reflection of a point of `H₊` lies outside `H₊`. -/
theorem halfSpaceReflection_notMem (he : ‖e‖ = 1) {y : V} (hy : y ∈ openHalfSpace e) :
    halfSpaceReflection e y ∉ openHalfSpace e := by
  rw [mem_openHalfSpace, inner_halfSpaceReflection he] at *
  linarith

/-- **The distance to the reflected point**: `‖y - σ y‖ = 2 |⟪y, e⟫|` for a unit vector `e`. -/
theorem norm_sub_halfSpaceReflection (he : ‖e‖ = 1) (y : V) :
    ‖y - halfSpaceReflection e y‖ = 2 * |inner ℝ y e| := by
  rw [halfSpaceReflection_apply he, sub_sub_cancel, norm_smul, he, mul_one, Real.norm_eq_abs,
    abs_mul, abs_two]

variable (e) in
/-- The **even reflection** of `u` across the hyperplane `e^⊥`:
`E u (y) = 1_{H₊} u (y) + 1_{H₊} u (σ y)`, that is `u` on `H₊`, `u ∘ σ` on `σ(H₊)` and `0` on
the hyperplane. -/
noncomputable def evenReflection (u : V → ℂ) (y : V) : ℂ :=
  (openHalfSpace e : Set V).indicator u y +
    (openHalfSpace e : Set V).indicator u (halfSpaceReflection e y)

/-- On `H₊` the even reflection of `u` is `u`. -/
theorem evenReflection_of_mem (he : ‖e‖ = 1) (u : V → ℂ) {y : V} (hy : y ∈ openHalfSpace e) :
    evenReflection e u y = u y := by
  rw [evenReflection, indicator_of_mem hy,
    indicator_of_notMem (halfSpaceReflection_notMem he hy), add_zero]

/-- On `σ(H₊)` the even reflection of `u` is `u ∘ σ`. -/
theorem evenReflection_of_reflection_mem (he : ‖e‖ = 1) (u : V → ℂ) {y : V}
    (hy : halfSpaceReflection e y ∈ openHalfSpace e) :
    evenReflection e u y = u (halfSpaceReflection e y) := by
  have hy' : y ∉ openHalfSpace e := by
    simpa using halfSpaceReflection_notMem he hy
  rw [evenReflection, indicator_of_notMem hy', indicator_of_mem hy, zero_add]

variable (e) in
/-- The even reflection is additive: `E(u + u') = E u + E u'`. -/
theorem evenReflection_add (u u' : V → ℂ) :
    evenReflection e (u + u') = evenReflection e u + evenReflection e u' := by
  funext y
  simp only [evenReflection, indicator_add', Pi.add_apply]
  ring

variable (e) in
/-- The even reflection is homogeneous: `E(c u) = c E u`. -/
theorem evenReflection_smul (c : ℂ) (u : V → ℂ) :
    evenReflection e (c • u) = c • evenReflection e u := by
  funext y
  simp only [evenReflection, Pi.smul_apply, smul_eq_mul]
  rw [show c • u = fun z => c • u z from rfl, indicator_const_smul]
  simp only [smul_eq_mul]
  ring

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

variable (e) in
/-- The reflection preserves the Lebesgue measure (Mathlib's
`LinearIsometryEquiv.measurePreserving`). -/
theorem measurePreserving_halfSpaceReflection :
    MeasurePreserving (halfSpaceReflection e) volume volume :=
  (halfSpaceReflection e).measurePreserving

end Reflection

/-! ### Cutoffs near the hyperplane -/

section Cutoff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable (e : V) in
/-- The **cutoffs near the hyperplane** `η_n(y) = s((n + 1)⟪y, e⟫ - 1)` with Mathlib's smooth
step `s = Real.smoothTransition`: `η_n = 0` where `⟪y, e⟫ ≤ 1/(n + 1)`, `η_n = 1` where
`⟪y, e⟫ ≥ 2/(n + 1)`, and `0 ≤ η_n ≤ 1`. -/
noncomputable def halfSpaceCutoff (n : ℕ) (y : V) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * inner ℝ y e - 1)

variable {e : V}

/-- The cutoffs `η_n` are smooth. -/
theorem contDiff_halfSpaceCutoff (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (halfSpaceCutoff e n) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)).sub contDiff_const)

/-- The cutoffs take values in `[0, 1]`. -/
theorem abs_halfSpaceCutoff_le (n : ℕ) (y : V) : |halfSpaceCutoff e n y| ≤ 1 := by
  rw [halfSpaceCutoff, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

/-- `η_n(y) = 0` where `⟪y, e⟫ ≤ 1/(n + 1)`. -/
theorem halfSpaceCutoff_eq_zero {n : ℕ} {y : V} (hy : inner ℝ y e ≤ 1 / ((n : ℝ) + 1)) :
    halfSpaceCutoff e n y = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have h := mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
  rw [mul_one_div_cancel (by positivity)] at h
  linarith

/-- The cutoffs vanish outside `H₊`. -/
theorem halfSpaceCutoff_eq_zero_of_notMem {n : ℕ} {y : V} (hy : y ∉ openHalfSpace e) :
    halfSpaceCutoff e n y = 0 :=
  halfSpaceCutoff_eq_zero ((not_lt.1 hy).trans (by positivity))

/-- **The closed support of `η_n` lies in `H₊`**: it lies in `{⟪y, e⟫ ≥ 1/(n + 1)}`. -/
theorem tsupport_halfSpaceCutoff_subset (n : ℕ) :
    tsupport (halfSpaceCutoff e n) ⊆ openHalfSpace e := by
  have hsub : tsupport (halfSpaceCutoff e n) ⊆ {y : V | 1 / ((n : ℝ) + 1) ≤ inner ℝ y e} :=
    closure_minimal (fun y hy => le_of_lt (not_le.1 fun h => hy (halfSpaceCutoff_eq_zero h)))
      (isClosed_le continuous_const (continuous_id.inner continuous_const))
  exact hsub.trans fun y hy => lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) hy

/-- **The cutoffs tend to `1` on `H₊`**: `η_n(y) = 1` as soon as `(n + 1)⟪y, e⟫ ≥ 2`. -/
theorem tendsto_halfSpaceCutoff {y : V} (hy : y ∈ openHalfSpace e) :
    Tendsto (fun n : ℕ => halfSpaceCutoff e n y) atTop (𝓝 1) := by
  rw [mem_openHalfSpace] at hy
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / inner ℝ y e)
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  refine (Real.smoothTransition.one_of_one_le ?_).symm
  have h1 : 2 / inner ℝ y e < (n : ℝ) + 1 := hN.trans_le (by exact_mod_cast hn.trans (by omega))
  rw [div_lt_iff₀ hy] at h1
  linarith

/-- **The derivative of the cutoff**:
`Dη_n(y) w = s'((n + 1)⟪y, e⟫ - 1) (n + 1) ⟪w, e⟫`. -/
theorem fderiv_halfSpaceCutoff_apply (n : ℕ) (y w : V) :
    fderiv ℝ (halfSpaceCutoff e n) y w =
      deriv Real.smoothTransition (((n : ℝ) + 1) * inner ℝ y e - 1) *
        (((n : ℝ) + 1) * inner ℝ w e) := by
  have hL : (fun y : V => inner ℝ y e) = innerSL ℝ e :=
    funext fun y => by rw [innerSL_apply_apply, real_inner_comm]
  have h1 : HasFDerivAt (fun y : V => inner ℝ y e) (innerSL ℝ e) y := by
    rw [hL]
    exact (innerSL ℝ e).hasFDerivAt
  have hA := (h1.const_mul ((n : ℝ) + 1)).sub_const 1
  have h := (((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
    ).comp_hasFDerivAt y hA
  rw [show halfSpaceCutoff e n = Real.smoothTransition ∘
    fun y : V => ((n : ℝ) + 1) * inner ℝ y e - 1 from rfl, h.fderiv]
  simp [innerSL_apply_apply, real_inner_comm]

/-- **The strip estimate**: if `|c(y)| ≤ C ⟪y, e⟫` at a point `y ∈ H₊`, then
`|s'((n + 1)⟪y, e⟫ - 1) (n + 1) c(y)| ≤ 2 D C` for a bound `D` of `|s'|`, since `s'` vanishes
unless `(n + 1)⟪y, e⟫ ≤ 2`. -/
theorem abs_deriv_smoothTransition_mul_le {D C c : ℝ}
    (hD : ∀ x, |deriv Real.smoothTransition x| ≤ D) {y : V} (hy : y ∈ openHalfSpace e)
    (hc : |c| ≤ C * inner ℝ y e) (n : ℕ) :
    |deriv Real.smoothTransition (((n : ℝ) + 1) * inner ℝ y e - 1) * (((n : ℝ) + 1) * c)| ≤
      2 * D * C := by
  rw [mem_openHalfSpace] at hy
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((abs_nonneg c).trans hc) hy
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  by_cases h2 : 1 < ((n : ℝ) + 1) * inner ℝ y e - 1
  · rw [Real.smoothTransition.deriv_eq_zero_of_one_lt h2, zero_mul, abs_zero]
    positivity
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hn]
  calc |deriv Real.smoothTransition (((n : ℝ) + 1) * inner ℝ y e - 1)| * (((n : ℝ) + 1) * |c|)
      ≤ D * (((n : ℝ) + 1) * (C * inner ℝ y e)) := by gcongr; exact hD _
    _ = D * C * (((n : ℝ) + 1) * inner ℝ y e) := by ring
    _ ≤ D * C * 2 := by gcongr; linarith
    _ = 2 * D * C := by ring

end Cutoff

/-! ### Integration by parts on the half-space -/

section IntegrationByParts

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {e : V}

/-- **Compactly supported multipliers**: for a measurable set `s`, if `b` is integrable on every
bounded part `s ∩ B(0, R)` of `s` and `c` is continuous with compact support, then `c b` is
integrable on `s`: `c` is bounded (Mathlib's `Continuous.bounded_above_of_compact_support`) and
vanishes outside some ball. -/
theorem integrableOn_smul_of_hasCompactSupport {s : Set V} (hs : MeasurableSet s) {c : V → ℝ}
    (hc : Continuous c) (hcc : HasCompactSupport c) {b : V → ℂ}
    (hb : ∀ R, IntegrableOn b (s ∩ ball 0 R)) : IntegrableOn (fun y => c y • b y) s := by
  obtain ⟨R, hR⟩ := hcc.isCompact.isBounded.subset_ball 0
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcc
  have h : IntegrableOn (fun y => c y • b y) (s ∩ ball 0 R) :=
    (hb R).bdd_smul C hc.aestronglyMeasurable (ae_of_all _ hC)
  refine h.of_forall_sdiff_eq_zero hs fun y hy => ?_
  have hy' : y ∉ tsupport c := fun h' => hy.2 ⟨hy.1, hR h'⟩
  rw [image_eq_zero_of_notMem_tsupport hy', zero_smul]

/-- **Multipliers supported in a set**: if moreover `c` vanishes outside the measurable set `s`,
then `c b` is integrable on `V` (`Rd.integrableOn_smul_of_hasCompactSupport`). -/
theorem integrable_smul_of_forall_notMem {s : Set V} (hs : MeasurableSet s) {c : V → ℝ}
    (hc : Continuous c) (hcc : HasCompactSupport c) (hcs : ∀ y ∉ s, c y = 0) {b : V → ℂ}
    (hb : ∀ R, IntegrableOn b (s ∩ ball 0 R)) : Integrable (fun y => c y • b y) :=
  (integrableOn_smul_of_hasCompactSupport hs hc hcc hb).integrable_of_forall_notMem_eq_zero
    fun y hy => by rw [hcs y hy, zero_smul]

/-- **The cutoffs in the limit**: for `F` integrable on `H₊`, `∫ η_n F → ∫_{H₊} F`, by dominated
convergence: `|η_n| ≤ 1`, `η_n → 1` on `H₊` and `η_n = 0` outside `H₊`. -/
theorem tendsto_integral_halfSpaceCutoff_smul {F : V → ℂ}
    (hF : IntegrableOn F (openHalfSpace e)) :
    Tendsto (fun n : ℕ => ∫ y, halfSpaceCutoff e n y • F y) atTop
      (𝓝 (∫ y in openHalfSpace e, F y)) := by
  have h0 : ∀ n : ℕ, ∫ y, halfSpaceCutoff e n y • F y =
      ∫ y in openHalfSpace e, halfSpaceCutoff e n y • F y := fun n =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [halfSpaceCutoff_eq_zero_of_notMem hy, zero_smul]).symm
  simp_rw [h0]
  refine tendsto_integral_of_dominated_convergence (fun y => ‖F y‖)
    (fun n => ((contDiff_halfSpaceCutoff n).continuous.aestronglyMeasurable).smul
      hF.aestronglyMeasurable) hF.norm (fun n => ae_of_all _ fun y => ?_) ?_
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_halfSpaceCutoff_le n y)
  · filter_upwards [ae_restrict_mem (openHalfSpace e).isOpen.measurableSet] with y hy
    simpa using (tendsto_halfSpaceCutoff hy).smul_const (F y)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The derivative terms of the cutoffs vanish outside the bounded part `H₊ ∩ B(0, R)` of `H₊`
for every multiplier `c` vanishing outside `B(0, R)`, since `s' = 0` on `(-∞, 0)`. -/
theorem deriv_smoothTransition_mul_eq_zero {c : V → ℝ} {R : ℝ} (hR : tsupport c ⊆ ball 0 R)
    (n : ℕ) {y : V} (hy : y ∉ (openHalfSpace e : Set V) ∩ ball 0 R) :
    deriv Real.smoothTransition (((n : ℝ) + 1) * inner ℝ y e - 1) * (((n : ℝ) + 1) * c y) = 0 := by
  by_cases hyH : y ∈ openHalfSpace e
  · have hc : c y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy ⟨hyH, hR h⟩
    rw [hc, mul_zero, mul_zero]
  · have hneg : ((n : ℝ) + 1) * inner ℝ y e - 1 < 0 := by
      have h := mul_le_mul_of_nonneg_left (not_lt.1 hyH) (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
      rw [mul_zero] at h
      linarith
    rw [Real.smoothTransition.deriv_eq_zero_of_neg hneg, zero_mul]

/-- **The derivatives of the cutoffs in the limit**: if `c` is continuous with compact support and
`|c(y)| ≤ C ⟪y, e⟫` on `H₊`, and `u` is integrable on every bounded part `H₊ ∩ B(0, R)`, then
`∫ s'((n + 1)⟪y, e⟫ - 1) (n + 1) c(y) u(y) dy → 0`. By the strip estimate
(`Rd.abs_deriv_smoothTransition_mul_le`) the integrands are bounded by `2 D C |u|` on
`H₊ ∩ B(0, R)`, vanish elsewhere (`Rd.deriv_smoothTransition_mul_eq_zero`), and tend to `0`
pointwise, since `s' = 0` on `(1, ∞)`. -/
theorem tendsto_integral_deriv_halfSpaceCutoff_smul {c : V → ℝ} (hc : Continuous c)
    (hcc : HasCompactSupport c) {C : ℝ}
    (hC : ∀ y ∈ openHalfSpace e, |c y| ≤ C * inner ℝ y e) {u : V → ℂ}
    (hu : ∀ R, IntegrableOn u ((openHalfSpace e : Set V) ∩ ball 0 R)) :
    Tendsto (fun n : ℕ => ∫ y, (deriv Real.smoothTransition (((n : ℝ) + 1) * inner ℝ y e - 1) *
      (((n : ℝ) + 1) * c y)) • u y) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hcc.isCompact.isBounded.subset_ball 0
  obtain ⟨D, -, hD⟩ := Real.smoothTransition.exists_abs_deriv_le
  have h0 : ∀ n : ℕ, ∫ y, (deriv Real.smoothTransition (((n : ℝ) + 1) * inner ℝ y e - 1) *
      (((n : ℝ) + 1) * c y)) • u y = ∫ y in (openHalfSpace e : Set V) ∩ ball 0 R,
        (deriv Real.smoothTransition (((n : ℝ) + 1) * inner ℝ y e - 1) *
          (((n : ℝ) + 1) * c y)) • u y := fun n =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [deriv_smoothTransition_mul_eq_zero hR n hy, zero_smul]).symm
  have hds : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hS : MeasurableSet ((openHalfSpace e : Set V) ∩ ball 0 R) :=
    (openHalfSpace e).isOpen.measurableSet.inter measurableSet_ball
  have hm : ∀ n : ℕ, Continuous fun y : V =>
      deriv Real.smoothTransition (((n : ℝ) + 1) * inner ℝ y e - 1) * (((n : ℝ) + 1) * c y) :=
    fun n => (hds.comp ((continuous_const.mul (continuous_id.inner continuous_const)).sub
      continuous_const)).mul (continuous_const.mul hc)
  simp_rw [h0]
  have hlim := tendsto_integral_of_dominated_convergence (μ := volume.restrict
    ((openHalfSpace e : Set V) ∩ ball 0 R)) (f := fun _ => (0 : ℂ))
    (F := fun (n : ℕ) y => (deriv Real.smoothTransition (((n : ℝ) + 1) * inner ℝ y e - 1) *
      (((n : ℝ) + 1) * c y)) • u y) (fun y => 2 * D * C * ‖u y‖)
    (fun n => (hm n).aestronglyMeasurable.smul (hu R).aestronglyMeasurable)
    ((hu R).norm.const_mul _) (fun n => ?_) ?_
  · simpa using hlim
  · filter_upwards [ae_restrict_mem hS] with y hy
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_deriv_smoothTransition_mul_le hD hy.1 (hC y hy.1) n)
      (norm_nonneg _)
  · filter_upwards [ae_restrict_mem hS] with y hy
    have ht : 0 < inner ℝ y e := hy.1
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / inner ℝ y e)
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have h1 : 2 / inner ℝ y e < (n : ℝ) + 1 := hN.trans_le (by exact_mod_cast hn.trans (by omega))
    rw [div_lt_iff₀ ht] at h1
    dsimp only
    rw [Real.smoothTransition.deriv_eq_zero_of_one_lt (by linarith), zero_mul, zero_smul]

/-- **The weak derivative tested against a cutoff product**: if `g = ∂_w u` weakly on `H₊` and
`χ` is smooth with compact support, then for every `n`
`∫ η_n χ g = -∫ η_n (∂_w χ) u - ∫ (∂_w η_n) χ u`: the product `η_n u` has the weak derivative
`η_n g + (∂_w η_n) u` on `V` (`Rd.HasWeakLineDeriv.mul_of_tsupport_subset`), tested against
`χ`. -/
theorem integral_halfSpaceCutoff_smul_eq {w : V} {u g : V → ℂ}
    (h : HasWeakLineDeriv (openHalfSpace e) (fun _ : Fin 1 => w) u g) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ) (n : ℕ) :
    ∫ y, halfSpaceCutoff e n y • (χ y • g y) =
      -(∫ y, halfSpaceCutoff e n y • (fderiv ℝ χ y w • u y)) -
        ∫ y, (fderiv ℝ (halfSpaceCutoff e n) y w * χ y) • u y := by
  have hη := contDiff_halfSpaceCutoff (e := e) n
  have hηH := tsupport_halfSpaceCutoff_subset (e := e) n
  have hmono := h.mono (inf_le_right : (⊤ ⊓ openHalfSpace e : Opens V) ≤ openHalfSpace e)
  have h' := hmono.mul_of_tsupport_subset hη hηH
  let φ : 𝓓((⊤ : Opens V), ℝ) := ⟨χ, hχ, hχc, by simp⟩
  have hI := h'.integral_eq φ
  rw [LineDeriv.iteratedLineDerivOp_one, pow_one, neg_one_smul] at hI
  have hc : Continuous fun y => (halfSpaceCutoff e n y : ℂ) :=
    Complex.continuous_ofReal.comp hη.continuous
  have hc' : Continuous fun y => (fderiv ℝ (halfSpaceCutoff e n) y w : ℂ) :=
    Complex.continuous_ofReal.comp ((hη.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hcH : tsupport (fun y => (halfSpaceCutoff e n y : ℂ)) ⊆ openHalfSpace e :=
    (tsupport_comp_subset Complex.ofReal_zero _).trans hηH
  have hcH' : tsupport (fun y => (fderiv ℝ (halfSpaceCutoff e n) y w : ℂ)) ⊆ openHalfSpace e :=
    ((tsupport_comp_subset Complex.ofReal_zero _).trans (tsupport_fderiv_apply_subset ℝ w)).trans
      hηH
  have i1 := φ.integrable_smul (locallyIntegrableOn_mul_of_tsupport_subset hmono.2 hc hcH)
  have i2 := φ.integrable_smul (locallyIntegrableOn_mul_of_tsupport_subset hmono.1 hc' hcH')
  have e1 : (fun y => φ y • ((halfSpaceCutoff e n y : ℂ) * g y +
      (fderiv ℝ (halfSpaceCutoff e n) y w : ℂ) * u y)) = fun y =>
        φ y • ((halfSpaceCutoff e n y : ℂ) * g y) +
          φ y • ((fderiv ℝ (halfSpaceCutoff e n) y w : ℂ) * u y) :=
    funext fun y => smul_add _ _ _
  rw [e1, integral_add i1 i2] at hI
  have e2 : (fun y => halfSpaceCutoff e n y • (χ y • g y)) =
      fun y => φ y • ((halfSpaceCutoff e n y : ℂ) * g y) := funext fun y => by
    change _ = χ y • _
    simp only [Complex.real_smul]
    ring
  have e3 : (fun y => (fderiv ℝ (halfSpaceCutoff e n) y w * χ y) • u y) =
      fun y => φ y • ((fderiv ℝ (halfSpaceCutoff e n) y w : ℂ) * u y) := funext fun y => by
    change _ = χ y • _
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring
  have e4 : (fun y => halfSpaceCutoff e n y • (fderiv ℝ χ y w • u y)) =
      fun y => (∂_{w} φ) y • ((halfSpaceCutoff e n y : ℂ) * u y) := funext fun y => by
    rw [lineDerivOp_testFunction_apply]
    change _ = fderiv ℝ χ y w • _
    simp only [Complex.real_smul]
    ring
  rw [e2, e3, e4]
  linear_combination hI

/-- **Integration by parts on the half-space with a vanishing boundary term**: let `g_k = ∂_{w_k} u`
weakly on `H₊` (`k = 1, 2`), with `u`, `g_1`, `g_2` integrable on every bounded part
`H₊ ∩ B(0, R)`, and let `χ_1`, `χ_2` be smooth with compact support and
`|⟪w_1, e⟫ χ_1(y) + ⟪w_2, e⟫ χ_2(y)| ≤ C ⟪y, e⟫` on `H₊`. Then
`∫_{H₊} (χ_1 g_1 + χ_2 g_2) = -∫_{H₊} ((∂_{w_1} χ_1) u + (∂_{w_2} χ_2) u)`. With the cutoffs
`η_n` (`Rd.integral_halfSpaceCutoff_smul_eq`), the boundary terms are
`∫ s'((n + 1)⟪y, e⟫ - 1) (n + 1) (⟪w_1, e⟫ χ_1 + ⟪w_2, e⟫ χ_2) u → 0`
(`Rd.tendsto_integral_deriv_halfSpaceCutoff_smul`), and the other terms converge by dominated
convergence (`Rd.tendsto_integral_halfSpaceCutoff_smul`). This is the half-space lemma of
Brezis (2011, Chapter 9) in a form with two test functions. -/
theorem setIntegral_openHalfSpace_smul_add_eq {w₁ w₂ : V} {u g₁ g₂ : V → ℂ}
    (hu : ∀ R, IntegrableOn u ((openHalfSpace e : Set V) ∩ ball 0 R))
    (hg₁ : ∀ R, IntegrableOn g₁ ((openHalfSpace e : Set V) ∩ ball 0 R))
    (hg₂ : ∀ R, IntegrableOn g₂ ((openHalfSpace e : Set V) ∩ ball 0 R))
    (h₁ : HasWeakLineDeriv (openHalfSpace e) (fun _ : Fin 1 => w₁) u g₁)
    (h₂ : HasWeakLineDeriv (openHalfSpace e) (fun _ : Fin 1 => w₂) u g₂) {χ₁ χ₂ : V → ℝ}
    (hχ₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ₁) (hχ₁c : HasCompactSupport χ₁)
    (hχ₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ₂) (hχ₂c : HasCompactSupport χ₂) {C : ℝ}
    (hC : ∀ y ∈ openHalfSpace e,
      |inner ℝ w₁ e * χ₁ y + inner ℝ w₂ e * χ₂ y| ≤ C * inner ℝ y e) :
    ∫ y in openHalfSpace e, (χ₁ y • g₁ y + χ₂ y • g₂ y) =
      -∫ y in openHalfSpace e, (fderiv ℝ χ₁ y w₁ • u y + fderiv ℝ χ₂ y w₂ • u y) := by
  have hd : ∀ {χ : V → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → ∀ w : V,
      Continuous fun y => fderiv ℝ χ y w := fun hχ w =>
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hH := (openHalfSpace e).isOpen.measurableSet
  have I1 := integrableOn_smul_of_hasCompactSupport hH hχ₁.continuous hχ₁c hg₁
  have I2 := integrableOn_smul_of_hasCompactSupport hH hχ₂.continuous hχ₂c hg₂
  have J1 := integrableOn_smul_of_hasCompactSupport hH (hd hχ₁ w₁)
    (hχ₁c.fderiv_apply (𝕜 := ℝ) w₁) hu
  have J2 := integrableOn_smul_of_hasCompactSupport hH (hd hχ₂ w₂)
    (hχ₂c.fderiv_apply (𝕜 := ℝ) w₂) hu
  have hK : ∀ (n : ℕ) {χ : V → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ →
      ∀ w : V, Integrable fun y => (fderiv ℝ (halfSpaceCutoff e n) y w * χ y) • u y :=
    fun n χ hχ hχc w => integrable_smul_of_forall_notMem hH
      ((hd (contDiff_halfSpaceCutoff n) w).mul hχ.continuous) hχc.mul_left (fun y hy => by
        change fderiv ℝ (halfSpaceCutoff e n) y w * χ y = 0
        rw [image_eq_zero_of_notMem_tsupport fun h => hy ((tsupport_halfSpaceCutoff_subset n)
          ((tsupport_fderiv_apply_subset ℝ w) h)), zero_mul]) hu
  have hsum : ∀ n : ℕ, (∫ y, halfSpaceCutoff e n y • (χ₁ y • g₁ y)) +
      ∫ y, halfSpaceCutoff e n y • (χ₂ y • g₂ y) =
      -((∫ y, halfSpaceCutoff e n y • (fderiv ℝ χ₁ y w₁ • u y)) +
        ∫ y, halfSpaceCutoff e n y • (fderiv ℝ χ₂ y w₂ • u y)) -
      ∫ y, (deriv Real.smoothTransition (((n : ℝ) + 1) * inner ℝ y e - 1) *
        (((n : ℝ) + 1) * (inner ℝ w₁ e * χ₁ y + inner ℝ w₂ e * χ₂ y))) • u y := fun n => by
    have H1 := integral_halfSpaceCutoff_smul_eq h₁ hχ₁ hχ₁c n
    have H2 := integral_halfSpaceCutoff_smul_eq h₂ hχ₂ hχ₂c n
    have he : (fun y => (deriv Real.smoothTransition (((n : ℝ) + 1) * inner ℝ y e - 1) *
        (((n : ℝ) + 1) * (inner ℝ w₁ e * χ₁ y + inner ℝ w₂ e * χ₂ y))) • u y) =
        fun y => (fderiv ℝ (halfSpaceCutoff e n) y w₁ * χ₁ y) • u y +
          (fderiv ℝ (halfSpaceCutoff e n) y w₂ * χ₂ y) • u y := funext fun y => by
      rw [fderiv_halfSpaceCutoff_apply, fderiv_halfSpaceCutoff_apply, ← add_smul]
      ring_nf
    rw [he, integral_add (hK n hχ₁ hχ₁c w₁) (hK n hχ₂ hχ₂c w₂)]
    linear_combination H1 + H2
  have hcont : Continuous fun y => inner ℝ w₁ e * χ₁ y + inner ℝ w₂ e * χ₂ y :=
    (continuous_const.mul hχ₁.continuous).add (continuous_const.mul hχ₂.continuous)
  have hL := ((tendsto_integral_halfSpaceCutoff_smul I1).add
    (tendsto_integral_halfSpaceCutoff_smul I2))
  have hR := ((tendsto_integral_halfSpaceCutoff_smul J1).add
    (tendsto_integral_halfSpaceCutoff_smul J2)).neg.sub
    (tendsto_integral_deriv_halfSpaceCutoff_smul hcont
      ((hχ₁c.mul_left).add (hχ₂c.mul_left)) hC hu)
  have hlim := tendsto_nhds_unique (hL.congr fun n => hsum n) hR
  rw [integral_add I1 I2, integral_add J1 J2, hlim, sub_zero]

end IntegrationByParts

/-! ### The weak derivatives of the even reflection -/

section EvenReflection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {e : V}

/-- **`L_p` functions on a set are integrable on its bounded parts**: for `1 ≤ p` and every set
`s`, every `u ∈ L_p(s)` is integrable on `s ∩ B(0, R)`, a set of finite measure (Mathlib's
`MemLp.integrable`). -/
theorem integrableOn_inter_ball_of_memLp {p : ℝ≥0∞} (hp : 1 ≤ p) {s : Set V} {u : V → ℂ}
    (hu : MemLp u p (volume.restrict s)) (R : ℝ) : IntegrableOn u (s ∩ ball 0 R) := by
  have hfin : IsFiniteMeasure (volume.restrict (s ∩ ball 0 R)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono inter_subset_right).trans_lt measure_ball_lt_top⟩
  have h := hu.restrict (ball 0 R)
  rw [Measure.restrict_restrict measurableSet_ball, inter_comm] at h
  exact h.integrable hp

/-- **The two halves of a reflected function are locally integrable**: for a measurable set `s`,
if `a` and `b` are integrable on every bounded part `s ∩ B(0, R)` of `s`, then
`y ↦ 1_s a (y) + 1_s b (σ y)` is locally integrable on `V`; the reflection `σ` preserves Lebesgue
measure and the balls `B(0, R)`. -/
theorem locallyIntegrable_indicator_add_indicator_comp_halfSpaceReflection {s : Set V}
    (hs : MeasurableSet s) {a b : V → ℂ} (ha : ∀ R, IntegrableOn a (s ∩ ball 0 R))
    (hb : ∀ R, IntegrableOn b (s ∩ ball 0 R)) :
    LocallyIntegrable (fun y => s.indicator a y + s.indicator b (halfSpaceReflection e y))
      volume := by
  refine (locallyIntegrable_of_forall_integrableOn_ball 0 fun R =>
    (integrableOn_indicator_iff hs.nullMeasurableSet).2 (ha R)).add
      (locallyIntegrable_of_forall_integrableOn_ball 0 fun R => ?_)
  have h := ((measurePreserving_halfSpaceReflection e).integrableOn_comp_preimage
    (halfSpaceReflection e).toHomeomorph.measurableEmbedding
      (f := s.indicator b) (s := ball 0 R)).2
        ((integrableOn_indicator_iff hs.nullMeasurableSet).2 (hb R))
  rwa [LinearIsometryEquiv.preimage_ball, map_zero] at h

/-- Multipliers of a function on a measurable set `s`: `∫ c 1_s b = ∫_s c b`. -/
theorem integral_smul_indicator {s : Set V} (hs : MeasurableSet s) (c : V → ℝ) (b : V → ℂ) :
    ∫ y, c y • s.indicator b y = ∫ y in s, c y • b y := by
  simp_rw [← indicator_smul_apply]
  exact integral_indicator hs

/-- **The reflected half**: for a measurable set `s`,
`∫ c(y) 1_s b (σ y) dy = ∫_s c(σ y) b(y) dy`, since `σ` is an involution that preserves Lebesgue
measure (Mathlib's `MeasurePreserving.integral_comp`). -/
theorem integral_smul_indicator_comp_halfSpaceReflection {s : Set V} (hs : MeasurableSet s)
    (c : V → ℝ) (b : V → ℂ) :
    ∫ y, c y • s.indicator b (halfSpaceReflection e y) =
      ∫ y in s, c (halfSpaceReflection e y) • b y := by
  have h := (measurePreserving_halfSpaceReflection e).integral_comp
    (halfSpaceReflection e).toHomeomorph.measurableEmbedding
      (fun y => c (halfSpaceReflection e y) • s.indicator b y)
  simp only [halfSpaceReflection_halfSpaceReflection] at h
  rw [h, integral_smul_indicator hs]

/-- Compactly supported multipliers of `1_s b` are integrable when `b` is integrable on every
bounded part of the measurable set `s` (`Rd.integrableOn_smul_of_hasCompactSupport`). -/
theorem integrable_smul_indicator {s : Set V} (hs : MeasurableSet s) {c : V → ℝ}
    (hc : Continuous c) (hcc : HasCompactSupport c) {b : V → ℂ}
    (hb : ∀ R, IntegrableOn b (s ∩ ball 0 R)) : Integrable fun y => c y • s.indicator b y := by
  simp_rw [← indicator_smul_apply]
  exact (integrableOn_smul_of_hasCompactSupport hs hc hcc hb).integrable_indicator hs

/-- Compactly supported multipliers of `1_s b ∘ σ` are integrable when `b` is integrable on every
bounded part of the measurable set `s`: compose with the measure-preserving `σ`. -/
theorem integrable_smul_indicator_comp_halfSpaceReflection {s : Set V} (hs : MeasurableSet s)
    {c : V → ℝ} (hc : Continuous c) (hcc : HasCompactSupport c) {b : V → ℂ}
    (hb : ∀ R, IntegrableOn b (s ∩ ball 0 R)) :
    Integrable fun y => c y • s.indicator b (halfSpaceReflection e y) := by
  have h := integrable_smul_indicator hs (hc.comp (halfSpaceReflection e).continuous)
    (hcc.comp_homeomorph (halfSpaceReflection e).toHomeomorph) hb
  have h' := ((measurePreserving_halfSpaceReflection e).integrable_comp_emb
    (halfSpaceReflection e).toHomeomorph.measurableEmbedding).2 h
  simpa [Function.comp_def] using h'

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The reflection bound for Lipschitz functions**: for `L`-Lipschitz `φ`, a unit vector `e` and
`y ∈ H₊`, `|⟪v, e⟫ φ(y) + ⟪σ v, e⟫ φ(σ y)| ≤ 2 L |⟪v, e⟫| ⟪y, e⟫`, since `⟪σ v, e⟫ = -⟪v, e⟫`
and `‖y - σ y‖ = 2⟪y, e⟫`. -/
theorem abs_inner_mul_add_inner_halfSpaceReflection_mul_le (he : ‖e‖ = 1) {φ : V → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (v : V) {y : V} (hy : y ∈ openHalfSpace e) :
    |inner ℝ v e * φ y + inner ℝ (halfSpaceReflection e v) e * φ (halfSpaceReflection e y)| ≤
      2 * L * |inner ℝ v e| * inner ℝ y e := by
  rw [mem_openHalfSpace] at hy
  rw [inner_halfSpaceReflection he, neg_mul, ← sub_eq_add_neg, ← mul_sub, abs_mul]
  have h := hφ.dist_le_mul y (halfSpaceReflection e y)
  rw [Real.dist_eq, dist_eq_norm, norm_sub_halfSpaceReflection he, abs_of_pos hy] at h
  calc |inner ℝ v e| * |φ y - φ (halfSpaceReflection e y)|
      ≤ |inner ℝ v e| * (L * (2 * inner ℝ y e)) := by gcongr
    _ = 2 * L * |inner ℝ v e| * inner ℝ y e := by ring

/-- **The even reflection is weakly differentiable** (Brezis 2011, Chapter 9; Evans–Gariepy,
Section 4.4): let `e` be a unit vector, `u` and its weak derivatives `g_w = ∂_w u` on `H₊`
integrable on every bounded part `H₊ ∩ B(0, R)` of `H₊`. Then for every `v ∈ V` the function
`y ↦ 1_{H₊} g_v (y) + 1_{H₊} g_{σ v} (σ y)` is the weak derivative `∂_v` of the even reflection
`E u` on `V`. Tested against `φ`, both sides are integrals over `H₊` after the change of
variables `y ↦ σ y` (`Rd.integral_smul_indicator_comp_halfSpaceReflection`), and they agree by
the integration by parts of `Rd.setIntegral_openHalfSpace_smul_add_eq` with `χ_1 = φ` and
`χ_2 = φ ∘ σ`, whose boundary term vanishes by
`Rd.abs_inner_mul_add_inner_halfSpaceReflection_mul_le`. -/
theorem hasWeakLineDeriv_evenReflection_of_forall (he : ‖e‖ = 1) {u : V → ℂ} {g : V → V → ℂ}
    (hu : ∀ R, IntegrableOn u ((openHalfSpace e : Set V) ∩ ball 0 R))
    (hg : ∀ w R, IntegrableOn (g w) ((openHalfSpace e : Set V) ∩ ball 0 R))
    (hug : ∀ w, HasWeakLineDeriv (openHalfSpace e) (fun _ : Fin 1 => w) u (g w)) (v : V) :
    HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) (evenReflection e u)
      (fun y => (openHalfSpace e : Set V).indicator (g v) y +
        (openHalfSpace e : Set V).indicator (g (halfSpaceReflection e v))
          (halfSpaceReflection e y)) := by
  have hH := (openHalfSpace e).isOpen.measurableSet
  refine (hasWeakLineDeriv_iff_integral
    ((locallyIntegrable_indicator_add_indicator_comp_halfSpaceReflection hH hu
      hu).locallyIntegrableOn _)
    ((locallyIntegrable_indicator_add_indicator_comp_halfSpaceReflection hH (hg v)
      (hg (halfSpaceReflection e v))).locallyIntegrableOn _)).2 fun φ => ?_
  rw [LineDeriv.iteratedLineDerivOp_one, pow_one, neg_one_smul]
  have hφ := φ.contDiff
  have hφc := φ.hasCompactSupport
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => φ (halfSpaceReflection e y) :=
    hφ.comp (halfSpaceReflection e).toContinuousLinearEquiv.contDiff
  have hψc : HasCompactSupport fun y => φ (halfSpaceReflection e y) :=
    hφc.comp_homeomorph (halfSpaceReflection e).toHomeomorph
  obtain ⟨L, hL⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
  have key := setIntegral_openHalfSpace_smul_add_eq hu (hg v) (hg (halfSpaceReflection e v))
    (hug v) (hug (halfSpaceReflection e v)) hφ hφc hψ hψc fun y hy =>
      abs_inner_mul_add_inner_halfSpaceReflection_mul_le he hL v hy
  have hdψ : ∀ y, fderiv ℝ (fun y => φ (halfSpaceReflection e y)) y (halfSpaceReflection e v) =
      (∂_{v} φ) (halfSpaceReflection e y) := fun y => by
    rw [lineDerivOp_testFunction_apply]
    have h := (halfSpaceReflection e).toContinuousLinearEquiv.comp_right_fderiv
      (f := (φ : V → ℝ)) (x := y) (𝕜 := ℝ)
    change fderiv ℝ ((φ : V → ℝ) ∘ (halfSpaceReflection e).toContinuousLinearEquiv) y
      (halfSpaceReflection e v) = _
    rw [h, ContinuousLinearMap.comp_apply]
    simp
  have hdφ : ∀ y, fderiv ℝ φ y v = (∂_{v} φ) y := fun y =>
    (lineDerivOp_testFunction_apply _ _ _).symm
  simp only [hdψ, hdφ] at key
  have hd := (∂_{v} φ).contDiff.continuous
  have hdc := (∂_{v} φ).hasCompactSupport
  simp only [smul_add]
  rw [integral_add (integrable_smul_indicator hH hφ.continuous hφc (hg v))
      (integrable_smul_indicator_comp_halfSpaceReflection hH hφ.continuous hφc
        (hg (halfSpaceReflection e v))),
    integral_add (integrable_smul_indicator hH hd hdc hu)
      (integrable_smul_indicator_comp_halfSpaceReflection hH hd hdc hu),
    integral_smul_indicator hH, integral_smul_indicator_comp_halfSpaceReflection hH,
    integral_smul_indicator hH, integral_smul_indicator_comp_halfSpaceReflection hH,
    ← integral_add (integrableOn_smul_of_hasCompactSupport hH hφ.continuous hφc (hg v))
      (integrableOn_smul_of_hasCompactSupport hH hψ.continuous hψc
        (hg (halfSpaceReflection e v))),
    key]
  congr 1
  exact integral_add (integrableOn_smul_of_hasCompactSupport hH hd hdc hu)
    (integrableOn_smul_of_hasCompactSupport hH (hd.comp (halfSpaceReflection e).continuous)
      (hdc.comp_homeomorph (halfSpaceReflection e).toHomeomorph) hu)

/-- **The even reflection in the basis directions** (the form of
`Rd.hasWeakLineDeriv_evenReflection_of_forall` with the derivatives `h_i = ∂_{e_i} u` along the
basis `e_i = Rd.gridBasis V i`): for a unit vector `e`, if `u` and the `h_i` are integrable on
every bounded part `H₊ ∩ B(0, R)` of `H₊`,
then for every `v ∈ V` the weak derivative `∂_v` of the even reflection `E u` on `V` is
`y ↦ 1_{H₊} (∑_i ⟪v, e_i⟫ h_i) (y) + 1_{H₊} (∑_i ⟪σ v, e_i⟫ h_i) (σ y)`; on `H₊` the derivative
along `w` is `∑_i ⟪w, e_i⟫ h_i` (`Rd.hasWeakLineDeriv_of_forall_gridBasis`). -/
theorem hasWeakLineDeriv_evenReflection (he : ‖e‖ = 1) {u : V → ℂ}
    {h : Fin (finrank ℝ V) → V → ℂ}
    (hu : ∀ R, IntegrableOn u ((openHalfSpace e : Set V) ∩ ball 0 R))
    (hh : ∀ i R, IntegrableOn (h i) ((openHalfSpace e : Set V) ∩ ball 0 R))
    (huh : ∀ i, HasWeakLineDeriv (openHalfSpace e) (fun _ : Fin 1 => gridBasis V i) u (h i))
    (v : V) :
    HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) (evenReflection e u)
      (fun y => (openHalfSpace e : Set V).indicator
          (fun x => ∑ i, (inner ℝ v (gridBasis V i) : ℂ) * h i x) y +
        (openHalfSpace e : Set V).indicator
          (fun x => ∑ i, (inner ℝ (halfSpaceReflection e v) (gridBasis V i) : ℂ) * h i x)
          (halfSpaceReflection e y)) :=
  hasWeakLineDeriv_evenReflection_of_forall he hu
    (fun _ R => integrable_finsetSum _ fun i _ => (hh i R).const_mul _)
    (fun w => hasWeakLineDeriv_of_forall_gridBasis huh w) v

/-- **The `L_p` norm of a reflected function**: for `1 ≤ p` and a measurable set `s`,
`‖y ↦ 1_s a (y) + 1_s b (σ y)‖_{L_p(V)} ≤ ‖a‖_{L_p(s)} + ‖b‖_{L_p(s)}`, by Minkowski's
inequality and since `σ` preserves Lebesgue measure (Mathlib's `eLpNorm_comp_measurePreserving`). -/
theorem eLpNorm_indicator_add_indicator_comp_halfSpaceReflection_le {E : Type*}
    [NormedAddCommGroup E] {p : ℝ≥0∞} (hp : 1 ≤ p) {s : Set V} (hs : MeasurableSet s)
    (a b : V → E) :
    eLpNorm (fun y => s.indicator a y + s.indicator b (halfSpaceReflection e y)) p volume ≤
      eLpNorm a p (volume.restrict s) + eLpNorm b p (volume.restrict s) := by
  have hc := eLpNorm_comp_le_of_mapsTo (h := s.indicator b) (U := univ)
    (measurePreserving_halfSpaceReflection e) MeasurableSet.univ (mapsTo_univ _ _) p
  rw [Measure.restrict_univ] at hc
  calc _ ≤ _ := eLpNorm_add_le (f := s.indicator a)
        (g := fun y => s.indicator b (halfSpaceReflection e y)) hp
    _ ≤ eLpNorm (s.indicator a) p volume + eLpNorm (s.indicator b) p volume :=
        add_le_add le_rfl hc
    _ = _ := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet,
        eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]

/-- **The `L_p` norm of the even reflection**: `‖E u‖_{L_p(V)} ≤ 2 ‖u‖_{L_p(H₊)}` for `1 ≤ p`
(`Rd.eLpNorm_indicator_add_indicator_comp_halfSpaceReflection_le`). -/
theorem eLpNorm_evenReflection_le {p : ℝ≥0∞} (hp : 1 ≤ p) (u : V → ℂ) :
    eLpNorm (evenReflection e u) p volume ≤ 2 * eLpNorm u p (volume.restrict (openHalfSpace e)) :=
  (eLpNorm_indicator_add_indicator_comp_halfSpaceReflection_le hp
    (openHalfSpace e).isOpen.measurableSet u u).trans_eq (two_mul _).symm

end EvenReflection

end Rd
