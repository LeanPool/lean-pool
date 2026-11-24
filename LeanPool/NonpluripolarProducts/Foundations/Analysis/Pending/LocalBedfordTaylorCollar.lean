/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ScaledSmoothMax
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothDDCHessianPositivity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.BottChern

/-!
# The common collar comparison for recursive Bedford--Taylor products

On an open `U ⊆ ℂⁿ`, for the currents of `Pending.LocalProductCurrents` and the recursive product
`B(u₀, …, u_{q-1}; T)` of `Pending.LocalBedfordTaylorProducts` (`bt:collar-comparison`,
`demailly-cadg:III.3.7`):

* `btProduct_succ_eq_ddcMul` — **peeling the outermost potential**:
  `B(u₀, u₁, …, u_q; T) = dd^c(u₀ B(u₁, …, u_q; T))` (the recursion peels the innermost one).
* `ddcForm g` — the form `dd^c g` of a function smooth on `U`, as a smooth closed form with values
  in `Λ₁`; `ddcWedge_eq_wedgeForm` (`dd^c g ∧ S` is the wedge of `S` with this form) and
  `btProduct_wedgeForm_ddcForm` (`B(u; T ∧ dd^c g) = B(u; T) ∧ dd^c g` for `g` with semipositive
  Levi form).
* `traceIntegral B f S` — the integral `∫_B f S ∧ ω₀^m` of a bounded weight against the trace
  measure of a positive current `S` of bidimension `(m,m)`.
* `traceIntegral_ddcMul_eq` — **the integration by parts on `B` without boundary terms**: for `Q`
  positive closed, `F` smooth with semipositive Levi form, `g` locally bounded PSH, and `F = g` on
  `B` off a compact subset of `B`, `∫_B F dd^c(g Q) ∧ ω₀^m = ∫_B g dd^c F ∧ Q ∧ ω₀^m`.
* `traceIntegral_btProduct_le` — **the comparison**: if `v_j ≤ w_j` on `B`, all agree with one
  function `h` on `B` off a compact subset of `B`, and every `w_j` is the pointwise limit on `B` of
  smooth functions with semipositive Levi form, `≥ w_j` on `B`, uniformly bounded on `B` and equal
  to `h` off a compact subset of `B`, then
  `∫_B v₀ B(v₁, …, v_q; T) ∧ ω₀^m ≤ ∫_B w₀ B(w₁, …, w_q; T) ∧ ω₀^m`.
* `collar_comparison` — **the ball case** (`bt:collar-comparison`): for `B = B(z₀, R)` with
  `BBar ⊆ U`, `h = A(|z - z₀|² - R²)` and locally bounded PSH `a_j ≤ b_j ≤ -1` on `BBar`, the
  functions `v_j = max(h, a_j)`, `w_j = max(h, b_j)` satisfy the comparison.
  For compact `K ⊆ B` and large `A`, `collarMax_eq_of_le` gives `v_j = a_j` near `K`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  CoordinateWedgeAssoc ClosedProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorSmooth
  LocalBedfordTaylorLocality LocalCurrentLebesgue ConstantFormProducts LocalBedfordTaylorForms

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n : ℕ}

local notation "E" => ComplexModel n

variable {U : Opens (ComplexModel n)}

/-! ### Peeling the outermost potential -/

section Peel

/-- Transport of a current along an equality of bidimensions. -/
def castLPC {a b : ℕ} (h : a = b) (T : LocalProductCurrent n U a) : LocalProductCurrent n U b :=
  h ▸ T

theorem heq_castLPC {a b : ℕ} (h : a = b) (T : LocalProductCurrent n U a) :
    HEq T (castLPC h T) := by
  subst h
  rfl

theorem isPositive_castLPC {a b : ℕ} (h : a = b) {T : LocalProductCurrent n U a}
    (hT : IsPositive T) : IsPositive (castLPC h T) := by
  subst h
  exact hT

theorem isClosedAny_castLPC {a b : ℕ} (h : a = b) {T : LocalProductCurrent n U a}
    (hT : IsClosedAny a T) : IsClosedAny b (castLPC h T) := by
  subst h
  exact hT

theorem ddcMul_heq {a b : ℕ} (h : a = b) {T : LocalProductCurrent n U (a + 1)}
    {T' : LocalProductCurrent n U (b + 1)} (hT : HEq T T') (u : E → ℝ) :
    HEq (ddcMul T u) (ddcMul T' u) := by
  subst h
  cases hT
  rfl

/-- **Peeling the outermost potential**: `B(u₀, u₁, …, u_q; T) = dd^c(u₀ B(u₁, …, u_q; T))` (the
current `T` read in the bidimension `(r + 1) + q`). -/
theorem btProduct_succ_eq_ddcMul : ∀ (q r : ℕ) (u : Fin (q + 1) → E → ℝ)
    (T : LocalProductCurrent n U (r + (q + 1))) (T' : LocalProductCurrent n U (r + 1 + q)),
    HEq T T' → btProduct (q + 1) r u T = ddcMul (btProduct q (r + 1) (Fin.tail u) T') (u 0)
  | 0, r, u, T, T', hT => by
    have e : T = T' := eq_of_heq hT
    subst e
    rfl
  | q + 1, r, u, T, T', hT => by
    rw [btProduct_succ, btProduct_succ_eq_ddcMul q r (Fin.init u) _
      (ddcMul T' (u (Fin.last (q + 1)))) (ddcMul_heq (a := r + (q + 1)) (b := r + 1 + q)
        (by omega) hT _), btProduct_succ,
      Fin.tail_init_eq_init_tail]
    rfl

end Peel

/-! ### `dd^c g` as a smooth closed form -/

section SmoothForms

/-- The second derivative `∂_a∂_b g` of a function smooth on `U`, at a point of `U`. -/
theorem hessFun_eq_realHessian {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) (a b : Fin (n * 2))
    {x : E} (hx : x ∈ U) :
    hessFun a b g x = realHessian g x (realBasis n a) (realBasis n b) := by
  rw [realHessian_eq_fderiv]
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_of_isOpen U.isOpen (m := ∞) (by simp)).differentiableOn (by simp)).differentiableAt
      (U.isOpen.mem_nhds hx)
  change fderiv ℝ (fun y => fderiv ℝ g y (realBasis n b)) x (realBasis n a) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- **`dd^c g` in coordinates** on `U`: `dd^c g = -(1/4π) ∑_{a,b} ∂_a∂_b g P_{ab}`. -/
theorem smoothDDC_eq_sum_hessFun {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) {x : E} (hx : x ∈ U) :
    smoothDDC g x = ∑ a, ∑ b, (-(1 / (4 * Real.pi)) * hessFun a b g x) • coeffForm a b := by
  have h2 : ContDiffAt ℝ 2 g x :=
    (hg.contDiffAt (U.isOpen.mem_nhds hx)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [smoothDDC_eq_sum h2]
  simp only [hessFun_eq_realHessian hg _ _ hx]

/-- The form `dd^c g`, of degree `2 = 2 · 1`. -/
abbrev ddcForm (g : E → ℝ) : E → RealForm n (2 * 1) := smoothDDC g

theorem contDiffOn_ddcForm {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (ddcForm g) U := by
  refine ContDiffOn.congr (f := fun x => ∑ a, ∑ b,
    (-(1 / (4 * Real.pi)) * hessFun a b g x) • (coeffForm a b : RealForm n (2 * 1))) ?_
    fun x hx => smoothDDC_eq_sum_hessFun hg hx
  refine ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ => ?_
  exact (contDiffOn_const.mul (contDiffOn_hessFun hg a b)).smul contDiffOn_const

/-- `dd^c g` is closed on `U`. -/
theorem extDeriv_ddcForm {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) {x : E} (hx : x ∈ U) :
    extDeriv (ddcForm g) x = 0 :=
  extDeriv_extDeriv_apply ((smoothDc_contDiffOn U.isOpen hg).contDiffAt (U.isOpen.mem_nhds hx))
    (by simp)

/-- `dd^c g` is semipositive where the Levi form of `g` is. -/
theorem isSemipositiveOneOne_smoothDDC_of_leviForm {g : E → ℝ} {x : E}
    (h2 : ContDiffAt ℝ 2 g x) (hl : ∀ v, 0 ≤ leviForm g x v) :
    IsSemipositiveOneOne (smoothDDC g x) := by
  refine ⟨fun u v => smoothDDC_isOneOne h2 u v, fun v => ?_⟩
  rw [smoothDDC_apply_eq_realHessian h2]
  have hI : Complex.I • (Complex.I • v) = (-1 : ℝ) • v := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, neg_one_smul]
  rw [hI, realHessian_smul_right]
  have hv := hl v
  rw [leviForm] at hv
  have hπ : 0 < 4 * Real.pi := by positivity
  rw [le_div_iff₀ hπ]
  linarith

/-- `dd^c g` is strongly positive on `U` when the Levi form of `g` is semipositive on `U`. -/
theorem ddcForm_mem_spCone {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hl : ∀ x ∈ U, ∀ v, 0 ≤ leviForm g x v) : ∀ x ∈ U, ddcForm g x ∈ spCone 1 := fun x hx =>
  mem_spCone_one (isSemipositiveOneOne_smoothDDC_of_leviForm
    ((hg.contDiffAt (U.isOpen.mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hl x hx))

theorem ddcForm_mem_formSpan {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hl : ∀ x ∈ U, ∀ v, 0 ≤ leviForm g x v) : ∀ x ∈ U, ddcForm g x ∈ formSpan n 1 :=
  fun x hx => mem_formSpan_of_mem_spCone (ddcForm_mem_spCone hg hl x hx)

/-- **`dd^c g ∧ S` is the wedge of `S` with the form `dd^c g`.** -/
theorem ddcWedge_eq_wedgeForm {q : ℕ} (S : LocalProductCurrent n U (q + 1)) {g : E → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) :
    ddcWedge S hg = wedgeForm rfl S (contDiffOn_ddcForm hg) := by
  classical
  ext γ φ
  have hβ : ∀ j : Fin (n * 2) × Fin (n * 2),
      (coeffForm j.1 j.2 : RealForm n (2 * 1)) ∈ formSpan n 1 := fun j =>
    oneOne_mem_formSpan (isOneOne_coeffForm j.1 j.2)
  have hf : ∀ j : Fin (n * 2) × Fin (n * 2),
      ContDiffOn ℝ ∞ (fun x => -(1 / (4 * Real.pi)) * hessFun j.1 j.2 g x) U := fun j =>
    contDiffOn_const.mul (contDiffOn_hessFun hg j.1 j.2)
  have hS : ∀ x ∈ U, ddcForm g x ∈ formSpan n 1 := fun x hx => by
    rw [ddcForm, smoothDDC_eq_sum_hessFun hg hx]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (hβ (a, b))
  rw [wedgeForm_apply_eq rfl S (contDiffOn_ddcForm hg) hS _ hf (fun j => ⟨_, hβ j⟩)
    (fun x hx => by
      rw [ddcForm, smoothDDC_eq_sum_hessFun hg hx, ← Finset.sum_product']
      rfl) γ φ, ddcWedge_apply, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : wedgeSpan n rfl γ ⟨_, hβ j⟩ = wedgeLM q (isOneOne_coeffForm j.1 j.2) γ := by
    ext1
    rw [coe_wedgeSpan_apply rfl _ _ (by omega), coe_wedgeLM_apply]
    rfl
  have e2 : mulSmoothOnCLM (hf j) φ =
      (-(1 / (4 * Real.pi))) • mulSmoothOnCLM (contDiffOn_hessFun hg j.1 j.2) φ := by
    ext x
    simp only [mulSmoothOnCLM_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e1, e2, map_smul, smul_eq_mul]

/-- `dd^c g ∧ S` is positive for `S` positive and `g` with semipositive Levi form on `U`. -/
theorem isPositive_ddcWedge {q : ℕ} {S : LocalProductCurrent n U (q + 1)} (hS : IsPositive S)
    {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) (hl : ∀ x ∈ U, ∀ v, 0 ≤ leviForm g x v) :
    IsPositive (ddcWedge S hg) := by
  rw [ddcWedge_eq_wedgeForm]
  exact isPositive_wedgeForm rfl hS _ (ddcForm_mem_spCone hg hl)

/-- **Commutation with the recursion**: `B(u; T ∧ dd^c g) = dd^c g ∧ B(u; T)` for `T` positive
closed and `g` smooth on `U` with semipositive Levi form. -/
theorem btProduct_wedgeForm_ddcForm {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hl : ∀ x ∈ U, ∀ v, 0 ≤ leviForm g x v) (q r : ℕ) (u : Fin q → E → ℝ)
    (T : LocalProductCurrent n U (r + 1 + q)) (h : r + q + 1 = r + 1 + q) (hT : IsPositive T)
    (hTc : IsClosedAny (r + 1 + q) T) (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    btProduct q r u (wedgeForm h T (contDiffOn_ddcForm hg)) =
      ddcWedge (btProduct q (r + 1) u T) hg := by
  rw [ddcWedge_eq_wedgeForm]
  exact btProduct_wedgeForm (contDiffOn_ddcForm hg) (ddcForm_mem_spCone hg hl)
    (fun x hx => extDeriv_ddcForm hg hx) q r u T h hT hTc hu

end SmoothForms

/-! ### Integrals over an inner set against trace measures -/

section TraceIntegral

variable {m : ℕ}

open Classical in
/-- **`∫_B f S ∧ ω₀^m`**: the integral over `B` of `f` against the trace measure of a positive
current `S` of bidimension `(m,m)` (a junk value `0` if `S` is not positive). -/
def traceIntegral (B : Set E) (f : E → ℝ) (S : LocalProductCurrent n U m) : ℝ :=
  if h : IsPositive S then ∫ x in B, f x ∂h.traceMeasure else 0

theorem traceIntegral_of_isPositive (B : Set E) (f : E → ℝ) {S : LocalProductCurrent n U m}
    (hS : IsPositive S) : traceIntegral B f S = ∫ x in B, f x ∂hS.traceMeasure :=
  dite_eq_left hS

theorem traceMeasure_congr {S S' : LocalProductCurrent n U m} (h : S = S') (hS : IsPositive S)
    (hS' : IsPositive S') : hS.traceMeasure = hS'.traceMeasure := by
  subst h
  rfl

/-- `f = g` on `B` off a compact subset of `B`. -/
def EqOffCompact (B : Set E) (f g : E → ℝ) : Prop :=
  ∃ K : Set E, IsCompact K ∧ K ⊆ B ∧ ∀ x ∈ B, x ∉ K → f x = g x

theorem EqOffCompact.symm {B : Set E} {f g : E → ℝ} (h : EqOffCompact B f g) :
    EqOffCompact B g f := by
  obtain ⟨K, hK, hKB, hfg⟩ := h
  exact ⟨K, hK, hKB, fun x hx hxK => (hfg x hx hxK).symm⟩

theorem EqOffCompact.trans {B : Set E} {f g k : E → ℝ} (h : EqOffCompact B f g)
    (h' : EqOffCompact B g k) : EqOffCompact B f k := by
  obtain ⟨K, hK, hKB, hfg⟩ := h
  obtain ⟨K', hK', hK'B, hgk⟩ := h'
  exact ⟨K ∪ K', hK.union hK', union_subset hKB hK'B, fun x hx hxK =>
    (hfg x hx fun h => hxK (Or.inl h)).trans (hgk x hx fun h => hxK (Or.inr h))⟩

variable {B : Opens (ComplexModel n)}

theorem subset_of_relativelyCompactIn (hB : RelativelyCompactIn B U) : (B : Set E) ⊆ U :=
  subset_closure.trans hB.2

theorem traceMeasure_lt_top_of_relativelyCompactIn {S : LocalProductCurrent n U m}
    (hS : IsPositive S) (hB : RelativelyCompactIn B U) : hS.traceMeasure B < ⊤ :=
  (measure_mono subset_closure).trans_lt (hS.traceMeasure_lt_top hB.1 hB.2)

theorem integrableOn_of_bounded {S : LocalProductCurrent n U m} (hS : IsPositive S)
    (hB : RelativelyCompactIn B U) {f : E → ℝ}
    (hf : AEStronglyMeasurable f (hS.traceMeasure.restrict B)) {M : ℝ}
    (hM : ∀ x ∈ (B : Set E), |f x| ≤ M) : IntegrableOn f B hS.traceMeasure := by
  refine IntegrableOn.of_bound (traceMeasure_lt_top_of_relativelyCompactIn hS hB) hf M ?_
  filter_upwards [ae_restrict_mem B.isOpen.measurableSet] with x hx
  rw [Real.norm_eq_abs]
  exact hM x hx

theorem exists_bound_of_isLocallyBoundedPshOn {g : E → ℝ} (hg : IsLocallyBoundedPshOn U g)
    (hB : RelativelyCompactIn B U) : ∃ M, ∀ x ∈ (B : Set E), |g x| ≤ M := by
  obtain ⟨M, hM⟩ := isLocallyBoundedOn_indicator hg _ hB.1 hB.2
  refine ⟨M, fun x hx => ?_⟩
  have := hM x (subset_closure hx)
  rwa [Set.indicator_of_mem (subset_of_relativelyCompactIn hB hx)] at this

theorem aestronglyMeasurable_of_isLocallyBoundedPshOn {g : E → ℝ}
    (hg : IsLocallyBoundedPshOn U g) (hB : RelativelyCompactIn B U) (μ : Measure E) :
    AEStronglyMeasurable g (μ.restrict B) := by
  refine (measurable_indicator_of_isLocallyBoundedPshOn hg).aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem B.isOpen.measurableSet] with x hx
  exact Set.indicator_of_mem (subset_of_relativelyCompactIn hB hx) g

theorem exists_bound_of_continuousOn {f : E → ℝ} (hf : ContinuousOn f U)
    (hB : RelativelyCompactIn B U) : ∃ M, ∀ x ∈ (B : Set E), |f x| ≤ M := by
  obtain ⟨M, hM⟩ := hB.1.exists_bound_of_continuousOn (hf.mono hB.2)
  exact ⟨M, fun x hx => by simpa [Real.norm_eq_abs] using hM x (subset_closure hx)⟩

theorem aestronglyMeasurable_of_continuousOn {f : E → ℝ} (hf : ContinuousOn f U)
    (hB : RelativelyCompactIn B U) (μ : Measure E) : AEStronglyMeasurable f (μ.restrict B) :=
  (hf.mono (subset_of_relativelyCompactIn hB)).aestronglyMeasurable B.isOpen.measurableSet

/-- A locally bounded PSH weight is integrable on `B`. -/
theorem integrableOn_of_isLocallyBoundedPshOn {S : LocalProductCurrent n U m}
    (hS : IsPositive S) (hB : RelativelyCompactIn B U) {g : E → ℝ}
    (hg : IsLocallyBoundedPshOn U g) : IntegrableOn g B hS.traceMeasure := by
  obtain ⟨M, hM⟩ := exists_bound_of_isLocallyBoundedPshOn hg hB
  exact integrableOn_of_bounded hS hB (aestronglyMeasurable_of_isLocallyBoundedPshOn hg hB _) hM

/-- A weight continuous on `U` is integrable on `B`. -/
theorem integrableOn_of_continuousOn {S : LocalProductCurrent n U m} (hS : IsPositive S)
    (hB : RelativelyCompactIn B U) {f : E → ℝ} (hf : ContinuousOn f U) :
    IntegrableOn f B hS.traceMeasure := by
  obtain ⟨M, hM⟩ := exists_bound_of_continuousOn hf hB
  exact integrableOn_of_bounded hS hB (aestronglyMeasurable_of_continuousOn hf hB _) hM

/-- A weight continuous on `U` times a locally bounded PSH weight is integrable on `B`. -/
theorem integrableOn_mul_of_isLocallyBoundedPshOn {S : LocalProductCurrent n U m}
    (hS : IsPositive S) (hB : RelativelyCompactIn B U) {a g : E → ℝ} (ha : ContinuousOn a U)
    (hg : IsLocallyBoundedPshOn U g) : IntegrableOn (fun x => a x * g x) B hS.traceMeasure := by
  obtain ⟨M, hM⟩ := exists_bound_of_continuousOn ha hB
  obtain ⟨N, hN⟩ := exists_bound_of_isLocallyBoundedPshOn hg hB
  refine integrableOn_of_bounded hS hB ((aestronglyMeasurable_of_continuousOn ha hB _).mul
    (aestronglyMeasurable_of_isLocallyBoundedPshOn hg hB _)) (M := M * N) fun x hx => ?_
  rw [abs_mul]
  exact mul_le_mul (hM x hx) (hN x hx) (abs_nonneg _) ((abs_nonneg _).trans (hM x hx))

/-- **Monotonicity in the weight.** -/
theorem traceIntegral_mono {S : LocalProductCurrent n U m} (hS : IsPositive S) {f g : E → ℝ}
    (hf : IntegrableOn f B hS.traceMeasure) (hg : IntegrableOn g B hS.traceMeasure)
    (hfg : ∀ x ∈ (B : Set E), f x ≤ g x) : traceIntegral B f S ≤ traceIntegral B g S := by
  rw [traceIntegral_of_isPositive _ _ hS, traceIntegral_of_isPositive _ _ hS]
  exact setIntegral_mono_on hf hg B.isOpen.measurableSet hfg

end TraceIntegral

/-! ### Integration by parts on `B` without boundary terms -/

section Symmetry

variable {m : ℕ} {B : Opens (ComplexModel n)}

/-- `u Q` and `u' Q` agree on a test function `ψ` if `u = u'` wherever `ψ ≠ 0`. -/
theorem mulBorel_apply_eq_of_forall {Q : LocalProductCurrent n U m} (hQ : IsPositive Q)
    {u u' : E → ℝ} (hu : Measurable u) (hub : IsLocallyBoundedOn u U) (hu' : Measurable u')
    (hub' : IsLocallyBoundedOn u' U) (γ : formSpan n m) (ψ : 𝓓(U, ℝ))
    (h : ∀ x, ψ x ≠ 0 → u x = u' x) : mulBorel Q u γ ψ = mulBorel Q u' γ ψ := by
  rw [mulBorel_apply hQ hu hub, mulBorel_apply hQ hu' hub']
  congr 1
  funext x
  by_cases hx : ψ x = 0
  · simp [hx]
  · rw [h x hx]

/-- The test functions `∂_b∂_a(F φ) - φ ∂_b∂_a F` measuring the defect of `dd^c(F ·)` from
`F dd^c(·)`; they vanish where `φ` is locally constant. -/
def defectTest {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (a b : Fin (n * 2)) (φ : 𝓓(U, ℝ)) :
    𝓓(U, ℝ) :=
  dTest (realBasis n b) (dTest (realBasis n a) (mulSmoothOnCLM hF φ)) -
    mulSmoothOnCLM (contDiffOn_hessFun hF b a) φ

theorem ddc_sub_ddcWedge (R : LocalProductCurrent n U (m + 1)) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (γ : formSpan n m) (φ : 𝓓(U, ℝ)) :
    ddc R γ (mulSmoothOnCLM hF φ) - ddcWedge R hF γ φ = ∑ a, ∑ b, (-(1 / (4 * Real.pi))) *
      R (wedgeLM m (isOneOne_coeffForm a b) γ) (defectTest hF a b φ) := by
  have e : ddcWedge R hF γ φ = ∑ a, ∑ b, (-(1 / (4 * Real.pi))) *
      R (wedgeLM m (isOneOne_coeffForm a b) γ) (mulSmoothOnCLM (contDiffOn_hessFun hF b a) φ) := by
    rw [ddcWedge_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [wedgeLM_congr (isOneOne_coeffForm b a) (isOneOne_coeffForm a b) (coeffForm_comm b a)]
  rw [e, ddc_apply_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [defectTest, map_sub, mul_sub]

theorem dTest_eventuallyEq {ψ : 𝓓(U, ℝ)} {k : E → ℝ} {x : E} (h : (ψ : E → ℝ) =ᶠ[𝓝 x] k)
    (v : E) : (dTest v ψ : E → ℝ) =ᶠ[𝓝 x] dFun v k := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  rw [dTest_apply, dFun, hy.fderiv_eq]

theorem defectTest_eq_zero_of_eventually_zero {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    (a b : Fin (n * 2)) (φ : 𝓓(U, ℝ)) {x : E} (hφ : (φ : E → ℝ) =ᶠ[𝓝 x] 0) :
    defectTest hF a b φ x = 0 := by
  have h0 : (mulSmoothOnCLM hF φ : E → ℝ) =ᶠ[𝓝 x] 0 := hφ.mono fun y hy => by
    simp only [mulSmoothOnCLM_apply, hy, Pi.zero_apply, zero_mul]
  have h1 := dTest_eventuallyEq (dTest_eventuallyEq h0 (realBasis n a)) (realBasis n b)
  have hz : ∀ v : E, dFun v (0 : E → ℝ) = 0 := fun v => by
    funext y
    simp [dFun]
  rw [hz, hz] at h1
  rw [defectTest, _root_.sub_apply, h1.eq_of_nhds, mulSmoothOnCLM_apply, hφ.eq_of_nhds]
  simp

theorem defectTest_eq_zero_of_eventually_one {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    (a b : Fin (n * 2)) (φ : 𝓓(U, ℝ)) {x : E} (hφ : (φ : E → ℝ) =ᶠ[𝓝 x] 1) :
    defectTest hF a b φ x = 0 := by
  have h0 : (mulSmoothOnCLM hF φ : E → ℝ) =ᶠ[𝓝 x] F := hφ.mono fun y hy => by
    simp only [mulSmoothOnCLM_apply, hy, Pi.one_apply, one_mul]
  have h1 := dTest_eventuallyEq (dTest_eventuallyEq h0 (realBasis n a)) (realBasis n b)
  rw [defectTest, _root_.sub_apply, h1.eq_of_nhds, mulSmoothOnCLM_apply, hφ.eq_of_nhds]
  simp [hessFun]

/-- **The interior identity** `dd^c(u Q)(γ)(F φ) = (dd^c F ∧ u Q)(γ)(φ)` when `u = F` wherever one
of the defect tests of `φ` is nonzero. -/
theorem ddc_mulBorel_eq_ddcWedge {Q : LocalProductCurrent n U (m + 1)} (hQ : IsPositive Q)
    (hQc : IsClosedCurrent Q) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {u : E → ℝ}
    (hu : Measurable u) (hub : IsLocallyBoundedOn u U) (γ : formSpan n m) (φ : 𝓓(U, ℝ))
    (h : ∀ a b x, defectTest hF a b φ x ≠ 0 → u x = F x) :
    ddc (mulBorel Q u) γ (mulSmoothOnCLM hF φ) = ddcWedge (mulBorel Q u) hF γ φ := by
  set uF := (U : Set E).indicator F with huF_def
  have huF : Measurable uF := measurable_indicator_of_continuousOn hF.continuousOn
  have huFb : IsLocallyBoundedOn uF U :=
    isLocallyBoundedOn_indicator_of_continuousOn hF.continuousOn
  rw [← sub_eq_zero, ddc_sub_ddcWedge]
  have e : ∀ a b, mulBorel Q u (wedgeLM m (isOneOne_coeffForm a b) γ) (defectTest hF a b φ) =
      mulBorel Q uF (wedgeLM m (isOneOne_coeffForm a b) γ) (defectTest hF a b φ) := fun a b =>
    mulBorel_apply_eq_of_forall hQ hu hub huF huFb _ _ fun x hx => by
      have hxU : x ∈ (U : Set E) := by
        by_contra hxU
        exact hx (testFunction_eq_zero_of_notMem _ hxU)
      rw [h a b x hx, huF_def, Set.indicator_of_mem hxU]
  simp only [e]
  rw [← ddc_sub_ddcWedge, sub_eq_zero]
  have h1 : ddc (mulBorel Q uF) = ddcWedge Q hF := ddcMul_eq_ddcWedge hQ hQc hF
  rw [h1, ddcWedge_apply, ddcWedge_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  rw [mulBorel_apply hQ huF huFb, hQ.apply_eq_integral_density]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [mulSmoothOnCLM_apply]
  by_cases hx : x ∈ (U : Set E)
  · rw [huF_def, Set.indicator_of_mem hx]
    ring
  · rw [testFunction_eq_zero_of_notMem φ hx]
    ring

/-- **Integration by parts on `B` without boundary terms** (`bt:collar-comparison`, the identity
`(*)`): for `Q` positive closed of bidimension `(m+1,m+1)`, `g` locally bounded PSH, `F` smooth on
`U` with semipositive Levi form, and `F = g` on `B` off a compact subset of `B`,
`∫_B F dd^c(g Q) ∧ ω₀^m = ∫_B g dd^c F ∧ Q ∧ ω₀^m`. -/
theorem traceIntegral_ddcMul_eq {Q : LocalProductCurrent n U (m + 1)} (hQ : IsPositive Q)
    (hQc : IsClosedCurrent Q) {g : E → ℝ} (hg : IsLocallyBoundedPshOn U g) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hFl : ∀ x ∈ U, ∀ v, 0 ≤ leviForm F x v)
    (hB : RelativelyCompactIn B U) (hFg : EqOffCompact B F g) :
    traceIntegral B F (ddcMul Q g) = traceIntegral B g (ddcWedge Q hF) := by
  classical
  obtain ⟨K, hK, hKB, hFgK⟩ := hFg
  have hBU := subset_of_relativelyCompactIn hB
  have hS := (isPositive_ddcMul hQ hQc hg).1
  have hS' := isPositive_ddcWedge hQ hF hFl
  rw [traceIntegral_of_isPositive _ _ hS, traceIntegral_of_isPositive _ _ hS']
  set u := (U : Set E).indicator g with hu_def
  have hum := measurable_indicator_of_isLocallyBoundedPshOn hg
  have hub := isLocallyBoundedOn_indicator hg
  set uF := (U : Set E).indicator F with huF_def
  have huF : Measurable uF := measurable_indicator_of_continuousOn hF.continuousOn
  have huFb : IsLocallyBoundedOn uF U :=
    isLocallyBoundedOn_indicator_of_continuousOn hF.continuousOn
  have huu : ∀ x ∈ (B : Set E), x ∉ K → u x = F x := fun x hx hxK => by
    rw [hu_def, Set.indicator_of_mem (hBU hx)]
    exact (hFgK x hx hxK).symm
  -- the cutoff `χ`, equal to one near `K` and supported in `B`
  obtain ⟨χ, hχ, hχ1, hχB⟩ := exists_cutoff hK B.isOpen hKB
  have hχc : HasCompactSupport χ :=
    hB.1.of_isClosed_subset (isClosed_tsupport χ) (hχB.trans subset_closure)
  let χ' : 𝓓(U, ℝ) :=
    { toFun := χ, contDiff' := hχ, hasCompactSupport' := hχc,
      tsupport_subset' := hχB.trans hBU }
  have hχ'_apply : ∀ x, χ' x = χ x := fun x => rfl
  have hχ0 : ∀ x ∉ (B : Set E), χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hχB h)
  have hχK : ∀ x ∈ K, χ x = 1 := fun x hx => (hχ1 x hx).eq_of_nhds
  have hdef : ∀ a b x, defectTest hF a b χ' x ≠ 0 → x ∈ (B : Set E) ∧ x ∉ K := by
    intro a b x hx
    by_contra hc
    apply hx
    by_cases hxB : x ∈ (B : Set E)
    · have hxK : x ∈ K := by
        by_contra hxK
        exact hc ⟨hxB, hxK⟩
      exact defectTest_eq_zero_of_eventually_one hF a b χ' (hχ1 x hxK)
    · exact defectTest_eq_zero_of_eventually_zero hF a b χ'
        (notMem_tsupport_iff_eventuallyEq.mp fun h => hxB (hχB h))
  -- the interior parts
  have hint : ∫ x, χ x * F x ∂hS.traceMeasure = ∫ x, χ x * g x ∂hS'.traceMeasure := by
    have e1 : ∫ x, χ x * F x ∂hS.traceMeasure =
        ddcMul Q g (kahlerPower n m) (mulSmoothOnCLM hF χ') := by
      rw [← hS.integral_traceMeasure]
      rfl
    have hd : IsLocalDensity (U := U) hS'.traceMeasure (fun _ => 1) :=
      ⟨hS'.traceMeasure_compl, fun K hK hKU => hS'.traceMeasure_lt_top hK hKU,
        measurable_const, fun K _ _ => ⟨1, fun _ _ => by simp⟩⟩
    have e2 : ∫ x, χ x * g x ∂hS'.traceMeasure =
        mulBorel (ddcWedge Q hF) u (kahlerPower n m) χ' := by
      rw [mulBorel_apply_of_integral_eq hS' _ hd (fun ψ => by
        rw [← hS'.integral_traceMeasure]
        simp) hum hub χ']
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hχ'_apply, mul_one]
      by_cases hx : x ∈ (B : Set E)
      · rw [Set.indicator_of_mem (hBU hx)]
      · rw [hχ0 x hx, zero_mul, zero_mul]
    rw [e1, e2, ddcWedge_eq_wedgeForm, mulBorel_wedgeForm rfl hQ _ (ddcForm_mem_spCone hF hFl) hum
      hub, ← ddcWedge_eq_wedgeForm]
    exact ddc_mulBorel_eq_ddcWedge hQ hQc hF hum hub _ χ' fun a b x hx =>
      huu x (hdef a b x hx).1 (hdef a b x hx).2
  -- the collar parts: the two currents agree on `W = B \ K`
  let W : Opens (ComplexModel n) := ⟨(B : Set E) \ K, B.isOpen.sdiff hK.isClosed⟩
  have hWU : W ≤ U := fun x hx => hBU hx.1
  have hR : restrict hWU (ddcMul Q g) = restrict hWU (ddcWedge Q hF) := by
    ext γ φ
    rw [LocalBedfordTaylorLocality.restrict_apply, LocalBedfordTaylorLocality.restrict_apply,
      ← ddcMul_eq_ddcWedge hQ hQc hF]
    simp only [ddcMul, ddc_apply_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    refine mulBorel_apply_eq_of_forall hQ hum hub huF huFb _ _ fun x hx => ?_
    have hxs : x ∈ tsupport (extTest hWU φ : E → ℝ) := by
      by_contra hxs
      exact hx (image_eq_zero_of_notMem_tsupport fun h =>
        hxs (((tsupport_dTest_subset _ _).trans (tsupport_dTest_subset _ _)) h))
    have hφe : (extTest hWU φ : E → ℝ) = φ := funext (extTest_apply hWU φ)
    rw [hφe] at hxs
    have hxW : x ∈ (W : Set E) := φ.tsupport_subset hxs
    exact (huu x hxW.1 hxW.2).trans (by rw [huF_def, Set.indicator_of_mem (hBU hxW.1)])
  have hσ : hS.traceMeasure.restrict W = hS'.traceMeasure.restrict W := by
    rw [← traceMeasure_restrict hS hWU, ← traceMeasure_restrict hS' hWU]
    exact traceMeasure_congr hR _ _
  -- assembly
  have hsplit : ∀ (μ : Measure E) (f : E → ℝ),
      IntegrableOn (fun x => χ x * f x) B μ → IntegrableOn (fun x => (1 - χ x) * f x) B μ →
      ∫ x in B, f x ∂μ = ∫ x, χ x * f x ∂μ + ∫ x in W, (1 - χ x) * f x ∂μ := by
    intro μ f h1 h2
    have e : ∫ x in B, f x ∂μ = ∫ x in B, (χ x * f x + (1 - χ x) * f x) ∂μ := by
      congr 1
      funext x
      ring
    rw [e, integral_add h1 h2, setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [hχ0 x hx, zero_mul]),
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero B.isOpen.measurableSet
        (s := (W : Set E)) sdiff_subset (fun x hx => by
          have hxK : x ∈ K := by
            by_contra hxK
            exact hx.2 ⟨hx.1, hxK⟩
          rw [hχK x hxK, sub_self, zero_mul])]
  have hχc' : ContinuousOn χ U := hχ.continuous.continuousOn
  have h1χ : ContinuousOn (fun x => 1 - χ x) U := continuousOn_const.sub hχc'
  rw [hsplit _ F (integrableOn_of_continuousOn hS hB (hχc'.mul hF.continuousOn))
      (integrableOn_of_continuousOn hS hB (h1χ.mul hF.continuousOn)),
    hsplit _ g (integrableOn_mul_of_isLocallyBoundedPshOn hS' hB hχc' hg)
      (integrableOn_mul_of_isLocallyBoundedPshOn hS' hB h1χ hg), hint, hσ]
  congr 1
  refine setIntegral_congr_fun W.isOpen.measurableSet fun x hx => ?_
  rw [hFgK x hx.1 hx.2]

end Symmetry

/-! ### The comparison -/

section Comparison

variable {B : Opens (ComplexModel n)}

/-- **Smooth approximants from above with a fixed collar**: functions `F j` smooth on `U` with
semipositive Levi form on `U`, `≥ w` on `B`, equal to `h` on `B` off a compact subset of `B`,
uniformly bounded on `B` and converging to `w` pointwise on `B`. -/
structure IsCollarApprox (U : Opens (ComplexModel n)) (B : Set E) (h w : E → ℝ)
    (F : ℕ → E → ℝ) : Prop where
  contDiffOn : ∀ j, ContDiffOn ℝ ∞ (F j) U
  leviForm_nonneg : ∀ j, ∀ x ∈ U, ∀ v, 0 ≤ leviForm (F j) x v
  le : ∀ j, ∀ x ∈ B, w x ≤ F j x
  eqOffCompact : ∀ j, EqOffCompact B (F j) h
  bounded : ∃ M, ∀ j, ∀ x ∈ B, |F j x| ≤ M
  tendsto : ∀ x ∈ B, Tendsto (fun j => F j x) atTop (𝓝 (w x))

/-- **The common collar comparison** (`bt:collar-comparison`, `demailly-cadg:III.3.7`).  Let `T`
be positive closed of bidimension `(m + q, m + q)` on `U`, `B` relatively compact in `U`, and
`v_j ≤ w_j` (`0 ≤ j ≤ q`) locally bounded PSH on `U` with `v_j ≤ w_j` on `B`, all equal to one
function `h` on `B` off a compact subset of `B`, each `w_j` with smooth approximants from above
    with
the collar `h` (`IsCollarApprox`).  Then
`∫_B v₀ B(v₁, …, v_q; T) ∧ ω₀^m ≤ ∫_B w₀ B(w₁, …, w_q; T) ∧ ω₀^m`. -/
theorem traceIntegral_btProduct_le (hB : RelativelyCompactIn B U) {h : E → ℝ} : ∀ (q m : ℕ)
    (T : LocalProductCurrent n U (m + q)), IsPositive T → IsClosedAny (m + q) T →
    ∀ (v w : Fin (q + 1) → E → ℝ), (∀ i, IsLocallyBoundedPshOn U (v i)) →
    (∀ i, IsLocallyBoundedPshOn U (w i)) → (∀ i, ∀ x ∈ (B : Set E), v i x ≤ w i x) →
    (∀ i, EqOffCompact B (v i) h) → (∀ i, EqOffCompact B (w i) h) →
    (∀ i, ∃ F, IsCollarApprox U B h (w i) F) →
    traceIntegral B (v 0) (btProduct q m (Fin.tail v) T) ≤
      traceIntegral B (w 0) (btProduct q m (Fin.tail w) T)
  | 0, _, T, hT, _, v, w, hv, hw, hvw, _, _, _ =>
    traceIntegral_mono hT (integrableOn_of_isLocallyBoundedPshOn hT hB (hv 0))
      (integrableOn_of_isLocallyBoundedPshOn hT hB (hw 0)) (hvw 0)
  | q + 1, m, T, hT, hTc, v, w, hv, hw, hvw, hvh, hwh, happ => by
    have hmq : m + (q + 1) = m + 1 + q := by omega
    have hT' := isPositive_castLPC hmq hT
    have hT'c := isClosedAny_castLPC hmq hTc
    rw [btProduct_succ_eq_ddcMul q m (Fin.tail v) T (castLPC hmq T) (heq_castLPC hmq T),
      btProduct_succ_eq_ddcMul q m (Fin.tail w) T (castLPC hmq T) (heq_castLPC hmq T)]
    have hQv := isPositive_btProduct q (m + 1) (Fin.tail (Fin.tail v)) (castLPC hmq T) hT' hT'c
      fun i => hv _
    have hQw := isPositive_btProduct q (m + 1) (Fin.tail (Fin.tail w)) (castLPC hmq T) hT' hT'c
      fun i => hw _
    obtain ⟨F, hF⟩ := happ 0
    have hSv : IsPositive (ddcMul (btProduct q (m + 1) (Fin.tail (Fin.tail v)) (castLPC hmq T))
        (Fin.tail v 0)) := (isPositive_ddcMul hQv.1 hQv.2 (hv _)).1
    have hSw : IsPositive (ddcMul (btProduct q (m + 1) (Fin.tail (Fin.tail w)) (castLPC hmq T))
        (Fin.tail w 0)) := (isPositive_ddcMul hQw.1 hQw.2 (hw _)).1
    have hh : m + q + 1 = m + 1 + q := by omega
    have key : ∀ j, traceIntegral B (v 0)
        (ddcMul (btProduct q (m + 1) (Fin.tail (Fin.tail v)) (castLPC hmq T)) (Fin.tail v 0)) ≤
        traceIntegral B (F j)
          (ddcMul (btProduct q (m + 1) (Fin.tail (Fin.tail w)) (castLPC hmq T))
            (Fin.tail w 0)) := by
      intro j
      have hFj := hF.contDiffOn j
      have hFl := hF.leviForm_nonneg j
      have hTα := isPositive_wedgeForm hh hT' (contDiffOn_ddcForm hFj) (ddcForm_mem_spCone hFj hFl)
      have hTαc := isClosedAny_wedgeForm hh hT'c (contDiffOn_ddcForm hFj)
        (ddcForm_mem_formSpan hFj hFl) fun x hx => extDeriv_ddcForm hFj hx
      calc traceIntegral B (v 0)
            (ddcMul (btProduct q (m + 1) (Fin.tail (Fin.tail v)) (castLPC hmq T)) (Fin.tail v 0))
          ≤ traceIntegral B (F j)
            (ddcMul (btProduct q (m + 1) (Fin.tail (Fin.tail v)) (castLPC hmq T))
              (Fin.tail v 0)) :=
            traceIntegral_mono hSv (integrableOn_of_isLocallyBoundedPshOn hSv hB (hv 0))
              (integrableOn_of_continuousOn hSv hB hFj.continuousOn) fun x hx =>
                (hvw 0 x hx).trans (hF.le j x hx)
        _ = traceIntegral B (Fin.tail v 0)
            (ddcWedge (btProduct q (m + 1) (Fin.tail (Fin.tail v)) (castLPC hmq T)) hFj) :=
            traceIntegral_ddcMul_eq hQv.1 hQv.2 (hv _) hFj hFl hB
              ((hF.eqOffCompact j).trans (hvh _).symm)
        _ = traceIntegral B (Fin.tail v 0)
            (btProduct q m (Fin.tail (Fin.tail v))
              (wedgeForm hh (castLPC hmq T) (contDiffOn_ddcForm hFj))) := by
            rw [btProduct_wedgeForm_ddcForm hFj hFl q m (Fin.tail (Fin.tail v)) (castLPC hmq T) hh
              hT' hT'c fun i => hv _]
        _ ≤ traceIntegral B (Fin.tail w 0)
            (btProduct q m (Fin.tail (Fin.tail w))
              (wedgeForm hh (castLPC hmq T) (contDiffOn_ddcForm hFj))) :=
            traceIntegral_btProduct_le hB q m _ hTα hTαc (Fin.tail v) (Fin.tail w)
              (fun i => hv _) (fun i => hw _) (fun i => hvw _) (fun i => hvh _) (fun i => hwh _)
              fun i => happ _
        _ = traceIntegral B (Fin.tail w 0)
            (ddcWedge (btProduct q (m + 1) (Fin.tail (Fin.tail w)) (castLPC hmq T)) hFj) := by
            rw [btProduct_wedgeForm_ddcForm hFj hFl q m (Fin.tail (Fin.tail w)) (castLPC hmq T) hh
              hT' hT'c fun i => hw _]
        _ = traceIntegral B (F j)
            (ddcMul (btProduct q (m + 1) (Fin.tail (Fin.tail w)) (castLPC hmq T))
              (Fin.tail w 0)) :=
            (traceIntegral_ddcMul_eq hQw.1 hQw.2 (hw _) hFj hFl hB
              ((hF.eqOffCompact j).trans (hwh _).symm)).symm
    refine ge_of_tendsto' (x := (atTop : Filter ℕ)) ?_ key
    simp only [traceIntegral_of_isPositive _ _ hSw]
    obtain ⟨M, hM⟩ := hF.bounded
    have : IsFiniteMeasure (hSw.traceMeasure.restrict B) :=
      isFiniteMeasure_restrict.mpr (traceMeasure_lt_top_of_relativelyCompactIn hSw hB).ne
    refine tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun j => aestronglyMeasurable_of_continuousOn (hF.contDiffOn j).continuousOn hB _)
      (integrable_const M) (fun j => ?_) ?_
    · filter_upwards [ae_restrict_mem B.isOpen.measurableSet] with x hx
      rw [Real.norm_eq_abs]
      exact hM j x hx
    · filter_upwards [ae_restrict_mem B.isOpen.measurableSet] with x hx
      exact hF.tendsto x hx

end Comparison

/-! ### The ball -/

section Ball

open Metric

/-- A semidefinite complex Hessian gives a semipositive Levi form. -/
theorem leviForm_nonneg_of_posSemidef {u : E → ℝ} {z : E} (hu : ContDiffAt ℝ 2 u z)
    (hH : (complexHessian u z).PosSemidef) (v : E) : 0 ≤ leviForm u z v := by
  have hv : (∑ j, ((star (v j)).re • coordinateVector j -
      (star (v j)).im • (Complex.I • coordinateVector j)) : ComplexModel n) = v := by
    ext i
    simp only [coordinateVector, WithLp.ofLp_sub, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Finset.sum_apply, Pi.sub_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single i (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
    simp [Complex.re_add_im]
  have key : star (fun i => star (v i)) ⬝ᵥ ((complexHessian u z).mulVec (fun i => star (v i))) =
      ((leviForm u z v : ℝ) : ℂ) := by
    rw [complexHessian_dotProduct_mulVec_eq_leviForm hu]
    congr 2
  have h0 := hH.dotProduct_mulVec_nonneg (fun i => star (v i))
  rw [key] at h0
  exact Complex.zero_le_real.mp h0

/-- The Levi form is invariant under translation. -/
theorem leviForm_comp_sub_const (φ : E → ℝ) (z₀ x v : E) :
    leviForm (fun y => φ (y - z₀)) x v = leviForm φ (x - z₀) v := by
  simp only [leviForm, realHessian, iteratedFDeriv_comp_sub]

/-- **`β = dd^c|z - z₀|² = ω₀ / π`**: the form `β` of `bt:collar-comparison` is `π⁻¹` times the
Kähler form `ω₀` of the trace measures. -/
theorem smoothDDC_norm_sub_sq (z₀ z : E) :
    smoothDDC (fun y => ‖y - z₀‖ ^ 2) z = (Real.pi)⁻¹ • kahlerForm n := by
  have h2 : ContDiffAt ℝ 2 (fun y : E => ‖y - z₀‖ ^ 2) z :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hH : ∀ a b : E, realHessian (fun y : E => ‖y - z₀‖ ^ 2) z a b = 2 * inner ℝ a b :=
    fun a b => by
      have e : realHessian (fun y : E => ‖y - z₀‖ ^ 2) z a b =
          realHessian (fun y : E => ‖y‖ ^ 2) (z - z₀) a b := by
        simp only [realHessian]
        rw [iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := fun y : E => ‖y‖ ^ 2) 2 z₀ z]
      rw [e, realHessian_norm_sq]
  ext w
  rw [eq_vec_two w, smoothDDC_apply_eq_realHessian h2, hH, hH,
    ContinuousAlternatingMap.smul_apply, kahlerForm, Kahler.fundamentalFormAlt_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Kahler.fundamentalForm]
  have hri : ∀ a b : E, inner ℝ a b = (inner ℂ a b).re := fun a b => by
    simp [PiLp.inner_apply, Complex.inner, Complex.re_sum, mul_comm]
  have hc : (inner ℂ (w 1) (w 0)).im = -(inner ℂ (w 0) (w 1)).im := by
    rw [← inner_conj_symm (w 0) (w 1), Complex.conj_im, neg_neg]
  rw [hri, hri, inner_smul_right, inner_smul_right, Complex.mul_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, hc, smul_eq_mul]
  field_simp
  ring

/-- `β^m = π^{-m} ω₀^m`: so `S ∧ β^m = π^{-m} S ∧ ω₀^m` for every current `S` of bidimension
`(m,m)`, and the integrals of `bt:collar-comparison` against `β^m` are `π^{-m}` times the
`traceIntegral`s. -/
theorem formPower_smoothDDC_norm_sub_sq (z₀ z : E) (m : ℕ) :
    formPower (smoothDDC (fun y => ‖y - z₀‖ ^ 2) z) m =
      ((Real.pi)⁻¹) ^ m • formPower (kahlerForm n) m := by
  rw [smoothDDC_norm_sub_sq]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [formPower_succ, formPower_succ, ih, coordinateWedge_smul_left,
      coordinateWedge_smul_right, smul_smul, pow_succ]

/-- **The collar potential** `h = A(|z - z₀|² - R²)`. -/
abbrev ballPot (A : ℝ) (z₀ : E) (R : ℝ) (z : E) : ℝ :=
  SmoothMax.quadraticCollar z₀ A R z

theorem contDiff_ballPot (A : ℝ) (z₀ : E) (R : ℝ) : ContDiff ℝ ∞ (ballPot A z₀ R) :=
  SmoothMax.contDiff_quadraticCollar z₀ A R

theorem leviForm_ballPot (A : ℝ) (z₀ : E) (R : ℝ) (x v : E) :
    leviForm (ballPot A z₀ R) x v = A * ‖v‖ ^ 2 := by
  have e : ballPot A z₀ R = fun y => (fun w : E => A * (‖w‖ ^ 2 - R ^ 2)) (y - z₀) := rfl
  rw [e]
  refine (leviForm_comp_sub_const (fun w : E => A * (‖w‖ ^ 2 - R ^ 2)) z₀ x v).trans ?_
  have e2 : (fun w : E => A * (‖w‖ ^ 2 - R ^ 2)) =
      A • (fun w : E => ‖w‖ ^ 2) + fun _ => -(A * R ^ 2) := by
    funext w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h2 : ContDiffAt ℝ 2 (fun w : E => ‖w‖ ^ 2) (x - z₀) :=
    (contDiff_norm_sq ℝ).contDiffAt
  rw [e2, leviForm_add (u := A • fun w : E => ‖w‖ ^ 2) (v := fun _ => -(A * R ^ 2))
    (h2.const_smul A) contDiffAt_const, leviForm_smul h2, leviForm_norm_sq, leviForm_const,
    add_zero]

theorem isLocallyBoundedPshOn_ballPot {A : ℝ} (hA : 0 ≤ A) (z₀ : E) (R : ℝ) :
    IsLocallyBoundedPshOn U (ballPot A z₀ R) := by
  refine ⟨plurisubharmonicOn_of_levi_nonneg
    ((contDiff_ballPot A z₀ R).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    U.isOpen fun x _ v => by rw [leviForm_ballPot]; positivity, fun z hz => ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen z hz
  obtain ⟨C, hC⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn
    (contDiff_ballPot A z₀ R).continuous.continuousOn
  exact ⟨⟨ball z r, isOpen_ball⟩, mem_ball_self hr, fun w hw => hball hw, C, fun w hw => by
    simpa [Real.norm_eq_abs] using hC w (ball_subset_closedBall hw)⟩

theorem isLocallyBoundedPshOn_max {f g : E → ℝ} (hf : IsLocallyBoundedPshOn U f)
    (hg : IsLocallyBoundedPshOn U g) : IsLocallyBoundedPshOn U fun z => max (f z) (g z) := by
  refine ⟨?_, fun z hz => ?_⟩
  · simpa only [EReal.coe_strictMono.monotone.map_max] using hf.1.max hg.1
  · obtain ⟨V, hzV, hVΩ, C, hC⟩ := hf.2 z hz
    obtain ⟨V', hzV', -, C', hC'⟩ := hg.2 z hz
    exact ⟨V ⊓ V', ⟨hzV, hzV'⟩, inf_le_left.trans hVΩ, C ⊔ C', fun y hy =>
      abs_max_le_max_abs_abs.trans (max_le_max (hC y hy.1) (hC' y hy.2))⟩

/-- **The collar modification** `max(A(|z - z₀|² - R²), a)`. -/
def collarMax (A : ℝ) (z₀ : E) (R : ℝ) (a : E → ℝ) (z : E) : ℝ := max (ballPot A z₀ R z) (a z)

theorem isLocallyBoundedPshOn_collarMax {A : ℝ} (hA : 0 ≤ A) (z₀ : E) (R : ℝ) {a : E → ℝ}
    (ha : IsLocallyBoundedPshOn U a) : IsLocallyBoundedPshOn U (collarMax A z₀ R a) :=
  isLocallyBoundedPshOn_max (isLocallyBoundedPshOn_ballPot hA z₀ R) ha

/-- The core `{|z - z₀| ≤ R, h(z) ≤ -1/2}` off which all the collar modifications equal `h`. -/
def collarCore (A : ℝ) (z₀ : E) (R : ℝ) : Set E :=
  closedBall z₀ R ∩ {z | ballPot A z₀ R z ≤ -1 / 2}

theorem isCompact_collarCore (A : ℝ) (z₀ : E) (R : ℝ) : IsCompact (collarCore A z₀ R) :=
  (isCompact_closedBall z₀ R).inter_right
    (isClosed_le (contDiff_ballPot A z₀ R).continuous continuous_const)

theorem collarCore_subset_ball {A : ℝ} (hA : 0 < A) (z₀ : E) (R : ℝ) :
    collarCore A z₀ R ⊆ ball z₀ R := by
  intro z hz
  rw [mem_ball, dist_eq_norm]
  by_contra hzR
  push Not at hzR
  have h1 : R ^ 2 ≤ ‖z - z₀‖ ^ 2 := by
    have hR : 0 ≤ R := le_trans dist_nonneg (mem_closedBall.mp hz.1)
    nlinarith
  have h2 : ballPot A z₀ R z ≤ -1 / 2 := hz.2
  have h3 : 0 ≤ ballPot A z₀ R z := mul_nonneg hA.le (by linarith)
  linarith

theorem lt_ballPot_of_notMem_collarCore {A : ℝ} {z₀ z : E} {R : ℝ} (hz : z ∈ ball z₀ R)
    (hzK : z ∉ collarCore A z₀ R) : -1 / 2 < ballPot A z₀ R z := by
  by_contra h
  exact hzK ⟨ball_subset_closedBall hz, not_lt.mp h⟩

/-- The collar modification of a function `≤ -1` equals `h` off the core. -/
theorem eqOffCompact_collarMax {A : ℝ} (hA : 0 < A) (z₀ : E) (R : ℝ) {a : E → ℝ}
    (ha : ∀ z ∈ closedBall z₀ R, a z ≤ -1) :
    EqOffCompact (ball z₀ R) (collarMax A z₀ R a) (ballPot A z₀ R) :=
  ⟨collarCore A z₀ R, isCompact_collarCore A z₀ R, collarCore_subset_ball hA z₀ R,
    fun z hz hzK => max_eq_left (by
      linarith [ha z (ball_subset_closedBall hz), lt_ballPot_of_notMem_collarCore hz hzK])⟩

/-- **A Dini argument**: a pointwise decreasing sequence of continuous functions with limit
`< c` on a compact set is eventually `< c` on it. -/
theorem exists_forall_lt_of_antitone {V : Set E} (hV : IsOpen V) {C : Set E} (hC : IsCompact C)
    (hCV : C ⊆ V) {f : ℕ → E → ℝ} (hf : ∀ j, ContinuousOn (f j) V)
    (hanti : ∀ z ∈ V, Antitone fun j => f j z) {b : E → ℝ}
    (hlim : ∀ z ∈ V, Tendsto (fun j => f j z) atTop (𝓝 (b z))) {c : ℝ}
    (hb : ∀ z ∈ C, b z < c) : ∃ j₀, ∀ j ≥ j₀, ∀ z ∈ C, f j z < c := by
  let O : ℕ → Set E := fun j => V ∩ f j ⁻¹' Iio c
  have hO : ∀ j, IsOpen (O j) := fun j => (hf j).isOpen_inter_preimage hV isOpen_Iio
  have hmono : Monotone O := fun i j hij z hz =>
    ⟨hz.1, lt_of_le_of_lt (hanti z hz.1 hij) hz.2⟩
  have hcov : C ⊆ ⋃ j, O j := fun z hz => by
    obtain ⟨j, hj⟩ := ((hlim z (hCV hz)).eventually (gt_mem_nhds (hb z hz))).exists
    exact mem_iUnion.mpr ⟨j, hCV hz, hj⟩
  obtain ⟨j₀, hj₀⟩ := hC.elim_directed_cover O hO hcov hmono.directed_le
  exact ⟨j₀, fun j hj z hz => lt_of_le_of_lt (hanti z (hCV hz) hj) (hj₀ hz).2⟩

/-- **Smooth approximants from above with the collar `h`** of `w = max(h, b)` (`b ≤ -1` on the
closed ball), smooth with semipositive Levi form on a neighbourhood `A'` of the closed ball:
`F_j = M_{δ_j}(h, f_{j + j₀})`, the regularized maximum of `h` and a decreasing smooth PSH
approximation of `b`, with `δ_j ↓ 0`. -/
theorem exists_isCollarApprox {A' : Opens (ComplexModel n)} (hA'U : RelativelyCompactIn A' U)
    {z₀ : E} {R A : ℝ} (hA : 0 < A) (hBA : closedBall z₀ R ⊆ A') {b : E → ℝ}
    (hb : IsLocallyBoundedPshOn U b) (hb1 : ∀ z ∈ closedBall z₀ R, b z ≤ -1) :
    ∃ F, IsCollarApprox A' (ball z₀ R) (ballPot A z₀ R) (collarMax A z₀ R b) F := by
  obtain ⟨f, hfs, hanti, hlim⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hb
    hA'U
  set h := ballPot A z₀ R with h_def
  have hC : IsCompact (closedBall z₀ R ∩ {z | -1 / 2 ≤ h z}) :=
    (isCompact_closedBall z₀ R).inter_right
      (isClosed_le continuous_const (contDiff_ballPot A z₀ R).continuous)
  obtain ⟨j₀, hj₀⟩ := exists_forall_lt_of_antitone A'.isOpen hC
    (fun z hz => hBA hz.1) (fun j => (hfs j).1.continuousOn) hanti hlim (c := -3 / 4)
    fun z hz => by linarith [hb1 z hz.1]
  set δ : ℕ → ℝ := fun j => 1 / 4 * (1 / ((j : ℝ) + 1)) with hδ_def
  have hδpos : ∀ j, 0 < δ j := fun j => by positivity
  have hδle : ∀ j, δ j ≤ 1 / 4 := fun j => by
    have : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    simp only [hδ_def]
    nlinarith
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 4)
    rw [mul_zero] at this
    exact this
  have hh : ContDiff ℝ ∞ h := contDiff_ballPot A z₀ R
  have hblef : ∀ z ∈ (A' : Set E), ∀ j, b z ≤ f j z := fun z hz j =>
    (hanti z hz).le_of_tendsto (hlim z hz) j
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall z₀ R).exists_bound_of_continuousOn
    ((hfs j₀).1.continuousOn.mono hBA)
  refine ⟨fun j => ScaledSmoothMax.scaledSmoothMax (δ j) h (f (j + j₀)),
    ⟨fun j => ?_, fun j x hx v => ?_, fun j z hz => ?_, fun j => ?_, ?_, fun z hz => ?_⟩⟩
  · -- smoothness
    have e : ScaledSmoothMax.scaledSmoothMax (δ j) h (f (j + j₀)) = fun z =>
        f (j + j₀) z + δ j * SmoothMax.posPart ((h z - f (j + j₀) z) / δ j) := rfl
    rw [e]
    exact (hfs _).1.add (contDiffOn_const.mul (SmoothMax.contDiff_posPart.comp_contDiffOn
      ((hh.contDiffOn.sub (hfs _).1).div_const _)))
  · -- semipositive Levi form
    have h2 : ∀ {g : E → ℝ}, ContDiffOn ℝ ∞ g A' → ContDiffAt ℝ 2 g x := fun hg =>
      (hg.contDiffAt (A'.isOpen.mem_nhds hx)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hF2 : ContDiffAt ℝ 2 (ScaledSmoothMax.scaledSmoothMax (δ j) h (f (j + j₀))) x := by
      have e : ScaledSmoothMax.scaledSmoothMax (δ j) h (f (j + j₀)) = fun z =>
          f (j + j₀) z + δ j * SmoothMax.posPart ((h z - f (j + j₀) z) / δ j) := rfl
      rw [e]
      exact h2 ((hfs _).1.add (contDiffOn_const.mul (SmoothMax.contDiff_posPart.comp_contDiffOn
        ((hh.contDiffOn.sub (hfs _).1).div_const _))))
    have hHh : (complexHessian h x).PosSemidef :=
      SmoothDDCHessianPositivity.complexHessian_posSemidef_of_leviForm_nonneg
        (h2 hh.contDiffOn) fun v => by rw [h_def, leviForm_ballPot]; positivity
    exact leviForm_nonneg_of_posSemidef hF2
      (ScaledSmoothMax.complexHessian_scaledSmoothMax_posSemidef (h2 hh.contDiffOn)
        (h2 (hfs _).1) hHh ((hfs _).2.2 x hx) (hδpos j)) v
  · -- above `w`
    have hzA : z ∈ (A' : Set E) := hBA (ball_subset_closedBall hz)
    exact (max_le_max le_rfl (hblef z hzA _)).trans
      (ScaledSmoothMax.max_le_scaledSmoothMax (hδpos j) _ _ z)
  · -- the collar
    refine ⟨collarCore A z₀ R, isCompact_collarCore A z₀ R, collarCore_subset_ball hA z₀ R,
      fun z hz hzK => ?_⟩
    have hhz := lt_ballPot_of_notMem_collarCore hz hzK
    have hfz := hj₀ (j + j₀) (by omega) z ⟨ball_subset_closedBall hz, hhz.le⟩
    exact ScaledSmoothMax.scaledSmoothMax_eq_left (hδpos j) (by linarith [hδle j])
  · -- uniform bound
    refine ⟨max (A * R ^ 2) (M₀ + 1), fun j z hz => ?_⟩
    have hzA : z ∈ (A' : Set E) := hBA (ball_subset_closedBall hz)
    have hz' : ‖z - z₀‖ < R := by rw [← dist_eq_norm]; exact hz
    have hh0 : h z < 0 := by
      simp only [h_def, SmoothMax.quadraticCollar]
      have : ‖z - z₀‖ ^ 2 < R ^ 2 := by
        have := norm_nonneg (z - z₀)
        nlinarith
      nlinarith
    have hhl : -(A * R ^ 2) ≤ h z := by
      simp only [h_def, SmoothMax.quadraticCollar]
      nlinarith [sq_nonneg ‖z - z₀‖]
    have hlo := (le_max_left (h z) (f (j + j₀) z)).trans
      (ScaledSmoothMax.max_le_scaledSmoothMax (hδpos j) h (f (j + j₀)) z)
    have hup := ScaledSmoothMax.scaledSmoothMax_le_max_add (hδpos j) h (f (j + j₀)) z
    have hfj0 : |f j₀ z| ≤ M₀ := by
      have h2 := hM₀ z (ball_subset_closedBall hz)
      rwa [Real.norm_eq_abs] at h2
    have hM₀0 : 0 ≤ M₀ := (abs_nonneg _).trans hfj0
    have hfj : f (j + j₀) z ≤ M₀ := by
      have h1 := hanti z hzA (show j₀ ≤ j + j₀ by omega)
      linarith [le_abs_self (f j₀ z)]
    have hmx : max (h z) (f (j + j₀) z) ≤ M₀ + 1 - 1 / 4 :=
      max_le (by linarith) (by linarith)
    rw [abs_le]
    constructor
    · linarith [le_max_left (A * R ^ 2) (M₀ + 1)]
    · linarith [hδle j, le_max_right (A * R ^ 2) (M₀ + 1)]
  · -- convergence
    have hzA : z ∈ (A' : Set E) := hBA (ball_subset_closedBall hz)
    have hf' : Tendsto (fun j => f (j + j₀) z) atTop (𝓝 (b z)) :=
      (hlim z hzA).comp (tendsto_add_atTop_nat j₀)
    have hmax : Tendsto (fun j => max (h z) (f (j + j₀) z)) atTop (𝓝 (max (h z) (b z))) :=
      tendsto_const_nhds.max hf'
    have hmax' : Tendsto (fun j => max (h z) (f (j + j₀) z) + δ j) atTop
        (𝓝 (max (h z) (b z))) := by simpa using hmax.add hδ0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hmax hmax'
      (fun j => ScaledSmoothMax.max_le_scaledSmoothMax (hδpos j) h (f (j + j₀)) z)
      (fun j => ScaledSmoothMax.scaledSmoothMax_le_max_add (hδpos j) h (f (j + j₀)) z)

/-- The integral over `B ⊆ V` does not see the restriction to `V`. -/
theorem traceIntegral_restrict {V : Opens (ComplexModel n)} (hVU : V ≤ U) {m : ℕ}
    {S : LocalProductCurrent n U m} (hS : IsPositive S) {B : Set E} (hB : MeasurableSet B)
    (hBV : B ⊆ V) (f : E → ℝ) : traceIntegral B f (restrict hVU S) = traceIntegral B f S := by
  rw [traceIntegral_of_isPositive _ _ (isPositive_restrict hS hVU),
    traceIntegral_of_isPositive _ _ hS, traceMeasure_restrict hS hVU,
    Measure.restrict_restrict hB, Set.inter_eq_left.mpr hBV]

/-- **The common collar comparison on a ball** (`bt:collar-comparison`,
`demailly-cadg:III.3.7`).  Let `B = B(z₀, R)` with `BBar ⊆ U`, `T` positive closed of bidimension
`(m + q, m + q)` on `U`, and `a_j ≤ b_j ≤ -1` on `BBar` (`0 ≤ j ≤ q`) locally bounded PSH on `U`.
With `h = A(|z - z₀|² - R²)`, `A > 0`, `v_j = max(h, a_j)` and `w_j = max(h, b_j)`,
`∫_B v₀ B(v₁, …, v_q; T) ∧ ω₀^m ≤ ∫_B w₀ B(w₁, …, w_q; T) ∧ ω₀^m`. -/
theorem collar_comparison {z₀ : E} {R A : ℝ} (hR : 0 < R) (hA : 0 < A)
    (hBU : closedBall z₀ R ⊆ U) {q m : ℕ} (T : LocalProductCurrent n U (m + q))
    (hT : IsPositive T) (hTc : IsClosedAny (m + q) T) (a b : Fin (q + 1) → E → ℝ)
    (ha : ∀ i, IsLocallyBoundedPshOn U (a i)) (hb : ∀ i, IsLocallyBoundedPshOn U (b i))
    (hab : ∀ i, ∀ z ∈ closedBall z₀ R, a i z ≤ b i z)
    (hb1 : ∀ i, ∀ z ∈ closedBall z₀ R, b i z ≤ -1) :
    traceIntegral (ball z₀ R) (collarMax A z₀ R (a 0))
        (btProduct q m (fun i => collarMax A z₀ R (a i.succ)) T) ≤
      traceIntegral (ball z₀ R) (collarMax A z₀ R (b 0))
        (btProduct q m (fun i => collarMax A z₀ R (b i.succ)) T) := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall z₀ R).exists_cthickening_subset_open U.isOpen hBU
  rw [cthickening_closedBall hδ.le hR.le] at hδU
  let A' : Opens (ComplexModel n) := ⟨ball z₀ (δ + R), isOpen_ball⟩
  let B' : Opens (ComplexModel n) := ⟨ball z₀ R, isOpen_ball⟩
  have hcl : ∀ r : ℝ, 0 < r → closure (ball z₀ r) = closedBall z₀ r := fun r hr =>
    closure_ball z₀ hr.ne'
  have hA'U : RelativelyCompactIn A' U := by
    refine ⟨?_, ?_⟩
    · change IsCompact (closure (ball z₀ (δ + R)))
      rw [hcl _ (by linarith)]
      exact isCompact_closedBall _ _
    · change closure (ball z₀ (δ + R)) ⊆ U
      rw [hcl _ (by linarith)]
      exact hδU
  have hle : A' ≤ U := fun z hz => hδU (ball_subset_closedBall hz)
  have hBA : closedBall z₀ R ⊆ (A' : Set E) := closedBall_subset_ball (by linarith)
  have hB'A' : RelativelyCompactIn B' A' := by
    refine ⟨?_, ?_⟩
    · change IsCompact (closure (ball z₀ R))
      rw [hcl _ hR]
      exact isCompact_closedBall _ _
    · change closure (ball z₀ R) ⊆ (A' : Set E)
      rw [hcl _ hR]
      exact hBA
  set v : Fin (q + 1) → E → ℝ := fun i => collarMax A z₀ R (a i) with hv_def
  set w : Fin (q + 1) → E → ℝ := fun i => collarMax A z₀ R (b i) with hw_def
  have hv : ∀ i, IsLocallyBoundedPshOn U (v i) := fun i =>
    isLocallyBoundedPshOn_collarMax hA.le z₀ R (ha i)
  have hw : ∀ i, IsLocallyBoundedPshOn U (w i) := fun i =>
    isLocallyBoundedPshOn_collarMax hA.le z₀ R (hb i)
  have key := traceIntegral_btProduct_le hB'A' (h := ballPot A z₀ R) q m (restrict hle T)
    (isPositive_restrict hT hle) (isClosedAny_restrict hTc hle) v w
    (fun i => isLocallyBoundedPshOn_mono (hv i) hle) (fun i => isLocallyBoundedPshOn_mono (hw i)
      hle)
    (fun i z hz => max_le_max le_rfl (hab i z (ball_subset_closedBall hz)))
    (fun i => eqOffCompact_collarMax hA z₀ R fun z hz => (hab i z hz).trans (hb1 i z hz))
    (fun i => eqOffCompact_collarMax hA z₀ R (hb1 i))
    (fun i => exists_isCollarApprox hA'U hA hBA (hb i) (hb1 i))
  have hPv := (isPositive_btProduct q m (Fin.tail v) T hT hTc fun i => hv _).1
  have hPw := (isPositive_btProduct q m (Fin.tail w) T hT hTc fun i => hw _).1
  rw [btProduct_restrict hle q m (Fin.tail v) T hT hTc (fun i => hv _),
    btProduct_restrict hle q m (Fin.tail w) T hT hTc (fun i => hw _),
    traceIntegral_restrict hle hPv (B := (B' : Set E)) B'.isOpen.measurableSet
      (ball_subset_closedBall.trans hBA),
    traceIntegral_restrict hle hPw (B := (B' : Set E)) B'.isOpen.measurableSet
      (ball_subset_closedBall.trans hBA)] at key
  exact key

/-- **Large `A` leaves the potentials unchanged near a compact subset of the ball**: for compact
`K ⊆ B(z₀, R)` and `M`, there are `A₀ > 0` and an open `V ⊇ K` with `max(h, a) = a` on `V` for
every `A ≥ A₀` and every `a ≥ -M` on `V`. -/
theorem collarMax_eq_of_le {z₀ : E} {R : ℝ} (hR : 0 < R) {K : Set E} (hK : IsCompact K)
    (hKB : K ⊆ ball z₀ R) (M : ℝ) :
    ∃ A₀ > 0, ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ ∀ A ≥ A₀, ∀ a : E → ℝ, ∀ z ∈ V, -M ≤ a z →
      collarMax A z₀ R a z = a z := by
  obtain ⟨r, hrR, hKr⟩ := exists_lt_subset_ball hK.isClosed hKB
  set r₁ := max r 0 with hr₁
  have hr₁R : r₁ < R := max_lt hrR hR
  have hr₁0 : 0 ≤ r₁ := le_max_right r 0
  have hgap : 0 < R ^ 2 - r₁ ^ 2 := by nlinarith
  refine ⟨max 1 (M / (R ^ 2 - r₁ ^ 2)), lt_of_lt_of_le one_pos (le_max_left _ _), ball z₀ r₁,
    isOpen_ball, hKr.trans (ball_subset_ball (le_max_left r 0)), fun A hA a z hz haz => ?_⟩
  have hA1 : M ≤ A * (R ^ 2 - r₁ ^ 2) := by
    have := (div_le_iff₀ hgap).mp ((le_max_right 1 _).trans hA)
    linarith
  have hz' : ‖z - z₀‖ ^ 2 < r₁ ^ 2 := by
    have h1 : ‖z - z₀‖ < r₁ := by rw [← dist_eq_norm]; exact hz
    have := norm_nonneg (z - z₀)
    nlinarith
  have hA0 : 0 ≤ A := (zero_le_one.trans (le_max_left _ _)).trans hA
  apply max_eq_right
  simp only [SmoothMax.quadraticCollar]
  nlinarith

end Ball

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
