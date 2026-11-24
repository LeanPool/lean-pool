/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.StronglyPositiveForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.KahlerDomination
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.FormPullback
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentials
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

/-!
# Test forms spanned by products of real `(1,1)`-forms

On a complex manifold `M` of dimension `n`, `testSpace q` is the real span of the global
smooth forms `h · β₁ ∧ ⋯ ∧ β_q` with `h` a smooth function and `β_j` smooth real
`(1,1)`-forms (degree `2q`), and `positiveCone q` consists of those whose value at every
point is strongly positive (`StronglyPositiveForms.spCone`).  By the basis theorem for
strongly positive forms (`demailly-cadg:III.1.4`: the forms `i γ₁ ∧ γBar₁ ∧ ⋯ ∧ i γ_q ∧ γBar_q`
span the real `(q,q)`-forms) this span is the space of smooth real `(q,q)`-forms; that
identification is NOT formalized here, and nothing below depends on it: the positive
currents of `Pending.PositiveProductCurrents` are functionals on `testSpace q` itself.

The construction needs, and supplies, the linear structure of `FirstPass.SmoothRealForm`
(pointwise in the charts), multiplication by chart-smooth functions, and the exterior
product with a two-form (`wedgeTwo`, pointwise `coordinateWedge`, smooth because the
exterior product is a continuous bilinear map of finite-dimensional spaces).

## Main results

* `instAddCommGroup`, `instModule` — `SmoothRealForm n M k` is a real vector space.
* `unitForm`, `smulFun`, `wedgeTwo`, `formPow` — the constant `1`, function multiples,
  the wedge with a two-form, the powers `ω^q`.
* `testSpace`, `positiveCone`; `formPow_mem_testSpace`, `formPow_mem_positiveCone`.
* `exists_orderUnit_bound` — on a COMPACT manifold with a Kähler form `ω`, every test form
  `φ` satisfies `c ω^q ± φ ∈ positiveCone` for some `c ≥ 0`: `ω^q` is an order unit.
  (Inductive step: `StronglyPositiveForms.orderUnit_step`; the uniform constants come from
  compactness, `KahlerDomination.exists_isSemipositive_add_smul` for the two-forms and the
  boundedness of continuous functions for the coefficients.)
* `pullback_wedgeTwo`, `pullback_smulFun`, `pullback_mem_testSpace`,
  `pullback_mem_positiveCone` — pullback along a holomorphic map preserves test forms
  and positive test forms; `pullbackTestLM` is the induced linear map.
-/

@[expose] public section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.ProductTestForms

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms

noncomputable section

/-! ### The exterior product is smooth -/

section Pointwise

variable {n : ℕ}

/-- Continuous alternating forms on the model space form a finite-dimensional space. -/
theorem realForm_finiteDimensional (k : ℕ) : FiniteDimensional ℝ (RealForm n k) := by
  let A : (ContinuousMultilinearMap ℝ (fun _ : Fin k => ComplexModel n) ℝ) →ₗ[ℝ]
      MultilinearMap (RingHom.id ℝ) (fun _ : Fin k => ComplexModel n) ℝ :=
    { toFun := ContinuousMultilinearMap.toMultilinearMap
      map_add' := ContinuousMultilinearMap.toMultilinearMap_add
      map_smul' := ContinuousMultilinearMap.toMultilinearMap_smul }
  have : FiniteDimensional ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => ComplexModel n) ℝ) :=
    FiniteDimensional.of_injective A ContinuousMultilinearMap.toMultilinearMap_injective
  exact FiniteDimensional.of_injective
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ (𝕜 := ℝ)
      (E := ComplexModel n) (F := ℝ) (ι := Fin k)).toLinearMap
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective

/-- The exterior product with a two-form, as a continuous bilinear map. -/
def wedgeCLM (n p : ℕ) : RealForm n p →L[ℝ] RealForm n 2 →L[ℝ] RealForm n (p + 2) :=
  haveI := realForm_finiteDimensional (n := n) p
  haveI := realForm_finiteDimensional (n := n) 2
  LinearMap.toContinuousLinearMap
    { toFun := fun A => LinearMap.toContinuousLinearMap (wedgeBilin n p A)
      map_add' := fun A A' => by
        ext B : 1
        simp only [LinearMap.coe_toContinuousLinearMap', add_apply,
          map_add]
      map_smul' := fun c A => by
        ext B : 1
        simp only [LinearMap.coe_toContinuousLinearMap', smul_apply,
          map_smul, RingHom.id_apply] }

@[simp] theorem wedgeCLM_apply {p : ℕ} (A : RealForm n p) (B : RealForm n 2) :
    wedgeCLM n p A B = coordinateWedge A B := rfl

theorem contDiffOn_coordinateWedge {p : ℕ} {U : Set (ComplexModel n)}
    {A : ComplexModel n → RealForm n p} {B : ComplexModel n → RealForm n 2}
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun z => coordinateWedge (A z) (B z)) U :=
  (((wedgeCLM n p).contDiff.comp_contDiffOn hA).clm_apply hB).congr fun _ _ => rfl

end Pointwise

/-! ### The vector space of smooth forms -/

section Algebra

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {k : ℕ}

theorem smoothRealForm_ext {a b : SmoothRealForm n M k}
    (h : ∀ e z, a.coeff e z = b.coeff e z) : a = b := by
  rcases a with ⟨ac, as, ap⟩
  rcases b with ⟨bc, bs, bp⟩
  have hc : ac = bc := funext fun e => funext fun z => h e z
  subst hc
  rfl

instance instZero : Zero (SmoothRealForm n M k) := ⟨SmoothRealForm.zero⟩

instance instAdd : Add (SmoothRealForm n M k) where
  add a b :=
    { coeff := fun e z => a.coeff e z + b.coeff e z
      smooth := fun e => (a.smooth e).add (b.smooth e)
      compatible := fun e f z hz v => by
        simp only [ContinuousAlternatingMap.add_apply, a.compatible e f z hz v,
          b.compatible e f z hz v] }

instance instSMul : SMul ℝ (SmoothRealForm n M k) where
  smul c a :=
    { coeff := fun e z => c • a.coeff e z
      smooth := fun e => (a.smooth e).const_smul c
      compatible := fun e f z hz v => by
        simp only [ContinuousAlternatingMap.smul_apply, a.compatible e f z hz v] }

instance instNeg : Neg (SmoothRealForm n M k) where
  neg a :=
    { coeff := fun e z => -a.coeff e z
      smooth := fun e => (a.smooth e).neg
      compatible := fun e f z hz v => by
        simp only [ContinuousAlternatingMap.neg_apply, a.compatible e f z hz v] }

instance instSub : Sub (SmoothRealForm n M k) where
  sub a b :=
    { coeff := fun e z => a.coeff e z - b.coeff e z
      smooth := fun e => (a.smooth e).sub (b.smooth e)
      compatible := fun e f z hz v => by
        simp only [ContinuousAlternatingMap.sub_apply, a.compatible e f z hz v,
          b.compatible e f z hz v] }

instance instNSMul : SMul ℕ (SmoothRealForm n M k) := ⟨fun m a => (m : ℝ) • a⟩

instance instZSMul : SMul ℤ (SmoothRealForm n M k) := ⟨fun m a => (m : ℝ) • a⟩

@[simp] theorem coeff_zero (e : ComplexChart n M) (z : ComplexModel n) :
    (0 : SmoothRealForm n M k).coeff e z = 0 := rfl

@[simp] theorem coeff_add (a b : SmoothRealForm n M k) (e : ComplexChart n M)
    (z : ComplexModel n) : (a + b).coeff e z = a.coeff e z + b.coeff e z := rfl

@[simp] theorem coeff_smul (c : ℝ) (a : SmoothRealForm n M k) (e : ComplexChart n M)
    (z : ComplexModel n) : (c • a).coeff e z = c • a.coeff e z := rfl

@[simp] theorem coeff_neg (a : SmoothRealForm n M k) (e : ComplexChart n M)
    (z : ComplexModel n) : (-a).coeff e z = -a.coeff e z := rfl

@[simp] theorem coeff_sub (a b : SmoothRealForm n M k) (e : ComplexChart n M)
    (z : ComplexModel n) : (a - b).coeff e z = a.coeff e z - b.coeff e z := rfl

theorem coeff_injective :
    Function.Injective (fun a : SmoothRealForm n M k => a.coeff) := fun _ _ h =>
  smoothRealForm_ext fun e z => congrFun (congrFun h e) z

instance instAddCommGroup : AddCommGroup (SmoothRealForm n M k) :=
  Function.Injective.addCommGroup (fun a : SmoothRealForm n M k => a.coeff) coeff_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun a m => by funext e z; exact Nat.cast_smul_eq_nsmul ℝ m (a.coeff e z))
    (fun a m => by funext e z; exact Int.cast_smul_eq_zsmul ℝ m (a.coeff e z))

/-- The coefficient family, as an additive homomorphism. -/
def coeffAddHom : SmoothRealForm n M k →+ (ComplexChart n M → ComplexModel n → RealForm n k) where
  toFun a := a.coeff
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule : Module ℝ (SmoothRealForm n M k) :=
  Function.Injective.module ℝ coeffAddHom coeff_injective (fun _ _ => rfl)

end Algebra

/-! ### The constant one, function multiples and the wedge with a two-form -/

section Operations

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {k : ℕ}

/-- The constant function `1`, as a smooth `0`-form. -/
def unitForm : SmoothRealForm n M 0 where
  coeff := fun _ _ => coordinateWedgeUnit
  smooth := fun _ => contDiffOn_const
  compatible := fun _ _ _ _ _ => rfl

@[simp] theorem unitForm_coeff (e : ComplexChart n M) (z : ComplexModel n) :
    (unitForm : SmoothRealForm n M 0).coeff e z = coordinateWedgeUnit := rfl

/-- Multiplication by a chart-smooth function. -/
def smulFun (h : M → ℝ) (hh : ChartSmooth (n := n) h) (a : SmoothRealForm n M k) :
    SmoothRealForm n M k where
  coeff := fun e z => h (e.val.symm z) • a.coeff e z
  smooth := fun e => (hh e).smul (a.smooth e)
  compatible := fun e f z hz v => by
    have hsymm : f.val.symm (chartTransition e f z) = e.val.symm z := by
      change f.val.symm (f.val (e.val.symm z)) = e.val.symm z
      exact f.val.left_inv hz.2
    simp only [ContinuousAlternatingMap.smul_apply, a.compatible e f z hz v, hsymm]

@[simp] theorem smulFun_coeff (h : M → ℝ) (hh : ChartSmooth (n := n) h)
    (a : SmoothRealForm n M k) (e : ComplexChart n M) (z : ComplexModel n) :
    (smulFun h hh a).coeff e z = h (e.val.symm z) • a.coeff e z := rfl

/-- The exterior product with a two-form, chart by chart. -/
def wedgeTwo (P : SmoothRealForm n M k) (β : SmoothRealForm n M 2) :
    SmoothRealForm n M (k + 2) where
  coeff := fun e z => coordinateWedge (P.coeff e z) (β.coeff e z)
  smooth := fun e => contDiffOn_coordinateWedge (P.smooth e) (β.smooth e)
  compatible := fun e f z hz v => by
    have hP : P.coeff e z = (P.coeff f (chartTransition e f z)).compContinuousLinearMap
        (chartTransitionDerivative e f z) := by
      ext w
      exact P.compatible e f z hz w
    have hβ : β.coeff e z = (β.coeff f (chartTransition e f z)).compContinuousLinearMap
        (chartTransitionDerivative e f z) := by
      ext w
      exact β.compatible e f z hz w
    rw [hP, hβ, ← coordinateWedge_compContinuousLinearMap]
    rfl

@[simp] theorem wedgeTwo_coeff (P : SmoothRealForm n M k) (β : SmoothRealForm n M 2)
    (e : ComplexChart n M) (z : ComplexModel n) :
    (wedgeTwo P β).coeff e z = coordinateWedge (P.coeff e z) (β.coeff e z) := rfl

theorem wedgeTwo_add_left (P P' : SmoothRealForm n M k) (β : SmoothRealForm n M 2) :
    wedgeTwo (P + P') β = wedgeTwo P β + wedgeTwo P' β :=
  smoothRealForm_ext fun _ _ => coordinateWedge_add_left _ _ _

theorem wedgeTwo_smul_left (c : ℝ) (P : SmoothRealForm n M k) (β : SmoothRealForm n M 2) :
    wedgeTwo (c • P) β = c • wedgeTwo P β :=
  smoothRealForm_ext fun _ _ => coordinateWedge_smul_left _ _ _

theorem wedgeTwo_add_right (P : SmoothRealForm n M k) (β β' : SmoothRealForm n M 2) :
    wedgeTwo P (β + β') = wedgeTwo P β + wedgeTwo P β' :=
  smoothRealForm_ext fun _ _ => coordinateWedge_add_right _ _ _

theorem wedgeTwo_smul_right (c : ℝ) (P : SmoothRealForm n M k) (β : SmoothRealForm n M 2) :
    wedgeTwo P (c • β) = c • wedgeTwo P β :=
  smoothRealForm_ext fun _ _ => coordinateWedge_smul_right _ _ _

/-- The wedge with a fixed two-form, as a linear map. -/
def wedgeTwoLM (β : SmoothRealForm n M 2) : SmoothRealForm n M k →ₗ[ℝ] SmoothRealForm n M (k + 2)
    where
  toFun P := wedgeTwo P β
  map_add' P P' := wedgeTwo_add_left P P' β
  map_smul' c P := wedgeTwo_smul_left c P β

/-- The powers `w^q` of a two-form. -/
def formPow (w : SmoothRealForm n M 2) : (q : ℕ) → SmoothRealForm n M (2 * q)
  | 0 => unitForm
  | q + 1 => wedgeTwo (formPow w q) w

theorem formPow_coeff (w : SmoothRealForm n M 2) (e : ComplexChart n M) (z : ComplexModel n) :
    ∀ q, (formPow w q).coeff e z = formPower (w.coeff e z) q
  | 0 => rfl
  | q + 1 => by
    change coordinateWedge ((formPow w q).coeff e z) (w.coeff e z) = _
    rw [formPow_coeff w e z q]
    rfl

end Operations

/-! ### The test space and its positive cone -/

section TestSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

variable (n M) in
/-- The real span of the forms `h · β₁ ∧ ⋯ ∧ β_q`, `h` chart-smooth and `β_j` smooth real
`(1,1)`-forms. -/
def testSpace : (q : ℕ) → Submodule ℝ (SmoothRealForm n M (2 * q))
  | 0 => Submodule.span ℝ
      {a | ∃ (h : M → ℝ) (hh : ChartSmooth (n := n) h), a = smulFun h hh unitForm}
  | q + 1 => Submodule.span ℝ
      {a | ∃ P ∈ testSpace q, ∃ β : SmoothRealForm n M 2, β.IsTypeOneOne ∧ a = wedgeTwo P β}

theorem smulFun_unitForm_mem_testSpace (h : M → ℝ) (hh : ChartSmooth (n := n) h) :
    smulFun h hh unitForm ∈ testSpace n M 0 :=
  Submodule.subset_span ⟨h, hh, rfl⟩

theorem wedgeTwo_mem_testSpace {q : ℕ} {P : SmoothRealForm n M (2 * q)}
    (hP : P ∈ testSpace n M q) {β : SmoothRealForm n M 2} (hβ : β.IsTypeOneOne) :
    wedgeTwo P β ∈ testSpace n M (q + 1) :=
  Submodule.subset_span ⟨P, hP, β, hβ, rfl⟩

omit [IsComplexManifold n M] in
theorem chartSmooth_const (c : ℝ) : ChartSmooth (n := n) (fun _ : M => c) :=
  fun _ => contDiffOn_const

theorem unitForm_mem_testSpace : (unitForm : SmoothRealForm n M 0) ∈ testSpace n M 0 := by
  have h : smulFun (fun _ : M => (1 : ℝ)) (chartSmooth_const 1) unitForm =
      (unitForm : SmoothRealForm n M 0) :=
    smoothRealForm_ext fun e z => one_smul ℝ _
  rw [← h]
  exact smulFun_unitForm_mem_testSpace _ _

theorem formPow_mem_testSpace {w : SmoothRealForm n M 2} (hw : w.IsTypeOneOne) :
    ∀ q, formPow w q ∈ testSpace n M q
  | 0 => unitForm_mem_testSpace
  | q + 1 => wedgeTwo_mem_testSpace (formPow_mem_testSpace hw q) hw

variable (n M) in
/-- The test forms that are strongly positive at every point of every chart. -/
def positiveCone (q : ℕ) : Set (testSpace n M q) :=
  {φ | ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    (φ : SmoothRealForm n M (2 * q)).coeff e z ∈ spCone q}

/-- A Kähler form is a semipositive `(1,1)`-form at every point of every chart. -/
theorem isSemipositiveOneOne_of_isHermitian {w : SmoothRealForm n M 2} (hw : w.IsHermitian)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    IsSemipositiveOneOne (w.coeff e z) :=
  ⟨(hw e z hz).1, fun v => KahlerDomination.lineValue_nonneg_of_isHermitian hw e hz v⟩

theorem formPow_mem_positiveCone {w : SmoothRealForm n M 2} (hw : w.IsHermitian) (q : ℕ) :
    (⟨formPow w q, formPow_mem_testSpace (fun e z hz => (hw e z hz).1) q⟩ : testSpace n M q) ∈
      positiveCone n M q := by
  intro e z hz
  change (formPow w q).coeff e z ∈ spCone q
  rw [formPow_coeff]
  exact formPower_mem_spCone (isSemipositiveOneOne_of_isHermitian hw e hz) q

end TestSpace

/-! ### The order unit on a compact manifold -/

section OrderUnit

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- A chart-smooth function is continuous. -/
theorem ChartSmooth.continuous {h : M → ℝ} (hh : ChartSmooth (n := n) h) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro x
  set e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have h1 : ContinuousAt (fun z => h (e.val.symm z)) (e.val x) :=
    ((hh e).continuousOn).continuousAt (e.val.open_target.mem_nhds (e.val.map_source hx))
  have h2 := h1.comp (e.val.continuousAt hx)
  refine h2.congr ?_
  filter_upwards [e.val.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply, e.val.left_inv hy]

/-- The pointwise form of the order-unit bound, at every point of every chart. -/
def PointwiseOrderBound (w : SmoothRealForm n M 2) {q : ℕ} (φ : SmoothRealForm n M (2 * q))
    (c : ℝ) : Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    c • formPower (w.coeff e z) q - φ.coeff e z ∈ spCone q ∧
      c • formPower (w.coeff e z) q + φ.coeff e z ∈ spCone q

theorem PointwiseOrderBound.add {w : SmoothRealForm n M 2} {q : ℕ}
    {φ ψ : SmoothRealForm n M (2 * q)} {c d : ℝ} (hφ : PointwiseOrderBound w φ c)
    (hψ : PointwiseOrderBound w ψ d) : PointwiseOrderBound w (φ + ψ) (c + d) := by
  intro e z hz
  obtain ⟨h₁, h₂⟩ := hφ e z hz
  obtain ⟨h₃, h₄⟩ := hψ e z hz
  constructor
  · have := (spCone q).add_mem h₁ h₃
    convert this using 1
    simp only [coeff_add, add_smul]
    abel
  · have := (spCone q).add_mem h₂ h₄
    convert this using 1
    simp only [coeff_add, add_smul]
    abel

theorem PointwiseOrderBound.smul {w : SmoothRealForm n M 2} {q : ℕ}
    {φ : SmoothRealForm n M (2 * q)} {c : ℝ} (hφ : PointwiseOrderBound w φ c) (a : ℝ) :
    PointwiseOrderBound w (a • φ) (|a| * c) := by
  intro e z hz
  obtain ⟨h₁, h₂⟩ := hφ e z hz
  set W := formPower (w.coeff e z) q
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha]
    have e₁ : (a * c) • W - (a • φ).coeff e z = a • (c • W - φ.coeff e z) := by
      simp only [coeff_smul]; module
    have e₂ : (a * c) • W + (a • φ).coeff e z = a • (c • W + φ.coeff e z) := by
      simp only [coeff_smul]; module
    rw [e₁, e₂]
    exact ⟨smul_mem_spCone h₁ ha, smul_mem_spCone h₂ ha⟩
  · rw [abs_of_neg ha]
    have e₁ : (-a * c) • W - (a • φ).coeff e z = (-a) • (c • W + φ.coeff e z) := by
      simp only [coeff_smul]; module
    have e₂ : (-a * c) • W + (a • φ).coeff e z = (-a) • (c • W - φ.coeff e z) := by
      simp only [coeff_smul]; module
    rw [e₁, e₂]
    exact ⟨smul_mem_spCone h₂ (neg_nonneg.mpr ha.le), smul_mem_spCone h₁ (neg_nonneg.mpr ha.le)⟩

theorem PointwiseOrderBound.zero (w : SmoothRealForm n M 2) (q : ℕ) :
    PointwiseOrderBound w (0 : SmoothRealForm n M (2 * q)) 0 := by
  intro e z hz
  simp only [zero_smul, coeff_zero, sub_zero, add_zero]
  exact ⟨(spCone q).zero_mem, (spCone q).zero_mem⟩

variable [CompactSpace M]

/-- **`w^q` dominates every test form** (pointwise form): on a compact manifold with a
Hermitian form `w`, every `φ ∈ testSpace q` satisfies `c w^q ± φ` strongly positive at
every point, for one constant `c ≥ 0`. -/
theorem exists_pointwiseOrderBound {w : SmoothRealForm n M 2} (hw : w.IsHermitian) :
    ∀ (q : ℕ) {φ : SmoothRealForm n M (2 * q)}, φ ∈ testSpace n M q →
      ∃ c : ℝ, 0 ≤ c ∧ PointwiseOrderBound w φ c
  | 0, φ, hφ => by
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      obtain ⟨c, hc⟩ := isCompact_univ.exists_bound_of_continuousOn
        (ChartSmooth.continuous hh).continuousOn
      refine ⟨max c 0, le_max_right _ _, fun e z hz => ?_⟩
      have hb0 : |h (e.val.symm z)| ≤ c := by
        simpa [Real.norm_eq_abs] using hc (e.val.symm z) (mem_univ _)
      have hb : |h (e.val.symm z)| ≤ max c 0 := hb0.trans (le_max_left _ _)
      have hu := unit_mem_spCone (n := n)
      simp only [smulFun_coeff, unitForm_coeff, formPower_zero]
      refine ⟨?_, ?_⟩
      · convert smul_mem_spCone hu
          (show 0 ≤ max c 0 - h (e.val.symm z) by linarith [le_abs_self (h (e.val.symm z))])
          using 1
        exact (sub_smul _ _ _).symm
      · convert smul_mem_spCone hu
          (show 0 ≤ max c 0 + h (e.val.symm z) by linarith [neg_abs_le (h (e.val.symm z))])
          using 1
        exact (add_smul _ _ _).symm
    | zero => exact ⟨0, le_rfl, PointwiseOrderBound.zero w 0⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hxc⟩ := hx
      obtain ⟨d, hd, hyd⟩ := hy
      exact ⟨c + d, add_nonneg hc hd, hxc.add hyd⟩
    | smul a x _ hx =>
      obtain ⟨c, hc, hxc⟩ := hx
      exact ⟨|a| * c, mul_nonneg (abs_nonneg a) hc, hxc.smul a⟩
  | q + 1, φ, hφ => by
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨P, hP, β, hβ, rfl⟩ := hx
      obtain ⟨c, hc, hPc⟩ := exists_pointwiseOrderBound hw q hP
      obtain ⟨A₁, hA₁, h₁⟩ := KahlerDomination.exists_isSemipositive_add_smul β w hw
      obtain ⟨A₂, hA₂, h₂⟩ := KahlerDomination.exists_isSemipositive_add_smul (-β) w hw
      refine ⟨c * (A₁ + A₂), mul_nonneg hc (by positivity), fun e z hz => ?_⟩
      have hwz := isSemipositiveOneOne_of_isHermitian hw e hz
      have hβz : IsOneOne (β.coeff e z) := hβ e z hz
      have hK₁ : IsSemipositiveOneOne ((A₁ + A₂) • w.coeff e z - β.coeff e z) := by
        refine ⟨fun u v => ?_, fun v => ?_⟩
        · simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
            hwz.1 u v, hβz u v]
        · have h₂v := h₂ e z hz v
          have hw0 := hwz.2 v
          simp only [coeff_neg, ContinuousAlternatingMap.neg_apply] at h₂v
          simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
            smul_eq_mul]
          nlinarith
      have hK₂ : IsSemipositiveOneOne ((A₁ + A₂) • w.coeff e z + β.coeff e z) := by
        refine ⟨fun u v => ?_, fun v => ?_⟩
        · simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
            hwz.1 u v, hβz u v]
        · have h₁v := h₁ e z hz v
          have hw0 := hwz.2 v
          simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
            smul_eq_mul]
          nlinarith
      obtain ⟨hPc₁, hPc₂⟩ := hPc e z hz
      exact orderUnit_step hPc₁ hPc₂ hK₁ hK₂
    | zero => exact ⟨0, le_rfl, PointwiseOrderBound.zero w (q + 1)⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hxc⟩ := hx
      obtain ⟨d, hd, hyd⟩ := hy
      exact ⟨c + d, add_nonneg hc hd, hxc.add hyd⟩
    | smul a x _ hx =>
      obtain ⟨c, hc, hxc⟩ := hx
      exact ⟨|a| * c, mul_nonneg (abs_nonneg a) hc, hxc.smul a⟩

/-- **`w^q` is an order unit for the positive test forms** on a compact manifold with a
Hermitian (e.g. Kähler) form `w`. -/
theorem exists_orderUnit_bound {w : SmoothRealForm n M 2} (hw : w.IsHermitian) (q : ℕ)
    (φ : testSpace n M q) :
    ∃ c : ℝ, 0 ≤ c ∧
      c • (⟨formPow w q, formPow_mem_testSpace (fun e z hz => (hw e z hz).1) q⟩ :
        testSpace n M q) - φ ∈ positiveCone n M q ∧
      c • (⟨formPow w q, formPow_mem_testSpace (fun e z hz => (hw e z hz).1) q⟩ :
        testSpace n M q) + φ ∈ positiveCone n M q := by
  obtain ⟨c, hc, hb⟩ := exists_pointwiseOrderBound hw q φ.2
  refine ⟨c, hc, fun e z hz => ?_, fun e z hz => ?_⟩
  · change (c • formPow w q - (φ : SmoothRealForm n M (2 * q))).coeff e z ∈ spCone q
    simpa only [coeff_sub, coeff_smul, formPow_coeff] using (hb e z hz).1
  · change (c • formPow w q + (φ : SmoothRealForm n M (2 * q))).coeff e z ∈ spCone q
    simpa only [coeff_add, coeff_smul, formPow_coeff] using (hb e z hz).2

end OrderUnit

/-! ### Pullback along holomorphic maps -/

section Pullback

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {f : V → M}

/-- Type `(1,1)` is preserved by pullback along a map commuting with `i`. -/
theorem isOneOne_compContinuousLinearMap {A : RealForm n 2} (hA : IsOneOne A)
    (L : ComplexModel k →L[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    IsOneOne (A.compContinuousLinearMap L) := by
  have hcomp : ∀ u v : ComplexModel k, (⇑L ∘ ![u, v]) = ![L u, L v] := by
    intro u v
    funext i
    fin_cases i <;> rfl
  intro u v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, hcomp, hL]
  exact hA (L u) (L v)

/-- Chart-smooth functions pull back to chart-smooth functions along holomorphic maps. -/
theorem chartSmooth_comp (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {h : M → ℝ} (hh : ChartSmooth (n := n) h) : ChartSmooth (n := k) (fun x => h (f x)) := by
  intro e u hu
  set d := complexChartAt (n := n) (f (e.val.symm u))
  have hud : u ∈ HolomorphicMaps.coordinateDomain f e d := ⟨hu, mem_complexChartAt_source _⟩
  have h1 := HolomorphicMaps.coordinateMap_contDiffAt_real hf e d hud
  have h2 := (hh d).contDiffAt
    (d.val.open_target.mem_nhds (HolomorphicMaps.coordinateMap_mem_target hud))
  have h3 := ContDiffAt.comp (g := fun z => h (d.val.symm z)) u h2 h1
  refine (h3.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(HolomorphicMaps.coordinateDomain_isOpen hf e d).mem_nhds hud] with u' hu'
  change h (f (e.val.symm u')) = h (d.val.symm (d.val (f (e.val.symm u'))))
  rw [d.val.left_inv hu'.2]

variable (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
include hf

theorem pullback_zero {p : ℕ} : SmoothRealForm.pullback hf (0 : SmoothRealForm n M p) = 0 :=
  smoothRealForm_ext fun _ _ => by ext v; rfl

theorem pullback_add {p : ℕ} (a b : SmoothRealForm n M p) :
    SmoothRealForm.pullback hf (a + b) =
      SmoothRealForm.pullback hf a + SmoothRealForm.pullback hf b :=
  smoothRealForm_ext fun _ _ => by ext v; rfl

theorem pullback_smul {p : ℕ} (c : ℝ) (a : SmoothRealForm n M p) :
    SmoothRealForm.pullback hf (c • a) = c • SmoothRealForm.pullback hf a :=
  smoothRealForm_ext fun _ _ => by ext v; rfl

theorem pullback_unitForm :
    SmoothRealForm.pullback hf (unitForm : SmoothRealForm n M 0) = unitForm :=
  smoothRealForm_ext fun _ _ => by ext v; rfl

theorem pullback_smulFun {p : ℕ} (h : M → ℝ) (hh : ChartSmooth (n := n) h)
    (a : SmoothRealForm n M p) :
    SmoothRealForm.pullback hf (smulFun h hh a) =
      smulFun (fun x => h (f x)) (chartSmooth_comp hf hh) (SmoothRealForm.pullback hf a) := by
  refine smoothRealForm_ext fun e z => ?_
  set d := complexChartAt (n := n) (f (e.val.symm z))
  have hd : d.val.symm (HolomorphicMaps.coordinateMap f e d z) = f (e.val.symm z) :=
    d.val.left_inv (mem_complexChartAt_source _)
  ext v
  change (h (d.val.symm (HolomorphicMaps.coordinateMap f e d z)) •
      a.coeff d (HolomorphicMaps.coordinateMap f e d z))
        (fun i => fderiv ℝ (HolomorphicMaps.coordinateMap f e d) z (v i)) =
    h (f (e.val.symm z)) • (a.coeff d (HolomorphicMaps.coordinateMap f e d z))
        (fun i => fderiv ℝ (HolomorphicMaps.coordinateMap f e d) z (v i))
  rw [hd]
  rfl

theorem pullback_wedgeTwo {p : ℕ} (P : SmoothRealForm n M p) (β : SmoothRealForm n M 2) :
    SmoothRealForm.pullback hf (wedgeTwo P β) =
      wedgeTwo (SmoothRealForm.pullback hf P) (SmoothRealForm.pullback hf β) :=
  smoothRealForm_ext fun _ _ => coordinateWedge_compContinuousLinearMap _ _ _

theorem isTypeOneOne_pullback {β : SmoothRealForm n M 2} (hβ : β.IsTypeOneOne) :
    (SmoothRealForm.pullback hf β).IsTypeOneOne := by
  intro e z hz
  set d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ HolomorphicMaps.coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [SmoothRealForm.pullback_coeff hf β e d hzd]
  exact isOneOne_compContinuousLinearMap
    (hβ d _ (HolomorphicMaps.coordinateMap_mem_target hzd)) _
    (fun v => HolomorphicMaps.coordinateMap_fderiv_map_smul_complex hf e d hzd Complex.I v)

/-- **Pullback preserves test forms.** -/
theorem pullback_mem_testSpace :
    ∀ (q : ℕ) {φ : SmoothRealForm n M (2 * q)}, φ ∈ testSpace n M q →
      SmoothRealForm.pullback hf φ ∈ testSpace k V q
  | 0, φ, hφ => by
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      rw [pullback_smulFun hf, pullback_unitForm hf]
      exact smulFun_unitForm_mem_testSpace _ _
    | zero => rw [pullback_zero hf]; exact (testSpace k V 0).zero_mem
    | add x y _ _ hx hy => rw [pullback_add hf]; exact (testSpace k V 0).add_mem hx hy
    | smul a x _ hx => rw [pullback_smul hf]; exact (testSpace k V 0).smul_mem a hx
  | q + 1, φ, hφ => by
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨P, hP, β, hβ, rfl⟩ := hx
      rw [pullback_wedgeTwo hf]
      exact wedgeTwo_mem_testSpace (pullback_mem_testSpace q hP) (isTypeOneOne_pullback hf hβ)
    | zero => rw [pullback_zero hf]; exact (testSpace k V (q + 1)).zero_mem
    | add x y _ _ hx hy =>
      rw [pullback_add hf]; exact (testSpace k V (q + 1)).add_mem hx hy
    | smul a x _ hx => rw [pullback_smul hf]; exact (testSpace k V (q + 1)).smul_mem a hx

omit hf in
/-- Pullback of test forms along a holomorphic map, as a linear map. -/
def pullbackTestLM (hf' : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) (q : ℕ) :
    testSpace n M q →ₗ[ℝ] testSpace k V q where
  toFun φ := ⟨SmoothRealForm.pullback hf' φ, pullback_mem_testSpace hf' q φ.2⟩
  map_add' φ ψ := Subtype.ext (pullback_add hf' (φ : SmoothRealForm n M (2 * q)) ψ)
  map_smul' c φ := by
    ext1
    exact pullback_smul hf' c (φ : SmoothRealForm n M (2 * q))

@[simp] theorem coe_pullbackTestLM (q : ℕ) (φ : testSpace n M q) :
    ((pullbackTestLM hf q φ : testSpace k V q) : SmoothRealForm k V (2 * q)) =
      SmoothRealForm.pullback hf (φ : SmoothRealForm n M (2 * q)) := rfl

/-- **Pullback preserves positive test forms.** -/
theorem pullbackTestLM_mem_positiveCone {q : ℕ} {φ : testSpace n M q}
    (hφ : φ ∈ positiveCone n M q) : pullbackTestLM hf q φ ∈ positiveCone k V q := by
  intro e z hz
  set d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ HolomorphicMaps.coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [coe_pullbackTestLM, SmoothRealForm.pullback_coeff hf _ e d hzd]
  exact compContinuousLinearMap_mem_spCone _
    (fun v => HolomorphicMaps.coordinateMap_fderiv_map_smul_complex hf e d hzd Complex.I v) q
    (hφ d _ (HolomorphicMaps.coordinateMap_mem_target hzd))

end Pullback

end

end SGPT.Foundations.Analysis.Pending.ProductTestForms
