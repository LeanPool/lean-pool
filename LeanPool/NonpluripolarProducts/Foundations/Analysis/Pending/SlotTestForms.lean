/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ClosedCurrentLocalTests
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothDDCForm
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ChartPartition

/-!
# Test forms with a free first slot; the Leibniz rule and integration by parts for closed currents

For a smooth real two-form `γ` and closed real `(1,1)`-forms `β₀, …, β_{k-1}`,
`slotForm γ k β = Π₁₁ γ ∧ β₀ ∧ ⋯ ∧ β_{k-1}` is a test form of bidimension `(k+1, k+1)`; it is
linear in `γ`, commutes with multiplication by chart-smooth functions, and the closed test
forms of `ClosedProductCurrents` are `slotForm (d(f dg))` (`closedTestForm_eq_slotForm`).
For a positive current `T` of bidimension `(k+1, k+1)` the functional `γ ↦ T (slotForm γ k β)`
is the positive `(1,1)`-bidimension current `T ∧ β₀ ∧ ⋯ ∧ β_{k-1}` evaluated on `Π₁₁ γ`: it is
nonnegative on two-forms that are nonnegative on complex lines (`slotForm_mem_positiveCone`;
`Π₁₁ γ (v, iv) = γ (v, iv)`), and only the values of `γ` at chart points matter.

* **Leibniz** (`apply_smulTest_closedTestForm`): for a closed positive `T`,
  `T (U Π₁₁ d(f dg) ∧ β) = - T (f Π₁₁ (dU ∧ dg) ∧ β)` (since `d(Uf) = U df + f dU`).
* **Chain rule** (`exactPair_coeff_eq_deriv_smul`): `d(θ(v) dg) = θ'(v) d(v dg)`.
* **Integration by parts** (`slotForm_ibp`): for a closed positive `T`, a chart-smooth `u` and
  `h` smooth with compact support in one chart,
  `T (h ddᶜu ∧ β) = T (u ddᶜh ∧ β)`.  In the chart, `h dᶜu - u dᶜh = ∑ⱼ cⱼ d(χ ℓⱼ)` (real
  coordinates `ℓⱼ`, cut-off `χ = 1` near the support), each `T (Π₁₁ d(cⱼ d(χℓⱼ)) ∧ β)` vanishes
  by closedness, and `Π₁₁ (dh ∧ dᶜu - du ∧ dᶜh) = 0`.

These are steps (E3) and (IBP) of the Skoda--El Mir argument for the diagonal
(`demailly-cadg:III.2.3`, TN.4 step B4.3).
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.SlotTestForms

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents TopDegreeDensity ClosedProductCurrents
  SmoothCurrentClosedness ClosedCurrentLocalTests CurrentTraceMeasure SmoothDDCForm ChartPartition

/-! ### The `(1,1)`-part on complex lines -/

section Pointwise

variable {n : ℕ}

theorem I_smul_I_smul (v : ComplexModel n) : Complex.I • Complex.I • v = -v := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

/-- `Π₁₁ A (v, iv) = A (v, iv)` for every real two-form `A`. -/
theorem pi11_apply_line (A : RealForm n 2) (v : ComplexModel n) :
    pi11 A ![v, Complex.I • v] = A ![v, Complex.I • v] := by
  rw [pi11_apply, I_smul_I_smul, coordinateFrame_twoForm_neg_right,
    coordinateFrame_twoForm_swap A v (Complex.I • v)]
  ring

theorem isSemipositiveOneOne_pi11 {A : RealForm n 2} (hA : CoefficientSemipositive A) :
    IsSemipositiveOneOne (pi11 A) :=
  ⟨isOneOne_pi11 A, fun v => by rw [pi11_apply_line]; exact hA v⟩

theorem pi11_add (A B : RealForm n 2) : pi11 (A + B) = pi11 A + pi11 B :=
  map_add (pi11CLM n) A B

theorem pi11_smul (c : ℝ) (A : RealForm n 2) : pi11 (c • A) = c • pi11 A :=
  map_smul (pi11CLM n) c A

theorem pi11_sub (A B : RealForm n 2) : pi11 (A - B) = pi11 A - pi11 B :=
  map_sub (pi11CLM n) A B

theorem pi11_sum {ι : Type*} (s : Finset ι) (A : ι → RealForm n 2) :
    pi11 (∑ i ∈ s, A i) = ∑ i ∈ s, pi11 (A i) :=
  map_sum (pi11CLM n) A s

theorem pi11_zero : pi11 (0 : RealForm n 2) = 0 := map_zero (pi11CLM n)

/-- A product of two-forms with a zero factor vanishes. -/
theorem wedgeProd_cons_zero (k : ℕ) (β : Fin k → RealForm n 2) :
    wedgeProd (k + 1) (Fin.cons 0 β) = 0 := by
  have h := wedgeProd_update_zero (k + 1) (Fin.cons 0 β) 0
  rwa [Fin.update_cons_zero] at h

end Pointwise

/-! ### The slot test forms -/

section Slot

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem pi11Form_add (a b : SmoothRealForm n M 2) : pi11Form (a + b) = pi11Form a + pi11Form b :=
  smoothRealForm_ext fun _ _ => pi11_add _ _

theorem pi11Form_smul (c : ℝ) (a : SmoothRealForm n M 2) : pi11Form (c • a) = c • pi11Form a :=
  smoothRealForm_ext fun _ _ => pi11_smul _ _

theorem pi11Form_smulFun (h : M → ℝ) (hh : ChartSmooth (n := n) h) (a : SmoothRealForm n M 2) :
    pi11Form (smulFun h hh a) = smulFun h hh (pi11Form a) :=
  smoothRealForm_ext fun _ _ => pi11_smul _ _

/-- The test form `Π₁₁ γ ∧ β₀ ∧ ⋯ ∧ β_{k-1}` of degree `2(k+1)`, for any smooth two-form `γ`. -/
def slotForm (γ : SmoothRealForm n M 2) :
    (k : ℕ) → (Fin k → ClosedRealOneOneForm n M) → testSpace n M (k + 1)
  | 0, _ => ⟨wedgeTwo unitForm (pi11Form γ),
      wedgeTwo_mem_testSpace unitForm_mem_testSpace (isTypeOneOne_pi11Form _)⟩
  | k + 1, β => wedgeTestLM (β (Fin.last k)).2.2 (k + 1) (slotForm γ k fun j => β j.castSucc)

/-- The closed test forms are the slot forms of `d(f dg)`. -/
theorem closedTestForm_eq_slotForm {f g : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hg : ChartSmooth (n := n) g) :
    ∀ (k : ℕ) (β : Fin k → ClosedRealOneOneForm n M),
      closedTestForm f g hf hg k β = slotForm (exactPair f g hf hg) k β
  | 0, _ => rfl
  | k + 1, β => by
    change wedgeTestLM _ (k + 1) (closedTestForm f g hf hg k fun j => β j.castSucc) =
      wedgeTestLM _ (k + 1) (slotForm (exactPair f g hf hg) k fun j => β j.castSucc)
    rw [closedTestForm_eq_slotForm hf hg k]

theorem slotForm_add (γ γ' : SmoothRealForm n M 2) :
    ∀ (k : ℕ) (β : Fin k → ClosedRealOneOneForm n M),
      slotForm (γ + γ') k β = slotForm γ k β + slotForm γ' k β
  | 0, _ => Subtype.ext (by
      change wedgeTwo unitForm (pi11Form (γ + γ')) =
        wedgeTwo unitForm (pi11Form γ) + wedgeTwo unitForm (pi11Form γ')
      rw [pi11Form_add, wedgeTwo_add_right])
  | k + 1, β => by
    change wedgeTestLM _ (k + 1) (slotForm (γ + γ') k fun j => β j.castSucc) =
      wedgeTestLM _ (k + 1) (slotForm γ k fun j => β j.castSucc) +
        wedgeTestLM _ (k + 1) (slotForm γ' k fun j => β j.castSucc)
    rw [slotForm_add γ γ' k, map_add]

theorem slotForm_smul (c : ℝ) (γ : SmoothRealForm n M 2) :
    ∀ (k : ℕ) (β : Fin k → ClosedRealOneOneForm n M), slotForm (c • γ) k β = c • slotForm γ k β
  | 0, _ => Subtype.ext (by
      change wedgeTwo unitForm (pi11Form (c • γ)) = c • wedgeTwo unitForm (pi11Form γ)
      rw [pi11Form_smul, wedgeTwo_smul_right])
  | k + 1, β => by
    change wedgeTestLM _ (k + 1) (slotForm (c • γ) k fun j => β j.castSucc) =
      c • wedgeTestLM _ (k + 1) (slotForm γ k fun j => β j.castSucc)
    rw [slotForm_smul c γ k, map_smul]

/-- `slotForm` as a linear map. -/
def slotLM (k : ℕ) (β : Fin k → ClosedRealOneOneForm n M) :
    SmoothRealForm n M 2 →ₗ[ℝ] testSpace n M (k + 1) where
  toFun γ := slotForm γ k β
  map_add' γ γ' := slotForm_add γ γ' k β
  map_smul' c γ := slotForm_smul c γ k β

@[simp] theorem slotLM_apply (k : ℕ) (β : Fin k → ClosedRealOneOneForm n M)
    (γ : SmoothRealForm n M 2) : slotLM k β γ = slotForm γ k β := rfl

theorem slotForm_sub (γ γ' : SmoothRealForm n M 2) (k : ℕ)
    (β : Fin k → ClosedRealOneOneForm n M) :
    slotForm (γ - γ') k β = slotForm γ k β - slotForm γ' k β :=
  map_sub (slotLM k β) γ γ'

theorem slotForm_sum {ι : Type*} (s : Finset ι) (γ : ι → SmoothRealForm n M 2) (k : ℕ)
    (β : Fin k → ClosedRealOneOneForm n M) :
    slotForm (∑ i ∈ s, γ i) k β = ∑ i ∈ s, slotForm (γ i) k β :=
  map_sum (slotLM k β) γ s

/-- Multiplication by a chart-smooth function passes through the slot. -/
theorem slotForm_smulFun (h : M → ℝ) (hh : ChartSmooth (n := n) h) (γ : SmoothRealForm n M 2) :
    ∀ (k : ℕ) (β : Fin k → ClosedRealOneOneForm n M),
      slotForm (smulFun h hh γ) k β = smulTest h hh (slotForm γ k β)
  | 0, _ => Subtype.ext (by
      change wedgeTwo unitForm (pi11Form (smulFun h hh γ)) =
        smulFun h hh (wedgeTwo unitForm (pi11Form γ))
      rw [pi11Form_smulFun]
      exact smoothRealForm_ext fun _ _ => coordinateWedge_smul_right _ _ _)
  | k + 1, β => by
    change wedgeTestLM _ (k + 1) (slotForm (smulFun h hh γ) k fun j => β j.castSucc) =
      smulTest h hh (wedgeTestLM _ (k + 1) (slotForm γ k fun j => β j.castSucc))
    rw [slotForm_smulFun h hh γ k]
    exact Subtype.ext (smulFun_wedgeTwo h hh _ _).symm

/-- **The coefficients of the slot form**. -/
theorem slotForm_coeff (γ : SmoothRealForm n M 2) :
    ∀ (k : ℕ) (β : Fin k → ClosedRealOneOneForm n M) (e : ComplexChart n M) (z : ComplexModel n),
      ((slotForm γ k β : testSpace n M (k + 1)) : SmoothRealForm n M (2 * (k + 1))).coeff e z =
        wedgeProd (k + 1) (Fin.cons (pi11 (γ.coeff e z)) fun j => (β j).val.coeff e z)
  | 0, _, _, _ => rfl
  | k + 1, β, e, z => by
    change coordinateWedge (((slotForm γ k fun j => β j.castSucc :
        testSpace n M (k + 1)) : SmoothRealForm n M (2 * (k + 1))).coeff e z)
      ((β (Fin.last k)).val.coeff e z) = _
    rw [slotForm_coeff γ k, ← wedgeProd_snoc, ← Fin.cons_snoc_eq_snoc_cons]
    congr 2
    exact Fin.snoc_init_self (fun j => (β j).val.coeff e z)

/-- **Slot forms of forms nonnegative on complex lines are positive** (with semipositive closed
slots). -/
theorem slotForm_mem_positiveCone {γ : SmoothRealForm n M 2}
    (hγ : ∀ (e : ComplexChart n M) z, z ∈ e.val.target → CoefficientSemipositive (γ.coeff e z)) :
    ∀ (k : ℕ) (β : Fin k → ClosedRealOneOneForm n M), (∀ j, (β j).val.IsSemipositive) →
      slotForm γ k β ∈ positiveCone n M (k + 1)
  | 0, _, _ => fun e z hz =>
      wedge_mem_spCone unit_mem_spCone (isSemipositiveOneOne_pi11 (hγ e z hz))
  | k + 1, β, hβ => fun e z hz =>
      wedge_mem_spCone (slotForm_mem_positiveCone hγ k _ (fun j => hβ j.castSucc) e z hz)
        ⟨(β (Fin.last k)).2.2 e z hz, fun v => hβ (Fin.last k) e z hz v⟩

end Slot

/-! ### The slot functional of a positive current -/

section Functional

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {k : ℕ} {T : ProductCurrent n M (k + 1)}

/-- Only the `(1,1)`-parts at chart points matter. -/
theorem apply_slotForm_congr (hT : IsPositive T) (β : Fin k → ClosedRealOneOneForm n M)
    {γ γ' : SmoothRealForm n M 2}
    (h : ∀ (e : ComplexChart n M) z, z ∈ e.val.target →
      pi11 (γ.coeff e z) = pi11 (γ'.coeff e z)) :
    T (slotForm γ k β) = T (slotForm γ' k β) :=
  hT.apply_eq_of_coeff_eqOn fun e z hz => by
    rw [slotForm_coeff, slotForm_coeff, h e z hz]

/-- Only the values at chart points matter. -/
theorem apply_slotForm_congr' (hT : IsPositive T) (β : Fin k → ClosedRealOneOneForm n M)
    {γ γ' : SmoothRealForm n M 2}
    (h : ∀ (e : ComplexChart n M) z, z ∈ e.val.target → γ.coeff e z = γ'.coeff e z) :
    T (slotForm γ k β) = T (slotForm γ' k β) :=
  apply_slotForm_congr hT β fun e z hz => by rw [h e z hz]

theorem apply_slotForm_nonneg (hT : IsPositive T) {β : Fin k → ClosedRealOneOneForm n M}
    (hβ : ∀ j, (β j).val.IsSemipositive) {γ : SmoothRealForm n M 2}
    (hγ : ∀ (e : ComplexChart n M) z, z ∈ e.val.target → CoefficientSemipositive (γ.coeff e z)) :
    0 ≤ T (slotForm γ k β) :=
  hT _ (slotForm_mem_positiveCone hγ k β hβ)

end Functional

/-! ### The Leibniz rule and the chain rule for `d(f dg)` -/

section Leibniz

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Leibniz** at a chart point: `d((Uf) dg) = U d(f dg) + f d(U dg)`. -/
theorem exactPair_mul_coeff {U f g : M → ℝ} (hU : ChartSmooth (n := n) U)
    (hf : ChartSmooth (n := n) f) (hg : ChartSmooth (n := n) g) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (exactPair (fun x => U x * f x) g (chartSmooth_mul hU hf) hg).coeff e z =
      U (e.val.symm z) • (exactPair f g hf hg).coeff e z +
        f (e.val.symm z) • (exactPair U g hU hg).coeff e z := by
  have hnhds : e.val.target ∈ 𝓝 z := e.val.open_target.mem_nhds hz
  have hUd : DifferentiableAt ℝ (fun y => U (e.val.symm y)) z :=
    ((hU e).contDiffAt hnhds).differentiableAt (by simp)
  have hfd : DifferentiableAt ℝ (fun y => f (e.val.symm y)) z :=
    ((hf e).contDiffAt hnhds).differentiableAt (by simp)
  ext w
  rw [eq_vec_two' w, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.smul_apply, exactPair_coeff_apply _ g _ hg e hz,
    exactPair_coeff_apply f g hf hg e hz, exactPair_coeff_apply U g hU hg e hz]
  have hprod : ∀ a, fderiv ℝ (fun y => U (e.val.symm y) * f (e.val.symm y)) z a =
      U (e.val.symm z) * fderiv ℝ (fun y => f (e.val.symm y)) z a +
        f (e.val.symm z) * fderiv ℝ (fun y => U (e.val.symm y)) z a := fun a => by
    rw [show (fun y => U (e.val.symm y) * f (e.val.symm y)) =
      (fun y => U (e.val.symm y)) * fun y => f (e.val.symm y) from rfl, fderiv_mul hUd hfd]
    simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hprod, hprod]
  simp only [smul_eq_mul]
  ring

/-- **Chain rule**: where `U = θ ∘ v` near the point, `d(U dg) = θ'(v) d(v dg)`. -/
theorem exactPair_coeff_eq_deriv_smul {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {U v g : M → ℝ}
    (hU : ChartSmooth (n := n) U) (hv : ChartSmooth (n := n) v) (hg : ChartSmooth (n := n) g)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (heq : (fun y => U (e.val.symm y)) =ᶠ[𝓝 z] fun y => θ (v (e.val.symm y))) :
    (exactPair U g hU hg).coeff e z = deriv θ (v (e.val.symm z)) • (exactPair v g hv hg).coeff e z
      := by
  have hnhds : e.val.target ∈ 𝓝 z := e.val.open_target.mem_nhds hz
  have hvd : DifferentiableAt ℝ (fun y => v (e.val.symm y)) z :=
    ((hv e).contDiffAt hnhds).differentiableAt (by simp)
  have hθd : DifferentiableAt ℝ θ (v (e.val.symm z)) :=
    (hθ.differentiable (by simp)).differentiableAt
  have hD : fderiv ℝ (fun y => U (e.val.symm y)) z =
      deriv θ (v (e.val.symm z)) • fderiv ℝ (fun y => v (e.val.symm y)) z := by
    rw [heq.fderiv_eq]
    exact (hθd.hasDerivAt.comp_hasFDerivAt z hvd.hasFDerivAt).fderiv
  ext w
  rw [eq_vec_two' w, ContinuousAlternatingMap.smul_apply, exactPair_coeff_apply U g hU hg e hz,
    exactPair_coeff_apply v g hv hg e hz, hD]
  simp only [smul_apply, smul_eq_mul]
  ring

variable {k : ℕ} {T : ProductCurrent n M (k + 1)}

/-- **The Leibniz reduction** (Skoda--El Mir step E3): for a closed positive current,
`T (U Π₁₁ d(f dg) ∧ β) = - T (f Π₁₁ (dU ∧ dg) ∧ β)`. -/
theorem apply_smulTest_closedTestForm (hT : IsPositive T) (hTc : IsClosedCurrent T)
    {U f g : M → ℝ} (hU : ChartSmooth (n := n) U) (hf : ChartSmooth (n := n) f)
    (hg : ChartSmooth (n := n) g) (β : Fin k → ClosedRealOneOneForm n M) :
    T (smulTest U hU (closedTestForm f g hf hg k β)) =
      -T (smulTest f hf (slotForm (exactPair U g hU hg) k β)) := by
  rw [closedTestForm_eq_slotForm, ← slotForm_smulFun, ← slotForm_smulFun]
  have hcongr := apply_slotForm_congr' hT β (γ := smulFun U hU (exactPair f g hf hg))
    (γ' := exactPair (fun x => U x * f x) g (chartSmooth_mul hU hf) hg -
      smulFun f hf (exactPair U g hU hg)) fun e z hz => by
    rw [coeff_sub, exactPair_mul_coeff hU hf hg e hz, smulFun_coeff, smulFun_coeff]
    abel
  rw [hcongr, slotForm_sub, map_sub, ← closedTestForm_eq_slotForm,
    (isClosedCurrent_succ_iff T).mp hTc, zero_sub]

end Leibniz

/-! ### Integration by parts in a chart -/

section ModelIBP

variable {n : ℕ}

/-- The real coordinate functionals of the standard real frame. -/
def coordFun (j : Fin (2 * n)) : ComplexModel n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((topBasis n).coord j)

theorem sum_coordFun_smul (v : ComplexModel n) : ∑ j, coordFun j v • topBasis n j = v :=
  (topBasis n).sum_repr v

/-- The coefficients `cⱼ = (H dᶜU - U dᶜH)(eⱼ)` of the one-form `H dᶜU - U dᶜH` in the real frame
(`dᶜF (b) = -(1/4π) dF (i b)`). -/
def ibpCoeff (H U : ComplexModel n → ℝ) (j : Fin (2 * n)) (y : ComplexModel n) : ℝ :=
  H y * (-1 / (4 * Real.pi) * fderiv ℝ U y (Complex.I • topBasis n j)) -
    -1 / (4 * Real.pi) * fderiv ℝ H y (Complex.I • topBasis n j) * U y

/-- The one-form `H dᶜU - U dᶜH` evaluated on `b`. -/
def ibpForm (H U : ComplexModel n → ℝ) (b y : ComplexModel n) : ℝ :=
  H y * (-1 / (4 * Real.pi) * fderiv ℝ U y (Complex.I • b)) -
    -1 / (4 * Real.pi) * fderiv ℝ H y (Complex.I • b) * U y

theorem sum_ibpCoeff_mul (H U : ComplexModel n → ℝ) (b y : ComplexModel n) :
    ∑ j, ibpCoeff H U j y * coordFun j b = ibpForm H U b y := by
  have hb : Complex.I • b = ∑ j, coordFun j b • (Complex.I • topBasis n j) := by
    conv_lhs => rw [← sum_coordFun_smul b]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
  rw [ibpForm, hb, map_sum, map_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ibpCoeff, map_smul, smul_eq_mul]
  ring

theorem hasFDerivAt_fderiv_apply {F : ComplexModel n → ℝ} {z : ComplexModel n}
    (hF : ContDiffAt ℝ 2 F z) (c : ComplexModel n) :
    HasFDerivAt (fun y => fderiv ℝ F y c) ((fderiv ℝ (fderiv ℝ F) z).flip c) z := by
  have hDD : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simpa using hDD.hasFDerivAt.clm_apply (hasFDerivAt_const c z)

theorem hasFDerivAt_ibpForm {H U : ComplexModel n → ℝ} {z : ComplexModel n}
    (hH : ContDiffAt ℝ 2 H z) (hU : ContDiffAt ℝ 2 U z) (b : ComplexModel n) :
    HasFDerivAt (ibpForm H U b)
      (H z • ((-1 / (4 * Real.pi)) • (fderiv ℝ (fderiv ℝ U) z).flip (Complex.I • b)) +
        (-1 / (4 * Real.pi) * fderiv ℝ U z (Complex.I • b)) • fderiv ℝ H z -
        ((-1 / (4 * Real.pi) * fderiv ℝ H z (Complex.I • b)) • fderiv ℝ U z +
          U z • ((-1 / (4 * Real.pi)) • (fderiv ℝ (fderiv ℝ H) z).flip (Complex.I • b)))) z := by
  have hHd := (hH.differentiableAt (by norm_num)).hasFDerivAt
  have hUd := (hU.differentiableAt (by norm_num)).hasFDerivAt
  exact (hHd.mul ((hasFDerivAt_fderiv_apply hU _).const_mul _)).sub
    (((hasFDerivAt_fderiv_apply hH _).const_mul _).mul hUd)

theorem hasFDerivAt_ibpCoeff {H U : ComplexModel n → ℝ} {z : ComplexModel n}
    (hH : ContDiffAt ℝ 2 H z) (hU : ContDiffAt ℝ 2 U z) (j : Fin (2 * n)) :
    DifferentiableAt ℝ (ibpCoeff H U j) z :=
  (hasFDerivAt_ibpForm hH hU (topBasis n j)).differentiableAt

/-- `∑ⱼ dcⱼ(a) ℓⱼ(b) = d(α(b))(a)` for `α = H dᶜU - U dᶜH`, explicitly. -/
theorem sum_fderiv_ibpCoeff {H U : ComplexModel n → ℝ} {z : ComplexModel n}
    (hH : ContDiffAt ℝ 2 H z) (hU : ContDiffAt ℝ 2 U z) (a b : ComplexModel n) :
    ∑ j, fderiv ℝ (ibpCoeff H U j) z a * coordFun j b =
      H z * (-1 / (4 * Real.pi) * fderiv ℝ (fderiv ℝ U) z a (Complex.I • b)) +
        -1 / (4 * Real.pi) * fderiv ℝ U z (Complex.I • b) * fderiv ℝ H z a -
        (-1 / (4 * Real.pi) * fderiv ℝ H z (Complex.I • b) * fderiv ℝ U z a +
          U z * (-1 / (4 * Real.pi) * fderiv ℝ (fderiv ℝ H) z a (Complex.I • b))) := by
  have h2 : HasFDerivAt (fun y => ∑ j, ibpCoeff H U j y * coordFun j b)
      (∑ j, coordFun j b • fderiv ℝ (ibpCoeff H U j) z) z :=
    HasFDerivAt.fun_sum fun j _ => (hasFDerivAt_ibpCoeff hH hU j).hasFDerivAt.mul_const _
  have heq : (fun y => ∑ j, ibpCoeff H U j y * coordFun j b) = ibpForm H U b :=
    funext fun y => sum_ibpCoeff_mul H U b y
  rw [heq] at h2
  have hu := congrArg (fun L : ComplexModel n →L[ℝ] ℝ => L a)
    (h2.unique (hasFDerivAt_ibpForm hH hU b))
  simp only [_root_.sum_apply, smul_apply, smul_eq_mul,
    sub_apply, add_apply, ContinuousLinearMap.flip_apply] at hu
  rw [← hu]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **The model identity behind integration by parts**: the `(1,1)`-part of
`∑ⱼ dcⱼ ∧ dℓⱼ = d(H dᶜU - U dᶜH)` is `H ddᶜU - U ddᶜH`. -/
theorem ibp_identity {H U : ComplexModel n → ℝ} {z : ComplexModel n}
    (hH : ContDiffAt ℝ 2 H z) (hU : ContDiffAt ℝ 2 U z) (a b : ComplexModel n) :
    ((∑ j, (fderiv ℝ (ibpCoeff H U j) z a * coordFun j b -
        fderiv ℝ (ibpCoeff H U j) z b * coordFun j a)) +
      ∑ j, (fderiv ℝ (ibpCoeff H U j) z (Complex.I • a) * coordFun j (Complex.I • b) -
        fderiv ℝ (ibpCoeff H U j) z (Complex.I • b) * coordFun j (Complex.I • a))) / 2 =
      H z * smoothDDC U z ![a, b] - U z * smoothDDC H z ![a, b] := by
  simp only [Finset.sum_sub_distrib]
  rw [sum_fderiv_ibpCoeff hH hU, sum_fderiv_ibpCoeff hH hU, sum_fderiv_ibpCoeff hH hU,
    sum_fderiv_ibpCoeff hH hU, smoothDDC_apply_eq_realHessian hU,
    smoothDDC_apply_eq_realHessian hH]
  simp only [realHessian_eq_fderiv, I_smul_I_smul, map_neg]
  have sU : ∀ x y, fderiv ℝ (fderiv ℝ U) z x y = fderiv ℝ (fderiv ℝ U) z y x := fun x y =>
    hU.isSymmSndFDerivAt (by norm_num) x y
  have sH : ∀ x y, fderiv ℝ (fderiv ℝ H) z x y = fderiv ℝ (fderiv ℝ H) z y x := fun x y =>
    hH.isSymmSndFDerivAt (by norm_num) x y
  rw [sU (Complex.I • a) b, sU (Complex.I • b) a, sH (Complex.I • a) b, sH (Complex.I • b) a]
  ring

end ModelIBP

section IBP

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Two global forms agreeing at the points of one chart, and vanishing at the chart points off a
subset `K` of its domain, agree at every chart point. -/
theorem coeff_eq_of_chart {p : ℕ} {a b : SmoothRealForm n M p} (e : ComplexChart n M)
    {K : Set M} (hKe : K ⊆ e.val.source)
    (hab : ∀ z ∈ e.val.target, a.coeff e z = b.coeff e z)
    (ha : ∀ (e' : ComplexChart n M) z, z ∈ e'.val.target → e'.val.symm z ∉ K → a.coeff e' z = 0)
    (hb : ∀ (e' : ComplexChart n M) z, z ∈ e'.val.target → e'.val.symm z ∉ K → b.coeff e' z = 0)
    (e' : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e'.val.target) :
    a.coeff e' z = b.coeff e' z := by
  by_cases hx : e'.val.symm z ∈ K
  · have hzs : z ∈ (chartTransition e' e).source := ⟨hz, hKe hx⟩
    have hmem : chartTransition e' e z ∈ e.val.target := e.val.map_source (hKe hx)
    ext v
    rw [a.compatible e' e z hzs v, b.compatible e' e z hzs v, hab _ hmem]
  · rw [ha e' z hz hx, hb e' z hz hx]

omit [IsComplexManifold n M] in
theorem chartExtend_symm {e : ComplexChart n M} {β : ComplexModel n → ℝ} {z : ComplexModel n}
    (hz : z ∈ e.val.target) : chartExtend e β (e.val.symm z) = β z := by
  rw [chartExtend_of_mem (e.val.map_target hz), e.val.right_inv hz]

omit [IsComplexManifold n M] in
theorem chartExtend_eventuallyEq {e : ComplexChart n M} {β : ComplexModel n → ℝ}
    {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (fun y => chartExtend e β (e.val.symm y)) =ᶠ[𝓝 z] β := by
  filter_upwards [e.val.open_target.mem_nhds hz] with y hy
  exact chartExtend_symm hy

theorem tsupport_chartExtend_subset {e : ComplexChart n M} {β : ComplexModel n → ℝ}
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKe : K ⊆ e.val.target)
    (hβ : tsupport β ⊆ K) : tsupport (chartExtend e β) ⊆ e.val.symm '' K := by
  have hKc : IsCompact (e.val.symm '' K) :=
    hK.image_of_continuousOn (e.val.continuousOn_symm.mono hKe)
  refine (support_chartExtend_subset e).trans ?_
  rw [hKc.isClosed.closure_subset_iff]
  exact image_mono hβ

omit [IsComplexManifold n M] in
theorem image_symm_subset_source {e : ComplexChart n M} {K : Set (ComplexModel n)}
    (hKe : K ⊆ e.val.target) : e.val.symm '' K ⊆ e.val.source := by
  rintro _ ⟨z, hz, rfl⟩
  exact e.val.map_target (hKe hz)

/-- A chart-smooth function vanishing near `e'.symm z` has `ddᶜ = 0` there. -/
theorem ddcForm_coeff_eq_zero {h : M → ℝ} (hh : ChartSmooth (n := n) h) {e : ComplexChart n M}
    {z : ComplexModel n} (hz : z ∈ e.val.target) (hx : e.val.symm z ∉ tsupport h) :
    (ddcForm h hh).coeff e z = 0 := by
  have h0 := chart_eventuallyEq_zero (N := n) hx (e.val.map_target hz)
  rw [e.val.right_inv hz] at h0
  rw [ddcForm_coeff, smoothDDC_congr h0]
  exact smoothDDC_zero z

variable {k : ℕ} {T : ProductCurrent n M (k + 1)}

/-- **Integration by parts against a closed positive current**: for `h` smooth with compact
support in one chart and `u` chart-smooth, `T (h ddᶜu ∧ β) = T (u ddᶜh ∧ β)`. -/
theorem slotForm_ibp (hT : IsPositive T) (hTc : IsClosedCurrent T)
    (β : Fin k → ClosedRealOneOneForm n M) (e : ComplexChart n M) {χ : ComplexModel n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχt : tsupport χ ⊆ e.val.target)
    {u : M → ℝ} (hu : ChartSmooth (n := n) u) :
    T (slotForm (smulFun (chartExtend e χ) (chartSmooth_chartExtend e hχ hχc hχt)
        (ddcForm u hu)) k β) =
      T (slotForm (smulFun u hu (ddcForm (chartExtend e χ)
        (chartSmooth_chartExtend e hχ hχc hχt))) k β) := by
  classical
  set hh := chartSmooth_chartExtend e hχ hχc hχt
  set h := chartExtend e χ with h_def
  set U : ComplexModel n → ℝ := fun z => u (e.val.symm z) with hU_def
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hUs : ContDiffOn ℝ ∞ U e.val.target := hu e
  have hUC : ∀ z ∈ e.val.target, ContDiffAt ℝ 2 U z := fun z hz =>
    (hUs.contDiffAt (e.val.open_target.mem_nhds hz)).of_le h2
  have hχC : ∀ z, ContDiffAt ℝ 2 χ z := fun z => hχ.contDiffAt.of_le h2
  have hdU : ContDiffOn ℝ ∞ (fun y => fderiv ℝ U y) e.val.target :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen e.val.open_target).mp hUs).2
  have hdχ : ContDiff ℝ ∞ (fun y => fderiv ℝ χ y) := (contDiff_infty_iff_fderiv.mp hχ).2
  -- a cut-off equal to one near the support of `χ`
  obtain ⟨χ₂, hχ₂1, -⟩ := exists_testFunction_eq_one_nhds_compact
    (Ω := (⟨e.val.target, e.val.open_target⟩ : TopologicalSpace.Opens (ComplexModel n)))
    hχc hχt
  -- the coefficient functions and their supports
  set c : Fin (2 * n) → ComplexModel n → ℝ := fun j => ibpCoeff χ U j with hc_def
  have hcs : ∀ j, tsupport (c j) ⊆ tsupport χ := by
    intro j
    refine closure_minimal (fun y hy => ?_) (isClosed_tsupport _)
    by_contra hyχ
    have h1 : χ y = 0 := image_eq_zero_of_notMem_tsupport hyχ
    have h2' : fderiv ℝ χ y = 0 :=
      image_eq_zero_of_notMem_tsupport fun hy' => hyχ (tsupport_fderiv_subset ℝ hy')
    exact hy (by simp [hc_def, ibpCoeff, h1, h2'])
  have hcd : ∀ j, ContDiff ℝ ∞ (c j) := by
    intro j
    have hA : ContDiff ℝ ∞ (fun y => χ y *
        (-1 / (4 * Real.pi) * fderiv ℝ U y (Complex.I • topBasis n j))) :=
      contDiff_mul_of_tsupport_subset e.val.open_target hχ hχt
        (contDiffOn_const.mul (hdU.clm_apply contDiffOn_const))
    have hψ : ContDiff ℝ ∞ (fun y => -1 / (4 * Real.pi) *
        fderiv ℝ χ y (Complex.I • topBasis n j)) :=
      contDiff_const.mul (hdχ.clm_apply contDiff_const)
    have hψs : tsupport (fun y => -1 / (4 * Real.pi) *
        fderiv ℝ χ y (Complex.I • topBasis n j)) ⊆ e.val.target := by
      refine (closure_minimal (fun y hy => ?_) (isClosed_tsupport _)).trans hχt
      by_contra hyχ
      have h2' : fderiv ℝ χ y = 0 :=
        image_eq_zero_of_notMem_tsupport fun hy' => hyχ (tsupport_fderiv_subset ℝ hy')
      exact hy (by simp [h2'])
    have hB := contDiff_mul_of_tsupport_subset e.val.open_target hψ hψs hUs
    exact hA.sub hB
  have hcc : ∀ j, HasCompactSupport (c j) := fun j =>
    IsCompact.of_isClosed_subset hχc (isClosed_tsupport _) (hcs j)
  have hct : ∀ j, tsupport (c j) ⊆ e.val.target := fun j => (hcs j).trans hχt
  set C : Fin (2 * n) → M → ℝ := fun j => chartExtend e (c j) with hC_def
  have hC : ∀ j, ChartSmooth (n := n) (C j) := fun j =>
    chartSmooth_chartExtend e (hcd j) (hcc j) (hct j)
  set g : Fin (2 * n) → ComplexModel n → ℝ := fun j z => χ₂ z * coordFun j z with hg_def
  have hgd : ∀ j, ContDiff ℝ ∞ (g j) := fun j => χ₂.contDiff.mul (coordFun j).contDiff
  have hgs : ∀ j, tsupport (g j) ⊆ e.val.target := fun j =>
    tsupport_mul_subset_left.trans χ₂.tsupport_subset
  have hgc : ∀ j, HasCompactSupport (g j) := fun j => χ₂.hasCompactSupport.mul_right
  set G : Fin (2 * n) → M → ℝ := fun j => chartExtend e (g j) with hG_def
  have hG : ∀ j, ChartSmooth (n := n) (G j) := fun j =>
    chartSmooth_chartExtend e (hgd j) (hgc j) (hgs j)
  -- closedness kills the sum of the exact pairs
  have hsum0 : T (slotForm (∑ j, exactPair (C j) (G j) (hC j) (hG j)) k β) = 0 := by
    rw [slotForm_sum, map_sum]
    exact Finset.sum_eq_zero fun j _ => by
      rw [← closedTestForm_eq_slotForm]
      exact hTc _ _ _ _ β
  -- the compact set carrying everything
  set K : Set M := e.val.symm '' tsupport χ with hK_def
  have hKe : K ⊆ e.val.source := image_symm_subset_source hχt
  have hhK : tsupport h ⊆ K := tsupport_chartExtend_subset hχc hχt subset_rfl
  have hCK : ∀ j, tsupport (C j) ⊆ K := fun j => tsupport_chartExtend_subset hχc hχt (hcs j)
  -- the coefficient identity
  set A : SmoothRealForm n M 2 := smulFun h hh (ddcForm u hu) - smulFun u hu (ddcForm h hh)
    with hA_def
  set S : SmoothRealForm n M 2 := ∑ j, exactPair (C j) (G j) (hC j) (hG j) with hS_def
  have hS_coeff : ∀ (e' : ComplexChart n M) z, S.coeff e' z =
      ∑ j, (exactPair (C j) (G j) (hC j) (hG j)).coeff e' z := fun e' z => by
    rw [hS_def, coeff_sum]
  have hident : ∀ (e' : ComplexChart n M) z, z ∈ e'.val.target →
      pi11 (A.coeff e' z) = pi11 (S.coeff e' z) := by
    refine coeff_eq_of_chart (a := pi11Form A) (b := pi11Form S) e hKe ?_ ?_ ?_
    · -- in the chart `e`
      intro z hz
      rw [pi11Form_coeff, pi11Form_coeff]
      by_cases hzχ : z ∈ tsupport χ
      · -- the computation
        have hUz := hUC z hz
        have hχz := hχC z
        have hhe : (fun y => h (e.val.symm y)) =ᶠ[𝓝 z] χ := chartExtend_eventuallyEq hz
        have hAz : A.coeff e z = χ z • smoothDDC U z - U z • smoothDDC χ z := by
          rw [hA_def, coeff_sub, smulFun_coeff, smulFun_coeff, ddcForm_coeff, ddcForm_coeff,
            smoothDDC_congr hhe, h_def, chartExtend_symm hz]
        have hχ₂z : ∀ᶠ y in 𝓝 z, χ₂ y = 1 := hχ₂1.filter_mono (nhds_le_nhdsSet hzχ)
        have hCe : ∀ j, fderiv ℝ (fun y => C j (e.val.symm y)) z = fderiv ℝ (c j) z := fun j =>
          (chartExtend_eventuallyEq hz).fderiv_eq
        have hGe : ∀ j, fderiv ℝ (fun y => G j (e.val.symm y)) z = coordFun j := fun j => by
          have : (fun y => G j (e.val.symm y)) =ᶠ[𝓝 z] coordFun j := by
            filter_upwards [chartExtend_eventuallyEq (β := g j) hz, hχ₂z] with y hy hy2
            change chartExtend e (g j) (e.val.symm y) = coordFun j y
            rw [hy]
            simp [hg_def, hy2]
          rw [this.fderiv_eq, (coordFun j).fderiv]
        ext w
        rw [eq_vec_two' w, pi11_apply, pi11_apply, hS_coeff, hAz]
        simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.sub_apply,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul,
          exactPair_coeff_apply _ _ _ _ e hz, hCe, hGe]
        have hid := ibp_identity hχz hUz (w 0) (w 1)
        rw [smoothDDC_isOneOne hUz, smoothDDC_isOneOne hχz]
        simp only [Finset.sum_sub_distrib] at hid ⊢
        linarith
      · -- off the support both vanish
        have hχ0 : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hzχ
        have hAz : A.coeff e z = 0 := by
          have hhe : (fun y => h (e.val.symm y)) =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
            (chartExtend_eventuallyEq hz).trans hχ0
          rw [hA_def, coeff_sub, smulFun_coeff, smulFun_coeff, ddcForm_coeff, ddcForm_coeff,
            smoothDDC_congr hhe, smoothDDC_zero, h_def, chartExtend_symm hz,
            image_eq_zero_of_notMem_tsupport hzχ]
          simp
        have hSz : S.coeff e z = 0 := by
          rw [hS_coeff]
          refine Finset.sum_eq_zero fun j _ => exactPair_coeff_eq_zero _ _ hz ?_
          exact (chartExtend_eventuallyEq hz).trans
            (notMem_tsupport_iff_eventuallyEq.mp fun hz' => hzχ (hcs j hz'))
        rw [hAz, hSz]
    · -- `A` vanishes off `K`
      intro e' z hz hx
      have hxh : e'.val.symm z ∉ tsupport h := fun h' => hx (hhK h')
      rw [pi11Form_coeff, hA_def, coeff_sub, smulFun_coeff, smulFun_coeff,
        ddcForm_coeff_eq_zero hh hz hxh, image_eq_zero_of_notMem_tsupport hxh]
      simp [pi11_zero]
    · -- `S` vanishes off `K`
      intro e' z hz hx
      rw [pi11Form_coeff, hS_coeff]
      have : ∑ j, (exactPair (C j) (G j) (hC j) (hG j)).coeff e' z = 0 := by
        refine Finset.sum_eq_zero fun j _ => exactPair_coeff_eq_zero _ _ hz ?_
        have h0 := chart_eventuallyEq_zero (N := n) (fun h' => hx (hCK j h'))
          (e'.val.map_target hz)
        rwa [e'.val.right_inv hz] at h0
      rw [this, pi11_zero]
  have hcong := apply_slotForm_congr hT β hident
  rw [hA_def, slotForm_sub, map_sub] at hcong
  linarith

end IBP

end SGPT.Foundations.Analysis.Pending.SlotTestForms
