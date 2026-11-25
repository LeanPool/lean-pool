/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PositiveProductCurrents
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ExteriorDerivative
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateDensityFrame

/-!
# Closed currents in the product-test-form framework

A current of bidimension `(q, q)` in the sense of `Pending.PositiveProductCurrents` is a linear
functional on the test forms `h · β₁ ∧ ⋯ ∧ β_q` (`β` real `(1,1)`-forms).  A current `T` of
bidimension `(k+1, k+1)` is *closed* (`IsClosedCurrent`) when

`T (Π₁₁ d(f dg) ∧ β₁ ∧ ⋯ ∧ β_k) = 0`

for all chart-smooth functions `f, g` and all CLOSED real `(1,1)`-forms `βⱼ`, where `Π₁₁` is the
`(1,1)`-part of a real two-form, `Π₁₁ A (u, v) = (A(u, v) + A(iu, iv)) / 2` (`pi11`).

*Faithfulness.*  If `T` extends to a current `T̂` on all forms of degree `2(k+1)` vanishing off
type `(k+1, k+1)` and `dT̂ = 0`, then `T̂(d(f dg ∧ β)) = T̂(d(f dg) ∧ β) = T(Π₁₁ d(f dg) ∧ β)`,
because `β` is closed and the `(2,0) + (0,2)`-part of `d(f dg)` wedged with a `(k,k)`-form is
not of type `(k+1, k+1)`; so a closed current in the sense of `demailly-cadg:III.1` is closed
here.  Conversely these are exactly the tests used by the Skoda--El Mir theorem and by the
support theorems (`demailly-cadg:III.2.3`, `III.2.10`, `III.2.13`), with `g` a cut-off linear
coordinate and `β` cut-off constant-coefficient forms (`dd^c` of cut-off quadratic functions,
which are globally closed).  On a compact manifold every one-form is a finite sum of forms
`f dg`, so testing with `f dg` is testing with all one-forms.  No use is made of the basis lemma
`demailly-cadg:III.1.4`.  (Design: the Skoda–El Mir extension argument, D1.)

In a chart, `d(f dg)(u, v) = df(u) dg(v) - df(v) dg(u)` (`exactPair_coeff_apply`): the scalar
Leibniz rule `d(F α) = dF ∧ α + F dα` (`extDeriv_smul_eq`) and `d² = 0`.

## Main results

* `complexJ`, `pi11`, `isOneOne_pi11`, `pi11_eq_self`, `pi11CLM`; `pi11Form`,
    `isTypeOneOne_pi11Form`.
* `oneWedge`, `oneWedge_apply_two`, `extDeriv_smul_eq` (scalar Leibniz), `extDeriv_zeroForm_eq`.
* `exactPair` (`d(f dg)` as a global two-form), `exactPair_coeff_apply`.
* `closedTestForm`, `closedTestForm_snoc`, `IsClosedCurrent`; `isClosedCurrent_zero`,
  `IsClosedCurrent.add`, `IsClosedCurrent.smul`, `isClosedCurrent_of_tendsto` (weak limits),
  `IsClosedCurrent.wedge` (wedge with a closed `(1,1)`-form).
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.ClosedProductCurrents

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms ProductTestForms PositiveProductCurrents

/-! ### The `(1,1)`-part of a real two-form -/

section Pointwise

variable {n : ℕ}

variable (n) in
/-- Multiplication by `i`, as a real-linear map of the model space. -/
abbrev complexJ : ComplexModel n →L[ℝ] ComplexModel n :=
  modelComplexStructure n

@[simp] theorem complexJ_apply (v : ComplexModel n) : complexJ n v = Complex.I • v := rfl

theorem comp_two (L : ComplexModel n →L[ℝ] ComplexModel n) (u v : ComplexModel n) :
    (⇑L ∘ ![u, v]) = ![L u, L v] := by
  funext i
  fin_cases i <;> rfl

/-- The `(1,1)`-part `Π₁₁ A (u, v) = (A(u, v) + A(iu, iv)) / 2` of a real two-form. -/
def pi11 (A : RealForm n 2) : RealForm n 2 :=
  (1 / 2 : ℝ) • (A + A.compContinuousLinearMap (complexJ n))

theorem pi11_apply (A : RealForm n 2) (u v : ComplexModel n) :
    pi11 A ![u, v] = (A ![u, v] + A ![Complex.I • u, Complex.I • v]) / 2 := by
  simp only [pi11, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, comp_two, complexJ_apply,
    smul_eq_mul]
  ring

theorem eq_vec_two (w : Fin 2 → ComplexModel n) : w = ![w 0, w 1] := by
  funext i
  fin_cases i <;> rfl

theorem neg_neg_apply (A : RealForm n 2) (u v : ComplexModel n) : A ![-u, -v] = A ![u, v] := by
  have h1 := twoForm_smul_left A (-1) u (-v)
  have h2 := twoForm_smul_right A (-1) u v
  simp only [neg_smul, one_smul] at h1 h2
  rw [h1, h2]
  ring

/-- `Π₁₁ A` is of type `(1,1)`. -/
theorem isOneOne_pi11 (A : RealForm n 2) : IsOneOne (pi11 A) := by
  intro u v
  rw [pi11_apply, pi11_apply, smul_smul, smul_smul, Complex.I_mul_I, neg_one_smul, neg_one_smul,
    neg_neg_apply]
  ring

/-- `Π₁₁` fixes `(1,1)`-forms. -/
theorem pi11_eq_self {A : RealForm n 2} (hA : IsOneOne A) : pi11 A = A := by
  ext w
  rw [eq_vec_two w, pi11_apply, hA]
  ring

variable (n) in
/-- `Π₁₁` as a continuous linear map. -/
def pi11CLM : RealForm n 2 →L[ℝ] RealForm n 2 :=
  haveI := realForm_finiteDimensional (n := n) 2
  LinearMap.toContinuousLinearMap
    { toFun := pi11
      map_add' := fun A B => by
        ext w
        simp only [pi11, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
          ContinuousAlternatingMap.compContinuousLinearMap_apply, smul_eq_mul]
        ring
      map_smul' := fun c A => by
        ext w
        simp only [pi11, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
          ContinuousAlternatingMap.compContinuousLinearMap_apply, smul_eq_mul, RingHom.id_apply]
        ring }

@[simp] theorem pi11CLM_apply (A : RealForm n 2) : pi11CLM n A = pi11 A := rfl

end Pointwise

/-! ### Chart calculus: the scalar Leibniz rule -/

section Calculus

variable {n k : ℕ}

/-- The exterior product `ℓ ∧ α` of a covector with a `k`-form, by the alternating sum
`(ℓ ∧ α)(v) = ∑ᵢ (-1)ⁱ ℓ(vᵢ) α(v without vᵢ)`. -/
def oneWedge (ℓ : ComplexModel n →L[ℝ] ℝ) (α : RealForm n k) : RealForm n (k + 1) :=
  ContinuousAlternatingMap.alternatizeUncurryFin (ℓ.smulRight α)

theorem oneWedge_apply_two (ℓ m : ComplexModel n →L[ℝ] ℝ) (u v : ComplexModel n) :
    oneWedge ℓ (ContinuousAlternatingMap.ofSubsingleton ℝ (ComplexModel n) ℝ (0 : Fin 1) m)
        ![u, v] = ℓ u * m v - ℓ v * m u := by
  rw [oneWedge, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, Fin.val_zero, pow_zero, one_smul,
    Fin.val_one, pow_one, neg_smul, smul_eq_mul]
  simp [Fin.removeNth]
  ring

/-- **The scalar Leibniz rule** `d(F α) = dF ∧ α + F dα` at a point of differentiability. -/
theorem extDeriv_smul_eq {F : ComplexModel n → ℝ} {α : ComplexModel n → RealForm n k}
    {z : ComplexModel n} (hF : DifferentiableAt ℝ F z) (hα : DifferentiableAt ℝ α z) :
    extDeriv (fun y => F y • α y) z = oneWedge (fderiv ℝ F z) (α z) + F z • extDeriv α z := by
  change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (fun y => F y • α y) z) =
    ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ F z).smulRight (α z)) +
      F z • ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ α z)
  rw [fderiv_fun_smul hF hα, ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
  exact add_comm _ _

theorem smul_coordinateWedgeUnit (c : ℝ) :
    c • (coordinateWedgeUnit : RealForm n 0) =
      ContinuousAlternatingMap.constOfIsEmpty ℝ (ComplexModel n) (Fin 0) c := by
  ext v
  simp [coordinateWedgeUnit]

/-- The exterior derivative of a `0`-form `G · 1`. -/
theorem extDeriv_zeroForm_eq (G : ComplexModel n → ℝ) (z : ComplexModel n) :
    extDeriv (fun y => G y • (coordinateWedgeUnit : RealForm n 0)) z =
      ContinuousAlternatingMap.ofSubsingleton ℝ (ComplexModel n) ℝ (0 : Fin 1) (fderiv ℝ G z) := by
  simp only [smul_coordinateWedgeUnit]
  exact extDeriv_constOfIsEmpty G z

end Calculus

/-! ### Global forms -/

section Global

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The `(1,1)`-part of a global smooth two-form. -/
def pi11Form (a : SmoothRealForm n M 2) : SmoothRealForm n M 2 where
  coeff e z := pi11 (a.coeff e z)
  smooth e := (pi11CLM n).contDiff.comp_contDiffOn (a.smooth e)
  compatible e f z hz v := by
    set D := chartTransitionDerivative e f z
    have hJ : ∀ w, D (Complex.I • w) = Complex.I • D w := fun w =>
      chartTransitionDerivative_complex_smul e f z hz Complex.I w
    obtain ⟨u, w, rfl⟩ : ∃ u w, v = ![u, w] := ⟨v 0, v 1, eq_vec_two v⟩
    have h1 : (fun i => D (![u, w] i)) = ![D u, D w] := by
      funext i; fin_cases i <;> rfl
    have h2 : (fun i => D (![Complex.I • u, Complex.I • w] i)) =
        ![Complex.I • D u, Complex.I • D w] := by
      funext i; fin_cases i <;> simp [hJ]
    change pi11 (a.coeff e z) ![u, w] = pi11 (a.coeff f (chartTransition e f z)) (fun i => D (![u,
      w] i))
    rw [h1, pi11_apply, pi11_apply, a.compatible e f z hz, a.compatible e f z hz, h1, h2]

@[simp] theorem pi11Form_coeff (a : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) : (pi11Form a).coeff e z = pi11 (a.coeff e z) := rfl

theorem isTypeOneOne_pi11Form (a : SmoothRealForm n M 2) : (pi11Form a).IsTypeOneOne :=
  fun _ _ _ => isOneOne_pi11 _

/-- `d(f dg)`, as a global smooth two-form. -/
def exactPair (f g : M → ℝ) (hf : ChartSmooth (n := n) f) (hg : ChartSmooth (n := n) g) :
    SmoothRealForm n M 2 :=
  SmoothRealForm.exteriorDerivative
    (smulFun f hf (SmoothRealForm.exteriorDerivative (smulFun g hg unitForm)))

/-- **`d(f dg)` in a chart**: `d(f dg)(u, v) = df(u) dg(v) - df(v) dg(u)`, with the
derivatives of `f ∘ e⁻¹` and `g ∘ e⁻¹`. -/
theorem exactPair_coeff_apply (f g : M → ℝ) (hf : ChartSmooth (n := n) f)
    (hg : ChartSmooth (n := n) g) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) (u v : ComplexModel n) :
    (exactPair f g hf hg).coeff e z ![u, v] =
      fderiv ℝ (fun y => f (e.val.symm y)) z u * fderiv ℝ (fun y => g (e.val.symm y)) z v -
        fderiv ℝ (fun y => f (e.val.symm y)) z v * fderiv ℝ (fun y => g (e.val.symm y)) z u := by
  set F : ComplexModel n → ℝ := fun y => f (e.val.symm y)
  set G : ComplexModel n → ℝ := fun y => g (e.val.symm y)
  have hnhds : e.val.target ∈ 𝓝 z := e.val.open_target.mem_nhds hz
  have hFs : ContDiffAt ℝ ∞ F z := (hf e).contDiffAt hnhds
  have hGs : ContDiffAt ℝ ∞ G z := (hg e).contDiffAt hnhds
  -- the one-form `dg` in the chart
  set dG : ComplexModel n → RealForm n 1 := fun y =>
    ContinuousAlternatingMap.ofSubsingleton ℝ (ComplexModel n) ℝ (0 : Fin 1) (fderiv ℝ G y)
  have hdg : (SmoothRealForm.exteriorDerivative (smulFun g hg unitForm)).coeff e = dG := by
    funext y
    change extDeriv (fun w => g (e.val.symm w) • (coordinateWedgeUnit : RealForm n 0)) y = _
    exact extDeriv_zeroForm_eq G y
  have hcoeff : (exactPair f g hf hg).coeff e = extDeriv (fun y => F y • dG y) := by
    change extDeriv (fun y => f (e.val.symm y) •
      (SmoothRealForm.exteriorDerivative (smulFun g hg unitForm)).coeff e y) = _
    rw [hdg]
  -- `dG` is the exterior derivative of the `0`-form `G`, hence smooth with `d dG = 0`
  have hdG_eq : dG = extDeriv (fun y => G y • (coordinateWedgeUnit : RealForm n 0)) := by
    funext y
    exact (extDeriv_zeroForm_eq G y).symm
  have hG0 : ContDiffAt ℝ ∞ (fun y => G y • (coordinateWedgeUnit : RealForm n 0)) z :=
    hGs.smul contDiffAt_const
  have hdGdiff : DifferentiableAt ℝ dG z := by
    rw [hdG_eq]
    have h := ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ).contDiff
      (n := ∞)).contDiffAt.comp z (hG0.fderiv_right (m := ∞) le_rfl)
    exact h.differentiableAt (by simp)
  have hddG : extDeriv dG z = 0 := by
    rw [hdG_eq]
    exact extDeriv_extDeriv_apply hG0
      (by simp)
  rw [hcoeff, extDeriv_smul_eq (hFs.differentiableAt (by simp)) hdGdiff, hddG, smul_zero,
    add_zero]
  exact oneWedge_apply_two _ _ u v

/-- The test form `Π₁₁ d(f dg) ∧ β₀ ∧ ⋯ ∧ β_{k-1}` of degree `2(k+1)`. -/
def closedTestForm (f g : M → ℝ) (hf : ChartSmooth (n := n) f) (hg : ChartSmooth (n := n) g) :
    (k : ℕ) → (Fin k → ClosedRealOneOneForm n M) → testSpace n M (k + 1)
  | 0, _ => ⟨wedgeTwo unitForm (pi11Form (exactPair f g hf hg)),
      wedgeTwo_mem_testSpace unitForm_mem_testSpace (isTypeOneOne_pi11Form _)⟩
  | k + 1, β => wedgeTestLM (β (Fin.last k)).2.2 (k + 1)
      (closedTestForm f g hf hg k fun j => β j.castSucc)

theorem closedTestForm_snoc (f g : M → ℝ) (hf : ChartSmooth (n := n) f)
    (hg : ChartSmooth (n := n) g) (k : ℕ) (β : Fin k → ClosedRealOneOneForm n M)
    (γ : ClosedRealOneOneForm n M) :
    closedTestForm f g hf hg (k + 1) (Fin.snoc β γ) =
      wedgeTestLM γ.2.2 (k + 1) (closedTestForm f g hf hg k β) := by
  rw [closedTestForm]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]

end Global

/-! ### Closed currents -/

section Closed

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Closedness of a current** of bidimension `(q, q)`: for `q = k + 1`,
`T (Π₁₁ d(f dg) ∧ β₀ ∧ ⋯ ∧ β_{k-1}) = 0` for all chart-smooth `f, g` and closed real
`(1,1)`-forms `βⱼ`; currents of bidimension `(0, 0)` are closed. -/
def IsClosedCurrent : {q : ℕ} → ProductCurrent n M q → Prop
  | 0, _ => True
  | k + 1, T => ∀ (f g : M → ℝ) (hf : ChartSmooth (n := n) f) (hg : ChartSmooth (n := n) g)
      (β : Fin k → ClosedRealOneOneForm n M), T (closedTestForm f g hf hg k β) = 0

theorem isClosedCurrent_succ_iff {k : ℕ} (T : ProductCurrent n M (k + 1)) :
    IsClosedCurrent T ↔ ∀ (f g : M → ℝ) (hf : ChartSmooth (n := n) f)
      (hg : ChartSmooth (n := n) g) (β : Fin k → ClosedRealOneOneForm n M),
        T (closedTestForm f g hf hg k β) = 0 :=
  Iff.rfl

theorem isClosedCurrent_zero : ∀ {q : ℕ}, IsClosedCurrent (0 : ProductCurrent n M q)
  | 0 => trivial
  | _ + 1 => fun _ _ _ _ _ => rfl

theorem IsClosedCurrent.add : ∀ {q : ℕ} {S T : ProductCurrent n M q},
    IsClosedCurrent S → IsClosedCurrent T → IsClosedCurrent (S + T)
  | 0, _, _, _, _ => trivial
  | _ + 1, _, _, hS, hT => fun f g hf hg β => by
    rw [LinearMap.add_apply, hS f g hf hg β, hT f g hf hg β, add_zero]

theorem IsClosedCurrent.smul : ∀ {q : ℕ} {T : ProductCurrent n M q},
    IsClosedCurrent T → ∀ c : ℝ, IsClosedCurrent (c • T)
  | 0, _, _, _ => trivial
  | _ + 1, _, hT, c => fun f g hf hg β => by
    rw [LinearMap.smul_apply, hT f g hf hg β, smul_zero]

theorem IsClosedCurrent.sub : ∀ {q : ℕ} {S T : ProductCurrent n M q},
    IsClosedCurrent S → IsClosedCurrent T → IsClosedCurrent (S - T)
  | 0, _, _, _, _ => trivial
  | _ + 1, _, _, hS, hT => fun f g hf hg β => by
    rw [LinearMap.sub_apply, hS f g hf hg β, hT f g hf hg β, sub_zero]

/-- **Weak limits of closed currents are closed.** -/
theorem isClosedCurrent_of_tendsto : ∀ {q : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    {T : ι → ProductCurrent n M q} {S : ProductCurrent n M q},
    (∀ i, IsClosedCurrent (T i)) → (∀ φ, Tendsto (fun i => T i φ) l (𝓝 (S φ))) →
      IsClosedCurrent S
  | 0, _, _, _, _, _, _, _ => trivial
  | _ + 1, _, _, _, T, _, hT, hlim => fun f g hf hg β => by
    refine tendsto_nhds_unique (hlim _) ?_
    have : (fun i => T i (closedTestForm f g hf hg _ β)) = fun _ => 0 :=
      funext fun i => hT i f g hf hg β
    rw [this]
    exact tendsto_const_nhds

/-- **The wedge of a closed current with a closed `(1,1)`-form is closed.** -/
theorem IsClosedCurrent.wedge {k : ℕ} {T : ProductCurrent n M (k + 1 + 1)}
    (hT : IsClosedCurrent T) (γ : ClosedRealOneOneForm n M) :
    IsClosedCurrent (PositiveProductCurrents.wedge γ.2.2 T) := by
  intro f g hf hg β
  rw [wedge_apply, ← closedTestForm_snoc]
  exact hT f g hf hg (Fin.snoc β γ)

end Closed

end SGPT.Foundations.Analysis.Pending.ClosedProductCurrents
