/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentials

/-!
# Smooth closed real `(1,1)`-forms

The representatives are compatible smooth forms with closedness and type `(1,1)`.
The real module operations use the coefficient functions in each chart. The file also proves
linearity of the normalized `dᶜ` and `ddᶜ` on the open domain of smoothness.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ}

/-- The normalized first derivative of a smooth function is smooth on its open domain. -/
theorem smoothDc_contDiffOn {h : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) :
    ContDiffOn ℝ ∞ (smoothDc h) U := by
  apply (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ComplexModel n) (F := ℝ)
    (0 : Fin 1)).contDiff.comp_contDiffOn
  exact ((hh.fderiv_of_isOpen hU (by simp)).clm_comp
    contDiffOn_const).const_smul (-1 / (4 * Real.pi) : ℝ)

@[simp] theorem smoothDc_zero (z : ComplexModel n) :
    smoothDc (fun _ : ComplexModel n => (0 : ℝ)) z = 0 := by
  ext v
  simp [smoothDc_apply]

/-- Additivity is asserted at points where both functions are differentiable. -/
theorem smoothDc_add {h g : ComplexModel n → ℝ} {z : ComplexModel n}
    (hh : DifferentiableAt ℝ h z) (hg : DifferentiableAt ℝ g z) :
    smoothDc (fun y => h y + g y) z = smoothDc h z + smoothDc g z := by
  change smoothDc (h + g) z = _
  ext v
  simp [smoothDc_apply, fderiv_add hh hg, mul_add]

theorem smoothDc_smul {h : ComplexModel n → ℝ} {z : ComplexModel n}
    (hh : DifferentiableAt ℝ h z) (c : ℝ) :
    smoothDc (fun y => c • h y) z = c • smoothDc h z := by
  ext v
  rw [smoothDc_apply, fderiv_fun_const_smul hh c]
  simp only [smul_apply, ContinuousAlternatingMap.smul_apply,
    smoothDc_apply, smul_eq_mul]
  ring

theorem smoothDc_neg {h : ComplexModel n → ℝ} {z : ComplexModel n}
    (hh : DifferentiableAt ℝ h z) :
    smoothDc (fun y => -h y) z = -smoothDc h z := by
  have heq := smoothDc_smul hh (-1)
  have hfun : (fun y => (-1 : ℝ) • h y) = (fun y => -h y) := by
    funext y
    exact neg_one_mul _
  rw [hfun] at heq
  apply heq.trans
  ext v
  exact neg_one_mul _

@[simp] theorem smoothDDC_zero (z : ComplexModel n) :
    smoothDDC (fun _ : ComplexModel n => (0 : ℝ)) z = 0 := by
  have hzero : smoothDc (fun _ : ComplexModel n => (0 : ℝ)) = 0 := by
    funext y
    exact smoothDc_zero y
  simp only [smoothDDC, hzero, extDeriv, fderiv_zero, Pi.zero_apply]
  exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)

/-- Open-domain linearity uses equality of smooth germs, not arbitrary extensions. -/
theorem smoothDDC_add {h g : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) (hg : ContDiffOn ℝ ∞ g U)
    {z : ComplexModel n} (hz : z ∈ U) :
    smoothDDC (fun y => h y + g y) z = smoothDDC h z + smoothDDC g z := by
  have heq : smoothDc (fun y => h y + g y) =ᶠ[𝓝 z] smoothDc h + smoothDc g := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact smoothDc_add ((hh y hy).contDiffAt (hU.mem_nhds hy) |>.differentiableAt (by simp))
      ((hg y hy).contDiffAt (hU.mem_nhds hy) |>.differentiableAt (by simp))
  exact heq.extDeriv_eq.trans (extDeriv_add
    (((smoothDc_contDiffOn hU hh) z hz).contDiffAt (hU.mem_nhds hz)
      |>.differentiableAt (by simp))
    (((smoothDc_contDiffOn hU hg) z hz).contDiffAt (hU.mem_nhds hz)
      |>.differentiableAt (by simp)))

theorem smoothDDC_smul {h : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) (c : ℝ)
    {z : ComplexModel n} (hz : z ∈ U) :
    smoothDDC (fun y => c • h y) z = c • smoothDDC h z := by
  have heq : smoothDc (fun y => c • h y) =ᶠ[𝓝 z] c • smoothDc h := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact smoothDc_smul
      ((hh y hy).contDiffAt (hU.mem_nhds hy) |>.differentiableAt (by simp)) c
  exact heq.extDeriv_eq.trans (extDeriv_smul c (smoothDc h))

theorem smoothDDC_neg {h : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) {z : ComplexModel n} (hz : z ∈ U) :
    smoothDDC (fun y => -h y) z = -smoothDDC h z := by
  have heq := smoothDDC_smul hU hh (-1) hz
  have hfun : (fun y => (-1 : ℝ) • h y) = (fun y => -h y) := by
    funext y
    exact neg_one_mul _
  rw [hfun] at heq
  apply heq.trans
  ext v
  exact neg_one_mul _

/-- Genuine smooth closed real `(1,1)`-forms, with their existing overlap law. -/
def ClosedRealOneOneForm (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] :=
  {a : SmoothRealForm n M 2 // a.IsClosed ∧ a.IsTypeOneOne}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

namespace ClosedRealOneOneForm

@[ext] theorem ext {a b : ClosedRealOneOneForm n M}
    (h : ∀ e z, a.val.coeff e z = b.val.coeff e z) : a = b := by
  rcases a with ⟨⟨ac, as, ap⟩, ha⟩
  rcases b with ⟨⟨bc, bs, bp⟩, hb⟩
  have hc : ac = bc := funext fun e => funext fun z => h e z
  cases hc
  rfl

instance instZero : Zero (ClosedRealOneOneForm n M) where
  zero := by
    refine ⟨SmoothRealForm.zero, ?_, ?_⟩
    · intro e z hz
      change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)
        (fderiv ℝ (fun _ : ComplexModel n =>
          (0 : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)) z) = 0
      rw [fderiv_const_apply, map_zero]
    · intro e z hz u v
      rfl

instance instAdd : Add (ClosedRealOneOneForm n M) where
  add a b := by
    refine ⟨{
      coeff := fun e z => a.val.coeff e z + b.val.coeff e z
      smooth := fun e => (a.val.smooth e).add (b.val.smooth e)
      compatible := ?_ }, ?_, ?_⟩
    · intro e f z hz v
      exact congrArg₂ (· + ·) (a.val.compatible e f z hz v) (b.val.compatible e f z hz v)
    · intro e z hz
      change extDeriv (fun y => a.val.coeff e y + b.val.coeff e y) z = 0
      rw [extDeriv_fun_add
        (((a.val.smooth e) z hz).contDiffAt (e.val.open_target.mem_nhds hz)
          |>.differentiableAt (by simp))
        (((b.val.smooth e) z hz).contDiffAt (e.val.open_target.mem_nhds hz)
          |>.differentiableAt (by simp)), a.property.1 e z hz, b.property.1 e z hz, add_zero]
    · intro e z hz u v
      exact congrArg₂ (· + ·) (a.property.2 e z hz u v) (b.property.2 e z hz u v)

instance instSMul : SMul ℝ (ClosedRealOneOneForm n M) where
  smul c a := by
    refine ⟨{
      coeff := fun e z => c • a.val.coeff e z
      smooth := fun e => (a.val.smooth e).const_smul c
      compatible := ?_ }, ?_, ?_⟩
    · intro e f z hz v
      exact congrArg (c • ·) (a.val.compatible e f z hz v)
    · intro e z hz
      change extDeriv (c • a.val.coeff e) z = 0
      rw [extDeriv_smul, a.property.1 e z hz, smul_zero]
    · intro e z hz u v
      exact congrArg (c • ·) (a.property.2 e z hz u v)

instance instNeg : Neg (ClosedRealOneOneForm n M) := ⟨fun a => (-1 : ℝ) • a⟩

@[simp] theorem coeff_zero (e : ComplexChart n M) (z : ComplexModel n) :
    (0 : ClosedRealOneOneForm n M).val.coeff e z = 0 := rfl

@[simp] theorem coeff_add (a b : ClosedRealOneOneForm n M) (e : ComplexChart n M)
    (z : ComplexModel n) : (a + b).val.coeff e z = a.val.coeff e z + b.val.coeff e z := rfl

@[simp] theorem coeff_smul (c : ℝ) (a : ClosedRealOneOneForm n M) (e : ComplexChart n M)
    (z : ComplexModel n) : (c • a).val.coeff e z = c • a.val.coeff e z := rfl

@[simp] theorem coeff_neg (a : ClosedRealOneOneForm n M) (e : ComplexChart n M)
    (z : ComplexModel n) : (-a).val.coeff e z = -a.val.coeff e z := by
  ext v
  exact neg_one_mul _

instance instAddCommGroup : AddCommGroup (ClosedRealOneOneForm n M) where
  add_assoc a b c := ext fun e z => add_assoc _ _ _
  zero_add a := ext fun e z => zero_add _
  add_zero a := ext fun e z => add_zero _
  add_comm a b := ext fun e z => add_comm _ _
  neg_add_cancel a := by
    apply ext
    intro e z
    rw [coeff_add, coeff_neg, coeff_zero, neg_add_cancel]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instModule : Module ℝ (ClosedRealOneOneForm n M) where
  one_smul _ := ext fun _ _ => one_smul ℝ _
  mul_smul c d _ := ext fun _ _ => mul_smul c d _
  smul_zero c := ext fun _ _ => smul_zero c
  smul_add c _ _ := ext fun _ _ => smul_add c _ _
  add_smul c d _ := ext fun _ _ => add_smul c d _
  zero_smul _ := ext fun _ _ => zero_smul ℝ _

end ClosedRealOneOneForm

end

end SGPT.Foundations.Analysis.FirstPass
