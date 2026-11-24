/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentials

/-!
# Real Bott–Chern classes of smooth closed `(1,1)`-forms

The representatives are genuine compatible smooth forms. The equivalence relation
uses a globally chart-smooth real function and the actual normalized `smoothDDC`
on open chart targets. No closedness or overlap theorem for an arbitrary `ddC`
is imposed as extra data. Equality ignores all off-target coefficient extensions.

Representative operations descend to a real module. Bundled global smooth `ddC`,
existence of local potentials, and comparison with current classes remain separate
problems; no finite-dimensionality or positivity comparison is asserted here.
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

/-- The difference is the actual `ddᶜ` of a globally smooth real function,
tested only on open chart targets. No bundled global `ddᶜ` is assumed. -/
def BottChernRel (a b : ClosedRealOneOneForm n M) : Prop :=
  ∃ h : M → ℝ, ChartSmooth (n := n) h ∧
    ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      b.val.coeff e z = a.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z

theorem BottChernRel.refl (a : ClosedRealOneOneForm n M) : BottChernRel a a := by
  refine ⟨fun _ => 0, fun _ => contDiffOn_const, ?_⟩
  intro e z hz
  rw [smoothDDC_zero, add_zero]

theorem BottChernRel.symm {a b : ClosedRealOneOneForm n M}
    (hab : BottChernRel a b) : BottChernRel b a := by
  obtain ⟨h, hh, heq⟩ := hab
  refine ⟨fun x => -h x, fun e => (hh e).neg, ?_⟩
  intro e z hz
  rw [smoothDDC_neg e.val.open_target (hh e) hz, heq e z hz, add_neg_cancel_right]

theorem BottChernRel.trans {a b c : ClosedRealOneOneForm n M}
    (hab : BottChernRel a b) (hbc : BottChernRel b c) : BottChernRel a c := by
  obtain ⟨h, hh, heq⟩ := hab
  obtain ⟨g, hg, geq⟩ := hbc
  refine ⟨fun x => h x + g x, fun e => (hh e).add (hg e), ?_⟩
  intro e z hz
  rw [smoothDDC_add e.val.open_target (hh e) (hg e) hz, geq e z hz, heq e z hz,
    add_assoc]

/-- Geometric equality is included, using the zero potential. -/
theorem bottChernRel_of_geometricallyEq {a b : ClosedRealOneOneForm n M}
    (hab : a.val.GeometricallyEq b.val) : BottChernRel a b := by
  refine ⟨fun _ => 0, fun _ => contDiffOn_const, ?_⟩
  intro e z hz
  rw [smoothDDC_zero, add_zero]
  exact (hab e hz).symm

theorem bottChernRel_geometricallyEq_iff {a a' b b' : ClosedRealOneOneForm n M}
    (haa : a.val.GeometricallyEq a'.val) (hbb : b.val.GeometricallyEq b'.val) :
    BottChernRel a b ↔ BottChernRel a' b' := by
  have ha := bottChernRel_of_geometricallyEq haa
  have hb := bottChernRel_of_geometricallyEq hbb
  exact ⟨fun h => ha.symm.trans (h.trans hb), fun h => ha.trans (h.trans hb.symm)⟩

theorem BottChernRel.add {a b c d : ClosedRealOneOneForm n M}
    (hab : BottChernRel a b) (hcd : BottChernRel c d) : BottChernRel (a + c) (b + d) := by
  obtain ⟨h, hh, heq⟩ := hab
  obtain ⟨g, hg, geq⟩ := hcd
  refine ⟨fun x => h x + g x, fun e => (hh e).add (hg e), ?_⟩
  intro e z hz
  rw [coeff_add, coeff_add, smoothDDC_add e.val.open_target (hh e) (hg e) hz,
    heq e z hz, geq e z hz]
  abel

theorem BottChernRel.smul {a b : ClosedRealOneOneForm n M}
    (hab : BottChernRel a b) (c : ℝ) : BottChernRel (c • a) (c • b) := by
  obtain ⟨h, hh, heq⟩ := hab
  refine ⟨fun x => c • h x, fun e => (hh e).const_smul c, ?_⟩
  intro e z hz
  rw [coeff_smul, coeff_smul, smoothDDC_smul e.val.open_target (hh e) c hz,
    heq e z hz, smul_add]

theorem BottChernRel.neg {a b : ClosedRealOneOneForm n M}
    (hab : BottChernRel a b) : BottChernRel (-a) (-b) := hab.smul (-1)

/-- The explicit equivalence relation on closed smooth real `(1,1)`-forms. -/
def bottChernSetoid : Setoid (ClosedRealOneOneForm n M) where
  r := BottChernRel
  iseqv := ⟨BottChernRel.refl, BottChernRel.symm, BottChernRel.trans⟩

end ClosedRealOneOneForm

/-- Real Bott–Chern `(1,1)` classes, without a finite-dimensionality assertion. -/
def RealBottChern (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] :=
  Quotient (ClosedRealOneOneForm.bottChernSetoid (n := n) (M := M))

namespace RealBottChern

/-- The Bott–Chern class of a closed real `(1,1)`-form. -/
def ofRepresentative (a : ClosedRealOneOneForm n M) : RealBottChern n M :=
  Quotient.mk _ a

/-- Class equality is exactly existence of a globally chart-smooth `ddᶜ` difference. -/
theorem ofRepresentative_eq_iff (a b : ClosedRealOneOneForm n M) :
    ofRepresentative a = ofRepresentative b ↔ ClosedRealOneOneForm.BottChernRel a b :=
  Quotient.eq

theorem ofRepresentative_eq_of_geometricallyEq {a b : ClosedRealOneOneForm n M}
    (hab : a.val.GeometricallyEq b.val) : ofRepresentative a = ofRepresentative b :=
  (ofRepresentative_eq_iff a b).mpr
    (ClosedRealOneOneForm.bottChernRel_of_geometricallyEq hab)

instance instZero : Zero (RealBottChern n M) := ⟨ofRepresentative 0⟩

instance instAdd : Add (RealBottChern n M) where
  add a b := Quotient.liftOn₂' a b (fun a b => ofRepresentative (a + b))
    (fun _ _ _ _ hab hcd => Quotient.sound (ClosedRealOneOneForm.BottChernRel.add hab hcd))

instance instSMul : SMul ℝ (RealBottChern n M) where
  smul c a := Quotient.liftOn a (fun a => ofRepresentative (c • a))
    (fun _ _ hab => Quotient.sound (ClosedRealOneOneForm.BottChernRel.smul hab c))

instance instNeg : Neg (RealBottChern n M) where
  neg a := Quotient.liftOn a (fun a => ofRepresentative (-a))
    (fun _ _ hab => Quotient.sound (ClosedRealOneOneForm.BottChernRel.neg hab))

@[simp] theorem ofRepresentative_zero :
    ofRepresentative (0 : ClosedRealOneOneForm n M) = 0 := rfl

@[simp] theorem ofRepresentative_add (a b : ClosedRealOneOneForm n M) :
    ofRepresentative (a + b) = ofRepresentative a + ofRepresentative b := rfl

@[simp] theorem ofRepresentative_smul (c : ℝ) (a : ClosedRealOneOneForm n M) :
    ofRepresentative (c • a) = c • ofRepresentative a := rfl

@[simp] theorem ofRepresentative_neg (a : ClosedRealOneOneForm n M) :
    ofRepresentative (-a) = -ofRepresentative a := rfl

instance instAddCommGroup : AddCommGroup (RealBottChern n M) where
  add_assoc a b c := Quotient.inductionOn₃ a b c fun a b c =>
    congrArg ofRepresentative (add_assoc a b c)
  zero_add a := Quotient.inductionOn a fun a => congrArg ofRepresentative (zero_add a)
  add_zero a := Quotient.inductionOn a fun a => congrArg ofRepresentative (add_zero a)
  add_comm a b := Quotient.inductionOn₂ a b fun a b => congrArg ofRepresentative (add_comm a b)
  neg_add_cancel a := Quotient.inductionOn a fun a =>
    congrArg ofRepresentative (neg_add_cancel a)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instModule : Module ℝ (RealBottChern n M) where
  one_smul a := Quotient.inductionOn a fun a => congrArg ofRepresentative (one_smul ℝ a)
  mul_smul c d a := Quotient.inductionOn a fun a => congrArg ofRepresentative (mul_smul c d a)
  smul_zero c := congrArg ofRepresentative (smul_zero c)
  smul_add c a b := Quotient.inductionOn₂ a b fun a b =>
    congrArg ofRepresentative (smul_add c a b)
  add_smul c d a := Quotient.inductionOn a fun a => congrArg ofRepresentative (add_smul c d a)
  zero_smul a := Quotient.inductionOn a fun a => congrArg ofRepresentative (zero_smul ℝ a)

/-- The class map is linear for the actual representative and quotient operations. -/
def ofRepresentativeLinearMap : ClosedRealOneOneForm n M →ₗ[ℝ] RealBottChern n M where
  toFun := ofRepresentative
  map_add' := ofRepresentative_add
  map_smul' := ofRepresentative_smul

end RealBottChern

end

end SGPT.Foundations.Analysis.FirstPass
