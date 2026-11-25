/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ClosedRealOneOneForms

/-!
# Kähler backgrounds and smooth potential changes

The background is a smooth closed real `(1,1)`-form that is positive on every complex tangent
line. Adding a smooth potential to the background and subtracting it from a theta-PSH
function preserves the corrected local expressions, including at poles.
-/

@[expose] public section

open Set
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass.PositiveClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

open ClosedRealOneOneForm

/-- A genuine background, supplied as data rather than assumed to exist. -/
structure KahlerBackground (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] where
  /-- The underlying smooth closed real `(1,1)`-form. -/
  form : ClosedRealOneOneForm n M
  isKahler : form.val.IsKahler

/-- Semipositivity of a two-form coefficient on every complex tangent line. -/
def CoefficientSemipositive (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) : Prop :=
  ∀ v : ComplexModel n, 0 ≤ a ![v, Complex.I • v]

theorem coefficientSemipositive_zero :
    CoefficientSemipositive (0 : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) := by
  intro v
  exact le_refl 0

theorem coefficientSemipositive_add
    {a b : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : CoefficientSemipositive a) (hb : CoefficientSemipositive b) :
    CoefficientSemipositive (a + b) := fun v => add_nonneg (ha v) (hb v)

theorem coefficientSemipositive_smul {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    {c : ℝ} (hc : 0 ≤ c) (ha : CoefficientSemipositive a) :
    CoefficientSemipositive (c • a) := fun v => mul_nonneg hc (ha v)

theorem KahlerBackground.isSemipositive (omega : KahlerBackground n M) :
    omega.form.val.IsSemipositive := by
  intro e z hz v
  by_cases hv : v = 0
  · subst v
    rw [(omega.form.val.coeff e z).map_coord_zero (0 : Fin 2) rfl]
  · exact (omega.isKahler.1 e z hz).2 v hv |>.le

/-- Subtraction linearity holds on the open set of smoothness. -/
theorem smoothDDC_sub {h f : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) (hf : ContDiffOn ℝ ∞ f U)
    {z : ComplexModel n} (hz : z ∈ U) :
    smoothDDC (fun y => h y - f y) z = smoothDDC h z - smoothDDC f z := by
  simp only [sub_eq_add_neg]
  rw [smoothDDC_add hU hh hf.neg hz, smoothDDC_neg hU hf hz]

/-- Cancellation of finite corrections is valid also at extended-real poles. -/
theorem sub_coe_add_coe (a : EReal) (r s : ℝ) :
    a - (r : EReal) + ((s + r : ℝ) : EReal) = a + (s : EReal) := by
  rw [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add]
  congr 2
  ring

/-- Adding the global smooth correction gives an actual local potential of
the changed representative, on the same coordinate neighborhood. -/
theorem isSmoothLocalPotential_add_chartSmooth {θ η : SmoothRealForm n M 2}
    {f : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hθη : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      η.coeff e z = θ.coeff e z + smoothDDC (fun y => f (e.val.symm y)) z)
    {e : ComplexChart n M} {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ) :
    IsSmoothLocalPotential η e W (fun y => ρ y + f (e.val.symm y)) := by
  refine ⟨hρ.1, hρ.2.1, hρ.2.2.1.add ((hf e).mono hρ.2.1), ?_⟩
  intro y hy
  rw [smoothDDC_add hρ.1 hρ.2.2.1 ((hf e).mono hρ.2.1) hy,
    hρ.2.2.2 hy, hθη e y (hρ.2.1 hy)]

/-- The raw theta-PSH predicate transforms without requiring a non-pole point
in every neighborhood. Finite real corrections cancel also at `-∞`. -/
theorem thetaPlurisubharmonic_sub_smooth {θ η : SmoothRealForm n M 2}
    {f : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hθη : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      η.coeff e z = θ.coeff e z + smoothDDC (fun y => f (e.val.symm y)) z)
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ u) :
    ThetaPlurisubharmonic η (fun x => u x - (f x : EReal)) := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hu e z hz
  refine ⟨W, fun y => ρ y + f (e.val.symm y), hzW,
    isSmoothLocalPotential_add_chartSmooth hf hθη hρ, ?_⟩
  have heq : (fun y => chartFunction (fun x => u x - (f x : EReal)) e y +
      ((ρ y + f (e.val.symm y) : ℝ) : EReal)) =
      (fun y => chartFunction u e y + (ρ y : EReal)) := by
    funext y
    exact sub_coe_add_coe _ _ _
  rw [heq]
  exact hp

/-- Under a smooth change of representative, subtract the same function from
the potential and add it to each local smooth potential. The corrected PSH
function is exactly unchanged, not merely equal away from poles. -/
theorem thetaPshPotential_sub_smooth {θ η : SmoothRealForm n M 2}
    {f : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hθη : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      η.coeff e z = θ.coeff e z + smoothDDC (fun y => f (e.val.symm y)) z)
    {u : M → EReal} (hu : IsThetaPshPotential θ u) :
    IsThetaPshPotential η (fun x => u x - (f x : EReal)) := by
  constructor
  · exact thetaPlurisubharmonic_sub_smooth hf hθη hu.1
  · intro x U hU hx
    obtain ⟨y, hy, hfin⟩ := hu.2 x U hU hx
    refine ⟨y, hy, ?_⟩
    change u y - (f y : EReal) ≠ ⊥
    rw [sub_eq_add_neg, ← EReal.coe_neg]
    exact EReal.add_ne_bot_iff.mpr ⟨hfin, EReal.coe_ne_bot _⟩

/-- Subtracting a finite constant preserves the same raw theta-PSH class. -/
theorem thetaPlurisubharmonic_sub_const {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) (c : ℝ) :
    ThetaPlurisubharmonic θ (fun x => u x - (c : EReal)) := by
  apply thetaPlurisubharmonic_sub_smooth (fun _ => contDiffOn_const) _ hu
  intro e z _
  rw [smoothDDC_const, add_zero]

end

end SGPT.Foundations.Analysis.FirstPass.PositiveClasses
