/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.BottChern

/-!
# Positivity predicates on real Bott–Chern classes

Nefness is the smooth epsilon-test on actual complex tangent lines, relative to
an explicitly supplied Kähler form. Pseudoeffectivity and bigness here are named
`ViaPotentials`: they use the existing, locally nondegenerate theta-PSH predicate.
Their identification with the full cones of positive currents is not asserted.

All comparisons take place on chart targets, with `ddC = i/(2π) ∂∂bar`.
There is no order on off-target coefficient extensions and no implicit existence
of a Kähler background or of local potentials for arbitrary closed forms.
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

/-- Every positive error admits a globally smooth correction whose actual
two-form is nonnegative on all complex lines in all chart targets. -/
def NefWithRespectTo (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ h : M → ℝ, ChartSmooth (n := n) h ∧
    ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      CoefficientSemipositive
        (θ.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z + ε • omega.form.val.coeff e z)

/-- Potential-based pseudoeffectivity. Comparison with all positive currents
in the class remains a separate theorem. -/
def PseudoeffectiveViaPotentials (θ : ClosedRealOneOneForm n M) : Prop :=
  ∃ u : M → EReal, IsThetaPshPotential θ.val u

/-- Potential-based bigness relative to a supplied Kähler background.
No equivalence with the full Kähler-current cone is asserted here. -/
def BigWithRespectToViaPotentials (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ u : M → EReal, IsThetaPshPotential (θ - ε • omega.form).val u

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

/-- A smooth test for `θ` becomes the test `h-f` for `η = θ + ddC f`. -/
theorem nefWithRespectTo_of_bottChernRel {θ η : ClosedRealOneOneForm n M}
    (omega : KahlerBackground n M) (hθη : BottChernRel θ η)
    (hθ : NefWithRespectTo omega θ) : NefWithRespectTo omega η := by
  obtain ⟨f, hf, heq⟩ := hθη
  intro ε hε
  obtain ⟨h, hh, hpos⟩ := hθ ε hε
  refine ⟨fun x => h x - f x, fun e => (hh e).sub (hf e), ?_⟩
  intro e z hz
  rw [heq e z hz, smoothDDC_sub e.val.open_target (hh e) (hf e) hz]
  convert hpos e z hz using 1
  congr 1
  abel

theorem nefWithRespectTo_bottChernRel_iff {θ η : ClosedRealOneOneForm n M}
    (omega : KahlerBackground n M) (hθη : BottChernRel θ η) :
    NefWithRespectTo omega θ ↔ NefWithRespectTo omega η :=
  ⟨nefWithRespectTo_of_bottChernRel omega hθη,
    nefWithRespectTo_of_bottChernRel omega hθη.symm⟩

theorem pseudoeffectiveViaPotentials_of_bottChernRel {θ η : ClosedRealOneOneForm n M}
    (hθη : BottChernRel θ η) (hθ : PseudoeffectiveViaPotentials θ) :
    PseudoeffectiveViaPotentials η := by
  obtain ⟨f, hf, heq⟩ := hθη
  obtain ⟨u, hu⟩ := hθ
  exact ⟨fun x => u x - (f x : EReal), thetaPshPotential_sub_smooth hf heq hu⟩

theorem pseudoeffectiveViaPotentials_bottChernRel_iff {θ η : ClosedRealOneOneForm n M}
    (hθη : BottChernRel θ η) :
    PseudoeffectiveViaPotentials θ ↔ PseudoeffectiveViaPotentials η :=
  ⟨pseudoeffectiveViaPotentials_of_bottChernRel hθη,
    pseudoeffectiveViaPotentials_of_bottChernRel hθη.symm⟩

theorem bigWithRespectToViaPotentials_of_bottChernRel {θ η : ClosedRealOneOneForm n M}
    (omega : KahlerBackground n M) (hθη : BottChernRel θ η)
    (hθ : BigWithRespectToViaPotentials omega θ) : BigWithRespectToViaPotentials omega η := by
  obtain ⟨ε, hε, hu⟩ := hθ
  have hrel : BottChernRel (θ - ε • omega.form) (η - ε • omega.form) := by
    simpa only [sub_eq_add_neg] using hθη.add (BottChernRel.refl (-(ε • omega.form)))
  exact ⟨ε, hε, pseudoeffectiveViaPotentials_of_bottChernRel hrel hu⟩

theorem bigWithRespectToViaPotentials_bottChernRel_iff {θ η : ClosedRealOneOneForm n M}
    (omega : KahlerBackground n M) (hθη : BottChernRel θ η) :
    BigWithRespectToViaPotentials omega θ ↔ BigWithRespectToViaPotentials omega η :=
  ⟨bigWithRespectToViaPotentials_of_bottChernRel omega hθη,
    bigWithRespectToViaPotentials_of_bottChernRel omega hθη.symm⟩

/-- Nefness descends to the actual real Bott–Chern quotient. -/
def ClassNefWithRespectTo (omega : KahlerBackground n M) (α : RealBottChern n M) : Prop :=
  Quotient.lift (s := bottChernSetoid) (NefWithRespectTo omega)
    (fun _ _ h => propext (nefWithRespectTo_bottChernRel_iff omega h)) α

/-- Potential-based pseudoeffectivity on the actual quotient. -/
def ClassPseudoeffectiveViaPotentials (α : RealBottChern n M) : Prop :=
  Quotient.lift (s := bottChernSetoid) PseudoeffectiveViaPotentials
    (fun _ _ h => propext (pseudoeffectiveViaPotentials_bottChernRel_iff h)) α

/-- Potential-based bigness on the actual quotient, with the same background. -/
def ClassBigWithRespectToViaPotentials (omega : KahlerBackground n M)
    (α : RealBottChern n M) : Prop :=
  Quotient.lift (s := bottChernSetoid) (BigWithRespectToViaPotentials omega)
    (fun _ _ h => propext (bigWithRespectToViaPotentials_bottChernRel_iff omega h)) α

@[simp] theorem classNefWithRespectTo_ofRepresentative (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) :
    ClassNefWithRespectTo omega (RealBottChern.ofRepresentative θ) ↔ NefWithRespectTo omega θ :=
      Iff.rfl

@[simp] theorem classPseudoeffectiveViaPotentials_ofRepresentative
    (θ : ClosedRealOneOneForm n M) :
    ClassPseudoeffectiveViaPotentials (RealBottChern.ofRepresentative θ) ↔
      PseudoeffectiveViaPotentials θ := Iff.rfl

@[simp] theorem classBigWithRespectToViaPotentials_ofRepresentative (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) :
    ClassBigWithRespectToViaPotentials omega (RealBottChern.ofRepresentative θ) ↔
      BigWithRespectToViaPotentials omega θ := Iff.rfl

/-- The zero correction proves nefness for a semipositive representative. -/
theorem nefWithRespectTo_of_semipositive (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} (hθ : θ.val.IsSemipositive) :
    NefWithRespectTo omega θ := by
  intro ε hε
  refine ⟨fun _ => 0, fun _ => contDiffOn_const, ?_⟩
  intro e z hz
  rw [smoothDDC_zero, add_zero]
  exact coefficientSemipositive_add (hθ e z hz)
    (coefficientSemipositive_smul hε.le (omega.isSemipositive e z hz))

theorem nefWithRespectTo_zero (omega : KahlerBackground n M) :
    NefWithRespectTo omega 0 :=
  nefWithRespectTo_of_semipositive omega (fun _ _ _ => coefficientSemipositive_zero)

/-- Split the error evenly between the two smooth tests. -/
theorem nefWithRespectTo_add (omega : KahlerBackground n M)
    {θ η : ClosedRealOneOneForm n M}
    (hθ : NefWithRespectTo omega θ) (hη : NefWithRespectTo omega η) :
    NefWithRespectTo omega (θ + η) := by
  intro ε hε
  obtain ⟨h, hh, hpos⟩ := hθ (ε / 2) (half_pos hε)
  obtain ⟨k, hk, kpos⟩ := hη (ε / 2) (half_pos hε)
  refine ⟨fun x => h x + k x, fun e => (hh e).add (hk e), ?_⟩
  intro e z hz v
  rw [coeff_add, smoothDDC_add e.val.open_target (hh e) (hk e) hz]
  have hsum := add_nonneg (hpos e z hz v) (kpos e z hz v)
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at hsum ⊢
  linarith

/-- For a positive scalar use error `ε/c`; zero is handled separately. -/
theorem nefWithRespectTo_smul (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {c : ℝ}
    (hc : 0 ≤ c) (hθ : NefWithRespectTo omega θ) :
    NefWithRespectTo omega (c • θ) := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · rw [← hc0, zero_smul]
    exact nefWithRespectTo_zero omega
  · intro ε hε
    obtain ⟨h, hh, hpos⟩ := hθ (ε / c) (div_pos hε hcpos)
    refine ⟨fun x => c • h x, fun e => (hh e).const_smul c, ?_⟩
    intro e z hz
    rw [coeff_smul, smoothDDC_smul e.val.open_target (hh e) c hz]
    have heps : c * (ε / c) = ε := by field_simp
    have hscaled := coefficientSemipositive_smul hc (hpos e z hz)
    simpa only [smul_add, smul_smul, heps] using hscaled

theorem classNefWithRespectTo_of_semipositive (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} (hθ : θ.val.IsSemipositive) :
    ClassNefWithRespectTo omega (RealBottChern.ofRepresentative θ) :=
  nefWithRespectTo_of_semipositive omega hθ

theorem classNefWithRespectTo_zero (omega : KahlerBackground n M) :
    ClassNefWithRespectTo omega (0 : RealBottChern n M) := nefWithRespectTo_zero omega

theorem classNefWithRespectTo_add (omega : KahlerBackground n M)
    {α β : RealBottChern n M}
    (hα : ClassNefWithRespectTo omega α) (hβ : ClassNefWithRespectTo omega β) :
    ClassNefWithRespectTo omega (α + β) := by
  revert hα hβ
  refine Quotient.inductionOn₂ α β ?_
  intro θ η hθ hη
  exact nefWithRespectTo_add omega hθ hη

theorem classNefWithRespectTo_smul (omega : KahlerBackground n M)
    {α : RealBottChern n M} {c : ℝ} (hc : 0 ≤ c)
    (hα : ClassNefWithRespectTo omega α) : ClassNefWithRespectTo omega (c • α) := by
  revert hα
  refine Quotient.inductionOn α ?_
  intro θ hθ
  exact nefWithRespectTo_smul omega hc hθ

end

end SGPT.Foundations.Analysis.FirstPass.PositiveClasses
