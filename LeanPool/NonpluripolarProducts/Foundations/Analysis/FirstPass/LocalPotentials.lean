/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ClosedRealOneOneForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshAddition

/-!
# Linear operations on genuine smooth local potentials

All equalities concern the complete alternating two-form on the stated open
chart neighborhood. Smoothness outside that neighborhood is never required.
These closure lemmas do not assert the local dd-bar lemma: existence for an
arbitrary closed real `(1,1)` form remains a separate Pending theorem.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace SGPT.Foundations.Analysis.FirstPass.LocalPotentials

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem localPotential_zero (e : ComplexChart n M) {W : Set (ComplexModel n)}
    (hW : IsOpen W) (hWe : W ⊆ e.val.target) :
    IsSmoothLocalPotential (0 : ClosedRealOneOneForm n M).val e W (fun _ => 0) := by
  refine ⟨hW, hWe, contDiffOn_const, ?_⟩
  intro z hz
  rw [smoothDDC_zero, ClosedRealOneOneForm.coeff_zero]

theorem localPotential_add {a b : ClosedRealOneOneForm n M} {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ σ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential a.val e W ρ)
    (hσ : IsSmoothLocalPotential b.val e W σ) :
    IsSmoothLocalPotential (a + b).val e W (fun z => ρ z + σ z) := by
  refine ⟨hρ.1, hρ.2.1, hρ.2.2.1.add hσ.2.2.1, ?_⟩
  intro z hz
  rw [smoothDDC_add hρ.1 hρ.2.2.1 hσ.2.2.1 hz,
    hρ.2.2.2 hz, hσ.2.2.2 hz, ClosedRealOneOneForm.coeff_add]

theorem localPotential_smul {a : ClosedRealOneOneForm n M} {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential a.val e W ρ) (c : ℝ) :
    IsSmoothLocalPotential (c • a).val e W (fun z => c • ρ z) := by
  refine ⟨hρ.1, hρ.2.1, hρ.2.2.1.const_smul c, ?_⟩
  intro z hz
  rw [smoothDDC_smul hρ.1 hρ.2.2.1 c hz, hρ.2.2.2 hz,
    ClosedRealOneOneForm.coeff_smul]

theorem localPotential_neg {a : ClosedRealOneOneForm n M} {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential a.val e W ρ) :
    IsSmoothLocalPotential (-a).val e W (fun z => -ρ z) := by
  refine ⟨hρ.1, hρ.2.1, hρ.2.2.1.neg, ?_⟩
  intro z hz
  rw [smoothDDC_neg hρ.1 hρ.2.2.1 hz, hρ.2.2.2 hz,
    ClosedRealOneOneForm.coeff_neg]

theorem localPotential_sub {a b : ClosedRealOneOneForm n M} {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ σ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential a.val e W ρ)
    (hσ : IsSmoothLocalPotential b.val e W σ) :
    IsSmoothLocalPotential (a - b).val e W (fun z => ρ z - σ z) := by
  simpa only [sub_eq_add_neg] using localPotential_add hρ (localPotential_neg hσ)

theorem hasLocalPotentials_zero :
    HasSmoothLocalPotentials (0 : ClosedRealOneOneForm n M).val := by
  intro e z hz
  exact ⟨e.val.target, fun _ => 0, hz, localPotential_zero e e.val.open_target Subset.rfl⟩

theorem hasLocalPotentials_add {a b : ClosedRealOneOneForm n M}
    (ha : HasSmoothLocalPotentials a.val) (hb : HasSmoothLocalPotentials b.val) :
    HasSmoothLocalPotentials (a + b).val := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ⟩ := ha e z hz
  obtain ⟨V, σ, hzV, hσ⟩ := hb e z hz
  have hWV : IsOpen (W ∩ V) := hρ.1.inter hσ.1
  exact ⟨W ∩ V, fun y => ρ y + σ y, ⟨hzW, hzV⟩,
    localPotential_add (hρ.mono hWV inter_subset_left) (hσ.mono hWV inter_subset_right)⟩

theorem hasLocalPotentials_smul {a : ClosedRealOneOneForm n M}
    (ha : HasSmoothLocalPotentials a.val) (c : ℝ) :
    HasSmoothLocalPotentials (c • a).val := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ⟩ := ha e z hz
  exact ⟨W, fun y => c • ρ y, hzW, localPotential_smul hρ c⟩

theorem hasLocalPotentials_neg {a : ClosedRealOneOneForm n M}
    (ha : HasSmoothLocalPotentials a.val) : HasSmoothLocalPotentials (-a).val := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ⟩ := ha e z hz
  exact ⟨W, fun y => -ρ y, hzW, localPotential_neg hρ⟩

theorem hasLocalPotentials_sub {a b : ClosedRealOneOneForm n M}
    (ha : HasSmoothLocalPotentials a.val) (hb : HasSmoothLocalPotentials b.val) :
    HasSmoothLocalPotentials (a - b).val := by
  simpa only [sub_eq_add_neg] using hasLocalPotentials_add ha (hasLocalPotentials_neg hb)

theorem hasLocalPotentials_geometricallyEq_iff {a b : SmoothRealForm n M 2}
    (hab : a.GeometricallyEq b) : HasSmoothLocalPotentials a ↔ HasSmoothLocalPotentials b := by
  constructor
  · intro ha e z hz
    obtain ⟨W, ρ, hzW, hρ⟩ := ha e z hz
    exact ⟨W, ρ, hzW, (hab.localPotential_iff e W ρ).mp hρ⟩
  · intro hb e z hz
    obtain ⟨W, ρ, hzW, hρ⟩ := hb e z hz
    exact ⟨W, ρ, hzW, (hab.localPotential_iff e W ρ).mpr hρ⟩

/-- Corrected PSH germs add on the intersection of their potential neighborhoods.
This is the raw criterion; no assertion about sums of pole sets is needed. -/
theorem thetaPlurisubharmonic_add {a b : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : ThetaPlurisubharmonic a.val u) (hv : ThetaPlurisubharmonic b.val v) :
    ThetaPlurisubharmonic (a + b).val (fun x => u x + v x) := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hu e z hz
  obtain ⟨V, σ, hzV, hσ, hq⟩ := hv e z hz
  have hWV : IsOpen (W ∩ V) := hρ.1.inter hσ.1
  refine ⟨W ∩ V, fun y => ρ y + σ y, ⟨hzW, hzV⟩,
    localPotential_add (hρ.mono hWV inter_subset_left) (hσ.mono hWV inter_subset_right), ?_⟩
  have hfun :
      (fun y => chartFunction (fun x => u x + v x) e y + ((ρ y + σ y : ℝ) : EReal)) =
      (fun y => (chartFunction u e y + (ρ y : EReal)) +
        (chartFunction v e y + (σ y : EReal))) := by
    funext y
    simp only [chartFunction, EReal.coe_add]
    ac_rfl
  rw [hfun]
  exact (hp.mono inter_subset_left).add (hq.mono inter_subset_right)

/-- A background admitting the zero PSH potential may be added without changing
the original potential, including its negative-infinite values. -/
theorem thetaPlurisubharmonic_add_of_zero {a b : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : ThetaPlurisubharmonic a.val u)
    (hb : ThetaPlurisubharmonic b.val (fun _ => 0)) :
    ThetaPlurisubharmonic (a + b).val u := by
  simpa only [add_zero] using thetaPlurisubharmonic_add hu hb

theorem isThetaPshPotential_add_of_zero {a b : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : IsThetaPshPotential a.val u)
    (hb : ThetaPlurisubharmonic b.val (fun _ => 0)) :
    IsThetaPshPotential (a + b).val u :=
  ⟨thetaPlurisubharmonic_add_of_zero hu.1 hb, hu.2⟩

end

end SGPT.Foundations.Analysis.FirstPass.LocalPotentials
