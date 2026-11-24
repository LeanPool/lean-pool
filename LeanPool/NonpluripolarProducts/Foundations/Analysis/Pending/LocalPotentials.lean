/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalDDbar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalPotentials

/-!
# The local dd-bar lemma and its smooth positivity consequences

Local existence for an actual smooth closed real `(1,1)` form is
`exists_smooth_local_ddc_potential_of_ne_zero` (Poincaré plus Dolbeault).
Global local-potential existence, the closed-background smooth theta-PSH
criterion, and enlargement by a semipositive background are proof
compositions.

No positive-current comparison or global extension of a local potential is
asserted. The entire alternating two-form is represented on a smaller open set.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalPotentials

open FirstPass

noncomputable section

/-- In complex dimension zero every alternating two-form vanishes, so the
constant zero function is already a normalized local potential. -/
private theorem exists_smooth_local_ddc_potential_zero_dim
    {U : Set (ComplexModel 0)} (hU : IsOpen U)
    (a : ComplexModel 0 → (ComplexModel 0) [⋀^Fin 2]→L[ℝ] ℝ)
    {z : ComplexModel 0} (hz : z ∈ U) :
    ∃ (W : Set (ComplexModel 0)) (ρ : ComplexModel 0 → ℝ), z ∈ W ∧ IsOpen W ∧ W ⊆ U ∧
      ContDiffOn ℝ ∞ ρ W ∧ EqOn (smoothDDC ρ) a W := by
  refine ⟨U, fun _ ↦ 0, hz, hU, Subset.rfl, contDiffOn_const, ?_⟩
  intro y _
  rw [smoothDDC_zero]
  ext v
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  simp

/-- Smooth local dd-bar lemma in the concrete complex model, with the
manuscript normalization. The potential is smooth only on `W`. -/
theorem exists_smooth_local_ddc_potential
    {n : ℕ} {U : Set (ComplexModel n)} (hU : IsOpen U)
    (a : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : ContDiffOn ℝ ∞ a U)
    (hclosed : ∀ z ∈ U, extDeriv a z = 0)
    (h11 : ∀ z ∈ U, IsOneOne (a z))
    {z : ComplexModel n} (hz : z ∈ U) :
    ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ), z ∈ W ∧ IsOpen W ∧ W ⊆ U ∧
      ContDiffOn ℝ ∞ ρ W ∧ EqOn (smoothDDC ρ) a W := by
  by_cases hn : n = 0
  · subst n
    exact exists_smooth_local_ddc_potential_zero_dim hU a hz
  · obtain ⟨W, ρ, hzW, hW, hWU, hρ, heq⟩ :=
      exists_smooth_local_ddc_potential_of_ne_zero hn hU a ha hclosed h11 hz
    exact ⟨W, ρ, hzW, hW, hWU, hρ.contDiffOn, heq⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem hasSmoothLocalPotentials_of_closed_typeOneOne (θ : SmoothRealForm n M 2)
    (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne) : HasSmoothLocalPotentials θ := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hW, hWe, hρ, heq⟩ := exists_smooth_local_ddc_potential
    e.val.open_target (θ.coeff e) (θ.smooth e) (hclosed e) (h11 e) hz
  exact ⟨W, ρ, hzW, hW, hWe, hρ, heq⟩

theorem closedRealOneOne_hasLocalPotentials (a : ClosedRealOneOneForm n M) :
    HasSmoothLocalPotentials a.val :=
  hasSmoothLocalPotentials_of_closed_typeOneOne a.val a.property.1 a.property.2

/-- The local-potential hypothesis in the old smooth criterion is now derived
from actual closedness and type `(1,1)`, rather than passed as extra data. -/
theorem thetaPlurisubharmonic_smooth_iff (a : ClosedRealOneOneForm n M)
    (u : M → ℝ) (hu : ChartSmooth (n := n) u) :
    ThetaPlurisubharmonic a.val (fun x => (u x : EReal)) ↔
      ∀ (e : ComplexChart n M) z, z ∈ e.val.target → ∀ v : ComplexModel n,
        0 ≤ a.val.coeff e z ![v, Complex.I • v] +
          smoothDDC (fun y => u (e.val.symm y)) z ![v, Complex.I • v] :=
  SGPT.Foundations.Analysis.Pending.thetaPlurisubharmonic_smooth_iff a.val
    (closedRealOneOne_hasLocalPotentials a) u hu

theorem thetaPlurisubharmonic_zero_iff (a : ClosedRealOneOneForm n M) :
    ThetaPlurisubharmonic a.val (fun _ => 0) ↔ a.val.IsSemipositive := by
  simpa [SmoothRealForm.IsSemipositive] using
    thetaPlurisubharmonic_smooth_iff a (fun _ => 0) (fun _ => contDiffOn_const)

theorem isThetaPshPotential_zero_iff (a : ClosedRealOneOneForm n M) :
    IsThetaPshPotential a.val (fun _ => 0) ↔ a.val.IsSemipositive := by
  constructor
  · intro h
    exact (thetaPlurisubharmonic_zero_iff a).mp h.1
  · intro h
    refine ⟨(thetaPlurisubharmonic_zero_iff a).mpr h, ?_⟩
    intro x U hU hx
    exact ⟨x, hx, EReal.coe_ne_bot 0⟩

theorem thetaPlurisubharmonic_add_of_semipositive {a b : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : ThetaPlurisubharmonic a.val u)
    (hb : b.val.IsSemipositive) : ThetaPlurisubharmonic (a + b).val u :=
  FirstPass.LocalPotentials.thetaPlurisubharmonic_add_of_zero hu
    ((thetaPlurisubharmonic_zero_iff b).mpr hb)

theorem isThetaPshPotential_add_of_semipositive {a b : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : IsThetaPshPotential a.val u)
    (hb : b.val.IsSemipositive) : IsThetaPshPotential (a + b).val u :=
  FirstPass.LocalPotentials.isThetaPshPotential_add_of_zero hu
    ((thetaPlurisubharmonic_zero_iff b).mpr hb)

end

end SGPT.Foundations.Analysis.Pending.LocalPotentials
