/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalInteriorUC
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityRegularity
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.LocalBox

/-!
# Vorticity charts and spatial propagation of vanishing

On a unit past cylinder where a suitable solution has bounded velocity,
`thm:vorticity-regularity` gives a regular vorticity representative.  Unique
continuation (`thm:uc`) applied at every top time near `t` then propagates
vanishing of the weak vorticity near `(x', t)` to a space-time neighborhood of
`(x, t)` whenever `x'` is close to `x`; this is the closedness step in the
proof of `thm:ess-local` (spatial unique continuation).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- An essential upper bound of a function continuous on an open parabolic set
holds at every point of that set. -/
theorem essLocal_le_of_ae_le_of_continuousOn {O : Set ParabolicPoint} (hO : IsOpen O)
    {f : ParabolicPoint → ℝ} (hf : ContinuousOn f O) {C : ℝ}
    (h : ∀ᵐ z ∂(volume.restrict O), f z ≤ C) : ∀ z ∈ O, f z ≤ C := by
  have : Measure.IsOpenPosMeasure (volume : Measure ParabolicPoint) :=
    ⟨fun U hU hne => by
      have ho : IsOpen (parabolicHomeomorph.symm ⁻¹' U) :=
        hU.preimage parabolicHomeomorph.symm.continuous
      have hn : (parabolicHomeomorph.symm ⁻¹' U).Nonempty := by
        obtain ⟨z, hz⟩ := hne
        exact ⟨parabolicHomeomorph z, hz⟩
      exact ho.measure_ne_zero (volume : Measure (Vec3 × ℝ)) hn⟩
  intro z hz
  by_contra hle
  have hlt : C < f z := lt_of_not_ge hle
  let W : Set ParabolicPoint := O ∩ f ⁻¹' Ioi C
  have hWopen : IsOpen W := hf.isOpen_inter_preimage hO isOpen_Ioi
  have hWae : ∀ᵐ y ∂(volume.restrict W), f y ≤ C :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left h
  have hW0 : (volume : Measure ParabolicPoint) W = 0 := by
    have hglob := (ae_restrict_iff' hWopen.measurableSet).1 hWae
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hglob] with y hy hyW
    exact not_le_of_gt hyW.2 (hy hyW)
  have hWempty := (hWopen.measure_eq_zero_iff (volume : Measure ParabolicPoint)).1 hW0
  have hzW : z ∈ W := ⟨hz, hlt⟩
  rw [hWempty] at hzW
  exact hzW

/-- A property holding almost everywhere near every point of a parabolic set
holds almost everywhere on that set. -/
theorem essLocal_ae_restrict_of_local {S : Set ParabolicPoint} (hS : MeasurableSet S)
    {P : ParabolicPoint → Prop}
    (h : ∀ z ∈ S, ∃ N : Set ParabolicPoint, IsOpen N ∧ z ∈ N ∧
      ∀ᵐ y ∂(volume.restrict N), P y) :
    ∀ᵐ y ∂(volume.restrict S), P y := by
  let B : Set ParabolicPoint := {y | ¬ P y}
  have hLind : IsLindelof S := HereditarilyLindelofSpace.isLindelof S
  have hcompl : Sᶜ ∈ ae ((volume : Measure ParabolicPoint).restrict B) := by
    refine hLind.compl_mem_sets_of_nhdsWithin fun z hz => ?_
    obtain ⟨N, hNopen, hzN, hNae⟩ := h z hz
    refine ⟨N, mem_nhdsWithin_of_mem_nhds (hNopen.mem_nhds hzN), ?_⟩
    rw [mem_ae_iff, compl_compl, Measure.restrict_apply hNopen.measurableSet]
    have h0 : (volume.restrict N) B = 0 := by
      rw [ae_iff] at hNae
      exact hNae
    rw [Measure.restrict_apply' hNopen.measurableSet] at h0
    rw [inter_comm]
    exact h0
  rw [ae_iff, Measure.restrict_apply' hS]
  rw [mem_ae_iff, compl_compl, Measure.restrict_apply hS] at hcompl
  rw [inter_comm]
  exact hcompl

/-- A Euclidean ball in Vec3 is convex. -/
theorem essLocal_convex_vec3Ball (c : Vec3) (r : ℝ) : Convex ℝ (vec3Ball c r) := by
  have hmem : ∀ y : Vec3, y ∈ vec3Ball c r ↔
      WithLp.toLp 2 y ∈ Metric.ball (WithLp.toLp 2 c) r := by
    intro y
    rw [mem_vec3Ball, Metric.mem_ball, dist_eq_norm, ← WithLp.toLp_sub,
      vec3EuclideanNorm_eq_l2]
  intro y₁ h₁ y₂ h₂ a b ha hb hab
  rw [hmem] at h₁ h₂ ⊢
  have hconv := convex_ball (WithLp.toLp 2 c) r h₁ h₂ ha hb hab
  simpa only [WithLp.toLp_add, WithLp.toLp_smul] using hconv

/-- `thm:vorticity-regularity` on a unit past cylinder of a suitable solution on
a spatially global slab, with the gradient energy bound supplied by
suitability. -/
theorem essLocal_vorticityChart
    {J : Set ℝ} {V : ParabolicPoint → Vec3} {DV : ParabolicPoint → Fin 3 → Vec3}
    {pv : ParabolicPoint → ℝ} (M : ℝ) (hM : 0 ≤ M)
    (hsws : IsSuitableWeakSolution Set.univ J 3 V DV pv (0 : ParabolicPoint → Vec3))
    (x : Vec3) (t₁ : ℝ)
    (hcl : closure (parabolicCylinder x t₁ 1) ⊆ spaceTimeSet Set.univ J)
    (hV : ∀ᵐ z ∂(volume.restrict (parabolicCylinder x t₁ 1)),
      vec3EuclideanNorm (V z) ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∃ (ω : ParabolicPoint → Vec3) (Dω : ParabolicPoint → Fin 3 → Vec3)
      (D2ω : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtω : ParabolicPoint → Vec3),
      ω =ᵐ[volume.restrict (parabolicCylinder x t₁ (1 / 2 : ℝ))] weakVorticity DV ∧
      ContinuousOn ω (closure (parabolicCylinder x t₁ (1 / 2 : ℝ))) ∧
      HasSpaceTimeWeakDerivs (vec3Ball x (1 / 2 : ℝ)) (Ioo (t₁ - (1 / 4 : ℝ)) t₁)
        ω Dω D2ω Dtω ∧
      (∫⁻ z in parabolicCylinder x t₁ (1 / 2 : ℝ),
        ‖ω z‖ₑ ^ (2 : ℝ) + ‖Dω z‖ₑ ^ (2 : ℝ) +
          ‖D2ω z‖ₑ ^ (2 : ℝ) + ‖Dtω z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
      (∀ᵐ z ∂(volume.restrict (parabolicCylinder x t₁ (1 / 2 : ℝ))),
        vec3EuclideanNorm (fun i => Dtω z i - ∑ j, D2ω z i j j) ≤
          C * (vec3EuclideanNorm (ω z) + Real.sqrt (spatialGradientSq ω Dω z))) ∧
      (∀ᵐ z ∂(volume.restrict (parabolicCylinder x t₁ (1 / 2 : ℝ))),
        vec3EuclideanNorm (ω z) ≤ C) := by
  have hΩ : IsOpen (Set.univ : Set Vec3) := isOpen_univ
  have hJ : IsOpen J := hsws.2.1
  have hcpt : IsCompact (closure (parabolicCylinder x t₁ 1)) := by
    rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1)]
    have hball : IsCompact {y : Vec3 | vec3EuclideanNorm (y - x) ≤ 1} := by
      have hbd : Bornology.IsBounded {y : Vec3 | vec3EuclideanNorm (y - x) ≤ 1} := by
        refine (Metric.isBounded_closedBall (x := x) (r := 1)).subset ?_
        intro y hy
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact (norm_le_vec3EuclideanNorm _).trans hy
      have hcl' : IsClosed {y : Vec3 | vec3EuclideanNorm (y - x) ≤ 1} :=
        isClosed_le (CKN.continuous_vec3EuclideanNorm.comp
          (continuous_id.sub continuous_const)) continuous_const
      exact Metric.isCompact_of_isClosed_isBounded hcl' hbd
    have hprod := hball.prod (isCompact_Icc (a := t₁ - 1 ^ 2) (b := t₁))
    exact (parabolicHomeomorph.isCompact_preimage).2 hprod
  obtain ⟨Ω', J', hbox, hK⟩ :=
    caccioppoli_localBox_of_compact_subset hΩ hJ hsws.2.2.1 hcpt hcl
  have hdata := hsws.2.2.2.2.2.1 Ω' J' hbox
  have hfin := hdata.2.2.2.2.2.1
  let I₀ : ℝ≥0∞ := ∫⁻ z in parabolicCylinder x t₁ 1, ‖DV z‖ₑ ^ (2 : ℝ)
  have hI₀ : I₀ < ⊤ := by
    refine lt_of_le_of_lt ?_ hfin
    calc
      I₀ ≤ ∫⁻ z in spaceTimeSet Ω' J', ‖DV z‖ₑ ^ (2 : ℝ) :=
        lintegral_mono_set (subset_closure.trans hK)
      _ ≤ ∫⁻ z in spaceTimeSet Ω' J', ‖V z‖ₑ ^ (2 : ℝ) + ‖DV z‖ₑ ^ (2 : ℝ) :=
        lintegral_mono fun z => le_add_self
  let E : ℝ := Real.sqrt I₀.toReal
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have hEsq : ENNReal.ofReal (E ^ 2) = I₀ := by
    rw [Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hI₀.ne]
  obtain ⟨C, hC, hreg⟩ := vorticityRegularity 3 M E (by norm_num) hM hE
  refine ⟨C, hC, ?_⟩
  exact hreg Set.univ J V DV pv x t₁ hΩ hJ hsws hcl hV (le_of_eq hEsq.symm)

end ESS
