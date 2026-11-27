/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.NormalStateCompression
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
Finite convex mixtures of actual positive normal states on the original VNA.
Normality is proved for every directed positive set. The norm bound is in the
full continuous dual, and the final witness concerns an actual observable.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Filter
open scoped Topology ComplexOrder

section CStar
variable {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- The actual convex combination, including both endpoints t=0 and t=1. -/
def stateMixture (φ ψ : C →ₚ[ℂ] ℂ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    C →ₚ[ℂ] ℂ where
  toLinearMap := (1 - t) • φ.toLinearMap + t • ψ.toLinearMap
  monotone' := fun _ _ h => add_le_add
    (smul_le_smul_of_nonneg_left (φ.monotone' h) (sub_nonneg.mpr ht1))
    (smul_le_smul_of_nonneg_left (ψ.monotone' h) ht)

omit [StarOrderedRing C] in
@[simp] theorem stateMixture_apply (φ ψ : C →ₚ[ℂ] ℂ)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (X : C) :
    stateMixture φ ψ t ht ht1 X = (1 - t) • φ X + t • ψ X := rfl

omit [StarOrderedRing C] in
theorem stateMixture_one (φ ψ : C →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) : stateMixture φ ψ t ht ht1 1 = 1 := by
  rw [stateMixture_apply, hφ, hψ, ← add_smul]
  simp only [sub_add_cancel, one_smul]

/-- The full functional norm, not just a finite collection of observables. -/
theorem stateMixture_dual_error_le (φ ψ : C →ₚ[ℂ] ℂ)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(PositiveContinuousLinearMap.ofClass (stateMixture φ ψ t ht ht1)).toContinuousLinearMap -
      (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap‖ ≤ 2 * t := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro X
  change ‖(1 - t) • φ X + t • ψ X - φ X‖ ≤ (2 * t) * ‖X‖
  have he : (1 - t) • φ X + t • ψ X - φ X = t • (ψ X - φ X) := by
    simp only [sub_smul, one_smul, smul_sub]
    abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  calc
    t * ‖ψ X - φ X‖ ≤ t * (‖ψ X‖ + ‖φ X‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) ht
    _ ≤ t * (‖X‖ + ‖X‖) := mul_le_mul_of_nonneg_left
      (add_le_add (stateFunctional_norm_apply_le ψ hψ X)
        (stateFunctional_norm_apply_le φ hφ X)) ht
    _ = (2 * t) * ‖X‖ := by ring

omit [StarOrderedRing C] in
theorem stateMixture_real_gt_one (φ ψ : C →ₚ[ℂ] ℂ) (R : C)
    (hφR : φ R = 1) (hψR : 1 < (ψ R).re)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    1 < (stateMixture φ ψ t ht.le ht1 R).re := by
  simp only [stateMixture_apply, hφR, Complex.add_re, Complex.smul_re,
    Complex.one_re, smul_eq_mul]
  nlinarith [mul_pos ht (sub_pos.mpr hψR)]

end CStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance mixture_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- Order-normality supplies the real expectation limit on the directed set itself. -/
theorem positiveFunctional_real_tendsto_of_normal (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ)
    {s : Set M.toStarSubalgebra} (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (hp : ∀ X ∈ s, 0 ≤ X) {X : M.toStarSubalgebra} (hX : IsLUB s X) :
    Tendsto (fun i : s => (φ i.1).re) atTop (𝓝 (φ X).re) := by
  have he : Set.range (fun i : s => (φ i.1).re) = (fun Y => (φ Y).re) '' s := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨Y, hY, rfl⟩; exact ⟨⟨Y, hY⟩, rfl⟩
  apply tendsto_atTop_isLUB
  · intro i j hij
    exact (Complex.le_def.mp (φ.monotone' hij)).1
  · rw [he]
    exact hn s hs hd hp X hX

/-- The limit argument uses all positive directed suprema, with no countability. -/
theorem stateMixture_isNormal (M : VonNeumannAlgebra H)
    (φ ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hnφ : IsNormalFunctional M φ) (hnψ : IsNormalFunctional M ψ)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsNormalFunctional M (stateMixture φ ψ t ht ht1) := by
  intro s hs hd hp X hX
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hd.isDirectedOrder
  have hlim : Tendsto (fun i : s => (stateMixture φ ψ t ht ht1 i.1).re) atTop
      (𝓝 (stateMixture φ ψ t ht ht1 X).re) := by
    simpa only [stateMixture_apply, Complex.add_re, Complex.smul_re, smul_eq_mul] using
      ((positiveFunctional_real_tendsto_of_normal M φ hnφ hs hd hp hX).const_mul (1 - t)).add
        ((positiveFunctional_real_tendsto_of_normal M ψ hnψ hs hd hp hX).const_mul t)
  constructor
  · rintro _ ⟨Y, hY, rfl⟩
    exact (Complex.le_def.mp ((stateMixture φ ψ t ht ht1).monotone' (hX.1 hY))).1
  · intro r hr
    exact le_of_tendsto hlim (Filter.Eventually.of_forall fun i : s => hr ⟨i.1, i.2, rfl⟩)

theorem stateMixture_isNormalState (M : VonNeumannAlgebra H)
    (φ ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hnφ : IsNormalFunctional M φ) (hnψ : IsNormalFunctional M ψ)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsNormalStateFunctional M (stateMixture φ ψ t ht ht1) :=
  ⟨⟨stateMixture φ ψ t ht ht1, stateMixture_one φ ψ hφ hψ t ht ht1, fun _ => rfl⟩,
    stateMixture_isNormal M φ ψ hnφ hnψ t ht ht1⟩

/-- A normal state with witness value exactly 1 can be perturbed in full norm
by any normal state whose value at that same witness has real part above 1. -/
theorem exists_normal_mixture_near_of_real_gap (M : VonNeumannAlgebra H)
    (φ ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hnφ : IsNormalFunctional M φ) (hnψ : IsNormalFunctional M ψ)
    (R : M.toStarSubalgebra) (hφR : φ R = 1) (hψR : 1 < (ψ R).re)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : StrongDual ℂ M.toStarSubalgebra,
      IsNormalStateFunctional M ρ ∧ 1 < (ρ R).re ∧
      ‖ρ - (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap‖ < ε := by
  let t : ℝ := min (1 / 2) (ε / 4)
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  refine ⟨(PositiveContinuousLinearMap.ofClass (stateMixture φ ψ t ht.le
    ht1)).toContinuousLinearMap,
    stateMixture_isNormalState M φ ψ hφ hψ hnφ hnψ t ht.le ht1,
    stateMixture_real_gt_one φ ψ R hφR hψR t ht ht1, ?_⟩
  apply lt_of_le_of_lt (stateMixture_dual_error_le φ ψ hφ hψ t ht.le ht1)
  have htε : t ≤ ε / 4 := min_le_right _ _
  linarith

end VacuumBellSeparation.Bipartite
