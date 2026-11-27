/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Compactness.Compact

/-!
# The literal operator-norm unit ball is weak-operator compact

The auxiliary coefficient set records exactly bounded sesquilinearity.
Tychonoff compactness and Riesz representation reconstruct actual bounded
operators on the full Hilbert space. No finite-dimensionality or predual
of an operator algebra is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped InnerProductSpace Topology
open ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Coefficients are ordered as `inner (T x) y`, conjugate-linear in x. -/
private def unitCoefficientSet (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] : Set (H × H → ℂ) :=
  {c | (∀ x z y, c (x + z, y) = c (x, y) + c (z, y)) ∧
    (∀ (a : ℂ) x y, c (a • x, y) = star a * c (x, y)) ∧
    (∀ x y z, c (x, y + z) = c (x, y) + c (x, z)) ∧
    (∀ (a : ℂ) x y, c (x, a • y) = a * c (x, y)) ∧
    (∀ x y, ‖c (x, y)‖ ≤ ‖x‖ * ‖y‖)}

omit [CompleteSpace H] in
private theorem isClosed_unitCoefficientSet : IsClosed (unitCoefficientSet H) := by
  unfold unitCoefficientSet
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_iInter fun x => isClosed_iInter fun z => isClosed_iInter fun y =>
    isClosed_eq (by fun_prop) (by fun_prop)).inter ?_
  refine (isClosed_iInter fun a => isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_eq (by fun_prop) (by fun_prop)).inter ?_
  refine (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
    isClosed_eq (by fun_prop) (by fun_prop)).inter ?_
  refine (isClosed_iInter fun a => isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_eq (by fun_prop) (by fun_prop)).inter ?_
  exact isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_le (by fun_prop) continuous_const

omit [CompleteSpace H] in
private theorem isCompact_unitCoefficientSet : IsCompact (unitCoefficientSet H) := by
  have hprod : IsCompact {c : H × H → ℂ |
      ∀ p, c p ∈ Metric.closedBall (0 : ℂ) (‖p.1‖ * ‖p.2‖)} :=
    isCompact_pi_infinite fun p => isCompact_closedBall (0 : ℂ) (‖p.1‖ * ‖p.2‖)
  apply hprod.of_isClosed_subset isClosed_unitCoefficientSet
  intro c hc p
  simpa only [Metric.mem_closedBall, dist_zero_right] using hc.2.2.2.2 p.1 p.2

private def coefficientSesq (c : unitCoefficientSet H) : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := fun y => c.1 (x, y)
      map_add' := fun y z => c.2.2.2.1 x y z
      map_smul' := fun a y => by
        simpa only [smul_eq_mul, RingHom.id_apply] using c.2.2.2.2.1 a x y }
  map_add' x z := by
    ext y
    exact c.2.1 x z y
  map_smul' a x := by
    ext y
    exact c.2.2.1 a x y

private def coefficientSesqContinuous (c : unitCoefficientSet H) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  (coefficientSesq c).mkContinuous₂ 1 (fun x y => by
    change ‖c.1 (x, y)‖ ≤ 1 * ‖x‖ * ‖y‖
    simpa only [one_mul] using c.2.2.2.2.2 x y)

private def coefficientOperator (c : unitCoefficientSet H) : H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin (coefficientSesqContinuous c)

private theorem coefficientOperator_inner (c : unitCoefficientSet H) (x y : H) :
    inner ℂ (coefficientOperator c x) y = c.1 (x, y) := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply _ x y

private theorem coefficientOperator_norm_le (c : unitCoefficientSet H) :
    ‖coefficientOperator c‖ ≤ 1 := by
  have hb : ‖coefficientSesqContinuous c‖ ≤ 1 :=
    (coefficientSesq c).mkContinuous₂_norm_le zero_le_one _
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(InnerProductSpace.toDual ℂ H).symm (coefficientSesqContinuous c x)‖ ≤ 1 * ‖x‖
  rw [(InnerProductSpace.toDual ℂ H).symm.norm_map]
  exact (coefficientSesqContinuous c).le_of_opNorm_le hb x

private theorem continuous_coefficientOperator :
    Continuous (fun c : unitCoefficientSet H => ofCLM (coefficientOperator c)) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  have he : (fun c : unitCoefficientSet H => inner ℂ y (coefficientOperator c x)) =
      (fun c : unitCoefficientSet H => star (c.1 (x, y))) := by
    funext c
    simpa only [coefficientOperator_inner, starRingEnd_apply] using
      (inner_conj_symm (𝕜 := ℂ) y (coefficientOperator c x)).symm
  change Continuous (fun c : unitCoefficientSet H => inner ℂ y (coefficientOperator c x))
  rw [he]
  exact ((continuous_apply (x, y)).comp continuous_subtype_val).star

omit [CompleteSpace H] in
private theorem operator_coefficients_mem (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    (fun p : H × H => inner ℂ (T p.1) p.2) ∈ unitCoefficientSet H := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x z y
    simp only [map_add, inner_add_left]
  · intro a x y
    simp only [map_smul, inner_smul_left, starRingEnd_apply]
  · intro x y z
    exact inner_add_right _ _ _
  · intro a x y
    exact inner_smul_right _ _ _
  · intro x y
    exact (norm_inner_le_norm (T x) y).trans
      (mul_le_mul_of_nonneg_right (by simpa only [one_mul] using T.le_of_opNorm_le hT x)
        (norm_nonneg y))

/-- The actual operator-norm unit ball, viewed in mathlib's WOT type copy,
is compact even when the original Hilbert space is infinite dimensional. -/
theorem isCompact_operator_unitBall_wot :
    IsCompact {T : H →WOT[ℂ] H | ‖T.toCLM‖ ≤ 1} := by
  let : CompactSpace (unitCoefficientSet H) :=
    isCompact_iff_compactSpace.mp isCompact_unitCoefficientSet
  have hr : Set.range (fun c : unitCoefficientSet H => ofCLM (coefficientOperator c)) =
      {T : H →WOT[ℂ] H | ‖T.toCLM‖ ≤ 1} := by
    ext T
    constructor
    · rintro ⟨c, rfl⟩
      exact coefficientOperator_norm_le c
    · intro hT
      let c : unitCoefficientSet H :=
        ⟨fun p => inner ℂ (T.toCLM p.1) p.2, operator_coefficients_mem T.toCLM hT⟩
      refine ⟨c, ?_⟩
      apply ContinuousLinearMapWOT.toCLM_injective
      apply ContinuousLinearMap.ext
      intro x
      apply ext_inner_right ℂ
      intro y
      exact coefficientOperator_inner c x y
  rw [← hr]
  exact isCompact_range continuous_coefficientOperator

end VacuumBellSeparation.Bipartite
