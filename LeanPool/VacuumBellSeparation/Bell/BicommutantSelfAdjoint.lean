/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.BicommutantStrongDensity
public import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Selfadjoint finite-vector approximation

Symmetrization of a strong approximation net converges weakly. Its tuple
orbits form a real linear subspace. Hahn--Banach equality of weak and norm
closures for real convex sets gives actual selfadjoint approximation on
every finite family. No continuity of adjoint in the strong topology is
assumed, and no norm bound on approximants is claimed.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tendsto_toWeakSpace_of_inner {α : Type*} {l : Filter α} {xs : α → H} {x : H}
    (h : ∀ y : H, Tendsto (fun i => ⟪y, xs i⟫_ℂ) l (𝓝 ⟪y, x⟫_ℂ)) :
    Tendsto (fun i => toWeakSpace ℂ H (xs i)) l (𝓝 (toWeakSpace ℂ H x)) := by
  have hinj : Function.Injective (topDualPairing ℂ H).flip := by
    intro u v huv
    apply ext_inner_left ℂ
    intro y
    exact congrArg (fun f => f (InnerProductSpace.toDual ℂ H y)) huv
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing ℂ H).flip hinj).mpr
  intro f
  change Tendsto (fun i => f (xs i)) l (𝓝 (f x))
  simpa only [InnerProductSpace.toDual_symm_apply] using h ((InnerProductSpace.toDual ℂ H).symm f)

theorem starSubalgebra_real_smul_mem (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {A : H →L[ℂ] H} (hA : A ∈ S) (c : ℝ) : c • A ∈ S :=
  (S.toSubalgebra.toSubmodule.restrictScalars ℝ).smul_mem c hA

/-- The orbit of a finite vector family under all self-adjoint operators in the algebra. -/
def selfAdjointTupleOrbit (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {ι : Type*} (x : ι → H) : Submodule ℝ (PiLp 2 (fun _ : ι => H)) where
  carrier := {y | ∃ A ∈ S, IsSelfAdjoint A ∧ WithLp.toLp 2 (fun i => A (x i)) = y}
  zero_mem' := ⟨0, S.zero_mem, IsSelfAdjoint.zero _, by ext i; simp⟩
  add_mem' := by
    rintro y z ⟨A, hA, hsa, rfl⟩ ⟨B, hB, hsb, rfl⟩
    exact ⟨A + B, S.add_mem hA hB, hsa.add hsb, by ext i; simp⟩
  smul_mem' := by
    rintro c y ⟨A, hA, hsa, rfl⟩
    exact ⟨c • A, starSubalgebra_real_smul_mem S hA c,
      (IsSelfAdjoint.all c).smul hsa, by ext i; simp⟩

theorem symmetrized_strong_net_weak {α : Type*} {l : Filter α}
    {As : α → (H →L[ℂ] H)} {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (hAs : ∀ x : H, Tendsto (fun i => As i x) l (𝓝 (T x))) (x y : H) :
    Tendsto (fun i => ⟪y, ((1 / 2 : ℂ) • (As i + star (As i))) x⟫_ℂ)
      l (𝓝 ⟪y, T x⟫_ℂ) := by
  have hstar : Tendsto (fun i => ⟪y, star (As i) x⟫_ℂ) l (𝓝 ⟪y, T x⟫_ℂ) := by
    have h := (hAs y).inner (𝕜 := ℂ) (tendsto_const_nhds (x := x))
    have he : ⟪T y, x⟫_ℂ = ⟪y, T x⟫_ℂ := hT.isSymmetric y x
    simpa only [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, he] using h
  have h := ((tendsto_const_nhds (x := y)).inner (hAs x)).add hstar
  have hh := h.const_mul (1 / 2 : ℂ)
  convert hh using 1
  · ext i
    simp only [smul_apply, add_apply, inner_smul_right, inner_add_right]
  · congr 1
    ring

/-- The actual selfadjoint orbit has the target tuple in its norm closure. -/
theorem selfAdjoint_bicommutant_tuple_mem_closure
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ generatedVNA (S : Set (H →L[ℂ] H))) (hsa : IsSelfAdjoint T)
    {ι : Type*} [Finite ι] (x : ι → H) :
    WithLp.toLp 2 (fun i => T (x i)) ∈ closure (selfAdjointTupleOrbit S x : Set _) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨As, hmem, hstrong⟩ := exists_strong_approximation_in_starSubalgebra S hT
  let Bs := fun j => (1 / 2 : ℂ) • (As j + star (As j))
  let ys := fun j => WithLp.toLp 2 (fun i => Bs j (x i))
  let y := WithLp.toLp 2 (fun i => T (x i))
  have hys : ∀ j, ys j ∈ selfAdjointTupleOrbit S x := by
    intro j
    refine ⟨Bs j, S.smul_mem (S.add_mem (hmem j) (S.star_mem' (hmem j))) _, ?_, rfl⟩
    exact (show IsSelfAdjoint (1 / 2 : ℂ) by simp [isSelfAdjoint_iff]).smul
      (IsSelfAdjoint.add_star_self (As j))
  have hweak : Tendsto (fun j => toWeakSpace ℂ _ (ys j)) atTop (𝓝 (toWeakSpace ℂ _ y)) := by
    apply tendsto_toWeakSpace_of_inner
    intro z
    change Tendsto (fun j => ∑ i, ⟪z i, Bs j (x i)⟫_ℂ) atTop
      (𝓝 (∑ i, ⟪z i, T (x i)⟫_ℂ))
    exact tendsto_finsetSum _ (fun i _ => symmetrized_strong_net_weak hsa hstrong (x i) (z i))
  have hc := mem_closure_of_tendsto hweak
    (Eventually.of_forall (fun j => Set.mem_image_of_mem (toWeakSpace ℂ _) (hys j)))
  rw [← (selfAdjointTupleOrbit S x).convex.toWeakSpace_closure ℂ] at hc
  obtain ⟨v, hv, he⟩ := hc
  have he' : v = y := (toWeakSpace ℂ _).injective he
  change y ∈ closure (selfAdjointTupleOrbit S x : Set _)
  exact he' ▸ hv

theorem selfAdjoint_bicommutant_approximate_finite_family
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ generatedVNA (S : Set (H →L[ℂ] H))) (hsa : IsSelfAdjoint T)
    {ι : Type*} [Finite ι] (x : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ S, IsSelfAdjoint A ∧ ∀ i, ‖T (x i) - A (x i)‖ < ε := by
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨y, ⟨A, hA, hself, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp
    (selfAdjoint_bicommutant_tuple_mem_closure S hT hsa x) ε hε
  refine ⟨A, hA, hself, fun i => ?_⟩
  exact lt_of_le_of_lt (PiLp.norm_apply_le
    (WithLp.toLp 2 (fun i => T (x i)) - WithLp.toLp 2 (fun i => A (x i))) i)
      (by simpa only [dist_eq_norm] using hdist)

end VacuumBellSeparation
