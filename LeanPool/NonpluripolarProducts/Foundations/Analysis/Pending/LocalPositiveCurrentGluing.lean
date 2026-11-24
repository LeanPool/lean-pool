/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ScalarLeviPositiveCurrent
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorLocality

/-! # Full positivity of actual local product currents is local -/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentGluing

open FirstPass StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorLocality ScalarLeviPositiveCurrent

variable {n : ℕ} {U V : Opens (ComplexModel n)}

/-- The actual scalar top current commutes with genuine open restriction. -/
theorem scalarTopCurrent_restrict (hVU : V ≤ U) (T : 𝓓'(U, ℝ)) :
    restrict hVU (scalarTopCurrent T) = scalarTopCurrent (restrictDistribution T hVU) := by
  ext γ φ
  rw [LocalBedfordTaylorLocality.restrict_apply, scalarTopCurrent_apply, scalarTopCurrent_apply,
    restrictDistribution_apply]
  rfl

/-- Restriction also commutes with the scalar top current's genuine differential. -/
theorem ddc_scalarTopCurrent_restrict
    {m : ℕ} {A B : Opens (ComplexModel (m + 1))} (hBA : B ≤ A) (T : 𝓓'(A, ℝ)) :
    restrict hBA (ddc (scalarTopCurrent T)) =
      ddc (scalarTopCurrent (restrictDistribution T hBA)) := by
  rw [← ddc_restrict, scalarTopCurrent_restrict]

/-- Full variable-test positivity is local; the compact-test partition is produced internally. -/
theorem isPositive_of_local_restrict {q : ℕ} {S : LocalProductCurrent n U q}
    (hloc : ∀ x ∈ U, ∃ (V : Opens (ComplexModel n)) (hVU : V ≤ U),
      x ∈ V ∧ IsPositive (restrict hVU S)) : IsPositive S := by
  classical
  intro ι _ γ φ hγ
  let K : Set (ComplexModel n) := ⋃ i : ι, tsupport (φ i)
  have hK : IsCompact K := isCompact_iUnion fun i => (φ i).hasCompactSupport
  have hKU : K ⊆ U := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (φ i).tsupport_subset hi
  choose W hWU hxW hpos using fun x : U => hloc x x.property
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : U => (W x : Set (ComplexModel n)))
    (fun x => (W x).isOpen) (fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hxW ⟨x, hKU hx⟩⟩)
  let J := ↥s
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ComplexModel n)) hK.isClosed
    (fun a : J => (W a.val : Set (ComplexModel n))) (fun a => (W a.val).isOpen) (by
      intro x hx
      obtain ⟨a, ha⟩ := mem_iUnion.mp (hs hx)
      obtain ⟨has, hxa⟩ := mem_iUnion.mp ha
      exact mem_iUnion.mpr ⟨⟨a, has⟩, hxa⟩)
  let ψ (a : J) (i : ι) : 𝓓(W a.val, ℝ) :=
    ⟨fun x => ρ a x * φ i x,
      (ρ a).contMDiff.contDiff.mul (φ i).contDiff,
      (φ i).hasCompactSupport.mul_left,
      tsupport_mul_subset_left.trans (hρ a)⟩
  let Ψ (a : J) (i : ι) : 𝓓(U, ℝ) := extTest (hWU a.val) (ψ a i)
  have hsum_apply : ∀ t : Finset J, ∀ i : ι, ∀ x : ComplexModel n,
      (∑ a ∈ t, Ψ a i) x = ∑ a ∈ t, ρ a x * φ i x := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro i x; rfl
    | @insert a t ha ih =>
        intro i x
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        change Ψ a i x + (∑ b ∈ t, Ψ b i) x =
          ρ a x * φ i x + ∑ b ∈ t, ρ b x * φ i x
        rw [ih i x]
        rw [show Ψ a i x = ρ a x * φ i x from by
          change extTest (hWU a.val) (ψ a i) x = ρ a x * φ i x
          rw [extTest_apply]
          rfl]
  have hφsum : ∀ i : ι, φ i = ∑ a : J, Ψ a i := by
    intro i
    apply TestFunction.ext
    intro x
    rw [hsum_apply, ← Finset.sum_mul]
    by_cases hx : x ∈ K
    · have hsum : ∑ a : J, ρ a x = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hsum, one_mul]
    · have hφx : φ i x = 0 := image_eq_zero_of_notMem_tsupport fun hi =>
        hx (mem_iUnion.mpr ⟨i, hi⟩)
      rw [hφx, mul_zero]
  have hnonneg : ∀ a : J, 0 ≤ ∑ i, S (γ i) (Ψ a i) := by
    intro a
    apply hpos a.val ι γ (ψ a)
    intro x
    change (∑ i, (ρ a x * φ i x) • (γ i : RealForm n (2 * q))) ∈ spCone q
    have heq : (∑ i, (ρ a x * φ i x) • (γ i : RealForm n (2 * q))) =
        ρ a x • (∑ i, φ i x • (γ i : RealForm n (2 * q))) := by
      simp only [Finset.smul_sum, smul_smul]
    rw [heq]
    exact smul_mem_spCone (hγ x) (ρ.nonneg a x)
  have heq : (∑ i, S (γ i) (φ i)) = ∑ a : J, ∑ i, S (γ i) (Ψ a i) := by
    simp only [hφsum, map_sum]
    exact Finset.sum_comm
  rw [heq]
  exact Finset.sum_nonneg fun a _ => hnonneg a

/-- Scalar Levi positivity produces full current positivity on the entire actual open set. -/
theorem isPositive_ddc_scalarTopCurrent
    {m : ℕ} {A : Opens (ComplexModel (m + 1))} {T : 𝓓'(A, ℝ)}
    (hT : HasNonnegativeDistributionalLevi T) : IsPositive (ddc (scalarTopCurrent T)) := by
  apply isPositive_of_local_restrict
  intro x hx
  obtain ⟨B, hBA, hxB, hpos⟩ := exists_local_isPositive_ddc_scalarTopCurrent hT x hx
  exact ⟨B, hBA, hxB, by simpa only [ddc_scalarTopCurrent_restrict] using hpos⟩

end SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentGluing
