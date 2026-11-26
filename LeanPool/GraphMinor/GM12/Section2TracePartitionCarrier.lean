/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TracePartition
public import LeanPool.GraphMinor.GM12.Section2WalkCarriers

/-!
# Keeping the point set when assembling region visits

For Case 1 of XII (2.1), page 244, assemble the two-edge walks of
the region visits while retaining their point sets. Concatenation
unions these sets. The initial and joining vertices already belong
to the first walk's point set, so the resulting trace has exactly
the union of the prescribed region-path point sets, together with
its initial vertex in the zero-interval case.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Assemble the trace steps and retain the union of the point sets
of the individual two-edge region visits. -/
theorem exists_traceSteps_of_partition_with_carrier
    {S : Type*} [TopologicalSpace S] [T1Space S] {Γ K : Drawing S} {f : ℝ → S}
    {n : ℕ} (t : Fin (n + 1) → ℝ)
    (hΓ : ∀ i, f (t i) ∈ Γ.V) (hK : ∀ i, f (t i) ∈ K.V) (C : Fin n → Set S)
    (hsteps : ∀ i : Fin n,
      ∃ W : GraphWalk K.toGraph (f (t i.castSucc)) (f (t i.succ)),
        TraceSteps Γ K f (t i.castSucc) (t i.succ) W ∧ W.length = 2 ∧
        (walkDrawing K W).U = C i) :
    ∃ W : GraphWalk K.toGraph (f (t 0)) (f (t (Fin.last n))),
      TraceSteps Γ K f (t 0) (t (Fin.last n)) W ∧ W.length = 2 * n ∧
      (walkDrawing K W).U = {f (t 0)} ∪ ⋃ i, C i := by
  induction n with
  | zero =>
    refine ⟨.nil (hK 0), ⟨rfl, rfl, hΓ 0⟩, rfl, ?_⟩
    rw [walkDrawing_U_nil K (hK 0)]
    simp only [iUnion_of_empty, union_empty]
  | succ n ih =>
    let t' : Fin (n + 1) → ℝ := fun i => t i.succ
    let C' : Fin n → Set S := fun i => C i.succ
    have hsteps' : ∀ i : Fin n,
        ∃ W : GraphWalk K.toGraph (f (t' i.castSucc)) (f (t' i.succ)),
          TraceSteps Γ K f (t' i.castSucc) (t' i.succ) W ∧ W.length = 2 ∧
          (walkDrawing K W).U = C' i := fun i => hsteps i.succ
    obtain ⟨Q, hQ, hQlen, hQU⟩ := ih t' (fun i => hΓ i.succ) (fun i => hK i.succ) C' hsteps'
    have hhead := hsteps (0 : Fin (n + 1))
    simp only [Fin.castSucc_zero] at hhead
    obtain ⟨P, hP, hPlen, hPU⟩ := hhead
    have hstart : f (t 0) ∈ C 0 := by
      rw [← hPU]
      apply (walkDrawing K P).V_subset_U
      rw [walkDrawing_V]
      exact P.start_mem_support
    have hend : f (t' 0) ∈ C 0 := by
      rw [← hPU]
      apply (walkDrawing K P).V_subset_U
      rw [walkDrawing_V]
      exact P.end_mem_support
    have hunion : (⋃ i : Fin (n + 1), C i) = C 0 ∪ ⋃ i : Fin n, C i.succ := by
      ext x
      simp only [mem_iUnion, mem_union]
      constructor
      · rintro ⟨i, hi⟩
        obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
        · exact Or.inl hi
        · exact Or.inr ⟨j, hi⟩
      · rintro (hi | ⟨j, hj⟩)
        · exact ⟨0, hi⟩
        · exact ⟨j.succ, hj⟩
    refine ⟨P.append Q, traceSteps_append P Q hP hQ, ?_, ?_⟩
    · rw [GraphWalk.length_append P Q, hPlen, hQlen]
      omega
    · rw [walkDrawing_U_append K P Q, hPU, hQU]
      change C 0 ∪ ({f (t' 0)} ∪ ⋃ i : Fin n, C i.succ) =
        {f (t 0)} ∪ ⋃ i : Fin (n + 1), C i
      rw [← union_assoc, union_eq_left.mpr (singleton_subset_iff.mpr hend), hunion,
        ← union_assoc, union_eq_right.mpr (singleton_subset_iff.mpr hstart)]

end GraphMinor.GM12
