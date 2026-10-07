/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessWeak
public import Mathlib.Topology.Bases

/-!
# Compactness Gradient Diagonal

Supporting estimates for the Navier–Stokes development.
-/

public section

open Filter Set Topology

namespace CKN.Leray

/-- A countable family of uniformly bounded Hilbert-space sequences has one
subsequence that converges weakly in every member of the family. -/
theorem exists_common_subsequence_weak_limit_of_bounded
    {ι : Type*} [Countable ι]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, CompleteSpace (E i)]
    [∀ i, TopologicalSpace.SeparableSpace (E i)]
    (u : ℕ → ∀ i, E i)
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ n i, ‖u n i‖ ≤ C i) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ v : ∀ i, E i,
      ∀ i x, Tendsto (fun n => inner ℝ (u (σ n) i) x) atTop
        (nhds (inner ℝ (v i) x)) := by
  classical
  choose ψ hψ using fun i => TopologicalSpace.exists_dense_seq (E i)
  let F : ℕ → ι × ℕ → ℝ := fun n p => inner ℝ (u n p.1) (ψ p.1 p.2)
  have hcompact (p : ι × ℕ) :
      IsCompact (closure (range fun n => F n p)) := by
    let B : ℝ := C p.1 * ‖ψ p.1 p.2‖
    have hB : 0 ≤ B := mul_nonneg (hC p.1) (norm_nonneg _)
    have hrange : range (fun n => F n p) ⊆ Icc (-B) B := by
      rintro y ⟨n, rfl⟩
      rw [mem_Icc]
      have hinner : |F n p| ≤ B := by
        dsimp [F, B]
        exact (abs_real_inner_le_norm (u n p.1) (ψ p.1 p.2)).trans
          (mul_le_mul_of_nonneg_right (hbound n p.1) (norm_nonneg _))
      exact abs_le.mp hinner
    exact IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
      (closure_minimal hrange isClosed_Icc)
  obtain ⟨σ, hσ, L, hL⟩ :=
    exists_strictMono_tendsto_forall_of_isCompact_closure_range F hcompact
  have hlimit (i : ι) : ∃ v : E i,
      ∀ x, Tendsto (fun n => inner ℝ (u (σ n) i) x) atTop
        (nhds (inner ℝ v x)) := by
    apply exists_weak_limit_of_tendsto_pairings_on_dense_range
      (fun n => u (σ n) i) (C i) (hC i)
      (fun n => hbound (σ n) i) (ψ i) (hψ i)
    intro m
    exact ⟨L (i,m), hL (i,m)⟩
  choose v hv using hlimit
  exact ⟨σ, hσ, v, fun i => hv i⟩

end CKN.Leray
