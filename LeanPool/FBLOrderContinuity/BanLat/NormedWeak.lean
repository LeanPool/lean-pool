/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Normed
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Data.Fintype.Order

/-!
# Monotone weak convergence in normed vector lattices

Monotone nets that converge weakly converge in norm.
-/

@[expose] public section

namespace NormedVectorLattice

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

private theorem mem_closure_convexHull_tail_of_weak_tendsto
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → X} {x : X}
    (hweak : Filter.Tendsto (fun i => (toWeakSpace ℝ X) (u i)) Filter.atTop
      (nhds ((toWeakSpace ℝ X) x))) (i : ι) :
    x ∈ closure (convexHull ℝ (u '' Set.Ici i)) := by
  have hx : (toWeakSpace ℝ X) x ∈
      closure (toWeakSpace ℝ X '' convexHull ℝ (u '' Set.Ici i)) := by
    apply mem_closure_of_tendsto hweak
    filter_upwards [Filter.Ici_mem_atTop i] with j hj
    exact ⟨u j, subset_convexHull ℝ _ ⟨j, hj, rfl⟩, rfl⟩
  rw [← (convex_convexHull ℝ (u '' Set.Ici i)).toWeakSpace_closure ℝ] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  simpa only [(toWeakSpace ℝ X).injective hyx] using hy

private theorem tendsto_of_monotone_weak_tendsto_aux
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → X} {x : X} (hmono : Monotone u)
    (hweak : Filter.Tendsto (fun i => (toWeakSpace ℝ X) (u i)) Filter.atTop
      (nhds ((toWeakSpace ℝ X) x))) :
    Filter.Tendsto u Filter.atTop (nhds x) := by
  classical
  have hle (i : ι) : u i ≤ x := by
    apply closure_minimal _ isClosed_Ici
      (mem_closure_convexHull_tail_of_weak_tendsto hweak i)
    apply convexHull_min _ (convex_Ici (u i))
    rintro _ ⟨j, hij, rfl⟩
    exact hmono hij
  rw [Metric.tendsto_nhds]
  intro ε hε
  let i₀ : ι := Classical.choice inferInstance
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp
    (mem_closure_convexHull_tail_of_weak_tendsto hweak i₀) ε hε
  obtain ⟨κ, hκ, w, z, hw, hw_one, hz, hwy⟩ :=
    mem_convexHull_iff_exists_fintype.mp hy
  let : Fintype κ := hκ
  let r : κ → ι := fun a => (hz a).choose
  have hzr (a : κ) : u (r a) = z a := (hz a).choose_spec.2
  obtain ⟨j, hj⟩ := Finite.exists_le r
  have hyj : y ≤ u j := by
    rw [← hwy]
    calc
      ∑ a, w a • z a ≤ ∑ a, w a • u j := by
        apply Finset.sum_le_sum
        intro a _
        apply smul_le_smul_of_nonneg_left _ (hw a)
        calc z a = u (r a) := (hzr a).symm
          _ ≤ u j := hmono (hj a)
      _ = (∑ a, w a) • u j := by rw [Finset.sum_smul]
      _ = u j := by rw [hw_one, one_smul]
  have hxy_norm : ‖x - y‖ < ε := by simpa only [dist_eq_norm] using hxy
  have hnorm_j : ‖x - u j‖ < ε := by
    refine (norm_le_norm_of_abs_le_abs ?_).trans_lt hxy_norm
    rw [abs_of_nonneg (sub_nonneg.mpr (hle j)),
      abs_of_nonneg (sub_nonneg.mpr (hyj.trans (hle j)))]
    exact sub_le_sub_left hyj x
  filter_upwards [Filter.Ici_mem_atTop j] with k hjk
  rw [dist_eq_norm, norm_sub_rev]
  refine (norm_le_norm_of_abs_le_abs ?_).trans_lt hnorm_j
  rw [abs_of_nonneg (sub_nonneg.mpr (hle k)),
    abs_of_nonneg (sub_nonneg.mpr (hle j))]
  exact sub_le_sub_left (hmono hjk) x

/-- **Dini's theorem**: a monotone net in a normed vector lattice that converges weakly
converges in norm. -/
theorem tendsto_of_monotone_weak_tendsto
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → X} {x : X} (hmono : Monotone u ∨ Antitone u)
    (hweak : Filter.Tendsto (fun i => (toWeakSpace ℝ X) (u i)) Filter.atTop
      (nhds ((toWeakSpace ℝ X) x))) :
    Filter.Tendsto u Filter.atTop (nhds x) := by
  rcases hmono with hmono | hanti
  · exact tendsto_of_monotone_weak_tendsto_aux hmono hweak
  · have hneg_mono : Monotone fun i => -u i := fun _ _ hij => neg_le_neg (hanti hij)
    have hneg_weak :
        Filter.Tendsto (fun i => (toWeakSpace ℝ X) (-u i)) Filter.atTop
          (nhds ((toWeakSpace ℝ X) (-x))) := by
      simpa using hweak.neg
    have hneg := tendsto_of_monotone_weak_tendsto_aux hneg_mono hneg_weak
    simpa using hneg.neg


end NormedVectorLattice
