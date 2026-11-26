/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.Surface.Classification
import LeanPool.GraphMinor.Surface.ModelCriterion

/-!
# Constants in the proof of Graph Minors VII (4.6)

The proof on page 224 chooses a surface model and uses its constants throughout.
We choose a model attaining the natural-number infimum defining `vSurface`.
This makes the bound in the hypotheses equal to the bound used by the proof.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

/-- The model and constants chosen at the start of VII (4.6), page 224.
The infimum defining `vSurface` is attained by an actual surface model. -/
theorem exists_model_vSurface {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [ConnectedSpace S] (k : ℕ) :
    ∃ a b c : ℕ, Nonempty (S ≃ₜ SurfaceModel a b c) ∧
      vSurface S k = vModel a b c k := by
  obtain ⟨a, b, c, hmodel⟩ := classification S hS ‹ConnectedSpace S›
  have hne : {v : ℕ | ∃ a b c : ℕ,
      Nonempty (S ≃ₜ SurfaceModel a b c) ∧ v = vModel a b c k}.Nonempty :=
    ⟨vModel a b c k, a, b, c, hmodel, rfl⟩
  exact Nat.sInf_mem hne

/-- The model's third parameter is the number of cuffs, including for
the model chosen to attain `vSurface` in VII (4.6), page 224. -/
theorem ncard_cuffs_eq_of_surface_model {S : Type u} [TopologicalSpace S]
    {a b c : ℕ} (e : S ≃ₜ SurfaceModel a b c) : (cuffs S).ncard = c := by
  obtain ⟨ht, f, hf⟩ := presents_ew a b c
  have := ht
  rw [ncard_cuffs_congr e]
  exact ncard_cuffs hf

/-- The start of VII (4.6) can choose an attaining model with at least
two cuffs, so its factor `2a+b+c-1` is positive. -/
theorem exists_model_vSurface_two_cuffs {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [ConnectedSpace S] (hcuffs : 2 ≤ (cuffs S).ncard) (k : ℕ) :
    ∃ a b c : ℕ, 2 ≤ c ∧ Nonempty (S ≃ₜ SurfaceModel a b c) ∧
      vSurface S k = vModel a b c k := by
  obtain ⟨a, b, c, ⟨e⟩, hv⟩ := exists_model_vSurface hS k
  have hc := ncard_cuffs_eq_of_surface_model e
  exact ⟨a, b, c, hc ▸ hcuffs, ⟨e⟩, hv⟩

/-- The maximum defining `w` includes every model with the cuff bound used
on page 226 of the proof of VII (4.6). -/
theorem wSurface_model_le_wMaxModel {a b c c' k : ℕ}
    (hc' : c' ≤ 2 * (2 * a + b + c - 1)) :
    wSurface (SurfaceModel a b c') (2 * k) (3 * (2 * a + b + c - 1)) ≤
      wMaxModel a b c k := by
  unfold wMaxModel
  exact Finset.le_sup (f := fun c' =>
    wSurface (SurfaceModel a b c') (2 * k) (3 * (2 * a + b + c - 1)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hc'))

/-- Numerical bounds used on pages 225 and 228 of VII (4.6). In particular,
a seam edge on a cuff cannot be long, and the shortcut bound is at most `v`. -/
theorem constants_bounds_4_6 {a b c k : ℕ} (hc : 2 ≤ c) :
    2 * k < 2 * muModel a b c k + wMaxModel a b c k + 2 ∧
    muModel a b c k ≤ vModel a b c k ∧
    6 * (2 * a + b + c - 1) * muModel a b c k ≤ vModel a b c k - 2 * k := by
  have hn : 0 < 6 * (2 * a + b + c - 1) := by omega
  have hk : 2 * k ≤ muModel a b c k := by
    unfold muModel
    exact Nat.le_add_left _ _
  have hm : muModel a b c k ≤
      wMaxModel a b c k + 2 * muModel a b c k + 1 := by omega
  have hv : muModel a b c k ≤
      6 * (2 * a + b + c - 1) *
        (wMaxModel a b c k + 2 * muModel a b c k + 1) :=
    hm.trans (Nat.le_mul_of_pos_left _ hn)
  refine ⟨by omega, ?_, ?_⟩
  · exact hv.trans (Nat.le_add_right _ _)
  · unfold vModel
    rw [Nat.add_sub_cancel]
    exact Nat.mul_le_mul_left _ hm

/-- The boundary hypotheses of VII (4.6) force `k ≥ 2`: two distinct
cuffs each contain two vertices, and their vertex sets are disjoint. -/
theorem two_le_k_of_boundary_4_6 {S : Type u} [TopologicalSpace S]
    {G : Drawing S} {k : ℕ} (hcuffs : 2 ≤ (cuffs S).ncard)
    (hbd : (G.V ∩ bd S).ncard ≤ 2 * k)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard) : 2 ≤ k := by
  obtain ⟨C, hC, C', hC', hne⟩ :=
    (Set.one_lt_ncard (Set.finite_of_ncard_pos (by omega))).mp (by omega : 1 < (cuffs S).ncard)
  have hdis : Disjoint (G.V ∩ C) (G.V ∩ C') :=
    (cuffs_disjoint hC hC' hne).mono inter_subset_right inter_subset_right
  have hsub : (G.V ∩ C) ∪ (G.V ∩ C') ⊆ G.V ∩ bd S := by
    rintro x (hx | hx)
    · exact ⟨hx.1, sUnion_cuffs (S := S) ▸ ⟨C, hC, hx.2⟩⟩
    · exact ⟨hx.1, sUnion_cuffs (S := S) ▸ ⟨C', hC', hx.2⟩⟩
  have hcard := Set.ncard_le_ncard hsub (G.finite_V.subset inter_subset_left)
  rw [Set.ncard_union_eq hdis (G.finite_V.subset inter_subset_left)
    (G.finite_V.subset inter_subset_left)] at hcard
  have hC2 := hiii C hC
  have hC'2 := hiii C' hC'
  omega

end GraphMinor.GM07
