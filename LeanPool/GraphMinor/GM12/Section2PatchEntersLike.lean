/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2EntryWitness
public import LeanPool.GraphMinor.GM12.Section2PatchEntryComparison
import LeanPool.GraphMinor.GM12.Section2SpokePaths
import LeanPool.GraphMinor.GM12.Section2EntryPaths

/-!
# The exact entry witness from a normal patch

For the omitted entry lemma of XII, page 243, normalize a terminal
real interval of the approaching curve to a path. Compare that path
with the supplied spoke inside the normal patch. The shortened
parameter interval is again affine, so the comparison supplies exactly
the entry curve and region homotopy in `EntersLike`.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A simply connected normal patch turns a spoke through its region
into an `EntersLike` witness for any continuous approach in that region. -/
theorem entersLike_of_normal_patch
    {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {r N X : Set S} (hr : r ∈ Γ.R) {v w : S}
    (hv : v ∈ Γ.V) (hw : w ∈ r)
    (hN : IsOpen N) (hvN : v ∈ N) (hvX : v ∈ X)
    (hX : IsSimplyConnectedSet X) (hpuncture : IsPathConnected (X \ {v}))
    (hXZ : X ⊆ r ∪ {v}) (hcover : N \ Γ.U ⊆ X)
    (β : Path v w) (hβi : Function.Injective β) {e : Set S}
    (hβe : β '' Ioo (0 : unitInterval) 1 = e) (hβr : ∀ t, 0 < t → β t ∈ r)
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hac : a < c) (hfc : f c = v)
    (hinside : ∀ t ∈ Ioo a c, f t ∈ r) : EntersLike f a c e r v w := by
  let h₀ := (a + c) / 2
  have hh₀ : h₀ ∈ Ioo a c := ⟨by dsimp [h₀]; linarith, by dsimp [h₀]; linarith⟩
  obtain ⟨F, hFval, hF⟩ := exists_affine_approach_path hh₀.2 hf.continuousOn hfc
    (fun t ht => hinside t ⟨hh₀.1.trans_le ht.1, ht.2⟩)
  obtain ⟨q₀, hq₀⟩ := exists_path_in_region_vertex hw β hβr
  let q := q₀.cast F.target rfl
  have hq : ∀ t, (q t).val = β t := hq₀
  obtain ⟨t, ht, ρ, hρ, hhom⟩ := entry_comparison_from_normal_patch hr hv hN hvN hvX
    hX hpuncture hXZ hcover F q hF (fun t ht => hq t ▸ hβr t ht)
  let h := h₀ + t.val * (c - h₀)
  have htime := affine_approach_parameter_mem_Ico hh₀.2 ht
  have hh : h ∈ Ioo a c := ⟨hh₀.1.trans_le htime.1, htime.2⟩
  have hp : ∀ s : unitInterval, ((F.subpath t 1) s).val = f (h + s.val * (c - h)) :=
    affine_approach_subpath_apply F hFval t
  have hqi : Function.Injective (fun t => (q t).val) := by
    intro s t he
    change (q s).val = (q t).val at he
    rw [hq, hq] at he
    exact hβi he
  have hqe : (fun t => (q t).val) '' Ioo (0 : unitInterval) 1 = e := by
    rw [show (fun t => (q t).val) = β from funext hq]
    exact hβe
  exact entersLike_of_path_comparison hh rfl (F.subpath t 1) q ρ hp hqi hqe hρ hhom

end GraphMinor.GM12
