/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2SectorExistence
import LeanPool.GraphMinor.GM12.Section2EntryPaths

/-!
# Entry-edge existence with an explicit entering sector

This file connects the local existence proof to the real parameters in
XII's trace definition, page 243. Normalize a terminal interval of the
curve to a path. The entering-spoke comparison supplies a shorter
interval and a homotopy. Its affine parametrization gives an exact
`EntersLike` witness.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The omitted entry-edge existence assertion in XII, page 243, for a
curve whose terminal interval is in a specified sector. -/
theorem exists_entersLike_of_sector {S : Type*} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ K : Drawing S} (hrad : PreRad (.drawing Γ) K)
    (hmax : RadMax (.drawing Γ) K) (hE : Γ.E.Nonempty)
    {γ : Set S → unitInterval → S} {v : S} (hv : v ∈ Γ.V)
    {next : halfEdges Γ γ v → halfEdges Γ γ v}
    {ρ P Q : halfEdges Γ γ v → Set S} {W : Set S}
    {τ : halfEdges Γ γ v → unitInterval}
    (hsec : IsSectors Γ γ v next ρ P W Q τ)
    (hcover : W \ Γ.U ⊆ ⋃ k, Q k) (k : halfEdges Γ γ v)
    {w : S} (hw : w ∈ ρ k) (hwV : w ∈ K.V)
    {f : ℝ → S} {a c h₀ : ℝ} (hh₀ : h₀ ∈ Ioo a c)
    (hf : ContinuousOn f (Icc h₀ c)) (hfc : f c = v)
    (hinside : ∀ t ∈ Ico h₀ c, f t ∈ ρ k ∩ (Q k \ discBd (Q k))) :
    ∃ e ∈ K.E, EntersLike f a c e (ρ k) v w := by
  obtain ⟨F, hFval, -⟩ := exists_affine_approach_path hh₀.2 hf hfc
    (fun t ht => (hinside t ht).1)
  have hF : ∀ t, t < 1 → (F t).val ∈ ρ k ∩ (Q k \ discBd (Q k)) := by
    intro t ht
    rw [hFval]
    exact hinside _ (affine_approach_parameter_mem_Ico hh₀.2 ht)
  obtain ⟨e, he, q, hqi, hqe, t, ht, ρpath, hρpath, hhom⟩ :=
    exists_entry_comparison_in_sector hS hrad hmax hE hv hsec hcover k hw hwV F hF
  let h := h₀ + t.val * (c - h₀)
  have htime := affine_approach_parameter_mem_Ico hh₀.2 ht
  have hh : h ∈ Ioo a c := ⟨hh₀.1.trans_le htime.1, htime.2⟩
  have hp : ∀ s : unitInterval, ((F.subpath t 1) s).val = f (h + s.val * (c - h)) :=
    affine_approach_subpath_apply F hFval t
  exact ⟨e, he, entersLike_of_path_comparison hh rfl (F.subpath t 1) q ρpath hp hqi hqe hρpath hhom⟩

end GraphMinor.GM12
