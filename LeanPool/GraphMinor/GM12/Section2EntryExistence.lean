/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2SectorExistence

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
  have hpos : 0 < c - h₀ := sub_pos.mpr hh₀.2
  let m : unitInterval → ℝ := fun t => h₀ + t.val * (c - h₀)
  have hm : Continuous m := by fun_prop
  have hmI : ∀ t, m t ∈ Icc h₀ c := by
    intro t
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg t.property.1 hpos.le)
    · have hle := mul_le_of_le_one_left hpos.le t.property.2
      dsimp only [m]
      linarith
  have hmLt : ∀ t, t < 1 → m t ∈ Ico h₀ c := by
    intro t ht
    refine ⟨(hmI t).1, ?_⟩
    have hlt := mul_lt_of_lt_one_left hpos ht
    dsimp only [m]
    linarith
  have hg : Continuous (f ∘ m) := hf.comp_continuous hm hmI
  have hmem : ∀ t, f (m t) ∈ ρ k ∪ {v} := by
    intro t
    by_cases ht : t = 1
    · right
      change f (h₀ + t.val * (c - h₀)) ∈ {v}
      rw [ht]
      simpa only [Icc.coe_one, one_mul, add_sub_cancel, hfc] using mem_singleton v
    · exact Or.inl (hinside _ (hmLt t (unitInterval.lt_one_iff_ne_one.mpr ht))).1
  have hx : f h₀ ∈ ρ k ∪ {v} := Or.inl (hinside h₀ ⟨le_rfl, hh₀.2⟩).1
  let F : Path (⟨f h₀, hx⟩ : (ρ k ∪ {v} : Set S)) ⟨v, Or.inr rfl⟩ := {
    toFun := fun t => ⟨f (m t), hmem t⟩
    continuous_toFun := hg.subtype_mk _
    source' := Subtype.ext (by simp [m])
    target' := Subtype.ext (by simpa only [m, Icc.coe_one, one_mul, add_sub_cancel] using hfc) }
  have hFval : ∀ t, (F t).val = f (h₀ + t.val * (c - h₀)) := fun _ => rfl
  have hF : ∀ t, t < 1 → (F t).val ∈ ρ k ∩ (Q k \ discBd (Q k)) :=
    fun t ht => hinside _ (hmLt t ht)
  obtain ⟨e, he, q, hqi, hqe, t, ht, ρpath, hρpath, hhom⟩ :=
    exists_entry_comparison_in_sector hS hrad hmax hE hv hsec hcover k hw hwV F hF
  let h := h₀ + t.val * (c - h₀)
  have hh : h ∈ Ioo a c := by
    refine ⟨lt_of_lt_of_le hh₀.1 (hmI t).1, (hmLt t ht).2⟩
  have hp : ∀ s : unitInterval, ((F.subpath t 1) s).val = f (h + s.val * (c - h)) := by
    intro s
    change (F (Icc.convexComb t 1 s)).val = _
    rw [hFval]
    congr 1
    simp only [Icc.coe_convexComb, Icc.coe_one]
    dsimp only [h]
    ring
  exact ⟨e, he, entersLike_of_path_comparison hh rfl (F.subpath t 1) q ρpath hp hqi hqe hρpath hhom⟩

end GraphMinor.GM12
