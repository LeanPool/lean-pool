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
  have hmLt : ∀ t, t < 1 → m t ∈ Ioo a c := by
    intro t ht
    refine ⟨hh₀.1.trans_le (hmI t).1, ?_⟩
    have hlt := mul_lt_of_lt_one_left hpos ht
    dsimp only [m]
    linarith
  have hmem : ∀ t, f (m t) ∈ r ∪ {v} := by
    intro t
    by_cases ht : t = 1
    · right
      change f (h₀ + t.val * (c - h₀)) ∈ {v}
      rw [ht]
      simpa only [Icc.coe_one, one_mul, add_sub_cancel, hfc] using mem_singleton v
    · exact Or.inl (hinside _ (hmLt t (unitInterval.lt_one_iff_ne_one.mpr ht)))
  let F : Path (⟨f h₀, Or.inl (hinside h₀ hh₀)⟩ : (r ∪ {v} : Set S)) ⟨v, Or.inr rfl⟩ := {
    toFun := fun t => ⟨f (m t), hmem t⟩
    continuous_toFun := (hf.comp hm).subtype_mk _
    source' := Subtype.ext (by simp [m])
    target' := Subtype.ext (by simpa only [m, Icc.coe_one, one_mul, add_sub_cancel] using hfc) }
  have hFval : ∀ t, (F t).val = f (h₀ + t.val * (c - h₀)) := fun _ => rfl
  have hF : ∀ t, t < 1 → (F t).val ∈ r := fun t ht => hinside _ (hmLt t ht)
  obtain ⟨q₀, hq₀⟩ := exists_path_in_region_vertex hw β hβr
  let q := q₀.cast F.target rfl
  have hq : ∀ t, (q t).val = β t := hq₀
  obtain ⟨t, ht, ρ, hρ, hhom⟩ := entry_comparison_from_normal_patch hr hv hN hvN hvX
    hX hpuncture hXZ hcover F q hF (fun t ht => hq t ▸ hβr t ht)
  let h := h₀ + t.val * (c - h₀)
  have hh : h ∈ Ioo a c := ⟨hh₀.1.trans_le (hmI t).1, (hmLt t ht).2⟩
  have hp : ∀ s : unitInterval, ((F.subpath t 1) s).val = f (h + s.val * (c - h)) := by
    intro s
    change (F (Icc.convexComb t 1 s)).val = _
    rw [hFval]
    congr 1
    simp only [Icc.coe_convexComb, Icc.coe_one]
    dsimp only [h]
    ring
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
