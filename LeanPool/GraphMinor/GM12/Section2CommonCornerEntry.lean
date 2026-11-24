/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM12.Section2EntryAtPath
import LeanPool.GraphMinor.GM12.Section2CommonPatchSpokes
import LeanPool.GraphMinor.GM12.Section2SpokeUniqueness
import LeanPool.GraphMinor.GM12.Section2EntryEnds
import LeanPool.GraphMinor.GM11.Regions

/-!
# Entry edges agree for approaches in the same corner

For trace restriction in XII (2.1), pages 243--244, the original
curve and its simple subcurve can use different parameterizations.
Read their entry witnesses on normalized terminal paths. If these
paths lie in the same simply connected corner patch, joining their
starts inside the punctured patch makes their spokes homotopic.
The radial spoke uniqueness theorem then identifies the edges.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Different approaches through one corner patch have the same
entry edge. This is the local comparison needed for the image
restriction argument in XII (2.1), pages 243--244. -/
theorem entersLike_edge_eq_of_common_patch
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {r e e' X : Set S} {v w : S} (hr : r ∈ Γ.R) (hv : v ∈ Γ.V)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E) (he' : e' ∈ K.E)
    (hX : IsSimplyConnectedSet X) (hXZ : X ⊆ r ∪ {v})
    (hpuncture : IsPathConnected (X \ {v})) (hXR : X \ {v} ⊆ r)
    {f g : ℝ → S} (hf : Continuous f) (hg : Continuous g)
    {a c b d s t : ℝ} (hs : s ∈ Ioo a c) (ht : t ∈ Ioo b d)
    (hfc : f c = v) (hgd : g d = v)
    (hfr : ∀ z ∈ Ioo a c, f z ∈ r) (hgr : ∀ z ∈ Ioo b d, g z ∈ r)
    (hentry : EntersLike f a c e r v w) (hentry' : EntersLike g b d e' r v w)
    {x y : (r ∪ {v} : Set S)}
    (F : Path x (⟨v, Or.inr rfl⟩ : (r ∪ {v} : Set S)))
    (G : Path y (⟨v, Or.inr rfl⟩ : (r ∪ {v} : Set S)))
    (hF : ∀ z, (F z).val = f (s + z.val * (c - s)))
    (hG : ∀ z, (G z).val = g (t + z.val * (d - t)))
    (hFX : ∀ z, (F z).val ∈ X) (hGX : ∀ z, (G z).val ∈ X)
    (hx : x.val ∈ X \ {v}) (hy : y.val ∈ X \ {v}) : e = e' := by
  have hvE : v ∉ e := fun hz => (he.2.1 hz).2 (hK.2.1.2.1 hv)
  have hwE : w ∉ e := fun hz => (he.2.1 hz).2 hw.2
  have hvE' : v ∉ e' := fun hz => (he'.2.1 hz).2 (hK.2.1.2.1 hv)
  have hwE' : w ∉ e' := fun hz => (he'.2.1 hz).2 hw.2
  have hvw : v ≠ w := fun h => region_subset hr (h.symm ▸ hw.1) (Γ.V_subset_U hv)
  obtain ⟨β, ρ, hβ, hβrange, _, hρ, hhom⟩ :=
    entry_comparison_at_path_start (hK.1.2 r hr) hw.1 hvE hwE hvw
      hf hs hfc hfr hentry F hF
  obtain ⟨β', ρ', hβ', hβrange', _, hρ', hhom'⟩ :=
    entry_comparison_at_path_start (hK.1.2 r hr) hw.1 hvE' hwE' hvw
      hg ht hgd hgr hentry' G hG
  have hh := spokes_homotopic_of_common_ambient_patch hX
    (hK.1.2 r hr).isSimplyConnectedSet hXZ subset_union_left hpuncture hXR
    F G β β' hFX hGX hx hy ρ ρ' hρ hρ' hhom hhom'
  have hends := (entersLike_isLink hS ⟨hK.1, hK.2.1⟩ hr hv hw.1 hw.2 he hfc hentry).2.2.2
  have hends' := (entersLike_isLink hS ⟨hK.1, hK.2.1⟩ hr hv hw.1 hw.2 he' hgd hentry').2.2.2
  apply spoke_eq_of_paths_homotopic hS hConn hK.2.1 hr hv hw he he' hends hends'
    β β' _ _ hβrange hβrange' hh
  · intro z z' hzz
    exact hβ (congrArg Subtype.val hzz)
  · intro z z' hzz
    exact hβ' (congrArg Subtype.val hzz)

private theorem normalized_terminal_path
    {S : Type*} [TopologicalSpace S] {r X : Set S} {v : S}
    {f : ℝ → S} (hf : Continuous f) {a c s : ℝ} (hs : s ∈ Ioo a c)
    (hfc : f c = v) (hfr : ∀ z ∈ Ioo a c, f z ∈ r)
    (hX : ∀ z ∈ Icc s c, f z ∈ X) (hv : v ∉ r) :
    ∃ (x : (r ∪ {v} : Set S))
      (F : Path x (⟨v, Or.inr rfl⟩ : (r ∪ {v} : Set S))),
      (∀ z, (F z).val = f (s + z.val * (c - s))) ∧
      (∀ z, (F z).val ∈ X) ∧ x.val ∈ X \ {v} := by
  have hpos : 0 < c - s := sub_pos.mpr hs.2
  have hm : ∀ z : unitInterval, s + z.val * (c - s) ∈ Icc s c := by
    intro z
    refine ⟨le_add_of_nonneg_right (mul_nonneg z.property.1 hpos.le), ?_⟩
    have := mul_le_of_le_one_left hpos.le z.property.2
    linarith
  have hmem : ∀ z : unitInterval, f (s + z.val * (c - s)) ∈ r ∪ {v} := by
    intro z
    by_cases hz : z = 1
    · subst z
      right
      simpa only [Icc.coe_one, one_mul, add_sub_cancel, hfc] using mem_singleton v
    · left
      apply hfr
      refine ⟨hs.1.trans_le (hm z).1, ?_⟩
      have := mul_lt_of_lt_one_left hpos (unitInterval.lt_one_iff_ne_one.mpr hz)
      linarith
  let x : (r ∪ {v} : Set S) := ⟨f s, Or.inl (hfr s hs)⟩
  let F : Path x (⟨v, Or.inr rfl⟩ : (r ∪ {v} : Set S)) := {
    toFun := fun z => ⟨f (s + z.val * (c - s)), hmem z⟩
    continuous_toFun := (hf.comp (by fun_prop)).subtype_mk _
    source' := Subtype.ext (by simp only [Icc.coe_zero, zero_mul, add_zero]; rfl)
    target' := Subtype.ext (by simpa only [Icc.coe_one, one_mul, add_sub_cancel] using hfc) }
  refine ⟨x, F, fun _ => rfl, fun z => hX _ (hm z), hX s ⟨le_rfl, hs.2.le⟩, ?_⟩
  intro heq
  exact hv (heq ▸ hfr s hs)

/-- The common-corner comparison expressed directly on terminal real
intervals. Only the terminal parts of the two approaches need to lie
in the patch; their earlier portions may differ arbitrarily. -/
theorem entersLike_edge_eq_of_common_terminal_patch
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {r e e' X : Set S} {v w : S} (hr : r ∈ Γ.R) (hv : v ∈ Γ.V)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E) (he' : e' ∈ K.E)
    (hX : IsSimplyConnectedSet X) (hXZ : X ⊆ r ∪ {v})
    (hpuncture : IsPathConnected (X \ {v})) (hXR : X \ {v} ⊆ r)
    {f g : ℝ → S} (hf : Continuous f) (hg : Continuous g)
    {a c b d s t : ℝ} (hs : s ∈ Ioo a c) (ht : t ∈ Ioo b d)
    (hfc : f c = v) (hgd : g d = v)
    (hfr : ∀ z ∈ Ioo a c, f z ∈ r) (hgr : ∀ z ∈ Ioo b d, g z ∈ r)
    (hentry : EntersLike f a c e r v w) (hentry' : EntersLike g b d e' r v w)
    (hfX : ∀ z ∈ Icc s c, f z ∈ X) (hgX : ∀ z ∈ Icc t d, g z ∈ X) : e = e' := by
  have hvr : v ∉ r := fun hz => region_subset hr hz (Γ.V_subset_U hv)
  obtain ⟨x, F, hF, hFX, hx⟩ := normalized_terminal_path hf hs hfc hfr hfX hvr
  obtain ⟨y, G, hG, hGX, hy⟩ := normalized_terminal_path hg ht hgd hgr hgX hvr
  exact entersLike_edge_eq_of_common_patch hS hConn hK hr hv hw he he'
    hX hXZ hpuncture hXR hf hg hs ht hfc hgd hfr hgr hentry hentry'
    F G hF hG hFX hGX hx hy

end GraphMinor.GM12
