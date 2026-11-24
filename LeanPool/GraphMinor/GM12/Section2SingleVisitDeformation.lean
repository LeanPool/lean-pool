/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2RegionPathDeformation
public import LeanPool.GraphMinor.GM12.Section2TraceComposition
import LeanPool.GraphMinor.GM12.Section2NormalEntryExistence
import LeanPool.GraphMinor.GM12.Section2SpokePairTopology
import LeanPool.GraphMinor.GM12.Section2SpokePaths
import LeanPool.GraphMinor.GM12.Section2WalkCarriers
import LeanPool.GraphMinor.GM11.RadialRegions

/-!
# The full deformation data for one region visit

For Case 1 of XII (2.1), page 244, choose the radial hub and the
entry and exit edges of one real region interval. Deform that interval
to the two spoke paths and record the corresponding two-edge walk.
Their point sets agree exactly. The new path is injective on its
half-open interval, unless both ends and both edges agree. In that
case its point set is a line in the region with the boundary vertex
restored. These are the two alternatives used in Case 1.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Deform a single region visit, retaining its exact two-edge trace
and its simplicity or backtracking alternative. -/
theorem exists_single_visit_deformation
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hac : a < c)
    (ha : f a ∈ Γ.V) (hc : f c ∈ Γ.V) {r Z : Set S} (hr : r ∈ Γ.R) (hrZ : r ⊆ Z)
    (hfr : ∀ t ∈ Ioo a c, f t ∈ r)
    (γ : C(unitInterval, S)) (hγ : ∀ t, γ t = f (a + t.val * (c - a)))
    (hγZ : range γ ⊆ Z) :
    ∃ (δ : C(unitInterval, S)) (W : GraphWalk K.toGraph (f a) (f c)),
      TraceSteps Γ K f a c W ∧ W.length = 2 ∧ range δ = (walkDrawing K W).U ∧
      CurvesHomotopicIn Z γ δ ∧ δ 0 = f a ∧ δ 1 = f c ∧
      (∀ t, 0 < t.val → t.val < 1 → δ t ∈ r) ∧
      (InjOn δ (Ico (0 : unitInterval) 1) ∨
        (f a = f c ∧ ∃ L : Set S, IsLine L ∧ range δ = L ∧ L ⊆ r ∪ {f a})) := by
  have hrad : PreRad (.drawing Γ) K := ⟨hK.1, hK.2.1⟩
  obtain ⟨w, ⟨hwr, hwK⟩, _⟩ := hrad.2.2.2.1 r hr
  obtain ⟨e, he, hleave⟩ := exists_leavesLike hS hrad hK.2.2 hE ha hr hwr hwK hf hac rfl hfr
  obtain ⟨e', he', henter⟩ := exists_entersLike hS hrad hK.2.2 hE hc hr hwr hwK hf hac rfl hfr
  have hl := leavesLike_isLink hS hrad hr ha hwr hwK he rfl hleave
  have hl' := entersLike_isLink hS hrad hr hc hwr hwK he' rfl henter
  have hγ0 : γ 0 = f a := by simpa only [Icc.coe_zero, zero_mul, add_zero] using hγ 0
  have hγ1 : γ 1 = f c := by simpa only [Icc.coe_one, one_mul, add_sub_cancel] using hγ 1
  have haZ : f a ∈ Z := hγ0 ▸ hγZ (mem_range_self 0)
  have hcZ : f c ∈ Z := hγ1 ▸ hγZ (mem_range_self 1)
  let P : Path (⟨f a, haZ⟩ : Z) ⟨f c, hcZ⟩ := {
    toFun := fun t => ⟨γ t, hγZ (mem_range_self t)⟩
    continuous_toFun := γ.continuous.subtype_mk _
    source' := Subtype.ext hγ0
    target' := Subtype.ext hγ1 }
  have haE : f a ∉ e := fun hz => (he.2.1 hz).2 (hK.2.1.2.1 ha)
  have hcE' : f c ∉ e' := fun hz => (he'.2.1 hz).2 (hK.2.1.2.1 hc)
  have hwE : w ∉ e := fun hz => (he.2.1 hz).2 hwK
  have hwE' : w ∉ e' := fun hz => (he'.2.1 hz).2 hwK
  have haw : f a ≠ w := fun heq => region_subset hr (heq.symm ▸ hwr) (Γ.V_subset_U ha)
  have hcw : f c ≠ w := fun heq => region_subset hr (heq.symm ▸ hwr) (Γ.V_subset_U hc)
  obtain ⟨α, β, hαi, hβi, hαrange, hβrange, hαe, hβe, hhom⟩ :=
    region_path_homotopic_to_spokes (hK.1.2 r hr) hrZ haZ hcZ hwr haE hwE haw
      hcE' hwE' hcw hf hac rfl rfl hfr hleave henter P hγ
  let p : Path (f a) w := α.map continuous_subtype_val
  let q : Path (f c) w := β.map continuous_subtype_val
  let δ : C(unitInterval, S) := (p.trans q.symm).toContinuousMap
  let W : GraphWalk K.toGraph (f a) (f c) := .cons hl (.cons hl'.symm (.nil hl'.left_mem))
  have hW : TraceSteps Γ K f a c W :=
    ⟨c, hac, rfl, ha, rfl, hwK, r, hr, hwr, hfr, hleave, henter, rfl, rfl, hc⟩
  have hδrange : range δ = closure e ∪ closure e' := by
    change range (p.trans q.symm) = _
    rw [Path.trans_range, Path.symm_range]
    exact congrArg₂ Set.union hαrange hβrange
  have hwcl : w ∈ closure e := hαrange ▸ ⟨1, congrArg Subtype.val α.target⟩
  have hwcl' : w ∈ closure e' := hβrange ▸ ⟨1, congrArg Subtype.val β.target⟩
  have her : e ⊆ r := spoke_subset_region hS hrad hr he hwr hwK hwcl
  have he'r : e' ⊆ r := spoke_subset_region hS hrad hr he' hwr hwK hwcl'
  have hpr := path_positive_in_region p hwr hαe her
  have hqr := path_positive_in_region q hwr hβe he'r
  refine ⟨δ, W, hW, rfl, ?_, ?_, (p.trans q.symm).source, (p.trans q.symm).target,
    ?_, ?_⟩
  · rw [hδrange]
    exact (walkDrawing_U_two_edges K hl hl'.symm).symm
  · have H := curvesHomotopicIn_of_paths_homotopic hhom
    have hleft : (⟨fun t => (P t).val, continuous_subtype_val.comp P.continuous⟩ : C(unitInterval,
      S)) = γ := rfl
    have hright : (⟨fun t => ((α.trans β.symm) t).val,
        continuous_subtype_val.comp (α.trans β.symm).continuous⟩ : C(unitInterval, S)) = δ := by
      ext t
      change ((α.trans β.symm) t).val = (p.trans q.symm) t
      rw [Path.trans_apply, Path.trans_apply]
      split_ifs <;> rfl
    rw [hleft, hright] at H
    exact H
  · intro t ht0 ht1
    exact spoke_pair_path_interior_subset p q hpr hqr t ⟨ht0, ht1⟩
  · by_cases hacv : f a = f c
    · by_cases hee : e = e'
      · right
        refine ⟨hacv, closure e, ?_, ?_, ?_⟩
        · have hpemb : IsEmbedding p := p.continuous.isClosedEmbedding hαi |>.isEmbedding
          exact ⟨hpemb.toHomeomorph.trans (Homeomorph.setCongr hαrange)⟩
        · rw [hδrange, ← hee, union_self]
        · intro x hx
          obtain ⟨t, rfl⟩ := hαrange.symm ▸ hx
          by_cases ht : t = 0
          · right
            change (α t).val = f a
            rw [ht]
            exact congrArg (fun z : Z => z.val) α.source
          · exact Or.inl (hpr t (unitInterval.pos_iff_ne_zero.mpr ht))
      · left
        let q' : Path (f a) w := q.cast hacv rfl
        exact parallel_spoke_pair_path_halfopen_injective he he' hee hl.2.2.2
          p q' hαi hβi hαrange hβrange
    · left
      exact (spoke_pair_path_injective he he' hl.2.2.2 hl'.2.2.2 hacv haw
        p q hαi hβi hαrange hβrange).injOn

end GraphMinor.GM12
