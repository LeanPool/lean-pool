/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.MarkCross
public import LeanPool.GraphMinor.Surface.Wedge
public import LeanPool.GraphMinor.Surface.CutTwoArc

/-!
# Lifting a cell to the cut surface

Let `ψ` be the map from a cut surface to the surface. It is a homeomorphism off the arc `F`
(`CutMap.exists_sec`, `CutMap.mem_bd_iff`). The
closure of the preimage of a cell off `F` is a copy of the closure of the cell
(`CutMap.exists_lift`). The key step is that a cell comes to
each point of `F` from one side only, because a small neighbourhood of a point of the boundary of a
disc stays connected after removing
the point.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology Filter Metric GraphMinor.Surface

variable {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]

/-- The properties of the map from one part of the cut surface to the surface. -/
structure CutMap (ψ : Y → S) (F : Set S) : Prop where
  cont : Continuous ψ
  inj : InjOn ψ (ψ ⁻¹' Fᶜ)
  isOpen : IsOpen (range ψ \ F)
  closed : IsClosed F
  fib : ∀ x ∈ F, (ψ ⁻¹' {x}).encard ≤ 2
  bdF : ψ ⁻¹' F ⊆ bd Y

variable [CompactSpace Y] [T2Space Y] [T2Space S] {ψ : Y → S} {F : Set S}

omit [T2Space Y] in
/-- The map has a continuous inverse off `F`. -/
theorem CutMap.exists_sec [Nonempty Y] (h : CutMap ψ F) :
    ∃ σ : S → Y, ContinuousOn σ (range ψ \ F) ∧ (∀ x ∈ range ψ \ F, ψ (σ x) = x) ∧ ∀ y, ψ y ∉ F → σ
      (ψ y) = y := by
  have hr : ∀ y, ψ y ∉ F → Function.invFun ψ (ψ y) = y := fun y hy => by
    have h1 : ψ (Function.invFun ψ (ψ y)) = ψ y := Function.invFun_eq ⟨y, rfl⟩
    exact h.inj (show _ ∈ ψ ⁻¹' Fᶜ by rw [mem_preimage, h1]; exact hy) hy h1
  refine ⟨Function.invFun ψ, fun x hx => ?_, fun x hx => Function.invFun_eq hx.1, hr⟩
  rw [ContinuousWithinAt, _root_.tendsto_nhds]
  intro V hV hxV
  have hO : IsOpen (ψ '' Vᶜ)ᶜ := (h.cont.isClosedMap _ hV.isClosed_compl).isOpen_compl
  have hxO : x ∈ (ψ '' Vᶜ)ᶜ := by
    rintro ⟨y, hy, rfl⟩
    exact hy (by rw [hr y hx.2] at hxV; exact hxV)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hxO), self_mem_nhdsWithin] with x' h1 h2
  by_contra h3
  exact h1 ⟨_, h3, Function.invFun_eq h2.1⟩

omit [T2Space Y] in
/-- Off `F` the map keeps the boundary. -/
theorem CutMap.mem_bd_iff [Nonempty Y] (h : CutMap ψ F) {y : Y} (hy : ψ y ∉ F) : y ∈ bd Y ↔ ψ y ∈
  bd S := by
  obtain ⟨σ, h1, h2, h3⟩ := h.exists_sec
  have hW : IsOpen (ψ ⁻¹' Fᶜ) := h.closed.isOpen_compl.preimage h.cont
  let e : (ψ ⁻¹' Fᶜ : Set Y) ≃ₜ (range ψ \ F : Set S) :=
    { toFun := fun y => ⟨ψ y, mem_range_self _, y.2⟩
      invFun := fun x => ⟨σ x, show ψ (σ x) ∈ Fᶜ by rw [h2 x x.2]; exact x.2.2⟩
      left_inv := fun y => Subtype.ext (h3 y y.2)
      right_inv := fun x => Subtype.ext (h2 x x.2)
      continuous_toFun := (h.cont.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuousOn_iff_continuous_domRestrict.mp h1).subtype_mk _ }
  have h4 := isInteriorPoint_homeomorph_iff e ⟨y, hy⟩
  have h5 := mem_bd_sub hW (x := ⟨y, hy⟩)
  have h6 := mem_bd_sub h.isOpen (x := e ⟨y, hy⟩)
  have h7 : (e ⟨y, hy⟩ : S) = ψ y := rfl
  rw [h7] at h6
  rw [← h5, ← h6]
  exact not_congr h4.symm

omit [T2Space Y] in
/-- The preimage of a connected set off `F`. -/
theorem CutMap.isPreconnected_preimage [Nonempty Y] (h : CutMap ψ F) {P : Set S}
  (hP : IsPreconnected P) (hs : P ⊆ range ψ \ F) : IsPreconnected (ψ ⁻¹' P) := by
  obtain ⟨σ, h1, h2, h3⟩ := h.exists_sec
  have h4 : ψ ⁻¹' P = σ '' P := by
    ext y
    constructor
    · intro hy
      exact ⟨ψ y, hy, h3 y (hs hy).2⟩
    · rintro ⟨x, hx, rfl⟩
      rw [mem_preimage, h2 x (hs hx)]
      exact hx
  rw [h4]
  exact hP.image _ (h1.mono hs)

/-- A closed ball without a point of its sphere is convex. -/
theorem isPreconnected_ball_diff {z₀ : ℂ} (hz : ‖z₀‖ = 1) (ε : ℝ) : IsPreconnected ((closedBall
  (0 : ℂ) 1 ∩ ball z₀ ε) \ {z₀}) := by
  refine Convex.isPreconnected (show Convex ℝ _ from ?_)
  rw [convex_iff_forall_pos]
  intro p hp q hq a b ha hb hab
  refine ⟨(convex_iff_forall_pos.mp ((convex_closedBall (0 : ℂ) 1).inter
    (convex_ball z₀ ε))) hp.1 hq.1 ha hb hab, fun he => ?_⟩
  by_cases hpq : p = q
  · apply hp.2
    rw [mem_singleton_iff] at he ⊢
    rw [← he, ← hpq, ← add_smul, hab, one_smul]
  · have h1 := (strictConvex_closedBall ℝ (0 : ℂ) 1) hp.1.1 hq.1.1 hpq ha hb hab
    rw [interior_closedBall _ one_ne_zero, mem_singleton_iff.mp he] at h1
    simp [hz] at h1

/-- A cell off `F` comes to a point of `F` from one side only: the map is injective on the closure
of the preimage of the cell. -/
theorem CutMap.injOn_closure [Nonempty Y] (h : CutMap ψ F) {c : Set S} (hcF : Disjoint c F)
  (hA : IsClosedDisc (closure c)) (ht : tilde c ⊆ discBd (closure c))
    (hfin : (tilde c).Finite) (hcR : c ⊆ range ψ \ F) : InjOn ψ (closure (ψ ⁻¹' c)) := by
  intro y hy y' hy' he
  by_contra hne
  have hmap : ψ '' closure (ψ ⁻¹' c) ⊆ closure c := (image_closure_subset_closure_image
    h.cont).trans (closure_mono (image_preimage_subset _ _))
  have huA : ψ y ∈ closure c := hmap (mem_image_of_mem _ hy)
  have huF : ψ y ∈ F := by
    by_contra hn
    exact hne (h.inj hn (by rw [mem_preimage, ← he]; exact hn) he)
  have huc : ψ y ∉ c := fun hu => disjoint_left.mp hcF hu huF
  have hut : ψ y ∈ tilde c := ⟨huA, huc⟩
  obtain ⟨V, V', hV, hV', hyV, hyV', hdis⟩ := t2_separation hne
  have hfibs : ψ ⁻¹' {ψ y} ⊆ V ∪ V' := fun z hz => by
    rcases eq_or_of_encard_le_two (h.fib _ huF) (show y ∈ ψ ⁻¹' {ψ y} from rfl)
      (show y' ∈ ψ ⁻¹' {ψ y} from he.symm) hz hne with rfl | rfl
    · exact .inl hyV
    · exact .inr hyV'
  have hO : IsOpen (ψ '' (V ∪ V')ᶜ)ᶜ := (h.cont.isClosedMap _ (hV.union
    hV').isClosed_compl).isOpen_compl
  have huO : ψ y ∈ (ψ '' (V ∪ V')ᶜ)ᶜ := by
    rintro ⟨z, hz, hez⟩
    exact hz (hfibs hez)
  obtain ⟨k, g, ch⟩ := hA.exists_isChart
  have hAc : IsCompact (closure c) := isCompact_of_isClosedDisc hA
  have hz₀ : ‖k (ψ y)‖ = 1 := by
    have h1 : k (ψ y) ∈ sphere (0 : ℂ) 1 := ch.bd ▸ mem_image_of_mem _ (ht hut)
    simpa using h1
  have hbad : IsCompact (closure c ∩ (ψ '' (V ∪ V')ᶜ)ᶜᶜ ∪ (tilde c \ {ψ y})) :=
    (hAc.inter_right hO.isClosed_compl).union (hfin.subset sdiff_subset).isCompact
  have hbads : closure c ∩ (ψ '' (V ∪ V')ᶜ)ᶜᶜ ∪ (tilde c \ {ψ y}) ⊆ closure c
    := union_subset inter_subset_left (sdiff_subset.trans (fun x hx => hx.1))
  have hk0 : k (ψ y) ∉ k '' (closure c ∩ (ψ '' (V ∪ V')ᶜ)ᶜᶜ ∪ (tilde c \ {ψ y})) := by
    rintro ⟨x, hx, hex⟩
    have h1 : x = ψ y := by rw [← ch.gh (hbads hx), hex, ch.gh huA]
    rcases hx with hx | hx
    · exact hx.2 (h1 ▸ huO)
    · exact hx.2 h1
  have hbado := (hbad.image_of_continuousOn (ch.hc.mono hbads)).isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hbado _ hk0
  have hgood : ∀ x ∈ closure c, k x ∈ ball (k (ψ y)) ε → x ∈ (ψ '' (V ∪ V')ᶜ)ᶜ ∧ (x ∈ tilde c → x
    = ψ y) := fun x hx hk => by
    have h1 : x ∉ closure c ∩ (ψ '' (V ∪ V')ᶜ)ᶜᶜ ∪ (tilde c \ {ψ y}) := fun hm => hball hk
      (mem_image_of_mem _ hm)
    constructor
    · by_contra h2
      exact h1 (.inl ⟨hx, h2⟩)
    · intro h2
      by_contra h3
      exact h1 (.inr ⟨h2, h3⟩)
  set C : Set ℂ := (closedBall (0 : ℂ) 1 ∩ ball (k (ψ y)) ε) \ {k (ψ y)} with hC
  have hCs : C ⊆ closedBall 0 1 := fun w hw => hw.1.1
  have hPc : g '' C ⊆ c := by
    rintro _ ⟨w, hw, rfl⟩
    have hgA : g w ∈ closure c := ch.gm hw.1.1
    have hkg : k (g w) = w := ch.hg hw.1.1
    by_contra hn
    have h1 := (hgood _ hgA (by rw [hkg]; exact hw.1.2)).2 ⟨hgA, hn⟩
    exact hw.2 (by rw [mem_singleton_iff, ← hkg, h1])
  have hP : IsPreconnected (g '' C) := (isPreconnected_ball_diff hz₀ ε).image _ (ch.gc.mono hCs)
  have hT := h.isPreconnected_preimage hP (hPc.trans hcR)
  have hTs : ψ ⁻¹' (g '' C) ⊆ V ∪ V' := by
    rintro t ⟨w, hw, hew⟩
    have h1 := (hgood _ (ch.gm hw.1.1) (by rw [ch.hg hw.1.1]; exact hw.1.2)).1
    by_contra h2
    exact h1 ⟨t, h2, hew.symm⟩
  have hO2 : ∀ {y₁ : Y} {V₁ : Set Y}, y₁ ∈ closure (ψ ⁻¹' c) → ψ y₁ = ψ y → IsOpen V₁ → y₁ ∈ V₁ → ¬
    (ψ ⁻¹' (g '' C) ⊆ V₁ᶜ) := by
    intro y₁ V₁ hy₁ he₁ hV₁ hyV₁ hsub
    obtain ⟨O₂, hO₂, hO₂e⟩ := continuousOn_iff'.mp ch.hc (ball (k (ψ y)) ε) isOpen_ball
    have hV₂ : IsOpen (V₁ ∩ ψ ⁻¹' O₂) := hV₁.inter (hO₂.preimage h.cont)
    have hm : ψ y ∈ k ⁻¹' ball (k (ψ y)) ε ∩ closure c := ⟨mem_ball_self hε, huA⟩
    rw [hO₂e] at hm
    have hy₂ : y₁ ∈ V₁ ∩ ψ ⁻¹' O₂ := by
      refine ⟨hyV₁, ?_⟩
      rw [mem_preimage, he₁]
      exact hm.1
    obtain ⟨w, ⟨hw1, hw2⟩, hw3⟩ := mem_closure_iff.mp hy₁ _ hV₂ hy₂
    have hwA : ψ w ∈ closure c := subset_closure hw3
    have hwk : k (ψ w) ∈ ball (k (ψ y)) ε := by
      have : ψ w ∈ O₂ ∩ closure c := ⟨hw2, hwA⟩
      rw [← hO₂e] at this
      exact this.1
    have hwn : ψ w ≠ ψ y := fun h9 => huc (h9 ▸ hw3)
    have hwC : k (ψ w) ∈ C := ⟨⟨ch.hm hwA, hwk⟩, fun h9 => hwn (by rw [← ch.gh hwA, h9, ch.gh huA])⟩
    exact hsub (show w ∈ ψ ⁻¹' (g '' C) from ⟨_, hwC, ch.gh hwA⟩) hw1
  rcases hT.subset_or_subset hV hV' hdis hTs with h1 | h1
  · exact hO2 hy' he.symm hV' hyV' (h1.trans fun x hx hx' => disjoint_left.mp hdis hx hx')
  · exact hO2 hy rfl hV hyV (h1.trans fun x hx hx' => disjoint_left.mp hdis hx' hx)

omit [CompactSpace Y] [T2Space S] in
/-- The inverse of an injective map on a compact set is continuous. -/
theorem continuousOn_invFunOn' {A T : Type*} [TopologicalSpace A] [Nonempty A] [TopologicalSpace T]
  [T2Space T] {Δ : Set A} (hc : IsCompact Δ)
    {f : A → T} (hf : ContinuousOn f Δ) (hi : InjOn f Δ) : ContinuousOn (Function.invFunOn f Δ)
      (f '' Δ) := by
  have hl : LeftInvOn (Function.invFunOn f Δ) f Δ := hi.leftInvOn_invFunOn
  have hcomp : CompactSpace Δ := isCompact_iff_compactSpace.mp hc
  let g : Δ → f '' Δ := fun x => ⟨f x, x.1, x.2, rfl⟩
  have hg : Continuous g := (continuousOn_iff_continuous_domRestrict.mp hf).subtype_mk _
  have hgb : Function.Bijective g := by
    constructor
    · intro x y h
      exact Subtype.ext (hi x.2 y.2 (congrArg Subtype.val h))
    · rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let e : Δ ≃ₜ f '' Δ := hg.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hgb)
  have hr : (f '' Δ).domRestrict (Function.invFunOn f Δ) = fun y => (e.symm y).1 := by
    funext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [e.symm_apply_apply]
    exact hl x.2
  rw [continuousOn_iff_continuous_domRestrict, hr]
  exact continuous_subtype_val.comp e.symm.continuous

/-- The closure of the preimage of a cell is a copy of the closure of the cell. -/
theorem CutMap.exists_lift [Nonempty Y] (h : CutMap ψ F) {c : Set S} (hcF : Disjoint c F)
  (hA : IsClosedDisc (closure c)) (ht : tilde c ⊆ discBd (closure c))
    (hfin : (tilde c).Finite) (hcR : c ⊆ range ψ \ F) :
    ∃ τ : S → Y, ContinuousOn τ (closure c) ∧ τ '' closure c = closure (ψ ⁻¹' c) ∧
      (∀ x ∈ closure c, ψ (τ x) = x) ∧ (∀ y ∈ closure (ψ ⁻¹' c), τ (ψ y) = y) ∧
      tilde (ψ ⁻¹' c) = τ '' tilde c ∧ IsClosedDisc (closure (ψ ⁻¹' c)) ∧ tilde (ψ ⁻¹' c) ⊆ discBd
        (closure (ψ ⁻¹' c)) := by
  have hi := h.injOn_closure hcF hA ht hfin hcR
  set M := closure (ψ ⁻¹' c) with hM
  have hMc : IsCompact M := isClosed_closure.isCompact
  have hψM : ψ '' M = closure c := by
    apply subset_antisymm
    · exact (image_closure_subset_closure_image h.cont).trans (closure_mono
      (image_preimage_subset _ _))
    · refine closure_minimal (fun x hx => ?_) (hMc.image h.cont).isClosed
      obtain ⟨y, rfl⟩ := (hcR hx).1
      exact ⟨y, subset_closure hx, rfl⟩
  let τ : S → Y := Function.invFunOn ψ M
  have hτc : ContinuousOn τ (closure c) := hψM ▸ continuousOn_invFunOn' hMc h.cont.continuousOn hi
  have hl : ∀ y ∈ M, τ (ψ y) = y := fun y hy => hi.leftInvOn_invFunOn hy
  have hr : ∀ x ∈ closure c, ψ (τ x) = x := fun x hx => Function.invFunOn_eq (hψM ▸ hx : x ∈ ψ '' M)
  have hτM : τ '' closure c = M := by
    rw [← hψM, image_image]
    exact (image_congr hl).trans (image_id' _)
  obtain ⟨h1, h2⟩ := hA.image hτc (by rw [hτM]; exact h.cont.continuousOn) hr
  rw [hτM] at h1 h2
  have htl : tilde (ψ ⁻¹' c) = τ '' tilde c := by
    apply subset_antisymm
    · rintro y ⟨hy, hyc⟩
      have hyA : ψ y ∈ closure c := hψM ▸ mem_image_of_mem _ hy
      exact ⟨ψ y, ⟨hyA, hyc⟩, hl y hy⟩
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨hτM.subset (mem_image_of_mem _ hx.1), fun hc => hx.2 ?_⟩
      rw [mem_preimage, hr x hx.1] at hc
      exact hc
  refine ⟨τ, hτc, hτM, hr, hl, htl, h1, ?_⟩
  rw [htl, h2]
  exact image_mono ht

omit [CompactSpace Y] [T2Space Y] [T2Space S] in
/-- A closed disc without two points of its boundary. -/
theorem disc_diff_two [T2Space Y] {D : Set Y} {u v : Y} (hD : IsClosedDisc D) (hu : u ∈ discBd D)
  (hv : v ∈ discBd D) :
    closure (D \ {u, v}) = D ∧ tilde (D \ {u, v}) = {u, v} ∧ IsPathConnected (D \ {u, v}) ∧
      (D \ {u, v}).Nonempty := by
  have hbd : discBd D ⊆ D := discBd_subset D
  obtain ⟨hne, hpc, h1⟩ := hD.sdiff_of_inter_subset_discBd
    (F := {u, v}) (by
      rintro x ⟨rfl | rfl, -⟩
      · exact hu
      · exact hv)
  have h2 : tilde (D \ {u, v}) = {u, v} := by
    rw [tilde, h1]
    ext x
    simp only [Set.mem_sdiff, not_and, not_not]
    constructor
    · rintro ⟨h3, h4⟩
      exact h4 h3
    · rintro h3
      refine ⟨?_, fun _ => h3⟩
      rcases h3 with rfl | rfl
      · exact hbd hu
      · exact hbd hv
  exact ⟨h1, h2, hpc, hne⟩

end GraphMinor.GM17
