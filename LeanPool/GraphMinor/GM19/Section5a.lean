/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Thinning

/-!
# Graph Minors XIX, (5.1): images under homeomorphisms

A homeomorphism `α` of the surface that preserves the frame carries a coloured painting to a
coloured painting.
Here we first show that `α` keeps each cuff with its orientation, since it fixes the two ends of a
side and keeps
the side. Then a (linear) inflation carries over to the images.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

universe w

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-! ### The frame as a painting -/

/-- A frame, seen as a painting with `U = bd(Σ)`. -/
noncomputable def Frame.toPainting (Φ : Frame S) (hbd : IsClosed (bd S)) : Painting S where
  U := bd S
  V := Φ.V
  γ := Φ.γ
  isClosed_U := hbd
  V_subset := Φ.V_subset
  finite_V := Φ.finite_V
  bd_subset := subset_rfl
  finite_edges := Φ.finite_sides
  edge_shape s hs := Or.inl (Φ.side_shape s hs)
  γ_nodup := Φ.γ_nodup
  γ_set := Φ.γ_set
  border_edge s hs _ := ⟨(Φ.side_shape s hs).1, hs.2.1.trans sdiff_subset⟩

omit [T2Space S] in
theorem Frame.tilde_subset (Φ : Frame S) (hbd : IsClosed (bd S)) {s : Set S} (hs : s ∈ Φ.sides) :
    tilde s ⊆ Φ.V :=
  (Φ.toPainting hbd).tilde_subset_V hs

omit [T2Space S] in
/-- A side has its ends fixed and goes to itself, so its closure goes to itself. -/
theorem image_closure_side {Φ : Frame S} {α : S ≃ₜ S} (hα : IsFramePreservingHomeo Φ α) {s : Set S}
    (hs : s ∈ Φ.sides) : α '' closure s = closure s := by
  rw [α.image_closure, hα.preserve_sides s hs]

/-- A homeomorphism of the circle that fixes `exp a`, `exp b` and keeps the arc between them
preserves
orientation. -/
theorem preserves_of_arc {ψ : Circle ≃ₜ Circle} {a b : ℝ} (hab : a < b) (hb : b < a + 2 * Real.pi)
    (ha' : ψ (Circle.exp a) = Circle.exp a) (hb' : ψ (Circle.exp b) = Circle.exp b)
    (harc : ∀ t ∈ Ioo a b, ∃ t' ∈ Ioo a b, ψ (Circle.exp t) = Circle.exp t') :
    PreservesCircleOrientation ψ := by
  have hpi := Real.pi_pos
  obtain ⟨L, hLc, hL, hLe⟩ := exists_circle_lift ψ
  rcases hL with hL | hL
  · exact ⟨L, hLc, hL, hLe⟩
  exfalso
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp ((hLe a).symm.trans ha')
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp ((hLe b).symm.trans hb')
  have hlt : L b < L a := hL hab
  obtain ⟨c, hc⟩ : ∃ c, c ∈ Ioo a b := ⟨(a + b) / 2, by constructor <;> linarith⟩
  obtain ⟨c', hc', he⟩ := harc c hc
  rw [hLe] at he
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
  have h1 : L b < L c := hL hc.2
  have h2 : L c < L a := hL hc.1
  have hup : L a - 2 * Real.pi ≤ L (a + 2 * Real.pi) := by
    by_contra hn'
    push Not at hn'
    obtain ⟨t, ht, hte⟩ := intermediate_value_Icc' (a := a) (b := a + 2 * Real.pi) (f := L)
      (by linarith)
      hLc.continuousOn (show L a - 2 * Real.pi ∈ Icc (L (a + 2 * Real.pi)) (L a) from
        ⟨hn'.le, by linarith⟩)
    have hta : t ≠ a := fun h ↦ by
      rw [h] at hte
      linarith
    have htb : t ≠ a + 2 * Real.pi := fun h ↦ by
      rw [h] at hte
      linarith
    have he₂ : Circle.exp t = Circle.exp a := ψ.injective (by
      rw [hLe, hLe, hte]
      exact Circle.exp_eq_exp.mpr ⟨-1, by push_cast; ring⟩)
    obtain ⟨j, hj⟩ := Circle.exp_eq_exp.mp he₂
    have h1' : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
    have h2' : t < a + 2 * Real.pi := lt_of_le_of_ne ht.2 htb
    have h3' : (0 : ℝ) < j := by
      by_contra hneg
      push Not at hneg
      nlinarith
    have h4' : (j : ℝ) < 1 := by
      by_contra hneg
      push Not at hneg
      nlinarith
    have h5 : 0 < j := by exact_mod_cast h3'
    have h6 : j < 1 := by exact_mod_cast h4'
    omega
  have hb2 : L (a + 2 * Real.pi) < L b := hL hb
  have h3 : ((m : ℝ) - n) * (2 * Real.pi) > b - a := by nlinarith
  have h4 : ((m : ℝ) - n) * (2 * Real.pi) < 2 * Real.pi + (b - a) := by nlinarith
  have h5 : (0 : ℝ) < (m : ℝ) - n := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have h6 : (m : ℝ) - n < 2 := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have h7 : 0 < m - n := by exact_mod_cast h5
  have h8 : m - n < 2 := by exact_mod_cast h6
  obtain rfl : m = n + 1 := by omega
  push_cast at hm
  have h9 : (n : ℝ) < k := by
    by_contra hneg
    push Not at hneg
    nlinarith [hc'.2]
  have h10 : (k : ℝ) < n + 1 := by
    by_contra hneg
    push Not at hneg
    nlinarith [hc'.1]
  have h11 : n < k := by exact_mod_cast h9
  have h12 : k < n + 1 := by exact_mod_cast h10
  omega


/-! ### Frame-preserving homeomorphisms -/

section Preserving

variable {Φ : Frame S} {α : S ≃ₜ S}

omit [T2Space S] in
theorem IsFramePreservingHomeo.symm (hα : IsFramePreservingHomeo Φ α) :
    IsFramePreservingHomeo Φ α.symm := by
  refine ⟨fun v hv ↦ ?_, fun s hs ↦ ?_, fun ω Δ hΔ a b c ha hb hc hab hbc hac ↦ ?_⟩
  · rw [Homeomorph.symm_apply_eq, hα.fix_V v hv]
  · conv_lhs => rw [← hα.preserve_sides s hs]
    exact symm_image_image' α s
  · have h := hα.preserves_orientation ω (α.symm '' Δ) (GM20.image_isClosedDisc α.symm hΔ)
      (α.symm a) (α.symm b) (α.symm c) (GM20.image_discBd α.symm Δ ▸ mem_image_of_mem _ ha)
      (GM20.image_discBd α.symm Δ ▸ mem_image_of_mem _ hb)
      (GM20.image_discBd α.symm Δ ▸ mem_image_of_mem _ hc)
      (fun he ↦ hab (α.symm.injective he)) (fun he ↦ hbc (α.symm.injective he))
      (fun he ↦ hac (α.symm.injective he))
    simp only [Homeomorph.apply_symm_apply] at h
    have hΔ' : α '' (α.symm '' Δ) = Δ := by
      rw [← image_comp]
      simp
    rw [hΔ'] at h
    exact h.symm

omit [T2Space S] in
/-- Each cuff has a side on it. -/
theorem exists_side_on_cuff (hbd : IsClosed (bd S)) (Φ : Frame S) (C : cuffs S)
  (f : Circle ≃ₜ C.1) :
    ∃ s ∈ Φ.sides, s ⊆ C.1 := by
  obtain ⟨e, he, heC, -⟩ := exists_edge_on_cuff (Φ.toPainting hbd) C f
  exact ⟨e, he, heC⟩

/-- A frame-preserving homeomorphism has null signature: it keeps a side of each cuff, with its
ends. -/
theorem IsFramePreservingHomeo.null (_hS : IsSurface S) (hα : IsFramePreservingHomeo Φ α) :
    HasNullSignature α := by
  have hbd : IsClosed (bd S) := isClosed_bd S
  intro C f hC
  obtain ⟨s, hs, hsC⟩ := exists_side_on_cuff hbd Φ ⟨C, hC⟩ f
  have hP := Φ.toPainting hbd
  obtain ⟨a, θ, hθ, heq⟩ := edge_arc (Φ.toPainting hbd) f hs (Φ.side_shape s hs).1 hsC
  have hab : a < a + θ := by linarith [hθ.1]
  have hb : a + θ < a + 2 * Real.pi := by linarith [hθ.2]
  have hx : (s).Nonempty := hs.1
  have hαC : α '' C = C := by
    have hc := cuffs_eq_image α (S := S) (T := S)
    have hmem : α '' C ∈ cuffs S := hc ▸ mem_image_of_mem _ hC
    obtain ⟨x, hxs⟩ := hx
    have h₁ : α x ∈ s := by
      rw [← hα.preserve_sides s hs]
      exact mem_image_of_mem _ hxs
    have hne : (⟨_, hmem⟩ : cuffs S) = ⟨C, hC⟩ := by
      by_contra hne
      exact disjoint_left.mp (cuffs_disjoint' hne) (mem_image_of_mem _ (hsC hxs)) (hsC h₁)
    exact congrArg Subtype.val hne
  have hmem : ∀ x, x ∈ C ↔ α x ∈ C := fun x ↦ by
    conv_rhs => rw [← hαC]
    exact (α.injective.mem_set_image).symm
  let ψ : Circle ≃ₜ Circle := f.trans ((α.subtype hmem).trans f.symm)
  have hψ : ∀ z, α (f z).1 = (f (ψ z)).1 := fun z ↦ by
    simp [ψ]
  refine ⟨ψ, ?_, hψ⟩
  have hfix : ∀ t, cuffPoint f t ∈ tilde s → ψ (Circle.exp t) = Circle.exp t := fun t ht ↦ by
    have h₁ := hψ (Circle.exp t)
    have h₂ : α (cuffPoint f t) = cuffPoint f t := hα.fix_V _ (Frame.tilde_subset Φ hbd hs ht)
    apply f.injective
    apply Subtype.ext
    exact h₁.symm.trans h₂
  have htl : tilde s = {cuffPoint f a, cuffPoint f (a + θ)} := by
    rw [heq]
    exact tilde_arcOf f hab hb
  refine preserves_of_arc hab hb (hfix a (htl ▸ Or.inl rfl)) (hfix _ (htl ▸ Or.inr rfl)) fun t ht ↦
    ?_
  have h₁ : cuffPoint f t ∈ s := heq ▸ ⟨t, ht, rfl⟩
  have h₂ : α (cuffPoint f t) ∈ s := by
    rw [← hα.preserve_sides s hs]
    exact mem_image_of_mem _ h₁
  rw [heq] at h₂
  obtain ⟨t', ht', he⟩ := h₂
  refine ⟨t', ht', ?_⟩
  apply f.injective
  apply Subtype.ext
  exact ((hψ (Circle.exp t)).symm.trans he.symm).symm ▸ rfl

omit [T2Space S] in
/-- The image of a painting that fits a frame fits the frame. -/
theorem Painting.Fits.push (hα : IsFramePreservingHomeo Φ α) {Γ : Painting S} (hf : Γ.Fits Φ) :
    (Γ.push α).Fits Φ := by
  refine ⟨fun v hv ↦ ?_, fun t ht ↦ ?_, ?_, push_internally α Γ hf.internally_three_connected, ?_⟩
  · exact ⟨v, hf.V_subset hv, hα.fix_V v hv⟩
  · have := push_mem α Γ (hf.short_sides ht)
    rwa [hα.preserve_sides t ht.1] at this
  · intro e' he' hb s hs hes
    rw [push_E] at he'
    obtain ⟨e, he, rfl⟩ := he'
    have hes₀ : e ⊆ s := by
      rw [← hα.preserve_sides s hs] at hes
      exact (image_subset_image_iff α.injective).mp hes
    obtain ⟨f, t₁, t₂, hlt, hsub, h₁, h₂, h₃, h₄⟩ := hf.border_dir e he
      ((isBorder_image α).mp hb) s hs hes₀
    have hcl := image_closure_side hα hs
    have hmem : ∀ x, x ∈ closure s ↔ α x ∈ closure s := fun x ↦ by
      conv_rhs => rw [← hcl]
      exact (α.injective.mem_set_image).symm
    have hbd : IsClosed (bd S) := isClosed_bd S
    have hfix : ∀ x, some x = (Φ.γ s).head? ∨ some x = (Φ.γ s).getLast? → α x = x := by
      intro x hx
      have hx' : x ∈ Φ.γ s := by
        rcases hx with hx | hx
        · exact List.mem_of_mem_head? hx.symm
        · exact List.mem_of_getLast? hx.symm
      have hxt : x ∈ tilde s := by
        rw [← Φ.γ_set s hs]
        exact hx'
      exact hα.fix_V x (Frame.tilde_subset Φ hbd hs hxt)
    refine ⟨f.trans (α.subtype hmem), t₁, t₂, hlt, hes, ?_, ?_, ?_, ?_⟩
    · simp only [Homeomorph.trans_apply, Homeomorph.subtype_apply_coe]
      rw [hfix _ (Or.inl h₁.symm)]
      exact h₁
    · simp only [Homeomorph.trans_apply, Homeomorph.subtype_apply_coe]
      rw [hfix _ (Or.inr h₂.symm)]
      exact h₂
    · rw [push_γ, List.head?_map, h₃]
      rfl
    · rw [push_γ, List.getLast?_map, h₄]
      rfl
  · intro e' he' h3 r hr hcard f hf'
    have hcomp : ∀ X : Set S, componentsIn (α '' X) = (fun c ↦ α '' c) '' componentsIn X := fun X ↦
      componentsIn_image (f' := α.symm) α.continuous.continuousOn α.symm.continuous.continuousOn
        (fun x _ ↦ by simp)
    rw [push_E] at he'
    obtain ⟨e, he, rfl⟩ := he'
    have hreg : (Γ.push α).regions = (fun c ↦ α '' c) '' Γ.regions := by
      change componentsIn (α '' Γ.U)ᶜ = _
      rw [← image_compl_eq α.bijective, hcomp]
      rfl
    rw [hreg] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    change 3 ≤ (closure (α '' r₀) ∩ α '' Γ.V).ncard at hcard
    rw [← α.image_closure, ← image_inter α.injective,
      ncard_image_of_injective _ α.injective] at hcard
    simp only at hf'
    rw [← α.image_closure, ← image_inter α.injective, hcomp] at hf'
    obtain ⟨f₀, hf₀, rfl⟩ := hf'
    obtain ⟨x, hx, hxb⟩ := hf.size_three_region e he (by rw [← ncard_tilde_image α]; exact h3) r₀
      hr₀
      hcard f₀ hf₀
    refine ⟨α x, ?_, ?_⟩
    · simp only
      rw [← α.image_closure]
      exact mem_image_of_mem _ hx
    · rw [← image_bd α]
      exact mem_image_of_mem _ hxb

end Preserving

/-! ### Images of coloured paintings -/

section Image

variable {α₀ : Type w} {χ : ColourScheme S α₀}

/-- `(Γ', φ')` is the image of `(Γ, φ)` under `α` (Graph Minors XIX, page 335). -/
structure IsColouredImage (α : S ≃ₜ S) (P P' : ColouredPainting χ) : Prop where
  U : P'.Γ.U = α '' P.Γ.U
  V : P'.Γ.V = α '' P.Γ.V
  γ : ∀ e ∈ P.Γ.E, P'.Γ.γ (α '' e) = (P.Γ.γ e).map α
  φ : ∀ e ∈ P.Γ.E, P'.φ (α '' e) = P.φ e

/-- The image of a coloured painting under a frame-preserving homeomorphism. -/
noncomputable def ColouredPainting.image (P : ColouredPainting χ) (α : S ≃ₜ S)
    (hα : IsFramePreservingHomeo χ.Φ α) : ColouredPainting χ where
  Γ := P.Γ.push α
  φ e := P.φ (α.symm '' e)
  fits := P.fits.push hα
  internal_2_mem := by
    intro e he hi h2
    rw [push_E] at he
    obtain ⟨c, hc, rfl⟩ := he
    simp only [symm_image_image' α]
    refine P.internal_2_mem c hc ?_ (by rw [← ncard_tilde_image α]; exact h2)
    exact isInternal_iff_not_border.mpr fun hb ↦ (isInternal_iff_not_border.mp hi)
      ((isBorder_image α).mpr hb)
  internal_3_mem := by
    intro e he hi h3
    rw [push_E] at he
    obtain ⟨c, hc, rfl⟩ := he
    simp only [symm_image_image' α]
    refine P.internal_3_mem c hc ?_ (by rw [← ncard_tilde_image α]; exact h3)
    exact isInternal_iff_not_border.mpr fun hb ↦ (isInternal_iff_not_border.mp hi)
      ((isBorder_image α).mpr hb)
  border_mem := by
    intro e he s hs hbs
    rw [push_E] at he
    obtain ⟨c, hc, rfl⟩ := he
    simp only [symm_image_image' α]
    refine P.border_mem c hc s hs ⟨(isBorder_image α).mp hbs.1, ?_⟩
    have := hbs.2
    rw [← hα.preserve_sides s hs] at this
    exact (image_subset_image_iff α.injective).mp this

omit [T2Space S] in
theorem ColouredPainting.isImage_image (P : ColouredPainting χ) (α : S ≃ₜ S)
    (hα : IsFramePreservingHomeo χ.Φ α) : IsColouredImage α P (P.image α hα) where
  U := rfl
  V := rfl
  γ e _ := push_γ α P.Γ e
  φ e _ := congrArg P.φ (symm_image_image' α e)

end Image


section Transfer

variable {α₀ : Type w} {χ : ColourScheme S α₀} {P₁ P₂ P₁' P₂' : ColouredPainting χ}
  {α₁ α₂ : S ≃ₜ S}

omit [T2Space S] in
theorem IsColouredImage.E_eq {α : S ≃ₜ S} {P P' : ColouredPainting χ} (I : IsColouredImage α P P') :
    P'.Γ.E = (fun c ↦ α '' c) '' P.Γ.E := by
  change arcComponentsIn (P'.Γ.U \ P'.Γ.V) = _
  rw [I.U, I.V, ← image_sdiff α.injective, GM20.image_arcComponentsIn]
  rfl

omit [T2Space S] in
theorem IsColouredImage.symm {α : S ≃ₜ S} {P P' : ColouredPainting χ} (I : IsColouredImage α P P') :
    IsColouredImage α.symm P' P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [I.U, symm_image_image' α]
  · rw [I.V, symm_image_image' α]
  · intro e he
    rw [I.E_eq] at he
    obtain ⟨c, hc, rfl⟩ := he
    rw [symm_image_image' α, I.γ c hc, List.map_map]
    simp
  · intro e he
    rw [I.E_eq] at he
    obtain ⟨c, hc, rfl⟩ := he
    rw [symm_image_image' α, I.φ c hc]

omit [T2Space S] in
theorem skAdj_image {α : S ≃ₜ S} {P P' : ColouredPainting χ} (I : IsColouredImage α P P') {x y : S}
    (h : P.Γ.skAdj.Adj x y) : P'.Γ.skAdj.Adj (α x) (α y) := by
  obtain ⟨hne, hx, hy, e, he, hxe, hye⟩ := h
  refine ⟨fun h ↦ hne (α.injective h), ?_, ?_, α '' e, ?_, ?_, ?_⟩
  · rw [I.V]
    exact mem_image_of_mem _ hx
  · rw [I.V]
    exact mem_image_of_mem _ hy
  · rw [I.E_eq]
    exact mem_image_of_mem _ he
  · rw [tilde_image_homeo]
    exact mem_image_of_mem _ hxe
  · rw [tilde_image_homeo]
    exact mem_image_of_mem _ hye

omit [T2Space S] in
theorem inter_cuff_image (hS : IsSurface S) {α : S ≃ₜ S} (hα : HasNullSignature α)
    (hα' : HasNullSignature α.symm) {X Θ : Set S} (hΘ : Θ ∈ cuffs S) :
    (α '' X ∩ Θ).Nonempty ↔ (X ∩ Θ).Nonempty := by
  have hO := (cuff_statement S hS).2.2 Θ hΘ
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxΘ⟩
    refine ⟨x, hx, ?_⟩
    have := null_mem hα' hΘ hO hxΘ
    simpa using this
  · rintro ⟨x, hx, hxΘ⟩
    exact ⟨α x, mem_image_of_mem _ hx, null_mem hα hΘ hO hxΘ⟩

/-- The new `σ` on vertices. -/
def imgV (α₁ α₂ : S ≃ₜ S) (σv : S → Set S) (v : S) : Set S := α₂ '' σv (α₁.symm v)

/-- The new `σ` on edges. -/
def imgE (α₁ α₂ : S ≃ₜ S) (σe : Set S → Set S) (e : Set S) : Set S := α₂ '' σe (α₁.symm '' e)

omit [T2Space S] in
theorem imgE_image (σe : Set S → Set S) (e : Set S) :
    imgE α₁ α₂ σe (α₁ '' e) = α₂ '' σe e := by
  rw [imgE, symm_image_image' α₁]

omit [T2Space S] in
theorem imgV_image (σv : S → Set S) (v : S) : imgV α₁ α₂ σv (α₁ v) = α₂ '' σv v := by
  simp [imgV]

omit [T2Space S] in
theorem IsInflation.image (I₁ : IsColouredImage α₁ P₁ P₁') (I₂ : IsColouredImage α₂ P₂ P₂')
    {σv : S → Set S} {σe : Set S → Set S} (h : IsInflation P₁.Γ P₂.Γ σv σe) :
    IsInflation P₁'.Γ P₂'.Γ (imgV α₁ α₂ σv) (imgE α₁ α₂ σe) := by
  have hV : ∀ v ∈ P₁'.Γ.V, ∃ v₀ ∈ P₁.Γ.V, α₁ v₀ = v := fun v hv ↦ by
    rw [I₁.V] at hv
    exact hv
  refine
    { edge_mem := ?_
      edge_size := ?_
      edge_injOn := ?_
      vertex_nonempty := ?_
      vertex_subset := ?_
      vertex_connected := ?_
      vertex_disjoint := ?_
      ends := ?_ }
  · intro e he
    rw [I₁.E_eq] at he
    obtain ⟨c, hc, rfl⟩ := he
    simp only
    rw [imgE_image, I₂.E_eq]
    exact mem_image_of_mem _ (h.edge_mem c hc)
  · intro e he
    rw [I₁.E_eq] at he
    obtain ⟨c, hc, rfl⟩ := he
    simp only
    rw [imgE_image, ncard_tilde_image, ncard_tilde_image, h.edge_size c hc]
  · intro e he e' he' heq
    rw [I₁.E_eq] at he he'
    obtain ⟨c, hc, rfl⟩ := he
    obtain ⟨c', hc', rfl⟩ := he'
    simp only [imgE_image] at heq
    have := h.edge_injOn hc hc' (α₂.injective.image_injective heq)
    rw [this]
  · intro v hv
    obtain ⟨v₀, hv₀, rfl⟩ := hV v hv
    rw [imgV_image]
    exact (h.vertex_nonempty v₀ hv₀).image _
  · intro v hv
    obtain ⟨v₀, hv₀, rfl⟩ := hV v hv
    rw [imgV_image, I₂.V]
    exact image_mono (h.vertex_subset v₀ hv₀)
  · intro v hv
    obtain ⟨v₀, hv₀, rfl⟩ := hV v hv
    rw [imgV_image]
    let f : P₂.Γ.skAdj.induce (σv v₀) →g P₂'.Γ.skAdj.induce (α₂ '' σv v₀) :=
      ⟨fun x ↦ ⟨α₂ x.1, mem_image_of_mem _ x.2⟩, fun hxy ↦ skAdj_image I₂ hxy⟩
    refine (h.vertex_connected v₀ hv₀).map f ?_
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · intro v hv w hw hne
    obtain ⟨v₀, hv₀, rfl⟩ := hV v hv
    obtain ⟨w₀, hw₀, rfl⟩ := hV w hw
    rw [imgV_image, imgV_image]
    exact (disjoint_image_iff α₂.injective).mpr
      (h.vertex_disjoint v₀ hv₀ w₀ hw₀ fun he ↦ hne (by rw [he]))
  · intro e he i hi hi'
    rw [I₁.E_eq] at he
    obtain ⟨c, hc, rfl⟩ := he
    simp only [imgE_image] at hi' ⊢
    have h₁ := I₁.γ c hc
    have h₂ := I₂.γ _ (h.edge_mem c hc)
    simp only [h₁, h₂, List.length_map] at hi hi' ⊢
    simp only [List.getElem_map]
    rw [imgV_image]
    exact mem_image_of_mem _ (h.ends c hc i hi hi')

omit [T2Space S] in
theorem IsColouredInflation.image (_hS : IsSurface S) (h₁ : IsFramePreservingHomeo χ.Φ α₁)
    (h₂ : IsFramePreservingHomeo χ.Φ α₂) (I₁ : IsColouredImage α₁ P₁ P₁')
    (I₂ : IsColouredImage α₂ P₂ P₂') {σv : S → Set S} {σe : Set S → Set S}
    (h : IsColouredInflation χ P₁ P₂ σv σe) :
    IsColouredInflation χ P₁' P₂' (imgV α₁ α₂ σv) (imgE α₁ α₂ σe) := by
  have hint : ∀ {α : S ≃ₜ S} {e : Set S}, Painting.IsInternal (α '' e) → Painting.IsInternal e := by
    intro α e hi
    exact isInternal_iff_not_border.mpr fun hb ↦ (isInternal_iff_not_border.mp hi)
      ((isBorder_image α).mpr hb)
  have hsub : ∀ {α : S ≃ₜ S}, IsFramePreservingHomeo χ.Φ α → ∀ {e s : Set S}, s ∈ χ.Φ.sides →
      (α '' e ⊆ s ↔ e ⊆ s) := by
    intro α hα e s hs
    conv_lhs => rw [← hα.preserve_sides s hs]
    exact image_subset_image_iff α.injective
  refine ⟨h.isInflation.image I₁ I₂, ?_, ?_, ?_, ?_⟩
  · intro e he hb
    rw [I₁.E_eq] at he
    obtain ⟨c, hc, rfl⟩ := he
    obtain ⟨h₃, h₄⟩ := h.respects c hc ((isBorder_image α₁).mp hb)
    rw [imgE_image]
    refine ⟨(isBorder_image α₂).mpr h₃, fun s hs ↦ ?_⟩
    rw [hsub h₁ hs, hsub h₂ hs]
    exact h₄ s hs
  · intro e he hi h2
    rw [I₁.E_eq] at he
    obtain ⟨c, hc, rfl⟩ := he
    rw [imgE_image, I₁.φ c hc, I₂.φ _ (h.isInflation.edge_mem c hc)]
    exact h.le_internal_2 c hc (hint hi) (by rw [← ncard_tilde_image α₁]; exact h2)
  · intro e he hi h3
    rw [I₁.E_eq] at he
    obtain ⟨c, hc, rfl⟩ := he
    rw [imgE_image, I₁.φ c hc, I₂.φ _ (h.isInflation.edge_mem c hc)]
    exact h.le_internal_3 c hc (hint hi) (by rw [← ncard_tilde_image α₁]; exact h3)
  · intro e he s hs hb
    rw [I₁.E_eq] at he
    obtain ⟨c, hc, rfl⟩ := he
    rw [imgE_image, I₁.φ c hc, I₂.φ _ (h.isInflation.edge_mem c hc)]
    exact h.le_border c hc s hs ⟨(isBorder_image α₁).mp hb.1, (hsub h₁ hs).mp hb.2⟩

theorem IsColouredLinearInflation.image (hS : IsSurface S) (h₁ : IsFramePreservingHomeo χ.Φ α₁)
    (h₂ : IsFramePreservingHomeo χ.Φ α₂) (I₁ : IsColouredImage α₁ P₁ P₁')
    (I₂ : IsColouredImage α₂ P₂ P₂') {σv : S → Set S} {σe : Set S → Set S}
    (h : IsColouredLinearInflation χ P₁ P₂ σv σe) :
    IsColouredLinearInflation χ P₁' P₂' (imgV α₁ α₂ σv) (imgE α₁ α₂ σe) := by
  have hn₁ := h₁.null hS
  have hn₁' := h₁.symm.null hS
  have hn₂ := h₂.null hS
  have hn₂' := h₂.symm.null hS
  have hc := IsColouredInflation.image hS h₁ h₂ I₁ I₂ h.toIsColouredInflation
  have hL := h.isLinear
  refine ⟨hc, { hc.isInflation with borders_iff := ?_, border_edge := ?_, orientation := ?_ }⟩
  · intro e he Θ hΘ
    rw [I₁.E_eq] at he
    obtain ⟨c, hc', rfl⟩ := he
    rw [imgE_image, inter_cuff_image hS hn₁ hn₁' hΘ, inter_cuff_image hS hn₂ hn₂' hΘ]
    exact hL.borders_iff c hc' Θ hΘ
  · intro e' he' hb hne
    rw [I₂.E_eq] at he'
    obtain ⟨e, he, rfl⟩ := he'
    obtain ⟨v, hv, hsub⟩ := hL.border_edge e he ((isBorder_image α₂).mp hb) (by
      rintro ⟨c, hc', rfl⟩
      refine hne ⟨α₁ '' c, ?_, imgE_image _ _⟩
      rw [I₁.E_eq]
      exact mem_image_of_mem _ hc')
    refine ⟨α₁ v, ?_, ?_⟩
    · rw [I₁.V]
      exact mem_image_of_mem _ hv
    · rw [imgV_image, tilde_image_homeo]
      exact image_mono hsub
  · intro e he Θ hΘ hne f n n' hn hn' hp
    rw [I₁.E_eq] at he
    obtain ⟨c, hc', rfl⟩ := he
    rw [imgE_image] at hn' ⊢
    rw [I₁.γ c hc', List.head?_map] at hn
    rw [I₂.γ _ (hL.edge_mem c hc'), List.head?_map] at hn'
    obtain ⟨n₀, hn₀, rfl⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨n₀', hn₀', rfl⟩ := Option.map_eq_some_iff.mp hn'
    have hp₁ := hp.null hn₁' hΘ
    simp only [Homeomorph.symm_apply_apply, symm_image_image' α₁] at hp₁
    have hp₂ := hL.orientation c hc' Θ hΘ
      ((inter_cuff_image hS hn₁ hn₁' hΘ).mp hne) f n₀ n₀' hn₀ hn₀' hp₁
    exact hp₂.null hn₂ hΘ

/-- **Graph Minors XIX, (5.1)** for linear inflations. -/
theorem theorem_5_1_proof (hS : IsSurface S) (h₁ : IsFramePreservingHomeo χ.Φ α₁)
    (h₂ : IsFramePreservingHomeo χ.Φ α₂) (I₁ : IsColouredImage α₁ P₁ P₁')
    (I₂ : IsColouredImage α₂ P₂ P₂') :
    (∃ σv σe, IsColouredLinearInflation χ P₁' P₂' σv σe) ↔
      ∃ σv σe, IsColouredLinearInflation χ P₁ P₂ σv σe := by
  constructor
  · rintro ⟨σv, σe, h⟩
    exact ⟨_, _, h.image hS h₁.symm h₂.symm I₁.symm I₂.symm⟩
  · rintro ⟨σv, σe, h⟩
    exact ⟨_, _, h.image hS h₁ h₂ I₁ I₂⟩

omit [T2Space S] in
/-- **Graph Minors XIX, (5.1)** for inflations. -/
theorem theorem_5_1' (hS : IsSurface S) (h₁ : IsFramePreservingHomeo χ.Φ α₁)
    (h₂ : IsFramePreservingHomeo χ.Φ α₂) (I₁ : IsColouredImage α₁ P₁ P₁')
    (I₂ : IsColouredImage α₂ P₂ P₂') :
    (∃ σv σe, IsColouredInflation χ P₁' P₂' σv σe) ↔ ∃ σv σe, IsColouredInflation χ P₁ P₂ σv σe
      := by
  constructor
  · rintro ⟨σv, σe, h⟩
    exact ⟨_, _, IsColouredInflation.image hS h₁.symm h₂.symm I₁.symm I₂.symm h⟩
  · rintro ⟨σv, σe, h⟩
    exact ⟨_, _, IsColouredInflation.image hS h₁ h₂ I₁ I₂ h⟩

end Transfer

end GraphMinor.GM19
