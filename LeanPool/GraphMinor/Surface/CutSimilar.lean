/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutOArc
public import LeanPool.GraphMinor.Surface.ModelHomeo

/-!
# Finitely many classes of proper arcs

Two spaces with the same word are homeomorphic by a map that keeps each side (`presents_homeo`).
Cutting a surface `S` along a
proper arc gives a word of `S` that has the arc as a side (`arc_data`). There are only finitely many
of these words, since the
classification bounds the parameters of the cut surface. So a surface has finitely many classes of
proper arcs
(`similarArcsFinite`). This is the proof of Graph Minors VII, (3.1), page 218.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe u

/-- Two spaces with the same word are homeomorphic. -/
theorem presents_homeo {X X' : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace X']
  [T2Space X'] {W : ℕ → List Letter}
    (hW : {i | W i ≠ []}.Finite) {f : ℕ × ℂ → X} {f' : ℕ × ℂ → X'} (hf : Presents W f)
      (hf' : Presents W f') :
    ∃ e : X ≃ₜ X', ∀ a ∈ Dsk W, e (f a) = f' a := by
  have hD : IsCompact (Dsk W) := isCompact_Dsk hW
  obtain ⟨hc, hs, hrel⟩ := hf
  obtain ⟨hc', hs', hrel'⟩ := hf'
  have ex1 : ∀ x : X, ∃ y ∈ Dsk W, f y = x := fun x => by
    have h1 : x ∈ f '' Dsk W := hs ▸ mem_univ x
    exact h1
  have ex2 : ∀ x : X', ∃ y ∈ Dsk W, f' y = x := fun x => by
    have h1 : x ∈ f' '' Dsk W := hs' ▸ mem_univ x
    exact h1
  choose s1 hs1 hs1' using ex1
  choose s2 hs2 hs2' using ex2
  have e1 : ∀ a ∈ Dsk W, f' (s1 (f a)) = f' a := fun a ha => (hrel' _ (hs1 _) _ ha).mpr ((hrel _
    (hs1 _) _ ha).mp (hs1' _))
  have e2 : ∀ a ∈ Dsk W, f (s2 (f' a)) = f a := fun a ha => (hrel _ (hs2 _) _ ha).mpr ((hrel' _
    (hs2 _) _ ha).mp (hs2' _))
  have c1 : Continuous fun x => f' (s1 x) := continuous_of_compact_quotient hD hc hs
    (hc'.congr fun a ha => e1 a ha)
  have c2 : Continuous fun x => f (s2 x) := continuous_of_compact_quotient hD hc' hs'
    (hc.congr fun a ha => e2 a ha)
  refine ⟨{
    toFun := fun x => f' (s1 x)
    invFun := fun x => f (s2 x)
    left_inv := fun x => ?_
    right_inv := fun x => ?_
    continuous_toFun := c1
    continuous_invFun := c2
  }, e1⟩
  · change f (s2 (f' (s1 x))) = x
    rw [e2 _ (hs1 x), hs1']
  · change f' (s1 (f (s2 x))) = x
    rw [e1 _ (hs2 x), hs2']

/-- `F` is a side of the word `W` of the surface. -/
def HasData {S : Type*} [TopologicalSpace S] (F : Set S) (W : ℕ → List Letter) (p : ℕ) : Prop :=
  ∃ (f : ℕ × ℂ → S) (a : ℝ → S), Presents W f ∧ SideVal W f p a ∧ a '' Icc 0 1 = F

/-- Two arcs with the same side of the same word are similar. -/
theorem similar_of_data {S : Type*} [TopologicalSpace S] [T2Space S] {F F₀ : Set S} {W : ℕ
  → List Letter} {p : ℕ} (hW : {i | W i ≠ []}.Finite)
    (h : HasData F W p) (h₀ : HasData F₀ W p) : ∃ α : S ≃ₜ S, α '' F₀ = F := by
  obtain ⟨f, a, h1, ⟨i, q, h2, h3⟩, rfl⟩ := h
  obtain ⟨f₀, a₀, h1', ⟨i₀, q₀, h2', h3'⟩, rfl⟩ := h₀
  obtain ⟨e, he⟩ := presents_homeo hW h1' h1
  refine ⟨e, ?_⟩
  rw [image_image]
  refine image_congr fun u hu => ?_
  by_cases hne : (i₀, q₀) = (i, q)
  · simp only [Prod.mk.injEq] at hne
    obtain ⟨rfl, rfl⟩ := hne
    have hs : Stp W (i₀, sdPt (W i₀).length q₀ true u) (i₀, sdPt (W i₀).length q₀ true u) ∨ True
      := .inr trivial
    have hmem : (i₀, sdPt (W i₀).length q₀ true u) ∈ Dsk W := by
      refine ⟨?_, ?_⟩
      · intro hn
        simp only at hn
        rw [hn] at h2
        simp at h2
      · simp only [sdPt, per, cis']
        rw [Complex.norm_exp_ofReal_mul_I]
    rw [← h3' u hu, he _ hmem, h3 u hu]
  · have hs : Stp W (i₀, sdPt (W i₀).length q₀ true u) (i, sdPt (W i).length q true u) :=
      ⟨i₀, i, q₀, q, p, true, true, u, h2', h2, hne, hu, rfl, rfl⟩
    obtain ⟨h4, h5⟩ := hs.mem_Dsk
    rw [← h3' u hu, he _ h4, ← h3 u hu]
    exact (h1.2.2 _ h4 _ h5).mpr (.rel _ _ hs)

/-- The words of a surface that have a proper arc as a side. -/
noncomputable def arcCode (t a b c a₂ b₂ c₂ i j : ℕ) (σ : Bool) : (ℕ → List Letter) × ℕ :=
  if t = 0 then (sW (blkA a b c i j σ ++ rW a b c (((List.range' 0 c).erase i).erase j)),
    (rL a b i).1)
  else if t = 1 then (sW (blkB a b c i σ ++ rW a b c ((List.range' 0 c).erase i)), (rL a b i).1)
  else (dW (wArc₁ a b c i ((List.range' 0 c).erase i))
      (wArc₂ a₂ b₂ c₂ j ((List.range' 0 c₂).erase j) (frL a b c + 1) ((rL a b i).1, σ)),
        (rL a b i).1)

theorem finite_arcCode (t a b c a₂ b₂ c₂ i j : ℕ) (σ : Bool) : {k | (arcCode t a b c a₂ b₂ c₂ i j
  σ).1 k ≠ []}.Finite := by
  unfold arcCode
  split_ifs
  · exact finW_sW _
  · exact finW_sW _
  · refine (finite_le_nat 1).subset fun k hk => ?_
    rcases dW_cases _ _ k with ⟨rfl, -⟩ | ⟨rfl, -⟩ | e
    · simp
    · simp
    · exact absurd e hk

/-- The parameters of the words, below a bound. -/
abbrev ArcIdx (B : ℕ) : Type :=
  Fin (B + 1) × Fin (B + 1) × Fin (B + 1) × Fin (B + 1) × Fin (B + 1) × Fin (B + 1) × Fin
    (B + 1) × Fin (B + 1) × Fin (B + 1) × Bool

/-- The word with the given parameters. -/
noncomputable def arcWord {B : ℕ} (x : ArcIdx B) : (ℕ → List Letter) × ℕ :=
  arcCode x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.1
    x.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2

/-- A proper arc of a connected surface is a side of a word with bounded parameters. -/
theorem arc_data {S : Type u} [TopologicalSpace S] (hS : IsSurface S) [hconn : ConnectedSpace S]
  {a₀ b₀ c₀ : ℕ} (e₀ : S ≃ₜ SurfaceModel a₀ b₀ c₀)
    {F : Set S} (hF' : IsProperIArc F) : ∃ x : ArcIdx (2 * a₀ + b₀ + c₀ + 3), HasData F
      (arcWord x).1 (arcWord x).2 := by
  obtain ⟨s, t, hst, hF, hl⟩ := hF'
  have hcS : CompactSpace S := hS.1
  have ht2 : T2Space S := hS.2.1
  have crit : ∀ {a b c : ℕ}, Nonempty (S ≃ₜ SurfaceModel a b c) → c = c₀ ∧ 2 * a + b = 2 * a₀ + b₀
    := fun {a b c} h => by
    obtain ⟨e'⟩ := h
    obtain ⟨h1, h2, -⟩ := (modelCriterion.2 a b c a₀ b₀ c₀).mp ⟨e'.symm.trans e₀⟩
    exact ⟨h1, h2⟩
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, X, X', hP⟩ := exists_cut_arc hS hst hF hl
  have hcY : CompactSpace Y := hY.1
  have hPc := hP
  obtain ⟨x0, x1, y0, y1, l1, l2, hd, hun, b1, b2, h7, h8, h9, h10⟩ := hP
  obtain ⟨a₁, ξ, η, L, ha0, ha1, himξ, himη, hiξ, hiη⟩ := exists_arcLift hPc hψ
  have hXb : X ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inl hz)
  have hXb' : X' ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inr hz)
  have pX : IsPreconnected X := himξ ▸ isPreconnected_Icc.image _ L.cξ
  have pX' : IsPreconnected X' := himη ▸ isPreconnected_Icc.image _ L.cη
  have hex : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hx : ξ 0 ∈ X := himξ ▸ ⟨0, hex, rfl⟩
  have hy : η 0 ∈ X' := himη ▸ ⟨0, hex, rfl⟩
  have hξm : ∀ u ∈ Icc (0 : ℝ) 1, ξ u ∈ X := fun u hu => himξ ▸ ⟨u, hu, rfl⟩
  have hηm : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ X' := fun u hu => himη ▸ ⟨u, hu, rfl⟩
  have hdcuff := cuff_statement.{u} Y hY
  have : Nonempty S := ⟨s⟩
  rcases cut_comps hψ hY pX pX' hun hx hy with hYc | ⟨W₁, W₂, hne, hsc, hX₁, hX₂, hW₁, hW₂, hU,
    hdW, hc₁, hc₂⟩
  · obtain ⟨a, b, c, ⟨e⟩⟩ := classification.{u} Y hY hYc
    have hC : connectedComponentIn (bd Y) (ξ 0) ∈ cuffs Y := ⟨_, hXb hx, rfl⟩
    have hC' : connectedComponentIn (bd Y) (η 0) ∈ cuffs Y := ⟨_, hXb' hy, rfl⟩
    have hXC := pX.subset_connectedComponentIn hx hXb
    have hXC' := pX'.subset_connectedComponentIn hy hXb'
    by_cases hCC : connectedComponentIn (bd Y) (ξ 0) = connectedComponentIn (bd Y) (η 0)
    · obtain ⟨i, hi, φ, g, hg, hs⟩ := exists_one_hole e hC
      obtain ⟨a', ξ', η', m, L', ha', hxim, heim, hix, hie, hmc, hmm, hmξ⟩ := orient_lift L φ
        (fun u hu => hXC (hξm u hu)) hiξ hiη
      obtain ⟨hN, hLf⟩ := erase_facts c i
      have hξ' : ∀ u ∈ Icc (0 : ℝ) 1, ξ' u ∈ X := fun u hu => by
        rw [← himξ, ← hxim]
        exact ⟨u, hu, rfl⟩
      have hη' : ∀ u ∈ Icc (0 : ℝ) 1, η' u ∈ X' := fun u hu => by
        rw [← himη, ← heim]
        exact ⟨u, hu, rfl⟩
      obtain ⟨σ, g', hp, hsd, -⟩ := arc_one_aux hY L' hψ.1 hψ.2.1 hC φ hi hLf hg hs hmc hmm hmξ
        (fun u hu => hCC ▸ hXC' (hη' u hu)) hix hie (fun u hu v hv he => Set.disjoint_left.mp hd
          (hξ' u hu) (he ▸ hη' v hv))
      have hn := nf_blkB (a := a) (b := b) (c := c) hi hN hLf σ
      have hlen := length_erase_range hi
      have hb : a ≤ 2 * a₀ + b₀ + c₀ + 3 ∧ b ≤ 2 * a₀ + b₀ + c₀ + 3 ∧ c ≤ 2 * a₀ + b₀ + c₀ + 3 := by
        cases σ with
        | false =>
          obtain ⟨w, h5, h6⟩ := hn.1 rfl
          have := crit (homeo_of_nf hp h5 h6)
          omega
        | true =>
          obtain ⟨w, h5, h6⟩ := hn.2 rfl
          have := crit (homeo_of_nf hp h5 h6)
          omega
      refine ⟨(⟨1, by omega⟩, ⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩, ⟨0, by omega⟩, ⟨0,
        by omega⟩, ⟨0, by omega⟩, ⟨i, by omega⟩, ⟨0, by omega⟩, σ), ?_⟩
      exact ⟨_, a', hp, hsd, L'.img⟩
    · have hdis := cuffs_disjoint hC hC' hCC
      obtain ⟨i, hi, j, hj, hij, φ, φ', g, hg, hs, hs'⟩ := exists_two_holes e hC hC' hCC
      obtain ⟨a', ξ', η', m, L', ha', hxim, heim, hix, hie, hmc, hmm, hmξ⟩ := orient_lift L φ
        (fun u hu => hXC (hξm u hu)) hiξ hiη
      obtain ⟨hN, hLf⟩ := erase_erase_facts c i j
      have hη' : ∀ u ∈ Icc (0 : ℝ) 1, η' u ∈ X' := fun u hu => by
        rw [← himη, ← heim]
        exact ⟨u, hu, rfl⟩
      obtain ⟨σ, g', hp, hsd⟩ := arc_two_aux hY L' hψ.1 hψ.2.1 hC hC'
        (hdcuff.2.2 _ hC).isCompact.isClosed
        (hdcuff.2.2 _ hC').isCompact.isClosed hdis φ φ' hij hi hj hLf hg hs hs' hmc hmm hmξ
          (fun u hu => hXC' (hη' u hu)) hix hie
      have hn := nf_blkA (a := a) (b := b) (c := c) hij hi hj hN hLf σ
      have hlen := length_erase_erase hij hi hj
      have hb : a ≤ 2 * a₀ + b₀ + c₀ + 3 ∧ b ≤ 2 * a₀ + b₀ + c₀ + 3 ∧ c ≤ 2 * a₀ + b₀ + c₀ + 3 := by
        cases σ with
        | false =>
          obtain ⟨w, h5, h6⟩ := hn.1 rfl
          have := crit (homeo_of_nf hp h5 h6)
          omega
        | true =>
          obtain ⟨w, h5, h6⟩ := hn.2 rfl
          have := crit (homeo_of_nf hp h5 h6)
          omega
      refine ⟨(⟨0, by omega⟩, ⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩, ⟨0, by omega⟩, ⟨0,
        by omega⟩, ⟨0, by omega⟩, ⟨i, by omega⟩, ⟨j, by omega⟩, σ), ?_⟩
      exact ⟨_, a', hp, hsd, L'.img⟩
  · obtain ⟨a₃, b₃, c₃, ⟨e₁⟩⟩ := classification.{u} W₁ (isSurface_sub hY hW₁) hc₁
    obtain ⟨a₂, b₂, c₂, ⟨e₂⟩⟩ := classification.{u} W₂ (isSurface_sub hY hW₂) hc₂
    obtain ⟨i, j, σ, a', f, hi, hj, himg, -, hf, hsd⟩ := arc_comps_aux hY L hψ.1 hψ.2.1 hW₁ hW₂ hdW
      hU e₁ e₂
      (by rw [himξ]; exact hX₁) (by rw [himη]; exact hX₂) (by rw [himξ]; exact hXb)
        (by rw [himη]; exact hXb') hiξ hiη
    obtain ⟨hN₁, hL₁⟩ := erase_facts c₃ i
    obtain ⟨hN₂, hL₂⟩ := erase_facts c₂ j
    have hb := crit (homeo_of_two_arc hi hj hN₁ hN₂ hL₁ hL₂ hf)
    rw [length_erase_range hi, length_erase_range hj] at hb
    refine ⟨(⟨2, by omega⟩, ⟨a₃, by omega⟩, ⟨b₃, by omega⟩, ⟨c₃, by omega⟩, ⟨a₂, by omega⟩, ⟨b₂,
      by omega⟩, ⟨c₂, by omega⟩, ⟨i, by omega⟩, ⟨j, by omega⟩, σ), ?_⟩
    exact ⟨f, a', hf, hsd, himg⟩

/-- A connected surface has finitely many classes of proper arcs. -/
theorem similar_conn {S : Type u} [TopologicalSpace S] (hS : IsSurface S) [hconn : ConnectedSpace
  S] :
    ∃ 𝓕 : Set (Set S), 𝓕.Finite ∧ ∀ F : Set S, IsProperIArc F → ∃ F₀ ∈ 𝓕, ∃ α : S ≃ₜ S, α '' F₀ = F
      := by
  classical
  have ht2 : T2Space S := hS.2.1
  obtain ⟨a₀, b₀, c₀, ⟨e₀⟩⟩ := classification.{u} S hS hconn
  set B := 2 * a₀ + b₀ + c₀ + 3
  let pick : ArcIdx B → Set S := fun x =>
    if h : ∃ F : Set S, IsProperIArc F ∧ HasData F (arcWord x).1 (arcWord x).2 then h.choose else ∅
  refine ⟨range pick, finite_range _, fun F hF => ?_⟩
  obtain ⟨x, hx⟩ := arc_data hS e₀ hF
  have hex : ∃ F : Set S, IsProperIArc F ∧ HasData F (arcWord x).1 (arcWord x).2 := ⟨F, hF, hx⟩
  have h1 : pick x = hex.choose := dite_eq_left hex
  refine ⟨pick x, ⟨x, rfl⟩, ?_⟩
  rw [h1]
  exact similar_of_data (finite_arcCode ..) hx hex.choose_spec.2

open Classical in
/-- A map of a clopen part, extended by the identity. -/
noncomputable def extId {S : Type*} {W : Set S} (γ : W → W) (x : S) : S := if h : x ∈ W then
  (γ ⟨x, h⟩).1 else x

theorem extId_mem {S : Type*} {W : Set S} (γ : W → W) (x : W) : extId γ x.1 = (γ x).1 := by
  simp [extId]

theorem extId_not {S : Type*} {W : Set S} (γ : W → W) {x : S} (h : x ∉ W) : extId γ x = x := by
  simp [extId, h]

theorem continuous_extId {S : Type*} [TopologicalSpace S] {W : Set S} (hW : IsClopen W) {γ : W → W}
  (hγ : Continuous γ) :
    Continuous (extId γ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases h : x ∈ W
  · have h1 : ContinuousAt (extId γ ∘ (Subtype.val : W → S)) ⟨x, h⟩ := by
      have : extId γ ∘ (Subtype.val : W → S) = Subtype.val ∘ γ := funext fun y => extId_mem γ y
      rw [this]
      exact (continuous_subtype_val.comp hγ).continuousAt
    exact (hW.2.isOpenEmbedding_subtypeVal.continuousAt_iff).mp h1
  · have h2 : IsOpen Wᶜ := hW.1.isOpen_compl
    have h1 : ContinuousAt (extId γ ∘ (Subtype.val : (Wᶜ : Set S) → S)) ⟨x, h⟩ := by
      have : extId γ ∘ (Subtype.val : (Wᶜ : Set S) → S) = Subtype.val := funext fun y
        => extId_not γ y.2
      rw [this]
      exact continuous_subtype_val.continuousAt
    exact (h2.isOpenEmbedding_subtypeVal.continuousAt_iff).mp h1

/-- A homeomorphism of a clopen part, extended by the identity. -/
theorem exists_extend {S : Type*} [TopologicalSpace S] {W : Set S} (hW : IsClopen W) (α : W ≃ₜ W) :
    ∃ β : S ≃ₜ S, (∀ x : W, β x = (α x).1) ∧ ∀ x ∉ W, β x = x := by
  have inv : ∀ (γ δ : W → W), (∀ y, γ (δ y) = y) → ∀ x, extId γ (extId δ x) = x := by
    intro γ δ h x
    by_cases hx : x ∈ W
    · have h1 := extId_mem δ ⟨x, hx⟩
      simp only at h1
      rw [h1, extId_mem γ, h]
    · rw [extId_not δ hx, extId_not γ hx]
  exact ⟨{ toFun := extId α, invFun := extId α.symm, left_inv := inv _ _ fun y
    => α.symm_apply_apply y,
           right_inv := inv _ _ fun y => α.apply_symm_apply y, continuous_toFun
             := continuous_extId hW α.continuous,
           continuous_invFun := continuous_extId hW α.symm.continuous }, fun x
             => extId_mem _ x, fun _ hx => extId_not _ hx⟩

/-- The arcs of one component of a surface. -/
theorem similar_comp {S : Type u} [TopologicalSpace S] (hS : IsSurface S) (x : S) :
    ∃ 𝓖 : Set (Set S), 𝓖.Finite ∧ ∀ F : Set S, IsProperIArc F → F ⊆ connectedComponent x →
      ∃ F₀ ∈ 𝓖, ∃ α : S ≃ₜ S, α '' F₀ = F := by
  have := hS.locallyConnected
  have hW : IsClopen (connectedComponent x) := isClopen_connectedComponent
  have ht2 : T2Space S := hS.2.1
  have hW1 : IsSurface (connectedComponent x) := isSurface_sub hS hW
  have hc : ConnectedSpace (connectedComponent x) := isConnected_iff_connectedSpace.mp
    isConnected_connectedComponent
  obtain ⟨𝓕, h1, h2⟩ := similar_conn hW1
  refine ⟨image (image Subtype.val) 𝓕, h1.image _, fun F hF hsub => ?_⟩
  obtain ⟨s, t, hst, hb, hl⟩ := id hF
  have hsW : s ∈ connectedComponent x := hsub hl.left_mem
  have htW : t ∈ connectedComponent x := hsub hl.right_mem
  have hF' : IsProperIArc (Subtype.val ⁻¹' F : Set (connectedComponent x)) := by
    refine ⟨⟨s, hsW⟩, ⟨t, htW⟩, fun he => hst (congrArg Subtype.val he), ?_, ?_⟩
    · ext y
      have h3 : y ∈ bd (connectedComponent x) ↔ y.1 ∈ bd S := mem_bd_sub hW.2
      have h4 := Set.ext_iff.mp hb y.1
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_preimage, h3,
        Subtype.ext_iff]
      simpa using h4
    · obtain ⟨u', v', e1, e2, h5⟩ := hl.pull (j := (Subtype.val : connectedComponent x
        → S)) IsEmbedding.subtypeVal (by rwa [Subtype.range_coe])
      have e3 : u' = ⟨s, hsW⟩ := Subtype.ext e1
      have e4 : v' = ⟨t, htW⟩ := Subtype.ext e2
      rwa [e3, e4] at h5
  obtain ⟨F₀, h3, α, h4⟩ := h2 _ hF'
  obtain ⟨β, hβ, -⟩ := exists_extend hW α
  refine ⟨_, mem_image_of_mem _ h3, β, ?_⟩
  have e1 : Subtype.val '' (Subtype.val ⁻¹' F : Set (connectedComponent x)) = F := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsub]
  rw [← e1, ← h4, image_image, image_image]
  exact image_congr fun y _ => hβ y

/-- **Finitely many classes of proper arcs.** Graph Minors VII, (3.1), page 218: cut along the arc
and use the classification.
Here `arc_data` gives a word of the surface with the arc as a side, and `presents_homeo` compares
two arcs with the same word. -/
theorem similarArcsFinite : SimilarArcsFiniteStatement.{u} := by
  intro S _ hS
  have hcS : CompactSpace S := hS.1
  have := hS.locallyConnected
  choose 𝓖 h1 h2 using similar_comp hS
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : S => connectedComponent x)
    (fun x => isOpen_connectedComponent) (fun x _ => mem_iUnion.mpr ⟨x, mem_connectedComponent⟩)
  refine ⟨⋃ x ∈ T, 𝓖 x, T.finite_toSet.biUnion fun x _ => h1 x, fun F hF => ?_⟩
  obtain ⟨s, t, hst, hb, hl⟩ := id hF
  obtain ⟨x, hx, hs⟩ := mem_iUnion₂.mp (hT (mem_univ s))
  have hsub : F ⊆ connectedComponent x := by
    rw [connectedComponent_eq hs]
    obtain ⟨a, ha, e, -, -⟩ := hl.exists_arc
    have hp : IsPreconnected F := e ▸ isPreconnected_range ha.1
    exact hp.subset_connectedComponent hl.left_mem
  obtain ⟨F₀, h3, α, h4⟩ := h2 x F hF hsub
  exact ⟨F₀, mem_iUnion₂.mpr ⟨x, hx, h3⟩, α, h4⟩

end GraphMinor.Surface
