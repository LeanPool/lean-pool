/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Cover
public import LeanPool.GraphMinor.GM19.Section6Six

import LeanPool.GraphMinor.GM19.Section6aProved
import LeanPool.GraphMinor.GM19.UniverseLift2

/-!
# Theorem (6.2) of Graph Minors XIX

We follow the proof on pages 342-343. From an inflation `σ` we build the enlargement `τ` of `sk(Γ₁)`
in
`sk(Γ₂)` (`exists_enlargement`), and (6.7) says that these are blocks with the same representativity
as
the paintings. Then (6.6) gives a larger enlargement `τ'`, which meets each region in a connected
part.
This gives a larger inflation `σ'`. For each cuff, `τ'(v)` meets the cuff in a connected part, and
this
gives the cover of the cuff (`cuff_cover`) that makes `σ'` linear. The direction condition is not
spelled
out in the paper. It follows from the directions of the sides of the frame
(`precedes_of_dirAgrees`),
since `e` and `σ(e)` lie in one side.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S} {D : Drawing Shat}

omit [T2Space Shat] in
omit [T2Space S] in
/-- The pasted disc of a cuff is a region of `sk(Γ)` in `Σ̂`. -/
theorem cuffDisc_mem_regions (hD : IsSkHat cap Γ D) {Θ : Set S}
  (hΘ : Θ ∈ cuffs S) :
    cap.cuffDisc Θ ∈ D.regions := by
  have hnotR : ∀ {Θ' : Set S} {x : Shat}, Θ' ∈ cuffs S → x ∈ cap.cuffDisc Θ' → x ∉ range cap.emb
    := by
    intro Θ' x hΘ' hx
    have : x ∈ (range cap.emb)ᶜ := by
      rw [cap.compl_eq]
      exact mem_iUnion₂.2 ⟨Θ', hΘ', hx⟩
    exact this
  obtain ⟨x, hx⟩ : (cap.cuffDisc Θ).Nonempty := by
    obtain ⟨z, hz, hz'⟩ := id hΘ
    have hzΘ : z ∈ Θ := hz' ▸ mem_connectedComponentIn hz
    have hb : cap.emb z ∈ discBd (closure (cap.cuffDisc Θ)) := by
      rw [cap.cuffDisc_bd Θ hΘ]
      exact mem_image_of_mem _ hzΘ
    exact closure_nonempty_iff.mp ⟨_, Surface.discBd_subset _ hb⟩
  have hxU : x ∈ (Γ.hatU cap)ᶜ := by
    rintro ⟨y, -, rfl⟩
    exact hnotR hΘ hx (mem_range_self y)
  have hr : connectedComponentIn (Γ.hatU cap)ᶜ x ∈ Γ.hatRegions cap := ⟨x, hxU, rfl⟩
  have hxr := mem_connectedComponentIn hxU
  rcases hatRegion_cases cap Γ hr with h | ⟨Θ', hΘ', h⟩
  · exact absurd (h hxr) (hnotR hΘ hx)
  · have hxΘ' : x ∈ cap.cuffDisc Θ' := h ▸ hxr
    obtain rfl : Θ = Θ' := by
      by_contra hne
      exact disjoint_left.mp (cap.cuffDisc_disjoint Θ hΘ Θ' hΘ' hne) (subset_closure hx)
        (subset_closure hxΘ')
    rw [regions_eq_R]
    exact hD.hatRegion_mem_R (h ▸ hr)

/-- A connected drawing is a connected set. -/
theorem drawing_U_preconnected {T : Type} [TopologicalSpace T] (G : Drawing T)
    (hne : G.V.Nonempty) (hends : ∀ e ∈ G.E, (tilde e).Nonempty)
    (h : (G.adj.induce G.V).Preconnected) : IsPreconnected G.U := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hcl : ∀ e ∈ G.E, IsPreconnected (closure e) := fun e he =>
    he.2.2.1.isConnected.isPreconnected.closure
  have key : ∀ {a b : G.V}, (G.adj.induce G.V).Walk a b →
      ∃ C, C ⊆ G.U ∧ a.1 ∈ C ∧ b.1 ∈ C ∧ IsPreconnected C := by
    intro a b w
    induction w with
    | @nil a =>
      exact ⟨{a.1}, singleton_subset_iff.mpr (G.V_subset_U a.2), rfl, rfl, isPreconnected_singleton⟩
    | @cons a c b hadj _ ih =>
      obtain ⟨C, hC, hc, hb, hpre⟩ := ih
      obtain ⟨-, -, -, e, he, hae, hce⟩ := hadj
      refine ⟨closure e ∪ C, union_subset (G.closure_subset_U he) hC, .inl hae.1, .inr hb, ?_⟩
      exact (hcl e he).union c.1 hce.1 hc hpre
  have hV : ∀ y (hy : y ∈ G.V), ∃ t, t ⊆ G.U ∧ x₀ ∈ t ∧ y ∈ t ∧ IsPreconnected t := fun y hy => by
    obtain ⟨w⟩ := h ⟨x₀, hx₀⟩ ⟨y, hy⟩
    exact key w
  refine isPreconnected_of_forall x₀ fun y hy => ?_
  by_cases hyV : y ∈ G.V
  · exact hV y hyV
  · obtain ⟨e, he, hye⟩ := exists_edge_of_mem G hy hyV
    obtain ⟨u, hu⟩ := hends e he
    have huV : u ∈ G.V := (tilde_eq_inter_V G he ▸ hu).2
    obtain ⟨C, hC, hx, hu', hpre⟩ := hV u huV
    exact ⟨C ∪ closure e, union_subset hC (G.closure_subset_U he), .inl hx,
      .inr (subset_closure hye),
      hpre.union u hu' hu.1 (hcl e he)⟩

section Three

variable {Γ₂ : Painting S}

/-- **`τ'(v)` is left by at most two edges of a cuff.** This uses the third statement of (6.6) for
the
region that is the disc pasted onto the cuff, and `no_three_arcs`. -/
theorem three_mixed (hS : IsSurface S) {D₂ : Drawing Shat} (hD₂ : IsSkHat cap Γ₂ D₂)
  (hl₂ : LoopFree D₂)
    {ρ : Drawing Shat} (hρ : ρ.IsSubdrawing D₂)
    (hconn : ∀ r ∈ D₂.regions,
      ((GM19.Drawing.adj (ρ.interSet (closure r))).induce (ρ.interSet (closure r)).V).Preconnected)
    {Θ : Set S} (hΘ : Θ ∈ cuffs S) {f₁ f₂ f₃ : Set S} (h₁ : f₁ ∈ Γ₂.E) (h₂ : f₂ ∈ Γ₂.E)
      (h₃ : f₃ ∈ Γ₂.E)
    (h12 : f₁ ≠ f₂) (h13 : f₁ ≠ f₃) (h23 : f₂ ≠ f₃) (hs₁ : f₁ ⊆ Θ) (hs₂ : f₂ ⊆ Θ) (hs₃ : f₃ ⊆ Θ)
    (hm₁ : Mixed (cap.emb ⁻¹' ρ.V) f₁) (hm₂ : Mixed (cap.emb ⁻¹' ρ.V) f₂)
    (hm₃ : Mixed (cap.emb ⁻¹' ρ.V) f₃) : False := by
  have hinj := cap.isEmbedding.injective
  have hClosed := cap.isClosedEmbedding hS
  have hO : IsOArc Θ := (cuff_statement S hS).2.2 Θ hΘ
  have hcΘ : IsClosed Θ := hO.isCompact.isClosed
  have hDisc := cap.cuffDisc_closedDisc Θ hΘ
  have hF : IsOArc (cap.emb '' Θ) := cap.cuffDisc_bd Θ hΘ ▸ hDisc.isOArc_discBd
  set r := cap.cuffDisc Θ with hrdef
  have hr : r ∈ D₂.regions := cuffDisc_mem_regions hD₂ hΘ
  set T := ρ.interSet (closure r) with hTdef
  have hclr : closure r = r ∪ cap.emb '' Θ := cap.closure_cuffDisc hΘ
  have hrU : ∀ {x}, x ∈ r → x ∉ D₂.U := by
    intro x hx hU
    rw [hD₂.hU] at hU
    obtain ⟨y, -, rfl⟩ := hU
    have : cap.emb y ∈ (range cap.emb)ᶜ := by
      rw [cap.compl_eq]
      exact mem_iUnion₂.2 ⟨Θ, hΘ, hx⟩
    exact this (mem_range_self y)
  have hρU : ρ.V ⊆ D₂.U := hρ.1.trans D₂.V_subset_U
  have hTE : ∀ e ∈ T.E, e ∈ ρ.E ∧ e ⊆ closure r := by
    intro e he
    rw [hTdef, Drawing.interSet, Drawing.span_E] at he
    exact he.1
  have hTV : ∀ x ∈ T.V, x ∈ ρ.V ∧ x ∈ closure r := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨hx.2, hx.1.2⟩
    · obtain ⟨e, ⟨he, -⟩, hxe⟩ := mem_iUnion₂.1 hx
      exact ⟨hxe.2, closure_minimal he.2 isClosed_closure hxe.1⟩
  have hin : ∀ {x}, x ∈ closure r → x ∈ D₂.U → x ∈ cap.emb '' Θ := by
    intro x hx hU
    rw [hclr] at hx
    exact hx.resolve_left fun h => hrU h hU
  have hTU : T.U ⊆ cap.emb '' Θ := by
    intro x hx
    by_cases hxV : x ∈ T.V
    · exact hin (hTV x hxV).2 (hρU (hTV x hxV).1)
    · obtain ⟨e, he, hxe⟩ := exists_edge_of_mem T hx hxV
      obtain ⟨heρ, hecl⟩ := hTE e he
      exact hin (hecl hxe) (D₂.closure_subset_U (hρ.2 heρ) (subset_closure hxe))
  have hedge : ∀ {f}, f ∈ Γ₂.E → f ⊆ Θ → cap.emb '' f ∈ D₂.E ∧ closure f ⊆ Θ := by
    intro f hf hfΘ
    obtain ⟨x, hx⟩ := hf.2.2.1.nonempty
    have h2 := (edge_sub_cuff Γ₂ hΘ hf ⟨x, hx, hfΘ hx⟩).2
    exact ⟨hD₂.edge_iff.mpr ⟨f, sk_of_edge Γ₂ hf h2, rfl⟩, closure_minimal hfΘ hcΘ⟩
  have hdisj : ∀ {f}, f ∈ Γ₂.E → f ⊆ Θ → Mixed (cap.emb ⁻¹' ρ.V) f → Disjoint T.U (cap.emb '' f)
    := by
    intro f hf hfΘ hmix
    obtain ⟨hE, -⟩ := hedge hf hfΘ
    refine disjoint_left.mpr fun x hxT hxf => ?_
    have hxV : x ∉ D₂.V := (hE.2.1 hxf).2
    have hxTV : x ∉ T.V := fun h => hxV (hρ.1 (hTV x h).1)
    obtain ⟨e, he, hxe⟩ := exists_edge_of_mem T hxT hxTV
    have heρ := (hTE e he).1
    obtain rfl := arcComp_eq_of_mem (hρ.2 heρ) hE hxe hxf
    refine hmix.2 fun a ha => ?_
    have h' : cap.emb a ∈ tilde (cap.emb '' f) := by
      rw [tilde_emb hS]
      exact mem_image_of_mem _ ha
    rw [tilde_eq_inter_V ρ heρ] at h'
    exact h'.2
  have hend : ∀ {f}, f ∈ Γ₂.E → f ⊆ Θ → ∀ {a}, a ∈ tilde f ∩ cap.emb ⁻¹' ρ.V → cap.emb a ∈ T.V := by
    intro f hf hfΘ a ha
    have hab : cap.emb a ∈ cap.emb '' Θ := mem_image_of_mem _ ((hedge hf hfΘ).2 ha.1.1)
    have hmem : cap.emb a ∈ closure r := by
      rw [hclr]
      exact .inr hab
    exact .inl ⟨⟨ha.2, hmem⟩, ha.2⟩
  have hclose : ∀ {f}, f ∈ Γ₂.E → f ⊆ Θ → Mixed (cap.emb ⁻¹' ρ.V) f →
      (closure (cap.emb '' f) ∩ T.U).Nonempty := by
    intro f hf hfΘ hmix
    obtain ⟨a, ha⟩ := hmix.1
    refine ⟨cap.emb a, ?_, T.V_subset_U (hend hf hfΘ ha)⟩
    rw [hClosed.closure_image_eq]
    exact mem_image_of_mem _ ha.1.1
  have hpre : ∀ {f}, f ∈ Γ₂.E → IsPreconnected (cap.emb '' f) := fun hf =>
    (edge_preconnected Γ₂ hf).image _ cap.isEmbedding.continuous.continuousOn
  have hsubF : ∀ {f : Set S}, f ⊆ Θ → cap.emb '' f ⊆ cap.emb '' Θ := fun h => image_mono h
  have hdd : ∀ {f g}, f ∈ Γ₂.E → g ∈ Γ₂.E → f ≠ g → Disjoint (cap.emb '' f) (cap.emb '' g) := by
    intro f g hf hg hne
    refine (disjoint_image_iff hinj).mpr (disjoint_left.mpr fun x hxf hxg => hne ?_)
    exact arcComp_eq_of_mem hf hg hxf hxg
  obtain ⟨a₃, ha₃⟩ := hm₃.1
  have hTne : T.V.Nonempty := ⟨_, hend h₃ hs₃ ha₃⟩
  have hTconn : IsPreconnected T.U := by
    refine drawing_U_preconnected T hTne (fun e he => ?_) (hconn r hr)
    obtain ⟨u, v, -, ht, -⟩ := hl₂ e (hρ.2 (hTE e he).1)
    exact ht ▸ ⟨u, .inl rfl⟩
  obtain ⟨x, hx⟩ := h₃.2.2.1.nonempty
  have h2₃ := (edge_sub_cuff Γ₂ hΘ h₃ ⟨x, hx, hs₃ hx⟩).2
  obtain ⟨u, v, huv, ht⟩ := ncard_eq_two.mp h2₃
  have htA : tilde (cap.emb '' f₃) = {cap.emb u, cap.emb v} := by
    rw [tilde_emb hS, ht, image_pair]
  have hendA : cap.emb u ∈ T.U ∨ cap.emb v ∈ T.U := by
    have hA := T.V_subset_U (hend h₃ hs₃ ha₃)
    have ha : a₃ ∈ ({u, v} : Set S) := ht ▸ ha₃.1
    rcases ha with rfl | rfl
    · exact .inl hA
    · exact .inr hA
  exact no_three_arcs hF (fun h => huv (hinj h)) hTconn hTU (hpre h₁) (hpre h₂) (hpre h₃)
    (h₁.2.2.1.nonempty.image _) (h₂.2.2.1.nonempty.image _) (hsubF hs₁) (hsubF hs₂) (hsubF hs₃)
    (by rw [hClosed.closure_image_eq]; exact image_mono (hedge h₃ hs₃).2) (hdisj h₁ hs₁ hm₁)
    (hdisj h₂ hs₂ hm₂) (hdisj h₃ hs₃ hm₃) (hdd h₁ h₂ h12) (hdd h₁ h₃ h13) (hdd h₂ h₃ h23)
    (hclose h₁ hs₁ hm₁) (hclose h₂ hs₂ hm₂) htA hendA

end Three

omit [T2Space S] in
theorem tilde_of_march (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) (h2 : (tilde e).ncard
  = 2) {a b : S}
    (ha : (Γ.γ e).head? = some a) (hb : (Γ.γ e).getLast? = some b) : tilde e = {a, b} := by
  have hlen : (Γ.γ e).length = 2 := by rw [Γ.length_γ he, h2]
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hlen
  rw [hxy] at ha hb
  simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons,
    List.getLast?_singleton] at ha hb
  subst ha hb
  rw [← Γ.γ_set e he, hxy]
  ext z
  simp

/-- **(6.2)** for a surface `Σ`, from (6.6). -/
theorem theorem_6_2_of_6_6 : Theorem62Statement.{0} := by
  classical
  intro S Shat _ _ _ _ cap hS
  have := cap.connected
  obtain ⟨k, hk⟩ := GraphMinor.GM19.theorem_6_6_proof Shat cap.isSurface cap.connected cap.bd_empty
  refine ⟨k + 1, ?_⟩
  intro Φ Γ₁ Γ₂ rad hf₁ hf₂ hn σv σe hσ hresp
  have hinj := cap.isEmbedding.injective
  have h3₁ := hf₁.internally_three_connected
  have h3₂ := hf₂.internally_three_connected
  obtain ⟨D₁, hD₁⟩ := exists_isSkHat hS cap Γ₁
  obtain ⟨D₂, hD₂⟩ := exists_isSkHat hS cap Γ₂
  have rad₂ := (Painting.exists_radialDrawing hS cap Γ₂ (h3₂.hatRegions_isOpenDisc hS cap)).some
  obtain ⟨hb₁, hrep⟩ := theorem_6_7_proof rad hS hD₁ h3₁
  have hb₂ := sk_block rad₂ hS hD₂ h3₂
  have hl₁ := sk_loopFree hS hD₁
  have hl₂ := sk_loopFree hS hD₂
  obtain ⟨τv, τe, hτ, -, hτv⟩ := exists_enlargement hS hD₁ hD₂ hl₂ hσ
  have hlt : (k : ℕ∞) < D₁.rep := by
    rw [hrep]
    refine lt_of_lt_of_le ?_ hn
    exact_mod_cast Nat.lt_succ_self k
  obtain ⟨ρ, hρ, hsub, -, -, hreg⟩ := hk D₁ D₂ (gm19_of_loopFree cap.bd_empty hl₁)
    (gm19_of_loopFree cap.bd_empty hl₂) hb₁ hb₂ hlt τv τe hτ
  have hmemV : ∀ {v}, v ∈ Γ₁.V → cap.emb v ∈ D₁.V := fun hv => hD₁.hV ▸ mem_image_of_mem _ hv
  let ℓ : S → Set S := fun v => cap.emb ⁻¹' (ρ (cap.emb v)).V
  have hle : ∀ v ∈ Γ₁.V, σv v ⊆ ℓ v := by
    intro v hv a ha
    have h₁ : cap.emb a ∈ (τv (cap.emb v)).V := by
      rw [hτv v hv]
      exact mem_image_of_mem _ ha
    exact (hsub _ (hmemV hv)).1 h₁
  have hρsub : ∀ {v}, v ∈ Γ₁.V → (ρ (cap.emb v)).IsSubdrawing D₂ := fun hv =>
    hρ.vertex_subdrawing _ (hmemV hv)
  have hinfl : IsInflation Γ₁ Γ₂ ℓ σe := by
    refine ⟨hσ.edge_mem, hσ.edge_size, hσ.edge_injOn, fun v hv => (hσ.vertex_nonempty v hv).mono
      (hle v hv),
      ?_, ?_, ?_, ?_⟩
    · intro v hv a ha
      have h₁ : cap.emb a ∈ D₂.V := (hρsub hv).1 ha
      rw [hD₂.hV] at h₁
      obtain ⟨b, hb, hab⟩ := h₁
      exact hinj hab ▸ hb
    · intro v hv
      have : Nonempty S := ⟨v⟩
      have hleft : Function.LeftInverse (Function.invFun cap.emb) cap.emb :=
        Function.leftInverse_invFun hinj
      have hrange : ∀ {x}, x ∈ (ρ (cap.emb v)).V → ∃ a, cap.emb a = x := by
        intro x hx
        have h₁ := (hρsub hv).1 hx
        rw [hD₂.hV] at h₁
        obtain ⟨a, -, rfl⟩ := h₁
        exact ⟨a, rfl⟩
      refine preconnected_image (Function.invFun cap.emb) (hρ.vertex_connected _ (hmemV hv)) ?_ ?_
      · ext a
        constructor
        · intro ha
          exact ⟨cap.emb a, ha, hleft a⟩
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨b, rfl⟩ := hrange hx
          change cap.emb (Function.invFun cap.emb (cap.emb b)) ∈ (ρ (cap.emb v)).V
          rw [hleft b]
          exact hx
      · intro x hx y hy hadj
        obtain ⟨a, rfl⟩ := hrange hx
        obtain ⟨b, rfl⟩ := hrange hy
        rw [hleft a, hleft b]
        obtain ⟨hne, hxV, hyV, e, he, hxe, hye⟩ := hadj
        exact adj_sk_of hS hD₂ ⟨hne, (hρsub hv).1 hxV, (hρsub hv).1 hyV, e, (hρsub hv).2 he, hxe,
          hye⟩
    · intro v₁ hv₁ v₂ hv₂ hne
      exact (hρ.vertex_disjoint _ (hmemV hv₁) _ (hmemV hv₂) fun h => hne (hinj h)).preimage cap.emb
    · intro e he i hi hi'
      have hmem : (Γ₁.γ e)[i] ∈ tilde e := by
        rw [← Γ₁.γ_set e he]
        exact List.getElem_mem hi
      exact hle _ (Γ₁.tilde_subset_V he hmem) (hσ.ends e he i hi hi')
  have hside : ∀ e ∈ Γ₁.E, ∀ Θ ∈ cuffs S, (e ∩ Θ).Nonempty →
      Painting.IsBorder e ∧ ∃ s ∈ Φ.sides, e ⊆ s ∧ s ⊆ Θ := by
    rintro e he Θ hΘ ⟨x, hxe, hxΘ⟩
    have hb : Painting.IsBorder e := ⟨x, hxe, cuff_sub_bd hΘ hxΘ⟩
    have hebd := (Γ₁.border_edge e he hb).2
    obtain ⟨s, hs, hes⟩ := exists_arcComp_superset he.2.2.1 (F := bd S \ Φ.V)
      fun y hy => ⟨hebd hy, fun hyΦ => Γ₁.disjoint_V he hy (hf₁.V_subset hyΦ)⟩
    refine ⟨hb, s, hs, hes, sub_cuff hΘ hs.2.2.1.isConnected.isPreconnected
      (hs.2.1.trans sdiff_subset) ⟨x, hes hxe, hxΘ⟩⟩
  have hmove : ∀ e ∈ Γ₁.E, ∀ Θ ∈ cuffs S, (e ∩ Θ).Nonempty → σe e ⊆ Θ := by
    intro e he Θ hΘ hm
    obtain ⟨hb, s, hs, hes, hsΘ⟩ := hside e he Θ hΘ hm
    exact ((hresp e he hb).2 s hs).1 hes |>.trans hsΘ
  have hcover : ∀ {Θ f : Set S}, Θ ∈ cuffs S → f ∈ Γ₂.E → f ⊆ Θ →
      (∃ v ∈ Γ₁.V, tilde f ⊆ ℓ v) ∨ ∃ e ∈ Γ₁.E, (e ∩ Θ).Nonempty ∧ f = σe e := by
    intro Θ f hΘ hf hfΘ
    refine cuff_cover hS hinfl ?_ hmove hΘ hf hfΘ
    intro Θ' hΘ' v hv f₁ h₁ f₂ h₂ f₃ h₃ h12 h13 h23 hs₁ hs₂ hs₃ hm₁ hm₂ hm₃
    exact three_mixed hS hD₂ hl₂ (hρsub hv) (fun r hr => hreg r hr _ (hmemV hv)) hΘ' h₁ h₂ h₃ h12
      h13 h23
      hs₁ hs₂ hs₃ hm₁ hm₂ hm₃
  refine ⟨ℓ, { hinfl with borders_iff := ?_, border_edge := ?_, orientation := ?_ }, hle⟩
  · intro e he Θ hΘ
    constructor
    · intro hm
      obtain ⟨y, hy⟩ := (hσ.edge_mem e he).2.2.1.nonempty
      exact ⟨y, hy, hmove e he Θ hΘ hm hy⟩
    · rintro ⟨y, hy, hyΘ⟩
      have hE := hσ.edge_mem e he
      obtain ⟨hs, h2⟩ := edge_sub_cuff Γ₂ hΘ hE ⟨y, hy, hyΘ⟩
      rcases hcover hΘ hE hs with ⟨v, hv, hsub'⟩ | ⟨e₀, he₀, hm, heq⟩
      · exfalso
        have h2' : (tilde e).ncard = 2 := by rw [← hσ.edge_size e he, h2]
        obtain ⟨u, w, huw, ht⟩ := ncard_eq_two.mp h2'
        have hsame : ∀ {x}, x ∈ tilde e → x = v := by
          intro x hx
          obtain ⟨a, hat, ha⟩ := (infl_ends hinfl he).2 x hx
          by_contra hne
          exact disjoint_left.mp (hinfl.vertex_disjoint x (Γ₁.tilde_subset_V he hx) v hv hne) ha
            (hsub' hat)
        exact huw ((hsame (ht ▸ .inl rfl)).trans (hsame (ht ▸ .inr rfl)).symm)
      · rw [hσ.edge_injOn he he₀ heq]
        exact hm
  · rintro e' hE ⟨x, hxe, hxb⟩ hnot
    have hΘ : connectedComponentIn (bd S) x ∈ cuffs S := ⟨x, hxb, rfl⟩
    have hx := mem_connectedComponentIn hxb
    rcases hcover hΘ hE (edge_sub_cuff Γ₂ hΘ hE ⟨x, hxe, hx⟩).1 with ⟨v, hv, hs⟩ | ⟨e, he, -, rfl⟩
    · exact ⟨v, hv, hs⟩
    · exact absurd ⟨e, he, rfl⟩ hnot
  · intro e he Θ hΘ hm f n n' hn₁ hn₂ hpre
    obtain ⟨hb, s, hs, hes, hsΘ⟩ := hside e he Θ hΘ hm
    have hE := hσ.edge_mem e he
    have hes' : σe e ⊆ s := ((hresp e he hb).2 s hs).1 hes
    have hO : IsOArc Θ := (cuff_statement S hS).2.2 Θ hΘ
    have hclS : closure s ⊆ Θ := closure_minimal hsΘ hO.isCompact.isClosed
    obtain ⟨u, w, huw, ht⟩ := ncard_eq_two.mp (Φ.side_shape s hs).1
    have hspre : IsPreconnected s := hs.2.2.1.isConnected.isPreconnected
    obtain ⟨p, hpΘ, hp⟩ := exists_notMem_closure hO huw hspre hsΘ hclS ht
    have h2 := (edge_sub_cuff Γ₁ hΘ he hm).2
    have h2' : (tilde (σe e)).ncard = 2 := by rw [hσ.edge_size e he, h2]
    exact precedes_of_dirAgrees f hclS hpΘ hp (hf₁.border_dir e he hb s hs hes)
      (hf₂.border_dir (σe e) hE (hresp e he hb).1 s hs hes') (edge_preconnected Γ₁ he)
      (edge_preconnected Γ₂ hE) (fun a b ha hb' => tilde_of_march Γ₁ he h2 ha hb')
      (fun a b ha hb' => tilde_of_march Γ₂ hE h2' ha hb') hn₁ hn₂ hpre

/-- **Theorem (6.2) of Graph Minors XIX**, page 339, by the proof on pages 342-343. -/
theorem theorem_6_2_proof : Theorem62Statement.{u} :=
  theorem_6_2_lift theorem_6_2_of_6_6

end GraphMinor.GM19
