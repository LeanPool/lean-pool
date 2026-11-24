/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Enl
public import LeanPool.GraphMinor.GM19.FrameMove

/-!
# Graph Minors XIX, proof of (6.2): the cover of a cuff

The last step of the proof of (6.2), page 343. Let `σ'` be an inflation of `Γ₁` in `Γ₂` such that
each
`σ'(v)` meets a cuff `Θ` in a connected part. The paper sees the circuit `C₂`
on `Θ` as the paths `P₁, …, P_t` joined by the edges `σ'(e₁), …, σ'(e_t)`. Hence an edge of `Γ₂` on
`Θ` is
either some `σ'(e_i)`, or has both ends in one `σ'(v)`.

We prove this in `cuff_cover`, in this form. A set `σ'(v)` with `v` on `Θ` is left by two edges
`σ'(e)`,
for the two edges `e` of `Γ₁` at `v` on `Θ`, and it is not left by a third, by the connectedness. So
the
vertices of `Θ` in sets `σ'(v)` with `v` on `Θ` are closed under following edges of `Θ`, and they
are all of
the vertices of `Γ₂` on `Θ`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

local notation "𝕀" => unitInterval

variable {S : Type} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
theorem sub_cuff {Θ C : Set S} (hΘ : Θ ∈ cuffs S) (hC : IsPreconnected C) (hb : C ⊆ bd S)
    (hm : (C ∩ Θ).Nonempty) : C ⊆ Θ := by
  obtain ⟨x, hxC, hxΘ⟩ := hm
  obtain ⟨z, -, rfl⟩ := hΘ
  rw [connectedComponentIn_eq hxΘ]
  exact hC.subset_connectedComponentIn hxC hb

omit [T2Space S] in
theorem cuff_sub_bd {Θ : Set S} (hΘ : Θ ∈ cuffs S) : Θ ⊆ bd S := by
  obtain ⟨z, -, rfl⟩ := hΘ
  exact connectedComponentIn_subset _ _

omit [T2Space S] in
theorem edge_preconnected (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) : IsPreconnected e :=
  he.2.2.1.isConnected.isPreconnected

omit [T2Space S] in
/-- An edge meeting a cuff is a border edge inside the cuff. -/
theorem edge_sub_cuff (Γ : Painting S) {Θ e : Set S} (hΘ : Θ ∈ cuffs S) (he : e ∈ Γ.E)
    (hm : (e ∩ Θ).Nonempty) : e ⊆ Θ ∧ (tilde e).ncard = 2 := by
  obtain ⟨x, hxe, hxΘ⟩ := hm
  obtain ⟨h2, hb⟩ := Γ.border_edge e he ⟨x, hxe, cuff_sub_bd hΘ hxΘ⟩
  exact ⟨sub_cuff hΘ (edge_preconnected Γ he) hb ⟨x, hxe, hxΘ⟩, h2⟩

omit [T2Space S] in
/-- Along a line from the vertex `v` to another vertex, the first part is in an edge at `v`. -/
theorem exists_first_edge (Γ : Painting S) {Θ L : Set S} (hΘ : Θ ∈ cuffs S) (hLΘ : L ⊆ Θ) {v w : S}
    (hL : IsLineWithEnds L v w) (_hvw : v ≠ w) (hv : v ∈ Γ.V) (hw : w ∈ Γ.V) :
    ∃ e ∈ Γ.E, e ⊆ Θ ∧ v ∈ tilde e ∧ (e ∩ L).Nonempty := by
  obtain ⟨φ, hφ, hr, h0, h1⟩ := exists_line_emb hL
  have hT : (φ ⁻¹' Γ.V \ {0}).Finite := (Γ.finite_V.preimage hφ.injective.injOn).subset sdiff_subset
  have h10 : (1 : 𝕀) ≠ 0 := one_ne_zero
  have hone : (1 : 𝕀) ∈ φ ⁻¹' Γ.V \ {0} := ⟨show φ 1 ∈ Γ.V by rw [h1]; exact hw, h10⟩
  obtain ⟨t₀, ht₀, hmin⟩ := Set.exists_min_image _ id hT ⟨1, hone⟩
  have hpos : (0 : ℝ) < t₀ := lt_of_le_of_ne t₀.2.1 fun h => ht₀.2 (Subtype.ext h.symm)
  let ψ : ℝ → S := fun x => φ (projIcc 0 1 zero_le_one x)
  have hψ : Continuous ψ := hφ.continuous.comp continuous_projIcc
  have hval : ∀ {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) t₀), ψ x = φ ⟨x, hx.1.le, hx.2.le.trans t₀.2.2⟩ :=
    fun {x} hx => congrArg φ (projIcc_of_mem _ ⟨hx.1.le, hx.2.le.trans t₀.2.2⟩)
  have hpc : IsPathConnected (ψ '' Ioo (0 : ℝ) t₀) :=
    ((convex_Ioo _ _).isPathConnected (nonempty_Ioo.mpr hpos)).image hψ
  have hinΘ : ψ '' Ioo (0 : ℝ) t₀ ⊆ Θ := by
    rintro _ ⟨x, -, rfl⟩
    exact hLΘ (hr ▸ mem_range_self _)
  have hsub : ψ '' Ioo (0 : ℝ) t₀ ⊆ Γ.U \ Γ.V := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Γ.bd_subset (cuff_sub_bd hΘ (hinΘ ⟨x, hx, rfl⟩)), fun hV => ?_⟩
    rw [hval hx] at hV
    have hmem : (⟨x, hx.1.le, hx.2.le.trans t₀.2.2⟩ : 𝕀) ∈ φ ⁻¹' Γ.V \ {0} :=
      ⟨hV, fun h => hx.1.ne' (congrArg Subtype.val h)⟩
    exact absurd (hmin _ hmem) (not_le.mpr hx.2)
  obtain ⟨e, he, hsupe⟩ := exists_arcComp_superset hpc hsub
  obtain ⟨y, hy⟩ := nonempty_Ioo.mpr hpos
  have hye : ψ y ∈ e := hsupe ⟨y, hy, rfl⟩
  have hyL : ψ y ∈ L := hr ▸ mem_range_self _
  have hyΘ : ψ y ∈ Θ := hLΘ hyL
  refine ⟨e, he, (edge_sub_cuff Γ hΘ he ⟨_, hye, hyΘ⟩).1, ⟨?_, fun h => Γ.disjoint_V he h hv⟩, _,
    hye, hyL⟩
  have hcl : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) t₀) := by
    rw [closure_Ioo hpos.ne]
    exact ⟨le_rfl, hpos.le⟩
  have h2 := image_closure_subset_closure_image hψ (mem_image_of_mem ψ hcl)
  have h3 : ψ 0 = v := by
    change φ (projIcc 0 1 zero_le_one 0) = v
    rw [projIcc_left]
    exact h0
  rw [h3] at h2
  exact closure_mono hsupe h2

/-- A vertex on a cuff is an end of two edges on the cuff. -/
theorem two_edges_at (hS : IsSurface S) (Γ : Painting S) {Θ : Set S} (hΘ : Θ ∈ cuffs S) {v : S}
    (hv : v ∈ Γ.V) (hvΘ : v ∈ Θ) :
    ∃ e₁ ∈ Γ.E, ∃ e₂ ∈ Γ.E, e₁ ≠ e₂ ∧ e₁ ⊆ Θ ∧ e₂ ⊆ Θ ∧ v ∈ tilde e₁ ∧ v ∈ tilde e₂ := by
  have hO : IsOArc Θ := (cuff_statement S hS).2.2 Θ hΘ
  have hcΘ : IsClosed Θ := hO.isCompact.isClosed
  obtain ⟨f⟩ := id hO
  obtain ⟨e, he, heΘ, -⟩ := exists_edge_on_cuff Γ ⟨Θ, hΘ⟩ f
  obtain ⟨x, hxe⟩ := he.2.2.1.nonempty
  have h2 := (edge_sub_cuff Γ hΘ he ⟨x, hxe, heΘ hxe⟩).2
  obtain ⟨w, hwt, hwv⟩ := exists_ne_of_one_lt_ncard (show 1 < (tilde e).ncard by omega) v
  have hwΘ : w ∈ Θ := closure_minimal heΘ hcΘ hwt.1
  have hwV : w ∈ Γ.V := Γ.tilde_subset_V he hwt
  obtain ⟨A₁, A₂, h₁, h₂, hU, hI⟩ := hO.lines hvΘ hwΘ hwv.symm
  have hA₁ : A₁ ⊆ Θ := hU ▸ subset_union_left
  have hA₂ : A₂ ⊆ Θ := hU ▸ subset_union_right
  obtain ⟨e₁, he₁, hs₁, ht₁, hm₁⟩ := exists_first_edge Γ hΘ hA₁ h₁ hwv.symm hv hwV
  obtain ⟨e₂, he₂, hs₂, ht₂, hm₂⟩ := exists_first_edge Γ hΘ hA₂ h₂ hwv.symm hv hwV
  refine ⟨e₁, he₁, e₂, he₂, ?_, hs₁, hs₂, ht₁, ht₂⟩
  rintro rfl
  obtain ⟨y, hye, hy⟩ := (isPreconnected_closed_iff.mp (edge_preconnected Γ he₁)) A₁ A₂
    (isClosed_of_cuffLine h₁) (isClosed_of_cuffLine h₂) (hU ▸ hs₁) hm₁ hm₂
  rw [hI] at hy
  rcases hy with rfl | rfl
  · exact Γ.disjoint_V he₁ hye hv
  · exact Γ.disjoint_V he₁ hye hwV

/-- One end of `f` is in `Y` and another is not. -/
def Mixed (Y f : Set S) : Prop := (tilde f ∩ Y).Nonempty ∧ ¬ tilde f ⊆ Y

variable {Γ₁ Γ₂ : Painting S} {ℓ : S → Set S} {σe : Set S → Set S}

omit [T2Space S] in
theorem mixed_image (h : IsInflation Γ₁ Γ₂ ℓ σe) {e : Set S} (he : e ∈ Γ₁.E) (h2 : (tilde e).ncard
  = 2)
    {v : S} (hv : v ∈ Γ₁.V) (hvt : v ∈ tilde e) : Mixed (ℓ v) (σe e) := by
  obtain ⟨-, hends⟩ := infl_ends h he
  obtain ⟨a, hat, ha⟩ := hends v hvt
  obtain ⟨y, hyt, hyv⟩ := exists_ne_of_one_lt_ncard (show 1 < (tilde e).ncard by omega) v
  obtain ⟨b, hbt, hb⟩ := hends y hyt
  refine ⟨⟨a, hat, ha⟩, fun hsub => ?_⟩
  exact disjoint_left.mp (h.vertex_disjoint y (Γ₁.tilde_subset_V he hyt) v hv hyv) hb (hsub hbt)

/-- **The cover of a cuff** (Graph Minors XIX, proof of (6.2), page 343). -/
theorem cuff_cover (hS : IsSurface S) (h : IsInflation Γ₁ Γ₂ ℓ σe)
    (hthree : ∀ Θ ∈ cuffs S, ∀ v ∈ Γ₁.V, ∀ f₁ ∈ Γ₂.E, ∀ f₂ ∈ Γ₂.E, ∀ f₃ ∈ Γ₂.E, f₁ ≠ f₂ → f₁ ≠ f₃ →
      f₂ ≠ f₃ → f₁ ⊆ Θ → f₂ ⊆ Θ → f₃ ⊆ Θ → Mixed (ℓ v) f₁ → Mixed (ℓ v) f₂ → Mixed (ℓ v) f₃ → False)
    (hmove : ∀ e ∈ Γ₁.E, ∀ Θ ∈ cuffs S, (e ∩ Θ).Nonempty → σe e ⊆ Θ)
    {Θ f : Set S} (hΘ : Θ ∈ cuffs S) (hf : f ∈ Γ₂.E) (hfΘ : f ⊆ Θ) :
    (∃ v ∈ Γ₁.V, tilde f ⊆ ℓ v) ∨ ∃ e ∈ Γ₁.E, (e ∩ Θ).Nonempty ∧ f = σe e := by
  classical
  have hO : IsOArc Θ := (cuff_statement S hS).2.2 Θ hΘ
  have hcΘ : IsClosed Θ := hO.isCompact.isClosed
  have hclo : ∀ {g : Set S}, g ⊆ Θ → closure g ⊆ Θ := fun hg => closure_minimal hg hcΘ
  have hsize₂ : ∀ {g}, g ∈ Γ₂.E → g ⊆ Θ → (tilde g).ncard = 2 := fun {g} hg hgΘ => by
    obtain ⟨x, hx⟩ := hg.2.2.1.nonempty
    exact (edge_sub_cuff Γ₂ hΘ hg ⟨x, hx, hgΘ hx⟩).2
  have hmeet : ∀ {e : Set S}, e ∈ Γ₁.E → e ⊆ Θ → (e ∩ Θ).Nonempty := fun {e} he heΘ => by
    obtain ⟨x, hx⟩ := he.2.2.1.nonempty
    exact ⟨x, hx, heΘ hx⟩
  -- Only the two edges at `v` leave `σ'(v)`.
  have hCY : ∀ v ∈ Γ₁.V, v ∈ Θ → ∀ g ∈ Γ₂.E, g ⊆ Θ → Mixed (ℓ v) g →
      ∃ e ∈ Γ₁.E, e ⊆ Θ ∧ v ∈ tilde e ∧ g = σe e := by
    intro v hv hvΘ g hg hgΘ hmix
    obtain ⟨e₁, he₁, e₂, he₂, hne, hs₁, hs₂, ht₁, ht₂⟩ := two_edges_at hS Γ₁ hΘ hv hvΘ
    by_cases h₁ : g = σe e₁
    · exact ⟨e₁, he₁, hs₁, ht₁, h₁⟩
    by_cases h₂ : g = σe e₂
    · exact ⟨e₂, he₂, hs₂, ht₂, h₂⟩
    have hz₁ := (edge_sub_cuff Γ₁ hΘ he₁ (hmeet he₁ hs₁)).2
    have hz₂ := (edge_sub_cuff Γ₁ hΘ he₂ (hmeet he₂ hs₂)).2
    exact (hthree Θ hΘ v hv _ (h.edge_mem _ he₁) _ (h.edge_mem _ he₂) g hg
      (fun heq => hne (h.edge_injOn he₁ he₂ heq)) (Ne.symm h₁) (Ne.symm h₂)
      (hmove e₁ he₁ Θ hΘ (hmeet he₁ hs₁)) (hmove e₂ he₂ Θ hΘ (hmeet he₂ hs₂)) hgΘ
      (mixed_image h he₁ hz₁ hv ht₁) (mixed_image h he₂ hz₂ hv ht₂) hmix).elim
  let Y : Set S := {a | a ∈ Γ₂.V ∧ a ∈ Θ ∧ ∃ v ∈ Γ₁.V, v ∈ Θ ∧ a ∈ ℓ v}
  have hclosed : ∀ g ∈ Γ₂.E, g ⊆ Θ → ∀ a ∈ tilde g, a ∈ Y → ∀ b ∈ tilde g, b ∈ Y := by
    rintro g hg hgΘ a hat ⟨-, -, v, hv, hvΘ, ha⟩ b hbt
    have hbV := Γ₂.tilde_subset_V hg hbt
    have hbΘ := hclo hgΘ hbt.1
    by_cases hb : b ∈ ℓ v
    · exact ⟨hbV, hbΘ, v, hv, hvΘ, hb⟩
    obtain ⟨e, he, heΘ, -, rfl⟩ := hCY v hv hvΘ g hg hgΘ ⟨⟨a, hat, ha⟩, fun hs => hb (hs hbt)⟩
    obtain ⟨y, hyt, hby⟩ := (infl_ends h he).1 b hbt
    exact ⟨hbV, hbΘ, y, Γ₁.tilde_subset_V he hyt, hclo heΘ hyt.1, hby⟩
  have hYne : Y.Nonempty := by
    obtain ⟨c⟩ := id hO
    obtain ⟨e, he, heΘ, -⟩ := exists_edge_on_cuff Γ₁ ⟨Θ, hΘ⟩ c
    have heΘ' : e ⊆ Θ := heΘ
    have h2 := (edge_sub_cuff Γ₁ hΘ he (hmeet he heΘ')).2
    obtain ⟨v, hvt⟩ : (tilde e).Nonempty := nonempty_of_ncard_ne_zero (by omega)
    have hvV := Γ₁.tilde_subset_V he hvt
    obtain ⟨a, hat, ha⟩ := (infl_ends h he).2 v hvt
    have hE := h.edge_mem e he
    exact ⟨a, Γ₂.tilde_subset_V hE hat, hclo (hmove e he Θ hΘ (hmeet he heΘ')) hat.1, v, hvV,
      hclo heΘ' hvt.1, ha⟩
  have hYsub : Y ⊆ Γ₂.V := fun a ha => ha.1
  -- All vertices of `Γ₂` on `Θ` lie in `Y`, because `Θ` is connected.
  have hall : ∀ a ∈ Γ₂.V, a ∈ Θ → a ∈ Y := by
    intro a₀ ha₀ ha₀Θ
    by_contra hnot
    let P : Set S → Prop := fun g => (tilde g ∩ Y).Nonempty
    have hF : {g | g ∈ Γ₂.E ∧ g ⊆ Θ}.Finite := Γ₂.finite_edges.subset fun g hg => hg.1
    let Z₁ : Set S := Y ∪ ⋃ g ∈ {g | g ∈ {g | g ∈ Γ₂.E ∧ g ⊆ Θ} ∧ P g}, closure g
    let Z₂ : Set S := ((Γ₂.V ∩ Θ) \ Y) ∪ ⋃ g ∈ {g | g ∈ {g | g ∈ Γ₂.E ∧ g ⊆ Θ} ∧ ¬ P g}, closure g
    have hF₁ : {g | g ∈ {g | g ∈ Γ₂.E ∧ g ⊆ Θ} ∧ P g}.Finite :=
      hF.subset fun _ hg => hg.1
    have hF₂ : {g | g ∈ {g | g ∈ Γ₂.E ∧ g ⊆ Θ} ∧ ¬ P g}.Finite :=
      hF.subset fun _ hg => hg.1
    have hV₂ : ((Γ₂.V ∩ Θ) \ Y).Finite := (Γ₂.finite_V.subset inter_subset_left).sdiff
    have hc₁ : IsClosed Z₁ := (Γ₂.finite_V.subset hYsub).isClosed.union
      (hF₁.isClosed_biUnion fun _ _ => isClosed_closure)
    have hc₂ : IsClosed Z₂ := hV₂.isClosed.union
      (hF₂.isClosed_biUnion fun _ _ => isClosed_closure)
    have hcover : Θ ⊆ Z₁ ∪ Z₂ := by
      intro x hxΘ
      by_cases hxV : x ∈ Γ₂.V
      · by_cases hxY : x ∈ Y
        · exact .inl (.inl hxY)
        · exact .inr (.inl ⟨⟨hxV, hxΘ⟩, hxY⟩)
      · have hm : x ∈ Γ₂.U \ Γ₂.V := ⟨Γ₂.bd_subset (cuff_sub_bd hΘ hxΘ), hxV⟩
        obtain ⟨g, hg, hxg⟩ := exists_arcComp_superset (isPathConnected_singleton x)
          (singleton_subset_iff.mpr hm)
        have hgΘ := (edge_sub_cuff Γ₂ hΘ hg ⟨x, hxg rfl, hxΘ⟩).1
        by_cases hPg : P g
        · exact .inl (.inr (mem_iUnion₂.2 ⟨g, ⟨⟨hg, hgΘ⟩, hPg⟩, subset_closure (hxg rfl)⟩))
        · exact .inr (.inr (mem_iUnion₂.2 ⟨g, ⟨⟨hg, hgΘ⟩, hPg⟩, subset_closure (hxg rfl)⟩))
    have hne₁ : (Θ ∩ Z₁).Nonempty := by
      obtain ⟨y, hy⟩ := hYne
      exact ⟨y, hy.2.1, .inl hy⟩
    have hne₂ : (Θ ∩ Z₂).Nonempty := ⟨a₀, ha₀Θ, .inl ⟨⟨ha₀, ha₀Θ⟩, hnot⟩⟩
    have hconn : IsPreconnected Θ := by
      obtain ⟨c⟩ := id hO
      have : ConnectedSpace (Θ : Set S) := c.surjective.connectedSpace c.continuous
      exact isPreconnected_iff_preconnectedSpace.mpr inferInstance
    obtain ⟨z, -, hz₁, hz₂⟩ := (isPreconnected_closed_iff.mp hconn) Z₁ Z₂ hc₁ hc₂ hcover hne₁ hne₂
    have hvert : ∀ {g}, g ∈ Γ₂.E → z ∈ closure g → z ∉ g → z ∈ tilde g := fun _ hc hn => ⟨hc, hn⟩
    rcases hz₁ with hzY | hz₁ <;> rcases hz₂ with hzo | hz₂
    · exact hzo.2 hzY
    · obtain ⟨g, ⟨⟨hgE, -⟩, hPg⟩, hzg⟩ := mem_iUnion₂.1 hz₂
      exact hPg ⟨z, ⟨hzg, fun hin => Γ₂.disjoint_V hgE hin hzY.1⟩, hzY⟩
    · obtain ⟨g, ⟨⟨hgE, hgΘ⟩, a, hat, haY⟩, hzg⟩ := mem_iUnion₂.1 hz₁
      have hzt : z ∈ tilde g := ⟨hzg, fun hin => Γ₂.disjoint_V hgE hin hzo.1.1⟩
      exact hzo.2 (hclosed g hgE hgΘ a hat haY z hzt)
    · obtain ⟨g, ⟨⟨hgE, hgΘ⟩, a, hat, haY⟩, hzg⟩ := mem_iUnion₂.1 hz₁
      obtain ⟨g', ⟨⟨hgE', hgΘ'⟩, hPg'⟩, hzg'⟩ := mem_iUnion₂.1 hz₂
      by_cases hzV : z ∈ Γ₂.V
      · have hzt : z ∈ tilde g := ⟨hzg, fun hin => Γ₂.disjoint_V hgE hin hzV⟩
        have hzt' : z ∈ tilde g' := ⟨hzg', fun hin => Γ₂.disjoint_V hgE' hin hzV⟩
        exact hPg' ⟨z, hzt', hclosed g hgE hgΘ a hat haY z hzt⟩
      · have hin : ∀ {g : Set S}, g ∈ Γ₂.E → z ∈ closure g → z ∈ g := fun {g} hg hc =>
          by_contra fun hn => hzV (Γ₂.tilde_subset_V hg ⟨hc, hn⟩)
        obtain rfl := arcComp_eq_of_mem hgE hgE' (hin hgE hzg) (hin hgE' hzg')
        exact hPg' ⟨a, hat, haY⟩
  have h2 := hsize₂ hf hfΘ
  obtain ⟨a, hat⟩ : (tilde f).Nonempty := nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨-, -, v, hv, hvΘ, ha⟩ := hall a (Γ₂.tilde_subset_V hf hat) (hclo hfΘ hat.1)
  by_cases hsub : tilde f ⊆ ℓ v
  · exact .inl ⟨v, hv, hsub⟩
  · obtain ⟨e, he, heΘ, -, rfl⟩ := hCY v hv hvΘ f hf hfΘ ⟨⟨a, hat, ha⟩, hsub⟩
    exact .inr ⟨e, he, hmeet he heΘ, rfl⟩

end GraphMinor.GM19
