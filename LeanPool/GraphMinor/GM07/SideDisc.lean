/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.TameLines
public import LeanPool.GraphMinor.GM06.Section3Dual

/-!
# A disc around one side of a vertex separation

Let `Γ` be a drawing in a sphere, with two disjoint discs `B₀` and `E₀` that its edges keep out of.
Let `X` be a set of vertices that cuts `Γ` so that the part `K` next to
`B₀` misses `E₀`. Then a disc holds `B₀` and misses the inside of `E₀`, and its boundary meets `Γ`
only in `X`. This is `exists_disc_of_side`, the step from a Menger separator
to a curve.
-/

public section

namespace GraphMinor.GM07

open Set Topology Metric Function GraphMinor.Surface GraphMinor.GM11

local notation "I" => unitInterval

variable {T : Type} [TopologicalSpace T]

/-- Star discs at finitely many vertices, disjoint, each off a given closed set. -/
theorem exists_star_family (hS : IsClosedSurface T) (Γ : Drawing T) {K : Set T}
  (hK : K ⊆ Γ.V) {P : T → Set T} (hP : ∀ v ∈ K, IsClosed (P v)) (hvP : ∀ v ∈ K, v ∉ P v) :
    ∃ R : T → Set T, (∀ v ∈ K, IsStarDisc Γ v (R v) ∧ Disjoint (R v) (P v))
      ∧ ∀ u ∈ K, ∀ v ∈ K, u ≠ v → Disjoint (R u) (R v) := by
  have ht2 : T2Space T := hS.2.1
  obtain ⟨Uo, hUo, hdU⟩ := (Γ.finite_V.subset hK).t2_separation
  have hex : ∀ v ∈ K, ∃ R, IsStarDisc Γ v R ∧ R ⊆ Uo v ∩ (P v)ᶜ := fun v hv =>
    exists_starDisc hS Γ (hK hv) ((hUo v).2.inter (hP v hv).isOpen_compl) ⟨(hUo v).1, hvP v hv⟩
  choose! R hR hsub using hex
  refine ⟨R, fun v hv => ⟨hR v hv, disjoint_left.mpr fun x hx h => (hsub v hv hx).2 h⟩,
    fun u hu v hv huv => ?_⟩
  exact (hdU hu hv huv).mono ((hsub u hu).trans inter_subset_left) ((hsub v hv).trans
    inter_subset_left)

variable [T2Space T] {H : Drawing T} {f : Set T} {γ : I → T}

theorem EdgeParam.closure_eq (h : EdgeParam H f γ) : closure f = range γ := by
  have h1 := h.closure_Ioo (τ := 1) zero_lt_one
  rw [h.img] at h1
  rw [h1, ← image_univ]
  congr 1
  ext t
  exact ⟨fun _ => trivial, fun _ => ⟨unitInterval.nonneg t, unitInterval.le_one t⟩⟩

theorem EdgeParam.exists_orient (hf : f ∈ H.E) {u : T} (hu : u ∈ closure f)
  (huV : u ∈ H.V) : ∃ γ, EdgeParam H f γ ∧ γ 0 = u := by
  obtain ⟨γ, h1, h2, h3, h4, h5⟩ := exists_edge_param H hf
  have hγ : EdgeParam H f γ := ⟨h1, h2, h3, h4, h5⟩
  rw [hγ.closure_eq] at hu
  obtain ⟨z, rfl⟩ := hu
  by_cases h0 : z = 0
  · exact ⟨γ, hγ, by rw [h0]⟩
  by_cases h6 : z = 1
  · exact ⟨_, hγ.rev, by simp [h6]⟩
  · exact absurd huV (hγ.not_V hf (unitInterval.pos_iff_ne_zero.mpr h0)
      (unitInterval.lt_one_iff_ne_one.mpr h6))

/-- The closure of an edge is a union of atoms. -/
theorem isGammaNice_closure {Γ : Drawing T} {H : Drawing T} (hH : H.E ⊆ Γ.E) (hV : H.V ⊆ Γ.V)
  (hf : f ∈ H.E) (hγ : EdgeParam H f γ) : IsGammaNice Γ (closure f) := by
  refine ⟨insert f ((fun v => ({v} : Set T)) '' (closure f ∩ H.V)), ?_, ?_⟩
  · rintro _ (rfl | ⟨v, hv, rfl⟩)
    · exact .inl (.inr (hH hf))
    · exact .inl (.inl ⟨v, hV hv.2, rfl⟩)
  · apply Subset.antisymm
    · intro x hx
      rw [hγ.closure_eq] at hx
      obtain ⟨z, rfl⟩ := hx
      by_cases hv : γ z ∈ H.V
      · exact ⟨{γ z}, .inr ⟨γ z, ⟨hγ.closure_eq ▸ mem_range_self z, hv⟩, rfl⟩, rfl⟩
      · obtain ⟨h1, h2⟩ := hγ.pos_of_ne hv
        exact ⟨f, .inl rfl, hγ.mem_edge h1 h2⟩
    · rintro x ⟨_, (rfl | ⟨v, hv, rfl⟩), hx⟩
      · exact subset_closure hx
      · obtain rfl := hx
        exact hv.1

omit [T2Space T] in
/-- The boundary curve of a drawing on it is a union of atoms. -/
theorem isGammaNice_of_U {Γ D : Drawing T} (hE : D.E ⊆ Γ.E) (hV : D.V ⊆ Γ.V) : IsGammaNice Γ D.U
  := by
  refine ⟨D.E ∪ (fun v => ({v} : Set T)) '' D.V, ?_, ?_⟩
  · rintro _ (h | ⟨v, hv, rfl⟩)
    · exact .inl (.inr (hE h))
    · exact .inl (.inl ⟨v, hV hv, rfl⟩)
  · apply Subset.antisymm
    · intro x hx
      by_cases hv : x ∈ D.V
      · exact ⟨{x}, .inr ⟨x, hv, rfl⟩, rfl⟩
      · obtain ⟨e, he, h⟩ := D.exists_edge_of_mem hx hv
        exact ⟨e, .inl he, h⟩
    · rintro x ⟨_, h | ⟨v, hv, rfl⟩, hx⟩
      · exact (h.2.1 hx).1
      · obtain rfl := hx
        exact D.V_subset_U hv

/-- What the proof of `exists_disc_of_side` needs of the middle piece `γ '' Icc s t` of an edge `f`
of `Γ` that starts in `K`. -/
structure IsPiece (Γ : Drawing T) (K X : Set T) (R : T → Set T) (f : Set T) (L : Set T) (a b : T)
  (u v : T) : Prop where
  edge : f ∈ Γ.E
  line : IsLineWithEnds L a b
  ne : a ≠ b
  sub : L ⊆ closure f
  ends_mem : u ∈ K
  a_bd : a ∈ discBd (R u)
  a_notV : a ∉ Γ.V
  b_mem : (v ∈ K ∧ b ∈ discBd (R v) ∧ b ∉ Γ.V) ∨ v ∉ K ∧ b ∈ X
  vertex : ∀ x ∈ L, x ∈ Γ.V → x = b ∧ b ∈ X
  disc : ∀ w ∈ K, ∀ x ∈ L, x ∈ R w → x = a ∨ x = b
  rest : ∀ x ∈ f, x ∉ L → ∃ w ∈ K, x ∈ discInt (R w)
  onEdge : ∀ x ∈ L, x ∈ f ∨ x ∈ Γ.V

/-- The cut of an edge gives a piece. -/
theorem exists_piece {Γ Γ₁ : Drawing T} {K X : Set T} {R : T → Set T}
  (hman : ∀ x : T, IsManifoldPoint x) (hE : Γ.E ⊆ Γ₁.E) (hV : Γ.V ⊆ Γ₁.V) (hVK : K ⊆ Γ.V)
    (hR : ∀ v ∈ K, IsStarDisc Γ₁ v (R v))
    (hγ : EdgeParam Γ f γ) (hf : f ∈ Γ.E) (h0 : γ 0 ∈ K) (hm : ∀ v ∈ K, γ quarter₂ ∉ R v)
      (hoffV : ∀ v ∈ K, ∀ w ∈ Γ.V, w ≠ v → w ∉ R v)
    (hends : ∀ v ∈ K, (R v ∩ closure f).Nonempty → v ∈ closure f) (hK : γ 1 ∈ K ∪ X) :
    ∃ L a b, IsPiece Γ K X R f L a b (γ 0) (γ 1) := by
  have hR' : ∀ v ∈ K, IsClosedDisc (R v) ∧ v ∈ discInt (R v) ∧ IsOpen (discInt (R v)) := fun v hv =>
    ⟨(hR v hv).disc, (hR v hv).mem, (hR v hv).disc.isOpen_discInt hman⟩
  have hcl := hγ.closure_eq
  have hstar : ∀ v ∈ K, ∀ y ∈ R v ∩ range γ, ∃ C, IsPreconnected C ∧ C ⊆ range γ ∧ y ∈ C ∧ v ∈ C
    ∧ C \ {y} ⊆ discInt (R v) := fun v hv y hy => by
    rw [← hcl] at hy ⊢
    exact (hR v hv).star _ isClosed_closure (isGammaNice_closure hE hV hf hγ) y hy
  have hvert : ∀ v ∈ K, v ∈ range γ → v = γ 0 ∨ v = γ 1 := fun v hv h => by
    obtain ⟨z, rfl⟩ := h
    by_contra hn
    push Not at hn
    have h1 : 0 < z := unitInterval.pos_iff_ne_zero.mpr fun e => hn.1 (by rw [e])
    have h2 : z < 1 := unitInterval.lt_one_iff_ne_one.mpr fun e => hn.2 (by rw [e])
    exact hγ.not_V hf h1 h2 (hVK hv)
  have hq1 : quarter₂ < (1 : I) := unitInterval.lt_one_iff_ne_one.mpr fun e => by
    have h1 := congrArg Subtype.val e
    norm_num [quarter₂] at h1
  have hq0 : (0 : I) < quarter₂ := unitInterval.pos_iff_ne_zero.mpr fun e => by
    have h1 := congrArg Subtype.val e
    norm_num [quarter₂] at h1
  obtain ⟨s, t, hs0, hsm, hmt, hsb, hspre, hcase, hmiss⟩ := hγ.exists_cut hf hR' hstar h0 hq1 hm
    (fun h1 v hv he => hoffV v hv _ hγ.mem1 (fun e => h1 (e ▸ hv)) he)
    (fun v hv ⟨y, h1, h2⟩ => hvert v hv (hcl ▸ hends v hv ⟨y, h1, hcl.symm ▸ h2⟩))
    (fun hne h1 => ⟨hoffV _ h1 _ hγ.mem0 (Ne.symm hne), hoffV _ h0 _ hγ.mem1 hne⟩)
  have hst : s < t := hsm.trans hmt
  have hs1 : s < 1 := lt_of_lt_of_le hst (unitInterval.le_one t)
  have hle : ∀ τ ∈ Icc s t, 0 < τ := fun τ h => hs0.trans_le h.1
  have hsV : γ s ∉ Γ.V := hγ.not_V hf hs0 hs1
  have hbX : γ 1 ∉ K → γ 1 ∈ X := fun h => hK.resolve_left h
  have hcasesplit : t < 1 ∨ t = 1 := lt_or_eq_of_le (unitInterval.le_one t)
  refine ⟨γ '' Icc s t, γ s, γ t, ⟨hf, hγ.line_Icc hf hs0 hst, fun e => ?_, ?_, h0, hsb, hsV, ?_,
    ?_, ?_, ?_, ?_⟩⟩
  · rcases hcasesplit with h | h
    · exact hst.ne (hγ.inj ⟨hs0, hs1⟩ ⟨hs0.trans hst, h⟩ e)
    · rw [h] at e
      exact hsV (e ▸ hγ.mem1)
  · rintro _ ⟨τ, -, rfl⟩
    exact hcl ▸ mem_range_self τ
  · rcases hcase with ⟨h1, h2, h3, -⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, h3, hγ.not_V hf (hs0.trans hst) h2⟩
    · rw [h2]
      exact .inr ⟨h1, hbX h1⟩
  · rintro _ ⟨τ, hτ, rfl⟩ hv
    obtain ⟨-, h2⟩ := by_contra (fun hn : ¬ (0 < τ ∧ ¬ τ < 1) => hn ⟨hle τ hτ, fun h3
      => hγ.not_V hf (hle τ hτ) h3 hv⟩)
    have hτ1 : τ = 1 := le_antisymm (unitInterval.le_one τ) (not_lt.mp h2)
    have ht1 : t = 1 := le_antisymm (unitInterval.le_one t) (hτ1 ▸ hτ.2)
    rcases hcase with ⟨-, h3, -⟩ | ⟨h3, -⟩
    · exact absurd ht1 h3.ne
    · rw [hτ1, ht1]
      exact ⟨rfl, hbX h3⟩
  · rintro w hw _ ⟨τ, hτ, rfl⟩ hx
    by_contra hn
    push Not at hn
    have h1 : s < τ := lt_of_le_of_ne hτ.1 fun e => hn.1 (by rw [e])
    have h2 : τ < t := lt_of_le_of_ne hτ.2 fun e => hn.2 (by rw [e])
    exact hmiss w hw τ h1 h2 hx
  · intro x hx hxL
    rw [← hγ.img] at hx
    obtain ⟨τ, hτ, rfl⟩ := hx
    by_cases h1 : τ < s
    · exact ⟨_, h0, hspre τ h1⟩
    by_cases h2 : t < τ
    · rcases hcase with ⟨h3, -, -, h4⟩ | ⟨-, h3⟩
      · exact ⟨_, h3, h4 τ h2⟩
      · exact absurd hτ.2 (not_lt.mpr (h3 ▸ h2.le))
    · exact absurd ⟨τ, ⟨not_lt.mp h1, not_lt.mp h2⟩, rfl⟩ hxL
  · rintro _ ⟨τ, hτ, rfl⟩
    have hcs : τ < 1 ∨ τ = 1 := lt_or_eq_of_le (unitInterval.le_one τ)
    rcases hcs with h | h
    · exact .inl (hγ.mem_edge (hle τ hτ) h)
    · rw [h]
      exact .inr hγ.mem1

private theorem tree_attachment_lines_disjoint
    {T : Type}
    [TopologicalSpace T]
    (Γ : Drawing T)
    {B₀ : Set T}
    {K : Set T}
    (hKV : K ⊆ Γ.V)
    {ρ : T → ℕ}
    (𝓔 : Set (Set T))
    (γ : Set T → ↑I → T)
    (L : Set T → Set T)
    (hmeetV : ∀ e ∈ 𝓔, ∀ f ∈ 𝓔, e ≠ f → ∀ x ∈ L e, x ∈ L f → x ∈ Γ.V)
    (hvert : ∀ e ∈ 𝓔, ∀ x ∈ closure e, x ∈ Γ.V → x = γ e 0 ∨ x = γ e 1)
    (hnoV : ∀ e ∈ 𝓔, γ e 1 ∈ K → ∀ x ∈ L e, x ∉ Γ.V) :
    let N : Type := ↥(K \ discBd B₀)
    ∀ (eT : N → Set T),
    (∀ (u : N), eT u ∈ 𝓔) →
    ∀ (wT : N → T),
    (∀ (u : N), wT u ∈ K) →
    (∀ (u : N), wT u ≠ ↑u) →
    (∀ (u : N), ↑u ∈ closure (eT u)) →
    (∀ (u : N), wT u ∈ closure (eT u)) →
    (∀ (u : N), wT u ∉ discBd B₀ → ρ (wT u) < ρ ↑u) →
    (∀ (u : N), γ (eT u) 1 ∈ K) →
    ∀ (u : N),
    ∀ (v : N),
    (u ≠ v) →
    Disjoint (L (eT u)) (L (eT v)) := by
  intro N eT heT wT hwT hwne huc hwc hrk hT1 u v huv
  have hne : eT u ≠ eT v := fun he => by
    have hvu : u.1 ≠ v.1 := fun e => huv (Subtype.ext e)
    have h1 := hvert _ (heT u) _ (huc u) (hKV u.2.1)
    have h2 := hvert _ (heT u) _ (hwc u) (hKV (hwT u))
    have h3 := hvert _ (heT u) _ (he ▸ huc v) (hKV v.2.1)
    have h4 := hvert _ (heT u) _ (he ▸ hwc v) (hKV (hwT v))
    have hw1 : wT u = v.1 := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
      · exact absurd (h2.trans h1.symm) (hwne u)
      · exact absurd (h2.trans h1.symm) (hwne u)
      · exact absurd (h1.trans h3.symm) hvu
      · exact h2.trans h3.symm
      · exact h2.trans h3.symm
      · exact absurd (h1.trans h3.symm) hvu
      · exact absurd (h2.trans h1.symm) (hwne u)
      · exact absurd (h2.trans h1.symm) (hwne u)
    have hw2 : wT v = u.1 := by
      rcases h1 with h1 | h1 <;> rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4
      · exact absurd (h1.trans h3.symm) hvu
      · exact absurd (h1.trans h3.symm) hvu
      · exact h4.trans h1.symm
      · exact absurd (h4.trans h3.symm) (hwne v)
      · exact absurd (h4.trans h3.symm) (hwne v)
      · exact h4.trans h1.symm
      · exact absurd (h1.trans h3.symm) hvu
      · exact absurd (h1.trans h3.symm) hvu
    have h5 := hrk u (hw1 ▸ v.2.2)
    have h6 := hrk v (hw2 ▸ u.2.2)
    rw [hw1] at h5
    rw [hw2] at h6
    omega
  refine disjoint_left.mpr fun x hx hy => ?_
  exact hnoV _ (heT u) (hT1 u) x hx (hmeetV _ (heT u) _ (heT v) hne x hx hy)

private theorem disc_from_rooted_attachments
    {T : Type}
    [TopologicalSpace T]
    [T2Space T]
    (hS : IsClosedSurface T)
    (hsph : IsSphere T)
    (Γ : Drawing T)
    {B₀ : Set T}
    {E₀ : Set T}
    {X : Set T}
    {K : Set T}
    (hE₀ : IsClosedDisc E₀)
    (hd : Disjoint B₀ E₀)
    (hbd : Γ.U ∩ discBd B₀ ⊆ Γ.V)
    (hEU : Γ.U ∩ E₀ ⊆ Γ.V)
    (hEint : Disjoint Γ.U (discInt E₀))
    (hXV : X ⊆ Γ.V)
    (hXK : Disjoint X K)
    (hcuff : Γ.V ∩ discBd B₀ ⊆ K ∪ X)
    {ρ : T → ℕ}
    (hB₀V : ∀ x ∈ Γ.U, x ∈ B₀ → x ∈ discBd B₀ ∧ x ∈ Γ.V)
    (hclV : ∀ g ∈ Γ.E, ∀ x ∈ closure g, x ∉ Γ.V → x ∈ g)
    (hclU : ∀ g ∈ Γ.E, closure g ⊆ Γ.U) :
    let 𝓔 : Set (Set T) := {e | e ∈ Γ.E ∧ ∃ u ∈ K, u ∈ closure e}
    (𝓔.Finite) →
    ∀ (γ : Set T → ↑I → T),
    (∀ e ∈ 𝓔, γ e 0 ∈ K) →
    ∀ (R : T → Set T),
    (∀ v ∈ K, v ∈ discInt (R v)) →
    (∀ v ∈ K, ∀ w ∈ Γ.V, w ≠ v → w ∉ R v) →
    (∀ v ∈ K, ∀ e ∈ Γ.E, v ∉ closure e → Disjoint (R v) (closure e)) →
    (∀ v ∈ K, Disjoint (R v) E₀) →
    ∀ (L : Set T → Set T),
    ∀ (a : Set T → T),
    ∀ (b : Set T → T),
    (∀ e ∈ 𝓔, IsPiece Γ K X R e (L e) (a e) (b e) (γ e 0) (γ e 1)) →
    (∀ e ∈ 𝓔, L e ⊆ Γ.U) →
    (∀ e ∈ 𝓔, ∀ x ∈ L e, x ∈ Γ.V → x = b e ∧ b e ∈ X) →
    (∀ e ∈ 𝓔, ∀ f ∈ 𝓔, e ≠ f → ∀ x ∈ L e, x ∈ L f → x ∈ Γ.V) →
    (K.Finite) →
    ∀ (K₀ : Set T),
    (∀ {v : T}, v ∈ K₀ → v ∈ K ∩ discBd B₀) →
    ∀ (B₁ : Set T),
    (B₀ ⊆ B₁) →
    (discBd B₁ ⊆ discBd B₀ ∪ (⋃ i ∈ K₀, discBd (R i))) →
    (discBd B₀ \ (⋃ i ∈ K₀, R i) ⊆ discBd B₁) →
    (∀ x ∈ B₁, x ∈ B₀ ∨ ∃ v ∈ K, v ∈ discBd B₀ ∧ x ∈ R v) →
    (∀ v ∈ K, v ∈ discBd B₀ → ∀ x ∈ discBd (R v), x ∉ Γ.V → x ∈ Γ.U → x ∈ discBd B₁) →
    (∀ v ∈ K, v ∈ discBd B₀ → discInt (R v) ⊆ discInt B₁) →
    (∀ e ∈ 𝓔, ∀ x ∈ L e, x ∈ B₁ → x = a e ∨ x = b e) →
    (∀ e ∈ 𝓔, γ e 1 ∈ K → ∀ x ∈ L e, x ∉ Γ.V) →
    let N : Type := ↥(K \ discBd B₀)
    ∀ (eT : N → Set T),
    (∀ (u : N), eT u ∈ 𝓔) →
    (∀ (u : N), γ (eT u) 1 ∈ K) →
    ∀ (p : N → T),
    ∀ (q : N → T),
    (∀ (u : N), IsLineWithEnds (L (eT u)) (p u) (q u)) →
    (∀ (u : N), p u ∈ discBd (R ↑u)) →
    ∀ (par : N → Option N),
    let c₀ : Option N → Set T := fun n => n.elim B₁ fun u => R ↑u
    (∀ (n : Option N), IsClosedDisc (c₀ n)) →
    (∀ (m n : Option N), m ≠ n → Disjoint (c₀ m) (c₀ n)) →
    (∀ (u v : N), par u = some v → ρ ↑v < ρ ↑u) →
    (∀ (u : N), q u ∈ discBd (c₀ (par u))) →
    (∀ (u : N) (n : Option N), L (eT u) ∩ c₀ n ⊆ {p u, q u}) →
    (∀ (u v : N), u ≠ v → Disjoint (L (eT u)) (L (eT v))) →
    ∃ B : Set T, IsClosedDisc B ∧ B₀ ⊆ B ∧ Disjoint (discInt E₀) B ∧ discBd B ∩ Γ.U ⊆ X := by
  intro 𝓔 h𝓔 γ hγK R hRmem hoffV hcloff hRE L a b hL hLU hLVmem hmeetV hKfin K₀ hmemK₀ B₁ h1a h1d
    h1g hB₁cases hbB₁ hintR hLB₁ hnoV N eT heT hT1 p q hpql hpb par c₀ hd' hdj' hρ' hq' hLc' hLL'
  classical
  have hfin : (𝓔 \ range eT).Finite := h𝓔.subset sdiff_subset
  set s := hfin.toFinset with hs
  have hmem : ∀ {e}, e ∈ s → e ∈ 𝓔 ∧ ∀ u, eT u ≠ e := fun {e} h => by
    obtain ⟨h1, h2⟩ := hfin.mem_toFinset.mp h
    exact ⟨h1, fun u hu => h2 ⟨u, hu⟩⟩
  have hXfin : X.Finite := Γ.finite_V.subset hXV
  set Y : Set T := X ∪ (Γ.V \ K) ∪ (⋃ f ∈ Γ.E \ 𝓔, closure f) ∪ E₀ with hY
  have hYc : IsClosed Y := ((hXfin.isClosed.union (Γ.finite_V.subset sdiff_subset).isClosed).union
    ((Γ.finite_edges.subset sdiff_subset).isClosed_biUnion fun e _ => isClosed_closure)).union
      hE₀.isClosed
  have hclf : ∀ f ∈ Γ.E \ 𝓔, ∀ v ∈ K, v ∉ closure f := fun f hf v hv h => hf.2 ⟨hf.1, v, hv, h⟩
  have hYR : ∀ v ∈ K, ∀ x ∈ R v, x ∉ Y := fun v hv x hx => by
    rintro (((h | h) | h) | h)
    · exact hoffV v hv x (hXV h) (fun e => disjoint_left.mp hXK h (e ▸ hv)) hx
    · exact hoffV v hv x h.1 (fun e => h.2 (e ▸ hv)) hx
    · obtain ⟨f, hf, h1⟩ := mem_iUnion₂.mp h
      exact disjoint_left.mp (hcloff v hv f hf.1 (hclf f hf v hv)) hx h1
    · exact disjoint_left.mp (hRE v hv) hx h
  have hYL : ∀ e ∈ 𝓔, ∀ x ∈ L e, x ∈ Y → x ∈ Γ.V := fun e he x hx => by
    rintro (((h | h) | h) | h)
    · exact hXV h
    · exact h.1
    · obtain ⟨f, hf, h1⟩ := mem_iUnion₂.mp h
      by_contra hn
      have h2 := hclV f hf.1 x h1 hn
      rcases (hL e he).onEdge x hx with h3 | h3
      · have hef : e = f := by
          by_contra hne
          exact disjoint_left.mp (GM06.disjoint_edges_of_ne Γ he.1 hf.1 hne) h3 h2
        exact hf.2 (hef ▸ he)
      · exact hn h3
    · exact hEU ⟨hLU e he hx, h⟩
  have hint' : IsPreconnected (discInt E₀) := hE₀.isPreconnected_discInt
  have hYne : (discInt E₀).Nonempty := hE₀.nonempty_discInt
  have hXY : Disjoint X (discInt E₀) := disjoint_left.mpr fun x hx h => disjoint_left.mp hEint
    (Γ.V_subset_U (hXV hx)) h
  have hY₀Y : discInt E₀ ⊆ Y := fun x hx => .inr hx.1
  have hLY' : ∀ u, Disjoint (L (eT u)) Y := fun u => disjoint_left.mpr fun x hx h =>
    hnoV _ (heT u) (hT1 u) x hx (hYL _ (heT u) x hx h)
  have hLℓ : ∀ u, ∀ e ∈ s, Disjoint (L (eT u)) (L e) := fun u e he => disjoint_left.mpr fun x hx h
    =>
    hnoV _ (heT u) (hT1 u) x hx (hmeetV _ (heT u) _ (hmem he).1 ((hmem he).2 u) x hx h)
  have hcY₀ : ∀ n, Disjoint (discInt E₀) (c₀ n) := fun n => by
    cases n with
    | none =>
      refine disjoint_left.mpr fun x hx h => ?_
      rcases hB₁cases x h with h1 | ⟨v, hv, -, h1⟩
      · exact disjoint_left.mp hd h1 hx.1
      · exact disjoint_left.mp (hRE v hv) h1 hx.1
    | some u => exact ((hRE u.1 u.2.1).mono_right fun x hx => hx.1).symm
  have hbY : ∀ n, discBd (c₀ n) ∩ Y ⊆ X := fun n => by
    cases n with
    | none =>
      rintro x ⟨hx, hy⟩
      rcases h1d hx with h | h
      · have hxB := h
        rcases hy with ((h1 | h1) | h1) | h1
        · exact h1
        · rcases h1 with ⟨h2, h3⟩
          exact (hcuff ⟨h2, hxB⟩).resolve_left h3
        · obtain ⟨f, hf, h2⟩ := mem_iUnion₂.mp h1
          have h3 := hbd ⟨hclU f hf.1 h2, hxB⟩
          rcases hcuff ⟨h3, hxB⟩ with h4 | h4
          · exact absurd h2 (hclf f hf x h4)
          · exact h4
        · exact absurd h1 (disjoint_left.mp hd (GM11.discBd_subset _ hxB))
      · obtain ⟨v, hv, h2⟩ := mem_iUnion₂.mp h
        exact absurd hy (hYR v (hmemK₀ hv).1 x (GM11.discBd_subset _ h2))
    | some u =>
      rintro x ⟨hx, hy⟩
      exact absurd hy (hYR u.1 u.2.1 x (GM11.discBd_subset _ hx))
  have hbon : ∀ v ∈ K, ∀ x ∈ discBd (R v), x ∉ Γ.V → x ∈ Γ.U → ∃ n, x ∈ discBd (c₀ n)
    := fun v hv x hx h2 h3 => by
    by_cases h1 : v ∈ discBd B₀
    · exact ⟨none, hbB₁ v hv h1 x hx h2 h3⟩
    · exact ⟨some ⟨v, hv, h1⟩, hx⟩
  have : Finite N := (hKfin.subset sdiff_subset).to_subtype
  obtain ⟨B, hB, hc, hLint, hY₀B, hbdY, hbdL⟩ := exists_disc_of_tree hS hsph (c₀ := c₀) (L := fun u
    => L (eT u)) (p := p) (q := q) (par := par) (ρ := fun u => ρ u.1) hd' hdj' hρ' hpql hpb hq'
      hLc' hLL'
    s L a b (X := X) (Y := Y) (Y₀ := discInt E₀) hint' hYne hXY hYc hY₀Y hLY' hLℓ hcY₀ hbY
      (fun e he => (hL e (hmem he).1).line) (fun e he => (hL e (hmem he).1).ne)
    (fun e he h => (hL e (hmem he).1).a_notV (hXV h)) (fun e he => hbon _ (hγK e (hmem he).1) _
      (hL e (hmem he).1).a_bd (hL e (hmem he).1).a_notV (hLU e (hmem he).1 (hL e
        (hmem he).1).line.left_mem))
    (fun e he => by
      have h𝓔e := (hmem he).1
      rcases (hL e h𝓔e).b_mem with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · exact .inl (hbon _ h1 _ h2 h3 (hLU e h𝓔e (hL e h𝓔e).line.right_mem))
      · have hbU := hLU e h𝓔e (hL e h𝓔e).line.right_mem
        have hbR : ∀ v ∈ K, b e ∉ R v := fun v hv h => hYR v hv _ h (.inl (.inl (.inl h2)))
        by_cases h3 : b e ∈ discBd B₀
        · refine .inl ⟨none, h1g ⟨h3, fun h => ?_⟩⟩
          obtain ⟨v, hv, h4⟩ := mem_iUnion₂.mp h
          exact hbR v (hmemK₀ hv).1 h4
        · refine .inr ⟨h2, fun n h => ?_⟩
          cases n with
          | none =>
            rcases hB₁cases _ h with h4 | ⟨v, hv, -, h4⟩
            · exact h3 (hB₀V _ hbU h4).1
            · exact hbR v hv h4
          | some u => exact hbR u.1 u.2.1 h)
    (fun e he n x hx => by
      have h𝓔e := (hmem he).1
      cases n with
      | none => exact hLB₁ e h𝓔e x hx.1 hx.2
      | some v => exact (hL e h𝓔e).disc v.1 v.2.1 x hx.1 hx.2)
    (fun e he x hx => (hLVmem e (hmem he).1 x hx.1 (hYL e (hmem he).1 x hx.1 hx.2)).1 ▸ (hLVmem e
      (hmem he).1 x hx.1 (hYL e (hmem he).1 x hx.1 hx.2)).2)
    (fun e he => disjoint_left.mpr fun x hx h => hx.2 (.inr (hLVmem e (hmem he).1 x hx.1
      (hXV h)).1))
    (fun e he f hf hef x hx => by
      have h2 := hmeetV e (hmem he).1 f (hmem hf).1 hef x hx.1 hx.2
      have h3 := hLVmem e (hmem he).1 x hx.1 h2
      exact h3.1 ▸ h3.2)
  have hRint : ∀ v ∈ K, discInt (R v) ⊆ discInt B := fun v hv x hx => by
    by_cases h1 : v ∈ discBd B₀
    · exact (hc none).2 (hintR v hv h1 hx)
    · exact (hc (some ⟨v, hv, h1⟩)).2 hx
  refine ⟨B, hB, h1a.trans (hc none).1, hY₀B, ?_⟩
  rintro x ⟨hx, hU⟩
  have hnotint : x ∉ discInt B := fun h => h.2 hx
  by_cases hV : x ∈ Γ.V
  · by_cases hK : x ∈ K
    · exact absurd (hRint x hK (hRmem x hK)) hnotint
    · exact hbdY ⟨hx, .inl (.inl (.inr ⟨hV, hK⟩))⟩
  obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hU hV
  by_cases h𝓔e : e ∈ 𝓔
  · by_cases hxL : x ∈ L e
    · by_cases hmemT : e ∈ range eT
      · obtain ⟨u, rfl⟩ := hmemT
        exact absurd (hLint u hxL) hnotint
      · exact hbdL e (hfin.mem_toFinset.mpr ⟨h𝓔e, hmemT⟩) ⟨hx, hxL⟩
    · obtain ⟨w, hw, h1⟩ := (hL e h𝓔e).rest x hxe hxL
      exact absurd (hRint w hw h1) hnotint
  · exact hbdY ⟨hx, .inl (.inr (mem_iUnion₂.mpr ⟨e, ⟨he, h𝓔e⟩, subset_closure hxe⟩))⟩

private theorem tree_edge_endpoints
    {T : Type}
    [TopologicalSpace T]
    (Γ : Drawing T)
    {B₀ : Set T}
    {K : Set T}
    (hKV : K ⊆ Γ.V)
    (𝓔 : Set (Set T))
    (γ : Set T → ↑I → T)
    (hvert : ∀ e ∈ 𝓔, ∀ x ∈ closure e, x ∈ Γ.V → x = γ e 0 ∨ x = γ e 1) :
    let N : Type := ↥(K \ discBd B₀)
    ∀ (eT : N → Set T),
    (∀ (u : N), eT u ∈ 𝓔) →
    ∀ (wT : N → T),
    (∀ (u : N), wT u ∈ K) →
    (∀ (u : N), wT u ≠ ↑u) →
    (∀ (u : N), ↑u ∈ closure (eT u)) →
    (∀ (u : N), wT u ∈ closure (eT u)) →
    ∀ (u : N),
    γ (eT u) 0 = ↑u ∧ γ (eT u) 1 = wT u ∨ γ (eT u) 0 = wT u ∧ γ (eT u) 1 = ↑u := by
  intro N eT heT wT hwT hwne huc hwc u
  have hu := hvert _ (heT u) _ (huc u) (hKV u.2.1)
  have hw := hvert _ (heT u) _ (hwc u) (hKV (hwT u))
  rcases hu with h1 | h1 <;> rcases hw with h2 | h2
  · exact absurd (h2.trans h1.symm) (hwne u)
  · exact .inl ⟨h1.symm, h2.symm⟩
  · exact .inr ⟨h2.symm, h1.symm⟩
  · exact absurd (h2.trans h1.symm) (hwne u)

private theorem orient_tree_attachment
    {T : Type}
    [TopologicalSpace T]
    (Γ : Drawing T)
    {B₀ : Set T}
    {X : Set T}
    {K : Set T}
    (𝓔 : Set (Set T))
    (γ : Set T → ↑I → T)
    (R : T → Set T)
    (L : Set T → Set T)
    (a : Set T → T)
    (b : Set T → T)
    (hL : ∀ e ∈ 𝓔, IsPiece Γ K X R e (L e) (a e) (b e) (γ e 0) (γ e 1))
    (hbK : ∀ e ∈ 𝓔, γ e 1 ∈ K → b e ∈ discBd (R (γ e 1)) ∧ b e ∉ Γ.V) :
    let N : Type := ↥(K \ discBd B₀)
    ∀ (eT : N → Set T),
    (∀ (u : N), eT u ∈ 𝓔) →
    ∀ (wT : N → T),
    (∀ (u : N), γ (eT u) 0 = ↑u ∧ γ (eT u) 1 = wT u ∨ γ (eT u) 0 = wT u ∧ γ (eT u) 1 =
      ↑u) →
    (∀ (u : N), γ (eT u) 1 ∈ K) →
    ∀ (u : N),
    ∃ p q : T, IsLineWithEnds (L (eT u)) p q ∧ p ∈ discBd (R ↑u) ∧ q ∈ discBd (R (wT u)) ∧
      ({p, q} : Set T) = {a (eT u), b (eT u)} := by
  intro N eT heT wT hTends hT1 u
  have hP := hL _ (heT u)
  have hb' := (hbK _ (heT u) (hT1 u)).1
  rcases hTends u with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨a _, b _, hP.line, h1 ▸ hP.a_bd, h2 ▸ hb', rfl⟩
  · exact ⟨b _, a _, hP.line.symm, h2 ▸ hb', h1 ▸ hP.a_bd, pair_comm _ _⟩

private theorem rooted_discs_disjoint
    {T : Type}
    [TopologicalSpace T]
    {B₀ : Set T}
    {K : Set T}
    (R : T → Set T)
    (hRd : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → Disjoint (R u) (R v))
    (B₁ : Set T) :
    let N : Type := ↥(K \ discBd B₀)
    let c₀ : Option N → Set T := fun n => n.elim B₁ fun u => R ↑u
    (∀ (u : N), Disjoint (R ↑u) B₁) →
    ∀ (m : Option N),
    ∀ (n : Option N),
    (m ≠ n) →
    Disjoint (c₀ m) (c₀ n) := by
  intro N c₀ hRB₁ m n hmn
  cases m with
  | none =>
    cases n with
    | none => exact absurd rfl hmn
    | some u => exact (hRB₁ u).symm
  | some u =>
    cases n with
    | none => exact hRB₁ u
    | some v => exact hRd u.1 u.2.1 v.1 v.2.1 fun e => hmn (congrArg some (Subtype.ext e))

private theorem parent_rank_decreases
    {T : Type}
    [TopologicalSpace T]
    {B₀ : Set T}
    {K : Set T}
    {ρ : T → ℕ} :
    let N : Type := ↥(K \ discBd B₀)
    ∀ (wT : N → T),
    ∀ (hwT : ∀ (u : N), wT u ∈ K),
    (∀ (u : N), wT u ∉ discBd B₀ → ρ (wT u) < ρ ↑u) →
    let par : N → Option N := fun u => @dite (Option N) (wT u ∉ discBd B₀)
      (Classical.propDecidable _) (fun h => some ⟨wT u, hwT u, h⟩) (fun _ => none)
    ∀ (u : N),
    ∀ (v : N),
    (par u = some v) →
    ρ ↑v < ρ ↑u := by
  intro N wT hwT hrk par u v h
  by_cases h1 : wT u ∉ discBd B₀
  · have h2 : par u = some ⟨wT u, hwT u, h1⟩ := dite_eq_left h1
    rw [h2] at h
    obtain rfl := Option.some.inj h
    exact hrk u h1
  · have h2 : par u = none := dite_eq_right h1
    rw [h2] at h
    exact absurd h (by simp)

private theorem attachment_end_on_parent_disc
    {T : Type}
    [TopologicalSpace T]
    (Γ : Drawing T)
    {B₀ : Set T}
    {K : Set T}
    (𝓔 : Set (Set T))
    (γ : Set T → ↑I → T)
    (R : T → Set T)
    (L : Set T → Set T)
    (hLU : ∀ e ∈ 𝓔, L e ⊆ Γ.U)
    (B₁ : Set T)
    (hbB₁ : ∀ v ∈ K, v ∈ discBd B₀ → ∀ x ∈ discBd (R v), x ∉ Γ.V → x ∈ Γ.U → x ∈ discBd B₁)
    (hnoV : ∀ e ∈ 𝓔, γ e 1 ∈ K → ∀ x ∈ L e, x ∉ Γ.V) :
    let N : Type := ↥(K \ discBd B₀)
    ∀ (eT : N → Set T),
    (∀ (u : N), eT u ∈ 𝓔) →
    ∀ (wT : N → T),
    ∀ (hwT : ∀ (u : N), wT u ∈ K),
    (∀ (u : N), γ (eT u) 1 ∈ K) →
    ∀ (p : N → T),
    ∀ (q : N → T),
    (∀ (u : N), IsLineWithEnds (L (eT u)) (p u) (q u)) →
    (∀ (u : N), q u ∈ discBd (R (wT u))) →
    let par : N → Option N := fun u => @dite (Option N) (wT u ∉ discBd B₀)
      (Classical.propDecidable _) (fun h => some ⟨wT u, hwT u, h⟩) (fun _ => none)
    let c₀ : Option N → Set T := fun n => n.elim B₁ fun u => R ↑u
    ∀ (u : N),
    q u ∈ discBd (c₀ (par u)) := by
  intro N eT heT wT hwT hT1 p q hpql hqb par c₀ u
  have hqU : q u ∈ L (eT u) := (hpql u).right_mem
  by_cases h1 : wT u ∉ discBd B₀
  · have h2 : par u = some ⟨wT u, hwT u, h1⟩ := dite_eq_left h1
    rw [h2]
    exact hqb u
  · have h2 : par u = none := dite_eq_right h1
    rw [h2]
    exact hbB₁ _ (hwT u) (not_not.mp h1) _ (hqb u) (hnoV _ (heT u) (hT1 u) _ hqU) (hLU _
      (heT u) hqU)

/-- **A disc around one side of a separation.** See the module docstring. The rank `ρ` says that
each vertex of `K` is joined to `B₀` inside `K`. -/
theorem exists_disc_of_side (hS : IsClosedSurface T) (hsph : IsSphere T)
  (Γ : Drawing T) {B₀ E₀ X K : Set T} (hB₀ : IsClosedDisc B₀) (hE₀ : IsClosedDisc E₀)
    (hd : Disjoint B₀ E₀)
    (hbd : Γ.U ∩ discBd B₀ ⊆ Γ.V) (hint : Disjoint Γ.U (discInt B₀)) (hEU : Γ.U ∩ E₀ ⊆ Γ.V)
      (hEint : Disjoint Γ.U (discInt E₀)) (hKV : K ⊆ Γ.V) (hXV : X ⊆ Γ.V) (hXK : Disjoint X K)
    (hcuff : Γ.V ∩ discBd B₀ ⊆ K ∪ X) (hKE : Disjoint K E₀) (hedge : ∀ e ∈ Γ.E, ∀ u ∈ K, u ∈
      closure e → ∀ w ∈ Γ.V, w ∈ closure e → w ∈ K ∪ X)
    {ρ : T → ℕ} (hreach : ∀ u ∈ K, u ∉ discBd B₀ → ∃ e ∈ Γ.E, ∃ w ∈ K, w ≠ u ∧ u ∈ closure e
      ∧ w ∈ closure e ∧ (w ∉ discBd B₀ → ρ w < ρ u)) :
    ∃ B, IsClosedDisc B ∧ B₀ ⊆ B ∧ Disjoint (discInt E₀) B ∧ discBd B ∩ Γ.U ⊆ X := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  by_cases hA : (Γ.V ∩ discBd B₀).Nonempty
  swap
  · refine ⟨B₀, hB₀, Subset.rfl, hd.symm.mono_left fun x hx => hx.1, fun x hx => ?_⟩
    exact absurd ⟨x, hbd ⟨hx.2, hx.1⟩, hx.1⟩ hA
  obtain ⟨D, hDU, hDV⟩ := exists_drawing_on_oArc hB₀.isOArc_discBd (Γ.finite_V.subset
    inter_subset_left) hA inter_subset_right
  have hmeet : Γ.U ∩ D.U ⊆ Γ.V ∩ D.V := fun x hx => by
    have hx2 : x ∈ discBd B₀ := hDU ▸ hx.2
    have hxV := hbd ⟨hx.1, hx2⟩
    exact ⟨hxV, hDV ▸ ⟨hxV, hx2⟩⟩
  have hE₁ : Γ.E ⊆ (Γ.glue D hmeet).E := by
    rw [Drawing.glue_E]
    exact subset_union_left
  have hD₁ : D.E ⊆ (Γ.glue D hmeet).E := by
    rw [Drawing.glue_E]
    exact subset_union_right
  have hV₁ : Γ.V ⊆ (Γ.glue D hmeet).V := subset_union_left
  have hDV₁ : D.V ⊆ (Γ.glue D hmeet).V := subset_union_right
  have hB₀V : ∀ x ∈ Γ.U, x ∈ B₀ → x ∈ discBd B₀ ∧ x ∈ Γ.V := fun x hx h => by
    have h1 : x ∈ discBd B₀ := by
      by_contra hn
      exact disjoint_left.mp hint hx ⟨h, hn⟩
    exact ⟨h1, hbd ⟨hx, h1⟩⟩
  have hclV : ∀ g ∈ Γ.E, ∀ x ∈ closure g, x ∉ Γ.V → x ∈ g := fun g hg x hx hn => by
    rw [← Γ.closure_diff_V hg]
    exact ⟨hx, hn⟩
  have hclU : ∀ g ∈ Γ.E, closure g ⊆ Γ.U := fun _ hg => Γ.closure_subset_U hg
  let 𝓔 : Set (Set T) := {e ∈ Γ.E | ∃ u ∈ K, u ∈ closure e}
  have h𝓔 : 𝓔.Finite := Γ.finite_edges.subset (sep_subset _ _)
  have hor : ∀ e ∈ 𝓔, ∃ c, EdgeParam Γ e c ∧ c 0 ∈ K := fun e he => by
    obtain ⟨u, hu, huc⟩ := he.2
    obtain ⟨c, h1, h2⟩ := EdgeParam.exists_orient he.1 huc (hKV hu)
    exact ⟨c, h1, h2 ▸ hu⟩
  have : Nonempty (I → T) := ⟨fun _ => hA.some⟩
  choose! γ hγ hγK using hor
  have hzex : ∀ v : T, ∃ z ∈ discBd B₀, z ≠ v := fun v => hB₀.isOArc_discBd.exists_ne v
  choose z hz hzv using hzex
  have hq1 : quarter₂ < (1 : I) := unitInterval.lt_one_iff_ne_one.mpr fun e => by
    have h1 := congrArg Subtype.val e
    norm_num [quarter₂] at h1
  have hq0 : (0 : I) < quarter₂ := unitInterval.pos_iff_ne_zero.mpr fun e => by
    have h1 := congrArg Subtype.val e
    norm_num [quarter₂] at h1
  let P : T → Set T := fun v => (Γ.V \ {v}) ∪ (⋃ e ∈ {e ∈ Γ.E | v ∉ closure e}, closure e) ∪
    ((fun e => γ e quarter₂) '' 𝓔) ∪ E₀ ∪ (if v ∈ discBd B₀ then {z v} else B₀)
  have hPc : ∀ v ∈ K, IsClosed (P v) := fun v _ => by
    refine (((((Γ.finite_V.subset sdiff_subset).isClosed).union ((Γ.finite_edges.subset
      (sep_subset _ _)).isClosed_biUnion fun e _ => isClosed_closure)).union
        (h𝓔.image _).isClosed).union hE₀.isClosed).union ?_
    split_ifs
    · exact isClosed_singleton
    · exact hB₀.isClosed
  have hvP : ∀ v ∈ K, v ∉ P v := fun v hv => by
    rintro ((((h | h) | ⟨e, he, h⟩) | h) | h)
    · exact h.2 rfl
    · obtain ⟨e, he, h1⟩ := mem_iUnion₂.mp h
      exact he.2 h1
    · have h' : γ e quarter₂ = v := h
      exact (hγ e he).not_V he.1 hq0 hq1 (h'.symm ▸ hKV hv)
    · exact disjoint_left.mp hKE hv h
    · split_ifs at h with h2
      · exact hzv v h.symm
      · exact h2 (hB₀V v (Γ.V_subset_U (hKV hv)) h).1
  obtain ⟨R, hR, hRd⟩ := exists_star_family hS (Γ.glue D hmeet) (hKV.trans hV₁) hPc hvP
  have hRP : ∀ v ∈ K, ∀ x ∈ R v, x ∉ P v := fun v hv x hx h => disjoint_left.mp (hR v hv).2 hx h
  have hoffV : ∀ v ∈ K, ∀ w ∈ Γ.V, w ≠ v → w ∉ R v := fun v hv w hw hne h => hRP v hv w h (.inl
    (.inl (.inl (.inl ⟨hw, hne⟩))))
  have hcloff : ∀ v ∈ K, ∀ e ∈ Γ.E, v ∉ closure e → Disjoint (R v) (closure e) := fun v hv e he hn
    => disjoint_left.mpr fun x hx h =>
    hRP v hv x hx (.inl (.inl (.inl (.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hn⟩, h⟩)))))
  have hRE : ∀ v ∈ K, Disjoint (R v) E₀ := fun v hv => disjoint_left.mpr fun x hx h
    => hRP v hv x hx (.inl (.inr h))
  have hRB₀ : ∀ v ∈ K, v ∉ discBd B₀ → Disjoint (R v) B₀ := fun v hv hn
    => disjoint_left.mpr fun x hx h => hRP v hv x hx (.inr (by rwa [ite_eq_right hn]))
  have hpiece : ∀ e ∈ 𝓔, ∃ L a b, IsPiece Γ K X R e L a b (γ e 0) (γ e 1) := fun e he =>
    exists_piece hman hE₁ hV₁ hKV (fun v hv => (hR v hv).1) (hγ e he) he.1 (hγK e he) (fun v hv h
      => hRP v hv _ h (.inl (.inl (.inr ⟨e, he, rfl⟩))))
      hoffV (fun v hv ⟨y, h1, h2⟩ => by
        by_contra hn
        exact disjoint_left.mp (hcloff v hv e he.1 hn) h1 h2)
      (hedge e he.1 _ (hγK e he) ((hγ e he).closure_eq ▸ mem_range_self _) _ (hγ e he).mem1
        ((hγ e he).closure_eq ▸ mem_range_self _))
  have : Nonempty T := ⟨hA.some⟩
  choose! L a b hL using hpiece
  have hLU : ∀ e ∈ 𝓔, L e ⊆ Γ.U := fun e he x hx => hclU e he.1 ((hL e he).sub hx)
  have hLVmem : ∀ e ∈ 𝓔, ∀ x ∈ L e, x ∈ Γ.V → x = b e ∧ b e ∈ X := fun e he x hx hv =>
    (hL e he).vertex x hx hv
  have hmeetV : ∀ e ∈ 𝓔, ∀ f ∈ 𝓔, e ≠ f → ∀ x ∈ L e, x ∈ L f → x ∈ Γ.V := fun e he f hf hef x hx hy
    => by
    rcases (hL e he).onEdge x hx with h1 | h1
    · rcases (hL f hf).onEdge x hy with h2 | h2
      · exact absurd h2 (disjoint_left.mp (GM06.disjoint_edges_of_ne Γ he.1 hf.1 hef) h1)
      · exact h2
    · exact h1
  -- The discs at the vertices of `K` on the boundary of `B₀`, joined to it.
  have hKfin : K.Finite := Γ.finite_V.subset hKV
  have hchord : ∀ v ∈ K ∩ discBd B₀, ∃ F y₁ y₂, IsLineWithEnds F y₁ y₂ ∧ y₁ ≠ y₂ ∧ F ⊆ R v
    ∧ F ∩ discBd (R v) = {y₁, y₂} ∧ R v ∩ discBd B₀ = F ∧ v ∈ F := fun v hv => by
    have hst := (hR v hv.1).1
    refine exists_star_chord hB₀.isOArc_discBd hv.2 hst.disc (hst.disc.isOpen_discInt hman) hst.mem
      (hz v) (fun h => ?_) (fun y hy => ?_)
    · exact hRP v hv.1 _ h (.inr (by rw [ite_eq_left hv.2]; exact rfl))
    · exact hst.star _ hB₀.isOArc_discBd.isCompact.isClosed (hDU ▸ isGammaNice_of_U hD₁ hDV₁) y hy
  choose! F y₁ y₂ hF₁ hF₂ hF₃ hF₄ hF₅ hF₆ using hchord
  have hK₀ : (K ∩ discBd B₀).Finite := hKfin.subset inter_subset_left
  have hmemK₀ : ∀ {v}, v ∈ hK₀.toFinset → v ∈ K ∩ discBd B₀ := fun {v} h => hK₀.mem_toFinset.mp h
  obtain ⟨B₁, hB₁, h1a, h1b, h1c, h1d, h1e, h1f, h1g⟩ := exists_blob (R := R) (F := F) (y₁ := y₁)
    (y₂ := y₂) (v := id) hS hB₀ hK₀.toFinset (fun v hv => (hR v (hmemK₀ hv).1).1.disc)
    (fun v hv => hF₁ v (hmemK₀ hv)) (fun v hv => hF₂ v (hmemK₀ hv)) (fun v hv => hF₃ v (hmemK₀ hv))
      (fun v hv => hF₄ v (hmemK₀ hv)) (fun v hv => hF₅ v (hmemK₀ hv))
    (fun v hv => hF₆ v (hmemK₀ hv)) (fun v hv => (hR v (hmemK₀ hv).1).1.mem) (fun u hu v hv huv
      => hRd u (hmemK₀ hu).1 v (hmemK₀ hv).1 huv)
  have hB₁cases : ∀ x ∈ B₁, x ∈ B₀ ∨ ∃ v ∈ K, v ∈ discBd B₀ ∧ x ∈ R v := fun x hx => by
    rcases h1c hx with h | h
    · exact .inl h
    · obtain ⟨v, hv, h2⟩ := mem_iUnion₂.mp h
      exact .inr ⟨v, (hmemK₀ hv).1, (hmemK₀ hv).2, h2⟩
  have hbB₁ : ∀ v ∈ K, v ∈ discBd B₀ → ∀ x ∈ discBd (R v), x ∉ Γ.V → x ∈ Γ.U → x ∈ discBd B₁
    := fun v hv hvb x hx h2 h3 =>
    h1f v (hK₀.mem_toFinset.mpr ⟨hv, hvb⟩) ⟨hx, fun h => h2 (hB₀V x h3 h).2⟩
  have hintR : ∀ v ∈ K, v ∈ discBd B₀ → discInt (R v) ⊆ discInt B₁ := fun v hv hvb x hx => by
    have hm := hK₀.mem_toFinset.mpr ⟨hv, hvb⟩
    exact ⟨h1b v hm hx.1, fun h => disjoint_left.mp (h1e v hm) h hx⟩
  have hLB₁ : ∀ e ∈ 𝓔, ∀ x ∈ L e, x ∈ B₁ → x = a e ∨ x = b e := fun e he x hx hxB => by
    rcases hB₁cases x hxB with h | ⟨v, hv, -, h⟩
    · exact .inr (hLVmem e he x hx (hB₀V x (hLU e he hx) h).2).1
    · exact (hL e he).disc v hv x hx h
  -- The tree.
  have hvert : ∀ e ∈ 𝓔, ∀ x ∈ closure e, x ∈ Γ.V → x = γ e 0 ∨ x = γ e 1 := fun e he x hx hv => by
    rw [(hγ e he).closure_eq] at hx
    obtain ⟨y, rfl⟩ := hx
    by_contra hn
    push Not at hn
    have h1 : 0 < y := unitInterval.pos_iff_ne_zero.mpr fun e' => hn.1 (by rw [e'])
    have h2 : y < 1 := unitInterval.lt_one_iff_ne_one.mpr fun e' => hn.2 (by rw [e'])
    exact (hγ e he).not_V he.1 h1 h2 hv
  have hnoV : ∀ e ∈ 𝓔, γ e 1 ∈ K → ∀ x ∈ L e, x ∉ Γ.V := fun e he h1 x hx hv => by
    obtain ⟨-, h2⟩ := hLVmem e he x hx hv
    rcases (hL e he).b_mem with ⟨-, -, h3⟩ | ⟨h3, -⟩
    · exact h3 (hXV h2)
    · exact h3 h1
  have hbK : ∀ e ∈ 𝓔, γ e 1 ∈ K → b e ∈ discBd (R (γ e 1)) ∧ b e ∉ Γ.V := fun e he h1 => by
    rcases (hL e he).b_mem with ⟨-, h3, h4⟩ | ⟨h3, -⟩
    · exact ⟨h3, h4⟩
    · exact absurd h1 h3
  let N : Type := ↥(K \ discBd B₀)
  have htree : ∀ u : N, ∃ e ∈ 𝓔, ∃ w ∈ K, w ≠ u.1 ∧ u.1 ∈ closure e ∧ w ∈ closure e ∧
    (w ∉ discBd B₀ → ρ w < ρ u.1) := fun u => by
    obtain ⟨e, he, w, hw, h1, h2, h3, h4⟩ := hreach u.1 u.2.1 u.2.2
    exact ⟨e, ⟨he, u.1, u.2.1, h2⟩, w, hw, h1, h2, h3, h4⟩
  choose eT heT wT hwT hwne huc hwc hrk using htree
  have hTends : ∀ u : N, (γ (eT u) 0 = u.1 ∧ γ (eT u) 1 = wT u) ∨ (γ (eT u) 0 = wT u ∧ γ (eT u) 1
    = u.1) := fun u => by
    exact tree_edge_endpoints (T := T) Γ (B₀ := B₀) (K := K) hKV 𝓔 γ hvert eT heT wT hwT hwne
      huc hwc u
  have hT1 : ∀ u : N, γ (eT u) 1 ∈ K := fun u => by
    rcases hTends u with ⟨-, h⟩ | ⟨-, h⟩
    · exact h ▸ hwT u
    · exact h ▸ u.2.1
  have hpq : ∀ u : N, ∃ p q, IsLineWithEnds (L (eT u)) p q ∧ p ∈ discBd (R u.1) ∧ q ∈ discBd (R
    (wT u)) ∧ ({p, q} : Set T) = {a (eT u), b (eT u)} := fun u => by
    exact orient_tree_attachment (T := T) Γ (B₀ := B₀) (X := X) (K := K) 𝓔 γ R L a b hL hbK eT
      heT wT hTends hT1 u
  choose p q hpql hpb hqb hpq_ends using hpq
  let par : N → Option N := fun u =>
    @dite (Option N) (wT u ∉ discBd B₀) (Classical.propDecidable _)
      (fun h => some ⟨wT u, hwT u, h⟩) (fun _ => none)
  let c₀ : Option N → Set T := fun n => n.elim B₁ fun u => R u.1
  have hRB₁ : ∀ u : N, Disjoint (R u.1) B₁ := fun u => disjoint_left.mpr fun x hx h => by
    rcases hB₁cases x h with h1 | ⟨v, hv, hvb, h1⟩
    · exact disjoint_left.mp (hRB₀ u.1 u.2.1 u.2.2) hx h1
    · exact disjoint_left.mp (hRd u.1 u.2.1 v hv fun e => u.2.2 (e ▸ hvb)) hx h1
  have hd' : ∀ n, IsClosedDisc (c₀ n) := fun n => by
    cases n with
    | none => exact hB₁
    | some u => exact (hR u.1 u.2.1).1.disc
  have hdj' : ∀ m n, m ≠ n → Disjoint (c₀ m) (c₀ n) := fun m n hmn => by
    exact rooted_discs_disjoint (T := T) (B₀ := B₀) (K := K) R hRd B₁ hRB₁ m n hmn
  have hρ' : ∀ u v, par u = some v → ρ v.1 < ρ u.1 := fun u v h => by
    exact parent_rank_decreases (T := T) (B₀ := B₀) (K := K) (ρ := ρ) wT hwT hrk u v h
  have hq' : ∀ u, q u ∈ discBd (c₀ (par u)) := fun u => by
    exact attachment_end_on_parent_disc (T := T) Γ (B₀ := B₀) (K := K) 𝓔 γ R L hLU B₁ hbB₁ hnoV
      eT heT wT hwT hT1 p q hpql hqb u
  have hLc' : ∀ u n, L (eT u) ∩ c₀ n ⊆ {p u, q u} := fun u n x hx => by
    rw [hpq_ends u]
    cases n with
    | none => exact hLB₁ _ (heT u) x hx.1 hx.2
    | some v => exact (hL _ (heT u)).disc v.1 v.2.1 x hx.1 hx.2
  have hLL' : ∀ u v, u ≠ v → Disjoint (L (eT u)) (L (eT v)) := fun u v huv => by
    exact tree_attachment_lines_disjoint (T := T) Γ (B₀ := B₀) (K := K) hKV (ρ := ρ) 𝓔 γ L hmeetV
      hvert hnoV eT heT wT hwT hwne huc hwc hrk hT1 u v huv
  -- The other lines, and the rest of the drawing.
  exact disc_from_rooted_attachments (T := T) hS hsph Γ (B₀ := B₀) (E₀ := E₀) (X := X) (K := K)
    hE₀ hd hbd hEU hEint hXV hXK hcuff (ρ := ρ) hB₀V hclV hclU h𝓔 γ hγK R
    (fun v hv => (hR v hv).1.mem) hoffV
    hcloff hRE L a b hL hLU hLVmem hmeetV hKfin hK₀.toFinset hmemK₀ B₁ h1a h1d h1g hB₁cases hbB₁
      hintR
    hLB₁ hnoV eT heT hT1 p q hpql hpb par hd' hdj' hρ' hq' hLc' hLL'

end GraphMinor.GM07
