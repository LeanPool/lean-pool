/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.SideCoord
public import LeanPool.GraphMinor.GM19.Section15o

/-!
# The ends along a side

Step (1) of the proof of Graph Minors XIX, (15.2) gives edges of `Γ` along each long side, in the
order of the edges of `Γ₀`. Here we turn this into what step (2) needs. Each end `y` of `β(e)` has a
vertex `endVertex y` of `e`, and along a side the vertices come in the order of the ends
(`lineCoord_endVertex_le`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

local notation "𝕀" => unitInterval

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

namespace TangleDatum

/-- The end `y` of `β(e)` corresponds to the vertex `v` of `e`. -/
def IsEndOf (P₀ P : ColouredPainting χ) (b : Set S → Set S) (y v : S) : Prop :=
  ∃ e ∈ P₀.Γ.E, ∃ (i : ℕ) (hi : i < (P₀.Γ.γ e).length) (hi' : i < (P.Γ.γ (b e)).length),
    (P₀.Γ.γ e)[i] = v ∧ (P.Γ.γ (b e))[i] = y

open Classical in
/-- The vertex of `Γ₀` of an end. -/
noncomputable def endVertex (P₀ P : ColouredPainting χ) (b : Set S → Set S) (y : S) : S :=
  if h : ∃ v, IsEndOf P₀ P b y v then h.choose else y

variable {D : TangleDatum cap χ} {P₀ : ColouredPainting χ} {n : ℕ} {b : Set S → Set S}

omit [T2Space S] in
theorem exists_isEndOf (hb : D.IsEdgeMap P₀ n b) {e : Set S} (he : e ∈ P₀.Γ.E) {y : S}
  (hy : y ∈ tilde (b e)) : ∃ v ∈ tilde e, IsEndOf P₀ D.P b y v := by
  have hbe := hb.mem e he
  have hy' : y ∈ {v | v ∈ D.P.Γ.γ (b e)} := by rw [D.P.Γ.γ_set _ hbe]; exact hy
  obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hy'
  have hlen : (P₀.Γ.γ e).length = (D.P.Γ.γ (b e)).length := by
    rw [P₀.Γ.length_γ_eq he, D.P.Γ.length_γ_eq hbe, hb.size e he]
  have hi : i < (P₀.Γ.γ e).length := hlen ▸ hi'
  refine ⟨(P₀.Γ.γ e)[i], ?_, e, he, i, hi, hi', rfl, rfl⟩
  have : (P₀.Γ.γ e)[i] ∈ {v | v ∈ P₀.Γ.γ e} := List.getElem_mem hi
  rwa [P₀.Γ.γ_set _ he] at this

theorem IsMatchSetting.isEndOf_unique (hM : D.IsMatchSetting P₀ n b) (hS : IsSurface S) {y v v' :
  S} (h : IsEndOf P₀ D.P b y v) (h' : IsEndOf P₀ D.P b y v') : v = v' := by
  by_contra hne
  exact Set.disjoint_left.mp (hM.disjoint_endClass hS hne) ⟨y, h, rfl⟩ ⟨y, h', rfl⟩

theorem IsMatchSetting.endVertex_eq (hM : D.IsMatchSetting P₀ n b) (hS : IsSurface S) {y v : S}
  (h : IsEndOf P₀ D.P b y v) : endVertex P₀ D.P b y = v := by
  have hex : ∃ v, IsEndOf P₀ D.P b y v := ⟨v, h⟩
  rw [endVertex, dite_eq_left hex]
  exact hM.isEndOf_unique hS hex.choose_spec h

end TangleDatum

omit [T2Space S] in
/-- A border edge lies along its side in the direction of the side. -/
theorem exists_march_of_side {P : ColouredPainting χ} {s e : Set S} (hs : s ∈ χ.Φ.sides) {u w : S}
  (hγ : χ.Φ.γ s = [u, w]) (σ : 𝕀 ≃ₜ closure s) (h0 : (σ 0).1 = u) (h1 : (σ 1).1 = w)
    (he : e ∈ P.Γ.E) (hes : e ⊆ s)
    (hbd : s ⊆ bd S) : ∃ a a', P.Γ.γ e = [a, a'] ∧ lineCoord σ a < lineCoord σ a' := by
  have hb : Painting.IsBorder e := by
    obtain ⟨x, hx⟩ : e.Nonempty := he.1
    exact ⟨x, hx, hbd (hes hx)⟩
  have h2 := (P.Γ.border_edge e he hb).1
  have hlen : (P.Γ.γ e).length = 2 := by rw [P.Γ.length_γ_eq he, h2]
  obtain ⟨a, a', hl⟩ := List.length_eq_two.mp hlen
  obtain ⟨f, t₁, t₂, ht, -, h3, h4, h5, h6⟩ := P.fits.border_dir e he hb s hs hes
  rw [hl] at h5 h6
  rw [hγ] at h3 h4
  simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons,
    List.getLast?_singleton] at h3 h4 h5 h6
  refine ⟨a, a', hl, ?_⟩
  rw [h5, h6]
  exact lineCoord_lt_of_ends σ f (Subtype.ext (h3.symm.trans h0.symm)) (Subtype.ext
    (h4.symm.trans h1.symm)) ht

omit [T2Space S] in
/-- Edges along a side, in order, have closures in order. -/
theorem lineCoord_le_of_borders {Γ : Painting S} {s c : Set S} {m : ℕ} {f : Fin m
  → Set S} {u₀ u₁ : S} (h : TangleDatum.BordersInOrder χ Γ s c f u₀ u₁) (hs : s ∈ χ.Φ.sides)
    (hc : IsClosed c) (hsc : s ⊆ c) {u w : S}
    (hγ : χ.Φ.γ s = [u, w]) (σ : 𝕀 ≃ₜ closure s) (h0 : (σ 0).1 = u) (h1 : (σ 1).1
      = w) {i j : Fin m} (hij : i < j) {x y : S} (hx : x ∈ closure (f i)) (hy : y ∈ closure
        (f j)) : lineCoord σ x ≤ lineCoord σ y := by
  obtain ⟨h₁, h₂, -, h₄, h₅⟩ := h
  rw [hγ] at h₁ h₂
  simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons,
    List.getLast?_singleton] at h₁ h₂
  subst h₁ h₂
  have hnd := χ.Φ.γ_nodup s hs
  rw [hγ] at hnd
  have hne : u ≠ w := by simpa using hnd
  have hset := χ.Φ.γ_set s hs
  have huS : u ∉ s := by
    have : u ∈ {v | v ∈ χ.Φ.γ s} := by rw [hγ]; simp
    rw [hset] at this
    exact this.2
  have hwS : w ∉ s := by
    have : w ∈ {v | v ∈ χ.Φ.γ s} := by rw [hγ]; simp
    rw [hset] at this
    exact this.2
  have hLc : closure s ⊆ c := closure_minimal hsc hc
  have hcl := continuousOn_lineCoord σ
  have base : ∀ x ∈ f i, ∀ y ∈ f j, lineCoord σ x ≤ lineCoord σ y := fun x hx y hy => by
    have hxs := (h₄ i).2 hx
    have hys := (h₄ j).2 hy
    exact lineCoord_le_of_inOrder hLc σ (h₅ i j hij x hx y hy) h0 h1 hne (subset_closure hxs)
      (subset_closure hys) (fun e => huS (e ▸ hxs)) (fun e => hwS (e ▸ hxs)) (fun e => huS
        (e ▸ hys))
  have step1 : ∀ y ∈ f j, lineCoord σ x ≤ lineCoord σ y := fun y hy => by
    have hclosed : IsClosed (closure s ∩ lineCoord σ ⁻¹' Iic (lineCoord σ y))
      := hcl.preimage_isClosed_of_isClosed isClosed_closure isClosed_Iic
    have hsub : f i ⊆ closure s ∩ lineCoord σ ⁻¹' Iic (lineCoord σ y) := fun x' hx'
      => ⟨subset_closure ((h₄ i).2 hx'), base x' hx' y hy⟩
    exact (closure_minimal hsub hclosed hx).2
  have hclosed : IsClosed (closure s ∩ lineCoord σ ⁻¹' Ici (lineCoord σ x))
    := hcl.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici
  have hsub : f j ⊆ closure s ∩ lineCoord σ ⁻¹' Ici (lineCoord σ x) := fun y' hy'
    => ⟨subset_closure ((h₄ j).2 hy'), step1 y' hy'⟩
  exact (closure_minimal hsub hclosed hy).2

namespace TangleDatum

variable {D : TangleDatum cap χ} {P₀ : ColouredPainting χ} {n : ℕ} {b : Set S → Set S}

/-- **The vertices come in the order of the ends.** If `y` comes before `y'` along a side, then the
vertex of `y` is not after the vertex of `y'`. On a long side this is the order of step (1) together
with the
direction of each edge. On a short side the end and its vertex are the same point. -/
theorem IsMatchSetting.lineCoord_endVertex_le (hM : D.IsMatchSetting P₀ n b)
  (hS : IsSurface S) {s : Set S} (hs : s ∈ χ.Φ.sides) {u w : S} (hγ : χ.Φ.γ s = [u, w])
    (σ : 𝕀 ≃ₜ closure s) (h0 : (σ 0).1 = u)
    (h1 : (σ 1).1 = w) {Θ : Set S} (hΘ : Θ ∈ cuffs S) (hsΘ : s ⊆ Θ) {e e' : Set S}
      (he : e ∈ P₀.Γ.E) (he' : e' ∈ P₀.Γ.E) (hes : e ⊆ s) (hes' : e' ⊆ s) (hbs : b e ⊆ s)
        (hbs' : b e' ⊆ s)
    (hsh : s ∉ χ.Φ.longSides → b e = s) (hsh' : s ∉ χ.Φ.longSides → b e' = s) {y y' : S}
      (hy : y ∈ tilde (b e)) (hy' : y' ∈ tilde (b e')) (hlt : lineCoord σ y < lineCoord σ y') :
    lineCoord σ (endVertex P₀ D.P b y) ≤ lineCoord σ (endVertex P₀ D.P b y') := by
  have hbd : s ⊆ bd S := hsΘ.trans (cuff_subset_bd ⟨Θ, hΘ⟩)
  obtain ⟨v, hv, hv'⟩ := exists_isEndOf hM.edge he hy
  obtain ⟨v₁, hv₁, hv₁'⟩ := exists_isEndOf hM.edge he' hy'
  rw [hM.endVertex_eq hS hv', hM.endVertex_eq hS hv₁']
  by_cases hl : s ∈ χ.Φ.longSides
  · obtain ⟨m, f, g, c, r, u₀, u₁, u₀', u₁', hX⟩ := hM.edge.side s hl
    obtain ⟨p, rfl⟩ := hX.all₀ e he hes
    obtain ⟨q, rfl⟩ := hX.all₀ e' he' hes'
    rw [hX.map] at hy hbs
    rw [hX.map] at hy' hbs'
    have hcc : IsClosed c := ((cuff_statement S hS).2.2 _ hX.cuff).isCompact.isClosed
    rcases lt_trichotomy p q with hpq | rfl | hpq
    · exact lineCoord_le_of_borders hX.order₀ hs hcc hX.side_cuff hγ σ h0 h1 hpq hv.1 hv₁.1
    · obtain ⟨a, a', hl₁, hlt₁⟩ := exists_march_of_side (P := P₀) hs hγ σ h0 h1 he hes hbd
      have hge := hM.edge.mem _ he
      rw [hX.map] at hge
      obtain ⟨c₀, c₁, hl₂, hlt₂⟩ := exists_march_of_side (P := D.P) hs hγ σ h0 h1 hge hbs hbd
      have hset : ∀ {z}, z ∈ tilde (g p) → z = c₀ ∨ z = c₁ := fun {z} hz => by
        have : z ∈ {v | v ∈ D.P.Γ.γ (g p)} := by rw [D.P.Γ.γ_set _ hge]; exact hz
        rw [hl₂] at this
        simpa using this
      have hyc : y = c₀ := by
        rcases hset hy with h | h
        · exact h
        · exfalso
          rcases hset hy' with h' | h'
          · rw [h, h'] at hlt
            linarith
          · rw [h, h'] at hlt
            exact lt_irrefl _ hlt
      have hyc' : y' = c₁ := by
        rcases hset hy' with h | h
        · exfalso
          rw [hyc, h] at hlt
          exact lt_irrefl _ hlt
        · exact h
      have hbl : b (f p) = g p := hX.map p
      have e₀ : IsEndOf P₀ D.P b y a :=
        ⟨f p, he, 0, by simp [hl₁], by simp [hbl, hl₂],
          by simp [hl₁], by simp [hbl, hl₂, hyc]⟩
      have e₁ : IsEndOf P₀ D.P b y' a' :=
        ⟨f p, he, 1, by simp [hl₁], by simp [hbl, hl₂],
          by simp [hl₁], by simp [hbl, hl₂, hyc']⟩
      rw [hM.isEndOf_unique hS hv' e₀, hM.isEndOf_unique hS hv₁' e₁]
      exact hlt₁.le
    · exfalso
      exact absurd hlt (not_lt.mpr (lineCoord_le_of_borders hX.order hs hcc hX.side_cuff hγ σ h0 h1
        hpq hy'.1 hy.1))
  · have hsh₁ : s ∈ χ.Φ.shortSides := ⟨hs, fun h => hl ⟨hs, h⟩⟩
    have hsE₀ := P₀.fits.short_sides hsh₁
    have heq : ∀ {e : Set S}, e ∈ P₀.Γ.E → e ⊆ s → e = s := fun {e} he hes => by
      obtain ⟨x, hx⟩ : e.Nonempty := he.1
      exact arcComponent_eq he hsE₀ hx (hes hx)
    have hbss : b s = s := hM.edge.short s hsh₁
    have hself : ∀ {z}, z ∈ tilde s → IsEndOf P₀ D.P b z z := fun {z} hz => by
      have hγ₀ := short_γ_eq P₀ hsh₁
      have hγ₁ := short_γ_eq D.P hsh₁
      have hz' : z ∈ {v | v ∈ χ.Φ.γ s} := by rw [χ.Φ.γ_set s hs]; exact hz
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz'
      have h1' : i < (P₀.Γ.γ s).length := by rw [hγ₀]; exact hi
      have h2' : i < (D.P.Γ.γ (b s)).length := by rw [hbss, hγ₁]; exact hi
      refine ⟨s, hsE₀, i, h1', h2', ?_, ?_⟩
      · simp only [hγ₀]
      · simp only [hbss, hγ₁]
    have hes₁ := heq he hes
    have hes₂ := heq he' hes'
    rw [hes₁, hbss] at hy
    rw [hes₂, hbss] at hy'
    rw [hM.isEndOf_unique hS hv' (hself hy), hM.isEndOf_unique hS hv₁' (hself hy')]
    exact hlt.le

end TangleDatum

end GraphMinor.GM19
