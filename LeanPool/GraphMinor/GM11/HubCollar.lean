/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.HubCycle
public import LeanPool.GraphMinor.GM11.Cylinder

/-!
# A collar of the frontier of a region

Let `Γ` be a 2-cell drawing in a sphere with no loop, `Γ'` a radial drawing of `Γ`, and `r` a region
of `Γ`
with vertex `c`. The corners at `c`, in their cyclic order, are closed discs with three sides.
Coordinates
on them (`exists_square_chart`) that agree on the spokes form a map on the cylinder
(`exists_cylinder`),
which runs along the frontier of `r` at height `0` and is injective on the rest
(`exists_hub_collar`).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- What the corners at the vertex of a region give. Here `v i`, `a i`, `s i`, `P i` are the `i`-th
vertex
of the frontier of `r`, edge of the frontier, spoke, and region of `Γ ∪ Γ'`, and these repeat with
period
`n`. The map `ε i` runs along the closure of `a i`, and `h` is the collar. -/
structure IsHubCollar (Γ Γ' H : Drawing S) (r : Set S) (n : ℕ) (v : ℕ → S) (a s P : ℕ → Set S)
    (ε : ℕ → I → S) (h : C(Circle × I, S)) : Prop where
  two_le : 2 ≤ n
  per_v : ∀ i, v (i + n) = v i
  per_a : ∀ i, a (i + n) = a i
  per_s : ∀ i, s (i + n) = s i
  per_P : ∀ i, P (i + n) = P i
  per_ε : ∀ i, ε (i + n) = ε i
  edge : ∀ i, a i ∈ Γ.E
  vertex : ∀ i, v i ∈ Γ.V
  cap : ∀ i, closure (a i) ∩ Γ.V = {v i, v (i + 1)}
  ne : ∀ i, v i ≠ v (i + 1)
  spoke : ∀ i, s i ∈ Γ'.E
  spoke_cap : ∀ i, ∃ c ∈ r, closure (s i) ∩ Γ'.V = {v i, c}
  region : ∀ i, P i ∈ H.R
  region_sub : ∀ i, P i ⊆ r
  edge_cl : ∀ i, a i ⊆ closure (P i)
  spoke_cl : ∀ i, s i ⊆ closure (P i) ∧ s (i + 1) ⊆ closure (P i)
  inj : ∀ i j, i < n → j < n → P i = P j → i = j
  all : ∀ p ∈ H.R, p ⊆ r → ∃ i, i < n ∧ p = P i
  ε_cont : ∀ i, Continuous (ε i)
  ε_inj : ∀ i, Function.Injective (ε i)
  ε_zero : ∀ i, ε i 0 = v i
  ε_one : ∀ i, ε i 1 = v (i + 1)
  ε_range : ∀ i, range (ε i) = closure (a i)
  bottom : ∀ i, i < n → ∀ u : I, h (Circle.exp (2 * Real.pi * ((i + u.1) / n)), 0) = ε i u
  injOn : InjOn h {p | 0 < p.2}
  mem_r : ∀ p : Circle × I, 0 < p.2 → h p ∈ r
  range_bottom : range (fun z : Circle => h (z, 0)) = frontier r
  isOpen : IsOpen (rᶜ ∪ h '' {p | p.2 < 1})

variable {Γ Γ' : Drawing S}

omit [ConnectedSpace S] in
/-- Two half-edges at the vertex of a region with the same spoke are equal. -/
theorem half_unique (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') (hS : IsClosedSurface S)
    {γ : Set S → I → S} (hγ : EdgePar (radialUnion hrad) γ) {r : Set S}
    (hr : r ∈ Γ.R) {c : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V) {k k' : halfEdges (radialUnion hrad) γ c}
    (h : k.1.1 = k'.1.1) : k = k' := by
  have hs : k.1.1 ∈ Γ'.E := hub_half_spoke hrad hr hc k hγ
  have hcs : c ∈ closure k.1.1 := by
    have := end_mem_closure hγ k.2.1 k.1.2
    rwa [k.2.2] at this
  obtain ⟨a, ha, hcap⟩ := spoke_end hrad hS hr hc hcV hs hcs
  have hac : a ≠ c := fun h => region_subset hr hc (Γ.V_subset_U (h ▸ ha))
  have ham : a ∈ closure k.1.1 ∩ Γ'.V := by rw [hcap]; simp
  have haH : a ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact ham.2
  obtain ⟨b, hb⟩ := exists_end_eq hγ k.2.1 haH ham.1
  apply Subtype.ext
  refine Prod.ext h ?_
  by_contra hbb
  have h₁ : γ k.1.1 (endOf k.1.2) = c := k.2.2
  have h₂ : γ k.1.1 (endOf k'.1.2) = c := by
    rw [h]
    exact k'.2.2
  have : b = k.1.2 ∨ b = k'.1.2 := by
    cases b <;> cases hk : k.1.2 <;> cases hk' : k'.1.2 <;> simp_all
  rcases this with rfl | rfl
  · exact hac (hb.symm.trans h₁)
  · exact hac (hb.symm.trans h₂)

omit [ConnectedSpace S] in
private theorem half_height_collar {r : Set S} (H₀ : C(Circle × I, S)) {c : S}
    (hbotU : ∀ z, H₀ (z, 0) ∉ r) (hHc : ∀ z, H₀ (z, 1) = c)
    (hpos' : ∀ {p : Circle × I}, 0 < p.2 → H₀ p ∈ r)
    (hinjH : InjOn H₀ {p | 0 < p.2 ∧ p.2 < 1})
    (hcover : ∀ z ∈ r, ∃ p : Circle × I, 0 < p.2 ∧ H₀ p = z)
    (havoid : ∀ p : Circle × I, 0 < p.2 → p.2 < 1 → H₀ p ≠ c) :
    ∃ hh : C(Circle × I, S), (∀ z, hh (z, 0) = H₀ (z, 0)) ∧
      InjOn hh {p | 0 < p.2} ∧ (∀ p : Circle × I, 0 < p.2 → hh p ∈ r) ∧
      IsOpen (rᶜ ∪ hh '' {p | p.2 < 1}) := by
  have isCompact_closed_set : IsCompact {p : Circle × I | (1 / 2 : ℝ) ≤ p.2.1} :=
    (isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)).isCompact
  let hh : C(Circle × I, S) := ⟨fun p => H₀ (p.1, halfT p.2), by
    refine H₀.continuous.comp (continuous_fst.prodMk ?_)
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_snd).div_const 2⟩
  have hhalf0 : ∀ t : I, 0 < t → 0 < halfT t := fun t ht => by
    change (0 : ℝ) < t.1 / 2
    have : (0 : ℝ) < t.1 := ht
    positivity
  have hhalf1 : ∀ t : I, halfT t < 1 := fun t => by
    change t.1 / 2 < 1
    have := t.2.2
    linarith
  have hhz : ∀ z, hh (z, 0) = H₀ (z, 0) := fun z => by
    change H₀ (z, halfT 0) = _
    congr 2
    exact Subtype.ext (by simp [halfT])
  have hzero' : ∀ {p : Circle × I}, H₀ p ∈ r → 0 < p.2 := by
    rintro ⟨z, t⟩ hm
    by_contra hnot
    have ht : t = 0 := le_antisymm (not_lt.mp hnot) (unitInterval.nonneg t)
    exact hbotU z (ht ▸ hm)
  have hcompl : (rᶜ ∪ hh '' {p | p.2 < 1})ᶜ = H₀ '' {p | (1 / 2 : ℝ) ≤ p.2.1} := by
    ext x
    constructor
    · intro hx
      have hxr : x ∈ r := by
        by_contra h
        exact hx (Or.inl h)
      obtain ⟨p, hp, rfl⟩ := hcover x hxr
      refine ⟨p, ?_, rfl⟩
      by_contra hlt
      have hlt' : p.2.1 < 1 / 2 := not_le.mp hlt
      refine hx (Or.inr ⟨(p.1, ⟨2 * p.2.1, by have := p.2.2.1; positivity, by linarith⟩), ?_, ?_⟩)
      · change 2 * p.2.1 < 1
        linarith
      · change H₀ (p.1, halfT _) = H₀ p
        congr 1
        refine Prod.ext rfl (Subtype.ext ?_)
        simp [halfT]
    · rintro ⟨p, hp, rfl⟩ (hcase | ⟨q, hq, hqe⟩)
      · have hp0 : 0 < p.2 := by
          change (0 : ℝ) < p.2.1
          have : (1 / 2 : ℝ) ≤ p.2.1 := hp
          linarith
        exact hcase (hpos' hp0)
      · have hp0 : 0 < p.2 := by
          change (0 : ℝ) < p.2.1
          have : (1 / 2 : ℝ) ≤ p.2.1 := hp
          linarith
        have hm : H₀ (q.1, halfT q.2) ∈ r := by
          have : H₀ (q.1, halfT q.2) = H₀ p := hqe
          rw [this]
          exact hpos' hp0
        have hq0 : 0 < halfT q.2 := hzero' (p := (q.1, halfT q.2)) hm
        have hlt : (halfT q.2).1 < 1 / 2 := by
          have : q.2.1 < 1 := hq
          change q.2.1 / 2 < 1 / 2
          linarith
        by_cases hp1 : p.2 < 1
        · have heq := hinjH (x₁ := (q.1, halfT q.2)) (x₂ := p) ⟨hq0, hhalf1 _⟩ ⟨hp0, hp1⟩ hqe
          have : (1 / 2 : ℝ) ≤ p.2.1 := hp
          rw [← heq] at this
          have h₂ : (1 / 2 : ℝ) ≤ (halfT q.2).1 := this
          linarith
        · have hp1' : p.2 = 1 := le_antisymm (unitInterval.le_one _) (not_lt.mp hp1)
          obtain ⟨z, t⟩ := p
          simp only at hp1'
          subst hp1'
          have hqc : H₀ (q.1, halfT q.2) = c := hqe.trans (hHc z)
          exact havoid ⟨q.1, halfT q.2⟩ hq0 (hhalf1 _) hqc
  refine ⟨hh, hhz, ?_, ?_, ?_⟩
  · rintro ⟨z, t⟩ ht ⟨z', t'⟩ ht' heq
    have hpt := hinjH (x₁ := (z, halfT t)) (x₂ := (z', halfT t')) ⟨hhalf0 _ ht, hhalf1 _⟩
      ⟨hhalf0 _ ht', hhalf1 _⟩ heq
    have h₁ : z = z' := congrArg Prod.fst hpt
    have h₂ : halfT t = halfT t' := congrArg Prod.snd hpt
    have h₃ : t.1 / 2 = t'.1 / 2 := congrArg Subtype.val h₂
    subst h₁
    exact Prod.ext rfl (Subtype.ext (by linarith))
  · intro p hp
    exact hpos' (p := (p.1, halfT p.2)) (hhalf0 _ hp)
  · rw [← isClosed_compl_iff, hcompl]
    exact (isCompact_closed_set.image H₀.continuous).isClosed

omit [ConnectedSpace S] in
private theorem corner_charts_cover_region (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ')
    (hS : IsClosedSurface S) {r : Set S} (hr : r ∈ Γ.R) {c : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V)
    {γ : Set S → I → S} (hγ : EdgePar (radialUnion hrad) γ) (hcH : c ∈ (radialUnion hrad).V) :
    let K := halfEdges (radialUnion hrad) γ c
    ∀ {next : K → K} {ρ : K → Set S}, IsCorners (radialUnion hrad) γ c next ρ →
    ∀ {A : K → S} {E' : K → Set S} {sp ε₀ : K → I → S} {G : K → I × I → S},
    (∀ k, A k ∈ Γ.V) → (∀ k, E' k ∈ Γ.E) →
    (∀ k, range (sp k) = closure k.1.1) → (∀ k, sp k 0 = A k) → (∀ k, sp k 1 = c) →
    (∀ k, range (ε₀ k) = closure (E' k)) → (∀ k, range (G k) = closure (ρ k)) →
    (∀ k t, G k (0, t) = sp k t) → (∀ k u, G k (u, 0) = ε₀ k u) →
    Nonempty K → ∀ {n : ℕ} {κ : ℕ → K} {H₀ : C(Circle × I, S)},
    (∀ k, ∃ i, i < n ∧ κ i = k) →
    (∀ i, i < n → ∀ u t : I, H₀ (Circle.exp (2 * Real.pi * ((i + u.1) / n)), t) = G (κ i) (u, t)) →
    ∀ z ∈ r, ∃ p : Circle × I, 0 < p.2 ∧ H₀ p = z := by
  intro K next ρ hcor A E' sp ε₀ G hA hE' hspR hspZ hspO hεr hGr' hGl hGb hK n κ H₀ hκall hH₀
  obtain ⟨k₀⟩ := hK
  intro z hz
  have hup : ∀ (k : halfEdges (radialUnion hrad) γ c) (q : I × I), 0 < q.2 → G k q = z →
      ∃ p : Circle × I, 0 < p.2 ∧ H₀ p = z := by
    intro k q hq hG
    obtain ⟨i, hi, rfl⟩ := hκall k
    exact ⟨(Circle.exp (2 * Real.pi * ((i + q.1.1) / n)), q.2), hq, by rw [hH₀ i hi q.1 q.2]; exact
      hG⟩
  have hzΓ : z ∉ Γ.U := region_subset hr hz
  by_cases hzH : z ∈ (radialUnion hrad).U
  · have hzU' : z ∈ Γ'.U := hzH.resolve_left hzΓ
    by_cases hzV : z ∈ Γ'.V
    · obtain rfl : z = c := hub_unique hrad hr hc hcV hz hzV
      exact hup k₀ (0, 1) one_pos (by rw [hGl, hspO])
    · rw [Γ'.U_eq] at hzU'
      rcases hzU' with h | h
      · exact (hzV h).elim
      obtain ⟨g', hg', hzg'⟩ := mem_iUnion₂.mp h
      have hzg : z ∈ g' := Γ'.closure_diff_V hg' ▸ ⟨hzg', hzV⟩
      have hcg := (spoke_in_region hrad hS hr hc hcV hg' hzg hz).1
      have hgH : g' ∈ (radialUnion hrad).E := by
        rw [radialUnion_E]
        exact Or.inr hg'
      obtain ⟨b, hb⟩ := exists_end_eq hγ hgH hcH hcg
      let k : halfEdges (radialUnion hrad) γ c := ⟨(g', b), hgH, hb⟩
      have hzr : z ∈ range (sp k) := hspR k ▸ hzg'
      obtain ⟨t, rfl⟩ := hzr
      refine hup k (0, t) (lt_of_le_of_ne (unitInterval.nonneg t) ?_) (hGl k t)
      rintro rfl
      exact hzΓ (by
        rw [hspZ]
        exact Γ.V_subset_U (hA k))
  · obtain ⟨p, hp, hzp⟩ := exists_region_of_notMem hzH
    have hpr : p ⊆ r := by
      obtain ⟨r', hr', hsub⟩ := exists_region_of_sub hrad hp
      obtain rfl := region_eq_of_mem hr' hr (hsub hzp) hz
      exact hsub
    have hcp := hub_mem_closure hrad hS hr hp hpr hc hcV
    obtain ⟨k, rfl⟩ := IsCorners.all hcor p hp hcp
    have hzm : z ∈ range (G k) := hGr' k ▸ subset_closure hzp
    obtain ⟨q, rfl⟩ := hzm
    refine hup k q (lt_of_le_of_ne (unitInterval.nonneg _) ?_) rfl
    intro hq
    have h₁ : q = (q.1, 0) := Prod.ext rfl hq.symm
    have h₂ : G k q = ε₀ k q.1 := by
      rw [h₁]
      exact hGb k q.1
    exact hzΓ (h₂ ▸ Γ.closure_subset_U (hE' k) (hεr k ▸ mem_range_self _))

omit [ConnectedSpace S] in
private theorem cylinder_bottom_eq_frontier {r : Set S} (hrOpen : IsOpen r)
    (H₀ : C(Circle × I, S))
    (hcover : ∀ z ∈ r, ∃ p : Circle × I, 0 < p.2 ∧ H₀ p = z)
    (hpos' : ∀ {p : Circle × I}, 0 < p.2 → H₀ p ∈ r)
    (hbotU : ∀ z, H₀ (z, 0) ∉ r) : range (fun z : Circle => H₀ (z, 0)) = frontier r := by
  have hcl : closure r ⊆ range H₀ := by
    have hcomp : IsCompact (range H₀) := isCompact_range H₀.continuous
    refine closure_minimal (fun z hz => ?_) hcomp.isClosed
    obtain ⟨p, -, rfl⟩ := hcover z hz
    exact mem_range_self p
  apply subset_antisymm
  · rintro _ ⟨z, rfl⟩
    rw [hrOpen.frontier_eq]
    refine ⟨?_, hbotU z⟩
    have hcont : Continuous fun t : I => H₀ (z, t) :=
      H₀.continuous.comp (Continuous.prodMk continuous_const continuous_id)
    have h₀ : (0 : I) ∈ closure (Ioi (0 : I)) := by
      rw [closure_Ioi' ⟨1, zero_lt_one⟩]
      exact self_mem_Ici
    have h₁ := image_closure_subset_closure_image hcont (mem_image_of_mem _ h₀)
    refine closure_mono ?_ h₁
    rintro _ ⟨t, ht, rfl⟩
    exact hpos' (p := (z, t)) ht
  · intro x hx
    have hxr : x ∉ r := by
      have := hx
      rw [hrOpen.frontier_eq] at this
      exact this.2
    obtain ⟨⟨z, t⟩, rfl⟩ := hcl (frontier_subset_closure hx)
    by_cases ht : 0 < t
    · exact (hxr (hpos' ht)).elim
    · have : t = 0 := le_antisymm (not_lt.mp ht) (unitInterval.nonneg t)
      subst this
      exact ⟨z, rfl⟩

omit [ConnectedSpace S] in
private theorem corner_square_chart (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ')
    (hS : IsClosedSurface S) {r : Set S} (hr : r ∈ Γ.R) {c : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V)
    {γ : Set S → I → S} (hγ : EdgePar (radialUnion hrad) γ) :
    let K := halfEdges (radialUnion hrad) γ c
    ∀ {next : K → K} {ρ P Q : K → Set S} {W : Set S} {τ : K → I},
    IsSectors (radialUnion hrad) γ c next ρ P W Q τ →
    ∀ {A B : K → S} {E' : K → Set S},
    (∀ k, E' k ∈ Γ.E) → (∀ k : K, k.1.1 ∈ Γ'.E) → (∀ k, A k ≠ B k) →
    (∀ k, A k ≠ c) → (∀ k, B k = A (next k)) →
    (∀ k, closure k.1.1 ∩ Γ'.V = {A k, c}) →
    (∀ k, closure (next k).1.1 ∩ Γ'.V = {B k, c}) →
    (∀ k, frontier (ρ k) = closure k.1.1 ∪ closure (next k).1.1 ∪ closure (E' k)) →
    (∀ k, IsClosedDisc (closure (ρ k)) ∧ discInt (closure (ρ k)) = ρ k ∧
      discBd (closure (ρ k)) = frontier (ρ k)) →
    ∀ (f : ∀ k : K, I ≃ₜ closure k.1.1) (g : ∀ k : K, I ≃ₜ closure (E' k)),
    let sp : K → I → S := fun k t => (f k t).1
    let ε₀ : K → I → S := fun k t => (g k t).1
    (∀ k, Continuous (sp k)) → (∀ k, Continuous (ε₀ k)) →
    (∀ k, Function.Injective (sp k)) → (∀ k, Function.Injective (ε₀ k)) →
    (∀ k, range (sp k) = closure k.1.1) → (∀ k, range (ε₀ k) = closure (E' k)) →
    (∀ k, sp k 0 = A k) → (∀ k, sp k 1 = c) →
    (∀ k, ε₀ k 0 = A k) → (∀ k, ε₀ k 1 = B k) →
    ∀ k, ∃ G : I × I → S, Continuous G ∧ (∀ u, G (u, 0) = ε₀ k u) ∧ (∀ t, G (0, t) = sp k t) ∧
    (∀ t, G (1, t) = sp (next k) t) ∧ (∀ u, G (u, 1) = sp k 1) ∧ InjOn G {p | p.2 < 1} ∧
    range G = closure (ρ k) ∧
    (∀ p : I × I, 0 < p.1 → p.1 < 1 → 0 < p.2 → p.2 < 1 → G p ∉ discBd (closure (ρ k))) := by
  intro K next ρ P Q W τ hsec A B E' hE' hsp hAB hAc hBnext hcapa hcapb hfr hdisc
    f g sp ε₀ hspC hεc hspI hεi hspR hεr hspZ hspO hε0 hε1
  have hUU : Γ.U ∩ Γ'.U = Γ.V := radial_inter hrad
  have hse : ∀ (k k' : halfEdges (radialUnion hrad) γ c) {x}, x ∈ closure (E' k)
    → x ∈ closure k'.1.1 →
      x ∈ Γ.V := fun k k' x h₁ h₂ =>
    hUU ▸ (⟨Γ.closure_subset_U (hE' k) h₁, Γ'.closure_subset_U (hsp k') h₂⟩ : x ∈ Γ.U ∩ Γ'.U)
  intro k
  obtain ⟨hD, -, hbd⟩ := hdisc k
  have hkne : k.1.1 ≠ (next k).1.1 := by
    intro h
    exact IsSectors.next_ne hsec k (half_unique hrad hS hγ hr hc hcV h.symm)
  refine exists_square_chart hD hS.2.2 (hεc k) (hspC k) (hspC (next k)) (hεi k) (hspI k) (hspI
    (next k))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hε0, hspZ]
  · rw [hε1, hspZ, hBnext]
  · rw [hspO, hspO]
  · intro s t h
    have h₁ : ε₀ k s ∈ closure (E' k) := (g k s).2
    have h₂ : ε₀ k s ∈ closure k.1.1 := h ▸ (f k t).2
    have hV := hse k k h₁ h₂
    have h₃ : ε₀ k s ∈ closure k.1.1 ∩ Γ'.V := ⟨h₂, radial_V hrad hV⟩
    rw [hcapa] at h₃
    have h₄ : ε₀ k s = A k := h₃.resolve_right fun h' => hAc k (by
      have h₅ : ε₀ k s ∈ Γ.V := hV
      exact (region_subset hr hc (Γ.V_subset_U (h' ▸ h₅))).elim)
    exact ⟨hεi k (h₄.trans (hε0 k).symm), hspI k ((h.symm.trans h₄).trans (hspZ k).symm)⟩
  · intro s t h
    have h₁ : ε₀ k s ∈ closure (E' k) := (g k s).2
    have h₂ : ε₀ k s ∈ closure (next k).1.1 := h ▸ (f (next k) t).2
    have hV := hse k (next k) h₁ h₂
    have h₃ : ε₀ k s ∈ closure (next k).1.1 ∩ Γ'.V := ⟨h₂, radial_V hrad hV⟩
    rw [hcapb] at h₃
    have h₄ : ε₀ k s = B k := h₃.resolve_right fun h' => hAc k (by
      have h₅ : ε₀ k s ∈ Γ.V := hV
      exact (region_subset hr hc (Γ.V_subset_U (h' ▸ h₅))).elim)
    refine ⟨hεi k (h₄.trans (hε1 k).symm), hspI (next k) ((h.symm.trans h₄).trans ?_)⟩
    rw [hBnext, hspZ]
  · intro s t h
    have h₁ : sp k s ∈ closure k.1.1 := (f k s).2
    have h₂ : sp k s ∈ closure (next k).1.1 := h ▸ (f (next k) t).2
    have hV := closure_inter_subset_V (hsp k) (hsp (next k)) hkne ⟨h₁, h₂⟩
    have m₁ : sp k s ∈ closure k.1.1 ∩ Γ'.V := ⟨h₁, hV⟩
    have m₂ : sp k s ∈ closure (next k).1.1 ∩ Γ'.V := ⟨h₂, hV⟩
    rw [hcapa] at m₁
    rw [hcapb] at m₂
    have hxc : sp k s = c := by
      rcases m₁ with e₁ | e₁
      · rcases m₂ with e₂ | e₂
        · exact (hAB k (e₁.symm.trans e₂)).elim
        · exact e₂
      · exact e₁
    exact ⟨hspI k (hxc.trans (hspO k).symm), hspI (next k) ((h.symm.trans hxc).trans (hspO _).symm)⟩
  · rw [(hdisc k).2.2, hfr k, hεr, hspR, hspR]
    ext x
    simp only [mem_union]
    tauto

omit [ConnectedSpace S] in
private theorem cylinder_between_boundaries (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ')
    (hS : IsClosedSurface S) {r : Set S} (hr : r ∈ Γ.R) {c : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V)
    {γ : Set S → I → S} (hγ : EdgePar (radialUnion hrad) γ) :
    let K := halfEdges (radialUnion hrad) γ c
    ∀ {ρ : K → Set S} {sp : K → I → S} {G : K → I × I → S},
    (∀ k : K, k.1.1 ∈ Γ'.E) → (∀ k, ρ k ∈ (radialUnion hrad).R) →
    (∀ k, ρ k ⊆ r) → (∀ k : K, k.1.1 ⊆ r) →
    (∀ k k', ρ k = ρ k' → k = k') →
    (∀ k, Function.Injective (sp k)) →
    (∀ k, InjOn (G k) {p | p.2 < 1}) →
    (∀ k t, G k (0, t) = sp k t) →
    (∀ k (p : I × I), 0 < p.1 → p.1 < 1 → 0 < p.2 → p.2 < 1 → G k p ∈ ρ k) →
    (∀ k (t : I), 0 < t → t < 1 → sp k t ∈ k.1.1) →
    ∀ {n : ℕ}, 0 < n →
    ∀ {κ : ℕ → K} {H₀ : C(Circle × I, S)},
    (∀ i j, i < n → j < n → κ i = κ j → i = j) →
    (∀ i, i < n → ∀ u t : I, H₀ (Circle.exp (2 * Real.pi * ((i + u.1) / n)), t) = G (κ i) (u, t)) →
    (∀ {p : Circle × I}, 0 < p.2 → p.2 < 1 → H₀ p ∈ r) ∧
      InjOn H₀ {p | 0 < p.2 ∧ p.2 < 1} ∧
      ∀ p : Circle × I, 0 < p.2 → p.2 < 1 → H₀ p ≠ c := by
  intro K ρ sp G hsp hR hρr hsubr hcoreq hspI hGi hGl hGin hspIn n hn κ H₀ hκinj hH₀
  have hclass : ∀ (z : Circle) (t : I), 0 < t → t < 1 → ∃ i, i < n ∧ ∃ u : I, u < 1 ∧
      z = Circle.exp (2 * Real.pi * ((i + u.1) / n)) ∧ H₀ (z, t) = G (κ i) (u, t) ∧
      ((0 < u ∧ H₀ (z, t) ∈ ρ (κ i)) ∨ (u = 0 ∧ H₀ (z, t) = sp (κ i) t ∧ H₀ (z, t) ∈ (κ i).1.1))
        := by
    intro z t h₀ h₁
    obtain ⟨i, hi, u, hu, rfl⟩ := exists_circle_param hn z
    refine ⟨i, hi, u, hu, rfl, hH₀ i hi u t, ?_⟩
    rw [hH₀ i hi u t]
    by_cases hu0 : 0 < u
    · exact Or.inl ⟨hu0, hGin _ _ hu0 hu h₀ h₁⟩
    · have hu0' : u = 0 := le_antisymm (not_lt.mp hu0) (unitInterval.nonneg u)
      subst hu0'
      refine Or.inr ⟨rfl, hGl _ _, ?_⟩
      rw [hGl]
      exact hspIn _ _ h₀ h₁
  have hpos : ∀ {p : Circle × I}, 0 < p.2 → p.2 < 1 → H₀ p ∈ r := by
    rintro ⟨z, t⟩ h₀ h₁
    obtain ⟨i, -, u, -, -, -, h | h⟩ := hclass z t h₀ h₁
    · exact hρr _ h.2
    · exact hsubr _ h.2.2
  have hinjH : InjOn H₀ {p | 0 < p.2 ∧ p.2 < 1} := by
    rintro ⟨z, t⟩ ⟨h₀, h₁⟩ ⟨z', t'⟩ ⟨h₀', h₁'⟩ heq
    simp only at h₀ h₁ h₀' h₁'
    obtain ⟨i, hi, u, hu, rfl, hG₁, c₁⟩ := hclass z t h₀ h₁
    obtain ⟨i', hi', u', hu', rfl, hG₂, c₂⟩ := hclass z' t' h₀' h₁'
    have hspokeU : ∀ {i x}, x ∈ (κ i).1.1 → x ∈ (radialUnion hrad).U := fun {i x} hx =>
      Or.inr ((hsp (κ i)).2.1 hx).1
    have hii : i = i' ∧ (u = u' ∨ False) ∧ t = t' := by
      rcases c₁ with ⟨hu0, c₁⟩ | ⟨hu0, c₁, c₃⟩ <;> rcases c₂ with ⟨hu0', c₂⟩ | ⟨hu0', c₂, c₄⟩
      · have e₁ : ρ (κ i) = ρ (κ i') := region_eq_of_mem (hR _) (hR _) c₁ (heq ▸ c₂)
        have e₂ := hκinj i i' hi hi' (hcoreq _ _ e₁)
        subst e₂
        rw [hG₁, hG₂] at heq
        have := hGi (κ i) (show (u, t).2 < 1 from h₁) (show (u', t').2 < 1 from h₁') heq
        exact ⟨rfl, Or.inl (congrArg Prod.fst this), congrArg Prod.snd this⟩
      · exact (region_subset (hR _) c₁ (hspokeU (heq ▸ c₄))).elim
      · exact (region_subset (hR _) c₂ (hspokeU (heq ▸ c₃))).elim
      · have hee : (κ i).1.1 = (κ i').1.1 :=
          Γ'.edge_eq_of_mem (hsp _) (hsp _) c₃ (heq ▸ c₄)
        have e₂ := hκinj i i' hi hi' (half_unique hrad hS hγ hr hc hcV hee)
        subst e₂
        rw [c₁, c₂] at heq
        exact ⟨rfl, Or.inl (hu0.trans hu0'.symm), hspI _ heq⟩
    obtain ⟨rfl, hu₁ | hu₁, rfl⟩ := hii
    · rw [hu₁]
    · exact hu₁.elim
  have havoid : ∀ p : Circle × I, 0 < p.2 → p.2 < 1 → H₀ p ≠ c := by
    rintro ⟨z, t⟩ ht₀ ht₁ he
    obtain ⟨i, -, u, -, -, -, h | h⟩ := hclass z t ht₀ ht₁
    · exact region_subset (hR _) (he ▸ h.2) (Or.inr (Γ'.V_subset_U hcV))
    · have hcin : c ∈ (κ i).1.1 := he ▸ h.2.2
      exact ((Γ'.closure_diff_V (hsp (κ i))).superset hcin).2 hcV
  exact ⟨fun {_} hp₀ hp₁ => hpos hp₀ hp₁, hinjH, havoid⟩

omit [T2Space S] [ConnectedSpace S] in
private theorem range_homeomorph_subtype {U : Set S} (f : I ≃ₜ U) :
    range (fun t => (f t).1) = U := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact (f t).2
  · intro hx
    exact ⟨f.symm ⟨x, hx⟩, by simp⟩

/-- **The collar of the frontier of a region.** -/
theorem exists_hub_collar (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') (hS : IsClosedSurface S)
    (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ') (hsph : IsSphere S) (hE : Γ.E.Nonempty)
    (hloop : ∀ e ∈ Γ.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ.V = {x, y}) {r : Set S} (hr : r ∈ Γ.R) :
    ∃ n v a s P ε h, IsHubCollar Γ Γ' (radialUnion hrad) r n v a s P ε h := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hne : Nonempty S := ⟨(region_nonempty hr).some⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar (radialUnion hrad)
  obtain ⟨c, ⟨hc, hcV⟩, -⟩ := hrad.2.2.2.1 r hr
  change c ∈ r at hc
  change c ∈ Γ'.V at hcV
  have hcH : c ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact hcV
  obtain ⟨next, ρ, Pc, Wc, Qc, τc, hsec⟩ := exists_sectors hS _ hγ hcH
    (hub_two_halves hrad hS hmax hE hloop hγ hr hc hcV)
  have hcor := IsSectors.corners hsec
  have hsurj := next_surjective hcor
  have hR : ∀ k, ρ k ∈ (radialUnion hrad).R := IsCorners.region hcor
  have hρr : ∀ k, ρ k ⊆ r := fun k => by
    obtain ⟨r', hr', hsub⟩ := exists_region_of_sub hrad (hR k)
    obtain ⟨w, hw', hw⟩ := mem_closure_iff.mp (IsCorners.closure_v hcor k) r (region_isOpen hr) hc
    obtain rfl := region_eq_of_mem hr' hr (hsub hw) hw'
    exact hsub
  have hdata := corner_data hrad hS hmax hE hloop hγ hr hc hcV hsec hρr
  choose E' hE' A B hAB hA hB hcap hep hcapa hcapb hfr using hdata
  have hsp : ∀ k : halfEdges (radialUnion hrad) γ c, k.1.1 ∈ Γ'.E := fun k
    => hub_half_spoke hrad hr hc k hγ
  have hBnext : ∀ k, B k = A (next k) := by
    intro k
    have h₁ : B k ∈ closure (next k).1.1 ∩ Γ'.V := by rw [hcapb]; simp
    rw [hcapa] at h₁
    rcases h₁ with h | h
    · exact h
    · exact (region_subset hr hc (Γ.V_subset_U (h ▸ hB k))).elim
  have hAc : ∀ k, A k ≠ c := fun k h => region_subset hr hc (Γ.V_subset_U (h ▸ hA k))
  have hBc : ∀ k, B k ≠ c := fun k h => region_subset hr hc (Γ.V_subset_U (h ▸ hB k))
  have hL : ∀ k : halfEdges (radialUnion hrad) γ c, IsLineWithEnds (closure k.1.1) (A k) c := fun k
    =>
    isLine_closure (hsp k) (hAc k) (hcapa k)
  have hLe : ∀ k, IsLineWithEnds (closure (E' k)) (A k) (B k) := fun k =>
    isLine_closure (hE' k) (hAB k) (hcap k)
  choose f hf0 hf1 using hL
  choose g hg0 hg1 using hLe
  let sp : halfEdges (radialUnion hrad) γ c → I → S := fun k t => (f k t).1
  let ε₀ : halfEdges (radialUnion hrad) γ c → I → S := fun k t => (g k t).1
  have hspC : ∀ k, Continuous (sp k) := fun k => continuous_subtype_val.comp (f k).continuous
  have hεc : ∀ k, Continuous (ε₀ k) := fun k => continuous_subtype_val.comp (g k).continuous
  have hspI : ∀ k, Function.Injective (sp k) := fun k x y h =>
    (f k).injective (Subtype.ext h)
  have hεi : ∀ k, Function.Injective (ε₀ k) := fun k x y h =>
    (g k).injective (Subtype.ext h)
  have hspR : ∀ k, range (sp k) = closure k.1.1 := fun k => range_homeomorph_subtype (f k)
  have hεr : ∀ k, range (ε₀ k) = closure (E' k) := fun k => range_homeomorph_subtype (g k)
  have hspZ : ∀ k, sp k 0 = A k := hf0
  have hspO : ∀ k, sp k 1 = c := hf1
  have hε0 : ∀ k, ε₀ k 0 = A k := hg0
  have hε1 : ∀ k, ε₀ k 1 = B k := hg1
  have hdisc := isClosedDisc_closure_corner hrad hS hmax hsph hE hloop hγ hr hc hcV hsec hρr
  have hsquare := corner_square_chart hrad hS hr hc hcV hγ hsec hE' hsp hAB hAc hBnext
    hcapa hcapb hfr hdisc f g hspC hεc hspI hεi hspR hεr hspZ hspO hε0 hε1
  choose G hGc hGb hGl hGr hGt hGi hGr' hGint using hsquare
  have hsubr : ∀ k : halfEdges (radialUnion hrad) γ c, k.1.1 ⊆ r := by
    intro k y hy
    obtain ⟨v', hv', r', hr', w, hwr, hwV, -, hsub⟩ := spoke_ends hrad hS (hsp k)
    have hkcl : k.1.1 ⊆ closure (ρ k) := by
      obtain ⟨l, hl⟩ := hsurj k
      have := IsCorners.right hcor l
      rwa [hl] at this
    obtain ⟨z, hz, hzp⟩ := mem_closure_iff.mp (hkcl hy) r' (region_isOpen hr') (hsub hy)
    obtain rfl := region_eq_of_mem hr' hr hz (hρr k hzp)
    exact hsub hy
  have hspIn : ∀ k (t : I), 0 < t → t < 1 → sp k t ∈ k.1.1 := by
    intro k t h₀ h₁
    have hm : sp k t ∈ closure k.1.1 := (f k t).2
    have hnV : sp k t ∉ Γ'.V := by
      intro hV
      have : sp k t ∈ closure k.1.1 ∩ Γ'.V := ⟨hm, hV⟩
      rw [hcapa] at this
      rcases this with h | h
      · exact h₀.ne ((hspI k (h.trans (hspZ k).symm)).symm)
      · exact h₁.ne (hspI k (h.trans (hspO k).symm))
    exact Γ'.closure_diff_V (hsp k) ▸ (⟨hm, hnV⟩ : sp k t ∈ closure k.1.1 \ Γ'.V)
  have hGin : ∀ k (p : I × I), 0 < p.1 → p.1 < 1 → 0 < p.2 → p.2 < 1 → G k p ∈ ρ k := by
    intro k p a₁ a₂ a₃ a₄
    have hmem : G k p ∈ closure (ρ k) := hGr' k ▸ mem_range_self p
    have := (hdisc k).2.1
    rw [← this]
    exact ⟨hmem, hGint k p a₁ a₂ a₃ a₄⟩
  -- The cyclic order.
  obtain ⟨k₀⟩ : Nonempty (halfEdges (radialUnion hrad) γ c) := by
    have := hub_two_halves hrad hS hmax hE hloop hγ hr hc hcV
    have hfin : Finite (halfEdges (radialUnion hrad) γ c) := (finite_halfEdges _ _ _).to_subtype
    exact (Finite.one_lt_card_iff_nontrivial.mp this).to_nonempty
  have hfin : Finite (halfEdges (radialUnion hrad) γ c) := (finite_halfEdges _ _ _).to_subtype
  have hinj : Function.Injective next := IsCorners.inj hcor
  have hper : k₀ ∈ Function.periodicPts next := hinj.mem_periodicPts k₀
  let n := Function.minimalPeriod next k₀
  have hn : 0 < n := Function.minimalPeriod_pos_of_mem_periodicPts hper
  let κ : ℕ → halfEdges (radialUnion hrad) γ c := fun i => next^[i] k₀
  have hκs : ∀ i, κ (i + 1) = next (κ i) := fun i => Function.iterate_succ_apply' next i k₀
  have hκn : ∀ i, κ (i + n) = κ i := fun i => by
    change next^[i + n] k₀ = next^[i] k₀
    rw [Function.iterate_add_apply, Function.iterate_minimalPeriod]
  have hκinj : ∀ i j, i < n → j < n → κ i = κ j → i = j := fun i j hi hj h =>
    Function.iterate_injOn_Iio_minimalPeriod hi hj h
  have hκall : ∀ k, ∃ i, i < n ∧ κ i = k := by
    intro k
    have hreach := IsCorners.reach hcor k₀ k
    have : ∃ m, next^[m] k₀ = k := by
      induction hreach with
      | refl => exact ⟨0, rfl⟩
      | tail _ h ih =>
        obtain ⟨m, hm⟩ := ih
        exact ⟨m + 1, by rw [Function.iterate_succ_apply', hm, h]⟩
    obtain ⟨m, hm⟩ := this
    refine ⟨m % n, Nat.mod_lt _ hn, ?_⟩
    rw [← hm]
    exact Function.iterate_mod_minimalPeriod_eq
  have hcoreq : ∀ k k', ρ k = ρ k' → k = k' := by
    intro k k' h
    by_contra hkk
    exact corner_regions_ne hrad hS hr hc hcV hsec hkk h
  have htwo : 2 ≤ n := by
    by_contra hlt
    have hn1 : n = 1 := by omega
    have h₁ : κ 1 = κ 0 := by simpa [hn1] using hκn 0
    rw [hκs] at h₁
    exact IsSectors.next_ne hsec _ h₁
  obtain ⟨H₀, hH₀⟩ := exists_cylinder hn (G := fun i => G (κ i)) (fun i => hGc _)
    (fun i t => by
      rw [hGr, hGl, hκs])
    (fun t => by
      have := hκn 0
      rw [zero_add] at this
      rw [this])
  -- Points of the cylinder at positive height.
  obtain ⟨hpos, hinjH, havoid⟩ :=
    cylinder_between_boundaries hrad hS hr hc hcV hγ hsp hR hρr hsubr hcoreq hspI hGi hGl
      hGin hspIn hn hκinj hH₀
  have hzpar : ∀ (z : Circle) (t : I), ∃ i, i < n ∧ ∃ u : I, H₀ (z, t) = G (κ i) (u, t) := by
    intro z t
    obtain ⟨i, hi, u, hu, rfl⟩ := exists_circle_param hn z
    exact ⟨i, hi, u, hH₀ i hi u t⟩
  have hHc : ∀ z, H₀ (z, 1) = c := by
    intro z
    obtain ⟨i, -, u, h⟩ := hzpar z 1
    rw [h, hGt]
    exact hspO _
  have hcover := corner_charts_cover_region hrad hS hr hc hcV hγ hcH hcor
    hA hE' hspR hspZ hspO hεr hGr' hGl hGb ⟨k₀⟩ hκall hH₀
  have hpos' : ∀ {p : Circle × I}, 0 < p.2 → H₀ p ∈ r := by
    rintro ⟨z, t⟩ h₀
    by_cases h₁ : t < 1
    · exact hpos h₀ h₁
    · have : t = 1 := le_antisymm (unitInterval.le_one t) (not_lt.mp h₁)
      subst this
      rw [hHc]
      exact hc
  have hbotU : ∀ z, H₀ (z, 0) ∉ r := by
    intro z hz
    obtain ⟨i, -, u, h⟩ := hzpar z 0
    rw [h, hGb] at hz
    exact region_subset hr hz (Γ.closure_subset_U (hE' _) (hεr _ ▸ mem_range_self _))
  have hfrontier := cylinder_bottom_eq_frontier (region_isOpen hr) H₀ hcover hpos' hbotU
  obtain ⟨hh, hhz, hhinj, hhmem, hhopen⟩ := half_height_collar H₀ hbotU hHc hpos' hinjH hcover
    havoid
  refine ⟨n, fun i => A (κ i), fun i => E' (κ i), fun i => (κ i).1.1, fun i => ρ (κ i),
    fun i => ε₀ (κ i), hh, ?_⟩
  refine ⟨htwo, fun i => by simp only [hκn], fun i => by simp only [hκn],
    fun i => by simp only [hκn],
    fun i => by simp only [hκn], fun i => by simp only [hκn], fun i => hE' _, fun i => hA _, ?_, ?_,
    fun i => hsp _, fun i => ⟨c, hc, hcapa _⟩, fun i => hR _, fun i => hρr _, fun i
      => hep _, ?_, ?_, ?_,
    fun i => hεc _, fun i => hεi _, fun i => hε0 _, ?_, fun i => hεr _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hcap, hBnext, hκs]
  · intro i
    rw [hκs, ← hBnext]
    exact hAB _
  · intro i
    obtain ⟨l, hl⟩ := hsurj (κ i)
    refine ⟨?_, ?_⟩
    · have := IsCorners.right hcor l
      rwa [hl] at this
    · rw [hκs]
      exact IsCorners.left hcor _
  · intro i j hi hj h
    exact hκinj i j hi hj (hcoreq _ _ h)
  · intro p hp hpr
    obtain ⟨k, rfl⟩ := IsCorners.all hcor p hp (hub_mem_closure hrad hS hr hp hpr hc hcV)
    obtain ⟨i, hi, rfl⟩ := hκall k
    exact ⟨i, hi, rfl⟩
  · intro i
    rw [hε1, hBnext, hκs]
  · intro i hi u
    rw [hhz, hH₀ i hi u 0, hGb]
  · exact hhinj
  · exact hhmem
  · rw [← hfrontier]
    congr 1
    funext z
    exact hhz z
  · exact hhopen

end GraphMinor.GM11
