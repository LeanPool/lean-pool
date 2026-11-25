/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10q

/-!
# A distance flaw gives outer data

This is the text of page 356 between "n-flawed in distance" and (10.4), written out from XI (9.2).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


namespace TangleDatum

variable {D : TangleDatum cap χ}

/-- A walk of length zero stays at its start. -/
theorem support_of_length_eq_zero {α β : Type*} {G : Graph α β} {a b : α} (R : GraphWalk G a b)
  (h : R.length = 0) : a = b ∧ ∀ x ∈ R.support, x = a := by
  cases R with
  | nil hv => exact ⟨rfl, by simp [GraphWalk.support]⟩
  | cons hl r => simp [GraphWalk.length] at h

/-- The edges of a walk are at most as many as its length. -/
theorem ncard_E_le_length {T : Type} [TopologicalSpace T] [T2Space T] (G : Drawing T) {u v : T}
  (W : GraphWalk G.toGraph u v) :
    (walkDrawing G W).E.ncard ≤ W.length := by
  classical
  rw [walkDrawing_E]
  have : {e | e ∈ W.edges} = ↑W.edges.toFinset := by
    ext e
    simp
  rw [this, ncard_coe_finset]
  exact List.toFinset_card_le _

/-- A simple walk from a vertex to itself has no edge. -/
theorem length_of_simple_self {α β : Type*} {G : Graph α β} {a : α} (R : GraphWalk G a a)
  (hR : R.IsSimple) : R.length = 0 := by
  cases R with
  | nil hv => rfl
  | cons hl r =>
    have h : (GraphWalk.cons hl r).support.Nodup := hR
    simp only [GraphWalk.support_cons, List.nodup_cons] at h
    exact (h.1 r.end_mem_support).elim

variable (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)
include hS h3

/-- A closed walk no longer than `2n` that has a vertex with label `Θ`, around a circuit with a pole
`r` inside, where `r` is not the pole of `Θ`. -/
theorem outer_of_touch [Nonempty S] {n : ℕ} (hn₁ : 1 ≤ n) (hn : n < D.rep) (hd :
  ((n + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad)
    (hNP : ¬ ∃ C, D.IsPairCircuit n C) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
      (hc : C.E.ncard ≤ 2 * n)
    (hlink : GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins C))
      (partIn cap D.P.Γ (closure (D.ins C)ᶜ)))
    {r p : Shat} (hr : r ∈ D.rad.poles) (hri : r ∈ D.ins C) (hp : p ∈ D.rad.poles)
      (hrp : r ≠ p) {Θ : Set S} (hΘ : Θ ∈ cuffs S)
    (hreg : D.rad.regionOf p = cap.cuffDisc Θ) {u₀ : Shat} (Z : GraphWalk D.rad.G.toGraph u₀ u₀)
      (hZ : Z.length ≤ 2 * n) (hpos : 0 < Z.length)
    (hZC : ∀ x ∈ C.V, x ∈ Z.support) {y : Shat} (hy : y ∈ Z.support) (hl : cuffLabel cap y
      = some Θ) : ∃ 𝓓 K, IsOuterData D n 𝓓 K := by
  have hlt : C.E.ncard < 2 * D.rep := by omega
  have hnp : ∀ z ∈ C.V, z ∉ D.rad.poles := fun z hz hzp ↦ by
    obtain ⟨Θ', hΘ', hreg', hzd⟩ := D.rad.pole_cases hzp
    have := labels_eq hS h3 hd Z hZ (hZC z hz) hy (cuffLabel_eq hΘ' (subset_closure hzd)) hl
    subst this
    obtain ⟨-, -, hG3, -⟩ := id D.rad.isPreRadial
    have m₁ := D.rad.regionOf_mem hzp.1
    have m₂ := D.rad.regionOf_mem hp.1
    have hzq : z = p := (hG3 _ m₁.1).unique ⟨m₁.2, hzp.1.1⟩ ⟨(hreg'.trans hreg.symm) ▸ m₂.2, hp.1.1⟩
    subst hzq
    exact hNP ⟨C, hC, hc, r, hr, z, hp, hrp, hri, D.U_subset_ins hC hlt (C.V_subset_U hz)⟩
  obtain ⟨v, -, hvΘ, hvZ⟩ := exists_touch Z hpos hy hl
  exact outer_of_disc_point hS h3 hn₁ hn hd hNP hC hc hlink hr hri hnp hp hrp hΘ hreg Z hZ hZC hvΘ
    hvZ

/-- A circuit with one pole inside and a walk from its inside to a second pole. -/
theorem outer_of_disc_pole [Nonempty S] {n : ℕ} (hn₁ : 1 ≤ n) (hn : n < D.rep) (hd :
  ((n + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad)
    (hNP : ¬ ∃ C, D.IsPairCircuit n C) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
    (hlink : GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins C))
      (partIn cap D.P.Γ (closure (D.ins C)ᶜ)))
    {r p a : Shat} (hr : r ∈ D.rad.poles) (hri : r ∈ D.ins C) (hp : p ∈ D.rad.poles) (hrp : r ≠ p)
      (ha : a ∈ D.ins C) (Q : GraphWalk D.rad.G.toGraph a p)
    (hlen : C.E.ncard + 2 * Q.length ≤ 2 * n) : ∃ 𝓓 K, IsOuterData D n 𝓓 K := by
  classical
  have hc : C.E.ncard ≤ 2 * n := by omega
  have hlt : C.E.ncard < 2 * D.rep := by omega
  have hpi : p ∉ D.ins C := fun h ↦ hNP ⟨C, hC, hc, r, hr, p, hp, hrp, hri, h⟩
  obtain ⟨a', ha', b', hb', T', hT'e, -, hA, -⟩ := exists_crossing (D.ins C) {p} Q ha rfl
  obtain rfl : b' = p := hb'
  obtain ⟨R, hRs, hRsupp, hRe⟩ := GraphWalk.exists_isSimple T'
  have hne : a' ≠ b' := fun h ↦ hpi (h ▸ ha')
  have hRA : ∀ x ∈ R.support, x ∈ D.ins C → x = a' := fun x hx ↦ hA x (hRsupp x hx)
  have ha'C : a' ∈ C.V := by
    obtain ⟨e, y, hl, hy, hya⟩ := walk_first_step R hRs hne
    exact D.exit_mem hC hlt hl ha' fun h ↦ hya (hRA y hy h)
  obtain ⟨Z₁, hl₁, hp₁, hZ₁⟩ := exists_circuit_walk hC ha'C
  have hRl : R.length ≤ Q.length := by
    have h₁ : R.length ≤ T'.length := length_le_of_edges hRs hRe
    have h₂ : T'.length ≤ Q.length := hT'e.length_le
    omega
  obtain ⟨Θ, hΘ, hreg, hrd⟩ := D.rad.pole_cases hp
  have hlab : cuffLabel cap b' = some Θ := cuffLabel_eq hΘ (subset_closure hrd)
  refine outer_of_touch hS h3 hn₁ hn hd hNP hC hc hlink hr hri hp hrp hΘ hreg (Z₁.append
    (R.append R.reverse)) ?_ ?_ ?_ (y := b') ?_ hlab
  · rw [GraphWalk.length_append, GraphWalk.length_append, GraphWalk.length_reverse]
    omega
  · rw [GraphWalk.length_append]
    omega
  · intro x hx
    refine (GraphWalk.mem_support_append _ _).mpr (Or.inl ?_)
    rwa [← hZ₁, walkDrawing_V] at hx
  · exact (GraphWalk.mem_support_append _ _).mpr (Or.inr ((GraphWalk.mem_support_append _ _).mpr
      (Or.inl R.end_mem_support)))

omit hS h3 in
omit [T2Space S] in
/-- Two circuits that meet in at most one vertex, and a walk between their insides, give a simple
walk between the circuits that meets each inside once. -/
theorem exists_join (_hrep : 1 ≤ D.rep) {C₁ C₂ : Drawing Shat} (hC₁ : C₁.IsCircuitOf D.rad.G)
  (hC₂ : C₂.IsCircuitOf D.rad.G) (hl₁ : C₁.E.ncard < 2 * D.rep)
    (hl₂ : C₂.E.ncard < 2 * D.rep) (hinter : D.ins C₁ ∩ D.ins C₂ ⊆ C₁.V ∩ C₂.V) (hone :
      (C₁.V ∩ C₂.V).Subsingleton) {a b : Shat} (ha : a ∈ D.ins C₁) (hb : b ∈ D.ins C₂)
    (Q : GraphWalk D.rad.G.toGraph a b) :
    ∃ (a' b' : Shat) (R : GraphWalk D.rad.G.toGraph a' b'), R.IsSimple ∧ a' ∈ C₁.V ∧ b' ∈ C₂.V
      ∧ R.length ≤ Q.length ∧ (∀ x ∈ R.support, x ∈ D.ins C₁ → x = a') ∧
      (∀ x ∈ R.support, x ∈ D.ins C₂ → x = b') ∧ (D.ins C₁ ∩ D.ins C₂ ⊆ {a'}) := by
  classical
  by_cases hw : (C₁.V ∩ C₂.V).Nonempty
  · obtain ⟨w, hw₁, hw₂⟩ := hw
    have hsub : D.ins C₁ ∩ D.ins C₂ ⊆ {w} := fun x hx ↦ hone (hinter hx) ⟨hw₁, hw₂⟩
    refine ⟨w, w, GraphWalk.nil (hC₁.1.1 hw₁), by simp [GraphWalk.IsSimple, GraphWalk.support],
      hw₁, hw₂, Nat.zero_le _, ?_, ?_, hsub⟩
    · simp [GraphWalk.support]
    · simp [GraphWalk.support]
  · have hemp : ∀ x, x ∈ D.ins C₁ → x ∈ D.ins C₂ → False := fun x h₁ h₂ ↦ hw ⟨x, hinter ⟨h₁, h₂⟩⟩
    obtain ⟨a', ha', b', hb', T', hT'e, -, hA, hB⟩ := exists_crossing (D.ins C₁) (D.ins C₂) Q ha hb
    obtain ⟨R, hRs, hRsupp, hRe⟩ := GraphWalk.exists_isSimple T'
    have hne : a' ≠ b' := fun h ↦ hemp a' ha' (h ▸ hb')
    have hRA : ∀ x ∈ R.support, x ∈ D.ins C₁ → x = a' := fun x hx ↦ hA x (hRsupp x hx)
    have hRB : ∀ x ∈ R.support, x ∈ D.ins C₂ → x = b' := fun x hx ↦ hB x (hRsupp x hx)
    have ha'C : a' ∈ C₁.V := by
      obtain ⟨e, y, hl, hy, hya⟩ := walk_first_step R hRs hne
      exact D.exit_mem hC₁ hl₁ hl ha' fun h ↦ hya (hRA y hy h)
    have hb'C : b' ∈ C₂.V := by
      obtain ⟨e, y, hl, hy, hya⟩ := walk_first_step R.reverse (by
        unfold GraphWalk.IsSimple
        rw [GraphWalk.support_reverse]
        exact List.nodup_reverse.2 hRs) hne.symm
      rw [GraphWalk.support_reverse] at hy
      exact D.exit_mem hC₂ hl₂ hl hb' fun h ↦ hya (hRB y (List.mem_reverse.1 hy) h)
    have hRl : R.length ≤ Q.length := by
      have h₁ : R.length ≤ T'.length := length_le_of_edges hRs hRe
      have h₂ : T'.length ≤ Q.length := hT'e.length_le
      omega
    exact ⟨a', b', R, hRs, ha'C, hb'C, hRl, hRA, hRB, fun x hx ↦ (hemp x hx.1 hx.2).elim⟩

/-- Two circuits, with a pole inside each, and a walk between their insides. -/
theorem outer_of_discs [Nonempty S] {n : ℕ} (hn₁ : 1 ≤ n) (hn : n < D.rep) (hd :
  ((n + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad)
    (hNP : ¬ ∃ C, D.IsPairCircuit n C) {C₁ C₂ : Drawing Shat} (hC₁ : C₁.IsCircuitOf D.rad.G)
      (hC₂ : C₂.IsCircuitOf D.rad.G)
    (hlink₁ : GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins C₁))
      (partIn cap D.P.Γ (closure (D.ins C₁)ᶜ)))
    (hlink₂ : GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins C₂))
      (partIn cap D.P.Γ (closure (D.ins C₂)ᶜ)))
    {r₁ r₂ a b : Shat} (hr₁ : r₁ ∈ D.rad.poles) (hr₂ : r₂ ∈ D.rad.poles) (hne : r₁ ≠ r₂)
      (hi₁ : r₁ ∈ D.ins C₁) (hi₂ : r₂ ∈ D.ins C₂)
    (ha : a ∈ D.ins C₁) (hb : b ∈ D.ins C₂) (Q : GraphWalk D.rad.G.toGraph a b)
      (hlen : C₁.E.ncard + C₂.E.ncard + 2 * Q.length ≤ 2 * n) :
    ∃ 𝓓 K, IsOuterData D n 𝓓 K := by
  classical
  have hrep : 1 ≤ D.rep := by omega
  have hc₁ : C₁.E.ncard ≤ 2 * n := by omega
  have hc₂ : C₂.E.ncard ≤ 2 * n := by omega
  have hlt₁ : C₁.E.ncard < 2 * D.rep := by omega
  have hlt₂ : C₂.E.ncard < 2 * D.rep := by omega
  have hi₁' : r₁ ∉ D.ins C₂ := fun h ↦ hNP ⟨C₂, hC₂, hc₂, r₁, hr₁, r₂, hr₂, hne, h, hi₂⟩
  have hi₂' : r₂ ∉ D.ins C₁ := fun h ↦ hNP ⟨C₁, hC₁, hc₁, r₁, hr₁, r₂, hr₂, hne, hi₁, h⟩
  have hone : (C₁.V ∩ C₂.V).Subsingleton := by
    intro x hx y hy
    by_contra hxy
    obtain ⟨C, hC, hc, h₁, h₂⟩ := no_two_common hn hC₁ hC₂ (by omega) hxy hx.1 hx.2 hy.1 hy.2
    exact hNP ⟨C, hC, hc, r₁, hr₁, r₂, hr₂, hne, h₁ hi₁, h₂ hi₂⟩
  have hinterV := ins_inter_ins hrep hC₁ hC₂ hlt₁ hlt₂ hone hi₁ hi₁' hi₂ hi₂'
  obtain ⟨a', b', R, hRs, ha'C, hb'C, hRl, hRA, hRB, hinter⟩ := exists_join hrep hC₁ hC₂ hlt₁ hlt₂
    hinterV hone ha hb Q
  obtain ⟨Z₁, hl₁, hp₁, hZ₁⟩ := exists_circuit_walk hC₁ ha'C
  obtain ⟨Z₂, hl₂, hp₂, hZ₂⟩ := exists_circuit_walk hC₂ hb'C
  set Z := Z₁.append (R.append (Z₂.append R.reverse)) with hZdef
  have hZl : Z.length = Z₁.length + (R.length + (Z₂.length + R.length)) := by
    simp only [hZdef, GraphWalk.length_append, GraphWalk.length_reverse]
  have hZle : Z.length ≤ 2 * n := by omega
  have hZpos : 0 < Z.length := by omega
  have hin₁ : ∀ x ∈ Z₁.support, x ∈ Z.support := fun x hx ↦ (GraphWalk.mem_support_append _ _).mpr
    (Or.inl hx)
  have hin₂ : ∀ x ∈ R.support, x ∈ Z.support := fun x hx ↦
    (GraphWalk.mem_support_append _ _).mpr (Or.inr ((GraphWalk.mem_support_append _ _).mpr
      (Or.inl hx)))
  have hin₃ : ∀ x ∈ Z₂.support, x ∈ Z.support := fun x hx ↦
    (GraphWalk.mem_support_append _ _).mpr (Or.inr ((GraphWalk.mem_support_append _ _).mpr (Or.inr
      ((GraphWalk.mem_support_append _ _).mpr (Or.inl hx)))))
  have hC₁Z : ∀ x ∈ C₁.V, x ∈ Z.support := fun x hx ↦ hin₁ x (by rwa [← hZ₁, walkDrawing_V] at hx)
  have hC₂Z : ∀ x ∈ C₂.V, x ∈ Z.support := fun x hx ↦ hin₃ x (by rwa [← hZ₂, walkDrawing_V] at hx)
  by_cases htouch : ∃ y Θ, y ∈ Z.support ∧ cuffLabel cap y = some Θ
  · obtain ⟨y, Θ, hy, hl⟩ := htouch
    have hΘ := (cuffLabel_some hl).1
    obtain ⟨p, hp, -, hreg⟩ := D.rad.exists_pole hΘ
    by_cases hrp : r₁ = p
    · have hrp₂ : r₂ ≠ p := fun h ↦ hne (hrp.trans h.symm)
      exact outer_of_touch hS h3 hn₁ hn hd hNP hC₂ hc₂ hlink₂ hr₂ hi₂ hp hrp₂ hΘ hreg Z hZle hZpos
        hC₂Z hy hl
    · exact outer_of_touch hS h3 hn₁ hn hd hNP hC₁ hc₁ hlink₁ hr₁ hi₁ hp hrp hΘ hreg Z hZle hZpos
        hC₁Z hy hl
  · push Not at htouch
    have hnl : ∀ {y}, y ∈ Z.support → ∀ Θ, cuffLabel cap y ≠ some Θ := fun {y} hy Θ ↦ htouch y Θ hy
    have hnp : ∀ {y}, y ∈ Z.support → y ∉ D.rad.poles := fun {y} hy hyp ↦ by
      obtain ⟨Θ, hΘ, -, hyd⟩ := D.rad.pole_cases hyp
      exact hnl hy Θ (cuffLabel_eq hΘ (subset_closure hyd))
    have hnp₁ : ∀ z ∈ C₁.V, z ∉ D.rad.poles := fun z hz ↦ hnp (hC₁Z z hz)
    have hnp₂ : ∀ z ∈ C₂.V, z ∉ D.rad.poles := fun z hz ↦ hnp (hC₂Z z hz)
    have hrange₁ := subset_range_of_no_pole D.rad hC₁.1 hnp₁
    have hrange₂ := subset_range_of_no_pole D.rad hC₂.1 hnp₂
    set R' := walkDrawing D.rad.G R with hR'
    have hR's : R'.IsSubdrawing D.rad.G := walkDrawing_isSubdrawing _ _
    have hR'V : ∀ {z}, z ∈ R'.V → z ∈ R.support := fun {z} hz ↦ by rwa [hR', walkDrawing_V] at hz
    have hR'r := subset_range_of_no_pole D.rad hR's fun z hz ↦ hnp (hin₂ z (hR'V hz))
    have hnoB : ∀ {X : Drawing Shat}, X.IsSubdrawing D.rad.G → (∀ z ∈ X.V, z ∈ Z.support)
      → ∀ {v : S}, v ∈ bd S → cap.emb v ∉ X.U := fun {X} hX hsup {v} hv hvX ↦ by
      obtain ⟨-, h₂, Θ', hΘ', hvΘ⟩ := D.rad.bd_point hX hv hvX
      exact hnl (hsup _ h₂) Θ' (cuffLabel_emb hΘ' hvΘ)
    have hone₁ : ∀ {x y : S}, x ∈ bd S → y ∈ bd S → cap.emb x ∈ C₁.U → cap.emb y ∈ C₁.U → x = y
      := fun hx _ hxC _ ↦ (hnoB hC₁.1 hC₁Z hx hxC).elim
    have hone₂ : ∀ {x y : S}, x ∈ bd S → y ∈ bd S → cap.emb x ∈ C₂.U → cap.emb y ∈ C₂.U → x = y
      := fun hx _ hxC _ ↦ (hnoB hC₂.1 hC₂Z hx hxC).elim
    obtain ⟨hO₁, a₁, b₁, hab₁, ha₁, hb₁⟩ := ring_marks hS h3 hC₁ hlt₁ hnp₁ hone₁ hr₁ hi₁
    obtain ⟨hO₂, a₂, b₂, hab₂, ha₂, hb₂⟩ := ring_marks hS h3 hC₂ hlt₂ hnp₂ hone₂ hr₂ hi₂
    obtain ⟨u, rfl⟩ := hrange₁ (C₁.V_subset_U ha'C)
    obtain ⟨w, rfl⟩ := hrange₂ (C₂.V_subset_U hb'C)
    have hR'L : cap.emb '' (cap.emb ⁻¹' R'.U) = R'.U := image_preimage_eq_of_subset hR'r
    have hj := cap.isClosedEmbedding hS
    have hmemU : ∀ {x}, x ∈ R'.U ↔ x ∈ {x | x ∈ R.support} ∪ ⋃ e ∈ {e | e ∈ R.edges}, closure e
      := fun {x} ↦ by
      rw [hR', mem_walkDrawing_U]
      simp
    have hL : (cap.emb ⁻¹' R'.U = {u} ∧ u = w) ∨ IsLineWithEnds (cap.emb ⁻¹' R'.U) u w := by
      by_cases hab : cap.emb u = cap.emb w
      · left
        have huw := cap.isEmbedding.injective hab
        subst huw
        have hzero : R.length = 0 := length_of_simple_self R hRs
        have hsup := (support_of_length_eq_zero R hzero).2
        have hed : R.edges = [] := List.length_eq_zero_iff.1 hzero
        refine ⟨?_, rfl⟩
        ext x
        simp only [mem_preimage, hmemU, hed, mem_singleton_iff]
        constructor
        · rintro (h | h)
          · exact cap.isEmbedding.injective (hsup _ h)
          · simp at h
        · rintro rfl
          exact Or.inl R.start_mem_support
      · right
        have hline : IsLineWithEnds (cap.emb '' (cap.emb ⁻¹' R'.U)) (cap.emb u) (cap.emb w) := by
          rw [hR'L]
          have := walk_isLine D.rad.G R hRs hab
          convert this using 1
          ext x
          exact hmemU
        exact isLine_comap hj hline
    have hPV : ((D.rad.G.sup C₁ C₂).V) = C₁.V ∪ C₂.V := Drawing.sup_V hC₁.1 hC₂.1
    have hPE : ((D.rad.G.sup C₁ C₂).E) = C₁.E ∪ C₂.E := Drawing.sup_E hC₁.1 hC₂.1
    have hPs := D.rad.G.sup_isSubdrawing C₁ C₂
    have hPPV : (D.rad.G.sup (D.rad.G.sup C₁ C₂) R').V = (C₁.V ∪ C₂.V) ∪ R'.V := by
      rw [Drawing.sup_V hPs hR's, hPV]
    have hPPE : (D.rad.G.sup (D.rad.G.sup C₁ C₂) R').E = (C₁.E ∪ C₂.E) ∪ R'.E := by
      rw [Drawing.sup_E hPs hR's, hPE]
    have hPU : (D.rad.G.sup (D.rad.G.sup C₁ C₂) R').U = C₁.U ∪ C₂.U ∪ R'.U := by
      rw [U_union (Drawing.sup_V hPs hR's) (Drawing.sup_E hPs hR's), U_union hPV hPE]
    have hu₁ : cap.emb u ∈ C₁.U := C₁.V_subset_U ha'C
    have hw₂ : cap.emb w ∈ C₂.U := C₂.V_subset_U hb'C
    refine outer_of_two hS h3 hn₁ hn hC₁ hC₂ hc₁ hc₂ hlink₁ hlink₂ hr₁ hr₂ hne hi₁ hi₂ hi₁' hrange₁
      hrange₂ hO₁ hab₁ ha₁ hb₁ hO₂ hab₂ ha₂ hb₂ hL
      (D.rad.G.sup_isSubdrawing (D.rad.G.sup C₁ C₂) R') ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hu₁ hw₂
    · rw [hPU]
      exact union_subset (union_subset hrange₁ hrange₂) hR'r
    · intro v hv
      rw [hPPV] at hv
      rcases hv with (hv | hv) | hv
      · obtain ⟨e, he, hve⟩ := circuit_iso hC₁.2 v hv
        exact ⟨e, by rw [hPPE]; exact Or.inl (Or.inl he), hve⟩
      · obtain ⟨e, he, hve⟩ := circuit_iso hC₂.2 v hv
        exact ⟨e, by rw [hPPE]; exact Or.inl (Or.inr he), hve⟩
      · rcases Nat.eq_zero_or_pos R.length with h0 | h0
        · obtain ⟨-, h₂⟩ := support_of_length_eq_zero R h0
          obtain ⟨e, he, hve⟩ := circuit_iso hC₁.2 _ ha'C
          exact ⟨e, by rw [hPPE]; exact Or.inl (Or.inl he), h₂ v (hR'V hv) ▸ hve⟩
        · obtain ⟨e, he, hve⟩ := exists_edge_at R h0 (hR'V hv)
          exact ⟨e, by rw [hPPE]; exact Or.inr (by rw [hR', walkDrawing_E]; exact he), hve⟩
    · rw [hPU, hR'L]
    · rw [hR'L]
      refine Subset.antisymm (fun x hx ↦ D.walk_inter_ins hC₁ hlt₁ hRs hRA hx.1 hx.2) ?_
      rintro _ rfl
      exact ⟨R'.V_subset_U (by rw [hR', walkDrawing_V]; exact R.start_mem_support), D.U_subset_ins
        hC₁ hlt₁ hu₁⟩
    · rw [hR'L]
      refine Subset.antisymm (fun x hx ↦ D.walk_inter_ins hC₂ hlt₂ hRs hRB hx.1 hx.2) ?_
      rintro _ rfl
      exact ⟨R'.V_subset_U (by rw [hR', walkDrawing_V]; exact R.end_mem_support), D.U_subset_ins
        hC₂ hlt₂ hw₂⟩
    · rw [disjoint_left]
      rintro _ ⟨v, hv, rfl⟩ hvP
      rw [hPU] at hvP
      rcases hvP with (h | h) | h
      · exact hnoB hC₁.1 hC₁Z hv h
      · exact hnoB hC₂.1 hC₂Z hv h
      · exact hnoB hR's (fun z hz ↦ hin₂ z (hR'V hz)) hv h
    · exact hinter
    · have h₁ := IsCircuit.ncard_V hC₁.2
      have h₂ := IsCircuit.ncard_V hC₂.2
      have h₃ : R'.V.ncard ≤ R.length + 1 := ncard_walk_V D.rad.G R
      have h₄ : R'.E.ncard = R.length := ncard_walk_E D.rad.G hRs
      have h₅ : (D.rad.G.sup (D.rad.G.sup C₁ C₂) R').V.ncard ≤ C₁.V.ncard + C₂.V.ncard + R'.V.ncard
        := by
        rw [hPPV]
        exact (ncard_union_le _ _).trans (by have := ncard_union_le C₁.V C₂.V; omega)
      have h₆ : (D.rad.G.sup (D.rad.G.sup C₁ C₂) R').E.ncard ≤ C₁.E.ncard + C₂.E.ncard + R'.E.ncard
        := by
        rw [hPPE]
        exact (ncard_union_le _ _).trans (by have := ncard_union_le C₁.E C₂.E; omega)
      omega

/-- What a piece gives at a pole `r` in it: the pole alone, or a linked circuit with `r` inside that
is no longer than `ℓ`. -/
def IsEnd (D : TangleDatum cap χ) (r : Shat) (A : Set Shat) (ℓ : ℕ) : Prop :=
  A = {r} ∨ ∃ C : Drawing Shat, C.IsCircuitOf D.rad.G ∧ C.E.ncard ≤ ℓ ∧ A = D.ins C ∧ r ∈ D.ins C ∧
    GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins C)) (partIn cap D.P.Γ
      (closure (D.ins C)ᶜ))

/-- Replace a piece by what it gives at a pole in it. When `r` is on the piece we move along its
walk to `r`, and otherwise the piece is a disc bounded by a circuit, which we make linked. -/
theorem end_of_piece {Y A : Set Shat} {G : Drawing Shat} (hP : IsPiece D.rad.G D.ins
  (2 * D.rep) Y A G) {r a b : Shat} (hr : r ∈ D.rad.poles) (hrA : r ∈ A)
    (Z : GraphWalk D.rad.G.toGraph a a) (hZ : walkDrawing D.rad.G Z = G) (ha : a ∈ G.V)
      (hlt : Z.length < 2 * D.rep) (Q : GraphWalk D.rad.G.toGraph a b) :
    ∃ (A' : Set Shat) (a' : Shat) (Q' : GraphWalk D.rad.G.toGraph a' b) (ℓ : ℕ), D.IsEnd r A' ℓ
      ∧ a' ∈ A' ∧ ℓ + 2 * Q'.length ≤ Z.length + 2 * Q.length := by
  have : ConnectedSpace Shat := cap.connected
  by_cases hrV : r ∈ G.V
  · have hrs : r ∈ Z.support := by rwa [← hZ, walkDrawing_V] at hrV
    obtain ⟨W, hW, -, -⟩ := exists_half_walk Z hrs Z.start_mem_support
    refine ⟨{r}, r, W.append Q, 0, Or.inl rfl, rfl, ?_⟩
    rw [GraphWalk.length_append]
    omega
  · rcases hP.kind with ⟨hc, rfl⟩ | ⟨e, u, v, -, -, hset, hV, -, rfl, -⟩ | ⟨v, hV, -, rfl, -⟩
    · have hC : G.IsCircuitOf D.rad.G := ⟨walkDrawing_isSubdrawing D.rad.G Z |> fun h ↦ hZ ▸ h, hc⟩
      have hGl : G.E.ncard ≤ Z.length := hZ ▸ ncard_E_le_length D.rad.G Z
      obtain ⟨C', hC', hle, -, hsub, hlink⟩ := exists_linked hS h3 hC (by omega)
      refine ⟨D.ins C', a, Q, Z.length, Or.inr ⟨C', hC', by omega, rfl, hsub hrA, hlink⟩,
        hsub (D.U_subset_ins hC (by omega) (G.V_subset_U ha)), le_rfl⟩
    · have : r ∈ closure e ∩ D.rad.G.V := ⟨hrA, hr.1.1⟩
      rw [hset, ← hV] at this
      exact (hrV this).elim
    · have : r = v := hrA
      exact (hrV (by rw [hV, this]; rfl)).elim

omit hS h3 in
omit [T2Space S] in
/-- No walk of length at most `n` joins two poles when `dist` is large. -/
theorem no_short_walk {n : ℕ} (hd : ((n + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad) {p q : Shat}
  (hp : p ∈ D.rad.poles) (hq : q ∈ D.rad.poles) (hne : p ≠ q)
    (W : GraphWalk D.rad.G.toGraph p q) (hW : W.length ≤ n) : False := by
  have h₁ := D.two_dist_le hp hq hne W
  have h₂ : (W.length : ℕ∞) ≤ ((n + 2 : ℕ) : ℕ∞) := by exact_mod_cast (by omega : W.length ≤ n + 2)
  exact absurd (h₁.trans h₂) (not_le.2 hd)

/-- The step of page 356: from a distance flaw with no short circuit around two poles, we get the
second or the third bullet. -/
theorem outer_of_flaw [Nonempty S] {n : ℕ} (hn₁ : 1 ≤ n) (hn : n < D.rep) (hd :
  ((n + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad)
    (hNP : ¬ ∃ C, D.IsPairCircuit n C) {r₁ r₂ : Shat} (h₁ : r₁ ∈ D.rad.poles)
      (h₂ : r₂ ∈ D.rad.poles) (hne : r₁ ≠ r₂) (hdist : D.vDist r₁ r₂ ≤ n) :
    ∃ 𝓓 K, IsOuterData D n 𝓓 K := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hrep : 1 ≤ D.rep := by omega
  have ha₁ : D.rad.atomOf r₁ = D.rad.regionOf r₁ := by
    classical
    unfold RadialDrawing.atomOf
    rw [ite_eq_right h₁.1.2]
  have ha₂ : D.rad.atomOf r₂ = D.rad.regionOf r₂ := by
    classical
    unfold RadialDrawing.atomOf
    rw [ite_eq_right h₂.1.2]
  have hreg : D.rad.regionOf r₁ ≠ D.rad.regionOf r₂ := fun heq ↦ by
    obtain ⟨-, -, hG3, -⟩ := id D.rad.isPreRadial
    have m₁ := D.rad.regionOf_mem h₁.1
    have m₂ := D.rad.regionOf_mem h₂.1
    exact hne ((hG3 _ m₁.1).unique ⟨m₁.2, h₁.1.1⟩ ⟨heq ▸ m₂.2, h₂.1.1⟩)
  have hv : D.vDist r₁ r₂ = D.dist (D.rad.regionOf r₁) (D.rad.regionOf r₂) := by
    rw [vDist, ha₁, ha₂]
  have hd' : D.dist (D.rad.regionOf r₁) (D.rad.regionOf r₂) < D.rep := by omega
  obtain ⟨T, hm₁, hm₂, hl⟩ := D.exists_of_dist_lt hreg hd'
  have hr₁ := D.center_mem_ins hrep h₁.1 T hm₁
  have hr₂ := D.center_mem_ins hrep h₂.1 T hm₂
  obtain ⟨hY, hlY⟩ := isRestraint_ins D hrep T
  have hA : ∀ {r : Shat}, r ∈ D.rad.poles → ({r} : Set Shat) ∈ D.rad.G.A := fun {r} hr ↦ Or.inl
    (Or.inl ⟨r, hr.1.1, rfl⟩)
  have hlen : perimeterWalkLength D.rad.G T.ins ≤ 2 * n := by omega
  rcases GM11.exists_pieces hT (D.isSlope hrep) (hA h₁) (hA h₂) hY (singleton_subset_iff.2 hr₁)
    (singleton_subset_iff.2 hr₂) with
    ⟨A, G, hP, ht₁, ht₂⟩ | ⟨A, G, B, H, hP, hP', ht₁, ht₂, -, a, b, Q, Z₁, Z₂, ha, hb, hZ₁, hZ₂,
      hl'⟩
  · exfalso
    have hA₁ : r₁ ∈ A := ht₁ rfl
    have hA₂ : r₂ ∈ A := ht₂ rfl
    obtain ⟨x, hx⟩ := hP.Vne
    obtain ⟨Z, hZ, hc⟩ := hP.walk x hx
    have hZl : Z.length ≤ 2 * n := (length_le_of_count hT hY (fun e he ↦ mem_E_of_mem_edges Z he)
      hc).trans hlen
    have hboth : ∀ {r : Shat}, r ∈ G.V → r ∈ Z.support := fun {r} hr ↦ by rwa [← hZ, walkDrawing_V]
      at hr
    have hclose : r₁ ∈ G.V → r₂ ∈ G.V → False := fun h h' ↦ by
      obtain ⟨W, hW, -, -⟩ := exists_half_walk Z (hboth h) (hboth h')
      exact no_short_walk hd h₁ h₂ hne W (by omega)
    rcases hP.kind with ⟨hc', rfl⟩ | ⟨e, u, v, -, -, hset, hV, -, rfl, -⟩ | ⟨v, hV, -, rfl, -⟩
    · have hC : GM19.Drawing.IsCircuitOf G D.rad.G := ⟨walkDrawing_isSubdrawing D.rad.G Z |> fun h
        ↦ hZ ▸ h, hc'⟩
      have hGl : G.E.ncard ≤ Z.length := hZ ▸ ncard_E_le_length D.rad.G Z
      exact hNP ⟨G, hC, by omega, r₁, h₁, r₂, h₂, hne, hA₁, hA₂⟩
    · have m₁ : r₁ ∈ closure e ∩ D.rad.G.V := ⟨hA₁, h₁.1.1⟩
      have m₂ : r₂ ∈ closure e ∩ D.rad.G.V := ⟨hA₂, h₂.1.1⟩
      rw [hset, ← hV] at m₁ m₂
      exact hclose m₁ m₂
    · exact hne (hA₁.trans hA₂.symm)
  · obtain ⟨A', a', Q', ℓ₁, hE₁, ha', hl₁⟩ := end_of_piece hS h3 hP h₁ (ht₁ rfl) Z₁ hZ₁ ha
      (by omega) Q
    obtain ⟨B', b', Q'', ℓ₂, hE₂, hb', hl₂⟩ := end_of_piece hS h3 hP' h₂ (ht₂ rfl) Z₂ hZ₂ hb
      (by omega) Q'.reverse
    rw [GraphWalk.length_reverse] at hl₂
    rcases hE₁ with rfl | ⟨C₁, hC₁, hc₁, rfl, hi₁, hlink₁⟩ <;> rcases hE₂ with rfl | ⟨C₂, hC₂, hc₂,
      rfl, hi₂, hlink₂⟩
    · obtain rfl : a' = r₁ := ha'
      obtain rfl : b' = r₂ := hb'
      exact (no_short_walk hd h₁ h₂ hne Q''.reverse (by rw [GraphWalk.length_reverse]; omega)).elim
    · obtain rfl : a' = r₁ := ha'
      exact outer_of_disc_pole hS h3 hn₁ hn hd hNP hC₂ hlink₂ h₂ hi₂ h₁ hne.symm hb' Q'' (by omega)
    · obtain rfl : b' = r₂ := hb'
      exact outer_of_disc_pole hS h3 hn₁ hn hd hNP hC₁ hlink₁ h₁ hi₁ h₂ hne ha' Q''.reverse
        (by rw [GraphWalk.length_reverse]; omega)
    · exact outer_of_discs hS h3 hn₁ hn hd hNP hC₁ hC₂ hlink₁ hlink₂ h₁ h₂ hne hi₁ hi₂ ha' hb'
        Q''.reverse (by rw [GraphWalk.length_reverse]; omega)

end TangleDatum

end GraphMinor.GM19
