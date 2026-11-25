/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section11c

/-!
# Graph Minors XIX, (11.3) and (11.4)

A feast of least order is disjoint, and if it also has least weight then its members are `λ`-linked
to the tangle. We prove both for feasts whose members all have `½|E(F)| ≤ c`, with
`c + 1` at least the bound on the order. The numbered results take `c` to be the bound. The proof of
(11.1) needs `c` one smaller, so that the separations made from the bites
have order less than the bound (`exists_side_flaw`). A single bite of length exactly `2(m + 1)n`
would break this, and the paper does not say why it does not arise.

Instead of the planar graph in the paper's proof of (11.3), we change the feast one or two members
at a time, using `Section11c.lean`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


namespace TangleDatum

variable {D : TangleDatum cap χ}

omit [T2Space S] in
/-- A short circuit with its inside linked to the tangle is `λ`-linked in the sense of the paper. -/
theorem isLambdaLinkedCircuit_of_ins {F : Drawing Shat} (hF : F.IsCircuitOf D.rad.G)
  (hlt : F.E.ncard < 2 * D.rep)
    (hl : GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins F)) (partIn cap D.P.Γ
      (closure (D.ins F)ᶜ))) : IsLambdaLinkedCircuit D.tb D.ord D.𝒯 F := by
  have h₁ : D.rep ≤ D.ord := (tangleRep_spec D.rad D.ord D.𝒯).1
  have h₂ : (D.rep : ℕ∞) ≤ Painting.rep D.rad := tangleRep_le_rep D.rad D.ord D.𝒯
  have h₃ : (D.rep : ℕ∞) ≤ min (D.ord : ℕ∞) (Painting.rep D.rad) := le_min (by exact_mod_cast h₁) h₂
  have h₄ : (F.E.ncard : ℕ∞) < 2 * (D.rep : ℕ∞) := by exact_mod_cast hlt
  exact ⟨hF, lt_of_lt_of_le h₄ (by gcongr), _, _, D.sides_ins hF hlt, hl⟩

omit [T2Space S] [T2Space Shat] in
/-- A member of a family of order at most `N` has at most `2N` edges. -/
theorem ncard_E_le_of_mem {ℱ : Set (Drawing Shat)} (hf : ℱ.Finite) (hc : ∀ F ∈ ℱ, F.IsCircuitOf
  D.rad.G) {N : ℕ} (hord : feastOrder ℱ ≤ N) {F : Drawing Shat} (hF : F ∈ ℱ) :
    F.E.ncard ≤ 2 * N := by
  have : ConnectedSpace Shat := cap.connected
  have h := feastOrder_diff_singleton hf hF
  have h' := D.ncard_E_eq_hat (hc F hF)
  omega

namespace IsSideSetting

variable {side Θ : Set S} {r : Shat} {N : ℕ} (X : D.IsSideSetting side Θ r N)
include X

omit [T2Space S] in
/-- The frontier of the region of `r` is the cuff. -/
theorem frontier_region : closure (D.rad.regionOf r) \ D.rad.regionOf r
  = cap.emb '' Θ := by
  rw [X.reg, cap.closure_cuffDisc X.cuff]
  ext x
  constructor
  · rintro ⟨hx | hx, hn⟩
    · exact absurd hx hn
    · exact hx
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Or.inr (mem_image_of_mem _ hy), fun hd ↦ cap.notMem_range X.cuff hd (mem_range_self y)⟩

/-- **A feast of least order is disjoint.** -/
theorem isDisjointFeast_of_min (hS : IsSurface S) {ω : List β} {ℱ : Set (Drawing Shat)} {c : ℕ}
  (hNc : N ≤ c + 1) (hfe : D.IsFeast r side ω ℱ) (hord : feastOrder ℱ ≤ N)
    (hsm : ∀ F ∈ ℱ, F.E.ncard ≤ 2 * c) (hmin : ∀ ℱ', D.IsFeast r side ω ℱ' → (∀ F ∈ ℱ', F.E.ncard
      ≤ 2 * c) → feastOrder ℱ ≤ feastOrder ℱ') : D.IsDisjointFeast r side ω ℱ := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hf := hfe.finite_bites
  have hsN : ∀ {F}, F ∈ ℱ → F.E.ncard ≤ 2 * N := fun hF ↦ ncard_E_le_of_mem hf (fun F hF ↦
    (hfe.all_bites F hF).is_circuit) hord hF
  have hone : ∀ {F₁ F₂}, F₁ ∈ ℱ → F₂ ∈ ℱ → F₁ ≠ F₂ → (F₁.V ∩ F₂.V).Subsingleton := by
    rintro F₁ F₂ h₁ h₂ hne x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩
    by_contra hxy
    obtain ⟨ℱ', h₃, h₄, h₅⟩ := X.exists_merge hS hNc hfe hord hsm h₁ h₂ hne hxy hx₁ hx₂ hy₁ hy₂
    have := hmin ℱ' h₃ h₅
    omega
  have hnotsub : ∀ {F₁ F₂}, F₁ ∈ ℱ → F₂ ∈ ℱ → F₁ ≠ F₂ → ¬ D.ins F₁ ⊆ D.ins F₂ := by
    intro F₁ F₂ h₁ h₂ hne hsub
    obtain ⟨ℱ', h₃, h₄, h₅⟩ := X.exists_drop hS hfe hord h₁ h₂ hne hsub
    have := hmin ℱ' h₄ fun F hF ↦ hsm F (h₃ hF)
    omega
  have hrep1 : 1 ≤ D.rep := by have := X.rep_gt; omega
  refine ⟨hfe, fun F hF ↦ ?_, fun F hF F' hF' hne ↦ ?_⟩
  · have hb := hfe.all_bites F hF
    obtain ⟨v₁, v₂, Β, L, A, A', Di, Do, hsh⟩ := X.shape hS hb (hsN hF)
    rw [X.frontier_region]
    refine Subset.antisymm (hsh.biteArc_subset) fun x hx ↦ ?_
    rcases hsh.mem_biteArc_or hx.2 hx.1 with h' | ⟨hxV, hxA⟩
    · exact h'
    exfalso
    obtain ⟨F', hF', hlt, hsub, hrF⟩ := X.exists_shorter hS hsh hxV hxA
    have hc' : F'.E.ncard ≤ 2 * N := by have := hsN hF; omega
    have hb' : D.IsBiteAt r F' := ⟨X.pole, hF', by have := X.rep_gt; omega, hrF⟩
    have e₁ := feastOrder_diff_singleton hf hF
    have e₂ := feastOrder_insert_le (hf.subset (sdiff_subset (t := {F}))) F'
    have k₁ := D.ncard_E_eq_hat hb.is_circuit
    have k₂ := D.ncard_E_eq_hat hF'
    have hmn := hmin (insert F' (ℱ \ {F})) (hfe.of_arc_subset ((hf.subset sdiff_subset).insert F')
      ?_ ?_ ?_) ?_
    · omega
    · rintro G (rfl | hG)
      · exact hb'
      · exact hfe.all_bites G hG.1
    · have h₁ := ncard_insert_le F' (ℱ \ {F})
      have h₂ := ncard_sdiff_singleton_add_one hF hf
      have := hfe.card_le
      omega
    · intro z hz
      obtain ⟨G, hG, hzG⟩ := mem_iUnion₂.1 hz
      by_cases e : G = F
      · subst e
        exact mem_iUnion₂.2 ⟨F', mem_insert _ _, X.biteArc_subset_of_ins hS hb hb'
          (hsN hF) hc' hsub hzG⟩
      · exact mem_iUnion₂.2 ⟨G, mem_insert_of_mem _ ⟨hG, e⟩, hzG⟩
    · rintro G (rfl | hG)
      · have := hsm F hF
        omega
      · exact hsm G hG.1
  · have b₁ := hfe.all_bites F hF
    have b₂ := hfe.all_bites F' hF'
    obtain ⟨a, ha₁, ha₂⟩ := not_subset.1 (hnotsub hF hF' hne)
    obtain ⟨b, hb₁, hb₂⟩ := not_subset.1 (hnotsub hF' hF hne.symm)
    have hsub := ins_inter_ins hrep1 b₁.is_circuit b₂.is_circuit b₁.card_lt b₂.card_lt
      (hone hF hF' hne) ha₁ ha₂ hb₁ hb₂
    refine Subset.antisymm (fun x hx ↦ ?_) ?_
    · exact (hone hF hF' hne) (hsub hx) ⟨b₁.rstar_mem, b₂.rstar_mem⟩
    · rintro x hx
      rw [mem_singleton_iff.1 hx]
      exact ⟨D.U_subset_ins b₁.is_circuit b₁.card_lt (F.V_subset_U b₁.rstar_mem),
        D.U_subset_ins b₂.is_circuit b₂.card_lt (F'.V_subset_U b₂.rstar_mem)⟩

omit X in
omit [T2Space S] [T2Space Shat] in
/-- Two circuits of the same length with the same weight are equal, as the weights are rationally
independent. -/
theorem eq_of_weight_eq (F F' : Drawing Shat) (hF : F.IsCircuitOf D.rad.G)
  (hF' : F'.IsCircuitOf D.rad.G) (hcard : F'.E.ncard = F.E.ncard) (hw : D.tb.weightSub F'
    = D.tb.weightSub F) :
    F' = F := by
  have : ConnectedSpace Shat := cap.connected
  have hEE : F'.E = F.E := by
    by_contra hne
    have hdiff : (F.E \ F'.E).Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hemp
      exact hne (eq_of_subset_of_ncard_le hemp hcard.le F'.finite_edges).symm
    have hX : F'.E \ F.E ⊆ D.rad.G.E := fun e he ↦ hF'.1.2 he.1
    have hY : F.E \ F'.E ⊆ D.rad.G.E := fun e he ↦ hF.1.2 he.1
    have hd : Disjoint (F'.E \ F.E) (F.E \ F'.E) := disjoint_left.mpr fun e h₁ h₂ ↦ h₁.2 h₂.1
    refine D.tb.weight_ne hX hY hd hdiff ?_
    have split : ∀ {s t : Set (Set Shat)}, s.Finite → ∑ᶠ e ∈ s, D.tb.wtE e =
        ∑ᶠ e ∈ s ∩ t, D.tb.wtE e + ∑ᶠ e ∈ s \ t, D.tb.wtE e := by
      intro s t hs
      have hd : Disjoint (s ∩ t) (s \ t) := disjoint_left.mpr fun _ h₁ h₂ ↦ h₂.2 h₁.2
      rw [← finsum_mem_union hd (hs.inter_of_left _) hs.sdiff, inter_union_sdiff]
    have e₁ := split (s := F'.E) (t := F.E) F'.finite_edges
    have e₂ := split (s := F.E) (t := F'.E) F.finite_edges
    rw [Set.inter_comm] at e₂
    simp only [TieBreaker.weightSub] at hw
    linarith
  have hUU : F'.U = F.U := by
    have key : ∀ {A B : Drawing Shat}, A.IsCircuit → A.E = B.E → A.U ⊆ B.U := by
      intro A B hA hE
      exact U_of_edges hA B.isClosed_U fun e he ↦ (subset_closure.trans (B.closure_subset_U
        (hE ▸ he)))
    exact Subset.antisymm (key hF'.2 hEE) (key hF.2 hEE.symm)
  refine Drawing.ext_of_V_E ?_ hEE
  ext x
  exact ⟨fun hx ↦ mem_V_of_mem_U hF.1 (hUU ▸ F'.V_subset_U hx) (hF'.1.1 hx),
    fun hx ↦ mem_V_of_mem_U hF'.1 (hUU ▸ F.V_subset_U hx) (hF.1.1 hx)⟩

/-- **A feast of least order and then least weight has all its members linked to the tangle.** -/
theorem linked_of_min (hS : IsSurface S) {ω : List β} {ℱ : Set (Drawing Shat)} {c : ℕ}
  (hfe : D.IsFeast r side ω ℱ) (hord : feastOrder ℱ ≤ N)
    (hsm : ∀ F ∈ ℱ, F.E.ncard ≤ 2 * c) (hmin : ∀ ℱ', D.IsFeast r side ω ℱ' → (∀ F ∈ ℱ', F.E.ncard
      ≤ 2 * c) → feastOrder ℱ ≤ feastOrder ℱ')
    (hw : ∀ ℱ', D.IsFeast r side ω ℱ' → (∀ F ∈ ℱ', F.E.ncard ≤ 2 * c) → feastOrder ℱ'
      = feastOrder ℱ → D.feastWeight ℱ ≤ D.feastWeight ℱ') {F : Drawing Shat} (hF : F ∈ ℱ) :
    GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins F)) (partIn cap D.P.Γ
      (closure (D.ins F)ᶜ)) := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hf := hfe.finite_bites
  have hsN : F.E.ncard ≤ 2 * N := ncard_E_le_of_mem hf (fun F hF ↦ (hfe.all_bites F hF).is_circuit)
    hord hF
  have hb := hfe.all_bites F hF
  obtain ⟨F', hF', hle, heq, hsub, hlink⟩ := exists_linked hS X.h3 hb.is_circuit hb.card_lt
  have hc' : F'.E.ncard ≤ 2 * N := by omega
  have hb' : D.IsBiteAt r F' := X.bite_of_ins hF' hc' (hsub (D.U_subset_ins hb.is_circuit
    hb.card_lt (F.V_subset_U hb.rstar_mem)))
  have hfA : (ℱ \ {F}).Finite := hf.subset sdiff_subset
  have e₁ := feastOrder_diff_singleton hf hF
  have e₂ := feastOrder_insert_le hfA F'
  have k₁ := D.ncard_E_eq_hat hb.is_circuit
  have k₂ := D.ncard_E_eq_hat hF'
  have hfe' : D.IsFeast r side ω (insert F' (ℱ \ {F})) := by
    refine hfe.of_arc_subset (hfA.insert F') ?_ ?_ ?_
    · rintro G (rfl | hG)
      · exact hb'
      · exact hfe.all_bites G hG.1
    · have h₁ := ncard_insert_le F' (ℱ \ {F})
      have h₂ := ncard_sdiff_singleton_add_one hF hf
      have := hfe.card_le
      omega
    · intro z hz
      obtain ⟨G, hG, hzG⟩ := mem_iUnion₂.1 hz
      by_cases e : G = F
      · subst e
        exact mem_iUnion₂.2 ⟨F', mem_insert _ _, X.biteArc_subset_of_ins hS hb hb' hsN hc' hsub hzG⟩
      · exact mem_iUnion₂.2 ⟨G, mem_insert_of_mem _ ⟨hG, e⟩, hzG⟩
  have hsm' : ∀ G ∈ insert F' (ℱ \ {F}), G.E.ncard ≤ 2 * c := by
    rintro G (rfl | hG)
    · have := hsm F hF
      omega
    · exact hsm G hG.1
  have hm₁ := hmin _ hfe' hsm'
  have hcard : F'.E.ncard = F.E.ncard := by
    by_contra hne
    omega
  have hnot : F' ∉ ℱ \ {F} := by
    intro hm
    have : insert F' (ℱ \ {F}) = ℱ \ {F} := insert_eq_of_mem hm
    rw [this] at hm₁
    have hpos : 0 < F.E.ncard := (ncard_pos F.finite_edges).2 (IsCircuit.E_nonempty hb.is_circuit.2)
    omega
  have hm₂ := hw _ hfe' hsm' (by omega)
  rw [feastWeight_insert hfA hnot, ← feastWeight_diff_singleton (D := D) hf hF] at hm₂
  have hw₁ := heq hcard
  have hEq : F' = F := eq_of_weight_eq F F' hb.is_circuit hF' hcard (le_antisymm hw₁ (by linarith))
  rw [hEq] at hlink
  exact hlink

omit [T2Space S] X in
omit [T2Space Shat] in
/-- The finitely many feasts have one of least order and then least weight, if there is a feast at
all. -/
theorem exists_min_feast {ω : List β} {c : ℕ} {ℱ₀ : Set (Drawing Shat)}
  (hfe : D.IsFeast r side ω ℱ₀) (hsm : ∀ F ∈ ℱ₀, F.E.ncard ≤ 2 * c) :
    ∃ ℱ, D.IsFeast r side ω ℱ ∧ (∀ F ∈ ℱ, F.E.ncard ≤ 2 * c) ∧ feastOrder ℱ ≤ feastOrder ℱ₀ ∧
      (∀ ℱ', D.IsFeast r side ω ℱ' → (∀ F ∈ ℱ', F.E.ncard ≤ 2 * c) → feastOrder ℱ ≤ feastOrder ℱ') ∧
      ∀ ℱ', D.IsFeast r side ω ℱ' → (∀ F ∈ ℱ', F.E.ncard ≤ 2 * c) → feastOrder ℱ' = feastOrder ℱ
        → D.feastWeight ℱ ≤ D.feastWeight ℱ' := by
  classical
  let 𝒳 : Set (Set (Drawing Shat)) := {ℱ | D.IsFeast r side ω ℱ ∧ ∀ F ∈ ℱ, F.E.ncard ≤ 2 * c}
  have hfin : 𝒳.Finite := by
    refine (finite_circuits D.rad.G).finite_subsets.subset fun ℱ hℱ F hF ↦ ?_
    have := (hℱ.1.all_bites F hF).is_circuit
    exact ⟨this.2, this.1⟩
  have hne : 𝒳.Nonempty := ⟨ℱ₀, hfe, hsm⟩
  obtain ⟨ℱ, hℱ, hm⟩ := exists_min_image 𝒳 (fun ℱ ↦ toLex (feastOrder ℱ, D.feastWeight ℱ)) hfin hne
  refine ⟨ℱ, hℱ.1, hℱ.2, ?_, fun ℱ' h₁ h₂ ↦ ?_, fun ℱ' h₁ h₂ h₃ ↦ ?_⟩
  · have := hm ℱ₀ ⟨hfe, hsm⟩
    rw [Prod.Lex.toLex_le_toLex] at this
    rcases this with h | h
    · exact h.le
    · exact h.1.le
  · have := hm ℱ' ⟨h₁, h₂⟩
    rw [Prod.Lex.toLex_le_toLex] at this
    rcases this with h | h
    · exact h.le
    · exact h.1.le
  · have := hm ℱ' ⟨h₁, h₂⟩
    rw [Prod.Lex.toLex_le_toLex] at this
    rcases this with h | h
    · exact absurd h (by simp only [h₃, lt_irrefl, not_false_eq_true])
    · exact h.2

end IsSideSetting

variable (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)
include hS h3

omit [T2Space S] hS in
/-- What it means to be flawed on a side, read at the pole of the cuff of the side. -/
theorem isSideSetting_of_flawed {side : Set S} (hside : side ∈ χ.Φ.longSides) {n : ℕ} {ω : List β}
  (hω : ω ≠ []) (hfl : D.IsFlawedOnSide side n ω) {Θ : Set S} {r : Shat}
    (hsΘ : side ⊆ Θ) (hΘ : Θ ∈ cuffs S) (hr : r ∈ D.rad.poles) (hreg : D.rad.regionOf r
      = cap.cuffDisc Θ) : D.IsSideSetting side Θ r ((ω.length + 1) * n) := by
  obtain ⟨hrep, hdist, hnd, hnf, -⟩ := hfl
  have hm1 : 1 ≤ ω.length := List.length_pos_iff.2 hω
  have hrepN : (ω.length + 1) * n < D.rep := by nlinarith
  have hd : ∀ r₁ ∈ D.rad.poles, ∀ r₂ ∈ D.rad.poles, r₁ ≠ r₂ → (ω.length + 1) * n < D.vDist r₁ r₂
    := by
    intro r₁ h₁ r₂ h₂ hne
    by_contra hle
    exact hnd ⟨hrepN, hdist, r₁, h₁, r₂, h₂, hne, not_lt.1 hle⟩
  exact ⟨h3, hside, hsΘ, hΘ, hr, hreg, hrepN, hd, fun C hC ↦ hnf ⟨hrepN, hd, C, hC⟩⟩

/-- **Graph Minors XIX, (11.3)** (page 360): "Every feast of minimum order with order $\le (m + 1)n$
is disjoint." -/
theorem theorem_11_3_proof {side : Set S} (hside : side ∈ χ.Φ.longSides) {n : ℕ} (_ : 4
  ≤ n) {ω : List β} (hω : ω ≠ []) (hfl : D.IsFlawedOnSide side n ω) {Θ : Set S} {r : Shat}
    (hsΘ : side ⊆ Θ) (hΘ : Θ ∈ cuffs S) (hr : r ∈ D.rad.poles) (hreg : D.rad.regionOf r
      = cap.cuffDisc Θ) {ℱ : Set (Drawing Shat)} (hfe : D.IsFeast r side ω ℱ)
    (hord : feastOrder ℱ ≤ (ω.length + 1) * n) (hmin : ∀ ℱ', D.IsFeast r side ω ℱ' → feastOrder ℱ
      ≤ feastOrder ℱ') : D.IsDisjointFeast r side ω ℱ := by
  have X := isSideSetting_of_flawed h3 hside hω hfl hsΘ hΘ hr hreg
  exact X.isDisjointFeast_of_min hS (c := (ω.length + 1) * n) (by omega) hfe hord
    (fun F hF ↦ ncard_E_le_of_mem hfe.finite_bites (fun F hF ↦ (hfe.all_bites F hF).is_circuit)
      hord hF) fun ℱ' h _ ↦ hmin ℱ' h

/-- **Graph Minors XIX, (11.4)** (page 361): "Let $\mathcal{F}$ be a feast of minimum order $\le
(m+1)n$ and subject to that with
$\Sigma(\lambda(F) : F \in \mathcal{F})$ minimum. Then each $F \in \mathcal{F}$ is
$\lambda$-linked to $\mathcal{T}$." -/
theorem theorem_11_4_proof {side : Set S} (hside : side ∈ χ.Φ.longSides) {n : ℕ} (_ : 4
  ≤ n) {ω : List β} (hω : ω ≠ []) (hfl : D.IsFlawedOnSide side n ω) {Θ : Set S} {r : Shat}
    (hsΘ : side ⊆ Θ) (hΘ : Θ ∈ cuffs S) (hr : r ∈ D.rad.poles) (hreg : D.rad.regionOf r
      = cap.cuffDisc Θ) {ℱ : Set (Drawing Shat)} (hfe : D.IsFeast r side ω ℱ)
    (hord : feastOrder ℱ ≤ (ω.length + 1) * n) (hmin : ∀ ℱ', D.IsFeast r side ω ℱ' → feastOrder ℱ
      ≤ feastOrder ℱ')
    (hw : ∀ ℱ', D.IsFeast r side ω ℱ' → feastOrder ℱ' = feastOrder ℱ → D.feastWeight ℱ
      ≤ D.feastWeight ℱ') {F : Drawing Shat} (hF : F ∈ ℱ) :
    IsLambdaLinkedCircuit D.tb D.ord D.𝒯 F := by
  have X := isSideSetting_of_flawed h3 hside hω hfl hsΘ hΘ hr hreg
  have hl := X.linked_of_min hS (c := (ω.length + 1) * n) hfe hord (fun F hF ↦ ncard_E_le_of_mem
    hfe.finite_bites (fun F hF ↦ (hfe.all_bites F hF).is_circuit) hord hF)
    (fun ℱ' h _ ↦ hmin ℱ' h) (fun ℱ' h _ h' ↦ hw ℱ' h h') hF
  exact isLambdaLinkedCircuit_of_ins (hfe.all_bites F hF).is_circuit (hfe.all_bites F hF).card_lt hl

/-- **The flaw of a side**, as the paper uses it in the proof of (11.1). The members have `½|E(F)| <
(m + 1)n`, and removing a member leaves no feast. -/
theorem exists_side_flaw {side : Set S} (hside : side ∈ χ.Φ.longSides) {n : ℕ} (hn : 4
  ≤ n) {ω : List β} (hω : ω ≠ []) (hfl : D.IsFlawedOnSide side n ω) :
    ∃ (r : Shat) (Θ : Set S) (ℱ : Set (Drawing Shat)), D.IsSideSetting side Θ r
      ((ω.length + 1) * n) ∧ D.IsSideLabelFlaw r side n ω ℱ ∧
      (∀ F ∈ ℱ, F.E.ncard ≤ 2 * ((ω.length + 1) * n - 1)) ∧
      (∀ F ∈ ℱ, GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins F))
        (partIn cap D.P.Γ (closure (D.ins F)ᶜ))) ∧
      ∀ F ∈ ℱ, ¬ D.IsFeast r side ω (ℱ \ {F}) := by
  obtain ⟨r, Θ, hΘ, hsΘ, hr, hreg, ℱ₀, hf₀, ho₀, hs₀⟩ := theorem_11_2_proof hS h3 hside hn hω hfl
  have X := isSideSetting_of_flawed h3 hside hω hfl hsΘ hΘ hr hreg
  have hm1 : 1 ≤ ω.length := List.length_pos_iff.2 hω
  set N := (ω.length + 1) * n with hN
  have h2n : 2 * n ≤ N := by rw [hN]; nlinarith
  have hsm₀ : ∀ F ∈ ℱ₀, F.E.ncard ≤ 2 * (N - 1) := fun F hF ↦ by have := hs₀ F hF; omega
  obtain ⟨ℱ, hfe, hsm, hle, hmin, hw⟩ := IsSideSetting.exists_min_feast hf₀ hsm₀
  have hord : feastOrder ℱ ≤ N := hle.trans ho₀
  have hNc : N ≤ N - 1 + 1 := by omega
  have hdis := X.isDisjointFeast_of_min hS hNc hfe hord hsm hmin
  have hlink := fun F hF ↦ X.linked_of_min hS (c := N - 1) hfe hord hsm hmin hw (F := F) hF
  refine ⟨r, Θ, ℱ, X, ⟨hdis, hord, fun F hF ↦ isLambdaLinkedCircuit_of_ins
    (hfe.all_bites F hF).is_circuit (hfe.all_bites F hF).card_lt (hlink F hF)⟩, hsm, hlink, fun F
      hF h ↦ ?_⟩
  have := hmin _ h fun G hG ↦ hsm G hG.1
  have e := feastOrder_diff_singleton hfe.finite_bites hF
  have : ConnectedSpace Shat := cap.connected
  have hb := hfe.all_bites F hF
  have k := D.ncard_E_eq_hat hb.is_circuit
  have hpos : 0 < F.E.ncard := (ncard_pos F.finite_edges).2 (IsCircuit.E_nonempty hb.is_circuit.2)
  omega

end TangleDatum

end GraphMinor.GM19
