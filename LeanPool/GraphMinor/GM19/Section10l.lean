/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10k

/-!
# Short circuits around two poles

The first steps from a tie to a distance flaw. A circuit of the first bullet of page 355 is chosen
with `λ(F)` minimal, and
then the argument of (10.1) applies. The paper says only "it follows from Theorem 9.2 of [6]".
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


namespace TangleDatum

variable {D : TangleDatum cap χ} {F F₁ F₂ Q : Drawing Shat} {a b : Shat}

omit [T2Space S] in
/-- A circuit made of `Q` and one path of `F` is no longer than `F`. -/
theorem improve_card (ht : TwoPaths D.rad.G F F₁ F₂ Q a b) (hc : Q.E.ncard ≤ F₁.E.ncard) :
    (D.rad.G.sup Q F₂).E.ncard ≤ F.E.ncard := by
  have : ConnectedSpace Shat := cap.connected
  have hE : (D.rad.G.sup Q F₂).E = Q.E ∪ F₂.E := Drawing.sup_E ht.path.1 ht.sub₂
  have hdis : Disjoint Q.E F₂.E := disjoint_left.mpr fun e he he' ↦ disjoint_left.mp ht.meet_E he
    (ht.right.1.2 he')
  rw [hE, ncard_union_eq hdis Q.finite_edges F₂.finite_edges, ht.union_E,
    ncard_union_eq ht.disj_E F₁.finite_edges F₂.finite_edges]
  omega

omit [T2Space S] in
/-- A circuit made of `Q` and one path of `F` is no longer than `F`, and it is lighter. -/
theorem improve (ht : TwoPaths D.rad.G F F₁ F₂ Q a b) (hc : Q.E.ncard ≤ F₁.E.ncard)
  (hw : D.tb.weightSub Q < D.tb.weightSub F₁) :
    Drawing.IsCircuitOf (D.rad.G.sup Q F₂) D.rad.G ∧ (D.rad.G.sup Q F₂).E.ncard ≤ F.E.ncard ∧
      D.tb.weightSub (D.rad.G.sup Q F₂) < D.tb.weightSub F := by
  have : ConnectedSpace Shat := cap.connected
  have hE : (D.rad.G.sup Q F₂).E = Q.E ∪ F₂.E := Drawing.sup_E ht.path.1 ht.sub₂
  have hdis : Disjoint Q.E F₂.E := disjoint_left.mpr fun e he he' ↦ disjoint_left.mp ht.meet_E he
    (ht.right.1.2 he')
  refine ⟨⟨D.rad.G.sup_isSubdrawing Q F₂, ht.left_circuit⟩, ?_, ?_⟩
  · rw [hE, ncard_union_eq hdis Q.finite_edges F₂.finite_edges, ht.union_E,
      ncard_union_eq ht.disj_E F₁.finite_edges F₂.finite_edges]
    omega
  · rw [D.tb.weightSub_sup hE hdis, D.tb.weightSub_sup ht.union_E ht.disj_E]
    linarith

omit [T2Space S] [T2Space Shat] in
/-- A circuit of `Γ*` shorter than `2 rep(𝒯)` lies in its inside. -/
theorem U_subset_ins (D : TangleDatum cap χ) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
  (hlt : C.E.ncard < 2 * D.rep) :
    C.U ⊆ D.ins C := by
  have hi := D.ins_spec hC hlt
  rw [← hi.2.2.2.1]
  exact Surface.discBd_subset _

omit [T2Space S] in
/-- The three circuits of a theta: the inside of one is covered by the insides of the two others. -/
theorem ins_theta (hrep : 1 ≤ D.rep) (ht : TwoPaths D.rad.G F F₁ F₂ Q a b)
  (hFc : F.IsCircuitOf D.rad.G) (hF : F.E.ncard < 2 * D.rep)
    (h₁ : (D.rad.G.sup Q F₁).E.ncard < 2 * D.rep) (h₂ : (D.rad.G.sup Q F₂).E.ncard < 2 * D.rep) :
    D.ins F ⊆ D.ins (D.rad.G.sup Q F₁) ∪ D.ins (D.rad.G.sup Q F₂) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hs := D.isSlope hrep
  set G := D.rad.G with hG
  have hC₂ : Drawing.IsCircuitOf (G.sup Q F₂) G := ⟨G.sup_isSubdrawing Q F₂, ht.left_circuit⟩
  have hC₁ : Drawing.IsCircuitOf (G.sup Q F₁) G := ⟨G.sup_isSubdrawing Q F₁, ht.swap.left_circuit⟩
  have hsup : G.sup F₁ F₂ = F := Drawing.ext_of_V_E (by rw [Drawing.sup_V
    (ht.left.1.trans ht.sub) ht.sub₂, ht.union_V])
    (by rw [Drawing.sup_E (ht.left.1.trans ht.sub) ht.sub₂, ht.union_E])
  have hcomm : ∀ {X Y : Drawing Shat}, X.IsSubdrawing G → Y.IsSubdrawing G → G.sup X Y = G.sup Y X
    := fun hX hY ↦
    Drawing.ext_of_V_E (by rw [Drawing.sup_V hX hY, Drawing.sup_V hY hX, Set.union_comm])
      (by rw [Drawing.sup_E hX hY, Drawing.sup_E hY hX, Set.union_comm])
  have hsF₁ := ht.left.1.trans ht.sub
  have hsF₂ := ht.sub₂
  have hsQ := ht.path.1
  have hab₁ := ht.mem_V₁
  have hab₂ := ht.swap.mem_V₁
  obtain ⟨W, -, hWV, hWE⟩ := ht.path.2
  have habQ : a ∈ Q.V ∧ b ∈ Q.V := ⟨by rw [hWV]; exact W.start_mem_support, by rw [hWV]; exact
    W.end_mem_support⟩
  have hpos : ∀ {X : Drawing Shat}, X.IsPathBetween a b → 0 < X.length := fun {X} hX ↦ by
    obtain ⟨V, -, -, hVE⟩ := hX
    refine (ncard_pos X.finite_edges).2 ?_
    cases V with
    | nil h' => exact absurd rfl ht.ne
    | @cons _ x _ e h' r => exact ⟨e, by
        change e ∈ X.E
        rw [hVE]
        simp [GraphWalk.edges]⟩
  have hab : ({a, b} : Set Shat) ⊆ Q.V ∩ F₁.V := by
    rintro x (rfl | rfl)
    · exact ⟨habQ.1, hab₁.1⟩
    · exact ⟨habQ.2, hab₁.2⟩
  have hm₀₁ : Q.V ∩ F₁.V = {a, b} := by
    refine Subset.antisymm (fun x hx => ht.meet_V ⟨hx.1, ?_⟩) hab
    rw [ht.union_V]
    exact Or.inl hx.2
  have hm₁₂ : F₁.V ∩ F₂.V = {a, b} := by
    refine Subset.antisymm ht.inter_V ?_
    rintro x (rfl | rfl)
    · exact ⟨hab₁.1, hab₂.1⟩
    · exact ⟨hab₁.2, hab₂.2⟩
  have hm₂₀ : F₂.V ∩ Q.V = {a, b} := by
    refine Subset.antisymm (fun x hx ↦ ht.meet_V ⟨hx.2, by rw [ht.union_V]; exact Or.inr hx.1⟩) ?_
    rintro x (rfl | rfl)
    · exact ⟨hab₂.1, habQ.1⟩
    · exact ⟨hab₂.2, habQ.2⟩
  have hd₀₁ : Disjoint Q.E F₁.E := disjoint_left.mpr fun e he he' ↦ disjoint_left.mp ht.meet_E he
    (ht.left.1.2 he')
  have hd₀₂ : Disjoint Q.E F₂.E := disjoint_left.mpr fun e he he' ↦ disjoint_left.mp ht.meet_E he
    (ht.right.1.2 he')
  have hl₁ : (G.sup F₁ F₂).length < 2 * D.rep := by rw [hsup]; exact hF
  have hl₂ : (G.sup F₂ Q).length < 2 * D.rep := by rw [hcomm hsF₂ hsQ]; exact h₂
  have hl₃ : (G.sup Q F₁).length < 2 * D.rep := h₁
  have hcase := hs.three_paths Q F₁ F₂ a b ht.path.2 ht.left.2 ht.right.2 hsQ hsF₁ hsF₂
    (hpos ht.path.2) (hpos ht.left.2) (hpos ht.right.2)
    hm₀₁ hm₁₂ hm₂₀ hd₀₁ ht.disj_E hd₀₂.symm hl₁ hl₂ hl₃
  rw [hsup, hcomm hsF₂ hsQ] at hcase
  rcases hcase with ⟨c₂, c₁⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have hi := D.ins_spec hFc hF
    have hi₁ := D.ins_spec hC₁ h₁
    have hi₂ := D.ins_spec hC₂ h₂
    have hd := hi.2.2.1
    have hbd := hi.2.2.2.1
    have hout := isSide_out hT hd hbd
    have hd₁ : Disjoint (D.ins F)ᶜ (D.ins (G.sup Q F₁)) := disjoint_left.mpr fun x hx hx' ↦ hx
      (c₁ hx')
    have hd₂ : Disjoint (D.ins F)ᶜ (D.ins (G.sup Q F₂)) := disjoint_left.mpr fun x hx hx' ↦ hx
      (c₂ hx')
    intro x hx
    rcases ht.swap.theta_cover hT hout hi₂.2.2.1 hi₁.2.2.1 hi₂.2.2.2.1 hi₁.2.2.2.1 hd₂ hd₁ x with h
      | h | h
    · have hxF : x ∈ F.U := by
        have : x ∈ frontier (D.ins F) := by
          rw [frontier_eq_closure_inter_closure]
          exact ⟨subset_closure hx, h⟩
        rwa [IsClosedDisc.frontier_eq_discBd hT hd, hbd] at this
      rw [ht.U_eq] at hxF
      rcases hxF with h' | h'
      · exact Or.inl (D.U_subset_ins hC₁ h₁ (by rw [ht.swap.U_right]; exact Or.inr h'))
      · exact Or.inr (D.U_subset_ins hC₂ h₂ (by rw [ht.U_right]; exact Or.inr h'))
    · exact Or.inr h
    · exact Or.inl h
  · exact h.trans subset_union_right
  · exact h.trans subset_union_left

/-- A circuit of length at most `2n` with two poles in its inside: the first bullet of page 355. -/
def IsPairCircuit (D : TangleDatum cap χ) (n : ℕ) (C : Drawing Shat) : Prop :=
  C.IsCircuitOf D.rad.G ∧ C.E.ncard ≤ 2 * n ∧ ∃ p ∈ D.rad.poles, ∃ q ∈ D.rad.poles, p ≠ q
    ∧ p ∈ D.ins C ∧ q ∈ D.ins C

omit [T2Space S] in
omit [T2Space Shat] in
/-- A circuit of `IsPairCircuit` that is shortest, and lightest among the shortest. -/
theorem exists_least_pair {n : ℕ} (h : ∃ C, D.IsPairCircuit n C)
  :
    ∃ F, D.IsPairCircuit n F ∧ ∀ C, D.IsPairCircuit n C → F.E.ncard ≤ C.E.ncard ∧ (F.E.ncard
      = C.E.ncard → D.tb.weightSub F ≤ D.tb.weightSub C) := by
  have hfin : {C | D.IsPairCircuit n C}.Finite := (finite_circuits D.rad.G).subset fun C hC ↦
    ⟨hC.1.2, hC.1.1⟩
  obtain ⟨F₀, hF₀, hmin⟩ := Set.exists_min_image _ (fun C ↦ C.E.ncard) hfin h
  have hfin' : {C | D.IsPairCircuit n C ∧ C.E.ncard = F₀.E.ncard}.Finite
    := hfin.subset fun C hC ↦ hC.1
  obtain ⟨F, hF, hmin'⟩ := Set.exists_min_image _ (fun C ↦ D.tb.weightSub C) hfin' ⟨F₀, hF₀, rfl⟩
  refine ⟨F, hF.1, fun C hC ↦ ?_⟩
  rw [hF.2]
  exact ⟨hmin C hC, fun heq ↦ hmin' C ⟨hC, heq.symm⟩⟩

variable (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)

omit [T2Space S] in
/-- The least circuit around two poles cannot be improved through a pole. -/
theorem thetaFree_of_least {n : ℕ} (hn : n < D.rep) {F : Drawing Shat} (hF : D.IsPairCircuit n F)
    (hmin : ∀ C, D.IsPairCircuit n C → F.E.ncard ≤ C.E.ncard ∧ (F.E.ncard = C.E.ncard
      → D.tb.weightSub F ≤ D.tb.weightSub C)) : ThetaFree D F := by
  intro F₁ F₂ Q a b ht ⟨p, hp, hpQ⟩ c₁ w₁ c₂ w₂
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨hFc, hle, q₁, hq₁, q₂, hq₂, hne, hi₁, hi₂⟩ := hF
  have hrep : 1 ≤ D.rep := by omega
  obtain ⟨q, hq, hqi, hqp⟩ : ∃ q ∈ D.rad.poles, q ∈ D.ins F ∧ q ≠ p := by
    by_cases h : q₁ = p
    · exact ⟨q₂, hq₂, hi₂, fun h' ↦ hne (h.trans h'.symm)⟩
    · exact ⟨q₁, hq₁, hi₁, h⟩
  obtain ⟨hC₂, hl₂, hw₂⟩ := improve ht c₁ w₁
  obtain ⟨hC₁, hl₁, hw₁⟩ := improve ht.swap c₂ w₂
  have key : ∀ {C : Drawing Shat}, C.IsCircuitOf D.rad.G → C.E.ncard ≤ F.E.ncard
    → D.tb.weightSub C < D.tb.weightSub F → Q.U ⊆ C.U →
      q ∈ D.ins C → False := by
    intro C hC hl hw hQC hqC
    have hlt : C.E.ncard < 2 * D.rep := by omega
    have := hmin C ⟨hC, by omega, q, hq, p, hp, hqp, hqC, D.U_subset_ins hC hlt (hQC
      (Q.V_subset_U hpQ))⟩
    exact absurd (this.2 (le_antisymm this.1 hl)) (not_le.2 hw)
  rcases ins_theta hrep ht hFc (by omega) (by omega) (by omega) hqi with h | h
  · exact key hC₁ hl₁ hw₁ (by rw [ht.swap.U_right]; exact subset_union_left) h
  · exact key hC₂ hl₂ hw₂ (by rw [ht.U_right]; exact subset_union_left) h

include hS h3 in
/-- A circuit shorter than `2 rep(𝒯)` lies in a linked circuit that is no longer, and is no heavier
if it is as long. This is
(8.7) with `ins` in place of the sides. -/
theorem exists_linked {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
  (hlt : C.E.ncard < 2 * D.rep) :
    ∃ C', C'.IsCircuitOf D.rad.G ∧ C'.E.ncard ≤ C.E.ncard ∧ (C'.E.ncard = C.E.ncard
      → D.tb.weightSub C' ≤ D.tb.weightSub C) ∧
      D.ins C ⊆ D.ins C' ∧ GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins C'))
        (partIn cap D.P.Γ (closure (D.ins C')ᶜ)) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hi := D.ins_spec hC hlt
  have hs : IsSidesOf C (D.ins C) (closure (D.ins C)ᶜ) := by
    have h : Sided C (discInt (D.ins C)) (D.ins C)ᶜ := ⟨D.ins C, hi.2.2.1, hi.2.2.2.1, Or.inl ⟨rfl,
      rfl⟩⟩
    have := h.isSidesOf hT
    rwa [closure_discInt hi.2.2.1] at this
  have hle₁ : D.rep ≤ D.ord := (tangleRep_spec D.rad D.ord D.𝒯).1
  have hle₂ : (D.rep : ℕ∞) ≤ Painting.rep D.rad := tangleRep_le_rep D.rad D.ord D.𝒯
  have hlt' : (C.E.ncard : ℕ∞) < 2 * min (D.ord : ℕ∞) (Painting.rep D.rad) := by
    have h₁ : (D.rep : ℕ∞) ≤ min (D.ord : ℕ∞) (Painting.rep D.rad) := le_min
      (by exact_mod_cast hle₁) hle₂
    have h₂ : (C.E.ncard : ℕ∞) < 2 * (D.rep : ℕ∞) := by exact_mod_cast hlt
    exact lt_of_lt_of_le h₂ (by gcongr)
  obtain ⟨C', S₁', S₂', hL, hs', hlink, hle, hw, hsub, -⟩ := theorem_8_7_proof hS h3 D.tb
    D.isTangle hC hlt' hs hi.2.2.2.2
  have hlt₂ : C'.E.ncard < 2 * D.rep := by omega
  have hi' := D.ins_spec hL.1 hlt₂
  rcases isSidesOf_cases hT hi'.2.2.1 hi'.2.2.2.1 hs' with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · rw [e₁, e₂] at hlink
    exact ⟨C', hL.1, hle, hw, e₁ ▸ hsub, hlink⟩
  · exfalso
    rw [e₁, e₂] at hlink
    have hO := isSide_int hT hi'.2.2.1 hi'.2.2.2.1
    have hu := part_cover D.rad hL.1.1 hL.1.1 hL.1.1 (isSide_out hT hi'.2.2.1 hi'.2.2.2.1) hO hO
      (fun x ↦ by
      rw [closure_discInt hi'.2.2.1]
      by_cases hx : x ∈ D.ins C'
      · exact Or.inr (Or.inl hx)
      · exact Or.inl (subset_closure hx))
    rw [closure_discInt hi'.2.2.1] at hu
    exact D.isTangle.axiom2 hlink.1 hi'.2.2.2.2 hi'.2.2.2.2 hu

end TangleDatum

end GraphMinor.GM19
