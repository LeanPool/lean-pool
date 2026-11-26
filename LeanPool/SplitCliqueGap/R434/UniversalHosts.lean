/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.ResidualIsolates
public import LeanPool.SplitCliqueGap.R434.RobustHosts

/-! Split realizations whose new core vertices are universal. -/

@[expose] public section
namespace GapExtremal.R434
open Finset

section
variable {V H C : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
    [Fintype C] [DecidableEq C]

/-- The new host labels indexed by a colour and a cyclic base coordinate. -/
abbrev AddedHosts (V C : Type) [Fintype V] (x : ℕ) := C × ZMod (Fintype.card V + x)

private def universalPalettes (N : H → Finset V) (colour : V → C) {x q : ℕ} :
    H ⊕ (AddedHosts V C x ⊕ Fin q) → Finset (V ⊕ Fin x)
  | .inl h => (N h).disjSum univ
  | .inr (.inl (c, _)) => (univ.filter fun v => colour v = c).disjSum univ
  | .inr (.inr _) => (∅ : Finset V).disjSum univ

private noncomputable def coreLabel (x : ℕ) [NeZero (Fintype.card V + x)] : (V ⊕ Fin x) ≃ ZMod
  (Fintype.card V + x) :=
  Fintype.equivOfCardEq (by simp [ZMod.card])

private noncomputable def universalAssign (φ : V → V → H) (colour : V → C) (c₀ : C)
    {x q : ℕ} [NeZero (Fintype.card V + x)] (u v : V ⊕ Fin x) : H ⊕ (AddedHosts V C x ⊕ Fin q) :=
  match u, v with
  | .inl a, .inl b => .inl (φ a b)
  | .inl a, .inr _ => .inr (.inl (colour a, coreLabel x u + coreLabel x v))
  | .inr _, .inl b => .inr (.inl (colour b, coreLabel x u + coreLabel x v))
  | .inr _, .inr _ => .inr (.inl (c₀, coreLabel x u + coreLabel x v))

omit [DecidableEq H] [DecidableEq V] [Fintype C] [Fintype H] in
private theorem universal_hyp {B : SimpleGraph V}
    {N : H → Finset V} {φ : V → V → H} (original : HostHyp B N φ)
    (colour : V → C) (c₀ : C) (hcolour : ∀ a b, B.Adj a b → colour a ≠ colour b)
    (x q : ℕ) [NeZero (Fintype.card V + x)] : HostHyp (withIsolates B)
      (universalPalettes N colour : H ⊕ (AddedHosts V C x ⊕ Fin q) → _)
      (universalAssign φ colour c₀) where
  indep := by
    intro h a ha b hb hab
    rcases a with a | a
    · rcases b with b | b
      · have hab := (isolates_adj_inl B a b).mp hab
        rcases h with h | (⟨c,k⟩ | r)
        · exact original.indep h a (by simpa [universalPalettes] using ha)
            b (by simpa [universalPalettes] using hb) hab
        · have ha : colour a = c := by simpa [universalPalettes] using ha
          have hb : colour b = c := by simpa [universalPalettes] using hb
          exact hcolour a b hab (ha.trans hb.symm)
        · simp [universalPalettes] at ha
      · exact isolates_not_adj_inr B _ _ hab
    · exact isolates_not_adj_inr B _ _ hab.symm
  cover := by
    intro u v hne hnadj
    rcases u with a | a <;> rcases v with b | b
    · simpa [universalAssign, universalPalettes] using original.cover a b
        (fun e => hne (congrArg Sum.inl e)) (fun h => hnadj ((isolates_adj_inl B a b).mpr h))
    all_goals simp [universalAssign, universalPalettes]
  symm := by
    intro u v
    rcases u with a | a <;> rcases v with b | b <;>
      simp [universalAssign, original.symm, add_comm]
  inj := by
    intro u v v' huv ha huv' ha' heq
    have joined {u v v' : V ⊕ Fin x}
        (h : coreLabel x u + coreLabel x v = coreLabel x u + coreLabel x v') : v = v' :=
      (coreLabel x).injective (add_left_cancel h)
    rcases u with a | a <;> rcases v with b | b <;> rcases v' with c | c
    · simp only [universalAssign, Sum.inl.injEq] at heq
      exact congrArg Sum.inl (original.inj a b c (by simpa using huv) (by simpa using ha)
        (by simpa using huv') (by simpa using ha') heq)
    all_goals
      simp only [universalAssign, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
        Sum.inr_ne_inl, Prod.mk.injEq] at heq
    all_goals exact joined heq.2

omit [DecidableEq C] [DecidableEq H] in
theorem universal_graph_of_host_scores_with_support {B : SimpleGraph V} [DecidableRel B.Adj]
    {N : H → Finset V} {φ : V → V → H} (original : HostHyp B N φ)
    (colour : V → C) (c₀ : C) (hcolour : ∀ a b, B.Adj a b → colour a ≠ colour b)
    {x n : ℕ} (hx : 0 < x)
    (hn : Fintype.card (V ⊕ H) + x + Fintype.card C * (Fintype.card V + x) ≤ n)
    (I : ℤ) (hi : ∀ P : Finset (Finset V), IsPack P → ∑ Q ∈ P, w B Q ≤ I)
    {y : Finset V → ℝ} (hy : ResPack y) :
    ∃ (T : Type) (_ : Fintype T) (_ : DecidableEq T) (G : SimpleGraph T),
      Fintype.card T = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G x ∧
      (∑ Q, y Q * (w B Q : ℝ)) - (I : ℝ) ≤ gap G ∧
      ((∀ S, y S ≠ 0 → S.card ≤ 3) →
         (∑ Q, y Q * (w B Q : ℝ)) - (I : ℝ) ≤ gapWithFracFour G) := by
  classical
  let : NeZero (Fintype.card V + x) := ⟨by omega⟩
  let q := n - (Fintype.card (V ⊕ H) + x + Fintype.card C * (Fintype.card V + x))
  let M := universalPalettes N colour (x := x) (q := q)
  let T := (V ⊕ Fin x) ⊕ (H ⊕ (AddedHosts V C x ⊕ Fin q))
  have hm (i) : x ≤ (M i).card := by
    rcases i with h | (⟨c,k⟩ | r) <;> simp [M, universalPalettes, card_disjSum]
  have hcore : x ≤ Fintype.card (V ⊕ Fin x) := by simp
  have hc : Fintype.card T = n := by
    dsimp [T,q]
    simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_prod,ZMod.card] at hn ⊢
    omega
  have cuts : SurvivesCuts (hostGraph M) x := by
    refine ⟨?_, connected_after_cut M hcore hm⟩
    simp only [Fintype.card_sum, Fintype.card_fin]
    have hp : 0 < Fintype.card (AddedHosts V C x) := Fintype.card_pos_iff.mpr ⟨(c₀, 0)⟩
    omega
  obtain ⟨z, hz, hs, hscore⟩ := isolate_fractional_lift_with_support (X := Fin x) B hy
  have hg := gap_ge (universal_hyp original colour c₀ hcolour x q) I
    (isolate_integral_bound B I hi) hz
  rw [hscore] at hg
  refine ⟨T, inferInstance, inferInstance, hostGraph M, hc, isSplit_hostGraph M,
    connected_hostGraph M (.inr ⟨0,hx⟩) (fun i => card_pos.mp (hx.trans_le (hm i))), cuts, hg, ?_⟩
  intro hsmall
  have h := gapWithFracFour_ge (universal_hyp original colour c₀ hcolour x q) I
    (isolate_integral_bound B I hi) hz (hs hsmall)
  rw [hscore] at h
  exact h

omit [DecidableEq C] [DecidableEq H] in
theorem universal_graph_of_host_scores {B : SimpleGraph V} [DecidableRel B.Adj]
    {N : H → Finset V} {φ : V → V → H} (original : HostHyp B N φ)
    (colour : V → C) (c₀ : C) (hcolour : ∀ a b, B.Adj a b → colour a ≠ colour b)
    {x n : ℕ} (hx : 0 < x)
    (hn : Fintype.card (V ⊕ H) + x + Fintype.card C * (Fintype.card V + x) ≤ n)
    (I : ℤ) (hi : ∀ P : Finset (Finset V), IsPack P → ∑ Q ∈ P, w B Q ≤ I)
    {y : Finset V → ℝ} (hy : ResPack y) :
    ∃ (T : Type) (_ : Fintype T) (_ : DecidableEq T) (G : SimpleGraph T),
      Fintype.card T = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G x ∧
      (∑ Q, y Q * (w B Q : ℝ)) - (I : ℝ) ≤ gap G := by
  obtain ⟨T, fT, dT, G, hc, hsplit, hconn, hcuts, hgap, _⟩ :=
    universal_graph_of_host_scores_with_support original colour c₀ hcolour hx hn I hi hy
  exact ⟨T, fT, dT, G, hc, hsplit, hconn, hcuts, hgap⟩

end
end GapExtremal.R434
