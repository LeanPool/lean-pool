/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.EHPSHostTransfer

/-! Enlarged host neighborhoods and connectivity after vertex deletion. -/

@[expose] public section

open Finset

namespace GapExtremal.R434

/-- Deleting fewer than k vertices leaves a connected graph, and the order exceeds k. -/
def SurvivesCuts {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ D : Finset V, D.card < k →
    (G.induce {v | v ∉ D}).Connected

theorem connected_after_cut {V H : Type*} [Fintype V]
    (N : H → Finset V) {k : ℕ}
    (hcore : k ≤ Fintype.card V) (hN : ∀ h, k ≤ (N h).card)
    (D : Finset (V ⊕ H)) (hD : D.card < k) :
    ((hostGraph N).induce {v | v ∉ D}).Connected := by
  classical
  have survivor (S : Finset V) (hs : k ≤ S.card) : ∃ v ∈ S, (Sum.inl v : V ⊕ H) ∉ D := by
    have hi : (S.image (Sum.inl : V → V ⊕ H)).card = S.card :=
      card_image_of_injective _ Sum.inl_injective
    obtain ⟨_,he,hd⟩ := exists_mem_notMem_of_card_lt_card (hD.trans_le (hs.trans hi.ge))
    obtain ⟨v,hv,rfl⟩ := mem_image.mp he
    exact ⟨v,hv,hd⟩
  obtain ⟨v,_,hv⟩ := survivor univ (by simpa using hcore)
  let G := (hostGraph N).induce {u | u ∉ D}
  let root : {u : V ⊕ H // u ∉ D} := ⟨.inl v,hv⟩
  have reach (w : V) (hw : (Sum.inl w : V ⊕ H) ∉ D) : G.Reachable root ⟨.inl w,hw⟩ := by
    by_cases eq : v = w
    · subst w; exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (G := G) ((hostGraph_inl_inl N _ _).mpr eq)
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨root,?_⟩
  rintro ⟨w | h, hw⟩
  · exact reach w hw
  · obtain ⟨w,hm,hd⟩ := survivor (N h) (hN h)
    exact (reach w hd).trans (SimpleGraph.Adj.reachable (G := G) ((hostGraph_inl_inr N _ _).mpr hm))

namespace H54

private theorem role_exists (p : Sym2 Role) : ∃ r : Role, ∀ z ∈ p, ¬roleGraph.Adj r z := by
  refine p.inductionOn (fun a b => ?_)
  have table : ∀ a b : Role, ∃ r : Role, ¬roleGraph.Adj r a ∧ ¬roleGraph.Adj r b := by
    decide +kernel
  obtain ⟨r,ha,hb⟩ := table a b
  refine ⟨r, fun z hz => ?_⟩
  rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption

private noncomputable def safeRole (p : Sym2 Role) := (role_exists p).choose

end H54

namespace EHPS

theorem robust_graph_from_EHPS_scores_with {ε : ℝ} {m j n : ℕ} [NeZero m] (hm : Odd m)
    {C : Type} [Fintype C]
    (χ : ProductGrid m j → C)
    (hχ : ∀ a b, a ∉ productSupport ε m j → b ∉ productSupport ε m j → χ a = χ b →
      productHalf m j * (a + b) ∉ productSupport ε m j)
    (hn : Fintype.card ((H54.Role × ProductGrid m j) ⊕ MidHost H54.Role (ProductGrid m j) C) ≤ n)
    (I : ℤ) {y : Finset (H54.Role × ProductGrid m j) → ℝ}
    (hi : ∀ P : Finset (Finset (H54.Role × ProductGrid m j)), IsPack P →
      ∑ Q ∈ P, w (H54.coreGraph (productHalf m j) (productSupport ε m j)) Q ≤ I)
    (hy : ResPack y) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G ((m^2)^j) ∧
      (∑ Q, y Q * (w (H54.coreGraph (productHalf m j)
        (productSupport ε m j)) Q : ℝ)) - (I : ℝ) ≤ gap G := by
  classical
  let R := ProductGrid m j
  let H := MidHost H54.Role R C
  let : DecidableEq H := Classical.decEq H
  let T := H54.Role × R
  let h := productHalf m j
  let A := productSupport ε m j
  let B := H54.coreGraph h A
  let step := H54.roleStep h
  let φ := midAssign H54.roleGraph step h χ
  let N := midPalette H54.roleGraph step A h (H54.roleStep_swap h) χ
  have base : HostHyp B N φ := midpoint_host_hyp _ _ _ _ _ (productHalf_spec hm) χ
    hχ
  let fibre (r : H54.Role) : Finset T := {r} ×ˢ univ
  have hrole {v : T} {i : H} (hv : v ∈ N i) : v.1 ∈ i.1 := by
    simp only [N, midPalette, mem_filter, mem_univ, true_and] at hv
    obtain ⟨u,_,_,he⟩ := hv
    rw [← he]; exact Sym2.mem_mk_left _ _
  let q := n - Fintype.card (T ⊕ H)
  let M : H ⊕ Fin q → Finset T
    | .inl i => N i ∪ fibre (H54.safeRole i.1)
    | .inr _ => fibre (0,0)
  have big : HostHyp B M (fun x y => Sum.inl (φ x y)) := by
    constructor
    · rintro (i | i) x hx y hy adj
      · change x ∈ N i ∪ fibre _ at hx
        change y ∈ N i ∪ fibre _ at hy
        have safe := (H54.role_exists i.1).choose_spec
        have bad : H54.roleGraph.Adj x.1 y.1 := adj.1
        rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
        · exact base.indep i x hx y hy adj
        · have eq := mem_singleton.mp (mem_product.mp hy).1
          rw [eq] at bad
          exact safe x.1 (hrole hx) bad.symm
        · have eq := mem_singleton.mp (mem_product.mp hx).1
          rw [eq] at bad
          exact safe y.1 (hrole hy) bad
        · have ex := mem_singleton.mp (mem_product.mp hx).1
          have ey := mem_singleton.mp (mem_product.mp hy).1
          exact H54.roleGraph.loopless.irrefl _ (ex.trans ey.symm ▸ bad)
      · have ex := mem_singleton.mp (mem_product.mp hx).1
        have ey := mem_singleton.mp (mem_product.mp hy).1
        exact H54.roleGraph.loopless.irrefl _ (ex.trans ey.symm ▸ adj.1)
    · intro x y hne hn
      obtain ⟨hx,hy⟩ := base.cover x y hne hn
      exact ⟨mem_union_left _ hx,mem_union_left _ hy⟩
    · intro x y; rw [base.symm x y]
    · intro x y z h1 h2 h3 h4 eq
      exact base.inj x y z h1 h2 h3 h4 (Sum.inl_injective eq)
  have hR : Fintype.card R = (m^2)^j := by simp [R,ProductGrid,ZMod.card,pow_two]
  have hsize (i) : Fintype.card R ≤ (M i).card := by
    have hf (r) : (fibre r).card = Fintype.card R := by simp [fibre]
    cases i with
    | inl i => exact (hf _).ge.trans (card_le_card (subset_union_right (s₁ := N i)))
    | inr i => exact (hf _).ge
  have hT : Fintype.card T = 15 * Fintype.card R := by simp [T,H54.Role]
  have ht : 0 < Fintype.card R := Fintype.card_pos
  have hn' : Fintype.card (T ⊕ H) ≤ n := hn
  have hcard : Fintype.card (T ⊕ (H ⊕ Fin q)) = n := (card_pad q).trans (Nat.add_sub_of_le hn')
  have hcore : Fintype.card R ≤ Fintype.card T := by omega
  have hconn := connected_hostGraph M ((0,0),0) (fun i => card_pos.mp (ht.trans_le (hsize i)))
  refine ⟨_, inferInstance, inferInstance, hostGraph M,hcard,isSplit_hostGraph M,hconn,?_,gap_ge
    big I hi hy⟩
  rw [← hR]
  constructor
  · rw [Fintype.card_sum]; omega
  · exact connected_after_cut M hcore hsize

theorem robust_graph_from_EHPS_scores {ε : ℝ} {m j n : ℕ} [NeZero m] (hm : Odd m)
    (hn : hostFactor j * (m ^ 2) ^ j ≤ n)
    (I : ℤ) {y : Finset (H54.Role × ProductGrid m j) → ℝ}
    (hi : ∀ P : Finset (Finset (H54.Role × ProductGrid m j)), IsPack P →
      ∑ Q ∈ P, w (H54.coreGraph (productHalf m j) (productSupport ε m j)) Q ≤ I)
    (hy : ResPack y) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G ((m^2)^j) ∧
      (∑ Q, y Q * (w (H54.coreGraph (productHalf m j)
        (productSupport ε m j)) Q : ℝ)) - (I : ℝ) ≤ gap G := by
  exact robust_graph_from_EHPS_scores_with hm (productColour ε m j)
    (fun _ _ ha hb hc => product_mid_outside hm ha hb hc) ((host_order m j).trans_le hn) I hi hy

end EHPS
end GapExtremal.R434
