/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BalancedGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.NormalCycleEdge
public import LeanPool.GoldbergSeymour.ScheideTrunkRotationCycle

/-!
# Scheide Trunk Rotation Normal

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hrho_injective_88.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k)
      (_ : TreeSequence G (NormalCycleEdge N j)),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    Function.Injective rho := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B T' rho a b hab
  have hmod (r : Fin N.height) :
      (j.val + r.val) % N.height =
        if j.val + r.val < N.height then
          j.val + r.val
        else
          j.val + r.val - N.height := by
    by_cases hr : j.val + r.val < N.height
    · simp [hr, Nat.mod_eq_of_lt hr]
    · rw [ite_eq_right hr, Nat.mod_eq_sub_mod (by omega)]
      rw [Nat.mod_eq_of_lt]
      omega
  have hv := congrArg Fin.val hab
  change (j.val + a.val) % N.height =
    (j.val + b.val) % N.height at hv
  rw [hmod a, hmod b] at hv
  by_cases ha : j.val + a.val < N.height <;>
    by_cases hb : j.val + b.val < N.height <;>
    simp [ha, hb] at hv <;>
    apply Fin.ext <;> omega

private theorem helper_hrot_vertex_133.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (T' : TreeSequence G
        (NormalCycleEdge N j)), (
    ∀ (r : Fin (T'.length + (1 : ℕ))), (↑r : ℕ) < N.height →
    ∃ (i : Fin N.height), (↑i : ℕ) = ((↑j : ℕ) + (↑r : ℕ)) % N.height ∧ T'.vertex r = T.vertex
        (Fin.castLE N.height_upper i)) →
    ∀ (hnew_upper : N.height ≤ T'.length + (1 : ℕ)),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    ∀ (r : Fin N.height), T'.vertex (Fin.castLE hnew_upper r) = T.vertex (Fin.castLE
        N.height_upper (rho r)) := by
  classical
  intro V E _ _ _ G k e0 phi T N j T' hvertex hnew_upper rho r
  obtain ⟨i, hi, hv⟩ := hvertex (Fin.castLE hnew_upper r) (by
    simp)
  rw [hv]
  apply congrArg T.vertex
  apply congrArg (Fin.castLE N.height_upper)
  apply Fin.ext
  change i.val = (j.val + r.val) % N.height
  simpa using hi

private theorem helper_hpair_colors_150.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (A B : Fin k), (A =
        if Odd (↑j : ℕ) then N.beta else N.alpha) → (B = if Odd (↑j : ℕ) then N.alpha else N.beta)
        → (
    ∀ (i : Fin N.height), (1 : ℕ) ≤ (↑i : ℕ) → phi (NormalCycleEdge N i) = if Odd (↑i : ℕ) then
        some N.alpha else some N.beta) →
    ∀ (q : Fin N.height), (1 : ℕ) ≤ (↑q : ℕ) → phi (NormalCycleEdge N q) = some A ∨ phi
        (NormalCycleEdge N q) = some B := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B hA hB hcycle_colors q hq
  have hc := hcycle_colors q hq
  by_cases ho : Odd j.val
  · have hAe : A = N.beta := by simpa [ho] using hA
    have hBe : B = N.alpha := by simpa [ho] using hB
    by_cases hqo : Odd q.val
    · right
      rw [hBe]
      simpa [hqo] using hc
    · left
      rw [hAe]
      simpa [hqo] using hc
  · have hAe : A = N.alpha := by simpa [ho] using hA
    have hBe : B = N.beta := by simpa [ho] using hB
    by_cases hqo : Odd q.val
    · left
      rw [hAe]
      simpa [hqo] using hc
    · right
      rw [hBe]
      simpa [hqo] using hc

private theorem helper_hrot_color_173.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi psi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height), (1 :
        ℕ) ≤ (↑j : ℕ) →
    ∀ (A B : Fin k), (
    ∀ (i : Fin (↑j : ℕ)), psi (NormalCycleEdge N (Fin.castLE (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ) i)) = phi (NormalCycleEdge N (⟨(↑i : ℕ) + (1 : ℕ),
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ⟩ : Fin N.height))) → (
    ∀ (f : E), (
    ∀ (i : Fin ((↑j : ℕ) + (1 : ℕ))), f ≠ NormalCycleEdge N (Fin.castLE (
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ) i)) → psi f = phi f) →
    ∀ (_ : TreeSequence G (NormalCycleEdge N j)) (hp3 : (3 : ℕ) ≤ N.height), Function.Injective
        (NormalCycleEdge N) →
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r; Function.Injective
        rho → rho (⟨(0 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin N.height) = j → (
    ∀ (q : Fin N.height), (1 : ℕ) ≤ (↑q : ℕ) → phi (NormalCycleEdge N q) = some A ∨ phi
        (NormalCycleEdge N q) = some B) →
    ∀ (r : Fin N.height), (1 : ℕ) ≤ (↑r : ℕ) → psi (NormalCycleEdge N (rho r)) = some A ∨ psi
        (NormalCycleEdge N (rho r)) = some B := by
  classical
  intro V E _ _ _ G k e0 phi psi T N j hj A B hshift hfixed T' hp3 hcycle_injective rho
      hrho_injective hrho_zero hpair_colors r hr
  have hne : rho r ≠ j := by
    intro heq
    have hz := hrho_injective (heq.trans hrho_zero.symm)
    have hv := congrArg Fin.val hz
    simp at hv
    omega
  by_cases hq : (rho r).val < j.val
  · let a : Fin j.val := ⟨(rho r).val, hq⟩
    have hs := hshift a
    have hc := hpair_colors
      ⟨a.val + 1, by
        have hjlt := j.isLt
        simp [a] at *
        omega⟩ (by simp [a])
    have ha : Fin.castLE (Nat.le_of_lt j.isLt) a = rho r := by
      apply Fin.ext
      rfl
    rw [ha] at hs
    rw [hs]
    simpa [a] using hc
  · have hgt : j.val < (rho r).val := by
      have hn : (rho r).val ≠ j.val := by
        intro hn
        apply hne
        apply Fin.ext
        exact hn
      omega
    have hf : psi (NormalCycleEdge N (rho r)) =
        phi (NormalCycleEdge N (rho r)) := by
      apply hfixed
      intro a heq
      have hi := hcycle_injective heq
      have hv := congrArg Fin.val hi
      simp at hv
      omega
    rw [hf]
    exact hpair_colors (rho r) (by omega)

private theorem helper_htrunk_edge_eq_213.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k) (T' :
        TreeSequence G (NormalCycleEdge N j)), (
    ∀ (r : Fin T'.length), (↑r : ℕ) + (1 : ℕ) < N.height →
    ∃ (i : Fin N.height), (↑i : ℕ) = ((↑j : ℕ) + (↑r : ℕ)) % N.height ∧ T'.edge r =
        NormalCycleEdge N i) →
    ∀ (_ : (3 : ℕ) ≤ N.height),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    ∀ (r : Fin T'.length) (hr : (↑r : ℕ) + (1 : ℕ) < N.height), T'.edge r = NormalCycleEdge N (rho
        (⟨(↑r : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              have := GoldbergSeymour.TreeSequence.positive T'
              omega
    ⟩ : Fin N.height)) := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B T' hedge hp3 rho r hr
  obtain ⟨i, hi, he⟩ := hedge r hr
  rw [he]
  apply congrArg (NormalCycleEdge N)
  apply Fin.ext
  change i.val = (j.val + r.val) % N.height
  exact hi

private theorem helper_hchain_398.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi psi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (A B :
        Fin k) (T' : TreeSequence G (NormalCycleEdge N j)) (hp3 : (3 : ℕ) ≤ N.height) (hnew_upper
        : N.height ≤ T'.length + (1 : ℕ)),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r; (
    ∀ (r : Fin N.height), G.ends (NormalCycleEdge N (rho r)) = s(T'.vertex (Fin.castLE hnew_upper
        r), T'.vertex (Fin.castLE hnew_upper (⟨((↑r : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt ((↑r :
        ℕ) + (1 : ℕ)) (
    by
                        omega
    )⟩ : Fin N.height)))) → (
    ∀ (r : Fin N.height), (1 : ℕ) ≤ (↑r : ℕ) → psi (NormalCycleEdge N (rho r)) = some A ∨ psi
        (NormalCycleEdge N (rho r)) = some B) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G psi A B;
    let pathNode : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ)) → V ⊕ E := fun (n : Fin ((2 : ℕ)
        * (N.height - (1 : ℕ)) + (1 : ℕ))) ↦ if _ : (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) then Sum.inl
        (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt
        ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                      omega
    )⟩ : Fin N.height))) else Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                  omega
    ⟩ : Fin N.height))); (
    ∀ (n : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ))), (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) →
        pathNode n = Sum.inl (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) %
        N.height, Nat.mod_lt ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                          omega
    )⟩ : Fin N.height)))) → (
    ∀ (n : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ))), (↑n : ℕ) % (2 : ℕ) ≠ (0 : ℕ) →
        pathNode n = Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                      omega
    ⟩ : Fin N.height)))) →
    let nodes : List (V ⊕ E) := List.ofFn pathNode; List.IsChain H.Adj nodes := by
  classical
  intro V E _ _ _ G k e0 phi psi T N j A B T' hp3 hnew_upper rho hrot_ends hrot_color H pathNode
      hnode_even hnode_odd nodes
  rw [List.isChain_iff_getElem]
  intro i hi
  rw [List.length_ofFn] at hi
  rw [List.getElem_ofFn, List.getElem_ofFn]
  by_cases he : i % 2 = 0
  · have ho : (i + 1) % 2 ≠ 0 := by omega
    rw [hnode_even _ he, hnode_odd _ ho]
    let r : Fin N.height := ⟨i / 2 + 1, by omega⟩
    have hidx : (i / 2 + 1) % N.height = r.val :=
      Nat.mod_eq_of_lt r.isLt
    have hedgeidx : (i + 1 + 1) / 2 = r.val := by
      dsimp [r]
      omega
    change H.Adj
      (Sum.inl (T'.vertex (Fin.castLE hnew_upper
        ⟨(i / 2 + 1) % N.height, _⟩)))
      (Sum.inr (NormalCycleEdge N
        (rho ⟨(i + 1 + 1) / 2, _⟩)))
    rw [show (⟨(i / 2 + 1) % N.height, _⟩ : Fin N.height) = r by
        apply Fin.ext
        exact hidx,
      show (⟨(i + 1 + 1) / 2, _⟩ : Fin N.height) = r by
        apply Fin.ext
        exact hedgeidx]
    change Incident G (T'.vertex (Fin.castLE hnew_upper r))
        (NormalCycleEdge N (rho r)) ∧
      (psi (NormalCycleEdge N (rho r)) = some A ∨
        psi (NormalCycleEdge N (rho r)) = some B)
    constructor
    · rw [Incident, hrot_ends]
      simp
    · exact hrot_color r (by simp [r])
  · have ho : i % 2 = 1 := by omega
    have he' : (i + 1) % 2 = 0 := by omega
    rw [hnode_odd _ he, hnode_even _ he']
    let r : Fin N.height := ⟨(i + 1) / 2, by omega⟩
    have hedgeidx : (i + 1) / 2 = r.val := rfl
    have hvertexidx : ((i + 1) / 2 + 1) % N.height =
        (r.val + 1) % N.height := by rfl
    change H.Adj
      (Sum.inr (NormalCycleEdge N
        (rho ⟨(i + 1) / 2, _⟩)))
      (Sum.inl (T'.vertex (Fin.castLE hnew_upper
        ⟨((i + 1) / 2 + 1) % N.height, _⟩)))
    rw [show (⟨(i + 1) / 2, _⟩ : Fin N.height) = r by
        apply Fin.ext
        exact hedgeidx,
      show (⟨((i + 1) / 2 + 1) % N.height, _⟩ : Fin N.height) =
          ⟨(r.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩ by
        apply Fin.ext
        exact hvertexidx]
    change Incident G
        (T'.vertex (Fin.castLE hnew_upper
          ⟨(r.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩))
        (NormalCycleEdge N (rho r)) ∧
      (psi (NormalCycleEdge N (rho r)) = some A ∨
        psi (NormalCycleEdge N (rho r)) = some B)
    constructor
    · rw [Incident, hrot_ends]
      simp
    · exact hrot_color r (by simp [r]; omega)

private theorem helper_hnode_injective_505.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi psi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (A B :
        Fin k) (T' : TreeSequence G (NormalCycleEdge N j)) (hp3 : (3 : ℕ) ≤ N.height),
        Function.Injective (NormalCycleEdge N) →
    ∀ (hnew_upper : N.height ≤ T'.length + (1 : ℕ)),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r; Function.Injective
        rho →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G psi A B;
    let pathNode : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ)) → V ⊕ E := fun (n : Fin ((2 : ℕ)
        * (N.height - (1 : ℕ)) + (1 : ℕ))) ↦ if _ : (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) then Sum.inl
        (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt
        ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                      omega
    )⟩ : Fin N.height))) else Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                  omega
    ⟩ : Fin N.height))); (
    ∀ (n : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ))), (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) →
        pathNode n = Sum.inl (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) %
        N.height, Nat.mod_lt ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                          omega
    )⟩ : Fin N.height)))) → (
    ∀ (n : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ))), (↑n : ℕ) % (2 : ℕ) ≠ (0 : ℕ) →
        pathNode n = Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                      omega
    ⟩ : Fin N.height)))) →
    let nodes : List (V ⊕ E) := List.ofFn pathNode; List.IsChain H.Adj nodes →
    ∀ (hnodes_nonempty : nodes ≠ []), nodes.head hnodes_nonempty = Sum.inl (T'.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T'.positive⟩ : Fin (T'.length + (1 : ℕ)))) → nodes.getLast
        hnodes_nonempty = Sum.inl (T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T'.length⟩ : Fin
        (T'.length + (1 : ℕ)))) → Function.Injective pathNode := by
  classical
  intro V E _ _ _ G k e0 phi psi T N j A B T' hp3 hcycle_injective hnew_upper rho hrho_injective
      H pathNode hnode_even hnode_odd nodes hchain hnodes_nonempty hstart hend a b hab
  by_cases ha : a.val % 2 = 0
  · by_cases hb : b.val % 2 = 0
    · rw [hnode_even a ha, hnode_even b hb] at hab
      have hv := T'.vertex_injective (Sum.inl.inj hab)
      have hvv := congrArg Fin.val
        (Fin.castLE_injective hnew_upper hv)
      change (a.val / 2 + 1) % N.height =
        (b.val / 2 + 1) % N.height at hvv
      have hdiv : a.val / 2 = b.val / 2 := by
        by_cases hal : a.val / 2 + 1 < N.height
        · by_cases hbl : b.val / 2 + 1 < N.height
          · rw [Nat.mod_eq_of_lt hal, Nat.mod_eq_of_lt hbl] at hvv
            omega
          · have hbeq : b.val / 2 + 1 = N.height := by omega
            rw [hbeq, Nat.mod_self, Nat.mod_eq_of_lt hal] at hvv
            omega
        · by_cases hbl : b.val / 2 + 1 < N.height
          · have haeq : a.val / 2 + 1 = N.height := by omega
            rw [haeq, Nat.mod_self, Nat.mod_eq_of_lt hbl] at hvv
            omega
          · have haeq : a.val / 2 + 1 = N.height := by omega
            have hbeq : b.val / 2 + 1 = N.height := by omega
            omega
      apply Fin.ext
      omega
    · rw [hnode_even a ha, hnode_odd b hb] at hab
      simp at hab
  · by_cases hb : b.val % 2 = 0
    · rw [hnode_odd a ha, hnode_even b hb] at hab
      simp at hab
    · rw [hnode_odd a ha, hnode_odd b hb] at hab
      have hc := hcycle_injective (Sum.inr.inj hab)
      have hr := hrho_injective hc
      have hv := congrArg Fin.val hr
      simp at hv
      apply Fin.ext
      omega

private theorem helper_hvertex_support_547.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi psi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (A B :
        Fin k) (T' : TreeSequence G (NormalCycleEdge N j)) (hp3 : (3 : ℕ) ≤ N.height) (hnew_upper
        : N.height ≤ T'.length + (1 : ℕ)),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G psi A B;
    let pathNode : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ)) → V ⊕ E := fun (n : Fin ((2 : ℕ)
        * (N.height - (1 : ℕ)) + (1 : ℕ))) ↦ if _ : (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) then Sum.inl
        (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt
        ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                      omega
    )⟩ : Fin N.height))) else Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                  omega
    ⟩ : Fin N.height))); (
    ∀ (n : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ))), (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) →
        pathNode n = Sum.inl (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) %
        N.height, Nat.mod_lt ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                          omega
    )⟩ : Fin N.height)))) → (
    ∀ (n : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ))), (↑n : ℕ) % (2 : ℕ) ≠ (0 : ℕ) →
        pathNode n = Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                      omega
    ⟩ : Fin N.height)))) →
    let nodes : List (V ⊕ E) := List.ofFn pathNode;
    ∀ (hchain : List.IsChain H.Adj nodes) (hnodes_nonempty : nodes ≠ []),
    let rawPath : H.Walk (nodes.head hnodes_nonempty) (nodes.getLast hnodes_nonempty) :=
        SimpleGraph.Walk.ofSupport nodes hnodes_nonempty hchain;
    ∀ (hstart : nodes.head hnodes_nonempty = Sum.inl (T'.vertex (⟨(1 : ℕ), Nat.succ_lt_succ
        T'.positive⟩ : Fin (T'.length + (1 : ℕ))))) (hend : nodes.getLast hnodes_nonempty =
        Sum.inl (T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T'.length⟩ : Fin (T'.length + (1 : ℕ))))),
    let closingPath : H.Walk (Sum.inl (T'.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T'.positive⟩ : Fin
        (T'.length + (1 : ℕ))))) (Sum.inl (T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T'.length⟩ : Fin
        (T'.length + (1 : ℕ))))) := rawPath.copy hstart hend; closingPath.support = nodes →
        closingPath.length = (2 : ℕ) * (N.height - (1 : ℕ)) →
    ∀ (v : V), Sum.inl v ∈ closingPath.support ↔
    ∃ (i : Fin N.height), v = T'.vertex (Fin.castLE hnew_upper i) := by
  classical
  intro V E _ _ _ G k e0 phi psi T N j A B T' hp3 hnew_upper rho H pathNode hnode_even hnode_odd
      nodes hchain hnodes_nonempty rawPath hstart hend closingPath hpath_support hpath_length v
  rw [hpath_support]
  change Sum.inl v ∈ List.ofFn pathNode ↔ _
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨n, hn⟩
    by_cases he : n.val % 2 = 0
    · rw [hnode_even n he] at hn
      exact ⟨⟨(n.val / 2 + 1) % N.height,
        Nat.mod_lt _ (by omega)⟩, (Sum.inl.inj hn).symm⟩
    · rw [hnode_odd n he] at hn
      simp at hn
  · rintro ⟨i, rfl⟩
    by_cases hi : i.val = 0
    · let n : Fin (2 * (N.height - 1) + 1) :=
        ⟨2 * (N.height - 1), by omega⟩
      refine ⟨n, ?_⟩
      rw [hnode_even n (by simp [n])]
      congr 2
      apply Fin.ext
      simp only [Fin.castLE_mk, Fin.val_castLE]
      have hh : N.height - 1 + 1 = N.height := by omega
      have hdiv : n.val / 2 = N.height - 1 := by dsimp [n]; omega
      rw [hdiv, hh, Nat.mod_self, hi]
    · let n : Fin (2 * (N.height - 1) + 1) :=
        ⟨2 * (i.val - 1), by omega⟩
      refine ⟨n, ?_⟩
      rw [hnode_even n (by simp [n])]
      congr 2
      apply Fin.ext
      simp only [Fin.castLE_mk, Fin.val_castLE]
      have hieq : i.val - 1 + 1 = i.val := by omega
      have hdiv : n.val / 2 = i.val - 1 := by dsimp [n]; omega
      rw [hdiv, hieq, Nat.mod_eq_of_lt i.isLt]

private theorem helper_hedge_support_585.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi psi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (A B :
        Fin k) (T' : TreeSequence G (NormalCycleEdge N j)), T'.length = T.length →
    ∀ (hp3 : (3 : ℕ) ≤ N.height) (hnew_upper : N.height ≤ T'.length + (1 : ℕ)),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r; (
    ∀ (r : Fin T'.length) (hr : (↑r : ℕ) + (1 : ℕ) < N.height), T'.edge r = NormalCycleEdge N (rho
        (⟨(↑r : ℕ),
    by
                  omega
    ⟩ : Fin N.height))) →
    let last : Fin N.height := (⟨N.height - (1 : ℕ),
    by
          omega
    ⟩ : Fin N.height);
    let pred : Fin N.height := rho last;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G psi A B;
    let pathNode : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ)) → V ⊕ E := fun (n : Fin ((2 : ℕ)
        * (N.height - (1 : ℕ)) + (1 : ℕ))) ↦ if _ : (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) then Sum.inl
        (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt
        ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                      omega
    )⟩ : Fin N.height))) else Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                  omega
    ⟩ : Fin N.height))); (
    ∀ (n : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ))), (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) →
        pathNode n = Sum.inl (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) %
        N.height, Nat.mod_lt ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                          omega
    )⟩ : Fin N.height)))) → (
    ∀ (n : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ))), (↑n : ℕ) % (2 : ℕ) ≠ (0 : ℕ) →
        pathNode n = Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                      omega
    ⟩ : Fin N.height)))) →
    let nodes : List (V ⊕ E) := List.ofFn pathNode;
    ∀ (hchain : List.IsChain H.Adj nodes) (hnodes_nonempty : nodes ≠ []),
    let rawPath : H.Walk (nodes.head hnodes_nonempty) (nodes.getLast hnodes_nonempty) :=
        SimpleGraph.Walk.ofSupport nodes hnodes_nonempty hchain;
    ∀ (hstart : nodes.head hnodes_nonempty = Sum.inl (T'.vertex (⟨(1 : ℕ), Nat.succ_lt_succ
        T'.positive⟩ : Fin (T'.length + (1 : ℕ))))) (hend : nodes.getLast hnodes_nonempty =
        Sum.inl (T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T'.length⟩ : Fin (T'.length + (1 : ℕ))))),
    let closingPath : H.Walk (Sum.inl (T'.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T'.positive⟩ : Fin
        (T'.length + (1 : ℕ))))) (Sum.inl (T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T'.length⟩ : Fin
        (T'.length + (1 : ℕ))))) := rawPath.copy hstart hend; closingPath.support = nodes →
        closingPath.length = (2 : ℕ) * (N.height - (1 : ℕ)) →
    ∀ (f : E), Sum.inr f ∈ closingPath.support ↔ f = NormalCycleEdge N pred ∨
    ∃ (r : Fin T'.length), (1 : ℕ) ≤ (↑r : ℕ) ∧ (↑r : ℕ) + (2 : ℕ) ≤ N.height ∧ f = T'.edge r := by
  classical
  intro V E _ _ _ G k e0 phi psi T N j A B T' hlength hp3 hnew_upper rho htrunk_edge_eq last pred
      H pathNode hnode_even hnode_odd nodes hchain hnodes_nonempty rawPath hstart hend
      closingPath hpath_support hpath_length f
  rw [hpath_support]
  change Sum.inr f ∈ List.ofFn pathNode ↔ _
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨n, hn⟩
    by_cases he : n.val % 2 = 0
    · rw [hnode_even n he] at hn
      simp at hn
    · rw [hnode_odd n he] at hn
      let r : Fin N.height := ⟨(n.val + 1) / 2, by omega⟩
      have hrpos : 1 ≤ r.val := by
        dsimp [r]
        omega
      by_cases hlast : r.val + 1 = N.height
      · left
        have hr : r = last := by
          apply Fin.ext
          simp [last]
          omega
        simpa [pred, r, hr] using (Sum.inr.inj hn).symm
      · right
        have hrbefore : r.val + 1 < N.height := by omega
        let rt : Fin T'.length := ⟨r.val, by
          have hu := hnew_upper
          omega⟩
        refine ⟨rt, by simpa [rt] using hrpos, by simp [rt]; omega, ?_⟩
        have heq := htrunk_edge_eq rt (by simp [rt]; omega)
        have hrr : (⟨rt.val, by
            simp [rt]⟩ : Fin N.height) = r := by
          apply Fin.ext
          rfl
        rw [heq, hrr]
        exact (Sum.inr.inj hn).symm
  · rintro (hclose | ⟨r, hrpos, hrbound, rfl⟩)
    · let n : Fin (2 * (N.height - 1) + 1) :=
        ⟨2 * (N.height - 1) - 1, by omega⟩
      refine ⟨n, ?_⟩
      rw [hnode_odd n (by simp [n]; omega)]
      rw [hclose]
      congr 2
      apply congrArg rho
      apply Fin.ext
      simp [n, last]
      omega
    · let n : Fin (2 * (N.height - 1) + 1) :=
        ⟨2 * r.val - 1, by omega⟩
      refine ⟨n, ?_⟩
      rw [hnode_odd n (by simp [n]; omega)]
      have heq := htrunk_edge_eq r (by omega)
      rw [heq]
      congr 2
      apply congrArg rho
      apply Fin.ext
      simp [n]
      omega

private theorem helper_hrho_succ_860.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k) (_ :
        TreeSequence G (NormalCycleEdge N j)) (hp3 : (3 : ℕ) ≤ N.height),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    ∀ (r : Fin N.height), rho (⟨((↑r : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt ((↑r : ℕ) + (1 : ℕ)) (
    by
                omega
    )⟩ : Fin N.height) = (⟨((↑(rho r) : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt ((↑(rho r) : ℕ) + (1
        : ℕ)) (
    by
              omega
    )⟩ : Fin N.height) := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B T' hp3 rho r
  apply Fin.ext
  change (j.val + ((r.val + 1) % N.height)) % N.height =
    (((j.val + r.val) % N.height) + 1) % N.height
  calc
    (j.val + ((r.val + 1) % N.height)) % N.height =
        ((j.val % N.height) + (((r.val + 1) % N.height) % N.height)) %
          N.height := Nat.add_mod _ _ _
    _ = ((j.val % N.height) + ((r.val + 1) % N.height)) %
        N.height := by
      rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))]
    _ = (j.val + (r.val + 1)) % N.height :=
      (Nat.add_mod _ _ _).symm
    _ = ((j.val + r.val) + 1) % N.height := by congr 1
    _ = (((j.val + r.val) % N.height) + (1 % N.height)) %
        N.height := Nat.add_mod (j.val + r.val) 1 N.height
    _ = (((j.val + r.val) % N.height) + 1) % N.height := by
      rw [Nat.mod_eq_of_lt (by omega : 1 < N.height)]

private theorem helper_hstart_936.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k) (T' :
        TreeSequence G (NormalCycleEdge N j)) (hp3 : (3 : ℕ) ≤ N.height) (hnew_upper : N.height ≤
        T'.length + (1 : ℕ)),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    let pathNode : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ)) → V ⊕ E := fun (n : Fin ((2 : ℕ)
        * (N.height - (1 : ℕ)) + (1 : ℕ))) ↦ if _ : (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) then Sum.inl
        (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt
        ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                      omega
    )⟩ : Fin N.height))) else Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                  omega
    ⟩ : Fin N.height))); (
    ∀ (n : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ))), (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) →
        pathNode n = Sum.inl (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) %
        N.height, Nat.mod_lt ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                          omega
    )⟩ : Fin N.height)))) →
    let nodes : List (V ⊕ E) := List.ofFn pathNode;
    ∀ (hnodes_nonempty : nodes ≠ []), nodes.head hnodes_nonempty = Sum.inl (T'.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T'.positive⟩ : Fin (T'.length + (1 : ℕ)))) := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B T' hp3 hnew_upper rho pathNode hnode_even nodes
      hnodes_nonempty
  change (List.ofFn pathNode).head _ = _
  rw [List.head_ofFn, hnode_even]
  · congr 2
    apply Fin.ext
    simpa using (Nat.mod_eq_of_lt (by omega : 1 < N.height))
  · simp

private theorem helper_hend_944.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k) (T' :
        TreeSequence G (NormalCycleEdge N j)) (hp3 : (3 : ℕ) ≤ N.height) (hnew_upper : N.height ≤
        T'.length + (1 : ℕ)),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    let pathNode : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ)) → V ⊕ E := fun (n : Fin ((2 : ℕ)
        * (N.height - (1 : ℕ)) + (1 : ℕ))) ↦ if _ : (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) then Sum.inl
        (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt
        ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                      omega
    )⟩ : Fin N.height))) else Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                  omega
    ⟩ : Fin N.height))); (
    ∀ (n : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ))), (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) →
        pathNode n = Sum.inl (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) %
        N.height, Nat.mod_lt ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                          omega
    )⟩ : Fin N.height)))) →
    let nodes : List (V ⊕ E) := List.ofFn pathNode;
    ∀ (hnodes_nonempty : nodes ≠ []), nodes.getLast hnodes_nonempty = Sum.inl (T'.vertex (⟨(0 :
        ℕ), Nat.zero_lt_succ T'.length⟩ : Fin (T'.length + (1 : ℕ)))) := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B T' hp3 hnew_upper rho pathNode hnode_even nodes
      hnodes_nonempty
  change (List.ofFn pathNode).getLast _ = _
  rw [List.getLast_ofFn_succ, hnode_even]
  · congr 2
    apply Fin.ext
    change ((2 * (N.height - 1)) / 2 + 1) % N.height = 0
    have hh : N.height - 1 + 1 = N.height := by omega
    rw [Nat.mul_div_right (N.height - 1) (by omega : 0 < 2), hh,
      Nat.mod_self]
  · change (2 * (N.height - 1)) % 2 = 0
    omega

private theorem helper_hpath_support_960.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi psi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (A B :
        Fin k) (T' : TreeSequence G (NormalCycleEdge N j)) (hp3 : (3 : ℕ) ≤ N.height) (hnew_upper
        : N.height ≤ T'.length + (1 : ℕ)),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G psi A B;
    let pathNode : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ)) → V ⊕ E := fun (n : Fin ((2 : ℕ)
        * (N.height - (1 : ℕ)) + (1 : ℕ))) ↦ if _ : (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) then Sum.inl
        (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt
        ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                      omega
    )⟩ : Fin N.height))) else Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                  omega
    ⟩ : Fin N.height)));
    let nodes : List (V ⊕ E) := List.ofFn pathNode;
    ∀ (hchain : List.IsChain H.Adj nodes) (hnodes_nonempty : nodes ≠ []),
    let rawPath : H.Walk (nodes.head hnodes_nonempty) (nodes.getLast hnodes_nonempty) :=
        SimpleGraph.Walk.ofSupport nodes hnodes_nonempty hchain;
    ∀ (hstart : nodes.head hnodes_nonempty = Sum.inl (T'.vertex (⟨(1 : ℕ), Nat.succ_lt_succ
        T'.positive⟩ : Fin (T'.length + (1 : ℕ))))) (hend : nodes.getLast hnodes_nonempty =
        Sum.inl (T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T'.length⟩ : Fin (T'.length + (1 : ℕ))))),
    let closingPath : H.Walk (Sum.inl (T'.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T'.positive⟩ : Fin
        (T'.length + (1 : ℕ))))) (Sum.inl (T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T'.length⟩ : Fin
        (T'.length + (1 : ℕ))))) := rawPath.copy hstart hend; closingPath.support = nodes := by
  classical
  intro V E _ _ _ G k e0 phi psi T N j A B T' hp3 hnew_upper rho H pathNode nodes hchain
      hnodes_nonempty rawPath hstart hend closingPath
  calc
    closingPath.support = rawPath.support := by
      simpa only [closingPath] using
        SimpleGraph.Walk.support_copy rawPath hstart hend
    _ = nodes := by
      simpa only [rawPath] using
        SimpleGraph.Walk.support_ofSupport hnodes_nonempty hchain

private theorem helper_hpath_length_968.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi psi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (A B :
        Fin k) (T' : TreeSequence G (NormalCycleEdge N j)) (hp3 : (3 : ℕ) ≤ N.height) (hnew_upper
        : N.height ≤ T'.length + (1 : ℕ)),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G psi A B;
    let pathNode : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ)) → V ⊕ E := fun (n : Fin ((2 : ℕ)
        * (N.height - (1 : ℕ)) + (1 : ℕ))) ↦ if _ : (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) then Sum.inl
        (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt
        ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                      omega
    )⟩ : Fin N.height))) else Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                  omega
    ⟩ : Fin N.height)));
    let nodes : List (V ⊕ E) := List.ofFn pathNode;
    ∀ (hchain : List.IsChain H.Adj nodes) (hnodes_nonempty : nodes ≠ []),
    let rawPath : H.Walk (nodes.head hnodes_nonempty) (nodes.getLast hnodes_nonempty) :=
        SimpleGraph.Walk.ofSupport nodes hnodes_nonempty hchain;
    ∀ (hstart : nodes.head hnodes_nonempty = Sum.inl (T'.vertex (⟨(1 : ℕ), Nat.succ_lt_succ
        T'.positive⟩ : Fin (T'.length + (1 : ℕ))))) (hend : nodes.getLast hnodes_nonempty =
        Sum.inl (T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T'.length⟩ : Fin (T'.length + (1 : ℕ))))),
    let closingPath : H.Walk (Sum.inl (T'.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T'.positive⟩ : Fin
        (T'.length + (1 : ℕ))))) (Sum.inl (T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T'.length⟩ : Fin
        (T'.length + (1 : ℕ))))) := rawPath.copy hstart hend; closingPath.length = (2 : ℕ) *
        (N.height - (1 : ℕ)) := by
  classical
  intro V E _ _ _ G k e0 phi psi T N j A B T' hp3 hnew_upper rho H pathNode nodes hchain
      hnodes_nonempty rawPath hstart hend closingPath
  calc
    closingPath.length = rawPath.length := by
      simpa only [closingPath] using
        SimpleGraph.Walk.length_copy rawPath hstart hend
    _ = nodes.length - 1 := by
      simpa only [rawPath] using
        SimpleGraph.Walk.length_ofSupport hnodes_nonempty hchain
    _ = 2 * (N.height - 1) := by
      simp [nodes]

private theorem helper_hclosing_ends_995.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi psi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (A B :
        Fin k) (T' : TreeSequence G (NormalCycleEdge N j)) (hp3 : (3 : ℕ) ≤ N.height) (hnew_upper
        : N.height ≤ T'.length + (1 : ℕ)),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r; (
    ∀ (r : Fin N.height), G.ends (NormalCycleEdge N (rho r)) = s(T'.vertex (Fin.castLE hnew_upper
        r), T'.vertex (Fin.castLE hnew_upper (⟨((↑r : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt ((↑r :
        ℕ) + (1 : ℕ)) (
    by
                        omega
    )⟩ : Fin N.height)))) →
    let last : Fin N.height := (⟨N.height - (1 : ℕ),
    by
          omega
    ⟩ : Fin N.height);
    let pred : Fin N.height := rho last;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G psi A B;
    let pathNode : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ)) → V ⊕ E := fun (n : Fin ((2 : ℕ)
        * (N.height - (1 : ℕ)) + (1 : ℕ))) ↦ if _ : (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) then Sum.inl
        (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt
        ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                      omega
    )⟩ : Fin N.height))) else Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                  omega
    ⟩ : Fin N.height)));
    let nodes : List (V ⊕ E) := List.ofFn pathNode; List.IsChain H.Adj nodes →
    ∀ (hnodes_nonempty : nodes ≠ []), nodes.head hnodes_nonempty = Sum.inl (T'.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T'.positive⟩ : Fin (T'.length + (1 : ℕ)))) → nodes.getLast
        hnodes_nonempty = Sum.inl (T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T'.length⟩ : Fin
        (T'.length + (1 : ℕ)))) →
    let lastIndex : Fin (T'.length + (1 : ℕ)) := Fin.castLE hnew_upper last; G.ends
        (NormalCycleEdge N pred) = s(T'.vertex lastIndex, T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ
        T'.length⟩ : Fin (T'.length + (1 : ℕ)))) := by
  classical
  intro V E _ _ _ G k e0 phi psi T N j A B T' hp3 hnew_upper rho hrot_ends last pred H pathNode
      nodes hchain hnodes_nonempty hstart hend lastIndex
  rw [show pred = rho last by rfl, hrot_ends]
  apply Sym2.eq_iff.mpr
  left
  constructor
  · rfl
  · apply congrArg T'.vertex
    apply Fin.ext
    change (N.height - 1 + 1) % N.height = 0
    have hh : N.height - 1 + 1 = N.height := by omega
    rw [hh, Nat.mod_self]

private theorem helper_htrunk_ends_1008.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi psi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (A B :
        Fin k) (T' : TreeSequence G (NormalCycleEdge N j)) (hp3 : (3 : ℕ) ≤ N.height) (hnew_upper
        : N.height ≤ T'.length + (1 : ℕ)),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r; (
    ∀ (r : Fin N.height), G.ends (NormalCycleEdge N (rho r)) = s(T'.vertex (Fin.castLE hnew_upper
        r), T'.vertex (Fin.castLE hnew_upper (⟨((↑r : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt ((↑r :
        ℕ) + (1 : ℕ)) (
    by
                        omega
    )⟩ : Fin N.height)))) → (
    ∀ (r : Fin T'.length) (hr : (↑r : ℕ) + (1 : ℕ) < N.height), T'.edge r = NormalCycleEdge N (rho
        (⟨(↑r : ℕ),
    by
                  omega
    ⟩ : Fin N.height))) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G psi A B;
    let pathNode : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ)) → V ⊕ E := fun (n : Fin ((2 : ℕ)
        * (N.height - (1 : ℕ)) + (1 : ℕ))) ↦ if _ : (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) then Sum.inl
        (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt
        ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                      omega
    )⟩ : Fin N.height))) else Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                  omega
    ⟩ : Fin N.height)));
    let nodes : List (V ⊕ E) := List.ofFn pathNode; List.IsChain H.Adj nodes →
    ∀ (hnodes_nonempty : nodes ≠ []), nodes.head hnodes_nonempty = Sum.inl (T'.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T'.positive⟩ : Fin (T'.length + (1 : ℕ)))) → nodes.getLast
        hnodes_nonempty = Sum.inl (T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T'.length⟩ : Fin
        (T'.length + (1 : ℕ)))) →
    ∀ (r : Fin T'.length), (1 : ℕ) ≤ (↑r : ℕ) → (↑r : ℕ) + (2 : ℕ) ≤ N.height → G.ends (T'.edge r)
        = s(T'.vertex (⟨(↑r : ℕ), Nat.lt_succ_of_lt r.isLt⟩ : Fin (T'.length + (1 : ℕ))),
        T'.vertex r.succ) := by
  classical
  intro V E _ _ _ G k e0 phi psi T N j A B T' hp3 hnew_upper rho hrot_ends htrunk_edge_eq H
      pathNode nodes hchain hnodes_nonempty hstart hend r hrpos hrbound
  have hrbefore : r.val + 1 < N.height := by omega
  rw [htrunk_edge_eq r hrbefore,
    hrot_ends ⟨r.val, by omega⟩]
  apply Sym2.eq_iff.mpr
  left
  constructor
  · apply congrArg T'.vertex
    apply Fin.ext
    rfl
  · apply congrArg T'.vertex
    apply Fin.ext
    change (r.val + 1) % N.height = r.val + 1
    exact Nat.mod_eq_of_lt (by omega)

private theorem helper_hnew_one_1032.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi psi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (A B :
        Fin k) (T' : TreeSequence G (NormalCycleEdge N j)) (hp3 : (3 : ℕ) ≤ N.height) (hnew_upper
        : N.height ≤ T'.length + (1 : ℕ)),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r; (
    ∀ (r : Fin N.height), T'.vertex (Fin.castLE hnew_upper r) = T.vertex (Fin.castLE
        N.height_upper (rho r))) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G psi A B;
    let pathNode : Fin ((2 : ℕ) * (N.height - (1 : ℕ)) + (1 : ℕ)) → V ⊕ E := fun (n : Fin ((2 : ℕ)
        * (N.height - (1 : ℕ)) + (1 : ℕ))) ↦ if _ : (↑n : ℕ) % (2 : ℕ) = (0 : ℕ) then Sum.inl
        (T'.vertex (Fin.castLE hnew_upper (⟨((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt
        ((↑n : ℕ) / (2 : ℕ) + (1 : ℕ)) (
    by
                      omega
    )⟩ : Fin N.height))) else Sum.inr (NormalCycleEdge N (rho (⟨((↑n : ℕ) + (1 : ℕ)) / (2 : ℕ),
    by
                  omega
    ⟩ : Fin N.height)));
    let nodes : List (V ⊕ E) := List.ofFn pathNode;
    ∀ (_ : List.IsChain H.Adj nodes) (hnodes_nonempty : nodes ≠ []) (_ : nodes.head
        hnodes_nonempty = Sum.inl (T'.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T'.positive⟩ : Fin
        (T'.length + (1 : ℕ))))) (_ : nodes.getLast hnodes_nonempty = Sum.inl (T'.vertex (⟨(0 :
        ℕ), Nat.zero_lt_succ T'.length⟩ : Fin (T'.length + (1 : ℕ))))), T'.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T'.positive⟩ : Fin (T'.length + (1 : ℕ))) = T.vertex (Fin.castLE
        N.height_upper (⟨((↑j : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt ((↑j : ℕ) + (1 : ℕ)) (
    by
                  omega
    )⟩ : Fin N.height)) := by
  classical
  intro V E _ _ _ G k e0 phi psi T N j A B T' hp3 hnew_upper rho hrot_vertex H pathNode nodes
      hchain hnodes_nonempty hstart hend
  rw [show (⟨1, Nat.succ_lt_succ T'.positive⟩ : Fin (T'.length + 1)) =
      Fin.castLE hnew_upper (⟨1, by omega⟩ : Fin N.height) by rfl,
    hrot_vertex]
  apply congrArg T.vertex
  apply congrArg (Fin.castLE N.height_upper)
  apply Fin.ext
  rfl

theorem ScheideTrunkRotationNormal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi psi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (j : Fin N.height) (hj : 1 ≤ j.val) (A B : Fin k)
    (_ : A ≠ B)
    (hA : A = (if Odd j.val then N.beta else N.alpha))
    (hB : B = (if Odd j.val then N.alpha else N.beta))
    (hshift : ∀ i : Fin j.val,
      psi (NormalCycleEdge N
          (Fin.castLE (Nat.le_of_lt j.isLt) i)) =
        phi (NormalCycleEdge N
          ⟨i.val + 1, by
            have hi := i.isLt
            have _ := j.isLt
            omega⟩))
    (hfixed : ∀ f : E,
      (∀ i : Fin (j.val + 1),
        f ≠ NormalCycleEdge N
          (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i)) →
      psi f = phi f)
    (T' : TreeSequence G (NormalCycleEdge N j))
    (hglobal : GlobalMaximumTriple G k (NormalCycleEdge N j) psi T')
    (hmissA : A ∈ MissingColors G psi
      (T.vertex (Fin.castLE N.height_upper j)))
    (hmissB : B ∈ MissingColors G psi
      (T.vertex (Fin.castLE N.height_upper
        ⟨(j.val + 1) % N.height, by
          exact Nat.mod_lt _ (by
            have hp := N.height_lower
            omega)⟩)))
    (hlength : T'.length = T.length)
    (hvertex : ∀ r : Fin (T'.length + 1), r.val < N.height →
      ∃ i : Fin N.height,
        i.val = (j.val + r.val) % N.height ∧
          T'.vertex r = T.vertex (Fin.castLE N.height_upper i))
    (hedge : ∀ r : Fin T'.length, r.val + 1 < N.height →
      ∃ i : Fin N.height,
        i.val = (j.val + r.val) % N.height ∧
          T'.edge r = NormalCycleEdge N i) :
    ∃ N' : NormalGlobalMaximumTriple G k (NormalCycleEdge N j) psi T',
      N'.height = N.height ∧
      N'.alpha = A ∧ N'.beta = B ∧
      ∃ pred : Fin N.height,
        pred.val = (j.val + N.height - 1) % N.height ∧
          N'.closingEdge = NormalCycleEdge N pred := by
  classical
  obtain ⟨hp3, _hpodd, hcycle_injective, hcycle_ends, hcycle_colors⟩ :=
    ScheideTrunkRotationCycle G k e0 phi T N hbalanced
  have hnew_upper : N.height ≤ T'.length + 1 := by
    rw [hlength]
    exact N.height_upper
  let rho : Fin N.height → Fin N.height := fun r => j + r
  have hrho_val (r : Fin N.height) :
      (rho r).val = (j.val + r.val) % N.height := by
    rfl
  have hrho_injective : Function.Injective rho := by
    apply helper_hrho_injective_88 <;> assumption
  have hrho_zero : rho ⟨0, by omega⟩ = j := by
    apply Fin.ext
    change (j.val + 0) % N.height = j.val
    simpa using Nat.mod_eq_of_lt j.isLt
  have hrho_succ (r : Fin N.height) :
      rho ⟨(r.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩ =
        ⟨((rho r).val + 1) % N.height, Nat.mod_lt _ (by omega)⟩ := by
    apply helper_hrho_succ_860 <;> assumption
  have hrot_vertex (r : Fin N.height) :
      T'.vertex (Fin.castLE hnew_upper r) =
        T.vertex (Fin.castLE N.height_upper (rho r)) := by
    apply helper_hrot_vertex_133; assumption
  have hrot_ends (r : Fin N.height) :
      G.ends (NormalCycleEdge N (rho r)) =
        s(T'.vertex (Fin.castLE hnew_upper r),
          T'.vertex (Fin.castLE hnew_upper
            ⟨(r.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩)) := by
    rw [hcycle_ends, hrot_vertex, hrot_vertex, hrho_succ]
  have hpair_colors (q : Fin N.height) (hq : 1 ≤ q.val) :
      phi (NormalCycleEdge N q) = some A ∨
        phi (NormalCycleEdge N q) = some B := by
    apply helper_hpair_colors_150 <;> assumption
  have hrot_color (r : Fin N.height) (hr : 1 ≤ r.val) :
      psi (NormalCycleEdge N (rho r)) = some A ∨
        psi (NormalCycleEdge N (rho r)) = some B := by
    apply helper_hrot_color_173 <;> assumption
  have htrunk_edge_eq (r : Fin T'.length)
      (hr : r.val + 1 < N.height) :
      T'.edge r = NormalCycleEdge N
        (rho ⟨r.val, by omega⟩) := by
    apply helper_htrunk_edge_eq_213 <;> assumption
  let last : Fin N.height := ⟨N.height - 1, by omega⟩
  let pred : Fin N.height := rho last
  have hpred_val : pred.val =
      (j.val + N.height - 1) % N.height := by
    change (j.val + (N.height - 1)) % N.height = _
    congr 1
    omega
  let H := TwoColorIncidenceGraph G psi A B
  let pathNode : Fin (2 * (N.height - 1) + 1) → Sum V E := fun n =>
    if he : n.val % 2 = 0 then
      Sum.inl (T'.vertex (Fin.castLE hnew_upper
        ⟨(n.val / 2 + 1) % N.height, Nat.mod_lt _ (by omega)⟩))
    else
      Sum.inr (NormalCycleEdge N
        (rho ⟨(n.val + 1) / 2, by omega⟩))
  have hnode_even (n : Fin (2 * (N.height - 1) + 1))
      (hn : n.val % 2 = 0) :
      pathNode n = Sum.inl (T'.vertex (Fin.castLE hnew_upper
        ⟨(n.val / 2 + 1) % N.height, Nat.mod_lt _ (by omega)⟩)) := by
    simp [pathNode, hn]
  have hnode_odd (n : Fin (2 * (N.height - 1) + 1))
      (hn : n.val % 2 ≠ 0) :
      pathNode n = Sum.inr (NormalCycleEdge N
        (rho ⟨(n.val + 1) / 2, by omega⟩)) := by
    simp [pathNode, hn]
  let nodes : List (Sum V E) := List.ofFn pathNode
  have hchain : nodes.IsChain H.Adj := by
    apply helper_hchain_398 <;> assumption
  have hnodes_nonempty : nodes ≠ [] := by
    simp [nodes]
  let rawPath := SimpleGraph.Walk.ofSupport nodes hnodes_nonempty hchain
  have hstart : nodes.head hnodes_nonempty =
      Sum.inl (T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩) := by
    apply helper_hstart_936 <;> assumption
  have hend : nodes.getLast hnodes_nonempty =
      Sum.inl (T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩) := by
    apply helper_hend_944 <;> assumption
  let closingPath : H.Walk
      (Sum.inl (T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩))
      (Sum.inl (T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩)) :=
    rawPath.copy hstart hend
  have hpath_support : closingPath.support = nodes := by
    apply helper_hpath_support_960; assumption
  have hpath_length : closingPath.length = 2 * (N.height - 1) := by
    apply helper_hpath_length_968; assumption
  have hnode_injective : Function.Injective pathNode := by
    apply helper_hnode_injective_505 <;> assumption
  have hpath_isPath : closingPath.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hpath_support]
    exact List.nodup_ofFn.mpr hnode_injective
  have hvertex_support :
    ∀ v : V, Sum.inl v ∈ closingPath.support ↔
    ∃ i : Fin N.height, v = T'.vertex (Fin.castLE hnew_upper i) := by
    apply helper_hvertex_support_547 <;> assumption
  have hedge_support :
    ∀ f : E, Sum.inr f ∈ closingPath.support ↔ f = NormalCycleEdge N pred ∨
    ∃ r : Fin T'.length, 1 ≤ r.val ∧ r.val + 2 ≤ N.height ∧ f = T'.edge r := by
    apply helper_hedge_support_585 <;> assumption
  let lastIndex : Fin (T'.length + 1) := Fin.castLE hnew_upper last
  have hclosing_ends : G.ends (NormalCycleEdge N pred) =
      s(T'.vertex lastIndex,
        T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩) := by
    apply helper_hclosing_ends_995 <;> assumption
  have htrunk_ends :
    ∀ r : Fin T'.length, 1 ≤ r.val → r.val + 2 ≤ N.height → G.ends (T'.edge r) = s(T'.vertex
        ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩, T'.vertex r.succ) := by
    apply helper_htrunk_ends_1008 <;> assumption
  have hnew_zero : T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩ =
      T.vertex (Fin.castLE N.height_upper j) := by
    rw [show (⟨0, Nat.zero_lt_succ T'.length⟩ : Fin (T'.length + 1)) =
        Fin.castLE hnew_upper (⟨0, by omega⟩ : Fin N.height) by rfl,
      hrot_vertex, hrho_zero]
  have hnew_one : T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩ =
      T.vertex (Fin.castLE N.height_upper
        ⟨(j.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩) := by
    apply helper_hnew_one_1032 <;> assumption
  let N' : NormalGlobalMaximumTriple G k (NormalCycleEdge N j) psi T' :=
    { global := hglobal
      height := N.height
      height_lower := by omega
      height_upper := hnew_upper
      alpha := A
      beta := B
      alpha_missing := by
        rw [hnew_zero]
        exact hmissA
      beta_missing := by
        rw [hnew_one]
        exact hmissB
      closingEdge := NormalCycleEdge N pred
      lastIndex := lastIndex
      lastIndex_height := by
        change (N.height - 1) + 1 = N.height
        omega
      closing_ends := hclosing_ends
      closingPath := closingPath
      closingPath_isPath := hpath_isPath
      closingPath_length := hpath_length
      closingPath_vertices := hvertex_support
      closingPath_edges := hedge_support
      trunk_edge_ends := htrunk_ends }
  refine ⟨N', rfl, rfl, rfl, pred, hpred_val, rfl⟩

end GoldbergSeymour

end
