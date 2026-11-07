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
# Scheide Trunk Rotation Tree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hrho_injective_91.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    Function.Injective rho := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B rho a b hab
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

private theorem helper_hvertex_injective_155.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k),
    (3 : ℕ) ≤ N.height →
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    Function.Injective rho →
    let newVertex : Fin (T.length + (1 : ℕ)) → V := fun (r : Fin (T.length + (1 : ℕ))) ↦
      if hr : (↑r : ℕ) < N.height then
        T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))
      else T.vertex r;
    (∀ (r : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) < N.height),
        newVertex r =
          T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))) →
    (∀ (r : Fin (T.length + (1 : ℕ))), N.height ≤ (↑r : ℕ) → newVertex r = T.vertex r) →
    Function.Injective newVertex := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B hp3 rho hrho_injective newVertex hvertex_prefix
      hvertex_tail a b hab
  by_cases ha : a.val < N.height
  · by_cases hb : b.val < N.height
    · rw [hvertex_prefix a ha, hvertex_prefix b hb] at hab
      have hc := T.vertex_injective hab
      have hr := hrho_injective (Fin.castLE_injective N.height_upper hc)
      apply Fin.ext
      have hv := congrArg (fun q : Fin N.height => q.val) hr
      simpa using hv
    · rw [hvertex_prefix a ha,
        hvertex_tail b (by omega)] at hab
      have hc := congrArg Fin.val (T.vertex_injective hab)
      have hlt := (rho ⟨a.val, ha⟩).isLt
      simp at hc
      omega
  · by_cases hb : b.val < N.height
    · rw [hvertex_tail a (by omega),
        hvertex_prefix b hb] at hab
      have hc := congrArg Fin.val (T.vertex_injective hab)
      have hlt := (rho ⟨b.val, hb⟩).isLt
      simp at hc
      omega
    · rw [hvertex_tail a (by omega),
        hvertex_tail b (by omega)] at hab
      exact T.vertex_injective hab

private theorem helper_hedge_injective_197.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k)
      (_ : (3 : ℕ) ≤ N.height),
    Function.Injective (NormalCycleEdge N) →
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    Function.Injective rho →
    let newEdge : Fin T.length → E := fun (r : Fin T.length) ↦
      if hr : (↑r : ℕ) + (1 : ℕ) < N.height then
        NormalCycleEdge N
          (rho
            (⟨(↑r : ℕ), by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin N.height))
      else T.edge r;
    (∀ (r : Fin T.length) (hr : (↑r : ℕ) + (1 : ℕ) < N.height),
        newEdge r =
          NormalCycleEdge N
            (rho
              (⟨(↑r : ℕ), by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega⟩ :
                Fin N.height))) →
    (∀ (r : Fin T.length), N.height - (1 : ℕ) ≤ (↑r : ℕ) → newEdge r = T.edge r) →
    (∀ (i : Fin N.height) (r : Fin T.length),
        N.height - (1 : ℕ) ≤ (↑r : ℕ) → NormalCycleEdge N i ≠ T.edge r) →
    Function.Injective newEdge := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B hp3 hcycle_injective rho hrho_injective newEdge
      hedge_prefix hedge_tail hcycle_tail_ne a b hab
  by_cases ha : a.val + 1 < N.height
  · by_cases hb : b.val + 1 < N.height
    · rw [hedge_prefix a ha, hedge_prefix b hb] at hab
      have hc := hcycle_injective hab
      have hr := hrho_injective hc
      apply Fin.ext
      have hv := congrArg (fun q : Fin N.height => q.val) hr
      simpa using hv
    · rw [hedge_prefix a ha, hedge_tail b (by omega)] at hab
      exfalso
      exact (hcycle_tail_ne _ b (by omega)) hab
  · by_cases hb : b.val + 1 < N.height
    · rw [hedge_tail a (by omega), hedge_prefix b hb] at hab
      exfalso
      exact (hcycle_tail_ne _ a (by omega)) hab.symm
    · rw [hedge_tail a (by omega), hedge_tail b (by omega)] at hab
      exact T.edge_injective hab

private theorem helper_htransport_index_221.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k),
    (3 : ℕ) ≤ N.height →
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    Function.Surjective rho →
    let newVertex : Fin (T.length + (1 : ℕ)) → V := fun (r : Fin (T.length + (1 : ℕ))) ↦
      if hr : (↑r : ℕ) < N.height then
        T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))
      else T.vertex r;
    (∀ (r : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) < N.height),
        newVertex r =
          T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))) →
    (∀ (r : Fin (T.length + (1 : ℕ))), N.height ≤ (↑r : ℕ) → newVertex r = T.vertex r) →
    ∀ (r : Fin T.length),
    N.height - (1 : ℕ) ≤ (↑r : ℕ) →
    ∀ (a : Fin ((↑r : ℕ) + (1 : ℕ))),
    ∃ (b : Fin ((↑r : ℕ) + (1 : ℕ))),
    newVertex
        (b.castLT
          (by
            have := GoldbergSeymour.TreeSequence.positive T
            omega)) =
      T.vertex
        (a.castLT
          (by
            have := GoldbergSeymour.TreeSequence.positive T
            omega)) := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B hp3 rho hrho_surjective newVertex hvertex_prefix
      hvertex_tail r hr a
  by_cases ha : a.val < N.height
  · obtain ⟨q, hq⟩ := hrho_surjective ⟨a.val, ha⟩
    let b : Fin (r.val + 1) := ⟨q.val, by
      have hq_lt := q.isLt
      omega⟩
    refine ⟨b, ?_⟩
    rw [hvertex_prefix _ (by simp [b])]
    apply congrArg T.vertex
    apply Fin.ext
    have hv := congrArg Fin.val hq
    simpa [b] using hv
  · let b : Fin (r.val + 1) := ⟨a.val, a.isLt⟩
    refine ⟨b, ?_⟩
    rw [hvertex_tail _ (by simpa [b] using (show N.height ≤ a.val by omega))]

private theorem helper_hnew_zero_282.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k)
      (hp3 : (3 : ℕ) ≤ N.height),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    rho
          (⟨(0 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin N.height) =
        j →
    let newVertex : Fin (T.length + (1 : ℕ)) → V := fun (r : Fin (T.length + (1 : ℕ))) ↦
      if hr : (↑r : ℕ) < N.height then
        T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))
      else T.vertex r;
    let newEdge : Fin T.length → E := fun (r : Fin T.length) ↦
      if hr : (↑r : ℕ) + (1 : ℕ) < N.height then
        NormalCycleEdge N
          (rho
            (⟨(↑r : ℕ), by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin N.height))
      else T.edge r;
    (∀ (r : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) < N.height),
        newVertex r =
          T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))) →
    ∀ (hvertex_injective : Function.Injective newVertex)
      (hedge_injective : Function.Injective newEdge)
      (hfirst_edge : newEdge (⟨(0 : ℕ), T.positive⟩ : Fin T.length) = NormalCycleEdge N j)
      (hattaches :
        ∀ (r : Fin T.length),
          ∃ (a : Fin ((↑r : ℕ) + (1 : ℕ))),
            G.ends (newEdge r) =
              s(newVertex r.succ,
                newVertex
                  (a.castLT
                    (by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega)))),
    let T' : TreeSequence G (NormalCycleEdge N j) :=
      { length := T.length, positive := T.positive, vertex := newVertex, edge := newEdge,
        vertex_injective := hvertex_injective, edge_injective := hedge_injective,
        first_edge := hfirst_edge, attaches := hattaches :
        TreeSequence G (NormalCycleEdge N j) };
    T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T'.length⟩ : Fin (T'.length + (1 : ℕ))) =
      T.vertex (Fin.castLE N.height_upper j) := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B hp3 rho hrho_zero newVertex newEdge hvertex_prefix
      hvertex_injective hedge_injective hfirst_edge hattaches T'
  change newVertex ⟨0, Nat.zero_lt_succ T.length⟩ = _
  rw [hvertex_prefix _ (by
    change 0 < N.height
    omega)]
  exact congrArg (fun q => T.vertex (Fin.castLE N.height_upper q)) hrho_zero

private theorem helper_hcycle_color_pair_306.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (A B : Fin k),
    (∀ (i : Fin N.height),
        (1 : ℕ) ≤ (↑i : ℕ) →
          phi (NormalCycleEdge N i) = if Odd (↑i : ℕ) then some N.alpha else some N.beta) →
    (insert N.alpha ({ N.beta } : Finset (Fin k)) : Finset (Fin k)) =
        (insert A ({ B } : Finset (Fin k)) : Finset (Fin k)) →
    ∀ (q : Fin N.height),
    (1 : ℕ) ≤ (↑q : ℕ) →
    phi (NormalCycleEdge N q) = some A ∨ phi (NormalCycleEdge N q) = some B := by
  classical
  intro V E _ _ _ G k e0 phi T N A B hcycle_colors hpair_colors q hq
  have hc := hcycle_colors q hq
  have halpha : N.alpha = A ∨ N.alpha = B := by
    have hm : N.alpha ∈ ({N.alpha, N.beta} : Finset (Fin k)) := by simp
    rw [hpair_colors] at hm
    simpa using hm
  have hbeta : N.beta = A ∨ N.beta = B := by
    have hm : N.beta ∈ ({N.alpha, N.beta} : Finset (Fin k)) := by simp
    rw [hpair_colors] at hm
    simpa using hm
  by_cases ho : Odd q.val
  · rw [ite_eq_left ho] at hc
    rcases halpha with ha | ha
    · left
      simpa [ha] using hc
    · right
      simpa [ha] using hc
  · rw [ite_eq_right ho] at hc
    rcases hbeta with hb | hb
    · left
      simpa [hb] using hc
    · right
      simpa [hb] using hc

private theorem helper_htrunk_color_331.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi psi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height),
    (1 : ℕ) ≤ (↑j : ℕ) →
    ∀ (A B : Fin k),
    (∀ (i : Fin (↑j : ℕ)),
        psi
            (NormalCycleEdge N
              (Fin.castLE
                (by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega)
                i)) =
          phi
            (NormalCycleEdge N
              (⟨(↑i : ℕ) + (1 : ℕ),
                  by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega⟩ :
                Fin N.height))) →
    (∀ (f : E),
        (∀ (i : Fin ((↑j : ℕ) + (1 : ℕ))),
            f ≠
              NormalCycleEdge N
                (Fin.castLE
                  (by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega)
                  i)) →
          psi f = phi f) →
    ∀ (hp3 : (3 : ℕ) ≤ N.height),
    Function.Injective (NormalCycleEdge N) →
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    Function.Injective rho →
    rho
          (⟨(0 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin N.height) =
        j →
    let newEdge : Fin T.length → E := fun (r : Fin T.length) ↦
      if hr : (↑r : ℕ) + (1 : ℕ) < N.height then
        NormalCycleEdge N
          (rho
            (⟨(↑r : ℕ), by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin N.height))
      else T.edge r;
    (∀ (r : Fin T.length) (hr : (↑r : ℕ) + (1 : ℕ) < N.height),
        newEdge r =
          NormalCycleEdge N
            (rho
              (⟨(↑r : ℕ), by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega⟩ :
                Fin N.height))) →
    (∀ (q : Fin N.height),
        (1 : ℕ) ≤ (↑q : ℕ) →
          phi (NormalCycleEdge N q) = some A ∨ phi (NormalCycleEdge N q) = some B) →
    ∀ (r : Fin T.length),
    (1 : ℕ) ≤ (↑r : ℕ) →
    (↑r : ℕ) + (1 : ℕ) < N.height →
    psi (newEdge r) = some A ∨ psi (newEdge r) = some B := by
  classical
  intro V E _ _ _ G k e0 phi psi T N j hj A B hshift hfixed hp3 hcycle_injective rho
      hrho_injective hrho_zero newEdge hedge_prefix hcycle_color_pair r hrpos hr
  let q : Fin N.height := rho ⟨r.val, by omega⟩
  rw [hedge_prefix r hr]
  change psi (NormalCycleEdge N q) = some A ∨
    psi (NormalCycleEdge N q) = some B
  have hqj : q ≠ j := by
    intro heq
    have hz := hrho_injective (heq.trans hrho_zero.symm)
    have hv := congrArg Fin.val hz
    simp at hv
    omega
  by_cases hq : q.val < j.val
  · let a : Fin j.val := ⟨q.val, hq⟩
    have hs := hshift a
    have hc := hcycle_color_pair
      ⟨a.val + 1, by
        have hjlt := j.isLt
        simp [a] at *
        omega⟩ (by simp [a])
    have hqa : Fin.castLE (Nat.le_of_lt j.isLt) a = q := by
      apply Fin.ext
      rfl
    rw [hqa] at hs
    rw [hs]
    simpa [a] using hc
  · have hqgt : j.val < q.val := by
      have hn : q.val ≠ j.val := by
        intro hn
        apply hqj
        apply Fin.ext
        exact hn
      omega
    have hf : psi (NormalCycleEdge N q) = phi (NormalCycleEdge N q) := by
      apply hfixed
      intro a heq
      have hi := hcycle_injective heq
      have hv := congrArg Fin.val hi
      simp at hv
      omega
    rw [hf]
    exact hcycle_color_pair q (by omega)

private theorem helper_hmissing_preserved_374.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi psi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (A B : Fin k),
    IsOneEdgeUncolored psi (NormalCycleEdge N j) →
    (∀ (i : Fin (↑j : ℕ)),
        psi
            (NormalCycleEdge N
              (Fin.castLE
                (by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega)
                i)) =
          phi
            (NormalCycleEdge N
              (⟨(↑i : ℕ) + (1 : ℕ),
                  by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega⟩ :
                Fin N.height))) →
    (∀ (f : E),
        (∀ (i : Fin ((↑j : ℕ) + (1 : ℕ))),
            f ≠
              NormalCycleEdge N
                (Fin.castLE
                  (by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega)
                  i)) →
          psi f = phi f) →
    ∀ (hp3 : (3 : ℕ) ≤ N.height),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    rho
          (⟨(0 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin N.height) =
        j →
    (∀ (q : Fin N.height),
        (1 : ℕ) ≤ (↑q : ℕ) →
          phi (NormalCycleEdge N q) = some A ∨ phi (NormalCycleEdge N q) = some B) →
    ∀ (v : V) (c : Fin k),
    c ≠ A →
    c ≠ B →
    c ∈ MissingColors G phi v →
    c ∈ MissingColors G psi v := by
  classical
  intro V E _ _ _ G k e0 phi psi T N j A B hone hshift hfixed hp3 rho hrho_zero hcycle_color_pair
      v c hcA hcB hc
  simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ,
    true_and] at hc ⊢
  intro hpresent
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hpresent
  obtain ⟨f, hfv, hfc⟩ := hpresent
  by_cases hspecial : ∃ q : Fin (j.val + 1),
      f = NormalCycleEdge N
        (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) q)
  · obtain ⟨q, hq⟩ := hspecial
    by_cases hlast : q.val = j.val
    · have hqj : Fin.castLE (Nat.succ_le_iff.mpr j.isLt) q = j := by
        apply Fin.ext
        exact hlast
      rw [hq, hqj, hone.1] at hfc
      simp at hfc
    · let a : Fin j.val := ⟨q.val, by omega⟩
      have hqa : Fin.castLE (Nat.le_of_lt j.isLt) a =
          Fin.castLE (Nat.succ_le_iff.mpr j.isLt) q := by
        apply Fin.ext
        rfl
      have hs := hshift a
      rw [hq, ← hqa, hs] at hfc
      have hpair := hcycle_color_pair
        ⟨a.val + 1, by
          have hjlt := j.isLt
          simp [a] at *
          omega⟩ (by simp [a])
      rcases hpair with hpair | hpair
      · rw [hpair] at hfc
        exact hcA (Option.some.inj hfc.symm)
      · rw [hpair] at hfc
        exact hcB (Option.some.inj hfc.symm)
  · have hfix : psi f = phi f := by
      apply hfixed
      intro q heq
      exact hspecial ⟨q, heq⟩
    apply hc
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨f, hfv, hfix.symm.trans hfc⟩

private theorem helper_hvertex_set_477.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k)
      (_ : (3 : ℕ) ≤ N.height),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    Function.Surjective rho →
    let newVertex : Fin (T.length + (1 : ℕ)) → V := fun (r : Fin (T.length + (1 : ℕ))) ↦
      if hr : (↑r : ℕ) < N.height then
        T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))
      else T.vertex r;
    let newEdge : Fin T.length → E := fun (r : Fin T.length) ↦
      if hr : (↑r : ℕ) + (1 : ℕ) < N.height then
        NormalCycleEdge N
          (rho
            (⟨(↑r : ℕ), by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin N.height))
      else T.edge r;
    (∀ (r : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) < N.height),
        newVertex r =
          T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))) →
    (∀ (r : Fin (T.length + (1 : ℕ))), N.height ≤ (↑r : ℕ) → newVertex r = T.vertex r) →
    ∀ (hvertex_injective : Function.Injective newVertex)
      (hedge_injective : Function.Injective newEdge)
      (hfirst_edge : newEdge (⟨(0 : ℕ), T.positive⟩ : Fin T.length) = NormalCycleEdge N j)
      (hattaches :
        ∀ (r : Fin T.length),
          ∃ (a : Fin ((↑r : ℕ) + (1 : ℕ))),
            G.ends (newEdge r) =
              s(newVertex r.succ,
                newVertex
                  (a.castLT
                    (by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega)))),
    let T' : TreeSequence G (NormalCycleEdge N j) :=
      { length := T.length, positive := T.positive, vertex := newVertex, edge := newEdge,
        vertex_injective := hvertex_injective, edge_injective := hedge_injective,
        first_edge := hfirst_edge, attaches := hattaches :
        TreeSequence G (NormalCycleEdge N j) };
    TreeSequenceVertexSet T' = TreeSequenceVertexSet T := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B hp3 rho hrho_surjective newVertex newEdge hvertex_prefix
      hvertex_tail hvertex_injective hedge_injective hfirst_edge hattaches T'
  apply Finset.ext
  intro v
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨a, rfl⟩
    change ∃ b : Fin (T.length + 1), T.vertex b = newVertex a
    by_cases ha : a.val < N.height
    · refine ⟨Fin.castLE N.height_upper (rho ⟨a.val, ha⟩), ?_⟩
      exact (hvertex_prefix a ha).symm
    · refine ⟨a, ?_⟩
      exact (hvertex_tail a (by omega)).symm
  · rintro ⟨a, rfl⟩
    change ∃ b : Fin (T.length + 1), newVertex b = T.vertex a
    by_cases ha : a.val < N.height
    · obtain ⟨q, hq⟩ := hrho_surjective ⟨a.val, ha⟩
      let b : Fin (T.length + 1) :=
        ⟨q.val, Nat.lt_of_lt_of_le q.isLt N.height_upper⟩
      refine ⟨b, ?_⟩
      rw [hvertex_prefix b (by simp [b])]
      apply congrArg T.vertex
      apply Fin.ext
      have hv := congrArg Fin.val hq
      simpa [b] using hv
    · refine ⟨a, hvertex_tail a (by omega)⟩

private theorem helper_branch_510.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k)
      (_ : (3 : ℕ) ≤ N.height),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    (∀ (r : Fin N.height), (↑(rho r) : ℕ) = ((↑j : ℕ) + (↑r : ℕ)) % N.height) →
    let newVertex : Fin (T.length + (1 : ℕ)) → V := fun (r : Fin (T.length + (1 : ℕ))) ↦
      if hr : (↑r : ℕ) < N.height then
        T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))
      else T.vertex r;
    let newEdge : Fin T.length → E := fun (r : Fin T.length) ↦
      if hr : (↑r : ℕ) + (1 : ℕ) < N.height then
        NormalCycleEdge N
          (rho
            (⟨(↑r : ℕ), by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin N.height))
      else T.edge r;
    (∀ (r : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) < N.height),
        newVertex r =
          T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))) →
    ∀ (hvertex_injective : Function.Injective newVertex)
      (hedge_injective : Function.Injective newEdge)
      (hfirst_edge : newEdge (⟨(0 : ℕ), T.positive⟩ : Fin T.length) = NormalCycleEdge N j)
      (hattaches :
        ∀ (r : Fin T.length),
          ∃ (a : Fin ((↑r : ℕ) + (1 : ℕ))),
            G.ends (newEdge r) =
              s(newVertex r.succ,
                newVertex
                  (a.castLT
                    (by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega)))),
    let T' : TreeSequence G (NormalCycleEdge N j) :=
      { length := T.length, positive := T.positive, vertex := newVertex, edge := newEdge,
        vertex_injective := hvertex_injective, edge_injective := hedge_injective,
        first_edge := hfirst_edge, attaches := hattaches :
        TreeSequence G (NormalCycleEdge N j) };
    ∀ (r : Fin (T'.length + (1 : ℕ))),
    (↑r : ℕ) < N.height →
    ∃ (i : Fin N.height),
    (↑i : ℕ) = ((↑j : ℕ) + (↑r : ℕ)) % N.height ∧
    T'.vertex r = T.vertex (Fin.castLE N.height_upper i) := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B hp3 rho hrho_val newVertex newEdge hvertex_prefix
      hvertex_injective hedge_injective hfirst_edge hattaches T' r hr
  let i : Fin N.height := rho ⟨r.val, hr⟩
  refine ⟨i, ?_, ?_⟩
  · exact hrho_val ⟨r.val, hr⟩
  · change newVertex r = _
    rw [hvertex_prefix r hr]

private theorem helper_branch_520.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k)
      (_ : (3 : ℕ) ≤ N.height),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    (∀ (r : Fin N.height), (↑(rho r) : ℕ) = ((↑j : ℕ) + (↑r : ℕ)) % N.height) →
    let newVertex : Fin (T.length + (1 : ℕ)) → V := fun (r : Fin (T.length + (1 : ℕ))) ↦
      if hr : (↑r : ℕ) < N.height then
        T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))
      else T.vertex r;
    let newEdge : Fin T.length → E := fun (r : Fin T.length) ↦
      if hr : (↑r : ℕ) + (1 : ℕ) < N.height then
        NormalCycleEdge N
          (rho
            (⟨(↑r : ℕ), by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin N.height))
      else T.edge r;
    (∀ (r : Fin T.length) (hr : (↑r : ℕ) + (1 : ℕ) < N.height),
        newEdge r =
          NormalCycleEdge N
            (rho
              (⟨(↑r : ℕ), by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega⟩ :
                Fin N.height))) →
    ∀ (hvertex_injective : Function.Injective newVertex)
      (hedge_injective : Function.Injective newEdge)
      (hfirst_edge : newEdge (⟨(0 : ℕ), T.positive⟩ : Fin T.length) = NormalCycleEdge N j)
      (hattaches :
        ∀ (r : Fin T.length),
          ∃ (a : Fin ((↑r : ℕ) + (1 : ℕ))),
            G.ends (newEdge r) =
              s(newVertex r.succ,
                newVertex
                  (a.castLT
                    (by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega)))),
    let T' : TreeSequence G (NormalCycleEdge N j) :=
      { length := T.length, positive := T.positive, vertex := newVertex, edge := newEdge,
        vertex_injective := hvertex_injective, edge_injective := hedge_injective,
        first_edge := hfirst_edge, attaches := hattaches :
        TreeSequence G (NormalCycleEdge N j) };
    ∀ (r : Fin T'.length),
    (↑r : ℕ) + (1 : ℕ) < N.height →
    ∃ (i : Fin N.height),
    (↑i : ℕ) = ((↑j : ℕ) + (↑r : ℕ)) % N.height ∧
    T'.edge r = NormalCycleEdge N i := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B hp3 rho hrho_val newVertex newEdge hedge_prefix
      hvertex_injective hedge_injective hfirst_edge hattaches T' r hr
  let i : Fin N.height := rho ⟨r.val, by omega⟩
  refine ⟨i, ?_, ?_⟩
  · exact hrho_val ⟨r.val, by omega⟩
  · change newEdge r = _
    rw [hedge_prefix r hr]

private theorem helper_branch_526.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k)
      (_ : (3 : ℕ) ≤ N.height),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    let newVertex : Fin (T.length + (1 : ℕ)) → V := fun (r : Fin (T.length + (1 : ℕ))) ↦
      if hr : (↑r : ℕ) < N.height then
        T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))
      else T.vertex r;
    let newEdge : Fin T.length → E := fun (r : Fin T.length) ↦
      if hr : (↑r : ℕ) + (1 : ℕ) < N.height then
        NormalCycleEdge N
          (rho
            (⟨(↑r : ℕ), by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin N.height))
      else T.edge r;
    (∀ (r : Fin T.length), N.height - (1 : ℕ) ≤ (↑r : ℕ) → newEdge r = T.edge r) →
    ∀ (hvertex_injective : Function.Injective newVertex)
      (hedge_injective : Function.Injective newEdge)
      (hfirst_edge : newEdge (⟨(0 : ℕ), T.positive⟩ : Fin T.length) = NormalCycleEdge N j)
      (hattaches :
        ∀ (r : Fin T.length),
          ∃ (a : Fin ((↑r : ℕ) + (1 : ℕ))),
            G.ends (newEdge r) =
              s(newVertex r.succ,
                newVertex
                  (a.castLT
                    (by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega)))),
    let T' : TreeSequence G (NormalCycleEdge N j) :=
      { length := T.length, positive := T.positive, vertex := newVertex, edge := newEdge,
        vertex_injective := hvertex_injective, edge_injective := hedge_injective,
        first_edge := hfirst_edge, attaches := hattaches :
        TreeSequence G (NormalCycleEdge N j) };
    ∀ (r : Fin T'.length),
    N.height - (1 : ℕ) ≤ (↑r : ℕ) →
    ∃ (s : Fin T.length),
    (↑s : ℕ) = (↑r : ℕ) ∧
    T'.edge r = T.edge s := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B hp3 rho newVertex newEdge hedge_tail hvertex_injective
      hedge_injective hfirst_edge hattaches T' r hr
  refine ⟨⟨r.val, by simp [T']⟩, rfl, ?_⟩
  change newEdge r = _
  exact hedge_tail r hr

private theorem helper_hrho_succ_760.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k)
      (hp3 : (3 : ℕ) ≤ N.height),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    ∀ (r : Fin N.height) (hr : (↑r : ℕ) + (1 : ℕ) < N.height),
    rho (⟨(↑r : ℕ) + (1 : ℕ), hr⟩ : Fin N.height) =
      (⟨((↑(rho r) : ℕ) + (1 : ℕ)) % N.height,
          Nat.mod_lt ((↑(rho r) : ℕ) + (1 : ℕ))
            (by
              omega)⟩ :
        Fin N.height) := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B hp3 rho r hr
  apply Fin.ext
  change (j.val + (r.val + 1)) % N.height =
    (((j.val + r.val) % N.height) + 1) % N.height
  calc
    (j.val + (r.val + 1)) % N.height =
        ((j.val + r.val) + 1) % N.height := by congr 1
    _ = (((j.val + r.val) % N.height) + (1 % N.height)) %
        N.height := Nat.add_mod (j.val + r.val) 1 N.height
    _ = (((j.val + r.val) % N.height) + 1) % N.height := by
      rw [Nat.mod_eq_of_lt (by omega : 1 < N.height)]

private theorem helper_hnew_one_874.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (_ _ : Fin k)
      (hp3 : (3 : ℕ) ≤ N.height),
    let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
    (∀ (r : Fin N.height), (↑(rho r) : ℕ) = ((↑j : ℕ) + (↑r : ℕ)) % N.height) →
    let newVertex : Fin (T.length + (1 : ℕ)) → V := fun (r : Fin (T.length + (1 : ℕ))) ↦
      if hr : (↑r : ℕ) < N.height then
        T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))
      else T.vertex r;
    let newEdge : Fin T.length → E := fun (r : Fin T.length) ↦
      if hr : (↑r : ℕ) + (1 : ℕ) < N.height then
        NormalCycleEdge N
          (rho
            (⟨(↑r : ℕ), by
                omega⟩ :
              Fin N.height))
      else T.edge r;
    (∀ (r : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) < N.height),
        newVertex r =
          T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))) →
    ∀ (hvertex_injective : Function.Injective newVertex)
      (hedge_injective : Function.Injective newEdge)
      (hfirst_edge : newEdge (⟨(0 : ℕ), T.positive⟩ : Fin T.length) = NormalCycleEdge N j)
      (hattaches :
        ∀ (r : Fin T.length),
          ∃ (a : Fin ((↑r : ℕ) + (1 : ℕ))),
            G.ends (newEdge r) =
              s(newVertex r.succ,
                newVertex (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt))))),
    let T' : TreeSequence G (NormalCycleEdge N j) :=
      { length := T.length, positive := T.positive, vertex := newVertex, edge := newEdge,
        vertex_injective := hvertex_injective, edge_injective := hedge_injective,
        first_edge := hfirst_edge, attaches := hattaches :
        TreeSequence G (NormalCycleEdge N j) };
    T'.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T'.positive⟩ : Fin (T'.length + (1 : ℕ))) =
      T.vertex
        (Fin.castLE N.height_upper
          (⟨((↑j : ℕ) + (1 : ℕ)) % N.height,
              Nat.mod_lt ((↑j : ℕ) + (1 : ℕ))
                (by
                  omega)⟩ :
            Fin N.height)) := by
  classical
  intro V E _ _ _ G k e0 phi T N j A B hp3 rho hrho_val newVertex newEdge hvertex_prefix
      hvertex_injective hedge_injective hfirst_edge hattaches T'
  change newVertex ⟨1, Nat.succ_lt_succ T.positive⟩ = _
  rw [hvertex_prefix _ (by
    change 1 < N.height
    omega)]
  apply congrArg T.vertex
  apply Fin.ext
  exact hrho_val ⟨1, by omega⟩

private abbrev helperContinuation1037Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi psi : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height)
   (hj : (1 : ℕ) ≤ (↑j : ℕ)) (A B : Fin k) (_ : IsProperEdgeColoring G psi)
   (_ : IsOneEdgeUncolored psi (NormalCycleEdge N j))
   (_ : A ∈ MissingColors G psi (T.vertex (Fin.castLE N.height_upper j)))
   (_ :
    B ∈
     MissingColors G psi
      (T.vertex
       (Fin.castLE N.height_upper
        (⟨((↑j : ℕ) + (1 : ℕ)) % N.height, by
          first
          | omega
          | (
            have := GoldbergSeymour.TreeSequence.positive T
            have := GoldbergSeymour.NormalGlobalMaximumTriple.height_upper N
            have := Fin.isLt j
            all_goals
             first
             | omega
             | exact Nat.mod_lt _ (by omega))⟩ :
         Fin N.height))))
   (_ :
    ∀ (i : Fin (↑j : ℕ)),
     psi (NormalCycleEdge N (Fin.castLE (Nat.le_of_lt j.isLt) i)) =
      phi (NormalCycleEdge N (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin N.height)))
   (_ :
    ∀ (f : E),
     (∀ (i : Fin ((↑j : ℕ) + (1 : ℕ))), f ≠ NormalCycleEdge N (Fin.castLE (by omega) i)) →
      psi f = phi f)
   (hp3 : (3 : ℕ) ≤ N.height) (_ : Function.Injective (NormalCycleEdge N))
   (_ :
    ∀ (i : Fin N.height),
     (1 : ℕ) ≤ (↑i : ℕ) →
      phi (NormalCycleEdge N i) = if Odd (↑i : ℕ) then some N.alpha else some N.beta),
   let rho : Fin N.height → Fin N.height := fun (r : Fin N.height) ↦ j + r;
   ∀ (_ : ∀ (r : Fin N.height), (↑(rho r) : ℕ) = ((↑j : ℕ) + (↑r : ℕ)) % N.height)
    (_ : Function.Injective rho) (_ : Function.Surjective rho)
    (_ : rho (⟨(0 : ℕ), by omega⟩ : Fin N.height) = j),
    let newVertex : Fin (T.length + (1 : ℕ)) → V := fun (r : Fin (T.length + (1 : ℕ))) ↦
     if hr : (↑r : ℕ) < N.height then
      T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height)))
     else T.vertex r;
    let newEdge : Fin T.length → E := fun (r : Fin T.length) ↦
     if hr : (↑r : ℕ) + (1 : ℕ) < N.height then
      NormalCycleEdge N (rho (⟨(↑r : ℕ), by omega⟩ : Fin N.height))
     else T.edge r;
    ∀
     (_ :
      ∀ (r : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) < N.height),
       newVertex r = T.vertex (Fin.castLE N.height_upper (rho (⟨(↑r : ℕ), hr⟩ : Fin N.height))))
     (_ : ∀ (r : Fin (T.length + (1 : ℕ))) (_ : N.height ≤ (↑r : ℕ)), newVertex r = T.vertex r)
     (_ :
      ∀ (r : Fin T.length) (hr : (↑r : ℕ) + (1 : ℕ) < N.height),
       newEdge r = NormalCycleEdge N (rho (⟨(↑r : ℕ), by omega⟩ : Fin N.height)))
     (_ : ∀ (r : Fin T.length) (_ : N.height - (1 : ℕ) ≤ (↑r : ℕ)), newEdge r = T.edge r)
     (hvertex_injective : Function.Injective newVertex)
     (_ :
      ∀ (i : Fin N.height) (r : Fin T.length) (_ : N.height - (1 : ℕ) ≤ (↑r : ℕ)),
       NormalCycleEdge N i ≠ T.edge r)
     (hedge_injective : Function.Injective newEdge)
     (hfirst_edge : newEdge (⟨(0 : ℕ), T.positive⟩ : Fin T.length) = NormalCycleEdge N j)
     (_ :
      ∀ (r : Fin T.length) (_ : N.height - (1 : ℕ) ≤ (↑r : ℕ)) (a : Fin ((↑r : ℕ) + (1 : ℕ))),
       ∃ (b : Fin ((↑r : ℕ) + (1 : ℕ))),
        newVertex (b.castLT (Nat.lt_trans b.isLt (Nat.succ_lt_succ r.isLt))) =
         T.vertex (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt))))
     (hattaches :
      ∀ (r : Fin T.length),
       ∃ (a : Fin ((↑r : ℕ) + (1 : ℕ))),
        G.ends (newEdge r) =
         s(newVertex r.succ, newVertex (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt))))),
     let T' : TreeSequence G (NormalCycleEdge N j) :=
      {
       length := T.length, positive := T.positive, vertex := newVertex, edge := newEdge,
       vertex_injective := hvertex_injective, edge_injective := hedge_injective,
       first_edge := hfirst_edge, attaches := hattaches : TreeSequence G (NormalCycleEdge N j) };
     ∀
      (_ :
       T'.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T'.length⟩ : Fin (T'.length + (1 : ℕ))) =
        T.vertex (Fin.castLE N.height_upper j))
      (_ :
       T'.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T'.positive⟩ : Fin (T'.length + (1 : ℕ))) =
        T.vertex
         (Fin.castLE N.height_upper
          (⟨((↑j : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt ((↑j : ℕ) + (1 : ℕ)) (by omega)⟩ :
           Fin N.height)))
      (_ :
       (insert N.alpha ({ N.beta } : Finset (Fin k)) : Finset (Fin k)) =
        (insert A ({ B } : Finset (Fin k)) : Finset (Fin k))),
      ∃ (T' : TreeSequence G (NormalCycleEdge N j)),
       GlobalMaximumTriple G k (NormalCycleEdge N j) psi T' ∧
        T'.length = T.length ∧
         TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
          (∀ (r : Fin (T'.length + (1 : ℕ))),
            (↑r : ℕ) < N.height →
             ∃ (i : Fin N.height),
              (↑i : ℕ) = ((↑j : ℕ) + (↑r : ℕ)) % N.height ∧
               T'.vertex r = T.vertex (Fin.castLE N.height_upper i)) ∧
           (∀ (r : Fin (T'.length + (1 : ℕ))),
             N.height ≤ (↑r : ℕ) →
              ∃ (s : Fin (T.length + (1 : ℕ))), (↑s : ℕ) = (↑r : ℕ) ∧ T'.vertex r = T.vertex s) ∧
            (∀ (r : Fin T'.length),
              (↑r : ℕ) + (1 : ℕ) < N.height →
               ∃ (i : Fin N.height),
                (↑i : ℕ) = ((↑j : ℕ) + (↑r : ℕ)) % N.height ∧ T'.edge r = NormalCycleEdge N i) ∧
             ∀ (r : Fin T'.length),
              N.height - (1 : ℕ) ≤ (↑r : ℕ) →
               ∃ (s : Fin T.length), (↑s : ℕ) = (↑r : ℕ) ∧ T'.edge r = T.edge s

private theorem helper_continuation_1037.{u_1, u_2} :
    helperContinuation1037Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi psi T N j hj A B hproper hone hmissA hmissB hshift hfixed hp3
      hcycle_injective hcycle_colors rho hrho_val hrho_injective hrho_surjective hrho_zero
      newVertex newEdge hvertex_prefix hvertex_tail hedge_prefix hedge_tail hvertex_injective
      hcycle_tail_ne hedge_injective hfirst_edge htransport_index hattaches T' hnew_zero hnew_one
      hpair_colors
  have hcycle_color_pair (q : Fin N.height) (hq : 1 ≤ q.val) :
      phi (NormalCycleEdge N q) = some A ∨
        phi (NormalCycleEdge N q) = some B := by
    exact @helper_hcycle_color_pair_306 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@N) (@A) (@B) (@hcycle_colors) (@hpair_colors) (@q) (@hq)
  have htrunk_color (r : Fin T.length) (hrpos : 1 ≤ r.val)
      (hr : r.val + 1 < N.height) :
      psi (newEdge r) = some A ∨ psi (newEdge r) = some B := by
    exact @helper_htrunk_color_331 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@psi) (@T) (@N) (@j) (@hj) (@A) (@B) (@hshift) (@hfixed) (@hp3)
        (@hcycle_injective) (@hrho_injective) (@hrho_zero) (@hedge_prefix) (@hcycle_color_pair)
        (@r) (@hrpos) (@hr)
  have hmissing_preserved (v : V) (c : Fin k)
      (hcA : c ≠ A) (hcB : c ≠ B)
      (hc : c ∈ MissingColors G phi v) :
      c ∈ MissingColors G psi v := by
    exact @helper_hmissing_preserved_374 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@psi) (@T) (@N) (@j) (@A) (@B) (@hone) (@hshift) (@hfixed) (@hp3)
        (@hrho_zero) (@hcycle_color_pair) (@v) (@c) (@hcA) (@hcB) (@hc)
  have htashkinov : TashkinovTree G (NormalCycleEdge N j) psi T' := by
    intro r hrpos
    change ∃ a : Fin (r.val + 1), ∃ c : Fin k,
      psi (newEdge r) = some c ∧
        c ∈ MissingColors G psi
          (newVertex (Fin.castLT a
            (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt))))
    by_cases hr : r.val + 1 < N.height
    · rcases htrunk_color r hrpos hr with hc | hc
      · let a : Fin (r.val + 1) := ⟨0, by omega⟩
        refine ⟨a, A, hc, ?_⟩
        change A ∈ MissingColors G psi
          (newVertex ⟨0, Nat.zero_lt_succ T.length⟩)
        rw [show newVertex ⟨0, Nat.zero_lt_succ T.length⟩ =
            T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩ by rfl,
          hnew_zero]
        exact hmissA
      · let a : Fin (r.val + 1) := ⟨1, by omega⟩
        refine ⟨a, B, hc, ?_⟩
        change B ∈ MissingColors G psi
          (newVertex ⟨1, Nat.succ_lt_succ T.positive⟩)
        rw [show newVertex ⟨1, Nat.succ_lt_succ T.positive⟩ =
            T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩ by rfl,
          hnew_one]
        exact hmissB
    · obtain ⟨a, c, hc, hcmiss⟩ := N.global.2.1 r hrpos
      have htail : N.height - 1 ≤ r.val := by omega
      have hfix : psi (T.edge r) = phi (T.edge r) := by
        apply hfixed
        intro q heq
        exact (hcycle_tail_ne _ r htail) heq.symm
      have hcnew : psi (newEdge r) = some c := by
        rw [hedge_tail r htail, hfix]
        exact hc
      by_cases hcA : c = A
      · let b : Fin (r.val + 1) := ⟨0, by omega⟩
        refine ⟨b, c, hcnew, ?_⟩
        subst c
        change A ∈ MissingColors G psi
          (newVertex ⟨0, Nat.zero_lt_succ T.length⟩)
        rw [show newVertex ⟨0, Nat.zero_lt_succ T.length⟩ =
            T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩ by rfl,
          hnew_zero]
        exact hmissA
      · by_cases hcB : c = B
        · let b : Fin (r.val + 1) := ⟨1, by omega⟩
          refine ⟨b, c, hcnew, ?_⟩
          subst c
          change B ∈ MissingColors G psi
            (newVertex ⟨1, Nat.succ_lt_succ T.positive⟩)
          rw [show newVertex ⟨1, Nat.succ_lt_succ T.positive⟩ =
              T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩ by rfl,
            hnew_one]
          exact hmissB
        · obtain ⟨b, hb⟩ := htransport_index r htail a
          refine ⟨b, c, hcnew, ?_⟩
          rw [hb]
          exact hmissing_preserved _ c hcA hcB hcmiss
  have hvertex_set : TreeSequenceVertexSet T' = TreeSequenceVertexSet T := by
    exact @helper_hvertex_set_477 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@j) (@A) (@B) (@hp3) (@hrho_surjective) (@hvertex_prefix)
        (@hvertex_tail) (@hvertex_injective) (@hedge_injective) (@hfirst_edge) (@hattaches)
  have hglobal :
      GlobalMaximumTriple G k (NormalCycleEdge N j) psi T' := by
    refine ⟨⟨N.global.1.1, N.global.1.2.1,
      N.global.1.2.2.1, hproper, hone⟩, htashkinov, ?_⟩
    rw [hvertex_set]
    exact N.global.2.2
  refine ⟨T', hglobal, rfl, hvertex_set, ?_, ?_, ?_, ?_⟩
  · exact @helper_branch_510 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@j) (@A) (@B) (@hp3) (@hrho_val) (@hvertex_prefix) (@hvertex_injective)
      (@hedge_injective) (@hfirst_edge) (@hattaches)
  · intro r hr
    refine ⟨⟨r.val, by simpa [T'] using r.isLt⟩, rfl, ?_⟩
    change newVertex r = _
    exact hvertex_tail r hr
  · exact @helper_branch_520 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@j) (@A) (@B) (@hp3) (@hrho_val) (@hedge_prefix) (@hvertex_injective)
      (@hedge_injective) (@hfirst_edge) (@hattaches)
  · exact @helper_branch_526 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@j) (@A) (@B) (@hp3) (@hedge_tail) (@hvertex_injective)
      (@hedge_injective) (@hfirst_edge) (@hattaches)

theorem ScheideTrunkRotationTree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi psi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (j : Fin N.height) (hj : 1 ≤ j.val) (A B : Fin k)
    (_ : A ≠ B)
    (hA : A = (if Odd j.val then N.beta else N.alpha))
    (hB : B = (if Odd j.val then N.alpha else N.beta))
    (hproper : IsProperEdgeColoring G psi)
    (hone : IsOneEdgeUncolored psi (NormalCycleEdge N j))
    (hmissA : A ∈ MissingColors G psi
      (T.vertex (Fin.castLE N.height_upper j)))
    (hmissB : B ∈ MissingColors G psi
      (T.vertex (Fin.castLE N.height_upper
        ⟨(j.val + 1) % N.height, by
          exact Nat.mod_lt _ (by
            have hp := N.height_lower
            omega)⟩)))
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
      psi f = phi f) :
    ∃ T' : TreeSequence G (NormalCycleEdge N j),
      GlobalMaximumTriple G k (NormalCycleEdge N j) psi T' ∧
      T'.length = T.length ∧
      TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
      (∀ r : Fin (T'.length + 1), r.val < N.height →
        ∃ i : Fin N.height,
          i.val = (j.val + r.val) % N.height ∧
            T'.vertex r = T.vertex (Fin.castLE N.height_upper i)) ∧
      (∀ r : Fin (T'.length + 1), N.height ≤ r.val →
        ∃ s : Fin (T.length + 1),
          s.val = r.val ∧ T'.vertex r = T.vertex s) ∧
      (∀ r : Fin T'.length, r.val + 1 < N.height →
        ∃ i : Fin N.height,
          i.val = (j.val + r.val) % N.height ∧
            T'.edge r = NormalCycleEdge N i) ∧
      ∀ r : Fin T'.length, N.height - 1 ≤ r.val →
        ∃ s : Fin T.length,
          s.val = r.val ∧ T'.edge r = T.edge s := by
  classical
  obtain ⟨hp3, _hpodd, hcycle_injective, hcycle_ends, hcycle_colors⟩ :=
    ScheideTrunkRotationCycle G k e0 phi T N hbalanced
  let rho : Fin N.height → Fin N.height := fun r => j + r
  have hrho_val (r : Fin N.height) :
      (rho r).val = (j.val + r.val) % N.height := by
    rfl
  have hrho_injective : Function.Injective rho := by
    exact @helper_hrho_injective_91 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@j) (@A) (@B)
  have hrho_surjective : Function.Surjective rho :=
    Finite.injective_iff_surjective.mp hrho_injective
  have hrho_zero : rho ⟨0, by omega⟩ = j := by
    apply Fin.ext
    change (j.val + 0) % N.height = j.val
    simpa using Nat.mod_eq_of_lt j.isLt
  have hrho_succ (r : Fin N.height) (hr : r.val + 1 < N.height) :
      rho ⟨r.val + 1, hr⟩ =
        ⟨((rho r).val + 1) % N.height, Nat.mod_lt _ (by omega)⟩ := by
    exact @helper_hrho_succ_760 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@j) (@A) (@B) (@hp3) (@r) (@hr)
  let newVertex : Fin (T.length + 1) → V := fun r =>
    if hr : r.val < N.height then
      T.vertex (Fin.castLE N.height_upper (rho ⟨r.val, hr⟩))
    else
      T.vertex r
  let newEdge : Fin T.length → E := fun r =>
    if hr : r.val + 1 < N.height then
      NormalCycleEdge N (rho ⟨r.val, by omega⟩)
    else
      T.edge r
  have hvertex_prefix (r : Fin (T.length + 1)) (hr : r.val < N.height) :
      newVertex r =
        T.vertex (Fin.castLE N.height_upper (rho ⟨r.val, hr⟩)) := by
    simp [newVertex, hr]
  have hvertex_tail (r : Fin (T.length + 1)) (hr : N.height ≤ r.val) :
      newVertex r = T.vertex r := by
    simp [newVertex, show ¬ r.val < N.height by omega]
  have hedge_prefix (r : Fin T.length) (hr : r.val + 1 < N.height) :
      newEdge r = NormalCycleEdge N (rho ⟨r.val, by omega⟩) := by
    simp [newEdge, hr]
  have hedge_tail (r : Fin T.length) (hr : N.height - 1 ≤ r.val) :
      newEdge r = T.edge r := by
    have hnot : ¬ r.val + 1 < N.height := by omega
    simp [newEdge, hnot]
  have hvertex_injective : Function.Injective newVertex := by
    exact @helper_hvertex_injective_155 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@N) (@j) (@A) (@B) (@hp3) (@hrho_injective) (@hvertex_prefix)
        (@hvertex_tail)
  have hcycle_tail_ne (i : Fin N.height) (r : Fin T.length)
      (hr : N.height - 1 ≤ r.val) :
      NormalCycleEdge N i ≠ T.edge r := by
    intro heq
    obtain ⟨a, ha⟩ := T.attaches r
    have hpairs := congrArg (fun e => G.ends e) heq
    rw [hcycle_ends i, ha] at hpairs
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · have hv := congrArg Fin.val (T.vertex_injective hd.1)
      have hi := i.isLt
      simp at hv
      omega
    · have hv := congrArg Fin.val (T.vertex_injective hs.2)
      have hn := Nat.mod_lt (i.val + 1) (by omega : 0 < N.height)
      simp at hv
      omega
  have hedge_injective : Function.Injective newEdge := by
    exact @helper_hedge_injective_197 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@N) (@j) (@A) (@B) (@hp3) (@hcycle_injective) (@hrho_injective)
        (@hedge_prefix) (@hedge_tail) (@hcycle_tail_ne)
  have hfirst_edge : newEdge ⟨0, T.positive⟩ = NormalCycleEdge N j := by
    rw [hedge_prefix _ (by
      change 0 + 1 < N.height
      omega)]
    exact congrArg (NormalCycleEdge N) hrho_zero
  have htransport_index (r : Fin T.length)
      (hr : N.height - 1 ≤ r.val) (a : Fin (r.val + 1)) :
      ∃ b : Fin (r.val + 1),
        newVertex (Fin.castLT b
          (Nat.lt_trans b.isLt (Nat.succ_lt_succ r.isLt))) =
          T.vertex (Fin.castLT a
            (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt))) := by
    exact @helper_htransport_index_221 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@N) (@j) (@A) (@B) (@hp3) (@hrho_surjective) (@hvertex_prefix)
        (@hvertex_tail) (@r) (@hr) (@a)
  have hattaches : ∀ r : Fin T.length, ∃ a : Fin (r.val + 1),
      G.ends (newEdge r) =
        s(newVertex r.succ,
          newVertex (Fin.castLT a
            (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt)))) := by
    intro r
    by_cases hr : r.val + 1 < N.height
    · let a : Fin (r.val + 1) := ⟨r.val, Nat.lt_succ_self _⟩
      refine ⟨a, ?_⟩
      rw [hedge_prefix r hr, hcycle_ends,
        hvertex_prefix r.succ (by simpa using hr),
        hvertex_prefix (Fin.castLT a
          (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt))) (by
            simp [a]
            omega)]
      apply Sym2.eq_iff.mpr
      right
      constructor
      · apply congrArg T.vertex
        apply Fin.ext
        rfl
      · apply congrArg T.vertex
        apply Fin.ext
        have hs := hrho_succ ⟨r.val, by omega⟩ hr
        have hv := congrArg (fun q : Fin N.height => q.val) hs.symm
        simpa using hv
    · obtain ⟨a, ha⟩ := T.attaches r
      obtain ⟨b, hb⟩ := htransport_index r (by omega) a
      refine ⟨b, ?_⟩
      rw [hedge_tail r (by omega), ha,
        hvertex_tail r.succ (by simp; omega), hb]
  let T' : TreeSequence G (NormalCycleEdge N j) :=
    { length := T.length
      positive := T.positive
      vertex := newVertex
      edge := newEdge
      vertex_injective := hvertex_injective
      edge_injective := hedge_injective
      first_edge := hfirst_edge
      attaches := hattaches }
  have hnew_zero :
      T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩ =
        T.vertex (Fin.castLE N.height_upper j) := by
    exact @helper_hnew_zero_282 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@j) (@A) (@B) (@hp3) (@hrho_zero) (@hvertex_prefix)
        (@hvertex_injective) (@hedge_injective) (@hfirst_edge) (@hattaches)
  have hnew_one :
      T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩ =
        T.vertex (Fin.castLE N.height_upper
          ⟨(j.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩) := by
    exact @helper_hnew_one_874 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@j) (@A) (@B) (@hp3) (@hrho_val) (@hvertex_prefix)
        (@hvertex_injective) (@hedge_injective) (@hfirst_edge) (@hattaches)
  have hpair_colors :
      ({N.alpha, N.beta} : Finset (Fin k)) = {A, B} := by
    by_cases ho : Odd j.val
    · simp [hA, hB, ho, Finset.pair_comm]
    · simp [hA, hB, ho]
  exact @helper_continuation_1037 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@psi) (@T) (@N) (@j) (@hj) (@A) (@B) (@hproper) (@hone) (@hmissA) (@hmissB)
      (@hshift) (@hfixed) (@hp3) (@hcycle_injective) (@hcycle_colors) (@hrho_val)
      (@hrho_injective) (@hrho_surjective) (@hrho_zero) (@hvertex_prefix) (@hvertex_tail)
      (@hedge_prefix) (@hedge_tail) (@hvertex_injective) (@hcycle_tail_ne) (@hedge_injective)
      (@hfirst_edge) (@htransport_index) (@hattaches) (@hnew_zero) (@hnew_one) (@hpair_colors)
end GoldbergSeymour

end
