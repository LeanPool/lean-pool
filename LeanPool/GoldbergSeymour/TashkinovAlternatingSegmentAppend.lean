/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TwoColorComponent

/-!
# Tashkinov Alternating Segment Append

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private theorem helper_vMap_injective_121.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) {e0 : E} (S : TreeSequence G e0)
        (m : ℕ)
      (pathVertex : Fin (m + (1 : ℕ)) → V),
      Function.Injective pathVertex →
        (∀ (i : Fin m), pathVertex i.succ ∉ TreeSequenceVertexSet S) →
          let vMap : (t : ℕ) → t ≤ m → Fin (S.length + t + (1 : ℕ)) → V :=
            fun (t : ℕ) (ht : t ≤ m) (i : Fin (S.length + t + (1 : ℕ))) ↦
            if h : (↑i : ℕ) ≤ S.length then S.vertex (⟨(↑i : ℕ), by omega⟩ : Fin (S.length + (1 :
                ℕ)))
            else pathVertex (⟨(↑i : ℕ) - S.length, by omega⟩ : Fin (m + (1 : ℕ)));
          ∀ (t : ℕ) (ht : t ≤ m), Function.Injective (vMap t ht) := by
  classical
  intro V E G e0 S m pathVertex hvertexInjective houtside vMap t ht a b hab
  by_cases ha : a.val ≤ S.length
  · by_cases hb : b.val ≤ S.length
    · have hold : S.vertex ⟨a.val, by omega⟩ =
          S.vertex ⟨b.val, by omega⟩ := by
        simpa only [vMap, dite_eq_left ha, dite_eq_left hb] using hab
      have := congrArg Fin.val (S.vertex_injective hold)
      apply Fin.ext
      simpa using this
    · let ib : Fin m := ⟨b.val - S.length - 1, by omega⟩
      have hp : (⟨b.val - S.length, by omega⟩ : Fin (m + 1)) = ib.succ := by
        apply Fin.ext
        simp [ib]
        omega
      have hmem : S.vertex ⟨a.val, by omega⟩ ∈ TreeSequenceVertexSet S := by
        simp [TreeSequenceVertexSet]
      have hab' : S.vertex ⟨a.val, by omega⟩ =
          pathVertex ⟨b.val - S.length, by omega⟩ := by
        simpa only [vMap, dite_eq_left ha, dite_eq_right hb] using hab
      apply False.elim
      apply houtside ib
      rw [← hp]
      rw [← hab']
      exact hmem
  · by_cases hb : b.val ≤ S.length
    · let ia : Fin m := ⟨a.val - S.length - 1, by omega⟩
      have hp : (⟨a.val - S.length, by omega⟩ : Fin (m + 1)) = ia.succ := by
        apply Fin.ext
        simp [ia]
        omega
      have hmem : S.vertex ⟨b.val, by omega⟩ ∈ TreeSequenceVertexSet S := by
        simp [TreeSequenceVertexSet]
      have hab' : pathVertex ⟨a.val - S.length, by omega⟩ =
          S.vertex ⟨b.val, by omega⟩ := by
        simpa only [vMap, dite_eq_right ha, dite_eq_left hb] using hab
      apply False.elim
      apply houtside ia
      rw [← hp]
      rw [hab']
      exact hmem
    · have hnew : pathVertex ⟨a.val - S.length, by omega⟩ =
          pathVertex ⟨b.val - S.length, by omega⟩ := by
        simpa only [vMap, dite_eq_right ha, dite_eq_right hb] using hab
      have := congrArg Fin.val (hvertexInjective hnew)
      apply Fin.ext
      simp only [] at this ⊢
      omega

private theorem helper_eMap_injective_186.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) {e0 : E} (S : TreeSequence G e0)
        (m : ℕ)
      (pathEdge : Fin m → E),
      Function.Injective pathEdge →
        (∀ (i : Fin m) (j : Fin S.length), pathEdge i ≠ S.edge j) →
          let eMap : (t : ℕ) → t ≤ m → Fin (S.length + t) → E := fun (t : ℕ) (ht : t ≤ m) (i :
              Fin (S.length + t)) ↦
            if h : (↑i : ℕ) < S.length then S.edge (⟨(↑i : ℕ), h⟩ : Fin S.length)
            else pathEdge (⟨(↑i : ℕ) - S.length, by omega⟩ : Fin m);
          ∀ (t : ℕ) (ht : t ≤ m), Function.Injective (eMap t ht) := by
  classical
  intro V E G e0 S m pathEdge hedgeInjective hedgeFresh eMap t ht a b hab
  by_cases ha : a.val < S.length
  · by_cases hb : b.val < S.length
    · have hold : S.edge ⟨a.val, ha⟩ = S.edge ⟨b.val, hb⟩ := by
        simpa only [eMap, dite_eq_left ha, dite_eq_left hb] using hab
      have := congrArg Fin.val (S.edge_injective hold)
      apply Fin.ext
      simpa using this
    · have hfresh := hedgeFresh
          (⟨b.val - S.length, by omega⟩ : Fin m) (⟨a.val, ha⟩ : Fin S.length)
      exact False.elim (hfresh (by
        simpa only [eMap, dite_eq_left ha, dite_eq_right hb] using hab.symm))
  · by_cases hb : b.val < S.length
    · have hfresh := hedgeFresh
          (⟨a.val - S.length, by omega⟩ : Fin m) (⟨b.val, hb⟩ : Fin S.length)
      exact False.elim (hfresh (by
        simpa only [eMap, dite_eq_right ha, dite_eq_left hb] using hab))
    · have hnew : pathEdge ⟨a.val - S.length, by omega⟩ =
          pathEdge ⟨b.val - S.length, by omega⟩ := by
        simpa only [eMap, dite_eq_right ha, dite_eq_right hb] using hab
      have := congrArg Fin.val (hedgeInjective hnew)
      apply Fin.ext
      simp only [] at this ⊢
      omega

private theorem helper_branch_247.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) {e0 : E} (S : TreeSequence G e0)
        (m : ℕ)
      (pathVertex : Fin (m + (1 : ℕ)) → V) (pathEdge : Fin m → E),
      let vMap : (t : ℕ) → t ≤ m → Fin (S.length + t + (1 : ℕ)) → V :=
        fun (t : ℕ) (ht : t ≤ m) (i : Fin (S.length + t + (1 : ℕ))) ↦
        if h : (↑i : ℕ) ≤ S.length then S.vertex (⟨(↑i : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)))
        else pathVertex (⟨(↑i : ℕ) - S.length, by omega⟩ : Fin (m + (1 : ℕ)));
      let eMap : (t : ℕ) → t ≤ m → Fin (S.length + t) → E := fun (t : ℕ) (ht : t ≤ m) (i : Fin
          (S.length + t)) ↦
        if h : (↑i : ℕ) < S.length then S.edge (⟨(↑i : ℕ), h⟩ : Fin S.length)
        else pathEdge (⟨(↑i : ℕ) - S.length, by omega⟩ : Fin m);
      (∀ (t : ℕ) (ht : t ≤ m) (i : Fin (S.length + (1 : ℕ))), vMap t ht (Fin.castLE (by omega) i)
          = S.vertex i) →
        ∀ (t : ℕ) (ht : t ≤ m) (j : Fin (S.length + t)),
          (↑j : ℕ) < S.length →
            ∃ (i : Fin ((↑j : ℕ) + (1 : ℕ))), G.ends (eMap t ht j) = s(vMap t ht j.succ, vMap t
                ht (i.castLT (by omega))) := by
  classical
  intro V E G e0 S m pathVertex pathEdge vMap eMap vMap_old t ht j hj
  let jo : Fin S.length := ⟨j.val, hj⟩
  rcases S.attaches jo with ⟨i, hi⟩
  let ii : Fin (j.val + 1) := ⟨i.val, by simpa [jo] using i.isLt⟩
  refine ⟨ii, ?_⟩
  rw [show eMap t ht j = S.edge jo by
    simp only [eMap, dite_eq_left hj]; congr]
  rw [hi]
  have hleV : S.length + 1 ≤ S.length + t + 1 := by omega
  have hjEq : j.succ = Fin.castLE hleV jo.succ := by
    apply Fin.ext
    rfl
  have hiEq : Fin.castLT ii (by omega) = Fin.castLE hleV
      (Fin.castLT i (Nat.lt_trans i.isLt
        (Nat.succ_lt_succ jo.isLt))) := by
    apply Fin.ext
    rfl
  rw [hjEq, vMap_old t ht, hiEq, vMap_old t ht]

private theorem helper_vMap_new_244.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) {e0 : E} (S : TreeSequence G e0)
        (m : ℕ) (pathVertex : Fin (m + (1 : ℕ)) → V),
    let vMap : (t : ℕ) → t ≤ m → Fin (S.length + t + (1 : ℕ)) → V := fun (t : ℕ) (ht : t ≤ m) (i :
        Fin (S.length + t + (1 : ℕ))) ↦ if h : (↑i : ℕ) ≤ S.length then S.vertex (⟨(↑i : ℕ),
    by
              omega
    ⟩ : Fin (S.length + (1 : ℕ))) else pathVertex (⟨(↑i : ℕ) - S.length,
    by
              omega
    ⟩ : Fin (m + (1 : ℕ)));
    ∀ (t : ℕ) (ht : t ≤ m) (i : Fin t), vMap t ht (⟨S.length + (↑i : ℕ) + (1 : ℕ),
    by
            omega
    ⟩ : Fin (S.length + t + (1 : ℕ))) = pathVertex (Fin.castLE (Nat.succ_le_succ ht) i.succ) := by
  classical
  intro V E G e0 S m pathVertex vMap t ht i
  change (if h : S.length + i.val + 1 ≤ S.length then
      S.vertex ⟨S.length + i.val + 1, by omega⟩
    else pathVertex ⟨S.length + i.val + 1 - S.length, by omega⟩) = _
  rw [dite_eq_right (by omega)]
  congr
  simp only [Fin.val_succ]
  omega

private theorem helper_eMap_new_254.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) {e0 : E} (S : TreeSequence G e0)
        (m : ℕ) (pathEdge : Fin m → E),
    let eMap : (t : ℕ) → t ≤ m → Fin (S.length + t) → E := fun (t : ℕ) (ht : t ≤ m) (i : Fin
        (S.length + t)) ↦ if h : (↑i : ℕ) < S.length then S.edge (⟨(↑i : ℕ), h⟩ : Fin S.length)
        else pathEdge (⟨(↑i : ℕ) - S.length,
    by
              omega
    ⟩ : Fin m);
    ∀ (t : ℕ) (ht : t ≤ m) (i : Fin t), eMap t ht (⟨S.length + (↑i : ℕ),
    by
            omega
    ⟩ : Fin (S.length + t)) = pathEdge (Fin.castLE ht i) := by
  classical
  intro V E G e0 S m pathEdge eMap t ht i
  change (if h : S.length + i.val < S.length then
      S.edge ⟨S.length + i.val, h⟩
    else pathEdge ⟨S.length + i.val - S.length, by omega⟩) = _
  rw [dite_eq_right (by omega)]
  congr
  omega

private abbrev helperFirstEdge354Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) {e0 : E} (S : TreeSequence G e0)
   (m : ℕ) (pathEdge : Fin m → E),
   let eMap : (t : ℕ) → (ht : t ≤ m) → Fin (S.length + t) → E :=
    fun (t : ℕ) (ht : t ≤ m) (i : Fin (S.length + t)) ↦
    if h : (↑i : ℕ) < S.length then S.edge (⟨(↑i : ℕ), h⟩ : Fin S.length)
    else pathEdge (⟨(↑i : ℕ) - S.length, by omega⟩ : Fin m);
   ∀
    (eMap_old :
     ∀ (t : ℕ) (ht : t ≤ m) (i : Fin S.length), eMap t ht (Fin.castLE (by omega) i) = S.edge i)
    (t : ℕ) (ht : t ≤ m),
    eMap t ht
      (⟨(0 : ℕ),
        have this : (1 : ℕ) ≤ S.length := S.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ S.length + t) ↦ by omega⟩ :
       Fin (S.length + t)) =
     e0

private theorem helper_first_edge_354.{u_1, u_2} :
    helperFirstEdge354Conditions.{u_1, u_2} := by
  classical
  intro V E G e0 S m pathEdge eMap eMap_old t ht
  have hzero : (⟨0, by have := S.positive; omega⟩ : Fin (S.length + t)) =
      Fin.castLE (by omega) (⟨0, S.positive⟩ : Fin S.length) := by
    apply Fin.ext
    rfl
  rw [hzero, eMap_old t ht]
  exact S.first_edge

private noncomputable abbrev helperExtend398.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
        {E : Type u_2} →
          (G : LooplessMultigraph V E) →
            {e0 : E} →
              (S : TreeSequence G e0) →
                (m : ℕ) →
                  (pathVertex : Fin (m + (1 : ℕ)) → V) →
                    (pathEdge : Fin m → E) →
                      (hends :
                          ∀ (i : Fin m),
                            G.ends (pathEdge i) = s(pathVertex i.castSucc, pathVertex i.succ)) →
                        let vMap : (t : ℕ) → (ht : t ≤ m) → Fin (S.length + t + (1 : ℕ)) → V :=
                          fun (t : ℕ) (ht : t ≤ m) (i : Fin (S.length + t + (1 : ℕ))) ↦
                          if h : (↑i : ℕ) ≤ S.length then
                            S.vertex (⟨(↑i : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)))
                          else pathVertex (⟨(↑i : ℕ) - S.length, by omega⟩ : Fin (m + (1 : ℕ)));
                        let eMap : (t : ℕ) → (ht : t ≤ m) → Fin (S.length + t) → E :=
                          fun (t : ℕ) (ht : t ≤ m) (i : Fin (S.length + t)) ↦
                          if h : (↑i : ℕ) < S.length then S.edge (⟨(↑i : ℕ), h⟩ : Fin S.length)
                          else pathEdge (⟨(↑i : ℕ) - S.length, by omega⟩ : Fin m);
                        (vMap_old :
                            ∀ (t : ℕ) (ht : t ≤ m) (i : Fin (S.length + (1 : ℕ))),
                              vMap t ht (Fin.castLE (by omega) i) = S.vertex i) →
                          (eMap_old :
                              ∀ (t : ℕ) (ht : t ≤ m) (i : Fin S.length),
                                eMap t ht (Fin.castLE (by omega) i) = S.edge i) →
                            (vMap_new :
                                ∀ (t : ℕ) (ht : t ≤ m) (i : Fin t),
                                  vMap t ht
                                      (⟨S.length + (↑i : ℕ) + (1 : ℕ), by omega⟩ :
                                        Fin (S.length + t + (1 : ℕ))) =
                                    pathVertex (Fin.castLE (Nat.succ_le_succ ht) i.succ)) →
                              (eMap_new :
                                  ∀ (t : ℕ) (ht : t ≤ m) (i : Fin t),
                                    eMap t ht
                                        (⟨S.length + (↑i : ℕ), by omega⟩ : Fin (S.length + t)) =
                                      pathEdge (Fin.castLE ht i)) →
                                (vMap_injective :
                                    ∀ (t : ℕ) (ht : t ≤ m), Function.Injective (vMap t ht)) →
                                  (eMap_injective :
                                      ∀ (t : ℕ) (ht : t ≤ m), Function.Injective (eMap t ht)) →
                                    (hstart_index :
                                        ∃ (q : Fin (S.length + (1 : ℕ))),
                                          S.vertex q = pathVertex (0 : Fin (m + (1 : ℕ)))) →
                                      (t : ℕ) → (ht : t ≤ m) → TreeSequence G e0 := by
  classical
  intro V E G e0 S m pathVertex pathEdge hends vMap eMap vMap_old eMap_old vMap_new eMap_new
      vMap_injective eMap_injective hstart_index t ht
  exact {
    length := S.length + t
    positive := by have := S.positive; omega
    vertex := vMap t ht
    edge := eMap t ht
    vertex_injective := vMap_injective t ht
    edge_injective := eMap_injective t ht
    first_edge := by
      exact @helper_first_edge_354 (@V) (@E) (@G) (@e0) (@S) (@m) (@pathEdge) (@eMap_old) (@t) (@ht)
    attaches := by
      intro j
      by_cases hj : j.val < S.length
      · exact @helper_branch_247 (@V) (@E) (@G) (@e0) (@S) (@m) (@pathVertex) (@pathEdge)
          (@vMap_old) (@t) (@ht) (@j) (@hj)
      · let p : Fin t := ⟨j.val - S.length, by omega⟩
        have hjpos : S.length ≤ j.val := by omega
        have hjform : j.val = S.length + p.val := by
          simp [p]
          omega
        rw [show eMap t ht j = pathEdge (Fin.castLE ht p) by
          rw [show j = (⟨S.length + p.val, by omega⟩ : Fin (S.length + t)) by
            apply Fin.ext
            exact hjform]
          exact eMap_new t ht p]
        rw [hends (Fin.castLE ht p)]
        by_cases hp : p.val = 0
        · rcases hstart_index with ⟨q, hq⟩
          let ii : Fin (j.val + 1) := ⟨q.val, by omega⟩
          refine ⟨ii, ?_⟩
          have hjSuccEq : j.succ =
              (⟨S.length + p.val + 1, by omega⟩ : Fin (S.length + t + 1)) := by
            apply Fin.ext
            simpa using congrArg Nat.succ hjform
          have htarget : vMap t ht j.succ =
              pathVertex (Fin.castLE ht p).succ := by
            rw [hjSuccEq, vMap_new t ht p]
            have hidx : Fin.castLE (Nat.succ_le_succ ht) p.succ =
                (Fin.castLE ht p).succ := by
              apply Fin.ext
              rfl
            rw [hidx]
          have hleV : S.length + 1 ≤ S.length + t + 1 := by omega
          have hiEq : Fin.castLT ii (by omega) = Fin.castLE hleV q := by
            apply Fin.ext
            rfl
          have hatt : vMap t ht (Fin.castLT ii (by omega)) =
              pathVertex (Fin.castLE ht p).castSucc := by
            rw [hiEq, vMap_old t ht, hq]
            have hidx : (0 : Fin (m + 1)) = (Fin.castLE ht p).castSucc := by
              apply Fin.ext
              simp [hp]
            rw [hidx]
          rw [htarget, hatt]
          exact Sym2.eq_swap
        · let pp : Fin t := ⟨p.val - 1, by omega⟩
          let ii : Fin (j.val + 1) := ⟨j.val, Nat.lt_succ_self _⟩
          refine ⟨ii, ?_⟩
          have hjSuccEq : j.succ =
              (⟨S.length + p.val + 1, by omega⟩ : Fin (S.length + t + 1)) := by
            apply Fin.ext
            simpa using congrArg Nat.succ hjform
          have htarget : vMap t ht j.succ =
              pathVertex (Fin.castLE ht p).succ := by
            rw [hjSuccEq, vMap_new t ht p]
            have hidx : Fin.castLE (Nat.succ_le_succ ht) p.succ =
                (Fin.castLE ht p).succ := by
              apply Fin.ext
              rfl
            rw [hidx]
          have hiEq : Fin.castLT ii (by omega) =
              (⟨S.length + pp.val + 1, by omega⟩ : Fin (S.length + t + 1)) := by
            apply Fin.ext
            simp [ii, pp]
            omega
          have hatt : vMap t ht (Fin.castLT ii (by omega)) =
              pathVertex (Fin.castLE ht p).castSucc := by
            rw [hiEq, vMap_new t ht pp]
            have hidx : Fin.castLE (Nat.succ_le_succ ht) pp.succ =
                (Fin.castLE ht p).castSucc := by
              apply Fin.ext
              simp [pp]
              omega
            rw [hidx]
          rw [htarget, hatt]
          exact Sym2.eq_swap }

private theorem helper_continuation_699.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Finite V] [ Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (phi : PartialEdgeColoring E k) (S : TreeSequence G e0) (alpha beta : Fin k) (y :
        V) (m : ℕ) (_ : (1 : ℕ) ≤ m) (pathVertex : Fin (m + (1 : ℕ)) → V) (pathEdge : Fin m → E)
        (_ :
    ∀ (i : Fin m), pathVertex i.succ ∉ TreeSequenceVertexSet S) (_ :
    ∀ (i : Fin (m + (1 : ℕ))), Sum.inl (pathVertex i) ∈ TwoColorComponent G phi alpha beta
        (Sum.inl y)) (_ :
    ∀ (i : Fin m), Sum.inr (pathEdge i) ∈ TwoColorComponent G phi alpha beta (Sum.inl y)) (_ :
    ∀ (i : Fin m), phi (pathEdge i) = some alpha ∨ phi (pathEdge i) = some beta) (hends :
    ∀ (i : Fin m), G.ends (pathEdge i) = s(pathVertex i.castSucc, pathVertex i.succ)),
    let vMap : (t : ℕ) → (ht : t ≤ m) → Fin (S.length + t + (1 : ℕ)) → V := fun (t : ℕ) (ht : t ≤
        m) (i : Fin (S.length + t + (1 : ℕ))) ↦ if h : (↑i : ℕ) ≤ S.length then S.vertex (⟨(↑i :
        ℕ),
    by
              omega
    ⟩ : Fin (S.length + (1 : ℕ))) else pathVertex (⟨(↑i : ℕ) - S.length,
    by
              omega
    ⟩ : Fin (m + (1 : ℕ)));
    let eMap : (t : ℕ) → (ht : t ≤ m) → Fin (S.length + t) → E := fun (t : ℕ) (ht : t ≤ m) (i :
        Fin (S.length + t)) ↦ if h : (↑i : ℕ) < S.length then S.edge (⟨(↑i : ℕ), h⟩ : Fin
        S.length) else pathEdge (⟨(↑i : ℕ) - S.length,
    by
              omega
    ⟩ : Fin m);
    ∀ (vMap_old :
    ∀ (t : ℕ) (ht : t ≤ m) (i : Fin (S.length + (1 : ℕ))), vMap t ht (Fin.castLE (
    by
                  omega
    ) i) = S.vertex i) (eMap_old :
    ∀ (t : ℕ) (ht : t ≤ m) (i : Fin S.length), eMap t ht (Fin.castLE (
    by
                  omega
    ) i) = S.edge i) (vMap_new :
    ∀ (t : ℕ) (ht : t ≤ m) (i : Fin t), vMap t ht (⟨S.length + (↑i : ℕ) + (1 : ℕ),
    by
                  omega
    ⟩ : Fin (S.length + t + (1 : ℕ))) = pathVertex (Fin.castLE (Nat.succ_le_succ ht) i.succ))
        (eMap_new :
    ∀ (t : ℕ) (ht : t ≤ m) (i : Fin t), eMap t ht (⟨S.length + (↑i : ℕ),
    by
                  omega
    ⟩ : Fin (S.length + t)) = pathEdge (Fin.castLE ht i)) (vMap_injective :
    ∀ (t : ℕ) (ht : t ≤ m), Function.Injective (vMap t ht)) (eMap_injective :
    ∀ (t : ℕ) (ht : t ≤ m), Function.Injective (eMap t ht)) (hstart_index :
    ∃ (q : Fin (S.length + (1 : ℕ))), S.vertex q = pathVertex (0 : Fin (m + (1 : ℕ)))),
    let extend : (t : ℕ) → (ht : t ≤ m) → TreeSequence G e0 := fun (t : ℕ) (ht : t ≤ m) ↦
        helperExtend398 G S m pathVertex pathEdge hends vMap_old eMap_old vMap_new eMap_new
        vMap_injective eMap_injective hstart_index t ht;
    ∀ (_ :
    ∀ (t : ℕ) (ht : t ≤ m), TreeSequenceInitialSegment S (extend t ht)) (_ :
    ∀ (t : ℕ) (_ : (1 : ℕ) ≤ t) (ht : t ≤ m), TashkinovAugmentationSequence phi S (extend t ht)),
    let _ : TreeSequence G e0 := extend m le_rfl;
    ∃ (S' : TreeSequence G e0), TreeSequenceInitialSegment S S' ∧ S'.length = S.length + m ∧ (
    ∀ (i : Fin m),
    ∃ (r : Fin S'.length), (↑r : ℕ) = S.length + (↑i : ℕ) ∧ S'.edge r = pathEdge i ∧ S'.vertex
        r.succ = pathVertex i.succ) ∧ S.length < S'.length ∧ TashkinovAugmentationSequence phi S
        S' ∧ S'.vertex (Fin.last S'.length) = pathVertex (Fin.last m) ∧
    ∀ (r : Fin S'.length), S.length ≤ (↑r : ℕ) → S'.vertex r.succ ∉ TreeSequenceVertexSet S ∧
        Sum.inr (S'.edge r) ∈ TwoColorComponent G phi alpha beta (Sum.inl y) ∧ Sum.inl (S'.vertex
        r.succ) ∈ TwoColorComponent G phi alpha beta (Sum.inl y) ∧ (phi (S'.edge r) = some alpha ∨
        phi (S'.edge r) = some beta) ∧ G.ends (S'.edge r) = if (↑r : ℕ) = S.length then
        s(pathVertex (0 : Fin (m + (1 : ℕ))), S'.vertex r.succ) else s(S'.vertex r.castSucc,
        S'.vertex r.succ) := by
  classical
  intro V E _ _ G k e0 phi S alpha beta y m hm pathVertex pathEdge houtside hvertexComponent
      hedgeComponent hcolors hends vMap eMap vMap_old eMap_old vMap_new eMap_new vMap_injective
      eMap_injective hstart_index extend initial_from_old augmentation_from_one S'
  let _ := Fintype.ofFinite V
  refine ⟨S', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact initial_from_old m le_rfl
  · simp only [S', extend]
  · intro i
    let r : Fin S'.length := ⟨S.length + i.val, by
      simp only [S', extend]
      omega⟩
    refine ⟨r, by simp [r], ?_, ?_⟩
    · change eMap m le_rfl r = pathEdge i
      have hr : r = (⟨S.length + i.val, by omega⟩ : Fin (S.length + m)) := by
        apply Fin.ext
        rfl
      rw [hr, eMap_new m le_rfl i]
      congr
    · change vMap m le_rfl r.succ = pathVertex i.succ
      have hr : r.succ =
          (⟨S.length + i.val + 1, by omega⟩ : Fin (S.length + m + 1)) := by
        apply Fin.ext
        rfl
      rw [hr, vMap_new m le_rfl i]
      congr
  · simp only [S', extend]
    omega
  · exact augmentation_from_one m hm le_rfl
  · let i : Fin m := ⟨m - 1, by omega⟩
    change vMap m le_rfl (Fin.last (S.length + m)) = pathVertex (Fin.last m)
    have hlast : Fin.last (S.length + m) =
        (⟨S.length + i.val + 1, by omega⟩ : Fin (S.length + m + 1)) := by
      apply Fin.ext
      simp [i]
      omega
    rw [hlast, vMap_new m le_rfl i]
    congr
    apply Fin.ext
    simp [i]
    omega
  · intro r hr
    let i : Fin m := ⟨r.val - S.length, by
      have hrlt := r.isLt
      change r.val < S.length + m at hrlt
      omega⟩
    have hrform : r.val = S.length + i.val := by
      simp [i]
      omega
    have hedge : S'.edge r = pathEdge i := by
      change eMap m le_rfl r = pathEdge i
      rw [show r = (⟨S.length + i.val, by omega⟩ : Fin (S.length + m)) by
        apply Fin.ext
        exact hrform]
      rw [eMap_new m le_rfl i]
      congr
    have hvertex : S'.vertex r.succ = pathVertex i.succ := by
      change vMap m le_rfl r.succ = pathVertex i.succ
      rw [show r.succ =
          (⟨S.length + i.val + 1, by omega⟩ : Fin (S.length + m + 1)) by
        apply Fin.ext
        simpa using congrArg Nat.succ hrform]
      rw [vMap_new m le_rfl i]
      congr
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hvertex]
      exact houtside i
    · rw [hedge]
      exact hedgeComponent i
    · rw [hvertex]
      exact hvertexComponent i.succ
    · rw [hedge]
      exact hcolors i
    · rw [hedge, hends i]
      by_cases hfirst : r.val = S.length
      · rw [ite_eq_left hfirst, hvertex]
        congr
        apply Fin.ext
        simp [i]
        omega
      · rw [ite_eq_right hfirst, hvertex]
        have hprev : S'.vertex r.castSucc = pathVertex i.castSucc := by
          change vMap m le_rfl r.castSucc = pathVertex i.castSucc
          have hlarge : ¬r.val ≤ S.length := by omega
          simp only [vMap, Fin.val_castSucc, dite_eq_right hlarge]
          congr
        rw [hprev]

theorem TashkinovAlternatingSegmentAppend
    {V E : Type*}
    [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (S : TreeSequence G e0)
    (alpha beta : Fin k) (y : V)
    (m : Nat) (hm : 1 ≤ m)
    (pathVertex : Fin (m + 1) → V) (pathEdge : Fin m → E)
    (hvertexInjective : Function.Injective pathVertex)
    (hedgeInjective : Function.Injective pathEdge)
    (hstart : pathVertex 0 ∈ TreeSequenceVertexSet S)
    (houtside : ∀ i : Fin m,
      pathVertex i.succ ∉ TreeSequenceVertexSet S)
    (hvertexComponent : ∀ i : Fin (m + 1),
      Sum.inl (pathVertex i) ∈
        TwoColorComponent G phi alpha beta (Sum.inl y))
    (hedgeComponent : ∀ i : Fin m,
      Sum.inr (pathEdge i) ∈
        TwoColorComponent G phi alpha beta (Sum.inl y))
    (hcolors : ∀ i : Fin m,
      phi (pathEdge i) = some alpha ∨
        phi (pathEdge i) = some beta)
    (hends : ∀ i : Fin m,
      G.ends (pathEdge i) =
        s(pathVertex i.castSucc, pathVertex i.succ))
    (hedgeFresh : ∀ i : Fin m, ∀ j : Fin S.length,
      pathEdge i ≠ S.edge j)
    (halpha : alpha ∈ TreeMissingColors phi S)
    (hbeta : beta ∈ TreeMissingColors phi S) :
    ∃ S' : TreeSequence G e0,
      TreeSequenceInitialSegment S S' ∧
        S'.length = S.length + m ∧
        (∀ i : Fin m, ∃ r : Fin S'.length,
          r.val = S.length + i.val ∧
            S'.edge r = pathEdge i ∧
            S'.vertex r.succ = pathVertex i.succ) ∧
        S.length < S'.length ∧
        TashkinovAugmentationSequence phi S S' ∧
        S'.vertex (Fin.last S'.length) = pathVertex (Fin.last m) ∧
        ∀ r : Fin S'.length, S.length ≤ r.val →
          S'.vertex r.succ ∉ TreeSequenceVertexSet S ∧
            Sum.inr (S'.edge r) ∈
              TwoColorComponent G phi alpha beta (Sum.inl y) ∧
            Sum.inl (S'.vertex r.succ) ∈
              TwoColorComponent G phi alpha beta (Sum.inl y) ∧
            (phi (S'.edge r) = some alpha ∨
              phi (S'.edge r) = some beta) ∧
            G.ends (S'.edge r) =
              if r.val = S.length then
                s(pathVertex 0, S'.vertex r.succ)
              else
                s(S'.vertex r.castSucc, S'.vertex r.succ) := by
  classical
  let _ := Fintype.ofFinite V
  let vMap (t : Nat) (ht : t ≤ m) : Fin (S.length + t + 1) → V := fun i =>
    if h : i.val ≤ S.length then
      S.vertex ⟨i.val, by omega⟩
    else
      pathVertex ⟨i.val - S.length, by omega⟩
  let eMap (t : Nat) (ht : t ≤ m) : Fin (S.length + t) → E := fun i =>
    if h : i.val < S.length then
      S.edge ⟨i.val, h⟩
    else
      pathEdge ⟨i.val - S.length, by omega⟩
  have vMap_old (t : Nat) (ht : t ≤ m) (i : Fin (S.length + 1)) :
      vMap t ht (Fin.castLE (by omega) i) = S.vertex i := by
    change (if h : i.val ≤ S.length then S.vertex ⟨i.val, by omega⟩
      else pathVertex ⟨i.val - S.length, by omega⟩) = S.vertex i
    rw [dite_eq_left (by omega)]
  have eMap_old (t : Nat) (ht : t ≤ m) (i : Fin S.length) :
      eMap t ht (Fin.castLE (by omega) i) = S.edge i := by
    change (if h : i.val < S.length then S.edge ⟨i.val, h⟩
      else pathEdge ⟨i.val - S.length, by omega⟩) = S.edge i
    rw [dite_eq_left i.isLt]
  have vMap_new := @helper_vMap_new_244 (@V) (@E) (@G) (@e0) (@S) (@m) (@pathVertex)
  have eMap_new := @helper_eMap_new_254 (@V) (@E) (@G) (@e0) (@S) (@m) (@pathEdge)
  have vMap_injective := @helper_vMap_injective_121 (@V) (@E) (@G) (@e0) (@S) (@m) (@pathVertex)
      (@hvertexInjective) (@houtside)
  have eMap_injective := @helper_eMap_injective_186 (@V) (@E) (@G) (@e0) (@S) (@m) (@pathEdge)
      (@hedgeInjective) (@hedgeFresh)
  have hstart_index : ∃ q : Fin (S.length + 1), S.vertex q = pathVertex 0 := by
    simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] using hstart
  let extend := @helperExtend398 (@V) (@E) (@G) (@e0) (@S) (@m) (@pathVertex) (@pathEdge) (@hends)
      (@vMap_old) (@eMap_old) (@vMap_new) (@eMap_new) (@vMap_injective) (@eMap_injective)
      (@hstart_index)
  have extend_initial (a b : Nat) (ha : a ≤ m) (hb : b ≤ m) (hab : a ≤ b) :
      TreeSequenceInitialSegment (extend a ha) (extend b hb) := by
    refine ⟨by simp only [extend]; omega, ?_, ?_⟩
    · intro i
      change Fin (S.length + a + 1) at i
      have hleV : S.length + a + 1 ≤ S.length + b + 1 := by omega
      change vMap b hb (Fin.castLE hleV i) = vMap a ha i
      by_cases hi : i.val ≤ S.length
      · have hi' : (Fin.castLE hleV i).val ≤
            S.length := hi
        simp only [vMap, Fin.val_castLE, dite_eq_left hi', dite_eq_left hi]
      · have hi' : ¬(Fin.castLE hleV i).val ≤
            S.length := hi
        simp only [vMap, Fin.val_castLE, dite_eq_right hi', dite_eq_right hi]
    · intro i
      change Fin (S.length + a) at i
      have hleE : S.length + a ≤ S.length + b := by omega
      change eMap b hb (Fin.castLE hleE i) = eMap a ha i
      by_cases hi : i.val < S.length
      · have hi' : (Fin.castLE hleE i).val <
            S.length := hi
        simp only [eMap, Fin.val_castLE, dite_eq_left hi', dite_eq_left hi]
      · have hi' : ¬(Fin.castLE hleE i).val <
            S.length := hi
        simp only [eMap, Fin.val_castLE, dite_eq_right hi', dite_eq_right hi]
  have initial_from_old (t : Nat) (ht : t ≤ m) :
      TreeSequenceInitialSegment S (extend t ht) := by
    refine ⟨by simp only [extend]; omega, ?_, ?_⟩
    · intro i
      change vMap t ht (Fin.castLE (by omega) i) = S.vertex i
      exact vMap_old t ht i
    · intro i
      change eMap t ht (Fin.castLE (by omega) i) = S.edge i
      exact eMap_old t ht i
  have old_missing (t : Nat) (ht : t ≤ m) (c : Fin k)
      (hc : c ∈ TreeMissingColors phi S) :
      c ∈ TreeMissingColors phi (extend t ht) := by
    rcases initial_from_old t ht with ⟨hlen0, hv0, he0⟩
    simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
    rcases hc with ⟨v, hvS, hcv⟩
    refine ⟨v, ?_, hcv⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hvS ⊢
    rcases hvS with ⟨i, -, rfl⟩
    refine ⟨Fin.castLE (by simp only [extend]; omega) i, Finset.mem_univ _, ?_⟩
    exact hv0 i
  have augmentation_step (t : Nat) (ht : t ≤ m) (hsucc : t + 1 ≤ m) :
      TashkinovAugmentation phi (extend t ht) (extend (t + 1) hsucc) := by
    have hlen : (extend (t + 1) hsucc).length = (extend t ht).length + 1 := by
      simp only [extend]
      omega
    refine ⟨hlen, extend_initial t (t + 1) ht hsucc (by omega), ?_⟩
    let p : Fin m := ⟨t, by omega⟩
    have hedge : (extend (t + 1) hsucc).edge
          (Fin.cast hlen.symm (Fin.last (extend t ht).length)) = pathEdge p := by
      change eMap (t + 1) hsucc
          (Fin.cast hlen.symm (Fin.last (S.length + t))) = pathEdge p
      have hindex : Fin.cast hlen.symm (Fin.last (S.length + t)) =
          (⟨S.length + t, by omega⟩ : Fin (S.length + (t + 1))) := by
        apply Fin.ext
        rfl
      rw [hindex]
      have hlocal : (⟨t, by omega⟩ : Fin (t + 1)) =
          (⟨t, Nat.lt_succ_self t⟩ : Fin (t + 1)) := by rfl
      rw [show eMap (t + 1) hsucc ⟨S.length + t, by omega⟩ =
          pathEdge (Fin.castLE hsucc ⟨t, Nat.lt_succ_self t⟩) by
        exact eMap_new (t + 1) hsucc ⟨t, Nat.lt_succ_self t⟩]
      congr
    rcases hcolors p with hp | hp
    · exact ⟨alpha, (congrArg phi hedge).trans hp,
        old_missing t ht alpha halpha⟩
    · exact ⟨beta, (congrArg phi hedge).trans hp,
        old_missing t ht beta hbeta⟩
  have augmentation_first :
      TashkinovAugmentation phi S (extend 1 (by omega)) := by
    have hlen : (extend 1 (by omega)).length = S.length + 1 := by
      simp only [extend]
    refine ⟨hlen, initial_from_old 1 (by omega), ?_⟩
    let p : Fin m := ⟨0, hm⟩
    have hedge : (extend 1 (by omega)).edge
          (Fin.cast hlen.symm (Fin.last S.length)) = pathEdge p := by
      change eMap 1 (by omega)
          (Fin.cast hlen.symm (Fin.last S.length)) = pathEdge p
      have hindex : Fin.cast hlen.symm (Fin.last S.length) =
          (⟨S.length, by omega⟩ : Fin (S.length + 1)) := by
        apply Fin.ext
        rfl
      rw [hindex]
      rw [show eMap 1 (by omega) ⟨S.length, by omega⟩ =
          pathEdge (Fin.castLE (by omega) (0 : Fin 1)) by
        exact eMap_new 1 (by omega) 0]
      congr
    rcases hcolors p with hp | hp
    · exact ⟨alpha, (congrArg phi hedge).trans hp, halpha⟩
    · exact ⟨beta, (congrArg phi hedge).trans hp, hbeta⟩
  have augmentation_from_one (t : Nat) (htpos : 1 ≤ t) (ht : t ≤ m) :
      TashkinovAugmentationSequence phi S (extend t ht) := by
    induction t with
    | zero => omega
    | succ t ih =>
        by_cases htzero : t = 0
        · subst t
          exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
            augmentation_first
        · have htpos' : 1 ≤ t := by omega
          have ht' : t ≤ m := by omega
          exact Relation.ReflTransGen.tail (ih htpos' ht')
            (augmentation_step t ht' (by omega))
  let S' := extend m le_rfl
  exact @helper_continuation_699 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi)
      (@S) (@alpha) (@beta) (@y) (@m) (@hm) (@pathVertex) (@pathEdge) (@houtside)
      (@hvertexComponent) (@hedgeComponent) (@hcolors) (@hends) (@vMap_old) (@eMap_old)
      (@vMap_new) (@eMap_new) (@vMap_injective) (@eMap_injective) (@hstart_index)
      (@initial_from_old) (@augmentation_from_one)
end GoldbergSeymour

end
