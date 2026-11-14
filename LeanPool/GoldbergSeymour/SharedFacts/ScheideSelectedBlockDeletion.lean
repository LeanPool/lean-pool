/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideReducedConfiguration

/-!
# Shared facts for ScheideSelectedBlockDeletion

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ScheideSelectedBlockDeletion

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev edgeClassGlobalStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
        (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s) (hi : (↑i : ℕ) < C.s)
        (hp : (2 : ℕ) ≤ C.p) (hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s)
        (hn : (3 : ℕ) ≤ T.length),
      let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
      let d : ℕ := C.p - (1 : ℕ) + (2 : ℕ) * (↑i : ℕ);
      let rV : Fin (T.length - (2 : ℕ) + (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
        fun (q : Fin (T.length - (2 : ℕ) + (1 : ℕ))) =>
        if h : (↑q : ℕ) < m then
          (⟨(↑q : ℕ),
              Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) => by
                omega⟩ :
            Fin (T.length + (1 : ℕ)))
        else
          (⟨(↑q : ℕ) + (2 : ℕ),
              Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) =>
                by omega⟩ :
            Fin (T.length + (1 : ℕ)));
      let rE : Fin (T.length - (2 : ℕ)) → Fin T.length :=
        fun (q : Fin (T.length - (2 : ℕ))) =>
        if _ : (↑q : ℕ) < d then
          (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) => by omega⟩ :
            Fin T.length)
        else
          (⟨(↑q : ℕ) + (2 : ℕ),
              Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) => by
                omega⟩ :
            Fin T.length);
      (∀ (q : Fin (T.length - (2 : ℕ))),
          (↑(rE q) : ℕ) = if (↑q : ℕ) < d then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
      m + (1 : ℕ) ≤ T.length →
      d + (1 : ℕ) < T.length →
      ∀
        (hfirst :
          rE
              (⟨(0 : ℕ),
                  Decidable.byContradiction fun (a : ¬(0 : ℕ) < T.length - (2 : ℕ)) => by
                    omega⟩ :
                Fin (T.length - (2 : ℕ))) =
            (⟨(0 : ℕ), T.positive⟩ : Fin T.length)),
      let nv : Fin (T.length - (2 : ℕ) + (1 : ℕ)) → V :=
        fun (q : Fin (T.length - (2 : ℕ) + (1 : ℕ))) => T.vertex (rV q);
      let ne : Fin (T.length - (2 : ℕ)) → E := fun (q : Fin (T.length - (2 : ℕ))) =>
        T.edge (rE q);
      ∀ (nv_inj : Function.Injective nv) (ne_inj : Function.Injective ne)
        (hatt :
          ∀ (q : Fin (T.length - (2 : ℕ))),
            ∃ (a : Fin ((↑q : ℕ) + (1 : ℕ))),
              G.ends (ne q) =
                s(nv q.succ, nv (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))))),
      let S : TreeSequence G e0 :=
        { length := T.length - (2 : ℕ),
          positive :=
            Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (2 : ℕ)) => by omega,
          vertex := nv, edge := ne, vertex_injective := nv_inj, edge_injective := ne_inj,
          first_edge :=
            have he :
              rE
                  (⟨(0 : ℕ),
                      Decidable.byContradiction fun (a : ¬(0 : ℕ) < T.length - (2 : ℕ)) => by
                        omega⟩ :
                    Fin (T.length - (2 : ℕ))) =
                (⟨(0 : ℕ), T.positive⟩ : Fin T.length) :=
              hfirst;
            id
              (Eq.mpr (id (congrArg (fun (_a : Fin T.length) => T.edge _a = e0) he))
                T.first_edge),
          attaches := hatt : TreeSequence G e0 };
      ∀ (q : Fin (T.length - (2 : ℕ))),
      (∃ (a : Fin (C.p - (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ S.edge q = C.baseEdge a) ∨
        ∃ (r : Fin C.s) (j : Fin (2 : ℕ)),
          r ≠ i ∧ C.p - (1 : ℕ) ≤ (↑q : ℕ) ∧ S.edge q = C.blockEdge r j

/-- A common proof used by the branches of this transport or construction argument. -/
theorem edge_class_global.{u_1, u_2} : edgeClassGlobalStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T C i hi hp hl hn m d rV rE rE_val hm hd hfirst nv ne nv_inj ne_inj
      hatt S q
  by_cases hq : q.val < d
  · by_cases hb : q.val < C.p - 1
    · left
      refine ⟨⟨q.val, hb⟩, rfl, ?_⟩
      have he : rE q = ⟨q.val, by omega⟩ := by
        apply Fin.ext
        rw [rE_val]
        simp [hq]
      change T.edge (rE q) = C.baseEdge ⟨q.val, hb⟩
      rw [he]
      exact C.base_edge_position ⟨q.val, hb⟩
    · right
      let x := q.val - (C.p - 1)
      let rr := x / 2
      let jj := x % 2
      have hx : q.val = C.p - 1 + x := by dsimp [x]; omega
      have hj : jj < 2 := by dsimp [jj]; omega
      have hr : rr < C.s := by
        dsimp [rr, x]
        omega
      let r : Fin C.s := ⟨rr, hr⟩
      let j : Fin 2 := ⟨jj, hj⟩
      have hri : r.val < i.val := by dsimp [r, rr, x]; omega
      refine ⟨r, j, ?_, ?_, ?_⟩
      · intro h
        exact (Nat.ne_of_lt hri) (congrArg Fin.val h)
      · omega
      · have he : rE q = ⟨C.p - 1 + 2 * r.val + j.val, by omega⟩ := by
          apply Fin.ext
          rw [rE_val]
          simp [hq]
          dsimp [r, j, rr, jj]
          omega
        change T.edge (rE q) = C.blockEdge r j
        rw [he]
        exact C.block_edge_position r j
  · right
    let x := q.val + 2 - (C.p - 1)
    let rr := x / 2
    let jj := x % 2
    have hx : q.val + 2 = C.p - 1 + x := by dsimp [x]; omega
    have hdiv : x = 2 * rr + jj := by dsimp [rr, jj]; omega
    have hj : jj < 2 := by dsimp [jj]; omega
    have hr : rr < C.s := by
      dsimp [rr, x]
      omega
    let r : Fin C.s := ⟨rr, hr⟩
    let j : Fin 2 := ⟨jj, hj⟩
    have hri : i.val < r.val := by
      dsimp [r, rr, x]
      omega
    refine ⟨r, j, ?_, ?_, ?_⟩
    · intro heq
      exact (Nat.ne_of_gt hri) (congrArg Fin.val heq)
    · omega
    · have he : rE q = ⟨C.p - 1 + 2 * r.val + j.val, by omega⟩ := by
        apply Fin.ext
        rw [rE_val]
        simp only [ite_eq_right hq]
        dsimp [r, j, rr, jj]
        omega
      change T.edge (rE q) = C.blockEdge r j
      rw [he, C.block_edge_position]

end GoldbergSeymour.SharedFacts.ScheideSelectedBlockDeletion

end
