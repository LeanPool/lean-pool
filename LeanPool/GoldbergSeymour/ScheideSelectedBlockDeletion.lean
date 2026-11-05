/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.ScheideReducedConfiguration
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Scheide Selected Block Deletion

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hatt_115.{u_1, u_2} :
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
    (∀ (q : Fin (T.length - (2 : ℕ) + (1 : ℕ))),
        (↑(rV q) : ℕ) = if (↑q : ℕ) < m then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (↑(rE q) : ℕ) = if (↑q : ℕ) < d then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    d + (1 : ℕ) < T.length →
    let nv : Fin (T.length - (2 : ℕ) + (1 : ℕ)) → V :=
      fun (q : Fin (T.length - (2 : ℕ) + (1 : ℕ))) => T.vertex (rV q);
    let ne : Fin (T.length - (2 : ℕ)) → E := fun (q : Fin (T.length - (2 : ℕ))) =>
      T.edge (rE q);
    ∀ (q : Fin (T.length - (2 : ℕ))),
    ∃ (a : Fin ((↑q : ℕ) + (1 : ℕ))),
    G.ends (ne q) =
      s(nv q.succ, nv (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt)))) := by
  classical
  intro V E _ _ _ G k e0 phi T C i hi hp hl hn m d rV rE rV_val rE_val hd nv ne q
  by_cases hq : q.val < d
  · obtain ⟨a, ha⟩ := T.attaches (rE q)
    have he : rE q = ⟨q.val, by omega⟩ := by
      apply Fin.ext; rw [rE_val]; simp [hq]
    have hav : a.val < q.val + 1 := by
      simpa [he] using a.isLt
    refine ⟨⟨a.val, hav⟩, ?_⟩
    dsimp [ne, nv]
    have hs : rV q.succ = (rE q).succ := by
      apply Fin.ext
      rw [rV_val]
      have her : (rE q).val = q.val := by
        simpa using congrArg Fin.val he
      change (if q.val + 1 < m then q.val + 1 else q.val + 1 + 2) =
        (rE q).val + 1
      rw [her]
      have : q.val + 1 < m := by dsimp [d, m] at *; omega
      simp [this]
    have haidx : rV ⟨a.val, by omega⟩ =
        Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ (rE q).isLt)) := by
      apply Fin.ext
      rw [rV_val]
      have ham : a.val < m := by dsimp [m, d] at *; omega
      simp [ham]
    have hqidx : q.succ = ⟨q.val + 1, by omega⟩ := rfl
    have hnvq : T.vertex (rV q.succ) = T.vertex (rE q).succ :=
      congrArg T.vertex hs
    have hnva : T.vertex (rV ⟨a.val, by omega⟩) =
        T.vertex (Fin.castLT a (Nat.lt_trans a.isLt
          (Nat.succ_lt_succ (rE q).isLt))) := congrArg T.vertex haidx
    rw [hnvq, hnva]
    exact ha
  · let x := q.val + 2 - (C.p - 1)
    let rr := x / 2
    let jj := x % 2
    have hq : d ≤ q.val := by omega
    have hqT : q.val + 2 < T.length := by omega
    have hx : q.val + 2 = C.p - 1 + x := by
      dsimp [x]
      omega
    have hdiv : x = 2 * rr + jj := by
      dsimp [rr, jj]
      omega
    have hj : jj < 2 := by dsimp [jj]; omega
    have hr : rr < C.s := by
      dsimp [rr, x]
      omega
    let r : Fin C.s := ⟨rr, hr⟩
    let j : Fin 2 := ⟨jj, hj⟩
    obtain ⟨b, hb⟩ := C.block_attaches_to_base r j
    have het : rE q = ⟨C.p - 1 + 2 * r.val + j.val, by omega⟩ := by
      apply Fin.ext
      rw [rE_val]
      have hn : ¬ q.val < d := by omega
      simp only [ite_eq_right hn]
      dsimp [r, j, rr, jj, x]
      omega
    have hrv : rV q.succ =
        ⟨C.p + 2 * r.val + j.val, by omega⟩ := by
      apply Fin.ext
      rw [rV_val]
      have hn : ¬ q.val + 1 < m := by dsimp [m, d] at *; omega
      simp only []
      have heq : q.val + 1 + 2 = C.p + 2 * rr + jj := by
        dsimp [x] at hx
        dsimp [rr, jj]
        omega
      simpa [r, j, hn] using heq
    have heb : ne q = C.blockEdge r j := by
      dsimp [ne]
      rw [het, C.block_edge_position]
    have hnv : nv q.succ = C.blockVertex r j := by
      dsimp [nv]
      rw [hrv, C.block_vertex_position]
    have hbq : b.val < q.val + 1 := by
      have := b.isLt
      dsimp [r, j] at hb ⊢
      omega
    refine ⟨⟨b.val, hbq⟩, ?_⟩
    rw [heb, hnv]
    have hcast : Fin.castLT ⟨b.val, hbq⟩
        (Nat.lt_trans (show b.val < q.val + 1 from hbq)
          (Nat.succ_lt_succ q.isLt)) = ⟨b.val, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hcast]
    have hnb : b.val < m := by dsimp [m]; omega
    change G.ends (C.blockEdge r j) =
      s(C.blockVertex r j, T.vertex (rV ⟨b.val, by omega⟩))
    have hrb : rV ⟨b.val, by omega⟩ = ⟨b.val, by omega⟩ := by
      apply Fin.ext
      rw [rV_val]
      simp [hnb]
    rw [hrb, C.base_vertex_position]
    exact hb.trans Sym2.eq_swap

private theorem helper_edge_class_global_229.{u_1, u_2} :
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
        r ≠ i ∧ C.p - (1 : ℕ) ≤ (↑q : ℕ) ∧ S.edge q = C.blockEdge r j := by
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

private theorem helper_branch_298.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
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
    (∀ (q : Fin (T.length - (2 : ℕ) + (1 : ℕ))),
        (↑(rV q) : ℕ) = if (↑q : ℕ) < m then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    m + (1 : ℕ) ≤ T.length →
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
    TreeSequenceVertexSet
        { length := T.length - (2 : ℕ),
          positive :=
            Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (2 : ℕ)) => by omega,
          vertex := nv, edge := ne, vertex_injective := nv_inj, edge_injective := ne_inj,
          first_edge :=
            have he :
              rE
                  (⟨(0 : ℕ),
                      Decidable.byContradiction fun (a : ¬(0 : ℕ) < T.length - (2 : ℕ)) =>
                        by omega⟩ :
                    Fin (T.length - (2 : ℕ))) =
                (⟨(0 : ℕ), T.positive⟩ : Fin T.length) :=
              hfirst;
            id
              (Eq.mpr (id (congrArg (fun (_a : Fin T.length) => T.edge _a = e0) he))
                T.first_edge),
          attaches := hatt : TreeSequence G e0 } =
      TreeSequenceVertexSet T \
        {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C i hi hp hl hn m d rV rE rV_val hm hfirst nv ne nv_inj ne_inj hatt
  ext x
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨⟨rV q, rfl⟩, ?_⟩
    · rintro (h | h)
      · change T.vertex (rV q) = C.blockVertex i 0 at h
        rw [← C.block_vertex_position i 0] at h
        have hv := T.vertex_injective h
        have heq : rV q = ⟨m, by omega⟩ := by
          exact hv
        have hvv := congrArg Fin.val heq
        rw [rV_val] at hvv
        by_cases hq : q.val < m <;> simp [hq] at hvv <;> omega
      · change T.vertex (rV q) = C.blockVertex i 1 at h
        rw [← C.block_vertex_position i 1] at h
        have hv := T.vertex_injective h
        have heq : rV q = ⟨m + 1, by omega⟩ := by
          exact hv
        have hvv := congrArg Fin.val heq
        rw [rV_val] at hvv
        by_cases hq : q.val < m <;> simp [hq] at hvv <;> omega
  · rintro ⟨⟨t, rfl⟩, hnot⟩
    by_cases ht : t.val < m
    · refine ⟨⟨t.val, by omega⟩, ?_⟩
      · have he : rV ⟨t.val, by omega⟩ = t := by
          apply Fin.ext
          rw [rV_val]
          simp [ht]
        exact congrArg T.vertex he
    · by_cases htm : t.val = m
      · exfalso
        apply hnot
        left
        rw [← C.block_vertex_position i 0]
        congr 1
        apply Fin.ext
        omega
      · by_cases htm1 : t.val = m + 1
        · exfalso
          apply hnot
          right
          rw [← C.block_vertex_position i 1]
          congr 1
          apply Fin.ext
          omega
        · have hgt : m + 1 < t.val := by omega
          refine ⟨⟨t.val - 2, by omega⟩, ?_⟩
          · have he : rV ⟨t.val - 2, by omega⟩ = t := by
              apply Fin.ext
              rw [rV_val]
              simp [show ¬ t.val - 2 < m by omega]
              omega
            exact congrArg T.vertex he

private theorem helper_branch_381.{u_1, u_2} :
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
    (∀ (q : Fin (T.length - (2 : ℕ) + (1 : ℕ))),
        (↑(rV q) : ℕ) = if (↑q : ℕ) < m then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (↑(rE q) : ℕ) = if (↑q : ℕ) < d then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    m + (1 : ℕ) ≤ T.length →
    d + (1 : ℕ) < T.length →
    let nv : Fin (T.length - (2 : ℕ) + (1 : ℕ)) → V :=
      fun (q : Fin (T.length - (2 : ℕ) + (1 : ℕ))) => T.vertex (rV q);
    let ne : Fin (T.length - (2 : ℕ)) → E := fun (q : Fin (T.length - (2 : ℕ))) =>
      T.edge (rE q);
    ∀ (r : Fin C.s),
    ¬r = i →
    ∀ (j : Fin (2 : ℕ)),
    ∃ (qv : Fin (T.length - (2 : ℕ) + (1 : ℕ))) (qe : Fin (T.length - (2 : ℕ))),
    C.p ≤ (↑qv : ℕ) ∧
      C.p - (1 : ℕ) ≤ (↑qe : ℕ) ∧
        (↑qe : ℕ) + (1 : ℕ) = (↑qv : ℕ) ∧
          nv qv = C.blockVertex r j ∧ ne qe = C.blockEdge r j := by
  classical
  intro V E _ _ _ G k e0 phi T C i hi hp hl hn m d rV rE rV_val rE_val hm hd nv ne r hri j
  have hr := r.isLt
  have hj := j.isLt
  have htwo : 2 ≤ T.length := by omega
  have hlen : T.length = C.p + 2 * C.s - 1 := by omega
  have hnew : T.length - 2 + 1 = T.length - 1 := by omega
  by_cases hri' : r.val < i.val
  · have hpos : C.p + 2 * r.val + j.val < m := by dsimp [m]; omega
    have hpose : C.p - 1 + 2 * r.val + j.val < d := by dsimp [d]; omega
    have hqv : C.p + 2 * r.val + j.val < T.length - 1 := by
      dsimp [m] at hpos
      omega
    have hqe : C.p - 1 + 2 * r.val + j.val < T.length - 2 := by
      dsimp [d] at hpose
      omega
    let qv : Fin (T.length - 2 + 1) := ⟨C.p + 2 * r.val + j.val, by omega⟩
    let qe : Fin (T.length - 2) := ⟨C.p - 1 + 2 * r.val + j.val, hqe⟩
    refine ⟨qv, qe, by dsimp [qv]; omega, by dsimp [qe]; omega,
      by dsimp [qv, qe]; omega, ?_, ?_⟩
    · dsimp [nv]
      have hold : C.p + 2 * r.val + j.val < T.length + 1 := by omega
      have he : rV qv =
          ⟨C.p + 2 * r.val + j.val, hold⟩ := by
        dsimp [qv]
        apply Fin.ext
        rw [rV_val]
        simp [hpos]
      rw [he, C.block_vertex_position]
    · dsimp [ne]
      have hold : C.p - 1 + 2 * r.val + j.val < T.length := by omega
      have he : rE qe =
          ⟨C.p - 1 + 2 * r.val + j.val, hold⟩ := by
        dsimp [qe]
        apply Fin.ext
        rw [rE_val]
        simp [hpose]
      rw [he, C.block_edge_position]
  · have hri'' : i.val < r.val := by omega
    have hpos : ¬ C.p + 2 * r.val + j.val - 2 < m := by dsimp [m]; omega
    have hpose : ¬ C.p - 1 + 2 * r.val + j.val - 2 < d := by dsimp [d]; omega
    have hqv : C.p + 2 * r.val + j.val - 2 < T.length - 1 := by
      dsimp [m] at hpos
      omega
    have hqe : C.p - 1 + 2 * r.val + j.val - 2 < T.length - 2 := by
      dsimp [d] at hpose
      omega
    let qv : Fin (T.length - 2 + 1) := ⟨C.p + 2 * r.val + j.val - 2, by rw [hnew]; exact hqv⟩
    let qe : Fin (T.length - 2) := ⟨C.p - 1 + 2 * r.val + j.val - 2, hqe⟩
    refine ⟨qv, qe, by dsimp [qv]; omega, by dsimp [qe]; omega,
      by dsimp [qv, qe]; omega, ?_, ?_⟩
    · dsimp [nv]
      have hold : C.p + 2 * r.val + j.val < T.length + 1 := by omega
      have he : rV qv =
          ⟨C.p + 2 * r.val + j.val, hold⟩ := by
        dsimp [qv]
        apply Fin.ext
        rw [rV_val]
        simp [hpos]
        omega
      rw [he, C.block_vertex_position]
    · dsimp [ne]
      have hold : C.p - 1 + 2 * r.val + j.val < T.length := by omega
      have he : rE qe =
          ⟨C.p - 1 + 2 * r.val + j.val, hold⟩ := by
        dsimp [qe]
        apply Fin.ext
        rw [rE_val]
        simp [hpose]
        omega
      rw [he, C.block_edge_position]

private theorem helper_edge_class_455.{u_1, u_2} :
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
        r ≠ i ∧ C.p - (1 : ℕ) ≤ (↑q : ℕ) ∧ S.edge q = C.blockEdge r j := by
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

private theorem helper_branch_529.{u_1, u_2} :
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
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (∃ (a : Fin (C.p - (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ S.edge q = C.baseEdge a) ∨
          ∃ (r : Fin C.s) (j : Fin (2 : ℕ)),
            r ≠ i ∧ C.p - (1 : ℕ) ≤ (↑q : ℕ) ∧ S.edge q = C.blockEdge r j) →
    ∀ (q : Fin (T.length - (2 : ℕ))),
    ¬Incident G (C.blockVertex i (0 : Fin (2 : ℕ))) (ne q) ∧
      ¬Incident G (C.blockVertex i (1 : Fin (2 : ℕ))) (ne q) := by
  classical
  intro V E _ _ _ G k e0 phi T C i hi hp hl hn m d rV rE hd hfirst nv ne nv_inj ne_inj hatt S
      edge_class_global q
  constructor
  · intro hinc
    change C.blockVertex i 0 ∈ G.ends (S.edge q) at hinc
    have hclass := edge_class_global q
    rcases hclass with ⟨a, ha, he⟩ | ⟨r, j, hri, hq, he⟩
    · obtain ⟨b, hb⟩ := T.attaches ⟨a.val, by omega⟩
      have ha' := a.isLt
      have hb' := b.isLt
      have hend := hb
      have hmemb : C.blockVertex i 0 ∈ s(T.vertex (Fin.succ ⟨a.val, by omega⟩),
          T.vertex (b.castLT (by omega))) := by
        rw [← hend]
        rw [he, ← C.base_edge_position a] at hinc
        simpa only [Fin.succ_mk] using hinc
      rcases Sym2.mem_iff.mp hmemb with h | h
      · rw [← C.block_vertex_position i 0] at h
        have hv := T.vertex_injective h
        have hvv := congrArg Fin.val hv
        simp at hvv
        have hba : b.val ≤ a.val := Nat.lt_succ_iff.mp b.isLt
        omega
      · rw [← C.block_vertex_position i 0] at h
        have hv := T.vertex_injective h
        have hvv := congrArg Fin.val hv
        simp at hvv
        have hba : b.val ≤ a.val := Nat.lt_succ_iff.mp b.isLt
        omega
    · obtain ⟨b, hb⟩ := C.block_attaches_to_base r j
      have hi' := i.isLt
      have hj := j.isLt
      have hr := r.isLt
      have heq : G.ends (S.edge q) = s(C.blockVertex r j, C.y b) := by
        calc
          G.ends (S.edge q) = G.ends (C.blockEdge r j) := congrArg G.ends he
          _ = s(C.y b, C.blockVertex r j) := hb
          _ = s(C.blockVertex r j, C.y b) := Sym2.eq_swap
      have hmemb : C.blockVertex i 0 ∈ s(C.blockVertex r j, C.y b) := by
        rw [← heq]
        exact hinc
      rcases Sym2.mem_iff.mp hmemb with h | h
      · rw [← C.block_vertex_position i 0, ← C.block_vertex_position r j] at h
        have hv := T.vertex_injective h
        have hvv := congrArg Fin.val hv
        simp at hvv
        apply hri
        apply Fin.ext
        omega
      · rw [← C.block_vertex_position i 0, ← C.base_vertex_position b] at h
        have hv := T.vertex_injective h
        have hvv := congrArg Fin.val hv
        have hb' := b.isLt
        simp at hvv
        omega
  · intro hinc
    change C.blockVertex i 1 ∈ G.ends (S.edge q) at hinc
    have hclass := edge_class_global q
    rcases hclass with ⟨a, ha, he⟩ | ⟨r, j, hri, hq, he⟩
    · obtain ⟨b, hb⟩ := T.attaches ⟨a.val, by omega⟩
      have ha' := a.isLt
      have hb' := b.isLt
      have hend := hb
      have hmemb : C.blockVertex i 1 ∈ s(T.vertex (Fin.succ ⟨a.val, by omega⟩),
          T.vertex (b.castLT (by omega))) := by
        rw [← hend]
        rw [he, ← C.base_edge_position a] at hinc
        simpa only [Fin.succ_mk] using hinc
      rcases Sym2.mem_iff.mp hmemb with h | h
      · rw [← C.block_vertex_position i 1] at h
        have hv := T.vertex_injective h
        have hvv := congrArg Fin.val hv
        simp at hvv
        have hba : b.val ≤ a.val := Nat.lt_succ_iff.mp b.isLt
        omega
      · rw [← C.block_vertex_position i 1] at h
        have hv := T.vertex_injective h
        have hvv := congrArg Fin.val hv
        simp at hvv
        have hba : b.val ≤ a.val := Nat.lt_succ_iff.mp b.isLt
        omega
    · obtain ⟨b, hb⟩ := C.block_attaches_to_base r j
      have hi' := i.isLt
      have hj := j.isLt
      have hr := r.isLt
      have heq : G.ends (S.edge q) = s(C.blockVertex r j, C.y b) := by
        calc
          G.ends (S.edge q) = G.ends (C.blockEdge r j) := congrArg G.ends he
          _ = s(C.y b, C.blockVertex r j) := hb
          _ = s(C.blockVertex r j, C.y b) := Sym2.eq_swap
      have hmemb : C.blockVertex i 1 ∈ s(C.blockVertex r j, C.y b) := by
        rw [← heq]
        exact hinc
      rcases Sym2.mem_iff.mp hmemb with h | h
      · rw [← C.block_vertex_position i 1, ← C.block_vertex_position r j] at h
        have hv := T.vertex_injective h
        have hvv := congrArg Fin.val hv
        simp at hvv
        apply hri
        apply Fin.ext
        omega
      · rw [← C.block_vertex_position i 1, ← C.base_vertex_position b] at h
        have hv := T.vertex_injective h
        have hvv := congrArg Fin.val hv
        have hb' := b.isLt
        simp at hvv
        omega

theorem ScheideSelectedBlockDeletion {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s) :
    ∃ S : TreeSequence G e0,
    TreeSequenceVertexSet S =
        TreeSequenceVertexSet T \ {C.blockVertex i 0, C.blockVertex i 1} ∧
      S.length + 2 = T.length ∧
        (∃ rV : Fin (S.length + 1) → Fin (T.length + 1),
            (∀ q : Fin (S.length + 1), S.vertex q = T.vertex (rV q)) ∧
              (∀ q : Fin (S.length + 1), q.val < C.p + 2 * i.val → (rV q).val = q.val) ∧
                ∀ q : Fin (S.length + 1),
                  C.p + 2 * i.val ≤ q.val → (rV q).val = q.val + 2) ∧
          (∃ rE : Fin S.length → Fin T.length,
              (∀ q : Fin S.length, S.edge q = T.edge (rE q)) ∧
                (∀ q : Fin S.length, q.val < C.p - 1 + 2 * i.val → (rE q).val = q.val) ∧
                  ∀ q : Fin S.length,
                    C.p - 1 + 2 * i.val ≤ q.val → (rE q).val = q.val + 2) ∧
            (∀ a : Fin C.p, ∃ q : Fin (S.length + 1), q.val = a.val ∧ S.vertex q = C.y a) ∧
              (∀ a : Fin (C.p - 1),
                  ∃ q : Fin S.length, q.val = a.val ∧ S.edge q = C.baseEdge a) ∧
                (∀ r : Fin C.s,
                    r ≠ i →
                      ∀ j : Fin 2,
                        ∃ qv : Fin (S.length + 1),
                          ∃ qe : Fin S.length,
                            C.p ≤ qv.val ∧
                              C.p - 1 ≤ qe.val ∧
                                qe.val + 1 = qv.val ∧
                                  S.vertex qv = C.blockVertex r j ∧
                                    S.edge qe = C.blockEdge r j) ∧
                  (∀ q : Fin S.length,
                      (∃ a : Fin (C.p - 1), q.val = a.val ∧ S.edge q = C.baseEdge a) ∨
                        (∃ r : Fin C.s,
                          ∃ j : Fin 2,
                            r ≠ i ∧ C.p - 1 ≤ q.val ∧ S.edge q = C.blockEdge r j)) ∧
                    (∀ q : Fin S.length, ∃ r : Fin T.length, S.edge q = T.edge r) ∧
                      ∀ q : Fin S.length,
                        ¬Incident G (C.blockVertex i 0) (S.edge q) ∧
                          ¬Incident G (C.blockVertex i 1) (S.edge q) := by
  classical
  have hi : i.val < C.s := i.isLt
  have hp : 2 ≤ C.p := C.p_ge_two
  have hl : T.length + 1 = C.p + 2 * C.s := C.length_eq
  have hn : 3 ≤ T.length := by omega
  let m := C.p + 2 * i.val
  let d := C.p - 1 + 2 * i.val
  let rV : Fin (T.length - 2 + 1) → Fin (T.length + 1) := fun q =>
    if h : q.val < m then ⟨q.val, by omega⟩ else ⟨q.val + 2, by omega⟩
  let rE : Fin (T.length - 2) → Fin T.length := fun q =>
    if h : q.val < d then ⟨q.val, by omega⟩ else ⟨q.val + 2, by omega⟩
  have rV_val (q : Fin (T.length - 2 + 1)) :
      (rV q).val = if q.val < m then q.val else q.val + 2 := by
    by_cases h : q.val < m <;> simp [rV, h]
  have rE_val (q : Fin (T.length - 2)) :
      (rE q).val = if q.val < d then q.val else q.val + 2 := by
    by_cases h : q.val < d <;> simp [rE, h]
  have rV_inj : Function.Injective rV := by
    intro q z hqz
    by_cases hq : q.val < m <;> by_cases hz : z.val < m
    all_goals
      have hv := congrArg Fin.val hqz
      rw [rV_val, rV_val] at hv
      simp [hq, hz] at hv
      apply Fin.ext
      omega
  have rE_inj : Function.Injective rE := by
    intro q z hqz
    by_cases hq : q.val < d <;> by_cases hz : z.val < d
    all_goals
      have hv := congrArg Fin.val hqz
      rw [rE_val, rE_val] at hv
      simp [hq, hz] at hv
      apply Fin.ext
      omega
  have hm : m + 1 ≤ T.length := by dsimp [m]; omega
  have hd : d + 1 < T.length := by dsimp [d]; omega
  have hfirst : rE ⟨0, by omega⟩ = ⟨0, T.positive⟩ := by
    apply Fin.ext
    rw [rE_val]
    have : (0 : ℕ) < d := by dsimp [d]; omega
    simp [this]
  let nv : Fin (T.length - 2 + 1) → V := fun q => T.vertex (rV q)
  let ne : Fin (T.length - 2) → E := fun q => T.edge (rE q)
  have nv_inj : Function.Injective nv := by
    intro q z hqz
    apply rV_inj
    exact T.vertex_injective hqz
  have ne_inj : Function.Injective ne := by
    intro q z hqz
    apply rE_inj
    exact T.edge_injective hqz
  have hatt := @helper_hatt_115 V E inferInstance inferInstance inferInstance G k e0 phi T C i hi hp
      hl hn rV_val rE_val hd
  let S : TreeSequence G e0 :=
    { length := T.length - 2
      positive := by omega
      vertex := nv
      edge := ne
      vertex_injective := nv_inj
      edge_injective := ne_inj
      first_edge := by
        have he : rE ⟨0, by omega⟩ = ⟨0, T.positive⟩ := hfirst
        dsimp [ne]
        rw [he]
        exact T.first_edge
      attaches := hatt }
  refine ⟨S, ?_⟩
  dsimp [S]
  have edge_class_global := @helper_edge_class_global_229 V E inferInstance inferInstance
      inferInstance G k e0 phi T C i hi hp hl hn rE_val hm hd hfirst nv_inj ne_inj hatt
  refine ⟨?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact @helper_branch_298 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C i hi hp hl hn rV_val hm hfirst nv_inj ne_inj hatt
  · refine ⟨rV, ?_, ?_, ?_⟩
    · intro q; rfl
    · intro q hq
      rw [rV_val]
      simp [show q.val < m by simpa [m] using hq]
    · intro q hq
      rw [rV_val]
      simp [show ¬ q.val < m by simpa [m] using hq]
  · refine ⟨rE, ?_, ?_, ?_⟩
    · intro q; rfl
    · intro q hq
      rw [rE_val]
      simp [show q.val < d by simpa [d] using hq]
    · intro q hq
      rw [rE_val]
      simp [show ¬ q.val < d by simpa [d] using hq]
  · intro a
    refine ⟨⟨a.val, by omega⟩, rfl, ?_⟩
    dsimp [nv]
    have hr : rV ⟨a.val, by omega⟩ = ⟨a.val, by omega⟩ := by
      apply Fin.ext; rw [rV_val]; simp [show a.val < m by dsimp [m]; omega]
    rw [hr, C.base_vertex_position]
  · intro a
    refine ⟨⟨a.val, by omega⟩, rfl, ?_⟩
    dsimp [ne]
    have hr : rE ⟨a.val, by omega⟩ = ⟨a.val, by omega⟩ := by
      apply Fin.ext; rw [rE_val]; simp [show a.val < d by dsimp [d]; omega]
    rw [hr, C.base_edge_position]
  · exact @helper_branch_381 V E inferInstance inferInstance inferInstance G k e0 phi T C i hi hp
      hl hn rV_val rE_val hm hd
  · have edge_class := @helper_edge_class_455 V E inferInstance inferInstance inferInstance G k e0
      phi
        T C i hi hp hl hn rE_val hm hd hfirst nv_inj ne_inj hatt
    intro q
    exact edge_class q
  · intro q
    exact ⟨rE q, rfl⟩
  · exact @helper_branch_529 V E inferInstance inferInstance inferInstance G k e0 phi T C i hi hp
      hl hn hd hfirst nv_inj ne_inj hatt edge_class_global
end GoldbergSeymour

end
