/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideExitNoFree
public import LeanPool.GoldbergSeymour.ScheideReducedConfiguration

/-!
# Scheide Structural Internal Pair

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private theorem helper_nv_injective_206.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s),
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmLast : m + (1 : ℕ) ≤ T.length),
    u0 ≠ u1 →
    let rix : Fin (T.length - (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
      fun (q : Fin (T.length - (1 : ℕ))) ↦
      if hqm : (↑q : ℕ) < m then
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ)))
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) ↦
              by omega⟩ :
          Fin (T.length + (1 : ℕ)));
    Function.Injective rix →
    let nv : Fin (T.length + (1 : ℕ)) → V := fun (q : Fin (T.length + (1 : ℕ))) ↦
      if hq : (↑q : ℕ) < T.length - (1 : ℕ) then
        T.vertex (rix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (1 : ℕ))))
      else if (↑q : ℕ) = T.length - (1 : ℕ) then u0 else u1;
    nv
          (⟨T.length - (1 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length + (1 : ℕ)) ↦
                by omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u0 →
    nv
          (⟨T.length,
              Decidable.byContradiction fun (a : ¬T.length < T.length + (1 : ℕ)) ↦ by
                omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u1 →
    (∀ (q : Fin (T.length - (1 : ℕ))), T.vertex (rix q) ≠ u0) →
    (∀ (q : Fin (T.length - (1 : ℕ))), T.vertex (rix q) ≠ u1) →
    Function.Injective nv := by
  classical
  intro V E _ _ _ G k e0 phi T C i u0 u1 hlength hlenThree m hmLast hu01 rix rix_injective nv
      nv_penultimate nv_last retained_ne_u0 retained_ne_u1 q r hqr
  by_cases hq : q.val < T.length - 1
  · by_cases hr : r.val < T.length - 1
    · let q' : Fin (T.length - 1) := ⟨q.val, hq⟩
      let r' : Fin (T.length - 1) := ⟨r.val, hr⟩
      have hv : T.vertex (rix q') = T.vertex (rix r') := by
        simpa [nv, hq, hr, q', r'] using hqr
      have hi := rix_injective (T.vertex_injective hv)
      apply Fin.ext
      simpa [q', r'] using congrArg Fin.val hi
    · have hrval : r.val = T.length - 1 ∨ r.val = T.length := by omega
      rcases hrval with hrval | hrval
      · have hre : r = ⟨T.length - 1, by omega⟩ := Fin.ext (by omega)
        have hqeq : q = ⟨q.val, by omega⟩ := rfl
        rw [hre, nv_penultimate] at hqr
        have hnq : nv q = T.vertex (rix ⟨q.val, hq⟩) := by
          simp [nv, hq]
        exact False.elim (retained_ne_u0 ⟨q.val, hq⟩ (hnq ▸ hqr))
      · have hre : r = ⟨T.length, by omega⟩ := Fin.ext (by omega)
        rw [hre, nv_last] at hqr
        have hnq : nv q = T.vertex (rix ⟨q.val, hq⟩) := by
          simp [nv, hq]
        exact False.elim (retained_ne_u1 ⟨q.val, hq⟩ (hnq ▸ hqr))
  · by_cases hr : r.val < T.length - 1
    · have hqval : q.val = T.length - 1 ∨ q.val = T.length := by omega
      rcases hqval with hqval | hqval
      · have hqe : q = ⟨T.length - 1, by omega⟩ := Fin.ext (by omega)
        rw [hqe, nv_penultimate] at hqr
        have hnr : nv r = T.vertex (rix ⟨r.val, hr⟩) := by
          simp [nv, hr]
        exact False.elim (retained_ne_u0 ⟨r.val, hr⟩ (hnr ▸ hqr.symm))
      · have hqe : q = ⟨T.length, by omega⟩ := Fin.ext (by omega)
        rw [hqe, nv_last] at hqr
        have hnr : nv r = T.vertex (rix ⟨r.val, hr⟩) := by
          simp [nv, hr]
        exact False.elim (retained_ne_u1 ⟨r.val, hr⟩ (hnr ▸ hqr.symm))
    · have hqval : q.val = T.length - 1 ∨ q.val = T.length := by omega
      have hrval : r.val = T.length - 1 ∨ r.val = T.length := by omega
      rcases hqval with hqval | hqval <;> rcases hrval with hrval | hrval
      · apply Fin.ext; omega
      · exfalso
        have hqe : q = ⟨T.length - 1, by omega⟩ := Fin.ext (by omega)
        have hre : r = ⟨T.length, by omega⟩ := Fin.ext (by omega)
        exact hu01 (by simpa [hqe, hre, nv_penultimate, nv_last] using hqr)
      · exfalso
        have hqe : q = ⟨T.length, by omega⟩ := Fin.ext (by omega)
        have hre : r = ⟨T.length - 1, by omega⟩ := Fin.ext (by omega)
        exact hu01 (by simpa [hqe, hre, nv_penultimate, nv_last] using hqr.symm)
      · apply Fin.ext; omega

private theorem helper_retained_vertex_index_257.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s),
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    let X : Finset V := TreeSequenceVertexSet T;
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    (2 : ℕ) ≤ m →
    ∀ (hmLast : m + (1 : ℕ) ≤ T.length),
    T.vertex
          (⟨m, Decidable.byContradiction fun (a : ¬m < T.length + (1 : ℕ)) ↦ by omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u0 →
    T.vertex
          (⟨m + (1 : ℕ),
              Decidable.byContradiction fun (a : ¬m + (1 : ℕ) < T.length + (1 : ℕ)) ↦ by
                omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u1 →
    let rix : Fin (T.length - (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
      fun (q : Fin (T.length - (1 : ℕ))) ↦
      if hqm : (↑q : ℕ) < m then
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ)))
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) ↦
              by omega⟩ :
          Fin (T.length + (1 : ℕ)));
    (∀ (q : Fin (T.length - (1 : ℕ))),
        (↑(rix q) : ℕ) = if (↑q : ℕ) < m then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    let nv : Fin (T.length + (1 : ℕ)) → V := fun (q : Fin (T.length + (1 : ℕ))) ↦
      if hq : (↑q : ℕ) < T.length - (1 : ℕ) then
        T.vertex (rix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (1 : ℕ))))
      else if (↑q : ℕ) = T.length - (1 : ℕ) then u0 else u1;
    (∀ (q : Fin (T.length - (1 : ℕ))),
        nv
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by
                  omega⟩ :
              Fin (T.length + (1 : ℕ))) =
          T.vertex (rix q)) →
    ∀ {w : V},
    w ∈ X →
    w ≠ u0 →
    w ≠ u1 →
    ∃ (q : Fin (T.length - (1 : ℕ))),
    nv
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ))) =
      w := by
  classical
  intro V E _ _ _ G k e0 phi T C i u0 u1 X hlength hlenThree m hmTwo hmLast hu0pos hu1pos rix
      rix_val nv nv_retained w hwX' hwu0 hwu1
  have hw : w ∈ TreeSequenceVertexSet T := by simpa only [X] using hwX'
  have hw' : ∃ t : Fin (T.length + 1), T.vertex t = w := by
    simpa [TreeSequenceVertexSet] using hw
  obtain ⟨t, ht⟩ := hw'
  have htm : t.val ≠ m := by
    intro hval
    have he : t = ⟨m, by omega⟩ := Fin.ext (by omega)
    exact hwu0 (by simpa [he, hu0pos] using ht.symm)
  have htm1 : t.val ≠ m + 1 := by
    intro hval
    have he : t = ⟨m + 1, by omega⟩ := Fin.ext (by omega)
    exact hwu1 (by simpa [he, hu1pos] using ht.symm)
  by_cases hbefore : t.val < m
  · let q : Fin (T.length - 1) := ⟨t.val, by omega⟩
    refine ⟨q, ?_⟩
    have hrix : rix q = t := by
      apply Fin.ext
      simp [rix_val, q, hbefore]
    simpa [nv_retained, hrix] using ht
  · have hafter : m + 2 ≤ t.val := by omega
    let q : Fin (T.length - 1) := ⟨t.val - 2, by omega⟩
    refine ⟨q, ?_⟩
    have hqnot : ¬ q.val < m := by dsimp [q]; omega
    have hrix : rix q = t := by
      apply Fin.ext
      rw [rix_val]
      simp only [ite_eq_right hqnot]
      dsimp [q]
      omega
    simpa [nv_retained, hrix] using ht

private theorem helper_later_indices_313.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s),
    (2 : ℕ) ≤ C.p →
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m) (_ : m + (1 : ℕ) ≤ T.length),
    let rix : Fin (T.length - (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
      fun (q : Fin (T.length - (1 : ℕ))) ↦
      if hqm : (↑q : ℕ) < m then
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ)))
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) ↦
              by omega⟩ :
          Fin (T.length + (1 : ℕ)));
    (∀ (q : Fin (T.length - (1 : ℕ))),
        (↑(rix q) : ℕ) = if (↑q : ℕ) < m then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (↑(eix q) : ℕ) = if (↑q : ℕ) < m - (1 : ℕ) then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    ∀ (q : Fin (T.length - (2 : ℕ))),
    m - (1 : ℕ) ≤ (↑q : ℕ) →
    ∃ (r : Fin C.s) (j : Fin (2 : ℕ)),
    (↑i : ℕ) < (↑r : ℕ) ∧
      (↑(eix q) : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ) ∧
        (↑(rix
                (⟨(↑q : ℕ) + (1 : ℕ),
                    Decidable.byContradiction
                      fun (a : ¬(↑q : ℕ) + (1 : ℕ) < T.length - (1 : ℕ)) ↦ by omega⟩ :
                  Fin (T.length - (1 : ℕ)))) :
            ℕ) =
          C.p + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ) := by
  classical
  intro V E _ _ _ G k e0 phi T C i hpTwo hlength hlenThree m hmTwo hmLast rix rix_val eix eix_val
      q hq
  let d := q.val + 2 - (C.p - 1)
  let rn := d / 2
  let jn := d % 2
  have hqLt := q.isLt
  have hqTwo : q.val + 2 < T.length := by omega
  have hbase : C.p - 1 ≤ q.val + 2 := by dsimp [m] at hq; omega
  have hd : q.val + 2 = C.p - 1 + d := by dsimp [d]; omega
  have hdecomp : d = 2 * rn + jn := by
    dsimp [rn, jn]
    omega
  have hjn : jn < 2 := by
    dsimp [jn]
    omega
  have hrn : rn < C.s := by
    dsimp [rn, d]
    omega
  let r : Fin C.s := ⟨rn, hrn⟩
  let j : Fin 2 := ⟨jn, hjn⟩
  refine ⟨r, j, ?_, ?_, ?_⟩
  · dsimp [r, rn, d]
    omega
  · rw [eix_val]
    have hnot : ¬ q.val < m - 1 := by omega
    simp only [ite_eq_right hnot]
    dsimp [r, j]
    omega
  · rw [rix_val]
    have hnot : ¬ q.val + 1 < m := by omega
    simp only [ite_eq_right hnot]
    dsimp [r, j]
    omega

private theorem helper_retained_not_incident_383.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s),
    (↑i : ℕ) < C.s →
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m) (_ : m + (1 : ℕ) ≤ T.length),
    let rix : Fin (T.length - (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
      fun (q : Fin (T.length - (1 : ℕ))) ↦
      if hqm : (↑q : ℕ) < m then
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ)))
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) ↦
              by omega⟩ :
          Fin (T.length + (1 : ℕ)));
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (↑(eix q) : ℕ) = if (↑q : ℕ) < m - (1 : ℕ) then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    (∀ (q : Fin (T.length - (2 : ℕ))),
        m - (1 : ℕ) ≤ (↑q : ℕ) →
          ∃ (r : Fin C.s) (j : Fin (2 : ℕ)),
            (↑i : ℕ) < (↑r : ℕ) ∧
              (↑(eix q) : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ) ∧
                (↑(rix
                        (⟨(↑q : ℕ) + (1 : ℕ),
                            Decidable.byContradiction
                              fun (a : ¬(↑q : ℕ) + (1 : ℕ) < T.length - (1 : ℕ)) ↦ by
                              omega⟩ :
                          Fin (T.length - (1 : ℕ)))) :
                    ℕ) =
                  C.p + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ)) →
    (∀ (j0 : Fin (2 : ℕ)) (q : Fin (T.length + (1 : ℕ))),
        (↑q : ℕ) < m → C.blockVertex i j0 ≠ T.vertex q) →
    ∀ (q : Fin (T.length - (2 : ℕ))) (j0 : Fin (2 : ℕ)),
    ¬Incident G (C.blockVertex i j0) (T.edge (eix q)) := by
  classical
  intro V E _ _ _ G k e0 phi T C i hiLt hlength hlenThree m hmTwo hmLast rix eix eix_val
      later_indices block_vertex_ne_before q j0 hinc
  by_cases hq : q.val < m - 1
  · have heval : (eix q).val = q.val := by simp [eix_val, hq]
    obtain ⟨a, ha⟩ := T.attaches (eix q)
    rw [Incident, ha] at hinc
    simp only [Sym2.mem_iff] at hinc
    rcases hinc with hnew | hold
    · exact block_vertex_ne_before j0 (eix q).succ (by
        dsimp
        omega) hnew
    · exact block_vertex_ne_before j0
        (Fin.castLT a (Nat.lt_trans a.isLt
          (Nat.succ_lt_succ (eix q).isLt))) (by
            dsimp
            omega) hold
  · have hq' : m - 1 ≤ q.val := by omega
    obtain ⟨r, j, hri, heix, _⟩ := later_indices q hq'
    have hedge : T.edge (eix q) = C.blockEdge r j := by
      calc
        T.edge (eix q) =
            T.edge ⟨C.p - 1 + 2 * r.val + j.val, by omega⟩ := by
          apply congrArg T.edge
          apply Fin.ext
          exact heix
        _ = C.blockEdge r j := C.block_edge_position r j
    obtain ⟨b, hb⟩ := C.block_attaches_to_base r j
    rw [hedge, Incident, hb] at hinc
    simp only [Sym2.mem_iff] at hinc
    rcases hinc with hbase | hblock
    · have hpos := C.block_vertex_position i j0
      have hbpos := C.base_vertex_position b
      have hv : T.vertex ⟨C.p + 2 * i.val + j0.val, by omega⟩ =
          T.vertex ⟨b.val, by omega⟩ := hpos.trans (hbase.trans hbpos.symm)
      have heq := congrArg Fin.val (T.vertex_injective hv)
      simp at heq
      omega
    · have hpos := C.block_vertex_position i j0
      have hrpos := C.block_vertex_position r j
      have hv : T.vertex ⟨C.p + 2 * i.val + j0.val, by omega⟩ =
          T.vertex ⟨C.p + 2 * r.val + j.val, by omega⟩ :=
        hpos.trans (hblock.trans hrpos.symm)
      have heq := congrArg Fin.val (T.vertex_injective hv)
      simp at heq
      omega

private theorem helper_ne_injective_450.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s),
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m) (a0 : E),
    Incident G u0 a0 →
    ∀ (a1 : E),
    Incident G u1 a1 →
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    Function.Injective eix →
    (∀ (q : Fin (T.length - (2 : ℕ))) (j0 : Fin (2 : ℕ)),
        ¬Incident G (C.blockVertex i j0) (T.edge (eix q))) →
    a0 ≠ a1 →
    let ne : Fin T.length → E := fun (q : Fin T.length) ↦
      if hq : (↑q : ℕ) < T.length - (2 : ℕ) then
        T.edge (eix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (2 : ℕ))))
      else if (↑q : ℕ) = T.length - (2 : ℕ) then a0 else a1;
    ne
          (⟨T.length - (2 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) < T.length) ↦ by
                omega⟩ :
            Fin T.length) =
        a0 →
    ne
          (⟨T.length - (1 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by
                omega⟩ :
            Fin T.length) =
        a1 →
    Function.Injective ne := by
  classical
  intro V E _ _ _ G k e0 phi T C i u0 u1 hlength hlenThree m hmTwo a0 ha0Inc a1 ha1Inc eix
      eix_injective retained_not_incident ha01 ne ne_penultimate ne_last q r hqr
  by_cases hq : q.val < T.length - 2
  · by_cases hr : r.val < T.length - 2
    · let q' : Fin (T.length - 2) := ⟨q.val, hq⟩
      let r' : Fin (T.length - 2) := ⟨r.val, hr⟩
      have he : T.edge (eix q') = T.edge (eix r') := by
        simpa [ne, hq, hr, q', r'] using hqr
      have hi := eix_injective (T.edge_injective he)
      apply Fin.ext
      simpa [q', r'] using congrArg Fin.val hi
    · have hrval : r.val = T.length - 2 ∨ r.val = T.length - 1 := by omega
      rcases hrval with hrval | hrval
      · have hre : r = ⟨T.length - 2, by omega⟩ := Fin.ext (by omega)
        rw [hre, ne_penultimate] at hqr
        have hnq : ne q = T.edge (eix ⟨q.val, hq⟩) := by
          simp [ne, hq]
        have heq : T.edge (eix ⟨q.val, hq⟩) = a0 := hnq ▸ hqr
        exact False.elim (retained_not_incident ⟨q.val, hq⟩ (0 : Fin 2)
          (by simpa [heq] using ha0Inc))
      · have hre : r = ⟨T.length - 1, by omega⟩ := Fin.ext (by omega)
        rw [hre, ne_last] at hqr
        have hnq : ne q = T.edge (eix ⟨q.val, hq⟩) := by
          simp [ne, hq]
        have heq : T.edge (eix ⟨q.val, hq⟩) = a1 := hnq ▸ hqr
        exact False.elim (retained_not_incident ⟨q.val, hq⟩ (1 : Fin 2)
          (by simpa [heq] using ha1Inc))
  · by_cases hr : r.val < T.length - 2
    · have hqval : q.val = T.length - 2 ∨ q.val = T.length - 1 := by omega
      rcases hqval with hqval | hqval
      · have hqe : q = ⟨T.length - 2, by omega⟩ := Fin.ext (by omega)
        rw [hqe, ne_penultimate] at hqr
        have hnr : ne r = T.edge (eix ⟨r.val, hr⟩) := by
          simp [ne, hr]
        have heq : T.edge (eix ⟨r.val, hr⟩) = a0 := hnr ▸ hqr.symm
        exact False.elim (retained_not_incident ⟨r.val, hr⟩ (0 : Fin 2)
          (by simpa [heq] using ha0Inc))
      · have hqe : q = ⟨T.length - 1, by omega⟩ := Fin.ext (by omega)
        rw [hqe, ne_last] at hqr
        have hnr : ne r = T.edge (eix ⟨r.val, hr⟩) := by
          simp [ne, hr]
        have heq : T.edge (eix ⟨r.val, hr⟩) = a1 := hnr ▸ hqr.symm
        exact False.elim (retained_not_incident ⟨r.val, hr⟩ (1 : Fin 2)
          (by simpa [heq] using ha1Inc))
    · have hqval : q.val = T.length - 2 ∨ q.val = T.length - 1 := by omega
      have hrval : r.val = T.length - 2 ∨ r.val = T.length - 1 := by omega
      rcases hqval with hqval | hqval <;> rcases hrval with hrval | hrval
      · apply Fin.ext; omega
      · exfalso
        have hqe : q = ⟨T.length - 2, by omega⟩ := Fin.ext (by omega)
        have hre : r = ⟨T.length - 1, by omega⟩ := Fin.ext (by omega)
        exact ha01 (by simpa [hqe, hre, ne_penultimate, ne_last] using hqr)
      · exfalso
        have hqe : q = ⟨T.length - 1, by omega⟩ := Fin.ext (by omega)
        have hre : r = ⟨T.length - 2, by omega⟩ := Fin.ext (by omega)
        exact ha01 (by simpa [hqe, hre, ne_penultimate, ne_last] using hqr.symm)
      · apply Fin.ext; omega

private theorem helper_branch_593.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s),
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    (2 : ℕ) ≤ C.p →
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m) (a0 a1 : E),
    let rix : Fin (T.length - (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
      fun (q : Fin (T.length - (1 : ℕ))) ↦
      if hqm : (↑q : ℕ) < m then
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ)))
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) ↦
              by omega⟩ :
          Fin (T.length + (1 : ℕ)));
    (∀ (q : Fin (T.length - (1 : ℕ))),
        (↑(rix q) : ℕ) = if (↑q : ℕ) < m then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    let nv : Fin (T.length + (1 : ℕ)) → V := fun (q : Fin (T.length + (1 : ℕ))) ↦
      if hq : (↑q : ℕ) < T.length - (1 : ℕ) then
        T.vertex (rix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (1 : ℕ))))
      else if (↑q : ℕ) = T.length - (1 : ℕ) then u0 else u1;
    (∀ (q : Fin (T.length - (1 : ℕ))),
        nv
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by
                  omega⟩ :
              Fin (T.length + (1 : ℕ))) =
          T.vertex (rix q)) →
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (↑(eix q) : ℕ) = if (↑q : ℕ) < m - (1 : ℕ) then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    (∀ (q : Fin (T.length - (2 : ℕ))),
        m - (1 : ℕ) ≤ (↑q : ℕ) →
          ∃ (r : Fin C.s) (j : Fin (2 : ℕ)),
            (↑i : ℕ) < (↑r : ℕ) ∧
              (↑(eix q) : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ) ∧
                (↑(rix
                        (⟨(↑q : ℕ) + (1 : ℕ),
                            Decidable.byContradiction
                              fun (a : ¬(↑q : ℕ) + (1 : ℕ) < T.length - (1 : ℕ)) ↦ by
                              omega⟩ :
                          Fin (T.length - (1 : ℕ)))) :
                    ℕ) =
                  C.p + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ)) →
    let ne : Fin T.length → E := fun (q : Fin T.length) ↦
      if hq : (↑q : ℕ) < T.length - (2 : ℕ) then
        T.edge (eix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (2 : ℕ))))
      else if (↑q : ℕ) = T.length - (2 : ℕ) then a0 else a1;
    (∀ (q : Fin (T.length - (2 : ℕ))),
        ne
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
              Fin T.length) =
          T.edge (eix q)) →
    ∀ (q : Fin T.length),
    (↑q : ℕ) < T.length - (2 : ℕ) →
    ∃ (a : Fin ((↑q : ℕ) + (1 : ℕ))),
    G.ends (ne q) =
      s(nv q.succ, nv (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt)))) := by
  classical
  intro V E _ _ _ G k e0 phi T C i u0 u1 hpTwo hlength hlenThree m hmTwo a0 a1 rix rix_val nv
      nv_retained eix eix_val later_indices ne ne_retained q hret
  let qr : Fin (T.length - 2) := ⟨q.val, hret⟩
  by_cases hbefore : q.val < m - 1
  · have heixval : (eix qr).val = q.val := by
      rw [eix_val]
      simp [qr, hbefore]
    obtain ⟨a, ha⟩ := T.attaches (eix qr)
    let a' : Fin (q.val + 1) := ⟨a.val, by omega⟩
    refine ⟨a', ?_⟩
    have hne : ne q = T.edge (eix qr) := by
      simpa [qr] using ne_retained qr
    have hnew : nv q.succ = T.vertex (eix qr).succ := by
      have hqsucc : q.val + 1 < T.length - 1 := by omega
      have hrix : rix ⟨q.val + 1, hqsucc⟩ = (eix qr).succ := by
        apply Fin.ext
        rw [rix_val]
        have hm' : q.val + 1 < m := by omega
        simp only [ite_eq_left hm']
        dsimp
        omega
      have hsuc : q.succ = ⟨q.val + 1, by omega⟩ := Fin.ext rfl
      rw [hsuc]
      calc
        nv ⟨q.val + 1, by omega⟩ =
            T.vertex (rix ⟨q.val + 1, hqsucc⟩) :=
          nv_retained ⟨q.val + 1, hqsucc⟩
        _ = T.vertex (eix qr).succ := congrArg T.vertex hrix
    have hold :
        nv (Fin.castLT a'
          (Nat.lt_trans a'.isLt (Nat.succ_lt_succ q.isLt))) =
          T.vertex (Fin.castLT a
            (Nat.lt_trans a.isLt (Nat.succ_lt_succ (eix qr).isLt))) := by
      have haval : a.val < m := by omega
      have haNewLt : a'.val < T.length - 1 := by omega
      have hcast :
          Fin.castLT a'
            (Nat.lt_trans a'.isLt (Nat.succ_lt_succ q.isLt)) =
            ⟨a'.val, by omega⟩ := Fin.ext rfl
      rw [hcast]
      calc
        nv ⟨a'.val, by omega⟩ =
            T.vertex (rix ⟨a'.val, haNewLt⟩) :=
          nv_retained ⟨a'.val, haNewLt⟩
        _ = T.vertex (Fin.castLT a
            (Nat.lt_trans a.isLt (Nat.succ_lt_succ (eix qr).isLt))) := by
          apply congrArg T.vertex
          apply Fin.ext
          rw [rix_val]
          have ha'val : a'.val < m := by dsimp [a']; exact haval
          simp only [ite_eq_left ha'val]
          rfl
    rw [hne, hnew, hold]
    exact ha
  · have hafter : m - 1 ≤ q.val := by omega
    obtain ⟨r, j, hri, heixval, hrixval⟩ := later_indices qr hafter
    obtain ⟨b, hb⟩ := C.block_attaches_to_base r j
    let b' : Fin (q.val + 1) := ⟨b.val, by dsimp [m] at hafter; omega⟩
    refine ⟨b', ?_⟩
    have hedge : ne q = C.blockEdge r j := by
      rw [show ne q = T.edge (eix qr) by simpa [qr] using ne_retained qr]
      calc
        T.edge (eix qr) =
            T.edge ⟨C.p - 1 + 2 * r.val + j.val, by omega⟩ := by
          apply congrArg T.edge
          apply Fin.ext
          exact heixval
        _ = C.blockEdge r j := C.block_edge_position r j
    have hnew : nv q.succ = C.blockVertex r j := by
      have hqsucc : q.val + 1 < T.length - 1 := by omega
      have hrix : rix ⟨q.val + 1, hqsucc⟩ =
          ⟨C.p + 2 * r.val + j.val, by omega⟩ := Fin.ext hrixval
      have hsuc : q.succ = ⟨q.val + 1, by omega⟩ := Fin.ext rfl
      rw [hsuc]
      calc
        nv ⟨q.val + 1, by omega⟩ =
            T.vertex (rix ⟨q.val + 1, hqsucc⟩) :=
          nv_retained ⟨q.val + 1, hqsucc⟩
        _ = T.vertex ⟨C.p + 2 * r.val + j.val, by omega⟩ := by rw [hrix]
        _ = C.blockVertex r j := C.block_vertex_position r j
    have hold :
        nv (Fin.castLT b'
          (Nat.lt_trans b'.isLt (Nat.succ_lt_succ q.isLt))) = C.y b := by
      have hbval : b.val < m := by dsimp [m]; omega
      have hbNewLt : b'.val < T.length - 1 := by omega
      have hcast :
          Fin.castLT b'
            (Nat.lt_trans b'.isLt (Nat.succ_lt_succ q.isLt)) =
            ⟨b'.val, by omega⟩ := Fin.ext rfl
      rw [hcast]
      have hrix : rix ⟨b'.val, by omega⟩ =
          ⟨b.val, by omega⟩ := by
        apply Fin.ext
        rw [rix_val]
        have hb'val : b'.val < m := by dsimp [b']; exact hbval
        simp only [ite_eq_left hb'val]
        rfl
      calc
        nv ⟨b'.val, by omega⟩ =
            T.vertex (rix ⟨b'.val, hbNewLt⟩) :=
          nv_retained ⟨b'.val, hbNewLt⟩
        _ = T.vertex ⟨b.val, by omega⟩ := by rw [hrix]
        _ = C.y b := C.base_vertex_position b
    rw [hedge, hnew, hold]
    exact hb.trans Sym2.eq_swap

private theorem helper_branch_696.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s),
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    let X : Finset V := TreeSequenceVertexSet T;
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m) (a0 a1 : E) (w0 : V),
    G.ends a0 = s(u0, w0) →
    ∀ (w1 : V),
    G.ends a1 = s(u1, w1) →
    w0 ≠ u0 →
    w1 ≠ u1 →
    w0 ∈ X →
    w1 ∈ X →
    ¬w0 = u1 →
    w1 ≠ u0 →
    let rix : Fin (T.length - (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
      fun (q : Fin (T.length - (1 : ℕ))) ↦
      if hqm : (↑q : ℕ) < m then
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ)))
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) ↦
              by omega⟩ :
          Fin (T.length + (1 : ℕ)));
    let nv : Fin (T.length + (1 : ℕ)) → V := fun (q : Fin (T.length + (1 : ℕ))) ↦
      if hq : (↑q : ℕ) < T.length - (1 : ℕ) then
        T.vertex (rix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (1 : ℕ))))
      else if (↑q : ℕ) = T.length - (1 : ℕ) then u0 else u1;
    nv
          (⟨T.length - (1 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length + (1 : ℕ)) ↦
                by omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u0 →
    nv
          (⟨T.length,
              Decidable.byContradiction fun (a : ¬T.length < T.length + (1 : ℕ)) ↦ by
                omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u1 →
    (∀ {w : V},
        w ∈ X →
          w ≠ u0 →
            w ≠ u1 →
              ∃ (q : Fin (T.length - (1 : ℕ))),
                nv
                    (⟨(↑q : ℕ),
                        Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦
                          by omega⟩ :
                      Fin (T.length + (1 : ℕ))) =
                  w) →
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    let ne : Fin T.length → E := fun (q : Fin T.length) ↦
      if hq : (↑q : ℕ) < T.length - (2 : ℕ) then
        T.edge (eix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (2 : ℕ))))
      else if (↑q : ℕ) = T.length - (2 : ℕ) then a0 else a1;
    ne
          (⟨T.length - (2 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) < T.length) ↦ by
                omega⟩ :
            Fin T.length) =
        a0 →
    ne
          (⟨T.length - (1 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by
                omega⟩ :
            Fin T.length) =
        a1 →
    ∀ (q : Fin T.length),
    ¬(↑q : ℕ) < T.length - (2 : ℕ) →
    ∃ (a : Fin ((↑q : ℕ) + (1 : ℕ))),
    G.ends (ne q) =
      s(nv q.succ, nv (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt)))) := by
  classical
  intro V E _ _ _ G k e0 phi T C i u0 u1 X hlength hlenThree m hmTwo a0 a1 w0 ha0Ends w1 ha1Ends
      hw0ne hw1ne hw0X hw1X hw0u1 hw1u0 rix nv nv_penultimate nv_last retained_vertex_index eix
      ne ne_penultimate ne_last q hret
  have hlast : q.val = T.length - 2 ∨ q.val = T.length - 1 := by omega
  rcases hlast with hq | hq
  · obtain ⟨a, ha⟩ := retained_vertex_index hw0X hw0ne hw0u1
    let a' : Fin (q.val + 1) := ⟨a.val, by omega⟩
    refine ⟨a', ?_⟩
    have hqe : q = ⟨T.length - 2, by omega⟩ := Fin.ext (by omega)
    have haCast :
        (Fin.castLT a'
          (Nat.lt_trans a'.isLt (Nat.succ_lt_succ q.isLt))) =
          ⟨a.val, by omega⟩ := Fin.ext rfl
    have hedge : ne q = a0 := (congrArg ne hqe).trans ne_penultimate
    have hsuc : q.succ = ⟨T.length - 1, by omega⟩ := by
      apply Fin.ext
      change q.val + 1 = T.length - 1
      omega
    have hnew : nv q.succ = u0 := by rw [hsuc]; exact nv_penultimate
    have hold : nv (Fin.castLT a'
          (Nat.lt_trans a'.isLt (Nat.succ_lt_succ q.isLt))) = w0 := by
      rw [haCast]
      exact ha
    rw [hedge, hnew, hold]
    exact ha0Ends
  · obtain ⟨a, ha⟩ := retained_vertex_index hw1X hw1u0 hw1ne
    let a' : Fin (q.val + 1) := ⟨a.val, by omega⟩
    refine ⟨a', ?_⟩
    have hqe : q = ⟨T.length - 1, by omega⟩ := Fin.ext (by omega)
    have haCast :
        (Fin.castLT a'
          (Nat.lt_trans a'.isLt (Nat.succ_lt_succ q.isLt))) =
          ⟨a.val, by omega⟩ := Fin.ext rfl
    have hedge : ne q = a1 := (congrArg ne hqe).trans ne_last
    have hsuc : q.succ = ⟨T.length, by omega⟩ := by
      apply Fin.ext
      change q.val + 1 = T.length
      omega
    have hnew : nv q.succ = u1 := by rw [hsuc]; exact nv_last
    have hold : nv (Fin.castLT a'
          (Nat.lt_trans a'.isLt (Nat.succ_lt_succ q.isLt))) = w1 := by
      rw [haCast]
      exact ha
    rw [hedge, hnew, hold]
    exact ha1Ends

private theorem helper_hattaches_522.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s),
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    let X : Finset V := TreeSequenceVertexSet T;
    (2 : ℕ) ≤ C.p →
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m) (_ : m + (1 : ℕ) ≤ T.length) (a0 a1 : E) (w0 : V),
    G.ends a0 = s(u0, w0) →
    ∀ (w1 : V),
    G.ends a1 = s(u1, w1) →
    w0 ≠ u0 →
    w1 ≠ u1 →
    w0 ∈ X →
    w1 ∈ X →
    ¬w0 = u1 →
    w1 ≠ u0 →
    let rix : Fin (T.length - (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
      fun (q : Fin (T.length - (1 : ℕ))) ↦
      if hqm : (↑q : ℕ) < m then
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ)))
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) ↦
              by omega⟩ :
          Fin (T.length + (1 : ℕ)));
    (∀ (q : Fin (T.length - (1 : ℕ))),
        (↑(rix q) : ℕ) = if (↑q : ℕ) < m then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    let nv : Fin (T.length + (1 : ℕ)) → V := fun (q : Fin (T.length + (1 : ℕ))) ↦
      if hq : (↑q : ℕ) < T.length - (1 : ℕ) then
        T.vertex (rix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (1 : ℕ))))
      else if (↑q : ℕ) = T.length - (1 : ℕ) then u0 else u1;
    (∀ (q : Fin (T.length - (1 : ℕ))),
        nv
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by
                  omega⟩ :
              Fin (T.length + (1 : ℕ))) =
          T.vertex (rix q)) →
    nv
          (⟨T.length - (1 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length + (1 : ℕ)) ↦
                by omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u0 →
    nv
          (⟨T.length,
              Decidable.byContradiction fun (a : ¬T.length < T.length + (1 : ℕ)) ↦ by
                omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u1 →
    (∀ {w : V},
        w ∈ X →
          w ≠ u0 →
            w ≠ u1 →
              ∃ (q : Fin (T.length - (1 : ℕ))),
                nv
                    (⟨(↑q : ℕ),
                        Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦
                          by omega⟩ :
                      Fin (T.length + (1 : ℕ))) =
                  w) →
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (↑(eix q) : ℕ) = if (↑q : ℕ) < m - (1 : ℕ) then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    (∀ (q : Fin (T.length - (2 : ℕ))),
        m - (1 : ℕ) ≤ (↑q : ℕ) →
          ∃ (r : Fin C.s) (j : Fin (2 : ℕ)),
            (↑i : ℕ) < (↑r : ℕ) ∧
              (↑(eix q) : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ) ∧
                (↑(rix
                        (⟨(↑q : ℕ) + (1 : ℕ),
                            Decidable.byContradiction
                              fun (a : ¬(↑q : ℕ) + (1 : ℕ) < T.length - (1 : ℕ)) ↦ by
                              omega⟩ :
                          Fin (T.length - (1 : ℕ)))) :
                    ℕ) =
                  C.p + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ)) →
    let ne : Fin T.length → E := fun (q : Fin T.length) ↦
      if hq : (↑q : ℕ) < T.length - (2 : ℕ) then
        T.edge (eix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (2 : ℕ))))
      else if (↑q : ℕ) = T.length - (2 : ℕ) then a0 else a1;
    (∀ (q : Fin (T.length - (2 : ℕ))),
        ne
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
              Fin T.length) =
          T.edge (eix q)) →
    ne
          (⟨T.length - (2 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) < T.length) ↦ by
                omega⟩ :
            Fin T.length) =
        a0 →
    ne
          (⟨T.length - (1 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by
                omega⟩ :
            Fin T.length) =
        a1 →
    ∀ (q : Fin T.length),
    ∃ (a : Fin ((↑q : ℕ) + (1 : ℕ))),
    G.ends (ne q) =
      s(nv q.succ, nv (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt)))) := by
  classical
  intro V E _ _ _ G k e0 phi T C i u0 u1 X hpTwo hlength hlenThree m hmTwo hmLast a0 a1 w0
      ha0Ends w1 ha1Ends hw0ne hw1ne hw0X hw1X hw0u1 hw1u0 rix rix_val nv nv_retained
      nv_penultimate nv_last retained_vertex_index eix eix_val later_indices ne ne_retained
      ne_penultimate ne_last q
  by_cases hret : q.val < T.length - 2
  · exact @helper_branch_593 V E inferInstance inferInstance inferInstance G k e0 phi T C i hpTwo
      hlength hlenThree hmTwo a0 a1 rix_val nv_retained eix_val later_indices ne_retained q hret
  · exact @helper_branch_696 V E inferInstance inferInstance inferInstance G k e0 phi T C i
      hlength hlenThree hmTwo a0 a1 w0 ha0Ends w1 ha1Ends hw0ne hw1ne hw0X hw1X hw0u1 hw1u0
      nv_penultimate nv_last retained_vertex_index ne_penultimate ne_last q hret
private theorem helper_branch_862.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s),
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    (2 : ℕ) ≤ C.p →
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m) (a0 a1 : E),
    let rix : Fin (T.length - (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
      fun (q : Fin (T.length - (1 : ℕ))) ↦
      if hqm : (↑q : ℕ) < m then
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ)))
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) ↦
              by omega⟩ :
          Fin (T.length + (1 : ℕ)));
    (∀ (q : Fin (T.length - (1 : ℕ))),
        (↑(rix q) : ℕ) = if (↑q : ℕ) < m then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    let nv : Fin (T.length + (1 : ℕ)) → V := fun (q : Fin (T.length + (1 : ℕ))) ↦
      if hq : (↑q : ℕ) < T.length - (1 : ℕ) then
        T.vertex (rix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (1 : ℕ))))
      else if (↑q : ℕ) = T.length - (1 : ℕ) then u0 else u1;
    (∀ (q : Fin (T.length - (1 : ℕ))),
        nv
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by
                  omega⟩ :
              Fin (T.length + (1 : ℕ))) =
          T.vertex (rix q)) →
    ∀ (nv_injective : Function.Injective nv),
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (↑(eix q) : ℕ) = if (↑q : ℕ) < m - (1 : ℕ) then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    (∀ (q : Fin (T.length - (2 : ℕ))),
        m - (1 : ℕ) ≤ (↑q : ℕ) →
          ∃ (r : Fin C.s) (j : Fin (2 : ℕ)),
            (↑i : ℕ) < (↑r : ℕ) ∧
              (↑(eix q) : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ) ∧
                (↑(rix
                        (⟨(↑q : ℕ) + (1 : ℕ),
                            Decidable.byContradiction
                              fun (a : ¬(↑q : ℕ) + (1 : ℕ) < T.length - (1 : ℕ)) ↦ by
                              omega⟩ :
                          Fin (T.length - (1 : ℕ)))) :
                    ℕ) =
                  C.p + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ)) →
    let ne : Fin T.length → E := fun (q : Fin T.length) ↦
      if hq : (↑q : ℕ) < T.length - (2 : ℕ) then
        T.edge (eix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (2 : ℕ))))
      else if (↑q : ℕ) = T.length - (2 : ℕ) then a0 else a1;
    (∀ (q : Fin (T.length - (2 : ℕ))),
        ne
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
              Fin T.length) =
          T.edge (eix q)) →
    ∀ (ne_injective : Function.Injective ne)
      (hfirst : ne (⟨(0 : ℕ), T.positive⟩ : Fin T.length) = e0)
      (hattaches :
        ∀ (q : Fin T.length),
          ∃ (a : Fin ((↑q : ℕ) + (1 : ℕ))),
            G.ends (ne q) =
              s(nv q.succ, nv (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))))),
    let T' : TreeSequence G e0 :=
      { length := T.length, positive := T.positive, vertex := nv, edge := ne,
        vertex_injective := nv_injective, edge_injective := ne_injective,
        first_edge := hfirst, attaches := hattaches : TreeSequence G e0 };
    ∀ (q : Fin T'.length),
    (1 : ℕ) ≤ (↑q : ℕ) →
    (↑q : ℕ) < T.length →
    (↑q : ℕ) < T.length - (2 : ℕ) →
    ∃ (a : Fin ((↑q : ℕ) + (1 : ℕ))) (c : Fin k),
    phi (ne q) = some c ∧
      c ∈
        MissingColors G phi (nv (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt)))) := by
  classical
  intro V E _ _ _ G k e0 phi T C i u0 u1 hpTwo hlength hlenThree m hmTwo a0 a1 rix rix_val nv
      nv_retained nv_injective eix eix_val later_indices ne ne_retained ne_injective hfirst
      hattaches T' q hqpos hqLt hret
  let qr : Fin (T.length - 2) := ⟨q.val, hret⟩
  by_cases hbefore : q.val < m - 1
  · have heixval : (eix qr).val = q.val := by
      rw [eix_val]
      simp [qr, hbefore]
    obtain ⟨a, c, hc, hm⟩ := C.globally_maximum.2.1 (eix qr) (by omega)
    let a' : Fin (q.val + 1) := ⟨a.val, by omega⟩
    refine ⟨a', c, ?_, ?_⟩
    · rw [show ne q = T.edge (eix qr) by simpa [qr] using ne_retained qr]
      exact hc
    · have haval : a.val < m := by omega
      have haNewLt : a'.val < T.length - 1 := by omega
      have hcast :
          Fin.castLT a'
            (Nat.lt_trans a'.isLt (Nat.succ_lt_succ q.isLt)) =
            ⟨a'.val, by omega⟩ := Fin.ext rfl
      rw [hcast]
      have hrix : rix ⟨a'.val, haNewLt⟩ =
          Fin.castLT a
            (Nat.lt_trans a.isLt
              (Nat.succ_lt_succ (eix qr).isLt)) := by
        apply Fin.ext
        rw [rix_val]
        have ha'val : a'.val < m := by dsimp [a']; exact haval
        simp only [ite_eq_left ha'val]
        rfl
      have hnv : nv ⟨a'.val, by omega⟩ =
          T.vertex (Fin.castLT a
            (Nat.lt_trans a.isLt
              (Nat.succ_lt_succ (eix qr).isLt))) := by
        calc
          nv ⟨a'.val, by omega⟩ =
              T.vertex (rix ⟨a'.val, haNewLt⟩) :=
            nv_retained ⟨a'.val, haNewLt⟩
          _ = _ := congrArg T.vertex hrix
      rw [hnv]
      exact hm
  · have hafter : m - 1 ≤ q.val := by omega
    obtain ⟨r, j, hri, heixval, _⟩ := later_indices qr hafter
    obtain ⟨b, hb⟩ := C.block_color_missing_on_base r
    let b' : Fin (q.val + 1) := ⟨b.val, by dsimp [m] at hafter; omega⟩
    refine ⟨b', C.gamma r, ?_, ?_⟩
    · rw [show ne q = T.edge (eix qr) by simpa [qr] using ne_retained qr]
      have hedge : T.edge (eix qr) = C.blockEdge r j := by
        calc
          T.edge (eix qr) =
              T.edge ⟨C.p - 1 + 2 * r.val + j.val, by omega⟩ := by
            apply congrArg T.edge
            apply Fin.ext
            exact heixval
          _ = C.blockEdge r j := C.block_edge_position r j
      rw [hedge]
      exact C.block_color r j
    · have hbval : b.val < m := by dsimp [m]; omega
      have hbNewLt : b'.val < T.length - 1 := by omega
      have hcast :
          Fin.castLT b'
            (Nat.lt_trans b'.isLt (Nat.succ_lt_succ q.isLt)) =
            ⟨b'.val, by omega⟩ := Fin.ext rfl
      have hrix : rix ⟨b'.val, hbNewLt⟩ = ⟨b.val, by omega⟩ := by
        apply Fin.ext
        rw [rix_val]
        have hb'val : b'.val < m := by dsimp [b']; exact hbval
        simp only [ite_eq_left hb'val]
        rfl
      have hnv : nv (Fin.castLT b'
            (Nat.lt_trans b'.isLt (Nat.succ_lt_succ q.isLt))) = C.y b := by
        rw [hcast]
        calc
          nv ⟨b'.val, by omega⟩ =
              T.vertex (rix ⟨b'.val, hbNewLt⟩) :=
            nv_retained ⟨b'.val, hbNewLt⟩
          _ = T.vertex ⟨b.val, by omega⟩ := by rw [hrix]
          _ = C.y b := C.base_vertex_position b
      rw [hnv]
      exact hb

private theorem helper_htash_685.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s) (alpha : Fin k) (z : V),
    alpha ∈ MissingColors G phi z →
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    let X : Finset V := TreeSequenceVertexSet T;
    z ∈ X →
    (2 : ℕ) ≤ C.p →
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m) (_ : m + (1 : ℕ) ≤ T.length),
    z ≠ u0 →
    z ≠ u1 →
    ∀ (a0 : E),
    phi a0 = some alpha →
    ∀ (a1 : E),
    phi a1 = some alpha →
    let rix : Fin (T.length - (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
      fun (q : Fin (T.length - (1 : ℕ))) ↦
      if hqm : (↑q : ℕ) < m then
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ)))
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) ↦
              by omega⟩ :
          Fin (T.length + (1 : ℕ)));
    (∀ (q : Fin (T.length - (1 : ℕ))),
        (↑(rix q) : ℕ) = if (↑q : ℕ) < m then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    let nv : Fin (T.length + (1 : ℕ)) → V := fun (q : Fin (T.length + (1 : ℕ))) ↦
      if hq : (↑q : ℕ) < T.length - (1 : ℕ) then
        T.vertex (rix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (1 : ℕ))))
      else if (↑q : ℕ) = T.length - (1 : ℕ) then u0 else u1;
    (∀ (q : Fin (T.length - (1 : ℕ))),
        nv
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by
                  omega⟩ :
              Fin (T.length + (1 : ℕ))) =
          T.vertex (rix q)) →
    ∀ (nv_injective : Function.Injective nv),
    (∀ {w : V},
        w ∈ X →
          w ≠ u0 →
            w ≠ u1 →
              ∃ (q : Fin (T.length - (1 : ℕ))),
                nv
                    (⟨(↑q : ℕ),
                        Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦
                          by omega⟩ :
                      Fin (T.length + (1 : ℕ))) =
                  w) →
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (↑(eix q) : ℕ) = if (↑q : ℕ) < m - (1 : ℕ) then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    (∀ (q : Fin (T.length - (2 : ℕ))),
        m - (1 : ℕ) ≤ (↑q : ℕ) →
          ∃ (r : Fin C.s) (j : Fin (2 : ℕ)),
            (↑i : ℕ) < (↑r : ℕ) ∧
              (↑(eix q) : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ) ∧
                (↑(rix
                        (⟨(↑q : ℕ) + (1 : ℕ),
                            Decidable.byContradiction
                              fun (a : ¬(↑q : ℕ) + (1 : ℕ) < T.length - (1 : ℕ)) ↦ by
                              omega⟩ :
                          Fin (T.length - (1 : ℕ)))) :
                    ℕ) =
                  C.p + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ)) →
    let ne : Fin T.length → E := fun (q : Fin T.length) ↦
      if hq : (↑q : ℕ) < T.length - (2 : ℕ) then
        T.edge (eix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (2 : ℕ))))
      else if (↑q : ℕ) = T.length - (2 : ℕ) then a0 else a1;
    (∀ (q : Fin (T.length - (2 : ℕ))),
        ne
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
              Fin T.length) =
          T.edge (eix q)) →
    ne
          (⟨T.length - (2 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) < T.length) ↦ by
                omega⟩ :
            Fin T.length) =
        a0 →
    ne
          (⟨T.length - (1 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by
                omega⟩ :
            Fin T.length) =
        a1 →
    ∀ (ne_injective : Function.Injective ne)
      (hfirst : ne (⟨(0 : ℕ), T.positive⟩ : Fin T.length) = e0)
      (hattaches :
        ∀ (q : Fin T.length),
          ∃ (a : Fin ((↑q : ℕ) + (1 : ℕ))),
            G.ends (ne q) =
              s(nv q.succ, nv (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))))),
    let T' : TreeSequence G e0 :=
      { length := T.length, positive := T.positive, vertex := nv, edge := ne,
        vertex_injective := nv_injective, edge_injective := ne_injective,
        first_edge := hfirst, attaches := hattaches : TreeSequence G e0 };
    TashkinovTree G e0 phi T' := by
  classical
  intro V E _ _ _ G k e0 phi T C i alpha z hzMissing u0 u1 X hzX hpTwo hlength hlenThree m hmTwo
      hmLast hzu0 hzu1 a0 ha0Color a1 ha1Color rix rix_val nv nv_retained nv_injective
      retained_vertex_index eix eix_val later_indices ne ne_retained ne_penultimate ne_last
      ne_injective hfirst hattaches T' q hqpos
  have hqLt : q.val < T.length := by simp [T']
  change ∃ a : Fin (q.val + 1), ∃ c : Fin k,
    phi (ne q) = some c ∧
      c ∈ MissingColors G phi
        (nv (Fin.castLT a
          (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))))
  by_cases hret : q.val < T.length - 2
  · exact @helper_branch_862 V E inferInstance inferInstance inferInstance G k e0 phi T C i hpTwo
      hlength hlenThree hmTwo a0 a1 rix_val nv_retained nv_injective eix_val later_indices
      ne_retained ne_injective hfirst hattaches q hqpos hqLt hret
  · have hlast : q.val = T.length - 2 ∨ q.val = T.length - 1 := by omega
    obtain ⟨a, ha⟩ := retained_vertex_index hzX hzu0 hzu1
    let a' : Fin (q.val + 1) := ⟨a.val, by rcases hlast with h | h <;> omega⟩
    refine ⟨a', alpha, ?_, ?_⟩
    · rcases hlast with hq | hq
      · have hqe : q = ⟨T.length - 2, by omega⟩ := Fin.ext (by omega)
        exact (congrArg (fun e => phi e) ((congrArg ne hqe).trans ne_penultimate)).trans
          ha0Color
      · have hqe : q = ⟨T.length - 1, by omega⟩ := Fin.ext (by omega)
        exact (congrArg (fun e => phi e) ((congrArg ne hqe).trans ne_last)).trans
          ha1Color
    · have hcast :
          Fin.castLT a'
            (Nat.lt_trans a'.isLt (Nat.succ_lt_succ q.isLt)) =
            ⟨a.val, by omega⟩ := Fin.ext rfl
      rw [hcast, ha]
      exact hzMissing

private theorem helper_hvertexSet_788.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s),
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    let X : Finset V := TreeSequenceVertexSet T;
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m) (_ : m + (1 : ℕ) ≤ T.length),
    u0 ∈ X →
    u1 ∈ X →
    ∀ (a0 a1 : E),
    let rix : Fin (T.length - (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
      fun (q : Fin (T.length - (1 : ℕ))) ↦
      if hqm : (↑q : ℕ) < m then
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ)))
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) ↦
              by omega⟩ :
          Fin (T.length + (1 : ℕ)));
    let nv : Fin (T.length + (1 : ℕ)) → V := fun (q : Fin (T.length + (1 : ℕ))) ↦
      if hq : (↑q : ℕ) < T.length - (1 : ℕ) then
        T.vertex (rix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (1 : ℕ))))
      else if (↑q : ℕ) = T.length - (1 : ℕ) then u0 else u1;
    (∀ (q : Fin (T.length - (1 : ℕ))),
        nv
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by
                  omega⟩ :
              Fin (T.length + (1 : ℕ))) =
          T.vertex (rix q)) →
    nv
          (⟨T.length - (1 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length + (1 : ℕ)) ↦
                by omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u0 →
    nv
          (⟨T.length,
              Decidable.byContradiction fun (a : ¬T.length < T.length + (1 : ℕ)) ↦ by
                omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u1 →
    ∀ (nv_injective : Function.Injective nv),
    (∀ {w : V},
        w ∈ X →
          w ≠ u0 →
            w ≠ u1 →
              ∃ (q : Fin (T.length - (1 : ℕ))),
                nv
                    (⟨(↑q : ℕ),
                        Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦
                          by omega⟩ :
                      Fin (T.length + (1 : ℕ))) =
                  w) →
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    let ne : Fin T.length → E := fun (q : Fin T.length) ↦
      if hq : (↑q : ℕ) < T.length - (2 : ℕ) then
        T.edge (eix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (2 : ℕ))))
      else if (↑q : ℕ) = T.length - (2 : ℕ) then a0 else a1;
    ∀ (ne_injective : Function.Injective ne)
      (hfirst : ne (⟨(0 : ℕ), T.positive⟩ : Fin T.length) = e0)
      (hattaches :
        ∀ (q : Fin T.length),
          ∃ (a : Fin ((↑q : ℕ) + (1 : ℕ))),
            G.ends (ne q) =
              s(nv q.succ, nv (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))))),
    let T' : TreeSequence G e0 :=
      { length := T.length, positive := T.positive, vertex := nv, edge := ne,
        vertex_injective := nv_injective, edge_injective := ne_injective,
        first_edge := hfirst, attaches := hattaches : TreeSequence G e0 };
    TreeSequenceVertexSet T' = X := by
  classical
  intro V E _ _ _ G k e0 phi T C i u0 u1 X hlength hlenThree m hmTwo hmLast hu0X hu1X a0 a1 rix
      nv nv_retained nv_penultimate nv_last nv_injective retained_vertex_index eix ne
      ne_injective hfirst hattaches T'
  ext w
  constructor
  · intro hw
    have hw' : ∃ q : Fin (T.length + 1), nv q = w := by
      simpa [TreeSequenceVertexSet, T'] using hw
    obtain ⟨q, hq⟩ := hw'
    by_cases hret : q.val < T.length - 1
    · let qr : Fin (T.length - 1) := ⟨q.val, hret⟩
      have hnv : nv q = T.vertex (rix qr) := by
        have he : q = ⟨qr.val, by omega⟩ := Fin.ext rfl
        rw [he]
        exact nv_retained qr
      rw [hnv] at hq
      rw [← hq]
      simp [X, TreeSequenceVertexSet]
    · have hlast : q.val = T.length - 1 ∨ q.val = T.length := by omega
      rcases hlast with hlast | hlast
      · have he : q = ⟨T.length - 1, by omega⟩ := Fin.ext (by omega)
        have : w = u0 := by simpa [he, nv_penultimate] using hq.symm
        simpa [this] using hu0X
      · have he : q = ⟨T.length, by omega⟩ := Fin.ext (by omega)
        have : w = u1 := by simpa [he, nv_last] using hq.symm
        simpa [this] using hu1X
  · intro hw
    by_cases hwu0 : w = u0
    · subst w
      have hw' : ∃ q : Fin (T.length + 1), nv q = u0 :=
        ⟨⟨T.length - 1, by omega⟩, nv_penultimate⟩
      simpa [TreeSequenceVertexSet, T'] using hw'
    · by_cases hwu1 : w = u1
      · subst w
        have hw' : ∃ q : Fin (T.length + 1), nv q = u1 :=
          ⟨⟨T.length, by omega⟩, nv_last⟩
        simpa [TreeSequenceVertexSet, T'] using hw'
      · obtain ⟨q, hq⟩ := retained_vertex_index hw hwu0 hwu1
        have hw' : ∃ r : Fin (T.length + 1), nv r = w :=
          ⟨⟨q.val, by omega⟩, hq⟩
        simpa [TreeSequenceVertexSet, T'] using hw'

private theorem helper_hgammaUnused_842.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s) (alpha : Fin k),
    alpha ≠ C.gamma i →
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m) (_ : m + (1 : ℕ) ≤ T.length) (a0 : E),
    phi a0 = some alpha →
    ∀ (a1 : E),
    phi a1 = some alpha →
    let rix : Fin (T.length - (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
      fun (q : Fin (T.length - (1 : ℕ))) ↦
      if hqm : (↑q : ℕ) < m then
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ)))
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) ↦
              by omega⟩ :
          Fin (T.length + (1 : ℕ)));
    let nv : Fin (T.length + (1 : ℕ)) → V := fun (q : Fin (T.length + (1 : ℕ))) ↦
      if hq : (↑q : ℕ) < T.length - (1 : ℕ) then
        T.vertex (rix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (1 : ℕ))))
      else if (↑q : ℕ) = T.length - (1 : ℕ) then u0 else u1;
    ∀ (nv_injective : Function.Injective nv),
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (↑(eix q) : ℕ) = if (↑q : ℕ) < m - (1 : ℕ) then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    (∀ (q : Fin (T.length - (2 : ℕ))),
        m - (1 : ℕ) ≤ (↑q : ℕ) →
          ∃ (r : Fin C.s) (j : Fin (2 : ℕ)),
            (↑i : ℕ) < (↑r : ℕ) ∧
              (↑(eix q) : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ) ∧
                (↑(rix
                        (⟨(↑q : ℕ) + (1 : ℕ),
                            Decidable.byContradiction
                              fun (a : ¬(↑q : ℕ) + (1 : ℕ) < T.length - (1 : ℕ)) ↦ by
                              omega⟩ :
                          Fin (T.length - (1 : ℕ)))) :
                    ℕ) =
                  C.p + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ)) →
    (∀ (q : Fin (T.length - (2 : ℕ))),
        C.p - (1 : ℕ) ≤ (↑q : ℕ) →
          (↑q : ℕ) < m - (1 : ℕ) →
            ∃ (r : Fin C.s) (j : Fin (2 : ℕ)),
              (↑r : ℕ) < (↑i : ℕ) ∧
                (↑(eix q) : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ)) →
    let ne : Fin T.length → E := fun (q : Fin T.length) ↦
      if hq : (↑q : ℕ) < T.length - (2 : ℕ) then
        T.edge (eix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (2 : ℕ))))
      else if (↑q : ℕ) = T.length - (2 : ℕ) then a0 else a1;
    (∀ (q : Fin (T.length - (2 : ℕ))),
        ne
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
              Fin T.length) =
          T.edge (eix q)) →
    ne
          (⟨T.length - (2 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) < T.length) ↦ by
                omega⟩ :
            Fin T.length) =
        a0 →
    ne
          (⟨T.length - (1 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by
                omega⟩ :
            Fin T.length) =
        a1 →
    ∀ (ne_injective : Function.Injective ne)
      (hfirst : ne (⟨(0 : ℕ), T.positive⟩ : Fin T.length) = e0)
      (hattaches :
        ∀ (q : Fin T.length),
          ∃ (a : Fin ((↑q : ℕ) + (1 : ℕ))),
            G.ends (ne q) =
              s(nv q.succ, nv (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))))),
    let T' : TreeSequence G e0 :=
      { length := T.length, positive := T.positive, vertex := nv, edge := ne,
        vertex_injective := nv_injective, edge_injective := ne_injective,
        first_edge := hfirst, attaches := hattaches : TreeSequence G e0 };
    C.gamma i ∉ TreeUsedColors phi T' := by
  classical
  intro V E _ _ _ G k e0 phi T C i alpha hAlphaGamma u0 u1 hlength hlenThree m hmTwo hmLast a0
      ha0Color a1 ha1Color rix nv nv_injective eix eix_val later_indices early_block_indices ne
      ne_retained ne_penultimate ne_last ne_injective hfirst hattaches T' hused
  simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hused
  obtain ⟨q, hqpos, hqcolor⟩ := hused
  have hqLt : q.val < T.length := by simp [T']
  have hqcolor' : phi (ne q) = some (C.gamma i) := by
    simpa [T'] using hqcolor
  by_cases hret : q.val < T.length - 2
  · let qr : Fin (T.length - 2) := ⟨q.val, hret⟩
    have hne : ne q = T.edge (eix qr) := by
      simpa [qr] using ne_retained qr
    by_cases hbefore : q.val < m - 1
    · by_cases hbase : q.val < C.p - 1
      · let b : Fin (C.p - 1) := ⟨q.val, hbase⟩
        have heix : eix qr = ⟨q.val, by omega⟩ := by
          apply Fin.ext
          rw [eix_val]
          simp [qr, hbefore]
        have hedge : T.edge (eix qr) = C.baseEdge b := by
          rw [heix]
          simpa [b] using C.base_edge_position b
        have hc : phi (C.baseEdge b) = some (C.gamma i) := by
          simpa [hne, hedge] using hqcolor'
        exact (C.initial_nonfirst_avoids_blocks b (by dsimp [b]; omega)
          (C.gamma i) hc i) rfl
      · have hbase' : C.p - 1 ≤ q.val := by omega
        obtain ⟨r, j, hri, heixval⟩ :=
          early_block_indices qr hbase' hbefore
        have hedge : T.edge (eix qr) = C.blockEdge r j := by
          calc
            T.edge (eix qr) =
                T.edge ⟨C.p - 1 + 2 * r.val + j.val, by omega⟩ := by
              apply congrArg T.edge
              apply Fin.ext
              exact heixval
            _ = C.blockEdge r j := C.block_edge_position r j
        have hcolors : C.gamma r = C.gamma i := by
          exact Option.some.inj ((C.block_color r j).symm.trans
            (by simpa [hne, hedge] using hqcolor'))
        have hriEq := C.gamma_injective hcolors
        have hv := congrArg Fin.val hriEq
        omega
    · have hafter : m - 1 ≤ q.val := by omega
      obtain ⟨r, j, hri, heixval, _⟩ := later_indices qr hafter
      have hedge : T.edge (eix qr) = C.blockEdge r j := by
        calc
          T.edge (eix qr) =
              T.edge ⟨C.p - 1 + 2 * r.val + j.val, by omega⟩ := by
            apply congrArg T.edge
            apply Fin.ext
            exact heixval
          _ = C.blockEdge r j := C.block_edge_position r j
      have hcolors : C.gamma r = C.gamma i := by
        exact Option.some.inj ((C.block_color r j).symm.trans
          (by simpa [hne, hedge] using hqcolor'))
      have hriEq := C.gamma_injective hcolors
      have hv := congrArg Fin.val hriEq
      omega
  · have hlast : q.val = T.length - 2 ∨ q.val = T.length - 1 := by omega
    rcases hlast with hq | hq
    · have hqe : q = ⟨T.length - 2, by omega⟩ := Fin.ext (by omega)
      have hc : phi a0 = some (C.gamma i) := by
        simpa [hqe, ne_penultimate] using hqcolor'
      exact hAlphaGamma (Option.some.inj (ha0Color.symm.trans hc))
    · have hqe : q = ⟨T.length - 1, by omega⟩ := Fin.ext (by omega)
      have hc : phi a1 = some (C.gamma i) := by
        simpa [hqe, ne_last] using hqcolor'
      exact hAlphaGamma (Option.some.inj (ha1Color.symm.trans hc))

private theorem helper_early_block_indices_1415.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s),
    (2 : ℕ) ≤ C.p →
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m),
    m + (1 : ℕ) ≤ T.length →
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (↑(eix q) : ℕ) = if (↑q : ℕ) < m - (1 : ℕ) then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    ∀ (q : Fin (T.length - (2 : ℕ))),
    C.p - (1 : ℕ) ≤ (↑q : ℕ) →
    (↑q : ℕ) < m - (1 : ℕ) →
    ∃ (r : Fin C.s) (j : Fin (2 : ℕ)),
    (↑r : ℕ) < (↑i : ℕ) ∧ (↑(eix q) : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ) := by
  classical
  intro V E _ _ _ G k e0 phi T C i hpTwo hlength hlenThree m hmTwo hmLast eix eix_val q hbase hq
  let d := q.val - (C.p - 1)
  let rn := d / 2
  let jn := d % 2
  have hqLt := q.isLt
  have hd : q.val = C.p - 1 + d := by dsimp [d]; omega
  have hdecomp : d = 2 * rn + jn := by
    dsimp [rn, jn]
    omega
  have hjn : jn < 2 := by dsimp [jn]; omega
  have hrn : rn < C.s := by dsimp [rn, d]; omega
  let r : Fin C.s := ⟨rn, hrn⟩
  let j : Fin 2 := ⟨jn, hjn⟩
  refine ⟨r, j, ?_, ?_⟩
  · dsimp [r, rn, d, m] at *
    omega
  · rw [eix_val]
    simp only [ite_eq_left hq]
    dsimp [r, j]
    omega

private theorem helper_hw1u0_1593.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s) (alpha : Fin k),
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    IsProperEdgeColoring G phi →
    u0 ≠ u1 →
    ∀ (a0 : E),
    Incident G u0 a0 →
    phi a0 = some alpha →
    ∀ (a1 : E),
    phi a1 = some alpha →
    ∀ (w0 : V),
    G.ends a0 = s(u0, w0) →
    ∀ (w1 : V),
    G.ends a1 = s(u1, w1) →
    ¬w0 = u1 →
    w1 ≠ u0 := by
  classical
  intro V E _ _ _ G k e0 phi T C i alpha u0 u1 hproper hu01 a0 ha0Inc ha0Color a1 ha1Color w0
      ha0Ends w1 ha1Ends hw0u1 h
  have ha01 : a0 ≠ a1 := by
    intro he
    have : s(u0, w0) = s(u1, u0) := by
      rw [← ha0Ends, he, ha1Ends, h]
    have hw0 : w0 = u1 := by
      have hm := Sym2.eq_iff.mp this
      rcases hm with hsame | hswap
      · exact False.elim (hu01 hsame.1)
      · exact hswap.2
    exact hw0u1 hw0
  exact hproper ha01 ⟨u0, ha0Inc, by simp [Incident, ha1Ends, h]⟩
    ha0Color ha1Color

private theorem helper_eix_injective_1675.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s)
      (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m),
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (↑(eix q) : ℕ) = if (↑q : ℕ) < m - (1 : ℕ) then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    Function.Injective eix := by
  classical
  intro V E _ _ _ G k e0 phi T C i hlength hlenThree m hmTwo eix eix_val q r hqr
  have hqLt := q.isLt
  have hrLt := r.isLt
  by_cases hqm : q.val < m - 1 <;>
    by_cases hrm : r.val < m - 1
  all_goals
    have hv := congrArg Fin.val hqr
    rw [eix_val, eix_val] at hv
    simp [hqm, hrm] at hv
    apply Fin.ext
    omega

private theorem helper_hfirst_1733.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s)
      (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m) (a0 a1 : E),
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (↑(eix q) : ℕ) = if (↑q : ℕ) < m - (1 : ℕ) then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    let ne : Fin T.length → E := fun (q : Fin T.length) ↦
      if hq : (↑q : ℕ) < T.length - (2 : ℕ) then
        T.edge (eix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (2 : ℕ))))
      else if (↑q : ℕ) = T.length - (2 : ℕ) then a0 else a1;
    (∀ (q : Fin (T.length - (2 : ℕ))),
        ne
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
              Fin T.length) =
          T.edge (eix q)) →
    ne (⟨(0 : ℕ), T.positive⟩ : Fin T.length) = e0 := by
  classical
  intro V E _ _ _ G k e0 phi T C i hlength hlenThree m hmTwo a0 a1 eix eix_val ne ne_retained
  have hret : (0 : ℕ) < T.length - 2 := by omega
  let q : Fin (T.length - 2) := ⟨0, hret⟩
  have heix : eix q = ⟨0, T.positive⟩ := by
    apply Fin.ext
    rw [eix_val]
    have hm : (0 : ℕ) < m - 1 := by omega
    simp [q, hm]
  calc
    ne ⟨0, T.positive⟩ = T.edge (eix q) := by
      simpa [q] using ne_retained q
    _ = T.edge ⟨0, T.positive⟩ := by rw [heix]
    _ = e0 := T.first_edge

private theorem helper_continuation_1778.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s) (alpha : Fin k),
    alpha ≠ C.gamma i →
    ∀ (z : V),
    alpha ∈ MissingColors G phi z →
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    let X : Finset V := TreeSequenceVertexSet T;
    z ∈ X →
    (2 : ℕ) ≤ C.p →
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    ∀ (hmTwo : (2 : ℕ) ≤ m) (_ : m + (1 : ℕ) ≤ T.length),
    u0 ∈ X →
    u1 ∈ X →
    z ≠ u0 →
    z ≠ u1 →
    ∀ (a0 : E),
    phi a0 = some alpha →
    ∀ (a1 : E),
    phi a1 = some alpha →
    let rix : Fin (T.length - (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
      fun (q : Fin (T.length - (1 : ℕ))) ↦
      if hqm : (↑q : ℕ) < m then
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ)))
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) ↦
              by omega⟩ :
          Fin (T.length + (1 : ℕ)));
    (∀ (q : Fin (T.length - (1 : ℕ))),
        (↑(rix q) : ℕ) = if (↑q : ℕ) < m then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    let nv : Fin (T.length + (1 : ℕ)) → V := fun (q : Fin (T.length + (1 : ℕ))) ↦
      if hq : (↑q : ℕ) < T.length - (1 : ℕ) then
        T.vertex (rix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (1 : ℕ))))
      else if (↑q : ℕ) = T.length - (1 : ℕ) then u0 else u1;
    (∀ (q : Fin (T.length - (1 : ℕ))),
        nv
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by
                  omega⟩ :
              Fin (T.length + (1 : ℕ))) =
          T.vertex (rix q)) →
    nv
          (⟨T.length - (1 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length + (1 : ℕ)) ↦
                by omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u0 →
    nv
          (⟨T.length,
              Decidable.byContradiction fun (a : ¬T.length < T.length + (1 : ℕ)) ↦ by
                omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u1 →
    Function.Injective nv →
    (∀ {w : V},
        w ∈ X →
          w ≠ u0 →
            w ≠ u1 →
              ∃ (q : Fin (T.length - (1 : ℕ))),
                nv
                    (⟨(↑q : ℕ),
                        Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦
                          by omega⟩ :
                      Fin (T.length + (1 : ℕ))) =
                  w) →
    let eix : Fin (T.length - (2 : ℕ)) → Fin T.length :=
      fun (q : Fin (T.length - (2 : ℕ))) ↦
      if _ : (↑q : ℕ) < m - (1 : ℕ) then
        (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length)
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length) ↦ by omega⟩ :
          Fin T.length);
    (∀ (q : Fin (T.length - (2 : ℕ))),
        (↑(eix q) : ℕ) = if (↑q : ℕ) < m - (1 : ℕ) then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    (∀ (q : Fin (T.length - (2 : ℕ))),
        m - (1 : ℕ) ≤ (↑q : ℕ) →
          ∃ (r : Fin C.s) (j : Fin (2 : ℕ)),
            (↑i : ℕ) < (↑r : ℕ) ∧
              (↑(eix q) : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ) ∧
                (↑(rix
                        (⟨(↑q : ℕ) + (1 : ℕ),
                            Decidable.byContradiction
                              fun (a : ¬(↑q : ℕ) + (1 : ℕ) < T.length - (1 : ℕ)) ↦ by
                              omega⟩ :
                          Fin (T.length - (1 : ℕ)))) :
                    ℕ) =
                  C.p + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ)) →
    (∀ (q : Fin (T.length - (2 : ℕ))),
        C.p - (1 : ℕ) ≤ (↑q : ℕ) →
          (↑q : ℕ) < m - (1 : ℕ) →
            ∃ (r : Fin C.s) (j : Fin (2 : ℕ)),
              (↑r : ℕ) < (↑i : ℕ) ∧
                (↑(eix q) : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑r : ℕ) + (↑j : ℕ)) →
    let ne : Fin T.length → E := fun (q : Fin T.length) ↦
      if hq : (↑q : ℕ) < T.length - (2 : ℕ) then
        T.edge (eix (⟨(↑q : ℕ), hq⟩ : Fin (T.length - (2 : ℕ))))
      else if (↑q : ℕ) = T.length - (2 : ℕ) then a0 else a1;
    (∀ (q : Fin (T.length - (2 : ℕ))),
        ne
            (⟨(↑q : ℕ),
                Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) ↦ by omega⟩ :
              Fin T.length) =
          T.edge (eix q)) →
    ne
          (⟨T.length - (2 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) < T.length) ↦ by
                omega⟩ :
            Fin T.length) =
        a0 →
    ne
          (⟨T.length - (1 : ℕ),
              Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by
                omega⟩ :
            Fin T.length) =
        a1 →
    Function.Injective ne →
    ne (⟨(0 : ℕ), T.positive⟩ : Fin T.length) = e0 →
    (∀ (q : Fin T.length),
        ∃ (a : Fin ((↑q : ℕ) + (1 : ℕ))),
          G.ends (ne q) =
            s(nv q.succ, nv (a.castLT (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))))) →
    False := by
  classical
  intro V E _ _ _ G k e0 phi T C i alpha hAlphaGamma z hzMissing u0 u1 X hzX hpTwo hlength
      hlenThree m hmTwo hmLast hu0X hu1X hzu0 hzu1 a0 ha0Color a1 ha1Color rix rix_val nv
      nv_retained nv_penultimate nv_last nv_injective retained_vertex_index eix eix_val
      later_indices early_block_indices ne ne_retained ne_penultimate ne_last ne_injective hfirst
      hattaches
  let T' : TreeSequence G e0 :=
    { length := T.length
      positive := T.positive
      vertex := nv
      edge := ne
      vertex_injective := nv_injective
      edge_injective := ne_injective
      first_edge := hfirst
      attaches := hattaches }
  have htash : TashkinovTree G e0 phi T' := by
    exact @helper_htash_685 V E inferInstance inferInstance inferInstance G k e0 phi T C i alpha
        z hzMissing hzX hpTwo hlength hlenThree hmTwo hmLast hzu0 hzu1 a0 ha0Color a1 ha1Color
        rix_val nv_retained nv_injective retained_vertex_index eix_val later_indices ne_retained
        ne_penultimate ne_last ne_injective hfirst hattaches
  have hvertexSet : TreeSequenceVertexSet T' = X := by
    exact @helper_hvertexSet_788 V E inferInstance inferInstance inferInstance G k e0 phi T C i
        hlength hlenThree hmTwo hmLast hu0X hu1X a0 a1 nv_retained nv_penultimate nv_last
        nv_injective retained_vertex_index ne_injective hfirst hattaches
  have hglobal' : GlobalMaximumTriple G k e0 phi T' := by
    refine ⟨C.globally_maximum.1, htash, ?_⟩
    rw [hvertexSet]
    exact C.globally_maximum.2.2
  obtain ⟨bGamma, hbGamma⟩ := C.block_color_missing_on_base i
  have hyGammaX : C.y bGamma ∈ X := by
    rw [← C.base_vertex_position bGamma]
    simp [X, TreeSequenceVertexSet]
  have hgammaMissing : C.gamma i ∈ TreeMissingColors phi T' := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    refine ⟨C.y bGamma, ?_, hbGamma⟩
    rw [hvertexSet]
    exact hyGammaX
  have hgammaUnused : C.gamma i ∉ TreeUsedColors phi T' := by
    exact @helper_hgammaUnused_842 V E inferInstance inferInstance inferInstance G k e0 phi T C i
        alpha hAlphaGamma hlength hlenThree hmTwo hmLast a0 ha0Color a1 ha1Color nv_injective
        eix_val later_indices early_block_indices ne_retained ne_penultimate ne_last ne_injective
        hfirst hattaches
  have hgammaFree : C.gamma i ∈ TreeFreeColors phi T' := by
    exact Finset.mem_sdiff.mpr ⟨hgammaMissing, hgammaUnused⟩
  have hexitPred (v : V) :
      ScheideExitVertex T' phi v ↔ ScheideExitVertex T phi v := by
    simp only [ScheideExitVertex, ScheideDefectiveChainPath, hvertexSet]
    rfl
  have hexits : ScheideExitVertices T' phi = ScheideExitVertices T phi := by
    ext v
    simp only [ScheideExitVertices, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hexitPred v
  obtain ⟨vExit, hvExit, hvGamma⟩ := C.every_block_color_at_exit i
  have hvExit' : vExit ∈ ScheideExitVertices T' phi := by
    rw [hexits]
    exact hvExit
  have hdisjoint := ScheideExitNoFree G k e0 phi T' hglobal' vExit hvExit'
  exact (Finset.disjoint_left.mp hdisjoint) hvGamma hgammaFree

private theorem helper_continuation_1719.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (i : Fin C.s) (alpha : Fin k),
    alpha ≠ C.gamma i →
    ∀ (z : V),
    alpha ∈ MissingColors G phi z →
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    let X : Finset V := TreeSequenceVertexSet T;
    z ∈ X →
    (↑i : ℕ) < C.s →
    (2 : ℕ) ≤ C.p →
    ∀ (hlength : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s) (hlenThree : (3 : ℕ) ≤ T.length),
    let m : ℕ := C.p + (2 : ℕ) * (↑i : ℕ);
    (2 : ℕ) ≤ m →
    ∀ (hmLast : m + (1 : ℕ) ≤ T.length),
    T.vertex
          (⟨m, Decidable.byContradiction fun (a : ¬m < T.length + (1 : ℕ)) ↦ by omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u0 →
    T.vertex
          (⟨m + (1 : ℕ),
              Decidable.byContradiction fun (a : ¬m + (1 : ℕ) < T.length + (1 : ℕ)) ↦ by
                omega⟩ :
            Fin (T.length + (1 : ℕ))) =
        u1 →
    u0 ∈ X →
    u1 ∈ X →
    u0 ≠ u1 →
    z ≠ u0 →
    z ≠ u1 →
    ∀ (a0 : E),
    Incident G u0 a0 →
    phi a0 = some alpha →
    ∀ (a1 : E),
    Incident G u1 a1 →
    phi a1 = some alpha →
    ∀ (w0 : V),
    G.ends a0 = s(u0, w0) →
    ∀ (w1 : V),
    G.ends a1 = s(u1, w1) →
    w0 ≠ u0 →
    w1 ≠ u1 →
    w0 ∈ X →
    w1 ∈ X →
    ¬w0 = u1 →
    w1 ≠ u0 →
    let rix : Fin (T.length - (1 : ℕ)) → Fin (T.length + (1 : ℕ)) :=
      fun (q : Fin (T.length - (1 : ℕ))) ↦
      if hqm : (↑q : ℕ) < m then
        (⟨(↑q : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦ by omega⟩ :
          Fin (T.length + (1 : ℕ)))
      else
        (⟨(↑q : ℕ) + (2 : ℕ),
            Decidable.byContradiction fun (a : ¬(↑q : ℕ) + (2 : ℕ) < T.length + (1 : ℕ)) ↦
              by omega⟩ :
          Fin (T.length + (1 : ℕ)));
    (∀ (q : Fin (T.length - (1 : ℕ))),
        (↑(rix q) : ℕ) = if (↑q : ℕ) < m then (↑q : ℕ) else (↑q : ℕ) + (2 : ℕ)) →
    Function.Injective rix →
    False := by
  classical
  intro V E _ _ _ G k e0 phi T C i alpha hAlphaGamma z hzMissing u0 u1 X hzX hiLt hpTwo hlength
      hlenThree m hmTwo hmLast hu0pos hu1pos hu0X hu1X hu01 hzu0 hzu1 a0 ha0Inc ha0Color a1
      ha1Inc ha1Color w0 ha0Ends w1 ha1Ends hw0ne hw1ne hw0X hw1X hw0u1 hw1u0 rix rix_val
      rix_injective
  have rix_avoids (q : Fin (T.length - 1)) :
      (rix q).val ≠ m ∧ (rix q).val ≠ m + 1 := by
    have hqLt := q.isLt
    rw [rix_val]
    split <;> omega
  let nv : Fin (T.length + 1) → V := fun q =>
    if hq : q.val < T.length - 1 then
      T.vertex (rix ⟨q.val, hq⟩)
    else if q.val = T.length - 1 then u0 else u1
  have nv_retained (q : Fin (T.length - 1)) :
      nv ⟨q.val, by omega⟩ = T.vertex (rix q) := by
    simp [nv]
  have nv_penultimate : nv ⟨T.length - 1, by omega⟩ = u0 := by
    simp [nv]
  have nv_last : nv ⟨T.length, by omega⟩ = u1 := by
    simp [nv, show ¬ T.length < T.length - 1 by omega,
      show T.length ≠ T.length - 1 by omega]
  have retained_ne_u0 (q : Fin (T.length - 1)) :
      T.vertex (rix q) ≠ u0 := by
    intro h
    have hv : T.vertex (rix q) = T.vertex ⟨m, by omega⟩ :=
      h.trans hu0pos.symm
    exact (rix_avoids q).1 (congrArg Fin.val (T.vertex_injective hv))
  have retained_ne_u1 (q : Fin (T.length - 1)) :
      T.vertex (rix q) ≠ u1 := by
    intro h
    have hv : T.vertex (rix q) = T.vertex ⟨m + 1, by omega⟩ :=
      h.trans hu1pos.symm
    exact (rix_avoids q).2 (congrArg Fin.val (T.vertex_injective hv))
  have nv_injective : Function.Injective nv := by
    exact @helper_nv_injective_206 V E inferInstance inferInstance inferInstance G k e0 phi T C i
        hlength hlenThree hmLast hu01 rix_injective nv_penultimate nv_last retained_ne_u0
        retained_ne_u1
  have retained_vertex_index {w : V} (hwX' : w ∈ X)
      (hwu0 : w ≠ u0) (hwu1 : w ≠ u1) :
      ∃ q : Fin (T.length - 1),
        nv ⟨q.val, by omega⟩ = w := by
    exact @helper_retained_vertex_index_257 V E inferInstance inferInstance inferInstance G k e0
        phi T C i hlength hlenThree hmTwo hmLast hu0pos hu1pos rix_val nv_retained w hwX' hwu0 hwu1
  let eix : Fin (T.length - 2) → Fin T.length := fun q =>
    if hqm : q.val < m - 1 then ⟨q.val, by omega⟩
    else ⟨q.val + 2, by omega⟩
  have eix_val (q : Fin (T.length - 2)) :
      (eix q).val = if q.val < m - 1 then q.val else q.val + 2 := by
    by_cases hqm : q.val < m - 1
    · simp [eix, hqm]
    · simp [eix, hqm]
  have eix_injective : Function.Injective eix := by
    exact @helper_eix_injective_1675 V E inferInstance inferInstance inferInstance G k e0 phi T C
        i hlength hlenThree hmTwo eix_val
  have later_indices (q : Fin (T.length - 2)) (hq : m - 1 ≤ q.val) :
      ∃ (r : Fin C.s) (j : Fin 2), i.val < r.val ∧
        (eix q).val = C.p - 1 + 2 * r.val + j.val ∧
        (rix ⟨q.val + 1, by omega⟩).val = C.p + 2 * r.val + j.val := by
    exact @helper_later_indices_313 V E inferInstance inferInstance inferInstance G k e0 phi T C
        i hpTwo hlength hlenThree hmTwo hmLast rix_val eix_val q hq
  have early_block_indices (q : Fin (T.length - 2))
      (hbase : C.p - 1 ≤ q.val) (hq : q.val < m - 1) :
      ∃ (r : Fin C.s) (j : Fin 2), r.val < i.val ∧
        (eix q).val = C.p - 1 + 2 * r.val + j.val := by
    exact @helper_early_block_indices_1415 V E inferInstance inferInstance inferInstance G k e0
        phi T C i hpTwo hlength hlenThree hmTwo hmLast eix_val q hbase hq
  have block_vertex_ne_before (j0 : Fin 2) (q : Fin (T.length + 1))
      (hq : q.val < m) : C.blockVertex i j0 ≠ T.vertex q := by
    intro h
    have hp := C.block_vertex_position i j0
    have hv : T.vertex ⟨C.p + 2 * i.val + j0.val, by omega⟩ =
        T.vertex q := hp.trans h
    have hiq := congrArg Fin.val (T.vertex_injective hv)
    simp at hiq
    dsimp [m] at hq
    omega
  have retained_not_incident (q : Fin (T.length - 2)) (j0 : Fin 2) :
      ¬ Incident G (C.blockVertex i j0) (T.edge (eix q)) := by
    exact @helper_retained_not_incident_383 V E inferInstance inferInstance inferInstance G k e0
        phi T C i hiLt hlength hlenThree hmTwo hmLast eix_val later_indices
        block_vertex_ne_before q j0
  have ha01 : a0 ≠ a1 := by
    intro h
    have he : s(u0, w0) = s(u1, w1) := by
      rw [← ha0Ends, h, ha1Ends]
    rcases Sym2.eq_iff.mp he with hsame | hswap
    · exact hu01 hsame.1
    · exact hw1u0 hswap.1.symm
  let ne : Fin T.length → E := fun q =>
    if hq : q.val < T.length - 2 then
      T.edge (eix ⟨q.val, hq⟩)
    else if q.val = T.length - 2 then a0 else a1
  have ne_retained (q : Fin (T.length - 2)) :
      ne ⟨q.val, by omega⟩ = T.edge (eix q) := by
    simp [ne]
  have ne_penultimate : ne ⟨T.length - 2, by omega⟩ = a0 := by
    simp [ne]
  have ne_last : ne ⟨T.length - 1, by omega⟩ = a1 := by
    simp [ne, show ¬ T.length - 1 < T.length - 2 by omega,
      show T.length - 1 ≠ T.length - 2 by omega]
  have ne_injective : Function.Injective ne := by
    exact @helper_ne_injective_450 V E inferInstance inferInstance inferInstance G k e0 phi T C i
        hlength hlenThree hmTwo a0 ha0Inc a1 ha1Inc eix_injective retained_not_incident ha01
        ne_penultimate ne_last
  have hfirst : ne ⟨0, T.positive⟩ = e0 := by
    exact @helper_hfirst_1733 V E inferInstance inferInstance inferInstance G k e0 phi T C i
        hlength hlenThree hmTwo a0 a1 eix_val ne_retained
  have hattaches : ∀ q : Fin T.length, ∃ a : Fin (q.val + 1),
      G.ends (ne q) =
        s(nv q.succ,
          nv (Fin.castLT a
            (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt)))) := by
    exact @helper_hattaches_522 V E inferInstance inferInstance inferInstance G k e0 phi T C i
        hpTwo hlength hlenThree hmTwo hmLast a0 a1 w0 ha0Ends w1 ha1Ends hw0ne hw1ne hw0X hw1X
        hw0u1 hw1u0 rix_val nv_retained nv_penultimate nv_last retained_vertex_index eix_val
        later_indices ne_retained ne_penultimate ne_last
  exact @helper_continuation_1778 V E inferInstance inferInstance inferInstance G k e0 phi T C i
      alpha hAlphaGamma z hzMissing hzX hpTwo hlength hlenThree hmTwo hmLast hu0X hu1X hzu0 hzu1
      a0 ha0Color a1 ha1Color rix_val nv_retained nv_penultimate nv_last nv_injective
      retained_vertex_index eix_val later_indices early_block_indices ne_retained ne_penultimate
      ne_last ne_injective hfirst hattaches
theorem ScheideStructuralInternalPair {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T) :
    ∀ (i : Fin C.s) (alpha : Fin k),
    alpha ≠ C.gamma i →
    (∃ z ∈ TreeSequenceVertexSet T \ {C.blockVertex i 0, C.blockVertex i 1},
        alpha ∈ MissingColors G phi z) →
    ∃ f : E,
    phi f = some alpha ∧ G.ends f = s(C.blockVertex i 0, C.blockVertex i 1) := by
  classical
  intro i alpha hAlphaGamma hmissing
  rcases hmissing with ⟨z, hzZ, hzMissing⟩
  let u0 := C.blockVertex i 0
  let u1 := C.blockVertex i 1
  let X := TreeSequenceVertexSet T
  have hzX : z ∈ X := (Finset.mem_sdiff.mp hzZ).1
  have horder := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have helem : ColoredVertexSetElementary G phi X := horder.2.2.2.1
  have hclosed : ColoredVertexSetClosed G phi X := horder.2.2.2.2
  have hproper : IsProperEdgeColoring G phi := C.globally_maximum.1.2.2.2.1
  have hone : IsOneEdgeUncolored phi e0 := C.globally_maximum.1.2.2.2.2
  have hiLt : i.val < C.s := i.isLt
  have hiS : 1 ≤ C.s :=
    Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt hiLt)
  have hpTwo : 2 ≤ C.p := C.p_ge_two
  have hlength : T.length + 1 = C.p + 2 * C.s := C.length_eq
  have hlenThree : 3 ≤ T.length := by omega
  let m := C.p + 2 * i.val
  have hmTwo : 2 ≤ m := by dsimp [m]; omega
  have hmLast : m + 1 ≤ T.length := by dsimp [m]; omega
  have hu0pos : T.vertex ⟨m, by omega⟩ = u0 := by
    simpa [m, u0] using C.block_vertex_position i (0 : Fin 2)
  have hu1pos : T.vertex ⟨m + 1, by omega⟩ = u1 := by
    simpa [m, u1] using C.block_vertex_position i (1 : Fin 2)
  have hu0X : u0 ∈ X := by
    rw [← hu0pos]
    simp [X, TreeSequenceVertexSet]
  have hu1X : u1 ∈ X := by
    rw [← hu1pos]
    simp [X, TreeSequenceVertexSet]
  have hu01 : u0 ≠ u1 := by
    intro h
    let q0 : Fin (T.length + 1) := ⟨m, by omega⟩
    let q1 : Fin (T.length + 1) := ⟨m + 1, by omega⟩
    have hv : T.vertex q0 = T.vertex q1 := by
      simpa [q0, q1] using hu0pos.trans (h.trans hu1pos.symm)
    have hi := T.vertex_injective hv
    have hiv := congrArg Fin.val hi
    simp [q0, q1] at hiv
  have hzu0 : z ≠ u0 := by
    have hn := (Finset.mem_sdiff.mp hzZ).2
    simpa [u0, u1] using fun h => hn (by simp [h])
  have hzu1 : z ≠ u1 := by
    have hn := (Finset.mem_sdiff.mp hzZ).2
    simpa [u0, u1] using fun h => hn (by simp [h])
  have alpha_present (u : V) (huX : u ∈ X) (hzu : z ≠ u) :
      alpha ∈ PresentColors G phi u := by
    have hnot : alpha ∉ MissingColors G phi u := by
      intro huMissing
      exact (Finset.disjoint_left.mp (helem hzX huX hzu)) hzMissing huMissing
    simpa [MissingColors] using hnot
  obtain ⟨a0, ha0Inc, ha0Color⟩ := by
    simpa [PresentColors] using alpha_present u0 hu0X hzu0
  obtain ⟨a1, ha1Inc, ha1Color⟩ := by
    simpa [PresentColors] using alpha_present u1 hu1X hzu1
  obtain ⟨w0, ha0Ends⟩ := Sym2.mem_iff_exists.mp ha0Inc
  obtain ⟨w1, ha1Ends⟩ := Sym2.mem_iff_exists.mp ha1Inc
  have hw0ne : w0 ≠ u0 := by
    intro h
    exact G.loopless a0 u0 (by simpa [h] using ha0Ends)
  have hw1ne : w1 ≠ u1 := by
    intro h
    exact G.loopless a1 u1 (by simpa [h] using ha1Ends)
  have other_end_in_X (a : E) (u w : V) (huX : u ∈ X)
      (haEnds : G.ends a = s(u, w)) (haColor : phi a = some alpha) : w ∈ X := by
    by_contra hwX
    have haBoundary : a ∈ BoundaryEdges G X := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u, huX, w, hwX, haEnds⟩
    exact hclosed haBoundary hzX haColor hzMissing
  have hw0X : w0 ∈ X := other_end_in_X a0 u0 w0 hu0X ha0Ends ha0Color
  have hw1X : w1 ∈ X := other_end_in_X a1 u1 w1 hu1X ha1Ends ha1Color
  by_cases hw0u1 : w0 = u1
  · exact ⟨a0, ha0Color, by simpa [u0, u1, hw0u1] using ha0Ends⟩
  exfalso
  have hw0Z : w0 ∈ X \ {u0, u1} := by
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hw0X, not_or_intro hw0ne hw0u1⟩
  have hw1u0 : w1 ≠ u0 := by
    exact @helper_hw1u0_1593 V E inferInstance inferInstance inferInstance G k e0 phi T C i alpha
        hproper hu01 a0 ha0Inc ha0Color a1 ha1Color w0 ha0Ends w1 ha1Ends hw0u1
  have hw1Z : w1 ∈ X \ {u0, u1} := by
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hw1X, not_or_intro hw1u0 hw1ne⟩
  let rix : Fin (T.length - 1) → Fin (T.length + 1) := fun q =>
    if hqm : q.val < m then ⟨q.val, by omega⟩
    else ⟨q.val + 2, by omega⟩
  have rix_val (q : Fin (T.length - 1)) :
      (rix q).val = if q.val < m then q.val else q.val + 2 := by
    by_cases hqm : q.val < m
    · simp [rix, hqm]
    · simp [rix, hqm]
  have rix_injective : Function.Injective rix := by
    intro q r hqr
    have hqLt := q.isLt
    have hrLt := r.isLt
    by_cases hqm : q.val < m <;> by_cases hrm : r.val < m
    all_goals
      have hv := congrArg Fin.val hqr
      rw [rix_val, rix_val] at hv
      simp [hqm, hrm] at hv
      apply Fin.ext
      omega
  exact @helper_continuation_1719 V E inferInstance inferInstance inferInstance G k e0 phi T C i
      alpha hAlphaGamma z hzMissing hzX hiLt hpTwo hlength hlenThree hmTwo hmLast hu0pos hu1pos
      hu0X hu1X hu01 hzu0 hzu1 a0 ha0Inc ha0Color a1 ha1Inc ha1Color w0 ha0Ends w1 ha1Ends hw0ne
      hw1ne hw0X hw1X hw0u1 hw1u0 rix_val rix_injective
end GoldbergSeymour

end
