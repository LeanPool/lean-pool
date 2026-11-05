/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.FixedPairMaximalTashkinovTree
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.TashTree

/-!
# Scheide Maximal Elementary Closed

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideMaximalElementaryClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (hmax : FixedPairMaximalTashkinovTree G e0 phi T) :
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧
      ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) := by
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
   TashTree (V := V) (E := E) G k e0 phi T htriple (hT := hmax.1)
  refine ⟨helem, ?_⟩
  unfold ColoredVertexSetClosed
  classical
  intro f c v hf hv hfc
  by_contra hbad
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  rcases hf with ⟨u, hu, w, hw, hends⟩
  let nv : Fin (T.length + 2) → V := Fin.lastCases w (fun i => T.vertex i)
  let ne : Fin (T.length + 1) → E := Fin.lastCases f (fun i => T.edge i)
  let hs : TreeSequence G e0 := by
    refine ⟨T.length + 1, by omega, nv, ne, ?_, ?_, ?_, ?_⟩
    · intro a
      refine Fin.lastCases ?_ (fun i => ?_) a
      · intro b
        refine Fin.lastCases ?_ (fun j => ?_) b
        · intro hab
          rfl
        · intro hab
          apply False.elim
          apply hw
          rw [TreeSequenceVertexSet]
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by simpa [nv] using hab.symm⟩
      · intro b
        refine Fin.lastCases ?_ (fun j => ?_) b
        · intro hab
          apply False.elim
          apply hw
          rw [TreeSequenceVertexSet]
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simpa [nv] using hab⟩
        · intro hab
          have hvertex : T.vertex i = T.vertex j := by simpa [nv] using hab
          exact congrArg Fin.castSucc (T.vertex_injective hvertex)
    · intro a
      refine Fin.lastCases ?_ (fun i => ?_) a
      · intro b
        refine Fin.lastCases ?_ (fun j => ?_) b
        · intro hab
          rfl
        · intro hab
          apply False.elim
          apply hw
          have he : f = T.edge j := by simpa [ne] using hab
          have hm : w ∈ G.ends (T.edge j) := by rw [← he, hends]; simp
          rw [T.attaches j |>.choose_spec] at hm
          simp only [Sym2.mem_iff] at hm
          rcases hm with hm | hm
          · exact Finset.mem_image.mpr ⟨j.succ, Finset.mem_univ _, hm.symm⟩
          · exact Finset.mem_image.mpr ⟨Fin.castLT (T.attaches j).choose (by omega),
              Finset.mem_univ _, hm.symm⟩
      · intro b
        refine Fin.lastCases ?_ (fun j => ?_) b
        · intro hab
          apply False.elim
          apply hw
          have he : T.edge i = f := by simpa [ne] using hab
          have hm : w ∈ G.ends (T.edge i) := by rw [he, hends]; simp
          rw [T.attaches i |>.choose_spec] at hm
          simp only [Sym2.mem_iff] at hm
          rcases hm with hm | hm
          · exact Finset.mem_image.mpr ⟨i.succ, Finset.mem_univ _, hm.symm⟩
          · exact Finset.mem_image.mpr ⟨Fin.castLT (T.attaches i).choose (by omega),
              Finset.mem_univ _, hm.symm⟩
        · intro hab
          have hedge : T.edge i = T.edge j := by simpa [ne] using hab
          exact congrArg Fin.castSucc (T.edge_injective hedge)
    · have hz : (0 : Fin (T.length + 1)) = (⟨0, T.positive⟩ : Fin T.length).castSucc := by rfl
      have he : ne ⟨0, by omega⟩ = T.edge ⟨0, T.positive⟩ := by
        calc
          ne ⟨0, by omega⟩ = ne (⟨0, T.positive⟩ : Fin T.length).castSucc := congrArg ne hz
          _ = T.edge ⟨0, T.positive⟩ := by
            simp only [ne, Fin.lastCases_castSucc]
      rw [he]
      exact T.first_edge
    · intro j
      refine Fin.lastCases ?_ (fun q => ?_) j
      · rw [TreeSequenceVertexSet] at hu
        rcases Finset.mem_image.mp hu with ⟨i, hi, hui⟩
        refine ⟨i, ?_⟩
        have hidx : Fin.castLT i (by omega) = i.castSucc := by ext; rfl
        rw [hidx]
        have he : ne (Fin.last T.length) = f := by simp [ne]
        have hvlast : nv (Fin.last T.length).succ = w := by simp [nv]
        rw [he, hvlast, hends]
        simp only [nv, Fin.lastCases_castSucc]
        rw [hui]
        exact Sym2.eq_swap
      · rcases T.attaches q with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have hidx : Fin.castLT i (by omega) = i := by ext; rfl
        have hnext : q.castSucc.succ = q.succ.castSucc := by ext; rfl
        have hiNv : nv (Fin.castLT i (by omega)) =
            T.vertex (Fin.castLT i (by omega)) := by
          let ilarge : Fin (T.length + 1) := Fin.castLT i (by omega)
          have heq : (Fin.castLT i (by omega) : Fin (T.length + 2)) = ilarge.castSucc := by
            ext
            rfl
          rw [heq]
          simp [nv, ilarge]
        rw [hnext, hiNv]
        simpa only [nv, ne, Fin.lastCases_castSucc] using hi
  have ht : TashkinovTree G e0 phi hs := by
    intro j
    dsimp [hs] at j ⊢
    change Fin (T.length + 1) at j
    refine Fin.lastCases ?_ (fun q => ?_) j
    · intro hj
      rw [TreeSequenceVertexSet] at hv
      rcases Finset.mem_image.mp hv with ⟨i, hi, hiv⟩
      have hne : hs.edge (Fin.last T.length) = f := by simp [hs, ne]
      refine ⟨i, c, ?_, ?_⟩
      · simpa [hs, ne, Fin.lastCases_last] using hfc
      · have hidx : Fin.castLT i (by omega) = i.castSucc := by ext; rfl
        rw [hidx]
        simp only [nv, Fin.lastCases_castSucc]
        rw [hiv]
        exact hbad
    · intro hj
      have hjq : 1 ≤ q.val := by exact hj
      rcases hmax.1 q hjq with ⟨r, d, hd, hm⟩
      refine ⟨r, d, ?_, ?_⟩
      · simpa [hs, ne] using hd
      · let rlarge : Fin (T.length + 1) := Fin.castLT r (by omega)
        have hidx : Fin.castLT r (by omega) = rlarge.castSucc := by ext; rfl
        rw [hidx]
        simp only [nv, Fin.lastCases_castSucc]
        exact hm
  have hsub : TreeSequenceVertexSet T ⊆ TreeSequenceVertexSet hs := by
    intro x hx
    rw [TreeSequenceVertexSet] at hx ⊢
    rcases Finset.mem_image.mp hx with ⟨i, hi, hxi⟩
    refine Finset.mem_image.mpr ⟨Fin.castLT i (by dsimp [hs]; omega), Finset.mem_univ _, ?_⟩
    have hidx : Fin.castLT i (by omega) = i.castSucc := by ext; rfl
    simpa [hs, nv, hidx, Fin.lastCases_castSucc] using hxi
  have hback := hmax.2 hs ht hsub
  apply hw
  apply hback
  rw [TreeSequenceVertexSet]
  exact Finset.mem_image.mpr ⟨Fin.last (T.length + 1), Finset.mem_univ _, by simp [hs, nv]⟩

end GoldbergSeymour

end
