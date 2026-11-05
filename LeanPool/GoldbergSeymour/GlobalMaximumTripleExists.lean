/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ChromaticIndexSpec

public import LeanPool.GoldbergSeymour.GlobalMaximumTriple

/-!
# Global Maximum Triple Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem GlobalMaximumTripleExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k) :
    ∃ (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0),
      GlobalMaximumTriple G k e0 phi T := by
  classical
  have hedge : Nonempty E := by
    by_contra hne
    have hempty : IsEmpty E := not_nonempty_iff.mp hne
    let coloring : PartialEdgeColoring E 0 := fun e => isEmptyElim e
    have hhas : HasKEdgeColoring G 0 := by
      refine ⟨coloring, ?_, ?_⟩
      · intro e f c hef hadj he hf
        exact isEmptyElim e
      · intro e
        exact isEmptyElim e
    have hzero : ChromaticIndex G = 0 :=
      Nat.eq_zero_of_le_zero ((ChromaticIndexSpec G).2 0 hhas)
    have hk : 1 ≤ k := by omega
    have : 2 ≤ ChromaticIndex G := by omega
    omega
  have hd : ChromaticIndex (DeleteEdge G (Classical.choice hedge)) ≤ k := by
    have hc := hcritical (Classical.choice hedge)
    rw [hindex] at hc
    omega
  obtain ⟨psi, hpsi, hpsifull⟩ := (ChromaticIndexSpec (DeleteEdge G (Classical.choice hedge))).1
  let phi : PartialEdgeColoring E k := fun e =>
    if he : e = Classical.choice hedge then none
    else (psi ⟨e, by simp [he]⟩).map (fun z => Fin.castLE hd z)
  have hproper : IsProperEdgeColoring G phi := by
    intro e f c hef hadj he hf
    have he0 : e ≠ Classical.choice hedge := by
      intro he0
      simp [phi, he0] at he
    have hf0 : f ≠ Classical.choice hedge := by
      intro hf0
      simp [phi, hf0] at hf
    obtain ⟨ce, hce⟩ := hpsifull ⟨e, by simp [he0]⟩
    obtain ⟨cf, hcf⟩ := hpsifull ⟨f, by simp [hf0]⟩
    have hceq : Fin.castLE hd ce = c := by
      simpa [phi, he0, hce] using he
    have hcfeq : Fin.castLE hd cf = c := by
      simpa [phi, hf0, hcf] using hf
    have hcfce : cf = ce := by
      apply Fin.ext
      have heval := congrArg Fin.val hceq
      have hfval := congrArg Fin.val hcfeq
      simp at heval hfval
      omega
    have hadj' : AdjacentEdges (DeleteEdge G (Classical.choice hedge))
        ⟨e, by simp [he0]⟩ ⟨f, by simp [hf0]⟩ := by
      exact hadj
    rw [hcfce] at hcf
    exact (hpsi (e := (⟨e, by simp [he0]⟩)) (f := (⟨f, by simp [hf0]⟩))
      (c := ce) (fun h => hef (congrArg Subtype.val h)) hadj' hce) hcf
  have hone : IsOneEdgeUncolored phi (Classical.choice hedge) := by
    refine ⟨?_, ?_⟩
    · simp [phi]
    · intro e he
      simp only [he, ↓reduceDIte, Option.map_eq_some_iff, ↓existsAndEq, and_true, phi]
      exact hpsifull ⟨e, by simp [he]⟩
  have htriple : KTriple G k (Classical.choice hedge) phi :=
    ⟨hcritical, hindex, hdegree, hproper, hone⟩
  obtain ⟨x, y, hends⟩ :=
    (Sym2.exists (f := fun z => G.ends (Classical.choice hedge) = z)).mp
      ⟨G.ends (Classical.choice hedge), rfl⟩
  have hxy : x ≠ y := by
    intro h
    apply G.loopless (Classical.choice hedge) x
    rw [hends, h]
  let short : TreeSequence G (Classical.choice hedge) :=
    { length := 1
      positive := by omega
      vertex := fun i => if i.val = 0 then x else y
      edge := fun _ => Classical.choice hedge
      vertex_injective := by
        intro a b hab
        apply Fin.ext
        by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
        · simp [ha, hb] at hab
          omega
        · simp only [Nat.reduceAdd, ha, ↓reduceIte, hb] at hab
          exact (hxy hab).elim
        · simp [ha, hb] at hab
          exact (hxy hab.symm).elim
        · simp [ha, hb] at hab
          omega
      edge_injective := by
        intro a b hab
        exact Subsingleton.elim a b
      first_edge := rfl
      attaches := by
        intro j
        have hj : j = ⟨0, by omega⟩ := Fin.ext (by
          have hj' := j.isLt
          omega)
        subst j
        refine ⟨⟨0, by omega⟩, ?_⟩
        rw [hends]
        exact Sym2.eq_swap }
  have hshorttree : TashkinovTree G (Classical.choice hedge) phi short := by
    intro j hj
    have hj' := j.isLt
    change j.val < 1 at hj'
    omega
  have hshortcard : (TreeSequenceVertexSet short).card = 2 := by
    have himage : (Finset.image (fun i : Fin (1 + 1) =>
        if i.val = 0 then x else y) Finset.univ) = {x, y} := by
      ext v
      simp [eq_comm]
    simp only [TreeSequenceVertexSet, short]
    rw [himage]
    simp [hxy]
  have hparam : ChromaticIndex G - 1 = k := by omega
  have hshortmem : 2 ∈
      (Finset.range (Fintype.card V + 1)).filter (fun n =>
        ∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex G - 1))
          (R : TreeSequence G e),
          KTriple G (ChromaticIndex G - 1) e p ∧
            TashkinovTree G e p R ∧
              (TreeSequenceVertexSet R).card = n) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · have hv : (TreeSequenceVertexSet short).card ≤ Fintype.card V :=
        Finset.card_le_card (Finset.subset_univ _)
      omega
    · refine ⟨Classical.choice hedge, ?_, short, ?_, ?_, ?_⟩
      · exact hparam.symm ▸ phi
      · exact hparam.symm ▸ htriple
      · exact hparam.symm ▸ hshorttree
      · exact hshortcard
  have hlower : 2 ≤ TashkinovOrder G := by
    unfold TashkinovOrder
    dsimp
    exact Finset.le_max' _ _ (Finset.mem_insert_of_mem hshortmem)
  have hmaxmem : TashkinovOrder G ∈
      insert 0 ((Finset.range (Fintype.card V + 1)).filter (fun n =>
        ∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex G - 1))
          (R : TreeSequence G e),
          KTriple G (ChromaticIndex G - 1) e p ∧
            TashkinovTree G e p R ∧
              (TreeSequenceVertexSet R).card = n)) := by
    unfold TashkinovOrder
    dsimp
    exact Finset.max'_mem _ _
  have horder_mem : TashkinovOrder G ∈
      (Finset.range (Fintype.card V + 1)).filter (fun n =>
        ∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex G - 1))
          (R : TreeSequence G e),
          KTriple G (ChromaticIndex G - 1) e p ∧
            TashkinovTree G e p R ∧
              (TreeSequenceVertexSet R).card = n) := by
    have hnezero : TashkinovOrder G ≠ 0 := by omega
    simpa [Finset.mem_insert, hnezero] using hmaxmem
  simp only [Finset.mem_filter] at horder_mem
  rcases horder_mem with ⟨hbound, e, p, R, hkp, htp, hcard⟩
  refine ⟨e, hparam ▸ p, R, ?_⟩
  cases hparam
  exact ⟨hkp, htp, hcard⟩

end GoldbergSeymour

end
