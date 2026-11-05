/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideMaximalElementaryClosed

/-!
# Scheide Maximal Odd Order

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideMaximalOddOrder {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (hmax : FixedPairMaximalTashkinovTree G e0 phi T) :
    Odd (TreeSequenceVertexSet T).card := by
  classical
  let X := TreeSequenceVertexSet T
  have hdata := ScheideMaximalElementaryClosed G k e0 phi T htriple hmax
  have hproper : IsProperEdgeColoring G phi := htriple.2.2.2.1
  have hbound : MaximumDegree G + 1 ≤ k := htriple.2.2.1
  have hdeg : ∀ v : V, Degree G v ≤ MaximumDegree G := by
    intro v
    unfold MaximumDegree
    exact Finset.le_max' _ _ (Finset.mem_insert.mpr (Or.inr
      (Finset.mem_image.mpr ⟨v, by simp⟩)))
  have present_le_degree : ∀ v : V, (PresentColors G phi v).card ≤ Degree G v := by
    intro v
    have chooseData (c : {c : Fin k // c ∈ PresentColors G phi v}) :
        ∃ e, Incident G v e ∧ phi e = some c.1 := by
      simpa [PresentColors] using c.property
    let choices : {c : Fin k // c ∈ PresentColors G phi v} →
        {e : E // Incident G v e} := fun c =>
      ⟨Classical.choose (chooseData c), (Classical.choose_spec (chooseData c)).1⟩
    have choice_spec : ∀ c : {c : Fin k // c ∈ PresentColors G phi v},
        phi (choices c).1 = some c.1 := by
      intro c
      exact (Classical.choose_spec (chooseData c)).2
    have inj : Function.Injective choices := by
      intro a b hab
      have ha := choice_spec a
      have hb := choice_spec b
      apply Subtype.ext
      apply Option.some.inj
      calc
        some (a : Fin k) = phi (choices a).1 := ha.symm
        _ = phi (choices b).1 := by rw [hab]
        _ = some (b : Fin k) := hb
    let : Fintype {c : Fin k // c ∈ PresentColors G phi v} := Fintype.ofFinite _
    have hc := Fintype.card_le_of_injective choices inj
    change (PresentColors G phi v).card ≤
      (Finset.univ.filter (fun e => Incident G v e)).card
    simpa [Fintype.card_subtype] using hc
  have missing_exists : ∀ v : V, (MissingColors G phi v).Nonempty := by
    intro v
    by_contra hn
    have hempty : MissingColors G phi v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hall : PresentColors G phi v = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro c
      by_contra hc
      have hm : c ∈ MissingColors G phi v := by simp [MissingColors, hc]
      exact (by simp [hempty] at hm)
    have hc : k ≤ Degree G v := by
      have := present_le_degree v
      simpa [hall] using this
    have : MaximumDegree G + 1 ≤ MaximumDegree G :=
      le_trans hbound (le_trans hc (hdeg v))
    omega
  have hx : X.Nonempty := by
    refine ⟨T.vertex ⟨0, Nat.zero_lt_succ _⟩, ?_⟩
    simp [X, TreeSequenceVertexSet]
  obtain ⟨x, hxX⟩ := hx
  obtain ⟨eta, heta⟩ := missing_exists x
  let Y := X.erase x
  let edges := (Finset.univ : Finset E).filter (fun e => phi e = some eta)
  have y_present : ∀ v, v ∈ Y → eta ∈ PresentColors G phi v := by
    intro v hv
    have hvX : v ∈ X := (Finset.mem_erase.mp hv).2
    have hvne : v ≠ x := (Finset.mem_erase.mp hv).1
    have hdis := hdata.1 hxX hvX hvne.symm
    have : eta ∉ MissingColors G phi v := by
      intro hm
      exact (Finset.disjoint_left.mp hdis) heta hm
    simpa [MissingColors] using this
  have edge_inc : ∀ v, v ∈ Y → ∃! e, e ∈ edges ∧ Incident G v e := by
    intro v hv
    obtain ⟨e, he, hve⟩ := by simpa [PresentColors] using y_present v hv
    refine ⟨e, ?_, ?_⟩
    · exact ⟨by simpa [edges] using hve, he⟩
    · intro f hf
      by_contra hef
      exact (hproper (fun h => hef h.symm) ⟨v, he, hf.2⟩ hve)
        (Finset.mem_filter.mp hf.1).2
  have no_x : ∀ e, e ∈ edges → ¬ Incident G x e := by
    intro e he hxe
    have hp : eta ∈ PresentColors G phi x := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, hxe, (Finset.mem_filter.mp he).2⟩
    exact (Finset.mem_sdiff.mp heta).2 hp
  have internal_other : ∀ e, e ∈ edges → ∀ v, v ∈ X → Incident G v e →
      ∀ z, Incident G z e → z ∈ X := by
    intro e he v hvX hve z hze
    by_contra hz
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hze
    have hzw : G.ends e = s(z, w) := hw
    have hvpair : v = z ∨ v = w := by
      have : v ∈ s(z, w) := by rw [← hzw]; exact hve
      simpa using this
    have hzwX : w ∈ X := by
      rcases hvpair with hvz | hvw
      · exact False.elim (hz (hvz ▸ hvX))
      · exact hvw ▸ hvX
    have hb : e ∈ BoundaryEdges G X := by
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      exact ⟨w, hzwX, z, hz, hzw.trans Sym2.eq_swap⟩
    have hc := hdata.2 hb hxX (Finset.mem_filter.mp he).2
    exact hc heta
  let good := edges.filter (fun e => ∀ v, Incident G v e → v ∈ X)
  have good_spec : ∀ e, e ∈ good ↔ e ∈ edges ∧ ∀ v, Incident G v e → v ∈ X := by
    intro e
    simp [good]
  have endpoint_card : ∀ e : E, (G.ends e).toFinset.card = 2 := by
    intro e
    apply Sym2.card_toFinset_of_not_isDiag
    intro hd
    exact G.loopless e ((G.ends e).diagElem hd) (Sym2.diag_diagElem hd).symm
  have good_disjoint : ∀ ⦃e⦄, e ∈ good → ∀ ⦃f⦄, f ∈ good →
      e ≠ f → Disjoint (G.ends e).toFinset (G.ends f).toFinset := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    have hce := (good_spec e).mp he |>.1
    have hcf := (good_spec f).mp hf |>.1
    exact (hproper hef ⟨v, Sym2.mem_toFinset.mp hev, Sym2.mem_toFinset.mp hvf⟩
      (Finset.mem_filter.mp hce).2) (Finset.mem_filter.mp hcf).2
  have union_card : (good.biUnion fun e => (G.ends e).toFinset).card = 2 * good.card := by
    have aux : ∀ s : Finset E, s ⊆ good →
        (s.biUnion fun e => (G.ends e).toFinset).card = 2 * s.card := by
      intro s hs
      induction s using Finset.induction_on with
      | empty => simp
      | @insert e s hes ih =>
        rw [Finset.biUnion_insert]
        have hd : Disjoint (G.ends e).toFinset
            (s.biUnion fun f => (G.ends f).toFinset) := by
          rw [Finset.disjoint_left]
          intro v hev hvs
          obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvs
          have hh := good_disjoint (hs (Finset.mem_insert_self e s))
            (hs (Finset.mem_insert_of_mem hf)) (by
              intro heq
              exact hes (by simpa [heq] using hf))
          exact (Finset.disjoint_left.mp hh) hev hvf
        rw [Finset.card_union_of_disjoint hd, endpoint_card]
        rw [ih (fun x hx => hs (Finset.mem_insert_of_mem hx))]
        rw [Finset.card_insert_of_notMem hes]
        omega
    exact aux good (by intro e he; exact he)
  have union_eq : good.biUnion (fun e => (G.ends e).toFinset) = Y := by
    ext v
    constructor
    · intro hv
      obtain ⟨e, he, hev⟩ := Finset.mem_biUnion.mp hv
      have hvX := (good_spec e |>.mp he).2 v (Sym2.mem_toFinset.mp hev)
      have hvx : v ≠ x := by
        intro hvx
        exact no_x e (good_spec e |>.mp he).1 (hvx ▸ Sym2.mem_toFinset.mp hev)
      exact Finset.mem_erase.mpr ⟨hvx, hvX⟩
    · intro hv
      have hvY : v ∈ Y := hv
      obtain ⟨e, he, hve⟩ := edge_inc v hvY
      have hg : e ∈ good := good_spec e |>.mpr ⟨he.1,
        internal_other e he.1 v (Finset.mem_erase.mp hvY).2 he.2⟩
      exact Finset.mem_biUnion.mpr ⟨e, hg, Sym2.mem_toFinset.mpr he.2⟩
  have heven : Even Y.card := by
    refine ⟨good.card, ?_⟩
    rw [← union_eq, union_card]
    omega
  have hodd : Odd (X.card) := by
    have hcard : X.card = Y.card + 1 := by
      have hh := Finset.card_erase_of_mem hxX
      simp [Y] at hh ⊢
      have hpos : 0 < X.card := Finset.card_pos.mpr ⟨x, hxX⟩
      omega
    rw [hcard]
    rcases heven with ⟨q, hq⟩
    exact ⟨q, by omega⟩
  exact hodd

end GoldbergSeymour

end
