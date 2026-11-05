/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ScheideMaximalContainsEveryTree
public import LeanPool.GoldbergSeymour.ScheideMaximalElementaryClosed
public import LeanPool.GoldbergSeymour.TashTree
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeColorUnusedThrough
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TashkinovTreeComponentSwapWitnessTransport

/-!
# Scheide Maximal Kempe Path

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hend_neighbor_227.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (S : TreeSequence G e0) (i _ : Fin (S.length + (1
        : ℕ))) (gamma delta : Fin k), gamma ∈ MissingColors G phi (S.vertex i) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G phi gamma delta (Sum.inl (S.vertex i));
        IsProperEdgeColoring G phi → gamma ≠ delta →
    ∀ (_ b : V ⊕ E) (p : H.Walk (Sum.inl (S.vertex i)) b), p.IsPath → {z : V ⊕ E | z ∈ p.support}
        = C → ¬p.Nil → (0 : ℕ) < p.length → b ∈ C →
    ∀ (z : V ⊕ E), H.Adj b z → z = p.getVert (p.length - (1 : ℕ)) := by
  classical
  intro V E _ _ G k e0 phi S i j gamma delta hgamma H C hproper hne b b p hp hps hpnil hp_pos hbC z
      hbz
  let _ := Fintype.ofFinite V
  have hzC : z ∈ C := by
    change H.connectedComponentMk z =
      H.connectedComponentMk (Sum.inl (S.vertex i))
    change H.connectedComponentMk b =
      H.connectedComponentMk (Sum.inl (S.vertex i)) at hbC
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hbz).symm.trans hbC
  have hzSupport : z ∈ p.support := by
    change z ∈ {w | w ∈ p.support}
    rw [hps]
    exact hzC
  obtain ⟨n, hn, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzSupport
  have hnlt : n < p.length := by
    have hnne : n ≠ p.length := by
      intro heq
      have hzb : z = b := by
        rw [← hn, heq, p.getVert_length]
      exact hbz.ne hzb.symm
    omega
  by_cases hpen : n + 1 = p.length
  · rw [← hn]
    congr 1
    omega
  by_cases hn0 : n = 0
  · have hnext : H.Adj (Sum.inl (S.vertex i)) (p.getVert 1) := by
      simpa [hn0, p.getVert_zero] using p.adj_getVert_succ hnlt
    have hbstart : H.Adj (Sum.inl (S.vertex i)) b := by
      rw [← hn, hn0, p.getVert_zero] at hbz
      exact hbz.symm
    have hneNext : p.getVert 1 ≠ b := by
      intro heq
      have hindices := hp.getVert_injOn
        (show 1 ≤ p.length by omega) (show p.length ≤ p.length by rfl)
        (heq.trans p.getVert_length.symm)
      omega
    let : Fintype (H.neighborSet (Sum.inl (S.vertex i))) :=
      Fintype.ofFinite _
    have htwo : 2 ≤ @SimpleGraph.degree _ H (Sum.inl (S.vertex i))
        (Fintype.ofFinite _) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let ss : Finset (Sum V E) := {p.getVert 1, b}
      have hss : ss ⊆ H.neighborFinset (Sum.inl (S.vertex i)) := by
        intro w hw
        simp only [ss, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · simpa [SimpleGraph.mem_neighborFinset] using hnext
        · simpa [SimpleGraph.mem_neighborFinset] using hbstart
      have hc : 2 ≤ ss.card := by simp [ss, hneNext]
      exact hc.trans (Finset.card_le_card hss)
    have honeDeg : @SimpleGraph.degree _ H (Sum.inl (S.vertex i))
        (Fintype.ofFinite _) ≤ 1 := by
      simpa [H] using MissingColorIncidenceEndpoint G phi gamma delta hne
        hproper (S.vertex i) hgamma
    omega
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hleft : H.Adj z (p.getVert (n - 1)) := by
      rw [← hn]
      have hadj := p.adj_getVert_succ (i := n - 1) (by omega)
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hadj.symm
    have hright : H.Adj z (p.getVert (n + 1)) := by
      rw [← hn]
      exact p.adj_getVert_succ hnlt
    have hbneLeft : b ≠ p.getVert (n - 1) := by
      intro heq
      have hindices := hp.getVert_injOn
        (show p.length ≤ p.length by rfl) (show n - 1 ≤ p.length by omega)
        (p.getVert_length.trans heq)
      omega
    have hbneRight : b ≠ p.getVert (n + 1) := by
      intro heq
      have hindices := hp.getVert_injOn
        (show p.length ≤ p.length by rfl) (show n + 1 ≤ p.length by omega)
        (p.getVert_length.trans heq)
      omega
    have hlrne : p.getVert (n - 1) ≠ p.getVert (n + 1) := by
      intro heq
      have hindices := hp.getVert_injOn
        (show n - 1 ≤ p.length by omega) (show n + 1 ≤ p.length by omega) heq
      omega
    let : Fintype (H.neighborSet z) := Fintype.ofFinite _
    have hthree : 3 ≤ @SimpleGraph.degree _ H z (Fintype.ofFinite _) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let ss : Finset (Sum V E) := {b, p.getVert (n - 1), p.getVert (n + 1)}
      have hss : ss ⊆ H.neighborFinset z := by
        intro w hw
        simp only [ss, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · simpa [SimpleGraph.mem_neighborFinset] using hbz.symm
        · simpa [SimpleGraph.mem_neighborFinset] using hleft
        · simpa [SimpleGraph.mem_neighborFinset] using hright
      have hc : 3 ≤ ss.card := by
        simp [ss, hbneLeft, hbneRight, hlrne]
      exact hc.trans (Finset.card_le_card hss)
    have htwo : @SimpleGraph.degree _ H z (Fintype.ofFinite _) ≤ 2 := by
      simpa [H] using TwoColorIncidenceDegreeAtMostTwo G phi gamma delta hproper z
    omega

private theorem helper_hbVertex_325.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi :
        PartialEdgeColoring E k) (S : TreeSequence G e0) (i _ : Fin (S.length + (1 : ℕ))) (gamma
        delta : Fin k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi gamma delta;
    ∀ (_ b : V ⊕ E) (p : H.Walk (Sum.inl (S.vertex i)) b), (0 : ℕ) < p.length → (
    ∀ (z : V ⊕ E), H.Adj b z → z = p.getVert (p.length - (1 : ℕ))) →
    ∃ (v : V), b = Sum.inl v := by
  classical
  intro V E G k e0 phi S i j gamma delta H b b p hp_pos hend_neighbor
  cases hbcase : b with
  | inl v => exact ⟨v, rfl⟩
  | inr e =>
      have hlastAdj : H.Adj (p.getVert (p.length - 1)) b := by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.length),
          p.getVert_length] using
          p.adj_getVert_succ (i := p.length - 1) (by omega)
      have hecolor : phi e = some gamma ∨ phi e = some delta := by
        cases hprev : p.getVert (p.length - 1) with
        | inl v =>
            rw [hprev, hbcase] at hlastAdj
            simpa [H, TwoColorIncidenceGraph] using hlastAdj |>.2
        | inr f =>
            rw [hprev, hbcase] at hlastAdj
            simp [H, TwoColorIncidenceGraph] at hlastAdj
      induction hends : G.ends e using Sym2.inductionOn with
      | _ u v =>
          have huv : u ≠ v := by
            intro huv
            subst v
            exact G.loopless e u hends
          have huAdj : H.Adj b (Sum.inl u) := by
            rw [hbcase]
            simpa [H, TwoColorIncidenceGraph, Incident, hends] using
              (show Incident G u e ∧
                  (phi e = some gamma ∨ phi e = some delta) from
                ⟨by simp [Incident, hends], hecolor⟩)
          have hvAdj : H.Adj b (Sum.inl v) := by
            rw [hbcase]
            simpa [H, TwoColorIncidenceGraph, Incident, hends] using
              (show Incident G v e ∧
                  (phi e = some gamma ∨ phi e = some delta) from
                ⟨by simp [Incident, hends], hecolor⟩)
          have heq := (hend_neighbor _ huAdj).trans (hend_neighbor _ hvAdj).symm
          exact False.elim (huv (Sum.inl.inj heq))

private theorem helper_hvlast_eq_j_369.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0) (i j : Fin (S.length +
        (1 : ℕ))) (gamma delta : Fin k), gamma ∈ MissingColors G phi (S.vertex i) → delta ∈
        MissingColors G phi (S.vertex j) →
    let X : Finset V := TreeSequenceVertexSet T;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi gamma delta; gamma ≠ delta →
        S.vertex i ∈ X → S.vertex j ∈ X → ColoredVertexSetElementary G phi X →
    ∀ (_ b : V ⊕ E) (p : H.Walk (Sum.inl (S.vertex i)) b), (
    ∀ (z : V ⊕ E), H.Adj b z → z = p.getVert (p.length - (1 : ℕ))) →
    ∀ (vlast : V), b = Sum.inl vlast → vlast ∈ X → vlast ≠ S.vertex i → vlast = S.vertex j := by
  classical
  intro V E _ _ G k e0 phi T S i j gamma delta hgamma hdelta X H hne hXi hXj hXelem b b p
      hend_neighbor vlast hb hvlastX hvlast_ne_i
  let _ := Fintype.ofFinite V
  by_contra hne_j
  have hgnot : gamma ∉ MissingColors G phi vlast := by
    intro hm
    have hd := hXelem hXi hvlastX (Ne.symm hvlast_ne_i)
    exact (Finset.disjoint_left.mp hd) hgamma hm
  have hdnot : delta ∉ MissingColors G phi vlast := by
    intro hm
    have hd := hXelem hXj hvlastX (Ne.symm hne_j)
    exact (Finset.disjoint_left.mp hd) hdelta hm
  have hgpres : gamma ∈ PresentColors G phi vlast := by
    simpa [MissingColors] using hgnot
  have hdpres : delta ∈ PresentColors G phi vlast := by
    simpa [MissingColors] using hdnot
  obtain ⟨eg, hegInc, hegColor⟩ := by simpa [PresentColors] using hgpres
  obtain ⟨ed, hedInc, hedColor⟩ := by simpa [PresentColors] using hdpres
  have hegAdj : H.Adj b (Sum.inr eg) := by
    rw [hb]
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G vlast eg ∧
          (phi eg = some gamma ∨ phi eg = some delta) from
        ⟨hegInc, Or.inl hegColor⟩)
  have hedAdj : H.Adj b (Sum.inr ed) := by
    rw [hb]
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G vlast ed ∧
          (phi ed = some gamma ∨ phi ed = some delta) from
        ⟨hedInc, Or.inr hedColor⟩)
  have heq := (hend_neighbor _ hegAdj).trans (hend_neighbor _ hedAdj).symm
  have egeq : eg = ed := Sum.inr.inj heq
  subst ed
  exact hne (Option.some.inj (hegColor.symm.trans hedColor))

private theorem helper_hflip_497.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi
        : PartialEdgeColoring E k) (S : TreeSequence G e0) (i j : Fin (S.length + (1 : ℕ))) (gamma
        delta : Fin k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi gamma delta; IsProperEdgeColoring
        G phi → gamma ≠ delta →
    ∀ (p : H.Walk (Sum.inl (S.vertex i)) (Sum.inl (S.vertex j))), p.IsPath → (
    ∀ n ≤ p.length, (n % (2 : ℕ) = (0 : ℕ) →
    ∃ (v : V), p.getVert n = Sum.inl v) ∧ (n % (2 : ℕ) = (1 : ℕ) →
    ∃ (e : E), p.getVert n = Sum.inr e)) →
    let m : ℕ := p.length / (2 : ℕ); p.length = (2 : ℕ) * m → (
    ∀ n < m,
    ∃ (e : E), p.getVert ((2 : ℕ) * n + (1 : ℕ)) = Sum.inr e ∧ (phi e = some gamma ∨ phi e = some
        delta)) → (
    ∃ (e : E), p.getVert (1 : ℕ) = Sum.inr e ∧ phi e = some delta) →
    ∀ n < m, (n % (2 : ℕ) = (0 : ℕ) →
    ∃ (e : E), p.getVert ((2 : ℕ) * n + (1 : ℕ)) = Sum.inr e ∧ phi e = some delta) ∧ (n % (2 : ℕ)
        = (1 : ℕ) →
    ∃ (e : E), p.getVert ((2 : ℕ) * n + (1 : ℕ)) = Sum.inr e ∧ phi e = some gamma) := by
  classical
  intro V E _ G k e0 phi S i j gamma delta H hproper hne p hp hshape m hlen hcolored hfirst n
  let := Fintype.ofFinite E
  induction n with
  | zero =>
      intro hn
      exact ⟨fun _ => hfirst, fun h => by omega⟩
  | succ n ih =>
      intro hn
      have hnold : n < m := by omega
      have hold := ih hnold
      obtain ⟨f, hf, hfcolor⟩ := hcolored (n + 1) hn
      have step_data : ∀ (e : E),
          p.getVert (2 * n + 1) = Sum.inr e →
          ∀ (c : Fin k), phi e = some c →
          ∃ f, p.getVert (2 * (n + 1) + 1) = Sum.inr f ∧
            phi f = some (if c = gamma then delta else gamma) := by
        intro e he c hec
        have hef : e ≠ f := by
          intro heq
          subst f
          have hindices := hp.getVert_injOn
            (show 2 * n + 1 ≤ p.length by rw [hlen]; omega)
            (show 2 * (n + 1) + 1 ≤ p.length by rw [hlen]; omega)
            (he.trans hf.symm)
          omega
        obtain ⟨v, hv⟩ :=
          (hshape (2 * n + 2) (by rw [hlen]; omega)).1 (by omega)
        have ha := p.adj_getVert_succ (i := 2 * n + 1)
          (by rw [hlen]; omega)
        have hb := p.adj_getVert_succ (i := 2 * n + 2)
          (by rw [hlen]; omega)
        rw [he, hv] at ha
        have hf' : p.getVert (2 * n + 2 + 1) = Sum.inr f := by
          rw [show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by omega]
          exact hf
        rw [hv, hf'] at hb
        have haData : Incident G v e ∧
            (phi e = some gamma ∨ phi e = some delta) := by
          simpa [H, TwoColorIncidenceGraph] using ha
        have hbData : Incident G v f ∧
            (phi f = some gamma ∨ phi f = some delta) := by
          simpa [H, TwoColorIncidenceGraph] using hb
        by_cases hcg : c = gamma
        · subst c
          have hfd : phi f = some delta := hfcolor.resolve_left (by
            intro hfg
            exact (hproper hef ⟨v, haData.1, hbData.1⟩ hec) hfg)
          exact ⟨f, hf, by simpa [hne] using hfd⟩
        · have hcd : c = delta := by
            rcases haData.2 with h | h
            · exact False.elim (hcg (Option.some.inj (hec.symm.trans h)))
            · exact Option.some.inj (hec.symm.trans h)
          have hfg : phi f = some gamma := hfcolor.resolve_right (by
            intro hfd
            exact (hproper hef ⟨v, haData.1, hbData.1⟩
              (hcd ▸ hec)) hfd)
          exact ⟨f, hf, by simpa [hcg] using hfg⟩
      constructor
      · intro heven
        obtain ⟨e, he, hec⟩ := hold.2 (by omega)
        obtain ⟨f, hf', hfc⟩ := step_data e he gamma hec
        exact ⟨f, hf', by simpa [hne] using hfc⟩
      · intro hodd
        obtain ⟨e, he, hec⟩ := hold.1 (by omega)
        obtain ⟨f, hf', hfc⟩ := step_data e he delta hec
        have hdg : delta ≠ gamma := hne.symm
        exact ⟨f, hf', by simpa [hdg] using hfc⟩

private theorem helper_branch_588.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (S : TreeSequence G e0), TashkinovTree G e0 phi S
        →
    ∀ (i j : Fin (S.length + (1 : ℕ))), (↑i : ℕ) < (↑j : ℕ) →
    ∀ (gamma delta : Fin k), gamma ∈ MissingColors G phi (S.vertex i) → delta ∈ MissingColors G
        phi (S.vertex j) →
    let XS : Finset V := TreeSequenceVertexSet S;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi gamma delta;
    let _ : Set (V ⊕ E) := TwoColorComponent G phi gamma delta (Sum.inl (S.vertex i));
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 → ColoredVertexSetElementary G phi
        XS → S.vertex j ∈ XS → gamma ≠ delta →
    ∀ (_ : H.Walk (Sum.inl (S.vertex i)) (Sum.inl (S.vertex j))), TreeColorUnusedThrough phi S
        gamma j → IsProperEdgeColoring G (TwoColorComponentSwap G phi gamma delta (Sum.inl
        (S.vertex i))) ∧ IsOneEdgeUncolored (TwoColorComponentSwap G phi gamma delta (Sum.inl
        (S.vertex i))) e0 ∧ TashkinovTree G e0 (TwoColorComponentSwap G phi gamma delta (Sum.inl
        (S.vertex i))) S := by
  classical
  intro V E _ _ G k e0 phi S hS i j hij gamma delta hgamma hdelta XS H C hproper hone hSelem hjS hne
      p hgammaUnused
  let _ := Fintype.ofFinite V
  have hdeltaUnused : TreeColorUnusedThrough phi S delta j := by
    intro r hr hrj hed
    obtain ⟨w, c, hc, hm⟩ := hS r hr
    have hcEq : c = delta := Option.some.inj (hc.symm.trans hed)
    subst c
    let wfull : Fin (S.length + 1) := Fin.castLT w
      (Nat.lt_trans w.isLt (Nat.succ_lt_succ r.isLt))
    have hwS : S.vertex wfull ∈ XS := by
      simp [XS, TreeSequenceVertexSet]
    have hwlt : wfull.val < j.val := by
      dsimp [wfull]
      omega
    have hwne : S.vertex wfull ≠ S.vertex j := by
      intro heq
      have hind := S.vertex_injective heq
      exact (Fin.ne_of_lt hwlt) hind
    have hd := hSelem hwS hjS hwne
    exact (Finset.disjoint_left.mp hd) hm hdelta
  have hcc : H.connectedComponentMk (Sum.inl (S.vertex i)) =
      H.connectedComponentMk (Sum.inl (S.vertex j)) := by
    exact SimpleGraph.ConnectedComponent.eq.mpr ⟨p⟩
  have hiCj : Sum.inl (S.vertex i) ∈
      TwoColorComponent G phi gamma delta (Sum.inl (S.vertex j)) := by
    change H.connectedComponentMk (Sum.inl (S.vertex i)) =
      H.connectedComponentMk (Sum.inl (S.vertex j))
    exact hcc
  have htransport := TashkinovTreeComponentSwapWitnessTransport
    G k e0 phi S hproper hS i j hij gamma delta hne hgamma hdelta
      hgammaUnused hdeltaUnused
  dsimp only at htransport
  have hTashJ : TashkinovTree G e0
      (TwoColorComponentSwap G phi gamma delta
        (Sum.inl (S.vertex j))) S :=
    (htransport.2.2 hiCj).2
  have hcompEq :
      TwoColorComponent G phi gamma delta (Sum.inl (S.vertex i)) =
        TwoColorComponent G phi gamma delta (Sum.inl (S.vertex j)) := by
    exact congrArg SimpleGraph.ConnectedComponent.supp hcc
  have hswapEq :
      TwoColorComponentSwap G phi gamma delta (Sum.inl (S.vertex i)) =
        TwoColorComponentSwap G phi gamma delta (Sum.inl (S.vertex j)) := by
    funext e
    simp only [TwoColorComponentSwap]
    rw [hcompEq]
  have hproper' : IsProperEdgeColoring G
      (TwoColorComponentSwap G phi gamma delta
        (Sum.inl (S.vertex i))) :=
    TwoColorComponentSwapProper G phi gamma delta hne hproper
      (Sum.inl (S.vertex i))
  have hone' : IsOneEdgeUncolored
      (TwoColorComponentSwap G phi gamma delta
        (Sum.inl (S.vertex i))) e0 := by
    constructor
    · simp [TwoColorComponentSwap, hone.1]
    · intro e he0
      obtain ⟨c, hc⟩ := hone.2 e he0
      by_cases heC : Sum.inr e ∈ C
      · by_cases hcg : c = gamma
        · refine ⟨delta, ?_⟩
          simp [TwoColorComponentSwap, C, heC, hc, hcg]
        · by_cases hcd : c = delta
          · refine ⟨gamma, ?_⟩
            simp [TwoColorComponentSwap, C, heC, hc, hcd]
          · refine ⟨c, ?_⟩
            simp [TwoColorComponentSwap, C, heC, hc, hcg, hcd]
      · exact ⟨c, by
          simpa [TwoColorComponentSwap, C, heC] using hc⟩
  exact ⟨hproper', hone', by simpa [hswapEq] using hTashJ⟩

private theorem helper_continuation_613.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0), TashkinovTree G e0 phi
        S →
    ∀ (i j : Fin (S.length + (1 : ℕ))), (↑i : ℕ) < (↑j : ℕ) →
    ∀ (gamma delta : Fin k), gamma ∈ MissingColors G phi (S.vertex i) → delta ∈ MissingColors G
        phi (S.vertex j) →
    let X : Finset V := TreeSequenceVertexSet T;
    let XS : Finset V := TreeSequenceVertexSet S;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G phi gamma delta (Sum.inl (S.vertex i));
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 → ColoredVertexSetElementary G phi
        XS → S.vertex j ∈ XS → gamma ≠ delta → S.vertex i ∈ X → S.vertex j ∈ X →
        ColoredVertexSetElementary G phi X → (
    ∀ (v : V), Sum.inl v ∈ C → v ∈ X) →
    ∀ (b : V ⊕ E) (p : H.Walk (Sum.inl (S.vertex i)) b), p.IsPath → {z : V ⊕ E | z ∈ p.support} =
        C →
    ∀ (firstEdge : E), Sum.inr firstEdge ∈ C →
    ∃ (p : (TwoColorIncidenceGraph G phi gamma delta).Walk (Sum.inl (S.vertex i)) (Sum.inl
        (S.vertex j))), p.IsPath ∧ {z : V ⊕ E | z ∈ p.support} = TwoColorComponent G phi gamma
        delta (Sum.inl (S.vertex i)) ∧ (4 : ℕ) ∣ p.length ∧ (
    ∀ (v : V), Sum.inl v ∈ p.support → v ∈ TreeSequenceVertexSet T) ∧ (TreeColorUnusedThrough phi
        S gamma j → IsProperEdgeColoring G (TwoColorComponentSwap G phi gamma delta (Sum.inl
        (S.vertex i))) ∧ IsOneEdgeUncolored (TwoColorComponentSwap G phi gamma delta (Sum.inl
        (S.vertex i))) e0 ∧ TashkinovTree G e0 (TwoColorComponentSwap G phi gamma delta (Sum.inl
        (S.vertex i))) S) := by
  classical
  intro V E _ _ G k e0 phi T S hS i j hij gamma delta hgamma hdelta X XS H C hproper hone hSelem hjS
      hne hXi hXj hXelem hcomponent_vertex b p hp hps firstEdge hfirstC
  let _ := Fintype.ofFinite V
  have hpnil : ¬ p.Nil := by
    intro hnil
    have hfirstSupport : Sum.inr firstEdge ∈ p.support := by
      change Sum.inr firstEdge ∈ {z | z ∈ p.support}
      rw [hps]
      exact hfirstC
    cases hnil
    simp at hfirstSupport
  have hp_pos : 0 < p.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp hpnil
  have hbC : b ∈ C := by
    rw [← hps]
    change b ∈ p.support
    simpa only [p.getVert_length] using p.getVert_mem_support p.length
  have hend_neighbor := @helper_hend_neighbor_227 V E inferInstance inferInstance G k e0 phi S i j
      gamma delta hgamma hproper hne b b p hp hps hpnil hp_pos hbC
  have hbVertex := @helper_hbVertex_325 V E G k e0 phi S i j gamma delta b b p hp_pos hend_neighbor
  obtain ⟨vlast, hb⟩ := hbVertex
  have hvlastC : Sum.inl vlast ∈ C := by simpa [hb] using hbC
  have hvlastX : vlast ∈ X := hcomponent_vertex vlast hvlastC
  have hvlast_ne_i : vlast ≠ S.vertex i := by
    intro heq
    have hendsame : b = Sum.inl (S.vertex i) := by simp [hb, heq]
    have : p.Nil := hp.nil_iff_eq.mpr hendsame.symm
    exact hpnil this
  have hvlast_eq_j := @helper_hvlast_eq_j_369 V E inferInstance inferInstance G k e0 phi T S i j
      gamma delta hgamma hdelta hne hXi hXj hXelem b b p hend_neighbor vlast hb hvlastX hvlast_ne_i
  subst vlast
  have hbfinal : b = Sum.inl (S.vertex j) := hb
  subst b
  have hshape : ∀ n ≤ p.length,
      (n % 2 = 0 → ∃ v, p.getVert n = Sum.inl v) ∧
      (n % 2 = 1 → ∃ e, p.getVert n = Sum.inr e) := by
    intro n
    induction n with
    | zero =>
        intro hn
        constructor
        · intro _
          exact ⟨S.vertex i, p.getVert_zero⟩
        · omega
    | succ n ih =>
        intro hn
        have hnlt : n < p.length := by omega
        have hadj := p.adj_getVert_succ hnlt
        have hold := ih (by omega)
        constructor
        · intro heven
          obtain ⟨e, he⟩ := hold.2 (by omega)
          cases hnext : p.getVert (n + 1) with
          | inl v => exact ⟨v, rfl⟩
          | inr f =>
              rw [he, hnext] at hadj
              simp [H, TwoColorIncidenceGraph] at hadj
        · intro hodd
          obtain ⟨v, hv⟩ := hold.1 (by omega)
          cases hnext : p.getVert (n + 1) with
          | inl w =>
              rw [hv, hnext] at hadj
              simp [H, TwoColorIncidenceGraph] at hadj
          | inr e => exact ⟨e, rfl⟩
  have hlenEven : p.length % 2 = 0 := by
    by_contra hnot
    have hodd : p.length % 2 = 1 := by omega
    obtain ⟨e, he⟩ := (hshape p.length (by rfl)).2 hodd
    rw [p.getVert_length] at he
    simp at he
  let m := p.length / 2
  have hlen : p.length = 2 * m := by
    dsimp [m]
    omega
  have hmpos : 0 < m := by
    rw [hlen] at hp_pos
    omega
  have hcolored : ∀ n < m, ∃ e,
      p.getVert (2 * n + 1) = Sum.inr e ∧
        (phi e = some gamma ∨ phi e = some delta) := by
    intro n hn
    have hindex : 2 * n + 1 ≤ p.length := by rw [hlen]; omega
    obtain ⟨e, he⟩ := (hshape (2 * n + 1) hindex).2 (by omega)
    obtain ⟨v, hv⟩ := (hshape (2 * n) (by rw [hlen]; omega)).1 (by omega)
    have hadj := p.adj_getVert_succ (i := 2 * n) (by rw [hlen]; omega)
    rw [hv, he] at hadj
    have hdata : Incident G v e ∧
        (phi e = some gamma ∨ phi e = some delta) := by
      simpa [H, TwoColorIncidenceGraph] using hadj
    exact ⟨e, he, hdata.2⟩
  have hfirst : ∃ e, p.getVert 1 = Sum.inr e ∧ phi e = some delta := by
    obtain ⟨e, he, hecolor⟩ := hcolored 0 hmpos
    have hadj := p.adj_getVert_succ (i := 0) (by rw [hlen]; omega)
    rw [p.getVert_zero, he] at hadj
    have hdata : Incident G (S.vertex i) e ∧
        (phi e = some gamma ∨ phi e = some delta) := by
      simpa [H, TwoColorIncidenceGraph] using hadj
    have hnotGamma : phi e ≠ some gamma := by
      intro heg
      have hpresent : gamma ∈ PresentColors G phi (S.vertex i) := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, hdata.1, heg⟩
      have hnotpresent : gamma ∉ PresentColors G phi (S.vertex i) := by
        simpa [MissingColors] using hgamma
      exact hnotpresent hpresent
    exact ⟨e, he, hecolor.resolve_left hnotGamma⟩
  have hlast : ∃ e, p.getVert (p.length - 1) = Sum.inr e ∧
      phi e = some gamma := by
    obtain ⟨e, he, hecolor⟩ := hcolored (m - 1) (by omega)
    have hindex : 2 * (m - 1) + 1 = p.length - 1 := by rw [hlen]; omega
    rw [hindex] at he
    have hadj := p.adj_getVert_succ (i := p.length - 1) (by omega)
    have hnext : p.length - 1 + 1 = p.length := by omega
    rw [hnext, p.getVert_length, he] at hadj
    have hdata : Incident G (S.vertex j) e ∧
        (phi e = some gamma ∨ phi e = some delta) := by
      simpa [H, TwoColorIncidenceGraph] using hadj.symm
    have hnotDelta : phi e ≠ some delta := by
      intro hed
      have hpresent : delta ∈ PresentColors G phi (S.vertex j) := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, hdata.1, hed⟩
      have hnotpresent : delta ∉ PresentColors G phi (S.vertex j) := by
        simpa [MissingColors] using hdelta
      exact hnotpresent hpresent
    exact ⟨e, he, hecolor.resolve_right hnotDelta⟩
  have hflip := @helper_hflip_497 V E inferInstance G k e0 phi S i j gamma delta hproper hne p hp
      hshape hlen hcolored hfirst
  have hlastIndex : 2 * (m - 1) + 1 = p.length - 1 := by rw [hlen]; omega
  have hmpar : (m - 1) % 2 = 1 := by
    by_contra hnot
    have heven : (m - 1) % 2 = 0 := by omega
    obtain ⟨ed, hed, hedcolor⟩ := (hflip (m - 1) (by omega)).1 heven
    obtain ⟨eg, heg, hegcolor⟩ := hlast
    have heq : ed = eg := by
      apply Sum.inr.inj
      rw [← hed, hlastIndex, heg]
    subst eg
    exact hne (Option.some.inj (hegcolor.symm.trans hedcolor))
  have hmEven : m % 2 = 0 := by omega
  have hdiv : 4 ∣ p.length := by
    refine ⟨m / 2, ?_⟩
    omega
  refine ⟨p, hp, hps, hdiv, ?_, ?_⟩
  · intro v hvp
    apply hcomponent_vertex v
    rw [← hps]
    exact hvp
  · exact @helper_branch_588 V E inferInstance inferInstance G k e0 phi S hS i j hij gamma delta
      hgamma hdelta hproper hone hSelem hjS hne p

theorem ScheideMaximalKempePath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (hmax : FixedPairMaximalTashkinovTree G e0 phi T)
    (hS : TashkinovTree G e0 phi S)
    (i j : Fin (S.length + 1)) (hij : i.val < j.val)
    (gamma delta : Fin k)
    (hgamma : gamma ∈ MissingColors G phi (S.vertex i))
    (hdelta : delta ∈ MissingColors G phi (S.vertex j)) :
    gamma ≠ delta ∧
      ∃ p :
        (TwoColorIncidenceGraph G phi gamma delta).Walk (Sum.inl (S.vertex i))
          (Sum.inl (S.vertex j)),
        p.IsPath ∧
          {z | z ∈ p.support} = TwoColorComponent G phi gamma delta (Sum.inl (S.vertex i)) ∧
            4 ∣ p.length ∧
              (∀ v : V, Sum.inl v ∈ p.support → v ∈ TreeSequenceVertexSet T) ∧
                (TreeColorUnusedThrough phi S gamma j →
                  IsProperEdgeColoring G
                      (TwoColorComponentSwap G phi gamma delta (Sum.inl (S.vertex i))) ∧
                    IsOneEdgeUncolored
                        (TwoColorComponentSwap G phi gamma delta (Sum.inl (S.vertex i)))
                        e0 ∧
                      TashkinovTree G e0
                        (TwoColorComponentSwap G phi gamma delta (Sum.inl (S.vertex i))) S) := by
  classical
  let X := TreeSequenceVertexSet T
  let XS := TreeSequenceVertexSet S
  let H := TwoColorIncidenceGraph G phi gamma delta
  let C := TwoColorComponent G phi gamma delta (Sum.inl (S.vertex i))
  have hproper : IsProperEdgeColoring G phi := htriple.2.2.2.1
  have hone : IsOneEdgeUncolored phi e0 := htriple.2.2.2.2
  have hSelem : ColoredVertexSetElementary G phi XS :=
    TashTree G k e0 phi S htriple hS
  have hiS : S.vertex i ∈ XS := by
    simp [XS, TreeSequenceVertexSet]
  have hjS : S.vertex j ∈ XS := by
    simp [XS, TreeSequenceVertexSet]
  have hvne : S.vertex i ≠ S.vertex j := by
    intro h
    exact (Fin.ne_of_lt hij) (S.vertex_injective h)
  have hne : gamma ≠ delta := by
    intro h
    subst delta
    have hd := hSelem hiS hjS hvne
    exact (Finset.disjoint_left.mp hd) hgamma hdelta
  refine ⟨hne, ?_⟩
  have hsub : XS ⊆ X := by
    exact ScheideMaximalContainsEveryTree G k e0 phi T S htriple hmax hS
  have hXi : S.vertex i ∈ X := hsub hiS
  have hXj : S.vertex j ∈ X := hsub hjS
  have hXdata := ScheideMaximalElementaryClosed G k e0 phi T htriple hmax
  have hXelem : ColoredVertexSetElementary G phi X := hXdata.1
  have hXclosed : ColoredVertexSetClosed G phi X := hXdata.2
  have edge_internal : ∀ (e : E),
      (phi e = some gamma ∨ phi e = some delta) →
      ∀ u, u ∈ X → Incident G u e →
      ∀ v, Incident G v e → v ∈ X := by
    intro e hecolor u hu hue v hve
    by_contra hv
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hve
    have hevw : G.ends e = s(v, w) := hw
    have hupair : u = v ∨ u = w := by
      have : u ∈ s(v, w) := by rw [← hevw]; exact hue
      simpa using this
    have hwX : w ∈ X := by
      rcases hupair with huv | huw
      · exact False.elim (hv (huv ▸ hu))
      · exact huw ▸ hu
    have heb : e ∈ BoundaryEdges G X := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨w, hwX, v, hv, hevw.trans Sym2.eq_swap⟩
    rcases hecolor with heg | hed
    · exact (hXclosed heb hXi heg) hgamma
    · exact (hXclosed heb hXj hed) hdelta
  let Good : Sum V E → Prop := fun z =>
    match z with
    | Sum.inl v => v ∈ X
    | Sum.inr e => ∀ v, Incident G v e → v ∈ X
  let HG := (⊤ : H.Subgraph).induce Good
  have hGoodClosed : ∀ z ∈ HG.verts, ∀ w, H.Adj z w → HG.Adj z w := by
    intro z hz w hzw
    have hzGood : Good z := by
      change Good z at hz
      exact hz
    have hwGood : Good w := by
      cases z with
      | inl u =>
          cases w with
          | inl v => simp [H, TwoColorIncidenceGraph] at hzw
          | inr e =>
              have hdata : Incident G u e ∧
                  (phi e = some gamma ∨ phi e = some delta) := by
                simpa [H, TwoColorIncidenceGraph] using hzw
              exact edge_internal e hdata.2 u (by simpa [Good] using hzGood)
                hdata.1
      | inr e =>
          cases w with
          | inl v =>
              have hdata : Incident G v e ∧
                  (phi e = some gamma ∨ phi e = some delta) := by
                simpa [H, TwoColorIncidenceGraph] using hzw
              exact hzGood v hdata.1
          | inr f => simp [H, TwoColorIncidenceGraph] at hzw
    exact ⟨hzGood, hwGood, by simpa [HG] using hzw⟩
  have hcomponent_vertex : ∀ v : V, Sum.inl v ∈ C → v ∈ X := by
    intro v hvC
    have hreach : H.Reachable (Sum.inl (S.vertex i)) (Sum.inl v) := by
      change H.connectedComponentMk (Sum.inl v) =
          H.connectedComponentMk (Sum.inl (S.vertex i)) at hvC
      exact SimpleGraph.ConnectedComponent.eq.mp hvC.symm
    have hroot : Sum.inl (S.vertex i) ∈ HG.verts := by
      change Good (Sum.inl (S.vertex i))
      simpa [Good] using hXi
    have hvHG := hreach.mem_subgraphVerts hGoodClosed hroot
    change Good (Sum.inl v) at hvHG
    simpa [Good] using hvHG
  have hiSub : Set.Subsingleton (H.neighborSet (Sum.inl (S.vertex i))) := by
    let : Fintype (H.neighborSet (Sum.inl (S.vertex i))) :=
      Fintype.ofFinite _
    have hdeg := MissingColorIncidenceEndpoint G phi gamma delta hne hproper
      (S.vertex i) hgamma
    have hcard : (H.neighborFinset (Sum.inl (S.vertex i))).card ≤ 1 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      simpa [H] using hdeg
    intro z hz w hw
    exact (Finset.card_le_one.mp hcard) z
      (by simpa [SimpleGraph.mem_neighborFinset] using hz) w
      (by simpa [SimpleGraph.mem_neighborFinset] using hw)
  obtain ⟨a, b, q, hq, hqs⟩ :=
    TwoColorComponentSpanningPath G phi gamma delta hproper
      (Sum.inl (S.vertex i))
  have hiC : Sum.inl (S.vertex i) ∈ C := by
    change Sum.inl (S.vertex i) ∈
      H.connectedComponentMk (Sum.inl (S.vertex i))
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have hiq : Sum.inl (S.vertex i) ∈ q.support := by
    change Sum.inl (S.vertex i) ∈ {z | z ∈ q.support}
    rw [hqs]
    exact hiC
  have hiEnd : (Sum.inl (S.vertex i) : Sum V E) = a ∨
      Sum.inl (S.vertex i) = b := by
    by_contra hn
    push Not at hn
    exact (hq.isTrail.notMem_support_of_subsingleton_neighborSet
      hn.1 hn.2 hiSub) hiq
  obtain ⟨b, p, hp, hps⟩ : ∃ b,
      ∃ p : H.Walk (Sum.inl (S.vertex i)) b,
        p.IsPath ∧ {z | z ∈ p.support} = C := by
    rcases hiEnd with hia | hib
    · subst a
      exact ⟨b, q, hq, hqs⟩
    · subst b
      refine ⟨a, q.reverse, hq.reverse, ?_⟩
      ext z
      rw [SimpleGraph.Walk.support_reverse]
      simpa using Set.ext_iff.mp hqs z
  have hdeltaPresentI : delta ∈ PresentColors G phi (S.vertex i) := by
    have hnot : delta ∉ MissingColors G phi (S.vertex i) := by
      intro hm
      have hd := hXelem hXi hXj hvne
      exact (Finset.disjoint_left.mp hd) hm hdelta
    simpa [MissingColors] using hnot
  obtain ⟨firstEdge, hfirstInc, hfirstColor⟩ := by
    simpa [PresentColors] using hdeltaPresentI
  have hfirstAdj : H.Adj (Sum.inl (S.vertex i)) (Sum.inr firstEdge) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (S.vertex i) firstEdge ∧
          (phi firstEdge = some gamma ∨ phi firstEdge = some delta) from
        ⟨hfirstInc, Or.inr hfirstColor⟩)
  have hfirstC : Sum.inr firstEdge ∈ C := by
    change H.connectedComponentMk (Sum.inr firstEdge) =
      H.connectedComponentMk (Sum.inl (S.vertex i))
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hfirstAdj |>.symm
  exact @helper_continuation_613 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi)
      (@T) (@S) (@hS) (@i) (@j) (@hij) (@gamma) (@delta) (@hgamma) (@hdelta) (@hproper) (@hone)
      (@hSelem) (@hjS) (@hne) (@hXi) (@hXj) (@hXelem) (@hcomponent_vertex) (@b) (@p) (@hp) (@hps)
      (@firstEdge) (@hfirstC)
end GoldbergSeymour

end
