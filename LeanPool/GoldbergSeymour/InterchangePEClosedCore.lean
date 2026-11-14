/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.InterchangePEClosureConstituent
public import LeanPool.GoldbergSeymour.InterchangePECommonMissingClosed
public import LeanPool.GoldbergSeymour.InterchangePETreeAwayFromDelta

public import LeanPool.GoldbergSeymour.ParallelBaseFourCommonMissingColors
public import LeanPool.GoldbergSeymour.TwoColorMissingVertexNeighbors

/-!
# Interchange PEClosed Core

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hterminal_154.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : ett.series.data.kind
        (Fin.last ett.rounds) = some TashkinovExtensionKind.PE),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) =>
    by
                omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : q.succ = n),
    ∃ (gamma : Fin k) (delta : Fin k) (f : E), ett.series.data.gamma n = some gamma ∧
        ett.series.data.delta n = some delta ∧ ett.series.data.connectingEdges n = { f } ∧
        ett.series.data.stored n = { delta, gamma } := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive hPE n q hq
  have hp : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE := by simpa [hq, n] using hPE
  generalize ht : q.succ = slot at hp
  have cert := ett.series.certified slot
  cases cert with
  | initial => exact (Fin.succ_ne_zero q ht).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    rw [currentKind] at hp
    cases hp
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    rw [currentKind] at hp
    cases hp
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
    have hi : i = q := by
      apply Fin.ext
      have hh := congrArg Fin.val ht
      simp at hh
      omega
    subst i
    exact ⟨gamma, choice.color, choice.edge,
      by simpa [hq] using currentGamma,
      by simpa [hq] using currentDelta,
      by simpa [hq] using currentEdges,
      by simpa [hq] using currentStored⟩

private theorem helper_hdeltaBoundary_215.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ :
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE) (base :
        HierarchyBase ett generating) (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored
        sigma e0) (_ : CombinedStableColoring (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) base.closure (TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds)) generating sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let X : Finset V := TreeSequenceVertexSet Tn;
    let Y : Finset V := TreeSequenceVertexSet base.closure;
    ∀ (_ : ett.series.data.chosenVertex (Fin.last ett.rounds) = some ((ett.series.data.tree
        (Fin.last ett.rounds).castSucc).vertex base.supportPosition)) (_ : generating =
        ett.series.data.coloring (Fin.last ett.rounds)) (_ : IsProperEdgeColoring G generating) (_
        : IsOneEdgeUncolored generating e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) =>
    by
                  omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : q.succ = n) (gamma delta : Fin k) (f : E) (_ : ett.series.data.gamma n = some gamma) (_
        : ett.series.data.delta n = some delta) (_ : ett.series.data.connectingEdges n = { f }) (_
        : delta ∈ TreeMissingColors generating Tn ∪ TashkinovStoredColors ett.series.data n),
    let seed : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    ∀ (_ : TreeSequenceVertexSet seed ⊆ Y),
    ∀ g ∈ BoundaryColorEdges G sigma X delta,
    ∃ w ∈ Y, Incident G w g := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett hpositive hPE base hproper hone hstable n
      Tn X Y hchosen hgen hproperGen honeGen q hq gamma delta f hgamma hdelta hf hdeltaControl
      seed hseedY g hg
  have hgb := (Finset.mem_filter.mp hg).1
  have hgc := (Finset.mem_filter.mp hg).2
  obtain ⟨v, hv, r, hr, hend⟩ := by
    simpa [BoundaryEdges] using hgb
  have hinc : TreeIncidentEdge Tn g :=
    ⟨v, hv, by simp [Incident, hend]⟩
  have hfix := (sc1 G e0 Tn (TashkinovStoredColors ett.series.data n)
    generating sigma hproperGen honeGen hproper hone).mp hstable.1 g hinc
    (Or.inr ⟨delta, hdeltaControl, hgc⟩)
  have hgg : g ∈ BoundaryColorEdges G generating X delta := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    exact ⟨hgb, hfix.symm.trans hgc⟩
  have hb := (HkuParallelBoundaryStructure G k ett.rounds e0 input
    ett.series q f delta gamma (Tn.vertex base.supportPosition)
    (by simpa [hq, n] using hPE) (by simpa [hq] using hf)
    (by simpa [hq] using hdelta) (by simpa [hq] using hgamma)
    (by simpa [hq] using hchosen)).2.1
  have hgg' : g ∈ BoundaryColorEdges G (ett.series.data.coloring q.succ)
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) delta := by
    simpa [hq, Tn, n, ← hgen] using hgg
  obtain ⟨w, hw, hwi⟩ := hb g hgg'
  have hw' : TreeVertexOrder Tn w (Tn.vertex base.supportPosition) := by
    simpa [hq, Tn] using hw
  obtain ⟨i, j, hi, hj, hij⟩ := hw'
  have hj' : j = base.supportPosition := Tn.vertex_injective hj
  subst j
  have hwseed : w ∈ TreeSequenceVertexSet seed := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    refine ⟨(⟨i.val, by omega⟩ : Fin (base.supportPosition.val + 1)), ?_⟩
    simpa [seed, TreeSequencePrefix] using hi
  exact ⟨w, hseedY hwseed, hwi⟩

private theorem helper_transport_460.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : (0 : ℕ) < ett.rounds) (base :
        HierarchyBase ett generating) (_ : IsProperEdgeColoring G sigma) (alpha beta : Fin k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let X : Finset V := TreeSequenceVertexSet Tn;
    let Y : Finset V := TreeSequenceVertexSet base.closure;
    let U : Finset V := TreeSequenceVertexSet base.core;
    ∀ (_ : U = X ∪ Y) (delta : Fin k) (_ : (
    ∀ g ∈ BoundaryColorEdges G sigma X delta,
    ∃ w ∈ Y, Incident G w g)) (_ : alpha ≠ beta) (c : Fin k) (_ : c ≠ beta),
    ∀ w ∈ TreeSequenceVertexSet base.closure,
    let psi : PartialEdgeColoring E k := OutsideTreeColorSwap base.core sigma alpha c; (
    ∀ (e : E), TreeIncidentEdge base.core e → psi e = sigma e) → (
    ∀ {e : E}, e ∈ BoundaryEdges G U → sigma e ≠ some alpha ∧ sigma e ≠ some c) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G psi c beta;
    ∀ r ∉ U, (
    ∃ x ∈ U, Sum.inl x ∈ TwoColorComponent G sigma alpha beta (Sum.inl r)) →
    ∃ s ∈ U, (beta = delta → s ∈ Y) ∧ H.Reachable (Sum.inl r) (Sum.inl s) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett hpositive base hproper alpha beta n Tn X
      Y U hU delta hdeltaBoundary hab c hcb w hwY psi fixed boundaryAvoid H r hr hmeet
  obtain ⟨m, hm, pv, pe, hpv, hpe, hs, hlast, hout, hvcomp,
    hecomp, hcolors, hends, hfresh⟩ :=
    TwoColorComponentNearestSegment G sigma base.core alpha beta r
      hproper hab hr hmeet
  let s := pv 0
  let z : Fin m := ⟨0, by omega⟩
  have hend0 : G.ends (pe z) = s(s, pv z.succ) := by
    simpa [s, z] using hends z
  have hb0 : pe z ∈ BoundaryEdges G U := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨s, hs, pv z.succ, hout z, hend0⟩
  have hcolor0 : sigma (pe z) = some beta :=
    (hcolors z).resolve_left (boundaryAvoid hb0).1
  have hinc0 : TreeIncidentEdge base.core (pe z) :=
    ⟨s, hs, by simp [Incident, hend0]⟩
  have hsY : beta = delta → s ∈ Y := by
    intro hbd
    by_cases hsX : s ∈ X
    · have hoX : pv z.succ ∉ X := by
        intro hx
        apply hout z
        change pv z.succ ∈ U
        rw [hU]
        exact Finset.mem_union_left _ hx
      have hbX : pe z ∈ BoundaryColorEdges G sigma X delta := by
        apply Finset.mem_filter.mpr
        refine ⟨?_, by simpa [hbd] using hcolor0⟩
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨s, hsX, pv z.succ, hoX, hend0⟩
      obtain ⟨w, hwY, hwi⟩ := hdeltaBoundary (pe z) hbX
      have hw : w = s := by
        simp only [Incident, hend0, Sym2.mem_iff] at hwi
        rcases hwi with hw | hw
        · exact hw
        · exfalso
          apply hout z
          change pv z.succ ∈ U
          rw [← hw, hU]
          exact Finset.mem_union_right _ hwY
      exact hw ▸ hwY
    · have hsU : s ∈ U := hs
      rw [hU] at hsU
      exact (Finset.mem_union.mp hsU).resolve_left hsX
  have newColors (i : Fin m) :
      psi (pe i) = some c ∨ psi (pe i) = some beta := by
    by_cases hi : i.val = 0
    · have hiz : i = z := by apply Fin.ext; exact hi
      subst i
      exact Or.inr ((fixed (pe z) hinc0).trans hcolor0)
    · let j : Fin m := ⟨i.val - 1, by omega⟩
      have hji : j.succ = i.castSucc := by
        apply Fin.ext
        simp [j]
        omega
      have hleftout : pv i.castSucc ∉ U := by
        rw [← hji]
        exact hout j
      have hnotinc : ¬ TreeIncidentEdge base.core (pe i) := by
        rintro ⟨x, hx, hxi⟩
        simp only [Incident, hends i, Sym2.mem_iff] at hxi
        rcases hxi with hxi | hxi
        · exact hleftout (hxi ▸ hx)
        · exact hout i (hxi ▸ hx)
      rcases hcolors i with ha | hb
      · exact Or.inl (by simp [psi, OutsideTreeColorSwap, hnotinc, ha])
      · exact Or.inr (by
          simp [psi, OutsideTreeColorSwap, hnotinc, hb, hab.symm, hcb.symm])
  have stepLeft (i : Fin m) : H.Adj (Sum.inl (pv i.castSucc)) (Sum.inr (pe i)) :=
    ⟨by simp [Incident, hends i], newColors i⟩
  have stepRight (i : Fin m) : H.Adj (Sum.inr (pe i)) (Sum.inl (pv i.succ)) :=
    ⟨by simp [Incident, hends i], newColors i⟩
  have reach : ∀ t (ht : t ≤ m),
      H.Reachable (Sum.inl s) (Sum.inl (pv ⟨t, by omega⟩)) := by
    intro t
    induction t with
    | zero => intro ht; exact SimpleGraph.Reachable.refl _
    | succ t ih =>
      intro ht
      let i : Fin m := ⟨t, by omega⟩
      exact (ih (by omega)).trans
        ((stepLeft i).reachable.trans (stepRight i).reachable)
  refine ⟨s, hs, hsY, ?_⟩
  have hr' := (reach m le_rfl).symm
  change H.Reachable (Sum.inl (pv (Fin.last m))) (Sum.inl s) at hr'
  rw [hlast] at hr'
  exact hr'

private theorem helper_hcolor_383.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett generating)
        (alpha beta : Fin k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (delta : Fin k) (_ : (4 : ℕ) ≤ (TreeMissingColors sigma Tn ∩ TreeMissingColors sigma
        base.closure).card),
    ∃ c ∈ TreeMissingColors sigma Tn ∩ TreeMissingColors sigma base.closure, c ≠ alpha ∧ c ≠ beta
        ∧ c ≠ delta := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett base alpha beta n Tn delta hfour
  by_contra hn
  push Not at hn
  have hsubset : TreeMissingColors sigma Tn ∩
      TreeMissingColors sigma base.closure ⊆ {alpha, beta, delta} := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases ha : c = alpha
    · exact Or.inl ha
    by_cases hb : c = beta
    · exact Or.inr (Or.inl hb)
    exact Or.inr (Or.inr (hn c hc ha hb))
  have hle := Finset.card_le_card hsubset
  have hthree : ({alpha, beta, delta} : Finset (Fin k)).card ≤ 3 := by
    exact (Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right ((Finset.card_insert_le _ _).trans
        (by simp)) 1)
  omega

private theorem helper_hproperPsi_447.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett generating) (_
        : IsProperEdgeColoring G sigma) (alpha : Fin k),
    let U : Finset V := TreeSequenceVertexSet base.core;
    ∀ (c : Fin k),
    let psi : PartialEdgeColoring E k := OutsideTreeColorSwap base.core sigma alpha c;
    let flip : Equiv.Perm (Option (Fin k)) := Equiv.swap (some alpha) (some c);
    ∀ (_ : (
    ∀ (e : E) (_ : TreeIncidentEdge base.core e), psi e = sigma e)) (_ : (
    ∀ r ∉ U,
    ∀ (e : E), Incident G r e → psi e = (flip : Option (Fin k) → Option (Fin k)) (sigma e))),
        IsProperEdgeColoring G psi := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett base hproper alpha U c psi flip fixed
      outside e g d heg hadj hed hgd
  obtain ⟨r, hre, hrg⟩ := hadj
  have hold : sigma e = sigma g := by
    by_cases hr : r ∈ U
    · rw [← fixed e ⟨r, hr, hre⟩, ← fixed g ⟨r, hr, hrg⟩]
      exact hed.trans hgd.symm
    · apply flip.injective
      rw [← outside r hr e hre, ← outside r hr g hrg]
      exact hed.trans hgd.symm
  cases he : sigma e with
  | none =>
    by_cases hr : r ∈ U
    · rw [fixed e ⟨r, hr, hre⟩, he] at hed
      cases hed
    · rw [outside r hr e hre, he] at hed
      simp [flip, Equiv.swap_apply_def] at hed
  | some d' =>
    exact hproper heg ⟨r, hre, hrg⟩ he (hold.symm.trans he)

private theorem helper_hstablePsi_495.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett generating) (_
        : CombinedStableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        base.closure (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) generating
        sigma) (alpha : Fin k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let X : Finset V := TreeSequenceVertexSet Tn;
    let Y : Finset V := TreeSequenceVertexSet base.closure;
    let U : Finset V := TreeSequenceVertexSet base.core;
    ∀ (_ : U = X ∪ Y) (c : Fin k),
    let psi : PartialEdgeColoring E k := OutsideTreeColorSwap base.core sigma alpha c;
    ∀ (_ : (
    ∀ (e : E) (_ : TreeIncidentEdge base.core e), psi e = sigma e)) (_ : (
    ∀ x ∈ U, MissingColors G psi x = MissingColors G sigma x)), CombinedStableColoring Tn
        base.closure (TashkinovStoredColors ett.series.data n) generating psi := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett base hstable alpha n Tn X Y U hU c psi
      fixed missingFixed
  constructor
  · constructor
    · intro e he hc'
      obtain ⟨x, hx, hxe⟩ := he
      have hxU : x ∈ U := by rw [hU]; exact Finset.mem_union_left _ hx
      exact (fixed e ⟨x, hxU, hxe⟩).trans
        (hstable.1.1 e ⟨x, hx, hxe⟩ hc')
    · intro x hx
      have hxU : x ∈ U := by rw [hU]; exact Finset.mem_union_left _ hx
      exact (missingFixed x hxU).trans (hstable.1.2 x hx)
  · constructor
    · intro e he hc'
      obtain ⟨x, hx, hxe⟩ := he
      have hxU : x ∈ U := by rw [hU]; exact Finset.mem_union_right _ hx
      exact (fixed e ⟨x, hxU, hxe⟩).trans
        (hstable.2.1 e ⟨x, hx, hxe⟩ hc')
    · intro x hx
      have hxU : x ∈ U := by rw [hU]; exact Finset.mem_union_right _ hx
      exact (missingFixed x hxU).trans (hstable.2.2 x hx)

private theorem helper_missingOutside_524.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett generating)
        (alpha beta : Fin k),
    let U : Finset V := TreeSequenceVertexSet base.core;
    ∀ (c : Fin k),
    let psi : PartialEdgeColoring E k := OutsideTreeColorSwap base.core sigma alpha c;
    ∀ (_ : (
    ∀ r ∉ U,
    ∀ (e : E), Incident G r e → (psi e = some c ↔ sigma e = some alpha) ∧ (psi e = some beta ↔
        sigma e = some beta))),
    ∀ r ∉ U, alpha ∈ MissingColors G sigma r ∨ beta ∈ MissingColors G sigma r → c ∈ MissingColors
        G psi r ∨ beta ∈ MissingColors G psi r := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett base alpha beta U c psi colorOutside r hr hm
  rcases hm with hm | hm
  · left
    have hn : ∀ e, Incident G r e → sigma e ≠ some alpha := by
      simpa [MissingColors, PresentColors] using hm
    have hn' : ∀ e, Incident G r e → psi e ≠ some c := by
      intro e he hd
      exact hn e he ((colorOutside r hr e he).1.mp hd)
    simpa [MissingColors, PresentColors] using hn'
  · right
    have hn : ∀ e, Incident G r e → sigma e ≠ some beta := by
      simpa [MissingColors, PresentColors] using hm
    have hn' : ∀ e, Incident G r e → psi e ≠ some beta := by
      intro e he hd
      exact hn e he ((colorOutside r hr e he).2.mp hd)
    simpa [MissingColors, PresentColors] using hn'

private theorem helper_equalRoot_593.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : MaximumProperty ett) (_ : (0 : ℕ) <
        ett.rounds) (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (_ :
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE) (base :
        HierarchyBase ett generating) (alpha beta : Fin k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let X : Finset V := TreeSequenceVertexSet Tn;
    let Y : Finset V := TreeSequenceVertexSet base.closure;
    let U : Finset V := TreeSequenceVertexSet base.core;
    ∀ (_ : ett.series.data.chosenVertex (Fin.last ett.rounds) = some ((ett.series.data.tree
        (Fin.last ett.rounds).castSucc).vertex base.supportPosition)) (_ : U = X ∪ Y) (gamma delta
        : Fin k) (_ : ett.series.data.gamma n = some gamma) (_ : ett.series.data.delta n = some
        delta) (c : Fin k) (_ : c ≠ beta) (_ : c ≠ delta),
    ∀ v ∈ TreeSequenceVertexSet Tn, v ∈ Y →
    let psi : PartialEdgeColoring E k := OutsideTreeColorSwap base.core sigma alpha c;
        IsProperEdgeColoring G psi → IsOneEdgeUncolored psi e0 → CombinedStableColoring Tn
        base.closure (TashkinovStoredColors ett.series.data n) generating psi →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G psi c beta; (
    ∀ (r : V), c ∈ MissingColors G psi r ∨ beta ∈ MissingColors G psi r → (H.neighborSet (Sum.inl
        r)).Subsingleton) → c ∈ TreeMissingColors psi Tn → TreeInterchangeable G base.closure psi
        c beta → (
    ∀ (r : V), Sum.inl r ∈ TwoColorComponent G psi c beta (Sum.inl r)) → TwoColorPathComponent G
        psi c beta (Sum.inl v) →
    ∀ (r s : V), s ∈ U → (beta = delta → s ∈ Y) → H.Reachable (Sum.inl r) (Sum.inl s) → c ∈
        MissingColors G psi r ∨ beta ∈ MissingColors G psi r → TwoColorComponent G psi c beta
        (Sum.inl r) = TwoColorComponent G psi c beta (Sum.inl v) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett hMP hpositive hlower hPE base alpha beta
      n Tn X Y U hchosen hU gamma delta hgamma hdelta c hcb hcd v hvX hvY psi hproperPsi honePsi
      hstablePsi H leaf hcX hinterY selfMem hvPath r s hs hsY hr hm
  have hrPath : TwoColorPathComponent G psi c beta (Sum.inl r) :=
    ⟨hcb, Sum.inl r, selfMem r, leaf r hm⟩
  have hsC : Sum.inl s ∈ TwoColorComponent G psi c beta (Sum.inl r) :=
    SimpleGraph.ConnectedComponent.eq.mpr hr.symm
  by_cases hbd : beta = delta
  · exact hinterY _ _ hrPath hvPath ⟨s, hsY hbd, hsC⟩
      ⟨v, hvY, selfMem v⟩
  · rw [hU] at hs
    rcases Finset.mem_union.mp hs with hsX | hsY'
    · have hinterX := InterchangePETreeAwayFromDelta G k e0 input T
        generating psi ett hMP hpositive hlower hPE base hproperPsi honePsi
        hstablePsi (Tn.vertex base.supportPosition) gamma delta c beta
        hchosen hgamma hdelta hcX hcd hbd
      exact hinterX _ _ hrPath hvPath ⟨s, hsX, hsC⟩
        ⟨v, hvX, selfMem v⟩
    · exact hinterY _ _ hrPath hvPath ⟨s, hsY', hsC⟩
        ⟨v, hvY, selfMem v⟩

private theorem helper_continuation_720.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : MaximumProperty ett) (_ : (0 : ℕ) <
        ett.rounds) (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (_ :
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE) (base :
        HierarchyBase ett generating) (_ : IsProperEdgeColoring G sigma) (alpha beta : Fin k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let X : Finset V := TreeSequenceVertexSet Tn;
    let Y : Finset V := TreeSequenceVertexSet base.closure;
    let U : Finset V := TreeSequenceVertexSet base.core;
    ∀ (_ : ett.series.data.chosenVertex (Fin.last ett.rounds) = some ((ett.series.data.tree
        (Fin.last ett.rounds).castSucc).vertex base.supportPosition)) (_ : U = X ∪ Y) (_ :
        TashkinovClosure generating (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ))))) (gamma delta : Fin k) (_ :
        ett.series.data.gamma n = some gamma) (_ : ett.series.data.delta n = some delta) (_ : (
    ∀ g ∈ BoundaryColorEdges G sigma X delta,
    ∃ w ∈ Y, Incident G w g)) (_ : alpha ≠ beta) (u1 s1 u2 s2 : V) (P1 : (TwoColorIncidenceGraph G
        sigma alpha beta).Walk (Sum.inl u1) (Sum.inl s1)) (P2 : (TwoColorIncidenceGraph G sigma
        alpha beta).Walk (Sum.inl u2) (Sum.inl s2)) (_ : TreeExitPath base.core sigma alpha beta
        u1 s1 P1) (_ : TreeExitPath base.core sigma alpha beta u2 s2 P2) (_ : u1 ≠ u2) (c : Fin k)
        (_ : c ≠ beta) (_ : c ≠ delta),
    ∀ v ∈ TreeSequenceVertexSet Tn, c ∈ MissingColors G sigma v →
    ∀ w ∈ TreeSequenceVertexSet base.closure, v ∈ Y →
    let psi : PartialEdgeColoring E k := OutsideTreeColorSwap base.core sigma alpha c; (
    ∀ (e : E), TreeIncidentEdge base.core e → psi e = sigma e) → (
    ∀ {e : E}, e ∈ BoundaryEdges G U → sigma e ≠ some alpha ∧ sigma e ≠ some c) →
        IsProperEdgeColoring G psi → IsOneEdgeUncolored psi e0 → (
    ∀ x ∈ U, MissingColors G psi x = MissingColors G sigma x) → CombinedStableColoring Tn
        base.closure (TashkinovStoredColors ett.series.data n) generating psi → (
    ∀ r ∉ U, alpha ∈ MissingColors G sigma r ∨ beta ∈ MissingColors G sigma r → c ∈ MissingColors
        G psi r ∨ beta ∈ MissingColors G psi r) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G psi c beta; (
    ∀ (r : V), c ∈ MissingColors G psi r ∨ beta ∈ MissingColors G psi r → (H.neighborSet (Sum.inl
        r)).Subsingleton) → False := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett hMP hpositive hlower hPE base hproper
      alpha beta n Tn X Y U hchosen hU _ gamma delta hgamma hdelta hdeltaBoundary hab u1 s1 u2 s2
      P1 P2 hP1 hP2 hu12 c hcb hcd v hvX hcv w hwY hvY psi fixed boundaryAvoid hproperPsi honePsi
      missingFixed hstablePsi missingOutside H leaf
  have transport (r : V) (hr : r ∉ U)
      (hmeet : ∃ x ∈ U,
        Sum.inl x ∈ TwoColorComponent G sigma alpha beta (Sum.inl r)) :
      ∃ s ∈ U, (beta = delta → s ∈ Y) ∧
        H.Reachable (Sum.inl r) (Sum.inl s) := by
    exact @helper_transport_460 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T generating sigma ett hpositive base hproper alpha beta hU delta hdeltaBoundary
        hab c hcb w hwY fixed boundaryAvoid r hr hmeet
  have oldMeet (u s : V)
      (P : (TwoColorIncidenceGraph G sigma alpha beta).Walk (Sum.inl u) (Sum.inl s))
      (hs : s ∈ U) :
      ∃ x ∈ U, Sum.inl x ∈ TwoColorComponent G sigma alpha beta (Sum.inl u) := by
    refine ⟨s, hs, ?_⟩
    exact SimpleGraph.ConnectedComponent.eq.mpr P.reachable.symm
  obtain ⟨t1, ht1, ht1Y, hr1⟩ := transport u1 hP1.2.2.1
    (oldMeet u1 s1 P1 hP1.2.2.2.1)
  obtain ⟨t2, ht2, ht2Y, hr2⟩ := transport u2 hP2.2.2.1
    (oldMeet u2 s2 P2 hP2.2.2.2.1)
  have hm1 := missingOutside u1 hP1.2.2.1 hP1.2.2.2.2.1
  have hm2 := missingOutside u2 hP2.2.2.1 hP2.2.2.2.2.1
  have hvU : v ∈ U := by rw [hU]; exact Finset.mem_union_left _ hvX
  have hcvPsi : c ∈ MissingColors G psi v := by
    rw [missingFixed v hvU]
    exact hcv
  have hcX : c ∈ TreeMissingColors psi Tn :=
    Finset.mem_biUnion.mpr ⟨v, hvX, hcvPsi⟩
  have hcY : c ∈ TreeMissingColors psi base.closure :=
    Finset.mem_biUnion.mpr ⟨v, hvY, hcvPsi⟩
  have hinterY := InterchangePEClosureConstituent G k e0 input T
    generating psi ett hMP hpositive hlower hPE base hproperPsi honePsi
    hstablePsi c beta hcY
  have selfMem (r : V) : Sum.inl r ∈ TwoColorComponent G psi c beta (Sum.inl r) :=
    SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Reachable.refl _)
  have hvPath : TwoColorPathComponent G psi c beta (Sum.inl v) :=
    ⟨hcb, Sum.inl v, selfMem v, leaf v (Or.inl hcvPsi)⟩
  have equalRoot (r s : V) (hs : s ∈ U)
      (hsY : beta = delta → s ∈ Y)
      (hr : H.Reachable (Sum.inl r) (Sum.inl s))
      (hm : c ∈ MissingColors G psi r ∨ beta ∈ MissingColors G psi r) :
      TwoColorComponent G psi c beta (Sum.inl r) =
        TwoColorComponent G psi c beta (Sum.inl v) := by
    exact @helper_equalRoot_593 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T generating sigma ett hMP hpositive hlower hPE base alpha beta hchosen hU gamma
        delta hgamma hdelta c hcb hcd v hvX hvY hproperPsi honePsi hstablePsi leaf hcX hinterY
        selfMem hvPath r s hs hsY hr hm
  have heq1 := equalRoot u1 t1 ht1 ht1Y hr1 hm1
  have heq2 := equalRoot u2 t2 ht2 ht2Y hr2 hm2
  obtain ⟨a, b, p, hp, hsupport⟩ :=
    TwoColorComponentSpanningPath G psi c beta hproperPsi (Sum.inl v)
  have endpoint (r : V)
      (hr : Sum.inl r ∈ TwoColorComponent G psi c beta (Sum.inl v))
      (hleaf : Set.Subsingleton (H.neighborSet (Sum.inl r))) :
      Sum.inl r = a ∨ Sum.inl r = b := by
    have hrp : Sum.inl r ∈ p.support := by
      change Sum.inl r ∈ {x | x ∈ p.support}
      rw [hsupport]
      exact hr
    by_contra hn
    push Not at hn
    exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet
      hn.1 hn.2 hleaf) hrp
  have hu1C : Sum.inl u1 ∈ TwoColorComponent G psi c beta (Sum.inl v) := by
    rw [← heq1]
    exact selfMem u1
  have hu2C : Sum.inl u2 ∈ TwoColorComponent G psi c beta (Sum.inl v) := by
    rw [← heq2]
    exact selfMem u2
  have end1 := endpoint u1 hu1C (leaf u1 hm1)
  have end2 := endpoint u2 hu2C (leaf u2 hm2)
  have endv := endpoint v (selfMem v) (leaf v (Or.inl hcvPsi))
  have hu1v : u1 ≠ v := by rintro rfl; exact hP1.2.2.1 hvU
  have hu2v : u2 ≠ v := by rintro rfl; exact hP2.2.2.1 hvU
  have hn12 : (Sum.inl u1 : Sum V E) ≠ Sum.inl u2 := by simpa using hu12
  have hn1v : (Sum.inl u1 : Sum V E) ≠ Sum.inl v := by simpa using hu1v
  have hn2v : (Sum.inl u2 : Sum V E) ≠ Sum.inl v := by simpa using hu2v
  rcases end1 with h1 | h1
  · rcases end2 with h2 | h2
    · exact hn12 (h1.trans h2.symm)
    · rcases endv with hv | hv
      · exact hn1v (h1.trans hv.symm)
      · exact hn2v (h2.trans hv.symm)
  · rcases end2 with h2 | h2
    · rcases endv with hv | hv
      · exact hn2v (h2.trans hv.symm)
      · exact hn1v (h1.trans hv.symm)
    · exact hn12 (h1.trans h2.symm)

private theorem helper_continuation_462.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : MaximumProperty ett) (_ : (0 : ℕ) <
        ett.rounds) (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (_ :
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE) (base :
        HierarchyBase ett generating) (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored
        sigma e0) (_ : CombinedStableColoring (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) base.closure (TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds)) generating sigma) (alpha beta : Fin k) (_ : TreeColorSetClosed G sigma
        base.core { alpha }),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let X : Finset V := TreeSequenceVertexSet Tn;
    let Y : Finset V := TreeSequenceVertexSet base.closure;
    let U : Finset V := TreeSequenceVertexSet base.core;
    ∀ (_ : ett.series.data.chosenVertex (Fin.last ett.rounds) = some ((ett.series.data.tree
        (Fin.last ett.rounds).castSucc).vertex base.supportPosition)) (_ : U = X ∪ Y) (_ :
        TashkinovClosure generating (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ))))) (_ : ColoredVertexSetElementary
        G sigma U) (gamma delta : Fin k) (_ : ett.series.data.gamma n = some gamma) (_ :
        ett.series.data.delta n = some delta) (_ : (
    ∀ g ∈ BoundaryColorEdges G sigma X delta,
    ∃ w ∈ Y, Incident G w g)) (_ : alpha ≠ beta) (u1 s1 u2 s2 : V) (P1 : (TwoColorIncidenceGraph G
        sigma alpha beta).Walk (Sum.inl u1) (Sum.inl s1)) (P2 : (TwoColorIncidenceGraph G sigma
        alpha beta).Walk (Sum.inl u2) (Sum.inl s2)) (_ : TreeExitPath base.core sigma alpha beta
        u1 s1 P1) (_ : TreeExitPath base.core sigma alpha beta u2 s2 P2) (_ : u1 ≠ u2) (_ : (4 :
        ℕ) ≤ (TreeMissingColors sigma Tn ∩ TreeMissingColors sigma base.closure).card), False := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett hMP hpositive hlower hPE base hproper
      hone hstable alpha beta hclosed n Tn X Y U hchosen hU _ helem gamma delta hgamma hdelta
      hdeltaBoundary hab u1 s1 u2 s2 P1 P2 hP1 hP2 hu12 hfour
  have hcolor : ∃ c ∈ TreeMissingColors sigma Tn ∩
      TreeMissingColors sigma base.closure,
      c ≠ alpha ∧ c ≠ beta ∧ c ≠ delta := by
    exact @helper_hcolor_383 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T generating sigma ett base alpha beta delta hfour
  obtain ⟨c, hc, hca, hcb, hcd⟩ := hcolor
  obtain ⟨v, hvX, hcv⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hc).1
  obtain ⟨w, hwY, hcw⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hc).2
  have hvY : v ∈ Y := by
    have hvU : v ∈ U := by rw [hU]; exact Finset.mem_union_left _ hvX
    have hwU : w ∈ U := by rw [hU]; exact Finset.mem_union_right _ hwY
    have hvw : v = w := by
      by_contra hvw
      exact (Finset.disjoint_left.mp (helem hvU hwU hvw)) hcv hcw
    exact hvw ▸ hwY
  have hcclosed := InterchangePECommonMissingClosed G k e0 input T
    generating sigma ett hMP hpositive hlower hPE base hproper hone hstable c
    (Finset.mem_inter.mp hc).1 (Finset.mem_inter.mp hc).2
  let psi := OutsideTreeColorSwap base.core sigma alpha c
  let flip := Equiv.swap (some alpha) (some c)
  have fixed (e : E) (he : TreeIncidentEdge base.core e) :
      psi e = sigma e := by
    simp [psi, OutsideTreeColorSwap, he]
  have boundaryOutside {r : V} {e : E} (hr : r ∉ U)
      (hre : Incident G r e) (he : TreeIncidentEdge base.core e) :
      e ∈ BoundaryEdges G U := by
    obtain ⟨x, hx, hxe⟩ := he
    have hxr : x ≠ r := by rintro rfl; exact hr hx
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hx, r, hr, (Sym2.mem_and_mem_iff hxr).mp ⟨hxe, hre⟩⟩
  have boundaryAvoid {e : E} (he : e ∈ BoundaryEdges G U) :
      sigma e ≠ some alpha ∧ sigma e ≠ some c := by
    constructor
    · intro ha
      have hm : e ∈ BoundaryColorEdges G sigma U alpha :=
        Finset.mem_filter.mpr ⟨he, ha⟩
      rw [hclosed alpha (Finset.mem_singleton_self _)] at hm
      exact Finset.notMem_empty e hm
    · intro hc'
      have hm : e ∈ BoundaryColorEdges G sigma U c :=
        Finset.mem_filter.mpr ⟨he, hc'⟩
      rw [hcclosed c (Finset.mem_singleton_self _)] at hm
      exact Finset.notMem_empty e hm
  have outside (r : V) (hr : r ∉ U) (e : E) (hre : Incident G r e) :
      psi e = flip (sigma e) := by
    by_cases he : TreeIncidentEdge base.core e
    · obtain ⟨ha, hc'⟩ := boundaryAvoid (boundaryOutside hr hre he)
      simp [fixed e he, flip, Equiv.swap_apply_def, ha, hc']
    · simp [psi, OutsideTreeColorSwap, he, flip, Equiv.swap_apply_def]
  have hproperPsi : IsProperEdgeColoring G psi := by
    exact @helper_hproperPsi_447 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T generating sigma ett base hproper alpha c fixed outside
  have hnone (e : E) : psi e = none ↔ sigma e = none := by
    by_cases he : TreeIncidentEdge base.core e
    · rw [fixed e he]
    · simp only [psi, OutsideTreeColorSwap, he, ite_false]
      by_cases ha : sigma e = some alpha
      · simp [ha]
      by_cases hc' : sigma e = some c
      · simp [hc', hca]
      · simp [ha, hc']
  have honePsi : IsOneEdgeUncolored psi e0 := by
    refine ⟨(hnone e0).mpr hone.1, ?_⟩
    intro e he
    obtain ⟨d, hd⟩ := hone.2 e he
    cases hpsi : psi e with
    | none =>
      have hn := (hnone e).mp hpsi
      rw [hd] at hn
      cases hn
    | some d' => exact ⟨d', rfl⟩
  have missingFixed (x : V) (hx : x ∈ U) :
      MissingColors G psi x = MissingColors G sigma x := by
    ext d
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    constructor
    · intro hn ⟨e, hxe, hed⟩
      exact hn ⟨e, hxe, (fixed e ⟨x, hx, hxe⟩).trans hed⟩
    · intro hn ⟨e, hxe, hed⟩
      exact hn ⟨e, hxe, (fixed e ⟨x, hx, hxe⟩).symm.trans hed⟩
  have hstablePsi : CombinedStableColoring Tn base.closure
      (TashkinovStoredColors ett.series.data n) generating psi := by
    exact @helper_hstablePsi_495 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T generating sigma ett base hstable alpha hU c fixed missingFixed
  have colorOutside (r : V) (hr : r ∉ U) (e : E) (hre : Incident G r e) :
      (psi e = some c ↔ sigma e = some alpha) ∧
      (psi e = some beta ↔ sigma e = some beta) := by
    rw [outside r hr e hre]
    by_cases ha : sigma e = some alpha <;>
      by_cases hc' : sigma e = some c <;>
      simp [flip, Equiv.swap_apply_def, ha, hc', hca, hca.symm,
        hcb, hab]
  have missingOutside (r : V) (hr : r ∉ U)
      (hm : alpha ∈ MissingColors G sigma r ∨ beta ∈ MissingColors G sigma r) :
      c ∈ MissingColors G psi r ∨ beta ∈ MissingColors G psi r := by
    exact @helper_missingOutside_524 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 input T generating sigma ett base alpha beta c colorOutside r hr hm
  let H := TwoColorIncidenceGraph G psi c beta
  have leaf (r : V)
      (hm : c ∈ MissingColors G psi r ∨ beta ∈ MissingColors G psi r) :
      Set.Subsingleton (H.neighborSet (Sum.inl r)) := by
    exact TwoColorMissingVertexNeighborsSubsingleton G psi hproperPsi c beta r hm
  -- Transport exact incidence segments; no old full component is reused after the swap.
  exact @helper_continuation_720 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating sigma ett hMP hpositive hlower hPE base hproper alpha beta hchosen hU
      (by assumption) gamma delta hgamma hdelta hdeltaBoundary hab u1 s1 u2 s2 P1 P2 hP1 hP2 hu12
      c hcb hcd v hvX hcv w hwY hvY fixed boundaryAvoid hproperPsi honePsi missingFixed
      hstablePsi missingOutside leaf
theorem InterchangePEClosedCore {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (base : HierarchyBase ett generating)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      generating sigma)
    (alpha beta : Fin k) :
    alpha ∈ TreeMissingColors sigma base.core →
      TreeColorSetClosed G sigma base.core {alpha} →
      TreeInterchangeable G base.core sigma alpha beta := by
  classical
  intro halpha hclosed
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let X := TreeSequenceVertexSet Tn
  let Y := TreeSequenceVertexSet base.closure
  let U := TreeSequenceVertexSet base.core
  obtain ⟨hchosen, hclosure, ⟨hunion⟩⟩ := base.parallel hPE
  have hU : U = X ∪ Y := hunion.vertexSet
  have hgen := ett.generatingColoring
  obtain ⟨hproperGen, honeGen, _⟩ := P2634_T1_PETerminalFacts ett hPE
  have hpreserved := CombinedStableClosurePreserved G k e0 input T
    generating generating sigma ett hpositive base hgen hPE
    hproperGen honeGen hproper hone hstable
  let baseSigma : HierarchyBase ett sigma := {
    core := base.core
    closure := base.closure
    supportPosition := base.supportPosition
    supportPositive := base.supportPositive
    terminalMissingColors := by
      dsimp
      ext c
      simp only [TreeMissingColors, Finset.mem_biUnion]
      constructor
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, by rw [← hstable.1.2 v hv]; exact hc⟩
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, by rw [hstable.1.2 v hv]; exact hc⟩
    parallel := fun hp => ⟨(base.parallel hp).1,
      hpreserved.2.2, (base.parallel hp).2.2⟩
    nonparallel := base.nonparallel }
  have helem : ColoredVertexSetElementary G sigma U :=
    ParallelClosureUnionElementary G k e0 input T generating ett hMP
      hpositive hlower hPE sigma hproper hone hstable.1 baseSigma
  have hdegree : MaximumDegree G + 1 ≤ k := by
    have htriple : KTriple G k e0 input := by
      cases ett.series.certified 0 with
      | initial => assumption
    exact htriple.2.2.1
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hq : q.succ = n := by
    apply Fin.ext
    simp [q, n]
    omega
  have hterminal : ∃ (gamma delta : Fin k) (f : E),
      ett.series.data.gamma n = some gamma ∧
      ett.series.data.delta n = some delta ∧
      ett.series.data.connectingEdges n = {f} ∧
      ett.series.data.stored n = {delta, gamma} := by
    exact @helper_hterminal_154 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett hpositive hPE hq
  obtain ⟨gamma, delta, f, hgamma, hdelta, hf, hstored⟩ := hterminal
  have hdeltaControl : delta ∈ TreeMissingColors generating Tn ∪
      TashkinovStoredColors ett.series.data n := by
    by_cases hm : delta ∈ TreeMissingColors generating Tn
    · exact Finset.mem_union_left _ hm
    · apply Finset.mem_union_right
      simp only [TashkinovStoredColors]
      rw [ite_eq_right (show n.val ≠ 0 by simp [n]; omega)]
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_biUnion.mpr ⟨n, Finset.mem_univ _, ?_⟩, ?_⟩
      · simp [hstored]
      · simpa [Tn, n, ← hgen] using hm
  let seed := TreeSequencePrefix Tn base.supportPosition.val
    base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt)
  have hseedY : TreeSequenceVertexSet seed ⊆ Y :=
    TreeSequenceInitialSegmentVertexSetSubset
      (TashkinovAugmentationSequenceInitialSegment generating seed base.closure
        hclosure.1)
  have hdeltaBoundary : ∀ g ∈ BoundaryColorEdges G sigma X delta,
      ∃ w ∈ Y, Incident G w g := by
    exact @helper_hdeltaBoundary_215 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 input T generating sigma ett hpositive hPE base hproper hone hstable hchosen hgen
        hproperGen honeGen hq gamma delta f hgamma hdelta hf hdeltaControl hseedY
  by_cases hab : alpha = beta
  · intro z w hz
    exact (hz.1 hab).elim
  change alpha ≠ beta at hab
  by_contra hnot
  obtain ⟨u1, s1, u2, s2, P1, P2, hP1, hP2, hdisjoint, hu12, hs12⟩ :=
    ElementaryClosedNoninterchangeableDisjointExitPaths G base.core sigma
      hproper helem alpha beta hab hclosed hnot
  have stableMissing {A : TreeSequence G e0} {C : Finset (Fin k)}
      {rho tau : PartialEdgeColoring E k} (hh : StableColoring A C rho tau) :
      TreeMissingColors tau A = TreeMissingColors rho A := by
    ext d
    simp only [TreeMissingColors, Finset.mem_biUnion]
    constructor
    · rintro ⟨x, hx, hd⟩
      exact ⟨x, hx, by rw [← hh.2 x hx]; exact hd⟩
    · rintro ⟨x, hx, hd⟩
      exact ⟨x, hx, by rw [hh.2 x hx]; exact hd⟩
  have missingGen (x : V) (hx : x ∈ U) :
      MissingColors G sigma x = MissingColors G generating x := by
    rw [hU] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hstable.1.2 x hx
    · exact hstable.2.2 x hx
  have helemGen : ColoredVertexSetElementary G generating U := by
    intro x hx y hy hxy
    rw [← missingGen x hx, ← missingGen y hy]
    exact helem hx hy hxy
  have hfour : 4 ≤ (TreeMissingColors sigma Tn ∩
      TreeMissingColors sigma base.closure).card := by
    rw [stableMissing hstable.1, stableMissing hstable.2]
    exact ParallelBaseFourCommonMissingColors ett base hPE
      hproperGen honeGen hdegree helemGen
  exact @helper_continuation_462 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating sigma ett hMP hpositive hlower hPE base hproper hone hstable alpha
      beta hclosed hchosen hU (by assumption) helem gamma delta hgamma hdelta hdeltaBoundary hab
      u1 s1 u2 s2 P1 P2 hP1 hP2 hu12 hfour
end GoldbergSeymour

end
