/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.Degree
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.LooplessMultigraph
public import LeanPool.GoldbergSeymour.MaximumDegree
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.PartialEdgeColoring
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Tree Missing Colors Card Lower Bound

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_present_le_without_root_106.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0),
    phi e0 = none →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) →
    let X : Finset V := TreeSequenceVertexSet T;
    let D : Finset V := (G.ends e0).toFinset;
    D ⊆ X →
    D.card = (2 : ℕ) →
    (∀ v ∈ D, Incident G v e0) →
    ∀ (v : V),
    Incident G v e0 →
    (PresentColors G phi v).card ≤ ({e : E | Incident G v e ∧ e ≠ e0} : Finset E).card := by
  classical
  intro V E _ _ G k e0 phi T hroot helem X D hDsub hDcard hDinc v he0
  let _ := Fintype.ofFinite V
  let target : Finset E := Finset.univ.filter (fun e => Incident G v e ∧ e ≠ e0)
  let chooseEdge : Fin k → E := fun c => if hc : c ∈ PresentColors G phi v then
    Classical.choose (show ∃ e, Incident G v e ∧ phi e = some c by
      simpa [PresentColors] using hc) else e0
  have choose_mem : ∀ c, c ∈ PresentColors G phi v → chooseEdge c ∈ target := by
    intro c hc
    have hw := Classical.choose_spec (show ∃ e, Incident G v e ∧ phi e = some c by
      simpa [PresentColors] using hc)
    have hne0 : Classical.choose (show ∃ e, Incident G v e ∧ phi e = some c by
        simpa [PresentColors] using hc) ≠ e0 := by
      intro he
      subst he
      rw [hroot] at hw
      simp at hw
    have hne : chooseEdge c ≠ e0 := by simpa [chooseEdge, hc] using hne0
    have hinc : Incident G v (chooseEdge c) := by simpa [chooseEdge, hc] using hw.1
    change chooseEdge c ∈ target
    simp [target, hinc, hne]
  have choose_eq : ∀ c, c ∈ PresentColors G phi v →
      phi (chooseEdge c) = some c := by
    intro c hc
    have hh := Classical.choose_spec (show ∃ e, Incident G v e ∧ phi e = some c by
      simpa [PresentColors] using hc)
    simpa [chooseEdge, dite_eq_left hc] using hh.2
  apply Finset.card_le_card_of_injOn chooseEdge
  · intro c hc
    exact choose_mem c hc
  · intro a ha b hb hab
    have ea := choose_eq a ha
    have eb := choose_eq b hb
    rw [hab] at ea
    exact Option.some.inj (ea.symm.trans eb)

private theorem helper_hmiss2_142.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k),
    MaximumDegree G + (1 : ℕ) ≤ k →
    (∀ (v : V), Degree G v ≤ MaximumDegree G) →
    (∀ (v : V),
        Incident G v e0 →
          (PresentColors G phi v).card ≤
            ({e : E | Incident G v e ∧ e ≠ e0} : Finset E).card) →
    ∀ (v : V),
    Incident G v e0 →
    (2 : ℕ) ≤ (MissingColors G phi v).card := by
  classical
  intro V E _ _ G k e0 phi hdegree hdeg present_le_without_root v hv
  have hcard : (Finset.univ.filter (fun e => Incident G v e ∧ e ≠ e0)).card
      ≤ Degree G v - 1 := by
    have he : e0 ∈ Finset.univ.filter (fun e => Incident G v e) := by simp [hv]
    have hc := Finset.card_erase_add_one he
    have hsub : (Finset.univ.filter (fun e => Incident G v e ∧ e ≠ e0)) =
        (Finset.univ.filter (fun e => Incident G v e)).erase e0 := by
      ext e
      simp [and_comm]
    rw [hsub]
    change ((Finset.univ.filter (fun e => Incident G v e)).erase e0).card ≤
      (Finset.univ.filter (fun e => Incident G v e)).card - 1
    omega
  have hp := (present_le_without_root v hv).trans hcard
  have hm : (MissingColors G phi v).card =
      k - (PresentColors G phi v).card := by
    simp [MissingColors, Finset.card_sdiff]
  rw [hm]
  have hdpos : 0 < Degree G v := by
    unfold Degree
    simp only [Finset.card_pos]
    exact ⟨e0, by simp [hv]⟩
  have hplt : (PresentColors G phi v).card < Degree G v :=
    (Nat.le_sub_one_iff_lt hdpos).mp hp
  have hdeg' : Degree G v + 1 <= MaximumDegree G + 1 :=
    Nat.add_le_add_right (hdeg v) 1
  have hpk' : (PresentColors G phi v).card + 2 <= Degree G v + 1 := by
    omega
  have hkm := le_trans hpk' (le_trans hdeg' hdegree)
  omega

private theorem helper_hinj_211.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0),
    let X : Finset V := TreeSequenceVertexSet T;
    let D : Finset V := (G.ends e0).toFinset;
    ∀ (hDsub : D ⊆ X),
    ((↑X : Set V).PairwiseDisjoint fun (v : V) ↦ MissingColors G phi v) →
    ∀ (hnonempty : ∀ v ∈ X, (MissingColors G phi v).Nonempty),
    let firstColor : (v : V) → v ∈ X → Fin k := fun (v : V) (hv : v ∈ X) ↦
      Classical.choose (hnonempty v hv);
    (∀ (v : V) (hv : v ∈ X), firstColor v hv ∈ MissingColors G phi v) →
    ∀
      (hsecond :
        ∀ (v : V) (hv : v ∈ D),
          ((MissingColors G phi v).erase (firstColor v (hDsub hv))).Nonempty),
    let extraColor : (v : V) → v ∈ D → Fin k := fun (v : V) (hv : v ∈ D) ↦
      Classical.choose (hsecond v hv);
    (∀ (v : V) (hv : v ∈ D),
        extraColor v hv ∈ (MissingColors G phi v).erase (firstColor v (hDsub hv))) →
    let domain : Type u_1 := ↥X ⊕ ↥D;
    let color : domain → Fin k := fun (p : domain) ↦
      match p with
      | Sum.inl v => firstColor (↑v : V) v.property
      | Sum.inr v => extraColor (↑v : V) v.property;
    Function.Injective color := by
  classical
  intro V E _ _ G k e0 phi T X D hDsub hdisj hnonempty firstColor firstMem hsecond extraColor
      extraMem domain color p q hpq
  let _ := Fintype.ofFinite V
  rcases p with p | p <;> rcases q with q | q
  · have hu : p.1 = q.1 := by
      by_contra hn
      have hd := hdisj p.2 q.2 hn
      have hpq' : firstColor p.1 p.2 = firstColor q.1 q.2 := by simpa [color] using hpq
      exact (Finset.disjoint_left.mp hd) (firstMem p.1 p.2)
        (by simpa only [hpq'] using firstMem q.1 q.2)
    cases Subtype.ext hu
    rfl
  · have hu : p.1 = q.1 := by
      by_contra hn
      have hd := hdisj p.2 (hDsub q.2) hn
      have hpq' : firstColor p.1 p.2 = extraColor q.1 q.2 := by simpa [color] using hpq
      exact (Finset.disjoint_left.mp hd) (firstMem p.1 p.2)
        (by simpa only [hpq'] using (Finset.mem_erase.mp (extraMem q.1 q.2)).2)
    have he := Finset.mem_erase.mp (extraMem q.1 q.2)
    exact False.elim (he.1 (by simpa [color, hu] using hpq.symm))
  · have hu : p.1 = q.1 := by
      by_contra hn
      have hd := hdisj (hDsub p.2) q.2 hn
      have hpq' : extraColor p.1 p.2 = firstColor q.1 q.2 := by simpa [color] using hpq
      exact (Finset.disjoint_left.mp hd) (Finset.mem_erase.mp (extraMem p.1 p.2)).2
        (by simpa only [hpq'] using firstMem q.1 q.2)
    have he := Finset.mem_erase.mp (extraMem p.1 p.2)
    exact False.elim (he.1 (by simpa [color, hu] using hpq))
  · have hu : p.1 = q.1 := by
      by_contra hn
      have hd := hdisj (hDsub p.2) (hDsub q.2) hn
      have hpq' : extraColor p.1 p.2 = extraColor q.1 q.2 := by simpa [color] using hpq
      exact (Finset.disjoint_left.mp hd) (Finset.mem_erase.mp (extraMem p.1 p.2)).2
        (by simpa only [hpq'] using (Finset.mem_erase.mp (extraMem q.1 q.2)).2)
    cases Subtype.ext hu
    rfl

theorem TreeMissingColorsCardLowerBound {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hroot : phi e0 = none)
    (hdegree : MaximumDegree G + 1 <= k)
    (helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T)) :
    (TreeSequenceVertexSet T).card + 2 <= (TreeMissingColors phi T).card := by
  classical
  let X := TreeSequenceVertexSet T
  let D := (G.ends e0).toFinset
  have hDsub : D ⊆ X := by
    intro v hv
    have hv' : v ∈ G.ends e0 := Sym2.mem_toFinset.mp hv
    rw [← T.first_edge] at hv'
    obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
    rw [hi, Sym2.mem_iff] at hv'
    rcases hv' with hv | hv <;> subst v <;>
      simp [X, TreeSequenceVertexSet]
  have hDcard : D.card = 2 := by
    have hn : Not (G.ends e0).IsDiag := by
      intro hd
      induction he : G.ends e0 using Sym2.inductionOn with
      | _ a b =>
        rw [he] at hd
        rw [Sym2.mk_isDiag_iff] at hd
        apply G.loopless e0 a
        rw [he, hd]
    exact Sym2.card_toFinset_of_not_isDiag _ hn
  have hDinc : ∀ v ∈ D, Incident G v e0 := by
    intro v hv
    exact Sym2.mem_toFinset.mp hv
  have hdeg : ∀ v : V, Degree G v ≤ MaximumDegree G := by
    intro v
    unfold MaximumDegree
    exact Finset.le_max' _ _ (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_image.mpr ⟨v, by simp⟩)))
  have present_le_degree : ∀ v : V,
      (PresentColors G phi v).card ≤ Degree G v := by
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
  have hmiss1 : ∀ v : V, 1 ≤ (MissingColors G phi v).card := by
    intro v
    have hp := present_le_degree v
    have hm : (MissingColors G phi v).card =
        k - (PresentColors G phi v).card := by
      simp [MissingColors, Finset.card_sdiff]
    have hpmax := hp.trans (hdeg v)
    rw [hm]
    omega
  have present_le_without_root := @helper_present_le_without_root_106 (@V) (@E) inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@hroot) (@helem) (@hDsub) (@hDcard) (@hDinc)
  have hmiss2 := @helper_hmiss2_142 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi)
      (@hdegree) (@hdeg) (@present_le_without_root)
  have hdisj : (X : Set V).PairwiseDisjoint (fun v => MissingColors G phi v) := by
    intro u hu v hv huv
    exact helem hu hv huv
  have hnonempty : ∀ v ∈ X, (MissingColors G phi v).Nonempty := by
    intro v hv
    exact Finset.card_pos.mp (by have := hmiss1 v; omega)
  let firstColor : (v : V) → v ∈ X → Fin k := fun v hv =>
    Classical.choose (hnonempty v hv)
  have firstMem : ∀ (v : V) (hv : v ∈ X),
      firstColor v hv ∈ MissingColors G phi v := by
    intro v hv
    exact Classical.choose_spec (hnonempty v hv)
  have hsecond : ∀ (v : V) (hv : v ∈ D),
      ((MissingColors G phi v).erase (firstColor v (hDsub hv))).Nonempty := by
    intro v hv
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (firstMem v (hDsub hv))]
    have hh := hmiss2 v (hDinc v hv)
    omega
  let extraColor : (v : V) → v ∈ D → Fin k := fun v hv =>
    Classical.choose (hsecond v hv)
  have extraMem : ∀ (v : V) (hv : v ∈ D),
      extraColor v hv ∈ (MissingColors G phi v).erase
        (firstColor v (hDsub hv)) := by
    intro v hv
    exact Classical.choose_spec (hsecond v hv)
  let domain := Sum {v : V // v ∈ X} {v : V // v ∈ D}
  let color : domain → Fin k := fun p => match p with
    | Sum.inl v => firstColor v.1 v.2
    | Sum.inr v => extraColor v.1 v.2
  have hmap : ∀ p : domain, color p ∈ TreeMissingColors phi T := by
    intro p
    rcases p with p | p
    · apply Finset.mem_biUnion.mpr
      exact ⟨p.1, p.2, firstMem p.1 p.2⟩
    · apply Finset.mem_biUnion.mpr
      exact ⟨p.1, hDsub p.2, (Finset.mem_erase.mp (extraMem p.1 p.2)).2⟩
  have hinj := @helper_hinj_211 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi) (@T)
      (@hDsub) (@hdisj) (@hnonempty) (@firstMem) (@hsecond) (@extraMem)
  let A : Finset domain :=
    X.attach.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
      D.attach.map ⟨Sum.inr, Sum.inr_injective⟩
  have hAdisj : Disjoint
      (X.attach.map ⟨Sum.inl, Sum.inl_injective⟩)
      (D.attach.map ⟨Sum.inr, Sum.inr_injective⟩) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rw [Finset.mem_map] at hz1 hz2
    rcases hz1 with ⟨u, hu, rfl⟩
    rcases hz2 with ⟨v, hv, h⟩
    cases h
  have hAc : A.card = X.card + 2 := by
    dsimp [A]
    rw [Finset.card_union_of_disjoint hAdisj]
    simp [hDcard]
  have hle : A.card ≤ (TreeMissingColors phi T).card := by
    apply Finset.card_le_card_of_injOn color
    · intro p hp
      exact hmap p
    · exact hinj.injOn
  simpa [X, hAc] using hle

end GoldbergSeymour

end
