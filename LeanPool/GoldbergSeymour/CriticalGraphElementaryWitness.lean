/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.ColoredVertexSetStronglyClosed
public import LeanPool.GoldbergSeymour.Critical
public import LeanPool.GoldbergSeymour.Elementary
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.MaximumDegree
public import LeanPool.GoldbergSeymour.StronglyClosedWitnessElementary

/-!
# egraph2

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private theorem helper_p_to_q_85.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ), Critical G → ChromaticIndex G = k + (1 : ℕ) →
    let P : Prop :=
    ∀ (e0 : E) (phi : PartialEdgeColoring E k), IsProperEdgeColoring G phi → IsOneEdgeUncolored
        phi e0 → ColoredVertexSetElementary G phi Finset.univ;
    let Q : Prop :=
    ∃ (e0 : E) (phi : PartialEdgeColoring E k), IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored
        phi e0 ∧ ColoredVertexSetElementary G phi Finset.univ; P → Q := by
  classical
  intro V E _ _ _ G k hcritical hindex P Q hp
  have hedge : ∃ e : E, True := by
    by_contra hn
    have he : IsFullEdgeColoring (fun _ : E => (none : Option (Fin 0))) := by
      intro e
      exact False.elim (hn ⟨e, trivial⟩)
    have hcol : HasKEdgeColoring G 0 := by
      refine ⟨fun _ => none, ?_, he⟩
      intro e f c hne hadj hce
      simp at hce
    have hz : ChromaticIndex G ≤ 0 := (ChromaticIndexSpec G).2 0 hcol
    omega
  obtain ⟨e0, _⟩ := hedge
  have hdel := hcritical e0
  have hle : ChromaticIndex (DeleteEdge G e0) ≤ k := by
    have ht : ChromaticIndex (DeleteEdge G e0) < k + 1 := by
      simpa [hindex] using hdel
    omega
  obtain ⟨psi, hpp, hfull⟩ := (ChromaticIndexSpec (DeleteEdge G e0)).1
  let phi : PartialEdgeColoring E k := fun e =>
    if he : e = e0 then none else
      some (Fin.castLE hle (Classical.choose (hfull ⟨e, by simp [he]⟩)))
  have hproper : IsProperEdgeColoring G phi := by
    intro e f c hef hadj hce
    by_cases he : e = e0
    · simp [phi, he] at hce
    · by_cases hf : f = e0
      · simp [phi, hf]
      · have hce' : Fin.castLE hle (Classical.choose (hfull ⟨e, by simp [he]⟩)) = c := by
          have hc := Classical.choose_spec (hfull ⟨e, by simp [he]⟩)
          have := Option.some.inj (show
            some (Fin.castLE hle (Classical.choose (hfull ⟨e, by simp [he]⟩))) = some c by
            simpa [phi, he] using hce)
          exact this
        have hpf := hpp (show (⟨e, by simp [he]⟩ : {e // e ∈ Finset.univ.erase e0}) ≠
            ⟨f, by simp [hf]⟩ by simpa using hef)
          (by simpa [AdjacentEdges, Incident, DeleteEdge, RestrictEdges] using hadj)
          (by simpa using Classical.choose_spec (hfull ⟨e, by simp [he]⟩))
        intro hbad
        apply hpf
        have hbad' := Option.some.inj (show
          some (Fin.castLE hle (Classical.choose (hfull ⟨f, by simp [hf]⟩))) = some c by
          simpa [phi, hf] using hbad)
        have hsame : Classical.choose (hfull ⟨f, by simp [hf]⟩) =
            Classical.choose (hfull ⟨e, by simp [he]⟩) := by
          apply Fin.ext
          exact (congrArg Fin.val hbad').trans (congrArg Fin.val hce').symm
        rw [← hsame]
        exact Classical.choose_spec (hfull ⟨f, by simp [hf]⟩)
  have ho : IsOneEdgeUncolored phi e0 := by
    constructor
    · simp [phi]
    · intro e he
      refine ⟨Fin.castLE hle (Classical.choose (hfull ⟨e, by simp [he]⟩)), ?_⟩
      simp [phi, he]
  exact ⟨e0, phi, hproper, ho, hp e0 phi hproper ho⟩

private theorem helper_continuation_315.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k),
        IsProperEdgeColoring G phi →
    ∀ (U : Finset V), EligibleOddSet U → (
    ∀ (e : E), (G.ends e).toFinset.card = (2 : ℕ)) → U = Finset.univ → (
    ∀ (c : Fin k), (2 : ℕ) * ({e ∈ Finset.univ.erase e0 | phi e = some c} : Finset E).card =
        U.card - (1 : ℕ)) → ColoredVertexSetElementary G phi Finset.univ := by
  classical
  intro V E _ _ _ G k e0 phi hp U hElig endpoint_card hUall hclass
  unfold ColoredVertexSetElementary
  intro u hu v hv hne
  by_contra hdis
  rw [Finset.not_disjoint_iff] at hdis
  obtain ⟨c, hcu, hcv⟩ := hdis
  have hcu' : c ∉ PresentColors G phi u := by
    exact (Finset.mem_sdiff.mp hcu).2
  have hcv' : c ∉ PresentColors G phi v := by
    exact (Finset.mem_sdiff.mp hcv).2
  let edges := (Finset.univ.erase e0).filter (fun e => phi e = some c)
  have edge_disjoint : ∀ ⦃e⦄, e ∈ edges → ∀ ⦃f⦄, f ∈ edges →
      e ≠ f → Disjoint (G.ends e).toFinset (G.ends f).toFinset := by
    intro e hee f hef hne'
    rw [Finset.disjoint_left]
    intro z hze hzf
    have hce := (Finset.mem_filter.mp hee).2
    have hcf := (Finset.mem_filter.mp hef).2
    exact hp hne' ⟨z, Sym2.mem_toFinset.mp hze, Sym2.mem_toFinset.mp hzf⟩ hce hcf
  have union_card : (edges.biUnion fun e => (G.ends e).toFinset).card =
      2 * edges.card := by
    have aux : ∀ s : Finset E, s ⊆ edges →
        (s.biUnion fun e => (G.ends e).toFinset).card = 2 * s.card := by
      intro s hs
      induction s using Finset.induction_on with
      | empty => simp
      | @insert e s hes ih =>
          rw [Finset.biUnion_insert]
          have hd : Disjoint (G.ends e).toFinset
              (s.biUnion fun f => (G.ends f).toFinset) := by
            rw [Finset.disjoint_left]
            intro z hze hzs
            obtain ⟨f, hf, hzf⟩ := Finset.mem_biUnion.mp hzs
            have hh := edge_disjoint (hs (Finset.mem_insert_self e s))
              (hs (Finset.mem_insert_of_mem hf)) (by
                intro heq'
                exact hes (by simpa [heq'] using hf))
            exact (Finset.disjoint_left.mp hh) hze hzf
          rw [Finset.card_union_of_disjoint hd, endpoint_card]
          rw [ih (fun x hx => hs (Finset.mem_insert_of_mem hx))]
          rw [Finset.card_insert_of_notMem hes]
          omega
    exact aux edges (by intro e hee; exact hee)
  have union_subset : edges.biUnion (fun e => (G.ends e).toFinset) ⊆
      (Finset.univ.erase u).erase v := by
    intro z hz
    obtain ⟨e, hee, hze⟩ := Finset.mem_biUnion.mp hz
    have hce := (Finset.mem_filter.mp hee).2
    have hzu : z ≠ u := by
      intro hzu
      apply hcu'
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      have hzinc : Incident G z e := Sym2.mem_toFinset.mp hze
      rw [hzu] at hzinc
      exact ⟨e, hzinc, hce⟩
    have hzv : z ≠ v := by
      intro hzv
      apply hcv'
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      have hzinc : Incident G z e := Sym2.mem_toFinset.mp hze
      rw [hzv] at hzinc
      exact ⟨e, hzinc, hce⟩
    simp [hzu, hzv]
  have hcard : 2 * edges.card ≤ U.card - 2 := by
    have := Finset.card_le_card union_subset
    have hcardUV : ((Finset.univ.erase u).erase v).card = Fintype.card V - 2 := by
      have hu' : (Finset.univ : Finset V).card - 1 =
          (Finset.univ.erase u).card := by
        symm
        exact Finset.card_erase_of_mem (by simp)
      have hv' : v ∈ (Finset.univ.erase u : Finset V) :=
        Finset.mem_erase.mpr ⟨hne.symm, by simp⟩
      rw [Finset.card_erase_of_mem hv', ← hu']
      have hlarge : 3 ≤ Fintype.card V := by
        simpa [hUall] using hElig.1
      simp
      omega
    calc
      2 * edges.card = (edges.biUnion fun e => (G.ends e).toFinset).card := union_card.symm
      _ ≤ ((Finset.univ.erase u).erase v).card := this
      _ = U.card - 2 := by rw [hcardUV, hUall]; simp
  have hceq := hclass c
  dsimp [edges] at hceq hcard
  have hlarge : 3 ≤ U.card := hElig.1
  omega

private theorem helper_continuation_337.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ),
        MaximumDegree G + (1 : ℕ) ≤ k → (
    ∀ (v : V),
    ∃ (e : E), Incident G v e) → Elementary G →
    ∀ (e0 : E) (phi : PartialEdgeColoring E k), IsProperEdgeColoring G phi → IsOneEdgeUncolored
        phi e0 →
    ∀ U ∈ ({U ∈ Finset.univ.powerset | EligibleOddSet U} : Finset (Finset V)), DensityValue G U =
        Density G → (↑k : ℚ) < DensityValue G U → EligibleOddSet U → (
    ∀ (e : E), (G.ends e).toFinset.card = (2 : ℕ)) → (
    ∀ (qphi : PartialEdgeColoring E k), IsProperEdgeColoring G qphi →
    ∀ (W : Finset V), EligibleOddSet W →
    ∀ (c : Fin k), (2 : ℕ) * ({e ∈ InternalEdges G W | qphi e = some c} : Finset E).card ≤ W.card
        - (1 : ℕ)) → (
    ∀ S ⊆ InternalEdges G U,
    ∀ (qphi : PartialEdgeColoring E k), IsProperEdgeColoring G qphi → (
    ∀ e ∈ S,
    ∃ (c : Fin k), qphi e = some c) → (2 : ℕ) * S.card ≤ k * (U.card - (1 : ℕ))) → (
    ∀ (f : E), f ∈ InternalEdges G U) → ColoredVertexSetElementary G phi Finset.univ := by
  classical
  intro V E _ _ G k hdegree hnoisolated he e0 phi hp ho U hU hEq hvalue hElig endpoint_card
      matching_card total_card edge_internal
  have hUall : U = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    obtain ⟨e, he⟩ := hnoisolated v
    have hi := edge_internal e
    have hi' : ∀ z, Incident G z e → z ∈ U := by
      simpa [InternalEdges] using hi
    exact hi' v he
  have hInternal : InternalEdges G U = (Finset.univ : Finset E) := by
    ext e
    simp [InternalEdges, hUall]
  have hSsub : (Finset.univ.erase e0 : Finset E) ⊆ InternalEdges G U := by
    intro e he
    rw [hInternal]
    simp
  have hfullS : ∀ e, e ∈ (Finset.univ.erase e0 : Finset E) →
      ∃ c, phi e = some c := by
    intro e he
    exact ho.2 e (Finset.mem_erase.mp he).1
  have hb := total_card (Finset.univ.erase e0) hSsub phi hp hfullS
  have hstrictQ : (k : ℚ) * ((U.card : ℚ) - 1) <
      2 * (Finset.univ : Finset E).card := by
    change (k : ℚ) < (2 * (InternalEdges G U).card : ℚ) /
        ((U.card : ℚ) - 1) at hvalue
    have hn : (0 : ℚ) < (U.card : ℚ) - 1 := by
      have ht := hElig.1
      exact sub_pos.mpr (by exact_mod_cast (show 1 < U.card by omega))
    apply (lt_div_iff₀ hn).1 at hvalue
    rw [hInternal] at hvalue
    exact hvalue
  have hstrict : k * (U.card - 1) < 2 * (Finset.univ : Finset E).card := by
    have hcast : (↑(U.card - 1) : ℚ) = (U.card : ℚ) - 1 := by
      have hU3 : 3 ≤ U.card := hElig.1
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hq : (k : ℚ) * (↑(U.card - 1) : ℚ) <
        2 * (Finset.univ : Finset E).card := by
      rw [hcast]
      exact hstrictQ
    exact_mod_cast hq
  have heq : 2 * (Finset.univ : Finset E).card - 2 = k * (U.card - 1) := by
    have hs := hElig.2
    obtain ⟨t, ht⟩ := hs
    have hc := (show (Finset.univ.erase e0 : Finset E).card =
        (Finset.univ : Finset E).card - 1 by simp)
    rw [hc] at hb
    have hprod : 2 ∣ k * (U.card - 1) := by
      refine ⟨k * t, ?_⟩
      rw [ht]
      simp [Nat.mul_assoc, Nat.mul_comm]
    omega
  have hclass :
    ∀ c : Fin k, 2 * ((Finset.univ.erase e0).filter (fun e => phi e = some c)).card = U.card - 1
  := by
    intro c
    have hm := matching_card phi hp U hElig c
    have hle : 2 * ((Finset.univ.erase e0).filter
        (fun e => phi e = some c)).card ≤ U.card - 1 := by
      have hsub : (Finset.univ.erase e0).filter (fun e => phi e = some c) =
          (InternalEdges G U).filter (fun e => phi e = some c) := by
        ext e
        by_cases he : e = e0
        · simp [he, ho.1]
        · simp [hInternal, he]
      rw [hsub]
      exact hm
    have recurrenceColors : ∀ T : Finset (Fin k),
        2 * ((Finset.univ.erase e0).filter (fun e => ∃ d ∈ T,
          phi e = some d)).card ≤ T.card * (U.card - 1) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp
      | @insert d T hdt ih =>
        let old := (Finset.univ.erase e0).filter (fun e => ∃ c ∈ T, phi e = some c)
        let fresh := (Finset.univ.erase e0).filter (fun e => phi e = some d)
        have split : (Finset.univ.erase e0).filter (fun e => ∃ c ∈ insert d T,
            phi e = some c) = old ∪ fresh := by
          ext e
          simp only [old, fresh, Finset.mem_union, Finset.mem_filter, Finset.mem_insert]
          aesop
        have disj : Disjoint old fresh := by
          rw [Finset.disjoint_left]
          intro e he ho
          have h1 := (Finset.mem_filter.mp he).2
          have h2 := (Finset.mem_filter.mp ho).2
          obtain ⟨c, hc, hce⟩ := h1
          have : c = d := by
            apply Option.some.inj
            exact hce.symm.trans h2
          exact hdt (this ▸ hc)
        rw [split, Finset.card_union_of_disjoint disj]
        have hdcard := matching_card phi hp U hElig d
        have hfresh : 2 * fresh.card ≤ U.card - 1 := by
          have hsubD : fresh = (InternalEdges G U).filter
              (fun e => phi e = some d) := by
            ext e
            by_cases he : e = e0
            · simp [fresh, he, ho.1]
            · simp [fresh, hInternal, he]
          rw [hsubD]
          exact hdcard
        dsimp [old, fresh] at ih ⊢
        calc
          2 * ((old.card) + fresh.card) = 2 * old.card + 2 * fresh.card := by omega
          _ ≤ T.card * (U.card - 1) + (U.card - 1) := Nat.add_le_add ih hfresh
          _ = (insert d T).card * (U.card - 1) := by
            rw [Finset.card_insert_of_notMem hdt]
            simp [Nat.add_mul, Nat.add_comm]
    have hother := recurrenceColors (Finset.univ.erase c : Finset (Fin k))
    have hpartition : (Finset.univ.erase e0 : Finset E) =
        ((Finset.univ.erase e0).filter (fun e => phi e = some c)) ∪
          ((Finset.univ.erase e0).filter (fun e => ∃ d ∈ Finset.univ.erase c,
            phi e = some d)) := by
      ext e
      by_cases he : e ∈ (Finset.univ.erase e0 : Finset E)
      · obtain ⟨d, hd⟩ := hfullS e he
        by_cases hdc : d = c
        · simp only [Finset.mem_union, Finset.mem_filter]
          constructor
          · intro _
            exact Or.inl ⟨he, by simpa [hdc] using hd⟩
          · intro _
            exact he
        · simp only [Finset.mem_union, Finset.mem_filter]
          constructor
          · intro _
            exact Or.inr ⟨he, d, Finset.mem_erase.mpr ⟨hdc, by simp⟩, hd⟩
          · intro _
            exact he
      · simp [he]
    have hsumcard : 2 * (Finset.univ.erase e0 : Finset E).card =
        k * (U.card - 1) := by
      have hc' : (Finset.univ.erase e0 : Finset E).card =
          (Finset.univ : Finset E).card - 1 := by simp
      rw [hc']
      omega
    have hleOther : 2 * ((Finset.univ.erase e0).filter (fun e => ∃ d ∈
        Finset.univ.erase c, phi e = some d)).card ≤
        (k - 1) * (U.card - 1) := by
      simpa using hother
    have hclass' : 2 * ((Finset.univ.erase e0).filter
        (fun e => phi e = some c)).card = U.card - 1 := by
      rw [hpartition] at hsumcard
      have hdj : Disjoint ((Finset.univ.erase e0).filter (fun e => phi e = some c))
          ((Finset.univ.erase e0).filter (fun e => ∃ d ∈ Finset.univ.erase c,
            phi e = some d)) := by
        rw [Finset.disjoint_left]
        intro e he ho
        obtain ⟨d, hd, hde⟩ := (Finset.mem_filter.mp ho).2
        have hcd : c = d := by
          apply Option.some.inj
          exact ((Finset.mem_filter.mp he).2).symm.trans hde
        exact (Finset.mem_erase.mp hd).1 hcd.symm
      rw [Finset.card_union_of_disjoint hdj] at hsumcard
      have hm' := matching_card phi hp U hElig c
      have hrel : k * (U.card - 1) =
          (k - 1) * (U.card - 1) + (U.card - 1) := by
        calc
          k * (U.card - 1) = (k - 1 + 1) * (U.card - 1) := by
            rw [Nat.sub_add_cancel (by omega)]
          _ = (k - 1) * (U.card - 1) + (U.card - 1) := by
            rw [Nat.add_mul]
            simp
      rw [hrel] at hsumcard
      simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true, Nat.mul_add] at hsumcard
      have hsum' : 2 * ((Finset.univ.erase e0).filter
            (fun e => phi e = some c)).card +
          2 * ((Finset.univ.erase e0).filter (fun e => ∃ d ∈
            Finset.univ.erase c, phi e = some d)).card =
          (k - 1) * (U.card - 1) + (U.card - 1) := by
        simpa [Nat.mul_add] using hsumcard
      omega
    exact hclass'
  exact @helper_continuation_315 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@hp) (@U) (@hElig) (@endpoint_card) (@hUall) (@hclass)
private theorem helper_matching_card_458.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ),
        (
    ∀ (e : E), (G.ends e).toFinset.card = (2 : ℕ)) →
    ∀ (qphi : PartialEdgeColoring E k), IsProperEdgeColoring G qphi →
    ∀ (W : Finset V), EligibleOddSet W →
    ∀ (c : Fin k), (2 : ℕ) * ({e ∈ InternalEdges G W | qphi e = some c} : Finset E).card ≤ W.card
        - (1 : ℕ) := by
  classical
  intro V E _ _ G k endpoint_card qphi hq W hW c
  let edges := (InternalEdges G W).filter fun e => qphi e = some c
  have disjoint_endpoints : ∀ ⦃e⦄, e ∈ edges → ∀ ⦃f⦄, f ∈ edges →
      e ≠ f → Disjoint (G.ends e).toFinset (G.ends f).toFinset := by
    intro e hee f hef hne
    rw [Finset.disjoint_left]
    intro v hev hvf
    have hce := (Finset.mem_filter.mp hee).2
    have hcf := (Finset.mem_filter.mp hef).2
    have hadj : AdjacentEdges G e f :=
      ⟨v, (Sym2.mem_toFinset.mp hev), (Sym2.mem_toFinset.mp hvf)⟩
    have hbad := hq hne hadj hce
    exact hbad hcf
  have union_card_for : ∀ s : Finset E, s ⊆ edges →
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
        have hde := disjoint_endpoints (hs (Finset.mem_insert_self e s))
          (hs (Finset.mem_insert_of_mem hf)) (by
            intro h
            exact hes (by simpa [h] using hf))
        exact (Finset.disjoint_left.mp hde) hev hvf
      rw [Finset.card_union_of_disjoint hd, endpoint_card]
      calc
        2 + (s.biUnion fun e => (G.ends e).toFinset).card = 2 + 2 * s.card := by
          rw [ih (fun x hx => hs (Finset.mem_insert_of_mem hx))]
        _ = 2 * (insert e s).card := by
          rw [Finset.card_insert_of_notMem hes]
          omega
  have union_card := union_card_for edges (by intro e hee; exact hee)
  have union_subset : edges.biUnion (fun e => (G.ends e).toFinset) ⊆ W := by
    intro v hv
    obtain ⟨e, hee, hev⟩ := Finset.mem_biUnion.mp hv
    have heI := (Finset.mem_filter.mp hee).1
    have heI' : ∀ z, Incident G z e → z ∈ W := by
      simpa [InternalEdges] using heI
    exact heI' v (Sym2.mem_toFinset.mp hev)
  have hcard : 2 * edges.card ≤ W.card := by
    rw [← union_card]
    exact Finset.card_le_card union_subset
  have hstrict : 2 * edges.card < W.card := by
    apply Nat.lt_of_le_of_ne hcard
    intro heq
    apply hW.2.not_two_dvd_nat
    refine ⟨edges.card, ?_⟩
    omega
  dsimp [edges] at hstrict ⊢
  omega

private theorem helper_total_card_517.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ),
        Elementary G →
    ∀ (U : Finset V), EligibleOddSet U → (
    ∀ (qphi : PartialEdgeColoring E k), IsProperEdgeColoring G qphi →
    ∀ (W : Finset V), EligibleOddSet W →
    ∀ (c : Fin k), (2 : ℕ) * ({e ∈ InternalEdges G W | qphi e = some c} : Finset E).card ≤ W.card
        - (1 : ℕ)) →
    ∀ S ⊆ InternalEdges G U,
    ∀ (qphi : PartialEdgeColoring E k), IsProperEdgeColoring G qphi → (
    ∀ e ∈ S,
    ∃ (c : Fin k), qphi e = some c) → (2 : ℕ) * S.card ≤ k * (U.card - (1 : ℕ)) := by
  classical
  intro V E _ _ G k he U hElig matching_card S hS qphi hq hfullU
  let colored := fun s : Finset (Fin k) =>
    S.filter (fun e => ∃ c ∈ s, qphi e = some c)
  have recurrence : ∀ s : Finset (Fin k),
      2 * (colored s).card ≤ s.card * (U.card - 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [colored]
    | @insert c s hcs ih =>
        let old := colored s
        let fresh := S.filter (fun e => qphi e = some c)
        have split : colored (insert c s) = old ∪ fresh := by
          ext e
          simp only [colored, old, fresh, Finset.mem_union, Finset.mem_filter,
            Finset.mem_insert]
          aesop
        have disj : Disjoint old fresh := by
          rw [Finset.disjoint_left]
          intro e hee hef
          have hs' := (Finset.mem_filter.mp hee).2
          have hc' := (Finset.mem_filter.mp hef).2
          obtain ⟨d, hd, hde⟩ := hs'
          have hsame : d = c := by
            have : some d = some c := hde.symm.trans hc'
            simpa using this
          exact hcs (hsame ▸ hd)
        rw [split, Finset.card_union_of_disjoint disj]
        have hm0 := matching_card qphi hq U hElig c
        have hsubfresh : fresh ⊆
            (InternalEdges G U).filter (fun e => qphi e = some c) := by
          intro e hee
          have hee' : e ∈ S ∧ qphi e = some c := by simpa [fresh] using hee
          exact Finset.mem_filter.mpr ⟨hS hee'.1, hee'.2⟩
        have hm : 2 * fresh.card ≤ U.card - 1 := by
          have hh := Finset.card_le_card hsubfresh
          omega
        dsimp [old, fresh] at ih ⊢
        calc
          2 * ((colored s).card + fresh.card) =
              2 * (colored s).card + 2 * fresh.card := by omega
          _ ≤ s.card * (U.card - 1) + (U.card - 1) :=
            Nat.add_le_add ih hm
          _ = (insert c s).card * (U.card - 1) := by
            rw [Finset.card_insert_of_notMem hcs]
            simp [Nat.add_mul, Nat.add_comm]
  have hall : colored (Finset.univ : Finset (Fin k)) = S := by
    ext e
    simp only [colored, Finset.mem_filter]
    constructor
    · rintro ⟨he, h⟩
      exact he
    · intro hee
      obtain ⟨c, hc⟩ := hfullU e hee
      exact ⟨hee, ⟨c, Finset.mem_univ c, hc⟩⟩
  rw [← hall]
  simpa using (recurrence (Finset.univ : Finset (Fin k)))

private theorem helper_edge_internal_577.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ), Critical G → ChromaticIndex G = k + (1 : ℕ) → Elementary
        G → (↑k : ℚ) < Density G →
    ∀ (U : Finset V), DensityValue G U = Density G → (↑k : ℚ) < DensityValue G U → EligibleOddSet
        U → (
    ∀ S ⊆ InternalEdges G U,
    ∀ (qphi : PartialEdgeColoring E k), IsProperEdgeColoring G qphi → (
    ∀ e ∈ S,
    ∃ (c : Fin k), qphi e = some c) → (2 : ℕ) * S.card ≤ k * (U.card - (1 : ℕ))) →
    ∀ (f : E), f ∈ InternalEdges G U := by
  classical
  intro V E _ _ _ G k hcritical hindex he hdensity U hEq hvalue hElig total_card f
  by_contra hf
  have hdf := hcritical f
  have hlf : ChromaticIndex (DeleteEdge G f) ≤ k := by
    have ht : ChromaticIndex (DeleteEdge G f) < k + 1 := by
      simpa [hindex] using hdf
    omega
  obtain ⟨psi, hpp, hfull⟩ := (ChromaticIndexSpec (DeleteEdge G f)).1
  let qphi : PartialEdgeColoring E k := fun e =>
    if he : e = f then none else
      some (Fin.castLE hlf (Classical.choose (hfull ⟨e, by simp [he]⟩)))
  have hq : IsProperEdgeColoring G qphi := by
    intro e g c heg hadj hce
    by_cases he : e = f
    · simp [qphi, he] at hce
    · by_cases hg : g = f
      · simp [qphi, hg]
      · have hce' : Fin.castLE hlf (Classical.choose (hfull ⟨e, by simp [he]⟩)) = c := by
          have hc := Classical.choose_spec (hfull ⟨e, by simp [he]⟩)
          exact Option.some.inj (show
            some (Fin.castLE hlf (Classical.choose (hfull ⟨e, by simp [he]⟩))) = some c by
            simpa [qphi, he] using hce)
        have hpg := hpp (show (⟨e, by simp [he]⟩ : {e // e ∈ Finset.univ.erase f}) ≠
            ⟨g, by simp [hg]⟩ by simpa using heg)
          (by simpa [AdjacentEdges, Incident, DeleteEdge, RestrictEdges] using hadj)
          (by simpa using Classical.choose_spec (hfull ⟨e, by simp [he]⟩))
        intro hbad
        apply hpg
        have hbad' := Option.some.inj (show
          some (Fin.castLE hlf (Classical.choose (hfull ⟨g, by simp [hg]⟩))) = some c by
          simpa [qphi, hg] using hbad)
        have hsame : Classical.choose (hfull ⟨g, by simp [hg]⟩) =
            Classical.choose (hfull ⟨e, by simp [he]⟩) := by
          apply Fin.ext
          exact (congrArg Fin.val hbad').trans (congrArg Fin.val hce').symm
        rw [← hsame]
        exact Classical.choose_spec (hfull ⟨g, by simp [hg]⟩)
  have hfullU : ∀ e, e ∈ InternalEdges G U → ∃ c, qphi e = some c := by
    intro e he
    have hne : e ≠ f := by
      intro hef
      apply hf
      simpa [hef] using he
    exact ⟨Fin.castLE hlf (Classical.choose (hfull ⟨e, by simp [hne]⟩)), by
      simp [qphi, hne]⟩
  have hb := total_card (InternalEdges G U) (by intro e he; exact he) qphi hq hfullU
  have hden : DensityValue G U ≤ k := by
    change (2 * (InternalEdges G U).card : ℚ) /
        ((U.card : ℚ) - 1) ≤ k
    have hn : (0 : ℚ) < (U.card : ℚ) - 1 := by
      have hU3 : 3 ≤ U.card := hElig.1
      exact sub_pos.mpr (by exact_mod_cast (show 1 < U.card by omega))
    apply (div_le_iff₀ hn).2
    change (2 * (InternalEdges G U).card : ℚ) ≤
      (k : ℚ) * ((U.card : ℚ) - 1)
    have hcast : (↑(U.card - 1) : ℚ) = (U.card : ℚ) - 1 := by
      have hU3 : 3 ≤ U.card := hElig.1
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [← hcast]
    exact_mod_cast hb
  have : (k : ℚ) < k := by exact lt_of_lt_of_le hvalue (by simpa using hden)
  linarith

private theorem helper_elem_to_p_142.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ), Critical G → ChromaticIndex G = k + (1 : ℕ) →
        MaximumDegree G + (1 : ℕ) ≤ k → (
    ∀ (v : V),
    ∃ (e : E), Incident G v e) →
    let P : Prop :=
    ∀ (e0 : E) (phi : PartialEdgeColoring E k), IsProperEdgeColoring G phi → IsOneEdgeUncolored
        phi e0 → ColoredVertexSetElementary G phi Finset.univ; Elementary G → P := by
  classical
  intro V E _ _ _ G k hcritical hindex hdegree hnoisolated P he e0 phi hp ho
  have hdensity : (k : ℚ) < Density G := by
    have hc : k < DensityCeil G := by
      calc
        k < k + 1 := Nat.lt_succ_self k
        _ = ChromaticIndex G := hindex.symm
        _ = DensityCeil G := he
    exact Nat.lt_ceil.mp hc
  have hpos : 0 < Density G := by
    have hk : 0 < k := by omega
    exact lt_trans (by exact_mod_cast hk) hdensity
  have hmem : Density G ∈ insert 0
      ((Finset.univ.powerset.filter (fun U : Finset V => EligibleOddSet U)).image
        (DensityValue G)) := by
    unfold Density
    exact Finset.max'_mem _ _
  simp only [Finset.mem_insert, Finset.mem_image] at hmem
  rcases hmem with hzero | ⟨U, hU, hEq⟩
  · linarith
  have hvalue : (k : ℚ) < DensityValue G U := by
    rw [hEq]
    exact hdensity
  have hElig : EligibleOddSet U := (Finset.mem_filter.mp hU).2
  have endpoint_card : ∀ e : E, (G.ends e).toFinset.card = 2 := by
    intro e
    apply Sym2.card_toFinset_of_not_isDiag
    intro hd
    exact G.loopless e ((G.ends e).diagElem hd) (Sym2.diag_diagElem hd).symm
  have matching_card := @helper_matching_card_458 (@V) (@E) inferInstance inferInstance
       (@G) (@k) (@endpoint_card)
  have total_card := @helper_total_card_517 (@V) (@E) inferInstance inferInstance  (@G)
      (@k) (@he) (@U) (@hElig) (@matching_card)
  have edge_internal := @helper_edge_internal_577 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@hcritical) (@hindex) (@he) (@hdensity) (@U) (@hEq) (@hvalue)
      (@hElig) (@total_card)
  exact @helper_continuation_337 (@V) (@E) inferInstance inferInstance  (@G) (@k)
      (@hdegree) (@hnoisolated) (@he) (@e0) (@phi) (@hp) (@ho) (@U) (@hU) (@hEq) (@hvalue)
      (@hElig) (@endpoint_card) (@matching_card) (@total_card) (@edge_internal)
theorem egraph2 {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e) :
    (Elementary G ↔
      ∀ (e0 : E) (phi : PartialEdgeColoring E k),
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 →
          ColoredVertexSetElementary G phi Finset.univ) ∧
    ((∀ (e0 : E) (phi : PartialEdgeColoring E k),
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 →
          ColoredVertexSetElementary G phi Finset.univ) ↔
      ∃ (e0 : E) (phi : PartialEdgeColoring E k),
        IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored phi e0 ∧
          ColoredVertexSetElementary G phi Finset.univ) ∧
    ((∃ (e0 : E) (phi : PartialEdgeColoring E k),
        IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored phi e0 ∧
          ColoredVertexSetElementary G phi Finset.univ) ↔
      ∃ (e0 : E) (phi : PartialEdgeColoring E k) (X : Finset V),
        IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored phi e0 ∧
          (∀ v, v ∈ G.ends e0 → v ∈ X) ∧
          ColoredVertexSetElementary G phi X ∧
          ColoredVertexSetStronglyClosed G phi X) := by
  classical
  let P := ∀ (e0 : E) (phi : PartialEdgeColoring E k),
    IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 →
      ColoredVertexSetElementary G phi Finset.univ
  let Q := ∃ (e0 : E) (phi : PartialEdgeColoring E k),
    IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored phi e0 ∧
      ColoredVertexSetElementary G phi Finset.univ
  let R := ∃ (e0 : E) (phi : PartialEdgeColoring E k) (X : Finset V),
    IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored phi e0 ∧
      (∀ v, v ∈ G.ends e0 → v ∈ X) ∧
      ColoredVertexSetElementary G phi X ∧
      ColoredVertexSetStronglyClosed G phi X
  have q_to_r : Q → R := by
    rintro ⟨e0, phi, hp, ho, he⟩
    refine ⟨e0, phi, Finset.univ, hp, ho, ?_, he, ?_⟩
    · simp
    · constructor
      · intro f c v hf hv hfv
        exfalso
        simp [BoundaryEdges] at hf
      · intro f g c hf hg hne hfc hgc
        exfalso
        simp [BoundaryEdges] at hf
  have p_to_q := @helper_p_to_q_85 V E inferInstance inferInstance inferInstance G k hcritical
      hindex
  have elem_to_p := @helper_elem_to_p_142 V E inferInstance inferInstance inferInstance G k
      hcritical hindex hdegree hnoisolated
  change (Elementary G ↔ P) ∧ (P ↔ Q) ∧ (Q ↔ R)
  have r_to_q : R → Q := by
    rintro ⟨e0, phi, X, hp, ho, he, hs, hc⟩
    have ha := StronglyClosedWitnessElementary G k hindex hdegree e0 phi X hp ho he hs hc
    exact ⟨e0, phi, hp, ho, (elem_to_p ha) e0 phi hp ho⟩
  have q_to_p : Q → P := by
    rintro ⟨w, psi, hwp, hwo, hwe⟩ e0 phi hp ho
    have helem : Elementary G := by
      apply StronglyClosedWitnessElementary G k hindex hdegree w psi Finset.univ
        hwp hwo (by simp) hwe
      constructor
      · intro f c v hf hv hfv
        exfalso
        simp [BoundaryEdges] at hf
      · intro f g c hf hg hne hfc hgc
        exfalso
        simp [BoundaryEdges] at hf
    unfold ColoredVertexSetElementary
    intro u hu v hv hne
    exact elem_to_p helem e0 phi hp ho hu hv hne
  have p_to_elem : P → Elementary G := by
    intro h
    rcases p_to_q h with ⟨w, psi, hwp, hwo, hwe⟩
    exact StronglyClosedWitnessElementary G k hindex hdegree w psi Finset.univ
      hwp hwo (by simp) hwe (by
        constructor
        · intro f c v hf hv hfv
          exfalso
          simp [BoundaryEdges] at hf
        · intro f g c hf hg hne hfc hgc
          exfalso
          simp [BoundaryEdges] at hf)
  exact ⟨⟨elem_to_p, p_to_elem⟩,
    ⟨p_to_q, q_to_p⟩, ⟨q_to_r, r_to_q⟩⟩

end GoldbergSeymour

end
