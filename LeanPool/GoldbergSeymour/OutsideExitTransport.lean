/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloringStable
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap
public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.TreeExitPath

public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# P2716_T1_Outside Exit Transport

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem P2716_T1_OutsideExitTransport_alphaOutside_256.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E) {k :
    ℕ} {e0 : E} (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha theta beta :
    Fin k), let X := TreeSequenceVertexSet T; (∀ {f : E} {u v : V}, phi f = some alpha ∨ phi f
    = some theta → Incident G u f → Incident G v f → (u ∈ X ↔ v ∈ X)) → ∀ (a b : V) (P :
    (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a) (Sum.inl b)), P.IsPath → (∀ w ∈
    TreeSequenceVertexSet T, Sum.inl w ∈ P.support ↔ w = b) → ∀ {f : E}, Sum.inr f ∈ P.support
    → phi f = some alpha → ¬TreeIncidentEdge T f := by
  classical
  intro V E _ _ G k e0 T phi alpha theta beta X sameSide a b P path only
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  as_aux_lemma =>
  intro f hf hfa hi
  obtain ⟨j, hj, hjle⟩ := P.mem_support_iff_exists_getVert.mp hf
  have hj0 : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    simp [hz] at hj
  have hjlt : j < P.length := by
    by_contra hn
    have hz : j = P.length := by omega
    simp [hz] at hj
  obtain ⟨u, hu, huf⟩ := hi
  have leftAdj := P.adj_getVert_succ (show j - 1 < P.length by omega)
  rw [show j - 1 + 1 = j by omega, hj] at leftAdj
  have rightAdj := P.adj_getVert_succ hjlt
  rw [hj] at rightAdj
  have left : ∃ v : V, P.getVert (j - 1) = Sum.inl v ∧ v ∈ X := by
    cases hx : P.getVert (j - 1) with
    | inr e => rw [hx] at leftAdj; exact leftAdj.elim
    | inl v =>
      rw [hx] at leftAdj
      exact ⟨v, rfl, (sameSide (Or.inl hfa) huf leftAdj.1).mp hu⟩
  have right : ∃ v : V, P.getVert (j + 1) = Sum.inl v ∧ v ∈ X := by
    cases hx : P.getVert (j + 1) with
    | inr e => rw [hx] at rightAdj; exact rightAdj.elim
    | inl v =>
      rw [hx] at rightAdj
      exact ⟨v, rfl, (sameSide (Or.inl hfa) huf rightAdj.1).mp hu⟩
  obtain ⟨v, hv, hvX⟩ := left
  obtain ⟨w, hw, hwX⟩ := right
  have hvb : v = b := (only v hvX).mp (hv ▸ P.getVert_mem_support _)
  have hwb : w = b := (only w hwX).mp (hw ▸ P.getVert_mem_support _)
  have hidx := path.getVert_injOn (show j - 1 ≤ P.length by omega)
    (show j + 1 ≤ P.length by omega) (by rw [hv, hw, hvb, hwb])
  omega

private theorem P2716_T1_OutsideExitTransport_sideAdj_144.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E}
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha theta : Fin k),
      let X := TreeSequenceVertexSet T;
      (∀ {f : E} {u v : V}, phi f = some alpha ∨ phi f = some theta → Incident G u f → Incident G
          v f → (u ∈ X ↔ v ∈ X)) →
        let side := fun (z : V ⊕ E) =>
          match z with
          | Sum.inl v => v ∈ X
          | Sum.inr f => TreeIncidentEdge T f;
        ∀ {x y : V ⊕ E}, (TwoColorIncidenceGraph G phi alpha theta).Adj x y → (side x ↔ side y)
           := by
  classical
  intro V E _ _ G k e0 T phi alpha theta X sameSide side
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  as_aux_lemma =>
  intro x y h
  cases x with
  | inl v =>
    cases y with
    | inl w => exact h.elim
    | inr f =>
      change Incident G v f ∧ (phi f = some alpha ∨ phi f = some theta) at h
      change v ∈ X ↔ TreeIncidentEdge T f
      refine ⟨fun hv => ⟨v, hv, h.1⟩, ?_⟩
      rintro ⟨u, hu, huf⟩
      exact (sameSide h.2 huf h.1).mp hu
  | inr f =>
    cases y with
    | inr g => exact h.elim
    | inl v =>
      change Incident G v f ∧ (phi f = some alpha ∨ phi f = some theta) at h
      change TreeIncidentEdge T f ↔ v ∈ X
      refine ⟨?_, fun hv => ⟨v, hv, h.1⟩⟩
      rintro ⟨u, hu, huf⟩
      exact (sameSide h.2 huf h.1).mp hu

private theorem P2716_T1_OutsideExitTransport_recolor_206.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Finite E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E} (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (alpha theta : Fin k),
      alpha ≠ theta →
        let X := TreeSequenceVertexSet T;
        let roots := Finset.image Sum.inl {v : V | v ∉ X};
        (∀ z ∈ roots, ∀ (v : V), Sum.inl v ∈ TwoColorComponent G phi alpha theta z → v ∉ X) →
          let sigma := OutsideTreeColorSwap T phi alpha theta;
          (∀ {f : E},
              ¬TreeIncidentEdge T f →
                phi f = some alpha ∨ phi f = some theta → ∃ z ∈ roots, Sum.inr f ∈
                    TwoColorComponent G phi alpha theta z) →
            OutsideKempeRecoloring T phi sigma alpha theta := by
  classical
  intro V E _ _ _ _ G k e0 T phi alpha theta hat X roots outsideComponents sigma selected
  let _ := Fintype.ofFinite E
  as_aux_lemma =>
  refine ⟨hat, roots, outsideComponents, ?_⟩
  intro f
  by_cases hf : TreeIncidentEdge T f
  · have fix : sigma f = phi f := by simp [sigma, OutsideTreeColorSwap, hf]
    rw [fix]
    by_cases hc : phi f = some alpha ∨ phi f = some theta
    · have hn : ¬ ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha theta z := by
        rintro ⟨z, hz, hzf⟩
        obtain ⟨v, hv, hvf⟩ := hf
        have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (show (TwoColorIncidenceGraph G phi alpha theta).Adj
            (Sum.inl v) (Sum.inr f) from ⟨hvf, hc⟩)
        have hvz : Sum.inl v ∈ TwoColorComponent G phi alpha theta z :=
          heq.trans ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hzf)
        exact outsideComponents z hz v hvz hv
      simp [hn]
    · push Not at hc
      simp [hc.1, hc.2]
  · by_cases ha : phi f = some alpha
    · simp [sigma, OutsideTreeColorSwap, hf, ha, selected hf (Or.inl ha)]
    · by_cases ht : phi f = some theta
      · simp [sigma, OutsideTreeColorSwap, hf, ht, selected hf (Or.inr ht)]
      · simp [sigma, OutsideTreeColorSwap, hf, ha, ht]

private theorem P2716_T1_OutsideExitTransport_subsetData_233.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k :
    ℕ} {e0 : E} (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha theta : Fin k),
    let X := TreeSequenceVertexSet T; let sigma := OutsideTreeColorSwap T phi alpha theta;
    StableColoring T ∅ phi sigma → (∀ (f : E), TreeIncidentEdge T f → sigma f = phi f) → ∀ (U
    : TreeSequence G e0), TreeSequenceVertexSet U ⊆ X → (∀ (C : Finset (Fin k)),
    StableColoring U C phi sigma) ∧ TreeMissingColors sigma U = TreeMissingColors phi U ∧ ∀ (c
    : Fin k), TreeColorSetClosed G phi U {c} → TreeColorSetClosed G sigma U {c} := by
  classical
  intro V E _ _ G k e0 T phi alpha theta X sigma stable fixed
  as_aux_lemma =>
  intro U hU
  have inc : ∀ f, TreeIncidentEdge U f → TreeIncidentEdge T f := by
    rintro f ⟨v, hv, hvf⟩
    exact ⟨v, hU hv, hvf⟩
  refine ⟨fun C => ⟨fun f hf _ => fixed f (inc f hf),
    fun v hv => stable.2 v (hU hv)⟩, ?_, ?_⟩
  · exact Finset.biUnion_congr rfl (fun v hv => stable.2 v (hU hv))
  · intro c hc d hd
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    change f ∈ (BoundaryEdges G (TreeSequenceVertexSet U)).filter
      (fun f => sigma f = some d) at hf
    obtain ⟨hb, hcolor⟩ := Finset.mem_filter.mp hf
    have hbData := hb
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hbData
    obtain ⟨u, hu, v, hv, he⟩ := hbData
    have hi : TreeIncidentEdge U f := by
      refine ⟨u, hu, ?_⟩
      change u ∈ G.ends f
      rw [he]
      exact Sym2.mem_mk_left _ _
    have old : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet U) d := by
      simp only [BoundaryColorEdges, Finset.mem_filter]
      exact ⟨hb, (fixed f (inc f hi)).symm.trans hcolor⟩
    rw [hc d hd] at old
    exact Finset.notMem_empty _ old

private theorem P2716_T1_OutsideExitTransport_outsideMissing_274.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E}
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha theta beta : Fin k),
      alpha ≠ theta →
        let X := TreeSequenceVertexSet T;
        (∀ {f : E} {u v : V}, phi f = some alpha ∨ phi f = some theta → Incident G u f → Incident
            G v f → (u ∈ X ↔ v ∈ X)) →
          let sigma := OutsideTreeColorSwap T phi alpha theta;
          (∀ (f : E), TreeIncidentEdge T f → sigma f = phi f) →
            (∀ (f : E), sigma f = some beta ↔ phi f = some beta) →
              ∀ a ∉ X,
                (alpha ∈ MissingColors G phi a → theta ∈ MissingColors G sigma a) ∧
                  (beta ∈ MissingColors G phi a → beta ∈ MissingColors G sigma a) := by
  classical
  intro V E _ _ G k e0 T phi alpha theta beta hat X sameSide sigma fixed betaEq
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
  intro a ha
  have missing : ∀ (psi : PartialEdgeColoring E k) (c : Fin k),
      c ∈ MissingColors G psi a ↔ ∀ f, Incident G a f → psi f ≠ some c := by
    simp [MissingColors, PresentColors]
  constructor
  · intro hm
    rw [missing] at hm ⊢
    intro f haf hsf
    by_cases hi : TreeIncidentEdge T f
    · have hpf : phi f = some theta := (fixed f hi).symm.trans hsf
      obtain ⟨v, hv, hvf⟩ := hi
      exact ha ((sameSide (Or.inr hpf) hvf haf).mp hv)
    · have hpf : phi f = some alpha := by
        by_cases hfa : phi f = some alpha
        · exact hfa
        · by_cases hft : phi f = some theta
          · simp [sigma, OutsideTreeColorSwap, hi, hft, hat, hat.symm] at hsf
          · simp [sigma, OutsideTreeColorSwap, hi, hfa, hft] at hsf
      exact hm f haf hpf
  · intro hm
    rw [missing] at hm ⊢
    intro f haf hs
    exact hm f haf ((betaEq f).mp hs)

private theorem P2716_T1_OutsideExitTransport_transferEdges_307.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E) {k :
    ℕ} {e0 : E} (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha theta beta :
    Fin k), let sigma := OutsideTreeColorSwap T phi alpha theta; (∀ (f : E), sigma f = some
    beta ↔ phi f = some beta) → ∀ (a b : V) (P : (TwoColorIncidenceGraph G phi alpha
    beta).Walk (Sum.inl a) (Sum.inl b)), (∀ {f : E}, Sum.inr f ∈ P.support → phi f = some
    alpha → ¬TreeIncidentEdge T f) → ∀ e ∈ P.edges, e ∈ (TwoColorIncidenceGraph G sigma theta
    beta).edgeSet := by
  classical
  intro V E _ _ G k e0 T phi alpha theta beta sigma betaEq a b P alphaOutside
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  as_aux_lemma =>
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
    have adj := P.adj_of_mem_edges he
    have convert : ∀ {v : V} {f : E},
        Incident G v f → (phi f = some alpha ∨ phi f = some beta) →
        Sum.inr f ∈ P.support →
        Incident G v f ∧ (sigma f = some theta ∨ sigma f = some beta) := by
      intro v f hv hc hf
      refine ⟨hv, ?_⟩
      rcases hc with hc | hc
      · left
        simp [sigma, OutsideTreeColorSwap, alphaOutside hf hc, hc]
      · exact Or.inr ((betaEq f).mpr hc)
    cases x with
    | inl v =>
      cases y with
      | inl w => exact adj.elim
      | inr f => exact convert adj.1 adj.2 (P.snd_mem_support_of_mem_edges he)
    | inr f =>
      cases y with
      | inr g => exact adj.elim
      | inl v => exact convert adj.1 adj.2 (P.fst_mem_support_of_mem_edges he)

theorem P2716_T1_OutsideExitTransport {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (alpha theta beta : Fin k) (hat : alpha ≠ theta)
    (hab : alpha ≠ beta) (htb : theta ≠ beta)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (haClosed : TreeColorSetClosed G phi T {alpha})
    (htClosed : TreeColorSetClosed G phi T {theta}) :
    ∃ sigma : PartialEdgeColoring E k,
      OutsideKempeRecoloring T phi sigma alpha theta ∧
      IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
      (∀ U : TreeSequence G e0,
        TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet T →
        (∀ C : Finset (Fin k), StableColoring U C phi sigma) ∧
        TreeMissingColors sigma U = TreeMissingColors phi U ∧
        (∀ c : Fin k, TreeColorSetClosed G phi U {c} →
          TreeColorSetClosed G sigma U {c})) ∧
      (∀ a : V, a ∉ TreeSequenceVertexSet T →
        (alpha ∈ MissingColors G phi a → theta ∈ MissingColors G sigma a) ∧
        (beta ∈ MissingColors G phi a → beta ∈ MissingColors G sigma a)) ∧
      (∀ (A : TreeSequence G e0),
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet T →
        ∀ (a b : V)
          (P : (TwoColorIncidenceGraph G phi alpha beta).Walk
            (Sum.inl a) (Sum.inl b)),
          TreeExitPath T phi alpha beta a b P →
          b ∈ TreeSequenceVertexSet A →
          ∃ Q : (TwoColorIncidenceGraph G sigma theta beta).Walk
              (Sum.inl a) (Sum.inl b),
            TreeExitPath A sigma theta beta a b Q ∧
            Q.support = P.support ∧ Q.length = P.length) := by
  classical
  let X := TreeSequenceVertexSet T
  have boundaryColor : ∀ {f : E}, f ∈ BoundaryEdges G X →
      phi f ≠ some alpha ∧ phi f ≠ some theta := by
    as_aux_lemma =>
    intro f hf
    constructor
    · intro hc
      have hm : f ∈ BoundaryColorEdges G phi X alpha := by
        simp [BoundaryColorEdges, hf, hc]
      rw [haClosed alpha (Finset.mem_singleton_self _)] at hm
      exact Finset.notMem_empty _ hm
    · intro hc
      have hm : f ∈ BoundaryColorEdges G phi X theta := by
        simp [BoundaryColorEdges, hf, hc]
      rw [htClosed theta (Finset.mem_singleton_self _)] at hm
      exact Finset.notMem_empty _ hm
  have sameSide : ∀ {f : E} {u v : V},
      (phi f = some alpha ∨ phi f = some theta) →
      Incident G u f → Incident G v f → (u ∈ X ↔ v ∈ X) := by
    as_aux_lemma =>
    intro f u v hc hu hv
    have forward : ∀ {u v : V}, Incident G u f → Incident G v f →
        u ∈ X → v ∈ X := by
      intro u v hu hv hux
      by_contra hvx
      have huv : u ≠ v := by rintro rfl; exact hvx hux
      have hf : f ∈ BoundaryEdges G X := by
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u, hux, v, hvx, (Sym2.mem_and_mem_iff huv).mp ⟨hu, hv⟩⟩
      rcases hc with hc | hc
      · exact (boundaryColor hf).1 hc
      · exact (boundaryColor hf).2 hc
    exact ⟨forward hu hv, forward hv hu⟩
  let side : Sum V E → Prop := fun z => match z with
    | Sum.inl v => v ∈ X
    | Sum.inr f => TreeIncidentEdge T f
  have sideAdj : ∀ {x y : Sum V E},
      (TwoColorIncidenceGraph G phi alpha theta).Adj x y →
      (side x ↔ side y) := by
    exact @P2716_T1_OutsideExitTransport_sideAdj_144 V E inferInstance inferInstance G k e0 T phi
        alpha theta sameSide
  have sideWalk : ∀ {x y : Sum V E}
      (p : (TwoColorIncidenceGraph G phi alpha theta).Walk x y),
      side x ↔ side y := by
    as_aux_lemma =>
    intro x y p
    induction p with
    | nil => rfl
    | cons h p ih => exact (sideAdj h).trans ih
  let roots : Finset (Sum V E) := (Finset.univ.filter fun v : V => v ∉ X).image Sum.inl
  have outsideComponents : ∀ z ∈ roots, ∀ v : V,
      Sum.inl v ∈ TwoColorComponent G phi alpha theta z → v ∉ X := by
    as_aux_lemma =>
    intro z hz v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    have haout : a ∉ X := (Finset.mem_filter.mp ha).2
    have reach : (TwoColorIncidenceGraph G phi alpha theta).Reachable
        (Sum.inl v) (Sum.inl a) := by
      exact SimpleGraph.ConnectedComponent.eq.mp
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hv)
    obtain ⟨p⟩ := reach
    exact fun hvx => haout ((sideWalk p).mp hvx)
  let sigma := OutsideTreeColorSwap T phi alpha theta
  have selected : ∀ {f : E}, ¬ TreeIncidentEdge T f →
      (phi f = some alpha ∨ phi f = some theta) →
      ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha theta z := by
    as_aux_lemma =>
    intro f hf hc
    obtain ⟨u, v, huv⟩ : ∃ u v, G.ends f = s(u, v) := by
      exact Sym2.inductionOn (G.ends f) (fun u v => ⟨u, v, rfl⟩)
    have hu : Incident G u f := by
      change u ∈ G.ends f
      rw [huv]
      exact Sym2.mem_mk_left _ _
    have huout : u ∉ X := fun hx => hf ⟨u, hx, hu⟩
    refine ⟨Sum.inl u, Finset.mem_image.mpr ⟨u, by simp [huout], rfl⟩, ?_⟩
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (show (TwoColorIncidenceGraph G phi alpha theta).Adj
        (Sum.inr f) (Sum.inl u) from ⟨hu, hc⟩)
  have recolor : OutsideKempeRecoloring T phi sigma alpha theta := by
    exact @P2716_T1_OutsideExitTransport_recolor_206 V E inferInstance inferInstance
        inferInstance inferInstance G k e0 T phi alpha theta hat outsideComponents selected
  obtain ⟨proper, one, stable, invariant, fixed⟩ :=
    OutsideKempeRecoloringStable G e0 T ∅ phi sigma alpha theta hproper hone recolor
  have subsetData : ∀ U : TreeSequence G e0,
      TreeSequenceVertexSet U ⊆ X →
      (∀ C : Finset (Fin k), StableColoring U C phi sigma) ∧
      TreeMissingColors sigma U = TreeMissingColors phi U ∧
      (∀ c : Fin k, TreeColorSetClosed G phi U {c} →
        TreeColorSetClosed G sigma U {c}) := by
    exact @P2716_T1_OutsideExitTransport_subsetData_233 V E inferInstance inferInstance G k e0 T
        phi alpha theta stable fixed
  have betaEq : ∀ f : E, sigma f = some beta ↔ phi f = some beta := by
    as_aux_lemma =>
    intro f
    by_cases hi : TreeIncidentEdge T f
    · simp [sigma, OutsideTreeColorSwap, hi]
    · by_cases ha : phi f = some alpha <;> by_cases ht : phi f = some theta <;>
        simp [sigma, OutsideTreeColorSwap, hi, ha, ht, hat.symm, hab, htb]
  have outsideMissing : ∀ a : V, a ∉ X →
      (alpha ∈ MissingColors G phi a → theta ∈ MissingColors G sigma a) ∧
      (beta ∈ MissingColors G phi a → beta ∈ MissingColors G sigma a) := by
    exact @P2716_T1_OutsideExitTransport_outsideMissing_274 V E inferInstance inferInstance G k
        e0 T phi alpha theta beta hat sameSide fixed betaEq
  refine ⟨sigma, recolor, proper, one, subsetData, outsideMissing, ?_⟩
  intro A hA a b P hP hbA
  rcases hP with ⟨path, plen, haout, hbin, hamiss, only⟩
  have alphaOutside : ∀ {f : E}, Sum.inr f ∈ P.support →
      phi f = some alpha → ¬ TreeIncidentEdge T f := by
    exact @P2716_T1_OutsideExitTransport_alphaOutside_256 V E inferInstance inferInstance G k e0
        T phi alpha theta beta sameSide a b P path only
  have transferEdges : ∀ e ∈ P.edges,
      e ∈ (TwoColorIncidenceGraph G sigma theta beta).edgeSet := by
    exact @P2716_T1_OutsideExitTransport_transferEdges_307 V E inferInstance inferInstance G k e0
        T phi alpha theta beta betaEq a b P alphaOutside
  let Q := P.transfer (TwoColorIncidenceGraph G sigma theta beta) transferEdges
  have supportEq : Q.support = P.support := P.support_transfer _
  have lengthEq : Q.length = P.length := P.length_transfer _
  refine ⟨Q, ⟨path.transfer _, by omega, fun ha => haout (hA ha), hbA, ?_, ?_⟩,
    supportEq, lengthEq⟩
  · rcases hamiss with ham | hbm
    · exact Or.inl ((outsideMissing a haout).1 ham)
    · exact Or.inr ((outsideMissing a haout).2 hbm)
  · intro v hv
    rw [supportEq]
    exact only v (hA hv)

end GoldbergSeymour

end
