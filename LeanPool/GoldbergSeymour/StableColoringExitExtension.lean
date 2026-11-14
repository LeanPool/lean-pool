/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.MaximumDegree
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TreeExit
public import LeanPool.GoldbergSeymour.StableColoringIncidentEdgeCriterion

/-!
# LEM_extable

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private theorem helper_ends_eq_of_mem_61.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ),
        MaximumDegree G + (1 : ℕ) ≤ k →
    ∀ {z : Sym2 V} {x y : V}, x ∈ z → y ∈ z → x ≠ y → z = s(x, y) := by
  classical
  intro V E _ _ G k _ z x y hx hy hxy
  induction z using Sym2.inductionOn with
  | _ a b =>
    simp only [Sym2.mem_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all []

private theorem helper_hbetat_71.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (T : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
        (delta : Fin k) (pi : PartialEdgeColoring E k), StableColoring T (insert delta C : Finset
        (Fin k)) phi pi →
    ∀ beta ∈ TreeMissingColors pi T, beta ∈ TreeMissingColors phi T := by
  classical
  intro V E _ _ G k e0 T C phi delta pi hstable beta hbetat
  let _ := Fintype.ofFinite V
  have hv : ∃ w ∈ TreeSequenceVertexSet T, beta ∈ MissingColors G pi w := by
    unfold TreeMissingColors at hbetat
    simpa only [Finset.mem_biUnion] using hbetat
  obtain ⟨w, hw, hbw⟩ := hv
  rw [hstable.2 w hw] at hbw
  unfold TreeMissingColors
  simp only [Finset.mem_biUnion]
  exact ⟨w, hw, hbw⟩

private theorem helper_tree_boundary_91.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (T : TreeSequence G e0), MaximumDegree G + (1 : ℕ) ≤ k → (
    ∀ {z : Sym2 V} {x y : V}, x ∈ z → y ∈ z → x ≠ y → z = s(x, y)) →
    ∀ {e g : E}, TreeIncidentEdge T e → ¬TreeIncidentEdge T g → AdjacentEdges G e g → e ∈
        BoundaryEdges G (TreeSequenceVertexSet T) := by
  classical
  intro V E _ _ G k e0 T _ ends_eq_of_mem e g he hg hadj
  obtain ⟨x, hx, hxe⟩ := he
  obtain ⟨w, hwe, hwg⟩ := hadj
  have hwout : w ∉ TreeSequenceVertexSet T := by
    intro hw
    exact hg ⟨w, hw, hwg⟩
  have hxy : x ≠ w := by
    intro h
    exact hwout (h ▸ hx)
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  change ∃ a ∈ TreeSequenceVertexSet T, ∃ b ∉ TreeSequenceVertexSet T,
    G.ends e = s(a, b)
  refine ⟨x, hx, w, hwout, ?_⟩
  exact ends_eq_of_mem hxe hwe hxy

private theorem helper_swap_injective_111 :
    open scoped Classical in
    ∀ (k : ℕ) (alpha beta : Fin k),
    Function.Injective fun (q : Option (Fin k)) ↦
      if q = some alpha then some beta else if q = some beta then some alpha else q := by
  classical
  intro k alpha beta q r h
  cases q <;> cases r
  · rfl
  · rename_i val
    by_cases ha : val = alpha
    · simp [ha] at h
    · by_cases hb : val = beta
      · have hab : beta ≠ alpha := by
          intro hab
          exact ha (hb.trans hab)
        simp [hb, hab] at h
      · simp [ha, hb] at h
  · rename_i val
    by_cases ha : val = alpha
    · simp [ha] at h
    · by_cases hb : val = beta
      · have hab : beta ≠ alpha := by
          intro hab
          exact ha (hb.trans hab)
        simp [hb, hab] at h
      · simp [ha, hb] at h
  · simp only [Option.some.injEq] at h ⊢
    rename_i a b
    by_cases qa : a = alpha <;> by_cases qb : a = beta <;>
      by_cases ra : b = alpha <;> by_cases rb : b = beta <;> simp_all

private theorem helper_branch_141.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (T : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
        (delta alpha : Fin k) (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi →
    ∀ (beta : Fin k), (
    ∀ (f : E), TreeIncidentEdge T f → ((
    ∃ c ∈ TreeMissingColors phi T ∪ (insert delta C : Finset (Fin k)), phi f = some c) ∨
    ∃ c ∈ TreeMissingColors phi T ∪ (insert delta C : Finset (Fin k)), pi f = some c) → pi f = phi
        f) → alpha ∈ TreeMissingColors phi T → beta ∈ TreeMissingColors phi T → (
    ∀ {g : E}, g ∈ BoundaryEdges G (TreeSequenceVertexSet T) → ¬phi g = some alpha) → (
    ∀ {g : E}, g ∈ BoundaryEdges G (TreeSequenceVertexSet T) → ¬phi g = some beta) →
    let sigma : PartialEdgeColoring E k := OutsideTreeColorSwap T pi alpha beta; (
    ∀ {e g : E}, TreeIncidentEdge T e → ¬TreeIncidentEdge T g → AdjacentEdges G e g → e ∈
        BoundaryEdges G (TreeSequenceVertexSet T)) → (
    ∀ {e : E}, TreeIncidentEdge T e → sigma e = pi e) →
    ∀ ⦃e g : E⦄ ⦃c : Fin k⦄, e ≠ g → AdjacentEdges G e g → sigma e = some c → TreeIncidentEdge T e
        → sigma g ≠ some c := by
  classical
  intro V E _ _ G k e0 T C phi delta alpha pi hpi beta hcriterion halphat hbetat' halphaClosed
      hbetaClosed sigma tree_boundary tree_fixed e g c hne hadj hec he
  by_cases hg : TreeIncidentEdge T g
  · intro hsg
    apply hpi hne hadj
    · simpa [tree_fixed he] using hec
    · simpa [tree_fixed hg] using hsg
  · have hb := tree_boundary he hg hadj
    have hna : pi e ≠ some alpha := by
      intro hpa
      have hfix := hcriterion e he (Or.inr ⟨alpha, Finset.mem_union_left _ halphat, hpa⟩)
      exact halphaClosed hb (hfix ▸ hpa)
    have hnb : pi e ≠ some beta := by
      intro hpb
      have hfix := hcriterion e he (Or.inr ⟨beta, Finset.mem_union_left _ hbetat', hpb⟩)
      exact hbetaClosed hb (hfix ▸ hpb)
    have hca : c ≠ alpha := by
      intro h
      exact hna (h ▸ (by simpa [tree_fixed he] using hec))
    have hcb : c ≠ beta := by
      intro h
      exact hnb (h ▸ (by simpa [tree_fixed he] using hec))
    have hpe : pi e = some c := by simpa [tree_fixed he] using hec
    intro hsg
    have hpg : pi g = some c := by
      by_cases ga : pi g = some alpha
      · have hs : some beta = some c := by
          simpa [sigma, OutsideTreeColorSwap, hg, ga] using hsg
        exact False.elim (hcb (Option.some.inj hs).symm)
      · by_cases gb : pi g = some beta
        · have hs : some alpha = some c := by
            have hab : alpha ≠ beta := by
              intro h
              exact ga (h ▸ gb)
            simpa [sigma, OutsideTreeColorSwap, hg, ga, gb, hab, hab.symm] using hsg
          exact False.elim (hca (Option.some.inj hs).symm)
        · simpa [sigma, OutsideTreeColorSwap, hg, ga, gb] using hsg
    exact hpi hne hadj hpe hpg

private theorem helper_branch_177.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 f : E) (T : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k) (u
        v : V) (delta : Fin k), IsOneEdgeUncolored phi e0 → ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T) → f ∈ BoundaryEdges G (TreeSequenceVertexSet T) → u ∉
        TreeSequenceVertexSet T → v ∈ TreeSequenceVertexSet T →
    ∀ (alpha : Fin k) (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi →
        IsOneEdgeUncolored pi e0 → StableColoring T (insert delta C : Finset (Fin k)) phi pi →
    ∀ beta ∈ TreeMissingColors pi T, (
    ∀ (f : E), TreeIncidentEdge T f → ((
    ∃ c ∈ TreeMissingColors phi T ∪ (insert delta C : Finset (Fin k)), phi f = some c) ∨
    ∃ c ∈ TreeMissingColors phi T ∪ (insert delta C : Finset (Fin k)), pi f = some c) → pi f = phi
        f) → alpha ∈ TreeMissingColors phi T → beta ∈ TreeMissingColors phi T → (
    ∀ {g : E}, g ∈ BoundaryEdges G (TreeSequenceVertexSet T) → ¬phi g = some alpha) → (
    ∀ {g : E}, g ∈ BoundaryEdges G (TreeSequenceVertexSet T) → ¬phi g = some beta) →
    let sigma : PartialEdgeColoring E k := OutsideTreeColorSwap T pi alpha beta; (
    ∀ {e g : E}, TreeIncidentEdge T e → ¬TreeIncidentEdge T g → AdjacentEdges G e g → e ∈
        BoundaryEdges G (TreeSequenceVertexSet T)) → (
    ∀ {e : E}, TreeIncidentEdge T e → sigma e = pi e) → (Function.Injective fun (q : Option (Fin
        k)) ↦ if q = some alpha then some beta else if q = some beta then some alpha else q) →
    ∀ ⦃e g : E⦄ ⦃c : Fin k⦄, e ≠ g → AdjacentEdges G e g → sigma e = some c → ¬TreeIncidentEdge T
        e → sigma g ≠ some c := by
  classical
  intro V E _ _ G k e0 f T C phi u v delta honePhi hclosed hfboundary huout hvin alpha pi hpi
      honepi hstable beta hbetat hcriterion halphat hbetat' halphaClosed hbetaClosed sigma
      tree_boundary tree_fixed swap_injective e g c hne hadj hec he
  by_cases hg : TreeIncidentEdge T g
  · obtain ⟨w, hwe, hwg⟩ := hadj
    have hb := tree_boundary hg he ⟨w, hwg, hwe⟩
    have hna : pi g ≠ some alpha := by
      intro hpa
      have hfix := hcriterion g hg (Or.inr ⟨alpha, Finset.mem_union_left _ halphat, hpa⟩)
      exact halphaClosed hb (hfix ▸ hpa)
    have hnb : pi g ≠ some beta := by
      intro hpb
      have hfix := hcriterion g hg (Or.inr ⟨beta, Finset.mem_union_left _ hbetat', hpb⟩)
      exact hbetaClosed hb (hfix ▸ hpb)
    have hsg : sigma g ≠ some c := by
      intro h
      have hpg : pi g = some c := by simpa [tree_fixed hg] using h
      have hca : c ≠ alpha := by
        intro hc
        exact hna (hc ▸ hpg)
      have hcb : c ≠ beta := by
        intro hc
        exact hnb (hc ▸ hpg)
      have hpe' : pi e = some c := by
        by_cases hea : pi e = some alpha
        · exfalso
          have : some beta = some c := by
            simpa [sigma, OutsideTreeColorSwap, he, hea] using hec
          exact hcb (Option.some.inj this).symm
        · by_cases heb : pi e = some beta
          · exfalso
            have : some alpha = some c := by
              have hab : alpha ≠ beta := by
                intro h
                exact hea (h ▸ heb)
              simpa [sigma, OutsideTreeColorSwap, he, hea, heb, hab, hab.symm] using hec
            exact hca (Option.some.inj this).symm
          · simpa [sigma, OutsideTreeColorSwap, he, hea, heb] using hec
      exact (hpi hne.symm ⟨w, hwg, hwe⟩ hpg hpe')
    exact hsg
  · intro hsg
    have hsame : sigma e = sigma g := hec.trans hsg.symm
    have hpi_eq : pi e = pi g := by
      apply swap_injective
      simpa [sigma, OutsideTreeColorSwap, he, hg] using hsame
    have he0 : TreeIncidentEdge T e0 := by
      have hatt := T.attaches (⟨0, T.positive⟩ : Fin T.length)
      obtain ⟨i, hi⟩ := hatt
      have hi0 : i = ⟨0, Nat.zero_lt_succ _⟩ := by
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
      subst i
      have hvertex : T.vertex ⟨0, Nat.zero_lt_succ _⟩ ∈ TreeSequenceVertexSet T := by
        simp [TreeSequenceVertexSet]
      refine ⟨T.vertex ⟨0, Nat.zero_lt_succ _⟩, hvertex, ?_⟩
      have hzero : (⟨0, Nat.zero_lt_succ _⟩ : Fin (T.length + 1)) =
          Fin.castLT (⟨0, Nat.zero_lt_succ _⟩ : Fin (0 + 1)) (by omega) := by
        apply Fin.ext
        rfl
      change T.vertex ⟨0, Nat.zero_lt_succ _⟩ ∈ G.ends e0
      have hmem : T.vertex ⟨0, Nat.zero_lt_succ _⟩ ∈ G.ends (T.edge ⟨0, T.positive⟩) := by
        simp [hi, hzero]
      simpa [T.first_edge] using hmem
    have he_ne : e ≠ e0 := by
      intro heq
      exact he (heq ▸ he0)
    obtain ⟨d, hpd⟩ := honepi.2 e he_ne
    exact (hpi hne hadj hpd) (hpi_eq ▸ hpd)

private theorem helper_branch_242.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0) (alpha : Fin k)
      (pi : PartialEdgeColoring E k),
    IsOneEdgeUncolored pi e0 →
    ∀ (beta : Fin k),
    let sigma : PartialEdgeColoring E k := OutsideTreeColorSwap T pi alpha beta;
    IsOneEdgeUncolored sigma e0 := by
  classical
  intro V E _ _ G k e0 T alpha pi honepi beta sigma
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  unfold IsOneEdgeUncolored
  constructor
  · have he0 : TreeIncidentEdge T e0 := by
      have hatt := T.attaches (⟨0, T.positive⟩ : Fin T.length)
      obtain ⟨i, hi⟩ := hatt
      have hi0 : i = ⟨0, Nat.zero_lt_succ _⟩ := by
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
      subst i
      have hvertex : T.vertex ⟨0, Nat.zero_lt_succ _⟩ ∈ TreeSequenceVertexSet T := by
        simp [TreeSequenceVertexSet]
      refine ⟨T.vertex ⟨0, Nat.zero_lt_succ _⟩, hvertex, ?_⟩
      have hmem : T.vertex ⟨0, Nat.zero_lt_succ _⟩ ∈ G.ends (T.edge ⟨0, T.positive⟩) := by
        have hzero : (⟨0, Nat.zero_lt_succ _⟩ : Fin (T.length + 1)) =
            Fin.castLT (⟨0, Nat.zero_lt_succ _⟩ : Fin (0 + 1))
              (by omega) := by
          apply Fin.ext
          rfl
        simp [hi, hzero]
      change T.vertex ⟨0, Nat.zero_lt_succ _⟩ ∈ G.ends e0
      simpa [T.first_edge] using hmem
    simpa [sigma, OutsideTreeColorSwap, he0] using honepi.1
  · intro e hne
    obtain ⟨c, hc⟩ := honepi.2 e hne
    by_cases he : TreeIncidentEdge T e
    · exact ⟨c, by simpa [sigma, OutsideTreeColorSwap, he] using hc⟩
    · by_cases hca : pi e = some alpha
      · exact ⟨beta, by simp [sigma, OutsideTreeColorSwap, he, hca]⟩
      · by_cases hcb : pi e = some beta
        · exact ⟨alpha, by simp [sigma, OutsideTreeColorSwap, he, hcb]⟩
        · exact ⟨c, by simpa [sigma, OutsideTreeColorSwap, he, hca, hcb] using hc⟩

private theorem helper_branch_273.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
      (C : Finset (Fin k)) (phi : PartialEdgeColoring E k) (delta alpha : Fin k)
      (pi : PartialEdgeColoring E k),
    StableColoring T (insert delta C : Finset (Fin k)) phi pi →
    ∀ (beta : Fin k),
    let sigma : PartialEdgeColoring E k := OutsideTreeColorSwap T pi alpha beta;
    (∀ {e : E}, TreeIncidentEdge T e → sigma e = pi e) →
    StableColoring T (insert delta C : Finset (Fin k)) phi sigma := by
  classical
  intro V E _ _ G k e0 T C phi delta alpha pi hstable beta sigma tree_fixed
  let _ := Fintype.ofFinite V
  unfold StableColoring
  constructor
  · intro e he hc
    rw [tree_fixed he]
    exact hstable.1 e he hc
  · intro w hw
    have hm : MissingColors G sigma w = MissingColors G pi w := by
      classical
      unfold MissingColors PresentColors
      congr 1
      ext c
      constructor
      · intro hc
        obtain ⟨_, ⟨e, he, hce⟩⟩ := (Finset.mem_filter.mp hc)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e, he, by simpa [tree_fixed ⟨w, hw,
            he⟩] using hce⟩⟩
      · intro hc
        obtain ⟨_, ⟨e, he, hce⟩⟩ := (Finset.mem_filter.mp hc)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e, he, by simpa [tree_fixed ⟨w, hw,
            he⟩] using hce⟩⟩
    exact hm.trans (hstable.2 w hw)

theorem LEM_extable {V E : Type*} [Fintype V] [Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ)
    (e0 f : E) (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi : PartialEdgeColoring E k) (u v : V) (delta : Fin k)
    (_ : MaximumDegree G + 1 ≤ k)
    (hproperPhi : IsProperEdgeColoring G phi)
    (honePhi : IsOneEdgeUncolored phi e0)
    (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T))
    (hfboundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet T))
    (hfends : G.ends f = s(u, v))
    (huout : u ∉ TreeSequenceVertexSet T)
    (hvin : v ∈ TreeSequenceVertexSet T)
    (hfcolor : phi f = some delta)
    (hexists : ∃ pi : PartialEdgeColoring E k,
      IsProperEdgeColoring G pi ∧ IsOneEdgeUncolored pi e0 ∧
        StableColoring T (insert delta C) phi pi ∧
        ∃ beta, beta ∈ MissingColors G pi u ∧ beta ∈ TreeMissingColors pi T) :
    ∀ alpha, alpha ∈ MissingColors G phi v →
    ∃ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0
        ∧ StableColoring T (insert delta C) phi sigma ∧ TreeExit T sigma alpha delta v := by
  classical
  exact (by
  intro alpha halpha
  obtain ⟨pi, hpi, honepi, hstable, beta, hbetau, hbetat⟩ := hexists
  have hcriterion := (sc1 G e0 T (insert delta C) phi pi hproperPhi honePhi hpi honepi).mp hstable
  have ends_eq_of_mem : ∀ {z : Sym2 V} {x y : V}, x ∈ z → y ∈ z → x ≠ y → z = s(x, y) := by
    exact @helper_ends_eq_of_mem_61 (@V) (@E) inferInstance inferInstance (@G) (@k) (by assumption)
  have halphat : alpha ∈ TreeMissingColors phi T := by
    unfold TreeMissingColors
    simp only [Finset.mem_biUnion]
    exact ⟨v, hvin, halpha⟩
  have hbetat' : beta ∈ TreeMissingColors phi T := by
    exact @helper_hbetat_71 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@T) (@C)
        (@phi) (@delta) (@pi) (@hstable) (@beta) (@hbetat)
  have halphaClosed : ∀ {g}, g ∈ BoundaryEdges G (TreeSequenceVertexSet T) →
      ¬ phi g = some alpha := by
    intro g hgb hgc
    obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp halphat
    exact (hclosed hgb hw hgc) haw
  have hbetaClosed : ∀ {g}, g ∈ BoundaryEdges G (TreeSequenceVertexSet T) →
      ¬ phi g = some beta := by
    intro g hgb hgc
    obtain ⟨w, hw, hbw⟩ := Finset.mem_biUnion.mp hbetat'
    exact (hclosed hgb hw hgc) hbw
  let sigma := OutsideTreeColorSwap T pi alpha beta
  have tree_boundary : ∀ {e g : E}, TreeIncidentEdge T e →
      ¬ TreeIncidentEdge T g → AdjacentEdges G e g →
      e ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
    exact @helper_tree_boundary_91 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@T)
        (by assumption) (@ends_eq_of_mem)
  have tree_fixed : ∀ {e : E}, TreeIncidentEdge T e → sigma e = pi e := by
    intro e he
    simp [sigma, OutsideTreeColorSwap, he]
  have swap_injective := @helper_swap_injective_111 (@k) (@alpha) (@beta)
  refine ⟨sigma, ?_, ?_, ?_, ?_⟩
  · intro e g c hne hadj hec
    by_cases he : TreeIncidentEdge T e
    · exact @helper_branch_141 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@T) (@C)
        (@phi) (@delta) (@alpha) (@pi) (@hpi) (@beta) (@hcriterion) (@halphat) (@hbetat')
        (@halphaClosed) (@hbetaClosed) (@tree_boundary) (@tree_fixed) (@e) (@g) (@c) (@hne)
        (@hadj) (@hec) (@he)
    · exact @helper_branch_177 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@f) (@T)
        (@C) (@phi) (@u) (@v) (@delta) (@honePhi) (@hclosed) (@hfboundary) (@huout) (@hvin)
        (@alpha) (@pi) (@hpi) (@honepi) (@hstable) (@beta) (@hbetat) (@hcriterion) (@halphat)
        (@hbetat') (@halphaClosed) (@hbetaClosed) (@tree_boundary) (@tree_fixed)
        (@swap_injective) (@e) (@g) (@c) (@hne) (@hadj) (@hec) (@he)
  · exact @helper_branch_242 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@T) (@alpha)
      (@pi) (@honepi) (@beta)
  · exact @helper_branch_273 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@T) (@C)
      (@phi) (@delta) (@alpha) (@pi) (@hstable) (@beta) (@tree_fixed)
  · unfold TreeExit
    have hfincident : TreeIncidentEdge T f := by
      refine ⟨v, hvin, ?_⟩
      change v ∈ G.ends f
      rw [hfends]
      simp
    have hpif : pi f = some delta := by
      have hfix := hcriterion f hfincident
        (Or.inl ⟨delta, Finset.mem_union_right _ (Finset.mem_insert_self _ _), hfcolor⟩)
      exact hfix.trans hfcolor
    have hsf : sigma f = some delta := by
      rw [tree_fixed hfincident, hpif]
    have huf : Incident G u f := by
      change u ∈ G.ends f
      rw [hfends]
      simp
    have hvf : Incident G v f := by
      change v ∈ G.ends f
      rw [hfends]
      simp
    let p := SimpleGraph.Walk.cons
      (show (TwoColorIncidenceGraph G sigma alpha delta).Adj (Sum.inl u) (Sum.inr f) from by
        exact ⟨huf, Or.inr hsf⟩)
      (SimpleGraph.Walk.cons
        (show (TwoColorIncidenceGraph G sigma alpha delta).Adj (Sum.inr f) (Sum.inl v) from by
          exact ⟨hvf, Or.inr hsf⟩)
        SimpleGraph.Walk.nil)
    refine ⟨u, p, ?_⟩
    unfold TreeExitPath
    have halphau : alpha ∈ MissingColors G sigma u := by
      classical
      change alpha ∈ Finset.univ \ PresentColors G sigma u
      rw [Finset.mem_sdiff]
      constructor
      · exact Finset.mem_univ _
      · intro hpresent
        unfold PresentColors at hpresent
        obtain ⟨_, ⟨e, he, hse⟩⟩ := Finset.mem_filter.mp hpresent
        by_cases ht : TreeIncidentEdge T e
        · obtain ⟨x, hx, hxe⟩ := ht
          have htree : TreeIncidentEdge T e := ⟨x, hx, hxe⟩
          have hxu : x ≠ u := by
            intro h
            exact huout (h ▸ hx)
          have hb : e ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
            unfold BoundaryEdges
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨x, hx, u, huout, ends_eq_of_mem hxe he hxu⟩
          have hpi_e : pi e = some alpha := by
            simpa [tree_fixed ⟨x, hx, hxe⟩] using hse
          have hfix := hcriterion e htree
            (Or.inr ⟨alpha, Finset.mem_union_left _ halphat, hpi_e⟩)
          exact halphaClosed hb (hfix ▸ hpi_e)
        · have hbetanot : beta ∉ PresentColors G pi u := by
            exact (Finset.mem_sdiff.mp (show beta ∈ Finset.univ \ PresentColors G pi u from
                hbetau)).2
          by_cases ha : pi e = some alpha
          · have : pi e = some beta := by
              by_cases hab : alpha = beta
              · simpa [hab] using ha
              · exfalso
                have hbad : some beta = some alpha := by
                  simpa [sigma, OutsideTreeColorSwap, ht, ha, hab] using hse
                exact hab (Option.some.inj hbad).symm
            exact hbetanot (by
              unfold PresentColors
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e, he, this⟩⟩)
          · by_cases hb : pi e = some beta
            · exact hbetanot (by
                unfold PresentColors
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e, he, hb⟩⟩)
            · simp [sigma, OutsideTreeColorSwap, ht, ha, hb] at hse
    have hunotv : u ≠ v := by
      intro huv
      apply huout
      simpa [huv] using hvin
    have hpath : p.IsPath := by
      dsimp [p]
      apply SimpleGraph.Walk.IsPath.cons
      · apply SimpleGraph.Walk.IsPath.cons
        · simp
        · simp
      · simp [hunotv]
    refine ⟨hpath, ?_, huout, hvin, Or.inl halphau, ?_⟩
    · simp [p]
    · intro w hw
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          Sum.inl.injEq,
    reduceCtorEq, List.not_mem_nil, or_false, false_or, or_iff_right_iff_imp, p]
      intro hwu
      exact (huout (hwu ▸ hw)).elim
   )

end GoldbergSeymour

end
