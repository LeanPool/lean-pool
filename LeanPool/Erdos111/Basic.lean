/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Edge costs, linear graphs, rooted patterns

Signs are Boolean: a sign assignment is `τ : V → Bool`, and an edge is
monochromatic under `τ` when its two ends receive the same sign.

* `edgeCost E` is the least number of monochromatic edges of the finite edge set `E`
  over all sign assignments, the number of deletions that make `E` bipartite.
* `Linear G C` says that every finite edge set of `G` whose ends lie in `s` has
  `edgeCost` at most `C |s|`.
* A `Pattern` has roots `R`, new vertices `S` and edges `E`. Its extension cost
  `extCost P.S P.E τ` is the least number of monochromatic edges after the signs of
  `S` are chosen freely and the others are those of `τ`.
* `Rooted G C N ν` is the property `J` of the proof: every pattern over `N` has
  expected extension cost at most `C |S|` under the law `ν` of the signs.
* `SameOn A μ ν` says that `μ` and `ν` have the same finite-dimensional marginals on
  the coordinates in `A`.
* `TraceBound C ν v T` bounds the trace energy `∑ u ∈ T, ν (σ u = σ v)` by `C`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Erdos111

variable {V : Type*}

open Classical in
/-- `mono τ e` holds when both ends of `e` receive the same sign under `τ`. -/
def mono (τ : V → Bool) : Sym2 V → Prop :=
  Sym2.lift ⟨fun a b => τ a = τ b, fun _ _ => propext eq_comm⟩

open Classical in
/-- The number of edges of `E` that are monochromatic under `τ`. -/
noncomputable def monoCount (E : Finset (Sym2 V)) (τ : V → Bool) : ℕ :=
  (E.filter (mono τ)).card

open Classical in
/-- The least number of monochromatic edges of `E` over all sign assignments. -/
noncomputable def edgeCost (E : Finset (Sym2 V)) : ℕ :=
  ⨅ τ : V → Bool, monoCount E τ

open Classical in
/-- The least number of monochromatic edges of `E` when the signs on `S` are chosen
freely and every other vertex keeps its sign under `τ`. -/
noncomputable def extCost (S : Finset V) (E : Finset (Sym2 V)) (τ : V → Bool) : ℕ :=
  ⨅ η : V → Bool, monoCount E (S.piecewise η τ)

open Classical in
/-- `G` is `C`-linear: every finite set of edges of `G` with ends in `s` can be made
bipartite by deleting at most `C |s|` of them. -/
def Linear (G : SimpleGraph V) (C : ℝ≥0) : Prop :=
  ∀ (s : Finset V) (E : Finset (Sym2 V)), ↑E ⊆ G.edgeSet → (∀ e ∈ E, ∀ v ∈ e, v ∈ s) →
    (edgeCost E : ℝ≥0) ≤ C * s.card

open Classical in
/-- A rooted pattern: roots `R`, new vertices `S` and edges `E`. -/
structure Pattern (V : Type*) where
  /-- The roots, whose signs are given. -/
  R : Finset V
  /-- The new vertices, whose signs are chosen. -/
  S : Finset V
  /-- The edges, each meeting `S` and lying inside `R ∪ S`. -/
  E : Finset (Sym2 V)

open Classical in
/-- `P` is a pattern of `G` over `N`: its roots lie in `N`, its new vertices lie outside
`N`, and its edges are edges of `G` that meet `S` and lie inside `R ∪ S`. -/
structure Pattern.IsOver (G : SimpleGraph V) (N : Set V) (P : Pattern V) : Prop where
  roots_subset : ↑P.R ⊆ N
  new_not_mem : ∀ v ∈ P.S, v ∉ N
  edges_subset : ↑P.E ⊆ G.edgeSet
  edges_meet : ∀ e ∈ P.E, ∃ v ∈ e, v ∈ P.S
  edges_inside : ∀ e ∈ P.E, ∀ v ∈ e, v ∈ P.R ∨ v ∈ P.S

open Classical in
/-- The property `J`: every pattern of `G` over `N` has expected extension cost at most
`C |S|` under `ν`. -/
def Rooted (G : SimpleGraph V) (C : ℝ≥0) (N : Set V) (ν : Measure (V → Bool)) : Prop :=
  ∀ P : Pattern V, P.IsOver G N →
    ∫⁻ τ, (extCost P.S P.E τ : ℝ≥0∞) ∂ν ≤ C * P.S.card

open Classical in
/-- `μ` and `ν` have the same finite-dimensional marginals on the coordinates in `A`. -/
def SameOn (A : Set V) (μ ν : Measure (V → Bool)) : Prop :=
  ∀ J : Finset V, ↑J ⊆ A → μ.map J.restrict = ν.map J.restrict

open Classical in
/-- The trace energy of `v` over `T` is at most `C`: every finite `B ⊆ T` has
`∑ u ∈ B, ν (σ u = σ v) ≤ C`. -/
def TraceBound (C : ℝ≥0) (ν : Measure (V → Bool)) (v : V) (T : Set V) : Prop :=
  ∀ B : Finset V, ↑B ⊆ T → ∑ u ∈ B, ν {ω | ω u = ω v} ≤ C

/-! ### Basic properties -/

open Classical in
/-- A function of finitely many coordinates factors through the restriction to them. -/
theorem DependsOn.eq_comp_restrict {β : Type*} {f : (V → Bool) → β} {J : Finset V}
    (hf : DependsOn f J) (ω : V → Bool) :
    f ω = f (fun v => if h : v ∈ J then J.restrict ω ⟨v, h⟩ else true) :=
  hf fun i hi => by simp [Finset.mem_coe.mp hi]

open Classical in
/-- A function of finitely many coordinates is measurable. -/
theorem measurable_of_dependsOn {β : Type*} [MeasurableSpace β] {f : (V → Bool) → β}
    {J : Finset V} (hf : DependsOn f J) : Measurable f := by
  have hg : Measurable fun x : J → Bool => f fun v => if h : v ∈ J then x ⟨v, h⟩ else true :=
    measurable_of_finite _
  convert hg.comp (Finset.measurable_restrict (X := fun _ : V => Bool) J) using 1
  exact funext (DependsOn.eq_comp_restrict hf)

open Classical in
/-- The monochromatic count depends only on the signs at the ends of the edges. -/
theorem monoCount_congr {E : Finset (Sym2 V)} {τ τ' : V → Bool}
    (h : ∀ e ∈ E, ∀ v ∈ e, τ v = τ' v) : monoCount E τ = monoCount E τ' := by
  unfold monoCount
  congr 1
  refine Finset.filter_congr fun e he => ?_
  induction e using Sym2.ind with
  | h a b => simp [mono, h _ he a (Sym2.mem_mk_left a b), h _ he b (Sym2.mem_mk_right a b)]

open Classical in
/-- The extension cost depends only on the signs off `S` at the ends of the edges. -/
theorem extCost_dependsOn {S : Finset V} {E : Finset (Sym2 V)} {R : Finset V}
    (hE : ∀ e ∈ E, ∀ v ∈ e, v ∈ R ∨ v ∈ S) : DependsOn (extCost S E) R := by
  intro τ τ' h
  refine congrArg iInf (funext fun η => monoCount_congr fun e he v hv => ?_)
  rcases hE e he v hv with hR | hS
  · by_cases hvS : v ∈ S
    · simp [hvS]
    · simp [hvS, h v hR]
  · simp [hS]

open Classical in
/-- Some sign assignment attains the edge cost. -/
theorem exists_monoCount_eq_edgeCost (E : Finset (Sym2 V)) :
    ∃ σ : V → Bool, monoCount E σ = edgeCost E :=
  Nat.sInf_mem (Set.range_nonempty fun σ : V → Bool => monoCount E σ)

open Classical in
/-- Every sign assignment costs at least the edge cost. -/
theorem edgeCost_le_monoCount (E : Finset (Sym2 V)) (σ : V → Bool) :
    edgeCost E ≤ monoCount E σ :=
  ciInf_le (OrderBot.bddBelow _) σ

open Classical in
/-- The extension cost is at most the number of edges. -/
theorem extCost_le_card (S : Finset V) (E : Finset (Sym2 V)) (τ : V → Bool) :
    extCost S E τ ≤ E.card :=
  (ciInf_le (OrderBot.bddBelow _) τ).trans (Finset.card_filter_le _ _)

open Classical in
/-- Some choice of the signs on `S` attains the extension cost. -/
theorem exists_extCost_eq (S : Finset V) (E : Finset (Sym2 V)) (τ : V → Bool) :
    ∃ η : V → Bool, monoCount E (S.piecewise η τ) = extCost S E τ :=
  Nat.sInf_mem (Set.range_nonempty _)

open Classical in
/-- Every choice of the signs on `S` costs at least the extension cost. -/
theorem extCost_le_monoCount (S : Finset V) (E : Finset (Sym2 V)) (τ η : V → Bool) :
    extCost S E τ ≤ monoCount E (S.piecewise η τ) :=
  ciInf_le (OrderBot.bddBelow _) η

open Classical in
/-- A linear graph satisfies `J` over the empty set, for every probability law: a pattern
with no roots costs at most `C |S|` whatever the signs. -/
theorem rooted_empty {G : SimpleGraph V} {C : ℝ≥0} (hG : Linear G C)
    (ν : Measure (V → Bool)) [IsProbabilityMeasure ν] : Rooted G C ∅ ν := by
  intro P hP
  have hS : ∀ e ∈ P.E, ∀ v ∈ e, v ∈ P.S := fun e he v hv =>
    (hP.edges_inside e he v hv).resolve_left fun hR => hP.roots_subset hR
  have hle : ∀ τ, extCost P.S P.E τ ≤ edgeCost P.E := fun τ =>
    le_ciInf fun σ => (extCost_le_monoCount P.S P.E τ σ).trans_eq
      (monoCount_congr fun e he v hv => by simp [hS e he v hv])
  have hC := hG P.S P.E hP.edges_subset hS
  calc ∫⁻ τ, (extCost P.S P.E τ : ℝ≥0∞) ∂ν ≤ ∫⁻ _, (edgeCost P.E : ℝ≥0∞) ∂ν :=
        lintegral_mono fun τ => Nat.mono_cast (hle τ)
    _ = edgeCost P.E := by simp
    _ ≤ C * P.S.card := by exact_mod_cast hC

open Classical in
/-- Laws with the same finite marginals on `A` integrate a function of finitely many
coordinates of `A` alike. -/
theorem SameOn.lintegral_eq {A : Set V} {μ ν : Measure (V → Bool)} (h : SameOn A μ ν)
    {f : (V → Bool) → ℝ≥0∞} {J : Finset V} (hf : DependsOn f J) (hJ : ↑J ⊆ A) :
    ∫⁻ ω, f ω ∂μ = ∫⁻ ω, f ω ∂ν := by
  obtain ⟨g, hg, e⟩ : ∃ g : (J → Bool) → ℝ≥0∞, Measurable g ∧ ∀ ω, f ω = g (J.restrict ω) :=
    ⟨fun x => f fun v => if h : v ∈ J then x ⟨v, h⟩ else true, measurable_of_finite _,
      DependsOn.eq_comp_restrict hf⟩
  have hJm := Finset.measurable_restrict (X := fun _ : V => Bool) J
  rw [lintegral_congr e, lintegral_congr e, ← lintegral_map hg hJm, ← lintegral_map hg hJm,
    h J hJ]

open Classical in
/-- `J` over `N` depends only on the finite marginals on `N`. -/
theorem Rooted.of_sameOn {G : SimpleGraph V} {C : ℝ≥0} {N : Set V}
    {μ ν : Measure (V → Bool)} (hμ : Rooted G C N μ) (h : SameOn N μ ν) :
    Rooted G C N ν := by
  intro P hP
  rw [← h.lintegral_eq (fun _ _ hxy => congrArg _ (extCost_dependsOn hP.edges_inside hxy))
    hP.roots_subset]
  exact hμ P hP

open Classical in
/-- A trace bound depends only on the finite marginals on the trace and the vertex. -/
theorem TraceBound.of_sameOn {C : ℝ≥0} {A T : Set V} {v : V}
    {μ ν : Measure (V → Bool)} (hμ : TraceBound C μ v T) (h : SameOn A μ ν)
    (hv : v ∈ A) (hT : T ⊆ A) : TraceBound C ν v T := by
  intro B hB
  have key : ∀ u ∈ B, ν {ω | ω u = ω v} = μ {ω | ω u = ω v} := by
    intro u hu
    have hJ : ↑({u, v} : Finset V) ⊆ A := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hT (hB hu)
      · rw [Finset.mem_singleton.mp hx]
        exact hv
    have hS : {ω : V → Bool | ω u = ω v} = ({u, v} : Finset V).restrict ⁻¹'
        {x | x ⟨u, by simp⟩ = x ⟨v, by simp⟩} := rfl
    rw [hS, ← Measure.map_apply (Finset.measurable_restrict _) (Set.toFinite _).measurableSet,
      ← Measure.map_apply (Finset.measurable_restrict _) (Set.toFinite _).measurableSet,
      h _ hJ]
  rw [Finset.sum_congr rfl key]
  exact hμ B hB

open Classical in
/-- Agreement of finite marginals is transitive. -/
theorem SameOn.trans {A : Set V} {μ ν ρ : Measure (V → Bool)} (h₁ : SameOn A μ ν)
    (h₂ : SameOn A ν ρ) : SameOn A μ ρ :=
  fun J hJ => (h₁ J hJ).trans (h₂ J hJ)

open Classical in
/-- Agreement of finite marginals on `A` gives agreement on every subset of `A`. -/
theorem SameOn.mono {A B : Set V} {μ ν : Measure (V → Bool)} (h : SameOn A μ ν)
    (hBA : B ⊆ A) : SameOn B μ ν :=
  fun J hJ => h J (hJ.trans hBA)

end Erdos111
