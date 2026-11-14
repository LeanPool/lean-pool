/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import LeanPool.Erdos111.Probability.Limit
public import LeanPool.Erdos111.Successor.Key
public import LeanPool.Erdos111.Successor.Mixture

/-!
# The successor step (Lemma S)

Let `N` be closed over `M` and let `ν` satisfy `J` over `M`. There is a law `ν'` with
the marginals of `ν` on `M`, satisfying `J` over `N`, under which every vertex of
`N \ M` with infinitely many neighbours in `M` has trace energy at most `C` over them.

*Proof.* Force the signs of the set `X` of such vertices, giving the law
`Λ = ν.map (forced X s)`. For each finite family of patterns over `N`, the key inequality
and the mixture lemma give a law with the marginals of `Λ` on `M ∪ X` meeting `J` for
those patterns. A limit along an ultrafilter finer than the filter of finite families
keeps the marginals on `M ∪ X` and meets `J` for every pattern over `N`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Erdos111

variable {V : Type*}

open Classical in
/-- For one finite family of patterns over `N`, the mixture lemma gives a law with the
marginals of the forced law on `M ∪ X` meeting `J` for the patterns of the family. -/
theorem exists_law_of_finset {G : SimpleGraph V} {C : ℝ≥0} {M N X : Set V}
    (hMN : ClosedOver G M N) {ν : Measure (V → Bool)}
    (hν : Rooted G C M ν) (hX : X ⊆ N \ M) (d : ForcingData G C M X ν)
    [IsProbabilityMeasure (ν.map (forced X d.s))] (F : Finset (Pattern V)) :
    ∃ μ : Measure (V → Bool), IsProbabilityMeasure μ ∧
      SameOn (M ∪ X) (ν.map (forced X d.s)) μ ∧
      ∀ P ∈ F, P.IsOver G N → ∫⁻ τ, (extCost P.S P.E τ : ℝ≥0∞) ∂μ ≤ C * P.S.card := by
  set L := F.filter (fun P => P.IsOver G N)
  let e := L.equivFin
  let P : Fin L.card → Pattern V := fun i => (e.symm i).1
  have hP : ∀ i, (P i).IsOver G N := fun i => (Finset.mem_filter.1 (e.symm i).2).2
  set roots := L.biUnion Pattern.R
  set U := roots.filter (· ∈ M ∪ X)
  set W := roots.filter (· ∉ M ∪ X)
  have hroots : ∀ i, ∀ v ∈ (P i).R, v ∈ roots := fun i v hv =>
    Finset.mem_biUnion.2 ⟨(e.symm i).1, (e.symm i).2, hv⟩
  have hW : ∀ w ∈ W, w ∉ M ∪ X := fun w hw => (Finset.mem_filter.1 hw).2
  have hWN : (↑W : Set V) ⊆ N \ M := by
    intro w hw
    obtain ⟨hw, hwMX⟩ := Finset.mem_filter.1 hw
    obtain ⟨Q, hQ, hwQ⟩ := Finset.mem_biUnion.1 hw
    exact ⟨(Finset.mem_filter.1 hQ).2.roots_subset hwQ, fun h => hwMX (Or.inl h)⟩
  have hf : ∀ i, DependsOn (extCost (P i).S (P i).E) (↑U ∪ ↑W) := by
    intro i
    rw [← Finset.coe_union]
    refine extCost_dependsOn fun e he v hv => ?_
    rcases (hP i).edges_inside e he v hv with h | h
    · left
      by_cases hv' : v ∈ M ∪ X
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hroots i v h, hv'⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hroots i v h, hv'⟩)
    · exact Or.inr h
  have hc : ∀ i, ((C * (P i).S.card : ℝ≥0) : ℝ≥0∞) = C * (P i).S.card := by
    intro i
    push_cast
    rfl
  obtain ⟨μ, hμ, hsame, hbound⟩ := exists_mixture (ν.map (forced X d.s)) (M ∪ X) U W hW
    (fun i => extCost (P i).S (P i).E) hf (fun i => C * (P i).S.card) (by
      intro ρ
      have hdep : DependsOn (fun τ => ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) *
          (extCost (P i).S (P i).E (W.piecewise η τ) : ℝ≥0∞)) ↑(U ∪ W) := by
        intro τ τ' h
        refine iInf_congr fun η => Finset.sum_congr rfl fun i _ => ?_
        have hτ : ∀ v ∈ (↑U ∪ ↑W : Set V), W.piecewise η τ v = W.piecewise η τ' v := by
          intro v hv
          by_cases hvW : v ∈ W
          · simp [Finset.piecewise_eq_of_mem _ _ _ hvW]
          · rw [Finset.piecewise_eq_of_notMem _ _ _ hvW,
              Finset.piecewise_eq_of_notMem _ _ _ hvW]
            exact h v (by simpa [Finset.coe_union] using hv)
        rw [hf i hτ]
      rw [lintegral_map (measurable_of_dependsOn hdep) (measurable_forced d)]
      simp only [hc]
      exact key_inequality hMN hν hX d P hP W
        (fun i v hv => by
          by_cases hv' : v ∈ M ∪ X
          · rcases hv' with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Finset.mem_filter.2 ⟨hroots i v hv, hv'⟩)))
        hWN ρ)
  refine ⟨μ, hμ, hsame, fun Q hQF hQ => ?_⟩
  have hQL : Q ∈ L := Finset.mem_filter.2 ⟨hQF, hQ⟩
  have h := hbound (e ⟨Q, hQL⟩)
  have hPQ : P (e ⟨Q, hQL⟩) = Q := by simp [P]
  rw [hc, hPQ] at h
  exact h

open Classical in
/-- Lemma S. -/
theorem exists_successor {G : SimpleGraph V} {C : ℝ≥0} {M N : Set V}
    (hMN : ClosedOver G M N) {ν : Measure (V → Bool)} [IsProbabilityMeasure ν]
    (hν : Rooted G C M ν) :
    ∃ ν' : Measure (V → Bool), IsProbabilityMeasure ν' ∧ SameOn M ν ν' ∧
      Rooted G C N ν' ∧
      ∀ y ∈ N \ M, {u | G.Adj y u ∧ u ∈ M}.Infinite →
        TraceBound C ν' y {u | G.Adj y u ∧ u ∈ M} := by
  set X : Set V := {y | y ∈ N \ M ∧ {u | G.Adj y u ∧ u ∈ M}.Infinite}
  have hXNM : X ⊆ N \ M := fun y hy => hy.1
  have hXM : Disjoint X M := Set.disjoint_left.2 fun y hy hyM => hy.1.2 hyM
  let d := (exists_forcingData hν (X := X) fun y hy => ⟨hy.1.2, hy.2⟩).some
  have : IsProbabilityMeasure (ν.map (forced X d.s)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_forced d).aemeasurable).2 inferInstance
  choose μ hμ hsame hbound using exists_law_of_finset hMN hν hXNM d
  have := hμ
  obtain ⟨ν', hν', hlim⟩ :=
    exists_limit (Ultrafilter.of (Filter.atTop : Filter (Finset (Pattern V)))) μ
  have := hν'
  have hΛ : SameOn (M ∪ X) (ν.map (forced X d.s)) ν' :=
    sameOn_of_tendsto hlim (Filter.Eventually.of_forall hsame)
  refine ⟨ν', hν', (sameOn_map_forced d hXM).trans (hΛ.mono Set.subset_union_left),
    rooted_of_tendsto hlim fun P hP => Ultrafilter.of_le _ ?_, fun y hy hinf => ?_⟩
  · exact (Filter.eventually_ge_atTop {P}).mono fun F hF =>
      hbound F P (hF (Finset.mem_singleton_self P)) hP
  · have hyX : y ∈ X := ⟨hy, hinf⟩
    exact (traceBound_map_forced d hXM hyX).of_sameOn hΛ (Or.inr hyX)
      fun u hu => Or.inl hu.2

end Erdos111
