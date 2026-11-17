/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import LeanPool.Erdos111.Chain
public import LeanPool.Erdos111.Successor

/-!
# The limit law (Proposition L)

For a linear graph and a chain, there is one law of the signs under which every vertex
with infinite trace has trace energy at most `C`.

*Proof.* By induction on `ξ`, there is a law satisfying `J` over every `N ζ` with
`ζ ≤ ξ` and the trace bound at every vertex of layer below `ξ` with infinite trace. Any
law satisfies `J` over `N 0 = ∅`. The successor step applies Lemma S to `N ξ ⊆ N (ξ + 1)`;
the new law has the old marginals on `N ξ`, which carry `J` over each earlier `N ζ` and
the earlier trace bounds. At a limit, every condition is closed and finite-dimensional,
and holds from some stage on, so a limit along an ultrafilter keeps them all; a pattern
over the union has its finitely many roots in an earlier set. At `(#V).ord` every vertex
has its layer below.
-/

@[expose] public section

open MeasureTheory Cardinal
open scoped ENNReal NNReal

universe u

namespace Erdos111

variable {V : Type u}

/-- Proposition L: one law gives every vertex with infinite trace trace energy at most
`C`. -/
theorem exists_traceBound_law {G : SimpleGraph V} {C : ℝ≥0} (hG : Linear G C)
    (c : Chain G) :
    ∃ ν : Measure (V → Bool), IsProbabilityMeasure ν ∧
      ∀ v, (c.trace v).Infinite → TraceBound C ν v (c.trace v) := by
  have key : ∀ ξ, ∃ ν : Measure (V → Bool), IsProbabilityMeasure ν ∧
      (∀ ζ ≤ ξ, Rooted G C (c.N ζ) ν) ∧
      ∀ v, c.layer v < ξ → (c.trace v).Infinite → TraceBound C ν v (c.trace v) := by
    intro ξ
    induction ξ using WellFoundedLT.induction with | ind ξ IH
    rcases Ordinal.zero_or_succ_or_isSuccLimit ξ with rfl | ⟨o, rfl⟩ | hξ
    · refine ⟨Measure.dirac fun _ => true, inferInstance, fun ζ hζ => ?_,
        fun v hv => (not_lt_zero hv).elim⟩
      rw [nonpos_iff_eq_zero.1 hζ, c.zero]
      exact rooted_empty hG _
    · obtain ⟨ν, hν, hR, hT⟩ := IH o (Order.lt_succ o)
      have := hν
      obtain ⟨ν', hν', hsame, hR', hT'⟩ := exists_successor (c.succ o) (hR o le_rfl)
      refine ⟨ν', hν', fun ζ hζ => ?_, fun v hv hinf => ?_⟩
      · rcases hζ.lt_or_eq with hζ | rfl
        · exact (hR ζ (Order.lt_succ_iff.1 hζ)).of_sameOn
            (hsame.mono (c.mono (Order.lt_succ_iff.1 hζ)))
        · rwa [Order.succ_eq_add_one]
      · rcases (Order.lt_succ_iff.1 hv).lt_or_eq with hv | hv
        · exact (hT v hv hinf).of_sameOn hsame (c.mem_N_iff.2 hv) fun u hu => c.mono hv.le hu.2
        · have htr : c.trace v = {u | G.Adj v u ∧ u ∈ c.N o} := by rw [Chain.trace, hv]
          rw [htr] at hinf ⊢
          refine hT' v ⟨?_, ?_⟩ hinf
          · rw [← Order.succ_eq_add_one, c.mem_N_iff, hv]
            exact Order.lt_succ o
          · rw [c.mem_N_iff, hv]
            exact lt_irrefl o
    · choose ν hν hR hT using fun ζ : Set.Iio ξ => IH ζ.1 ζ.2
      have := hν
      have : Nonempty (Set.Iio ξ) := ⟨⟨0, hξ.pos⟩⟩
      obtain ⟨μ, hμ, hlim⟩ :=
        exists_limit (Ultrafilter.of (Filter.atTop : Filter (Set.Iio ξ))) ν
      refine ⟨μ, hμ, fun ζ' hζ' => rooted_of_tendsto hlim fun P hP => ?_,
        fun v hv hinf => traceBound_of_tendsto hlim (Ultrafilter.of_le _ ?_)⟩
      · set ζ₀ := P.R.sup fun v => Order.succ (c.layer v)
        have hR₀ : ∀ v ∈ P.R, c.layer v < ζ' := fun v hv => c.mem_N_iff.1 (hP.roots_subset hv)
        have h₀ : ζ₀ ≤ ζ' := Finset.sup_le fun v hv => Order.succ_le_of_lt (hR₀ v hv)
        have h₀ξ : ζ₀ < ξ := (Finset.sup_lt_iff hξ.bot_lt).2 fun v hv =>
          hξ.succ_lt ((hR₀ v hv).trans_le hζ')
        have hP₀ : P.IsOver G (c.N ζ₀) :=
          { hP with
            roots_subset := fun v hv => c.mem_N_iff.2 ((Order.lt_succ _).trans_le
              (Finset.le_sup (f := fun v => Order.succ (c.layer v)) hv))
            new_not_mem := fun v hv hv₀ => hP.new_not_mem v hv (c.mono h₀ hv₀) }
        exact Ultrafilter.of_le _ ((Filter.eventually_ge_atTop ⟨ζ₀, h₀ξ⟩).mono
          fun ζ hζ => hR ζ ζ₀ hζ P hP₀)
      · exact (Filter.eventually_ge_atTop ⟨Order.succ (c.layer v), hξ.succ_lt hv⟩).mono
          fun ζ hζ => hT ζ v ((Order.lt_succ _).trans_le hζ) hinf
  obtain ⟨ν, hν, -, hT⟩ := key (#V).ord
  exact ⟨ν, hν, fun v hinf => hT v (c.layer_lt_ord v) hinf⟩

end Erdos111
