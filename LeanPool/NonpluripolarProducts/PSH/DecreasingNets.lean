/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.Basic
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicLimits
public import Mathlib.Topology.Semicontinuity.Lindelof
public import Mathlib.Order.Directed

/-!
# Actual decreasing nets

The existing main-branch theorem proves stability for decreasing sequences.
Here a countable USC lower envelope is selected on the actual domain and its
actual indices are enlarged to a monotone sequence in the directed preorder.
This constructs the sequence; no countable cofinality of the index set is
assumed. Local integrability and convergence are proved in `SGPT.PSH.LocalL1`;
manifold gluing remains a separate obligation.
-/

@[expose] public section

namespace SGPT.PSH

open Set

/-- Every sequence of actual indices has a monotone pointwise majorant in
an upward-directed preorder. -/
theorem exists_monotone_index_majorant {I : Type*} [Preorder I] [IsDirectedOrder I]
    (v : ℕ → I) : ∃ a : ℕ → I, Monotone a ∧ ∀ n, v n ≤ a n := by
  classical
  choose c hleft hright using fun i j : I ↦ exists_ge_ge i j
  let a : ℕ → I := Nat.rec (v 0) (fun n i ↦ c i (v (n + 1)))
  have hstep (n : ℕ) : a (n + 1) = c (a n) (v (n + 1)) := rfl
  refine ⟨a, monotone_nat_of_le_succ (fun n ↦ ?_), ?_⟩
  · rw [hstep]
    exact hleft _ _
  · intro n
    cases n with
    | zero => exact le_rfl
    | succ n =>
      rw [hstep]
      exact hright _ _

/-- A decreasing family of actual USC extended-real functions on a
hereditarily Lindelöf space has a decreasing sequential subfamily with
exactly the same pointwise infimum. Its monotone indices are constructed
inside the original directed preorder. -/
theorem exists_monotone_subfamily_iInf {X I : Type*} [TopologicalSpace X]
    [HereditarilyLindelofSpace X] [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (u : I → X → EReal) (hu : ∀ i, UpperSemicontinuous (u i))
    (hanti : ∀ x, Antitone (fun i ↦ u i x)) :
    ∃ a : ℕ → I, Monotone a ∧
      ∀ x, (⨅ n, u (a n) x) = ⨅ i, u i x := by
  classical
  let F : Set (X → EReal) := range u
  let s : X → EReal := fun x ↦ ⨅ i, u i x
  have hF : IsGLB F s := by
    constructor
    · rintro f ⟨i, rfl⟩ x
      exact iInf_le (fun i ↦ u i x) i
    · intro f hf x
      exact le_iInf (fun i ↦ hf (mem_range_self i) x)
  obtain ⟨G, hGF, hcount, hG⟩ := exists_countable_upperSemicontinuous_isGLB
    (fun f hf ↦ by obtain ⟨i, rfl⟩ := hf; exact hu i) hF
  choose c hc using fun g : G ↦ hGF g.2
  let : Countable G := hcount.to_subtype
  let i₀ : I := Classical.arbitrary I
  let A : Set I := insert i₀ (range c)
  have hA : A.Nonempty := ⟨i₀, mem_insert _ _⟩
  have hAcount : A.Countable := (Set.countable_range c).insert i₀
  obtain ⟨v, hv⟩ := (Set.countable_iff_exists_surjective hA).mp hAcount
  obtain ⟨a, ha, hbound⟩ := exists_monotone_index_majorant (fun n ↦ (v n).1)
  refine ⟨a, ha, fun x ↦ le_antisymm ?_ ?_⟩
  · have hlower : (fun x ↦ ⨅ n, u (a n) x) ∈ lowerBounds G := by
      intro g hg x
      let g' : G := ⟨g, hg⟩
      have hcA : c g' ∈ A := mem_insert_of_mem _ (mem_range_self g')
      obtain ⟨n, hn⟩ := hv ⟨c g', hcA⟩
      have hvn : (v n).1 = c g' := congrArg Subtype.val hn
      have hc_le : c g' ≤ a n := by simpa only [hvn] using hbound n
      have hfun : u (c g') x = g x := congrFun (hc g') x
      exact (iInf_le (fun n ↦ u (a n) x) n).trans
        ((hanti x hc_le).trans_eq hfun)
    exact hG.2 hlower x
  · exact le_iInf (fun n ↦ iInf_le (fun i ↦ u i x) (a n))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SecondCountableTopology E]
variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- Genuine directed-net stability on the actual common domain. The
decreasing sequential subfamily is produced from USC restricted functions;
the integral-limit theorem is reused from the main branch. -/
theorem discPshOn_iInf_of_antitone {u : I → E → EReal} {U : Set E}
    (hu : ∀ i, SGPT.Foundations.Analysis.DiscPshOn (u i) U)
    (hanti : ∀ x ∈ U, Antitone (fun i ↦ u i x)) :
    SGPT.Foundations.Analysis.DiscPshOn (fun x ↦ ⨅ i, u i x) U := by
  obtain ⟨a, ha, heq⟩ := exists_monotone_subfamily_iInf
    (fun i (x : U) ↦ u i x)
    (fun i ↦ upperSemicontinuousOn_iff_restrict.mpr (hu i).upperSemicontinuousOn)
    (fun x ↦ hanti x.1 x.2)
  have hseq : SGPT.Foundations.Analysis.DiscPshOn (fun x ↦ ⨅ n, u (a n) x) U :=
    SGPT.Foundations.Analysis.DiscPshOn.iInf_of_antitone (fun n ↦ hu (a n))
      (fun x hx m n hmn ↦ hanti x hx (ha hmn))
  exact hseq.congr (fun x hx ↦ heq ⟨x, hx⟩)

/-- The PSH membership part of Xia's `prop:pshfunction_closedseq(2)` in the
Euclidean-domain `PSHOn` convention. The Lean statement uses one global
non-bottom witness. The manuscript requires one on each connected component
and also proves local `L¹` convergence. -/
theorem pshOn_iInf_of_antitone {u : I → E → EReal} {U : Set E}
    (hu : ∀ i, PSHOn (u i) U)
    (hanti : ∀ x ∈ U, Antitone (fun i ↦ u i x))
    (hn : ∃ x ∈ U, (⨅ i, u i x) ≠ ⊥) :
    PSHOn (fun x ↦ ⨅ i, u i x) U :=
  ⟨discPshOn_iInf_of_antitone (fun i ↦ (hu i).disc) hanti, hn⟩

/-- Actual source complex-line criterion for the same constructed directed
limit, obtained through the already proved disc-line equivalence. -/
theorem linePSHOn_iInf_of_antitone {u : I → E → EReal} {U : Set E}
    (hu : ∀ i, LinePSHOn (u i) U)
    (hanti : ∀ x ∈ U, Antitone (fun i ↦ u i x))
    (hn : ∃ x ∈ U, (⨅ i, u i x) ≠ ⊥) :
    LinePSHOn (fun x ↦ ⨅ i, u i x) U :=
  linePSHOn_of_pshOn (pshOn_iInf_of_antitone (fun i ↦ pshOn_of_linePSHOn (hu i))
    hanti hn)

/-- The actual decreasing-net limit is source PSH or is identically bottom
on its domain. The source proposition excludes the latter on each component. -/
theorem pshOn_iInf_or_eqOn_bot {u : I → E → EReal} {U : Set E}
    (hu : ∀ i, PSHOn (u i) U)
    (hanti : ∀ x ∈ U, Antitone (fun i ↦ u i x)) :
    PSHOn (fun x ↦ ⨅ i, u i x) U ∨ EqOn (fun x ↦ ⨅ i, u i x) (fun _ ↦ ⊥) U := by
  classical
  by_cases hn : ∃ x ∈ U, (⨅ i, u i x) ≠ ⊥
  · exact Or.inl (pshOn_iInf_of_antitone hu hanti hn)
  · right
    intro x hx
    by_contra h
    exact hn ⟨x, hx, h⟩

end SGPT.PSH
