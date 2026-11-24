/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.Basic
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicPullback

/-!
# Source holomorphic pullback dichotomy

The main branch now proves singular holomorphic pullback from actual radial
regularizations and smooth Levi naturality. Reuse that checked producer and
retain the source's non-bottom alternative explicitly. The namespace of an
public import does not substitute for a transitive axiom audit.

-/

@[expose] public section

namespace SGPT.PSH

open Set
open SGPT.Foundations.Analysis.FirstPass

/-- The actual singular pullback satisfies the genuine disc criterion. -/
theorem discPshOn_comp_holomorphic {k n : ℕ}
    {F : ComplexModel k → ComplexModel n} {u : ComplexModel n → EReal}
    {U : Set (ComplexModel k)} {V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hF : DifferentiableOn ℂ F U)
    (hFV : MapsTo F U V) (hu : PSHOn u V) :
    SGPT.Foundations.Analysis.DiscPshOn (fun x ↦ u (F x)) U :=
  (SGPT.Foundations.Analysis.Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
    hU hF hFV (hu.disc.plurisubharmonicOn hV)).discPshOn

/-- The pullback dichotomy of Xia's `prop:func_domain`, using the Lean
`PSHOn` convention on arbitrary opens. A witness anywhere in the source
suffices for the PSH alternative. For disconnected manifolds, the manuscript's
`prop:pullbackpsh` tests for an identically bottom component. -/
theorem pshOn_comp_holomorphic_or_eqOn_bot {k n : ℕ}
    {F : ComplexModel k → ComplexModel n} {u : ComplexModel n → EReal}
    {U : Set (ComplexModel k)} {V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hF : DifferentiableOn ℂ F U)
    (hFV : MapsTo F U V) (hu : PSHOn u V) :
    PSHOn (fun x ↦ u (F x)) U ∨ EqOn (fun x ↦ u (F x)) (fun _ ↦ ⊥) U := by
  classical
  by_cases hn : ∃ x ∈ U, u (F x) ≠ ⊥
  · exact Or.inl ⟨discPshOn_comp_holomorphic hU hV hF hFV hu, hn⟩
  · right
    intro x hx
    by_contra h
    exact hn ⟨x, hx, h⟩

/-- The two source alternatives are disjoint, including on empty domains. -/
theorem not_pshOn_and_eqOn_bot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → EReal} {U : Set E} :
    ¬ (PSHOn u U ∧ EqOn u (fun _ ↦ ⊥) U) := by
  rintro ⟨hu, hb⟩
  obtain ⟨x, hx, hn⟩ := hu.nontrivial
  exact hn (hb hx)

end SGPT.PSH
