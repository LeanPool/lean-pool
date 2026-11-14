/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordRecursiveVertexDomains
public import LeanPool.ApollonianSuperharmonic.FordVertexDomain

-- [TABLET NODE: P5130T5DomainCover]

/-!
# P5130T5DomainCover

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5130T5DomainCover (P : FordFareyParameter) :
    (∀ x ∈ FordVertexDomain P.q, ∃ i, x ∈ FordRecursiveVertexDomains P i) ∧
    (∀ i x, x ∈ FordRecursiveVertexDomains P i → x ∈ FordVertexDomain P.q) := by
-- BODY
  have hs : (P.q : Int) = P.q₁ + P.q₂ := by exact_mod_cast P.sum_q
  constructor
  · intro x hx
    rcases hx with ⟨ha, hb, hc, hd⟩
    by_cases h₁ : x.re ≤ (P.q₁ : Int) ∧ x.im ≤ (P.q₁ : Int)
    · exact ⟨0, by simpa [FordRecursiveVertexDomains] using ⟨ha, h₁.1, hc, h₁.2⟩⟩
    by_cases h₂ : (P.q₂ : Int) ≤ x.re ∧ (P.q₂ : Int) ≤ x.im
    · exact ⟨1, by simpa [FordRecursiveVertexDomains] using ⟨h₂.1, hb, h₂.2, hd⟩⟩
    by_cases h₃ : (P.q₁ : Int) ≤ x.re ∧ x.im ≤ (P.q₂ : Int)
    · exact ⟨2, by simpa [FordRecursiveVertexDomains] using ⟨h₃.1, hb, hc, h₃.2⟩⟩
    · exact ⟨3, by simp [FordRecursiveVertexDomains]; omega⟩
  · intro i x hx
    fin_cases i <;> simp [FordRecursiveVertexDomains] at hx <;>
      simp only [FordVertexDomain, Set.mem_ofPred_eq] <;> omega

end ApollonianSuperharmonic

end
