/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticMultilinearClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Non quadratic multilinear closure

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `continuousMultilinear_mem_of_closed_factor_spans`.
-/

@[expose] public section

namespace GinibrePoincare
noncomputable section

/-- A closed linear target containing multilinear products of generators
contains products from each actual closed linear span. -/
theorem continuousMultilinear_mem_of_closed_factor_spans
    {ι : Type*} [Finite ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (M : ContinuousMultilinearMap ℂ E H) (S : ∀ i, Set (E i))
    (K : Submodule ℂ H) (hK : IsClosed (K : Set H))
    (hb : ∀ u : ∀ i, E i, (∀ i, u i ∈ S i) → M u ∈ K)
    (u : ∀ i, E i) (hu : ∀ i, u i ∈ (Submodule.span ℂ (S i)).topologicalClosure) : M u ∈ K := by
  classical
  have := Fintype.ofFinite ι
  have hh (s : Finset ι) : ∀ v : ∀ i, E i,
      (∀ i ∈ s, v i ∈ (Submodule.span ℂ (S i)).topologicalClosure) →
      (∀ i ∉ s, v i ∈ S i) → M v ∈ K := by
    induction s using Finset.induction_on with
    | empty =>
      intro v _ hv
      exact hb v (fun i => hv i (by simp))
    | @insert i s his ih =>
      intro v hv hs
      let L : E i →L[ℂ] H :=
        { __ := M.toMultilinearMap.toLinearMap v i
          cont := M.cont.comp (continuous_const.update i continuous_id) }
      let A := K.comap L.toLinearMap
      have hA : IsClosed (A : Set (E i)) := hK.preimage L.continuous
      have hbase : S i ⊆ A := by
        intro a ha
        apply ih (Function.update v i a)
        · intro j hjs
          rw [Function.update_of_ne (show j ≠ i from fun h => his (h ▸ hjs))]
          exact hv j (Finset.mem_insert_of_mem hjs)
        · intro j hjs
          by_cases hji : j = i
          · subst j
            simpa only [Function.update_self] using ha
          · rw [Function.update_of_ne hji]
            exact hs j (by simp [hjs, hji])
      have hspan : Submodule.span ℂ (S i) ≤ A := Submodule.span_le.mpr hbase
      have hvi : v i ∈ A := hA.closure_subset_iff.mpr hspan (hv i (Finset.mem_insert_self ..))
      change M (Function.update v i (v i)) ∈ K at hvi
      simpa only [Function.update_eq_self] using hvi
  exact hh Finset.univ u (fun i _ => hu i) (fun i hi => False.elim (hi (Finset.mem_univ i)))
end
end GinibrePoincare
