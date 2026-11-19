/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/EntireVandermondeFactorization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.EntireVandermondeDivision
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarWeakDomain
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireHyperplaneDivision

/-! # Entire factorization across all collision hyperplanes

Start with the one-hyperplane division theorem in
`GaussianEntireHyperplaneDivision`. To iterate it, the quotient must still
vanish on each remaining collision hyperplane. The first lemma proves this by
moving along a direction within that hyperplane but transverse to the factor
already divided out, then using continuity at the intersection.

Distinct ordered collision pairs admit such a coordinate direction. Finite-set
induction therefore divides out every factor exactly once, and their product is
the Vandermonde polynomial. Alternation supplies collision vanishing; uniqueness
of continuous quotients from `EntireVandermondeDivision` supplies symmetry.
The last theorem applies this pointwise argument to entire representatives of
alternating Gaussian L² classes.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators
namespace GinibrePoincare
noncomputable section

/-- The complex-linear form `z ↦ z p.2 - z p.1`, whose zero set is the collision hyperplane of
the pair `p`. -/
def collisionLinearForm {n : ℕ} (p : Fin n × Fin n) : Configuration n →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj p.2 : Configuration n →L[ℂ] ℂ) -
    (ContinuousLinearMap.proj p.1 : Configuration n →L[ℂ] ℂ)

@[simp] theorem collisionLinearForm_apply {n : ℕ} (p : Fin n × Fin n) (z : Configuration n) :
    collisionLinearForm p z = z p.2 - z p.1 := rfl

/-- Division by one linear factor preserves vanishing on a transverse
 hyperplane, by continuity along a line inside that hyperplane. -/
theorem entire_linearDivision_preserves_hyperplane_zero {n : ℕ}
    (a b : Configuration n →L[ℂ] ℂ) (v : Configuration n)
    (hav : a v ≠ 0) (hbv : b v = 0)
    (f g : Configuration n → ℂ) (hg : Continuous g)
    (hfac : ∀ z, f z = a z * g z) (hz : ∀ z, b z = 0 → f z = 0) :
    ∀ z, b z = 0 → g z = 0 := by
  intro z hzb
  by_cases hza : a z = 0
  · let τ : ℕ → ℂ := fun m => (((m : ℝ) + 1)⁻¹ : ℝ)
    have ht : Tendsto τ atTop (𝓝 0) := by
      have hr : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
      exact Complex.continuous_ofReal.tendsto 0 |>.comp hr
    have hτ (m : ℕ) : τ m ≠ 0 := by
      dsimp [τ]
      exact_mod_cast (inv_ne_zero (show (m : ℝ) + 1 ≠ 0 by positivity))
    have hzero (m : ℕ) : g (z + τ m • v) = 0 := by
      have hfb : f (z + τ m • v) = 0 := hz _ (by simp [map_add, map_smul, hzb, hbv])
      have haa : a (z + τ m • v) ≠ 0 := by
        simp only [map_add, map_smul, hza, zero_add, smul_eq_mul]
        exact mul_ne_zero (hτ m) hav
      exact (mul_eq_zero.mp ((hfac _).symm.trans hfb)).resolve_left haa
    have htz : Tendsto (fun m => z + τ m • v) atTop (𝓝 z) := by
      simpa using tendsto_const_nhds.add (ht.smul_const v)
    have htg : Tendsto (fun m => g (z + τ m • v)) atTop (𝓝 (g z)) :=
      (hg.tendsto z).comp htz
    exact tendsto_nhds_unique htg (by simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  · exact (mul_eq_zero.mp ((hfac z).symm.trans (hz z hzb))).resolve_left hza

/-- Unequal ordered collision pairs admit a coordinate direction contained
 in the second hyperplane and transverse to the first. -/
theorem collisionPairs_transverse_direction {n : ℕ} (a b : Fin n × Fin n)
    (ha : a.1 < a.2) (hb : b.1 < b.2) (hne : a ≠ b) :
    ∃ v : Configuration n, collisionLinearForm a v ≠ 0 ∧ collisionLinearForm b v = 0 := by
  have hk : ∃ k : Fin n, (k = a.1 ∨ k = a.2) ∧ k ≠ b.1 ∧ k ≠ b.2 := by
    by_cases hi : a.1 = b.1
    · refine ⟨a.2, Or.inr rfl, ?_, ?_⟩
      · rw [← hi]
        exact ha.ne'
      · intro hj
        exact hne (Prod.ext hi hj)
    · by_cases hij : a.1 = b.2
      · refine ⟨a.2, Or.inr rfl, ?_, ?_⟩
        · exact (hb.trans (hij ▸ ha)).ne'
        · rw [← hij]
          exact ha.ne'
      · exact ⟨a.1, Or.inl rfl, hi, hij⟩
  obtain ⟨k, hk, hk₁, hk₂⟩ := hk
  refine ⟨Pi.single k 1, ?_, ?_⟩
  · rcases hk with rfl | rfl
    · simp [collisionLinearForm, ha.ne']
    · simp [collisionLinearForm, ha.ne]
  · simp [collisionLinearForm, Ne.symm hk₁, Ne.symm hk₂]

/-- The ordered index pairs `(i, j)` with `i < j`, one for each Vandermonde factor. -/
def collisionPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

theorem collisionPairs_product_eq_vandermonde (n : ℕ) (z : Configuration n) :
    (∏ p ∈ collisionPairs n, collisionLinearForm p z) = vandermonde z := by
  rw [vandermonde_eq_product]
  unfold collisionPairs
  rw [Finset.prod_filter]
  change (∏ p : Fin n × Fin n, if p.1 < p.2 then z p.2 - z p.1 else 1) = _
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

/-- Simultaneous entire division by finitely many distinct ordered collision
 factors, preserving all remaining collision vanishing obligations. -/
theorem entire_division_collisionFactors (n : ℕ) (s : Finset (Fin n × Fin n))
    (hs : ∀ p ∈ s, p.1 < p.2)
    (f : Configuration n → ℂ) (hf : Differentiable ℂ f)
    (hz : ∀ p ∈ s, ∀ z, collisionLinearForm p z = 0 → f z = 0) :
    ∃ g : Configuration n → ℂ, Differentiable ℂ g ∧
      ∀ z, f z = (∏ p ∈ s, collisionLinearForm p z) * g z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => exact ⟨f, hf, fun z => by simp⟩
  | @insert a s has ih =>
    have ha : a.1 < a.2 := hs a (Finset.mem_insert_self _ _)
    have hv : collisionLinearForm a (Pi.single a.2 1) = 1 := by
      simp [collisionLinearForm, ha.ne]
    obtain ⟨h, hh, hfh⟩ := gaussian_entire_hyperplane_division
      (collisionLinearForm a) (Pi.single a.2 1) hv f hf
      (hz a (Finset.mem_insert_self _ _))
    have hs' : ∀ p ∈ s, p.1 < p.2 := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hzh : ∀ b ∈ s, ∀ z, collisionLinearForm b z = 0 → h z = 0 := by
      intro b hb
      obtain ⟨v, hva, hvb⟩ := collisionPairs_transverse_direction a b ha (hs' b hb)
        (fun he => has (he ▸ hb))
      exact entire_linearDivision_preserves_hyperplane_zero (collisionLinearForm a)
        (collisionLinearForm b) v hva hvb f h hh.continuous hfh
        (hz b (Finset.mem_insert_of_mem hb))
    obtain ⟨g, hg, hhg⟩ := ih hs' h hh hzh
    refine ⟨g, hg, ?_⟩
    intro z
    rw [hfh, hhg, Finset.prod_insert has]
    ring

/-- Arbitrary entire alternating functions admit a global entire symmetric
 Vandermonde quotient across all collision hyperplanes. -/
theorem entire_alternating_vandermonde_factorization {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℂ) (hf : Differentiable ℂ f) (ha : IsAlternating f) :
    ∃ g : Configuration n → ℂ, Differentiable ℂ g ∧ IsSymmetric g ∧
      ∀ z, f z = vandermonde z * g z := by
  have hs : ∀ p ∈ collisionPairs n, p.1 < p.2 := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hz : ∀ p ∈ collisionPairs n, ∀ z, collisionLinearForm p z = 0 → f z = 0 := by
    intro p hp z hz
    apply alternating_function_eq_zero_on_collision ha
    refine ⟨p.1, p.2, ?_, (hs p hp).ne⟩
    exact (sub_eq_zero.mp hz).symm
  obtain ⟨g, hg, hfg⟩ := entire_division_collisionFactors n (collisionPairs n) hs f hf hz
  have hfactor : ∀ z, f z = vandermonde z * g z := by
    intro z
    rw [hfg, collisionPairs_product_eq_vandermonde]
  exact ⟨g, hg, continuous_vandermonde_quotient_symmetric hn ha hg.continuous hfactor, hfactor⟩

/-- Entire representatives of actual alternating Gaussian L² classes have
 actual entire symmetric Vandermonde quotients. -/
theorem gaussianEntireAlternatingRepresentative_vandermonde_factorization {n : ℕ}
    (hn : 0 < n) (u : Lp ℂ 2 (complexGaussianMeasure n))
    (hu : u ∈ gaussianAlternatingL2 n) (f : Configuration n → ℂ)
    (hf : IsGaussianEntireRepresentative u f) :
    ∃ g : Configuration n → ℂ, Differentiable ℂ g ∧ IsSymmetric g ∧
      ∀ z, f z = vandermonde z * g z :=
  entire_alternating_vandermonde_factorization hn f hf.1
    (gaussianEntireRepresentative_alternating hn hu hf)

end
end GinibrePoincare

