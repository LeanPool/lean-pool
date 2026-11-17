/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.SupportingPlane

/-!
# Affine subtraction from extended-real potentials

`affineSubtract a b φ x = φ x - (⟪a, x⟫ + b)`: finite shifts commute with suprema, the Legendre
transform is translated
accordingly (`legendre_affineSubtract`), convex real epigraphs are preserved, finite shifts cancel
in `EReal`, and a
touching plane at `0` normalizes a potential to be nonnegative and zero at the origin. Pointwise; no
measure.

Supporting infrastructure for Cordero-Erausquin–Klartag, Proposition 12.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis


section
-- Subtracting an affine function from an extended-real potential, and its Legendre transform.

open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Subtract the actual affine function `inner a x + b`. -/
def affineSubtract (f : E → EReal) (a : E) (b : ℝ) (x : E) : EReal :=
  f x - ((inner ℝ a x + b : ℝ) : EReal)
/-- Translation by a finite real value commutes with an arbitrary EReal supremum. -/
theorem iSup_add_coe {ι : Type*} (F : ι → EReal) (b : ℝ) :
    (⨆ i, F i + (b : EReal)) = (⨆ i, F i) + (b : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact add_le_add (le_iSup F i) le_rfl
  · apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot b)) (.inl (EReal.coe_ne_top b))).mp
    apply iSup_le
    intro i
    exact (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot b)) (.inl (EReal.coe_ne_top b))).mpr
      (le_iSup (fun j => F j + (b : EReal)) i)
/-- Exact conjugate formula, including infinite input/conjugate values. -/
theorem legendre_affineSubtract (f : E → EReal) (a : E) (b : ℝ) (y : E) :
    legendre (affineSubtract f a b) y = legendre f (y + a) + (b : EReal) := by
  have hterm (x : E) :
      (inner ℝ x y : EReal) - affineSubtract f a b x =
        ((inner ℝ x (y + a) : EReal) - f x) + (b : EReal) := by
    change (inner ℝ x y : EReal) - (f x - ((inner ℝ a x + b : ℝ) : EReal)) =
      ((inner ℝ x (y + a) : EReal) - f x) + (b : EReal)
    generalize hz : f x = z
    induction z with
    | bot => simp
    | top =>
      rw [EReal.top_sub_coe]
      simp
    | coe z =>
      norm_cast
      simp only [inner_add_right, real_inner_comm a x]
      ring
  unfold legendre
  simp_rw [hterm]
  exact iSup_add_coe _ b
/-- At every finite input point the actual affine perturbation has its intended
real restriction; no global finiteness is assumed. -/
theorem affineSubtract_toReal_of_finite (f : E → EReal) (a : E) (b : ℝ) (x : E)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    (affineSubtract f a b x).toReal = (f x).toReal - (inner ℝ a x + b) := by
  exact EReal.toReal_sub ht hb (EReal.coe_ne_top _) (EReal.coe_ne_bot _)

end

section
-- Cancelling a real shift in extended-real subtraction.

open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Finite real shifts cancel even when the logarithm is infinite. -/
theorem sub_coe_cancel_shift (z : EReal) (A b : ℝ) :
    (z - (b : EReal)) - ((A - b : ℝ) : EReal) = z - (A : EReal) := by
  induction z with
  | bot => simp
  | top => rw [EReal.top_sub_coe b, EReal.top_sub_coe (A - b), EReal.top_sub_coe A]
  | coe z =>
    norm_cast
    ring

end

section
-- Normalizing a convex potential to vanish at the origin.

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Actual affine subtraction preserves convexity of the real epigraph. -/
theorem convex_epigraph_affineSubtract (f : E → EReal) (a : E) (b : ℝ)
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}) :
    Convex ℝ {p : E × ℝ | affineSubtract f a b p.1 ≤ (p.2 : EReal)} := by
  intro p hp q hq α β hα hβ hsum
  have hp' : (p.1, p.2 + (inner ℝ a p.1 + b)) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    change f p.1 ≤ ((p.2 + (inner ℝ a p.1 + b) : ℝ) : EReal)
    have ht := (EReal.sub_le_iff_le_add
      (.inl (EReal.coe_ne_bot (inner ℝ a p.1 + b)))
      (.inl (EReal.coe_ne_top (inner ℝ a p.1 + b)))).mp hp
    simpa only [EReal.coe_add] using ht
  have hq' : (q.1, q.2 + (inner ℝ a q.1 + b)) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    change f q.1 ≤ ((q.2 + (inner ℝ a q.1 + b) : ℝ) : EReal)
    have ht := (EReal.sub_le_iff_le_add
      (.inl (EReal.coe_ne_bot (inner ℝ a q.1 + b)))
      (.inl (EReal.coe_ne_top (inner ℝ a q.1 + b)))).mp hq
    simpa only [EReal.coe_add] using ht
  have hh := hf hp' hq' hα hβ hsum
  have halg : α * (p.2 + (inner ℝ a p.1 + b)) + β * (q.2 + (inner ℝ a q.1 + b)) =
      α * p.2 + β * q.2 + (inner ℝ a (α • p.1 + β • q.1) + b) := by
    simp only [inner_add_right, inner_smul_right]
    have hb : α * b + β * b = b := by rw [← add_mul, hsum, one_mul]
    nlinarith only [hb]
  change f (α • p.1 + β • q.1) ≤
    ((α * (p.2 + (inner ℝ a p.1 + b)) + β * (q.2 + (inner ℝ a q.1 + b)) : ℝ) : EReal) at hh
  rw [halg] at hh
  change f (α • p.1 + β • q.1) -
    ((inner ℝ a (α • p.1 + β • q.1) + b : ℝ) : EReal) ≤ ((α * p.2 + β * q.2 : ℝ) : EReal)
  apply (EReal.sub_le_iff_le_add
    (.inl (EReal.coe_ne_bot (inner ℝ a (α • p.1 + β • q.1) + b)))
    (.inl (EReal.coe_ne_top (inner ℝ a (α • p.1 + β • q.1) + b)))).mpr
  simpa only [EReal.coe_add] using hh
/-- An actual plane touching at0 is produced, then subtracted. No desired
minorant or nonnegative-normalization conclusion is assumed. -/
theorem exists_nonnegative_origin_zero_affine [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ConvexPotential f)
    (h0 : (0 : E) ∈ interior {x | f x ≠ ⊤}) :
    ∃ a : E, let g := affineSubtract f a (f 0).toReal
      ConvexPotential g ∧ (∀ x, 0 ≤ g x) ∧ g 0 = 0 := by
  obtain ⟨a, ha⟩ := exists_supporting_affine_at_zero f hf h0
  have hnn : ∀ x, 0 ≤ affineSubtract f a (f 0).toReal x := by
    intro x
    apply (EReal.sub_nonneg (.inr (EReal.coe_ne_top _)) (.inr (EReal.coe_ne_bot _))).mpr
    exact ha x
  refine ⟨a, ⟨?_, convex_epigraph_affineSubtract f a (f 0).toReal hf.2⟩, hnn, ?_⟩
  · intro x
    exact ne_of_gt (EReal.bot_lt_zero.trans_le (hnn x))
  · change f 0 - ((inner ℝ a 0 + (f 0).toReal : ℝ) : EReal) = 0
    rw [inner_zero_right, zero_add, ← EReal.coe_toReal (interior_subset h0) (hf.1 0),
      ← EReal.coe_sub]
    simp

end

end FunctionalInequalities.Analysis
