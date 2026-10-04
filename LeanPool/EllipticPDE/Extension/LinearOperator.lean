/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Extension.Operator


/-!
# Extension operator as a linear map

Guo's proof produces an extension of each class. Evans states the same theorem as a bounded
linear operator, and this file packages it that way: the partition, the charts, the bounded
graphs, the radii and the two cutoffs are all chosen from the domain alone, before any class
appears, so the assembled extension is a formula in the class, and every step of that formula
is either multiplication by a fixed function, precomposition with a fixed map, or a finite sum.

The domain of the operator is the pair of a class and its gradient, which is what the weak
gradient of this development relates; the bound of clause (iii) is stated on that pair, so the
operator is bounded in the sense the theorem asserts at every exponent, and not only at `2`.

## Main declarations

* `EllipticPdes.Extension.SobolevPair`: a class together with a candidate gradient.
* `EllipticPdes.Extension.extLinear`: the extension operator, as an `ℝ`-linear map.
* `EllipticPdes.Extension.extLinear_spec`: the three clauses of the theorem, stated for that
  map with a constant quantified before the class.
* `EllipticPdes.Extension.exists_extLinear`: the theorem as Evans states it, with the operator
  and the constant produced together.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1 (p. 253);
Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- A class together with a candidate for its gradient. This is the module the extension
operator acts on. -/
abbrev SobolevPair (d : ℕ) : Type :=
  (EuclideanSpace ℝ (Fin d) → ℝ) × (Fin d → EuclideanSpace ℝ (Fin d) → ℝ)

variable {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Linearity of the pieces -/

/-- The indicator of a set is additive in the function. -/
theorem indicator_add_apply {α : Type*} (s : Set α) (f g : α → ℝ) (y : α) :
    s.indicator (f + g) y = s.indicator f y + s.indicator g y := by
  by_cases h : y ∈ s <;> simp [h]

/-- The indicator of a set commutes with a scalar. -/
theorem indicator_smul_apply {α : Type*} (s : Set α) (a : ℝ) (f : α → ℝ) (y : α) :
    s.indicator (a • f) y = a * s.indicator f y := by
  by_cases h : y ∈ s <;> simp [h]


/-- A piece of the glued extension is additive in the class. -/
theorem extPiece_add (P : BoundaryPartition d Ω) (i : Option {x // x ∈ P.centres})
    (u v : EuclideanSpace ℝ (Fin d) → ℝ) :
    extPiece P i (u + v) = extPiece P i u + extPiece P i v := by
  funext y
  cases i with
  | none => simp only [extPiece, Pi.add_apply, indicator_add_apply]; ring
  | some x =>
      have h : localExt (P.chart x) x (pieceRadius_lt P x) (u + v)
          = localExt (P.chart x) x (pieceRadius_lt P x) u
            + localExt (P.chart x) x (pieceRadius_lt P x) v := by
        funext z
        exact congrFun (localExt_add (P.chart x) x (pieceRadius_lt P x) u v) z
      simp only [extPiece, h, Pi.add_apply, indicator_add_apply]
      ring

/-- A piece of the glued extension commutes with a scalar. -/
theorem extPiece_smul (P : BoundaryPartition d Ω) (i : Option {x // x ∈ P.centres}) (a : ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    extPiece P i (a • u) = a • extPiece P i u := by
  funext y
  cases i with
  | none =>
      simp only [extPiece, Pi.smul_apply, smul_eq_mul, indicator_smul_apply]
      ring
  | some x =>
      have h : localExt (P.chart x) x (pieceRadius_lt P x) (a • u)
          = a • localExt (P.chart x) x (pieceRadius_lt P x) u := by
        funext z
        exact congrFun (localExt_smul (P.chart x) x (pieceRadius_lt P x) a u) z
      simp only [extPiece, h, Pi.smul_apply, smul_eq_mul, indicator_smul_apply]
      ring

/-- The gradient of a piece is additive in the class and its gradient together. -/
theorem extPieceGrad_add (P : BoundaryPartition d Ω) (i : Option {x // x ∈ P.centres})
    (u v : EuclideanSpace ℝ (Fin d) → ℝ) (g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (k : Fin d) :
    extPieceGrad P i (u + v) (g + h) k = extPieceGrad P i u g k + extPieceGrad P i v h k := by
  funext y
  cases i with
  | none =>
      simp only [extPieceGrad, Pi.add_apply, indicator_add_apply]
      ring
  | some x =>
      have hu : localExt (P.chart x) x (pieceRadius_lt P x) (u + v)
          = localExt (P.chart x) x (pieceRadius_lt P x) u
            + localExt (P.chart x) x (pieceRadius_lt P x) v := by
        funext z
        exact congrFun (localExt_add (P.chart x) x (pieceRadius_lt P x) u v) z
      have hg : localExtGrad (P.chart x) x (pieceRadius_lt P x) (u + v) (g + h) k
          = localExtGrad (P.chart x) x (pieceRadius_lt P x) u g k
            + localExtGrad (P.chart x) x (pieceRadius_lt P x) v h k := by
        funext z
        exact congrFun (localExtGrad_add (P.chart x) x (pieceRadius_lt P x) u v g h k) z
      simp only [extPieceGrad, hu, hg, Pi.add_apply, indicator_add_apply]
      ring

/-- The gradient of a piece commutes with a scalar. -/
theorem extPieceGrad_smul (P : BoundaryPartition d Ω) (i : Option {x // x ∈ P.centres})
    (a : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (k : Fin d) :
    extPieceGrad P i (a • u) (a • g) k = a • extPieceGrad P i u g k := by
  funext y
  cases i with
  | none =>
      simp only [extPieceGrad, Pi.smul_apply, smul_eq_mul, indicator_smul_apply]
      ring
  | some x =>
      have hu : localExt (P.chart x) x (pieceRadius_lt P x) (a • u)
          = a • localExt (P.chart x) x (pieceRadius_lt P x) u := by
        funext z
        exact congrFun (localExt_smul (P.chart x) x (pieceRadius_lt P x) a u) z
      have hg : localExtGrad (P.chart x) x (pieceRadius_lt P x) (a • u) (a • g) k
          = a • localExtGrad (P.chart x) x (pieceRadius_lt P x) u g k := by
        funext z
        exact congrFun (localExtGrad_smul (P.chart x) x (pieceRadius_lt P x) a u g k) z
      simp only [extPieceGrad, hu, hg, Pi.smul_apply, smul_eq_mul, indicator_smul_apply]
      ring

/-! ### Linearity of the glued extension -/

/-- The glued extension is additive in the class. -/
theorem extFun_add (P : BoundaryPartition d Ω) (u v : EuclideanSpace ℝ (Fin d) → ℝ) :
    extFun P (u + v) = extFun P u + extFun P v := by
  funext y
  simp only [extFun, Pi.add_apply, extPiece_add, ← Finset.sum_add_distrib]

/-- The glued extension commutes with a scalar. -/
theorem extFun_smul (P : BoundaryPartition d Ω) (a : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    extFun P (a • u) = a • extFun P u := by
  funext y
  simp only [extFun, Pi.smul_apply, smul_eq_mul, extPiece_smul, Finset.mul_sum]

/-- The gradient of the glued extension is additive. -/
theorem extFunGrad_add (P : BoundaryPartition d Ω) (u v : EuclideanSpace ℝ (Fin d) → ℝ)
    (g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    extFunGrad P (u + v) (g + h) k = extFunGrad P u g k + extFunGrad P v h k := by
  funext y
  simp only [extFunGrad, Pi.add_apply, extPieceGrad_add, ← Finset.sum_add_distrib]

/-- The gradient of the glued extension commutes with a scalar. -/
theorem extFunGrad_smul (P : BoundaryPartition d Ω) (a : ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (k : Fin d) :
    extFunGrad P (a • u) (a • g) k = a • extFunGrad P u g k := by
  funext y
  simp only [extFunGrad, Pi.smul_apply, smul_eq_mul, extPieceGrad_smul, Finset.mul_sum]

/-! ### Linearity of the extension with its support cut down -/

/-- The cut-down extension is additive in the class. -/
theorem extSubsetFun_add (P : BoundaryPartition d Ω) (χ u v : EuclideanSpace ℝ (Fin d) → ℝ) :
    extSubsetFun P χ (u + v) = extSubsetFun P χ u + extSubsetFun P χ v := by
  funext y
  simp only [extSubsetFun, extFun_add, Pi.add_apply]
  ring

/-- The cut-down extension commutes with a scalar. -/
theorem extSubsetFun_smul (P : BoundaryPartition d Ω) (a : ℝ)
    (χ u : EuclideanSpace ℝ (Fin d) → ℝ) :
    extSubsetFun P χ (a • u) = a • extSubsetFun P χ u := by
  funext y
  simp only [extSubsetFun, extFun_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The gradient of the cut-down extension is additive. -/
theorem extSubsetGrad_add (P : BoundaryPartition d Ω) (χ u v : EuclideanSpace ℝ (Fin d) → ℝ)
    (g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    extSubsetGrad P χ (u + v) (g + h) k
      = extSubsetGrad P χ u g k + extSubsetGrad P χ v h k := by
  funext y
  simp only [extSubsetGrad, extFun_add, extFunGrad_add, Pi.add_apply]
  ring

/-- The gradient of the cut-down extension commutes with a scalar. -/
theorem extSubsetGrad_smul (P : BoundaryPartition d Ω) (a : ℝ)
    (χ u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (k : Fin d) :
    extSubsetGrad P χ (a • u) (a • g) k = a • extSubsetGrad P χ u g k := by
  funext y
  simp only [extSubsetGrad, extFun_smul, extFunGrad_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The operator -/

/-- **Extension operator.** A class and its gradient go to the extension and its gradient.
The partition, the charts, the graphs, the radii and the cutoff are fixed before the class, so
the map is linear. -/
def extLinear (P : BoundaryPartition d Ω) (χ : EuclideanSpace ℝ (Fin d) → ℝ) :
    SobolevPair d →ₗ[ℝ] SobolevPair d where
  toFun w := (extSubsetFun P χ w.1, fun k => extSubsetGrad P χ w.1 w.2 k)
  map_add' w w' := by
    refine Prod.ext ?_ ?_
    · exact extSubsetFun_add P χ w.1 w'.1
    · funext k
      exact extSubsetGrad_add P χ w.1 w'.1 w.2 w'.2 k
  map_smul' a w := by
    refine Prod.ext ?_ ?_
    · exact extSubsetFun_smul P a χ w.1
    · funext k
      exact extSubsetGrad_smul P a χ w.1 w.2 k

@[simp] theorem extLinear_fst (P : BoundaryPartition d Ω)
    (χ : EuclideanSpace ℝ (Fin d) → ℝ) (w : SobolevPair d) :
    (extLinear P χ w).1 = extSubsetFun P χ w.1 := rfl

@[simp] theorem extLinear_snd (P : BoundaryPartition d Ω)
    (χ : EuclideanSpace ℝ (Fin d) → ℝ) (w : SobolevPair d) (k : Fin d) :
    (extLinear P χ w).2 k = extSubsetGrad P χ w.1 w.2 k := rfl

/-- **Three clauses of the theorem for the operator.** The constant is quantified before
the class, so the map is bounded in the sense clause (iii) asserts. -/
theorem extLinear_spec (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (P : BoundaryPartition d Ω) {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχc : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ω')
    (hχ1 : ∀ y ∈ closure Ω, χ y = 1) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ w : SobolevPair d,
      IntegrableOn w.1 Ω volume → (∀ k, IntegrableOn (w.2 k) Ω volume) →
      HasWeakGradOn Ω w.1 w.2 →
        HasWeakGradOn Set.univ (extLinear P χ w).1 (extLinear P χ w).2 ∧
          HasCompactSupport (extLinear P χ w).1 ∧ tsupport (extLinear P χ w).1 ⊆ Ω' ∧
          Integrable (extLinear P χ w).1 volume ∧
          (∀ k, Integrable ((extLinear P χ w).2 k) volume) ∧
          (∀ y ∈ Ω, (extLinear P χ w).1 y = w.1 y) ∧
          eLpNorm (extLinear P χ w).1 p volume ≤ (K : ℝ≥0∞) * (eLpNorm w.1 p
            (volume.restrict Ω) + ∑ i, eLpNorm (w.2 i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm ((extLinear P χ w).2 k) p volume
            ≤ (K : ℝ≥0∞) * (eLpNorm w.1 p (volume.restrict Ω)
              + ∑ i, eLpNorm (w.2 i) p (volume.restrict Ω)) := by
  obtain ⟨K, hK⟩ := extension_subset_bound hΩopen hΩb P hχc hχcs hχs hχ1 hp
  refine ⟨K, fun w hu hgi hwg => ?_⟩
  simp only [extLinear_fst, extLinear_snd]
  exact hK w.1 w.2 hu hgi hwg

/-- **Evans's extension operator** (§5.4 Theorem 1, p. 253). On a bounded domain with `C¹`
boundary, and for any open set the closure of the domain sits in, there is one `ℝ`-linear map
and one constant such that every class with a weak gradient on the domain goes to a class with
a weak gradient on the whole space, agreeing with it on the domain, supported inside that open
set, and bounded together with its gradient in every `Lᵖ` seminorm. -/
theorem exists_extLinear (hd : 0 < d) (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) (hΩ'open : IsOpen Ω') (hsub : closure Ω ⊆ Ω')
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ (T : SobolevPair d →ₗ[ℝ] SobolevPair d) (K : ℝ≥0), ∀ w : SobolevPair d,
      IntegrableOn w.1 Ω volume → (∀ k, IntegrableOn (w.2 k) Ω volume) →
      HasWeakGradOn Ω w.1 w.2 →
        HasWeakGradOn Set.univ (T w).1 (T w).2 ∧
          HasCompactSupport (T w).1 ∧ tsupport (T w).1 ⊆ Ω' ∧
          Integrable (T w).1 volume ∧ (∀ k, Integrable ((T w).2 k) volume) ∧
          (∀ y ∈ Ω, (T w).1 y = w.1 y) ∧
          eLpNorm (T w).1 p volume ≤ (K : ℝ≥0∞) * (eLpNorm w.1 p (volume.restrict Ω)
            + ∑ i, eLpNorm (w.2 i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm ((T w).2 k) p volume ≤ (K : ℝ≥0∞) * (eLpNorm w.1 p (volume.restrict Ω)
            + ∑ i, eLpNorm (w.2 i) p (volume.restrict Ω)) := by
  classical
  obtain ⟨P⟩ := nonempty_boundaryPartition hd hΩopen hΩb hC1
  obtain ⟨Rb, hRb⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hclc : IsCompact (closure Ω) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) Rb).of_isClosed_subset isClosed_closure
      (closure_minimal hRb isClosed_closedBall)
  obtain ⟨χ, hχc, hχcs, hχs, hχ1⟩ := exists_cutoff_one_on_compact hclc hΩ'open hsub
  obtain ⟨K, hK⟩ := extLinear_spec hΩopen hΩb P hχc hχcs hχs hχ1 hp
  exact ⟨extLinear P χ, K, hK⟩

end EllipticPdes.Extension
