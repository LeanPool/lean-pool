/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.DoubledMu

/-!
# Coarse-graining support: Support.Book.Ch02.Theorems.DoubledMu

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport
namespace Book
namespace Ch02

noncomputable section

/-- Public doubled-`mu` theory package.  The internal proof may replace the
coefficient field by an a.e.-equal pointwise representative, but this theorem is
stated only for the public a.e.-native coefficient field `a`. -/
theorem doubledMuTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    DoubledMuTheory U a :=
  HCPolySupport.Internal.Ch02.BookCh02.doubledMuTheory U a

namespace IsDoubledMuMinimizer

/-- A pointwise doubled-`mu` minimizer realizes the public infimum. -/
theorem doubledMuValue_eq_doubledMu {d : ℕ} {U : Domain d} {a : CoeffOn U}
    {P : BlockVec d} {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U a P X) :
    doubledMuValue U a X = doubledMu U a P := by
  let s : Set ℝ := doubledMuValueSet U a P
  have hmem : doubledMuValue U a X ∈ s := ⟨X, hX.1, rfl⟩
  have hbdd : BddBelow s := by
    refine ⟨doubledMuValue U a X, ?_⟩
    intro m hm
    rcases hm with ⟨Y, hY, rfl⟩
    exact hX.2 Y hY
  have hnon : s.Nonempty := ⟨doubledMuValue U a X, hmem⟩
  apply le_antisymm
  · unfold doubledMu
    exact le_csInf hnon (by
      intro m hm
      rcases hm with ⟨Y, hY, rfl⟩
      exact hX.2 Y hY)
  · unfold doubledMu
    exact csInf_le hbdd hmem

end IsDoubledMuMinimizer

/-- A doubled-`mu` minimizer at loading `(-p, q)` extracts the gradient of the
scalar canonical response maximizer from its lower block image. -/
theorem doubledMuMinimizer_negLeft_eq_canonicalGradient
    {d : ℕ} (U : Domain d) (a : CoeffOn U) (p q : Vec d)
    {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U a (-p, q) X) :
    (fun x =>
        X.potential x +
          (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).2)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x =>
      (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad x :=
  HCPolySupport.Internal.Ch02.BookCh02.doubledMuMinimizer_negLeft_eq_canonicalGradient
    U a p q hX

/-- A doubled-`mu` minimizer at loading `(-p, q)` extracts the flux of the
scalar canonical response maximizer from its upper block image. -/
theorem doubledMuMinimizer_neg_left_extracts_canonicalMaximizerFlux
    {d : ℕ} (U : Domain d) (a : CoeffOn U) (p q : Vec d)
    {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U a (-p, q) X) :
    (fun x =>
        X.flux x +
          (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).1)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x =>
      matVecMul (a.toCoeffField x)
        ((canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad x) :=
  HCPolySupport.Internal.Ch02.BookCh02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerFlux
    U a p q hX

end

end Ch02
end Book
end HCPolySupport
