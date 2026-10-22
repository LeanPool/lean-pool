/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
import LeanPool.CCDN.Hilbert.CoordinateIndependence

/-! Full ambient Hilbert dimension forces the ideal to be zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A proper ideal whose filtered Hilbert polynomial has degree equal to the number of variables is
the zero ideal. -/
theorem ideal_eq_bot_of_full_hilbert_dimension
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤)
    (hdim : (filteredHilbertPolynomial I).natDegree = Fintype.card σ) : I = ⊥ := by
  classical
  obtain ⟨U, hU, hAI⟩ := exists_hilbert_dimension_independent_coordinates I hI
  have hcard : Fintype.card U = Fintype.card σ := by
    simpa only [Nat.card_eq_fintype_card, hdim] using hU
  have hmem : ∀ i : σ, i ∈ U := by
    intro i
    by_contra hn
    have hh := Fintype.card_subtype_lt hn
    have hc : Fintype.card U = Fintype.card {x // x ∈ U} :=
      Fintype.card_congr (Equiv.refl _)
    omega
  let j : σ → U := fun i => ⟨i, hmem i⟩
  have hj : Function.Injective j := fun _ _ h => congrArg Subtype.val h
  have hi : AlgebraicIndependent K (fun i : σ => (Ideal.Quotient.mk I) (X i)) := by
    exact hAI.comp j hj
  have he : aeval (fun i : σ => (Ideal.Quotient.mk I) (X i)) = Ideal.Quotient.mkₐ K I := by
    ext i
    simp
  have hinj : Function.Injective (Ideal.Quotient.mkₐ K I) := by
    rw [← he]
    exact hi
  have hk := (RingHom.injective_iff_ker_eq_bot
    (Ideal.Quotient.mkₐ K I).toRingHom).mp hinj
  simpa only [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker] using hk

end
end CCDN
