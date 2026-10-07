/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedOrderedDerivative

/-!
# Ordered coordinate and Fréchet derivatives

An ordered list of coordinate derivatives is the Fréchet derivative applied
to its corresponding tuple of coordinate basis vectors.
-/

public section

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The tuple of coordinate basis vectors associated with an ordered list. -/
@[expose]
def regularisedListBasisTuple (α : List (Fin 3)) :
    Fin α.length → Vec3 := fun k => CKN.basisVec (α.get k)

/-- Prepending a direction prepends its basis vector to the tuple. -/
theorem regularisedListBasisTuple_cons (i : Fin 3) (α : List (Fin 3)) :
    regularisedListBasisTuple (i :: α) =
      Fin.cons (α := fun _ : Fin (α.length + 1) => Vec3)
        (CKN.basisVec i) (regularisedListBasisTuple α) := by
  funext k
  refine Fin.cases ?_ (fun l => ?_) k
  · simp [regularisedListBasisTuple]
  · simp [regularisedListBasisTuple]

/-- An ordered coordinate derivative equals the matching Fréchet
derivative evaluated on its coordinate basis tuple. -/
theorem regularisedOrderedSpatialDerivative_eq_iteratedFDeriv
    (f : Vec3 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (α : List (Fin 3)) (x : Vec3) :
    regularisedOrderedSpatialDerivative α f x =
      (iteratedFDeriv ℝ α.length f x) (regularisedListBasisTuple α) := by
  induction α generalizing x with
  | nil =>
      simp [regularisedOrderedSpatialDerivative]
  | cons i α ih =>
      have hfun : regularisedOrderedSpatialDerivative α f =
          fun y : Vec3 =>
            (iteratedFDeriv ℝ α.length f y) (regularisedListBasisTuple α) := by
        funext y
        exact ih y
      change fderiv ℝ (regularisedOrderedSpatialDerivative α f) x
        (CKN.basisVec i) = _
      rw [hfun, regularisedListBasisTuple_cons]
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ α.length f) x :=
        hf.contDiffAt.differentiableAt_iteratedFDeriv
          (by exact_mod_cast ENat.natCast_lt_top α.length)
      have hsucc := hdiff.iteratedFDeriv_succ_apply_left'
        (m := Fin.cons (α := fun _ : Fin (α.length + 1) => Vec3)
          (CKN.basisVec i) (regularisedListBasisTuple α))
      simpa [Fin.tail_cons] using hsucc.symm

end CKN.Leray

end
