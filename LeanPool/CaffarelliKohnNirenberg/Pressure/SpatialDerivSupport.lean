/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-! ## Support and compact support of spatial derivatives -/

public section

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN



/-- The support of a spatial derivative is contained in the support of the function. -/
theorem support_spatialDeriv_subset {f : Vec3 → ℝ} (i : Fin 3) :
    Function.support (spatialDeriv f i) ⊆ tsupport f :=
  (subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ (basisVec i))

/-- The topological support of a spatial derivative is contained in the topological support
    of the function. -/
theorem tsupport_spatialDeriv_subset {f : Vec3 → ℝ} (i : Fin 3) :
    tsupport (spatialDeriv f i) ⊆ tsupport f :=
  closure_minimal (support_spatialDeriv_subset i) (isClosed_tsupport f)

/-- A function with compact support has a spatial derivative with compact support. -/
theorem hasCompactSupport_spatialDeriv {f : Vec3 → ℝ}
    (hf : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (spatialDeriv f i) := by
  change HasCompactSupport (fun x => (fderiv ℝ f x) (basisVec i))
  exact hf.fderiv_apply (𝕜 := ℝ) (basisVec i)

/-- The support of a mixed second derivative is contained in the topological support
of the function. -/
theorem support_mixedSecond_subset {f : Vec3 → ℝ} (i j : Fin 3) :
    Function.support (mixedSecond f i j) ⊆ tsupport f :=
  (support_spatialDeriv_subset (f := spatialDeriv f j) i).trans
    (tsupport_spatialDeriv_subset j)

/-- The topological support of a mixed second derivative is contained in the topological
    support of the function. -/
theorem tsupport_mixedSecond_subset {f : Vec3 → ℝ} (i j : Fin 3) :
    tsupport (mixedSecond f i j) ⊆ tsupport f :=
  closure_minimal (support_mixedSecond_subset i j) (isClosed_tsupport f)

/-- A function with compact support has a mixed second derivative with compact support. -/
theorem hasCompactSupport_mixedSecond {f : Vec3 → ℝ}
    (hf : HasCompactSupport f) (i j : Fin 3) :
    HasCompactSupport (mixedSecond f i j) :=
  HasCompactSupport.of_support_subset_isCompact hf.isCompact (support_mixedSecond_subset i j)

/-- The support of the spatial Laplacian is contained in the topological support
of the function. -/
theorem support_spatialLaplacian_subset {f : Vec3 → ℝ} :
    Function.support (spatialLaplacian f) ⊆ tsupport f := by
  intro x hx
  by_contra hxt
  apply hx
  simp only [spatialLaplacian]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hxi : x ∉ tsupport (spatialDeriv f i) := fun h => hxt (tsupport_spatialDeriv_subset i h)
  simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxi]

/-- The topological support of the spatial Laplacian is contained in the topological
    support of the function. -/
theorem tsupport_spatialLaplacian_subset {f : Vec3 → ℝ} :
    tsupport (spatialLaplacian f) ⊆ tsupport f :=
  closure_minimal support_spatialLaplacian_subset (isClosed_tsupport f)

/-- A function with compact support has a spatial Laplacian with compact support. -/
theorem hasCompactSupport_spatialLaplacian {f : Vec3 → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (spatialLaplacian f) :=
  HasCompactSupport.of_support_subset_isCompact hf.isCompact support_spatialLaplacian_subset

end CKN
