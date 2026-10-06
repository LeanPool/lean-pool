/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewResponse
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseAnnealed
public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNormCellAverage
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.GradientUniqueness

/-!
# High-contrast homogenization: Provider.Response.ConstantSkewCentered

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant-skew covariance of centered responses

The canonical optimizer for the recentered coefficient has the same gradient
as the canonical optimizer for the original coefficient with the corrected
second load.  Its averaged flux is shifted by the constant skew matrix applied
to its averaged gradient.  This records the covariance of the two separate
annealed centering factors.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem averageVec_congr_ae {U : Domain d} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[volumeMeasureOn (U : Set (Vec d))] G) :
    averageVec U F = averageVec U G := by
  funext i
  unfold averageVec Book.Ch02.average
  congr 1
  exact integral_congr_ae (hFG.mono fun x hx ↦ congrFun hx i)

private theorem averageVec_sub {U : Domain d} {F G : Vec d → Vec d}
    (hF : MemVectorL2 (U : Set (Vec d)) F)
    (hG : MemVectorL2 (U : Set (Vec d)) G) :
    averageVec U (fun x ↦ F x - G x) = averageVec U F - averageVec U G := by
  funext i
  unfold averageVec Book.Ch02.average
  have hFi := (memScalarL2_coord_of_memVectorL2 hF i).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hGi := (memScalarL2_coord_of_memVectorL2 hG i).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  simp only [Pi.sub_apply]
  rw [integral_sub hFi hGi]
  ring

/-- The canonical shifted optimizer and the original optimizer at the
corrected load have the same gradient almost everywhere. -/
theorem centeredResponseOptimizer_subSkew_gradient_ae
    (U : Domain d) (a : CoeffSpace d) (g : Mat d) (hg : IsSkewMat g)
    (p q : Vec d) :
    (centeredResponseOptimizer U (a.subSkew g hg) p q).toH1.grad =ᵐ[
        volumeMeasureOn (U : Set (Vec d))]
      (centeredResponseOptimizer U a p (q - matVecMul g p)).toH1.grad := by
  let b : CoeffOn U := (a.subSkew g hg).coeffOn U
  let a₀ : CoeffOn U := a.coeffOn U
  let u : Solution U a₀ := centeredResponseOptimizer U a p (q - matVecMul g p)
  have hshift : b.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x ↦ a₀.toCoeffField x - g := by
    exact CoeffSpace.coeffOn_subSkew_ae a U g hg
  obtain ⟨v, hv⟩ := exists_solution_subSkew g hg hshift u
  have hvmax : Book.Ch02.IsResponseMaximizer U b p q v := by
    intro w
    obtain ⟨w₀, hw₀⟩ := exists_solution_of_subSkew g hg hshift w
    have hle := centeredResponseOptimizer_isMaximizer U a
      p (q - matVecMul g p) w₀
    have hwval := responseValue_subSkew g hg hshift p q w₀ w hw₀.symm
    have hvval := responseValue_subSkew g hg hshift p q u v hv
    rw [hwval, hvval]
    exact hle
  have hcanonical :
      (centeredResponseOptimizer U (a.subSkew g hg) p q).toH1.grad =ᵐ[
          volumeMeasureOn (U : Set (Vec d))] v.toH1.grad :=
    Book.Ch02.sameGradientAE_of_isResponseMaximizer
      (centeredResponseOptimizer_isMaximizer U (a.subSkew g hg) p q) hvmax
  have hgrad : v.toH1.grad = u.toH1.grad := congrArg H1Function.grad hv
  exact hcanonical.trans (Filter.Eventually.of_forall fun x ↦ congrFun hgrad x)

/-- The spatially averaged gradient is unchanged by constant-skew
recentering, after correcting the second load. -/
theorem averageGradient_centeredResponseOptimizer_subSkew
    (U : Domain d) (a : CoeffSpace d) (g : Mat d) (hg : IsSkewMat g)
    (p q : Vec d) :
    averageGradient U ((a.subSkew g hg).coeffOn U)
        (centeredResponseOptimizer U (a.subSkew g hg) p q) =
      averageGradient U (a.coeffOn U)
        (centeredResponseOptimizer U a p (q - matVecMul g p)) := by
  unfold averageGradient
  exact averageVec_congr_ae
    (centeredResponseOptimizer_subSkew_gradient_ae U a g hg p q)

/-- The averaged optimizer flux changes by `-g` times the averaged gradient. -/
theorem averageFlux_centeredResponseOptimizer_subSkew
    (U : Domain d) (a : CoeffSpace d) (g : Mat d) (hg : IsSkewMat g)
    (p q : Vec d) :
    averageFlux U ((a.subSkew g hg).coeffOn U)
        (centeredResponseOptimizer U (a.subSkew g hg) p q) =
      averageFlux U (a.coeffOn U)
          (centeredResponseOptimizer U a p (q - matVecMul g p)) -
        matVecMul g
          (averageGradient U (a.coeffOn U)
            (centeredResponseOptimizer U a p (q - matVecMul g p))) := by
  let v := centeredResponseOptimizer U (a.subSkew g hg) p q
  let u := centeredResponseOptimizer U a p (q - matVecMul g p)
  have hgrad : v.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))] u.toH1.grad :=
    centeredResponseOptimizer_subSkew_gradient_ae U a g hg p q
  have hcoeff := CoeffSpace.coeffOn_subSkew_ae a U g hg
  have hflux :
      (fun x ↦ matVecMul (((a.subSkew g hg).coeffOn U).toCoeffField x)
        (v.toH1.grad x)) =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      (fun x ↦ matVecMul ((a.coeffOn U).toCoeffField x) (u.toH1.grad x) -
        matVecMul g (u.toH1.grad x)) := by
    filter_upwards [hcoeff, hgrad] with x hx hxu
    rw [hx, hxu]
    funext i
    simp only [matVecMul, Matrix.sub_apply, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have havg := averageVec_congr_ae hflux
  have hfluxMem := u.flux_memVectorL2
  have hgradMem := u.toH1.grad_memVectorL2
  have hggradMem := memVectorL2_constMatrix_mul_gradient g u.toH1
  have hsub := averageVec_sub hfluxMem hggradMem
  have hmat := averageVec_matVecMul g hgradMem
  change
    averageVec U
        (fun x ↦ matVecMul (((a.subSkew g hg).coeffOn U).toCoeffField x)
          (v.toH1.grad x)) =
      averageVec U
          (fun x ↦ matVecMul ((a.coeffOn U).toCoeffField x) (u.toH1.grad x)) -
        matVecMul g (averageVec U u.toH1.grad)
  calc
    _ = averageVec U
        (fun x ↦ matVecMul ((a.coeffOn U).toCoeffField x) (u.toH1.grad x) -
          matVecMul g (u.toH1.grad x)) := havg
    _ = averageVec U
          (fun x ↦ matVecMul ((a.coeffOn U).toCoeffField x) (u.toH1.grad x)) -
        averageVec U (fun x ↦ matVecMul g (u.toH1.grad x)) := hsub
    _ = _ := by rw [hmat]

end

end HCPolySupport.HighContrast.Response
