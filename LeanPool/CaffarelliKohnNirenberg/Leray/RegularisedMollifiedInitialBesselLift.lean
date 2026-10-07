/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSmoothLaplacianBridge
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialOrderedSobolev
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedLaplacianCommutation
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedMildInitialData
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropEnergy

/-!
# Even-order Bessel regularity of the mollified initial field

The all-order derivative bounds for the mollifier give L² representatives
for every classical Laplacian iterate, which identify its tempered
distributional iterates and yield the complete even-order lift.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap Laplacian
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The derivative of a source field in the `i`th standard spatial direction. -/
@[expose]
def regularisedSourceDirectionalDerivative (i : Fin 3)
    (g : Vec3 → Vec3) : Vec3 → Vec3 := fun x =>
  fderiv ℝ g x (CKN.basisVec i)

/-- The componentwise spatial Laplacian of a regularized source vector field. -/
@[expose]
def regularisedSourceVectorLaplacian
    (g : Vec3 → Vec3) : Vec3 → Vec3 := fun x =>
  ∑ i : Fin 3,
    regularisedSourceDirectionalDerivative i
      (regularisedSourceDirectionalDerivative i g) x

/-- The pullback of a complex-valued field along the regularized source coordinate map. -/
@[expose]
def regularisedComplexPullback (g : Vec3 → Vec3) :
    L2Vec3 → ComplexVec3 := fun x =>
  complexifyValue (l2Vec3Equiv.symm (g (l2Vec3Equiv x)))

private theorem regularisedSourceDirectionalDerivative_contDiff
    (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (regularisedSourceDirectionalDerivative i g) := by
  exact (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuousLinearMap_comp
    (ContinuousLinearMap.apply ℝ Vec3 (CKN.basisVec i))

private theorem regularisedSourceDirectionalDerivative_component
    (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i j : Fin 3) (x : Vec3) :
    regularisedSourceDirectionalDerivative i g x j =
      fderiv ℝ (fun y => g y j) x (CKN.basisVec i) := by
  let P : Vec3 →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) j
  have hG : HasFDerivAt g (fderiv ℝ g x) x :=
    (hg.contDiffAt (x := x)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hP := P.hasFDerivAt.comp x hG
  have heq : (fun y : Vec3 => g y j) = fun y => P (g y) := by
    funext y
    rfl
  have hderiv : fderiv ℝ (fun y : Vec3 => P (g y)) x =
      P.comp (fderiv ℝ g x) := by
    simpa [Function.comp_def] using hP.fderiv
  rw [heq, hderiv]
  rfl

private theorem regularisedSourceSecondDerivative_component
    (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i j : Fin 3) (x : Vec3) :
    regularisedSourceDirectionalDerivative i
        (regularisedSourceDirectionalDerivative i g) x j =
      fderiv ℝ
        (fun y => fderiv ℝ (fun z => g z j) y (CKN.basisVec i)) x
        (CKN.basisVec i) := by
  have hfirst (y : Vec3) :
      regularisedSourceDirectionalDerivative i g y j =
        fderiv ℝ (fun z => g z j) y (CKN.basisVec i) :=
    regularisedSourceDirectionalDerivative_component g hg i j y
  rw [regularisedSourceDirectionalDerivative_component
    (regularisedSourceDirectionalDerivative i g)
    (regularisedSourceDirectionalDerivative_contDiff g hg i) i j x]
  rw [show (fun y : Vec3 =>
      regularisedSourceDirectionalDerivative i g y j) =
      (fun y => fderiv ℝ (fun z => g z j) y (CKN.basisVec i)) from funext hfirst]

private theorem regularisedSourceVectorLaplacian_component
    (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (j : Fin 3) (x : Vec3) :
    regularisedSourceVectorLaplacian g x j =
      regularisedScalarLaplacian (fun y => g y j) x := by
  simp only [regularisedSourceVectorLaplacian, Finset.sum_apply,
    regularisedScalarLaplacian]
  apply Finset.sum_congr rfl
  intro i hi
  exact regularisedSourceSecondDerivative_component g hg i j x

private theorem regularisedSourceVectorLaplacian_contDiff
    (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (regularisedSourceVectorLaplacian g) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ i : Fin 3,
    regularisedSourceDirectionalDerivative i
      (regularisedSourceDirectionalDerivative i g) x)
  exact ContDiff.sum (s := Finset.univ) (fun i hi =>
    regularisedSourceDirectionalDerivative_contDiff
      (regularisedSourceDirectionalDerivative i g)
      (regularisedSourceDirectionalDerivative_contDiff g hg i) i)

private theorem regularisedScalarLaplacian_contDiff
    (g : Vec3 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (regularisedScalarLaplacian g) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ i : Fin 3,
    fderiv ℝ (fun y => fderiv ℝ g y (CKN.basisVec i)) x (CKN.basisVec i))
  exact ContDiff.sum (s := Finset.univ) (fun i hi => by
    simpa [regularisedOrderedSpatialDerivative] using
      regularisedOrderedSpatialDerivative_contDiff g hg [i, i])

private theorem regularisedSourceVectorLaplacian_iterate_contDiff
    (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) ((regularisedSourceVectorLaplacian^[j]) g) := by
  induction j with
  | zero => simpa using hg
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact regularisedSourceVectorLaplacian_contDiff _ ih

private theorem regularisedScalarLaplacian_iterate_contDiff
    (g : Vec3 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) ((regularisedScalarLaplacian^[j]) g) := by
  induction j with
  | zero => simpa using hg
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact regularisedScalarLaplacian_contDiff _ ih

private theorem regularisedSourceVectorLaplacian_iterate_component
    (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (j : ℕ) (i : Fin 3) :
    ∀ x : Vec3,
      (regularisedSourceVectorLaplacian^[j] g) x i =
        (regularisedScalarLaplacian^[j] (fun x => g x i)) x := by
  induction j with
  | zero => intro x; rfl
  | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply']
      rw [regularisedSourceVectorLaplacian_component
        ((regularisedSourceVectorLaplacian^[j]) g)
        (regularisedSourceVectorLaplacian_iterate_contDiff g hg j) i x]
      have hfun : (fun y : Vec3 =>
          (regularisedSourceVectorLaplacian^[j] g) y i) =
          (regularisedScalarLaplacian^[j] (fun y => g y i)) := funext ih
      rw [hfun]
      simp only [Function.iterate_succ_apply']

private theorem regularisedMollifiedScalarIterate_ordered_memLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (i : Fin 3)
    (j : ℕ) (α : List (Fin 3)) :
    MemLp (regularisedOrderedSpatialDerivative α
      ((regularisedScalarLaplacian^[j])
        (fun x => regUniformMollifiedInitial ρ ε hε a x i)))
      (2 : ℝ≥0∞) volume := by
  let g : Vec3 → ℝ := fun x => regUniformMollifiedInitial ρ ε hε a x i
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    (regUniformMollifiedInitial_contDiff ρ ε hε ha).continuousLinearMap_comp
      (ContinuousLinearMap.proj (R := ℝ) i)
  have hAll : ∀ β : List (Fin 3),
      MemLp (regularisedOrderedSpatialDerivative β g) (2 : ℝ≥0∞) volume := by
    intro β
    exact regUniformMollifiedInitial_orderedDerivative_memLp
      ρ ε hε a ha β i
  have hIter : ∀ n : ℕ, ∀ β : List (Fin 3),
      MemLp (regularisedOrderedSpatialDerivative β
        ((regularisedScalarLaplacian^[n]) g)) (2 : ℝ≥0∞) volume := by
    intro n
    induction n with
    | zero =>
        intro β
        simpa using hAll β
    | succ n ih =>
        intro β
        have hstep := regularisedOrderedSpatialDerivative_laplacian_memLp
          ((regularisedScalarLaplacian^[n]) g)
          (regularisedScalarLaplacian_iterate_contDiff g hg n) β
          (fun γ hγ => ih γ)
        simpa only [Function.iterate_succ_apply'] using hstep
  exact hIter j α

private theorem regularisedComplexPullback_memLp
    (g : Vec3 → Vec3) (hg : MemLp g (2 : ℝ≥0∞) volume) :
    MemLp (regularisedComplexPullback g) (2 : ℝ≥0∞) volume := by
  let E : L2Vec3 ≃L[ℝ] Vec3 := l2Vec3Equiv
  let T : Vec3 →L[ℝ] ComplexVec3 := complexifyValue.comp E.symm.toContinuousLinearMap
  have hcomp : MemLp (fun x : L2Vec3 => g (WithLp.ofLp x))
      (2 : ℝ≥0∞) volume :=
    hg.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
  change MemLp (fun x : L2Vec3 => T (g (WithLp.ofLp x)))
    (2 : ℝ≥0∞) volume
  exact hcomp.continuousLinearMap_comp T

private theorem regularisedComplexPullback_directionalDerivative
    (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 3) (x : L2Vec3) :
    fderiv ℝ (regularisedComplexPullback g) x
        (regularisedL2CoordinateBasis i) =
      regularisedComplexPullback
        (regularisedSourceDirectionalDerivative i g) x := by
  let E : L2Vec3 ≃L[ℝ] Vec3 := l2Vec3Equiv
  let T : Vec3 →L[ℝ] ComplexVec3 := complexifyValue.comp E.symm.toContinuousLinearMap
  have hE : HasFDerivAt (fun y : L2Vec3 => E y)
      E.toContinuousLinearMap x := E.toContinuousLinearMap.hasFDerivAt (x := x)
  have hgE : HasFDerivAt (fun y : L2Vec3 => g (E y))
      ((fderiv ℝ g (E x)).comp E.toContinuousLinearMap) x :=
    ((hg.contDiffAt (x := E x)).differentiableAt (by norm_num)).hasFDerivAt.comp x hE
  have hT : HasFDerivAt (fun y : L2Vec3 => T (g (E y)))
      (T.comp ((fderiv ℝ g (E x)).comp E.toContinuousLinearMap)) x :=
    T.hasFDerivAt.comp x hgE
  have hfun : regularisedComplexPullback g =
      fun y : L2Vec3 => T (g (E y)) := rfl
  rw [hfun, hT.fderiv]
  change T ((fderiv ℝ g (E x)) (E (regularisedL2CoordinateBasis i))) =
    T ((regularisedSourceDirectionalDerivative i g) (E x))
  congr 1
  change (fderiv ℝ g (E x))
      (E (regularisedL2CoordinateBasis i)) =
    (fderiv ℝ g (E x)) (CKN.basisVec i)
  have hbasis : E (regularisedL2CoordinateBasis i) = CKN.basisVec i := by
    rw [regularisedL2CoordinateBasis_apply]
    change E (E.symm (CKN.basisVec i)) = CKN.basisVec i
    exact E.apply_symm_apply _
  rw [hbasis]

private theorem regularisedComplexPullback_laplacian
    (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    regularisedL2ClassicalLaplacian (regularisedComplexPullback g) =
      regularisedComplexPullback (regularisedSourceVectorLaplacian g) := by
  funext x
  change ∑ i : Fin 3,
      fderiv ℝ
        (fun y => fderiv ℝ (regularisedComplexPullback g) y
          (regularisedL2CoordinateBasis i)) x (regularisedL2CoordinateBasis i) =
    regularisedComplexPullback (regularisedSourceVectorLaplacian g) x
  have hfirst (i : Fin 3) :
      (fun y : L2Vec3 => fderiv ℝ (regularisedComplexPullback g) y
          (regularisedL2CoordinateBasis i)) =
        regularisedComplexPullback
          (regularisedSourceDirectionalDerivative i g) := by
    funext y
    exact regularisedComplexPullback_directionalDerivative g hg i y
  calc
    (∑ i : Fin 3,
        fderiv ℝ
          (fun y => fderiv ℝ (regularisedComplexPullback g) y
            (regularisedL2CoordinateBasis i)) x
          (regularisedL2CoordinateBasis i)) =
        ∑ i : Fin 3,
          fderiv ℝ
            (regularisedComplexPullback
              (regularisedSourceDirectionalDerivative i g)) x
            (regularisedL2CoordinateBasis i) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [hfirst i]
    _ = ∑ i : Fin 3,
          regularisedComplexPullback
            (regularisedSourceDirectionalDerivative i
              (regularisedSourceDirectionalDerivative i g)) x := by
                apply Finset.sum_congr rfl
                intro i hi
                exact regularisedComplexPullback_directionalDerivative
                  (regularisedSourceDirectionalDerivative i g)
                  (regularisedSourceDirectionalDerivative_contDiff g hg i) i x
    _ = regularisedComplexPullback (regularisedSourceVectorLaplacian g) x := by
          simp [regularisedComplexPullback, regularisedSourceVectorLaplacian, map_sum]

private theorem regularisedComplexPullback_iterate_laplacian
    (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (j : ℕ) :
    (regularisedL2ClassicalLaplacian^[j]) (regularisedComplexPullback g) =
      regularisedComplexPullback (regularisedSourceVectorLaplacian^[j] g) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      simpa only [Function.iterate_succ_apply'] using
        regularisedComplexPullback_laplacian
          ((regularisedSourceVectorLaplacian^[j]) g)
          (regularisedSourceVectorLaplacian_iterate_contDiff g hg j)

private theorem regularisedMollifiedSource_iterate_memLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (j : ℕ) :
    MemLp ((regularisedSourceVectorLaplacian^[j])
      (regUniformMollifiedInitial ρ ε hε a)) (2 : ℝ≥0∞) volume := by
  apply memLp_pi_iff.mpr
  intro i
  have hcomponent := regularisedSourceVectorLaplacian_iterate_component
    (regUniformMollifiedInitial ρ ε hε a)
    (regUniformMollifiedInitial_contDiff ρ ε hε ha) j i
  have heq : (fun x : Vec3 =>
      (regularisedSourceVectorLaplacian^[j]
        (regUniformMollifiedInitial ρ ε hε a)) x i) =
      (regularisedScalarLaplacian^[j]
        (fun x => regUniformMollifiedInitial ρ ε hε a x i)) := funext hcomponent
  rw [heq]
  exact regularisedMollifiedScalarIterate_ordered_memLp
    ρ ε hε a ha i j []

private theorem regularisedMollifiedSource_iterate_firstDerivative_memLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (j : ℕ) (i : Fin 3) :
    MemLp (regularisedSourceDirectionalDerivative i
      ((regularisedSourceVectorLaplacian^[j])
        (regUniformMollifiedInitial ρ ε hε a))) (2 : ℝ≥0∞) volume := by
  apply memLp_pi_iff.mpr
  intro c
  let g := (regularisedSourceVectorLaplacian^[j])
    (regUniformMollifiedInitial ρ ε hε a)
  have hg := regularisedSourceVectorLaplacian_iterate_contDiff
    (regUniformMollifiedInitial ρ ε hε a)
    (regUniformMollifiedInitial_contDiff ρ ε hε ha) j
  have hsource : (fun y : Vec3 => g y c) =
      (regularisedScalarLaplacian^[j]
        (fun y => regUniformMollifiedInitial ρ ε hε a y c)) := by
    funext y
    exact regularisedSourceVectorLaplacian_iterate_component
      (regUniformMollifiedInitial ρ ε hε a)
      (regUniformMollifiedInitial_contDiff ρ ε hε ha) j c y
  have hcomponent :
      (fun x : Vec3 => regularisedSourceDirectionalDerivative i g x c) =
        regularisedOrderedSpatialDerivative [i]
          ((regularisedScalarLaplacian^[j])
            (fun x => regUniformMollifiedInitial ρ ε hε a x c)) := by
    funext x
    rw [regularisedSourceDirectionalDerivative_component g hg i c x]
    rw [hsource]
    rfl
  rw [hcomponent]
  exact regularisedMollifiedScalarIterate_ordered_memLp
    ρ ε hε a ha c j [i]

private theorem regularisedMollifiedSource_iterate_secondDerivative_memLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (j : ℕ) (i : Fin 3) :
    MemLp (regularisedSourceDirectionalDerivative i
      (regularisedSourceDirectionalDerivative i
        ((regularisedSourceVectorLaplacian^[j])
          (regUniformMollifiedInitial ρ ε hε a)))) (2 : ℝ≥0∞) volume := by
  apply memLp_pi_iff.mpr
  intro c
  let g := (regularisedSourceVectorLaplacian^[j])
    (regUniformMollifiedInitial ρ ε hε a)
  have hg := regularisedSourceVectorLaplacian_iterate_contDiff
    (regUniformMollifiedInitial ρ ε hε a)
    (regUniformMollifiedInitial_contDiff ρ ε hε ha) j
  have hDg := regularisedSourceDirectionalDerivative_contDiff g hg i
  have hsource : (fun y : Vec3 => g y c) =
      (regularisedScalarLaplacian^[j]
        (fun y => regUniformMollifiedInitial ρ ε hε a y c)) := by
    funext y
    exact regularisedSourceVectorLaplacian_iterate_component
      (regUniformMollifiedInitial ρ ε hε a)
      (regUniformMollifiedInitial_contDiff ρ ε hε ha) j c y
  have hcomponent :
      (fun x : Vec3 => regularisedSourceDirectionalDerivative i
        (regularisedSourceDirectionalDerivative i g) x c) =
        regularisedOrderedSpatialDerivative [i, i]
          ((regularisedScalarLaplacian^[j])
            (fun x => regUniformMollifiedInitial ρ ε hε a x c)) := by
    funext x
    rw [regularisedSourceSecondDerivative_component g hg i c x]
    rw [hsource]
    simp [regularisedOrderedSpatialDerivative]
  rw [hcomponent]
  exact regularisedMollifiedScalarIterate_ordered_memLp
    ρ ε hε a ha c j [i, i]

/-- Every even-order Bessel space contains the physical L² class of the
smooth mollification of an `IsInJ` initial field. -/
theorem regUniformMollifiedInitial_bessel_even_lift
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (k : ℕ) :
    ∃ b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2,
      regularisedBesselSobolevToL2 ((2 * k : ℕ) : ℝ)
        (by positivity) b =
      complexifyVectorL2
        ((lerayHopfLimit_initialField_memLp
          (regUniformMollifiedInitial ρ ε hε a)
          (regMollifiedInitial_isInJ ρ ε hε ha).1).toLp
            (regUniformSpatialField (regUniformMollifiedInitial ρ ε hε a))) := by
  let V : Vec3 → Vec3 := regUniformMollifiedInitial ρ ε hε a
  let f : L2Vec3 → ComplexVec3 := regularisedComplexPullback V
  have hV : ContDiff ℝ (⊤ : ℕ∞) V := regUniformMollifiedInitial_contDiff ρ ε hε ha
  have hsourceLp (j : ℕ) :
      MemLp ((regularisedSourceVectorLaplacian^[j]) V)
        (2 : ℝ≥0∞) volume := by
    simpa [V] using regularisedMollifiedSource_iterate_memLp ρ ε hε a ha j
  have hLp (j : ℕ) :
      MemLp ((regularisedL2ClassicalLaplacian^[j]) f)
        (2 : ℝ≥0∞) volume := by
    rw [regularisedComplexPullback_iterate_laplacian V hV j]
    exact regularisedComplexPullback_memLp _ (hsourceLp j)
  have hD1 (j : ℕ) (i : Fin 3) :
      MemLp (fun x => fderiv ℝ
        ((regularisedL2ClassicalLaplacian^[j]) f) x
          (regularisedL2CoordinateBasis i)) (2 : ℝ≥0∞) volume := by
    rw [regularisedComplexPullback_iterate_laplacian V hV j]
    have heq : (fun x : L2Vec3 => fderiv ℝ
        (regularisedComplexPullback
          ((regularisedSourceVectorLaplacian^[j]) V)) x
          (regularisedL2CoordinateBasis i)) =
        regularisedComplexPullback
          (regularisedSourceDirectionalDerivative i
            ((regularisedSourceVectorLaplacian^[j]) V)) := by
      funext x
      exact regularisedComplexPullback_directionalDerivative
        ((regularisedSourceVectorLaplacian^[j]) V)
        (regularisedSourceVectorLaplacian_iterate_contDiff V hV j) i x
    rw [heq]
    exact regularisedComplexPullback_memLp _
      (by simpa [V] using
        (regularisedMollifiedSource_iterate_firstDerivative_memLp
          ρ ε hε a ha j i))
  have hD2 (j : ℕ) (i : Fin 3) :
      MemLp (fun x => fderiv ℝ
        (fun y => fderiv ℝ ((regularisedL2ClassicalLaplacian^[j]) f) y
          (regularisedL2CoordinateBasis i)) x
            (regularisedL2CoordinateBasis i)) (2 : ℝ≥0∞) volume := by
    rw [regularisedComplexPullback_iterate_laplacian V hV j]
    have hfirst : (fun y : L2Vec3 => fderiv ℝ
        (regularisedComplexPullback
          ((regularisedSourceVectorLaplacian^[j]) V)) y
          (regularisedL2CoordinateBasis i)) =
        regularisedComplexPullback
          (regularisedSourceDirectionalDerivative i
            ((regularisedSourceVectorLaplacian^[j]) V)) := by
      funext y
      exact regularisedComplexPullback_directionalDerivative
        ((regularisedSourceVectorLaplacian^[j]) V)
        (regularisedSourceVectorLaplacian_iterate_contDiff V hV j) i y
    rw [hfirst]
    have heq : (fun x : L2Vec3 => fderiv ℝ
        (regularisedComplexPullback
          (regularisedSourceDirectionalDerivative i
            ((regularisedSourceVectorLaplacian^[j]) V))) x
          (regularisedL2CoordinateBasis i)) =
        regularisedComplexPullback
          (regularisedSourceDirectionalDerivative i
            (regularisedSourceDirectionalDerivative i
              ((regularisedSourceVectorLaplacian^[j]) V))) := by
      funext x
      exact regularisedComplexPullback_directionalDerivative
        (regularisedSourceDirectionalDerivative i
          ((regularisedSourceVectorLaplacian^[j]) V))
        (regularisedSourceDirectionalDerivative_contDiff
          ((regularisedSourceVectorLaplacian^[j]) V)
          (regularisedSourceVectorLaplacian_iterate_contDiff V hV j) i) i x
    rw [heq]
    exact regularisedComplexPullback_memLp _
      (by simpa [V] using
        (regularisedMollifiedSource_iterate_secondDerivative_memLp
          ρ ε hε a ha j i))
  obtain ⟨b, hb⟩ := regularised_smooth_L2_even_lift_of_classical_iterates
    k f (by
      have hT : ContDiff ℝ (⊤ : ℕ∞)
          (complexifyValue.comp l2Vec3Equiv.symm.toContinuousLinearMap) :=
        ((complexifyValue.comp l2Vec3Equiv.symm.toContinuousLinearMap).contDiff).of_le
          (show (⊤ : ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun x => (complexifyValue.comp l2Vec3Equiv.symm.toContinuousLinearMap)
          (V (l2Vec3Equiv x)))
      exact hT.comp (hV.comp l2Vec3Equiv.contDiff)) hLp hD1 hD2
  refine ⟨b, ?_⟩
  have hreal : MemLp (regUniformSpatialField V) (2 : ℝ≥0∞) volume :=
    lerayHopfLimit_initialField_memLp V
      (regMollifiedInitial_isInJ ρ ε hε ha).1
  have hbase : (hLp 0).toLp f =
      complexifyVectorL2 (hreal.toLp (regUniformSpatialField V)) := by
    have hmemf : MemLp f (2 : ℝ≥0∞) volume := by
      simpa [Function.iterate_zero] using hLp 0
    apply Lp.ext
    filter_upwards [hmemf.coeFn_toLp,
      complexifyValue.coeFn_compLpL (p := 2) (μ := volume)
        (hreal.toLp (regUniformSpatialField V)),
      hreal.coeFn_toLp] with x hf hc hr
    change (hLp 0).toLp f x =
      (complexifyValue.compLpL 2 volume
        (hreal.toLp (regUniformSpatialField V))) x
    rw [hf, hc, hr]
    change complexifyValue (WithLp.toLp 2 (V (WithLp.ofLp x))) =
      complexifyValue (WithLp.toLp 2 (V (WithLp.ofLp x)))
    rfl
  rw [hb, hbase]

end CKN.Leray

end
