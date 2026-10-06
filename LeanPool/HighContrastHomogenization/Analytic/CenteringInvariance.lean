/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.DualNormJunk

/-!
# High-contrast homogenization: Analytic.CenteringInvariance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Flux centering, and the classes that must not be vacuous

The flux differences of `e.random.dirichlet` and `e.random.corrector` are
written for the skew-centered coefficient field.  The first section is the
reason: a constant antisymmetric matrix added to the coefficient field and to
the homogenized matrix leaves the centered flux difference unchanged, while it
moves the uncentered difference by that matrix applied to the difference of the
two gradients — a quantity no datum of the hypotheses sees.

The remaining sections check that the corrector equation of
`t.random.homogenization`, the growth condition of the Liouville class
`e.random.liouville.growth` and the coefficient-weighted energies of the
weighted solution spaces of `s.introduction` are not satisfied by the failure of
an integral: each pairing carries its own absolute convergence, each energy is
valued in `ℝ≥0∞`, and each class is inhabited by the zero field, so none of them
is vacuous in either direction.  A ball sandwich finally makes its domain
nonempty, hence of positive volume, which is what keeps the volume averages and
volume-normalized norms from collapsing.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The centering convention makes the flux displays invariant

A constant antisymmetric matrix added to the coefficient field changes neither
the solutions nor the coarse-grained blocks, and it moves the homogenized matrix
by the same constant.  The flux differences of the two estimates are written for
the skew-centered field precisely so that they are unmoved by that change; the
displays written with the full homogenized matrix are moved by it, and by a
quantity no datum of the hypotheses sees. -/

theorem isSkewMat_apply {h : Mat d} (hh : IsSkewMat h) (i j : Fin d) :
    h j i = -h i j := by
  have := congrFun (congrFun hh i) j
  simpa [matTranspose, Matrix.transpose_apply, Matrix.neg_apply] using this

theorem symmPart_add_isSkewMat {M h : Mat d} (hh : IsSkewMat h) :
    symmPart (M + h) = symmPart M := by
  ext i j
  have hji := isSkewMat_apply hh i j
  simp only [symmPart, Matrix.add_apply]
  rw [hji]
  ring

theorem skewPart_add_isSkewMat {M h : Mat d} (hh : IsSkewMat h) :
    skewPart (M + h) = skewPart M + h := by
  ext i j
  have hji := isSkewMat_apply hh i j
  simp only [skewPart, Matrix.add_apply]
  rw [hji]
  ring

/-- The skew-centered flux difference is invariant under adding a constant
antisymmetric matrix to the coefficient field and to the homogenized matrix. -/
theorem centeredFlux_add_isSkewMat {A B h : Mat d} (hh : IsSkewMat h)
    (F G : Vec d) :
    matVecMul (A + h - skewPart (B + h)) F - matVecMul (symmPart (B + h)) G
      = matVecMul (A - skewPart B) F - matVecMul (symmPart B) G := by
  rw [symmPart_add_isSkewMat hh, skewPart_add_isSkewMat hh]
  have harg : A + h - (skewPart B + h) = A - skewPart B := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  rw [harg]

/-- The uncentered flux difference is NOT invariant: it moves by the constant
antisymmetric matrix applied to the difference of the two gradients.  This is
the quantity that neither the shape datum nor the reference aspect ratio sees,
and it is why the displays are written for the centered field. -/
theorem uncenteredFlux_add_isSkewMat (A B h : Mat d) (F G : Vec d) :
    matVecMul (A + h) F - matVecMul (B + h) G
      = (matVecMul A F - matVecMul B G) + matVecMul h (F - G) := by
  funext i
  simp only [matVecMul, Matrix.add_apply, Pi.sub_apply, Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## The weak equation is fail-closed -/

/-- The mechanism the weak equation used here closes: with a totalized Bochner
pairing, a flux that pairs divergently against a test satisfies the printed
identity at that test for no reason at all. -/
theorem integral_weakPairing_eq_zero_of_not_integrableOn
    (b : CoeffField d) (V : Set (Vec d)) (F : Vec d → Vec d) (φ : Vec d → ℝ)
    (h : ¬ IntegrableOn
      (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (F x))) V volume) :
    ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (b x) (F x)) ∂volume = 0 :=
  integral_undef h

/-- `IsWeakSolutionOn` excludes exactly that: it asserts absolute convergence
at every test. -/
theorem integrableOn_of_isWeakSolutionOn {b : CoeffField d} {V : Set (Vec d)}
    {F : Vec d → Vec d} (h : IsWeakSolutionOn b V F) {φ : Vec d → ℝ}
    (hφ : IsLocalTest V φ) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (F x))) V
      volume :=
  (h φ hφ).1

/-- The zero field solves the equation, so the class is nonempty. -/
theorem isWeakSolutionOn_zero (b : CoeffField d) (V : Set (Vec d)) :
    IsWeakSolutionOn b V (fun _ => (0 : Vec d)) := by
  intro φ _
  have hz : ∀ x : Vec d,
      vecDot (smoothGrad φ x) (matVecMul (b x) ((fun _ => (0 : Vec d)) x)) = 0 := by
    intro x
    simp [matVecMul, vecDot]
  constructor
  · simp [hz]
  · simp [hz]

/-! ## The growth condition of the Liouville class is fail-closed

The Liouville clause is a double inclusion, so its class appears both as a
hypothesis and as a conclusion and admits no junk in either direction.  Under a
totalized real average, a function whose square is not integrable on a ball is
assigned normalized `L²` average `0` there, so the growth condition holds for it
by the failure of the average; the class is junk-enlarged and the inclusion that
classifies its members is false. -/

/-- The mechanism, for the growth condition. -/
theorem sqrt_volumeAverage_sq_eq_zero_of_not_integrableOn (V : Set (Vec d))
    (v : Vec d → ℝ) (h : ¬ IntegrableOn (fun x => v x ^ 2) V volume) :
    Real.sqrt (volumeAverage V fun x => v x ^ 2) = 0 := by
  rw [volumeAverage_eq_zero_of_not_integrableOn V h, Real.sqrt_zero]

/-- The normalized `L²` norm of the zero function is zero, so the growth
condition is not vacuous in the other direction either. -/
theorem normalizedL2Norm_zero (V : Set (Vec d)) :
    normalizedL2Norm V (fun _ => (0 : ℝ)) = 0 := by
  unfold normalizedL2Norm
  have h : (fun x : Vec d => ENNReal.ofReal ((fun _ => (0 : ℝ)) x ^ 2))
      = fun _ => (0 : ℝ≥0∞) := by
    funext _
    simp
  rw [h, eVolumeAverage_zero, ENNReal.zero_rpow_of_pos (by norm_num)]

/-! ## The energies are fail-closed -/

/-- The mechanism for the weighted energies: under a totalized Bochner integral
a divergent Dirichlet energy is valued at `0`, making the `H¹_s` approximation
conditions satisfiable by fields of infinite energy. -/
theorem integral_sEnergy_eq_zero_of_not_integrableOn (b : CoeffField d)
    (V : Set (Vec d)) (F : Vec d → Vec d)
    (h : ¬ IntegrableOn
      (fun x => vecDot (F x) (matVecMul (symmPart (b x)) (F x))) V volume) :
    ∫ x in V, vecDot (F x) (matVecMul (symmPart (b x)) (F x)) ∂volume = 0 :=
  integral_undef h

/-- `sEnergyOn` is the Lebesgue integral of the same nonnegative integrand, so
it is infinite exactly where the energy is. -/
theorem sEnergyOn_eq_top_of_not_integrableOn (b : CoeffField d)
    (V : Set (Vec d)) (F : Vec d → Vec d)
    (hmeas : AEStronglyMeasurable
      (fun x => vecDot (F x) (matVecMul (symmPart (b x)) (F x)))
      (volume.restrict V))
    (hnonneg : 0 ≤ᵐ[volume.restrict V]
      fun x => vecDot (F x) (matVecMul (symmPart (b x)) (F x)))
    (h : ¬ IntegrableOn
      (fun x => vecDot (F x) (matVecMul (symmPart (b x)) (F x))) V volume) :
    sEnergyOn b V F = ⊤ := by
  unfold sEnergyOn
  by_contra hne
  exact h ⟨hmeas, (hasFiniteIntegral_iff_ofReal hnonneg).2 (lt_top_iff_ne_top.2 hne)⟩

/-- The zero field has zero energy. -/
theorem sEnergyOn_zero (b : CoeffField d) (V : Set (Vec d)) :
    sEnergyOn b V (fun _ => (0 : Vec d)) = 0 := by
  unfold sEnergyOn
  have hz : ∀ x : Vec d,
      vecDot ((fun _ => (0 : Vec d)) x)
        (matVecMul (symmPart (b x)) ((fun _ => (0 : Vec d)) x)) = 0 := by
    intro x
    simp [matVecMul, vecDot]
  simp [hz]

theorem h1sNormSqOn_zero (b : CoeffField d) (V : Set (Vec d)) :
    h1sNormSqOn b V (fun _ => (0 : ℝ)) (fun _ => (0 : Vec d)) = 0 := by
  unfold h1sNormSqOn
  rw [sEnergyOn_zero]
  simp

theorem skewFluxPairing_zero (b : CoeffField d) (V : Set (Vec d))
    (φ : Vec d → ℝ) :
    skewFluxPairing b V (fun _ => (0 : Vec d)) φ = 0 := by
  unfold skewFluxPairing
  have hz : ∀ x : Vec d,
      vecDot (smoothGrad φ x)
        (matVecMul (skewPart (b x)) ((fun _ => (0 : Vec d)) x)) = 0 := by
    intro x
    simp [matVecMul, vecDot]
  rw [ite_eq_left (by simp [hz] : IntegrableOn
      (fun x => vecDot (smoothGrad φ x)
        (matVecMul (skewPart (b x)) ((fun _ => (0 : Vec d)) x))) V volume)]
  simp [hz]

theorem skewFluxDualNorm_zero (b : CoeffField d) (V : Set (Vec d)) :
    skewFluxDualNorm b V (fun _ => (0 : Vec d)) = 0 := by
  unfold skewFluxDualNorm
  simp [skewFluxPairing_zero]

/-- The `H¹_{a,0}` class is nonempty: the zero pair belongs to it.  The
Dirichlet clause is therefore not vacuous through the failure of its solution
hypothesis. -/
theorem memH1a0_zero (b : CoeffField d) (V : Set (Vec d)) :
    MemH1a0 b V (fun _ => (0 : ℝ)) (fun _ => (0 : Vec d)) := by
  have hgrad : (fun x : Vec d =>
      smoothGrad (fun _ => (0 : ℝ)) x - (fun _ => (0 : Vec d)) x)
      = fun _ => (0 : Vec d) := by
    funext x
    simp [smoothGrad_zero]
  have hfun : (fun x : Vec d => (0 : ℝ) - (0 : ℝ)) = fun _ => (0 : ℝ) := by
    funext _
    simp
  refine ⟨⟨aestronglyMeasurable_const, fun _ => aestronglyMeasurable_const⟩, ?_,
    fun _ _ => (0 : ℝ), fun _ => isLocalTest_zero V, ?_, ?_⟩
  · intro _ _ _ _ _
    simp
  · have h : (fun _ : ℕ =>
        h1sNormSqOn b V (fun x => (0 : ℝ) - (0 : ℝ))
          (fun x => smoothGrad (fun _ => (0 : ℝ)) x - (fun _ => (0 : Vec d)) x))
        = fun _ => (0 : ℝ≥0∞) := by
      funext _
      rw [hgrad, hfun]
      exact h1sNormSqOn_zero b V
    rw [h]
    exact tendsto_const_nhds
  · have h : (fun _ : ℕ =>
        skewFluxDualNorm b V
          (fun x => smoothGrad (fun _ => (0 : ℝ)) x - (fun _ => (0 : Vec d)) x))
        = fun _ => (0 : ℝ≥0∞) := by
      funext _
      rw [hgrad]
      exact skewFluxDualNorm_zero b V
    rw [h]
    exact tendsto_const_nhds

/-! ## The domain guard

Every volume-normalized quantity above divides by `volume V`, and on a null `V`
each of them collapses to zero: the estimates would then hold by the collapse of
both sides.  The clause that carries a domain therefore binds a positive inner
radius, and that single binder is what makes the domain nonempty, hence of
positive volume. -/

/-- A ball sandwich makes the domain nonempty. -/
theorem HasBallSandwich.nonempty {U : Set (Vec d)} {ρ Rad : ℝ}
    (h : HasBallSandwich U ρ Rad) : U.Nonempty := by
  obtain ⟨hρ, -, c, hin, -⟩ := h
  refine ⟨c, hin ?_⟩
  have : (c - c) = (0 : Vec d) := by
    funext i
    simp
  simp only [euclideanBallAt, Set.mem_ofPred_eq, this, vecNormSq_zero_vec]
  positivity

end

end HighContrast
end HCPolySupport
