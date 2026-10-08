/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AnnealedVanishing

/-!
# High-contrast homogenization: Provider.Response.ResponseCongruence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The response sees only the almost everywhere class of the coefficient

Membership in the admissible class of a variational response problem is stable
under changing the coefficient on a null set: being a potential is a condition
on the field alone, and being solenoidal against every compactly supported test
gradient is an integral condition.  The response integrand is a pointwise
expression in the coefficient and the admissible gradient, so its normalized
average is unchanged as well.  Consequently the whole value set of the response
functional, and with it the response itself, depends on the coefficient only
through its almost everywhere class.

This is what turns the pathwise translation covariance of the response into a
statement about a coefficient sample: the translated sample and the translated
field agree almost everywhere, not everywhere.  Combining the two gives the
covariance under integer translations, and under a translation invariant law
the annealed response of a cube depends on the cube only through its scale.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open MeasureTheory

variable {d : ℕ}

/-! ## Almost everywhere stability of the admissible class -/

/-- An `a`-harmonic function is `b`-harmonic whenever `a` and `b` agree almost
everywhere, with the same underlying Sobolev function. -/
@[expose]
def aHarmonicOfAEEq {U : Set (Vec d)} {f g : CoeffField d}
    (h : f =ᵐ[volumeMeasureOn U] g) (u : AHarmonicFunction f U) :
    AHarmonicFunction g U where
  toH1 := u.toH1
  isHarmonic := IsAHarmonicGradient.of_ae_eq_coeff h u.isHarmonic

/-- The transported admissible function has the same gradient. -/
@[simp] theorem aHarmonicOfAEEq_grad {U : Set (Vec d)} {f g : CoeffField d}
    (h : f =ᵐ[volumeMeasureOn U] g) (u : AHarmonicFunction f U) :
    (aHarmonicOfAEEq h u).toH1.grad = u.toH1.grad := rfl

/-! ## Almost everywhere congruence of the response -/

/-- One inclusion of the value-set congruence. -/
theorem responseJValueSet_subset_of_ae_eq (U : Set (Vec d)) (p q : Vec d)
    {f g : CoeffField d} (h : f =ᵐ[volumeMeasureOn U] g) :
    responseJValueSet U p q f ⊆ responseJValueSet U p q g := by
  rintro m ⟨u, rfl⟩
  refine ⟨aHarmonicOfAEEq h u, ?_⟩
  unfold volumeAverage
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  simp only [scalarResponseIntegrand, aHarmonicOfAEEq_grad, hx]

/-- **The response value set sees only the almost everywhere class of the
coefficient.** -/
theorem responseJValueSet_congr_of_ae_eq (U : Set (Vec d)) (p q : Vec d)
    {f g : CoeffField d} (h : f =ᵐ[volumeMeasureOn U] g) :
    responseJValueSet U p q f = responseJValueSet U p q g :=
  Set.Subset.antisymm (responseJValueSet_subset_of_ae_eq U p q h)
    (responseJValueSet_subset_of_ae_eq U p q h.symm)

/-- **The response sees only the almost everywhere class of the coefficient**,
in the form restricted to the domain. -/
theorem ResponseJ_congr_of_ae_eq_restrict (U : Set (Vec d)) (p q : Vec d)
    {f g : CoeffField d} (h : f =ᵐ[volumeMeasureOn U] g) :
    ResponseJ U p q f = ResponseJ U p q g := by
  unfold ResponseJ
  rw [responseJValueSet_congr_of_ae_eq U p q h]

/-- **The response sees only the almost everywhere class of the
coefficient.** -/
theorem ResponseJ_congr_of_ae_eq (U : Set (Vec d)) (p q : Vec d)
    {f g : CoeffField d} (h : f =ᵐ[volume] g) :
    ResponseJ U p q f = ResponseJ U p q g :=
  ResponseJ_congr_of_ae_eq_restrict U p q (ae_restrict_of_ae h)

/-! ## Covariance of the response of a sample under integer translations -/

/-- **`J(U + z; a) = J(U; T_z a)`.**  The pathwise translation covariance of the
response at every sample of the coefficient space. -/
theorem ResponseJ_translateSet_intTranslation (z : Fin d → ℤ) (U : Set (Vec d))
    (p q : Vec d) (a : CoeffSpace d) :
    ResponseJ (translateSet (Source.AKL.intTranslation z) U) p q
        (⇑a.1 : Vec d → Mat d) =
      ResponseJ U p q (⇑(translateCoeff z a).1 : Vec d → Mat d) := by
  rw [ResponseJ_translateSet_eq_translateCoeffField]
  exact (ResponseJ_congr_of_ae_eq U p q (Recurrence.coe_translateCoeff_ae_eq z a)).symm

/-! ## Triadic cubes of nonnegative scale are integer translates -/

/-- A triadic cube of nonnegative scale is an integer translate of the centered
cube of the same scale. -/
theorem exists_intVec_openCubeSet_eq_translateSet (R : TriadicCube d)
    (hscale : 0 ≤ R.scale) :
    ∃ z : Fin d → ℤ,
      openCubeSet R =
        translateSet (Source.AKL.intTranslation z)
          (openCubeSet (originCube d R.scale)) := by
  refine ⟨fun i => R.index i * 3 ^ R.scale.toNat, ?_⟩
  have hcast : ∀ i : Fin d,
      ((R.index i * 3 ^ R.scale.toNat : ℤ) : ℝ) =
        (R.index i : ℝ) * (3 : ℝ) ^ R.scale := by
    intro i
    have hpow : ((3 ^ R.scale.toNat : ℤ) : ℝ) = (3 : ℝ) ^ R.scale := by
      have h1 : ((3 ^ R.scale.toNat : ℤ) : ℝ) = (3 : ℝ) ^ (R.scale.toNat : ℕ) := by
        push_cast
        ring
      rw [h1, ← zpow_natCast (3 : ℝ) R.scale.toNat, Int.toNat_of_nonneg hscale]
    rw [Int.cast_mul, hpow]
  have hmem : ∀ y : Vec d, y ∈ openCubeSet R ↔
      ∀ i, ((R.index i : ℝ) - 1 / 2) * (3 : ℝ) ^ R.scale < y i ∧
        y i < ((R.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ R.scale :=
    fun _ => Iff.rfl
  have hmem0 : ∀ y : Vec d, y ∈ openCubeSet (originCube d R.scale) ↔
      ∀ i, ((0 : ℝ) - 1 / 2) * (3 : ℝ) ^ R.scale < y i ∧
        y i < ((0 : ℝ) + 1 / 2) * (3 : ℝ) ^ R.scale := by
    intro y
    constructor
    · intro hy i
      simpa [originCube, cubeScaleFactor] using hy i
    · intro hy i
      simpa [originCube, cubeScaleFactor] using hy i
  ext x
  rw [mem_translateSet_iff_sub_mem, hmem, hmem0]
  have hsub : ∀ i : Fin d,
      (x - Source.AKL.intTranslation
          (fun i => R.index i * 3 ^ R.scale.toNat)) i =
        x i - (R.index i : ℝ) * (3 : ℝ) ^ R.scale := by
    intro i
    simp only [Pi.sub_apply, Source.AKL.intTranslation]
    rw [hcast i]
  constructor
  · intro hx i
    have hi := hx i
    rw [hsub i]
    constructor <;> linarith only [hi.1, hi.2]
  · intro hx i
    have hi := hx i
    rw [hsub i] at hi
    constructor <;> linarith only [hi.1, hi.2]

/-- The response on a triadic cube of nonnegative scale is the response on the
centered cube of the same scale, at a translated sample. -/
theorem exists_translateCoeff_ResponseJ_openCubeSet (R : TriadicCube d)
    (hscale : 0 ≤ R.scale) (p q : Vec d) :
    ∃ z : Fin d → ℤ, ∀ a : CoeffSpace d,
      ResponseJ (openCubeSet R) p q (⇑a.1 : Vec d → Mat d) =
        ResponseJ (openCubeSet (originCube d R.scale)) p q
          (⇑(translateCoeff z a).1 : Vec d → Mat d) := by
  obtain ⟨z, hz⟩ := exists_intVec_openCubeSet_eq_translateSet R hscale
  refine ⟨z, fun a => ?_⟩
  rw [hz]
  exact ResponseJ_translateSet_intTranslation z _ p q a

/-! ## The unconditional annealed vanishing -/

/-- **The cutoff-weighted child responses vanish in the mean**, with no carried
covariance hypothesis.  The only inputs are the stationarity of the law, the
nonnegativity of the child scale, the mean-one normalization of the cutoff, and
integrability. -/
theorem integral_descendantsAverage_cutoffWeighted_ResponseJ_eq_zero
    {P : Measure (CoeffSpace d)} (hP : HCPoly.Frozen.IsStationaryLaw P)
    (Q : TriadicCube d) (j : ℕ) (hscale : 0 ≤ Q.scale - (j : ℤ))
    (p q : Vec d) {φ : Vec d → ℝ}
    (hint : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun a : CoeffSpace d =>
        ResponseJ (openCubeSet R) p q (⇑a.1 : Vec d → Mat d)) P)
    (hbase : Integrable (fun a : CoeffSpace d =>
      ResponseJ (openCubeSet (originCube d (Q.scale - (j : ℤ)))) p q
        (⇑a.1 : Vec d → Mat d)) P)
    (hφ : IntegrableOn φ (cubeSet Q) volume) (hmean : cubeAverage Q φ = 1) :
    ∫ a, descendantsAverage Q j
        (fun R => (1 - cubeAverage R φ) *
          ResponseJ (openCubeSet R) p q (⇑a.1 : Vec d → Mat d)) ∂P = 0 := by
  refine integral_descendantsAverage_cutoffWeighted_eq_zero_of_covariance hP Q j
    (fun R a => ResponseJ (openCubeSet R) p q (⇑a.1 : Vec d → Mat d))
    (originCube d (Q.scale - (j : ℤ))) hint hbase ?_ hφ hmean
  intro R hR
  have hRs : R.scale = Q.scale - (j : ℤ) :=
    scale_eq_sub_of_mem_descendantsAtDepth hR
  have hRscale : 0 ≤ R.scale := by rw [hRs]; exact hscale
  obtain ⟨z, hz⟩ := exists_translateCoeff_ResponseJ_openCubeSet R hRscale p q
  refine ⟨z, fun a => ?_⟩
  show ResponseJ (openCubeSet R) p q (⇑a.1 : Vec d → Mat d) =
    ResponseJ (openCubeSet (originCube d (Q.scale - (j : ℤ)))) p q
      (⇑(translateCoeff z a).1 : Vec d → Mat d)
  rw [← hRs]
  exact hz a

end

end Response
end HighContrast
end HCPolySupport
