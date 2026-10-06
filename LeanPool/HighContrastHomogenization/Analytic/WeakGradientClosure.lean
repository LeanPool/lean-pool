/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.LocalIntegrability
public import LeanPool.HighContrastHomogenization.Analytic.WeightedEnergy
public import LeanPool.HighContrastHomogenization.Analytic.WeakPairing
public import LeanPool.HighContrastHomogenization.Analytic.ClassHonesty
public import LeanPool.HighContrastHomogenization.Analytic.ClassPairing

/-!
# High-contrast homogenization: Analytic.WeakGradientClosure

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The weak-gradient relation is an identity between convergent integrals

`HasWeakGradientOn U u Du` compares two Bochner integrals.  A Bochner integral
of a non-integrable integrand is `0`, so a pair whose pairings all diverge
satisfies the relation as `0 = -0`, saying nothing.  The disposition taken here
is not to change the relation but to prove that this branch is unreachable on
the classes the homogenization theorem actually reads: for a member of
`H¹_{s,loc}(ℝ^d)` and a local test on a centred ball, **both** pairings converge
absolutely, so the relation is an identity between genuine integrals.

The hypotheses used are exactly the coefficient class hypotheses `0 < lam` and
almost-everywhere ellipticity, the measurability of the pair, and membership in
the local class.  The ellipticity assumption is **not** removable: on a field
that vanishes identically every weighted energy vanishes, and the class then
constrains the gradient field by nothing beyond measurability.  At the places
`t.random.homogenization` reads these classes the field is
a member of the coefficient space, whose defining condition supplies exactly
those two hypotheses; the class-level wrappers at the end of the module state
the results in that form.

The final group of lemmas records what the measurability condition of the class
buys.  A function invisible to both the lower Lebesgue integral and the Bochner
integrals lands in the class with zero weak gradient whatever its measurability;
with the measurability condition present the same construction is degenerate,
producing only the zero function.  Whether the wider class without that
condition is strictly wider is a question about sets of inner measure zero and
is not settled here: the possibility that the two classes coincide is not ruled
out, so the construction below may be vacuous.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal
open scoped Matrix

noncomputable section

variable {d : ℕ}

/-! ## Absolute convergence of both pairings -/

/-- **The closure lemma.**  For a pair of the local class and a local test on a
centred ball, **both** pairings of the weak-gradient relation are absolutely
convergent.  The branch valuing a non-integrable integrand at `0` is therefore
unreachable on this class.

Hypotheses used, in full: local uniform ellipticity of the coefficient field,
whose constants are read on the ball; almost everywhere strong measurability of
`v` and of the components of `Dv` on the ball; membership in `MemH1sLoc`; and `φ`
a local test on the ball. -/
theorem integrableOn_weakGradientPairings_of_memH1sLoc {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d} {R : ℝ} (hR : 0 < R)
    (hvmeas : AEStronglyMeasurable v (volume.restrict (euclideanBall d R)))
    (hDmeas : ∀ j, AEStronglyMeasurable (fun x => Dv x j)
      (volume.restrict (euclideanBall d R)))
    (hv : MemH1sLoc b v Dv) {φ : Vec d → ℝ}
    (hφ : IsLocalTest (euclideanBall d R) φ) (i : Fin d) :
    IntegrableOn (fun x => v x * (fderiv ℝ φ x) (basisVec i))
        (euclideanBall d R) volume ∧
      IntegrableOn (fun x => Dv x i * φ x) (euclideanBall d R) volume := by
  have hVfin : volume (euclideanBall d R) ≠ ⊤ :=
    (isBounded_euclideanBall d hR).measure_lt_top.ne
  obtain ⟨B, hB⟩ := exists_bound_smoothGrad_of_isLocalTest hφ i
  obtain ⟨C, hC⟩ := exists_bound_of_isLocalTest hφ
  have hvL1 : IntegrableOn v (euclideanBall d R) volume :=
    integrableOn_of_memH1sLoc hv hR hvmeas
  obtain ⟨lam, Lam, hlam, -, hell⟩ :=
    hb.exists_ae_isEllipticMatrix_euclideanBall hR
  have hDL2 : IntegrableOn (fun x => vecNormSq (Dv x)) (euclideanBall d R) volume :=
    integrableOn_vecNormSq_of_sEnergyOn_ne_top_restrict (Lam := Lam) hlam hell
      hDmeas (sEnergyOn_ne_top_of_memH1sLoc hb hv hR)
  have hDL1 : IntegrableOn (fun x => Dv x i) (euclideanBall d R) volume :=
    integrableOn_apply_of_integrableOn_vecNormSq hVfin hDmeas hDL2 i
  refine ⟨hvL1.mul_bdd (c := B) ?_ ?_, hDL1.mul_bdd (c := C) ?_ ?_⟩
  · exact ((continuous_apply i).comp
      (continuous_smoothGrad hφ.contDiff)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hB x
  · exact hφ.contDiff.continuous.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hC x

/-- **The closure, in the form the weak-gradient relation is read.**  Both
pairings converge absolutely **and** the identity holds between them.  This is
the statement that the `0 = -0` branch is not what membership in the local class
is asserting. -/
theorem weakGradientPairing_eq_of_memH1sLoc {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d} {R : ℝ} (hR : 0 < R)
    (hvmeas : AEStronglyMeasurable v (volume.restrict (euclideanBall d R)))
    (hDmeas : ∀ j, AEStronglyMeasurable (fun x => Dv x j)
      (volume.restrict (euclideanBall d R)))
    (hv : MemH1sLoc b v Dv) {φ : Vec d → ℝ}
    (hφ : IsLocalTest (euclideanBall d R) φ) (i : Fin d) :
    IntegrableOn (fun x => v x * (fderiv ℝ φ x) (basisVec i))
        (euclideanBall d R) volume ∧
      IntegrableOn (fun x => Dv x i * φ x) (euclideanBall d R) volume ∧
      ∫ x in euclideanBall d R, v x * (fderiv ℝ φ x) (basisVec i) ∂volume =
        -∫ x in euclideanBall d R, Dv x i * φ x ∂volume := by
  obtain ⟨h1, h2⟩ := integrableOn_weakGradientPairings_of_memH1sLoc hb hR
    hvmeas hDmeas hv hφ i
  exact ⟨h1, h2,
    (hv.2 R hR).1 i φ hφ.contDiff hφ.hasCompactSupport hφ.tsupport_subset⟩

/-- **The localized form at `V = Set.univ`.**  A local test on all of `ℝ^d` has
compact support, so the ball form transfers. -/
theorem integrableOn_weakGradientPairings_univ_of_memH1sLoc {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (hvmeas : AEStronglyMeasurable v volume)
    (hDmeas : ∀ j, AEStronglyMeasurable (fun x => Dv x j) volume)
    (hv : MemH1sLoc b v Dv) {φ : Vec d → ℝ}
    (hφ : IsLocalTest (Set.univ : Set (Vec d)) φ) (i : Fin d) :
    IntegrableOn (fun x => v x * (fderiv ℝ φ x) (basisVec i))
        (Set.univ : Set (Vec d)) volume ∧
      IntegrableOn (fun x => Dv x i * φ x) (Set.univ : Set (Vec d)) volume := by
  obtain ⟨R, hR, hKR⟩ := exists_euclideanBall_superset_of_isCompact
    (hφ.hasCompactSupport : IsCompact (tsupport φ))
  have hφ' : IsLocalTest (euclideanBall d R) φ :=
    ⟨hφ.contDiff, hφ.hasCompactSupport, hKR⟩
  obtain ⟨h1, h2⟩ := integrableOn_weakGradientPairings_of_memH1sLoc hb hR
    hvmeas.restrict (fun j => (hDmeas j).restrict) hv hφ' i
  refine ⟨h1.of_forall_sdiff_eq_zero MeasurableSet.univ ?_,
    h2.of_forall_sdiff_eq_zero MeasurableSet.univ ?_⟩
  · intro x hx
    have hxn : x ∉ tsupport φ := fun hmem => hx.2 (hKR hmem)
    have hzero : smoothGrad φ x = 0 := smoothGrad_eq_zero_of_notMem_tsupport hxn
    have hcoord : (fderiv ℝ φ x) (basisVec i) = 0 := by
      have := congrFun hzero i
      simpa only [smoothGrad, Pi.zero_apply] using this
    rw [hcoord, mul_zero]
  · intro x hx
    have hxn : x ∉ tsupport φ := fun hmem => hx.2 (hKR hmem)
    rw [image_eq_zero_of_notMem_tsupport hxn, mul_zero]

/-! ## What the measurability condition of the class buys

The class sees `v` only through

* the *lower* Lebesgue integral `∫⁻ x in V, ENNReal.ofReal |w n x - v x|`, which
  is a supremum over simple functions **below** the integrand and is therefore
  blind to any perturbation supported on a set of inner measure zero; and
* the Bochner integrals of `HasWeakGradientOn`, which value a non-integrable
  integrand at `0`.

The two lemmas below make the reduction formal: any `v` that is invisible to
both lands in the local class with zero weak gradient, whatever its
measurability.  Instantiating with the indicator of a Bernstein set `B ⊆ ℝ^d`
— every measurable subset of `B` and of `Bᶜ` is null, so `B` has inner measure
`0` and full outer measure in every open set — would give a member of the wider
class that is not almost everywhere strongly measurable, hence not integrable on
any ball.  Bernstein sets are a ZFC construction and are not in Mathlib, so that
half is cited rather than formalized, and the possibility that the two classes
coincide is not ruled out here. -/

/-- The coordinate gradient of a constant vanishes. -/
theorem smoothGrad_const (c : ℝ) (x : Vec d) :
    smoothGrad (fun _ : Vec d => c) x = 0 := by
  funext i
  simp [smoothGrad]

/-- The weighted energy of the zero field vanishes. -/
theorem sEnergyOn_eq_zero_of_eq_zero {b : CoeffField d} {V : Set (Vec d)}
    {F : Vec d → Vec d} (hF : ∀ x, F x = 0) : sEnergyOn b V F = 0 := by
  calc sEnergyOn b V F = ∫⁻ _x in V, (0 : ℝ≥0∞) ∂volume := by
        simp only [sEnergyOn]
        exact lintegral_congr fun x => by rw [hF x]; simp [vecDot, matVecMul]
    _ = 0 := by simp

/-- A function whose lower Lebesgue integral vanishes on every ball, and whose
weak gradient is zero there, lies in the local class with zero gradient field,
for every coefficient field.

With the measurability condition present as a hypothesis the conclusion is
degenerate: those hypotheses together force the function to vanish almost
everywhere, so this construction exhibits nothing but the zero function.  It is
kept because it is the shape available before the class carried that condition,
and the difference between the two readings is exactly what the condition
buys. -/
theorem memH1sLoc_of_lintegral_abs_eq_zero {b : CoeffField d} {v : Vec d → ℝ}
    (hmeas : AEStronglyMeasurable v volume)
    (hw : ∀ R : ℝ, 0 < R → HasWeakGradientOn (euclideanBall d R) v (fun _ => 0))
    (hz : ∀ R : ℝ, 0 < R →
      (∫⁻ x in euclideanBall d R, ENNReal.ofReal |v x| ∂volume) = 0) :
    MemH1sLoc b v (fun _ => 0) := by
  refine ⟨⟨hmeas, fun _ => aestronglyMeasurable_const⟩, ?_⟩
  intro R hR
  refine ⟨hw R hR, fun _ => fun _ : Vec d => (0 : ℝ), fun _ => contDiff_const, ?_⟩
  refine tendsto_const_nhds.congr fun n => ?_
  symm
  simp only [h1sNormSqOn]
  have h1 : (∫⁻ x in euclideanBall d R,
      ENNReal.ofReal |(0 : ℝ) - v x| ∂volume) = 0 := by
    rw [lintegral_congr fun x => by rw [zero_sub, abs_neg]]
    exact hz R hR
  have h2 : sEnergyOn b (euclideanBall d R)
      (fun x => smoothGrad (fun _ : Vec d => (0 : ℝ)) x - (0 : Vec d)) = 0 :=
    sEnergyOn_eq_zero_of_eq_zero fun x => by rw [smoothGrad_const, sub_zero]
  rw [h1, h2]
  simp

/-- A function that is not almost everywhere measurable on a set is not
integrable there.  This is the contraposed measurability half of integrability,
and it is recorded only because it is the step at which a pair failing the
class's measurability condition is separated from the integrable ones; it says
nothing on its own about either the class or the reference text's spaces. -/
theorem not_integrableOn_of_blind {v : Vec d → ℝ} {R : ℝ}
    (hnm : ¬ AEStronglyMeasurable v (volume.restrict (euclideanBall d R))) :
    ¬ IntegrableOn v (euclideanBall d R) volume :=
  fun hI => hnm hI.1

/-! ## The class-level statements

The local class carries the measurability of its pair, so the statements above
may be restated with their measurability hypotheses discharged from the class
itself.  What remains assumed is the coefficient field, through local uniform
ellipticity: on every bounded set a pair of constants for that set. -/

theorem aestronglyMeasurable_of_memH1sLoc {b : CoeffField d} {v : Vec d → ℝ}
    {Dv : Vec d → Vec d} (h : MemH1sLoc b v Dv) (S : Set (Vec d)) :
    AEStronglyMeasurable v (volume.restrict S) :=
  h.1.1.restrict

theorem aestronglyMeasurable_grad_of_memH1sLoc {b : CoeffField d} {v : Vec d → ℝ}
    {Dv : Vec d → Vec d} (h : MemH1sLoc b v Dv) (S : Set (Vec d)) (j : Fin d) :
    AEStronglyMeasurable (fun x => Dv x j) (volume.restrict S) :=
  (h.1.2 j).restrict

/-- A member of the local class is integrable on every centred ball. -/
theorem integrableOn_of_memH1sLoc_class {b : CoeffField d} {v : Vec d → ℝ}
    {Dv : Vec d → Vec d} (h : MemH1sLoc b v Dv) {R : ℝ} (hR : 0 < R) :
    IntegrableOn v (euclideanBall d R) volume :=
  integrableOn_of_memH1sLoc h hR (aestronglyMeasurable_of_memH1sLoc h _)

/-- Both pairings of the weak gradient relation converge absolutely for a member
of the local class, on every centred ball. -/
theorem integrableOn_weakGradientPairings_of_memH1sLoc_class {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d} {R : ℝ} (hR : 0 < R)
    (hv : MemH1sLoc b v Dv) {φ : Vec d → ℝ}
    (hφ : IsLocalTest (euclideanBall d R) φ) (i : Fin d) :
    IntegrableOn (fun x => v x * (fderiv ℝ φ x) (basisVec i))
        (euclideanBall d R) volume ∧
      IntegrableOn (fun x => Dv x i * φ x) (euclideanBall d R) volume :=
  integrableOn_weakGradientPairings_of_memH1sLoc hb hR
    (aestronglyMeasurable_of_memH1sLoc hv _)
    (fun j => aestronglyMeasurable_grad_of_memH1sLoc hv _ j) hv hφ i

/-- The same on the whole space, which is where the corrector equation of
`t.random.homogenization` is read. -/
theorem integrableOn_weakGradientPairings_univ_of_memH1sLoc_class {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (hv : MemH1sLoc b v Dv) {φ : Vec d → ℝ}
    (hφ : IsLocalTest (Set.univ : Set (Vec d)) φ) (i : Fin d) :
    IntegrableOn (fun x => v x * (fderiv ℝ φ x) (basisVec i))
        (Set.univ : Set (Vec d)) volume ∧
      IntegrableOn (fun x => Dv x i * φ x) (Set.univ : Set (Vec d)) volume :=
  integrableOn_weakGradientPairings_univ_of_memH1sLoc hb hv.1.1 hv.1.2 hv hφ i

end

end HighContrast
end HCPolySupport
