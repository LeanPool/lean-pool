/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.ClassPairing
public import LeanPool.HighContrastHomogenization.Analytic.LocalIntegrability
public import LeanPool.HighContrastHomogenization.Analytic.WeakGradientClosure

/-!
# High-contrast homogenization: Analytic.ClosureH1a

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The closure family of `H¹_a(V)` and `H¹_{a,0}(V)`

The relation tying a function to its weak gradient is an identity between two
pairings against a test function.  Read without a convergence guard it is
satisfied vacuously — as `0 = -0` — by a pair both of whose pairings diverge.
The statements collected here are what makes that branch unreachable on the
coefficient-Sobolev classes of `s.introduction`: the function
slot of a member is of finite `L¹` mass and integrable, and the gradient slot is
square integrable with integrable components.

The two classes differ in exactly one place.  The approximants of `H¹_a(V)` are
globally smooth and nothing bounds them on an unbounded `V`, so that half
carries `Bornology.IsBounded V`; the approximants of `H¹_{a,0}(V)` are compactly
supported inside `V`, so that half carries no hypothesis on `V` at all.  The
step from square integrability of the gradient to integrability of one of its
components needs only that `V` have finite measure, which is strictly weaker
than boundedness.

The module closes with the gradient side of the local class `H¹_{s,loc}(ℝ^d)`,
which is square integrable on every centred ball and has integrable components
there and on every compact set.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Shared scaffolding

Two facts the closure statements below need and the two-sided energy comparison
does not supply: the scalar counterpart of
`lintegral_ofReal_vecNormSq_ne_top_of_hasCompactSupport`, and the extension of
an integrability statement from a measurable subset to a superset across which
the integrand vanishes.  The latter is stated without measurability of the
superset — it is the restriction identity `(μ|_V)|_K = μ|_{K ∩ V} = μ|_K`, not a
difference-set argument. -/

/-- A continuous function with compact support has finite `L¹` mass on every
set, with no hypothesis on the set. -/
theorem lintegral_ofReal_abs_ne_top_of_hasCompactSupport {V : Set (Vec d)}
    {g : Vec d → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) :
    (∫⁻ x in V, ENNReal.ofReal |g x| ∂volume) ≠ ⊤ := by
  classical
  have hK : IsCompact (tsupport g) := hgs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  have hpt : ∀ x, ENNReal.ofReal |g x| ≤
      (tsupport g).indicator (fun _ => ENNReal.ofReal C) x := by
    intro x
    by_cases hx : x ∈ tsupport g
    · rw [Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal
        (by simpa only [Real.norm_eq_abs] using hC x hx)
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
      simp
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal C * volume (tsupport g)) ?_ ?_
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK.measure_lt_top.ne
  · calc (∫⁻ x in V, ENNReal.ofReal |g x| ∂volume)
        ≤ ∫⁻ x, ENNReal.ofReal |g x| ∂volume := setLIntegral_le_lintegral V _
      _ ≤ ∫⁻ x, (tsupport g).indicator (fun _ => ENNReal.ofReal C) x ∂volume :=
          lintegral_mono hpt
      _ = ENNReal.ofReal C * volume (tsupport g) := by
          rw [lintegral_indicator (isClosed_tsupport g).measurableSet,
            setLIntegral_const]

/-- Integrability transfers from a measurable subset to any superset across which
the integrand vanishes.  No measurability of the superset is used. -/
theorem integrableOn_of_integrableOn_subset_of_eq_zero {V K : Set (Vec d)}
    {f : Vec d → ℝ} (hK : MeasurableSet K) (hKV : K ⊆ V)
    (hf : IntegrableOn f K volume) (hzero : ∀ x, x ∉ K → f x = 0) :
    IntegrableOn f V volume := by
  classical
  have hind : K.indicator f = f := by
    funext x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hzero x hx]
  have h1 : Integrable f ((volume.restrict V).restrict K) := by
    rw [Measure.restrict_restrict hK, Set.inter_eq_self_of_subset_left hKV]
    exact hf
  have h2 : Integrable (K.indicator f) (volume.restrict V) :=
    (integrable_indicator_iff hK).2 h1
  rwa [hind] at h2

/-- The function slot against a test gradient: an `L¹` function times the bounded
gradient of a local test. -/
theorem integrableOn_mul_testGrad_of_integrableOn {V : Set (Vec d)}
    {u : Vec d → ℝ} {φ : Vec d → ℝ} (hφ : IsLocalTest V φ)
    (hu : IntegrableOn u V volume) (i : Fin d) :
    IntegrableOn (fun x => u x * (fderiv ℝ φ x) (basisVec i)) V volume := by
  obtain ⟨B, hB⟩ := exists_bound_smoothGrad_of_isLocalTest hφ i
  refine hu.mul_bdd (c := B) ?_ ?_
  · exact ((continuous_apply i).comp
      (continuous_smoothGrad hφ.contDiff)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hB x

/-- The gradient slot against a test: a field that is `L²` on `V` pairs
absolutely with a local test.  The pairing is read on the compact support of the
test, which has finite measure whatever `V` is, so neither boundedness nor
measurability of `V` enters. -/
theorem integrableOn_grad_mul_test_of_integrableOn_vecNormSq {V : Set (Vec d)}
    {Du : Vec d → Vec d} {φ : Vec d → ℝ} (hφ : IsLocalTest V φ)
    (hDmeas : ∀ j, AEStronglyMeasurable (fun x => Du x j) (volume.restrict V))
    (hD : IntegrableOn (fun x => vecNormSq (Du x)) V volume) (i : Fin d) :
    IntegrableOn (fun x => Du x i * φ x) V volume := by
  classical
  have hKc : IsCompact (tsupport φ) := hφ.hasCompactSupport
  have hKm : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hKV : tsupport φ ⊆ V := hφ.tsupport_subset
  have hrestr : volume.restrict (tsupport φ) ≤ volume.restrict V :=
    Measure.restrict_mono hKV le_rfl
  have hDK : ∀ j, AEStronglyMeasurable (fun x => Du x j)
      (volume.restrict (tsupport φ)) := fun j => (hDmeas j).mono_measure hrestr
  have hDL1 : IntegrableOn (fun x => Du x i) (tsupport φ) volume :=
    integrableOn_apply_of_integrableOn_vecNormSq hKc.measure_lt_top.ne hDK
      (hD.mono_set hKV) i
  obtain ⟨C, hC⟩ := exists_bound_of_isLocalTest hφ
  have hmul : IntegrableOn (fun x => Du x i * φ x) (tsupport φ) volume := by
    refine hDL1.mul_bdd (c := C) ?_ ?_
    · exact hφ.contDiff.continuous.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact hC x
  refine integrableOn_of_integrableOn_subset_of_eq_zero hKm hKV hmul ?_
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-! ## The `H¹_a(V)` and `H¹_{a,0}(V)` closure family

The mirror, for the two global classes, of what the local class `H¹_{s,loc}`
already has.  The two classes differ in exactly one place: the approximants of
`MemH1a` are globally smooth and nothing bounds them on an unbounded `V`, so the
`H¹_a` half carries `Bornology.IsBounded V`, while the `H¹_{a,0}` half — whose
approximants are compactly supported inside `V` — carries no hypothesis on `V`
at all. -/

/-- The measurability of the function slot, read off the class. -/
theorem aestronglyMeasurable_of_memH1a {b : CoeffField d} {V : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a b V u Du) :
    AEStronglyMeasurable u (volume.restrict V) := hu.1.1

/-- The measurability of the gradient slot, read off the class. -/
theorem aestronglyMeasurable_grad_of_memH1a {b : CoeffField d} {V : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a b V u Du) (j : Fin d) :
    AEStronglyMeasurable (fun x => Du x j) (volume.restrict V) := hu.1.2 j

/-- The measurability of the function slot of `H¹_{a,0}`, read off the class. -/
theorem aestronglyMeasurable_of_memH1a0 {b : CoeffField d} {V : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a0 b V u Du) :
    AEStronglyMeasurable u (volume.restrict V) := hu.1.1

/-- The measurability of the gradient slot of `H¹_{a,0}`, read off the class. -/
theorem aestronglyMeasurable_grad_of_memH1a0 {b : CoeffField d} {V : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a0 b V u Du) (j : Fin d) :
    AEStronglyMeasurable (fun x => Du x j) (volume.restrict V) := hu.1.2 j

/-- **The `L¹` half of the `H¹_a(V)` class is honest on a bounded `V`**, with no
measurability input at all: the *lower* Lebesgue integral of `|u|` over `V` is
finite.

Boundedness of `V` is not removable: `MemH1a` is an approximability condition
and a globally smooth `u` approximates itself at distance `0` whatever its
growth (`exists_memH1a_sEnergyOn_eq_top` runs the same argument for the energy
slot). -/
theorem lintegral_abs_ne_top_of_memH1a {b : CoeffField d} {V : Set (Vec d)}
    (hVb : Bornology.IsBounded V) {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemH1a b V u Du) :
    (∫⁻ x in V, ENNReal.ofReal |u x| ∂volume) ≠ ⊤ := by
  obtain ⟨-, -, v, hv, htend, -⟩ := hu
  obtain ⟨n, hn⟩ := exists_lintegral_ofReal_abs_sub_ne_top htend
  have hvc : Continuous (v n) := (hv n).continuous
  refine lintegral_ofReal_abs_ne_top_of_sub (g := v n) (h := u) ?_
    (lintegral_ofReal_abs_ne_top_of_isBounded hVb hvc) hn
  exact (ENNReal.measurable_ofReal.comp hvc.abs.measurable).aemeasurable

/-- **The `L¹` half of the `H¹_{a,0}(V)` class is honest on an arbitrary `V`**:
the approximants are compactly supported inside `V`, so no hypothesis on `V` is
needed. -/
theorem lintegral_abs_ne_top_of_memH1a0 {b : CoeffField d} {V : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a0 b V u Du) :
    (∫⁻ x in V, ENNReal.ofReal |u x| ∂volume) ≠ ⊤ := by
  obtain ⟨-, -, v, hv, htend, -⟩ := hu
  obtain ⟨n, hn⟩ := exists_lintegral_ofReal_abs_sub_ne_top htend
  have hvc : Continuous (v n) := (hv n).contDiff.continuous
  refine lintegral_ofReal_abs_ne_top_of_sub (g := v n) (h := u) ?_
    (lintegral_ofReal_abs_ne_top_of_hasCompactSupport hvc
      (hv n).hasCompactSupport) hn
  exact (ENNReal.measurable_ofReal.comp hvc.abs.measurable).aemeasurable

/-- **A member of `H¹_a(V)` is integrable on a bounded `V`.**  The measurability
conjunct is read off the class; the finiteness is the previous lemma. -/
theorem integrableOn_of_memH1a_class {b : CoeffField d} {V : Set (Vec d)}
    (hVb : Bornology.IsBounded V) {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemH1a b V u Du) : IntegrableOn u V volume := by
  refine ⟨aestronglyMeasurable_of_memH1a hu, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs]
  exact lt_of_le_of_ne le_top (lintegral_abs_ne_top_of_memH1a hVb hu)

/-- **A member of `H¹_{a,0}(V)` is integrable on an arbitrary `V`.** -/
theorem integrableOn_of_memH1a0_class {b : CoeffField d} {V : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a0 b V u Du) :
    IntegrableOn u V volume := by
  refine ⟨aestronglyMeasurable_of_memH1a0 hu, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs]
  exact lt_of_le_of_ne le_top (lintegral_abs_ne_top_of_memH1a0 hu)

/-- **The gradient slot of `H¹_a(V)` is square integrable on a bounded `V`.** -/
theorem integrableOn_vecNormSq_grad_of_memH1a_class {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hVb : Bornology.IsBounded V) {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemH1a b V u Du) :
    IntegrableOn (fun x => vecNormSq (Du x)) V volume :=
  integrableOn_vecNormSq_of_sEnergyOn_ne_top hlam hell
    (aestronglyMeasurable_grad_of_memH1a hu)
    (sEnergyOn_ne_top_of_memH1a hlam hell hVb hu)

/-- **The gradient slot of `H¹_{a,0}(V)` is square integrable on an arbitrary
`V`.** -/
theorem integrableOn_vecNormSq_grad_of_memH1a0_class {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a0 b V u Du) :
    IntegrableOn (fun x => vecNormSq (Du x)) V volume :=
  integrableOn_vecNormSq_of_sEnergyOn_ne_top hlam hell
    (aestronglyMeasurable_grad_of_memH1a0 hu)
    (sEnergyOn_ne_top_of_memH1a0 hlam hell hu)

/-- **The components of the gradient slot of `H¹_a(V)` are integrable on a
bounded `V`.**  The step from `L²` to `L¹` is the finiteness of the measure of
`V`, which boundedness already supplies. -/
theorem integrableOn_grad_of_memH1a_class {b : CoeffField d} {V : Set (Vec d)}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hVb : Bornology.IsBounded V) {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemH1a b V u Du) (i : Fin d) :
    IntegrableOn (fun x => Du x i) V volume :=
  integrableOn_apply_of_integrableOn_vecNormSq hVb.measure_lt_top.ne
    (aestronglyMeasurable_grad_of_memH1a hu)
    (integrableOn_vecNormSq_grad_of_memH1a_class hlam hell hVb hu) i

/-- **The components of the gradient slot of `H¹_{a,0}(V)` are integrable on a
`V` of finite measure.**  Finiteness of the measure is the only thing the step
from `L²` to `L¹` needs, and it is strictly weaker than boundedness. -/
theorem integrableOn_grad_of_memH1a0_class {b : CoeffField d} {V : Set (Vec d)}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hVfin : volume V ≠ ⊤) {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemH1a0 b V u Du) (i : Fin d) :
    IntegrableOn (fun x => Du x i) V volume :=
  integrableOn_apply_of_integrableOn_vecNormSq hVfin
    (aestronglyMeasurable_grad_of_memH1a0 hu)
    (integrableOn_vecNormSq_grad_of_memH1a0_class hlam hell hu) i

/-! ## The gradient slot of the local class

The function slot `v` of `MemH1sLoc` is closed on every centred ball by the
local family; the gradient slot `Dv` is not.  The step from the class's finite
weighted energy to `L¹` of a component is the finiteness of the measure of the
ball, and the ellipticity pair converting the weighted energy into the
unweighted one is read on that ball as well. -/

/-- **The gradient slot of `H¹_{s,loc}` is square integrable on every centred
ball.** -/
theorem integrableOn_vecNormSq_grad_of_memH1sLoc_class {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d} (hv : MemH1sLoc b v Dv) {R : ℝ}
    (hR : 0 < R) :
    IntegrableOn (fun x => vecNormSq (Dv x)) (euclideanBall d R) volume := by
  obtain ⟨lam, Lam, hlam, -, hell⟩ :=
    hb.exists_ae_isEllipticMatrix_euclideanBall hR
  exact integrableOn_vecNormSq_of_sEnergyOn_ne_top_restrict (Lam := Lam) hlam hell
    (fun j => aestronglyMeasurable_grad_of_memH1sLoc hv _ j)
    (sEnergyOn_ne_top_of_memH1sLoc hb hv hR)

/-- The components of the gradient slot of a member of the local class are
integrable on every centred ball. -/
theorem integrableOn_grad_of_memH1sLoc_class {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d} (hv : MemH1sLoc b v Dv) {R : ℝ}
    (hR : 0 < R) (i : Fin d) :
    IntegrableOn (fun x => Dv x i) (euclideanBall d R) volume :=
  integrableOn_apply_of_integrableOn_vecNormSq
    (isBounded_euclideanBall d hR).measure_lt_top.ne
    (fun j => aestronglyMeasurable_grad_of_memH1sLoc hv _ j)
    (integrableOn_vecNormSq_grad_of_memH1sLoc_class hb hv hR) i

/-- The same on every compact set, which is the form the whole-space reading
needs. -/
theorem integrableOn_grad_isCompact_of_memH1sLoc_class {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d} (hv : MemH1sLoc b v Dv)
    {K : Set (Vec d)} (hK : IsCompact K) (i : Fin d) :
    IntegrableOn (fun x => Dv x i) K volume :=
  integrableOn_apply_of_integrableOn_vecNormSq hK.measure_lt_top.ne
    (fun j => aestronglyMeasurable_grad_of_memH1sLoc hv _ j)
    (integrableOn_vecNormSq_isCompact_of_memH1sLoc hb hv.1.2 hv hK) i

end

end HighContrast
end HCPolySupport
