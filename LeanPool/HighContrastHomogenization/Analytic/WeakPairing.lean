/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.AnalyticCarriers
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.BasicLemmas

/-!
# High-contrast homogenization: Analytic.WeakPairing

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Absolute convergence of the weak flux pairing

The weak interior equation of `t.random.homogenization` is
read against smooth compactly supported tests, and the printed distributional
display presupposes that each test pairing converges absolutely.  That
convergence is derived here rather than assumed: `∇φ` is continuous with compact
support, the entries of an almost everywhere uniformly elliptic coefficient
field are essentially bounded, and a field square integrable on the compact set
`tsupport φ` — which has finite measure whatever `V` is — pairs with them
absolutely.  Off `tsupport φ` the integrand vanishes identically, so nothing
about `V` beyond its measurability is used.

The consequence is that the integrability conjunct carried by
`IsWeakSolutionOn` costs nothing on the coefficient class: for a field of
`L²(V)` the predicate is equivalent to the bare vanishing of every test pairing.
A local variant, asking square integrability only on the compact subsets of `V`,
is what applies at `V = ℝ^d`, where no global `L²` bound is available.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The coordinate gradient of a smooth function is continuous. -/
theorem continuous_smoothGrad {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Continuous (smoothGrad φ) := by
  refine continuous_pi fun i => ?_
  simpa only [smoothGrad] using
    (hφ.continuous_fderiv (by simp)).clm_apply (continuous_const (y := basisVec i))

/-- The coordinate gradient vanishes off the topological support. -/
theorem smoothGrad_eq_zero_of_notMem_tsupport {φ : Vec d → ℝ} {x : Vec d}
    (hx : x ∉ tsupport φ) : smoothGrad φ x = 0 := by
  funext i
  simp [smoothGrad, fderiv_of_notMem_tsupport ℝ hx]

/-- **The core convergence lemma.**  The weak flux pairing of a local test
against a field that is square integrable on the test's support is absolutely
convergent.

Hypotheses used, in full: `V` measurable; the entries of `b` are a.e. strongly
measurable and a.e. bounded; `φ` is a local test on `V`; the components of `F`
are a.e. strongly measurable; and `F ∈ L²` on `tsupport φ` only. -/
theorem integrableOn_weakPairing_of_integrableOn_tsupport_of_locallyBounded
    {b : CoeffField d}
    {V : Set (Vec d)} {F : Vec d → Vec d} {φ : Vec d → ℝ}
    (hV : MeasurableSet V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    (hbdd : ∀ K : Set (Vec d), IsCompact K →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume.restrict K, ∀ i j, |b x i j| ≤ M)
    (hφ : IsLocalTest V φ)
    (hFmeas : ∀ j, AEStronglyMeasurable (fun x => F x j) (volume.restrict V))
    (hF : IntegrableOn (fun x => vecNormSq (F x)) (tsupport φ) volume) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (F x))) V
      volume := by
  classical
  obtain ⟨M, hM0, hM⟩ := hbdd (tsupport φ) hφ.hasCompactSupport
  have hKV : tsupport φ ⊆ V := hφ.tsupport_subset
  have hKc : IsCompact (tsupport φ) := hφ.hasCompactSupport
  have hKm : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hrestr : volume.restrict (tsupport φ) ≤ volume.restrict V :=
    Measure.restrict_mono hKV le_rfl
  have hbK : ∀ i j,
      AEStronglyMeasurable (fun x => b x i j) (volume.restrict (tsupport φ)) :=
    fun i j => (hbmeas i j).mono_measure hrestr
  have hFK : ∀ j,
      AEStronglyMeasurable (fun x => F x j) (volume.restrict (tsupport φ)) :=
    fun j => (hFmeas j).mono_measure hrestr
  have hcont : Continuous (smoothGrad φ) := continuous_smoothGrad hφ.contDiff
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  have : IsFiniteMeasure (volume.restrict (tsupport φ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
  -- Each component of `F` is integrable on the compact support of the test.
  have hFj : ∀ j, IntegrableOn (fun x => F x j) (tsupport φ) volume := by
    intro j
    refine Integrable.mono' (g := fun x => (1 + vecNormSq (F x)) / 2)
      (((integrable_const (1 : ℝ)).add hF).div_const 2) (hFK j) ?_
    filter_upwards with x
    have h1 : (F x j) ^ 2 ≤ vecNormSq (F x) := sq_apply_le_vecNormSq (F x) j
    have h2 : |F x j| ≤ (1 + (F x j) ^ 2) / 2 := by
      nlinarith only [sq_nonneg (|F x j| - 1), sq_abs (F x j)]
    rw [Real.norm_eq_abs]
    linarith only [h1, h2]
  -- The integrand is a finite sum of (bounded measurable) × (integrable).
  have hexp : (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (F x))) =
      fun x => ∑ i, ∑ j, smoothGrad φ x i * b x i j * F x j := by
    funext x
    simp only [vecDot, matVecMul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have hKint : IntegrableOn
      (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (F x))) (tsupport φ)
      volume := by
    rw [hexp]
    refine integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => ?_
    refine Integrable.bdd_mul (c := B * M) (hFj j) ?_ ?_
    · exact (((continuous_apply i).comp hcont).aestronglyMeasurable).mul (hbK i j)
    · filter_upwards [hM, ae_restrict_mem hKm] with x hx hxK
      have hgi : |smoothGrad φ x i| ≤ B := by
        simpa only [Real.norm_eq_abs] using
          (norm_le_pi_norm (smoothGrad φ x) i).trans (hB x hxK)
      have hB0 : (0 : ℝ) ≤ B := (norm_nonneg _).trans (hB x hxK)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hgi (hx i j) (abs_nonneg _) hB0
  -- Off the support of the test the integrand vanishes.
  refine hKint.of_forall_sdiff_eq_zero hV ?_
  intro x hx
  rw [smoothGrad_eq_zero_of_notMem_tsupport hx.2]
  simp [vecDot]

/-- The entry bound on all of `ℝ^d` restricts to every compact set. -/
theorem ae_abs_entry_le_isCompact_of_ae_abs_entry_le {b : CoeffField d}
    (hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume, ∀ i j, |b x i j| ≤ M)
    (K : Set (Vec d)) (_hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume.restrict K, ∀ i j, |b x i j| ≤ M := by
  obtain ⟨M, hM0, hM⟩ := hbdd
  exact ⟨M, hM0, ae_restrict_of_ae hM⟩

/-- **The core convergence lemma**, with the entry bound on all of `ℝ^d`. -/
theorem integrableOn_weakPairing_of_integrableOn_tsupport {b : CoeffField d}
    {V : Set (Vec d)} {F : Vec d → Vec d} {φ : Vec d → ℝ}
    (hV : MeasurableSet V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    (hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume, ∀ i j, |b x i j| ≤ M)
    (hφ : IsLocalTest V φ)
    (hFmeas : ∀ j, AEStronglyMeasurable (fun x => F x j) (volume.restrict V))
    (hF : IntegrableOn (fun x => vecNormSq (F x)) (tsupport φ) volume) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (F x))) V
      volume :=
  integrableOn_weakPairing_of_integrableOn_tsupport_of_locallyBounded hV hbmeas
    (ae_abs_entry_le_isCompact_of_ae_abs_entry_le hbdd) hφ hFmeas hF

/-- The weak flux pairing of a local test on `V` against a field of `L²(V)` is
absolutely convergent. -/
theorem integrableOn_weakPairing {b : CoeffField d} {V : Set (Vec d)}
    {F : Vec d → Vec d} {φ : Vec d → ℝ}
    (hV : MeasurableSet V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    (hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume, ∀ i j, |b x i j| ≤ M)
    (hφ : IsLocalTest V φ)
    (hFmeas : ∀ j, AEStronglyMeasurable (fun x => F x j) (volume.restrict V))
    (hF : IntegrableOn (fun x => vecNormSq (F x)) V volume) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (F x))) V
      volume :=
  integrableOn_weakPairing_of_integrableOn_tsupport hV hbmeas hbdd hφ hFmeas
    (hF.mono_set hφ.tsupport_subset)

/-- **The local form.**  Only square integrability on the compact subsets of `V`
is needed; this is the form that applies at `V = Set.univ`, where no global `L²`
bound is available. -/
theorem integrableOn_weakPairing_of_integrableOn_compacts {b : CoeffField d}
    {V : Set (Vec d)} {F : Vec d → Vec d} {φ : Vec d → ℝ}
    (hV : MeasurableSet V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    (hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume, ∀ i j, |b x i j| ≤ M)
    (hφ : IsLocalTest V φ)
    (hFmeas : ∀ j, AEStronglyMeasurable (fun x => F x j) (volume.restrict V))
    (hFloc : ∀ K : Set (Vec d), IsCompact K → K ⊆ V →
      IntegrableOn (fun x => vecNormSq (F x)) K volume) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (F x))) V
      volume :=
  integrableOn_weakPairing_of_integrableOn_tsupport hV hbmeas hbdd hφ hFmeas
    (hFloc _ hφ.hasCompactSupport hφ.tsupport_subset)

/-- **The local form, with the entry bound read on each compact set.**  This is
the form the whole-space reading takes on the coefficient class, where no entry
bound on all of `ℝ^d` is available. -/
theorem integrableOn_weakPairing_of_integrableOn_compacts_of_locallyBounded
    {b : CoeffField d}
    {V : Set (Vec d)} {F : Vec d → Vec d} {φ : Vec d → ℝ}
    (hV : MeasurableSet V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    (hbdd : ∀ K : Set (Vec d), IsCompact K →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume.restrict K, ∀ i j, |b x i j| ≤ M)
    (hφ : IsLocalTest V φ)
    (hFmeas : ∀ j, AEStronglyMeasurable (fun x => F x j) (volume.restrict V))
    (hFloc : ∀ K : Set (Vec d), IsCompact K → K ⊆ V →
      IntegrableOn (fun x => vecNormSq (F x)) K volume) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (F x))) V
      volume :=
  integrableOn_weakPairing_of_integrableOn_tsupport_of_locallyBounded hV hbmeas
    hbdd hφ hFmeas (hFloc _ hφ.hasCompactSupport hφ.tsupport_subset)

/-- **The design justification for `IsWeakSolutionOn`.**  On the coefficient
class, and for a field of `L²(V)`, the integrability conjunct of
`IsWeakSolutionOn` costs nothing: the predicate is equivalent to the bare
vanishing of every test pairing. -/
theorem isWeakSolutionOn_iff {b : CoeffField d} {V : Set (Vec d)}
    {F : Vec d → Vec d}
    (hV : MeasurableSet V)
    (hbmeas : ∀ i j, AEStronglyMeasurable (fun x => b x i j) (volume.restrict V))
    (hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume, ∀ i j, |b x i j| ≤ M)
    (hFmeas : ∀ j, AEStronglyMeasurable (fun x => F x j) (volume.restrict V))
    (hF : IntegrableOn (fun x => vecNormSq (F x)) V volume) :
    IsWeakSolutionOn b V F ↔
      ∀ φ : Vec d → ℝ, IsLocalTest V φ →
        ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (b x) (F x)) ∂volume = 0 :=
  ⟨fun h φ hφ => (h φ hφ).2,
   fun h φ hφ =>
     ⟨integrableOn_weakPairing hV hbmeas hbdd hφ hFmeas hF, h φ hφ⟩⟩

/-- The essential entry bound of the coefficient class on a compact set, in the
form the pairing lemmas take it: the upper constant of the set bounds every entry
there. -/
theorem ae_abs_entry_le_isCompact_of_ae_isEllipticMatrix_restrict
    {b : CoeffField d} {lam Lam : ℝ} {K : Set (Vec d)} (hlam : 0 < lam)
    (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume.restrict K, IsEllipticMatrix lam Lam (b x)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume.restrict K, ∀ i j, |b x i j| ≤ M := by
  refine ⟨Lam, hlam.le.trans hle, ?_⟩
  filter_upwards [hell] with x hx i j
  exact abs_apply_le_of_isEllipticMatrix hx i j

/-- The essential entry bound of the coefficient class, in the form the pairing
lemmas take it. -/
theorem ae_abs_entry_le_of_ae_isEllipticMatrix {b : CoeffField d} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume, ∀ i j, |b x i j| ≤ M := by
  refine ⟨Lam, hlam.le.trans hle, ?_⟩
  filter_upwards [hell] with x hx i j
  exact abs_apply_le_of_isEllipticMatrix hx i j

end

end HighContrast
end HCPolySupport
