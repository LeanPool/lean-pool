/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.Source.AKL
public import LeanPool.HighContrastHomogenization.Support.Probability.RandomField
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Internal.CoarseObservableMeasurability.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# High-contrast homogenization: Setup.CoefficientSpace

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The high-contrast coefficient space

This file fixes the coefficient class of `s.introduction`: measurable
coefficient fields modulo equality almost everywhere that are uniformly elliptic
almost everywhere on every bounded set, together with the integer translation
action on them.

**Scope of the coefficient class.**  The coefficient space used here is the set
of measurable fields that are *locally* uniformly elliptic: on every bounded
subset of `ℝ^d` one pair of ellipticity constants serves almost every value of
the field there, the pair being attached to the field and to the set rather than
fixed in advance.  No constant appearing in any statement below depends on such
a pair, and no bound of the development is uniform over the coefficient space.
The class contains the fields uniformly elliptic almost everywhere on all of
`ℝ^d`. The paper's condition `e.qualitative.ellipticity` states local essential
bounds on `s`, `s⁻¹` and `kᵗ s⁻¹ k`, expressing local uniform ellipticity in
matrix terms. The coefficient class here also satisfies the weaker local
integrability conditions used by the analytic library. All quantitative
content — the reference aspect ratio `Π`, the
concentration gauge and its growth witness, the annealed contrast `Θ_m`, and
every dimensional constant — is unchanged.

**The canonical measurable structure on `Mat d`.**  Several modules of the
reference library introduce a measurable structure on `Mat d`, all of them the
entrywise product structure transported from `Fin d → Fin d → ℝ`; one of them,
`HCPolySupport.Book.Ch04.SourceObservable`, declares its copy `private`, which
hides the name but still registers the instance globally.  Whichever copy
instance resolution happens to select, `BorelSpace (Mat d)` is then searched for
*that* copy, and the two Borel instances of the reference library are stated for
two of the others, so a goal `BorelSpace (Mat d)` becomes unsolvable in any
public import closure where the private copy wins.  The pair
`HCPolySupport.instMeasurableSpaceMat` and `HCPolySupport.instBorelSpaceMat`
is the canonical path, and it is raised here to a priority no other copy
reaches, so that every module of this library — both the polynomial-entry route
and the proofs of the other three theorems — resolves `MeasurableSpace (Mat d)`
and `BorelSpace (Mat d)` along one and the same path.  All the copies are the
same structure up to unfolding, so nothing stated for another of them stops
applying.
-/

attribute [instance 10000] HCPolySupport.instMeasurableSpaceMat
attribute [instance 10000] HCPolySupport.instBorelSpaceMat

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

/-! ## The coefficient space `Ω` -/

/-- Qualitative local uniform ellipticity of a coefficient field: on every ball
around the origin there is a pair of ellipticity constants for which almost every
value of the field on that ball is uniformly elliptic in the sense of
`IsEllipticMatrix`, that is, coercive with a bounded inverse.

The constants are quantified inside the predicate: they belong to the field and
to the ball, and never enter an estimate.  Since every bounded set lies in a
ball, the same statement holds with an arbitrary bounded set in place of the
ball. -/
@[expose]
def IsAELocallyUniformlyElliptic {d : ℕ} (b : CoeffField d) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
    ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : Vec d) R → IsEllipticMatrix lam Lam (b x)

/-- Qualitative local uniform ellipticity of a point of the a.e.-quotient carrier
`Source.AKL.Field`: local uniform ellipticity of any of its representatives.

The paper's local essential boundedness of `s`, `s⁻¹` and `kᵗ s⁻¹ k` at
`e.qualitative.ellipticity`, and the almost everywhere positive definiteness
of the symmetric part, both follow. -/
@[expose]
def AEUniformlyEllipticField {d : ℕ} (a : Source.AKL.Field d) : Prop :=
  IsAELocallyUniformlyElliptic (⇑a : CoeffField d)

/-- The coefficient space `Ω`: measurable coefficient fields modulo equality
almost everywhere, locally uniformly elliptic in the qualitative sense. -/
@[expose]
def CoeffSpace (d : ℕ) : Type :=
  {a : Source.AKL.Field d // AEUniformlyEllipticField a}

variable {d : ℕ}

/-! ## Bounded sets -/

/-- Every bounded subset of `ℝ^d` lies in a ball of positive radius around the
origin. -/
theorem exists_ball_of_isBounded {S : Set (Vec d)} (hS : Bornology.IsBounded S) :
    ∃ R : ℝ, 0 < R ∧ S ⊆ Metric.ball (0 : Vec d) R := by
  obtain ⟨r, hr⟩ := hS.subset_ball (0 : Vec d)
  exact ⟨max r 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    hr.trans (Metric.ball_subset_ball (le_max_left _ _))⟩

/-- The restricted Lebesgue measure of a subset is carried by any measurable set
containing it. -/
theorem ae_restrict_mem_of_subset {S T : Set (Vec d)} (hST : S ⊆ T)
    (hT : MeasurableSet T) : ∀ᵐ x ∂(volume.restrict S), x ∈ T :=
  ae_mono (Measure.restrict_mono hST le_rfl) (ae_restrict_mem hT)

private theorem matVecMul_one_mat (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- The identity matrix is uniformly elliptic with lower constant `1` and any
upper constant at least `1`. -/
theorem isEllipticMatrix_one_le {Theta : ℝ} (hTheta : (1 : ℝ) ≤ Theta) :
    IsEllipticMatrix (1 : ℝ) Theta (1 : Mat d) := by
  have hpos : 0 < Theta := lt_of_lt_of_le one_pos hTheta
  refine ⟨one_pos, hTheta, fun ξ => ?_, fun ξ => ?_⟩
  · simp [matVecMul_one_mat, vecNormSq]
  · rw [inv_one, matVecMul_one_mat]
    have hle : Theta⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hpos]
      exact hTheta
    have hmul : Theta⁻¹ * vecNormSq ξ ≤ 1 * vecNormSq ξ :=
      mul_le_mul_of_nonneg_right hle (vecNormSq_nonneg ξ)
    simpa [vecNormSq] using hmul

/-! ## Local uniform ellipticity of a coefficient field -/

/-- **Local uniform ellipticity on bounded sets.**  A locally uniformly elliptic
field has a pair of ellipticity constants for almost every value on any bounded
set, not only on a ball. -/
theorem IsAELocallyUniformlyElliptic.exists_ae_isEllipticMatrix_of_isBounded
    {b : CoeffField d} (hb : IsAELocallyUniformlyElliptic b)
    {S : Set (Vec d)} (hS : Bornology.IsBounded S) :
    ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      ∀ᵐ x ∂volume, x ∈ S → IsEllipticMatrix lam Lam (b x) := by
  obtain ⟨R, hR, hSR⟩ := exists_ball_of_isBounded hS
  obtain ⟨lam, Lam, hlam, hle, hell⟩ := hb R hR
  exact ⟨lam, Lam, hlam, hle, hell.mono fun x hx hxS => hx (hSR hxS)⟩

/-- Local uniform ellipticity depends only on the almost everywhere class of the
field. -/
theorem IsAELocallyUniformlyElliptic.congr {b b' : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b) (h : b =ᵐ[volume] b') :
    IsAELocallyUniformlyElliptic b' := by
  intro R hR
  obtain ⟨lam, Lam, hlam, hle, hell⟩ := hb R hR
  refine ⟨lam, Lam, hlam, hle, ?_⟩
  filter_upwards [hell, h] with x hx hxe hxb
  rw [← hxe]
  exact hx hxb

/-- Local uniform ellipticity is preserved by translating the argument: the ball
of radius `R` is served by the constants of the ball of radius `R + ‖z‖`. -/
theorem IsAELocallyUniformlyElliptic.comp_add_right {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b) (z : Vec d) :
    IsAELocallyUniformlyElliptic (fun x => b (x + z)) := by
  intro R hR
  obtain ⟨lam, Lam, hlam, hle, hell⟩ :=
    hb (R + ‖z‖) (lt_of_lt_of_le hR (le_add_of_nonneg_right (norm_nonneg _)))
  refine ⟨lam, Lam, hlam, hle, ?_⟩
  filter_upwards [(measurePreserving_add_right (volume : Measure (Vec d))
      z).quasiMeasurePreserving.tendsto_ae hell] with x hx hxb
  refine hx (mem_ball_zero_iff.2 ?_)
  have hxn : ‖x‖ < R := mem_ball_zero_iff.1 hxb
  exact lt_of_le_of_lt (norm_add_le _ _) (by linarith only [hxn])

/-- Almost every value of a locally uniformly elliptic field is uniformly
elliptic for some pair of constants: the balls of integer radius exhaust `ℝ^d`,
so the countably many null sets of the local statements unite into one. -/
theorem IsAELocallyUniformlyElliptic.ae_exists_isEllipticMatrix {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b) :
    ∀ᵐ x ∂volume, ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticMatrix lam Lam (b x) := by
  have h : ∀ n : ℕ, ∀ᵐ x ∂volume,
      x ∈ Metric.ball (0 : Vec d) ((n : ℝ) + 1) →
        ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧ IsEllipticMatrix lam Lam (b x) := by
    intro n
    obtain ⟨lam, Lam, hlam, hle, hell⟩ := hb ((n : ℝ) + 1) (by positivity)
    filter_upwards [hell] with x hx hxb
    exact ⟨lam, Lam, hlam, hle, hx hxb⟩
  rw [← ae_all_iff] at h
  filter_upwards [h] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact hx n (mem_ball_zero_iff.2 (hn.trans (lt_add_one _)))

/-- Every coordinate of `L x` is bounded by the sum of the absolute entries of
`L` times the sup norm of `x`. -/
theorem norm_matVecMul_le (L : Mat d) (x : Vec d) :
    ‖matVecMul L x‖ ≤ (∑ i : Fin d, ∑ j : Fin d, |L i j|) * ‖x‖ := by
  have hrow : ∀ i : Fin d, ∑ j : Fin d, |L i j| ≤
      ∑ i' : Fin d, ∑ j : Fin d, |L i' j| :=
    fun i => Finset.single_le_sum
      (f := fun i' : Fin d => ∑ j : Fin d, |L i' j|)
      (fun i' _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hnonneg : (0 : ℝ) ≤ ∑ i : Fin d, ∑ j : Fin d, |L i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hnonneg (norm_nonneg x))).2 fun i => ?_
  rw [Real.norm_eq_abs]
  calc |matVecMul L x i| = |∑ j : Fin d, L i j * x j| := rfl
    _ ≤ ∑ j : Fin d, |L i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin d, |L i j| * ‖x‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x j) (abs_nonneg _)
    _ = (∑ j : Fin d, |L i j|) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i' : Fin d, ∑ j : Fin d, |L i' j|) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg x)

/-- Local uniform ellipticity is preserved by composing the argument with a
matrix that transports the Lebesgue null sets: a ball is carried into a ball of
proportional radius. -/
theorem IsAELocallyUniformlyElliptic.comp_matVecMul {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b) (L : Mat d)
    (hL : Measure.QuasiMeasurePreserving (matVecMul L) volume volume) :
    IsAELocallyUniformlyElliptic (fun y => b (matVecMul L y)) := by
  intro R hR
  have hnonneg : (0 : ℝ) ≤ ∑ i : Fin d, ∑ j : Fin d, |L i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hC : (0 : ℝ) < (∑ i : Fin d, ∑ j : Fin d, |L i j|) + 1 := by positivity
  obtain ⟨lam, Lam, hlam, hle, hell⟩ :=
    hb (((∑ i : Fin d, ∑ j : Fin d, |L i j|) + 1) * R) (by positivity)
  refine ⟨lam, Lam, hlam, hle, ?_⟩
  filter_upwards [hL.tendsto_ae hell] with y hy hyb
  refine hy (mem_ball_zero_iff.2 ?_)
  have hyn : ‖y‖ < R := mem_ball_zero_iff.1 hyb
  calc ‖matVecMul L y‖ ≤ (∑ i : Fin d, ∑ j : Fin d, |L i j|) * ‖y‖ :=
        norm_matVecMul_le L y
    _ ≤ ((∑ i : Fin d, ∑ j : Fin d, |L i j|) + 1) * ‖y‖ :=
        mul_le_mul_of_nonneg_right (by linarith only []) (norm_nonneg y)
    _ < ((∑ i : Fin d, ∑ j : Fin d, |L i j|) + 1) * R :=
        mul_lt_mul_of_pos_left hyn hC

/-- **The globally elliptic companion on a bounded set.**  A locally uniformly
elliptic field agrees, almost everywhere on a bounded set, with a field that is
uniformly elliptic almost everywhere on all of `ℝ^d`: keep the field on a ball
containing the set and put the identity matrix outside. -/
theorem IsAELocallyUniformlyElliptic.exists_ae_isEllipticMatrix_ae_eq_restrict
    {b : CoeffField d} (hb : IsAELocallyUniformlyElliptic b)
    {S : Set (Vec d)} (hS : Bornology.IsBounded S) :
    ∃ (lam Lam : ℝ) (c : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      (∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (c x)) ∧
      b =ᵐ[volume.restrict S] c := by
  classical
  obtain ⟨R, hR, hSR⟩ := exists_ball_of_isBounded hS
  obtain ⟨lam, Lam, hlam, hle, hell⟩ := hb R hR
  have hminpos : (0 : ℝ) < min lam 1 := lt_min hlam one_pos
  have hminle : min lam 1 ≤ max Lam 1 :=
    le_trans (min_le_right _ _) (le_max_right _ _)
  refine ⟨min lam 1, max Lam 1,
    fun x => if x ∈ Metric.ball (0 : Vec d) R then b x else 1,
    hminpos, hminle, ?_, ?_⟩
  · filter_upwards [hell] with x hx
    by_cases hxb : x ∈ Metric.ball (0 : Vec d) R
    · simp only [ite_eq_left hxb]
      exact (hx hxb).mono hminpos (min_le_left _ _) (le_max_left _ _)
    · simp only [ite_eq_right hxb]
      exact (isEllipticMatrix_one_le (d := d) le_rfl).mono hminpos
        (min_le_right _ _) (le_max_right _ _)
  · filter_upwards [ae_restrict_mem_of_subset hSR measurableSet_ball] with x hxb
    simp only [ite_eq_left hxb]

/-- A field uniformly elliptic almost everywhere on all of `ℝ^d` is locally
uniformly elliptic, with the same pair of constants on every ball. -/
theorem isAELocallyUniformlyElliptic_of_ae_isEllipticMatrix {b : CoeffField d}
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x)) :
    IsAELocallyUniformlyElliptic b :=
  fun _ _ => ⟨lam, Lam, hlam, hle, hell.mono fun _ hx _ => hx⟩

/-! ## Local uniform ellipticity on the a.e.-quotient carrier -/

/-- **Local uniform ellipticity on bounded sets**, on the a.e.-quotient
carrier. -/
theorem AEUniformlyEllipticField.exists_ae_isEllipticMatrix_of_isBounded
    {a : Source.AKL.Field d} (ha : AEUniformlyEllipticField a)
    {S : Set (Vec d)} (hS : Bornology.IsBounded S) :
    ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      ∀ᵐ x ∂volume, x ∈ S → IsEllipticMatrix lam Lam (a x) :=
  IsAELocallyUniformlyElliptic.exists_ae_isEllipticMatrix_of_isBounded ha hS

/-- A point of the a.e.-quotient carrier whose representatives are locally
uniformly elliptic lies in the coefficient class. -/
theorem aeUniformlyEllipticField_of_ae_eq {a : Source.AKL.Field d}
    {b : CoeffField d} (hb : IsAELocallyUniformlyElliptic b)
    (hab : (⇑a : CoeffField d) =ᵐ[volume] b) :
    AEUniformlyEllipticField a :=
  hb.congr hab.symm

/-- The ball form and the bounded-set form of the coefficient class agree. -/
theorem aeUniformlyEllipticField_iff_isBounded {a : Source.AKL.Field d} :
    AEUniformlyEllipticField a ↔
      ∀ S : Set (Vec d), Bornology.IsBounded S →
        ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
          ∀ᵐ x ∂volume, x ∈ S → IsEllipticMatrix lam Lam (a x) :=
  ⟨fun ha _ hS => ha.exists_ae_isEllipticMatrix_of_isBounded hS,
    fun h _ _ => h _ Metric.isBounded_ball⟩

/-- A point of the a.e.-quotient carrier uniformly elliptic almost everywhere on
all of `ℝ^d` lies in the coefficient class, with the same pair of constants on
every ball. -/
theorem aeUniformlyEllipticField_of_ae_isEllipticMatrix {a : Source.AKL.Field d}
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (a x)) :
    AEUniformlyEllipticField a :=
  isAELocallyUniformlyElliptic_of_ae_isEllipticMatrix hlam hle hell

/-! ## Integer translations -/

/-- Qualitative local uniform ellipticity is preserved by integer translation of
the field: the ball of radius `R` for the translated field is served by the
constants of the ball of radius `R + ‖z‖` for the field. -/
theorem aeUniformlyEllipticField_translateField {d : ℕ} (z : Fin d → ℤ)
    {a : Source.AKL.Field d} (ha : AEUniformlyEllipticField a) :
    AEUniformlyEllipticField (Source.AKL.translateField z a) := by
  intro R hR
  obtain ⟨lam, Lam, hlam, hle, hell⟩ :=
    ha (R + ‖Source.AKL.intTranslation z‖)
      (lt_of_lt_of_le hR (le_add_of_nonneg_right (norm_nonneg _)))
  refine ⟨lam, Lam, hlam, hle, ?_⟩
  filter_upwards [Source.AKL.translateField_ae z a,
    (measurePreserving_add_right (volume : Measure (Vec d))
        (Source.AKL.intTranslation z)).quasiMeasurePreserving.tendsto_ae
      hell] with x hfield hx hxb
  rw [hfield]
  refine hx (mem_ball_zero_iff.2 ?_)
  have hxn : ‖x‖ < R := mem_ball_zero_iff.1 hxb
  exact lt_of_le_of_lt (norm_add_le _ _) (by linarith only [hxn])

/-- The integer translation action `T_z` on the coefficient space. -/
@[expose]
def translateCoeff (z : Fin d → ℤ) (a : CoeffSpace d) : CoeffSpace d :=
  ⟨Source.AKL.translateField z a.1, aeUniformlyEllipticField_translateField z a.2⟩

/-! ## Essential boundedness and pointwise representatives -/

/-- Every entry of a locally uniformly elliptic field is essentially bounded on
every bounded set, by the upper ellipticity constant of the field there. -/
theorem ae_abs_entry_le_of_aeUniformlyEllipticField {a : Source.AKL.Field d}
    (ha : AEUniformlyEllipticField a) {S : Set (Vec d)}
    (hS : Bornology.IsBounded S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume, x ∈ S → ∀ i j : Fin d, |a x i j| ≤ M := by
  obtain ⟨lam, Lam, hlam, hle, hell⟩ :=
    ha.exists_ae_isEllipticMatrix_of_isBounded hS
  refine ⟨Lam, le_trans hlam.le hle, ?_⟩
  filter_upwards [hell] with x hx hxS i j
  exact abs_apply_le_of_isEllipticMatrix (hx hxS) i j

/-- A field with an entry essentially unbounded on a bounded set is not in the
coefficient space. -/
theorem not_aeUniformlyEllipticField_of_not_ae_bounded {a : Source.AKL.Field d}
    {S : Set (Vec d)} (hS : Bornology.IsBounded S)
    (hub : ∀ M : ℝ, ¬ ∀ᵐ x ∂volume, x ∈ S → ∀ i j : Fin d, |a x i j| ≤ M) :
    ¬ AEUniformlyEllipticField a := by
  intro ha
  obtain ⟨M, _, hM⟩ := ae_abs_entry_le_of_aeUniformlyEllipticField ha hS
  exact hub M hM

/-- Every entry of a field of the coefficient space is square integrable on every
bounded set. -/
theorem integrableOn_sq_entry_of_aeUniformlyEllipticField {a : Source.AKL.Field d}
    (ha : AEUniformlyEllipticField a) {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) (i j : Fin d) :
    IntegrableOn (fun x => (a x i j) ^ 2) U volume := by
  obtain ⟨R, hR, hUR⟩ := exists_ball_of_isBounded hU
  obtain ⟨M, hM0, hM⟩ :=
    ae_abs_entry_le_of_aeUniformlyEllipticField ha
      (Metric.isBounded_ball (x := (0 : Vec d)) (r := R))
  have hentry : AEStronglyMeasurable (fun x => a x i j) volume :=
    (continuous_id.matrix_elem i j).comp_aestronglyMeasurable a.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun x => (a x i j) ^ 2) (volume.restrict U) :=
    (hentry.pow 2).restrict
  have hfin : volume U ≠ ⊤ := hU.measure_lt_top.ne
  refine Integrable.mono' (integrableOn_const (C := M ^ 2) hfin) hmeas ?_
  filter_upwards [ae_restrict_of_ae hM,
    ae_restrict_mem_of_subset hUR measurableSet_ball] with x hx hxb
  have h1 : |a x i j| ≤ M := hx hxb i j
  have h2 : |a x i j| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  simpa [Real.norm_eq_abs, abs_pow, abs_of_nonneg (sq_nonneg M)] using h2

/-- A field with an entry that fails to be square integrable on a bounded set is
not in the coefficient space. -/
theorem not_aeUniformlyEllipticField_of_not_integrableOn_sq
    {a : Source.AKL.Field d} {U : Set (Vec d)} (hU : Bornology.IsBounded U)
    (i j : Fin d) (h : ¬ IntegrableOn (fun x => (a x i j) ^ 2) U volume) :
    ¬ AEUniformlyEllipticField a :=
  fun ha => h (integrableOn_sq_entry_of_aeUniformlyEllipticField ha hU i j)

/-- No point of the coefficient space carries such a field, so no law on the
coefficient space is supported on one. -/
theorem ne_of_not_integrableOn_sq
    {a : Source.AKL.Field d} {U : Set (Vec d)} (hU : Bornology.IsBounded U)
    (i j : Fin d) (h : ¬ IntegrableOn (fun x => (a x i j) ^ 2) U volume) :
    ∀ b : CoeffSpace d, b.1 ≠ a := by
  intro b hb
  exact not_aeUniformlyEllipticField_of_not_integrableOn_sq hU i j h (hb ▸ b.2)

private theorem vecDot_matVecMul_smul (c : ℝ) (A : Mat d) (x : Vec d) :
    vecDot x (matVecMul (c • A) x) = c * vecDot x (matVecMul A x) := by
  simp only [vecDot, matVecMul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem inv_smul_mat {c : ℝ} (hc : c ≠ 0) {A : Mat d}
    (hA : IsUnit A.det) : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_nonsing_inv A hA, smul_smul,
    mul_inv_cancel₀ hc, one_smul]

/-- Normalizing the lower ellipticity constant to `1`. -/
theorem isEllipticMatrix_inv_smul {lam Lam : ℝ} (hlam : 0 < lam) {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) :
    IsEllipticMatrix 1 (Lam / lam) (lam⁻¹ • A) := by
  obtain ⟨-, hle, hlow, hinv⟩ := hA
  have hA' : IsUnit A.det :=
    isUnit_det_of_isEllipticMatrix ⟨hlam, hle, hlow, hinv⟩
  refine ⟨one_pos, (one_le_div hlam).2 hle, fun ξ => ?_, fun ξ => ?_⟩
  · rw [vecDot_matVecMul_smul]
    have := hlow ξ
    rw [one_mul]
    calc vecNormSq ξ = lam⁻¹ * (lam * vecNormSq ξ) := by
          field_simp
      _ ≤ lam⁻¹ * vecDot ξ (matVecMul A ξ) :=
          mul_le_mul_of_nonneg_left this (by positivity)
  · rw [inv_smul_mat (by positivity) hA', vecDot_matVecMul_smul]
    have hLam : 0 < Lam := lt_of_lt_of_le hlam hle
    have := hinv ξ
    calc (Lam / lam)⁻¹ * vecNormSq ξ = lam⁻¹⁻¹ * (Lam⁻¹ * vecNormSq ξ) := by
          field_simp
      _ ≤ lam⁻¹⁻¹ * vecDot ξ (matVecMul A⁻¹ ξ) :=
          mul_le_mul_of_nonneg_left this (by positivity)

/-- Undoing the normalization. -/
theorem isEllipticMatrix_smul {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    {B : Mat d} (hB : IsEllipticMatrix 1 (Lam / lam) B) :
    IsEllipticMatrix lam Lam (lam • B) := by
  obtain ⟨-, hΘ, hlow, hinv⟩ := hB
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hle
  have hB' : IsUnit B.det :=
    isUnit_det_of_isEllipticMatrix ⟨one_pos, hΘ, hlow, hinv⟩
  refine ⟨hlam, hle, fun ξ => ?_, fun ξ => ?_⟩
  · rw [vecDot_matVecMul_smul]
    have := hlow ξ
    rw [one_mul] at this
    exact mul_le_mul_of_nonneg_left this hlam.le
  · rw [inv_smul_mat hlam.ne' hB', vecDot_matVecMul_smul]
    have := hinv ξ
    calc Lam⁻¹ * vecNormSq ξ = lam⁻¹ * ((Lam / lam)⁻¹ * vecNormSq ξ) := by
          field_simp
      _ ≤ lam⁻¹ * vecDot ξ (matVecMul B⁻¹ ξ) :=
          mul_le_mul_of_nonneg_left this (by positivity)

/-- On a ball, a locally uniformly elliptic field is represented by a measurable
field that is uniformly elliptic at every point of `ℝ^d`: the field's own
constants on the ball serve, and the identity matrix is used outside it. -/
private theorem exists_ball_representative {a : Source.AKL.Field d}
    (ha : AEUniformlyEllipticField a) {R : ℝ} (hR : 0 < R) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧ Measurable f ∧
      (∀ x, IsEllipticMatrix lam Lam (f x)) ∧
      ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : Vec d) R → a x = f x := by
  classical
  obtain ⟨lam, Lam, hlam, hle, hell⟩ := ha R hR
  have hΘ : (1 : ℝ) ≤ Lam / lam := (one_le_div hlam).2 hle
  have hcmeas : StronglyMeasurable (fun x : Vec d =>
      if x ∈ Metric.ball (0 : Vec d) R then ((lam⁻¹ : ℝ) • a) x else (1 : Mat d)) :=
    StronglyMeasurable.ite measurableSet_ball
      ((lam⁻¹ : ℝ) • a).stronglyMeasurable stronglyMeasurable_const
  have hbell : ∀ᵐ x ∂volume,
      IsEllipticMatrix 1 (Lam / lam)
        ((AEEqFun.mk _ hcmeas.aestronglyMeasurable : Source.AKL.Field d) x) := by
    filter_upwards [AEEqFun.coeFn_mk _ hcmeas.aestronglyMeasurable, hell,
      AEEqFun.coeFn_smul (lam⁻¹ : ℝ) a] with x hbx hellx hsmx
    rw [hbx]
    by_cases hx : x ∈ Metric.ball (0 : Vec d) R
    · rw [ite_eq_left hx, hsmx]
      simp only [Pi.smul_apply]
      exact isEllipticMatrix_inv_smul hlam (hellx hx)
    · rw [ite_eq_right hx]
      exact isEllipticMatrix_one_le hΘ
  obtain ⟨g, hgm, hgp, hbg⟩ :=
    (Source.AKL.field_ae_elliptic_iff_exists_pointwise_representative hΘ
      (AEEqFun.mk _ hcmeas.aestronglyMeasurable)).1 hbell
  refine ⟨lam, Lam, fun x => lam • g x, hlam, hle, hgm.const_smul lam,
    fun x => isEllipticMatrix_smul hlam hle (hgp x), ?_⟩
  filter_upwards [AEEqFun.coeFn_mk _ hcmeas.aestronglyMeasurable, hbg,
    AEEqFun.coeFn_smul (lam⁻¹ : ℝ) a] with x hbx hbgx hsmx hxball
  have hgx : g x = lam⁻¹ • a x := by
    rw [← hbgx, hbx, ite_eq_left hxball, hsmx]
    rfl
  rw [hgx, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]

/-- **The pointwise representative on a bounded set.**  Every field of the
coefficient space has a measurable representative, equal to it almost everywhere,
that is uniformly elliptic at every point of a prescribed bounded set. -/
theorem exists_pointwise_elliptic_representative {a : Source.AKL.Field d}
    (ha : AEUniformlyEllipticField a) {S : Set (Vec d)}
    (hS : Bornology.IsBounded S) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧ Measurable f ∧
      (∀ x ∈ S, IsEllipticMatrix lam Lam (f x)) ∧
      (⇑a : Vec d → Mat d) =ᵐ[volume] f := by
  classical
  obtain ⟨R, hR, hSR⟩ := exists_ball_of_isBounded hS
  obtain ⟨lam, Lam, f, hlam, hle, hfm, hfp, hfa⟩ := exists_ball_representative ha hR
  refine ⟨lam, Lam,
    fun x => if x ∈ Metric.ball (0 : Vec d) R then f x else (⇑a : Vec d → Mat d) x,
    hlam, hle, Measurable.ite measurableSet_ball hfm a.measurable, ?_, ?_⟩
  · intro x hx
    simp only [ite_eq_left (hSR hx)]
    exact hfp x
  · filter_upwards [hfa] with x hx
    by_cases hxb : x ∈ Metric.ball (0 : Vec d) R
    · simp only [ite_eq_left hxb]
      exact hx hxb
    · simp only [ite_eq_right hxb]

/-- **The locally elliptic representative.**  Every field of the coefficient
space has one measurable representative, equal to it almost everywhere, that is
uniformly elliptic at every point of every ball, with the constants of that ball:
the representatives of the balls of integer radius are glued along the shells
they exhaust `ℝ^d` by. -/
theorem exists_locally_pointwise_elliptic_representative {a : Source.AKL.Field d}
    (ha : AEUniformlyEllipticField a) :
    ∃ f : CoeffField d, Measurable f ∧
      (⇑a : Vec d → Mat d) =ᵐ[volume] f ∧
      ∀ R : ℝ, 0 < R → ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
        ∀ x ∈ Metric.ball (0 : Vec d) R, IsEllipticMatrix lam Lam (f x) := by
  classical
  choose lam Lam g hlam hle hgm hgp hga using fun n : ℕ =>
    exists_ball_representative ha (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
  have hcover : ∀ x : Vec d, ∃ n : ℕ, x ∈ Metric.ball (0 : Vec d) ((n : ℝ) + 1) := by
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    exact ⟨n, mem_ball_zero_iff.2 (hn.trans (lt_add_one _))⟩
  refine ⟨fun x => g (Nat.find (hcover x)) x,
    Measurable.find hgm (fun _ => measurableSet_ball) hcover, ?_, ?_⟩
  · have hall : ∀ᵐ x ∂volume, ∀ n : ℕ,
        x ∈ Metric.ball (0 : Vec d) ((n : ℝ) + 1) → a x = g n x :=
      (ae_all_iff (p := fun x (n : ℕ) =>
        x ∈ Metric.ball (0 : Vec d) ((n : ℝ) + 1) → a x = g n x)).2 hga
    filter_upwards [hall] with x hx
    exact hx (Nat.find (hcover x)) (Nat.find_spec (hcover x))
  · intro R hR
    set K : ℕ := ⌈R⌉₊ with hK
    refine ⟨(Finset.range (K + 1)).inf' Finset.nonempty_range_add_one lam,
      (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one Lam, ?_, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff _).2 fun n _ => hlam n
    · exact le_trans (Finset.inf'_le lam (Finset.mem_range.2 (Nat.succ_pos K)))
        (le_trans (hle 0)
          (Finset.le_sup' Lam (Finset.mem_range.2 (Nat.succ_pos K))))
    · intro x hx
      have hxK : x ∈ Metric.ball (0 : Vec d) ((K : ℝ) + 1) := by
        refine mem_ball_zero_iff.2 (lt_of_lt_of_le (mem_ball_zero_iff.1 hx) ?_)
        exact le_trans (Nat.le_ceil R) (by linarith only [])
      have hmem : Nat.find (hcover x) ∈ Finset.range (K + 1) :=
        Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.find_le hxK))
      exact (hgp (Nat.find (hcover x)) x).mono
        ((Finset.lt_inf'_iff _).2 fun n _ => hlam n)
        (Finset.inf'_le lam hmem) (Finset.le_sup' Lam hmem)

/-- **The everywhere elliptic representative of a bounded set.**  Every field of
the coefficient space agrees, almost everywhere on a prescribed bounded set, with
a measurable field that is uniformly elliptic at every point of `ℝ^d`. -/
theorem exists_globally_elliptic_representative_ae_eq_on {a : Source.AKL.Field d}
    (ha : AEUniformlyEllipticField a) {S : Set (Vec d)}
    (hS : Bornology.IsBounded S) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧ Measurable f ∧
      (∀ x, IsEllipticMatrix lam Lam (f x)) ∧
      (⇑a : Vec d → Mat d) =ᵐ[volume.restrict S] f := by
  obtain ⟨R, hR, hSR⟩ := exists_ball_of_isBounded hS
  obtain ⟨lam, Lam, f, hlam, hle, hfm, hfp, hfa⟩ := exists_ball_representative ha hR
  refine ⟨lam, Lam, f, hlam, hle, hfm, hfp, ?_⟩
  filter_upwards [ae_restrict_of_ae hfa,
    ae_restrict_mem_of_subset hSR measurableSet_ball] with x hx hxb
  exact hx hxb

end

end HighContrast
end HCPolySupport
