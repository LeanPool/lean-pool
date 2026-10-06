/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# High-contrast homogenization: Consistency.QualitativeClass

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# An integrability consequence of local uniform ellipticity

This module checks the definition `CoeffSpace d` of the development: that the
locally uniformly elliptic fields it collects satisfy the local integrability
condition encoded by `IsQualitativeEllipticField`. This is an analytic
consequence of the paper's stronger local essential boundedness condition
`e.qualitative.ellipticity` in `s.introduction`.

This module is a consistency check of that definition and is not a result of
the paper.

The paper takes as its coefficient space the measurable fields
`a : ℝ^d → ℝ^{d×d}` whose symmetric part `s` is positive definite almost
everywhere and for which, writing `k` for the skew-symmetric part, the three
matrix fields

```
s,      s⁻¹,      kᵗ s⁻¹ k
```

are locally essentially bounded, entry by entry (`e.qualitative.ellipticity`).
The predicate checked here asks only that they be locally integrable.

The class used in this development, `AEUniformlyEllipticField`, asks that almost
every value of the field on a bounded set be uniformly elliptic, for a pair of
ellipticity constants attached to the field and to the set. This file proves
that those bounds imply the local integrability needed by the analytic library.

Both halves are quantitative consequences of `IsEllipticMatrix`, read on one
bounded set at a time.  Coercivity of the values gives coercivity of the
symmetric parts, hence positive definiteness on every ball and so, the balls
exhausting `ℝ^d`, almost everywhere.  The entry bounds `|a i j| ≤ Λ` and
`|(s)⁻¹ i j| ≤ λ⁻¹` make each of the three fields essentially bounded entry by
entry on every bounded set, and a measurable function bounded almost everywhere
on every compact set is locally integrable for the Lebesgue measure.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped Matrix

noncomputable section

variable {d : ℕ}

/-! ## The three fields of the qualitative condition -/

/-- The field `kᵗ s⁻¹ k` of `e.qualitative.ellipticity`, formed from the
symmetric part `s` and the skew-symmetric part `k` of a matrix. -/
@[expose]
def skewSchurTerm (A : Mat d) : Mat d :=
  matTranspose (skewPart A) * (symmPart A)⁻¹ * skewPart A

/-- A local integrability condition used by the analytic library: a measurable
matrix field whose symmetric part is positive definite almost everywhere and
whose three fields `s`, `s⁻¹` and `kᵗ s⁻¹ k` are entrywise locally integrable.
The paper's `e.qualitative.ellipticity` requires local essential boundedness
of those fields. -/
structure IsQualitativeEllipticField (a : Vec d → Mat d) : Prop where
  /-- The field is Borel measurable. -/
  measurable : Measurable a
  /-- The symmetric part is positive definite almost everywhere. -/
  posDef_symmPart : ∀ᵐ x ∂volume, (symmPart (a x)).PosDef
  /-- `s ∈ L¹_loc`, entry by entry. -/
  locallyIntegrable_symmPart :
    ∀ i j, LocallyIntegrable (fun x => symmPart (a x) i j) volume
  /-- `s⁻¹ ∈ L¹_loc`, entry by entry. -/
  locallyIntegrable_symmPart_inv :
    ∀ i j, LocallyIntegrable (fun x => (symmPart (a x))⁻¹ i j) volume
  /-- `kᵗ s⁻¹ k ∈ L¹_loc`, entry by entry. -/
  locallyIntegrable_skewSchurTerm :
    ∀ i j, LocallyIntegrable (fun x => skewSchurTerm (a x) i j) volume

/-! ## Measurability of the derived fields -/

private theorem measurable_entry {M : Vec d → Mat d} (hM : Measurable M) (i j : Fin d) :
    Measurable (fun x => M x i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)

private theorem measurable_matTranspose {M : Vec d → Mat d} (hM : Measurable M) :
    Measurable (fun x => matTranspose (M x)) :=
  Measurable.of_eval fun i => Measurable.of_eval fun j =>
    measurable_entry hM j i

private theorem measurable_matMul {M N : Vec d → Mat d} (hM : Measurable M)
    (hN : Measurable N) : Measurable (fun x => M x * N x) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_entry hM i k).mul (measurable_entry hN k j)

private theorem measurable_symmPart {M : Vec d → Mat d} (hM : Measurable M) :
    Measurable (fun x => symmPart (M x)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [symmPart]
  exact ((measurable_entry hM i j).add (measurable_entry hM j i)).div_const 2

private theorem measurable_skewPart {M : Vec d → Mat d} (hM : Measurable M) :
    Measurable (fun x => skewPart (M x)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [skewPart]
  exact ((measurable_entry hM i j).sub (measurable_entry hM j i)).div_const 2

/-- The pointwise inverse of a measurable matrix field is measurable: it is the
adjugate scaled by the inverse determinant, and both are measurable. -/
private theorem measurable_matInv {M : Vec d → Mat d} (hM : Measurable M) :
    Measurable (fun x => (M x)⁻¹) := by
  have hdet : Measurable (fun x => (M x).det) :=
    (Continuous.matrix_det continuous_id).measurable.comp hM
  have hadj : Measurable (fun x => (M x).adjugate) :=
    (Continuous.matrix_adjugate continuous_id).measurable.comp hM
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact hdet.inv.mul (measurable_entry hadj i j)

private theorem measurable_skewSchurTerm {M : Vec d → Mat d} (hM : Measurable M) :
    Measurable (fun x => skewSchurTerm (M x)) :=
  measurable_matMul
    (measurable_matMul (measurable_matTranspose (measurable_skewPart hM))
      (measurable_matInv (measurable_symmPart hM)))
    (measurable_skewPart hM)

/-! ## Essentially bounded measurable functions are locally integrable -/

/-- A measurable scalar field on `Vec d` that is bounded almost everywhere on
every bounded set is locally integrable for the Lebesgue measure. -/
theorem locallyIntegrable_of_ae_abs_le_isBounded {f : Vec d → ℝ} (hf : Measurable f)
    (hC : ∀ S : Set (Vec d), Bornology.IsBounded S →
      ∃ C : ℝ, ∀ᵐ x ∂volume, x ∈ S → |f x| ≤ C) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨C, hCk⟩ := hC k hk.isBounded
  refine Measure.integrableOn_of_bounded (hk.measure_lt_top).ne hf.aestronglyMeasurable
    (M := C) ?_
  filter_upwards [ae_restrict_of_ae hCk, ae_restrict_mem hk.measurableSet] with x hx hxk
  simpa [Real.norm_eq_abs] using hx hxk

/-! ## Entry bounds on the three fields -/

private theorem abs_average_le {u v C : ℝ} (hu : |u| ≤ C) (hv : |v| ≤ C) :
    |(u + v) / 2| ≤ C := by
  obtain ⟨hu1, hu2⟩ := abs_le.1 hu
  obtain ⟨hv1, hv2⟩ := abs_le.1 hv
  exact abs_le.2 ⟨by linarith only [hu1, hv1], by linarith only [hu2, hv2]⟩

private theorem abs_halfSub_le {u v C : ℝ} (hu : |u| ≤ C) (hv : |v| ≤ C) :
    |(u - v) / 2| ≤ C := by
  obtain ⟨hu1, hu2⟩ := abs_le.1 hu
  obtain ⟨hv1, hv2⟩ := abs_le.1 hv
  exact abs_le.2 ⟨by linarith only [hu1, hv2], by linarith only [hu2, hv1]⟩

private theorem abs_apply_symmPart_le {A : Mat d} {C : ℝ}
    (h : ∀ i j, |A i j| ≤ C) (i j : Fin d) : |symmPart A i j| ≤ C := by
  simpa only [symmPart] using abs_average_le (h i j) (h j i)

private theorem abs_apply_skewPart_le {A : Mat d} {C : ℝ}
    (h : ∀ i j, |A i j| ≤ C) (i j : Fin d) : |skewPart A i j| ≤ C := by
  simpa only [skewPart] using abs_halfSub_le (h i j) (h j i)

private theorem abs_apply_mul_le {A B : Mat d} {α β : ℝ} (hα : 0 ≤ α)
    (hA : ∀ i j, |A i j| ≤ α) (hB : ∀ i j, |B i j| ≤ β) (i j : Fin d) :
    |(A * B) i j| ≤ d * (α * β) := by
  rw [Matrix.mul_apply]
  calc |∑ k, A i k * B k j| ≤ ∑ k, |A i k * B k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, α * β := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) hα
    _ = d * (α * β) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem abs_apply_skewSchurTerm_le {lam Lam : ℝ} {A : Mat d}
    (h : IsEllipticMatrix lam Lam A) (i j : Fin d) :
    |skewSchurTerm A i j| ≤ d * (d * (Lam * lam⁻¹) * Lam) := by
  have hLam : 0 ≤ Lam := le_trans h.1.le h.2.1
  have hentry : ∀ p q : Fin d, |A p q| ≤ Lam := abs_apply_le_of_isEllipticMatrix h
  have hskew : ∀ p q : Fin d, |skewPart A p q| ≤ Lam := abs_apply_skewPart_le hentry
  have htrans : ∀ p q : Fin d, |matTranspose (skewPart A) p q| ≤ Lam := fun p q =>
    hskew q p
  have hinv : ∀ p q : Fin d, |((symmPart A)⁻¹ : Mat d) p q| ≤ lam⁻¹ :=
    abs_apply_symmPartInv_le_of_isEllipticMatrix h
  have hfirst : ∀ p q : Fin d,
      |(matTranspose (skewPart A) * (symmPart A)⁻¹) p q| ≤ d * (Lam * lam⁻¹) :=
    abs_apply_mul_le hLam htrans hinv
  have hnonneg : (0 : ℝ) ≤ d * (Lam * lam⁻¹) := by
    have : (0 : ℝ) ≤ lam⁻¹ := le_of_lt (inv_pos.2 h.1)
    positivity
  exact abs_apply_mul_le hnonneg hfirst hskew i j

/-! ## The implication -/

/-- The symmetric part of a uniformly elliptic matrix is positive definite. -/
theorem posDef_symmPart_of_isEllipticMatrix {lam Lam : ℝ} {A : Mat d}
    (h : IsEllipticMatrix lam Lam A) : (symmPart A).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, symmPart, add_comm]
  · intro x hx
    have hrewrite : star x ⬝ᵥ (symmPart A *ᵥ x) = vecDot x (matVecMul (symmPart A) x) := by
      simp [dotProduct, Matrix.mulVec, vecDot, matVecMul]
    rw [hrewrite]
    have hpos : 0 < vecNormSq x := by
      rcases lt_or_eq_of_le (vecNormSq_nonneg x) with hlt | heq
      · exact hlt
      · exact absurd (vecNormSq_eq_zero heq.symm) hx
    have hlam : 0 < lam := h.1
    exact lt_of_lt_of_le (by positivity) (lowerBound_symmPart_of_isEllipticMatrix h x)

/-- **The symmetric part is positive definite almost everywhere**, the first
half of the coefficient class of `s.introduction`.  The balls of integer
radius exhaust `ℝ^d`, so the countably many null sets of the local statements
unite into one. -/
theorem ae_posDef_symmPart_of_aeUniformlyEllipticField {a : Source.AKL.Field d}
    (ha : AEUniformlyEllipticField a) :
    ∀ᵐ x ∂volume, (symmPart (a x)).PosDef := by
  have h : ∀ n : ℕ, ∀ᵐ x ∂volume,
      x ∈ Metric.ball (0 : Vec d) ((n : ℝ) + 1) → (symmPart (a x)).PosDef := by
    intro n
    obtain ⟨lam, Lam, -, -, hell⟩ := ha ((n : ℝ) + 1) (by positivity)
    filter_upwards [hell] with x hx hxb
    exact posDef_symmPart_of_isEllipticMatrix (hx hxb)
  rw [← ae_all_iff] at h
  filter_upwards [h] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact hx n (mem_ball_zero_iff.2 (hn.trans (lt_add_one _)))

/-- **`s ∈ L¹_loc`**, entry by entry: an integrability consequence of the
paper's first locally bounded field in `e.qualitative.ellipticity`. -/
theorem locallyIntegrable_symmPart_of_aeUniformlyEllipticField
    {a : Source.AKL.Field d} (ha : AEUniformlyEllipticField a) (i j : Fin d) :
    LocallyIntegrable (fun x => symmPart (a x) i j) volume := by
  refine locallyIntegrable_of_ae_abs_le_isBounded
    (measurable_entry (measurable_symmPart a.stronglyMeasurable.measurable) i j)
    fun S hS => ?_
  obtain ⟨M, -, hM⟩ := ae_abs_entry_le_of_aeUniformlyEllipticField ha hS
  refine ⟨M, ?_⟩
  filter_upwards [hM] with x hx hxS
  exact abs_apply_symmPart_le (hx hxS) i j

/-- **`s⁻¹ ∈ L¹_loc`**, entry by entry: an integrability consequence of the
paper's second locally bounded field in `e.qualitative.ellipticity`. -/
theorem locallyIntegrable_symmPart_inv_of_aeUniformlyEllipticField
    {a : Source.AKL.Field d} (ha : AEUniformlyEllipticField a) (i j : Fin d) :
    LocallyIntegrable (fun x => (symmPart (a x))⁻¹ i j) volume := by
  refine locallyIntegrable_of_ae_abs_le_isBounded
    (measurable_entry (measurable_matInv
      (measurable_symmPart a.stronglyMeasurable.measurable)) i j) fun S hS => ?_
  obtain ⟨lam, Lam, -, -, hell⟩ := ha.exists_ae_isEllipticMatrix_of_isBounded hS
  refine ⟨lam⁻¹, ?_⟩
  filter_upwards [hell] with x hx hxS
  exact abs_apply_symmPartInv_le_of_isEllipticMatrix (hx hxS) i j

/-- **`kᵗ s⁻¹ k ∈ L¹_loc`**, entry by entry: an integrability consequence of
the paper's third locally bounded field in `e.qualitative.ellipticity`. -/
theorem locallyIntegrable_skewSchurTerm_of_aeUniformlyEllipticField
    {a : Source.AKL.Field d} (ha : AEUniformlyEllipticField a) (i j : Fin d) :
    LocallyIntegrable (fun x => skewSchurTerm (a x) i j) volume := by
  refine locallyIntegrable_of_ae_abs_le_isBounded
    (measurable_entry (measurable_skewSchurTerm a.stronglyMeasurable.measurable) i j)
    fun S hS => ?_
  obtain ⟨lam, Lam, -, -, hell⟩ := ha.exists_ae_isEllipticMatrix_of_isBounded hS
  refine ⟨d * (d * (Lam * lam⁻¹) * Lam), ?_⟩
  filter_upwards [hell] with x hx hxS
  exact abs_apply_skewSchurTerm_le (hx hxS) i j

/-- **Local uniform ellipticity implies the analytic integrability condition**:
a locally uniformly elliptic field is
measurable, its symmetric part is positive definite almost everywhere, and its
three fields `s`, `s⁻¹` and `kᵗ s⁻¹ k` are entrywise locally integrable. -/
theorem isQualitativeEllipticField_of_aeUniformlyEllipticField
    {a : Source.AKL.Field d} (ha : AEUniformlyEllipticField a) :
    IsQualitativeEllipticField (⇑a) where
  measurable := a.stronglyMeasurable.measurable
  posDef_symmPart := ae_posDef_symmPart_of_aeUniformlyEllipticField ha
  locallyIntegrable_symmPart :=
    locallyIntegrable_symmPart_of_aeUniformlyEllipticField ha
  locallyIntegrable_symmPart_inv :=
    locallyIntegrable_symmPart_inv_of_aeUniformlyEllipticField ha
  locallyIntegrable_skewSchurTerm :=
    locallyIntegrable_skewSchurTerm_of_aeUniformlyEllipticField ha

/-- Every field of the coefficient space `Ω` satisfies the analytic local
integrability condition. -/
theorem isQualitativeEllipticField_coeffSpace (a : CoeffSpace d) :
    IsQualitativeEllipticField (⇑a.1) :=
  isQualitativeEllipticField_of_aeUniformlyEllipticField a.2

end

end HighContrast
end HCPolySupport
