/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormProductMoment
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Finite sums in mixed norms

The three coordinate terms in an advective derivative inherit the same
finite mixed norm as their sum.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A sum of three scalar fields preserves slicewise membership and a finite
time moment in a finite mixed Lebesgue space. -/
theorem lps_mixed_sum_three_moment
    {T p q : ℝ} {f : Fin 3 → ParabolicPoint → ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hf : ∀ i, AEStronglyMeasurable (f i)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hSlice : ∀ i, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => f i (x,t)) (ENNReal.ofReal q) volume)
    (hMoment : ∀ i, (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => f i (x,t)) (ENNReal.ofReal q) volume ^ p) < ⊤) :
    (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => ∑ i : Fin 3, f i (x,t))
        (ENNReal.ofReal q) volume) ∧
    (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => ∑ i : Fin 3, f i (x,t))
        (ENNReal.ofReal q) volume ^ p) < ⊤ := by
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  let ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod μt
  let N : Fin 3 → ℝ → ℝ≥0∞ := fun i t =>
    eLpNorm (fun x : Vec3 => f i (x,t)) (ENNReal.ofReal q) volume
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hqtop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hNmeas : ∀ i, AEMeasurable (N i) μt := by
    intro i
    have hfiν : AEStronglyMeasurable (f i) ν := by
      change AEStronglyMeasurable (f i)
        ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))
      rw [← serrin_slab_measure_eq T]
      exact hf i
    have hpow : AEMeasurable (fun z : Vec3 × ℝ => ‖f i z‖ₑ ^ q) ν :=
      hfiν.enorm.pow_const q
    have hlin : AEMeasurable (fun t : ℝ =>
      ∫⁻ x : Vec3, ‖f i (x,t)‖ₑ ^ q ∂volume) μt := hpow.lintegral_prod_left'
    have hformula : N i =ᵐ[μt] fun t =>
        (∫⁻ x : Vec3, ‖f i (x,t)‖ₑ ^ q ∂volume) ^ (1 / q) := by
      filter_upwards [hSlice i] with t ht
      change eLpNorm (fun x : Vec3 => f i (x,t)) (ENNReal.ofReal q) volume = _
      have hformula := eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_pos.mpr hq0).ne' hqtop ht.aestronglyMeasurable
      rw [hformula, ENNReal.toReal_ofReal hq0.le]
    exact (hlin.pow_const (1 / q)).congr hformula.symm
  have hMoment' (i : Fin 3) : (∫⁻ t : ℝ, N i t ^ p ∂μt) < ⊤ := by
    simpa [N, μt] using hMoment i
  have hSumMeas01 : AEMeasurable (fun t : ℝ => N 0 t + N 1 t) μt :=
    (hNmeas 0).add (hNmeas 1)
  have hSumMeas : AEMeasurable (fun t : ℝ => N 0 t + N 1 t + N 2 t) μt :=
    hSumMeas01.add (hNmeas 2)
  have hSumMoment01 : (∫⁻ t : ℝ, (N 0 t + N 1 t) ^ p ∂μt) < ⊤ :=
    ENNReal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top
      (hNmeas 0) (hMoment' 0) (hMoment' 1) hp
  have hSumMoment : (∫⁻ t : ℝ, (N 0 t + N 1 t + N 2 t) ^ p ∂μt) < ⊤ :=
    ENNReal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top
      hSumMeas01 (by simpa [Pi.add_apply] using hSumMoment01) (hMoment' 2) hp
  have hSliceSum : ∀ᵐ t ∂μt,
      MemLp (fun x : Vec3 => ∑ i : Fin 3, f i (x,t))
        (ENNReal.ofReal q) volume := by
    filter_upwards [hSlice 0, hSlice 1, hSlice 2] with t h0 h1 h2
    have hsum (s : Finset (Fin 3)) :
        MemLp (fun x : Vec3 => ∑ i ∈ s, f i (x,t)) (ENNReal.ofReal q) volume := by
      classical
      induction s using Finset.induction_on with
      | empty =>
          simp
      | @insert i s hi ih =>
          have hmem : MemLp (fun x : Vec3 => f i (x,t))
              (ENNReal.ofReal q) volume := by
            fin_cases i <;> assumption
          have hsumEq :
              (fun x : Vec3 => ∑ j ∈ insert i s, f j (x,t)) =
                (fun x : Vec3 => f i (x,t) + ∑ j ∈ s, f j (x,t)) := by
            funext x
            simp [Finset.sum_insert, hi]
          rw [hsumEq]
          exact hmem.add ih
    simpa using hsum Finset.univ
  have hNormBound : ∀ᵐ t ∂μt,
      eLpNorm (fun x : Vec3 => ∑ i : Fin 3, f i (x,t))
        (ENNReal.ofReal q) volume ≤ N 0 t + N 1 t + N 2 t := by
    filter_upwards [hSlice 0, hSlice 1, hSlice 2] with t h0 h1 h2
    have hsum := eLpNorm_sum_le (μ := volume) (p := ENNReal.ofReal q)
      (s := Finset.univ) (f := fun i x => f i (x,t))
      (ENNReal.one_le_ofReal.mpr hq)
    have hfun : (∑ i : Fin 3, fun x : Vec3 => f i (x,t)) =
        (fun x : Vec3 => ∑ i : Fin 3, f i (x,t)) := by
      funext x
      simp
    rw [hfun] at hsum
    have hsum' : eLpNorm (fun x : Vec3 => ∑ i : Fin 3, f i (x,t))
        (ENNReal.ofReal q) volume ≤
        ∑ i : Fin 3, eLpNorm (fun x : Vec3 => f i (x,t))
          (ENNReal.ofReal q) volume := hsum
    simpa [N, Fin.sum_univ_succ, add_assoc] using hsum'
  have hMomentSum : (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => ∑ i : Fin 3, f i (x,t))
        (ENNReal.ofReal q) volume ^ p) < ⊤ := by
    apply lt_of_le_of_lt (lintegral_mono_ae ?_) hSumMoment
    filter_upwards [hNormBound] with t ht
    exact ENNReal.rpow_le_rpow ht (by positivity)
  refine ⟨?_, ?_⟩
  · simpa [μt] using hSliceSum
  · simpa [μt] using hMomentSum

end ESS

end
