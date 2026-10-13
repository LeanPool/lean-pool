/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.OriginConcentration

/-!
# ShellSecondMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The exact second moment of a single shell

ABK26 uses, in the proof of its stream `L²` displays, the non-degeneracy
normalization

`⨍_{cu_l} j_k(x) : j_k(x) dx = c⁺ (log 3) 3^{2γk} + O_{Γ₁}(...)`,

whose deterministic part is the pointwise identity

`E[ ‖j_k(x)‖_F² ] = 3^{2γk} c⁺ log 3   for every x ∈ ℝ^d`.

This module proves that identity together with the integrability and mean-zero
statements it rests on.  Here `c⁺` is
`Algsuperdiff.Section3.Disorder.cstarPlus`, characterized by
`originFrobeniusMass M = c⁺ log 3` with
`originFrobeniusMass M = E[‖j_0(0)‖_F²]`.

The proof is the source's: the frozen marginal scaling law
`e.diff.law.shift` (`ShellLawPrefix.marginal_scaling`) turns shell `k` at `x`
into `3^{γk} j_0(3^{-k} x)`, the frozen (J1) stationarity moves the base point
`3^{-k} x` to the origin, and the resulting expectation is by definition
`originFrobeniusMass`.  No independence is used here.

## Main results

* `map_shellFrobeniusMass_eq`: the exact law transport for the shell Frobenius
  mass.
* `integral_shellFrobeniusMass`: `E[‖j_k(x)‖_F²] = 3^{2γk} c⁺ log 3`.
* `integrable_shellFrobeniusMass`: its integrability.
* `integral_shell_entry_at_point_eq_zero`: (J1) mean zero, transported to
  shell `k` and an arbitrary base point.  (`Provider/Stream/TranslatedTransport.lean`
  proves the same statement under the name `integral_shell_entry_eq_zero`; the
  two are interchangeable.)
* `memLp_two_shell_entry`: every scalar entry of a shell value lies in `L²`.

## References

* ABK26, `e.km.L2.expectation`.
* ABK26, `e.km.kn.L2.bound`.
* ABK26 ((J4) and the non-degeneracy constant).
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Elementary Frobenius facts -/

/-- The Frobenius mass is quadratically homogeneous. -/
private theorem matrixFrobeniusNormSq_smul (c : ℝ) (A : Mat d) :
    matrixFrobeniusNormSq (c • A) = c ^ 2 * matrixFrobeniusNormSq A := by
  unfold matrixFrobeniusNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, mul_pow]

/-- Each squared entry is dominated by the full Frobenius mass. -/
theorem sq_entry_le_matrixFrobeniusNormSq (A : Mat d) (i l : Fin d) :
    A i l ^ 2 ≤ matrixFrobeniusNormSq A := by
  have h1 : A i l ^ 2 ≤ ∑ j : Fin d, A i j ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin d => A i j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ l)
  have h2 : (∑ j : Fin d, A i j ^ 2) ≤ ∑ p : Fin d, ∑ j : Fin d, A p j ^ 2 :=
    Finset.single_le_sum (f := fun p : Fin d => ∑ j : Fin d, A p j ^ 2)
      (fun p _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact h1.trans h2

/-- The Frobenius mass of a shell value at a fixed point is a measurable
observable of the shell. -/
theorem measurable_shellFrobeniusMass (x : Vec d) :
    Measurable (fun j : ShellField d => matrixFrobeniusNormSq (j x)) := by
  unfold matrixFrobeniusNormSq
  exact Finset.univ.measurable_sum fun i _ =>
    Finset.univ.measurable_sum fun l _ =>
      (ShellField.measurable_eval_entry x i l).pow_const 2

/-! ## Law transport for the shell Frobenius mass -/

/-- The exact effect of the frozen triadic scaling action on the Frobenius
mass: the amplitude enters squared. -/
private theorem matrixFrobeniusNormSq_triadicScale_apply (gamma : ℝ) (k : ℤ)
    (j : ShellField d) (x : Vec d) :
    matrixFrobeniusNormSq (ShellField.triadicScale gamma k j x) =
      (3 : ℝ) ^ (2 * gamma * (k : ℝ)) *
        matrixFrobeniusNormSq (j ((((3 : ℝ) ^ k)⁻¹) • x)) := by
  rw [ShellField.triadicScale_apply, matrixFrobeniusNormSq_smul]
  congr 1
  show ((3 : ℝ) ^ (gamma * (k : ℝ))) ^ 2 = (3 : ℝ) ^ (2 * gamma * (k : ℝ))
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (gamma * (k : ℝ))) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

/-- The law of the shell-`k` Frobenius mass at any point `x` equals the law of
`3^{2γk}` times the zero-shell Frobenius mass at the origin.  This combines
the frozen marginal scaling law with the frozen (J1) stationarity. -/
theorem map_shellFrobeniusMass_eq (M : ABKModel d) (k : ℤ) (x : Vec d) :
    Measure.map
        (fun omega : ShellSeq d => matrixFrobeniusNormSq ((omega k) x))
        M.P.toMeasure =
      Measure.map
        (fun j : ShellField d =>
          (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) * matrixFrobeniusNormSq (j 0))
        (ShellField.zeroShellLaw M.P).toMeasure := by
  have hbase : Measurable (fun j : ShellField d =>
      (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) * matrixFrobeniusNormSq (j 0)) :=
    measurable_const.mul (measurable_shellFrobeniusMass (0 : Vec d))
  have htranslate := map_zeroObservable_translate_eq M ((((3 : ℝ) ^ k)⁻¹) • x)
    (fun j : ShellField d =>
      (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) * matrixFrobeniusNormSq (j 0)) hbase
  have hshift : (fun j : ShellField d =>
        (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          matrixFrobeniusNormSq
            (ShellField.translate ((((3 : ℝ) ^ k)⁻¹) • x) j 0)) =
      fun j : ShellField d =>
        (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          matrixFrobeniusNormSq (j ((((3 : ℝ) ^ k)⁻¹) • x)) := by
    funext j
    rw [ShellField.translate_apply, zero_add]
  rw [hshift] at htranslate
  rw [map_shellObservable_eq_zero_triadicScale M k
    (fun j : ShellField d => matrixFrobeniusNormSq (j x))
    (measurable_shellFrobeniusMass x), ← htranslate]
  refine Measure.map_congr ?_
  filter_upwards with j
  exact matrixFrobeniusNormSq_triadicScale_apply M.gamma k j x

/-! ## The zero-shell Frobenius mass -/

/-- The zero-shell Frobenius mass at the origin is integrable, by the frozen
(J2) Gaussian tail. -/
theorem integrable_zeroShellFrobeniusMass (M : ABKModel d) :
    Integrable (fun j : ShellField d => matrixFrobeniusNormSq (j 0))
      (ShellField.zeroShellLaw M.P).toMeasure := by
  have hmap : (ShellField.zeroShellLaw M.P).toMeasure =
      Measure.map (fun F : ShellSeq d => F 0) M.P.toMeasure := rfl
  rw [hmap]
  refine (integrable_map_measure ?_ ?_).mpr ?_
  · exact (measurable_shellFrobeniusMass (0 : Vec d)).aestronglyMeasurable
  · exact (ShellField.measurable_zeroShellMap (d := d)).aemeasurable
  · exact Disorder.integrable_originFrobeniusMass M

/-- The zero-shell Frobenius mass at the origin is exactly `c⁺ log 3`. -/
theorem integral_zeroShellFrobeniusMass (M : ABKModel d) :
    ∫ j : ShellField d, matrixFrobeniusNormSq (j 0)
        ∂(ShellField.zeroShellLaw M.P).toMeasure =
      Disorder.cstarPlus M * Real.log 3 := by
  have hmap : (ShellField.zeroShellLaw M.P).toMeasure =
      Measure.map (fun F : ShellSeq d => F 0) M.P.toMeasure := rfl
  rw [hmap, integral_map (ShellField.measurable_zeroShellMap (d := d)).aemeasurable
    (measurable_shellFrobeniusMass (0 : Vec d)).aestronglyMeasurable]
  exact Disorder.cstarPlus_characterization M

/-! ## The shell second moment -/

/-- The Frobenius mass of shell `k` at a point is integrable. -/
theorem integrable_shellFrobeniusMass (M : ABKModel d) (k : ℤ) (x : Vec d) :
    Integrable (fun omega : ShellSeq d => matrixFrobeniusNormSq ((omega k) x))
      M.P.toMeasure := by
  have hshell : Measurable
      (fun omega : ShellSeq d => matrixFrobeniusNormSq ((omega k) x)) :=
    (measurable_shellFrobeniusMass x).comp (measurable_pi_apply k)
  have hbase : Measurable (fun j : ShellField d =>
      (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) * matrixFrobeniusNormSq (j 0)) :=
    measurable_const.mul (measurable_shellFrobeniusMass (0 : Vec d))
  have hbase_int : Integrable (fun j : ShellField d =>
      (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) * matrixFrobeniusNormSq (j 0))
      (ShellField.zeroShellLaw M.P).toMeasure :=
    (integrable_zeroShellFrobeniusMass M).const_mul _
  have hid : Integrable id (Measure.map
      (fun omega : ShellSeq d => matrixFrobeniusNormSq ((omega k) x))
      M.P.toMeasure) := by
    rw [map_shellFrobeniusMass_eq M k x]
    refine (integrable_map_measure aestronglyMeasurable_id hbase.aemeasurable).mpr ?_
    simpa only [Function.comp_def, id_eq] using hbase_int
  simpa only [Function.comp_def, id_eq] using
    (integrable_map_measure aestronglyMeasurable_id hshell.aemeasurable).mp hid

/-- The exact shell second-moment identity behind ABK26's non-degeneracy
normalization: for every scale `k` and every point `x`,

`E[ ‖j_k(x)‖_F² ] = 3^{2γk} c⁺ log 3`. -/
theorem integral_shellFrobeniusMass (M : ABKModel d) (k : ℤ) (x : Vec d) :
    ∫ omega : ShellSeq d, matrixFrobeniusNormSq ((omega k) x) ∂M.P.toMeasure =
      (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (Disorder.cstarPlus M * Real.log 3) := by
  have hshell : Measurable
      (fun omega : ShellSeq d => matrixFrobeniusNormSq ((omega k) x)) :=
    (measurable_shellFrobeniusMass x).comp (measurable_pi_apply k)
  have hbase : Measurable (fun j : ShellField d =>
      (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) * matrixFrobeniusNormSq (j 0)) :=
    measurable_const.mul (measurable_shellFrobeniusMass (0 : Vec d))
  calc ∫ omega : ShellSeq d, matrixFrobeniusNormSq ((omega k) x) ∂M.P.toMeasure
      = ∫ t : ℝ, t ∂Measure.map
          (fun omega : ShellSeq d => matrixFrobeniusNormSq ((omega k) x))
          M.P.toMeasure :=
        (integral_map hshell.aemeasurable aestronglyMeasurable_id).symm
    _ = ∫ t : ℝ, t ∂Measure.map
          (fun j : ShellField d =>
            (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) * matrixFrobeniusNormSq (j 0))
          (ShellField.zeroShellLaw M.P).toMeasure := by
        rw [map_shellFrobeniusMass_eq M k x]
    _ = ∫ j : ShellField d,
          (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) * matrixFrobeniusNormSq (j 0)
          ∂(ShellField.zeroShellLaw M.P).toMeasure :=
        integral_map hbase.aemeasurable aestronglyMeasurable_id
    _ = (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          ∫ j : ShellField d, matrixFrobeniusNormSq (j 0)
            ∂(ShellField.zeroShellLaw M.P).toMeasure :=
        integral_const_mul _ _
    _ = (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          (Disorder.cstarPlus M * Real.log 3) := by
        rw [integral_zeroShellFrobeniusMass M]

/-! ## Mean zero away from the origin -/

/-- ABK26's "`j_k` is mean zero" at an arbitrary base point and an arbitrary
scale.  This is the frozen (J1) mean-zero field, transported through the frozen
marginal scaling law.

Duplication note:
`Algsuperdiff.Section3.Provider.Stream.integral_shell_entry_eq_zero`, in
`Provider/Stream/TranslatedTransport.lean`, is the same statement with the same
proof.  A distinct name is used here so that both files can coexist. -/
theorem integral_shell_entry_at_point_eq_zero (M : ABKModel d) (k : ℤ) (x : Vec d)
    (i l : Fin d) :
    ∫ omega : ShellSeq d, (omega k) x i l ∂M.P.toMeasure = 0 := by
  rw [integral_shellObservable_eq M k (fun j : ShellField d => j x i l)
    (ShellField.measurable_eval_entry x i l)]
  have hpt : ∀ j : ShellField d, ShellField.triadicScale M.gamma k j x i l =
      (3 : ℝ) ^ (M.gamma * (k : ℝ)) * (j ((((3 : ℝ) ^ k)⁻¹) • x) i l) := by
    intro j
    rw [ShellField.triadicScale_apply]
    rfl
  simp only [hpt]
  rw [integral_const_mul,
    integral_zeroShell_entry_eq_zero M ((((3 : ℝ) ^ k)⁻¹) • x) i l, mul_zero]

/-- Every scalar entry of a shell value lies in `L²`: this is the exact
second-moment bound supplied by `integrable_shellFrobeniusMass`. -/
theorem memLp_two_shell_entry (M : ABKModel d) (k : ℤ) (x : Vec d)
    (i l : Fin d) :
    MemLp (fun omega : ShellSeq d => (omega k) x i l) 2 M.P.toMeasure := by
  have hmeas : Measurable (fun omega : ShellSeq d => (omega k) x i l) :=
    (ShellField.measurable_eval_entry x i l).comp (measurable_pi_apply k)
  refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr ?_
  refine Integrable.mono' (integrable_shellFrobeniusMass M k x)
    ((hmeas.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_entry_le_matrixFrobeniusNormSq ((omega k) x) i l

end

end Algsuperdiff.Section3.Provider.Stream
