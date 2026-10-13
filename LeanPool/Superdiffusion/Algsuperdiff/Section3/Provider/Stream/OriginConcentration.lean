/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.BlockConcentration
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.ShellBounds

/-!
# OriginConcentration

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The stream increment at the origin: ABK26's `e.k.ell.upscales`

This module proves the first display in the concentration part of ABK26's
stream increment lemma: for `n < m`,

`|(k_m - k_n)(0)| ≤ O_{Γ₂}(C (∑_{k = n+1}^m 3^{2γk})^{1/2})
   ≤ O_{Γ₂}(C min{γ^{-1/2}, (m-n)^{1/2}} 3^{γm})`.

Following the source, the input is: the value display `e.jk.O`
(`isBigOWith_gammaSigma_localCubeControl_shell`), the independence of the
shells (the frozen prefix field `independent`), that `j_k(0)` is mean zero
(the frozen (J1) field `mean_zero`, transported to shell `k` through the
frozen marginal scaling law), and the concentration proposition.  The
`ℓ²`-aggregated amplitude is supplied by
`Algsuperdiff.Section3.Provider.Stream.isBigO_gammaSigma_two_sum_Ioc_geometric`.

Two deviations from the source display are recorded explicitly.

* The source works with the matrix-valued random variable `j_k(0)` directly.
  Here the concentration proposition is applied to each of the `d²` scalar
  entries, which are independent across `k` and mean zero, and the entries are
  recombined into `matrixOperatorNorm` through
  `matrixOperatorNorm ≤ matrixFrobeniusNorm ≤ ∑_{i,l} |·_{il}|` and the
  generalized triangle inequality.  This costs the explicit dimensional factor
  `Γ-triangle-constant · d²`, which is absorbed by the source's `C(d)`.
* The amplitude is stated in the final `min` form of the source display; the
  intermediate `ℓ²` form `(∑ 3^{2γk})^{1/2}` is not produced, since the source
  itself immediately replaces it by the `min` form via `e.geo.part.sum`.

## Main results

* `Algsuperdiff.Section3.Provider.Stream.integral_shell_origin_entry_eq_zero`
* `Algsuperdiff.Section3.Provider.Stream.iIndepFun_shell_origin_entry`
* `Algsuperdiff.Section3.Provider.Stream.isBigO_gammaSigma_originIncrement_entry`
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_gammaSigma_originIncrement`

## References

* ABK26, `e.k.ell.upscales`.
* ABK26, `e.jk.O`.
* ABK26, Proposition `p.concentration`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Matrix entries as continuous linear functionals -/

/-- Evaluation of a matrix entry, as a continuous linear functional for the
elementwise matrix norm carried by the frozen shell field. -/
def matrixEntryCLM (i l : Fin d) : Mat d →L[ℝ] ℝ :=
  LinearMap.mkContinuous (Matrix.entryLinearMap ℝ ℝ i l) 1 fun A => by
    simpa using Matrix.norm_entry_le_entrywise_sup_norm A

@[simp] theorem matrixEntryCLM_apply (i l : Fin d) (A : Mat d) :
    matrixEntryCLM i l A = A i l :=
  rfl

/-! ## Mean zero at the origin -/

/-- Transport of an integral of a real shell observable through the frozen
marginal scaling law: the law of `F(j_k)` is the law of
`F(3^{γk} j_0(3^{-k} ·))`. -/
theorem integral_shellObservable_eq (M : ABKModel d) (k : ℤ) (F : ShellField d → ℝ)
    (hF : Measurable F) :
    ∫ omega : ShellSeq d, F (omega k) ∂M.P.toMeasure =
      ∫ j : ShellField d, F (ShellField.triadicScale M.gamma k j)
        ∂(ShellField.zeroShellLaw M.P).toMeasure := by
  have hmeas : Measurable (fun omega : ShellSeq d => F (omega k)) :=
    hF.comp (measurable_pi_apply k)
  have hmeas' : Measurable (fun j : ShellField d =>
      F (ShellField.triadicScale M.gamma k j)) :=
    hF.comp (ShellField.measurable_triadicScale M.gamma k)
  calc ∫ omega : ShellSeq d, F (omega k) ∂M.P.toMeasure
      = ∫ y : ℝ, y ∂(Measure.map (fun omega : ShellSeq d => F (omega k))
          M.P.toMeasure) :=
        (integral_map hmeas.aemeasurable aestronglyMeasurable_id).symm
    _ = ∫ y : ℝ, y ∂(Measure.map (fun j : ShellField d =>
          F (ShellField.triadicScale M.gamma k j))
            (ShellField.zeroShellLaw M.P).toMeasure) := by
        rw [map_shellObservable_eq_zero_triadicScale M k F hF]
    _ = ∫ j : ShellField d, F (ShellField.triadicScale M.gamma k j)
          ∂(ShellField.zeroShellLaw M.P).toMeasure :=
        integral_map hmeas'.aemeasurable aestronglyMeasurable_id

/-- The frozen (J1) mean-zero assumption, read entrywise under the zero-shell
law. -/
theorem integral_zeroShell_entry_eq_zero (M : ABKModel d) (x : Vec d) (i l : Fin d) :
    ∫ j : ShellField d, j x i l ∂(ShellField.zeroShellLaw M.P).toMeasure = 0 := by
  have hmap : (ShellField.zeroShellLaw M.P).toMeasure =
      Measure.map (fun F : ShellSeq d => F 0) M.P.toMeasure := rfl
  rw [hmap, integral_map (ShellField.measurable_zeroShellMap (d := d)).aemeasurable
    (ShellField.measurable_eval_entry x i l).aestronglyMeasurable]
  have h : (∫ omega : ShellSeq d, matrixEntryCLM i l ((omega 0) x) ∂M.P.toMeasure) =
      matrixEntryCLM i l (∫ omega : ShellSeq d, (omega 0) x ∂M.P.toMeasure) :=
    ContinuousLinearMap.integral_comp_comm (matrixEntryCLM i l) (M.J1.integrable x)
  rw [M.J1.mean_zero x] at h
  simpa only [matrixEntryCLM_apply, Matrix.zero_apply] using h

/-- ABK26's "`j_k(0)` is mean zero", for every shell index and every matrix
entry.  This is the frozen (J1) mean-zero field transported to shell `k`
through the frozen marginal scaling law. -/
theorem integral_shell_origin_entry_eq_zero (M : ABKModel d) (k : ℤ) (i l : Fin d) :
    ∫ omega : ShellSeq d, (omega k) 0 i l ∂M.P.toMeasure = 0 := by
  rw [integral_shellObservable_eq M k (fun j : ShellField d => j 0 i l)
    (ShellField.measurable_eval_entry 0 i l)]
  have hpt : ∀ j : ShellField d, (ShellField.triadicScale M.gamma k j) 0 i l =
      Real.rpow 3 (M.gamma * (k : ℝ)) * (j 0 i l) := by
    intro j
    rw [ShellField.triadicScale_apply, smul_zero]
    rfl
  simp only [hpt]
  rw [MeasureTheory.integral_const_mul, integral_zeroShell_entry_eq_zero M 0 i l,
    mul_zero]

/-! ## The per-shell tail and independence at the origin -/

/-- The origin lies in every origin-centred triadic cube. -/
theorem zero_mem_openCubeSet_originCube (k : ℤ) :
    (0 : Vec d) ∈ openCubeSet (originCube d k) := by
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hpos : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) k
  refine ⟨?_, ?_⟩ <;> · show _ < _ ; simp only [Pi.zero_apply]; linarith

/-- ABK26's `e.jk.O` at the origin, entrywise: `|j_k(0)_{il}| ≤ O_{Γ₂}(3^{γk})`. -/
theorem isBigO_gammaSigma_shell_origin_entry (M : ABKModel d) (k : ℤ) (i l : Fin d) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => (omega k) 0 i l)
      ((3 : ℝ) ^ (M.gamma * (k : ℝ))) :=
  (isBigOWith_gammaSigma_localCubeControl_shell M k).of_le fun omega =>
    abs_entry_le_localCubeControl k (omega k) (zero_mem_openCubeSet_originCube k) i l

/-- The frozen shell independence, read on the scalar entries of the shell
values at the origin. -/
theorem iIndepFun_shell_origin_entry (M : ABKModel d) (i l : Fin d) :
    ProbabilityTheory.iIndepFun
      (fun (k : ℤ) (omega : ShellSeq d) => (omega k) 0 i l) M.P.toMeasure :=
  M.shellPrefix.independent.comp
    (fun _ : ℤ => fun j : ShellField d => j 0 i l)
    (fun _ => ShellField.measurable_eval_entry 0 i l)

/-! ## The entrywise concentration estimate -/

/-- ABK26's `e.k.ell.upscales`, entrywise: for `n < m` and every matrix entry,

`∑_{k = n+1}^m j_k(0)_{il} = O_{Γ₂}(C min{γ^{-1/2}, (m-n)^{1/2}} 3^{γm})`. -/
theorem isBigO_gammaSigma_originIncrement_entry (M : ABKModel d) {n m : ℤ}
    (hnm : n < m) (i l : Fin d) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => ∑ k ∈ Finset.Ioc n m, (omega k) 0 i l)
      (geometricConcentrationConst *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ))) :=
  isBigO_gammaSigma_two_sum_Ioc_geometric M.shellPrefix.gamma_pos
    M.shellPrefix.gamma_le_quarter hnm
    (iIndepFun_shell_origin_entry M i l)
    (fun k => (ShellField.measurable_eval_entry 0 i l).comp (measurable_pi_apply k))
    (fun k => isBigO_gammaSigma_shell_origin_entry M k i l)
    (fun k => integral_shell_origin_entry_eq_zero M k i l)

/-! ## Recombining the entries -/

/-- The exact Euclidean operator norm of a matrix is dominated by the sum of
the absolute values of its entries, indexed by pairs. -/
theorem matrixOperatorNorm_le_sum_univ_abs_entry (A : Mat d) :
    matrixOperatorNorm A ≤ ∑ p : Fin d × Fin d, |A p.1 p.2| := by
  have hsum : ∑ p : Fin d × Fin d, |A p.1 p.2| = ∑ i, ∑ l, |A i l| :=
    Fintype.sum_prod_type (fun p : Fin d × Fin d => |A p.1 p.2|)
  rw [hsum]
  exact (matrixOperatorNorm_le_matrixFrobeniusNorm A).trans
    (matrixFrobeniusNorm_le_sum_abs_entries A)

/-- ABK26's `e.k.ell.upscales`:

`|(k_m - k_n)(0)| ≤ O_{Γ₂}(C min{γ^{-1/2}, (m-n)^{1/2}} 3^{γm})`,

with `|·|` the exact Euclidean matrix operator norm and `k_m - k_n` the finite
shell increment `∑_{k = n+1}^m j_k`.  The dimensional constant is explicit:
the source's `C(d)` is chosen as `Γ-triangle-constant · d²` times the
universal constant `geometricConcentrationConst`, the extra `d²` coming from
recombining the `d²` scalar entries. -/
theorem isBigOWith_gammaSigma_originIncrement (M : ABKModel d) {n m : ℤ}
    (hnm : n < m) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        matrixOperatorNorm (finiteShellIncrement omega n m 0))
      (IndependentSums.gammaTriangleConst 2 * ((d : ℝ) ^ 2 *
        (geometricConcentrationConst *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ))))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hAmp : (0 : ℝ) < geometricConcentrationConst *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
    have hmin : 0 < min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) := by
      refine lt_min (Real.sqrt_pos.2 (inv_pos.2 M.shellPrefix.gamma_pos))
        (Real.sqrt_pos.2 ?_)
      have : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    exact mul_pos (mul_pos geometricConcentrationConst_pos hmin)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty := by
    refine ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
  have hentry : ∀ p : Fin d × Fin d,
      IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d =>
          |∑ k ∈ Finset.Ioc n m, (omega k) 0 p.1 p.2|)
        (geometricConcentrationConst *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
    intro p
    have h := isBigO_gammaSigma_originIncrement_entry M hnm p.1 p.2
    have habs : (fun omega : ShellSeq d =>
        |(fun omega : ShellSeq d => |∑ k ∈ Finset.Ioc n m, (omega k) 0 p.1 p.2|)
          omega|) =
        fun omega : ShellSeq d => |∑ k ∈ Finset.Ioc n m, (omega k) 0 p.1 p.2| := by
      funext omega
      exact abs_abs _
    show IndependentSums.IsBigOWith _ _ _ _
    rw [habs]
    exact h
  have hmeas : ∀ p : Fin d × Fin d, Measurable (fun omega : ShellSeq d =>
      |∑ k ∈ Finset.Ioc n m, (omega k) 0 p.1 p.2|) := by
    intro p
    have hsummeas : Measurable (fun omega : ShellSeq d =>
        ∑ k ∈ Finset.Ioc n m, (omega k) 0 p.1 p.2) :=
      Finset.measurable_sum (Finset.Ioc n m) fun k _ =>
        (ShellField.measurable_eval_entry 0 p.1 p.2).comp (measurable_pi_apply k)
    have habs : (fun omega : ShellSeq d =>
        |∑ k ∈ Finset.Ioc n m, (omega k) 0 p.1 p.2|) =
        fun omega : ShellSeq d => ‖∑ k ∈ Finset.Ioc n m, (omega k) 0 p.1 p.2‖ := by
      funext omega
      exact (Real.norm_eq_abs _).symm
    rw [habs]
    exact Measurable.norm hsummeas
  have htriangle := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (Finset.univ : Finset (Fin d × Fin d))
    (X := fun p omega => |∑ k ∈ Finset.Ioc n m, (omega k) 0 p.1 p.2|)
    (a := fun _ : Fin d × Fin d => geometricConcentrationConst *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)))
    (σ := 2) (by norm_num) hne (fun p _ => hAmp) (fun p _ => hentry p)
    (fun p _ => hmeas p)
  have hcard : ∑ _p : Fin d × Fin d, (geometricConcentrationConst *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ))) =
      (d : ℝ) ^ 2 * (geometricConcentrationConst *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin]
    push_cast
    ring
  rw [hcard] at htriangle
  refine htriangle.of_le fun omega => ?_
  refine (matrixOperatorNorm_le_sum_univ_abs_entry _).trans ?_
  refine le_trans (le_of_eq ?_) (le_abs_self _)
  exact Finset.sum_congr rfl fun p _ => by
    rw [finiteShellIncrement_apply_entry]

end

end Algsuperdiff.Section3.Provider.Stream
