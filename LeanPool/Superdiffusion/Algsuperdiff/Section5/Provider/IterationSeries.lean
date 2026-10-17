/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.DivergenceContraction
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.SeriesLimit

/-!
# IterationSeries

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The perturbation iteration as a sequence

One step of the perturbation iteration on the cube `y + □_n` is
`IterationStep.lean`: from an increment `w_j` with a continuous representative
of `1/2`-Hölder seminorm at most `K_j` it produces the Laplace solution `h_j`
forced by `w_j ∇ · k` and the next increment `w_{j+1}` solving the rough-field
problem with datum `∇ h_j`, together with the good-event bound on the seminorm
of `w_{j+1}`.

Iterating that step needs the supremum bound `‖w_j‖_{L^∞} ≤ 3^{n/2} [w_j]`,
which holds because each increment has zero trace on the cube, and needs the
seminorm bound of the output to be of the same shape as the input's, which is
where the contraction hypothesis enters: as soon as

```text
  2 C_reg σ_n^{-1} 3^n C (‖∇·k‖_{L^∞} + 3^{n/2} [∇·k]_{1/2}) ≤ ρ ,
```

the seminorms obey `K_{j+1} ≤ ρ K_j`, so the whole sequence exists with
`K_j = K_0 ρ^j`.  The recursion is carried by a state carrying the increment,
its representative, its seminorm bound and its zero-trace witness, so that the
step can be applied again.

## Main results

* `rpow_three_neg_half_eq_inv` — the power of three the normalization uses.
* `sup_le_of_zeroTrace` — the supremum of a zero-trace increment on the cube.
* `exists_iterationSequence` — the sequence of increments and Laplace solutions,
  with the geometric seminorm bound and the geometric supremum bound on the
  gradients of the Laplace solutions.

## References

* ABK26, the iteration scheme of the proof of the injection estimate of
  Section 5.1.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-! ## 1. Two elementary steps -/

private theorem exists_seq_of_step {alpha : Type*} (a0 : alpha) (R : alpha → alpha → Prop)
    (hstep : ∀ a, ∃ b, R a b) : ∃ f : ℕ → alpha, f 0 = a0 ∧ ∀ j, R (f j) (f (j + 1)) := by
  classical
  choose g hg using hstep
  exact ⟨fun j => Nat.rec a0 (fun _ a => g a) j, rfl, fun j => hg _⟩

/-- `3^{n/2} · 3^{n/2} = 3^n`. -/
private theorem rpow_three_half_mul_self (n : ℤ) :
    Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 ((n : ℝ) / 2) = Real.rpow 3 (n : ℝ) := by
  change (3 : ℝ) ^ ((n : ℝ) / 2) * (3 : ℝ) ^ ((n : ℝ) / 2) = (3 : ℝ) ^ (n : ℝ)
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- `3^{-n/2} = (3^{n/2})⁻¹`. -/
theorem rpow_three_neg_half_eq_inv (n : ℤ) :
    Real.rpow 3 (-(n : ℝ) / 2) = (Real.rpow 3 ((n : ℝ) / 2))⁻¹ := by
  change (3 : ℝ) ^ (-(n : ℝ) / 2) = ((3 : ℝ) ^ ((n : ℝ) / 2))⁻¹
  rw [show (-(n : ℝ) / 2) = -((n : ℝ) / 2) by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]

/-- **The supremum of a zero-trace increment on the cube, from its own Hölder
seminorm.** -/
theorem sup_le_of_zeroTrace {y : Vec d} {n : ℤ} (hd : 0 < d)
    {v : H1Function (cubeSetAt y n)} {vRep : Vec d → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hzero : ∃ z : H10Function (cubeSetAt y n), ∀ x, v.toFun x = z.toH1Function.toFun x)
    (hrep : IsCubeRepresentative y n v vRep)
    (hKb : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) K vRep) :
    ∀ x ∈ cubeSetAt y n, ‖vRep x‖ ≤ Real.rpow 3 ((n : ℝ) / 2) * K := by
  have hPnn : (0 : ℝ) ≤ Real.rpow 3 ((n : ℝ) / 2) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have h1 := supNormOn_le_rpow_mul_holderSeminormOn_of_zeroTrace hd hzero hrep
  have h2 : holderSeminormOn (cubeSetAt y n) (1 / 2) vRep ≤ ENNReal.ofReal K :=
    (holderSeminormOn_le_ofReal_iff hK0).2 hKb
  have h3 : supNormOn (cubeSetAt y n) vRep ≤
      ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2) * K) := by
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul hPnn]
    gcongr
  exact (supNormOn_le_ofReal_iff (by positivity)).1 h3

/-! ## 2. The state of the iteration -/

private structure IterState (y : Vec d) (n : ℤ) where
  w : H1Function (cubeSetAt y n)
  wRep : Vec d → ℝ
  K : ℝ
  hK0 : 0 ≤ K
  hrep : IsCubeRepresentative y n w wRep
  hKb : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) K wRep
  hzero : ∃ z : H10Function (cubeSetAt y n), ∀ x, w.toFun x = z.toH1Function.toFun x

/-! ## 3. The sequence produced by the step -/

/-- **The perturbation iteration, as a sequence of increments.**

On the good cube event, and under the contraction hypothesis, the step of
`IterationStep.lean` can be applied indefinitely: the `1/2`-Hölder seminorms of
the continuous representatives decay geometrically with ratio `ρ`, and so do the
supremum norms of the gradients of the intermediate Laplace solutions. -/
theorem exists_iterationSequence (hdim : 2 ≤ d) :
    ∃ CIter : ℝ, 0 < CIter ∧
      ∀ (M : ABKModel d) (Creg : ℝ), 0 ≤ Creg →
      ∀ (n : ℤ) (y : Vec d) (ep : ℝ) (omega : Cutoff.CutoffSample d),
        omega ∈ goodCubeEvent M Creg n y ep →
        ∀ k : Vec d → Mat d,
          (∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q) →
          (∀ x : Vec d, matTranspose (k x) = -k x) →
          ∀ Kk Sk : ℝ,
            HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kk (matFieldDiv k) →
            (∀ x ∈ cubeSetAt y n, ‖matFieldDiv k x‖ ≤ Sk) →
            ∀ (g : Vec d → Vec d) (w0 : H1Function (cubeSetAt y n)) (w0Rep : Vec d → ℝ)
              (K0 rho : ℝ), 0 ≤ K0 → 0 ≤ rho →
              IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField)
                y n w0 g →
              IsCubeRepresentative y n w0 w0Rep →
              HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) K0 w0Rep →
              2 * Creg * ((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow 3 (n : ℝ) * CIter *
                  (Sk + Real.rpow 3 ((n : ℝ) / 2) * Kk) ≤ rho →
              ∃ (w : ℕ → H1Function (cubeSetAt y n)) (wRep : ℕ → Vec d → ℝ)
                (lap : ℕ → H1Function (cubeSetAt y n)),
                w 0 = w0 ∧
                (∀ j, IsCubeRepresentative y n (w j) (wRep j)) ∧
                (∀ j, ∃ z : H10Function (cubeSetAt y n),
                  ∀ x, (w j).toFun x = z.toH1Function.toFun x) ∧
                (∀ j, HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (K0 * rho ^ j) (wRep j)) ∧
                (∀ j, IsDirichletSolutionAt (fun _ => (1 : ℝ) • (1 : Mat d)) y n (lap j)
                  fun x => -matVecMul (k x) ((w j).grad x)) ∧
                (∀ j, ∀ x ∈ cubeSetAt y n, ‖(lap j).grad x‖ ≤
                  CIter * Real.rpow 3 ((n : ℝ) / 2) * K0 *
                    (Sk + Real.rpow 3 ((n : ℝ) / 2) * Kk) * rho ^ j) ∧
                (∀ j, IsDirichletSolutionAt
                  ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n (w (j + 1))
                  (lap j).grad) := by
  classical
  obtain ⟨CIter, hCIter, hstep⟩ := exists_iterationStep_of_mem_goodCubeEvent hdim
  refine ⟨CIter, hCIter, ?_⟩
  intro M Creg hCreg n y ep omega homega k hkC1 hkskew Kk Sk hKk hSk g w0 w0Rep K0 rho hK0
    hrho0 hw0 hw0rep hw0K hQ
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hdim
  have hP : (0 : ℝ) < Real.rpow 3 ((n : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hS : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := Provider.Orlicz.sigmaBar_pos M n
  have hKk0 : (0 : ℝ) ≤ Kk := holderSeminormBoundOn_nonneg_cubeSetAt hd hKk
  have hSk0 : (0 : ℝ) ≤ Sk := le_trans (norm_nonneg _) (hSk y (mem_cubeSetAt_self y n))
  have hzero0 : ∃ z : H10Function (cubeSetAt y n),
      ∀ x, w0.toFun x = z.toH1Function.toFun x := by
    obtain ⟨z, hz, -⟩ := hw0.1
    exact ⟨z, hz⟩
  have hQ' : 2 * Creg * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
      (Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 ((n : ℝ) / 2)) * CIter *
      (Sk + Real.rpow 3 ((n : ℝ) / 2) * Kk) ≤ rho := by
    rwa [rpow_three_half_mul_self]
  set s0 : IterState y n := ⟨w0, w0Rep, K0, hK0, hw0rep, hw0K, hzero0⟩ with hs0def
  have hstepR : ∀ s : IterState y n, ∃ t : IterState y n,
      (∃ lap : H1Function (cubeSetAt y n),
        IsDirichletSolutionAt (fun _ => (1 : ℝ) • (1 : Mat d)) y n lap
            (fun x => -matVecMul (k x) (s.w.grad x)) ∧
          (∀ x ∈ cubeSetAt y n, ‖lap.grad x‖ ≤
            CIter * Real.rpow 3 ((n : ℝ) / 2) *
              (Sk + Real.rpow 3 ((n : ℝ) / 2) * Kk) * s.K) ∧
          IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n
            t.w lap.grad) ∧ t.K = rho * s.K := by
    intro s
    have hSw := sup_le_of_zeroTrace hd s.hK0 s.hzero s.hrep s.hKb
    obtain ⟨lap, w', w'Rep, hlapsol, hlapsup, hlapHol, hw'sol, hw'rep, hw'reg⟩ :=
      hstep M Creg n y ep omega homega k hkC1 hkskew s.w s.wRep s.K
        (Real.rpow 3 ((n : ℝ) / 2) * s.K) Kk Sk s.hrep s.hKb hSw hKk hSk
    have hinner : (0 : ℝ) ≤ s.K * Sk + Real.rpow 3 ((n : ℝ) / 2) * s.K * Kk :=
      add_nonneg (mul_nonneg s.hK0 hSk0) (mul_nonneg (mul_nonneg hP.le s.hK0) hKk0)
    have hHolNN : (0 : ℝ) ≤
        CIter * (s.K * Sk + Real.rpow 3 ((n : ℝ) / 2) * s.K * Kk) :=
      mul_nonneg hCIter.le hinner
    have hgradHol : holderSeminormOn (cubeSetAt y n) (1 / 2) lap.grad ≤
        ENNReal.ofReal (CIter * (s.K * Sk + Real.rpow 3 ((n : ℝ) / 2) * s.K * Kk)) :=
      (holderSeminormOn_le_ofReal_iff hHolNN).2 hlapHol
    -- the real arithmetic behind the contraction
    have hKnn : (0 : ℝ) ≤ (Annealed.sigmaBar M n : ℝ) *
        (Real.rpow 3 ((n : ℝ) / 2))⁻¹ * s.K :=
      mul_nonneg (mul_nonneg hS.le (inv_nonneg.2 hP.le)) s.hK0
    have hfactor : 2 * Creg * Real.rpow 3 ((n : ℝ) / 2) *
        (CIter * (s.K * Sk + Real.rpow 3 ((n : ℝ) / 2) * s.K * Kk)) =
        (2 * Creg * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
            (Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 ((n : ℝ) / 2)) * CIter *
            (Sk + Real.rpow 3 ((n : ℝ) / 2) * Kk)) *
          ((Annealed.sigmaBar M n : ℝ) * (Real.rpow 3 ((n : ℝ) / 2))⁻¹ * s.K) := by
      field_simp
    have harith : 2 * Creg * Real.rpow 3 ((n : ℝ) / 2) *
        (CIter * (s.K * Sk + Real.rpow 3 ((n : ℝ) / 2) * s.K * Kk)) ≤
        (Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2) * (rho * s.K) := by
      have hmul := mul_le_mul_of_nonneg_right hQ' hKnn
      rw [← hfactor] at hmul
      refine hmul.trans (le_of_eq ?_)
      rw [rpow_three_neg_half_eq_inv]
      ring
    -- transport the arithmetic through `ENNReal`
    have hchain : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
        holderSeminormOn (cubeSetAt y n) (1 / 2) w'Rep ≤
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
          ENNReal.ofReal (rho * s.K) := by
      refine hw'reg.trans ?_
      have h1 : ENNReal.ofReal (2 * Creg) * ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) *
          holderSeminormOn (cubeSetAt y n) (1 / 2) lap.grad ≤
          ENNReal.ofReal (2 * Creg) * ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) *
            ENNReal.ofReal (CIter * (s.K * Sk + Real.rpow 3 ((n : ℝ) / 2) * s.K * Kk)) := by
        gcongr
      refine h1.trans ?_
      have hfold : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
          ENNReal.ofReal (rho * s.K) =
          ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2) *
            (rho * s.K)) :=
        (ENNReal.ofReal_mul (le_of_lt (mul_pos hS
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (-(n : ℝ) / 2))))).symm
      rw [← ENNReal.ofReal_mul (by linarith only [hCreg] : (0 : ℝ) ≤ 2 * Creg),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Creg * Real.rpow 3 ((n : ℝ) / 2)),
        hfold]
      exact ENNReal.ofReal_le_ofReal harith
    have hcancel : holderSeminormOn (cubeSetAt y n) (1 / 2) w'Rep ≤
        ENNReal.ofReal (rho * s.K) := by
      have hne : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact mul_pos hS (Real.rpow_pos_of_pos (by norm_num) _)
      exact (ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top).1 hchain
    have hzero' : ∃ z : H10Function (cubeSetAt y n),
        ∀ x, w'.toFun x = z.toH1Function.toFun x := by
      obtain ⟨z, hz, -⟩ := hw'sol.1
      exact ⟨z, hz⟩
    refine ⟨⟨w', w'Rep, rho * s.K, mul_nonneg hrho0 s.hK0, hw'rep,
      (holderSeminormOn_le_ofReal_iff (mul_nonneg hrho0 s.hK0)).1 hcancel, hzero'⟩, ⟨lap, ?_, ?_,
        ?_⟩, rfl⟩
    · exact hlapsol
    · intro x hx
      refine (hlapsup x hx).trans (le_of_eq ?_)
      ring
    · exact hw'sol
  obtain ⟨f, hf0, hfstep⟩ := exists_seq_of_step s0 _ hstepR
  choose lap hlapsol hlapsup hlapnext using fun j => (hfstep j).1
  have hKeq : ∀ j, (f j).K = K0 * rho ^ j := by
    intro j
    induction j with
    | zero => rw [hf0, hs0def, pow_zero, mul_one]
    | succ j ih =>
        have h := (hfstep j).2
        rw [h, ih]
        ring
  refine ⟨fun j => (f j).w, fun j => (f j).wRep, lap, ?_, fun j => (f j).hrep,
    fun j => (f j).hzero, ?_, hlapsol, ?_, hlapnext⟩
  · change (f 0).w = w0
    rw [hf0, hs0def]
  · intro j
    have h := (f j).hKb
    rwa [hKeq j] at h
  · intro j x hx
    refine (hlapsup j x hx).trans (le_of_eq ?_)
    rw [hKeq j]
    ring

end

end Algsuperdiff.Section5.Provider
