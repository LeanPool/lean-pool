/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityBoundedPairing
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityComponentConvergence
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityFiniteSumIntegral
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityQuadraticIntegral

/-!
# Passage of the regularized transport term to the limit

This is the nonlinear term passage in the solenoidal weak equation of
`prop:leray-hopf-limit`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal



namespace CKN.Leray

/-- Separate convergence of the linear, transport, and viscous terms passes a
regularized solenoidal momentum identity to the limit. -/
theorem lerayHopfLimit_momentumIdentity_of_termLimits
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (Aseq : ℕ → α → ℝ) (A : α → ℝ)
    (Bseq : ℕ → α → ℝ) (B : α → ℝ)
    (Cseq : ℕ → α → ℝ) (C : α → ℝ)
    (hAseq : ∀ n, Integrable (Aseq n) μ) (hA : Integrable A μ)
    (hBseq : ∀ n, Integrable (Bseq n) μ) (hB : Integrable B μ)
    (hCseq : ∀ n, Integrable (Cseq n) μ) (hC : Integrable C μ)
    (hAconv : Tendsto (fun n => ∫ x, Aseq n x ∂μ) atTop
      (nhds (∫ x, A x ∂μ)))
    (hBconv : Tendsto (fun n => ∫ x, Bseq n x ∂μ) atTop
      (nhds (∫ x, B x ∂μ)))
    (hCconv : Tendsto (fun n => ∫ x, Cseq n x ∂μ) atTop
      (nhds (∫ x, C x ∂μ)))
    (hreg : ∀ n, ∫ x, -Aseq n x - Bseq n x + Cseq n x ∂μ = 0) :
    ∫ x, -A x - B x + C x ∂μ = 0 := by
  have hABseq (n : ℕ) : Integrable (fun x => -Aseq n x - Bseq n x) μ :=
    (hAseq n).neg.sub (hBseq n)
  have hAB : Integrable (fun x => -A x - B x) μ := hA.neg.sub hB
  have hsplitN (n : ℕ) :
      (∫ x, -Aseq n x - Bseq n x + Cseq n x ∂μ) =
        -(∫ x, Aseq n x ∂μ) - (∫ x, Bseq n x ∂μ) +
          (∫ x, Cseq n x ∂μ) := by
    have hsubN :
        (∫ x, -Aseq n x - Bseq n x ∂μ) =
          -(∫ x, Aseq n x ∂μ) - (∫ x, Bseq n x ∂μ) := by
      calc
        (∫ x, -Aseq n x - Bseq n x ∂μ) =
            (∫ x, -Aseq n x ∂μ) - (∫ x, Bseq n x ∂μ) :=
          integral_sub ((hAseq n).neg) (hBseq n)
        _ = -(∫ x, Aseq n x ∂μ) - (∫ x, Bseq n x ∂μ) := by
          rw [integral_neg]
    calc
      (∫ x, -Aseq n x - Bseq n x + Cseq n x ∂μ) =
          (∫ x, -Aseq n x - Bseq n x ∂μ) + (∫ x, Cseq n x ∂μ) :=
        integral_add (hABseq n) (hCseq n)
      _ = -(∫ x, Aseq n x ∂μ) - (∫ x, Bseq n x ∂μ) +
          (∫ x, Cseq n x ∂μ) := by rw [hsubN]
  have hsplit :
      (∫ x, -A x - B x + C x ∂μ) =
        -(∫ x, A x ∂μ) - (∫ x, B x ∂μ) + (∫ x, C x ∂μ) := by
    have hsub :
        (∫ x, -A x - B x ∂μ) =
          -(∫ x, A x ∂μ) - (∫ x, B x ∂μ) := by
      calc
        (∫ x, -A x - B x ∂μ) = (∫ x, -A x ∂μ) - (∫ x, B x ∂μ) :=
          integral_sub hA.neg hB
        _ = -(∫ x, A x ∂μ) - (∫ x, B x ∂μ) := by rw [integral_neg]
    calc
      (∫ x, -A x - B x + C x ∂μ) =
          (∫ x, -A x - B x ∂μ) + (∫ x, C x ∂μ) :=
        integral_add hAB hC
      _ = -(∫ x, A x ∂μ) - (∫ x, B x ∂μ) +
          (∫ x, C x ∂μ) := by rw [hsub]
  have hsum : Tendsto
      (fun n => -(∫ x, Aseq n x ∂μ) - (∫ x, Bseq n x ∂μ) +
        (∫ x, Cseq n x ∂μ)) atTop
      (nhds (-(∫ x, A x ∂μ) - (∫ x, B x ∂μ) + (∫ x, C x ∂μ))) :=
    hAconv.neg.sub hBconv |>.add hCconv
  have hseqZero :
      (fun n => -(∫ x, Aseq n x ∂μ) - (∫ x, Bseq n x ∂μ) +
        (∫ x, Cseq n x ∂μ)) = fun _ => 0 := by
    funext n
    rw [← hsplitN n, hreg n]
  have hzero : Tendsto
      (fun n => -(∫ x, Aseq n x ∂μ) - (∫ x, Bseq n x ∂μ) +
        (∫ x, Cseq n x ∂μ)) atTop (nhds 0) := by
    rw [hseqZero]
    exact tendsto_const_nhds
  have hlimitZero := tendsto_nhds_unique hsum hzero
  rw [hsplit]
  exact hlimitZero

/-- Strong local `L³` convergence passes the linear weak-momentum term to the
limit against a bounded test derivative. -/
theorem lerayHopfLimit_linearTerm_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (U : ℕ → α → Fin 3 → ℝ) (u : α → Fin 3 → ℝ)
    (hU : ∀ n, MemLp (U n) 3 μ)
    (hUconv : Tendsto (fun n => eLpNorm (U n - u) 3 μ) atTop (nhds 0))
    (φ : Fin 3 → α → ℝ) (hφ : ∀ i, MemLp (φ i) ∞ μ) :
    Tendsto
      (fun n => ∫ x, ∑ i : Fin 3, U n x i * φ i x ∂μ) atTop
      (nhds (∫ x, ∑ i : Fin 3, u x i * φ i x ∂μ)) := by
  have hu : MemLp u 3 μ :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) hU u hUconv
  have hUcomponent (n : ℕ) (i : Fin 3) : MemLp (fun x => U n x i) 3 μ :=
    (memLp_pi_iff.mp (hU n)) i
  have hucomponent (i : Fin 3) : MemLp (fun x => u x i) 3 μ :=
    (memLp_pi_iff.mp hu) i
  have htermInt (n : ℕ) (i : Fin 3) :
      Integrable (fun x => U n x i * φ i x) μ :=
    stability_integrable_mul_bounded_test μ (by norm_num) (hUcomponent n i) (hφ i)
  have htermIntLimit (i : Fin 3) :
      Integrable (fun x => u x i * φ i x) μ :=
    stability_integrable_mul_bounded_test μ (by norm_num) (hucomponent i) (hφ i)
  have htermConv (i : Fin 3) : Tendsto
      (fun n => ∫ x, U n x i * φ i x ∂μ) atTop
      (nhds (∫ x, u x i * φ i x ∂μ)) := by
    have hcomponent := stability_tendsto_eLpNorm_component_three μ U u hU hUconv i
    have h := stability_tendsto_integral_mul_test_of_Lthree μ
      (fun n x => U n x i) (fun x => u x i) (φ i)
      (fun n => hUcomponent n i) (hφ i) hcomponent
    have heqFn (n : ℕ) :
        (∫ x, φ i x • U n x i ∂μ) = ∫ x, U n x i * φ i x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [smul_eq_mul, mul_comm]
    have heqG :
        (∫ x, φ i x • u x i ∂μ) = ∫ x, u x i * φ i x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [smul_eq_mul, mul_comm]
    simpa only [heqFn, heqG] using h
  simpa only [Fin.sum_univ_three] using
    (stability_tendsto_integral_finsetSum μ Finset.univ
      (fun n i x => U n x i * φ i x)
      (fun i x => u x i * φ i x)
      (fun n i _ => htermInt n i)
      (fun i _ => htermIntLimit i)
      (fun i _ => htermConv i))

/-- Weak local `L²` convergence of the velocity gradients passes their pairing
with a test gradient to the limit. -/
theorem lerayHopfLimit_weakGradientTerm_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (D : ℕ → α → Fin 3 → Fin 3 → ℝ) (d : α → Fin 3 → Fin 3 → ℝ)
    (hD : ∀ n i j, MemLp (fun x => D n x i j) 2 μ)
    (hd : ∀ i j, MemLp (fun x => d x i j) 2 μ)
    (hweak : ∀ i j (w : α → ℝ), MemLp w 2 μ →
      Tendsto (fun n => ∫ x, D n x i j * w x ∂μ) atTop
        (nhds (∫ x, d x i j * w x ∂μ)))
    (φ : Fin 3 → Fin 3 → α → ℝ)
    (hφ : ∀ i j, MemLp (φ i j) 2 μ) :
    Tendsto
      (fun n => ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
        D n x i j * φ i j x ∂μ) atTop
      (nhds (∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
        d x i j * φ i j x ∂μ)) := by
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ENNReal.HolderConjugate.instTwoTwo
  have htermInt (n : ℕ) (i j : Fin 3) :
      Integrable (fun x => D n x i j * φ i j x) μ := by
    have h : MemLp (fun x => D n x i j * φ i j x) (1 : ℝ≥0∞) μ :=
      (hD n i j).mul (hφ i j)
    exact memLp_one_iff_integrable.mp h
  have htermIntLimit (i j : Fin 3) :
      Integrable (fun x => d x i j * φ i j x) μ := by
    have h : MemLp (fun x => d x i j * φ i j x) (1 : ℝ≥0∞) μ :=
      (hd i j).mul (hφ i j)
    exact memLp_one_iff_integrable.mp h
  have htermConv (i j : Fin 3) : Tendsto
      (fun n => ∫ x, D n x i j * φ i j x ∂μ) atTop
      (nhds (∫ x, d x i j * φ i j x ∂μ)) := hweak i j (φ i j) (hφ i j)
  have hsumJ (n : ℕ) (i : Fin 3) : Integrable
      (fun x => ∑ j : Fin 3, D n x i j * φ i j x) μ := by
    exact integrable_finsetSum Finset.univ (fun j _ => htermInt n i j)
  have hsumJLimit (i : Fin 3) : Integrable
      (fun x => ∑ j : Fin 3, d x i j * φ i j x) μ := by
    exact integrable_finsetSum Finset.univ (fun j _ => htermIntLimit i j)
  have hsumJConv (i : Fin 3) : Tendsto
      (fun n => ∫ x, ∑ j : Fin 3, D n x i j * φ i j x ∂μ) atTop
      (nhds (∫ x, ∑ j : Fin 3, d x i j * φ i j x ∂μ)) := by
    simpa only [Fin.sum_univ_three] using
      (stability_tendsto_integral_finsetSum μ Finset.univ
        (fun n j x => D n x i j * φ i j x)
        (fun j x => d x i j * φ i j x)
        (fun n j _ => htermInt n i j)
        (fun j _ => htermIntLimit i j)
        (fun j _ => htermConv i j))
  have hsumI (n : ℕ) : Integrable
      (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
        D n x i j * φ i j x) μ := by
    exact integrable_finsetSum Finset.univ (fun i _ => hsumJ n i)
  have hsumILimit : Integrable
      (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
        d x i j * φ i j x) μ := by
    exact integrable_finsetSum Finset.univ (fun i _ => hsumJLimit i)
  simpa only [Fin.sum_univ_three] using
    (stability_tendsto_integral_finsetSum μ Finset.univ
      (fun n i x => ∑ j : Fin 3, D n x i j * φ i j x)
      (fun i x => ∑ j : Fin 3, d x i j * φ i j x)
      (fun n i _ => hsumJ n i)
      (fun i _ => hsumJLimit i)
      (fun i _ => hsumJConv i))

/-- Strong local `L³` convergence of the solution and its mollified transport
field passes the transport term to the quadratic limit. -/
theorem lerayHopfLimit_advectiveTerm_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (U J : ℕ → α → Fin 3 → ℝ) (u : α → Fin 3 → ℝ)
    (hU : ∀ n, MemLp (U n) 3 μ) (hJ : ∀ n, MemLp (J n) 3 μ)
    (hu : MemLp u 3 μ)
    (hUconv : Tendsto (fun n => eLpNorm (U n - u) 3 μ) atTop (nhds 0))
    (hJconv : Tendsto (fun n => eLpNorm (J n - u) 3 μ) atTop (nhds 0))
    (φ : Fin 3 → Fin 3 → α → ℝ)
    (hφ : ∀ i j, MemLp (φ i j) ∞ μ) :
    Tendsto
      (fun n => ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
        U n x i * J n x j * φ i j x ∂μ) atTop
      (nhds (∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
        u x i * u x j * φ i j x ∂μ)) := by
  let : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2 : ℝ≥0∞) := by
    have hreal : Real.HolderTriple 3 3 (3 / 2) := by
      exact ⟨by norm_num, by norm_num, by norm_num⟩
    simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using
      hreal.ennrealOfReal
  have hOne : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
    rw [← CKN.ofReal_threeHalves]
    simpa using ENNReal.ofReal_le_ofReal (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have hUcomponent (n : ℕ) (i : Fin 3) : MemLp (fun x => U n x i) 3 μ :=
    (memLp_pi_iff.mp (hU n)) i
  have hJcomponent (n : ℕ) (i : Fin 3) : MemLp (fun x => J n x i) 3 μ :=
    (memLp_pi_iff.mp (hJ n)) i
  have hucomponent (i : Fin 3) : MemLp (fun x => u x i) 3 μ :=
    (memLp_pi_iff.mp hu) i
  have hUcomponentConv (i : Fin 3) :=
    stability_tendsto_eLpNorm_component_three μ U u hU hUconv i
  have hJcomponentConv (j : Fin 3) :=
    stability_tendsto_eLpNorm_component_three μ J u hJ hJconv j
  have hQn (n : ℕ) (i j : Fin 3) :
      MemLp (fun x => U n x i * J n x j) (3 / 2 : ℝ≥0∞) μ := by
    have h : MemLp (fun x => U n x i * J n x j)
        (3 / 2 : ℝ≥0∞) μ :=
      (hUcomponent n i).mul (hJcomponent n j)
    exact h
  have hQ (i j : Fin 3) :
      MemLp (fun x => u x i * u x j) (3 / 2 : ℝ≥0∞) μ := by
    have h : MemLp (fun x => u x i * u x j) (3 / 2 : ℝ≥0∞) μ :=
      (hucomponent i).mul (hucomponent j)
    exact h
  have htermInt (n : ℕ) (i j : Fin 3) :
      Integrable (fun x => U n x i * J n x j * φ i j x) μ :=
    stability_integrable_mul_bounded_test μ hOne (hQn n i j) (hφ i j)
  have htermIntLimit (i j : Fin 3) :
      Integrable (fun x => u x i * u x j * φ i j x) μ :=
    stability_integrable_mul_bounded_test μ hOne (hQ i j) (hφ i j)
  have htermConv (i j : Fin 3) : Tendsto
      (fun n => ∫ x, U n x i * J n x j * φ i j x ∂μ) atTop
      (nhds (∫ x, u x i * u x j * φ i j x ∂μ)) :=
    stability_tendsto_integral_quadratic_test μ
      (fun n x => U n x i) (fun n x => J n x j)
      (fun x => u x i) (fun x => u x j) (φ i j)
      (fun n => hUcomponent n i) (fun n => hJcomponent n j)
      (hucomponent i) (hucomponent j) (hφ i j)
      (hUcomponentConv i) (hJcomponentConv j)
  have hsumJ (n : ℕ) (i : Fin 3) : Integrable
      (fun x => ∑ j : Fin 3, U n x i * J n x j * φ i j x) μ := by
    exact integrable_finsetSum Finset.univ (fun j _ => htermInt n i j)
  have hsumJLimit (i : Fin 3) : Integrable
      (fun x => ∑ j : Fin 3, u x i * u x j * φ i j x) μ := by
    exact integrable_finsetSum Finset.univ (fun j _ => htermIntLimit i j)
  have hsumJConv (i : Fin 3) : Tendsto
      (fun n => ∫ x, ∑ j : Fin 3, U n x i * J n x j * φ i j x ∂μ) atTop
      (nhds (∫ x, ∑ j : Fin 3, u x i * u x j * φ i j x ∂μ)) := by
    simpa only [Fin.sum_univ_three] using
      (stability_tendsto_integral_finsetSum μ Finset.univ
        (fun n j x => U n x i * J n x j * φ i j x)
        (fun j x => u x i * u x j * φ i j x)
        (fun n j _ => htermInt n i j)
        (fun j _ => htermIntLimit i j)
        (fun j _ => htermConv i j))
  have hsumI (n : ℕ) : Integrable
      (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
        U n x i * J n x j * φ i j x) μ := by
    exact integrable_finsetSum Finset.univ (fun i _ => hsumJ n i)
  have hsumILimit : Integrable
      (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
        u x i * u x j * φ i j x) μ := by
    exact integrable_finsetSum Finset.univ (fun i _ => hsumJLimit i)
  simpa only [Fin.sum_univ_three] using
    (stability_tendsto_integral_finsetSum μ Finset.univ
      (fun n i x => ∑ j : Fin 3, U n x i * J n x j * φ i j x)
      (fun i x => ∑ j : Fin 3, u x i * u x j * φ i j x)
      (fun n i _ => hsumJ n i)
      (fun i _ => hsumJLimit i)
      (fun i _ => hsumJConv i))

/-- The regularized solenoidal momentum identities pass to the limit under the
strong velocity and weak gradient convergences in `prop:leray-limit`. -/
theorem lerayHopfLimit_weakEquation_of_regularized
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (U J : ℕ → α → Fin 3 → ℝ) (u : α → Fin 3 → ℝ)
    (D : ℕ → α → Fin 3 → Fin 3 → ℝ)
    (d : α → Fin 3 → Fin 3 → ℝ)
    (hU : ∀ n, MemLp (U n) 3 μ) (hJ : ∀ n, MemLp (J n) 3 μ)
    (hu : MemLp u 3 μ)
    (hUconv : Tendsto (fun n => eLpNorm (U n - u) 3 μ) atTop (nhds 0))
    (hJconv : Tendsto (fun n => eLpNorm (J n - u) 3 μ) atTop (nhds 0))
    (hD : ∀ n i j, MemLp (fun x => D n x i j) 2 μ)
    (hd : ∀ i j, MemLp (fun x => d x i j) 2 μ)
    (hweakD : ∀ i j (w : α → ℝ), MemLp w 2 μ →
      Tendsto (fun n => ∫ x, D n x i j * w x ∂μ) atTop
        (nhds (∫ x, d x i j * w x ∂μ)))
    (dt : Fin 3 → α → ℝ) (hdt : ∀ i, MemLp (dt i) ∞ μ)
    (φ : Fin 3 → Fin 3 → α → ℝ)
    (hφtop : ∀ i j, MemLp (φ i j) ∞ μ)
    (hφ2 : ∀ i j, MemLp (φ i j) 2 μ)
    (hAseq : ∀ n, Integrable
      (fun x => ∑ i : Fin 3, U n x i * dt i x) μ)
    (hA : Integrable (fun x => ∑ i : Fin 3, u x i * dt i x) μ)
    (hBseq : ∀ n, Integrable
      (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
        U n x i * J n x j * φ i j x) μ)
    (hB : Integrable (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      u x i * u x j * φ i j x) μ)
    (hCseq : ∀ n, Integrable
      (fun x => ∑ i : Fin 3, ∑ j : Fin 3, D n x i j * φ i j x) μ)
    (hC : Integrable (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      d x i j * φ i j x) μ)
    (hreg : ∀ n, ∫ x,
      -(∑ i : Fin 3, U n x i * dt i x)
        - (∑ i : Fin 3, ∑ j : Fin 3,
            U n x i * J n x j * φ i j x)
        + (∑ i : Fin 3, ∑ j : Fin 3,
            D n x i j * φ i j x) ∂μ = 0) :
    ∫ x,
      -(∑ i : Fin 3, u x i * dt i x)
        - (∑ i : Fin 3, ∑ j : Fin 3,
            u x i * u x j * φ i j x)
        + (∑ i : Fin 3, ∑ j : Fin 3,
            d x i j * φ i j x) ∂μ = 0 := by
  have hAconv := lerayHopfLimit_linearTerm_tendsto μ U u hU hUconv dt hdt
  have hBconv := lerayHopfLimit_advectiveTerm_tendsto μ U J u hU hJ hu
    hUconv hJconv φ hφtop
  have hCconv := lerayHopfLimit_weakGradientTerm_tendsto μ D d hD hd
    hweakD φ hφ2
  exact lerayHopfLimit_momentumIdentity_of_termLimits μ
    (fun n x => ∑ i : Fin 3, U n x i * dt i x)
    (fun x => ∑ i : Fin 3, u x i * dt i x)
    (fun n x => ∑ i : Fin 3, ∑ j : Fin 3,
      U n x i * J n x j * φ i j x)
    (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      u x i * u x j * φ i j x)
    (fun n x => ∑ i : Fin 3, ∑ j : Fin 3, D n x i j * φ i j x)
    (fun x => ∑ i : Fin 3, ∑ j : Fin 3, d x i j * φ i j x)
    hAseq hA hBseq hB hCseq hC hAconv hBconv hCconv hreg

end CKN.Leray
