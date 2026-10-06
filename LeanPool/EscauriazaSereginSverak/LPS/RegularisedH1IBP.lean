/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingHeatPairing
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingOrderedProduct
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSolenoidalWords
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSobolevEmbedding

/-!
# Integration by parts for the regularized `H¹` energy

Whole-space integration by parts for smooth fields with square-integrable
derivatives, used to compare `‖∇U‖²`, `∫ U Δ U` and `‖∇²U‖²` in the
differentiated energy identity (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- Whole-space pairing of a smooth field with the Laplacian of another moves both derivatives: `∫ f Δg = -∑ⱼ ∫ ∂ⱼf ∂ⱼg` (`prop:lps-local-strong`). -/
theorem lps_pairing_laplacian
    {f g : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hf0 : MemLp f 2 volume) (hf1 : ∀ j, MemLp (spatialDeriv f j) 2 volume)
    (hg1 : ∀ j, MemLp (spatialDeriv g j) 2 volume)
    (hg2 : ∀ j, MemLp (spatialDeriv (spatialDeriv g j) j) 2 volume) :
    (∫ x, f x * spatialLaplacian g x) =
      -∑ j : Fin 3, ∫ x, spatialDeriv f j x * spatialDeriv g j x := by
  have hint (j : Fin 3) :
      Integrable (fun x => f x * spatialDeriv (spatialDeriv g j) j x) volume :=
    hf0.integrable_mul (hg2 j)
  calc (∫ x, f x * spatialLaplacian g x)
      = ∫ x, ∑ j : Fin 3, f x * spatialDeriv (spatialDeriv g j) j x := by
        congr 1; funext x; simp only [spatialLaplacian, Finset.mul_sum]
    _ = ∑ j : Fin 3, ∫ x, f x * spatialDeriv (spatialDeriv g j) j x :=
        integral_finsetSum _ fun j _ => hint j
    _ = ∑ j : Fin 3, -∫ x, spatialDeriv f j x * spatialDeriv g j x := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact lps_divergence_pairing_direction hf (contDiff_spatialDeriv_smooth hg j) j
          hf0 (hf1 j) (hg1 j) (hg2 j)
    _ = -∑ j : Fin 3, ∫ x, spatialDeriv f j x * spatialDeriv g j x := by
        rw [Finset.sum_neg_distrib]


/-- For a smooth field with square-integrable derivatives through order three, `‖Δg‖₂² = ‖∇²g‖₂²` (`prop:lps-local-strong`). -/
theorem lps_laplacian_sq_eq_hessian_sq
    {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hL2 : ∀ α : List (Fin 3), α.length ≤ 3 → MemLp (wordDeriv α g) 2 volume) :
    (∫ x, spatialLaplacian g x ^ 2) =
      ∑ j : Fin 3, ∑ k : Fin 3, ∫ x, spatialDeriv (spatialDeriv g j) k x ^ 2 := by
  have hsm (α : List (Fin 3)) : ContDiff ℝ (⊤ : ℕ∞) (wordDeriv α g) := contDiff_wordDeriv hg α
  have hjj (j : Fin 3) : MemLp (spatialDeriv (spatialDeriv g j) j) 2 volume := hL2 [j, j] (by simp)
  have hpair (j k : Fin 3) :
      (∫ x, spatialDeriv (spatialDeriv g j) j x * spatialDeriv (spatialDeriv g k) k x) =
        ∫ x, spatialDeriv (spatialDeriv g j) k x ^ 2 := by
    -- IBP in k
    have hA : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (spatialDeriv g j) j) := by
      simpa [wordDeriv] using hsm [j, j]
    have hF : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g k) := by simpa [wordDeriv] using hsm [k]
    have step1 := lps_divergence_pairing_direction hA hF k
      (hL2 [j, j] (by simp)) (hL2 [j, j, k] (by simp)) (hL2 [k] (by simp)) (hL2 [k, k] (by simp))
    -- commute
    have hcomm : spatialDeriv (spatialDeriv (spatialDeriv g j) j) k =
        spatialDeriv (spatialDeriv (spatialDeriv g j) k) j := by
      funext x
      exact (vorticityDivCurlSmooth_deriv_comm (by simpa [wordDeriv] using hsm [j]) j k x).symm
    have hB : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (spatialDeriv g j) k) := by
      simpa [wordDeriv] using hsm [j, k]
    have step2 := lps_divergence_pairing_direction hB hF j
      (hL2 [j, k] (by simp)) (hL2 [j, k, j] (by simp)) (hL2 [k] (by simp)) (hL2 [k, j] (by simp))
    have hcomm2 : spatialDeriv (spatialDeriv g k) j = spatialDeriv (spatialDeriv g j) k := by
      funext x
      exact (vorticityDivCurlSmooth_deriv_comm hg k j x).symm
    have step2' : ∫ x, spatialDeriv (spatialDeriv g j) k x * spatialDeriv (spatialDeriv g k) j x =
        ∫ x, spatialDeriv (spatialDeriv g j) k x ^ 2 := by
      rw [hcomm2]; simp only [sq]
    calc (∫ x, spatialDeriv (spatialDeriv g j) j x * spatialDeriv (spatialDeriv g k) k x)
        = -∫ x, spatialDeriv (spatialDeriv (spatialDeriv g j) j) k x * spatialDeriv g k x := step1
      _ = -∫ x, spatialDeriv (spatialDeriv (spatialDeriv g j) k) j x * spatialDeriv g k x := by
          rw [hcomm]
      _ = ∫ x, spatialDeriv (spatialDeriv g j) k x * spatialDeriv (spatialDeriv g k) j x := by
          exact step2.symm
      _ = _ := step2'
  calc (∫ x, spatialLaplacian g x ^ 2)
      = ∫ x, ∑ j : Fin 3, ∑ k : Fin 3,
          spatialDeriv (spatialDeriv g j) j x * spatialDeriv (spatialDeriv g k) k x := by
        congr 1; funext x
        simp only [spatialLaplacian, sq, Finset.sum_mul_sum]
    _ = ∑ j : Fin 3, ∑ k : Fin 3, ∫ x,
          spatialDeriv (spatialDeriv g j) j x * spatialDeriv (spatialDeriv g k) k x := by
        have hint1 (j : Fin 3) : Integrable (fun x => ∑ k : Fin 3,
            spatialDeriv (spatialDeriv g j) j x * spatialDeriv (spatialDeriv g k) k x) volume :=
          integrable_finsetSum _ fun k _ => (hjj j).integrable_mul (hjj k)
        rw [integral_finsetSum Finset.univ (fun j _ => hint1 j)]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact integral_finsetSum _ fun k _ => (hjj j).integrable_mul (hjj k)
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hpair j k


/-- For smooth fields with square-integrable derivatives through order two, the change of the
squared gradient norm is the pairing of the increment against minus the Laplacian of the sum
(`prop:lps-local-strong`). -/
theorem lps_gradient_energy_difference
    {f g : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hf0 : MemLp f 2 volume) (hf1 : ∀ j, MemLp (spatialDeriv f j) 2 volume)
    (hf2 : ∀ j, MemLp (spatialDeriv (spatialDeriv f j) j) 2 volume)
    (hg0 : MemLp g 2 volume) (hg1 : ∀ j, MemLp (spatialDeriv g j) 2 volume)
    (hg2 : ∀ j, MemLp (spatialDeriv (spatialDeriv g j) j) 2 volume) :
    (∫ x, (g x - f x) * (-(spatialLaplacian f x + spatialLaplacian g x))) =
      (∑ j : Fin 3, ∫ x, spatialDeriv g j x ^ 2) -
        ∑ j : Fin 3, ∫ x, spatialDeriv f j x ^ 2 := by
  have hLf : MemLp (spatialLaplacian f) 2 volume := by
    unfold spatialLaplacian
    exact memLp_finsetSum _ fun j _ => hf2 j
  have hLg : MemLp (spatialLaplacian g) 2 volume := by
    unfold spatialLaplacian
    exact memLp_finsetSum _ fun j _ => hg2 j
  have e1 := lps_pairing_laplacian hf hf hf0 hf1 hf1 hf2
  have e2 := lps_pairing_laplacian hg hg hg0 hg1 hg1 hg2
  have e3 := lps_pairing_laplacian hf hg hf0 hf1 hg1 hg2
  have e4 := lps_pairing_laplacian hg hf hg0 hg1 hf1 hf2
  have i_fLf : Integrable (fun x => f x * spatialLaplacian f x) volume := hf0.integrable_mul hLf
  have i_fLg : Integrable (fun x => f x * spatialLaplacian g x) volume := hf0.integrable_mul hLg
  have i_gLf : Integrable (fun x => g x * spatialLaplacian f x) volume := hg0.integrable_mul hLf
  have i_gLg : Integrable (fun x => g x * spatialLaplacian g x) volume := hg0.integrable_mul hLg
  have hexp : (fun x => (g x - f x) * (-(spatialLaplacian f x + spatialLaplacian g x))) =
      fun x => (-(g x * spatialLaplacian f x) - g x * spatialLaplacian g x) +
        (f x * spatialLaplacian f x + f x * spatialLaplacian g x) := by
    funext x; ring
  have h1 : Integrable (fun x => -(g x * spatialLaplacian f x) - g x * spatialLaplacian g x)
      volume := by exact i_gLf.neg.sub i_gLg
  have h2 : Integrable (fun x => f x * spatialLaplacian f x + f x * spatialLaplacian g x)
      volume := by exact i_fLf.add i_fLg
  have h1' : Integrable (fun x => -(g x * spatialLaplacian f x)) volume := by exact i_gLf.neg
  rw [hexp, integral_add h1 h2, integral_sub h1' i_gLg, integral_neg,
    integral_add i_fLf i_fLg, e1, e2, e3, e4]
  have hsym : (∑ j : Fin 3, ∫ x, spatialDeriv g j x * spatialDeriv f j x) =
      ∑ j : Fin 3, ∫ x, spatialDeriv f j x * spatialDeriv g j x := by
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; funext x; ring
  have hsq (h : Vec3 → ℝ) (j : Fin 3) :
      (∫ x, spatialDeriv h j x * spatialDeriv h j x) = ∫ x, spatialDeriv h j x ^ 2 := by
    congr 1; funext x; ring
  simp only [hsq, hsym]
  ring


/-- The Laplacian is the sum of the diagonal second ordered derivatives. -/
theorem lps_spatialLaplacian_eq_words (f : Vec3 → ℝ) :
    spatialLaplacian f = fun x => ∑ j : Fin 3, wordDeriv [j, j] f x := rfl

/-- The Laplacian of a smooth function is smooth. -/
theorem lps_spatialLaplacian_contDiff {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialLaplacian f) := by
  rw [lps_spatialLaplacian_eq_words]
  exact ContDiff.sum fun j _ => contDiff_wordDeriv hf [j, j]

/-- A derivative of the Laplacian is the sum of the diagonal third ordered derivatives. -/
theorem lps_spatialDeriv_spatialLaplacian {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) :
    spatialDeriv (spatialLaplacian f) i = fun x => ∑ j : Fin 3, wordDeriv [j, j, i] f x := by
  have h := localDivCurlSmooth_wordDeriv_sum [i] (f := fun j x => wordDeriv [j, j] f x)
    (fun j => contDiff_wordDeriv hf [j, j])
  rw [lps_spatialLaplacian_eq_words]
  exact h

/-- A derivative of the Laplacian of a smooth function with square-integrable derivatives through order three is square integrable. -/
theorem lps_spatialDeriv_spatialLaplacian_memLp {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hL2 : ∀ α : List (Fin 3), α.length ≤ 3 → MemLp (wordDeriv α f) 2 volume) (i : Fin 3) :
    MemLp (spatialDeriv (spatialLaplacian f) i) 2 volume := by
  rw [lps_spatialDeriv_spatialLaplacian hf i]
  exact memLp_finsetSum _ fun j _ => hL2 [j, j, i] (by simp)

/-- The componentwise Laplacian of a smooth solenoidal field is solenoidal (`prop:lps-local-strong`). -/
theorem lps_spatialLaplacian_solenoidal {u : Vec3 → Vec3}
    (hu : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i))
    (hdiv : ∀ x : Vec3, ∑ i : Fin 3, spatialDeriv (fun y => u y i) i x = 0) (x : Vec3) :
    ∑ i : Fin 3, spatialDeriv (spatialLaplacian (fun y => u y i)) i x = 0 := by
  simp only [lps_spatialDeriv_spatialLaplacian (hu _)]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h := ESS.lps_wordDeriv_solenoidal hu hdiv [j, j] x
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (congrFun (ESS.lps_wordDeriv_append_words [j, j] [i] (fun y => u y i)) x).symm

end ESS.LPS

end
