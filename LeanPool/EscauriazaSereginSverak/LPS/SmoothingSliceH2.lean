/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSliceConvection
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSobolevBridge
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateStrongFormAE
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTransportPairing
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticitySobolevSmooth

/-!
# The slice `H²` bound of a strong solution from its time derivative

On one time slice, a solenoidal vector field `f ∈ H²(ℝ³)` solving the stationary
Navier–Stokes system `Δf = g + (f·∇)f + ∇q` with `g ∈ L²` and a pressure `q ∈ H¹`
satisfies `‖D²f‖ ≤ 2‖g‖ + C‖∇f‖³` (`prop:lps-smoothing`).

The proof tests the equation with `Δf`: the Hessian and the Laplacian have the same
`L²` norm, the Laplacian of a solenoidal field lies in `J`, so the pressure gradient
drops out, and the convection term is bounded by `‖f‖_{L⁶}‖∇f‖_{L³}`, which the
Sobolev and interpolation inequalities control by `‖∇f‖^{3/2}‖D²f‖^{1/2}`. Young's
inequality absorbs the Hessian factor.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A square-integrable pressure with square-integrable weak gradient is orthogonal to
the solenoidal space `J`: `⟨∇q, w⟩ = 0` for every `w ∈ J` (`prop:lps-smoothing`). -/
theorem lps_weak_gradient_pairing_J_eq_zero {q : Vec3 → ℝ} {Gq : Fin 3 → Vec3 → ℝ}
    {w : Vec3 → Vec3} (hq : MemLp q 2 volume) (hGq : ∀ i, MemLp (Gq i) 2 volume)
    (hweak : ∀ i, HasWeakPartialDerivOn (Set.univ : Set Vec3) i q (Gq i))
    (hw : IsInJ w) :
    ∫ x, ∑ i : Fin 3, Gq i x * w x i = 0 := by
  obtain ⟨hw2, a, ha, hac, hadiv, hlim⟩ := hw
  have hGv : MemLp (fun x i => Gq i x : Vec3 → Vec3) 2 volume :=
    memLp_pi_iff.mpr hGq
  have hak (k : ℕ) : MemLp (a k) 2 volume :=
    (ha k).continuous.memLp_of_hasCompactSupport (hac k)
  have hzero (k : ℕ) : ∫ x, ∑ i : Fin 3, Gq i x * a k x i = 0 := by
    have hcomp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y => a k y i) :=
      contDiff_pi.mp (ha k) i
    have hcompc (i : Fin 3) : HasCompactSupport (fun y => a k y i) :=
      (hac k).comp_left (g := fun v : Vec3 => v i) rfl
    have hdmem (i : Fin 3) : MemLp (spatialDeriv (fun y => a k y i) i) 2 volume :=
      (contDiff_spatialDeriv_smooth (hcomp i) i).continuous.memLp_of_hasCompactSupport
        ((hcompc i).fderiv_apply (𝕜 := ℝ) (basisVec i))
    have hpart (i : Fin 3) : ∫ x, q x * spatialDeriv (fun y => a k y i) i x =
        -∫ x, Gq i x * a k x i := by
      have h := hweak i (fun y => a k y i) (hcomp i) (hcompc i) (subset_univ _)
      simpa only [Measure.restrict_univ, spatialDeriv] using h
    have hint1 (i : Fin 3) : Integrable (fun x => Gq i x * a k x i) volume :=
      (hGq i).integrable_mul ((hak k).eval i)
    have hint2 (i : Fin 3) :
        Integrable (fun x => q x * spatialDeriv (fun y => a k y i) i x) volume :=
      hq.integrable_mul (hdmem i)
    rw [integral_finsetSum _ fun i _ => hint1 i]
    have hswap : ∑ i : Fin 3, ∫ x, Gq i x * a k x i =
        -∑ i : Fin 3, ∫ x, q x * spatialDeriv (fun y => a k y i) i x := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hpart i, neg_neg]
    rw [hswap, ← integral_finsetSum _ fun i _ => hint2 i]
    have hpt : (fun x => ∑ i : Fin 3, q x * spatialDeriv (fun y => a k y i) i x) =
        fun _ => 0 := by
      funext x
      rw [← Finset.mul_sum, hadiv k x, mul_zero]
    rw [hpt, integral_zero, neg_zero]
  have hbound (k : ℕ) : |∫ x, ∑ i : Fin 3, Gq i x * w x i| ≤
      3 * (eLpNorm (fun x i => Gq i x : Vec3 → Vec3) 2 volume).toReal *
        (eLpNorm (w - a k) 2 volume).toReal := by
    have hi1 : Integrable (fun x => ∑ i : Fin 3, Gq i x * w x i) volume :=
      integrable_finsetSum _ fun i _ => (hGq i).integrable_mul (hw2.eval i)
    have hi2 : Integrable (fun x => ∑ i : Fin 3, Gq i x * a k x i) volume :=
      integrable_finsetSum _ fun i _ => (hGq i).integrable_mul ((hak k).eval i)
    have hdiff : ∫ x, ∑ i : Fin 3, Gq i x * w x i =
        ∫ x, ∑ i : Fin 3, Gq i x * (w - a k) x i := by
      have h := integral_sub hi1 hi2
      rw [hzero k, sub_zero] at h
      rw [← h]
      congr 1
      funext x
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hdiff]
    exact lps_abs_pairing_le (F := fun x i => Gq i x) hGv (hw2.sub (hak k))
  have hlim' : Tendsto (fun k => 3 * (eLpNorm (fun x i => Gq i x : Vec3 → Vec3) 2 volume).toReal *
      (eLpNorm (w - a k) 2 volume).toReal) atTop (𝓝 0) := by
    have h2 : Tendsto (fun k => eLpNorm (w - a k) 2 volume) atTop (𝓝 0) := by
      refine hlim.congr fun k => ?_
      rw [eLpNorm_sub_comm]
      rfl
    have h1 : Tendsto (fun k => (eLpNorm (w - a k) 2 volume).toReal) atTop (𝓝 0) := by
      have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
      rw [ENNReal.toReal_zero] at h3
      exact h3
    simpa using h1.const_mul (3 * (eLpNorm (fun x i => Gq i x : Vec3 → Vec3) 2 volume).toReal)
  have hle : |∫ x, ∑ i : Fin 3, Gq i x * w x i| ≤ 0 := ge_of_tendsto' hlim' hbound
  exact abs_nonpos_iff.mp hle

/-- A square-integrable vector field whose weak divergence vanishes almost everywhere
is weakly solenoidal (`prop:lps-smoothing`). -/
theorem lps_weak_div_free_of_ae_trace {f : Fin 3 → Vec3 → ℝ} {Df : Fin 3 → Vec3 → ℝ}
    (hf : ∀ i, MemLp (f i) 2 volume) (hDf : ∀ i, MemLp (Df i) 2 volume)
    (hweak : ∀ i, HasWeakPartialDerivOn (Set.univ : Set Vec3) i (f i) (Df i))
    (hdiv : ∀ᵐ x ∂(volume : Measure Vec3), ∑ i, Df i x = 0)
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    ∫ x, ∑ i : Fin 3, f i x * ψ.partialDeriv i x = 0 := by
  have hψs (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ.partialDeriv i x) :=
    contDiff_spatialDeriv_smooth ψ.contDiff i
  have hψc (i : Fin 3) : HasCompactSupport (fun x => ψ.partialDeriv i x) :=
    ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hψ2 : MemLp ψ.toFun 2 volume :=
    ψ.contDiff.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport
  have hpart (i : Fin 3) : ∫ x, f i x * ψ.partialDeriv i x = -∫ x, Df i x * ψ x := by
    have h := (hasWeakPartialDerivOn_iff_forall_testFunction.mp (hweak i)) ψ
    simpa only [Measure.restrict_univ] using h
  have hint1 (i : Fin 3) : Integrable (fun x => f i x * ψ.partialDeriv i x) volume :=
    (hf i).integrable_mul
      ((hψs i).continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) (hψc i))
  have hint2 (i : Fin 3) : Integrable (fun x => Df i x * ψ x) volume :=
    (hDf i).integrable_mul hψ2
  rw [integral_finsetSum _ fun i _ => hint1 i, Finset.sum_congr rfl fun i _ => hpart i,
    Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => hint2 i, neg_eq_zero]
  have hae : (fun x => ∑ i : Fin 3, Df i x * ψ x) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [hdiv] with x hx
    rw [← Finset.sum_mul, hx, zero_mul]
  rw [integral_congr_ae hae, integral_zero]

/-- Testing `L = g + N + P` with `L`, where `P` is orthogonal to `L`, gives
`‖L‖ ≤ ‖g‖ + ‖N‖` for the Euclidean `L²` norms. -/
private theorem lps_slice_test_norm_le {L g N P : Fin 3 → Vec3 → ℝ}
    (hL : ∀ i, MemLp (L i) 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hN : ∀ i, MemLp (N i) 2 volume) (hP : ∀ i, MemLp (P i) 2 volume)
    (heq : ∀ᵐ x ∂(volume : Measure Vec3), ∀ i, g i x - L i x + N i x + P i x = 0)
    (horth : ∫ x, ∑ i : Fin 3, P i x * L i x = 0) :
    Real.sqrt (∑ i, ∫ x, L i x ^ 2) ≤
      Real.sqrt (∑ i, ∫ x, g i x ^ 2) + Real.sqrt (∑ i, ∫ x, N i x ^ 2) := by
  have hgL (i : Fin 3) : Integrable (fun x => g i x * L i x) volume :=
    (hg i).integrable_mul (hL i)
  have hNL (i : Fin 3) : Integrable (fun x => N i x * L i x) volume :=
    (hN i).integrable_mul (hL i)
  have hPL (i : Fin 3) : Integrable (fun x => P i x * L i x) volume :=
    (hP i).integrable_mul (hL i)
  have hLL (i : Fin 3) : ∫ x, L i x ^ 2 =
      (∫ x, g i x * L i x) + (∫ x, N i x * L i x) + ∫ x, P i x * L i x := by
    have hgNL : Integrable (fun x => g i x * L i x + N i x * L i x) volume :=
      (hgL i).add (hNL i)
    rw [← integral_add (hgL i) (hNL i), ← integral_add hgNL (hPL i)]
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    have h := hx i
    linear_combination (-(L i x)) * h
  have hPsum : ∑ i : Fin 3, ∫ x, P i x * L i x = 0 := by
    rw [← integral_finsetSum _ fun i _ => hPL i]
    exact horth
  have hsum : ∑ i, ∫ x, L i x ^ 2 =
      (∑ i : Fin 3, ∫ x, g i x * L i x) + ∑ i : Fin 3, ∫ x, N i x * L i x := by
    rw [Finset.sum_congr rfl fun i _ => hLL i, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hPsum, add_zero]
  have hCg := lps_finset_integral_pairing_le Finset.univ g L (fun i _ => hg i) (fun i _ => hL i)
  have hCN := lps_finset_integral_pairing_le Finset.univ N L (fun i _ => hN i) (fun i _ => hL i)
  set S := ∑ i, ∫ x, L i x ^ 2 with hS
  set A := Real.sqrt (∑ i, ∫ x, g i x ^ 2)
  set B := Real.sqrt (∑ i, ∫ x, N i x ^ 2)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hSsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hx0 : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  have hmain : Real.sqrt S ^ 2 ≤ (A + B) * Real.sqrt S := by
    rw [hSsq]
    calc S = (∑ i : Fin 3, ∫ x, g i x * L i x) + ∑ i : Fin 3, ∫ x, N i x * L i x := hsum
      _ ≤ A * Real.sqrt S + B * Real.sqrt S := add_le_add hCg hCN
      _ = (A + B) * Real.sqrt S := by ring
  nlinarith only [hmain, hA0, hB0, hx0]

/-- The Euclidean `L²` norm of a two-index family dominates the `eLpNorm` of the
associated matrix field. -/
private theorem lps_eLpNorm_two_le_sqrt_sum₂ {F : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hF : ∀ i j, MemLp (F i j) 2 volume) :
    eLpNorm (fun x i j => F i j x : Vec3 → Fin 3 → Vec3) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (∑ i, ∑ j, ∫ x, F i j x ^ 2)) := by
  have hmem : MemLp (fun x i j => F i j x : Vec3 → Fin 3 → Vec3) 2 volume :=
    memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun j => hF i j
  have hB : Integrable (fun x => ∑ i, ∑ j, F i j x ^ 2) volume :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF i j).integrable_sq
  have hpt (y : Vec3) : ‖(fun i j => F i j y : Fin 3 → Vec3)‖ ^ 2 ≤
      ∑ i, ∑ j, F i j y ^ 2 := by
    have hB0 : 0 ≤ ∑ i, ∑ j, F i j y ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hle : ‖(fun i j => F i j y : Fin 3 → Vec3)‖ ≤ Real.sqrt (∑ i, ∑ j, F i j y ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
      rw [Real.norm_eq_abs]
      apply Real.abs_le_sqrt
      calc F i j y ^ 2 ≤ ∑ j', F i j' y ^ 2 :=
            Finset.single_le_sum (f := fun j' => F i j' y ^ 2) (fun _ _ => sq_nonneg _)
              (Finset.mem_univ j)
        _ ≤ ∑ i', ∑ j', F i' j' y ^ 2 :=
            Finset.single_le_sum (f := fun i' => ∑ j', F i' j' y ^ 2)
              (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    calc ‖(fun i j => F i j y : Fin 3 → Vec3)‖ ^ 2 ≤
        Real.sqrt (∑ i, ∑ j, F i j y ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = ∑ i, ∑ j, F i j y ^ 2 := Real.sq_sqrt hB0
  have h := vorticitySobolevSmooth_eLpNorm_le hmem.aestronglyMeasurable hB hpt
  have hint : ∫ y, ∑ i, ∑ j, F i j y ^ 2 = ∑ i, ∑ j, ∫ x, F i j x ^ 2 := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF i j).integrable_sq]
    exact Finset.sum_congr rfl fun i _ =>
      integral_finsetSum _ fun j _ => (hF i j).integrable_sq
  rwa [hint] at h

/-- The Euclidean `L²` norm of a three-index family dominates the `eLpNorm` of the
associated tensor field. -/
private theorem lps_eLpNorm_two_le_sqrt_sum₃ {F : Fin 3 → Fin 3 → Fin 3 → Vec3 → ℝ}
    (hF : ∀ i j k, MemLp (F i j k) 2 volume) :
    eLpNorm (fun x i j k => F i j k x : Vec3 → Fin 3 → Fin 3 → Vec3) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (∑ i, ∑ j, ∑ k, ∫ x, F i j k x ^ 2)) := by
  have hmem : MemLp (fun x i j k => F i j k x : Vec3 → Fin 3 → Fin 3 → Vec3) 2 volume :=
    memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun j => memLp_pi_iff.mpr fun k => hF i j k
  have hB : Integrable (fun x => ∑ i, ∑ j, ∑ k, F i j k x ^ 2) volume :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => (hF i j k).integrable_sq
  have hpt (y : Vec3) : ‖(fun i j k => F i j k y : Fin 3 → Fin 3 → Vec3)‖ ^ 2 ≤
      ∑ i, ∑ j, ∑ k, F i j k y ^ 2 := by
    have hB0 : 0 ≤ ∑ i, ∑ j, ∑ k, F i j k y ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun k _ => sq_nonneg _
    have hle : ‖(fun i j k => F i j k y : Fin 3 → Fin 3 → Vec3)‖ ≤
        Real.sqrt (∑ i, ∑ j, ∑ k, F i j k y ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun k => ?_
      rw [Real.norm_eq_abs]
      apply Real.abs_le_sqrt
      calc F i j k y ^ 2 ≤ ∑ k', F i j k' y ^ 2 :=
            Finset.single_le_sum (f := fun k' => F i j k' y ^ 2) (fun _ _ => sq_nonneg _)
              (Finset.mem_univ k)
        _ ≤ ∑ j', ∑ k', F i j' k' y ^ 2 :=
            Finset.single_le_sum (f := fun j' => ∑ k', F i j' k' y ^ 2)
              (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j)
        _ ≤ ∑ i', ∑ j', ∑ k', F i' j' k' y ^ 2 :=
            Finset.single_le_sum (f := fun i' => ∑ j', ∑ k', F i' j' k' y ^ 2)
              (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
              (Finset.mem_univ i)
    calc ‖(fun i j k => F i j k y : Fin 3 → Fin 3 → Vec3)‖ ^ 2 ≤
        Real.sqrt (∑ i, ∑ j, ∑ k, F i j k y ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = ∑ i, ∑ j, ∑ k, F i j k y ^ 2 := Real.sq_sqrt hB0
  have h := vorticitySobolevSmooth_eLpNorm_le hmem.aestronglyMeasurable hB hpt
  have hint : ∫ y, ∑ i, ∑ j, ∑ k, F i j k y ^ 2 = ∑ i, ∑ j, ∑ k, ∫ x, F i j k x ^ 2 := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => (hF i j k).integrable_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (hF i j k).integrable_sq]
    exact Finset.sum_congr rfl fun j _ =>
      integral_finsetSum _ fun k _ => (hF i j k).integrable_sq
  rwa [hint] at h

/-- The convection field `(f·∇)f` of an `H²` vector field on `ℝ³` is square integrable,
and its Euclidean `L²` norm is at most `K ‖∇f‖^{3/2} ‖D²f‖^{1/2}`: the velocity is in
`L⁶` by the Sobolev inequality and the gradient in `L³` by interpolation between `L²`
and `L⁶` (`prop:lps-smoothing`). -/
theorem lps_slice_convection_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : Fin 3 → Vec3 → ℝ) (Df : Fin 3 → Fin 3 → Vec3 → ℝ)
      (D2f : Fin 3 → Fin 3 → Fin 3 → Vec3 → ℝ),
      (∀ i, MemLp (f i) 2 volume) → (∀ i j, MemLp (Df i j) 2 volume) →
      (∀ i j k, MemLp (D2f i j k) 2 volume) →
      (∀ i j, HasWeakPartialDerivOn (Set.univ : Set Vec3) j (f i) (Df i j)) →
      (∀ i j k, HasWeakPartialDerivOn (Set.univ : Set Vec3) k (Df i j) (D2f i j k)) →
      (∀ i, MemLp (fun x => ∑ j, f j x * Df i j x) 2 volume) ∧
      Real.sqrt (∑ i, ∫ x, (∑ j, f j x * Df i j x) ^ 2) ≤
        K * Real.sqrt (∑ i, ∑ j, ∫ x, Df i j x ^ 2) *
          Real.sqrt (Real.sqrt (∑ i, ∑ j, ∫ x, Df i j x ^ 2)) *
          Real.sqrt (Real.sqrt (∑ i, ∑ j, ∑ k, ∫ x, D2f i j k x ^ 2)) := by
  set G := gagliardoNirenbergSobolevConstant with hGdef
  have hGne : G ≠ ⊤ := CKN.Leray.gagliardoNirenbergSobolevConstant_ne_top
  refine ⟨Real.sqrt 3 * (3 * (6 * G.toReal) * (9 * G.toReal ^ (1 / 2 : ℝ) *
    (2 : ℝ) ^ (1 / 2 : ℝ))), by positivity, ?_⟩
  intro f Df D2f hf hDf hD2f hwf hwDf
  let u : Vec3 → Vec3 := fun x j => f j x
  let Du : Vec3 → Fin 3 → Vec3 := fun x i j => Df i j x
  let D2u : Vec3 → Fin 3 → Fin 3 → Vec3 := fun x i j k => D2f i j k x
  have hu2 : MemLp u 2 volume := memLp_pi_iff.mpr fun i => hf i
  have hDu2 : MemLp Du 2 volume :=
    memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun j => hDf i j
  have hD2u2 : MemLp D2u 2 volume :=
    memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun j => memLp_pi_iff.mpr fun k => hD2f i j k
  have hgrad : ∀ i j : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => Du x i j) (fun x => D2u x i j) := fun i j k => hwDf i j k
  have hH1 : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x => u x i) ∧ h.grad = (fun x j => Du x i j) := fun i =>
    ⟨{ toFun := f i
       grad := fun x j => Df i j x
       memL2 := (hf i).restrict _
       gradMemL2 := fun j => (hDf i j).restrict _
       hasWeakGradient := fun j => hwf i j }, rfl, rfl⟩
  have hNmem (k : Fin 3) : MemLp (fun x => ∑ j, f j x * Df k j x) 2 volume :=
    lps_h1_convection_memLp_two hu2 hDu2 hD2u2 hH1 hgrad k
  refine ⟨hNmem, ?_⟩
  have h6 : eLpNorm u (ENNReal.ofReal 6) volume ≤ 6 * G * eLpNorm Du 2 volume := by
    rw [ENNReal.ofReal_ofNat]
    exact LPS.lps_regularised_h1_vector_six_bound hu2 hDu2 hH1
  have hgi := lps_h1_gradient_interpolation (s := 6) (by norm_num) hDu2 hD2u2 hgrad
  have e1 : (2 * 6 / (6 - 2) : ℝ) = 3 := by norm_num
  have e2 : ((3 : ℝ) / 6) = 1 / 2 := by norm_num
  have e3 : (((6 : ℝ) - 3) / 6) = 1 / 2 := by norm_num
  rw [e1, e2, e3] at hgi
  have hHolder : ENNReal.HolderTriple (ENNReal.ofReal 6) (ENNReal.ofReal 3)
      (ENNReal.ofReal 2) :=
    serrin_holder_ofReal3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb (v w : Vec3) : ‖∑ j : Fin 3, v j * w j‖ ≤ ((3 : ℝ≥0) : ℝ) * ‖v‖ * ‖w‖ := by
    calc ‖∑ j : Fin 3, v j * w j‖ ≤ ∑ j : Fin 3, ‖v j * w j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, ‖v‖ * ‖w‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul (norm_le_pi_norm v j) (norm_le_pi_norm w j) (norm_nonneg _)
            (norm_nonneg _)
      _ = ((3 : ℝ≥0) : ℝ) * ‖v‖ * ‖w‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            NNReal.coe_ofNat, Nat.cast_ofNat]
          ring
  have hbc : Continuous (Function.uncurry fun (v w : Vec3) => ∑ j : Fin 3, v j * w j) := by
    change Continuous fun p : Vec3 × Vec3 => ∑ j : Fin 3, p.1 j * p.2 j
    fun_prop
  set a := Real.sqrt (∑ i, ∑ j, ∫ x, Df i j x ^ 2) with ha_def
  set X := Real.sqrt (∑ i, ∑ j, ∑ k, ∫ x, D2f i j k x ^ 2) with hX_def
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hDuA : eLpNorm Du 2 volume ≤ ENNReal.ofReal a := lps_eLpNorm_two_le_sqrt_sum₂ hDf
  have hD2uX : eLpNorm D2u 2 volume ≤ ENNReal.ofReal X := lps_eLpNorm_two_le_sqrt_sum₃ hD2f
  set M : ℝ := 3 * (6 * G.toReal * a) *
    (9 * G.toReal ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ))
    with hM_def
  have hM0 : 0 ≤ M := by positivity
  have hk (k : Fin 3) : Real.sqrt (∫ x, (∑ j, f j x * Df k j x) ^ 2) ≤ M := by
    have hH : eLpNorm (fun x => Du x k) (ENNReal.ofReal 3) volume ≤
        eLpNorm (fun x => ∑ i : Fin 3, ‖Du x i‖) (ENNReal.ofReal 3) volume := by
      apply eLpNorm_mono_ae_real (hDu2.eval k).aestronglyMeasurable
      filter_upwards [] with x
      exact Finset.single_le_sum (f := fun i : Fin 3 => ‖Du x i‖) (fun i _ => norm_nonneg _)
        (Finset.mem_univ k)
    have hN := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (μ := volume)
      (p := ENNReal.ofReal 6) (q := ENNReal.ofReal 3) (r := ENNReal.ofReal 2)
      (fun (v w : Vec3) => ∑ j : Fin 3, v j * w j) 3 hbc hu2.aestronglyMeasurable
      (hDu2.eval k).aestronglyMeasurable (Eventually.of_forall fun x => hb (u x) (Du x k))
    rw [ENNReal.coe_ofNat] at hN
    have hE : eLpNorm (fun x => ∑ j, f j x * Df k j x) (ENNReal.ofReal 2) volume ≤
        3 * (6 * G * ENNReal.ofReal a) * (9 * G ^ (1 / 2 : ℝ) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal a ^ (1 / 2 : ℝ) * ENNReal.ofReal X ^ (1 / 2 : ℝ)) := by
      calc eLpNorm (fun x => ∑ j, f j x * Df k j x) (ENNReal.ofReal 2) volume ≤
          3 * eLpNorm u (ENNReal.ofReal 6) volume *
            eLpNorm (fun x => Du x k) (ENNReal.ofReal 3) volume := hN
        _ ≤ 3 * (6 * G * eLpNorm Du 2 volume) * (9 * G ^ (1 / 2 : ℝ) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
            eLpNorm Du 2 volume ^ (1 / 2 : ℝ) * eLpNorm D2u 2 volume ^ (1 / 2 : ℝ)) := by
          gcongr
          exact hH.trans hgi
        _ ≤ _ := by gcongr
    have hfin : 3 * (6 * G * ENNReal.ofReal a) * (9 * G ^ (1 / 2 : ℝ) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal a ^ (1 / 2 : ℝ) * ENNReal.ofReal X ^ (1 / 2 : ℝ)) ≠ ⊤ := by
      finiteness
    have hreal := ENNReal.toReal_mono hfin hE
    rw [ENNReal.ofReal_ofNat, vorticity_eLpNorm_two_eq_sqrt (hNmem k),
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hreal
    simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal ha0,
      ENNReal.toReal_ofReal hX0, ENNReal.toReal_ofNat, hM_def] using hreal
  have hsq (k : Fin 3) : ∫ x, (∑ j, f j x * Df k j x) ^ 2 ≤ M ^ 2 := by
    have h0 : 0 ≤ ∫ x, (∑ j, f j x * Df k j x) ^ 2 := integral_nonneg fun x => sq_nonneg _
    calc ∫ x, (∑ j, f j x * Df k j x) ^ 2 =
        Real.sqrt (∫ x, (∑ j, f j x * Df k j x) ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hk k) 2
  have hsum : ∑ i, ∫ x, (∑ j, f j x * Df i j x) ^ 2 ≤ 3 * M ^ 2 := by
    calc ∑ i, ∫ x, (∑ j, f j x * Df i j x) ^ 2 ≤ ∑ _i : Fin 3, M ^ 2 :=
        Finset.sum_le_sum fun i _ => hsq i
      _ = 3 * M ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
  calc Real.sqrt (∑ i, ∫ x, (∑ j, f j x * Df i j x) ^ 2) ≤ Real.sqrt (3 * M ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 3 * M := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hM0]
    _ = _ := by
      rw [hM_def, Real.sqrt_eq_rpow a, Real.sqrt_eq_rpow X]
      ring

/-- Young absorption: `X ≤ G + K a √a √X` gives `X ≤ 2G + K² a³`. -/
private theorem lps_slice_absorb {X G K a : ℝ} (hX : 0 ≤ X) (ha : 0 ≤ a)
    (h : X ≤ G + K * a * Real.sqrt a * Real.sqrt X) : X ≤ 2 * G + K ^ 2 * a ^ 3 := by
  have h1 : K * a * Real.sqrt a * Real.sqrt X ≤
      ((K * a * Real.sqrt a) ^ 2 + Real.sqrt X ^ 2) / 2 := by
    nlinarith only [sq_nonneg (K * a * Real.sqrt a - Real.sqrt X)]
  have h2 : (K * a * Real.sqrt a) ^ 2 = K ^ 2 * a ^ 3 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ha]
    ring
  have h3 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
  rw [h2, h3] at h1
  linarith only [h, h1]

/-- The slice `H²` bound (`prop:lps-smoothing`): if `f ∈ H²(ℝ³)` is solenoidal and
`g - Δf + (f·∇)f + ∇q = 0` almost everywhere with `g ∈ L²` and `q ∈ L²` having a
square-integrable weak gradient, then `‖D²f‖ ≤ 2‖g‖ + C‖∇f‖³` for the Euclidean `L²`
norms, with `C` universal. The second-order family of `f` uses ordered words, first
letter applied first. -/
theorem lps_slice_H2_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g Gq : Fin 3 → Vec3 → ℝ) (Df : Fin 3 → Fin 3 → Vec3 → ℝ)
      (D2f : Fin 3 → Fin 3 → Fin 3 → Vec3 → ℝ) (q : Vec3 → ℝ),
      (∀ i, IsSobolevFamilyOn 2 univ (f i)
        (fun α => match α with
          | [] => f i | [j] => Df i j | [j, k] => D2f i j k | _ => fun _ => 0)) →
      (∀ i, MemLp (g i) 2 volume) → MemLp q 2 volume → (∀ i, MemLp (Gq i) 2 volume) →
      (∀ i, HasWeakPartialDerivOn (Set.univ : Set Vec3) i q (Gq i)) →
      (∀ᵐ x ∂(volume : Measure Vec3), ∑ i, Df i i x = 0) →
      (∀ᵐ x ∂(volume : Measure Vec3), ∀ i,
        g i x - ∑ j, D2f i j j x + ∑ j, f j x * Df i j x + Gq i x = 0) →
      Real.sqrt (∑ i, ∑ j, ∑ k, ∫ x, (D2f i j k x) ^ 2) ≤
        2 * Real.sqrt (∑ i, ∫ x, (g i x) ^ 2) +
        C * (∑ i, ∑ j, ∫ x, (Df i j x) ^ 2) ^ (3 / 2 : ℝ) := by
  obtain ⟨K, -, hK⟩ := lps_slice_convection_bound
  refine ⟨K ^ 2, sq_nonneg K, ?_⟩
  intro f g Gq Df D2f q hfam hg hq hGq hwq hdiv heq
  have hf2 (i : Fin 3) : MemLp (f i) 2 volume := by
    have h := (hfam i).memL2 [] (by simp)
    rw [Measure.restrict_univ] at h
    exact h
  have hDf2 (i j : Fin 3) : MemLp (Df i j) 2 volume := by
    have h := (hfam i).memL2 [j] (by simp)
    rw [Measure.restrict_univ] at h
    exact h
  have hD2f2 (i j k : Fin 3) : MemLp (D2f i j k) 2 volume := by
    have h := (hfam i).memL2 [j, k] (by simp)
    rw [Measure.restrict_univ] at h
    exact h
  have hwf (i j : Fin 3) : HasWeakPartialDerivOn (Set.univ : Set Vec3) j (f i) (Df i j) :=
    (hfam i).weak [] j (by simp)
  have hwDf (i j k : Fin 3) :
      HasWeakPartialDerivOn (Set.univ : Set Vec3) k (Df i j) (D2f i j k) :=
    (hfam i).weak [j] k (by simp)
  obtain ⟨hNmem, hNbound⟩ := hK f Df D2f hf2 hDf2 hD2f2 hwf hwDf
  have hHess (i : Fin 3) :
      ∑ j, ∑ k, ∫ x, (D2f i j k x) ^ 2 = ∫ x, (∑ j, D2f i j j x) ^ 2 :=
    LPS.lps_h1_sobolev_hessian_eq_laplacian (hfam i)
  have hdivw := lps_weak_div_free_of_ae_trace (f := f) (Df := fun i => Df i i) hf2
    (fun i => hDf2 i i) (fun i => hwf i i) hdiv
  have hlapdiv := lps_h1_laplacian_weak_div_free (u := fun x j => f j x)
    (Du := fun x i j => Df i j x) (D2u := fun x i j k => D2f i j k x)
    (memLp_pi_iff.mpr fun i => hf2 i)
    (memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun j => hDf2 i j)
    (memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun j => memLp_pi_iff.mpr fun k => hD2f2 i j k)
    (fun i j => hwf i j) (fun i j k => hwDf i j k) hdivw
  have horth : ∫ x, ∑ i : Fin 3, Gq i x * ∑ j, D2f i j j x = 0 :=
    lps_weak_gradient_pairing_J_eq_zero hq hGq hwq (weakDivFreeL2_isInJ hlapdiv)
  have hlapmem (i : Fin 3) : MemLp (fun x => ∑ j, D2f i j j x) 2 volume :=
    memLp_finsetSum Finset.univ fun j _ => hD2f2 i j j
  have htest : Real.sqrt (∑ i, ∫ x, (∑ j, D2f i j j x) ^ 2) ≤
      Real.sqrt (∑ i, ∫ x, g i x ^ 2) + Real.sqrt (∑ i, ∫ x, (∑ j, f j x * Df i j x) ^ 2) :=
    lps_slice_test_norm_le (L := fun i x => ∑ j, D2f i j j x) (g := g)
      (N := fun i x => ∑ j, f j x * Df i j x) (P := Gq) hlapmem hg hNmem hGq heq horth
  have hX : Real.sqrt (∑ i, ∑ j, ∑ k, ∫ x, (D2f i j k x) ^ 2) =
      Real.sqrt (∑ i, ∫ x, (∑ j, D2f i j j x) ^ 2) := by
    rw [Finset.sum_congr rfl fun i _ => hHess i]
  set E := ∑ i, ∑ j, ∫ x, (Df i j x) ^ 2 with hE_def
  have hE0 : 0 ≤ E :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _
  set X := Real.sqrt (∑ i, ∑ j, ∑ k, ∫ x, (D2f i j k x) ^ 2) with hX_def
  have hmain : X ≤ Real.sqrt (∑ i, ∫ x, (g i x) ^ 2) +
      K * Real.sqrt E * Real.sqrt (Real.sqrt E) * Real.sqrt X := by
    rw [hX]
    refine htest.trans ?_
    rw [← hX]
    exact add_le_add_right hNbound _
  have habs := lps_slice_absorb (Real.sqrt_nonneg _) (Real.sqrt_nonneg E) hmain
  have hpow : Real.sqrt E ^ 3 = E ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hE0]
    norm_num
  rw [hpow] at habs
  exact habs

end ESS

end
