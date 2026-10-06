/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessUniform
public import LeanPool.CaffarelliKohnNirenberg.Foundation.RellichBalls
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Compactness Ball Pairing

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- The real Hilbert pairing of vector-valued `L²` functions is the integral
of their coordinatewise dot product. -/
theorem inner_toLp_vec3_eq_integral_dot
    (f g : Vec3 → L2Vec3)
    (hf : MemLp f 2 (volume : Measure Vec3))
    (hg : MemLp g 2 (volume : Measure Vec3)) :
    inner ℝ (hf.toLp f) (hg.toLp g) =
      ∫ x : Vec3, ∑ i : Fin 3, f x i * g x i ∂volume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx, PiLp.inner_apply]
  congr 1
  funext i
  exact Real.inner_apply _ _

/-- Moving a scalar cutoff between the field and test leaves the spatial
Hilbert pairing unchanged. -/
theorem inner_cutoff_vec3_eq_integral_dot
    (u : Vec3 → Vec3) (χ : Vec3 → ℝ) (ψ : Vec3 → L2Vec3)
    (hf : MemLp (fun x => χ x • WithLp.toLp 2 (u x)) 2
      (volume : Measure Vec3))
    (hψ : MemLp ψ 2 (volume : Measure Vec3)) :
    inner ℝ (hf.toLp (fun x => χ x • WithLp.toLp 2 (u x)))
      (hψ.toLp ψ) =
      ∫ x : Vec3, ∑ i : Fin 3, u x i * (χ x • ψ x) i ∂volume := by
  rw [inner_toLp_vec3_eq_integral_dot _ _ hf hψ]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  funext i
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- The indicator of a finite-measure set paired with a vector `L²` field
recovers the integral of one coordinate on that set. -/
theorem inner_indicator_basis_eq_integral_component
    {B : Set Vec3} (hB : MeasurableSet B) (hBfinite : volume B < ⊤)
    (f : Vec3 → L2Vec3) (hf : MemLp f 2 (volume : Measure Vec3))
    (i : Fin 3) :
    inner ℝ (hf.toLp f)
      (indicatorConstLp (2 : ℝ≥0∞) hB hBfinite.ne
        (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) =
      ∫ x in B, f x i ∂volume := by
  rw [L2.inner_def]
  have htest :
      (indicatorConstLp (2 : ℝ≥0∞) hB hBfinite.ne
        (WithLp.toLp 2 (Pi.single i (1 : ℝ))) :
          Lp L2Vec3 2 (volume : Measure Vec3)) =ᵐ[volume]
      B.indicator (fun _ => WithLp.toLp 2 (Pi.single i (1 : ℝ))) :=
    indicatorConstLp_coeFn
  have hEq : ∀ᵐ x ∂(volume : Measure Vec3),
      inner ℝ ((hf.toLp f) x)
        ((indicatorConstLp (2 : ℝ≥0∞) hB hBfinite.ne
          (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) x) =
      B.indicator (fun x => f x i) x := by
    filter_upwards [hf.coeFn_toLp, htest] with x hfx htx
    rw [hfx, htx]
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      simp [PiLp.inner_apply]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  rw [integral_congr_ae hEq]
  exact integral_indicator hB

/-- A ball coordinate average is a fixed Hilbert pairing multiplied by the
inverse volume. -/
theorem average_component_eq_scaled_inner
    {B : Set Vec3} (hB : MeasurableSet B) (hBfinite : volume B < ⊤)
    (f : Vec3 → L2Vec3) (hf : MemLp f 2 (volume : Measure Vec3))
    (i : Fin 3) :
    average (volume.restrict B) (fun x => f x i) =
      (volume B).toReal⁻¹ * inner ℝ (hf.toLp f)
        (indicatorConstLp (2 : ℝ≥0∞) hB hBfinite.ne
          (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) := by
  rw [average_eq, MeasureTheory.Measure.real, Measure.restrict_apply_univ]
  rw [smul_eq_mul, ← inner_indicator_basis_eq_integral_component hB hBfinite f hf i]

/-- If a cutoff is one on a finite-measure set, the original field's
coordinate average is a Hilbert pairing with the cutoff field. -/
theorem average_vec3_component_eq_cutoff_pairing
    {B : Set Vec3} (hB : MeasurableSet B) (hBfinite : volume B < ⊤)
    (u : Vec3 → Vec3) (χ : Vec3 → ℝ) (hχone : ∀ x ∈ B, χ x = 1)
    (hf : MemLp (fun x => χ x • WithLp.toLp 2 (u x)) 2
      (volume : Measure Vec3)) (i : Fin 3) :
    average (volume.restrict B) (fun x => u x i) =
      (volume B).toReal⁻¹ * inner ℝ
        (hf.toLp (fun x => χ x • WithLp.toLp 2 (u x)))
        (indicatorConstLp (2 : ℝ≥0∞) hB hBfinite.ne
          (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) := by
  have hae : (fun x => (χ x • WithLp.toLp 2 (u x)) i) =ᵐ[volume.restrict B]
      (fun x => u x i) := by
    filter_upwards [ae_restrict_mem hB] with x hx
    simp [hχone x hx]
  rw [← average_congr hae]
  exact average_component_eq_scaled_inner hB hBfinite
    (fun x => χ x • WithLp.toLp 2 (u x)) hf i

/-- Uniform convergence of three Hilbert pairings gives uniform convergence
of the associated vector of coefficients. -/
theorem eventually_uniform_vec3_of_uniform_pairings
    {T E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : ℕ → T → E) (v : T → E) (ψ : Fin 3 → E)
    (c : ℝ) (hc : 0 ≤ c)
    (hpair : ∀ i ε, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      dist (inner ℝ (u n t) (ψ i)) (inner ℝ (v t) (ψ i)) < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      vec3EuclideanNorm
        ((fun i => c * inner ℝ (u n t) (ψ i)) -
          (fun i => c * inner ℝ (v t) (ψ i))) ≤ ε := by
  intro ε hε
  let δ : ℝ := ε / (3 * (c + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hAll : ∀ᶠ n in atTop, ∀ i : Fin 3, ∀ t,
      dist (inner ℝ (u n t) (ψ i)) (inner ℝ (v t) (ψ i)) < δ := by
    have hAll' := (eventually_all_finset Finset.univ).2
      (fun i _ => hpair i δ hδ)
    filter_upwards [hAll'] with n hn i t
    exact hn i (Finset.mem_univ i) t
  filter_upwards [hAll] with n hn t
  have hcfrac : c / (c + 1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).2
    linarith only [hc]
  have hcomponent (i : Fin 3) :
      |c * inner ℝ (u n t) (ψ i) - c * inner ℝ (v t) (ψ i)| ≤ ε / 3 := by
    have hdist := (hn i t).le
    rw [Real.dist_eq] at hdist
    calc
      |c * inner ℝ (u n t) (ψ i) - c * inner ℝ (v t) (ψ i)| =
          c * |inner ℝ (u n t) (ψ i) - inner ℝ (v t) (ψ i)| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hc]
      _ ≤ c * δ := mul_le_mul_of_nonneg_left hdist hc
      _ = ε / 3 * (c / (c + 1)) := by
        dsimp [δ]
        have hden : c + 1 ≠ 0 := ne_of_gt (by positivity)
        field_simp
      _ ≤ ε / 3 := by
        have hε3 : 0 ≤ ε / 3 := by positivity
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hcfrac hε3
  calc
    vec3EuclideanNorm
        ((fun i => c * inner ℝ (u n t) (ψ i)) -
          (fun i => c * inner ℝ (v t) (ψ i))) ≤
        ∑ i : Fin 3,
          |c * inner ℝ (u n t) (ψ i) - c * inner ℝ (v t) (ψ i)| := by
          simpa only [Pi.sub_apply] using
            CKN.Foundation.Parabolic.vec3EuclideanNorm_le_sum_abs
              ((fun i => c * inner ℝ (u n t) (ψ i)) -
                (fun i => c * inner ℝ (v t) (ψ i)))
    _ ≤ ∑ _i : Fin 3, ε / 3 := Finset.sum_le_sum (fun i _ => hcomponent i)
    _ = ε := by simp; ring

/-- A bound on a Hilbert vector bounds any three fixed scalar pairings
assembled into a vector. -/
theorem vec3_norm_pairings_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (ψ : Fin 3 → E) (c C : ℝ) (hc : 0 ≤ c)
    (hC : ‖v‖ ≤ C) :
    vec3EuclideanNorm (fun i => c * inner ℝ v (ψ i)) ≤
      c * C * ∑ i : Fin 3, ‖ψ i‖ := by
  calc
    vec3EuclideanNorm (fun i => c * inner ℝ v (ψ i)) ≤
        ∑ i : Fin 3, |c * inner ℝ v (ψ i)| :=
      CKN.Foundation.Parabolic.vec3EuclideanNorm_le_sum_abs _
    _ ≤ ∑ i : Fin 3, c * C * ‖ψ i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg hc]
      calc
        c * |inner ℝ v (ψ i)| ≤ c * (‖v‖ * ‖ψ i‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hc
        _ ≤ c * (C * ‖ψ i‖) := by
          gcongr
        _ = c * C * ‖ψ i‖ := by ring
    _ = c * C * ∑ i : Fin 3, ‖ψ i‖ := by rw [Finset.mul_sum]

/-- Uniform weak convergence of cutoff slices gives uniform convergence of
the three coordinate averages on a set where the cutoff equals one. -/
theorem eventually_uniform_vec3_ball_averages
    {I J : Set ℝ} (hJI : J ⊆ I)
    {B : Set Vec3} (hB : MeasurableSet B) (hBfinite : volume B < ⊤)
    (u : ℕ → ParabolicPoint → Vec3) (χ : Vec3 → ℝ)
    (hχone : ∀ x ∈ B, χ x = 1)
    (hmem : ∀ n (t : I), MemLp
      (fun x => χ x • WithLp.toLp 2 (u n (x,t.1)))
      2 (volume : Measure Vec3))
    (V : I → Lp L2Vec3 2 (volume : Measure Vec3))
    (huniform : ∀ x ε, 0 < ε → ∀ᶠ n in atTop, ∀ t, (ht : t ∈ J) →
      dist (inner ℝ ((hmem n ⟨t, hJI ht⟩).toLp
        (fun y => χ y • WithLp.toLp 2 (u n (y,t)))) x)
        (inner ℝ (V ⟨t, hJI ht⟩) x) < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t, (ht : t ∈ J) →
      vec3EuclideanNorm
        ((fun i => average (volume.restrict B) (fun y => u n (y,t) i)) -
          (fun i => (volume B).toReal⁻¹ *
            inner ℝ (V ⟨t, hJI ht⟩)
              (indicatorConstLp (2 : ℝ≥0∞) hB hBfinite.ne
                (WithLp.toLp 2 (Pi.single i (1 : ℝ)))))) ≤ ε := by
  classical
  let c : ℝ := (volume B).toReal⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr ENNReal.toReal_nonneg
  let ψ : Fin 3 → Lp L2Vec3 2 (volume : Measure Vec3) := fun i =>
    indicatorConstLp (2 : ℝ≥0∞) hB hBfinite.ne
      (WithLp.toLp 2 (Pi.single i (1 : ℝ)))
  let F : ℕ → J → Lp L2Vec3 2 (volume : Measure Vec3) := fun n t =>
    (hmem n ⟨t.1, hJI t.property⟩).toLp
      (fun y => χ y • WithLp.toLp 2 (u n (y,t.1)))
  let W : J → Lp L2Vec3 2 (volume : Measure Vec3) :=
    fun t => V ⟨t.1, hJI t.property⟩
  have hpair (i : Fin 3) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, ∀ t : J,
        dist (inner ℝ (F n t) (ψ i)) (inner ℝ (W t) (ψ i)) < ε := by
    filter_upwards [huniform (ψ i) ε hε] with n hn t
    exact hn t.1 t.property
  have hvec := eventually_uniform_vec3_of_uniform_pairings F W ψ c hc hpair
  intro ε hε
  filter_upwards [hvec ε hε] with n hn t ht
  have havg (i : Fin 3) :
      average (volume.restrict B) (fun y => u n (y,t) i) =
        c * inner ℝ (F n ⟨t, ht⟩) (ψ i) := by
    simpa only [F, c, ψ] using
      average_vec3_component_eq_cutoff_pairing hB hBfinite
        (fun y => u n (y,t)) χ hχone (hmem n ⟨t, hJI ht⟩) i
  simpa only [havg, F, W, ψ, c] using hn ⟨t, ht⟩

end CKN.Leray
