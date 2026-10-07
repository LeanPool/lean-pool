/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessWeak
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Compactness Uniform

Supporting estimates for the Navier–Stokes development.
-/

public section

open Filter

namespace CKN.Leray

/-- Uniform convergence of pairings on a dense test sequence extends to every
Hilbert-space test under a common slice bound. Ball averages are particular
tests to which this conclusion applies. -/
theorem eventually_uniform_pairing_convergence_of_dense_tests
    {T E : Type*} [PseudoMetricSpace T] [CompactSpace T]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (u : ℕ → T → E) (v : T → E) (ψ : ℕ → E) (hψ : DenseRange ψ)
    (C : ℝ) (hC : 0 ≤ C) (hubound : ∀ n t, ‖u n t‖ ≤ C)
    (hvbound : ∀ t x, |inner ℝ (v t) x| ≤ C * ‖x‖)
    (F : ℕ → ℕ → C(T, ℝ)) (L : ℕ → C(T, ℝ))
    (hpair : ∀ n m t, F n m t = inner ℝ (u n t) (ψ m))
    (hLval : ∀ m t, L m t = inner ℝ (v t) (ψ m))
    (hLconv : ∀ m, Tendsto (fun n => F n m) atTop (nhds (L m))) :
    ∀ x ε, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      dist (inner ℝ (u n t) x) (inner ℝ (v t) x) < ε := by
  intro x ε hε
  let δ : ℝ := ε / (3 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨m, hxm⟩ := hψ.exists_dist_lt x hδ
  have hfrac : C / (3 * (C + 1)) ≤ (1 / 3 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [hC]
  have hsmall : C * dist x (ψ m) ≤ ε / 3 := by
    calc
      C * dist x (ψ m) ≤ C * δ := mul_le_mul_of_nonneg_left hxm.le hC
      _ = ε * (C / (3 * (C + 1))) := by dsimp [δ]; ring
      _ ≤ ε * (1 / 3) := mul_le_mul_of_nonneg_left hfrac hε.le
      _ = ε / 3 := by ring
  have hdist : Tendsto (fun n => dist (F n m) (L m)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => L m) atTop (nhds (L m)) :=
      tendsto_const_nhds
    simpa using (hLconv m).dist hconst
  have hε3 : 0 < ε / 3 := by positivity
  have hmiddle : ∀ᶠ n in atTop, dist (F n m) (L m) < ε / 3 :=
    hdist.eventually (isOpen_Iio.mem_nhds hε3)
  filter_upwards [hmiddle] with n hn t
  have hmidpoint : dist (F n m t) (L m t) ≤ dist (F n m) (L m) := by
    rw [dist_eq_norm, dist_eq_norm]
    calc
      ‖F n m t - L m t‖ = ‖(F n m - L m) t‖ := by rfl
      _ ≤ ‖F n m - L m‖ := (F n m - L m).norm_coe_le_norm t
  have hleft : dist (inner ℝ (u n t) x) (inner ℝ (u n t) (ψ m)) ≤
      C * dist x (ψ m) := by
    rw [dist_eq_norm, Real.norm_eq_abs, ← inner_sub_right]
    calc
      |inner ℝ (u n t) (x - ψ m)| ≤ C * ‖x - ψ m‖ := by
        exact (abs_real_inner_le_norm (u n t) (x - ψ m)).trans
          (mul_le_mul_of_nonneg_right (hubound n t) (norm_nonneg _))
      _ = C * dist x (ψ m) := by rw [dist_eq_norm]
  have hright : dist (inner ℝ (v t) (ψ m)) (inner ℝ (v t) x) ≤
      C * dist x (ψ m) := by
    rw [dist_eq_norm, Real.norm_eq_abs, ← inner_sub_right]
    calc
      |inner ℝ (v t) (ψ m - x)| ≤ C * ‖ψ m - x‖ := hvbound t _
      _ = C * dist (ψ m) x := by rw [dist_eq_norm]
      _ = C * dist x (ψ m) := by rw [dist_comm]
  have hmid : dist (inner ℝ (u n t) (ψ m))
      (inner ℝ (v t) (ψ m)) < ε / 3 := by
    have h := (hmidpoint.trans_lt hn)
    simpa [hpair n m t, hLval m t] using h
  calc
    dist (inner ℝ (u n t) x) (inner ℝ (v t) x) ≤
        dist (inner ℝ (u n t) x) (inner ℝ (u n t) (ψ m)) +
          (dist (inner ℝ (u n t) (ψ m)) (inner ℝ (v t) (ψ m)) +
            dist (inner ℝ (v t) (ψ m)) (inner ℝ (v t) x)) := by
      calc
        dist (inner ℝ (u n t) x) (inner ℝ (v t) x) ≤
            dist (inner ℝ (u n t) x) (inner ℝ (u n t) (ψ m)) +
              dist (inner ℝ (u n t) (ψ m)) (inner ℝ (v t) x) := dist_triangle _ _ _
        _ ≤ _ := by gcongr; exact dist_triangle _ _ _
    _ < ε / 3 + (ε / 3 + ε / 3) := by
      apply add_lt_add_of_le_of_lt (hleft.trans hsmall)
      apply add_lt_add_of_lt_of_le hmid (hright.trans hsmall)
    _ = ε := by ring

end CKN.Leray
