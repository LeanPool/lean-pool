/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Generic analysis for the Vlasov variational equation

Picard-series solutions and their parameter dependence, a Grönwall difference-quotient bound,
and joint differentiability from continuous partial derivatives.  These arguments use only
Mathlib, so they can compile independently of the characteristic-flow construction.
-/

@[expose] public section

namespace Vlasov

open MeasureTheory Filter Topology Asymptotics

/-- Picard iterates for the linear IVP `x' = 𝒜(t)x`, `x(0)=x₀` (the V1c engine):
`I₀ ≡ x₀`, `I_{n+1}(t) = ∫₀ᵗ 𝒜(s)(Iₙ(s)) ds`. -/
noncomputable def picardIter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) : ℕ → ℝ → E
  | 0, _ => x₀
  | (n + 1), t => ∫ s in (0 : ℝ)..t, 𝒜 s (picardIter 𝒜 x₀ n s)

@[simp] lemma picardIter_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (t : ℝ) : picardIter 𝒜 x₀ 0 t = x₀ := rfl

lemma picardIter_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (n : ℕ) (t : ℝ) :
    picardIter 𝒜 x₀ (n + 1) t = ∫ s in (0 : ℝ)..t, 𝒜 s (picardIter 𝒜 x₀ n s) := rfl

/-- **C3 V1c-engine — the Picard iterates are continuous and satisfy the geometric
`(Kt)ⁿ/n!`-bound on `[0,T]`.**  Proved by simultaneous induction (continuity feeds
integrability, which feeds the next bound).  This `Σ (KT)ⁿ/n! = e^{KT}`-summable bound is the
convergence driver for the V1c fixed point. -/
lemma picardIter_continuousOn_and_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E)
    (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hcont𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T))
    (hbound𝒜 : ∀ t ∈ Set.Icc 0 T, ‖𝒜 t‖ ≤ K) :
    ∀ n, ContinuousOn (picardIter 𝒜 x₀ n) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, ‖picardIter 𝒜 x₀ n t‖ ≤ (K * t) ^ n / n.factorial * ‖x₀‖ := by
  intro n
  induction n with
  | zero =>
    refine ⟨continuousOn_const, fun t ht => ?_⟩
    simp
  | succ n ih =>
    obtain ⟨ih_cont, ih_bd⟩ := ih
    have hg_cont : ContinuousOn (fun s => 𝒜 s (picardIter 𝒜 x₀ n s)) (Set.Icc 0 T) :=
      hcont𝒜.clm_apply ih_cont
    have hg_int : IntegrableOn (fun s => 𝒜 s (picardIter 𝒜 x₀ n s)) (Set.Icc 0 T) :=
      hg_cont.integrableOn_Icc
    refine ⟨?_, ?_⟩
    · have hcp := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T) (μ := volume)
        (f := fun s => 𝒜 s (picardIter 𝒜 x₀ n s)) (by rw [Set.uIcc_of_le hT]; exact hg_int)
      rw [Set.uIcc_of_le hT] at hcp
      exact hcp
    · intro t ht
      have ht0 : (0 : ℝ) ≤ t := ht.1
      have htT : t ≤ T := ht.2
      have h_ptwise : ∀ s ∈ Set.Icc (0 : ℝ) t,
          ‖𝒜 s (picardIter 𝒜 x₀ n s)‖ ≤ K * (K * s) ^ n / n.factorial * ‖x₀‖ := by
        intro s hs
        have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, le_trans hs.2 htT⟩
        calc ‖𝒜 s (picardIter 𝒜 x₀ n s)‖
            ≤ ‖𝒜 s‖ * ‖picardIter 𝒜 x₀ n s‖ := (𝒜 s).le_opNorm _
          _ ≤ K * ((K * s) ^ n / n.factorial * ‖x₀‖) :=
              mul_le_mul (hbound𝒜 s hsT) (ih_bd s hsT) (norm_nonneg _) hK
          _ = K * (K * s) ^ n / n.factorial * ‖x₀‖ := by ring
      have hRHS_int : IntervalIntegrable
          (fun s => K * (K * s) ^ n / n.factorial * ‖x₀‖) volume 0 t :=
        (Continuous.intervalIntegrable (by fun_prop) 0 t)
      have hLHS_int : IntervalIntegrable
          (fun s => ‖𝒜 s (picardIter 𝒜 x₀ n s)‖) volume 0 t := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le ht0]
        exact (hg_cont.mono (Set.Icc_subset_Icc_right htT)).norm
      calc ‖picardIter 𝒜 x₀ (n + 1) t‖
          = ‖∫ s in (0 : ℝ)..t, 𝒜 s (picardIter 𝒜 x₀ n s)‖ := by rw [picardIter_succ]
        _ ≤ ∫ s in (0 : ℝ)..t, ‖𝒜 s (picardIter 𝒜 x₀ n s)‖ :=
            intervalIntegral.norm_integral_le_integral_norm ht0
        _ ≤ ∫ s in (0 : ℝ)..t, K * (K * s) ^ n / n.factorial * ‖x₀‖ :=
            intervalIntegral.integral_mono_on ht0 hLHS_int hRHS_int h_ptwise
        _ = (K * t) ^ (n + 1) / (n + 1).factorial * ‖x₀‖ := by
            have hpow : ∀ s : ℝ, K * (K * s) ^ n / n.factorial * ‖x₀‖
                = (K ^ (n + 1) * ‖x₀‖ / n.factorial) * s ^ n := by
              intro s; rw [mul_pow]; ring
            simp_rw [hpow]
            rw [intervalIntegral.integral_const_mul, integral_pow]
            rw [Nat.factorial_succ]
            push_cast
            rw [mul_pow]
            field_simp
            ring

/-- The Picard majorant can be chosen uniformly over the whole time window. -/
private lemma picardIter_norm_le_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hcont𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (hbound𝒜 : ∀ t ∈ Set.Icc 0 T, ‖𝒜 t‖ ≤ K)
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖picardIter 𝒜 x₀ n t‖ ≤ (K * T) ^ n / n.factorial * ‖x₀‖ := by
  refine ((picardIter_continuousOn_and_bound 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜 n).2 t ht).trans ?_
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg hK ht.1) (mul_le_mul_of_nonneg_left ht.2 hK) n)
      (Nat.cast_nonneg _)) (norm_nonneg _)

/-- **Step 3 (i) — joint `(z,s)` continuity of the Dyson sum** (global-hypothesis form).
The Picard iterates are jointly continuous, and their common summable majorant gives continuity
of the sum on `univ ×ˢ Icc 0 T`.  Fixed-time continuity specializes this result. -/
lemma picardSum_continuous_param_joint
    {Z E : Type*} [TopologicalSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : Z → ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (h𝒜_cont : Continuous (fun p : Z × ℝ => 𝒜 p.1 p.2))
    (h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖𝒜 z s‖ ≤ K) :
    ContinuousOn (fun p : Z × ℝ => ∑' n, picardIter (𝒜 p.1) x₀ n p.2)
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) := by
  have hiter_cont : ∀ n, Continuous (fun p : Z × ℝ => picardIter (𝒜 p.1) x₀ n p.2) := by
    intro n
    induction n with
    | zero =>
      simp only [picardIter_zero]
      exact continuous_const
    | succ n ih =>
      have hg : Continuous (Function.uncurry fun z v => 𝒜 z v (picardIter (𝒜 z) x₀ n v)) :=
        h𝒜_cont.clm_apply ih
      have hpp := intervalIntegral.continuous_parametric_primitive_of_continuous
        (μ := volume) (a₀ := (0 : ℝ)) hg
      simp only [picardIter_succ]
      exact hpp
  have h𝒜cont_z : ∀ z, ContinuousOn (𝒜 z) (Set.Icc (0 : ℝ) T) := fun z =>
    (h𝒜_cont.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hbd : ∀ (n : ℕ) (p : Z × ℝ), p ∈ Set.univ ×ˢ Set.Icc (0 : ℝ) T →
      ‖picardIter (𝒜 p.1) x₀ n p.2‖ ≤ (K * T) ^ n / n.factorial * ‖x₀‖ :=
    fun n p hp => picardIter_norm_le_uniform (𝒜 p.1) x₀ T hT K hK
      (h𝒜cont_z p.1) (h𝒜_bound p.1) n p.2 hp.2
  have hsum : Summable (fun n => (K * T) ^ n / n.factorial * ‖x₀‖) :=
    (Real.summable_pow_div_factorial (K * T)).mul_right ‖x₀‖
  exact continuousOn_tsum (fun n => (hiter_cont n).continuousOn) hsum hbd

/-- **Step 3 (i) — joint `(z,s)` continuity of the Dyson sum** on a time window.
Clamp time into `[0,T]` so the global form applies, then transfer back by agreement of the
iterates on `[0,T]`.  Fixed-time continuity specializes this result. -/
lemma picardSum_continuous_param_Icc_joint
    {Z E : Type*} [TopologicalSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : Z → ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (h𝒜_contOn : ContinuousOn (fun p : Z × ℝ => 𝒜 p.1 p.2) (Set.univ ×ˢ Set.Icc (0 : ℝ) T))
    (h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖𝒜 z s‖ ≤ K) :
    ContinuousOn (fun p : Z × ℝ => ∑' n, picardIter (𝒜 p.1) x₀ n p.2)
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) := by
  set cl : ℝ → ℝ := fun s => ↑(Set.projIcc 0 T hT s) with hcl
  have hcl_cont : Continuous cl := continuous_subtype_val.comp continuous_projIcc
  have hcl_mem : ∀ s, cl s ∈ Set.Icc (0 : ℝ) T := fun s => (Set.projIcc 0 T hT s).2
  have hcl_eq : ∀ s ∈ Set.Icc (0 : ℝ) T, cl s = s := by
    intro s hs; change (↑(Set.projIcc 0 T hT s) : ℝ) = s; rw [Set.projIcc_of_mem hT hs]
  set 𝒜c : Z → ℝ → (E →L[ℝ] E) := fun z s => 𝒜 z (cl s) with h𝒜c
  have h𝒜c_cont : Continuous (fun p : Z × ℝ => 𝒜c p.1 p.2) := by
    have hmap : Continuous (fun p : Z × ℝ => ((p.1, cl p.2) : Z × ℝ)) :=
      continuous_fst.prodMk (hcl_cont.comp continuous_snd)
    have hmem : ∀ p : Z × ℝ, ((p.1, cl p.2) : Z × ℝ) ∈ Set.univ ×ˢ Set.Icc (0 : ℝ) T :=
      fun p => ⟨Set.mem_univ _, hcl_mem p.2⟩
    exact h𝒜_contOn.comp_continuous hmap hmem
  have h𝒜c_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖𝒜c z s‖ ≤ K :=
    fun z s _ => h𝒜_bound z (cl s) (hcl_mem s)
  have hagree : ∀ (n : ℕ) (z : Z), ∀ s ∈ Set.Icc (0 : ℝ) T,
      picardIter (𝒜c z) x₀ n s = picardIter (𝒜 z) x₀ n s := by
    intro n
    induction n with
    | zero => intro z s _; simp
    | succ n ih =>
      intro z s hs
      simp only [picardIter_succ]
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      have huIcc : u ∈ Set.Icc (0 : ℝ) T := by
        rw [Set.uIcc_of_le hs.1] at hu; exact ⟨hu.1, le_trans hu.2 hs.2⟩
      have e1 : 𝒜c z u = 𝒜 z u := by simp only [h𝒜c, hcl_eq u huIcc]
      rw [e1, ih z u huIcc]
  have key := picardSum_continuous_param_joint 𝒜c x₀ T hT K hK h𝒜c_cont h𝒜c_bound
  refine key.congr ?_
  rintro ⟨z, s⟩ ⟨_, hs⟩
  simp only
  congr 1; funext n; exact (hagree n z s hs).symm

/-- **C3 V1c-conv — the Dyson sum `M := ∑ₙ Iₙ` is continuous on `[0,T]`.**  Weierstrass M-test:
the terms are dominated by the summable majorant `(KT)ⁿ/n!·‖x₀‖`, so the series converges
uniformly; the uniform limit of the continuous partial sums is continuous.  (`M` is the candidate
solution: `M = x₀ + ∫₀ᵗ 𝒜(s)(M s) ds`, proved next.) -/
lemma picardSum_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hcont𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (hbound𝒜 : ∀ t ∈ Set.Icc 0 T, ‖𝒜 t‖ ≤ K) :
    ContinuousOn (fun t => ∑' n, picardIter 𝒜 x₀ n t) (Set.Icc 0 T) := by
  have hcb := picardIter_continuousOn_and_bound 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜
  have hbd : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
      ‖picardIter 𝒜 x₀ n t‖ ≤ (K * T) ^ n / n.factorial * ‖x₀‖ :=
    picardIter_norm_le_uniform 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜
  have hsum : Summable (fun n => (K * T) ^ n / n.factorial * ‖x₀‖) :=
    (Real.summable_pow_div_factorial (K * T)).mul_right ‖x₀‖
  exact continuousOn_tsum (fun n => (hcb n).1) hsum hbd

/-- **C3 V2-core — the Dyson sum is continuous in a parameter.**  Restrict joint continuity
of the Dyson sum to a fixed time in `[0,T]`.  The uniform majorant and convergence argument live
in `picardSum_continuous_param_joint`, shared by both forms. -/
lemma picardSum_continuous_param
    {Z E : Type*} [TopologicalSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : Z → ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (h𝒜_cont : Continuous (fun p : Z × ℝ => 𝒜 p.1 p.2))
    (h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖𝒜 z s‖ ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Continuous (fun z => ∑' n, picardIter (𝒜 z) x₀ n t) := by
  exact (picardSum_continuous_param_joint 𝒜 x₀ T hT K hK h𝒜_cont h𝒜_bound).comp_continuous
    (continuous_id.prodMk continuous_const) (fun z => ⟨Set.mem_univ z, ht⟩)

/-- Window version of `picardSum_continuous_param`: restrict the joint window theorem to a
fixed time.  The clamping and iterate-agreement argument is shared with the joint form. -/
lemma picardSum_continuous_param_Icc
    {Z E : Type*} [TopologicalSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : Z → ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (h𝒜_contOn : ContinuousOn (fun p : Z × ℝ => 𝒜 p.1 p.2) (Set.univ ×ˢ Set.Icc (0 : ℝ) T))
    (h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖𝒜 z s‖ ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Continuous (fun z => ∑' n, picardIter (𝒜 z) x₀ n t) := by
  exact (picardSum_continuous_param_Icc_joint 𝒜 x₀ T hT K hK h𝒜_contOn h𝒜_bound).comp_continuous
    (continuous_id.prodMk continuous_const) (fun z => ⟨Set.mem_univ z, ht⟩)

/-- **C3 V1c-rec — finite Picard recurrence.**  The `(N+1)`-th partial Dyson sum equals
`x₀ + ∫₀ᵗ 𝒜(s)(Sₙ(s)) ds`, where `Sₙ = ∑_{n<N} Iₙ`.  Only finite-sum swaps
(`integral_finsetSum`, `map_sum`); no infinite interchange.  Passing `N → ∞` against the
uniform convergence (`picardSum_continuousOn`'s M-test) yields the integral equation for `M`. -/
lemma picardSum_finset_recurrence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hcont𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (hbound𝒜 : ∀ t ∈ Set.Icc 0 T, ‖𝒜 t‖ ≤ K)
    (N : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∑ n ∈ Finset.range (N + 1), picardIter 𝒜 x₀ n t
      = x₀ + ∫ s in (0 : ℝ)..t, 𝒜 s (∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s) := by
  have hcb := picardIter_continuousOn_and_bound 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜
  have hint : ∀ n, IntervalIntegrable
      (fun s => 𝒜 s (picardIter 𝒜 x₀ n s)) volume 0 t := by
    intro n
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht.1]
    exact (hcont𝒜.clm_apply (hcb n).1).mono (Set.Icc_subset_Icc_right ht.2)
  rw [Finset.sum_range_succ', picardIter_zero]
  simp only [picardIter_succ]
  rw [add_comm]
  congr 1
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  exact (map_sum (𝒜 s) (fun i => picardIter 𝒜 x₀ i s) (Finset.range N)).symm

/-- **C3 V1c-inteq — the Dyson sum solves the integral equation.**
`M(t) = x₀ + ∫₀ᵗ 𝒜(s)(M s) ds` on `[0,T]`, where `M = ∑'ₙ Iₙ`.  Pass `N → ∞` in the finite
recurrence: LHS → `M t` (partial sums of the summable series); RHS via DCT (the terms
`𝒜(s)(S_N s) → 𝒜(s)(M s)` pointwise, dominated by the constant `K·∑'ₙ (KT)ⁿ/n!·‖x₀‖`). -/
lemma picardSum_solves_integralEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hcont𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (hbound𝒜 : ∀ t ∈ Set.Icc 0 T, ‖𝒜 t‖ ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∑' n, picardIter 𝒜 x₀ n t)
      = x₀ + ∫ s in (0 : ℝ)..t, 𝒜 s (∑' n, picardIter 𝒜 x₀ n s) := by
  have hcb := picardIter_continuousOn_and_bound 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hmaj : ∀ n, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖picardIter 𝒜 x₀ n s‖ ≤ (K * T) ^ n / n.factorial * ‖x₀‖ :=
    picardIter_norm_le_uniform 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜
  have hmaj_summable : Summable (fun n => (K * T) ^ n / n.factorial * ‖x₀‖) :=
    (Real.summable_pow_div_factorial (K * T)).mul_right ‖x₀‖
  have hsummable : ∀ s ∈ Set.Icc (0 : ℝ) T, Summable (fun n => picardIter 𝒜 x₀ n s) := by
    intro s hs
    exact (hmaj_summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hmaj n s hs)).of_norm
  set C : ℝ := ∑' n, (K * T) ^ n / n.factorial * ‖x₀‖ with hC
  have hSbound : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s‖ ≤ C := by
    intro N s hs
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun n _ => hmaj n s hs)) ?_
    exact hmaj_summable.sum_le_tsum _ (fun n _ => by positivity)
  set M : ℝ → E := fun u => ∑' n, picardIter 𝒜 x₀ n u with hM
  have hLHS : Filter.Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), picardIter 𝒜 x₀ n t)
      Filter.atTop (nhds (M t)) :=
    ((hsummable t ht).hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have hRHS_int : Filter.Tendsto
      (fun N => ∫ s in Set.Ioc (0 : ℝ) t, 𝒜 s (∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s))
      Filter.atTop (nhds (∫ s in Set.Ioc (0 : ℝ) t, 𝒜 s (M s))) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence (bound := fun _ => K * C)
    · intro N
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
      exact (hcont𝒜.clm_apply (continuousOn_finsetSum _ (fun n _ => (hcb n).1))).mono
        (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right htT))
    · exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
    · intro N
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt hs.1, le_trans hs.2 htT⟩
      calc ‖𝒜 s (∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s)‖
          ≤ ‖𝒜 s‖ * ‖∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s‖ := (𝒜 s).le_opNorm _
        _ ≤ K * C := mul_le_mul (hbound𝒜 s hsT) (hSbound N s hsT) (norm_nonneg _) hK
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt hs.1, le_trans hs.2 htT⟩
      exact ((𝒜 s).continuous.tendsto (M s)).comp ((hsummable s hsT).hasSum.tendsto_sum_nat)
  rw [intervalIntegral.integral_of_le ht0]
  have hrec' : ∀ N, ∑ n ∈ Finset.range (N + 1), picardIter 𝒜 x₀ n t
      = x₀ + ∫ s in Set.Ioc (0 : ℝ) t, 𝒜 s (∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s) := by
    intro N
    rw [picardSum_finset_recurrence 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜 N t ht,
      intervalIntegral.integral_of_le ht0]
  exact tendsto_nhds_unique hLHS ((hRHS_int.const_add x₀).congr (fun N => (hrec' N).symm))

/-- The explicit Picard sum satisfies the linear initial-value problem. -/
private lemma picardSum_spec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (T : ℝ) (hT : 0 ≤ T)
    (h𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (x₀ : E) :
    (∑' n, picardIter 𝒜 x₀ n 0) = x₀ ∧
      ContinuousOn (fun t => ∑' n, picardIter 𝒜 x₀ n t) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T,
        HasDerivWithinAt (fun t => ∑' n, picardIter 𝒜 x₀ n t)
          (𝒜 t (∑' n, picardIter 𝒜 x₀ n t)) (Set.Icc 0 T) t := by
  obtain ⟨K, hbK⟩ := isCompact_Icc.exists_bound_of_continuousOn h𝒜
  have hK'0 : 0 ≤ max K 0 := le_max_right _ _
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖𝒜 t‖ ≤ max K 0 :=
    fun t ht => le_trans (hbK t ht) (le_max_left _ _)
  set M : ℝ → E := fun u => ∑' n, picardIter 𝒜 x₀ n u with hM
  have hMcont : ContinuousOn M (Set.Icc 0 T) :=
    picardSum_continuousOn 𝒜 x₀ T hT (max K 0) hK'0 h𝒜 hbound
  have hMeq : ∀ t ∈ Set.Icc (0 : ℝ) T, M t = x₀ + ∫ s in (0 : ℝ)..t, 𝒜 s (M s) :=
    fun t ht => picardSum_solves_integralEq 𝒜 x₀ T hT (max K 0) hK'0 h𝒜 hbound t ht
  have hg_cont : ContinuousOn (fun s => 𝒜 s (M s)) (Set.Icc 0 T) := h𝒜.clm_apply hMcont
  refine ⟨?_, hMcont, fun t ht => ?_⟩
  · change M 0 = x₀
    rw [hMeq 0 ⟨le_refl 0, hT⟩, intervalIntegral.integral_same, add_zero]
  · have : Fact (t ∈ Set.Icc (0 : ℝ) T) := ⟨ht⟩
    have hg_int : IntervalIntegrable (fun s => 𝒜 s (M s)) volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ht.1]
      exact hg_cont.mono (Set.Icc_subset_Icc_right ht.2)
    have hg_meas : StronglyMeasurableAtFilter (fun s => 𝒜 s (M s)) (nhdsWithin t (Set.Icc 0 T)) :=
      ⟨Set.Icc 0 T, self_mem_nhdsWithin, hg_cont.aestronglyMeasurable measurableSet_Icc⟩
    have hFTC : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, 𝒜 s (M s)) (𝒜 t (M t))
        (Set.Icc 0 T) t :=
      intervalIntegral.integral_hasDerivWithinAt_right hg_int hg_meas (hg_cont t ht)
    exact (hFTC.const_add x₀).congr (fun y hy => hMeq y hy) (hMeq t ht)


/-- Existence for a linear ODE with continuous coefficients on a compact interval.
The Picard sum gives an explicit solution.  Its summable factorial majorant supplies continuity,
and its integral equation supplies the derivative through the fundamental theorem of calculus. -/
theorem exists_linearODE_solution_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (T : ℝ) (hT : 0 ≤ T)
    (h𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (x₀ : E) :
    ∃ M : ℝ → E, M 0 = x₀ ∧ ContinuousOn M (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt M (𝒜 t (M t)) (Set.Icc 0 T) t := by
  exact ⟨fun t => ∑' n, picardIter 𝒜 x₀ n t, picardSum_spec 𝒜 T hT h𝒜 x₀⟩

/-- **C3 V1c→matrix — the fundamental matrix of a linear ODE.**  Specialising
`exists_linearODE_solution_Icc` to the operator space `E := F →L[ℝ] F` with `𝒜(s) := A(s) ∘ (·)`
(left composition) and `x₀ := id` gives the fundamental solution `M' = A(t)∘M`, `M(0) = id`.
This `M(t)` is the candidate `Dflow t z` of the variational equation (#3), once `A` is the Vlasov
field Jacobian `A(s) = D_z b(s, Φ_s z)` along the flow (F2). -/
lemma exists_fundamentalMatrix
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : ℝ → (F →L[ℝ] F)) (T : ℝ) (hT : 0 ≤ T) (hA : ContinuousOn A (Set.Icc 0 T)) :
    ∃ M : ℝ → (F →L[ℝ] F), M 0 = ContinuousLinearMap.id ℝ F ∧ ContinuousOn M (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt M ((A t).comp (M t)) (Set.Icc 0 T) t := by
  obtain ⟨M, hM0, hMcont, hMderiv⟩ := exists_linearODE_solution_Icc
    (fun s => ContinuousLinearMap.compL ℝ F F F (A s)) T hT
    ((ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn hA)
    (ContinuousLinearMap.id ℝ F)
  refine ⟨M, hM0, hMcont, fun t ht => ?_⟩
  simpa [ContinuousLinearMap.compL_apply] using hMderiv t ht

/-- **C3 (shared) — Lipschitz-in-parameter + ContinuousOn-in-time ⇒ jointly ContinuousOn.**
A generic upgrade: if `G z ·` is `ContinuousOn (Icc 0 T)` for each `z` and `z ↦ G z s` is
`C`-Lipschitz uniformly over `s ∈ [0,T]`, then `(z,s) ↦ G z s` is jointly continuous on
`univ ×ˢ Icc 0 T`.  Used to derive flow joint continuity `(z,s) ↦ Φ_s z` from
`charFlow_lipschitzInZ_via_gronwall_Ioo` (Lipschitz-in-`z`) + per-`z` continuity in `s`. -/
lemma continuousOn_prod_of_lipschitz_continuousOn
    {Z E : Type*} [PseudoMetricSpace Z] [PseudoMetricSpace E]
    (G : Z → ℝ → E) (T C : ℝ)
    (hlip : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂, dist (G z₁ s) (G z₂ s) ≤ C * dist z₁ z₂)
    (hcont : ∀ z, ContinuousOn (fun s => G z s) (Set.Icc (0 : ℝ) T)) :
    ContinuousOn (fun p : Z × ℝ => G p.1 p.2) (Set.univ ×ˢ Set.Icc (0 : ℝ) T) := by
  rw [Metric.continuousOn_iff]
  rintro ⟨z₀, s₀⟩ ⟨_, hs₀⟩ ε hε
  obtain ⟨δ₁, hδ₁, hcs⟩ :=
    (Metric.continuousWithinAt_iff).mp (hcont z₀ s₀ hs₀) (ε/2) (by positivity)
  have hC1 : (0 : ℝ) < |C| + 1 := by positivity
  refine ⟨min δ₁ (ε / (2 * (|C| + 1))), by positivity, ?_⟩
  rintro ⟨z, s⟩ ⟨_, hs⟩ hd
  rw [Prod.dist_eq, max_lt_iff] at hd
  obtain ⟨hdz, hds⟩ := hd
  have hterm1 : dist (G z s) (G z₀ s) < ε/2 := by
    calc dist (G z s) (G z₀ s)
        ≤ C * dist z z₀ := hlip s hs z z₀
      _ ≤ (|C| + 1) * dist z z₀ :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) dist_nonneg
      _ < (|C| + 1) * (ε / (2 * (|C| + 1))) :=
          mul_lt_mul_of_pos_left (lt_of_lt_of_le hdz (min_le_right _ _)) hC1
      _ = ε/2 := by field_simp
  have hterm2 : dist (G z₀ s) (G z₀ s₀) < ε/2 :=
    hcs hs (lt_of_lt_of_le hds (min_le_left _ _))
  calc dist (G z s) (G z₀ s₀)
      ≤ dist (G z s) (G z₀ s) + dist (G z₀ s) (G z₀ s₀) := dist_triangle _ _ _
    _ < ε/2 + ε/2 := add_lt_add hterm1 hterm2
    _ = ε := by ring

/-- Generic Grönwall difference-quotient bound (open-interval ODE + `s₀→0⁺` limit).  Two curves
`uh, mh` that approximately solve the same linear ODE `w' = vlin·w` on `Ioo 0 T` from the same datum
(`uh 0 = mh 0`), with `mh` exact and `uh`'s defect uniformly `≤ εf`, satisfy
`dist (uh t) (mh t) ≤ gronwallBound 0 K εf t`.  `vlin` is abstract (kept opaque to avoid unfolding
the heavy `vlasovFieldJacobian` integral in the Grönwall application). -/
lemma gronwall_diffQuotient_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (vlin : ℝ → (E →L[ℝ] E)) (K : NNReal) (hvlin_lip : ∀ s, LipschitzWith K (vlin s))
    (uh mh Fuh : ℝ → E) (εf : ℝ) (T t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (huh_cont : ContinuousOn uh (Set.Icc 0 T)) (hmh_cont : ContinuousOn mh (Set.Icc 0 T))
    (huh_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt uh (Fuh s) s)
    (hmh_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt mh ((vlin s) (mh s)) s)
    (hdefect : ∀ s ∈ Set.Ioo (0 : ℝ) T, dist (Fuh s) (vlin s (uh s)) ≤ εf)
    (h0 : uh 0 = mh 0) :
    dist (uh t) (mh t) ≤ gronwallBound 0 (K:ℝ) εf t := by
  have hbound_s0 : ∀ s₀ ∈ Set.Ioo (0 : ℝ) t,
      dist (uh t) (mh t) ≤ gronwallBound (dist (uh s₀) (mh s₀)) (K:ℝ) εf (t - s₀) := by
    intro s₀ hs₀
    have hIco_sub : Set.Ico s₀ t ⊆ Set.Ioo 0 T := fun s hs =>
      ⟨lt_of_lt_of_le hs₀.1 hs.1, hs.2.trans ht.2⟩
    have hIcc_sub : Set.Icc s₀ t ⊆ Set.Icc 0 T := fun s hs =>
      ⟨le_trans hs₀.1.le hs.1, le_trans hs.2 ht.2.le⟩
    have key := dist_le_of_approx_trajectories_ODE (K := K)
      (εf := εf) (εg := 0) (δ := dist (uh s₀) (mh s₀))
      hvlin_lip (huh_cont.mono hIcc_sub)
      (fun s hs => (huh_deriv s (hIco_sub hs)).hasDerivWithinAt)
      (fun s hs => hdefect s (hIco_sub hs))
      (hmh_cont.mono hIcc_sub)
      (fun s hs => (hmh_deriv s (hIco_sub hs)).hasDerivWithinAt)
      (fun s _ => le_of_eq (dist_self _)) (le_refl _)
    have hkey := key t ⟨hs₀.2.le, le_refl t⟩
    simpa only [add_zero] using hkey
  have : (𝓝[Set.Ioo 0 t] (0 : ℝ)).NeBot := left_nhdsWithin_Ioo_neBot ht.1
  have hT0 : (0 : ℝ) ≤ T := le_trans ht.1.le ht.2.le
  have hsub_Icc : Set.Ioo (0 : ℝ) t ⊆ Set.Icc 0 T := fun s hs => ⟨hs.1.le, le_trans hs.2.le ht.2.le⟩
  have htend_uh : Tendsto uh (𝓝[Set.Ioo 0 t] 0) (𝓝 (uh 0)) :=
    (huh_cont 0 ⟨le_refl 0, hT0⟩).tendsto.mono_left (nhdsWithin_mono 0 hsub_Icc)
  have htend_mh : Tendsto mh (𝓝[Set.Ioo 0 t] 0) (𝓝 (mh 0)) :=
    (hmh_cont 0 ⟨le_refl 0, hT0⟩).tendsto.mono_left (nhdsWithin_mono 0 hsub_Icc)
  have htend_δ : Tendsto (fun s₀ => dist (uh s₀) (mh s₀)) (𝓝[Set.Ioo 0 t] 0) (𝓝 0) := by
    have := htend_uh.dist htend_mh
    rwa [h0, dist_self] at this
  have htend_x : Tendsto (fun s₀ : ℝ => t - s₀) (𝓝[Set.Ioo 0 t] 0) (𝓝 t) := by
    have h0' : Tendsto (fun s₀ : ℝ => t - s₀) (𝓝 0) (𝓝 (t - 0)) :=
      (continuous_const.sub continuous_id).tendsto 0
    rw [sub_zero] at h0'; exact h0'.mono_left nhdsWithin_le_nhds
  have hgb_cont : Continuous (fun p : ℝ × ℝ => gronwallBound p.1 (K:ℝ) εf p.2) := by
    by_cases hK : (K:ℝ) = 0
    · simp only [hK, gronwallBound_K0]; fun_prop
    · have heq : (fun p : ℝ × ℝ => gronwallBound p.1 (K:ℝ) εf p.2)
          = fun p => p.1 * Real.exp ((K:ℝ) * p.2) + εf / (K:ℝ) * (Real.exp ((K:ℝ) * p.2) - 1) := by
        funext p; rw [gronwallBound_of_K_ne_0 hK]
      rw [heq]; fun_prop
  have htend_gb : Tendsto (fun s₀ => gronwallBound (dist (uh s₀) (mh s₀)) (K:ℝ) εf (t - s₀))
      (𝓝[Set.Ioo 0 t] 0) (𝓝 (gronwallBound 0 (K:ℝ) εf t)) :=
    (hgb_cont.tendsto (0, t)).comp (htend_δ.prodMk_nhds htend_x)
  exact ge_of_tendsto htend_gb (eventually_nhdsWithin_of_forall (fun s₀ hs₀ => hbound_s0 s₀ hs₀))

/-- **Step 3 gating lemma (generic) — joint `C¹` from continuous partial derivatives** on a
`ℝ × E` domain (Mathlib-absent).  A partial `s`-derivative `Ds p` at every point (`Ds` continuous)
plus a partial `z`-derivative `Dz₀` at the base point ⇒ `f` is Fréchet-differentiable at `(s₀,z₀)`
with total derivative `(h,k) ↦ h•Ds(s₀,z₀) + Dz₀ k`.  Proof: split the increment into an
`s`-part (FTC `∫₀ʰ Ds(s₀+u,z₀+k)du ≈ h•Ds₀` by continuity of `Ds`) and a `z`-part
(`= Dz₀ k + o(k)`).
This is the keystone for the joint `(s,w)` regularity of the two-time flow `Φ_{s→t}`: the flow's
partials are `M_s z` (jointly continuous, V2) in `z` and `b_s(Φ_s z)` in `s`.

**PR-ABLE (Mathlib upstream candidate).**  This is a general real-analysis result with no Vlasov
content — "a function on `ℝ × E` with a continuous partial derivative in the `ℝ` factor and a
Fréchet partial derivative in the `E` factor is Fréchet-differentiable" — filling a genuine gap in
`Mathlib/Analysis/Calculus`.  Generalisation worth doing before a PR: replace the `ℝ` factor by an
arbitrary first factor with an analogous "integrate the partial along segments" hypothesis, and
weaken `Continuous Ds` to `ContinuousAt Ds` at the base point (the proof only uses a neighbourhood
of `(s₀,z₀)`). -/
theorem hasFDerivAt_of_continuous_partials
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ × E → F} {Ds : ℝ × E → F} {Dz₀ : E →L[ℝ] F} (s₀ : ℝ) (z₀ : E)
    (hDs : ∀ p : ℝ × E, HasDerivAt (fun s => f (s, p.2)) (Ds p) p.1)
    (hDs_cont : Continuous Ds)
    (hDz₀ : HasFDerivAt (fun z => f (s₀, z)) Dz₀ z₀) :
    HasFDerivAt f
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (Ds (s₀, z₀))
        + Dz₀.comp (ContinuousLinearMap.snd ℝ ℝ E)) (s₀, z₀) := by
  set Ds₀ : F := Ds (s₀, z₀) with hDs₀
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  have hBz : ∀ᶠ k in 𝓝 (0 : E),
      ‖f (s₀, z₀ + k) - f (s₀, z₀) - Dz₀ k‖ ≤ (ε / 2) * ‖k‖ := by
    have hz := hDz₀
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff] at hz
    exact hz (half_pos hε)
  have hBz' : ∀ᶠ p : ℝ × E in 𝓝 0,
      ‖f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2‖ ≤ (ε / 2) * ‖p.2‖ :=
    (continuous_snd.tendsto (0 : ℝ × E)).eventually hBz
  have hball : ∀ᶠ q in 𝓝 ((s₀, z₀) : ℝ × E), ‖Ds q - Ds₀‖ ≤ ε / 2 := by
    have hc : Tendsto Ds (𝓝 (s₀, z₀)) (𝓝 Ds₀) := hDs_cont.continuousAt
    have hsub : Tendsto (fun q => Ds q - Ds₀) (𝓝 (s₀, z₀)) (𝓝 (Ds₀ - Ds₀)) :=
      hc.sub tendsto_const_nhds
    rw [sub_self] at hsub
    have h0 : Tendsto (fun q => ‖Ds q - Ds₀‖) (𝓝 (s₀, z₀)) (𝓝 0) := by
      simpa using hsub.norm
    exact h0.eventually (Iic_mem_nhds (half_pos hε))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hball
  have hAs : ∀ᶠ p : ℝ × E in 𝓝 0,
      ‖f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀‖ ≤ (ε / 2) * ‖p‖ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ × E) hδpos] with p hp
    rw [mem_ball_zero_iff] at hp
    have hcont_u : Continuous (fun u => Ds (u, z₀ + p.2)) :=
      hDs_cont.comp (continuous_id.prodMk continuous_const)
    have hg_deriv : ∀ u : ℝ, HasDerivAt (fun s => f (s, z₀ + p.2)) (Ds (u, z₀ + p.2)) u :=
      fun u => hDs (u, z₀ + p.2)
    have hftc : ∫ u in s₀..(s₀ + p.1), Ds (u, z₀ + p.2)
        = f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hg_deriv u)
        (hcont_u.intervalIntegrable _ _)]
    have hbound_u : ∀ u ∈ Set.uIoc s₀ (s₀ + p.1), ‖Ds (u, z₀ + p.2) - Ds₀‖ ≤ ε / 2 := by
      intro u hu
      refine @hδ (u, z₀ + p.2) ?_
      have hple : |p.1| ≤ ‖p‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le p
      have hp1 : |u - s₀| ≤ ‖p‖ := by
        rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hu) with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - s₀)]
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1)] at hple; linarith
        · rw [abs_of_nonpos (by linarith : u - s₀ ≤ 0)]
          rw [abs_of_nonpos (by linarith : p.1 ≤ 0)] at hple; linarith
      have hp2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
      rw [Prod.dist_eq]
      simp only [dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs]
      exact lt_of_le_of_lt (max_le hp1 hp2) hp
    have hA_eq : f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀
        = ∫ u in s₀..(s₀ + p.1), (Ds (u, z₀ + p.2) - Ds₀) := by
      rw [intervalIntegral.integral_sub (hcont_u.intervalIntegrable _ _)
          (intervalIntegrable_const), hftc, intervalIntegral.integral_const,
          add_sub_cancel_left]
    rw [hA_eq]
    calc ‖∫ u in s₀..(s₀ + p.1), (Ds (u, z₀ + p.2) - Ds₀)‖
        ≤ (ε / 2) * |(s₀ + p.1) - s₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound_u
      _ = (ε / 2) * ‖p.1‖ := by rw [add_sub_cancel_left, Real.norm_eq_abs]
      _ ≤ (ε / 2) * ‖p‖ := mul_le_mul_of_nonneg_left (norm_fst_le p) (by positivity)
  filter_upwards [hAs, hBz'] with p hAp hBp
  have hdecomp :
      f ((s₀, z₀) + p) - f (s₀, z₀)
        - ((ContinuousLinearMap.fst ℝ ℝ E).smulRight Ds₀
            + Dz₀.comp (ContinuousLinearMap.snd ℝ ℝ E)) p
      = (f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀)
        + (f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2) := by
    rw [show ((s₀, z₀) + p : ℝ × E) = (s₀ + p.1, z₀ + p.2) from rfl]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd']
    abel
  rw [hdecomp]
  calc ‖(f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀)
          + (f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2)‖
      ≤ ‖f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀‖
        + ‖f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2‖ := norm_add_le _ _
    _ ≤ (ε / 2) * ‖p‖ + (ε / 2) * ‖p‖ :=
        add_le_add hAp (le_trans hBp (mul_le_mul_of_nonneg_left (norm_snd_le p) (by positivity)))
    _ = ε * ‖p‖ := by ring

/-- **Step 3 gating lemma (LOCAL / open-set form)** — joint `HasFDerivAt` from continuous partial
derivatives on an open set `U ⊆ ℝ × E`.  The open-set generalisation of
`hasFDerivAt_of_continuous_partials` (which is the `U := univ` special case) that the PR-note above
flagged: the `s`-partial is required only on `U`, and `Ds` only `ContinuousOn U`.  This is the form
the Vlasov flow needs — its partials exist and are continuous only on the open window
`Ioo 0 T ×ˢ univ`.  Proof = the global proof + ball-in-`U` bookkeeping (`B((s₀,z₀),r) ⊆ U`; the FTC
segment points `(u, z₀+p.2)`, `u ∈ uIcc s₀ (s₀+p.1)`, lie within `‖p‖ < min δ (r/2)` of `(s₀,z₀)`,
hence in `U` and within the continuity radius `δ`).

NOTE (consolidation TODO): the global `hasFDerivAt_of_continuous_partials` above is the `univ`
special case of this; a follow-up cleanup should rewrite it as the one-line corollary
`hasFDerivAt_of_continuous_partials_open isOpen_univ (Set.mem_univ _) (fun p _ => hDs p)
hDs_cont.continuousOn hDz₀` to drop the duplicated proof.  **PR-ABLE** (the more
general statement). -/
theorem hasFDerivAt_of_continuous_partials_open
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ × E → F} {Ds : ℝ × E → F} {Dz₀ : E →L[ℝ] F}
    {U : Set (ℝ × E)} (hU : IsOpen U) {s₀ : ℝ} {z₀ : E} (hmem : (s₀, z₀) ∈ U)
    (hDs : ∀ p ∈ U, HasDerivAt (fun s => f (s, p.2)) (Ds p) p.1)
    (hDs_cont : ContinuousOn Ds U)
    (hDz₀ : HasFDerivAt (fun z => f (s₀, z)) Dz₀ z₀) :
    HasFDerivAt f
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (Ds (s₀, z₀))
        + Dz₀.comp (ContinuousLinearMap.snd ℝ ℝ E)) (s₀, z₀) := by
  set Ds₀ : F := Ds (s₀, z₀) with hDs₀
  obtain ⟨r, hrpos, hrU⟩ := Metric.isOpen_iff.mp hU (s₀, z₀) hmem
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  have hBz : ∀ᶠ k in 𝓝 (0 : E),
      ‖f (s₀, z₀ + k) - f (s₀, z₀) - Dz₀ k‖ ≤ (ε / 2) * ‖k‖ := by
    have hz := hDz₀
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff] at hz
    exact hz (half_pos hε)
  have hBz' : ∀ᶠ p : ℝ × E in 𝓝 0,
      ‖f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2‖ ≤ (ε / 2) * ‖p.2‖ :=
    (continuous_snd.tendsto (0 : ℝ × E)).eventually hBz
  have hball : ∀ᶠ q in 𝓝 ((s₀, z₀) : ℝ × E), ‖Ds q - Ds₀‖ ≤ ε / 2 := by
    have hc : Tendsto Ds (𝓝 (s₀, z₀)) (𝓝 Ds₀) := hDs_cont.continuousAt (hU.mem_nhds hmem)
    have hsub : Tendsto (fun q => Ds q - Ds₀) (𝓝 (s₀, z₀)) (𝓝 (Ds₀ - Ds₀)) :=
      hc.sub tendsto_const_nhds
    rw [sub_self] at hsub
    have h0 : Tendsto (fun q => ‖Ds q - Ds₀‖) (𝓝 (s₀, z₀)) (𝓝 0) := by
      simpa using hsub.norm
    exact h0.eventually (Iic_mem_nhds (half_pos hε))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hball
  set ρr : ℝ := min δ (r / 2) with hρr
  have hρrpos : 0 < ρr := lt_min hδpos (by positivity)
  have hAs : ∀ᶠ p : ℝ × E in 𝓝 0,
      ‖f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀‖ ≤ (ε / 2) * ‖p‖ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ × E) hρrpos] with p hp
    rw [mem_ball_zero_iff] at hp
    have hdist : ∀ u ∈ Set.uIcc s₀ (s₀ + p.1),
        dist ((u, z₀ + p.2) : ℝ × E) (s₀, z₀) ≤ ‖p‖ := by
      intro u hu
      have hple : |p.1| ≤ ‖p‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le p
      have hp1 : |u - s₀| ≤ ‖p‖ := by
        rcases Set.mem_uIcc.mp hu with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - s₀)]
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1)] at hple; linarith
        · rw [abs_of_nonpos (by linarith : u - s₀ ≤ 0)]
          rw [abs_of_nonpos (by linarith : p.1 ≤ 0)] at hple; linarith
      have hp2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
      rw [Prod.dist_eq]
      refine max_le ?_ ?_
      · rw [dist_eq_norm]; simpa [Real.norm_eq_abs] using hp1
      · rw [dist_eq_norm, add_sub_cancel_left]; exact hp2
    have hmemU : ∀ u ∈ Set.uIcc s₀ (s₀ + p.1), ((u, z₀ + p.2) : ℝ × E) ∈ U := by
      intro u hu
      apply hrU
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (hdist u hu)
        (lt_of_lt_of_le hp (le_trans (min_le_right _ _) (by linarith)))
    have hcont_u : ContinuousOn (fun u => Ds (u, z₀ + p.2)) (Set.uIcc s₀ (s₀ + p.1)) := by
      refine hDs_cont.comp (continuous_id.prodMk continuous_const).continuousOn ?_
      exact fun u hu => hmemU u hu
    have hg_deriv : ∀ u ∈ Set.uIcc s₀ (s₀ + p.1),
        HasDerivAt (fun s => f (s, z₀ + p.2)) (Ds (u, z₀ + p.2)) u :=
      fun u hu => hDs (u, z₀ + p.2) (hmemU u hu)
    have hftc : ∫ u in s₀..(s₀ + p.1), Ds (u, z₀ + p.2)
        = f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hg_deriv u hu)
        (hcont_u.intervalIntegrable)]
    have hbound_u : ∀ u ∈ Set.uIoc s₀ (s₀ + p.1), ‖Ds (u, z₀ + p.2) - Ds₀‖ ≤ ε / 2 := by
      intro u hu
      refine @hδ (u, z₀ + p.2) ?_
      have hmem' := hdist u (Set.uIoc_subset_uIcc hu)
      exact lt_of_le_of_lt hmem' (lt_of_lt_of_le hp (min_le_left _ _))
    have hA_eq : f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀
        = ∫ u in s₀..(s₀ + p.1), (Ds (u, z₀ + p.2) - Ds₀) := by
      rw [intervalIntegral.integral_sub (hcont_u.intervalIntegrable)
          (intervalIntegrable_const), hftc, intervalIntegral.integral_const,
          add_sub_cancel_left]
    rw [hA_eq]
    calc ‖∫ u in s₀..(s₀ + p.1), (Ds (u, z₀ + p.2) - Ds₀)‖
        ≤ (ε / 2) * |(s₀ + p.1) - s₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound_u
      _ = (ε / 2) * ‖p.1‖ := by rw [add_sub_cancel_left, Real.norm_eq_abs]
      _ ≤ (ε / 2) * ‖p‖ := mul_le_mul_of_nonneg_left (norm_fst_le p) (by positivity)
  filter_upwards [hAs, hBz'] with p hAp hBp
  have hdecomp :
      f ((s₀, z₀) + p) - f (s₀, z₀)
        - ((ContinuousLinearMap.fst ℝ ℝ E).smulRight Ds₀
            + Dz₀.comp (ContinuousLinearMap.snd ℝ ℝ E)) p
      = (f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀)
        + (f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2) := by
    rw [show ((s₀, z₀) + p : ℝ × E) = (s₀ + p.1, z₀ + p.2) from rfl]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd']
    abel
  rw [hdecomp]
  calc ‖(f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀)
          + (f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2)‖
      ≤ ‖f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀‖
        + ‖f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2‖ := norm_add_le _ _
    _ ≤ (ε / 2) * ‖p‖ + (ε / 2) * ‖p‖ :=
        add_le_add hAp (le_trans hBp (mul_le_mul_of_nonneg_left (norm_snd_le p) (by positivity)))
    _ = ε * ‖p‖ := by ring

end Vlasov
