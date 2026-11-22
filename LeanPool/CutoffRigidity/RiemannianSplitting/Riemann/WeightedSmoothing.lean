/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedLocalSmooth
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedGradHelpers
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-! # Global smoothing of a 1-Lipschitz function with bounded gradient -/

@[expose] public section

open Bundle MeasureTheory Filter Set Manifold
open scoped Manifold ContDiff ENNReal Topology


namespace CutCur

section Smoothing

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M]

/-- A geometric series bound over finite sets of naturals. -/
theorem sum_half_pow_succ_le (T : Finset ℕ) : ∑ k ∈ T, (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := by
  have h := sum_le_hasSum T (fun _ _ => by positivity) hasSum_geometric_two
  have : ∑ k ∈ T, (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) * ∑ k ∈ T, (1 / 2 : ℝ) ^ k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [this]; linarith

include F

/-- **Smoothing of a 1-Lipschitz function**: there is a smooth `g` with `|g - f| ≤ 1` and
`‖∇g‖ ≤ 5`. -/
theorem exists_smooth_lip_approx [SigmaCompactSpace M] (hfin : ∀ x y : M, edist x y ≠ ⊤)
    {f : M → ℝ} (hf : LipschitzWith 1 f) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g ∧ (∀ x, |g x - f x| ≤ 1) ∧
      ∀ x, ‖mgrad F g x‖ ≤ 5 := by
  let : IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := 𝓘(ℝ, F)) (n := ∞)
  choose V hVo hpV hK hloc using exists_local_smooth F hfin hf
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (ι := M) 𝓘(ℝ, F)
    isClosed_univ V hVo (fun x _ => mem_iUnion.2 ⟨x, hpV x⟩)
  have hts : ∀ i, IsCompact (tsupport (ρ i)) := fun i => by
    obtain ⟨K, hKc, hKV⟩ := hK i
    exact hKc.of_isClosed_subset (isClosed_tsupport _) ((hρ i).trans hKV)
  have hC : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ tsupport (ρ i), ‖mgrad F (ρ i) x‖ ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := (hts i).exists_bound_of_continuousOn
      (f := fun x => ‖mgrad F (ρ i) x‖)
      (continuous_norm_mgrad F (ρ i).contMDiff).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun x hx => by
      have := hC x hx
      rw [norm_norm] at this
      exact this.trans (le_max_left _ _)⟩
  choose C hC0 hCb using hC
  have hcount : Countable {i : M // (Function.support (ρ i)).Nonempty} := by
    have hlf := (ρ.locallyFinite).comp_injective
      (Subtype.val_injective (p := fun i : M => (Function.support (ρ i)).Nonempty))
    exact (Set.countable_univ_iff.1 (hlf.countable_univ (fun i => i.2)))
  classical
  obtain ⟨nn, hnn⟩ := hcount.exists_injective_nat
  let n : M → ℕ := fun i => if h : (Function.support (ρ i)).Nonempty then nn ⟨i, h⟩ else 0
  have hn_inj : ∀ i j, (Function.support (ρ i)).Nonempty → (Function.support (ρ j)).Nonempty →
      n i = n j → i = j := by
    intro i j hi hj hij
    have e1 : n i = nn ⟨i, hi⟩ := by simp only [n]; exact dite_eq_left hi
    have e2 : n j = nn ⟨j, hj⟩ := by simp only [n]; exact dite_eq_left hj
    rw [e1, e2] at hij
    exact congrArg Subtype.val (hnn hij)
  set δ : M → ℝ := fun i => (1 / 2 : ℝ) ^ (n i + 1) / (C i + 1) with hδ
  have hδpos : ∀ i, 0 < δ i := fun i => by
    have := hC0 i
    simp only [hδ]; positivity
  have hδle : ∀ i, δ i ≤ 1 / 2 := fun i => by
    have := hC0 i
    have h1 : (1 / 2 : ℝ) ^ (n i + 1) ≤ 1 / 2 := by
      calc (1 / 2 : ℝ) ^ (n i + 1) ≤ (1 / 2) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := by norm_num
    simp only [hδ]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) (n i + 1)]
  have hδC : ∀ i, δ i * C i ≤ (1 / 2 : ℝ) ^ (n i + 1) := fun i => by
    have := hC0 i
    simp only [hδ]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) (n i + 1)]
  choose g hgs hgv hgd using fun i => hloc i (δ i) (hδpos i)
  set ψ : M → ℝ := fun x => ∑ᶠ i, ρ i x * g i x with hψ
  have hψsm : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ ψ := by
    have := ρ.contMDiff_finsum_smul (n := (⊤ : ℕ∞)) (g := g) (fun i x hx => hgs i x (hρ i hx))
    simpa [smul_eq_mul] using this
  have hmemS : ∀ x₀ i, ρ i x₀ ≠ 0 → i ∈ ρ.fintsupport x₀ := fun x₀ i hi =>
    (ρ.mem_fintsupport_iff x₀ i).2 (subset_tsupport _ hi)
  have hloc' : ∀ x₀, ∀ᶠ y in 𝓝 x₀, ∀ i, ρ i y ≠ 0 → i ∈ ρ.fintsupport x₀ := by
    intro x₀
    filter_upwards [ρ.eventually_fintsupport_subset x₀] with y hy i hi
    exact hy (hmemS y i hi)
  have hψeq : ∀ x₀ y, (∀ i, ρ i y ≠ 0 → i ∈ ρ.fintsupport x₀) →
      ψ y = ∑ i ∈ ρ.fintsupport x₀, ρ i y * g i y := by
    intro x₀ y hy
    exact finsum_eq_sum_of_support_subset _ (fun i hi => hy i (left_ne_zero_of_mul hi))
  have hsum1 : ∀ x₀ y, (∀ i, ρ i y ≠ 0 → i ∈ ρ.fintsupport x₀) →
      ∑ i ∈ ρ.fintsupport x₀, ρ i y = 1 := by
    intro x₀ y hy
    rw [← finsum_eq_sum_of_support_subset (s := ρ.fintsupport x₀) _ (fun i hi => hy i hi)]
    exact ρ.sum_eq_one (mem_univ y)
  refine ⟨ψ, hψsm, ?_, ?_⟩
  · intro x₀
    set S := ρ.fintsupport x₀ with hSdef
    have hS : ∀ i, ρ i x₀ ≠ 0 → i ∈ S := hmemS x₀
    have h1 := hsum1 x₀ x₀ hS
    rw [hψeq x₀ x₀ hS]
    have e : ∑ i ∈ S, ρ i x₀ * g i x₀ - f x₀ = ∑ i ∈ S, ρ i x₀ * (g i x₀ - f x₀) := by
      rw [Finset.sum_congr rfl (fun i _ => mul_sub (ρ i x₀) (g i x₀) (f x₀)),
        Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
    rw [e]
    calc |∑ i ∈ S, ρ i x₀ * (g i x₀ - f x₀)|
        ≤ ∑ i ∈ S, |ρ i x₀ * (g i x₀ - f x₀)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ S, ρ i x₀ * 1 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg (ρ.nonneg i x₀)]
        have hxV : x₀ ∈ V i := hρ i ((ρ.mem_fintsupport_iff x₀ i).1 hi)
        exact mul_le_mul_of_nonneg_left
          ((hgv i x₀ hxV).trans ((hδle i).trans (by norm_num))) (ρ.nonneg i x₀)
      _ = 1 := by rw [← Finset.sum_mul, h1, one_mul]
  · intro x₀
    set S := ρ.fintsupport x₀ with hSdef
    have hev := hloc' x₀
    have hxS : ∀ i ∈ S, x₀ ∈ tsupport (ρ i) := fun i hi => (ρ.mem_fintsupport_iff x₀ i).1 hi
    have hdρ : ∀ i, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (ρ i) x₀ := fun i =>
      ((ρ i).contMDiff.mdifferentiable (by simp)) x₀
    have hdg : ∀ i ∈ S, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (g i) x₀ := fun i hi =>
      (hgs i x₀ (hρ i (hxS i hi))).mdifferentiableAt (by simp)
    have hψφ : ψ =ᶠ[𝓝 x₀] fun y => ∑ i ∈ S, ρ i y * g i y := by
      filter_upwards [hev] with y hy using hψeq x₀ y hy
    have h1ev : (fun y => ∑ i ∈ S, ρ i y) =ᶠ[𝓝 x₀] fun _ => (1 : ℝ) := by
      filter_upwards [hev] with y hy using hsum1 x₀ y hy
    have hd1 : ∑ i ∈ S, mvfderiv 𝓘(ℝ, F) (ρ i) x₀ = 0 := by
      rw [← mvfderiv_finset_sum F S (fun i => ρ i) (fun i _ => hdρ i),
        mvfderiv_congr_ev F h1ev, mvfderiv_const]
    have hdψ : mvfderiv 𝓘(ℝ, F) ψ x₀ =
        ∑ i ∈ S, (ρ i x₀ • mvfderiv 𝓘(ℝ, F) (g i) x₀ + g i x₀ • mvfderiv 𝓘(ℝ, F) (ρ i) x₀) := by
      rw [mvfderiv_congr_ev F hψφ,
        mvfderiv_finset_sum F S (fun i y => ρ i y * g i y) (fun i hi => (hdρ i).mul (hdg i hi))]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      exact mvfderiv_fun_mul (hdρ i) (hdg i hi)
    apply norm_mgrad_le_of F (by norm_num)
    intro v
    have hv1 : ∑ i ∈ S, mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v = 0 := by
      have := congrArg (fun L => L v) hd1
      simpa [sum_apply] using this
    have hdψv : mvfderiv 𝓘(ℝ, F) ψ x₀ v = ∑ i ∈ S, ρ i x₀ * mvfderiv 𝓘(ℝ, F) (g i) x₀ v +
        ∑ i ∈ S, (g i x₀ - f x₀) * mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v := by
      rw [hdψ, sum_apply]
      have : ∑ i ∈ S, (g i x₀ - f x₀) * mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v =
          ∑ i ∈ S, g i x₀ * mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v -
            f x₀ * ∑ i ∈ S, mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [this, hv1, mul_zero, sub_zero, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by simp)
    have hsum1' : ∑ i ∈ S, ρ i x₀ = 1 := hsum1 x₀ x₀ (hmemS x₀)
    have hne : ∀ i ∈ S, (Function.support (ρ i)).Nonempty := fun i hi => by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have := hxS i hi
      simp [tsupport, h] at this
    have hinj : Set.InjOn n (S : Set M) := fun i hi j hj hij => hn_inj i j (hne i hi) (hne j hj) hij
    have hgeo : ∑ i ∈ S, (1 / 2 : ℝ) ^ (n i + 1) ≤ 1 := by
      rw [← Finset.sum_image (f := fun k => (1 / 2 : ℝ) ^ (k + 1)) hinj]
      exact sum_half_pow_succ_le _
    have hA : |∑ i ∈ S, ρ i x₀ * mvfderiv 𝓘(ℝ, F) (g i) x₀ v| ≤ 4 * ‖v‖ := by
      calc _ ≤ ∑ i ∈ S, |ρ i x₀ * mvfderiv 𝓘(ℝ, F) (g i) x₀ v| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ S, ρ i x₀ * (4 * ‖v‖) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_of_nonneg (ρ.nonneg i x₀)]
          exact mul_le_mul_of_nonneg_left
            (hgd i x₀ (hρ i (hxS i hi)) v) (ρ.nonneg i x₀)
        _ = 4 * ‖v‖ := by rw [← Finset.sum_mul, hsum1', one_mul]
    have hB : |∑ i ∈ S, (g i x₀ - f x₀) * mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v| ≤ 1 * ‖v‖ := by
      calc _ ≤ ∑ i ∈ S, |(g i x₀ - f x₀) * mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ S, (1 / 2 : ℝ) ^ (n i + 1) * ‖v‖ := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul]
          have h1 : |g i x₀ - f x₀| ≤ δ i := hgv i x₀ (hρ i (hxS i hi))
          have h2 : |mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v| ≤ C i * ‖v‖ :=
            (abs_mvfderiv_le_norm_mgrad F (ρ i) x₀ v).trans
              (mul_le_mul_of_nonneg_right (hCb i x₀ (hxS i hi)) (norm_nonneg _))
          calc |g i x₀ - f x₀| * |mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v|
              ≤ δ i * (C i * ‖v‖) :=
                mul_le_mul h1 h2 (abs_nonneg _) (hδpos i).le
            _ = (δ i * C i) * ‖v‖ := by ring
            _ ≤ (1 / 2 : ℝ) ^ (n i + 1) * ‖v‖ :=
                mul_le_mul_of_nonneg_right (hδC i) (norm_nonneg _)
        _ = (∑ i ∈ S, (1 / 2 : ℝ) ^ (n i + 1)) * ‖v‖ := by rw [Finset.sum_mul]
        _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hgeo (norm_nonneg _)
    rw [hdψv]
    calc _ ≤ |∑ i ∈ S, ρ i x₀ * mvfderiv 𝓘(ℝ, F) (g i) x₀ v| +
          |∑ i ∈ S, (g i x₀ - f x₀) * mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v| := abs_add_le _ _
      _ ≤ 4 * ‖v‖ + 1 * ‖v‖ := add_le_add hA hB
      _ = 5 * ‖v‖ := by ring

end Smoothing

end CutCur
