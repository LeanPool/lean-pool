/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AbPh project (AI-generated Lean proofs)
-/

-- Modified for Lean Pool: adapted the module name and imports.

module

public import LeanPool.VenNullClockRoundRates.LocalMaskGram
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Discharge moment independence and continuity in the concrete exponential
measurement family. A finite Vandermonde argument lives inside a regular
angular image patch. Bounded convergence is applied to unperturbed moments. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology
namespace VenMask
private theorem separating_slope {n : ℕ} (x s : Fin n → ℝ)
    (h : Function.Injective fun i ↦ (x i, s i)) :
    ∃ t : ℝ, Function.Injective (fun i ↦ x i + s i * t) := by
  let bad := fun ij : Fin n × Fin n ↦ (x ij.2 - x ij.1) / (s ij.1 - s ij.2)
  obtain ⟨t, ht⟩ := (Set.finite_range bad).exists_notMem
  refine ⟨t, fun i j hij ↦ ?_⟩
  by_cases hs : s i = s j
  · apply h
    exact Prod.ext (by simpa [hs] using hij) hs
  · exfalso
    apply ht
    refine ⟨(i,j), ?_⟩
    change (x j - x i) / (s i - s j) = t
    apply (div_eq_iff (sub_ne_zero.mpr hs)).mpr
    linarith only [hij]

private theorem kernel_indep {Ω : Type} [TopologicalSpace Ω] [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [μ.IsOpenPosMeasure]
    (x s : Fin n → ℝ) (F G : Ω → ℝ)
    (hmenu : Function.Injective fun i ↦ (x i, s i))
    (hpatch : ∃ p : ℝ × ℝ, Set.range (fun y ↦ (F y, G y)) ∈ 𝓝 p)
    (hF : Continuous F) (hG : Continuous G) :
    AEIndependent μ (kernel x s F G) := by
  intro c hzero
  have hc : Continuous (synthesis (kernel x s F G) c) := by
    unfold synthesis kernel; fun_prop
  have eqn := μ.eq_of_ae_eq hzero hc continuous_zero
  obtain ⟨t, ht⟩ := separating_slope x s hmenu
  obtain ⟨p, hp⟩ := hpatch
  let line := fun (a : ℝ) (j : Fin n) ↦ (p.1 + a * j.val, p.2 + t * a * j.val)
  have inPatch (j : Fin n) : ∀ᶠ a in 𝓝 (0 : ℝ), line a j ∈ Set.range (fun y ↦ (F y,G y)) := by
    have hlin : ContinuousAt (fun a ↦ line a j) 0 := by unfold line; fun_prop
    have h0 : line 0 j = p := by simp [line]
    exact (h0 ▸ hlin.tendsto : Tendsto (fun a ↦ line a j) (𝓝 0) (𝓝 p)) hp
  have hall := (eventually_all.mpr inPatch).filter_mono
    (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 0)
  have hpos : ∀ᶠ a in 𝓝[Set.Ioi (0 : ℝ)] 0, 0 < a := self_mem_nhdsWithin
  obtain ⟨a, ha, hal⟩ := (hpos.and hall).exists
  change 0 < a at ha
  let base := fun i ↦ Real.exp (a * (x i + s i * t))
  let intercept := fun i ↦ Real.exp (x i * p.1 + s i * p.2)
  have hinj : Function.Injective base := fun i j h ↦
    ht <| mul_left_cancel₀ ha.ne' (Real.exp_injective h)
  have heq (j : Fin n) : ∑ i, (c i * intercept i) * (base i)^(j : ℕ) = 0 := by
    obtain ⟨y, hy⟩ := hal j
    have hf := congrArg Prod.fst hy
    have hg := congrArg Prod.snd hy
    change F y = p.1 + a*j.val at hf
    change G y = p.2 + t*a*j.val at hg
    have ev := congrFun eqn y
    change ∑ i, c i * Real.exp (x i * F y + s i * G y) = 0 at ev
    rw [← ev]; apply Finset.sum_congr rfl; intro i _
    rw [hf, hg]
    have ar : x i * (p.1 + a * j.val) + s i * (p.2 + t * a * j.val) =
        x i * p.1 + s i * p.2 + (j.val : ℝ) * (a * (x i + s i * t)) := by ring
    rw [ar, Real.exp_add, Real.exp_nat_mul]
    simp [base, intercept, mul_assoc]
  have hz := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj heq
  funext i
  exact (mul_eq_zero.mp (congrFun hz i)).resolve_right (Real.exp_ne_zero _)
/-- Every distinct fixed finite menu of these scalar exponential readings is
locally maskable under the regular angular-image hypotheses. The *same* chosen
multiplier matches every read at the perturbed parameter. -/
theorem exponential_local_masking : ExponentialMaskingCertificate := by
  intro Ω Z _ _ _ _ _ n μ _ _ x s F G z₀ w₀ hw hm hp hc hparam he
  let k := fun z ↦ kernel x s (F z) (G z)
  let B := ∑ i, Real.exp (|x i| + |s i|)
  have hk (z : Z) (i : Fin n) : Continuous (k z i) := by
    obtain ⟨hf,hg⟩ := hc z
    unfold k kernel; fun_prop
  have hkpar (y : Ω) (i : Fin n) : ContinuousAt (fun z ↦ k z i y) z₀ := by
    obtain ⟨hf,hg⟩ := hparam y
    unfold k kernel; fun_prop
  have hB (z : Z) (i : Fin n) (y : Ω) : |k z i y| ≤ B := by
    dsimp [k,kernel]; rw [abs_of_pos (Real.exp_pos _)]
    apply le_trans _ (Finset.single_le_sum (f := fun i ↦ Real.exp (|x i| + |s i|))
      (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i))
    apply Real.exp_le_exp.mpr; apply add_le_add
    · calc x i * F z y ≤ |x i * F z y| := le_abs_self _
           _ = |x i| * |F z y| := abs_mul _ _
           _ ≤ |x i| * 1 := mul_le_mul_of_nonneg_left (he z y).1 (abs_nonneg _)
           _ = _ := mul_one _
    · calc s i * G z y ≤ |s i * G z y| := le_abs_self _
           _ = |s i| * |G z y| := abs_mul _ _
           _ ≤ |s i| * 1 := mul_le_mul_of_nonneg_left (he z y).2 (abs_nonneg _)
           _ = _ := mul_one _
  have hBpos : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ (Real.exp_pos _).le
  have pb (z : Z) (i j : Fin n) (y : Ω) : ‖k z j y * k z i y‖ ≤ B * B := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hB z j y) (hB z i y) (abs_nonneg _) hBpos
  apply local_masking μ k z₀ w₀ B hw (.of_forall hB)
  · exact .of_forall fun z i ↦ Integrable.of_bound (hk z i).aestronglyMeasurable B
      (ae_of_all _ fun y ↦ hB z i y)
  · exact .of_forall fun z i j ↦ Integrable.of_bound
      ((hk z j).mul (hk z i)).aestronglyMeasurable (B*B) (ae_of_all _ (pb z i j))
  · exact kernel_indep μ x s (F z₀) (G z₀) hm hp (hc _).1 (hc _).2
  · apply continuousAt_pi.mpr; intro i; apply continuousAt_pi.mpr; intro j
    apply continuousAt_of_dominated (bound := fun _ ↦ B*B)
      (.of_forall fun z ↦ ((hk z j).mul (hk z i)).aestronglyMeasurable)
      (.of_forall fun z ↦ ae_of_all _ (pb z i j)) (integrable_const _)
    exact ae_of_all _ fun y ↦ (hkpar y j).mul (hkpar y i)
  · apply continuousAt_pi.mpr; intro i
    apply continuousAt_of_dominated (bound := fun _ ↦ |w₀| * B)
      (.of_forall fun z ↦ (continuous_const.mul (hk z i)).aestronglyMeasurable)
      (.of_forall fun z ↦ ae_of_all _ fun y ↦ ?_) (integrable_const _)
      (ae_of_all _ fun y ↦ continuousAt_const.mul (hkpar y i))
    change |w₀ * k z i y| ≤ |w₀| * B
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB z i y) (abs_nonneg _)
end VenMask
