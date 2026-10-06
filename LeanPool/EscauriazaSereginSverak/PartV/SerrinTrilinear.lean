/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossIdentity

/-!
# Vanishing of transport trilinear forms

For a weakly divergence-free field `b`, the transport form
`∫ bⱼ (∂ⱼ fₖ gₖ + fₖ ∂ⱼ gₖ)` vanishes whenever the products involved are
integrable. The proof tests the weak product rule for `bⱼ fₖ` with cut-off
mollifications of `g` and passes to the limit. These identities reduce the
cross-testing identity to the relative energy inequality in
`lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem serrin_const_tendsto {F : Vec3 → ℝ} {r : ℝ≥0∞} :
    Tendsto (fun _ : ℕ => eLpNorm (fun x => F x - F x) r volume) atTop (𝓝 0) := by
  simp

/-- The transport trilinear form of a weakly divergence-free field vanishes. -/
theorem serrin_trilinear_vanish {b f g : Vec3 → Vec3} {Db Df Dg : Vec3 → Fin 3 → Vec3}
    (hb2 : MemLp b 2 volume) (hDb2 : MemLp Db 2 volume)
    (hbgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => b x i) (fun x => Db x i))
    (hbtr : ∀ᵐ x ∂volume, ∑ j : Fin 3, Db x j j = 0)
    (hf2 : MemLp f 2 volume) (hDf2 : MemLp Df 2 volume)
    (hfgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => f x i) (fun x => Df x i))
    (hg2 : MemLp g 2 volume) (hDg2 : MemLp Dg 2 volume)
    (hggrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => g x i) (fun x => Dg x i))
    {r s : ℝ≥0∞} [ENNReal.HolderTriple r s 1] (hs : 1 ≤ s) (hstop : s ≠ ⊤)
    (hbf : ∀ j k : Fin 3, MemLp (fun x => b x j * f x k) 2 volume)
    (hbDf : ∀ j k : Fin 3, MemLp (fun x => b x j * Df x k j) r volume)
    (hg : ∀ k : Fin 3, MemLp (fun x => g x k) s volume) :
    ∫ x : Vec3, ∑ k : Fin 3, ∑ j : Fin 3, b x j * (Df x k j * g x k + f x k * Dg x k j) = 0 := by
  set M : (Vec3 → ℝ) → ℕ → Vec3 → ℝ := fun h n =>
    CKN.mollify h (serrinRadius n) (serrinRadius_pos n) with hMdef
  have hgl (k : Fin 3) : LocallyIntegrable (fun x => g x k) volume :=
    (hg2.eval k).locallyIntegrable (by norm_num)
  have hDgl (k j : Fin 3) : LocallyIntegrable (fun x => Dg x k j) volume :=
    ((hDg2.eval k).eval j).locallyIntegrable (by norm_num)
  have hMs (k : Fin 3) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (M (fun x => g x k) n) :=
    CKN.mollify_contDiff (serrinRadius_pos n) (hgl k)
  let ψ : ℕ → Fin 3 → Vec3 → ℝ := fun n k x => serrinCutoff n x * M (fun x => g x k) n x
  have hψ (n : ℕ) (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (ψ n k) :=
    (serrinCutoff_contDiff n).mul (hMs k n)
  have hψc (n : ℕ) (k : Fin 3) : HasCompactSupport (ψ n k) :=
    (serrinCutoff_hasCompactSupport n).mul_right
  have hdψ (n : ℕ) (k j : Fin 3) (x : Vec3) : (fderiv ℝ (ψ n k) x) (basisVec j) =
      spatialDeriv (serrinCutoff n) j x * M (fun x => g x k) n x +
        serrinCutoff n x * M (fun x => Dg x k j) n x := by
    have hfd := (((serrinCutoff_contDiff n).differentiable (by simp)) x).hasFDerivAt
    have hgd := (((hMs k n).differentiable (by simp)) x).hasFDerivAt
    have h := (hfd.mul hgd).fderiv
    have htr : spatialDeriv (M (fun x => g x k) n) j x = M (fun x => Dg x k j) n x :=
      CKN.fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ (hgl k)
        (hDgl k j) (hggrad k j) (serrinRadius_pos n) (Set.subset_univ _)
    change (fderiv ℝ (serrinCutoff n * M (fun x => g x k) n) x) (basisVec j) = _
    rw [h]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [← htr]
    simp only [spatialDeriv]
    ring
  have hψL (n : ℕ) (k : Fin 3) (q : ℝ≥0∞) : MemLp (ψ n k) q volume :=
    (hψ n k).continuous.memLp_of_hasCompactSupport (hψc n k)
  have hψb (n : ℕ) (k : Fin 3) : ∃ C, ∀ x, ‖ψ n k x‖ ≤ C :=
    (hψc n k).exists_bound_of_continuous (hψ n k).continuous
  -- the integration by parts identity for each cutoff index and component
  have hIBP (n : ℕ) (k : Fin 3) :
      (∑ j : Fin 3, ∫ x : Vec3, b x j * f x k * (fderiv ℝ (ψ n k) x) (basisVec j)) =
        -∑ j : Fin 3, ∫ x : Vec3, b x j * Df x k j * ψ n k x := by
    have hbj (j : Fin 3) : MemLp (fun x => b x j) 2 (volume.restrict (Set.univ : Set Vec3)) := by
      rw [Measure.restrict_univ]
      exact hb2.eval j
    have hfk : MemLp (fun x => f x k) 2 (volume.restrict (Set.univ : Set Vec3)) := by
      rw [Measure.restrict_univ]
      exact hf2.eval k
    have hDbj (j i : Fin 3) : MemLp (fun x => Db x j i) 2
        (volume.restrict (Set.univ : Set Vec3)) := by
      rw [Measure.restrict_univ]
      exact (hDb2.eval j).eval i
    have hDfk (i : Fin 3) : MemLp (fun x => Df x k i) 2
        (volume.restrict (Set.univ : Set Vec3)) := by
      rw [Measure.restrict_univ]
      exact (hDf2.eval k).eval i
    have hj (j : Fin 3) : (∫ x : Vec3, b x j * f x k * (fderiv ℝ (ψ n k) x) (basisVec j)) =
        -∫ x : Vec3, (Db x j j * f x k + b x j * Df x k j) * ψ n k x := by
      have hprod := CKN.HasWeakGradientOn.mul_of_memLp_two isOpen_univ (hbj j) hfk
        (fun i => hDbj j i) (fun i => hDfk i) (hbgrad j) (hfgrad k)
      have h := hprod j (ψ n k) (hψ n k) (hψc n k) (Set.subset_univ _)
      simpa only [Measure.restrict_univ] using h
    obtain ⟨Cψ, hCψ⟩ := hψb n k
    have hA (j : Fin 3) : Integrable (fun x => Db x j j * f x k * ψ n k x) volume :=
      (((hDb2.eval j).eval j).integrable_mul (hf2.eval k)).mul_bdd
        (hψ n k).continuous.aestronglyMeasurable (Eventually.of_forall hCψ)
    have hB (j : Fin 3) : Integrable (fun x => b x j * Df x k j * ψ n k x) volume :=
      (hbDf j k).integrable_mul (hψL n k s)
    simp_rw [hj]
    have hsplit (j : Fin 3) : (∫ x : Vec3, (Db x j j * f x k + b x j * Df x k j) * ψ n k x) =
        (∫ x : Vec3, Db x j j * f x k * ψ n k x) + ∫ x : Vec3, b x j * Df x k j * ψ n k x := by
      rw [← integral_add (hA j) (hB j)]
      congr 1
      funext x
      ring
    simp_rw [hsplit]
    have hzero : (∫ x : Vec3, ∑ j : Fin 3, Db x j j * f x k * ψ n k x) = 0 := by
      have h : (fun x => ∑ j : Fin 3, Db x j j * f x k * ψ n k x) =ᵐ[volume] 0 := by
        filter_upwards [hbtr] with x hx
        rw [← Finset.sum_mul, ← Finset.sum_mul, hx]
        simp
      rw [integral_congr_ae h]
      simp
    have hsumA : (∑ j : Fin 3, ∫ x : Vec3, Db x j j * f x k * ψ n k x) = 0 := by
      rw [← integral_finsetSum _ fun j _ => hA j]
      exact hzero
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, hsumA, zero_add]
  obtain ⟨C, hC0, hCb⟩ := serrinCutoff_deriv_bound
  have hε : Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C
  have hMconv (h : Vec3 → ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ⊤) (hh : MemLp h q volume) :
      Tendsto (fun n => eLpNorm (fun x => M h n x - h x) q volume) atTop (𝓝 0) :=
    CKN.tendsto_eLpNorm_sub_zero_mollify hq hqt hh serrinRadius_tendsto serrinRadius_pos
  have hMm (h : Vec3 → ℝ) (hh : LocallyIntegrable h volume) :
      ∀ᶠ n in atTop, AEStronglyMeasurable (M h n) volume :=
    Eventually.of_forall fun n =>
      (CKN.mollify_continuous (serrinRadius_pos n) hh).aestronglyMeasurable
  have hηm (n : ℕ) : AEStronglyMeasurable (serrinCutoff n) volume :=
    (serrinCutoff_contDiff n).continuous.aestronglyMeasurable
  have hdηm (n : ℕ) (j : Fin 3) : AEStronglyMeasurable (spatialDeriv (serrinCutoff n) j) volume :=
    (((serrinCutoff_contDiff n).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable
  have hkey (k : Fin 3) : (∑ j : Fin 3, ∫ x : Vec3, b x j * f x k * Dg x k j) =
      -∑ j : Fin 3, ∫ x : Vec3, b x j * Df x k j * g x k := by
    -- limits of the two sides of the integration by parts identity
    have hLterm1 (j : Fin 3) := serrin_weighted_pairing_tendsto_zero (p := 2) (q := 2)
      (by norm_num) (by norm_num) (hbf j k) (hg2.eval k)
      (Eventually.of_forall fun _ => (hbf j k).aestronglyMeasurable)
      (hMm _ (hgl k)) (by simp) (hMconv _ (by norm_num) (by simp) (hg2.eval k))
      (cs := fun n x => spatialDeriv (serrinCutoff n) j x) (fun n x => hCb n j x) hε
    have hLterm2 (j : Fin 3) := serrin_weighted_pairing_tendsto (p := 2) (q := 2)
      (by norm_num) (hbf j k) ((hDg2.eval k).eval j)
      (Eventually.of_forall fun _ => (hbf j k).aestronglyMeasurable)
      (hMm _ (hDgl k j)) (by simp) (hMconv _ (by norm_num) (by simp) ((hDg2.eval k).eval j))
      (cs := fun n x => serrinCutoff n x) (c := fun _ => 1) hηm
      (fun n x => serrinCutoff_abs_le_one n x) aestronglyMeasurable_const (fun _ => by simp)
      (Eventually.of_forall fun x => serrinCutoff_tendsto_one x)
    have hRterm (j : Fin 3) := serrin_weighted_pairing_tendsto hs (hbDf j k) (hg k)
      (Eventually.of_forall fun _ => (hbDf j k).aestronglyMeasurable)
      (hMm _ (hgl k)) (by simp) (hMconv _ hs hstop (hg k))
      (cs := fun n x => serrinCutoff n x) (c := fun _ => 1) hηm
      (fun n x => serrinCutoff_abs_le_one n x) aestronglyMeasurable_const (fun _ => by simp)
      (Eventually.of_forall fun x => serrinCutoff_tendsto_one x)
    have hL := tendsto_finsetSum Finset.univ fun j _ => (hLterm1 j).add (hLterm2 j)
    have hR := (tendsto_finsetSum Finset.univ fun j _ => hRterm j).neg
    simp only [zero_add, one_mul] at hL hR
    refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
    have hconv : (-∑ j : Fin 3, ∫ x : Vec3, serrinCutoff n x * (b x j * Df x k j) *
        M (fun x => g x k) n x) = -∑ j : Fin 3, ∫ x : Vec3, b x j * Df x k j * ψ n k x := by
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      funext x
      simp only [ψ]
      ring
    rw [hconv, ← hIBP n k]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc1 : Continuous (fun x => spatialDeriv (serrinCutoff n) j x * M (fun x => g x k) n x) :=
      (((serrinCutoff_contDiff n).continuous_fderiv (by simp)).clm_apply
        continuous_const).mul (hMs k n).continuous
    have hc1s : HasCompactSupport
        (fun x => spatialDeriv (serrinCutoff n) j x * M (fun x => g x k) n x) :=
      ((serrinCutoff_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec j)).mul_right
    have hc2 : Continuous (fun x => serrinCutoff n x * M (fun x => Dg x k j) n x) :=
      (serrinCutoff_contDiff n).continuous.mul
        (CKN.mollify_continuous (serrinRadius_pos n) (hDgl k j))
    have hc2s : HasCompactSupport (fun x => serrinCutoff n x * M (fun x => Dg x k j) n x) :=
      (serrinCutoff_hasCompactSupport n).mul_right
    have hi1 : Integrable (fun x => spatialDeriv (serrinCutoff n) j x * (b x j * f x k) *
        M (fun x => g x k) n x) volume :=
      ((hbf j k).integrable_mul (q := 2) (hc1.memLp_of_hasCompactSupport hc1s)).congr
        (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
    have hi2 : Integrable (fun x => serrinCutoff n x * (b x j * f x k) *
        M (fun x => Dg x k j) n x) volume :=
      ((hbf j k).integrable_mul (q := 2) (hc2.memLp_of_hasCompactSupport hc2s)).congr
        (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
    rw [← integral_add hi1 hi2]
    congr 1
    funext x
    rw [hdψ n k j x]
    ring
  have hi1 (k j : Fin 3) : Integrable (fun x => b x j * Df x k j * g x k) volume :=
    (hbDf j k).integrable_mul (hg k)
  have hi2 (k j : Fin 3) : Integrable (fun x => b x j * f x k * Dg x k j) volume :=
    (hbf j k).integrable_mul (q := 2) ((hDg2.eval k).eval j)
  have hsum : (fun x => ∑ k : Fin 3, ∑ j : Fin 3, b x j * (Df x k j * g x k + f x k * Dg x k j)) =
      fun x => ∑ k : Fin 3, ((∑ j : Fin 3, b x j * Df x k j * g x k) +
        ∑ j : Fin 3, b x j * f x k * Dg x k j) := by
    funext x
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hs1 (k : Fin 3) : Integrable (fun x => ∑ j : Fin 3, b x j * Df x k j * g x k) volume :=
    integrable_finsetSum _ fun j _ => hi1 k j
  have hs2 (k : Fin 3) : Integrable (fun x => ∑ j : Fin 3, b x j * f x k * Dg x k j) volume :=
    integrable_finsetSum _ fun j _ => hi2 k j
  have hs12 (k : Fin 3) : Integrable (fun x => (∑ j : Fin 3, b x j * Df x k j * g x k) +
      ∑ j : Fin 3, b x j * f x k * Dg x k j) volume := (hs1 k).add (hs2 k)
  rw [hsum, integral_finsetSum _ fun k _ => hs12 k]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_add (hs1 k) (hs2 k), integral_finsetSum _ fun j _ => hi1 k j,
    integral_finsetSum _ fun j _ => hi2 k j, hkey k]
  ring

end ESS
