/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullGeneratorDensity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorResolvent

/-!
# Ginibre Full Generator Density
-/


@[expose] public section

namespace GinibrePoincare
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

/-- Actual real permutation-invariant Ginibre L² values. -/
def ginibreFullSymmetricValues (n : ℕ) : Submodule ℝ (GinibreFullValueL2 n) where
  carrier := {u | ∀ σ : ParticlePermutation n, ginibreRealPermutationL2 σ u = u}
  zero_mem' := by intro σ; simp
  add_mem' := by intro u v hu hv σ; simp [map_add, hu σ, hv σ]
  smul_mem' := by intro c u hu σ; rw [map_smul, hu σ]

theorem ginibreFullSymmetricValues_isClosed (n : ℕ) :
    IsClosed (ginibreFullSymmetricValues n : Set (GinibreFullValueL2 n)) := by
  change IsClosed {u | ∀ σ : ParticlePermutation n, ginibreRealPermutationL2 σ u = u}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro σ
  exact isClosed_eq (ginibreRealPermutationL2 σ).continuous continuous_id

instance ginibreFullSymmetricValues_complete (n : ℕ) : CompleteSpace (ginibreFullSymmetricValues
  n) :=
  (ginibreFullSymmetricValues_isClosed n).completeSpace_coe

/-- Smooth compact functions and their true gradients belong to weighted L². -/
theorem ginibreFull_smoothCompact_memLp (n : ℕ) (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    MemLp f 2 (ginibreMeasure n) ∧ MemLp (ginibreEuclideanGradient f) 2 (ginibreMeasure n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hgc : HasCompactSupport (ginibreEuclideanGradient f) := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ (isClosed_tsupport f)
    intro z hz
    by_contra hzF
    have hd : fderiv ℝ f z = 0 := fderiv_of_notMem_tsupport ℝ hzF
    apply hz
    ext k
    simp [ginibreEuclideanGradient, hd]
  exact ⟨hf.continuous.memLp_of_hasCompactSupport hc,
    (continuous_ginibreEuclideanGradient f hf).memLp_of_hasCompactSupport hgc⟩

/-- Every smooth compact symmetric observable is represented by an actual
symmetric ordinary distributional weak pair. -/
theorem ginibreFull_smoothCompact_symmetric_pair (n : ℕ) (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsSmoothCompactSymmetric f) :
    ∃ p : ginibreFullWeakSpace n hn, (p.val.1 : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f := by
  obtain ⟨hmv, hmg⟩ := ginibreFull_smoothCompact_memLp n hn f hf.1 hf.2.1
  let u := hmv.toLp f
  let g := hmg.toLp (ginibreEuclideanGradient f)
  have hweak := ginibre_smooth_distributional_gradient n hn u g f hf.1 hmv.coeFn_toLp hmg.coeFn_toLp
  have hsym : IsGinibreSymmetricWeakPair (u, g) := by
    intro σ
    constructor
    · apply Lp.ext
      have hcomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
        hmv.coeFn_toLp
      filter_upwards [ginibreRealPermutationL2_ae σ u, hcomp, hmv.coeFn_toLp] with z hp hc hu
      simp only [Function.comp_apply] at hc
      rw [hp, hc, hu]
      exact hf.2.2 σ z
    · apply Lp.ext
      have hcomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
        hmg.coeFn_toLp
      filter_upwards [ginibreGradientPermutationL2_ae σ g, hcomp, hmg.coeFn_toLp] with z hp hc hg
      simp only [Function.comp_apply] at hc
      rw [hp, hc, hg]
      have heq : (fun y => f (permute σ y)) = f := funext (hf.2.2 σ)
      rw [← ginibreEuclideanGradient_comp_permute σ f hf.1 z, heq]
  exact ⟨⟨(u, g), hweak, hsym⟩, hmv.coeFn_toLp⟩

/-- The Reynolds average preserves pairing with every symmetric L² value. -/
theorem ginibreFullSymmetricValues_inner_average (n : ℕ)
    (a : ginibreFullSymmetricValues n) (u : GinibreFullValueL2 n) :
    inner ℝ a.val (ginibreRealPermutationAverageL2 u) = inner ℝ a.val u := by
  classical
  have hterm (σ : ParticlePermutation n) : inner ℝ a.val (ginibreRealPermutationL2 σ u) = inner ℝ
    a.val u := by
    have h := (ginibreRealPermutationL2 σ).inner_map_map a.val u
    rw [a.property σ] at h
    exact h
  unfold ginibreRealPermutationAverageL2
  simp only [smul_apply, sum_apply]
  change inner ℝ a.val ((Fintype.card (ParticlePermutation n) : ℝ)⁻¹ •
    ∑ σ : ParticlePermutation n, ginibreRealPermutationL2 σ u) = _
  rw [real_inner_smul_right, inner_sum]
  simp_rw [hterm]
  have hc : (Fintype.card (ParticlePermutation n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [hc]


/-- Finite sums of L² classes have the expected representatives almost everywhere. -/
theorem ginibreFull_L2_sum_ae {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → GinibreFullValueL2 n) :
    ((∑ i ∈ s, f i : GinibreFullValueL2 n) : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := ginibreMeasure n)] with z hz
    simpa using hz
  | @insert i s hi ih =>
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with z hadd hs
    simp only [Finset.sum_insert hi]
    rw [hadd]
    change f i z + (∑ j ∈ s, f j : GinibreFullValueL2 n) z = _
    rw [hs]

/-- The scalar L² Reynolds operator has its literal finite-average representative. -/
theorem ginibreFull_permutationAverage_ae {n : ℕ}
    (u : GinibreFullValueL2 n) (f : Configuration n → ℝ)
    (hu : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f) :
    (ginibreRealPermutationAverageL2 u : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      ginibrePermutationAverage f := by
  classical
  have hterm (σ : ParticlePermutation n) :
      (ginibreRealPermutationL2 σ u : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
        fun z => f (permute σ z) := by
    have hcomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp hu
    filter_upwards [ginibreRealPermutationL2_ae σ u, hcomp] with z hp hc
    simp only [Function.comp_apply] at hc
    rw [hp, hc]
  unfold ginibreRealPermutationAverageL2
  simp only [smul_apply, sum_apply]
  filter_upwards [Lp.coeFn_smul ((Fintype.card (ParticlePermutation n) : ℝ)⁻¹)
      (∑ σ : ParticlePermutation n, ginibreRealPermutationL2 σ u),
    ginibreFull_L2_sum_ae Finset.univ (fun σ => ginibreRealPermutationL2 σ u),
    ae_all_iff.mpr hterm] with z hscale hsum hall
  change (↑((Fintype.card (ParticlePermutation n) : ℝ)⁻¹ •
    ∑ σ : ParticlePermutation n, ginibreRealPermutationL2 σ u) : Configuration n → ℝ) z = _
  rw [hscale]
  change (Fintype.card (ParticlePermutation n) : ℝ)⁻¹ *
    (∑ σ : ParticlePermutation n, ginibreRealPermutationL2 σ u : GinibreFullValueL2 n) z = _
  rw [hsum]
  simp only [ginibrePermutationAverage]
  congr 1
  exact Finset.sum_congr rfl (fun σ _ => hall σ)

/-- Full symmetric weak-H¹ values detect every actual symmetric L² value.
This is a concrete density statement, proved using all smooth compact tests. -/
theorem ginibreFullSymmetricValues_orthogonal_weak_eq_zero (n : ℕ) (hn : 0 < n)
    (a : ginibreFullSymmetricValues n)
    (ha : ∀ p : ginibreFullWeakSpace n hn, inner ℝ a.val p.val.1 = 0) : a = 0 := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have htest (ψ : Configuration n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
      (∫ z, ψ z • a.val z ∂ginibreMeasure n) = 0 := by
    let hm : MemLp ψ 2 (ginibreMeasure n) := hψ.continuous.memLp_of_hasCompactSupport hc
    let u := hm.toLp ψ
    obtain ⟨p, hp⟩ := ginibreFull_smoothCompact_symmetric_pair n hn (ginibrePermutationAverage ψ)
      (ginibrePermutationAverage_smoothCompact ψ hψ hc)
    have havg := ginibreFull_permutationAverage_ae u ψ hm.coeFn_toLp
    have hpval : p.val.1 = ginibreRealPermutationAverageL2 u := Lp.ext (hp.trans havg.symm)
    have hinner : inner ℝ a.val u = 0 := by
      rw [← ginibreFullSymmetricValues_inner_average n a u, ← hpval]
      exact ha p
    rw [L2.inner_def] at hinner
    rw [← hinner]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with z hz
    change u z = ψ z at hz
    change ψ z * a.val z = u z * a.val z
    rw [hz]
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((Lp.memLp a.val).integrable (by norm_num)).locallyIntegrable htest
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hz] with z hz
  simpa using hz


/-- The full value resolvent restricted to the actual symmetric L² Hilbert space. -/
def ginibreFullSymmetricResolvent (n : ℕ) (hn : 0 < n) :
    ginibreFullSymmetricValues n →L[ℝ] ginibreFullSymmetricValues n :=
  (((ginibreFullValueResolvent n hn).comp (ginibreFullSymmetricValues n).subtypeL)).codRestrict
    (ginibreFullSymmetricValues n) (by
      intro f σ
      exact (ginibreFullFormSpace_weak n hn (ginibreFullFormResolvent n hn f.val)).2 σ |>.1)

@[simp] theorem ginibreFullSymmetricResolvent_coe (n : ℕ) (hn : 0 < n)
    (f : ginibreFullSymmetricValues n) :
    (ginibreFullSymmetricResolvent n hn f).val = ginibreFullValueResolvent n hn f.val := rfl

theorem ginibreFullSymmetricResolvent_symmetric (n : ℕ) (hn : 0 < n)
    (f h : ginibreFullSymmetricValues n) :
    inner ℝ (ginibreFullSymmetricResolvent n hn f) h =
      inner ℝ f (ginibreFullSymmetricResolvent n hn h) :=
  ginibreFullValueResolvent_symmetric n hn f.val h.val

/-- The restricted full symmetric resolvent has no kernel. -/
theorem ginibreFullSymmetricResolvent_eq_zero_iff (n : ℕ) (hn : 0 < n)
    (f : ginibreFullSymmetricValues n) : ginibreFullSymmetricResolvent n hn f = 0 ↔ f = 0 := by
  constructor
  · intro hz
    have hnorm := ginibreFullValueResolvent_positive n hn f.val
    change inner ℝ f.val (ginibreFullSymmetricResolvent n hn f).val = _ at hnorm
    rw [hz] at hnorm
    simp only [Submodule.coe_zero, inner_zero_right] at hnorm
    have hR : ginibreFullFormResolvent n hn f.val = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (ginibreFullFormResolvent n hn f.val)]
    apply ginibreFullSymmetricValues_orthogonal_weak_eq_zero n hn f
    intro p
    have hr := ginibreFullFormResolvent_riesz n hn f.val (ginibreFullFormOfWeak n hn p)
    rw [hR, inner_zero_left, ginibreFullFormOfWeak_value] at hr
    exact hr.symm
  · intro hz
    simp [hz]

theorem ginibreFullSymmetricResolvent_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (ginibreFullSymmetricResolvent n hn) := by
  intro f h heq
  have hz : ginibreFullSymmetricResolvent n hn (f - h) = 0 := by
    rw [map_sub, heq, sub_self]
  exact sub_eq_zero.mp ((ginibreFullSymmetricResolvent_eq_zero_iff n hn (f - h)).mp hz)

/-- Every symmetric L² observable is approximable by values of the full
resolvent; consequently the concrete full form generator has dense domain. -/
theorem ginibreFullSymmetricResolvent_denseRange (n : ℕ) (hn : 0 < n) :
    DenseRange (ginibreFullSymmetricResolvent n hn) := by
  let K := (ginibreFullSymmetricResolvent n hn).toLinearMap.range.topologicalClosure
  let : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro a ha
    change a = 0
    have hRa : ginibreFullSymmetricResolvent n hn a = 0 := by
      apply ext_inner_right ℝ
      intro f
      have hmem : ginibreFullSymmetricResolvent n hn f ∈ K :=
        Submodule.le_topologicalClosure _ ⟨f, rfl⟩
      have hzero := (Submodule.mem_orthogonal' K a).mp ha _ hmem
      rw [ginibreFullSymmetricResolvent_symmetric]
      simpa using hzero
    exact (ginibreFullSymmetricResolvent_eq_zero_iff n hn a).mp hRa
  have hK : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp horth
  change Dense (Set.range (ginibreFullSymmetricResolvent n hn))
  rw [dense_iff_closure_eq]
  change closure ((ginibreFullSymmetricResolvent n hn).toLinearMap.range : Set
    (ginibreFullSymmetricValues n)) = Set.univ
  rw [← Submodule.topologicalClosure_coe]
  change (K : Set (ginibreFullSymmetricValues n)) = Set.univ
  rw [hK]
  rfl

end
end GinibrePoincare
