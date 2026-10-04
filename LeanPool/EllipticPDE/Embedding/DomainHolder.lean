/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.DomainLadder


/-!
# Hölder continuity up to the boundary

The second case of the Sobolev embedding at order `k` reads the Hölder exponent off Morrey's
inequality at the exponent the ladder reaches, and states it on the closure of the domain. This
file proves that statement.

The chain has three links. The ladder of `EllipticPdes.Embedding.DomainLadder` puts the member
and its first derivatives in `L^P(Ω)` for a `P` above the dimension;
`EllipticPdes.Extension.exists_extension_subset_bound` puts them on the whole space with the
same bound; and `morrey_ball` on a ball containing the closure of the domain produces the
continuous representative, whose Hölder seminorm is bounded by the `L^P` norms of the extended
gradient. Restricting the representative to the closure of the domain is the last step, and it
is where the conclusion reaches the boundary, which the interior statements of
`EllipticPdes.Embedding.HolderGeneral` do not.

## Supremum as well as seminorm

The `C^{0,γ}` norm of the cited statement is the supremum plus the Hölder seminorm, and Morrey
supplies the seminorm alone. The supremum comes from the support clause of the extension: the
extension vanishes outside a ball the closure of the domain sits inside, the representative is
therefore zero somewhere in the larger ball Morrey runs on, and the estimate against that point
bounds the representative everywhere by the seminorm times a power of the diameter. That power
depends on the two radii and the exponent alone, so one constant states both halves.

## Main declarations

* `EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_domain`: clause (ii) of the
  embedding on the closure of the domain, with a constant taken before the family.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem IV.2.3 case
(ii); L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.3 Theorem 6 clause (ii).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Extension (HasC1Boundary exists_extension_subset_bound)

variable {d : ℕ}

/-- **Clause (ii) of the embedding on a bounded domain with `C¹` boundary.** One constant,
depending on the domain, the dimension, the base exponent, the rung count and the landing
exponent, bounds both the supremum and the Hölder seminorm on the closure of the domain of a
representative of every member by a uniform `L^{p₀}` bound on the family. The Hölder exponent is
Morrey's `1 - d/P`, which `EllipticPdes.Embedding.morreyExponent_eq_ladder` identifies with the
`⌊n/p⌋ + 1 - n/p` of the cited statement at the landing exponent. -/
theorem exists_const_holderOnWith_of_gradClosed_domain (hd : 1 < d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) (ι : Type*) {p₀ P : ℝ≥0} (hp₀ : 1 ≤ p₀) {s : ℕ}
    (hsd : (p₀ : ℝ) * s ≤ (d : ℝ)) (hp₀P : p₀ ≤ P) (hPd : (d : ℝ) < (P : ℝ))
    (hPs : (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
      {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
      (∀ i, dep i < m → HasWeakGradOn Ω (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict Ω)) →
      ∀ M : ℝ≥0, (∀ j, dep j ≤ m → eLpNorm (F j) p₀ (volume.restrict Ω) ≤ (M : ℝ≥0∞)) →
      ∀ i, dep i + 1 + s ≤ m →
        ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
          w =ᵐ[volume.restrict Ω] F i ∧
            (∀ y ∈ closure Ω, ‖w y‖ ≤ ((C * M : ℝ≥0) : ℝ)) ∧
            HolderOnWith (C * M) (morreyExponent d (P : ℝ)) w (closure Ω) := by
  classical
  have hd0 : 0 < d := by omega
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  have hP1 : (1 : ℝ≥0) ≤ P := le_trans hp₀ hp₀P
  have hP1E : (1 : ℝ≥0∞) ≤ (P : ℝ≥0∞) := by exact_mod_cast hP1
  have hcast : ((P : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (P : ℝ) := by rw [ENNReal.ofReal_coe_nnreal]
  -- two balls: the extension is supported in the inner one, Morrey runs on the outer one
  obtain ⟨R₀, hR₀⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  set rb : ℝ := |R₀| + 1 with hrbdef
  set rb' : ℝ := |R₀| + 2 with hrb'def
  have habs : (0 : ℝ) ≤ |R₀| := abs_nonneg R₀
  have hrb : 0 < rb := by rw [hrbdef]; linarith
  have hrb' : 0 < rb' := by rw [hrb'def]; linarith
  have hbb : ball (0 : EuclideanSpace ℝ (Fin d)) rb ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) rb' :=
    ball_subset_ball (by rw [hrbdef, hrb'def]; linarith)
  have hΩcb : Ω ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) |R₀| := fun y hy =>
    mem_closedBall.mpr (le_trans (mem_closedBall.mp (hR₀ hy)) (le_abs_self R₀))
  have hclrb : closure Ω ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) rb :=
    (closure_minimal hΩcb isClosed_closedBall).trans
      (closedBall_subset_ball (by rw [hrbdef]; linarith))
  have hclrb' : closure Ω ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) rb' := hclrb.trans hbb
  have hΩrb' : Ω ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) rb' := subset_closure.trans hclrb'
  -- a point of the outer ball outside the inner one, where every such extension vanishes
  set z : EuclideanSpace ℝ (Fin d) :=
    (|R₀| + 3 / 2) • EuclideanSpace.single (⟨0, hd0⟩ : Fin d) (1 : ℝ) with hzdef
  have hznorm : ‖z‖ = |R₀| + 3 / 2 := by
    rw [hzdef, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hzin : z ∈ ball (0 : EuclideanSpace ℝ (Fin d)) rb' := by
    rw [mem_ball_zero_iff, hznorm, hrb'def]; linarith
  have hzout : z ∉ ball (0 : EuclideanSpace ℝ (Fin d)) rb := by
    rw [mem_ball_zero_iff, hznorm, hrbdef, not_lt]
    linarith
  obtain ⟨K, hK⟩ :=
    exists_const_memLp_of_gradClosed_domain hd hΩopen hΩb hC1 hp₀ ι s hsd hp₀P hPs
  obtain ⟨KE, hKE⟩ := exists_extension_subset_bound hd0 hΩopen hΩb hC1
    (Metric.isOpen_ball (x := (0 : EuclideanSpace ℝ (Fin d))) (ε := rb)) hclrb
    (p := (P : ℝ≥0∞)) hP1E
  obtain ⟨Cm, hCm⟩ := morrey_ball hd0 hPd (0 : EuclideanSpace ℝ (Fin d)) hrb'
  -- the seminorm's constant, and the power of the diameter the supremum adds to it
  set Cb : ℝ≥0 := Cm * ((d : ℝ≥0) * (KE * (((d + 1 : ℕ) : ℝ≥0) * K))) with hCbdef
  set Cd : ℝ≥0 := Real.toNNReal ((2 * rb') ^ ((morreyExponent d (P : ℝ) : ℝ≥0) : ℝ)) with hCddef
  have hCdcoe : ((Cd : ℝ≥0) : ℝ) = (2 * rb') ^ ((morreyExponent d (P : ℝ) : ℝ≥0) : ℝ) := by
    rw [hCddef, Real.coe_toNNReal _ (Real.rpow_nonneg (by linarith) _)]
  refine ⟨Cb + Cb * Cd, ?_⟩
  intro F nxt dep m hdep hgrad hmem M hM i hi
  -- the ladder, run to the exponent Morrey consumes
  have hlad : ∀ j, dep j + s ≤ m → MemLp (F j) P (volume.restrict Ω) ∧
      eLpNorm (F j) P (volume.restrict Ω) ≤ (K : ℝ≥0∞) * (M : ℝ≥0∞) :=
    fun j hj => hK hdep hgrad hmem (M : ℝ≥0∞) hM j hj
  have hi' : dep i + s ≤ m := by omega
  have hik : ∀ k, dep (nxt i k) + s ≤ m := fun k => by have := hdep i k; omega
  have hFint : ∀ j, dep j + s ≤ m → IntegrableOn (F j) Ω volume :=
    fun j hj => (hlad j hj).1.integrable hP1E
  -- the extension across the boundary, supported in the inner ball
  obtain ⟨U, G, hwgU, -, hsuppU, hUint, hGint, hag, hUb, hGb⟩ :=
    hKE (F i) (fun k => F (nxt i k)) (hFint i hi') (fun k => hFint (nxt i k) (hik k))
      (hgrad i (by omega))
  have hN : eLpNorm (F i) P (volume.restrict Ω)
      + ∑ k, eLpNorm (F (nxt i k)) P (volume.restrict Ω)
      ≤ (((d + 1 : ℕ) : ℝ≥0) : ℝ≥0∞) * ((K : ℝ≥0∞) * (M : ℝ≥0∞)) := by
    have hsum : ∑ k, eLpNorm (F (nxt i k)) P (volume.restrict Ω)
        ≤ ∑ _k : Fin d, (K : ℝ≥0∞) * (M : ℝ≥0∞) :=
      Finset.sum_le_sum fun k _ => (hlad (nxt i k) (hik k)).2
    calc eLpNorm (F i) P (volume.restrict Ω)
          + ∑ k, eLpNorm (F (nxt i k)) P (volume.restrict Ω)
        ≤ (K : ℝ≥0∞) * (M : ℝ≥0∞) + ∑ _k : Fin d, (K : ℝ≥0∞) * (M : ℝ≥0∞) :=
          add_le_add (hlad i hi').2 hsum
      _ = (((d + 1 : ℕ) : ℝ≥0) : ℝ≥0∞) * ((K : ℝ≥0∞) * (M : ℝ≥0∞)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hGtot : ∀ k, eLpNorm (G k) (P : ℝ≥0∞) volume
      ≤ ((KE * (((d + 1 : ℕ) : ℝ≥0) * K) * M : ℝ≥0) : ℝ≥0∞) := by
    intro k
    calc eLpNorm (G k) (P : ℝ≥0∞) volume
        ≤ (KE : ℝ≥0∞) * (eLpNorm (F i) P (volume.restrict Ω)
            + ∑ j, eLpNorm (F (nxt i j)) P (volume.restrict Ω)) := hGb k
      _ ≤ (KE : ℝ≥0∞) * ((((d + 1 : ℕ) : ℝ≥0) : ℝ≥0∞) * ((K : ℝ≥0∞) * (M : ℝ≥0∞))) :=
          mul_le_mul' le_rfl hN
      _ = ((KE * (((d + 1 : ℕ) : ℝ≥0) * K) * M : ℝ≥0) : ℝ≥0∞) := by
          push_cast
          ring
  have hGP : ∀ k, MemLp (G k) (ENNReal.ofReal (P : ℝ))
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) rb')) := by
    intro k
    have hm : MemLp (G k) (P : ℝ≥0∞) volume :=
      lt_of_le_of_lt (hGtot k) ENNReal.coe_lt_top
    have := hm.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) rb')
    rwa [hcast] at this
  -- Morrey on the outer ball
  obtain ⟨w, hwae, hwhol⟩ := hCm U G (MeasureTheory.Integrable.integrableOn hUint) hGP
    (hwgU.mono (Set.subset_univ _))
  have hseminorm : Cm * ∑ k, (eLpNorm (G k) (ENNReal.ofReal (P : ℝ))
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) rb'))).toNNReal ≤ Cb * M := by
    have hterm : ∀ k : Fin d, (eLpNorm (G k) (ENNReal.ofReal (P : ℝ))
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) rb'))).toNNReal
        ≤ KE * (((d + 1 : ℕ) : ℝ≥0) * K) * M := by
      intro k
      have hle : eLpNorm (G k) (ENNReal.ofReal (P : ℝ))
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) rb'))
          ≤ ((KE * (((d + 1 : ℕ) : ℝ≥0) * K) * M : ℝ≥0) : ℝ≥0∞) := by
        rw [← hcast]
        exact le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self) (hGtot k)
      have hne : eLpNorm (G k) (ENNReal.ofReal (P : ℝ))
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) rb')) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.coe_ne_top hle
      have h2 := (ENNReal.toNNReal_le_toNNReal hne ENNReal.coe_ne_top).mpr hle
      rwa [ENNReal.toNNReal_coe] at h2
    calc Cm * ∑ k, (eLpNorm (G k) (ENNReal.ofReal (P : ℝ))
            (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) rb'))).toNNReal
        ≤ Cm * ∑ _k : Fin d, KE * (((d + 1 : ℕ) : ℝ≥0) * K) * M := by
          gcongr with k _
          exact hterm k
      _ = Cb * M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hCbdef]
          ring
  have hwhol' : HolderOnWith (Cb * M) (morreyExponent d (P : ℝ)) w
      (ball (0 : EuclideanSpace ℝ (Fin d)) rb') := hwhol.mono_const hseminorm
  -- the representative vanishes somewhere in the outer ball
  set V : Set (EuclideanSpace ℝ (Fin d)) :=
    ball (0 : EuclideanSpace ℝ (Fin d)) rb' \ tsupport U with hVdef
  have hVopen : IsOpen V := Metric.isOpen_ball.sdiff (isClosed_tsupport U)
  have hVsub : V ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) rb' := Set.sdiff_subset
  have hzV : z ∈ V := ⟨hzin, fun hc => hzout (hsuppU hc)⟩
  have hVpos : 0 < volume V := hVopen.measure_pos volume ⟨z, hzV⟩
  have hVne : volume.restrict V ≠ 0 := by
    intro h
    have huniv : (volume.restrict V) Set.univ = 0 := by rw [h]; rfl
    rw [Measure.restrict_apply_univ] at huniv
    exact hVpos.ne' huniv
  have : (ae (volume.restrict V)).NeBot := ae_neBot.mpr hVne
  have hwV : ∀ᵐ x ∂(volume.restrict V), x ∈ V ∧ w x = 0 := by
    have hres : w =ᵐ[volume.restrict V] U :=
      ae_restrict_of_ae_restrict_of_subset hVsub hwae
    filter_upwards [hres, ae_restrict_mem hVopen.measurableSet] with x hx hxV
    exact ⟨hxV, by rw [hx, image_eq_zero_of_notMem_tsupport hxV.2]⟩
  obtain ⟨z₀, hz₀V, hz₀⟩ := hwV.exists
  -- the supremum, read off the estimate against that point
  have hsup : ∀ y ∈ closure Ω, ‖w y‖ ≤ (((Cb + Cb * Cd) * M : ℝ≥0) : ℝ) := by
    intro y hy
    have hyb : y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) rb' := hclrb' hy
    have hdist := hwhol'.dist_le hyb (hVsub hz₀V)
    rw [hz₀, Real.dist_eq, sub_zero] at hdist
    have hyz : dist y z₀ ≤ 2 * rb' := by
      have h1 : dist y (0 : EuclideanSpace ℝ (Fin d)) < rb' := mem_ball.mp hyb
      have h2 : dist z₀ (0 : EuclideanSpace ℝ (Fin d)) < rb' := mem_ball.mp (hVsub hz₀V)
      calc dist y z₀ ≤ dist y (0 : EuclideanSpace ℝ (Fin d))
            + dist (0 : EuclideanSpace ℝ (Fin d)) z₀ := dist_triangle _ _ _
        _ ≤ 2 * rb' := by rw [dist_comm (0 : EuclideanSpace ℝ (Fin d)) z₀]; linarith
    have hpow : dist y z₀ ^ ((morreyExponent d (P : ℝ) : ℝ≥0) : ℝ)
        ≤ (2 * rb') ^ ((morreyExponent d (P : ℝ) : ℝ≥0) : ℝ) :=
      Real.rpow_le_rpow dist_nonneg hyz (by positivity)
    have hstep : ((Cb * M : ℝ≥0) : ℝ) * dist y z₀ ^ ((morreyExponent d (P : ℝ) : ℝ≥0) : ℝ)
        ≤ ((Cb * M : ℝ≥0) : ℝ) * ((Cd : ℝ≥0) : ℝ) := by
      rw [hCdcoe]
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    rw [Real.norm_eq_abs]
    refine le_trans hdist (le_trans hstep ?_)
    push_cast
    nlinarith [(Cb : ℝ≥0).coe_nonneg, (M : ℝ≥0).coe_nonneg, (Cd : ℝ≥0).coe_nonneg]
  refine ⟨w, ?_, hsup, ?_⟩
  · refine Filter.EventuallyEq.trans (ae_restrict_of_ae_restrict_of_subset hΩrb' hwae) ?_
    exact (ae_restrict_iff' hΩopen.measurableSet).mpr
      (Filter.Eventually.of_forall fun y hy => hag y hy)
  · exact (hwhol'.mono hclrb').mono_const (mul_le_mul_left le_self_add _)

end EllipticPdes.Embedding
