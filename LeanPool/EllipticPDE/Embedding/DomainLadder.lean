/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.DomainSobolev


/-!
# Sobolev ladder on a bounded domain

The proof of the Sobolev embedding at order `k` applies the Gagliardo-Nirenberg-Sobolev
inequality to
`D^β u` for `|β| ≤ k - 1`, reads off `u ∈ W^{k-1,p⋆}(Ω)`, and repeats. This file runs that
iteration.

`EllipticPdes.Embedding.memLp_of_gradClosed_general` runs the same iteration on a ball inside a
ball, each rung shrinking the domain because the whole-space inequality is fed through a cutoff.
On a bounded domain with `C¹` boundary the extension operator supplies the cutoff once and for
all, so no rung shrinks anything and the estimate is on `Ω` throughout. That is what makes a
constant possible: one number, depending on the domain, the dimension, the base exponent, the
rung count and the target exponent, takes a uniform `L^{p₀}` bound on the family to an `L^q`
bound on the member.

## Two regimes of a rung

The step onto the target `q` consumes the exponent `p` with `1/p = 1/q + 1/d`, which is
admissible when `1/q + 1/d ≤ 1`. Below that the target sits under the conjugate exponent and one
rung from `p₀` overshoots it; the exponent is then lowered onto the target by the finite measure
of the domain, at the price of a factor `|Ω|^{1/q - 1/P}` the constant absorbs. Both regimes are
what `EllipticPdes.Embedding.memLp_of_gradClosed_general` separates on a ball.

## Main declarations

* `EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain`: the ladder on the domain,
  with a constant taken before the family.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem IV.2.3 case
(i); L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.3 Theorem 6 clause (i).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Extension (HasC1Boundary)

variable {d : ℕ}

private theorem inv_anti_dom {a b : ℝ} (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hb : 0 < b := lt_of_lt_of_le ha h
  nlinarith [mul_inv_cancel₀ ha.ne', mul_inv_cancel₀ hb.ne', inv_pos.mpr ha, inv_pos.mpr hb]

private theorem le_of_inv_le_inv_dom {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a⁻¹ ≤ b⁻¹) :
    b ≤ a := by
  nlinarith [mul_inv_cancel₀ ha.ne', mul_inv_cancel₀ hb.ne', inv_pos.mpr ha, inv_pos.mpr hb]

private theorem coe_toNNReal_inv_dom {t : ℝ} (ht : 0 < t) :
    ((Real.toNNReal t⁻¹ : ℝ≥0) : ℝ) = t⁻¹ :=
  Real.coe_toNNReal _ (inv_nonneg.mpr ht.le)

/-- **Lowering an exponent on a domain of finite measure.** The factor is
`|Ω|^{1/a - 1/b}`, finite because the exponent is nonnegative and the domain bounded. -/
private theorem exists_const_eLpNorm_mono_exponent_domain
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩb : Bornology.IsBounded Ω) {a b : ℝ≥0}
    (ha : 0 < (a : ℝ)) (hab : a ≤ b) :
    ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
      AEStronglyMeasurable f (volume.restrict Ω) →
      eLpNorm f a (volume.restrict Ω) ≤ eLpNorm f b (volume.restrict Ω) * (A : ℝ≥0∞) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have habE : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := by exact_mod_cast hab
  have he : (0 : ℝ) ≤ 1 / (a : ℝ≥0∞).toReal - 1 / (b : ℝ≥0∞).toReal := by
    have hac : (a : ℝ≥0∞).toReal = (a : ℝ) := by simp
    have hbc : (b : ℝ≥0∞).toReal = (b : ℝ) := by simp
    rw [hac, hbc, sub_nonneg]
    exact one_div_le_one_div_of_le ha habR
  have hAne : ((volume.restrict Ω) Set.univ
      ^ (1 / (a : ℝ≥0∞).toReal - 1 / (b : ℝ≥0∞).toReal)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg he (measure_ne_top (volume.restrict Ω) Set.univ)
  refine ⟨((volume.restrict Ω) Set.univ
    ^ (1 / (a : ℝ≥0∞).toReal - 1 / (b : ℝ≥0∞).toReal)).toNNReal, fun f hf => ?_⟩
  rw [ENNReal.coe_toNNReal hAne]
  exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ habE hf

/-- **Sobolev ladder on a bounded domain with `C¹` boundary and its constant.** Let `F`
assign a class to each index of `ι`, let `nxt i k` name a weak `k`-derivative of `F i` on `Ω`,
and let `dep` record how far an index sits above the root, so that differentiating adds at most
one. At rung `s` with `p₀ s ≤ d`, one constant takes a uniform `L^{p₀}` bound on the members of
depth at most `m` to an `L^q` bound on every member of depth at most `m - s`, for any `q ≥ p₀`
whose reciprocal is at least `1/p₀ - s/d`. This is the embedding's case (i), read on a
family closed under weak differentiation with a depth function in place of `D^α u`. -/
theorem exists_const_memLp_of_gradClosed_domain (hd : 1 < d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀) (ι : Type*) :
    ∀ (s : ℕ) {q : ℝ≥0}, (p₀ : ℝ) * s ≤ (d : ℝ) → p₀ ≤ q →
      (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ →
      ∃ K : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
        {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
        (∀ i, dep i < m → HasWeakGradOn Ω (F i) (fun k => F (nxt i k))) →
        (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict Ω)) →
        ∀ M : ℝ≥0∞, (∀ j, dep j ≤ m → eLpNorm (F j) p₀ (volume.restrict Ω) ≤ M) →
        ∀ i, dep i + s ≤ m →
          MemLp (F i) q (volume.restrict Ω) ∧
            eLpNorm (F i) q (volume.restrict Ω) ≤ (K : ℝ≥0∞) * M := by
  classical
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  have hd0 : 0 < d := by omega
  have hdpos : (0 : ℝ) < (d : ℝ) := by positivity
  have hd1 : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdinv0 : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.mpr hdpos
  have hp₀1 : (1 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀
  have hp₀0 : (0 : ℝ) < (p₀ : ℝ) := by linarith
  have hp₀inv : (p₀ : ℝ)⁻¹ ≤ 1 := by
    have := inv_anti_dom (a := (1 : ℝ)) one_pos hp₀1
    simpa using this
  intro s
  induction s with
  | zero =>
    intro q _ hpq hqs
    have hq0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le hp₀0 (by exact_mod_cast hpq)
    have hqp : q ≤ p₀ := by
      rw [← NNReal.coe_le_coe]
      refine le_of_inv_le_inv_dom hp₀0 hq0 ?_
      simpa using hqs
    have hqE : (q : ℝ≥0∞) ≤ (p₀ : ℝ≥0∞) := by exact_mod_cast hqp
    obtain ⟨A, hA⟩ := exists_const_eLpNorm_mono_exponent_domain hΩb hq0 hqp
    refine ⟨A, ?_⟩
    intro F nxt dep m _hdep _hgrad hmem M hM i hi
    have hmemq : MemLp (F i) q (volume.restrict Ω) :=
      (hmem i (by omega)).mono_exponent hqE
    refine ⟨hmemq, ?_⟩
    calc eLpNorm (F i) q (volume.restrict Ω)
        ≤ eLpNorm (F i) p₀ (volume.restrict Ω) * (A : ℝ≥0∞) := hA _ (hmem i (by
            omega)).aestronglyMeasurable
      _ ≤ M * (A : ℝ≥0∞) := mul_le_mul_left (hM i (by omega)) _
      _ = (A : ℝ≥0∞) * M := mul_comm _ _
  | succ s ih =>
    intro q hsd hpq hqs
    have hq0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le hp₀0 (by exact_mod_cast hpq)
    have hsdR : (p₀ : ℝ) * ((s : ℝ) + 1) ≤ (d : ℝ) := by push_cast at hsd; linarith
    have hsdprev : (p₀ : ℝ) * (s : ℝ) ≤ (d : ℝ) := by nlinarith
    push_cast at hqs
    -- The reciprocal at rung `s`, and the exponent naming it.
    set t : ℝ := (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ with ht_def
    have ht0 : 0 < t := by
      have hstep : (s : ℝ) * (d : ℝ)⁻¹ + (d : ℝ)⁻¹ ≤ (p₀ : ℝ)⁻¹ := by
        have hmul := mul_le_mul_of_nonneg_right hsdR (mul_pos hdinv0 (inv_pos.mpr hp₀0)).le
        have hc1 : (d : ℝ) * ((d : ℝ)⁻¹ * (p₀ : ℝ)⁻¹) = (p₀ : ℝ)⁻¹ := by field_simp
        have hc2 : (p₀ : ℝ) * ((s : ℝ) + 1) * ((d : ℝ)⁻¹ * (p₀ : ℝ)⁻¹)
            = ((s : ℝ) + 1) * (d : ℝ)⁻¹ := by field_simp
        rw [hc1, hc2] at hmul
        linarith
      rw [ht_def]; linarith
    have ht_le : t ≤ (p₀ : ℝ)⁻¹ := by
      have : 0 ≤ (s : ℝ) * (d : ℝ)⁻¹ := by positivity
      rw [ht_def]; linarith
    set Q : ℝ≥0 := Real.toNNReal t⁻¹ with hQ_def
    have hQcoe : ((Q : ℝ≥0) : ℝ) = t⁻¹ := by rw [hQ_def]; exact coe_toNNReal_inv_dom ht0
    have hQ0 : (0 : ℝ) < (Q : ℝ) := by rw [hQcoe]; exact inv_pos.mpr ht0
    have hQinv : ((Q : ℝ≥0) : ℝ)⁻¹ = t := by rw [hQcoe, inv_inv]
    have hp₀Q : p₀ ≤ Q := by
      rw [← NNReal.coe_le_coe, hQcoe]
      have := inv_anti_dom ht0 ht_le
      simpa using this
    obtain ⟨KQ, hKQ⟩ := ih hsdprev hp₀Q (le_of_eq hQinv.symm)
    by_cases hu1 : (q : ℝ)⁻¹ + (d : ℝ)⁻¹ ≤ 1
    · -- The target is at or above the conjugate exponent, so the rung runs onto it.
      set u : ℝ := (q : ℝ)⁻¹ + (d : ℝ)⁻¹ with hu_def
      have hu0 : 0 < u := by rw [hu_def]; positivity
      set p : ℝ≥0 := Real.toNNReal u⁻¹ with hp_def
      have hpcoe : ((p : ℝ≥0) : ℝ) = u⁻¹ := by rw [hp_def]; exact coe_toNNReal_inv_dom hu0
      have hp0 : (0 : ℝ) < (p : ℝ) := by rw [hpcoe]; exact inv_pos.mpr hu0
      have hpinv : ((p : ℝ≥0) : ℝ)⁻¹ = u := by rw [hpcoe, inv_inv]
      have hp1 : (1 : ℝ≥0) ≤ p := by
        rw [← NNReal.coe_le_coe, NNReal.coe_one, hpcoe]
        have := inv_anti_dom hu0 hu1
        simpa using this
      have htu : t ≤ u := by rw [ht_def, hu_def]; linarith
      have hpQ : p ≤ Q := by
        rw [← NNReal.coe_le_coe]
        refine le_of_inv_le_inv_dom hQ0 hp0 ?_
        rw [hQinv, hpinv]; exact htu
      have hpp' : ((q : ℝ≥0) : ℝ)⁻¹ = ((p : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
        rw [hpinv, hu_def]; ring
      obtain ⟨Kr, hKr⟩ := exists_eLpNorm_sobolevConj_le_domain_of_le hd0 hΩopen hΩb hC1
        (p := p) (q := Q) (p' := q) hp1 hpQ hpp'
      refine ⟨Kr * (((d + 1 : ℕ) : ℝ≥0) * KQ), ?_⟩
      have hKcoe : ((Kr * (((d + 1 : ℕ) : ℝ≥0) * KQ) : ℝ≥0) : ℝ≥0∞)
          = (Kr : ℝ≥0∞) * (((d : ℝ≥0∞) + 1) * (KQ : ℝ≥0∞)) := by push_cast; ring
      rw [hKcoe]
      intro F nxt dep m hdep hgrad hmem M hM i hi
      have hQi : MemLp (F i) Q (volume.restrict Ω) ∧
          eLpNorm (F i) Q (volume.restrict Ω) ≤ (KQ : ℝ≥0∞) * M :=
        hKQ hdep hgrad hmem M hM i (by omega)
      have hQk : ∀ k, MemLp (F (nxt i k)) Q (volume.restrict Ω) ∧
          eLpNorm (F (nxt i k)) Q (volume.restrict Ω) ≤ (KQ : ℝ≥0∞) * M := fun k =>
        hKQ hdep hgrad hmem M hM (nxt i k) (by have := hdep i k; omega)
      obtain ⟨hmemq, hbd⟩ := hKr (F i) (fun k => F (nxt i k)) hQi.1 (fun k => (hQk k).1)
        (hgrad i (by omega))
      refine ⟨hmemq, ?_⟩
      calc eLpNorm (F i) q (volume.restrict Ω)
          ≤ (Kr : ℝ≥0∞) * (eLpNorm (F i) Q (volume.restrict Ω)
              + ∑ k, eLpNorm (F (nxt i k)) Q (volume.restrict Ω)) := hbd
        _ ≤ (Kr : ℝ≥0∞) * ((KQ : ℝ≥0∞) * M + ∑ _k : Fin d, (KQ : ℝ≥0∞) * M) :=
            mul_le_mul' le_rfl (add_le_add hQi.2 (Finset.sum_le_sum fun k _ => (hQk k).2))
        _ = (Kr : ℝ≥0∞) * (((d : ℝ≥0∞) + 1) * (KQ : ℝ≥0∞)) * M := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    · -- The target sits below the conjugate exponent, so one rung from `p₀` overshoots it.
      have hu1' : 1 < (q : ℝ)⁻¹ + (d : ℝ)⁻¹ := lt_of_not_ge hu1
      set t₁ : ℝ := (p₀ : ℝ)⁻¹ - (d : ℝ)⁻¹ with ht₁_def
      have hd2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 2 ≤ d)
      have ht₁0 : 0 < t₁ := by
        by_contra hcon
        have hcon' : t₁ ≤ 0 := le_of_not_gt hcon
        have hple : (d : ℝ)⁻¹ ≥ (p₀ : ℝ)⁻¹ := by rw [ht₁_def] at hcon'; linarith
        have hdp : (d : ℝ) ≤ (p₀ : ℝ) := le_of_inv_le_inv_dom hp₀0 hdpos hple
        have hqge : (p₀ : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
        have hqinv' : (q : ℝ)⁻¹ ≤ (d : ℝ)⁻¹ := inv_anti_dom hdpos (le_trans hdp hqge)
        have hdd : (d : ℝ)⁻¹ ≤ 2⁻¹ := by
          have := inv_anti_dom (a := (2 : ℝ)) (by norm_num) hd2R
          simpa using this
        linarith
      set P : ℝ≥0 := Real.toNNReal t₁⁻¹ with hP_def
      have hPcoe : ((P : ℝ≥0) : ℝ) = t₁⁻¹ := by rw [hP_def]; exact coe_toNNReal_inv_dom ht₁0
      have hP0 : (0 : ℝ) < (P : ℝ) := by rw [hPcoe]; exact inv_pos.mpr ht₁0
      have hPinv : ((P : ℝ≥0) : ℝ)⁻¹ = t₁ := by rw [hPcoe, inv_inv]
      have hp₀P : ((P : ℝ≥0) : ℝ)⁻¹ = ((p₀ : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
        rw [hPinv, ht₁_def]
      have hqP : q ≤ P := by
        rw [← NNReal.coe_le_coe]
        refine le_of_inv_le_inv_dom hP0 hq0 ?_
        rw [hPinv, ht₁_def]
        have hs0 : 0 ≤ (s : ℝ) * (d : ℝ)⁻¹ := by positivity
        linarith
      obtain ⟨K₁, hK₁⟩ :=
        exists_eLpNorm_sobolevConj_le_domain hd0 hΩopen hΩb hC1 (p := p₀) (p' := P) hp₀ hp₀P
      obtain ⟨A, hA⟩ := exists_const_eLpNorm_mono_exponent_domain hΩb hq0 hqP
      refine ⟨K₁ * (((d + 1 : ℕ) : ℝ≥0) * A), ?_⟩
      have hKcoe : ((K₁ * (((d + 1 : ℕ) : ℝ≥0) * A) : ℝ≥0) : ℝ≥0∞)
          = (K₁ : ℝ≥0∞) * (((d : ℝ≥0∞) + 1) * (A : ℝ≥0∞)) := by push_cast; ring
      rw [hKcoe]
      intro F nxt dep m hdep hgrad hmem M hM i hi
      obtain ⟨hPmem, hPbd⟩ := hK₁ (F i) (fun k => F (nxt i k)) (hmem i (by omega))
        (fun k => hmem (nxt i k) (by have := hdep i k; omega)) (hgrad i (by omega))
      have hqE : (q : ℝ≥0∞) ≤ (P : ℝ≥0∞) := by exact_mod_cast hqP
      refine ⟨hPmem.mono_exponent hqE, ?_⟩
      calc eLpNorm (F i) q (volume.restrict Ω)
          ≤ eLpNorm (F i) P (volume.restrict Ω) * (A : ℝ≥0∞) := hA _ hPmem.aestronglyMeasurable
        _ ≤ (K₁ : ℝ≥0∞) * (eLpNorm (F i) p₀ (volume.restrict Ω)
              + ∑ k, eLpNorm (F (nxt i k)) p₀ (volume.restrict Ω)) * (A : ℝ≥0∞) :=
            mul_le_mul_left hPbd _
        _ ≤ (K₁ : ℝ≥0∞) * (M + ∑ _k : Fin d, M) * (A : ℝ≥0∞) := by
            refine mul_le_mul_left (mul_le_mul' le_rfl (add_le_add (hM i (by omega)) ?_)) _
            exact Finset.sum_le_sum fun k _ =>
              hM (nxt i k) (by have := hdep i k; omega)
        _ = (K₁ : ℝ≥0∞) * (((d : ℝ≥0∞) + 1) * (A : ℝ≥0∞)) * M := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring

end EllipticPdes.Embedding
