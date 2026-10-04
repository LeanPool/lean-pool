/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.GagliardoNirenberg


/-!
# Sobolev ladder for a compactly supported family

The ladder of `EllipticPdes.Embedding.SobolevLadderGeneral` runs on a ball and shrinks it at
every rung, because each rung multiplies by a cutoff. A compactly supported class needs no
cutoff, so the same induction runs on the whole space with no loss of domain, and the
conclusion is global.

Two facts replace the finite measure of the ball. A compactly supported `Lᵖ` class is
integrable, and its exponent lowers freely: both come from
`MeasureTheory.MemLp.mono_exponent_of_measure_support_ne_top` applied to the support.

This is the half of the classical order-`k` embedding that asks nothing of a boundary. The
general statement on a bounded domain with `C¹` boundary reduces to it through an extension
operator, which is where the boundary hypothesis is spent.

## Main declarations

* `EllipticPdes.Embedding.integrable_of_memLp_compactSupport`: a compactly supported `Lᵖ`
  class is integrable.
* `EllipticPdes.Embedding.memLp_sobolevConj_of_le_compactSupport`: one rung on the whole
  space, fed by data at an exponent at or above `p`.
* `EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport`: the ladder, on the whole space.
* `EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport_ideal`: the ladder at the
  exponent case (i) names, under the strict condition `p₀ s < d`.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.1 Thm 1 and §5.6.3 Thm 6.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

private theorem le_of_inv_le_inv_cs {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a⁻¹ ≤ b⁻¹) :
    b ≤ a := by
  nlinarith [mul_inv_cancel₀ ha.ne', mul_inv_cancel₀ hb.ne', inv_pos.mpr ha, inv_pos.mpr hb]

private theorem inv_anti_cs {a b : ℝ} (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
  one_div a ▸ one_div b ▸ one_div_le_one_div_of_le ha h

private theorem coe_toNNReal_inv_cs {t : ℝ} (ht : 0 < t) :
    ((Real.toNNReal t⁻¹ : ℝ≥0) : ℝ) = t⁻¹ :=
  Real.coe_toNNReal _ (inv_nonneg.mpr ht.le)

/-! ### Compact support in place of a finite measure -/

/-- **Free lowering of the exponent of a compactly supported class.** The support has finite
measure, so Hölder's inequality on it gives the smaller exponent, with no hypothesis on the
measure of the whole space. -/
theorem memLp_mono_exponent_compactSupport {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hcs : HasCompactSupport f) {p q : ℝ≥0∞} (hf : MemLp f q volume) (hpq : p ≤ q) :
    MemLp f p volume :=
  hf.mono_exponent_of_measure_support_ne_top
    (s := tsupport f) (fun _ hx => image_eq_zero_of_notMem_tsupport hx)
    hcs.isCompact.measure_lt_top.ne hpq

/-- **Integrability of a compactly supported `Lᵖ` class**, for any `p ≥ 1`. -/
theorem integrable_of_memLp_compactSupport {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hcs : HasCompactSupport f) {p : ℝ≥0} (hp : 1 ≤ p) (hf : MemLp f p volume) :
    Integrable f volume := by
  rw [← memLp_one_iff_integrable]
  exact memLp_mono_exponent_compactSupport hcs hf (by exact_mod_cast hp)

/-! ### One rung -/

/-- **One rung on the whole space.** A compactly supported `v` whose weak gradient `g` is
compactly supported and lies in `L^q` for some `q ≥ p` lies in `Lᵖ'`, where
`1/p' = 1/p - 1/d`. The exponents drop from `q` to `p` on the support, and
`exists_eLpNorm_sobolevConj_le_compactSupport` runs the rung. -/
theorem memLp_sobolevConj_of_le_compactSupport (hd : 0 < d) {p q p' : ℝ≥0}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹)
    {v : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hvcs : HasCompactSupport v) (hgcs : ∀ k, HasCompactSupport (g k))
    (hv : MemLp v q volume) (hg : ∀ k, MemLp (g k) q volume)
    (hwg : HasWeakGradOn Set.univ v g) :
    MemLp v p' volume := by
  have hpqE : (p : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hpq
  have hvp : MemLp v p volume := memLp_mono_exponent_compactSupport hvcs hv hpqE
  have hgp : ∀ k, MemLp (g k) p volume :=
    fun k => memLp_mono_exponent_compactSupport (hgcs k) (hg k) hpqE
  obtain ⟨_K, hK⟩ := exists_eLpNorm_sobolevConj_le_compactSupport hd hp hpp'
  exact (hK v g hvcs (integrable_of_memLp_compactSupport hvcs hp hvp) hvp hgp hwg).1

/-! ### The ladder -/

/-- **Sobolev ladder on the whole space.** Let `F` assign a function to each index of `ι`,
let `nxt i k` name a weak `k`-derivative of `F i` on `Set.univ`, and let `dep` record how far
an index sits above the root. If every member of the family is compactly supported, every
index of depth at most `m` lies in `L^{p₀}`, and every index of depth below `m` has its weak
gradient in the family, then at rung `s` with `p₀ s ≤ d` every index of depth at most `m - s`
lies in `L^q`, for any `q ≥ p₀` whose reciprocal is at least `1/p₀ - s/d`.

The statement is the one of `memLp_of_gradClosed_general` with the ball replaced by the whole
space and the radii gone: no rung shrinks the domain. -/
theorem memLp_of_gradClosed_compactSupport (hd : 1 < d)
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀)
    (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1) (hcs : ∀ i, HasCompactSupport (F i)) :
    ∀ (s : ℕ) {q : ℝ≥0}, (p₀ : ℝ) * s ≤ (d : ℝ) → p₀ ≤ q →
      (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ →
      (∀ i, dep i < m → HasWeakGradOn Set.univ (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) p₀ volume) →
      ∀ i, dep i + s ≤ m → MemLp (F i) q volume := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by positivity
  have hdinv0 : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.mpr hdpos
  have hp₀1 : (1 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀
  have hp₀0 : (0 : ℝ) < (p₀ : ℝ) := by linarith
  have hp₀inv : (p₀ : ℝ)⁻¹ ≤ 1 := by
    have := inv_anti_cs (a := (1 : ℝ)) one_pos hp₀1
    simpa using this
  intro s
  induction s with
  | zero =>
    intro q _ hpq hqs _ hmem i hi
    have hq0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le hp₀0 (by exact_mod_cast hpq)
    have hqp : q ≤ p₀ := by
      rw [← NNReal.coe_le_coe]
      refine le_of_inv_le_inv_cs hp₀0 hq0 ?_
      simpa using hqs
    exact memLp_mono_exponent_compactSupport (hcs i) (hmem i (by omega))
      (by exact_mod_cast hqp)
  | succ s ih =>
    intro q hsd hpq hqs hgrad hmem i hi
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
    have hQcoe : ((Q : ℝ≥0) : ℝ) = t⁻¹ := by rw [hQ_def]; exact coe_toNNReal_inv_cs ht0
    have hQ0 : (0 : ℝ) < (Q : ℝ) := by rw [hQcoe]; exact inv_pos.mpr ht0
    have hQinv : ((Q : ℝ≥0) : ℝ)⁻¹ = t := by rw [hQcoe, inv_inv]
    have hp₀Q : p₀ ≤ Q := by
      rw [← NNReal.coe_le_coe, hQcoe]
      have := inv_anti_cs ht0 ht_le
      simpa using this
    have hQmem : ∀ j, dep j + s ≤ m → MemLp (F j) Q volume :=
      ih hsdprev hp₀Q (le_of_eq hQinv.symm) hgrad hmem
    by_cases hu1 : (q : ℝ)⁻¹ + (d : ℝ)⁻¹ ≤ 1
    · -- The target is at or above the conjugate exponent, so the rung runs onto it.
      set u : ℝ := (q : ℝ)⁻¹ + (d : ℝ)⁻¹ with hu_def
      have hu0 : 0 < u := by rw [hu_def]; linarith
      set p : ℝ≥0 := Real.toNNReal u⁻¹ with hp_def
      have hpcoe : ((p : ℝ≥0) : ℝ) = u⁻¹ := by rw [hp_def]; exact coe_toNNReal_inv_cs hu0
      have hp0 : (0 : ℝ) < (p : ℝ) := by rw [hpcoe]; exact inv_pos.mpr hu0
      have hpinv : ((p : ℝ≥0) : ℝ)⁻¹ = u := by rw [hpcoe, inv_inv]
      have hp1 : (1 : ℝ≥0) ≤ p := by
        rw [← NNReal.coe_le_coe, NNReal.coe_one, hpcoe]
        have := inv_anti_cs hu0 hu1
        simpa using this
      have htu : t ≤ u := by rw [ht_def, hu_def]; linarith
      have hpQ : p ≤ Q := by
        rw [← NNReal.coe_le_coe]
        refine le_of_inv_le_inv_cs hQ0 hp0 ?_
        rw [hQinv, hpinv]; exact htu
      have hpp' : ((q : ℝ≥0) : ℝ)⁻¹ = ((p : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
        rw [hpinv, hu_def]; ring
      exact memLp_sobolevConj_of_le_compactSupport (by omega) hp1 hpQ hpp' (hcs i)
        (fun k => hcs (nxt i k)) (hQmem i (by omega))
        (fun k => hQmem (nxt i k) (by have := hdep i k; omega)) (hgrad i (by omega))
    · -- The target sits below the conjugate exponent, so one rung overshoots it.
      have hu1' : 1 < (q : ℝ)⁻¹ + (d : ℝ)⁻¹ := lt_of_not_ge hu1
      set t₁ : ℝ := (p₀ : ℝ)⁻¹ - (d : ℝ)⁻¹ with ht₁_def
      have hd2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 2 ≤ d)
      have ht₁0 : 0 < t₁ := by
        by_contra hcon
        have hcon' : t₁ ≤ 0 := le_of_not_gt hcon
        have hple : (d : ℝ)⁻¹ ≥ (p₀ : ℝ)⁻¹ := by rw [ht₁_def] at hcon'; linarith
        have hdp : (d : ℝ) ≤ (p₀ : ℝ) := le_of_inv_le_inv_cs hp₀0 hdpos hple
        have hqge : (p₀ : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
        have hqinv' : (q : ℝ)⁻¹ ≤ (d : ℝ)⁻¹ := inv_anti_cs hdpos (le_trans hdp hqge)
        have hdd : (d : ℝ)⁻¹ ≤ 2⁻¹ := by
          have := inv_anti_cs (a := (2 : ℝ)) (by norm_num) hd2R
          simpa using this
        linarith
      have ht₁_le : t₁ ≤ (p₀ : ℝ)⁻¹ := by rw [ht₁_def]; linarith
      set P : ℝ≥0 := Real.toNNReal t₁⁻¹ with hP_def
      have hPcoe : ((P : ℝ≥0) : ℝ) = t₁⁻¹ := by rw [hP_def]; exact coe_toNNReal_inv_cs ht₁0
      have hP0 : (0 : ℝ) < (P : ℝ) := by rw [hPcoe]; exact inv_pos.mpr ht₁0
      have hPinv : ((P : ℝ≥0) : ℝ)⁻¹ = t₁ := by rw [hPcoe, inv_inv]
      have hp₀P : ((P : ℝ≥0) : ℝ)⁻¹ = ((p₀ : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
        rw [hPinv, ht₁_def]
      -- One rung from `p₀`, then the exponent is lowered onto `q`.
      have hPmem : MemLp (F i) P volume :=
        memLp_sobolevConj_of_le_compactSupport (by omega) hp₀ le_rfl hp₀P (hcs i)
          (fun k => hcs (nxt i k)) (hmem i (by omega))
          (fun k => hmem (nxt i k) (by have := hdep i k; omega)) (hgrad i (by omega))
      have hqP : q ≤ P := by
        rw [← NNReal.coe_le_coe]
        refine le_of_inv_le_inv_cs hP0 hq0 ?_
        rw [hPinv, ht₁_def]
        have hs0 : 0 ≤ (s : ℝ) * (d : ℝ)⁻¹ := by positivity
        linarith
      exact memLp_mono_exponent_compactSupport (hcs i) hPmem (by exact_mod_cast hqP)

/-! ### The exponent of case (i) -/

/-- **Whole-space bootstrap at the exponent case (i) names.** Under the strict step condition
`p₀ s < d`, which is the `k < n/p` of Evans §5.6.3 Theorem 6, the reciprocal `1/p₀ - s/d` is
positive and names a finite exponent, and the bootstrap lands on it with no loss of domain.

The cited statement takes a bounded `Ω` with `C¹` boundary and concludes on it, with a norm
estimate. The statement here asks nothing of a boundary, takes a family of compact support on
the whole space, and is qualitative. The passage from the one to the other goes through the
extension operator, `EllipticPdes.Extension.exists_extension_subset_bound`, and the statement
it reaches on a bounded `C¹` domain is
`EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain`. -/
theorem memLp_of_gradClosed_compactSupport_ideal (hd : 1 < d)
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀)
    (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1) (hcs : ∀ i, HasCompactSupport (F i))
    (s : ℕ) (hsd : (p₀ : ℝ) * s < (d : ℝ))
    (hgrad : ∀ i, dep i < m → HasWeakGradOn Set.univ (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, dep i ≤ m → MemLp (F i) p₀ volume) :
    ∀ i, dep i + s ≤ m →
      MemLp (F i) (Real.toNNReal ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹) volume := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by positivity
  have hp₀1 : (1 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀
  have hp₀0 : (0 : ℝ) < (p₀ : ℝ) := by linarith
  have ht0 : 0 < (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ := by
    have h := mul_lt_mul_of_pos_right hsd (mul_pos (inv_pos.mpr hdpos) (inv_pos.mpr hp₀0))
    have hc1 : (p₀ : ℝ) * (s : ℝ) * ((d : ℝ)⁻¹ * (p₀ : ℝ)⁻¹) = (s : ℝ) * (d : ℝ)⁻¹ := by
      field_simp
    have hc2 : (d : ℝ) * ((d : ℝ)⁻¹ * (p₀ : ℝ)⁻¹) = (p₀ : ℝ)⁻¹ := by field_simp
    rw [hc1, hc2] at h
    linarith
  have hcoe : ((Real.toNNReal ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹ : ℝ≥0) : ℝ)
      = ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹ := coe_toNNReal_inv_cs ht0
  refine memLp_of_gradClosed_compactSupport hd hp₀ hdep hcs s hsd.le ?_ ?_ hgrad hmem
  · rw [← NNReal.coe_le_coe, hcoe]
    refine le_of_inv_le_inv_cs (inv_pos.mpr ht0) hp₀0 ?_
    rw [inv_inv]
    have : 0 ≤ (s : ℝ) * (d : ℝ)⁻¹ := by positivity
    linarith
  · rw [hcoe, inv_inv]

end EllipticPdes.Embedding
