/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Appendix

/-!
# The index of compactness

The Appendix of `human/proof_met.tex` identifies the index `ν = lim_k χ_k` built from the
Bernstein numbers with the usual *index of compactness*
`κ = lim_n (1/n) log‖𝓛^{(n)}_ω‖_c`. One inequality is the chain
`‖T‖_c ≤ 2k s_k(T) ≤ C_k ρ_k(T)` of `ProofMet.Appendix`, which gives `κ ≤ χ_k` for every `k`.

The other inequality is the counting argument of the paper, and it is what this file builds:
covering numbers of `𝓛^{(n)}_ω(𝔹_X)` grow at a definite exponential rate `r` (Kingman, applied
to a family that is *exactly* subadditive), while a `k`-dimensional subspace growing like
`e^{n(χ_k - ε)}` forces `e^{nk(χ_k - κ - 4ε)}` separated points in that image, each in its own
ball. Comparing the two bounds gives `k(χ_k - κ - 4ε) ≤ r` for every `k`, so `χ_k` cannot stay
above `κ` by a fixed margin.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter Metric Module TopologicalSpace
open scoped ENNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `coverPred T t m`: the image of the closed unit ball under `T` is covered by at most `m`
closed balls of radius `t`. -/
def coverPred (T : X →L[ℝ] X) (t : ℝ) (m : ℕ) : Prop :=
  ∃ Y : Finset X, Y.card ≤ m ∧ ∀ x : X, ‖x‖ ≤ 1 → ∃ y ∈ Y, ‖T x - y‖ ≤ t

theorem coverPred.mono_radius {T : X →L[ℝ] X} {t t' : ℝ} {m : ℕ} (h : coverPred T t m)
    (htt : t ≤ t') : coverPred T t' m := by
  obtain ⟨Y, hcard, hY⟩ := h
  exact ⟨Y, hcard, fun x hx => (hY x hx).imp fun y hy => ⟨hy.1, hy.2.trans htt⟩⟩

theorem coverPred.mono_card {T : X →L[ℝ] X} {t : ℝ} {m m' : ℕ} (h : coverPred T t m)
    (hmm : m ≤ m') : coverPred T t m' := by
  obtain ⟨Y, hcard, hY⟩ := h
  exact ⟨Y, hcard.trans hmm, hY⟩

/-- One ball of radius `‖T‖` around the origin already covers the image of the unit ball. -/
theorem coverPred_opNorm (T : X →L[ℝ] X) {m : ℕ} (hm : 1 ≤ m) : coverPred T ‖T‖ m := by
  refine ⟨{0}, by simpa using hm, fun x hx => ⟨0, Finset.mem_singleton_self 0, ?_⟩⟩
  have h1 : ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
  have h2 : ‖T‖ * ‖x‖ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg T)
  simpa using h1.trans (by simpa using h2)

/-- A point of the cover, written as `y + a • w` with `‖w‖ ≤ 1`. -/
theorem exists_smul_of_norm_sub_le {a : ℝ} (ha : 0 ≤ a) {u y : X} (h : ‖u - y‖ ≤ a) :
    ∃ w : X, ‖w‖ ≤ 1 ∧ u = y + a • w := by
  rcases eq_or_lt_of_le ha with rfl | hapos
  · refine ⟨0, by simp, ?_⟩
    have : ‖u - y‖ = 0 := le_antisymm (by simpa using h) (norm_nonneg _)
    have := sub_eq_zero.mp (norm_eq_zero.mp this)
    simp [this]
  · refine ⟨a⁻¹ • (u - y), ?_, ?_⟩
    · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hapos, inv_mul_le_iff₀ hapos]
      simpa using h
    · rw [smul_inv_smul₀ (ne_of_gt hapos)]
      abel

/-- **Covering numbers are submultiplicative.** If `T` sends the unit ball into `m` balls of
radius `a` and `S` sends it into `m'` balls of radius `b`, then `S ∘ T` sends it into `m * m'`
balls of radius `a * b`: apply `S` to each ball `y + a·B` of the first cover and cover
`a·S(B)` by the scaled second cover. -/
theorem coverPred_comp {S T : X →L[ℝ] X} {a b : ℝ} {m m' : ℕ} (ha : 0 ≤ a)
    (hT : coverPred T a m) (hS : coverPred S b m') :
    coverPred (S.comp T) (a * b) (m * m') := by
  classical
  obtain ⟨Y, hYcard, hY⟩ := hT
  obtain ⟨Z, hZcard, hZ⟩ := hS
  refine ⟨(Y ×ˢ Z).image (fun p => S p.1 + a • p.2), ?_, ?_⟩
  · refine le_trans Finset.card_image_le ?_
    simpa [Finset.card_product] using Nat.mul_le_mul hYcard hZcard
  · intro x hx
    obtain ⟨y, hyY, hy⟩ := hY x hx
    obtain ⟨w, hwnorm, hTx⟩ := exists_smul_of_norm_sub_le ha hy
    obtain ⟨z, hzZ, hz⟩ := hZ w hwnorm
    refine ⟨S y + a • z, Finset.mem_image.mpr ⟨(y, z), Finset.mem_product.mpr ⟨hyY, hzZ⟩, rfl⟩, ?_⟩
    have hrw : (S.comp T) x - (S y + a • z) = a • (S w - z) := by
      simp only [ContinuousLinearMap.comp_apply, hTx, map_add, map_smul]
      module
    rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left hz ha

/-- **An operator close to a compact one has finite covering numbers.** If `‖T‖_c < t` then
`T` maps the unit ball into finitely many balls of radius `t`: write `T = K + R` with `K`
compact and `‖R‖ < t`, cover the totally bounded set `K(B)` by balls of radius `t - ‖R‖`, and
keep the same centres. -/
theorem exists_coverPred_of_compactSeminorm_lt (T : X →L[ℝ] X) {t : ℝ}
    (ht : compactSeminorm T < t) : ∃ m : ℕ, 1 ≤ m ∧ coverPred T t m := by
  classical
  -- a compact `K` with `‖T - K‖ < t`
  obtain ⟨_, ⟨K, hK, rfl⟩, hKlt⟩ :
      ∃ r ∈ (fun K : X →L[ℝ] X => ‖T - K‖) '' {K | IsCompactOperator K},
      r < t := by
    have hne : ((fun K : X →L[ℝ] X => ‖T - K‖) '' {K | IsCompactOperator K}).Nonempty :=
      ⟨‖T - 0‖, ⟨0, isCompactOperator_zero, rfl⟩⟩
    have hbdd : BddBelow ((fun K : X →L[ℝ] X => ‖T - K‖) '' {K | IsCompactOperator K}) :=
      ⟨0, by rintro _ ⟨K, -, rfl⟩; exact norm_nonneg _⟩
    exact exists_lt_of_csInf_lt hne ht
  set ε : ℝ := t - ‖T - K‖ with hε
  have hεpos : 0 < ε := by simp [hε]; linarith
  -- `K` maps the closed unit ball into a totally bounded set
  have hcompact : IsCompact (closure (K '' Metric.closedBall 0 1)) :=
    hK.isCompact_closure_image_closedBall 1
  obtain ⟨Y, hYfin, hYcov⟩ :=
    Metric.totallyBounded_iff.mp hcompact.totallyBounded ε hεpos
  refine ⟨max 1 hYfin.toFinset.card, le_max_left _ _, hYfin.toFinset, le_max_right _ _, ?_⟩
  intro x hx
  have hxball : x ∈ Metric.closedBall (0 : X) 1 := by simpa using hx
  have : K x ∈ closure (K '' Metric.closedBall 0 1) :=
    subset_closure ⟨x, hxball, rfl⟩
  obtain ⟨y, hyY, hy⟩ := Set.mem_iUnion₂.mp (hYcov this)
  refine ⟨y, hYfin.mem_toFinset.mpr hyY, ?_⟩
  have h1 : ‖K x - y‖ ≤ ε := le_of_lt (by simpa [dist_eq_norm] using hy)
  have h2 : ‖T x - K x‖ ≤ ‖T - K‖ := by
    have := (T - K).le_opNorm x
    simp only [sub_apply] at this
    calc ‖T x - K x‖ ≤ ‖T - K‖ * ‖x‖ := this
      _ ≤ ‖T - K‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = ‖T - K‖ := mul_one _
  calc ‖T x - y‖ ≤ ‖T x - K x‖ + ‖K x - y‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub (T x) (K x) y
    _ ≤ ‖T - K‖ + ε := add_le_add h2 h1
    _ = t := by simp [hε]

/-- `coverRad T m`: the least radius (an infimum) at which `m` balls cover `T` of the unit
ball. -/
noncomputable def coverRad (T : X →L[ℝ] X) (m : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ coverPred T t m}

theorem coverRad_bddBelow (T : X →L[ℝ] X) (m : ℕ) :
    BddBelow {t : ℝ | 0 ≤ t ∧ coverPred T t m} := ⟨0, fun _ ht => ht.1⟩

theorem coverRad_nonneg (T : X →L[ℝ] X) (m : ℕ) : 0 ≤ coverRad T m := by
  rcases Set.eq_empty_or_nonempty {t : ℝ | 0 ≤ t ∧ coverPred T t m} with h | h
  · simp [coverRad, h]
  · exact le_csInf h fun _ ht => ht.1

theorem coverRad_le_of_coverPred {T : X →L[ℝ] X} {t : ℝ} {m : ℕ} (ht : 0 ≤ t)
    (h : coverPred T t m) : coverRad T m ≤ t :=
  csInf_le (coverRad_bddBelow T m) ⟨ht, h⟩

theorem coverRad_le_opNorm (T : X →L[ℝ] X) {m : ℕ} (hm : 1 ≤ m) : coverRad T m ≤ ‖T‖ :=
  coverRad_le_of_coverPred (norm_nonneg T) (coverPred_opNorm T hm)

theorem coverPred_of_coverRad_lt {T : X →L[ℝ] X} {t : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (h : coverRad T m < t) : coverPred T t m := by
  have hne : {t : ℝ | 0 ≤ t ∧ coverPred T t m}.Nonempty :=
    ⟨‖T‖, norm_nonneg T, coverPred_opNorm T hm⟩
  obtain ⟨t', ht', hlt⟩ := exists_lt_of_csInf_lt hne h
  exact ht'.2.mono_radius hlt.le

/-- Covering radii are submultiplicative under composition. -/
theorem coverRad_comp (S T : X →L[ℝ] X) {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    coverRad (S.comp T) (m * m') ≤ coverRad T m * coverRad S m' := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set cT := coverRad T m with hcT
  set cS := coverRad S m' with hcS
  have hcT0 : 0 ≤ cT := coverRad_nonneg T m
  have hcS0 : 0 ≤ cS := coverRad_nonneg S m'
  set δ : ℝ := min 1 (ε / (cT + cS + 1)) with hδ
  have hpos : (0:ℝ) < cT + cS + 1 := by linarith
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (cT + cS + 1) ≤ ε := by
    have : δ ≤ ε / (cT + cS + 1) := min_le_right _ _
    calc δ * (cT + cS + 1) ≤ (ε / (cT + cS + 1)) * (cT + cS + 1) :=
          mul_le_mul_of_nonneg_right this (le_of_lt hpos)
      _ = ε := by field_simp
  have h1 : coverPred T (cT + δ) m := coverPred_of_coverRad_lt hm (by linarith)
  have h2 : coverPred S (cS + δ) m' := coverPred_of_coverRad_lt hm' (by linarith)
  have hcomp := coverPred_comp (by positivity) h1 h2
  have hle := coverRad_le_of_coverPred (by positivity) hcomp
  refine hle.trans ?_
  nlinarith [hδpos, hδ1, hδε, hcT0, hcS0]

/-- Points whose images are pairwise more than `2t` apart lie in distinct balls of a cover of
radius `t`, so there are at most `m` of them. -/
theorem card_le_of_coverPred {T : X →L[ℝ] X} {t : ℝ} {m : ℕ} (hcov : coverPred T t m)
    {ι : Type*} (S : Finset ι) (f : ι → X) (hf : ∀ i ∈ S, ‖f i‖ ≤ 1)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 2 * t < ‖T (f i) - T (f j)‖) : S.card ≤ m := by
  classical
  obtain ⟨Y, hYcard, hY⟩ := hcov
  choose g hgY hgle using fun i (hi : i ∈ S) => hY (f i) (hf i hi)
  set G : ι → X := fun i => if h : i ∈ S then g i h else 0 with hG
  have hGY : ∀ i ∈ S, G i ∈ Y := by
    intro i hi; simp only [hG, dite_eq_left hi]; exact hgY i hi
  have hGle : ∀ i ∈ S, ‖T (f i) - G i‖ ≤ t := by
    intro i hi; simp only [hG, dite_eq_left hi]; exact hgle i hi
  have hinj : Set.InjOn G (S : Set ι) := by
    intro i hi' j hj' hij
    have hi : i ∈ S := Finset.mem_coe.mp hi'
    have hj : j ∈ S := Finset.mem_coe.mp hj'
    by_contra hne
    have hsij := hsep i hi j hj hne
    have hswap : ‖G i - T (f j)‖ = ‖T (f j) - G j‖ := by rw [hij, norm_sub_rev]
    have hd : ‖T (f i) - T (f j)‖ ≤ 2 * t := by
      calc ‖T (f i) - T (f j)‖ ≤ ‖T (f i) - G i‖ + ‖G i - T (f j)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = ‖T (f i) - G i‖ + ‖T (f j) - G j‖ := by rw [hswap]
        _ ≤ t + t := add_le_add (hGle i hi) (hGle j hj)
        _ = 2 * t := by ring
    linarith
  calc S.card = (S.image G).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Y.card := Finset.card_le_card (fun y hy => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
        exact hGY i hi)
    _ ≤ m := hYcard

/-- **The counting step.** A `k`-dimensional subspace on which `T` expands by at least `g`
carries a grid of `(g/(3ku))^k` points of the unit ball whose images are `3u`-separated, so any
cover of `T(𝔹_X)` by balls of radius `u` needs at least that many balls. -/
theorem pow_le_of_coverPred {T : X →L[ℝ] X} {k : ℕ} (hk : 1 ≤ k) {V : Submodule ℝ X}
    [FiniteDimensional ℝ V] (hV : Module.finrank ℝ V = k) {g u : ℝ} (hg : 0 < g)
    (hgV : g ≤ growth T V) {m : ℕ} (hu : 0 < u) (hcov : coverPred T u m) :
    (g / (3 * k * u)) ^ k ≤ m := by
  classical
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  set Q : ℝ := g / (3 * k * u) with hQ
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hm1 : 1 ≤ m := by
    obtain ⟨Y, hYcard, hY⟩ := hcov
    obtain ⟨y, hyY, -⟩ := hY 0 (by simp)
    have h1 : 1 ≤ Y.card := Finset.card_pos.mpr ⟨y, hyY⟩
    omega
  rcases lt_or_ge Q 1 with hQ1 | hQ1
  · calc Q ^ k ≤ 1 ^ k := pow_le_pow_left₀ hQpos.le hQ1.le k
      _ = 1 := one_pow k
      _ ≤ (m : ℝ) := by exact_mod_cast hm1
  set s : ℝ := 3 * u / g with hs
  have hspos : 0 < s := by rw [hs]; positivity
  have hQs : Q * (k * s) = 1 := by
    rw [hQ, hs]; field_simp
  obtain ⟨e, henorm, heaux⟩ := exists_auerbach_basis (E := V) hV
  set x : Fin k → X := fun i => (e i : X) with hx
  have hxV : ∀ i, x i ∈ V := fun i => (e i).2
  have hxnorm : ∀ i, ‖x i‖ = 1 := fun i => by simpa [hx] using henorm i
  have hcoeff : ∀ a : Fin k → ℝ, ‖a‖ ≤ ‖∑ i, a i • x i‖ := by
    intro a
    have h := heaux a
    have hcast : ((∑ i, a i • e i : V) : X) = ∑ i, a i • x i := by
      simp [hx]
    rw [← hcast]
    simpa using h
  set q : ℕ := ⌊Q⌋₊ with hq
  have hq1 : 1 ≤ q := (Nat.one_le_floor_iff Q).mpr hQ1
  have hqQ : (q : ℝ) ≤ Q := Nat.floor_le hQpos.le
  have hQ2q : Q ≤ 2 * (q : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one Q
    have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg q
    rw [← hq] at h
    linarith
  set G : Finset (Fin k → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-(q:ℤ)) (q:ℤ)) with hG
  have hIcc : (Finset.Icc (-(q:ℤ)) (q:ℤ)).card = 2 * q + 1 := by
    rw [Int.card_Icc]; omega
  have hGcard : (G.card : ℝ) = (2 * (q:ℝ) + 1) ^ k := by
    rw [hG, Fintype.card_piFinset]
    rw [Finset.prod_congr rfl (fun i _ => hIcc)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    ring
  set P : (Fin k → ℤ) → X := fun c => ∑ i, ((c i : ℝ) * s) • x i with hP
  have hPV : ∀ c, P c ∈ V := fun c =>
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hxV i))
  have hmemq : ∀ c ∈ G, ∀ i, |(c i : ℝ)| ≤ (q : ℝ) := by
    intro c hc i
    have := (Fintype.mem_piFinset.mp (by rw [hG] at hc; exact hc)) i
    rw [Finset.mem_Icc] at this
    have h1 : -(q:ℝ) ≤ (c i : ℝ) := by exact_mod_cast this.1
    have h2 : (c i : ℝ) ≤ (q:ℝ) := by exact_mod_cast this.2
    rw [abs_le]; exact ⟨h1, h2⟩
  have hPnorm : ∀ c ∈ G, ‖P c‖ ≤ 1 := by
    intro c hc
    have hbound : ∀ i : Fin k, ‖((c i : ℝ) * s) • x i‖ ≤ (q:ℝ) * s := by
      intro i
      rw [norm_smul, hxnorm i, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos hspos]
      exact mul_le_mul_of_nonneg_right (hmemq c hc i) hspos.le
    calc ‖P c‖ ≤ ∑ i, ‖((c i : ℝ) * s) • x i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin k, (q:ℝ) * s := Finset.sum_le_sum (fun i _ => hbound i)
      _ = (k : ℝ) * ((q:ℝ) * s) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (k : ℝ) * (Q * s) := by
          have := mul_le_mul_of_nonneg_right hqQ hspos.le
          nlinarith [hkR]
      _ = 1 := by nlinarith [hQs]
  have hsep : ∀ c ∈ G, ∀ c' ∈ G, c ≠ c' → 2 * u < ‖T (P c) - T (P c')‖ := by
    intro c hc c' hc' hne
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ c' i := Function.ne_iff.mp hne
    set a : Fin k → ℝ := fun j => ((c j : ℝ) - (c' j : ℝ)) * s with ha
    have hdiff : P c - P c' = ∑ j, a j • x j := by
      rw [hP]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [ha]
      rw [← sub_smul]
      ring_nf
    have hai : s ≤ |a i| := by
      rw [ha]
      have hne' : (c i : ℝ) - (c' i : ℝ) ≠ 0 := by
        intro h
        apply hi
        have : (c i : ℝ) = (c' i : ℝ) := by linarith
        exact_mod_cast this
      have h1 : (1:ℝ) ≤ |(c i : ℝ) - (c' i : ℝ)| := by
        have hz : (1:ℤ) ≤ |c i - c' i| := Int.one_le_abs (sub_ne_zero.mpr hi)
        have hcast : ((1:ℤ) : ℝ) ≤ ((|c i - c' i| : ℤ) : ℝ) := Int.cast_le.mpr hz
        push_cast at hcast
        exact hcast
      rw [abs_mul, abs_of_pos hspos]
      nlinarith [hspos]
    have hnormge : s ≤ ‖P c - P c'‖ := by
      rw [hdiff]
      refine le_trans ?_ (hcoeff a)
      exact le_trans hai (by simpa using norm_le_pi_norm a i)
    have hgrow : growth T V * ‖P c - P c'‖ ≤ ‖T (P c - P c')‖ :=
      growth_mul_norm_le T (Submodule.sub_mem _ (hPV c) (hPV c'))
    have hTsub : T (P c) - T (P c') = T (P c - P c') := by simp
    rw [hTsub]
    have h1 : g * s ≤ growth T V * ‖P c - P c'‖ :=
      mul_le_mul hgV hnormge hspos.le (le_trans hg.le hgV)
    have h2 : g * s = 3 * u := by rw [hs]; field_simp
    nlinarith [hgrow, h1, h2, hu]
  have hcard := card_le_of_coverPred hcov G P hPnorm hsep
  have hcardR : (2 * (q:ℝ) + 1) ^ k ≤ (m : ℝ) := by
    rw [← hGcard]; exact_mod_cast hcard
  calc Q ^ k ≤ (2 * (q:ℝ) + 1) ^ k := pow_le_pow_left₀ hQpos.le hQ2q k
    _ ≤ (m : ℝ) := hcardR

/-- A dense sequence meets every point of the closed unit ball from inside it. -/
theorem exists_dense_unit {D : ℕ → X} (hD : DenseRange D) {x : X} (hx : ‖x‖ ≤ 1) {η : ℝ}
    (hη : 0 < η) : ∃ j, ‖D j‖ ≤ 1 ∧ ‖x - D j‖ < η := by
  set θ : ℝ := min η 1 / 2 with hθ
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 1 / 2 := by
    rw [hθ]; have : min η 1 ≤ 1 := min_le_right _ _; linarith
  have hθη : θ < η := by
    rw [hθ]
    have h1 : min η 1 ≤ η := min_le_left _ _
    have h2 : 0 < min η 1 := lt_min hη one_pos
    linarith
  set x' : X := (1 - θ) • x with hx'
  have hx'norm : ‖x'‖ ≤ 1 - θ := by
    rw [hx', norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    calc (1 - θ) * ‖x‖ ≤ (1 - θ) * 1 := by
          exact mul_le_mul_of_nonneg_left hx (by linarith)
      _ = 1 - θ := mul_one _
  have hxx' : ‖x - x'‖ ≤ θ := by
    have : x - x' = θ • x := by rw [hx']; module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hθpos]
    calc θ * ‖x‖ ≤ θ * 1 := mul_le_mul_of_nonneg_left hx hθpos.le
      _ = θ := mul_one _
  obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp hD x' (min θ (η - θ)) (by
    refine lt_min hθpos ?_; linarith)
  refine ⟨j, ?_, ?_⟩
  · have h1 : ‖D j - x'‖ < θ := by
      have h := lt_of_lt_of_le hj (min_le_left _ _)
      rw [dist_comm] at h
      simpa [dist_eq_norm] using h
    calc ‖D j‖ ≤ ‖x'‖ + ‖D j - x'‖ := by simpa using norm_le_norm_add_norm_sub' (D j) x'
      _ ≤ (1 - θ) + θ := by linarith [hx'norm]
      _ = 1 := by ring
  · have h2 : ‖x' - D j‖ < η - θ := by
      have := lt_of_lt_of_le hj (min_le_right _ _)
      simpa [dist_eq_norm] using this
    calc ‖x - D j‖ ≤ ‖x - x'‖ + ‖x' - D j‖ := by
          simpa using norm_sub_le_norm_sub_add_norm_sub x x' (D j)
      _ < θ + (η - θ) := by linarith
      _ = η := by ring

/-- The covering radius is computed by centres drawn from a dense sequence and tested on a dense
sequence of points of the unit ball. -/
theorem coverRad_lt_iff {D : ℕ → X} (hD : DenseRange D) (T : X →L[ℝ] X) {m : ℕ} (hm : 1 ≤ m)
    {a : ℝ} :
    coverRad T m < a ↔ ∃ q : ℚ, 0 < q ∧ (q : ℝ) < a ∧ ∃ F : Finset ℕ, F.card ≤ m ∧
      ∀ j : ℕ, ‖D j‖ ≤ 1 → ∃ i ∈ F, ‖T (D j) - D i‖ < q := by
  classical
  constructor
  · intro hlt
    have hpos : 0 ≤ coverRad T m := coverRad_nonneg T m
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hqpos : 0 < (q:ℝ) := lt_of_le_of_lt hpos hq1
    set t : ℝ := (coverRad T m + (q:ℝ)) / 2 with ht
    have htlow : coverRad T m < t := by rw [ht]; linarith
    have hthigh : t < (q:ℝ) := by rw [ht]; linarith
    obtain ⟨Y, hYcard, hY⟩ := coverPred_of_coverRad_lt hm htlow
    -- move the centres onto the dense sequence
    have hchoice : ∀ y : X, ∃ i : ℕ, ‖y - D i‖ < ((q:ℝ) - t) / 2 := by
      intro y
      obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp hD y (((q:ℝ) - t)/2) (by linarith)
      exact ⟨i, by simpa [dist_eq_norm] using hi⟩
    choose idx hidx using hchoice
    refine ⟨q, by exact_mod_cast hqpos, hq2, Y.image idx, le_trans Finset.card_image_le hYcard, ?_⟩
    intro j hj
    obtain ⟨y, hyY, hy⟩ := hY (D j) hj
    refine ⟨idx y, Finset.mem_image_of_mem _ hyY, ?_⟩
    calc ‖T (D j) - D (idx y)‖ ≤ ‖T (D j) - y‖ + ‖y - D (idx y)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < (q:ℝ) := by have := hidx y; linarith
  · rintro ⟨q, hqpos, hqa, F, hFcard, hF⟩
    have hqR : (0:ℝ) < q := by exact_mod_cast hqpos
    -- `F` is nonempty, since some dense point lies in the unit ball
    obtain ⟨j0, hj0, -⟩ := exists_dense_unit hD (x := (0:X)) (by simp) one_pos
    obtain ⟨i0, hi0F, -⟩ := hF j0 hj0
    have hFne : F.Nonempty := ⟨i0, hi0F⟩
    have hcov : coverPred T (q:ℝ) m := by
      refine ⟨F.image D, le_trans Finset.card_image_le hFcard, ?_⟩
      intro x hx
      -- the minimum distance to the chosen centres is at most `q`
      set M : ℝ := (F.image (fun i => ‖T x - D i‖)).min' (by
        exact (Finset.image_nonempty).mpr hFne) with hM
      have hMle : M ≤ (q:ℝ) := by
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨j, hj1, hj2⟩ := exists_dense_unit hD hx
          (η := ε / (‖T‖ + 1)) (by positivity)
        obtain ⟨i, hiF, hi⟩ := hF j hj1
        have hstep : ‖T x - D i‖ ≤ ‖T (D j) - D i‖ + ‖T‖ * ‖x - D j‖ := by
          have h1 : ‖T x - T (D j)‖ ≤ ‖T‖ * ‖x - D j‖ := by
            have := T.le_opNorm (x - D j)
            simpa using this
          calc ‖T x - D i‖ ≤ ‖T x - T (D j)‖ + ‖T (D j) - D i‖ :=
                norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ ‖T‖ * ‖x - D j‖ + ‖T (D j) - D i‖ := by linarith
            _ = ‖T (D j) - D i‖ + ‖T‖ * ‖x - D j‖ := by ring
        have hmin : M ≤ ‖T x - D i‖ :=
          Finset.min'_le _ _ (Finset.mem_image_of_mem _ hiF)
        have hlast : ‖T‖ * ‖x - D j‖ ≤ ε := by
          have h0 : (0:ℝ) < ‖T‖ + 1 := by positivity
          have := mul_le_mul_of_nonneg_left hj2.le (norm_nonneg T)
          calc ‖T‖ * ‖x - D j‖ ≤ ‖T‖ * (ε / (‖T‖ + 1)) := this
            _ ≤ ε := by
                rw [mul_div_assoc'] at *
                rw [div_le_iff₀ h0]
                nlinarith [norm_nonneg T, hε.le]
        linarith
      obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp (Finset.min'_mem
        (F.image (fun i => ‖T x - D i‖)) (by exact (Finset.image_nonempty).mpr hFne))
      exact ⟨D v, Finset.mem_image_of_mem _ hv, by rw [hveq]; exact hMle⟩
    exact lt_of_le_of_lt (coverRad_le_of_coverPred hqR.le hcov) hqa

/-- **The covering radius of a strongly measurable family is measurable.** Both the centres and
the test points may be taken from a dense sequence, which turns the condition into a countable
combination of measurable ones. -/
theorem measurable_coverRad {Ω : Type*} [MeasurableSpace Ω] [SeparableSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {A : Ω → X →L[ℝ] X} (hA : ∀ x : X, Measurable fun ω => A ω x) {m : ℕ} (hm : 1 ≤ m) :
    Measurable fun ω => coverRad (A ω) m := by
  classical
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq X
  refine measurable_of_Iio fun a => ?_
  have hset : (fun ω => coverRad (A ω) m) ⁻¹' Set.Iio a
      = ⋃ q : ℚ, ⋃ (_ : 0 < q), ⋃ (_ : (q:ℝ) < a), ⋃ F : Finset ℕ, ⋃ (_ : F.card ≤ m),
          {ω | ∀ j : ℕ, ‖D j‖ ≤ 1 → ∃ i ∈ F, ‖A ω (D j) - D i‖ < q} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_ofPred_eq]
    rw [coverRad_lt_iff hD (A ω) hm]
    constructor
    · rintro ⟨q, hq0, hqa, F, hFc, hF⟩; exact ⟨q, hq0, hqa, F, hFc, hF⟩
    · rintro ⟨q, hq0, hqa, F, hFc, hF⟩; exact ⟨q, hq0, hqa, F, hFc, hF⟩
  rw [hset]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun F => MeasurableSet.iUnion fun _ => ?_
  have : {ω | ∀ j : ℕ, ‖D j‖ ≤ 1 → ∃ i ∈ F, ‖A ω (D j) - D i‖ < (q:ℝ)}
      = ⋂ j : ℕ, {ω | ‖D j‖ ≤ 1 → ∃ i ∈ F, ‖A ω (D j) - D i‖ < (q:ℝ)} := by
    ext ω; simp [Set.mem_iInter]
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  by_cases hj : ‖D j‖ ≤ 1
  · have heq : {ω | ‖D j‖ ≤ 1 → ∃ i ∈ F, ‖A ω (D j) - D i‖ < (q:ℝ)}
        = ⋃ i ∈ F, {ω | ‖A ω (D j) - D i‖ < (q:ℝ)} := by
      ext ω; simp [hj, Set.mem_iUnion]
    rw [heq]
    refine MeasurableSet.biUnion F.countable_toSet fun i _ => ?_
    have hmeas : Measurable fun ω => dist (A ω (D j)) (D i) :=
      (hA (D j)).dist measurable_const
    have heq2 : {ω | ‖A ω (D j) - D i‖ < (q:ℝ)}
        = (fun ω => dist (A ω (D j)) (D i)) ⁻¹' Set.Iio (q:ℝ) := by
      ext ω; simp [dist_eq_norm]
    rw [heq2]
    exact hmeas measurableSet_Iio
  · have heq : {ω | ‖D j‖ ≤ 1 → ∃ i ∈ F, ‖A ω (D j) - D i‖ < (q:ℝ)} = Set.univ := by
      ext ω; simp [hj]
    rw [heq]; exact MeasurableSet.univ

/-! ## The covering family of a cocycle -/

section Cocycle

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- The covering radius is antitone in the number of balls. -/
theorem coverRad_anti (T : X →L[ℝ] X) {m m' : ℕ} (hm : 1 ≤ m) (hmm : m ≤ m') :
    coverRad T m' ≤ coverRad T m := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h : coverPred T (coverRad T m + ε) m :=
    coverPred_of_coverRad_lt hm (by linarith)
  obtain ⟨Y, hcard, hY⟩ := h
  have h' : coverPred T (coverRad T m + ε) m' := ⟨Y, hcard.trans hmm, hY⟩
  have h0 : 0 ≤ coverRad T m + ε := by have := coverRad_nonneg T m; linarith
  exact coverRad_le_of_coverPred h0 h'

/-- **The covering family of a cocycle**, floored at `e^{-Mn}` so as to be real-valued
everywhere: `log max(coverRad(𝓛^{(n)}_ω, b^n), e^{-Mn})`. -/
noncomputable def Cocycle.covFam (R : Cocycle Ω X) (b M : ℕ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.log (max (coverRad (R.iterate n ω) (b ^ n)) (Real.exp (-(M : ℝ) * n)))

/-- The covering family is genuinely subadditive: covering numbers are submultiplicative, and the
floor `e^{-Mn}` is itself multiplicative. -/
theorem Cocycle.covFam_subadditive (R : Cocycle Ω X) {b : ℕ} (hb : 1 ≤ b) (M : ℕ) (m n : ℕ)
    (ω : Ω) :
    R.covFam b M (m + n) ω ≤ R.covFam b M m (R.σ^[n] ω) + R.covFam b M n ω := by
  have hbm : 1 ≤ b ^ m := Nat.one_le_pow _ _ hb
  have hbn : 1 ≤ b ^ n := Nat.one_le_pow _ _ hb
  have hiter : R.iterate (m + n) ω = (R.iterate m (R.σ^[n] ω)).comp (R.iterate n ω) :=
    R.iterate_add m n ω
  have hsub : coverRad (R.iterate (m + n) ω) (b ^ (m + n))
      ≤ coverRad (R.iterate n ω) (b ^ n) * coverRad (R.iterate m (R.σ^[n] ω)) (b ^ m) := by
    rw [hiter, pow_add, mul_comm (b ^ m) (b ^ n)]
    exact coverRad_comp _ _ hbn hbm
  have hexp : Real.exp (-(M : ℝ) * (m + n)) =
      Real.exp (-(M : ℝ) * m) * Real.exp (-(M : ℝ) * n) := by
    rw [← Real.exp_add]; ring_nf
  have hkey := log_max_le_of_le_mul (K := 1) (P := coverRad (R.iterate (m + n) ω) (b ^ (m + n)))
    (Q := coverRad (R.iterate m (R.σ^[n] ω)) (b ^ m)) (R := coverRad (R.iterate n ω) (b ^ n))
    (a := Real.exp (-(M : ℝ) * m)) (b := Real.exp (-(M : ℝ) * n)) le_rfl
    (coverRad_nonneg _ _) (coverRad_nonneg _ _) (Real.exp_pos _) (Real.exp_pos _)
    (by rw [one_mul]; rw [mul_comm]; exact hsub)
  simp only [Cocycle.covFam]
  rw [show ((m + n : ℕ) : ℝ) = (m : ℝ) + (n : ℝ) by push_cast; ring]
  calc Real.log (max (coverRad (R.iterate (m + n) ω) (b ^ (m + n)))
        (Real.exp (-(M : ℝ) * ((m:ℝ) + (n:ℝ)))))
      = Real.log (max (coverRad (R.iterate (m + n) ω) (b ^ (m + n)))
          (Real.exp (-(M : ℝ) * m) * Real.exp (-(M : ℝ) * n))) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.log (max (coverRad (R.iterate m (R.σ^[n] ω)) (b ^ m)) (Real.exp (-(M : ℝ) * m)))
        + Real.log (max (coverRad (R.iterate n ω) (b ^ n)) (Real.exp (-(M : ℝ) * n)))
        + Real.log 1 := hkey
    _ = _ := by rw [Real.log_one, add_zero]

theorem Cocycle.measurable_covFam (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {b : ℕ} (hb : 1 ≤ b) (M n : ℕ) : Measurable (R.covFam b M n) := by
  have h1 : Measurable fun ω => coverRad (R.iterate n ω) (b ^ n) :=
    measurable_coverRad (R.measurable_iterate_apply n) (Nat.one_le_pow _ _ hb)
  exact Real.measurable_log.comp (h1.max measurable_const)

/-- The floored covering radius is below the floored operator norm. -/
theorem Cocycle.covFam_le (R : Cocycle Ω X) {b : ℕ} (hb : 1 ≤ b) (M n : ℕ) (ω : Ω) :
    R.covFam b M n ω ≤ Real.log (max ‖R.iterate n ω‖ 1) := by
  have hb' : 1 ≤ b ^ n := Nat.one_le_pow _ _ hb
  have h1 : coverRad (R.iterate n ω) (b ^ n) ≤ ‖R.iterate n ω‖ := coverRad_le_opNorm _ hb'
  have h2 : Real.exp (-(M : ℝ) * n) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (0:ℝ) ≤ (M:ℝ) * n := by positivity
    linarith
  have hmax : max (coverRad (R.iterate n ω) (b ^ n)) (Real.exp (-(M : ℝ) * n))
      ≤ max ‖R.iterate n ω‖ 1 := max_le_max h1 h2
  have hpos : 0 < max (coverRad (R.iterate n ω) (b ^ n)) (Real.exp (-(M : ℝ) * n)) :=
    lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  exact Real.log_le_log hpos hmax

theorem Cocycle.covFam_ge (R : Cocycle Ω X) (b M n : ℕ) (ω : Ω) :
    -(M : ℝ) * n ≤ R.covFam b M n ω := by
  have h : Real.exp (-(M : ℝ) * n) ≤ max (coverRad (R.iterate n ω) (b ^ n))
      (Real.exp (-(M : ℝ) * n)) := le_max_right _ _
  have hpos : 0 < Real.exp (-(M : ℝ) * n) := Real.exp_pos _
  calc -(M : ℝ) * n = Real.log (Real.exp (-(M : ℝ) * n)) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log hpos h

/-- The log-norm of an iterate is dominated by the Birkhoff sum of the one-step log-norms. -/
theorem Cocycle.log_norm_iterate_le (R : Cocycle Ω X) (n : ℕ) (ω : Ω) :
    Real.log (max ‖R.iterate n ω‖ 1) ≤
      ∑ i ∈ Finset.range n, Real.log (max ‖R.L (R.σ^[i] ω)‖ 1) := by
  induction n with
  | zero =>
    have h : ‖(ContinuousLinearMap.id ℝ X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    simp [Cocycle.iterate, max_eq_right h]
  | succ n ih =>
    have hstep : ‖R.iterate (n + 1) ω‖ ≤ ‖R.L (R.σ^[n] ω)‖ * ‖R.iterate n ω‖ := by
      rw [show R.iterate (n + 1) ω = (R.L (R.σ^[n] ω)).comp (R.iterate n ω) from rfl]
      exact ContinuousLinearMap.opNorm_comp_le _ _
    have hmax : max ‖R.iterate (n + 1) ω‖ 1
        ≤ max ‖R.L (R.σ^[n] ω)‖ 1 * max ‖R.iterate n ω‖ 1 := by
      refine max_le ?_ ?_
      · calc ‖R.iterate (n + 1) ω‖ ≤ ‖R.L (R.σ^[n] ω)‖ * ‖R.iterate n ω‖ := hstep
          _ ≤ max ‖R.L (R.σ^[n] ω)‖ 1 * max ‖R.iterate n ω‖ 1 :=
              mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _)
                (le_trans (norm_nonneg _) (le_max_left _ _))
      · have h1 : (1:ℝ) ≤ max ‖R.L (R.σ^[n] ω)‖ 1 := le_max_right _ _
        have h2 : (1:ℝ) ≤ max ‖R.iterate n ω‖ 1 := le_max_right _ _
        nlinarith
    have hpos1 : (0:ℝ) < max ‖R.iterate (n+1) ω‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hpos2 : (0:ℝ) < max ‖R.L (R.σ^[n] ω)‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hpos3 : (0:ℝ) < max ‖R.iterate n ω‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    calc Real.log (max ‖R.iterate (n+1) ω‖ 1)
        ≤ Real.log (max ‖R.L (R.σ^[n] ω)‖ 1 * max ‖R.iterate n ω‖ 1) :=
          Real.log_le_log hpos1 hmax
      _ = Real.log (max ‖R.L (R.σ^[n] ω)‖ 1) + Real.log (max ‖R.iterate n ω‖ 1) :=
          Real.log_mul (ne_of_gt hpos2) (ne_of_gt hpos3)
      _ ≤ Real.log (max ‖R.L (R.σ^[n] ω)‖ 1) + ∑ i ∈ Finset.range n,
            Real.log (max ‖R.L (R.σ^[i] ω)‖ 1) := by linarith [ih]
      _ = ∑ i ∈ Finset.range (n+1), Real.log (max ‖R.L (R.σ^[i] ω)‖ 1) := by
          rw [Finset.sum_range_succ]; ring

theorem Cocycle.integrable_log_norm_iterate (R : Cocycle Ω X)
    (n : ℕ) : Integrable (fun ω => ∑ i ∈ Finset.range n,
      Real.log (max ‖R.L (R.σ^[i] ω)‖ 1)) R.μ := by
  have hmp : MeasurePreserving (⇑R.σ) R.μ R.μ := R.ergodic.toMeasurePreserving
  refine integrable_finsetSum _ (fun i _ => ?_)
  exact (hmp.iterate i).integrable_comp_of_integrable R.forwardIntegrable

theorem Cocycle.integrable_covFam (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {b : ℕ} (hb : 1 ≤ b) (M n : ℕ) : Integrable (R.covFam b M n) R.μ := by
  have hΨnn : ∀ ω, (0:ℝ) ≤ ∑ i ∈ Finset.range n, Real.log (max ‖R.L (R.σ^[i] ω)‖ 1) := by
    intro ω
    exact Finset.sum_nonneg fun i _ => Real.log_nonneg (le_max_right _ _)
  refine Integrable.mono'
    ((R.integrable_log_norm_iterate n).add (integrable_const ((M:ℝ) * n)))
    ((R.measurable_covFam hb M n).aestronglyMeasurable) ?_
  filter_upwards with ω
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have h1 := R.covFam_ge b M n ω
    have h2 := hΨnn ω
    have : (0:ℝ) ≤ (M:ℝ) * n := by positivity
    linarith
  · have h1 := (R.covFam_le hb M n ω).trans (R.log_norm_iterate_le n ω)
    have : (0:ℝ) ≤ (M:ℝ) * n := by positivity
    linarith

theorem Cocycle.exists_covFam_limit (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {b : ℕ} (hb : 1 ≤ b) (M : ℕ) :
    ∃ C : EReal, C < ⊤ ∧
      (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => ((R.covFam b M n ω / n : ℝ) : EReal)) atTop (nhds C)) ∧
      (∀ N : ℕ, 1 ≤ N → C ≤ (((∫ ω, R.covFam b M N ω ∂(R.μ)) / N : ℝ) : EReal)) := by
  have hsub : SubadditiveFamily (⇑R.σ) (R.covFam b M) :=
    ⟨fun n => R.measurable_covFam hb M n, fun m n ω => R.covFam_subadditive hb M m n ω⟩
  have h1 : Integrable (fun ω => max (R.covFam b M 1 ω) 0) R.μ :=
    (R.integrable_covFam hb M 1).sup (integrable_const 0)
  obtain ⟨C, hCtop, hae, hmean, -⟩ := kingman R.μ (⇑R.σ) R.ergodic (R.covFam b M) hsub h1
  refine ⟨C, hCtop, ?_, fun N hN => ?_⟩
  · filter_upwards [hae] with ω hω
    refine hω.congr fun n => ?_
    rw [coe_div_natCast]
  · have hm := hmean N hN
    have hint : Integrable (fun ω => R.covFam b M N ω / N) R.μ :=
      (R.integrable_covFam hb M N).div_const _
    rw [lowerIntegral_eq_integral hint] at hm
    rw [integral_div] at hm
    exact hm

/-- **A level at which most points admit a cover of controlled cardinality.** -/
theorem Cocycle.exists_good_cover_level (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {κ : EReal} (hκ : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal (compactSeminorm (R.iterate n ω)) / (n : EReal)) atTop (nhds κ))
    {c : ℝ} (hc : κ < (c : EReal)) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N bb : ℕ, 1 ≤ N ∧ 1 ≤ bb ∧
      R.μ {ω | ¬ (coverRad (R.iterate N ω) (bb ^ N) ≤ Real.exp (c * N))} ≤ δ := by
  classical
  set P : ℕ → ℕ → Set Ω :=
    fun N bb => {ω | coverRad (R.iterate N ω) (bb ^ N) ≤ Real.exp (c * N)} with hP
  have hPmeas : ∀ N bb, 1 ≤ bb → MeasurableSet (P N bb) := by
    intro N bb hbb
    exact measurableSet_le
      (measurable_coverRad (R.measurable_iterate_apply N) (Nat.one_le_pow _ _ hbb))
      measurable_const
  set B : ℕ → Set Ω := fun N => ⋃ bb : ℕ, P N (bb + 1) with hB
  have hBmeas : ∀ N, MeasurableSet (B N) := fun N =>
    MeasurableSet.iUnion fun bb => hPmeas N (bb + 1) (by omega)
  -- almost every `ω` is in `B N` for all large `N`
  have hae : ∀ᵐ ω ∂(R.μ), ∀ᶠ N : ℕ in atTop, ω ∈ B N := by
    filter_upwards [hκ] with ω hω
    have hev := eventually_lt_exp_of_tendsto hc hω
    filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
    obtain ⟨m, hm1, hmcov⟩ := exists_coverPred_of_compactSeminorm_lt (R.iterate N ω) hN
    have hmN : m ≤ m ^ N := Nat.le_self_pow (by omega) m
    have h1 : coverRad (R.iterate N ω) m ≤ Real.exp (c * N) :=
      coverRad_le_of_coverPred (Real.exp_pos _).le hmcov
    have h2 : coverRad (R.iterate N ω) (m ^ N) ≤ coverRad (R.iterate N ω) m :=
      coverRad_anti _ hm1 hmN
    refine Set.mem_iUnion.mpr ⟨m - 1, ?_⟩
    have : m - 1 + 1 = m := by omega
    rw [this]
    exact le_trans h2 h1
  -- the sets where this holds from `M` on increase to a conull set
  set C : ℕ → Set Ω := fun M => ⋂ N ∈ Set.Ici M, B N with hC
  have hCmeas : ∀ M, MeasurableSet (C M) := fun M =>
    MeasurableSet.biInter (Set.to_countable _) fun N _ => hBmeas N
  have hCmono : Monotone C := by
    intro M M' hMM ω hω
    simp only [hC, Set.mem_iInter₂, Set.mem_Ici] at hω ⊢
    exact fun N hN => hω N (le_trans hMM hN)
  have hCunion : R.μ (⋃ M, C M) = 1 := by
    have hmem : ∀ᵐ ω ∂(R.μ), ω ∈ ⋃ M, C M := by
      filter_upwards [hae] with ω hω
      obtain ⟨M, hM⟩ := eventually_atTop.mp hω
      refine Set.mem_iUnion.mpr ⟨M, ?_⟩
      simp only [hC, Set.mem_iInter₂, Set.mem_Ici]
      exact fun N hN => hM N hN
    have h3 : MeasurableSet (⋃ M, C M) := MeasurableSet.iUnion hCmeas
    have h2 : R.μ ((⋃ M, C M)ᶜ) = 0 := ae_iff.mp hmem
    exact (prob_compl_eq_zero_iff h3).mp h2
  -- pick `M` with `μ (C M)ᶜ ≤ δ`, using that the complements shrink to a null set
  have hinter : (⋂ M, (C M)ᶜ) = (⋃ M, C M)ᶜ := by
    rw [Set.compl_iUnion]
  have hnull : R.μ (⋂ M, (C M)ᶜ) = 0 := by
    rw [hinter]
    have h3 : MeasurableSet (⋃ M, C M) := MeasurableSet.iUnion hCmeas
    exact (prob_compl_eq_zero_iff h3).mpr hCunion
  have htend : Tendsto (fun M => R.μ (C M)ᶜ) atTop (nhds (R.μ (⋂ M, (C M)ᶜ))) :=
    tendsto_measure_iInter_atTop (fun M => ((hCmeas M).compl).nullMeasurableSet)
      (fun M M' h => Set.compl_subset_compl.mpr (hCmono h)) ⟨0, measure_ne_top _ _⟩
  rw [hnull] at htend
  obtain ⟨M, hM⟩ := ((tendsto_order.mp htend).2 δ hδ).exists
  set N : ℕ := max M 1 with hN
  have hN1 : 1 ≤ N := le_max_right _ _
  have hCB : C M ⊆ B N := by
    intro ω hω
    simp only [hC, Set.mem_iInter₂, Set.mem_Ici] at hω
    exact hω N (le_max_left _ _)
  have hBcompl : R.μ (B N)ᶜ < δ :=
    lt_of_le_of_lt (measure_mono (Set.compl_subset_compl.mpr hCB)) hM
  -- now increase the number of balls until most points are covered
  have hPmono : Antitone (fun bb : ℕ => (P N (bb + 1))ᶜ) := by
    intro bb bb' h
    refine Set.compl_subset_compl.mpr ?_
    intro ω hω
    simp only [hP, Set.mem_ofPred_eq] at hω ⊢
    refine le_trans (coverRad_anti _ (Nat.one_le_pow _ _ (by omega)) ?_) hω
    exact Nat.pow_le_pow_left (by omega) N
  have hPinter : (⋂ bb : ℕ, (P N (bb + 1))ᶜ) = (B N)ᶜ := by
    rw [hB, Set.compl_iUnion]
  have htendP : Tendsto (fun bb : ℕ => R.μ (P N (bb + 1))ᶜ) atTop
      (nhds (R.μ (⋂ bb : ℕ, (P N (bb + 1))ᶜ))) :=
    tendsto_measure_iInter_atTop (fun bb => ((hPmeas N (bb+1) (by omega)).compl).nullMeasurableSet)
      hPmono ⟨0, measure_ne_top _ _⟩
  rw [hPinter] at htendP
  obtain ⟨bb, hbb⟩ := ((tendsto_order.mp htendP).2 δ hBcompl).exists
  exact ⟨N, bb + 1, hN1, by omega, hbb.le⟩

/-- The mean of the covering family at a good level. -/
theorem Cocycle.integral_covFam_le (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {N bb M : ℕ} (hbb : 1 ≤ bb) {c' : ℝ} (hM : -(M : ℝ) ≤ c')
    {G : Set Ω} (hGm : MeasurableSet G)
    (hG : ∀ ω ∈ G, coverRad (R.iterate N ω) (bb ^ N) ≤ Real.exp (c' * N))
    {η : ℝ} (hη : ∀ i : ℕ, ∫ ω in Gᶜ, Real.log (max ‖R.L (R.σ^[i] ω)‖ 1) ∂(R.μ) ≤ η) :
    ∫ ω, R.covFam bb M N ω ∂(R.μ) ≤ c' * N * (R.μ G).toReal + N * η := by
  set Ψ : Ω → ℝ := fun ω => ∑ i ∈ Finset.range N, Real.log (max ‖R.L (R.σ^[i] ω)‖ 1) with hΨ
  have hΨint : Integrable Ψ R.μ := R.integrable_log_norm_iterate N
  have hint := R.integrable_covFam hbb M N
  -- pointwise: `c'N` on `G`, `Ψ` off `G`
  have hptG : ∀ ω ∈ G, R.covFam bb M N ω ≤ c' * N := by
    intro ω hω
    have h1 : max (coverRad (R.iterate N ω) (bb ^ N)) (Real.exp (-(M : ℝ) * N))
        ≤ Real.exp (c' * N) := by
      refine max_le (hG ω hω) (Real.exp_le_exp.mpr ?_)
      have : (0:ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    have hpos : 0 < max (coverRad (R.iterate N ω) (bb ^ N)) (Real.exp (-(M : ℝ) * N)) :=
      lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
    calc R.covFam bb M N ω ≤ Real.log (Real.exp (c' * N)) := Real.log_le_log hpos h1
      _ = c' * N := Real.log_exp _
  have hptGc : ∀ ω, R.covFam bb M N ω ≤ Ψ ω := fun ω =>
    (R.covFam_le hbb M N ω).trans (R.log_norm_iterate_le N ω)
  have hsplit := (integral_add_compl hGm hint).symm
  rw [hsplit]
  have h1 : ∫ ω in G, R.covFam bb M N ω ∂(R.μ) ≤ ∫ ω in G, c' * N ∂(R.μ) :=
    setIntegral_mono_on hint.integrableOn (integrable_const _) hGm hptG
  have h2 : ∫ ω in Gᶜ, R.covFam bb M N ω ∂(R.μ) ≤ ∫ ω in Gᶜ, Ψ ω ∂(R.μ) :=
    setIntegral_mono hint.integrableOn hΨint.integrableOn hptGc
  have h3 : ∫ ω in Gᶜ, Ψ ω ∂(R.μ) ≤ N * η := by
    rw [hΨ, integral_finsetSum]
    · calc ∑ i ∈ Finset.range N, ∫ ω in Gᶜ, Real.log (max ‖R.L (R.σ^[i] ω)‖ 1) ∂(R.μ)
          ≤ ∑ _i ∈ Finset.range N, η := Finset.sum_le_sum fun i _ => hη i
        _ = N * η := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · intro i _
      have hmp : MeasurePreserving (⇑R.σ) R.μ R.μ := R.ergodic.toMeasurePreserving
      exact ((hmp.iterate i).integrable_comp_of_integrable R.forwardIntegrable).integrableOn
  have h4 : ∫ ω in G, c' * N ∂(R.μ) = c' * N * (R.μ G).toReal := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def]; ring
  linarith
/-- **Many fast directions are incompatible with few balls.** If `𝓛^{(n)}_ω(𝔹_X)` is eventually
covered by `b^n` balls of radius `e^{n b₁}`, then every `χ_k` with `k ε > log b` is at most
`b₁ + ε`. -/
theorem Cocycle.chi_le_of_eventually_cover (R : Cocycle Ω X) {ω : Ω} {bb : ℕ} (hbb : 1 ≤ bb)
    {b₁ ε : ℝ} (_hε : 0 < ε)
    (hcov : ∀ᶠ n : ℕ in atTop, coverPred (R.iterate n ω) (Real.exp (b₁ * n)) (bb ^ n))
    {k : ℕ} (hk : 1 ≤ k) (hkε : Real.log bb < k * ε)
    (hχ : Tendsto (fun n : ℕ => logEReal (bernsteinNumber (R.iterate n ω) k) / (n : EReal))
      atTop (nhds (R.chi k ω))) :
    R.chi k ω ≤ ((b₁ + ε : ℝ) : EReal) := by
  by_contra hlt
  rw [not_le] at hlt
  set a : ℝ := b₁ + ε with ha
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hbbR : (1:ℝ) ≤ bb := by exact_mod_cast hbb
  have hlogbb : 0 ≤ Real.log bb := Real.log_nonneg hbbR
  have hgap : 0 < (k:ℝ) * ε - Real.log bb := by linarith
  have h3k : (0:ℝ) < 3 * k := by positivity
  set N₀ : ℕ := ⌈(k:ℝ) * Real.log (3 * k) / ((k:ℝ) * ε - Real.log bb)⌉₊ + 1 with hN₀
  have hev : ∀ᶠ n : ℕ in atTop, (a : EReal) <
      logEReal (bernsteinNumber (R.iterate n ω) k) / (n : EReal) :=
    hχ.eventually (lt_mem_nhds hlt)
  obtain ⟨n, ⟨hρ, hcn⟩, hn⟩ := ((hev.and hcov).and (eventually_ge_atTop N₀)).exists
  have hn1 : 1 ≤ n := le_trans (by omega) hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn1
  have hρ' : Real.exp (a * n) < bernsteinNumber (R.iterate n ω) k :=
    (lt_logEReal_div_iff hn1 a).mp hρ
  -- a `k`-dimensional subspace growing faster than `e^{an}`
  have hpos : 0 < bernsteinNumber (R.iterate n ω) k := lt_trans (Real.exp_pos _) hρ'
  have := nonempty_grassmannianFin_of_bernstein_pos hpos
  obtain ⟨_, ⟨V, rfl⟩, hV⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hρ'
  have : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
  have hcount := pow_le_of_coverPred hk V.2.2 (Real.exp_pos (a * n)) hV.le
    (Real.exp_pos (b₁ * n)) hcn
  -- take logarithms
  have hL : 0 < Real.exp (a * n) / (3 * k * Real.exp (b₁ * n)) := by positivity
  have hlog := Real.log_le_log (pow_pos hL k) hcount
  have hR : ((bb ^ n : ℕ) : ℝ) = (bb : ℝ) ^ n := by push_cast; ring
  rw [hR, Real.log_pow, Real.log_pow, Real.log_div (Real.exp_pos _).ne'
    (by positivity), Real.log_mul h3k.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_exp] at hlog
  -- `k (ε n - log 3k) ≤ n log b`, impossible for `n ≥ N₀`
  have hN₀le : (k:ℝ) * Real.log (3 * k) / ((k:ℝ) * ε - Real.log bb) < n := by
    have h1 := Nat.le_ceil ((k:ℝ) * Real.log (3 * k) / ((k:ℝ) * ε - Real.log bb))
    have h2 : ((N₀ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    rw [hN₀] at h2; push_cast at h2
    linarith
  rw [div_lt_iff₀ hgap] at hN₀le
  rw [ha] at hlog
  nlinarith [hlog, hN₀le]

/-- **`ν ≤ κ`**, in the form: `ν ≤ c` almost everywhere for every real `c > κ`. -/
theorem Cocycle.ae_nu_le_of_compactnessIndex_lt (R : Cocycle Ω X) [SeparableSpace X]
    [BorelSpace X] {κ : EReal} (hκ : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal (compactSeminorm (R.iterate n ω)) / (n : EReal)) atTop (nhds κ))
    {c : ℝ} (hc : κ < (c : EReal)) : ∀ᵐ ω ∂(R.μ), R.nu ω ≤ (c : EReal) := by
  obtain ⟨c', hκc', hc'c⟩ := EReal.lt_iff_exists_real_btwn.mp hc
  have hc'cR : c' < c := EReal.coe_lt_coe_iff.mp hc'c
  set ε : ℝ := (c - c') / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set g : Ω → ℝ := fun ω => Real.log (max ‖R.L ω‖ 1) with hg
  obtain ⟨δr, hδr, habs⟩ :=
    exists_delta_setIntegral_abs_le (μ := R.μ) g R.forwardIntegrable (ε := ε / 2) (by positivity)
  set δ' : ℝ := min δr (ε / (|c'| + 1)) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδr (by positivity)
  obtain ⟨N, bb, hN1, hbb, hGc⟩ :=
    R.exists_good_cover_level hκ hκc' (δ := ENNReal.ofReal δ') (by simpa using hδ'pos)
  set G : Set Ω := {ω | coverRad (R.iterate N ω) (bb ^ N) ≤ Real.exp (c' * N)} with hG
  have hGm : MeasurableSet G := measurableSet_le
    (measurable_coverRad (R.measurable_iterate_apply N) (Nat.one_le_pow _ _ hbb))
    measurable_const
  have hGcμ : R.μ Gᶜ ≤ ENNReal.ofReal δ' := by
    have : Gᶜ = {ω | ¬ (coverRad (R.iterate N ω) (bb ^ N) ≤ Real.exp (c' * N))} := by
      ext ω; simp [hG]
    rw [this]; exact hGc
  set M : ℕ := ⌈|c'|⌉₊ with hMdef
  have hM : -(M : ℝ) ≤ c' := by
    have h1 : |c'| ≤ (M:ℝ) := Nat.le_ceil _
    have h2 := neg_abs_le c'
    linarith
  -- the one-step log-norm integrates to at most `ε/2` over each translate of `Gᶜ`
  have hη : ∀ i : ℕ, ∫ ω in Gᶜ, Real.log (max ‖R.L (R.σ^[i] ω)‖ 1) ∂(R.μ) ≤ ε / 2 := by
    intro i
    have hGcm : MeasurableSet Gᶜ := hGm.compl
    have hcv := setIntegral_comp_iterate R.σ R.ergodic.toMeasurePreserving hGcm (h := g)
      R.forwardIntegrable i
    simp only [hg] at hcv
    rw [hcv]
    have himg : MeasurableSet ((⇑R.σ)^[i] '' Gᶜ) := by
      have := measurableSet_zIter_image R.σ (i : ℤ) hGcm
      rwa [zIter_natCast_fun] at this
    have hmeas : R.μ ((⇑R.σ)^[i] '' Gᶜ) = R.μ Gᶜ := by
      have := measure_zIter_image R.σ R.ergodic.toMeasurePreserving (i : ℤ) hGcm
      rwa [zIter_natCast_fun] at this
    have hsmall : R.μ ((⇑R.σ)^[i] '' Gᶜ) ≤ ENNReal.ofReal δr := by
      rw [hmeas]
      exact hGcμ.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
    have h1 := habs _ himg hsmall
    refine le_trans (setIntegral_mono_on ?_ ?_ himg fun ω _ => le_abs_self _) h1
    · exact R.forwardIntegrable.integrableOn
    · exact R.forwardIntegrable.abs.integrableOn
  have hint := R.integral_covFam_le (N := N) (M := M) hbb hM hGm (fun ω hω => hω) hη
  -- Kingman for the covering family
  obtain ⟨C, -, hae, hmean⟩ := R.exists_covFam_limit hbb M
  have hNR : (0:ℝ) < N := by exact_mod_cast hN1
  have hμG : 1 - δ' ≤ (R.μ G).toReal := by
    have h1 : (R.μ Gᶜ).toReal ≤ δ' := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hGcμ
      rwa [ENNReal.toReal_ofReal hδ'pos.le] at this
    have h2 : (R.μ G).toReal + (R.μ Gᶜ).toReal = 1 := by
      rw [← measureReal_def, ← measureReal_def, measureReal_add_measureReal_compl hGm]
      simp
    linarith
  have hμG1 : (R.μ G).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := R.μ) (s := G))
    simpa using this
  have hmeanR : (∫ ω, R.covFam bb M N ω ∂(R.μ)) / N ≤ c' + 2 * ε := by
    rw [div_le_iff₀ hNR]
    have hδε : |c'| * δ' ≤ ε := by
      have h1 : δ' ≤ ε / (|c'| + 1) := min_le_right _ _
      have h2 : |c'| * δ' ≤ (|c'| + 1) * δ' := by nlinarith [abs_nonneg c']
      have h3 : (|c'| + 1) * δ' ≤ ε := by
        rw [le_div_iff₀ (by positivity)] at h1; linarith
      linarith
    have hc'G : c' * (R.μ G).toReal ≤ c' + ε := by
      have : c' * (R.μ G).toReal - c' = c' * ((R.μ G).toReal - 1) := by ring
      have hab : |c' * ((R.μ G).toReal - 1)| ≤ |c'| * δ' := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by rw [abs_le]; constructor <;> linarith)
          (abs_nonneg _)
      have := (abs_le.mp (hab.trans hδε)).2
      linarith
    nlinarith [hint, hc'G]
  have hC : C < ((c' + 3 * ε : ℝ) : EReal) := by
    refine lt_of_le_of_lt (hmean N hN1) ?_
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  -- almost every orbit is eventually covered by `bb^n` balls of radius `e^{n(c'+3ε)}`
  set k : ℕ := ⌈Real.log bb / ε⌉₊ + 1 with hk
  have hk1 : 1 ≤ k := by omega
  have hkε : Real.log bb < k * ε := by
    have h1 := Nat.le_ceil (Real.log bb / ε)
    have h2 : (k:ℝ) = (⌈Real.log bb / ε⌉₊ : ℝ) + 1 := by rw [hk]; push_cast; ring
    rw [div_le_iff₀ hεpos] at h1
    rw [h2]; nlinarith
  have : NeZero k := ⟨by omega⟩
  filter_upwards [hae, R.ae_tendsto_chi k] with ω hω hχ
  have hcov : ∀ᶠ n : ℕ in atTop,
      coverPred (R.iterate n ω) (Real.exp ((c' + 3 * ε) * n)) (bb ^ n) := by
    have hev : ∀ᶠ n : ℕ in atTop,
        ((R.covFam bb M n ω / n : ℝ) : EReal) < ((c' + 3 * ε : ℝ) : EReal) :=
      hω.eventually (gt_mem_nhds hC)
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hnR : (0:ℝ) < n := by exact_mod_cast hn1
    have hlt : R.covFam bb M n ω < (c' + 3 * ε) * n := by
      have := EReal.coe_lt_coe_iff.mp hn
      rwa [div_lt_iff₀ hnR] at this
    refine coverPred_of_coverRad_lt (Nat.one_le_pow _ _ hbb) ?_
    have hpos : 0 < max (coverRad (R.iterate n ω) (bb ^ n)) (Real.exp (-(M : ℝ) * n)) :=
      lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
    have : max (coverRad (R.iterate n ω) (bb ^ n)) (Real.exp (-(M : ℝ) * n))
        < Real.exp ((c' + 3 * ε) * n) := by
      rw [← Real.exp_log hpos]
      exact Real.exp_lt_exp.mpr hlt
    exact lt_of_le_of_lt (le_max_left _ _) this
  have hχk := R.chi_le_of_eventually_cover hbb hεpos hcov hk1 hkε hχ
  refine (R.nu_le_chi ω hk1).trans (hχk.trans ?_)
  exact EReal.coe_le_coe_iff.mpr (by rw [hε]; linarith)

/-- **`κ ≤ χ_k`**: the compactness seminorm is dominated by `C_k ρ_k`. -/
theorem Cocycle.ae_le_chi_of_compactnessIndex (R : Cocycle Ω X) [SeparableSpace X]
    [BorelSpace X] {κ : EReal} (hκ : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal (compactSeminorm (R.iterate n ω)) / (n : EReal)) atTop (nhds κ))
    (k : ℕ) [NeZero k] : ∀ᵐ ω ∂(R.μ), κ ≤ R.chi k ω := by
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  set Ck : ℝ := 2 * k * (4 ^ (k - 1) * (Nat.factorial (k - 1) : ℝ)) with hCk
  have hCkpos : 0 < Ck := by rw [hCk]; positivity
  have hdom : ∀ T : X →L[ℝ] X, compactSeminorm T ≤ Ck * bernsteinNumber T k := by
    intro T
    have h1 := compactSeminorm_le_gelfand T hk
    have h2 := gelfand_le_bernstein T hk
    have h0 : (0:ℝ) ≤ 2 * k := by positivity
    calc compactSeminorm T ≤ 2 * k * gelfand T k := h1
      _ ≤ 2 * k * (4 ^ (k - 1) * (Nat.factorial (k - 1) : ℝ) * bernsteinNumber T k) :=
          mul_le_mul_of_nonneg_left h2 h0
      _ = Ck * bernsteinNumber T k := by rw [hCk]; ring
  filter_upwards [hκ, R.ae_tendsto_chi k] with ω hω hχ
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨a, hχa, haκ⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  obtain ⟨b, hab, hbκ⟩ := EReal.lt_iff_exists_real_btwn.mp haκ
  have habR : a < b := EReal.coe_lt_coe_iff.mp hab
  have hev1 := eventually_lt_exp_of_tendsto hχa hχ
  have hev2 : ∀ᶠ n : ℕ in atTop, (b : EReal) <
      logEReal (compactSeminorm (R.iterate n ω)) / (n : EReal) :=
    hω.eventually (lt_mem_nhds hbκ)
  set N₀ : ℕ := ⌈Real.log Ck / (b - a)⌉₊ + 1 with hN₀
  obtain ⟨n, ⟨h1, h2⟩, hn⟩ := ((hev1.and hev2).and (eventually_ge_atTop N₀)).exists
  have hn1 : 1 ≤ n := le_trans (by omega) hn
  have h2' : Real.exp (b * n) < compactSeminorm (R.iterate n ω) :=
    (lt_logEReal_div_iff hn1 b).mp h2
  have hbig : Ck * Real.exp (a * n) < Real.exp (b * n) := by
    have hlogC : Real.log Ck < (b - a) * n := by
      have h3 := Nat.le_ceil (Real.log Ck / (b - a))
      have h4 : ((N₀:ℕ):ℝ) ≤ n := by exact_mod_cast hn
      rw [hN₀] at h4; push_cast at h4
      rw [div_le_iff₀ (by linarith)] at h3
      nlinarith
    calc Ck * Real.exp (a * n) = Real.exp (Real.log Ck + a * n) := by
          rw [Real.exp_add, Real.exp_log hCkpos]
      _ < Real.exp (b * n) := Real.exp_lt_exp.mpr (by nlinarith)
  have := hdom (R.iterate n ω)
  have h1' : Ck * bernsteinNumber (R.iterate n ω) k < Ck * Real.exp (a * n) :=
    mul_lt_mul_of_pos_left h1 hCkpos
  linarith

/-- **The index `ν` is the index of compactness.** If `(1/n) log ‖𝓛^{(n)}_ω‖_c → κ` almost
everywhere, then `ν = κ` almost everywhere. -/
theorem nu_eq_compactnessIndex (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (κ : EReal) (hκ : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal (compactSeminorm (R.iterate n ω)) / (n : EReal)) atTop (nhds κ)) :
    ∀ᵐ ω ∂(R.μ), R.nu ω = κ := by
  have hlow : ∀ᵐ ω ∂(R.μ), ∀ k : ℕ, κ ≤ R.chi (k + 1) ω :=
    ae_all_iff.mpr fun k => R.ae_le_chi_of_compactnessIndex hκ (k + 1)
  have hup : ∀ᵐ ω ∂(R.μ), ∀ q : ℚ, κ < ((q : ℝ) : EReal) → R.nu ω ≤ ((q : ℝ) : EReal) := by
    refine ae_all_iff.mpr fun q => ?_
    by_cases hq : κ < ((q : ℝ) : EReal)
    · filter_upwards [R.ae_nu_le_of_compactnessIndex_lt hκ (c := (q : ℝ))
        hq] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  filter_upwards [hlow, hup] with ω h1 h2
  refine le_antisymm ?_ (le_iInf h1)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨q, hκq, hqν⟩ := EReal.lt_iff_exists_rat_btwn.mp hlt
  exact absurd (h2 q hκq) (not_le.mpr hqν)

end Cocycle

end MultiplicativeErgodic
