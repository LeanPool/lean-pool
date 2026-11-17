/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
module

public import LeanPool.LCAnalysis.Integral

/-!
# Existence of weak integrals

Weak integrals of continuous curves need not exist in a general locally convex space; they do
under completeness hypotheses (Glöckner–Neeb, §1.1; Kriegl–Michor, §2):

* if `F` is sequentially complete, every continuous curve `[a, b] → F` has a weak integral;
* if `F` is Mackey complete, every `C^1` curve has a weak integral.

In both cases the integral is the limit of the dyadic Riemann sums. Mackey completeness is
strictly weaker than sequential completeness, and it is the natural hypothesis for smooth
calculus. As an application, parameter-dependent integrals of `C^k` maps are `C^k`
(sequentially complete case), or `C^k` maps give `C^{k-1}` integrals (Mackey complete case),
with no existence hypotheses.

Completeness notions are stated directly in terms of the topological vector space structure
(`u n - u m` eventually in every neighborhood of `0`), so no uniform structure is needed; for a
uniform additive group, completeness implies sequential completeness.
-/

@[expose] public section

open Set Filter Function Finset
open scoped Topology Pointwise


noncomputable section

namespace LCAnalysis

universe u v

/-- A topological vector space is sequentially complete if every Cauchy sequence converges. -/
class SeqComplete (F : Type*) [AddCommGroup F] [TopologicalSpace F] : Prop where
  exists_tendsto : ∀ u : ℕ → F, (∀ W ∈ 𝓝 (0 : F), ∃ N, ∀ m ≥ N, ∀ n ≥ N, u n - u m ∈ W) →
    ∃ y, Tendsto u atTop (𝓝 y)

/-- A topological vector space is Mackey complete if every Mackey–Cauchy sequence converges:
`u l - u k ∈ r k • B` for `k ≤ l`, with `B` bounded and `r k → 0`. -/
class MackeyComplete (F : Type*) [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] : Prop where
  exists_tendsto : ∀ (u : ℕ → F) (B : Set F) (r : ℕ → ℝ), Bornology.IsVonNBounded ℝ B →
    Tendsto r atTop (𝓝 0) → (∀ k l, k ≤ l → u l - u k ∈ r k • B) → ∃ y, Tendsto u atTop (𝓝 y)

section Cauchy

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F]

omit [Module ℝ F] in
/-- A one-sided Cauchy condition implies the two-sided one. -/
theorem cauchy_of_forall_ge {u : ℕ → F}
    (h : ∀ V ∈ 𝓝 (0 : F), ∃ K, ∀ k ≥ K, ∀ l ≥ k, u l - u k ∈ V) :
    ∀ W ∈ 𝓝 (0 : F), ∃ N, ∀ m ≥ N, ∀ n ≥ N, u n - u m ∈ W := by
  intro W hW
  obtain ⟨V, hV, hVW⟩ := exists_nhds_zero_half hW
  obtain ⟨K, hK⟩ := h (V ∩ -V) (inter_mem hV (neg_mem_nhds_zero F hV))
  refine ⟨K, fun m hm n hn ↦ ?_⟩
  have h1 := hK K le_rfl n hn
  have h2 := hK K le_rfl m hm
  have := hVW _ h1.1 _ (show -(u m - u K) ∈ V from h2.2)
  convert this using 1
  abel

instance (priority := 100) SeqComplete.mackeyComplete [SeqComplete F] :
    MackeyComplete F where
  exists_tendsto u B r hB hr hu := by
    refine SeqComplete.exists_tendsto u (cauchy_of_forall_ge fun V hV ↦ ?_)
    have hev := hr.eventually ((hB hV).eventually_nhds_zero (mem_of_mem_nhds hV))
    obtain ⟨K, hK⟩ := eventually_atTop.mp hev
    exact ⟨K, fun k hk l hl ↦ by
      obtain ⟨b, hb, he⟩ := hu k l hl
      rw [← he]; exact hK k hk hb⟩

/-- Complete uniform additive groups are sequentially complete. -/
instance (priority := 100) SeqComplete.of_completeSpace {G : Type*} [AddCommGroup G]
    [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G] : SeqComplete G where
  exists_tendsto u hu := by
    refine ⟨_, (cauchySeq_tendsto_of_complete ?_).choose_spec⟩
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero G, tendsto_comap_iff]
    refine Filter.tendsto_def.mpr fun W hW ↦ ?_
    obtain ⟨N, hN⟩ := hu W hW
    rw [← prod_atTop_atTop_eq]
    exact mem_of_superset (prod_mem_prod (Ici_mem_atTop N) (Ici_mem_atTop N))
      fun p (hp : p ∈ Ici N ×ˢ Ici N) ↦ hN p.1 hp.1 p.2 hp.2

end Cauchy

/-! ### Riemann sums -/

section Riemann

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  {γ : ℝ → F} {a b : ℝ}

/-- The Riemann sum of `γ` over `[a, b]` with `N` equal subintervals and left endpoints. -/
def riemannSum (γ : ℝ → F) (a b : ℝ) (N : ℕ) : F :=
  ((b - a) / N) • ∑ i ∈ range N, γ (a + i * ((b - a) / N))

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
theorem map_riemannSum {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    (φ : F →L[ℝ] G) (N : ℕ) :
    φ (riemannSum γ a b N) = riemannSum (fun t ↦ φ (γ t)) a b N := by
  simp [riemannSum, map_sum]

omit [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
private theorem sum_range_mul (g : ℕ → F) (N m : ℕ) :
    ∑ j ∈ range (N * m), g j = ∑ i ∈ range N, ∑ r ∈ range m, g (i * m + r) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- The points of the refined partition lie close to the left endpoints of the coarse one. -/
theorem riemann_points (hab : a ≤ b) {N m i r : ℕ} (hm : 0 < m) (hi : i < N) (hr : r < m) :
    a + i * ((b - a) / N) ∈ Icc a b ∧
      a + ((i * m + r : ℕ) : ℝ) * ((b - a) / (N * m : ℕ)) ∈ Icc a b ∧
      a + i * ((b - a) / N) ≤ a + ((i * m + r : ℕ) : ℝ) * ((b - a) / (N * m : ℕ)) ∧
      a + ((i * m + r : ℕ) : ℝ) * ((b - a) / (N * m : ℕ)) - (a + i * ((b - a) / N)) ≤
        (b - a) / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set h := (b - a) / N with hh
  have h0 : 0 ≤ h := div_nonneg (by linarith) hN.le
  have hs : ((i * m + r : ℕ) : ℝ) * ((b - a) / (N * m : ℕ)) = i * h + (r / m) * h := by
    rw [hh]; push_cast; field_simp
  have hr1 : (r : ℝ) / m ≤ 1 := by
    rw [div_le_one hm']; exact_mod_cast hr.le
  have hr0 : 0 ≤ (r : ℝ) / m := by positivity
  have hi1 : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
  have hNh : (N : ℝ) * h = b - a := by rw [hh]; field_simp
  have hi0 : (0 : ℝ) ≤ i := by positivity
  rw [hs]
  refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
/-- Comparison of a Riemann sum with a refinement: if the increments of `γ` over steps of
length at most `(b - a) / N` lie in a convex set `V`, then the difference lies in `(b - a) • V`. -/
theorem riemannSum_mul_sub_mem (hab : a ≤ b) {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {V : Set F}
    (hV : Convex ℝ V)
    (hγV : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, t ≤ s → s - t ≤ (b - a) / N → γ s - γ t ∈ V) :
    riemannSum γ a b (N * m) - riemannSum γ a b N ∈ (b - a) • V := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set fine : ℕ × ℕ → ℝ := fun p ↦ a + ((p.1 * m + p.2 : ℕ) : ℝ) * ((b - a) / (N * m : ℕ))
  set coarse : ℕ → ℝ := fun i ↦ a + i * ((b - a) / N)
  have key : riemannSum γ a b (N * m) - riemannSum γ a b N = (b - a) •
      ∑ p ∈ range N ×ˢ range m, (1 / ((N : ℝ) * m)) • (γ (fine p) - γ (coarse p.1)) := by
    simp only [riemannSum, sum_range_mul, Finset.sum_product, smul_sub, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, ← Finset.smul_sum, smul_smul]
    congr 1
    · congr 1
      push_cast; field_simp
    · rw [Finset.smul_sum, ← Nat.cast_smul_eq_nsmul ℝ, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_smul, show (b - a) * (1 / ((N : ℝ) * m)) * m = (b - a) / N by field_simp]
  rw [key]
  refine smul_mem_smul_set (hV.sum_mem (fun _ _ ↦ by positivity) ?_ fun p hp ↦ ?_)
  · rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_range,
      nsmul_eq_mul]
    push_cast; field_simp
  · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    obtain ⟨h1, h2, h3, h4⟩ := riemann_points hab hm hp.1 hp.2
    exact hγV _ h2 _ h1 h3 h4

/-- Riemann sums of a continuous real function converge to its integral. -/
theorem tendsto_riemannSum_real {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    Tendsto (riemannSum g a b) atTop (𝓝 (∫ t in a..b, g t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (2 * (b - a + 1))
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) ε' hε'
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨N₀ + 1, fun N hN ↦ ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set h := (b - a) / N with hh
  have h0 : 0 ≤ h := div_nonneg (by linarith) hNpos.le
  have hhδ : h ≤ δ := by
    rw [hh, div_le_iff₀ hNpos]
    rw [div_lt_iff₀ hδ] at hN₀
    have : (N₀ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    nlinarith
  set t : ℕ → ℝ := fun i ↦ a + i * h with ht
  have htN : t N = b := by simp only [ht, hh]; field_simp; ring
  have hsub : ∀ i < N, Icc (t i) (t (i + 1)) ⊆ Icc a b := by
    intro i hi x hx
    have hi1 : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := by positivity
    simp only [ht, Nat.cast_add, Nat.cast_one] at hx
    have hNh : (N : ℝ) * h = b - a := by rw [hh]; field_simp
    constructor <;> nlinarith [hx.1, hx.2]
  have hle : ∀ i < N, t i ≤ t (i + 1) := fun i _ ↦ by
    simp only [ht, Nat.cast_add, Nat.cast_one]; nlinarith
  have hint : ∀ i < N, IntervalIntegrable g MeasureTheory.volume (t i) (t (i + 1)) :=
    fun i hi ↦ (hg.mono (hsub i hi)).intervalIntegrable_of_Icc (hle i hi)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have ht0 : t 0 = a := by simp [ht]
  rw [ht0, htN] at hsum
  have hR : riemannSum g a b N = ∑ i ∈ range N, ∫ x in t i..t (i + 1), g (t i) := by
    simp only [riemannSum, smul_eq_mul, Finset.mul_sum, intervalIntegral.integral_const]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [ht, Nat.cast_add, Nat.cast_one, ← hh]
    ring
  rw [Real.dist_eq, hR, ← hsum, ← Finset.sum_sub_distrib]
  have hbound : ∀ i ∈ range N, |(∫ x in t i..t (i + 1), g (t i)) - ∫ x in t i..t (i + 1), g x| ≤
      ε' * h := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← intervalIntegral.integral_sub intervalIntegrable_const (hint i hi)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t i) (b := t (i + 1))
      (C := ε') (f := fun x ↦ g (t i) - g x) fun x hx ↦ by
        rw [uIoc_of_le (hle i hi)] at hx
        have hxI := hsub i hi (Ioc_subset_Icc_self hx)
        have htI := hsub i hi (left_mem_Icc.mpr (hle i hi))
        have := hgδ (t i) htI x hxI (by
          rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hx.1])]
          have : t (i + 1) - t i = h := by simp only [ht, Nat.cast_add, Nat.cast_one]; ring
          linarith [hx.2])
        rwa [Real.dist_eq] at this
    have hti : t (i + 1) - t i = h := by simp only [ht, Nat.cast_add, Nat.cast_one]; ring
    rw [Real.norm_eq_abs, hti, abs_of_nonneg h0] at this
    exact this
  calc |∑ i ∈ range N, ((∫ x in t i..t (i + 1), g (t i)) - ∫ x in t i..t (i + 1), g x)|
      ≤ ∑ i ∈ range N, |(∫ x in t i..t (i + 1), g (t i)) - ∫ x in t i..t (i + 1), g x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range N, ε' * h := Finset.sum_le_sum hbound
    _ = ε' * (b - a) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hh]; field_simp
    _ < ε := by
        rw [show ε' = ε / (2 * (b - a + 1)) from rfl, div_mul_eq_mul_div,
          div_lt_iff₀ (by positivity)]
        nlinarith

end Riemann

/-! ### Existence of weak integrals -/

section Existence

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {γ : ℝ → F} {a b : ℝ} {y : F}

omit [LocallyConvexSpace ℝ F] [T2Space F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
/-- If the dyadic Riemann sums of a continuous curve converge, the limit is its weak integral. -/
theorem hasWeakIntegral_of_tendsto (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (h : Tendsto (fun k : ℕ ↦ riemannSum γ a b (2 ^ k)) atTop (𝓝 y)) :
    HasWeakIntegral γ a b y := by
  intro φ
  have h1 : Tendsto (fun k : ℕ ↦ riemannSum (fun t ↦ φ (γ t)) a b (2 ^ k)) atTop (𝓝 (φ y)) := by
    exact ((φ.continuous.tendsto y).comp h).congr fun k ↦ map_riemannSum φ _
  have h2 := (tendsto_riemannSum_real hab (φ.continuous.comp_continuousOn hγ)).comp
    (tendsto_atTop_mono (fun k ↦ (Nat.lt_two_pow_self (n := k)).le) tendsto_id)
  exact tendsto_nhds_unique h1 h2

omit [Module ℝ F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Uniform continuity of continuous curves on compact intervals. -/
theorem exists_pos_forall_sub_mem (hγ : ContinuousOn γ (Icc a b)) {W : Set F}
    (hW : W ∈ 𝓝 (0 : F)) :
    ∃ δ > 0, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |s - t| < δ → γ s - γ t ∈ W := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hγ
  have hmem : {p : F × F | p.2 + -p.1 ∈ W} ∈ uniformity F := by
    rw [uniformity_eq_comap_nhds_zero']; exact preimage_mem_comap hW
  have h1 := hu hmem
  rw [Filter.mem_map, mem_inf_principal] at h1
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_uniformity_dist.mp h1
  refine ⟨δ, hδ, fun s hs t ht hst ↦ ?_⟩
  have := hδs (a := t) (b := s) (by rwa [Real.dist_eq, abs_sub_comm]) ⟨ht, hs⟩
  simpa [sub_eq_add_neg] using this

omit [T2Space F] in
/-- In a sequentially complete space, continuous curves have weak integrals. -/
theorem exists_hasWeakIntegral_of_le [SeqComplete F] (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) : ∃ y, HasWeakIntegral γ a b y := by
  suffices hC : ∀ V ∈ 𝓝 (0 : F), ∃ K, ∀ k ≥ K, ∀ l ≥ k,
      riemannSum γ a b (2 ^ l) - riemannSum γ a b (2 ^ k) ∈ V by
    obtain ⟨y, hy⟩ := SeqComplete.exists_tendsto _ (cauchy_of_forall_ge hC)
    exact ⟨y, hasWeakIntegral_of_tendsto hab hγ hy⟩
  intro V hV
  have hc : b - a + 1 ≠ 0 := by linarith
  obtain ⟨W, hW, -, hWc, hWV⟩ := exists_closed_convex_nhds_subset
    ((set_smul_mem_nhds_zero_iff (inv_ne_zero hc)).mpr hV)
  obtain ⟨δ, hδ, hγδ⟩ := exists_pos_forall_sub_mem hγ hW
  obtain ⟨K, hK⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨K, fun k hk l hl ↦ ?_⟩
  have hpow : (2 : ℕ) ^ l = 2 ^ k * 2 ^ (l - k) := by rw [← pow_add]; congr 1; omega
  have h2k : ((b - a) / δ) < (2 : ℝ) ^ k := by
    calc (b - a) / δ < K := hK
      _ ≤ (2 : ℝ) ^ K := by exact_mod_cast (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hk
  have hmem := riemannSum_mul_sub_mem (γ := γ) hab (N := 2 ^ k) (m := 2 ^ (l - k))
    (by positivity) (by positivity) hWc fun s hs t ht hts hst ↦ hγδ s hs t ht (by
      rw [abs_of_nonneg (by linarith)]
      refine lt_of_le_of_lt hst ?_
      push_cast
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ] at h2k
      linarith)
  simp only [hpow]
  -- `(b - a) • W ⊆ (b - a + 1) • W ⊆ V`
  obtain ⟨w, hw, hw'⟩ := hmem
  rw [← hw']
  have hc' : 0 < b - a + 1 := by linarith
  have hw2 : ((b - a) / (b - a + 1)) • w ∈ W := hWc.smul_mem_of_zero_mem (mem_of_mem_nhds hW) hw
    ⟨div_nonneg (by linarith) hc'.le, (div_le_one hc').mpr (by linarith)⟩
  have := hWV hw2
  rw [mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hc), inv_inv, smul_smul] at this
  rwa [show (b - a + 1) * ((b - a) / (b - a + 1)) = b - a by field_simp] at this

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem HasWeakIntegral.symm (hy : HasWeakIntegral γ a b y) : HasWeakIntegral γ b a (-y) := by
  intro φ
  rw [map_neg, hy φ, intervalIntegral.integral_symm, neg_neg]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem hasWeakIntegral_same (γ : ℝ → F) (a : ℝ) : HasWeakIntegral γ a a 0 := by
  intro φ; simp

omit [T2Space F] in
/-- In a sequentially complete space, continuous curves have weak integrals. -/
theorem exists_hasWeakIntegral [SeqComplete F] (hγ : ContinuousOn γ (uIcc a b)) :
    ∃ y, HasWeakIntegral γ a b y := by
  rcases le_total a b with hab | hba
  · exact exists_hasWeakIntegral_of_le hab (by rwa [uIcc_of_le hab] at hγ)
  · obtain ⟨y, hy⟩ := exists_hasWeakIntegral_of_le hba (by rwa [uIcc_of_ge hba] at hγ)
    exact ⟨-y, hy.symm⟩

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F] in
/-- In a locally convex space, the convex hull of a bounded set is bounded. -/
theorem isVonNBounded_convexHull {B : Set F} (hB : Bornology.IsVonNBounded ℝ B) :
    Bornology.IsVonNBounded ℝ (convexHull ℝ B) := by
  intro V hV
  obtain ⟨W, ⟨hW, hWc⟩, hWV⟩ := (LocallyConvexSpace.convex_basis (𝕜 := ℝ) (0 : F)).mem_iff.mp hV
  exact Absorbs.mono_left (Filter.Eventually.mono (hB hW) fun c hc ↦
    convexHull_min hc (hWc.smul c)) hWV

/-- Mean value inclusion for curves: increments over steps of length at most `h` lie in
`h • B`, where `B` is the closed convex hull of `[0, 1] • γ'([a, b])`. -/
theorem sub_mem_smul_closure_convexHull {γ' : ℝ → F} (hγ' : ContinuousOn γ' (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDirDerivAt γ t 1 (γ' t)) {h : ℝ} (hh : 0 < h) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hts : t ≤ s) (hst : s - t ≤ h) :
    γ s - γ t ∈ h • closure (convexHull ℝ
      ((fun p : ℝ × ℝ ↦ p.1 • γ' p.2) '' (Set.Icc 0 1 ×ˢ Set.Icc a b))) := by
  set B :=
    closure (convexHull ℝ ((fun p : ℝ × ℝ ↦ p.1 • γ' p.2) '' (Set.Icc 0 1 ×ˢ Set.Icc a b)))
  have hpt : ∀ σ ∈ Icc (0 : ℝ) 1, t + σ • (s - t) ∈ Icc a b := fun σ hσ ↦ by
    rw [smul_eq_mul]
    constructor <;> nlinarith [hσ.1, hσ.2, hs.1, hs.2, ht.1, ht.2]
  have hd' : ∀ σ ∈ Icc (0 : ℝ) 1, HasDirDerivAt γ (t + σ • (s - t)) (s - t)
      ((s - t) • γ' (t + σ • (s - t))) := fun σ hσ ↦ by
    have := (hd _ (hpt σ hσ)).smul_dir (s - t)
    simpa only [smul_eq_mul, mul_one] using this
  have hD : ContinuousOn (fun σ : ℝ ↦ (s - t) • γ' (t + σ • (s - t))) (Icc 0 1) :=
    (continuous_const_smul _).comp_continuousOn
      (hγ'.comp (by fun_prop : Continuous fun σ : ℝ ↦ t + σ • (s - t)).continuousOn hpt)
  have := sub_mem_of_hasDirDerivAt (W := h • B) hd' hD ((convex_convexHull ℝ _).closure.smul h)
    (isClosed_closure.smul_of_ne_zero hh.ne') fun σ hσ ↦ by
      have hmem : ((s - t) / h, t + σ • (s - t)) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc a b :=
        ⟨⟨div_nonneg (sub_nonneg.mpr hts) hh.le, (div_le_one hh).mpr hst⟩, hpt σ hσ⟩
      have hB : ((s - t) / h) • γ' (t + σ • (s - t)) ∈ B := subset_closure (subset_convexHull ℝ _
        (Set.mem_image_of_mem (fun p : ℝ × ℝ ↦ p.1 • γ' p.2) hmem))
      refine (mem_smul_set_iff_inv_smul_mem₀ hh.ne' _ _).mpr ?_
      convert hB using 1
      rw [smul_smul]; congr 1; field_simp
  rwa [add_sub_cancel] at this

/-- In a Mackey complete space, `C^1` curves have weak integrals. -/
theorem exists_hasWeakIntegral_of_hasDirDerivAt_of_le [MackeyComplete F] (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) {γ' : ℝ → F} (hγ' : ContinuousOn γ' (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDirDerivAt γ t 1 (γ' t)) : ∃ y, HasWeakIntegral γ a b y := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact ⟨0, hasWeakIntegral_same γ a⟩
  set C := (fun p : ℝ × ℝ ↦ p.1 • γ' p.2) '' (Set.Icc 0 1 ×ˢ Set.Icc a b)
  have hC : IsCompact C := (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
    (continuous_fst.continuousOn.smul (hγ'.comp continuous_snd.continuousOn fun p hp ↦ hp.2))
  have hB : Bornology.IsVonNBounded ℝ (closure (convexHull ℝ C)) :=
    (isVonNBounded_convexHull (hC.isVonNBounded (𝕜 := ℝ))).closure
  have hr : Tendsto (fun k : ℕ ↦ (b - a) * ((b - a) / 2 ^ k)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ))))
  obtain ⟨y, hy⟩ := MackeyComplete.exists_tendsto (fun k : ℕ ↦ riemannSum γ a b (2 ^ k)) _ _ hB hr
    fun k l hkl ↦ by
      have hpow : (2 : ℕ) ^ l = 2 ^ k * 2 ^ (l - k) := by rw [← pow_add]; congr 1; omega
      have hk : (0 : ℝ) < (b - a) / 2 ^ k := div_pos (by linarith) (by positivity)
      have hmem := riemannSum_mul_sub_mem (γ := γ) hab (N := 2 ^ k) (m := 2 ^ (l - k))
        (by positivity) (by positivity) ((convex_convexHull ℝ C).closure.smul ((b - a) / 2 ^ k))
        fun s hs t ht hts hst ↦ sub_mem_smul_closure_convexHull hγ' hd hk hs ht hts
          (by push_cast at hst; exact hst)
      simp only [hpow]
      rwa [smul_smul] at hmem
  exact ⟨y, hasWeakIntegral_of_tendsto hab hγ hy⟩

/-- In a Mackey complete space, `C^1` curves have weak integrals. -/
theorem ContDiffMBOn.exists_hasWeakIntegral [MackeyComplete F] {T : Set ℝ}
    (hTab : uIcc a b ⊆ T) (hγ : ContDiffMBOn 1 γ T) : ∃ y, HasWeakIntegral γ a b y := by
  have h2 : ContinuousOn (dMB γ) (T ×ˢ univ) := hγ.2.2
  have hγ' : ContinuousOn (fun t ↦ dMB γ (t, 1)) T :=
    h2.comp (by fun_prop : Continuous fun t : ℝ ↦ (t, (1 : ℝ))).continuousOn
      fun t ht ↦ ⟨ht, mem_univ _⟩
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at hTab
    exact exists_hasWeakIntegral_of_hasDirDerivAt_of_le hab (hγ.continuousOn.mono hTab)
      (hγ'.mono hTab) fun t ht ↦ hγ.2.1 t (hTab ht) 1
  · rw [uIcc_of_ge hba] at hTab
    obtain ⟨y, hy⟩ := exists_hasWeakIntegral_of_hasDirDerivAt_of_le hba
      (hγ.continuousOn.mono hTab) (hγ'.mono hTab) fun t ht ↦ hγ.2.1 t (hTab ht) 1
    exact ⟨-y, hy.symm⟩

end Existence

/-! ### Parameter-dependent integrals -/

section Param

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {γ : ℝ → F} {a b : ℝ} {y : F}

/-- The weak integral of `γ` over `[a, b]` (junk value `0` if it does not exist). -/
def weakIntegral (γ : ℝ → F) (a b : ℝ) : F :=
  open Classical in
  if h : ∃ y, HasWeakIntegral γ a b y then h.choose else 0

theorem HasWeakIntegral.weakIntegral_eq (hy : HasWeakIntegral γ a b y) :
    weakIntegral γ a b = y := by
  have h : ∃ y, HasWeakIntegral γ a b y := ⟨y, hy⟩
  rw [weakIntegral, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.unique hy

theorem hasWeakIntegral_weakIntegral (h : ∃ y, HasWeakIntegral γ a b y) :
    HasWeakIntegral γ a b (weakIntegral γ a b) := by
  obtain ⟨y, hy⟩ := h
  rwa [hy.weakIntegral_eq]

/-- `φ (∫_a^b γ) = ∫_a^b φ ∘ γ`, when the weak integral exists. -/
theorem map_weakIntegral (h : ∃ y, HasWeakIntegral γ a b y) (φ : F →L[ℝ] ℝ) :
    φ (weakIntegral γ a b) = ∫ t in a..b, φ (γ t) :=
  hasWeakIntegral_weakIntegral h φ

/-- The induction behind the `C^k` results: if every `C^m` map on `U ×ˢ T` has weak integrals
along `[a, b]` in the second variable, then `C^(k + m)` maps give `C^k` integrals. -/
theorem contDiffMBOn_weakIntegral_of_exists {T : Set ℝ} (hT : IsOpen T) (hab : a ≤ b)
    (hTab : Icc a b ⊆ T) (m : ℕ)
    (hP : ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
      (f : E × ℝ → F) (U : Set E), IsOpen U → ContDiffMBOn m f (U ×ˢ T) →
        ∀ x ∈ U, ∃ y, HasWeakIntegral (fun t ↦ f (x, t)) a b y) :
    ∀ (k : ℕ) {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
      {f : E × ℝ → F} {U : Set E}, IsOpen U → ContDiffMBOn (k + m) f (U ×ˢ T) →
        ContDiffMBOn k (fun x ↦ weakIntegral (fun t ↦ f (x, t)) a b) U := by
  intro k
  induction k with
  | zero =>
    intro E _ _ _ _ _ _ _ f U hU hf
    rw [zero_add] at hf
    exact continuousOn_weakIntegral hU hT hab hTab hf.continuousOn
      fun x hx ↦ hasWeakIntegral_weakIntegral (hP f U hU hf x hx)
  | succ k ih =>
    intro E _ _ _ _ _ _ _ f U hU hf
    have hf' : ContDiffMBOn (k + m + 1) f (U ×ˢ T) := by
      rwa [show k + m + 1 = k + 1 + m by omega]
    have hI : ∀ x ∈ U, HasWeakIntegral (fun t ↦ f (x, t)) a b
        (weakIntegral (fun t ↦ f (x, t)) a b) := fun x hx ↦
      hasWeakIntegral_weakIntegral (hP f U hU (hf.of_le (by omega)) x hx)
    -- the partial derivative, as a map on `(E × E) × ℝ`
    let L : (E × E) × ℝ →L[ℝ] (E × ℝ) × (E × ℝ) :=
      (((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) ℝ)).prod
        (ContinuousLinearMap.snd ℝ (E × E) ℝ)).prod
      (((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) ℝ)).prod 0)
    have hL : ∀ q, L q = ((q.1.1, q.2), (q.1.2, 0)) := fun q ↦ rfl
    have hpre : L ⁻¹' ((U ×ˢ T) ×ˢ univ) = (U ×ˢ univ) ×ˢ T := by
      ext q; simp [hL]
    have hg := ContDiffMBOn.comp_clm L ((hU.prod hT).prod isOpen_univ) hf'.2.2
    rw [hpre] at hg
    have hJ := ih (hU.prod isOpen_univ) hg
    have hJex : ∀ x ∈ U, ∀ h, HasWeakIntegral (fun t ↦ dMB f ((x, t), (h, 0))) a b
        (weakIntegral (fun t ↦ dMB f ((x, t), (h, 0))) a b) := fun x hx h ↦
      hasWeakIntegral_weakIntegral (hP _ _ (hU.prod isOpen_univ) (hg.of_le (by omega)) (x, h)
        ⟨hx, mem_univ _⟩)
    obtain ⟨hC1, heq⟩ := ContDiffMBOn.contDiffMBOn_one_of_hasWeakIntegral hU hT hab hTab
      (hf.of_le (by omega)) hI
      (J := fun q ↦ weakIntegral (fun t ↦ dMB f ((q.1, t), (q.2, 0))) a b) hJex
    refine ⟨hC1.1, hC1.2.1, ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ)
      (fun q hq ↦ (heq q.1 hq.1 q.2).symm) ?_⟩
    exact hJ

/-- Parameter-dependent integrals in sequentially complete spaces: if `f` is `C^k` on
`U ×ˢ T`, then `x ↦ ∫_a^b f (x, t) dt` is `C^k` on `U`. -/
theorem ContDiffMBOn.contDiffMBOn_weakIntegral [SeqComplete F] {T : Set ℝ} (hT : IsOpen T)
    (hab : a ≤ b) (hTab : Icc a b ⊆ T) {k : ℕ} {f : E × ℝ → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn k f (U ×ˢ T)) :
    ContDiffMBOn k (fun x ↦ weakIntegral (fun t ↦ f (x, t)) a b) U :=
  contDiffMBOn_weakIntegral_of_exists hT hab hTab 0
    (fun f U _ hf x hx ↦ exists_hasWeakIntegral_of_le hab
      (hf.continuousOn.comp (by fun_prop : Continuous fun t : ℝ ↦ (x, t)).continuousOn
        fun t ht ↦ ⟨hx, hTab ht⟩)) k hU hf

/-- Parameter-dependent integrals in Mackey complete spaces: if `f` is `C^(k+1)` on
`U ×ˢ T`, then `x ↦ ∫_a^b f (x, t) dt` is `C^k` on `U`. -/
theorem ContDiffMBOn.contDiffMBOn_weakIntegral_of_mackey [MackeyComplete F] {T : Set ℝ}
    (hT : IsOpen T) (hab : a ≤ b) (hTab : Icc a b ⊆ T) {k : ℕ} {f : E × ℝ → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffMBOn (k + 1) f (U ×ˢ T)) :
    ContDiffMBOn k (fun x ↦ weakIntegral (fun t ↦ f (x, t)) a b) U := by
  refine contDiffMBOn_weakIntegral_of_exists hT hab hTab 1
    (@fun E' _ _ _ _ _ _ _ f U _ hf x hx ↦ ?_) k hU hf
  have h2 : ContinuousOn (dMB f) ((U ×ˢ T) ×ˢ univ) := hf.2.2
  refine exists_hasWeakIntegral_of_hasDirDerivAt_of_le hab
    (hf.continuousOn.comp (by fun_prop : Continuous fun t : ℝ ↦ (x, t)).continuousOn
      fun t ht ↦ ⟨hx, hTab ht⟩)
    (γ' := fun t ↦ dMB f ((x, t), (0, 1)))
    (h2.comp (by fun_prop : Continuous fun t : ℝ ↦ ((x, t), ((0 : E'), (1 : ℝ)))).continuousOn
      fun t ht ↦ ⟨⟨hx, hTab ht⟩, mem_univ _⟩) fun t ht ↦ ?_
  exact (hf.2.1 (x, t) ⟨hx, hTab ht⟩ (0, 1)).congr fun s ↦ by simp

/-- Smooth parameter-dependent integrals in Mackey complete spaces. -/
theorem SmoothMBOn.smoothMBOn_weakIntegral [MackeyComplete F] {T : Set ℝ} (hT : IsOpen T)
    (hab : a ≤ b) (hTab : Icc a b ⊆ T) {f : E × ℝ → F} {U : Set E} (hU : IsOpen U)
    (hf : SmoothMBOn f (U ×ˢ T)) :
    SmoothMBOn (fun x ↦ weakIntegral (fun t ↦ f (x, t)) a b) U := fun k ↦
  ContDiffMBOn.contDiffMBOn_weakIntegral_of_mackey hT hab hTab hU (hf (k + 1))

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Differentiation under the integral sign, sequentially complete case:
`d(∫_a^b f(·, t) dt)(x)(h) = ∫_a^b d₁f((x, t), h) dt` for `f` of class `C^1`. -/
theorem ContDiffMBOn.dMB_weakIntegral [SeqComplete F] {T : Set ℝ} (hT : IsOpen T)
    (hab : a ≤ b) (hTab : Icc a b ⊆ T) {f : E × ℝ → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn 1 f (U ×ˢ T)) {x : E} (hx : x ∈ U) (h : E) :
    dMB (fun x ↦ weakIntegral (fun t ↦ f (x, t)) a b) (x, h) =
      weakIntegral (fun t ↦ dMB f ((x, t), (h, 0))) a b := by
  have hcurve : ∀ x ∈ U, ContinuousOn (fun t ↦ f (x, t)) (Icc a b) := fun x hx ↦
    hf.continuousOn.comp (by fun_prop : Continuous fun t : ℝ ↦ (x, t)).continuousOn
      fun t ht ↦ ⟨hx, hTab ht⟩
  have h2 : ContinuousOn (dMB f) ((U ×ˢ T) ×ˢ univ) := hf.2.2
  refine (ContDiffMBOn.contDiffMBOn_one_of_hasWeakIntegral hU hT hab hTab hf
    (fun x hx ↦ hasWeakIntegral_weakIntegral (exists_hasWeakIntegral_of_le hab (hcurve x hx)))
    (J := fun q ↦ weakIntegral (fun t ↦ dMB f ((q.1, t), (q.2, 0))) a b)
    (fun x hx h ↦ hasWeakIntegral_weakIntegral (exists_hasWeakIntegral_of_le hab
      (h2.comp (by fun_prop : Continuous fun t : ℝ ↦ ((x, t), (h, (0 : ℝ)))).continuousOn
        fun t ht ↦ ⟨⟨hx, hTab ht⟩, mem_univ _⟩)))).2 x hx h

end Param

end LCAnalysis
