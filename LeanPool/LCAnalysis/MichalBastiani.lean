/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Order.CompletePartialOrder

/-!
# Michal–Bastiani calculus on locally convex spaces

Reference: K.-H. Neeb, *Towards a Lie theory of locally convex groups*, Jpn. J. Math. 1 (2006),
291–468 (arXiv:1501.06269), §I.2; H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*
(arXiv:2602.12362), Ch. 2.

For `E`, `F` real topological vector spaces, `U ⊆ E` open and `f : E → F`:
* `dMB f (x, h) = d/dt|_{t=0} f (x + t • h)` is the directional derivative (Definition I.2.1).
* `f` is `C^1` on `U` if all directional derivatives exist on `U` and
  `dMB f : E × E → F` is continuous on `U × E`.
* `f` is `C^{k+1}` on `U` if it is `C^1` and `dMB f` is `C^k` on `U × E`. This recursive
  definition is equivalent to Neeb's (continuity of all the iterated derivatives `d^j f`, see
  `contDiffMBOn_iff_hasContIterDerivOn` in `LCAnalysis.Higher`);
  it is the one used by Glöckner, and it avoids `j`-linear maps.

The directional derivative is defined literally as the limit of difference quotients, so no
normed structure is involved anywhere (Mathlib's `HasDerivAt` makes sense for curves in a
topological vector space, but its API is mostly stated for normed targets). To use the
one-variable calculus of Mathlib we compose with continuous linear functionals `F →L[ℝ] ℝ`.
Local convexity (and `T2`) only appear in the theorems: through Hahn–Banach, functionals
separate points, which is what makes the fundamental theorem of calculus, hence the chain
rule, work (Neeb, Example I.2.5).
-/

@[expose] public section

open Set Filter
open scoped Topology Pointwise

noncomputable section

namespace LCAnalysis

universe u v

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ContinuousSMul ℝ F]

/-! ### Directional derivatives and `C^k` maps (Definition I.2.1) -/

/-- `f` has derivative `y` at `x` in the direction `h`:
`t⁻¹ • (f (x + t • h) - f x) → y` as `t → 0`, `t ≠ 0`. -/
def HasDirDerivAt (f : E → F) (x h : E) (y : F) : Prop :=
  Tendsto (fun t : ℝ ↦ t⁻¹ • (f (x + t • h) - f x)) (𝓝[≠] 0) (𝓝 y)

/-- The directional derivative `df(x)(h)`, as a function on `E × E`
(junk value where it does not exist). -/
def dMB (f : E → F) (p : E × E) : F :=
  limUnder (𝓝[≠] (0 : ℝ)) fun t : ℝ ↦ t⁻¹ • (f (p.1 + t • p.2) - f p.1)

/-- `C^k` maps in the sense of Michal–Bastiani on a set `U` (meant to be open), `k ∈ ℕ`. -/
def ContDiffMBOn : ℕ → ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
    (E → F) → Set E → Prop
  | 0, _, _, _, _, f, U => ContinuousOn f U
  | k + 1, _, _, _, _, f, U =>
      ContinuousOn f U ∧ (∀ x ∈ U, ∀ h, HasDirDerivAt f x h (dMB f (x, h))) ∧
        ContDiffMBOn k (dMB f) (U ×ˢ univ)

/-- Smooth maps in the sense of Michal–Bastiani. -/
def SmoothMBOn (f : E → F) (U : Set E) : Prop := ∀ k, ContDiffMBOn k f U

/-! ### Basic properties -/

omit [ContinuousSMul ℝ F] in
theorem ContDiffMBOn.continuousOn {k : ℕ} {f : E → F} {U : Set E} (hf : ContDiffMBOn k f U) :
    ContinuousOn f U := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

omit [ContinuousSMul ℝ F] in
theorem ContDiffMBOn.hasDirDerivAt {k : ℕ} {f : E → F} {U : Set E}
    (hf : ContDiffMBOn (k + 1) f U) {x : E} (hx : x ∈ U) (h : E) :
    HasDirDerivAt f x h (dMB f (x, h)) :=
  hf.2.1 x hx h

omit [ContinuousSMul ℝ F] in
theorem ContDiffMBOn.of_succ : ∀ {k : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] {f : E → F} {U : Set E}, ContDiffMBOn (k + 1) f U → ContDiffMBOn k f U
  | 0, _, _, _, _, _, _, hf => hf.1
  | _ + 1, _, _, _, _, _, _, hf => ⟨hf.1, hf.2.1, ContDiffMBOn.of_succ hf.2.2⟩

omit [ContinuousSMul ℝ F] in
theorem ContDiffMBOn.of_le {k l : ℕ} {f : E → F} {U : Set E} (hf : ContDiffMBOn k f U)
    (hlk : l ≤ k) : ContDiffMBOn l f U := by
  induction hlk with
  | refl => exact hf
  | step _ ih => exact ih hf.of_succ

omit [ContinuousSMul ℝ F] in
theorem SmoothMBOn.contDiffMBOn {f : E → F} {U : Set E} (hf : SmoothMBOn f U) (k : ℕ) :
    ContDiffMBOn k f U :=
  hf k

section LocallyConvex

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

/-! ### Proposition I.2.3 -/

omit [TopologicalSpace E] [ContinuousSMul ℝ F] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F]
    [T2Space F] in
/-- Along the line `t ↦ x + t • h`, a directional derivative composed with a continuous
linear functional is an ordinary derivative. -/
theorem HasDirDerivAt.hasDerivAt_clm {f : E → F} {x h : E} {t : ℝ} {y : F}
    (hd : HasDirDerivAt f (x + t • h) h y) (φ : F →L[ℝ] ℝ) :
    HasDerivAt (fun s : ℝ ↦ φ (f (x + s • h))) (φ y) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine ((φ.continuous.tendsto y).comp hd).congr fun s ↦ ?_
  simp [add_smul, add_assoc, smul_eq_mul]

omit [TopologicalSpace E] [ContinuousSMul ℝ F] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
theorem HasDirDerivAt.dMB_eq {f : E → F} {x h : E} {y : F} (hd : HasDirDerivAt f x h y) :
    dMB f (x, h) = y :=
  hd.limUnder_eq

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- Homogeneity of directional derivatives in the direction. -/
theorem HasDirDerivAt.smul_dir {f : E → F} {x h : E} {y : F} (hd : HasDirDerivAt f x h y)
    (c : ℝ) : HasDirDerivAt f x (c • h) (c • y) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [HasDirDerivAt]
  · have hm : Tendsto (fun t : ℝ ↦ t * c) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall
        fun t ht ↦ mul_ne_zero ht hc⟩
      exact ((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).mono_left
        nhdsWithin_le_nhds
    refine ((hd.comp hm).const_smul c).congr fun t ↦ ?_
    change c • ((t * c)⁻¹ • (f (x + (t * c) • h) - f x)) = t⁻¹ • (f (x + t • c • h) - f x)
    rw [smul_smul, smul_smul t c h, mul_inv, mul_left_comm, mul_inv_cancel₀ hc, mul_one]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
theorem ContDiffMBOn.dMB_smul {f : E → F} {U : Set E} (hf : ContDiffMBOn 1 f U) {x : E}
    (hx : x ∈ U) (c : ℝ) (h : E) : dMB f (x, c • h) = c • dMB f (x, h) :=
  tendsto_nhds_unique (hf.2.1 x hx (c • h)) ((hf.2.1 x hx h).smul_dir c)

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- `h ↦ df(x)(h)` is continuous. -/
theorem ContDiffMBOn.continuous_dMB {f : E → F} {U : Set E} (hf : ContDiffMBOn 1 f U) {x : E}
    (hx : x ∈ U) : Continuous fun h ↦ dMB f (x, h) :=
  (hf.2.2 : ContinuousOn (dMB f) (U ×ˢ univ)).comp_continuous (by fun_prop)
    fun h ↦ ⟨hx, mem_univ h⟩

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Additivity of `df(x)`. The proof applies the mean value theorem to `φ ∘ f` along lines, for
continuous linear functionals `φ`, and uses that these separate points (Hahn–Banach). -/
theorem ContDiffMBOn.dMB_add {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffMBOn 1 f U)
    {x : E} (hx : x ∈ U) (h k : E) : dMB f (x, h + k) = dMB f (x, h) + dMB f (x, k) := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro φ
  have hφ : ∀ {z v : E} {y : F}, HasDirDerivAt f z v y →
      Tendsto (fun t : ℝ ↦ t⁻¹ * (φ (f (z + t • v)) - φ (f z))) (𝓝[≠] 0) (𝓝 (φ y)) :=
    fun hd ↦ ((φ.continuous.tendsto _).comp hd).congr fun t ↦ by simp [smul_eq_mul]
  have hA : Tendsto (fun t : ℝ ↦ t⁻¹ * (φ (f (x + t • h + t • k)) - φ (f (x + t • h))))
      (𝓝[≠] 0) (𝓝 (φ (dMB f (x, k)))) := by
    have hD : ContinuousAt (fun z ↦ φ (dMB f (z, k))) x := by
      have h1 : ContinuousAt (dMB f) (x, k) :=
        (hf.2.2 : ContinuousOn (dMB f) (U ×ˢ univ)).continuousAt
          (prod_mem_nhds (hU.mem_nhds hx) univ_mem)
      exact φ.continuous.continuousAt.comp
        (h1.comp (f := fun z : E ↦ (z, k)) (by fun_prop))
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have hW : ∀ᶠ z in 𝓝 x, z ∈ U ∧ dist (φ (dMB f (z, k))) (φ (dMB f (x, k))) < ε :=
      (hU.eventually_mem hx).and (Metric.tendsto_nhds.mp hD ε hε)
    have hΦ : Tendsto (fun p : ℝ × ℝ ↦ x + p.1 • h + p.2 • k) (𝓝 0) (𝓝 x) := by
      have : Continuous fun p : ℝ × ℝ ↦ x + p.1 • h + p.2 • k := by fun_prop
      simpa using this.tendsto 0
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hΦ.eventually hW)
    refine ⟨δ, hδ, fun t ht0 htδ ↦ ?_⟩
    have ht : t ≠ 0 := ht0
    have htabs : |t| < δ := by simpa [Real.dist_eq] using htδ
    have hseg : ∀ s, |s| ≤ |t| → x + t • h + s • k ∈ U ∧
        dist (φ (dMB f (x + t • h + s • k, k))) (φ (dMB f (x, k))) < ε := by
      intro s hs
      have hd : dist ((t, s) : ℝ × ℝ) 0 < δ := by
        rw [Prod.dist_eq]
        exact max_lt (by simpa [Real.dist_eq] using htabs)
          (by simpa [Real.dist_eq] using lt_of_le_of_lt hs htabs)
      exact @hball (t, s) hd
    set g : ℝ → ℝ := fun s ↦ φ (f (x + t • h + s • k)) with hgdef
    set g' : ℝ → ℝ := fun s ↦ φ (dMB f (x + t • h + s • k, k)) with hg'def
    have hg : ∀ s, |s| ≤ |t| → HasDerivAt g (g' s) s := fun s hs ↦
      (hf.2.1 _ (hseg s hs).1 k).hasDerivAt_clm φ
    have key : ∃ ξ, |ξ| ≤ |t| ∧ t⁻¹ * (g t - g 0) = g' ξ := by
      rcases lt_or_gt_of_ne ht with htn | htp
      · have hab : ∀ s ∈ Icc t 0, |s| ≤ |t| := fun s hs ↦ by
          rw [abs_of_nonpos hs.2, abs_of_neg htn]; linarith [hs.1]
        obtain ⟨ξ, hξ, heq⟩ := exists_hasDerivAt_eq_slope g g' htn
          (fun s hs ↦ (hg s (hab s hs)).continuousAt.continuousWithinAt)
          (fun s hs ↦ hg s (hab s (Ioo_subset_Icc_self hs)))
        refine ⟨ξ, hab ξ (Ioo_subset_Icc_self hξ), ?_⟩
        rw [heq]; field_simp; ring
      · have hab : ∀ s ∈ Icc 0 t, |s| ≤ |t| := fun s hs ↦ by
          rw [abs_of_nonneg hs.1, abs_of_pos htp]; exact hs.2
        obtain ⟨ξ, hξ, heq⟩ := exists_hasDerivAt_eq_slope g g' htp
          (fun s hs ↦ (hg s (hab s hs)).continuousAt.continuousWithinAt)
          (fun s hs ↦ hg s (hab s (Ioo_subset_Icc_self hs)))
        refine ⟨ξ, hab ξ (Ioo_subset_Icc_self hξ), ?_⟩
        rw [heq, sub_zero, div_eq_inv_mul]
    obtain ⟨ξ, hξ, heq⟩ := key
    have hg0 : g 0 = φ (f (x + t • h)) := by simp [hgdef]
    rw [← hg0, show φ (f (x + t • h + t • k)) = g t from rfl, heq]
    exact (hseg ξ hξ).2
  have hsum := hA.add (hφ (hf.2.1 x hx h))
  have h1 := hφ (hf.2.1 x hx (h + k))
  rw [map_add, add_comm (φ (dMB f (x, h)))]
  refine tendsto_nhds_unique h1 (hsum.congr fun t ↦ ?_)
  rw [smul_add, ← add_assoc]
  ring

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- (i) For a `C^1` map, `df(x)` is a continuous linear map. -/
theorem ContDiffMBOn.exists_clm {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn 1 f U) {x : E} (hx : x ∈ U) :
    ∃ L : E →L[ℝ] F, ∀ h, L h = dMB f (x, h) :=
  ⟨{ toFun := fun h ↦ dMB f (x, h)
     map_add' := hf.dMB_add hU hx
     map_smul' := hf.dMB_smul hx
     cont := hf.continuous_dMB hx }, fun _ ↦ rfl⟩

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F]
    [LocallyConvexSpace ℝ F] [T2Space F] in
/-- (ii) Fundamental theorem of calculus, in weak form (no completeness assumption on `F`):
for every continuous linear functional `φ`,
`φ (f (x + h)) - φ (f x) = ∫₀¹ φ (df(x + t h)(h)) dt`. -/
theorem ContDiffMBOn.integral_dMB {f : E → F} {U : Set E}
    (hf : ContDiffMBOn 1 f U) {x h : E} (hxh : ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U)
    (φ : F →L[ℝ] ℝ) :
    φ (f (x + h)) - φ (f x) = ∫ t in (0 : ℝ)..1, φ (dMB f (x + t • h, h)) := by
  have hline : Continuous fun t : ℝ ↦ x + t • h := by fun_prop
  have hcont : ContinuousOn (fun t : ℝ ↦ φ (f (x + t • h))) (Icc 0 1) :=
    φ.continuous.comp_continuousOn (hf.continuousOn.comp hline.continuousOn hxh)
  have hd : ContinuousOn (fun t : ℝ ↦ φ (dMB f (x + t • h, h))) (Icc 0 1) := by
    have h0 : ContinuousOn (dMB f) (U ×ˢ univ) := hf.2.2
    refine φ.continuous.comp_continuousOn (h0.comp (by fun_prop) fun t ht ↦ ?_)
    exact ⟨hxh t ht, mem_univ _⟩
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
    (fun t ht ↦ (hf.2.1 _ (hxh t (Ioo_subset_Icc_self ht)) h).hasDerivAt_clm φ)
    (hd.intervalIntegrable_of_Icc zero_le_one)
  simpa using this.symm

/-! ### The chain rule

The key step (Glöckner's characterization of `C^1`): the difference quotient
`t⁻¹ • (g (y + t • v) - g y)` extends continuously to `t = 0` by `dg(y)(v)`. The proof combines
the weak fundamental theorem of calculus with Hahn–Banach (the quotient lies in the closed
convex hull of `{dg(y + s t v)(v) : s ∈ [0, 1]}`) and local convexity (closed convex
neighborhoods form a basis). -/

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Mean value inclusion: the difference quotient lies in the closed convex hull of the
directional derivatives along the segment. -/
theorem ContDiffMBOn.quotient_mem_closure_convexHull {g : E → F} {U : Set E}
    (hg : ContDiffMBOn 1 g U) {y v : E} {t : ℝ} (ht : t ≠ 0)
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, y + s • (t • v) ∈ U) :
    t⁻¹ • (g (y + t • v) - g y) ∈
      closure (convexHull ℝ ((fun s : ℝ ↦ dMB g (y + s • (t • v), v)) '' Icc 0 1)) := by
  by_contra hnot
  obtain ⟨φ, u, hlt, hgt⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _).closure isClosed_closure hnot
  have hcont : ContinuousOn (fun s : ℝ ↦ φ (dMB g (y + s • (t • v), v))) (Icc 0 1) := by
    have h0 : ContinuousOn (dMB g) (U ×ˢ univ) := hg.2.2
    refine φ.continuous.comp_continuousOn (h0.comp (by fun_prop) fun s hs ↦ ?_)
    exact ⟨hseg s hs, mem_univ _⟩
  have hle : ∫ s in (0 : ℝ)..1, φ (dMB g (y + s • (t • v), v)) ≤ u := by
    have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) zero_le_one
      (hcont.intervalIntegrable_of_Icc zero_le_one)
      (continuousOn_const.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one)
      (fun s hs ↦ (hlt _ (subset_closure (subset_convexHull ℝ _ ⟨s, hs, rfl⟩))).le)
    simpa using this
  have hftc := hg.integral_dMB (x := y) (h := t • v) hseg φ
  have hsmul : ∫ s in (0 : ℝ)..1, φ (dMB g (y + s • (t • v), t • v)) =
      t * ∫ s in (0 : ℝ)..1, φ (dMB g (y + s • (t • v), v)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le zero_le_one] at hs
    simp only [hg.dMB_smul (hseg s hs), map_smul, smul_eq_mul]
  have hq : φ (t⁻¹ • (g (y + t • v) - g y)) =
      ∫ s in (0 : ℝ)..1, φ (dMB g (y + s • (t • v), v)) := by
    rw [map_smul, map_sub, smul_eq_mul, hftc, hsmul, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
  linarith

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Glöckner's lemma: for `g` of class `C^1`, the difference quotient
`t⁻¹ • (g (y + t • v) - g y)` tends to `dg(y)(v)` as `(y', v', t) → (y, v, 0)` with `t ≠ 0`. -/
theorem ContDiffMBOn.tendsto_quotient {g : E → F} {U : Set E} (hU : IsOpen U)
    (hg : ContDiffMBOn 1 g U) {y v : E} (hy : y ∈ U) :
    Tendsto (fun p : E × E × ℝ ↦ p.2.2⁻¹ • (g (p.1 + p.2.2 • p.2.1) - g p.1))
      (𝓝[{p | p.2.2 ≠ 0}] (y, v, 0)) (𝓝 (dMB g (y, v))) := by
  refine Filter.tendsto_def.mpr fun N hN ↦ ?_
  obtain ⟨N', ⟨hN', hN'c⟩, hN'N⟩ := (closed_nhds_basis _).mem_iff.mp hN
  obtain ⟨C, ⟨hC, hCconv⟩, hCN'⟩ := (LocallyConvexSpace.convex_basis (𝕜 := ℝ) _).mem_iff.mp hN'
  have hWN : closure C ⊆ N := (closure_minimal hCN' hN'c).trans hN'N
  have hcont : ContinuousAt (dMB g) (y, v) :=
    (hg.2.2 : ContinuousOn (dMB g) (U ×ˢ univ)).continuousAt
      (prod_mem_nhds (hU.mem_nhds hy) univ_mem)
  have hev : ∀ᶠ q : E × E in 𝓝 (y, v), q.1 ∈ U ∧ dMB g q ∈ C :=
    (continuous_fst.continuousAt.eventually_mem (hU.mem_nhds hy)).and
      (hcont.eventually_mem hC)
  have htube : ∀ᶠ p : E × E × ℝ in 𝓝 (y, v, 0), ∀ s ∈ Icc (0 : ℝ) 1,
      p.1 + s • (p.2.2 • p.2.1) ∈ U ∧ dMB g (p.1 + s • (p.2.2 • p.2.1), p.2.1) ∈ C := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun s _ ↦ ?_
    have hΨ : Continuous fun z : (E × E × ℝ) × ℝ ↦
        (z.1.1 + z.2 • (z.1.2.2 • z.1.2.1), z.1.2.1) := by
      fun_prop
    have : Tendsto (fun z : (E × E × ℝ) × ℝ ↦ (z.1.1 + z.2 • (z.1.2.2 • z.1.2.1), z.1.2.1))
        (𝓝 ((y, v, 0), s)) (𝓝 (y, v)) := by
      simpa using hΨ.tendsto ((y, v, (0 : ℝ)), s)
    exact this.eventually hev
  refine eventually_nhdsWithin_iff.mpr ?_
  filter_upwards [htube] with p hp hp0
  refine hWN ?_
  have hmem := hg.quotient_mem_closure_convexHull hp0 fun s hs ↦ (hp s hs).1
  refine closure_minimal (convexHull_min ?_ hCconv.closure) isClosed_closure hmem
  rintro _ ⟨s, hs, rfl⟩
  exact subset_closure (hp s hs).2

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Chain rule for directional derivatives. -/
theorem ContDiffMBOn.hasDirDerivAt_comp {f : E → F} {g : F → G} {V : Set F} (hV : IsOpen V)
    (hg : ContDiffMBOn 1 g V) {x h : E} {y : F} (hf : HasDirDerivAt f x h y) (hfx : f x ∈ V) :
    HasDirDerivAt (g ∘ f) x h (dMB g (f x, y)) := by
  have hq := hg.tendsto_quotient hV hfx (v := y)
  have hΔ : Tendsto (fun t : ℝ ↦ (f x, t⁻¹ • (f (x + t • h) - f x), t)) (𝓝[≠] 0)
      (𝓝[{p : F × F × ℝ | p.2.2 ≠ 0}] (f x, y, 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun t ht ↦ ht⟩
    exact tendsto_const_nhds.prodMk_nhds
      (Filter.Tendsto.prodMk_nhds hf (tendsto_id.mono_left nhdsWithin_le_nhds))
  refine (hq.comp hΔ).congr' (eventually_nhdsWithin_of_forall fun t ht ↦ ?_)
  have ht : t ≠ 0 := ht
  simp [smul_smul, mul_inv_cancel₀ ht]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Chain rule for `C^1` maps, with the formula `d(g ∘ f)(x) = dg(f x) ∘ df(x)`. -/
theorem ContDiffMBOn.comp_one {f : E → F} {g : F → G} {U : Set E} {V : Set F}
    (hV : IsOpen V) (hg : ContDiffMBOn 1 g V) (hf : ContDiffMBOn 1 f U) (hUV : MapsTo f U V) :
    ContDiffMBOn 1 (g ∘ f) U ∧ ∀ x ∈ U, ∀ h, dMB (g ∘ f) (x, h) = dMB g (f x, dMB f (x, h)) := by
  have hd : ∀ x ∈ U, ∀ h, HasDirDerivAt (g ∘ f) x h (dMB g (f x, dMB f (x, h))) :=
    fun x hx h ↦ hg.hasDirDerivAt_comp hV (hf.2.1 x hx h) (hUV hx)
  have heq : ∀ x ∈ U, ∀ h, dMB (g ∘ f) (x, h) = dMB g (f x, dMB f (x, h)) :=
    fun x hx h ↦ (hd x hx h).dMB_eq
  refine ⟨⟨hg.continuousOn.comp hf.continuousOn hUV, fun x hx h ↦ ?_, ?_⟩, heq⟩
  · rw [heq x hx h]; exact hd x hx h
  · have hc : ContinuousOn (fun p : E × E ↦ dMB g (f p.1, dMB f p)) (U ×ˢ univ) :=
      (hg.2.2 : ContinuousOn (dMB g) (V ×ˢ univ)).comp
        ((hf.continuousOn.comp continuousOn_fst
          fun p (hp : p ∈ U ×ˢ (univ : Set E)) ↦ hp.1).prodMk hf.2.2)
        fun p hp ↦ ⟨hUV hp.1, mem_univ _⟩
    exact hc.congr fun p hp ↦ heq p.1 hp.1 p.2

/-! ### Rules for `C^k` maps -/

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem HasDirDerivAt.congr_of_eventuallyEq {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
      {f₁ f₂ : E₁ → F}
    {x h : E₁} {y : F} (hd : HasDirDerivAt f₁ x h y) (heq : f₁ =ᶠ[𝓝 x] f₂) :
    HasDirDerivAt f₂ x h y := by
  have hl : Tendsto (fun t : ℝ ↦ x + t • h) (𝓝[≠] 0) (𝓝 x) := by
    have : Continuous fun t : ℝ ↦ x + t • h := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine hd.congr' ?_
  filter_upwards [hl.eventually heq] with t ht
  rw [ht, heq.eq_of_nhds]

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- `C^k` only depends on the values on the open set. -/
theorem ContDiffMBOn.congr_of_isOpen : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {f₁ f₂ : E₁ → F}
    {U : Set E₁}, IsOpen U → EqOn f₁ f₂ U → ContDiffMBOn k f₁ U → ContDiffMBOn k f₂ U := by
  intro k
  induction k with
  | zero =>
    intro E₁ _ _ _ _ _ _ _ f₁ f₂ U hU heq hf
    exact ContinuousOn.congr hf heq.symm
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ f₁ f₂ U hU heq hf
    have hd : ∀ x ∈ U, ∀ h, HasDirDerivAt f₂ x h (dMB f₁ (x, h)) := fun x hx h ↦
      (hf.2.1 x hx h).congr_of_eventuallyEq (heq.eventuallyEq_of_mem (hU.mem_nhds hx))
    have hdeq : EqOn (dMB f₁) (dMB f₂) (U ×ˢ univ) := fun p hp ↦
      ((hd p.1 hp.1 p.2).dMB_eq).symm
    refine ⟨ContinuousOn.congr hf.1 heq.symm, fun x hx h ↦ ?_,
      ih (hU.prod isOpen_univ) hdeq hf.2.2⟩
    rw [← hdeq ⟨hx, mem_univ h⟩]
    exact hd x hx h

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G] in
theorem HasDirDerivAt.prodMk {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
    {f : E₁ → F} {g : E₁ → G} {x h : E₁} {y : F} {z : G} (hf : HasDirDerivAt f x h y)
    (hg : HasDirDerivAt g x h z) : HasDirDerivAt (fun w ↦ (f w, g w)) x h (y, z) :=
  (hf.prodMk_nhds hg).congr fun t ↦ by simp only [Prod.mk_sub_mk, Prod.smul_mk]

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] in
/-- Pairs of `C^k` maps are `C^k`. -/
theorem ContDiffMBOn.prodMk : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {f : E₁ → F}
    {g : E₁ → G} {U : Set E₁}, IsOpen U → ContDiffMBOn k f U → ContDiffMBOn k g U →
      ContDiffMBOn k (fun w ↦ (f w, g w)) U := by
  intro k
  induction k with
  | zero =>
    intro E₁ _ _ _ _ _ _ _ f g U hU hf hg
    exact ContinuousOn.prodMk hf hg
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ f g U hU hf hg
    have hd : ∀ x ∈ U, ∀ h, HasDirDerivAt (fun w ↦ (f w, g w)) x h (dMB f (x, h), dMB g (x, h)) :=
      fun x hx h ↦ (hf.2.1 x hx h).prodMk (hg.2.1 x hx h)
    have hdeq : EqOn (fun p ↦ (dMB f p, dMB g p)) (dMB fun w ↦ (f w, g w)) (U ×ˢ univ) :=
      fun p hp ↦ ((hd p.1 hp.1 p.2).dMB_eq).symm
    refine ⟨ContinuousOn.prodMk hf.1 hg.1, fun x hx h ↦ ?_,
      ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ) hdeq
        (ih (hU.prod isOpen_univ) hf.2.2 hg.2.2)⟩
    rw [← hdeq ⟨hx, mem_univ h⟩]
    exact hd x hx h

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- Precomposition with a continuous linear map preserves `C^k`. -/
theorem ContDiffMBOn.comp_clm : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {E₂ : Type*}
    [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
    [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂]
    [T2Space E₂] (L : E₁ →L[ℝ] E₂) {f : E₂ → F} {U : Set E₂},
    IsOpen U → ContDiffMBOn k f U → ContDiffMBOn k (f ∘ L) (L ⁻¹' U) := by
  intro k
  induction k with
  | zero =>
    intro E₁ _ _ _ _ _ _ _ E₂ _ _ _ _ _ _ _ L f U hU hf
    exact ContinuousOn.comp hf L.continuous.continuousOn fun x hx ↦ hx
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ E₂ _ _ _ _ _ _ _ L f U hU hf
    have hd : ∀ x ∈ L ⁻¹' U, ∀ h, HasDirDerivAt (f ∘ L) x h (dMB f (L x, L h)) :=
      fun x hx h ↦ (hf.2.1 (L x) hx (L h)).congr fun t ↦ by simp
    have hdeq : EqOn (dMB f ∘ L.prodMap L) (dMB (f ∘ L)) ((L ⁻¹' U) ×ˢ univ) := fun p hp ↦ by
      simp only [Function.comp_apply, ContinuousLinearMap.coe_prodMap', Prod.map]
      exact ((hd p.1 hp.1 p.2).dMB_eq).symm
    refine ⟨ContinuousOn.comp hf.1 L.continuous.continuousOn fun x hx ↦ hx,
      fun x hx h ↦ ?_, ?_⟩
    · rw [← hdeq ⟨hx, mem_univ h⟩]
      exact hd x hx h
    · have h2 := ih (L.prodMap L) (hU.prod isOpen_univ) hf.2.2
      have hpre : (L.prodMap L) ⁻¹' (U ×ˢ univ) = (L ⁻¹' U) ×ˢ univ := by ext p; simp
      rw [hpre] at h2
      exact ContDiffMBOn.congr_of_isOpen ((hU.preimage L.continuous).prod isOpen_univ) hdeq h2

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem _root_.ContinuousLinearMap.hasDirDerivAt {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] (L : E₁ →L[ℝ] F) (x h : E₁) : HasDirDerivAt L x h (L h) := by
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  simp [smul_smul, inv_mul_cancel₀ ht]

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- Remark I.2.4: continuous linear maps are `C^k` for every `k`. -/
theorem _root_.ContinuousLinearMap.contDiffMBOn : ∀ (k : ℕ) {E₁ : Type u} [AddCommGroup E₁]
    [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] (L : E₁ →L[ℝ] F) (U : Set E₁),
    ContDiffMBOn k L U := by
  intro k
  induction k with
  | zero =>
    intro E₁ _ _ _ _ _ _ _ L U
    exact L.continuous.continuousOn
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ L U
    have heq : dMB L = ⇑(L.comp (ContinuousLinearMap.snd ℝ E₁ E₁)) := funext fun p ↦ by
      simp [(L.hasDirDerivAt p.1 p.2).dMB_eq]
    refine ⟨L.continuous.continuousOn, fun x _ h ↦ ?_, ?_⟩
    · rw [(L.hasDirDerivAt x h).dMB_eq]
      exact L.hasDirDerivAt x h
    · rw [heq]
      exact ih _ _

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- Remark I.2.4: continuous linear maps are smooth. -/
theorem _root_.ContinuousLinearMap.smoothMBOn (L : E →L[ℝ] F) (U : Set E) :
    SmoothMBOn L U :=
  fun k ↦ L.contDiffMBOn k U

theorem smoothMBOn_id (U : Set E) : SmoothMBOn (id : E → E) U :=
  (ContinuousLinearMap.id ℝ E).smoothMBOn U

/-- (vi) Chain rule for `C^k` maps. -/
theorem ContDiffMBOn.comp : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {F₁ : Type v}
    [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁] [IsTopologicalAddGroup F₁]
    [ContinuousSMul ℝ F₁] [LocallyConvexSpace ℝ F₁] [T2Space F₁] {f : E₁ → F₁} {g : F₁ → G}
    {U : Set E₁} {V : Set F₁}, IsOpen U → IsOpen V → ContDiffMBOn k g V → ContDiffMBOn k f U →
      MapsTo f U V → ContDiffMBOn k (g ∘ f) U := by
  intro k
  induction k with
  | zero =>
    intro E₁ _ _ _ _ _ _ _ F₁ _ _ _ _ _ _ _ f g U V hU hV hg hf hUV
    exact ContinuousOn.comp hg hf hUV
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ F₁ _ _ _ _ _ _ _ f g U V hU hV hg hf hUV
    obtain ⟨h1, heq⟩ := ContDiffMBOn.comp_one hV (hg.of_le (by omega)) (hf.of_le (by omega)) hUV
    refine ⟨h1.1, h1.2.1, ?_⟩
    have hfst : ContDiffMBOn k (f ∘ ContinuousLinearMap.fst ℝ E₁ E₁) (U ×ˢ univ) := by
      have := ContDiffMBOn.comp_clm (ContinuousLinearMap.fst ℝ E₁ E₁) hU hf.of_succ
      have hpre : (ContinuousLinearMap.fst ℝ E₁ E₁) ⁻¹' U = U ×ˢ univ := by ext; simp
      rwa [hpre] at this
    have hP := ContDiffMBOn.prodMk (hU.prod isOpen_univ) hfst hf.2.2
    have hc := ih (hU.prod isOpen_univ) (hV.prod isOpen_univ) hg.2.2 hP
      (fun p hp ↦ ⟨hUV hp.1, mem_univ _⟩)
    refine ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ) (fun p hp ↦ ?_) hc
    simp only [Function.comp_apply, ContinuousLinearMap.coe_fst']
    exact (heq p.1 hp.1 p.2).symm

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem ContDiffMBOn.mono : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {f : E₁ → F} {U V : Set E₁},
    ContDiffMBOn k f U → V ⊆ U → ContDiffMBOn k f V := by
  intro k
  induction k with
  | zero =>
    intro E₁ _ _ _ _ _ _ _ f U V hf hVU
    exact ContinuousOn.mono hf hVU
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ f U V hf hVU
    exact ⟨hf.1.mono hVU, fun x hx h ↦ hf.2.1 x (hVU hx) h,
      ih hf.2.2 (Set.prod_mono hVU subset_rfl)⟩

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] [ContinuousSMul ℝ F] in
/-- Being `C^k` is a local property. -/
theorem ContDiffMBOn.of_local : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {f : E₁ → F} {U : Set E₁}, IsOpen U →
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ ContDiffMBOn k f (U ∩ W)) → ContDiffMBOn k f U := by
  have hcont : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
      {f : E₁ → F} {U : Set E₁}, IsOpen U →
      (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ ContDiffMBOn k f (U ∩ W)) → ContinuousOn f U := by
    intro k E₁ _ _ _ f U hU hloc x hx
    obtain ⟨W, hW, hxW, hf⟩ := hloc x hx
    exact (hf.continuousOn x ⟨hx, hxW⟩ |>.continuousAt
      ((hU.inter hW).mem_nhds ⟨hx, hxW⟩)).continuousWithinAt
  intro k
  induction k with
  | zero =>
    intro E₁ _ _ _ _ _ _ _ f U hU hloc
    exact hcont hU hloc
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ f U hU hloc
    refine ⟨hcont hU hloc, fun x hx h ↦ ?_, ih (hU.prod isOpen_univ) fun p hp ↦ ?_⟩
    · obtain ⟨W, _, hxW, hf⟩ := hloc x hx
      exact hf.2.1 x ⟨hx, hxW⟩ h
    · obtain ⟨W, hW, hxW, hf⟩ := hloc p.1 hp.1
      refine ⟨W ×ˢ univ, hW.prod isOpen_univ, ⟨hxW, mem_univ _⟩, ?_⟩
      have := hf.2.2
      rwa [Set.prod_inter_prod, Set.inter_self]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ F] [T2Space F] in
/-- (vi) Chain rule: formula for the derivative. -/
theorem ContDiffMBOn.dMB_comp {f : E → F} {g : F → G} {U : Set E} {V : Set F}
    (hV : IsOpen V) (hg : ContDiffMBOn 1 g V) (hf : ContDiffMBOn 1 f U)
    (hUV : MapsTo f U V) {x : E} (hx : x ∈ U) (h : E) :
    dMB (g ∘ f) (x, h) = dMB g (f x, dMB f (x, h)) :=
  (hg.comp_one hV hf hUV).2 x hx h

/-! ### Mean value inclusion and partial derivatives (Michor 1980, 8.3–8.4) -/

omit [T2Space F] in
/-- Closed convex neighborhoods form a basis in a locally convex space. -/
theorem exists_closed_convex_nhds_subset {a : F} {N : Set F} (hN : N ∈ 𝓝 a) :
    ∃ W ∈ 𝓝 a, IsClosed W ∧ Convex ℝ W ∧ W ⊆ N := by
  obtain ⟨N', ⟨hN', hN'c⟩, hN'N⟩ := (closed_nhds_basis _).mem_iff.mp hN
  obtain ⟨C, ⟨hC, hCconv⟩, hCN'⟩ := (LocallyConvexSpace.convex_basis (𝕜 := ℝ) _).mem_iff.mp hN'
  exact ⟨closure C, mem_of_superset hC subset_closure, isClosed_closure, hCconv.closure,
    (closure_minimal hCN' hN'c).trans hN'N⟩

omit [TopologicalSpace E] [ContinuousSMul ℝ F] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F]
    [T2Space F] in
/-- Weak fundamental theorem of calculus along a segment, assuming only the directional
derivatives in the direction of the segment. -/
theorem integral_of_hasDirDerivAt {f : E → F} {z w : E} {D : ℝ → F}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDirDerivAt f (z + s • w) w (D s))
    (hD : ContinuousOn D (Icc 0 1)) (φ : F →L[ℝ] ℝ) :
    φ (f (z + w)) - φ (f z) = ∫ s in (0 : ℝ)..1, φ (D s) := by
  have hder : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s : ℝ ↦ φ (f (z + s • w))) (φ (D s)) s :=
    fun s hs ↦ (hd s hs).hasDerivAt_clm φ
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (fun s hs ↦ (hder s hs).continuousAt.continuousWithinAt)
    (fun s hs ↦ hder s (Ioo_subset_Icc_self hs))
    ((φ.continuous.comp_continuousOn hD).intervalIntegrable_of_Icc zero_le_one)
  simpa using this.symm

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] [T2Space F] in
/-- Mean value inclusion (Michor 8.4, remark): the increment along a segment lies in every
closed convex set containing the directional derivatives along the segment. -/
theorem sub_mem_of_hasDirDerivAt {f : E → F} {z w : E} {D : ℝ → F}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDirDerivAt f (z + s • w) w (D s))
    (hD : ContinuousOn D (Icc 0 1)) {W : Set F} (hWc : Convex ℝ W) (hWcl : IsClosed W)
    (hDW : ∀ s ∈ Icc (0 : ℝ) 1, D s ∈ W) : f (z + w) - f z ∈ W := by
  by_contra hnot
  obtain ⟨φ, u, hlt, hgt⟩ := geometric_hahn_banach_closed_point hWc hWcl hnot
  have hle : ∫ s in (0 : ℝ)..1, φ (D s) ≤ u := by
    have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) zero_le_one
      ((φ.continuous.comp_continuousOn hD).intervalIntegrable_of_Icc zero_le_one)
      (continuousOn_const.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one)
      (fun s hs ↦ (hlt _ (hDW s hs)).le)
    simpa using this
  have := integral_of_hasDirDerivAt hd hD φ
  rw [map_sub] at hgt
  linarith

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Directional difference quotients converge locally uniformly in the base point: if `f` has
directional derivative `D q` in the direction `w` at every `q ∈ U`, with `D` continuous, then
`t⁻¹ • (f (q + t • w) - f q) → D p` as `(q, t) → (p, 0)`, `t ≠ 0`. -/
theorem tendsto_quotient_of_hasDirDerivAt {f : E → F} {U : Set E} (hU : IsOpen U) {w : E}
    {D : E → F} (hd : ∀ q ∈ U, HasDirDerivAt f q w (D q)) (hD : ContinuousOn D U) {p : E}
    (hp : p ∈ U) :
    Tendsto (fun r : E × ℝ ↦ r.2⁻¹ • (f (r.1 + r.2 • w) - f r.1))
      (𝓝[{r | r.2 ≠ 0}] (p, 0)) (𝓝 (D p)) := by
  refine Filter.tendsto_def.mpr fun N hN ↦ ?_
  obtain ⟨W, hW, hWcl, hWc, hWN⟩ := exists_closed_convex_nhds_subset hN
  have hev : ∀ᶠ q in 𝓝 p, q ∈ U ∧ D q ∈ W :=
    (hU.eventually_mem hp).and ((hD.continuousAt (hU.mem_nhds hp)).eventually_mem hW)
  have htube : ∀ᶠ r : E × ℝ in 𝓝 (p, 0), ∀ s ∈ Icc (0 : ℝ) 1,
      r.1 + (s * r.2) • w ∈ U ∧ D (r.1 + (s * r.2) • w) ∈ W := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun s _ ↦ ?_
    have hΨ : Continuous fun z : (E × ℝ) × ℝ ↦ z.1.1 + (z.2 * z.1.2) • w := by fun_prop
    have : Tendsto (fun z : (E × ℝ) × ℝ ↦ z.1.1 + (z.2 * z.1.2) • w) (𝓝 ((p, 0), s)) (𝓝 p) := by
      simpa using hΨ.tendsto ((p, (0 : ℝ)), s)
    exact this.eventually hev
  refine eventually_nhdsWithin_iff.mpr ?_
  filter_upwards [htube] with r hr hr0
  have ht : r.2 ≠ 0 := hr0
  refine hWN ((Set.mem_smul_set_iff_inv_smul_mem₀ ht W _).mp ?_)
  have hpts : ∀ s : ℝ, r.1 + s • (r.2 • w) = r.1 + (s * r.2) • w := fun s ↦ by rw [smul_smul]
  have hd' : ∀ s ∈ Icc (0 : ℝ) 1, HasDirDerivAt f (r.1 + s • (r.2 • w)) (r.2 • w)
      (r.2 • D (r.1 + (s * r.2) • w)) := fun s hs ↦ by
    rw [hpts s]; exact (hd _ (hr s hs).1).smul_dir r.2
  have hD' : ContinuousOn (fun s : ℝ ↦ r.2 • D (r.1 + (s * r.2) • w)) (Icc 0 1) :=
    (continuous_const_smul _).comp_continuousOn (hD.comp
      (by fun_prop : Continuous fun s : ℝ ↦ r.1 + (s * r.2) • w).continuousOn
      fun s hs ↦ (hr s hs).1)
  exact sub_mem_of_hasDirDerivAt hd' hD' (hWc.smul r.2) (hWcl.smul_of_ne_zero ht)
    (fun s hs ↦ Set.smul_mem_smul_set (hr s hs).2)

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- A map with jointly continuous directional derivatives is continuous (Michor 8.1). -/
theorem continuousOn_of_hasDirDerivAt {f : E → F} {U : Set E} (hU : IsOpen U)
    {D : E × E → F} (hd : ∀ q ∈ U, ∀ w, HasDirDerivAt f q w (D (q, w)))
    (hD : ContinuousOn D (U ×ˢ univ)) : ContinuousOn f U := by
  intro p hp
  refine ContinuousAt.continuousWithinAt (Filter.tendsto_def.mpr fun N hN ↦ ?_)
  have hD0 : D (p, 0) = 0 := by
    refine tendsto_nhds_unique (hd p hp 0) ?_
    simp
  have hN0 : (fun z ↦ f p + z) ⁻¹' N ∈ 𝓝 (0 : F) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hN)
  obtain ⟨W, hW, hWcl, hWc, hWN⟩ := exists_closed_convex_nhds_subset hN0
  have hcont : ContinuousAt D (p, 0) :=
    hD.continuousAt (prod_mem_nhds (hU.mem_nhds hp) univ_mem)
  have hev : ∀ᶠ q : E × E in 𝓝 (p, 0), q.1 ∈ U ∧ D q ∈ W :=
    (continuous_fst.continuousAt.eventually_mem (hU.mem_nhds hp)).and
      (hcont.eventually_mem (by rwa [hD0]))
  have htube : ∀ᶠ q in 𝓝 p, ∀ s ∈ Icc (0 : ℝ) 1,
      p + s • (q - p) ∈ U ∧ D (p + s • (q - p), q - p) ∈ W := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun s _ ↦ ?_
    have hΨ : Continuous fun z : E × ℝ ↦ (p + z.2 • (z.1 - p), z.1 - p) := by fun_prop
    have : Tendsto (fun z : E × ℝ ↦ (p + z.2 • (z.1 - p), z.1 - p)) (𝓝 (p, s)) (𝓝 (p, 0)) := by
      simpa using hΨ.tendsto (p, s)
    exact this.eventually hev
  filter_upwards [htube] with q hq
  have hmem := sub_mem_of_hasDirDerivAt (f := f) (z := p) (w := q - p)
    (D := fun s ↦ D (p + s • (q - p), q - p)) (fun s hs ↦ hd _ (hq s hs).1 _)
    (hD.comp (by fun_prop : Continuous fun s : ℝ ↦ (p + s • (q - p), q - p)).continuousOn
      fun s hs ↦ ⟨(hq s hs).1, mem_univ _⟩) hWc hWcl
    (fun s hs ↦ (hq s hs).2)
  have := hWN hmem
  simpa using this

omit [LocallyConvexSpace ℝ E] [T2Space E] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Michor 1980, Lemma 8.3: a map on an open subset of `E × F` whose partial directional
derivatives exist and are jointly continuous is `C^1`, with
`df(p)(u, v) = D₁f(p) u + D₂f(p) v`. -/
theorem contDiffMBOn_one_of_partials {f : E × F → G} {U : Set (E × F)} (hU : IsOpen U)
    {d₁ : E × F → E → G} {d₂ : E × F → F → G}
    (h₁ : ∀ p ∈ U, ∀ u, HasDirDerivAt f p (u, 0) (d₁ p u))
    (h₂ : ∀ p ∈ U, ∀ v, HasDirDerivAt f p (0, v) (d₂ p v))
    (hc₁ : ContinuousOn (fun q : (E × F) × E ↦ d₁ q.1 q.2) (U ×ˢ univ))
    (hc₂ : ContinuousOn (fun q : (E × F) × F ↦ d₂ q.1 q.2) (U ×ˢ univ)) :
    ContDiffMBOn 1 f U ∧ ∀ p ∈ U, ∀ u v, dMB f (p, (u, v)) = d₁ p u + d₂ p v := by
  have hd : ∀ p ∈ U, ∀ u v, HasDirDerivAt f p (u, v) (d₁ p u + d₂ p v) := by
    intro p hp u v
    have hA := tendsto_quotient_of_hasDirDerivAt hU (w := ((u, 0) : E × F))
      (D := fun q ↦ d₁ q u) (fun q hq ↦ h₁ q hq u)
      (hc₁.comp (by fun_prop : Continuous fun q : E × F ↦ (q, u)).continuousOn
        fun q hq ↦ ⟨hq, mem_univ _⟩) hp
    have hr : Tendsto (fun t : ℝ ↦ (p + t • ((0, v) : E × F), t)) (𝓝[≠] 0)
        (𝓝[{r : (E × F) × ℝ | r.2 ≠ 0}] (p, 0)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun t ht ↦ ht⟩
      have : Continuous fun t : ℝ ↦ (p + t • ((0, v) : E × F), t) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine ((hA.comp hr).add (h₂ p hp v)).congr fun t ↦ ?_
    have hpt : p + t • ((0, v) : E × F) + t • ((u, 0) : E × F) = p + t • (u, v) := by
      ext <;> simp [add_comm]
    simp only [Function.comp_apply, hpt, ← smul_add, sub_add_sub_cancel]
  have heq : ∀ p ∈ U, ∀ u v, dMB f (p, (u, v)) = d₁ p u + d₂ p v :=
    fun p hp u v ↦ (hd p hp u v).dMB_eq
  have hDc : ContinuousOn (fun q : (E × F) × (E × F) ↦ d₁ q.1 q.2.1 + d₂ q.1 q.2.2)
      (U ×ˢ univ) :=
    (hc₁.comp (by fun_prop : Continuous fun q : (E × F) × (E × F) ↦ (q.1, q.2.1)).continuousOn
      fun q (hq : q ∈ U ×ˢ (univ : Set (E × F))) ↦ ⟨hq.1, mem_univ _⟩).add
      (hc₂.comp (by fun_prop : Continuous fun q : (E × F) × (E × F) ↦ (q.1, q.2.2)).continuousOn
        fun q (hq : q ∈ U ×ˢ (univ : Set (E × F))) ↦ ⟨hq.1, mem_univ _⟩)
  refine ⟨⟨continuousOn_of_hasDirDerivAt hU (fun q hq w ↦ hd q hq w.1 w.2) hDc,
    fun p hp w ↦ ?_, ?_⟩, heq⟩
  · rw [heq p hp w.1 w.2]; exact hd p hp w.1 w.2
  · exact hDc.congr fun q hq ↦ heq q.1 hq.1 q.2.1 q.2.2

/-! ### Proposition I.2.3 (ii) second part, and (iv) -/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] in
/-- (ii) A `C^1` map on a connected open set with `df = 0` is constant. -/
theorem ContDiffMBOn.eqOn_of_dMB_eq_zero {f : E → F} {U : Set E} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hf : ContDiffMBOn 1 f U) (h0 : ∀ x ∈ U, ∀ h, dMB f (x, h) = 0)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) : f x = f y := by
  have hloc : ∀ p ∈ U, ∀ᶠ q in 𝓝 p, f p = f q := by
    intro p hp
    obtain ⟨C, ⟨hC, hCconv⟩, hCU⟩ :=
      (LocallyConvexSpace.convex_basis (𝕜 := ℝ) p).mem_iff.mp (hU.mem_nhds hp)
    filter_upwards [hC] with q hq
    have hseg : ∀ s ∈ Icc (0 : ℝ) 1, p + s • (q - p) ∈ U := fun s hs ↦
      hCU (hCconv.add_smul_sub_mem (mem_of_mem_nhds hC) hq hs)
    have hmem := sub_mem_of_hasDirDerivAt (f := f) (z := p) (w := q - p) (D := fun _ ↦ 0)
      (fun s hs ↦ by
        have := hf.2.1 _ (hseg s hs) (q - p)
        rwa [h0 _ (hseg s hs)] at this)
      continuousOn_const (convex_singleton 0) isClosed_singleton (fun _ _ ↦ rfl)
    simp only [add_sub_cancel, mem_singleton_iff, sub_eq_zero] at hmem
    exact hmem.symm
  exact hUc.induction₂ (fun a b ↦ f a = f b)
    (fun z hz ↦ nhdsWithin_le_nhds (hloc z hz)) (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂)
    (fun _ _ _ _ h ↦ h.symm) hx hy

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem HasDirDerivAt.sub {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
    {f g : E₁ → F} {x h : E₁} {a b : F} (hf : HasDirDerivAt f x h a)
    (hg : HasDirDerivAt g x h b) : HasDirDerivAt (fun y ↦ f y - g y) x h (a - b) :=
  (Filter.Tendsto.sub hf hg).congr fun t ↦ by simp only [← smul_sub]; congr 1; abel

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem HasDirDerivAt.comp_add_const {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
     {f : E₁ → F} {y c w : E₁} {a : F} (hf : HasDirDerivAt f (y + c) w a) :
    HasDirDerivAt (fun z ↦ f (z + c)) y w a :=
  hf.congr fun t ↦ by simp only [add_right_comm]

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The key estimate for the symmetry of the second derivative: the second difference
`f (x + t h₁ + t h₂) - f (x + t h₁) - f (x + t h₂) + f x`, divided by `t²`, eventually lies in
any closed convex neighborhood of `d²f(x)(h₁, h₂)`. Two applications of the mean value
inclusion. -/
theorem ContDiffMBOn.second_diff_mem {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn 2 f U) {x : E} (hx : x ∈ U) (h₁ h₂ : E) {W : Set F}
    (hW : W ∈ 𝓝 (dMB (dMB f) ((x, h₁), (h₂, 0)))) (hWcl : IsClosed W) (hWc : Convex ℝ W) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      (t * t)⁻¹ • (f (x + t • h₁ + t • h₂) - f (x + t • h₁) - f (x + t • h₂) + f x) ∈ W := by
  set D₁₂ : E → F := fun y ↦ dMB (dMB f) ((y, h₁), (h₂, 0)) with hD₁₂
  have hf1 : ContDiffMBOn 1 f U := hf.of_le (by omega)
  have hdf : ContDiffMBOn 1 (dMB f) (U ×ˢ univ) := hf.2.2
  have hD : ContinuousOn D₁₂ U := by
    have h0 : ContinuousOn (dMB (dMB f)) ((U ×ˢ univ) ×ˢ univ) := hdf.2.2
    exact h0.comp
      (by fun_prop : Continuous fun y : E ↦ ((y, h₁), (h₂, (0 : E)))).continuousOn
      fun y hy ↦ ⟨⟨hy, mem_univ _⟩, mem_univ _⟩
  -- directional derivative of `y ↦ df(y)(h₁)` in the direction `h₂`
  have hinner : ∀ y ∈ U, HasDirDerivAt (fun y' ↦ dMB f (y', h₁)) y h₂ (D₁₂ y) := by
    intro y hy
    refine (hdf.2.1 (y, h₁) ⟨hy, mem_univ _⟩ (h₂, 0)).congr fun t ↦ ?_
    simp
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U ∧ D₁₂ y ∈ W :=
    (hU.eventually_mem hx).and ((hD.continuousAt (hU.mem_nhds hx)).eventually_mem hW)
  have htube : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      x + (q.1 * t) • h₁ + (q.2 * t) • h₂ ∈ U ∧ D₁₂ (x + (q.1 * t) • h₁ + (q.2 * t) • h₂) ∈ W := by
    refine (isCompact_Icc.prod isCompact_Icc).eventually_forall_of_forall_eventually
      fun q _ ↦ ?_
    have hΨ : Continuous fun z : ℝ × (ℝ × ℝ) ↦ x + (z.2.1 * z.1) • h₁ + (z.2.2 * z.1) • h₂ := by
      fun_prop
    have : Tendsto (fun z : ℝ × (ℝ × ℝ) ↦ x + (z.2.1 * z.1) • h₁ + (z.2.2 * z.1) • h₂)
        (𝓝 (0, q)) (𝓝 x) := by
      simpa using hΨ.tendsto ((0 : ℝ), q)
    exact this.eventually hev
  filter_upwards [nhdsWithin_le_nhds htube, self_mem_nhdsWithin] with t ht (ht0 : t ≠ 0)
  have hU' : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ τ ∈ Icc (0 : ℝ) 1,
      x + (σ * t) • h₁ + (τ * t) • h₂ ∈ U := fun σ hσ τ hτ ↦ (ht (σ, τ) ⟨hσ, hτ⟩).1
  -- inner step: `df(z + t h₂)(h₁) - df(z)(h₁) ∈ t • W` for `z = x + σ t h₁`
  have hstep : ∀ σ ∈ Icc (0 : ℝ) 1,
      dMB f (x + (σ * t) • h₁ + t • h₂, h₁) - dMB f (x + (σ * t) • h₁, h₁) ∈ t • W := by
    intro σ hσ
    have hpts : ∀ τ : ℝ, x + (σ * t) • h₁ + τ • (t • h₂) = x + (σ * t) • h₁ + (τ * t) • h₂ :=
      fun τ ↦ by rw [smul_smul]
    have hd : ∀ τ ∈ Icc (0 : ℝ) 1, HasDirDerivAt (fun y' ↦ dMB f (y', h₁))
        (x + (σ * t) • h₁ + τ • (t • h₂)) (t • h₂)
        (t • D₁₂ (x + (σ * t) • h₁ + (τ * t) • h₂)) := fun τ hτ ↦ by
      rw [hpts τ]; exact (hinner _ (hU' σ hσ τ hτ)).smul_dir t
    have hDc : ContinuousOn (fun τ : ℝ ↦ t • D₁₂ (x + (σ * t) • h₁ + (τ * t) • h₂)) (Icc 0 1) :=
      (continuous_const_smul _).comp_continuousOn (hD.comp
        (by fun_prop : Continuous fun τ : ℝ ↦ x + (σ * t) • h₁ + (τ * t) • h₂).continuousOn
        fun τ hτ ↦ hU' σ hσ τ hτ)
    exact sub_mem_of_hasDirDerivAt hd hDc (hWc.smul t) (hWcl.smul_of_ne_zero ht0)
      (fun τ hτ ↦ Set.smul_mem_smul_set (ht (σ, τ) ⟨hσ, hτ⟩).2)
  -- outer step, for `G y = f (y + t h₂) - f y` along `x + σ t h₁`
  have hpts : ∀ σ : ℝ, x + σ • (t • h₁) = x + (σ * t) • h₁ := fun σ ↦ by rw [smul_smul]
  have hU0 : ∀ σ ∈ Icc (0 : ℝ) 1, x + (σ * t) • h₁ ∈ U := fun σ hσ ↦ by
    simpa using hU' σ hσ 0 ⟨le_rfl, zero_le_one⟩
  have hU1 : ∀ σ ∈ Icc (0 : ℝ) 1, x + (σ * t) • h₁ + t • h₂ ∈ U := fun σ hσ ↦ by
    simpa using hU' σ hσ 1 ⟨zero_le_one, le_rfl⟩
  have hd : ∀ σ ∈ Icc (0 : ℝ) 1, HasDirDerivAt (fun y ↦ f (y + t • h₂) - f y)
      (x + σ • (t • h₁)) (t • h₁)
      (t • dMB f (x + (σ * t) • h₁ + t • h₂, h₁) - t • dMB f (x + (σ * t) • h₁, h₁)) := by
    intro σ hσ
    rw [hpts σ]
    exact (((hf1.2.1 _ (hU1 σ hσ) h₁).smul_dir t).comp_add_const).sub
      ((hf1.2.1 _ (hU0 σ hσ) h₁).smul_dir t)
  have hdfc : ContinuousOn (dMB f) (U ×ˢ univ) := hdf.continuousOn
  have hDc : ContinuousOn (fun σ : ℝ ↦
      t • dMB f (x + (σ * t) • h₁ + t • h₂, h₁) - t • dMB f (x + (σ * t) • h₁, h₁)) (Icc 0 1) := by
    refine ((continuous_const_smul t).comp_continuousOn (hdfc.comp
      (by fun_prop : Continuous fun σ : ℝ ↦ (x + (σ * t) • h₁ + t • h₂, h₁)).continuousOn
      fun σ hσ ↦ ⟨hU1 σ hσ, mem_univ _⟩)).sub
      ((continuous_const_smul t).comp_continuousOn (hdfc.comp
        (by fun_prop : Continuous fun σ : ℝ ↦ (x + (σ * t) • h₁, h₁)).continuousOn
        fun σ hσ ↦ ⟨hU0 σ hσ, mem_univ _⟩))
  have hmem := sub_mem_of_hasDirDerivAt hd hDc ((hWc.smul t).smul t)
    ((hWcl.smul_of_ne_zero ht0).smul_of_ne_zero ht0)
    (fun σ hσ ↦ by rw [← smul_sub]; exact Set.smul_mem_smul_set (hstep σ hσ))
  rw [smul_smul] at hmem
  refine (Set.mem_smul_set_iff_inv_smul_mem₀ (mul_ne_zero ht0 ht0) W _).mp ?_
  convert hmem using 1
  abel

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- (iv) Symmetry of the second derivative. -/
theorem ContDiffMBOn.dMB_dMB_symm {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn 2 f U) {x : E} (hx : x ∈ U) (h₁ h₂ : E) :
    dMB (dMB f) ((x, h₁), (h₂, 0)) = dMB (dMB f) ((x, h₂), (h₁, 0)) := by
  by_contra hne
  obtain ⟨N₁, N₂, hN₁, hN₂, hdisj⟩ := t2_separation_nhds hne
  obtain ⟨W₁, hW₁, hW₁cl, hW₁c, hW₁N⟩ := exists_closed_convex_nhds_subset hN₁
  obtain ⟨W₂, hW₂, hW₂cl, hW₂c, hW₂N⟩ := exists_closed_convex_nhds_subset hN₂
  have e₁ := hf.second_diff_mem hU hx h₁ h₂ hW₁ hW₁cl hW₁c
  have e₂ := hf.second_diff_mem hU hx h₂ h₁ hW₂ hW₂cl hW₂c
  obtain ⟨t, ht₁, ht₂⟩ := (e₁.and e₂).exists
  rw [add_right_comm x (t • h₂) (t • h₁)] at ht₂
  have : f (x + t • h₁ + t • h₂) - f (x + t • h₂) - f (x + t • h₁) + f x =
      f (x + t • h₁ + t • h₂) - f (x + t • h₁) - f (x + t • h₂) + f x := by abel
  rw [this] at ht₂
  exact Set.disjoint_left.mp hdisj (hW₁N ht₁) (hW₂N ht₂)

end LocallyConvex

end LCAnalysis
