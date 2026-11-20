/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Proximal
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Existence
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Supremum
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus

/-!
# Finite Lipschitz convex extension from compact support data

An open-domain C0 convex function in finite dimension has a finite global
Lipschitz convex extension agreeing on any nonempty compact subset. The
complete-space local C1 strict-convex interface is retained in every dimension. Only the compact
subset is extended. On its interior, the extension's global subgradient image
is exactly the original function's domain-relative supporting-slope image.

This supplies compact localization for Letwin arXiv:2607.24164v1, Lemma 2.2,
and the local Monge–Ampere regularity route of BB arXiv:1207.6128v1,
Theorem 2.24(ii). No whole-domain extension or MA identification is assumed. Actual Moreau
regularizers of the generated compact patch now give global convex C1 functions
with Lipschitz gradients and a genuine uniform limit on the compact set only.
No source Lipschitz/extension/regularity or regularized MA equation is assumed.
For zero-frontier closure-C0 convex sources, a negative compact sublevel now
generates a patch with the FULL ambient weak/strict sublevel identities. Actual
frontier crossing proves properness, without a coercivity or image input.
-/

@[expose] public section

section

open Set Metric Filter Topology
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Analysis

/-- The common affine-support construction. Each caller produces the actual
support family and its slope cap from its source data. -/
private theorem exists_extension_of_support_family {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : E → ℝ} {Ω K : Set E} (hv : ConvexOn ℝ Ω v)
    (hvc : ContinuousOn v Ω) (hKc : IsCompact K) (hKn : K.Nonempty) (hKΩ : K ⊆ Ω)
    (T : Set (E × E)) (hfamily : ∀ q ∈ T, q.1 ∈ K ∧ ∀ y ∈ Ω, v q.1 + ⟪q.2, y - q.1⟫ ≤ v y)
    (htouch : ∀ x ∈ K, ∃ p, (x, p) ∈ T) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ q ∈ T, ‖q.2‖ ≤ R) :
    ∃ (V : E → ℝ) (L : NNReal),
      ConvexOn ℝ univ V ∧
        LipschitzWith L V ∧
          (∀ x ∈ K, V x = v x) ∧
            (∀ G ⊆ interior K, subgradientImage V G = subgradientImageOn v Ω G) := by
  let A : E → (E × E) → ℝ := fun x q => v q.1 + ⟪q.2, x - q.1⟫
  let V : E → ℝ := fun x => sSup (A x '' T)
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hKn
    obtain ⟨p, hp⟩ := htouch z hz
    exact ⟨(z, p), hp⟩
  have hnonempty (x : E) : (A x '' T).Nonempty := hTne.image (A x)
  have hcont : ContinuousOn (fun z => |v z| + R * ‖z‖) K :=
    (hvc.mono hKΩ).abs.add (continuousOn_const.mul continuous_norm.continuousOn)
  obtain ⟨z₀, hz₀, hmax⟩ := hKc.exists_isMaxOn hKn hcont
  let C : ℝ := |v z₀| + R * ‖z₀‖
  have hbase : ∀ z ∈ K, |v z| + R * ‖z‖ ≤ C := fun z hz => hmax hz
  have hAbdd (x : E) : BddAbove (A x '' T) := by
    refine ⟨C + R * ‖x‖, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    have hp := hbound q hq
    have hi := real_inner_le_norm q.2 (x - q.1)
    have hn := norm_sub_le x q.1
    have hc := hbase q.1 (hfamily q hq).1
    dsimp [A]
    calc
      _ ≤ |v q.1| + R * ‖x - q.1‖ :=
        add_le_add (le_abs_self _) (hi.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _)))
      _ ≤ |v q.1| + R * (‖x‖ + ‖q.1‖) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hn hR)
      _ ≤ C + R * ‖x‖ := by linarith only [hc]
  have hAle (x : E) (q : E × E) (hq : q ∈ T) : A x q ≤ V x := le_csSup (hAbdd x) ⟨q, hq, rfl⟩
  have hVdom (x : E) (hx : x ∈ Ω) : V x ≤ v x := by
    apply csSup_le (hnonempty x)
    rintro _ ⟨q, hq, rfl⟩
    exact (hfamily q hq).2 x hx
  have hVK (x : E) (hx : x ∈ K) : V x = v x := by
    refine le_antisymm (hVdom x (hKΩ hx)) ?_
    obtain ⟨p, hp⟩ := htouch x hx
    have h := hAle x (x, p) hp
    simpa only [A, sub_self, inner_zero_right, add_zero] using h
  have hAconv : ∀ q ∈ T, ConvexOn ℝ univ (fun x => A x q) := by
    intro q _hq
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b _ha _hb hab
    have hvect : a • x + b • y - q.1 = a • (x - q.1) + b • (y - q.1) := by
      calc
        _ = a • x + b • y - (a + b) • q.1 := by rw [hab, one_smul]
        _ = _ := by module
    have hlin : A (a • x + b • y) q = a * A x q + b * A y q := by
      dsimp [A]
      rw [hvect, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      nlinarith [congrArg (fun t : ℝ => t * v q.1) hab]
    exact hlin.le
  have hconv : ConvexOn ℝ univ V :=
    convexOn_sSup_image_of_bddAbove convex_univ hTne (fun q x => A x q) hAconv
      (fun x _hx => hAbdd x)
  have hinc (x y : E) : V x ≤ V y + R * ‖x - y‖ := by
    apply csSup_le (hnonempty x)
    rintro _ ⟨q, hq, rfl⟩
    have hp := hbound q hq
    have hi :=
      (real_inner_le_norm q.2 (x - y)).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
    have hlin : A x q = A y q + ⟪q.2, x - y⟫ := by
      dsimp [A]
      simp only [inner_sub_right]
      ring
    rw [hlin]
    exact add_le_add (hAle y q hq) hi
  have hLip : LipschitzWith R.toNNReal V := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal R hR]
    have hxy := hinc x y
    have hyx := hinc y x
    rw [norm_sub_rev] at hyx
    exact abs_le.mpr ⟨by linarith only [hyx], by linarith only [hxy]⟩
  refine ⟨V, R.toNNReal, hconv, hLip, hVK, ?_⟩
  intro G hG
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    have hxI : x ∈ interior K := hG hx
    refine ⟨x, hx, ?_⟩
    have hloc : ∀ y ∈ interior K, v x + ⟪p, y - x⟫ ≤ v y := by
      intro y hy
      rw [← hVK x (interior_subset hxI), ← hVK y (interior_subset hy)]
      exact hp y
    exact subgradient_le_on_of_isOpen hv isOpen_interior (interior_subset.trans hKΩ) hxI hloc
  · rintro ⟨x, hx, hp⟩
    have hxI : x ∈ interior K := hG hx
    refine ⟨x, hx, ?_⟩
    have hloc : ∀ y ∈ interior K, V x + ⟪p, y - x⟫ ≤ V y := by
      intro y hy
      rw [hVK x (interior_subset hxI), hVK y (interior_subset hy)]
      exact hp y (hKΩ (interior_subset hy))
    have hall := subgradient_le_on_of_isOpen hconv isOpen_interior (subset_univ _) hxI hloc
    exact fun y => hall y (mem_univ _)


/-- The supremum of the actual tangent planes based on a nonempty compact set
is finite everywhere and globally convex. It agrees with the source on that
compact set; its supporting image there identifies DOMAIN-relative supports
only on the compact set's interior. The source needs no regularity or convexity
outside its open working domain. This includes complete spaces of any dimension. -/
theorem exists_compact_convex_extension {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {v : E → ℝ} {Ω K : Set E} (hΩ : IsOpen Ω)
    (hstrict : StrictConvexOn ℝ Ω v) (hv : ContDiffOn ℝ 1 v Ω) (hKc : IsCompact K)
    (hKn : K.Nonempty) (hKΩ : K ⊆ Ω) :
    ∃ V : E → ℝ,
      ConvexOn ℝ univ V ∧
        (∀ x ∈ K, V x = v x) ∧
          (∀ G ⊆ interior K,
            subgradientImage V G = {p | ∃ x ∈ G, ∀ y ∈ Ω, v x + ⟪p, y - x⟫ ≤ v y}) := by
  have hgradCD : ContDiffOn ℝ 0 (gradient v) Ω := contDiffOn_gradient hΩ hv (by norm_num)
  have hgradcont : ContinuousOn (gradient v) Ω := hgradCD.continuousOn
  have hnorm : ContinuousOn (fun z => ‖gradient v z‖) K := (hgradcont.mono hKΩ).norm
  obtain ⟨z₀, hz₀, hmax⟩ := hKc.exists_isMaxOn hKn hnorm
  let R : ℝ := ‖gradient v z₀‖
  let T : Set (E × E) := {q | q.1 ∈ K ∧ q.2 = gradient v q.1}
  have hfamily : ∀ q ∈ T, q.1 ∈ K ∧ ∀ y ∈ Ω, v q.1 + ⟪q.2, y - q.1⟫ ≤ v y := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    rw [hq.2]
    intro y hy
    by_cases hzy : q.1 = y
    · subst y
      simp
    · have hgap :=
        gradient_tangent_gap_pos_of_strictConvexOn hstrict (hKΩ hq.1) hy hzy
          (((hv.differentiableOn one_ne_zero) q.1 (hKΩ hq.1)).differentiableAt
            (hΩ.mem_nhds (hKΩ hq.1)))
      linarith
  have htouch : ∀ x ∈ K, ∃ p, (x, p) ∈ T := fun x hx => ⟨gradient v x, hx, rfl⟩
  have hbound : ∀ q ∈ T, ‖q.2‖ ≤ R := by
    intro q hq
    rw [hq.2]
    exact hmax hq.1
  obtain ⟨V, _L, hconv, _hLip, hVK, himage⟩ :=
    exists_extension_of_support_family hstrict.convexOn hv.continuousOn hKc hKn hKΩ T hfamily
      htouch R (norm_nonneg _) hbound
  exact ⟨V, hconv, hVK, himage⟩

/-- The actual C0 source produces a finite global convex Lipschitz function
agreeing on the compact set. No differentiability, strictness or desired
extension/support/finiteness bound is assumed. This includes zero dimension. -/
theorem exists_lipschitz_compact_convex_extension {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {v : E → ℝ} {Ω K : Set E} (hΩ : IsOpen Ω)
    (hv : ConvexOn ℝ Ω v) (hvc : ContinuousOn v Ω) (hKc : IsCompact K) (hKn : K.Nonempty)
    (hKΩ : K ⊆ Ω) :
    ∃ (V : E → ℝ) (L : NNReal),
      ConvexOn ℝ univ V ∧
        LipschitzWith L V ∧
          (∀ x ∈ K, V x = v x) ∧
            (∀ G ⊆ interior K, subgradientImage V G = subgradientImageOn v Ω G) := by
  obtain ⟨R, hR, hsupp, hbound⟩ := exists_uniform_subgradient_bound_on_compact hΩ hv hvc hKc hKΩ
  let T : Set (E × E) := {q | q.1 ∈ K ∧ ∀ y ∈ Ω, v q.1 + ⟪q.2, y - q.1⟫ ≤ v y}
  apply
    exists_extension_of_support_family hv hvc hKc hKn hKΩ T (fun _ hq => hq) (fun x hx => ?_) R
      hR (fun q hq => hbound q.1 hq.1 q.2 hq.2)
  obtain ⟨p, hp⟩ := hsupp x hx
  exact ⟨p, hx, hp⟩

section CompactMoreau
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
open Filter
open scoped Topology

/-- Genuine local C0 sources produce global C1,1 compact approximations. Agreement
with v is ONLY on K; this is not whole-frontier extension or MA stability. -/
theorem exists_compact_moreau_regularization {v : E → ℝ} {Ω K : Set E} (hΩ : IsOpen Ω)
    (hv : ConvexOn ℝ Ω v) (hvc : ContinuousOn v Ω) (hKc : IsCompact K) (hKn : K.Nonempty)
    (hKΩ : K ⊆ Ω) :
    ∃ (V : E → ℝ) (L : NNReal),
      ConvexOn ℝ univ V ∧
        LipschitzWith L V ∧
          (∀ x ∈ K, V x = v x) ∧
            (∀ ε : ℝ,
                0 < ε →
                  ConvexOn ℝ univ (moreauEnvelope V ε) ∧
                    ContDiff ℝ 1 (moreauEnvelope V ε) ∧
                      LipschitzWith (‖(ε⁻¹ : ℝ)‖₊ * 2) (gradient (moreauEnvelope V ε)) ∧
                        (∀ x ∈ K, |moreauEnvelope V ε x - v x| ≤ ε * (L : ℝ) ^ 2 / 2) ∧
                          (∀ x, ‖(proximalPoint (fun z => ε * V z)) x - x‖ ≤ ε * (L : ℝ))) ∧
              TendstoUniformlyOn (fun ε : ℝ => moreauEnvelope V ε) v (𝓝[>] (0 : ℝ)) K := by
  obtain ⟨V, L, hV, hL, heq, _⟩ :=
    exists_lipschitz_compact_convex_extension hΩ hv hvc hKc hKn hKΩ
  refine ⟨V, L, hV, hL, heq, ?_, ?_⟩
  · intro ε hε
    obtain ⟨hc, hd, _, hl⟩ := moreauEnvelope_regularization V hV hε
    refine ⟨hc, hd, hl, ?_, fun x => (moreauEnvelope_approximation V hV hL hε x).2.2⟩
    intro x hx
    rw [← heq x hx]
    exact (moreauEnvelope_approximation V hV hL hε x).2.1
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have hh :=
      (Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_moreauEnvelope V hV hL)) δ hδ
    filter_upwards [hh] with ε hε x hx
    rw [← heq x hx]
    exact hε x (mem_univ x)

end CompactMoreau

/-- A genuine line crossing forces an ambient convex sublevel to remain in K.
No coercivity, compact sublevel, extension or image identity is assumed. -/
private theorem sublevel_subset_of_frontier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → ℝ} (hV : ConvexOn ℝ univ V) {K : Set E} (hK : IsClosed K) {m : E}
    (hm : m ∈ interior K) {r : ℝ} (hVm : V m < r) (hfront : ∀ z ∈ frontier K, r ≤ V z) :
    {y | V y ≤ r} ⊆ K := by
  intro y hy
  by_contra hyK
  let F : ℝ → E := fun t => AffineMap.lineMap m y t
  have hF : Continuous F := by dsimp [F]; fun_prop
  let S : Set ℝ := Icc 0 1 ∩ F ⁻¹' K
  have hS : IsCompact S := isCompact_Icc.inter_right (hK.preimage hF)
  have h0 : (0 : ℝ) ∈ S := by
    simp only [S, mem_inter_iff, mem_Icc, mem_preimage, F, AffineMap.lineMap_apply_zero]
    exact ⟨⟨le_rfl, zero_le_one⟩, interior_subset hm⟩
  obtain ⟨t, htS, hmax⟩ := hS.exists_isMaxOn ⟨0, h0⟩ continuous_id.continuousOn
  have ht0 : 0 ≤ t := htS.1.1
  have ht1 : t < 1 := by
    refine lt_of_le_of_ne htS.1.2 ?_
    intro ht
    have : y ∈ K := by simpa [F, ht] using htS.2
    exact hyK this
  have hnotint : F t ∉ interior K := by
    intro hi
    have he₁ : ∀ᶠ s in 𝓝 t, F s ∈ interior K := hF.continuousAt (isOpen_interior.mem_nhds hi)
    have he₂ : ∀ᶠ s in 𝓝 t, s < 1 := eventually_lt_nhds ht1
    have hev : ∀ᶠ s in 𝓝 t, F s ∈ interior K ∧ s < 1 := he₁.and he₂
    obtain ⟨s, hts, hs⟩ := hev.exists_gt
    have hsS : s ∈ S := ⟨⟨ht0.trans hts.le, hs.2.le⟩, interior_subset (s := K) hs.1⟩
    have hst : s ≤ t := hmax hsS
    exact (not_le_of_gt hts) hst
  have htf : F t ∈ frontier K := ⟨subset_closure htS.2, hnotint⟩
  have hc :=
    hV.2 (mem_univ m) (mem_univ y) (sub_nonneg.mpr ht1.le) ht0 (show 1 - t + t = 1 by ring)
  have hc' : V (F t) ≤ (1 - t) * V m + t * V y := by
    simpa only [F, AffineMap.lineMap_apply_module, smul_eq_mul] using hc
  have hf := hfront (F t) htf
  have hcoef : 0 < 1 - t := sub_pos.mpr ht1
  have hmul := mul_le_mul_of_nonneg_left hy ht0
  have hstrict := mul_lt_mul_of_pos_left hVm hcoef
  nlinarith

/-- Local zero-boundary C0 convex data genuinely generate a finite GLOBAL
patch with the FULL ambient weak and strict sublevel identities. -/
theorem exists_negative_sublevel_patch {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) (hu : ConvexOn ℝ (closure Ω) u)
    (hC : ContinuousOn u (closure Ω)) (hz : ∀ z ∈ frontier Ω, u z = 0) {r : ℝ} (hr : r < 0)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) (hxr : u x₀ < r) :
    let K := {x ∈ closure Ω | u x ≤ r}
    IsCompact K ∧
      K.Nonempty ∧
        K ⊆ Ω ∧
          ∃ (V : E → ℝ) (L : NNReal),
            ConvexOn ℝ univ V ∧
              LipschitzWith L V ∧
                (∀ x ∈ K, V x = u x) ∧
                  {x | V x ≤ r} = K ∧
                    {x | V x < r} = {x ∈ Ω | u x < r} ∧
                      (∀ G ⊆ {x ∈ Ω | u x < r},
                        subgradientImage V G = subgradientImageOn u Ω G) := by
  let K : Set E := {x ∈ closure Ω | u x ≤ r}
  have hKclosed : IsClosed K := hC.preimage_isClosed_of_isClosed isClosed_closure isClosed_Iic
  have hKcomp : IsCompact K :=
    hb.isCompact_closure.of_isClosed_subset hKclosed (fun _ hx ↦ hx.1)
  have hKΩ : K ⊆ Ω := by
    intro x hx
    by_contra hn
    have hxf : x ∈ frontier Ω := ⟨hx.1, by simpa [hΩ.interior_eq] using hn⟩
    have := hz x hxf
    have hle : u x ≤ r := hx.2
    linarith
  have hstrict (x : E) (hx : x ∈ Ω) (hux : u x < r) : x ∈ interior K := by
    have hnhds : closure Ω ∈ 𝓝 x := mem_of_superset (hΩ.mem_nhds hx) subset_closure
    have hc : ContinuousAt u x := (hC x (subset_closure hx)).continuousAt hnhds
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hΩ.mem_nhds hx, hc (eventually_lt_nhds hux)] with y hy huy
    exact ⟨subset_closure hy, huy.le⟩
  have hxK : x₀ ∈ K := ⟨subset_closure hx₀, hxr.le⟩
  have hlevel : ∀ z ∈ frontier K, u z = r := by
    intro z hzK
    have hzmem : z ∈ K := hKclosed.closure_subset hzK.1
    refine le_antisymm hzmem.2 ?_
    by_contra hlt
    exact hzK.2 (hstrict z (hKΩ hzmem) (lt_of_not_ge hlt))
  obtain ⟨V, L, hV, hL, heq, himage⟩ :=
    exists_lipschitz_compact_convex_extension hΩ (hu.subset subset_closure hcΩ)
      (hC.mono subset_closure) hKcomp ⟨x₀, hxK⟩ hKΩ
  have hVx : V x₀ < r := by rw [heq x₀ hxK]; exact hxr
  have hVF : ∀ z ∈ frontier K, r ≤ V z := by
    intro z hzK
    rw [heq z (hKclosed.closure_subset hzK.1), hlevel z hzK]
  have hsub := sublevel_subset_of_frontier hV hKclosed (hstrict x₀ hx₀ hxr) hVx hVF
  have hweak : {x | V x ≤ r} = K := by
    apply Subset.antisymm hsub
    intro x hx
    change V x ≤ r
    rw [heq x hx]
    exact hx.2
  refine ⟨hKcomp, ⟨x₀, hxK⟩, hKΩ, V, L, hV, hL, heq, hweak, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      change V x < r at hx
      have hxK' : x ∈ K := hsub (show V x ≤ r from hx.le)
      exact ⟨hKΩ hxK', by rwa [heq x hxK'] at hx⟩
    · rintro ⟨hx, hux⟩
      change V x < r
      rw [heq x ⟨subset_closure hx, hux.le⟩]
      exact hux
  · intro G hG
    apply himage G
    intro x hx
    exact hstrict x (hG hx).1 (hG hx).2


end FunctionalInequalities.Analysis
