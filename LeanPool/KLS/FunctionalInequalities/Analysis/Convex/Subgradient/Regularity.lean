/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Existence
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Differentiability and continuous selections from unique supports

Supporting convex infrastructure for Letwin arXiv:2607.24164v1
Theorem 1.2 and Lemma 2.2. Mathematical scopes and source attributions
are retained in the individual declarations.
-/

@[expose] public section

section
open Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis
section ConvexC1

/-- **A differentiable convex function on a finite-dimensional space is `C¹`**: convexity makes the
derivative map continuous. -/
theorem contDiff_one_of_convexOn_of_differentiable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hdiff : Differentiable ℝ u) :
    ContDiff ℝ 1 u := by
  have hline (x w : E) :
      HasDerivAt (fun t : ℝ => u (x + t • w)) (fderiv ℝ u x w) 0 := by
    have hp : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
    have hu : HasFDerivAt u (fderiv ℝ u x) (x + (0 : ℝ) • w) := by
      simpa only [zero_smul, add_zero] using (hdiff x).hasFDerivAt
    exact hu.comp_hasDerivAt 0 hp
  -- The supporting hyperplane inequality follows from convexity on each line.
  have hsupport (x y : E) :
      fderiv ℝ u x (y - x) ≤ u y - u x := by
    have hc : ConvexOn ℝ Set.univ
        (fun t : ℝ => u (x + t • (y - x))) := by
      simpa only [Set.preimage_univ, Function.comp_def,
        AffineMap.lineMap_apply_module', add_comm] using
        hconv.comp_affineMap (AffineMap.lineMap x y)
    simpa only [slope_def_field, zero_smul, add_zero, one_smul,
      add_sub_cancel, sub_zero, div_one] using
      hc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
        zero_lt_one (hline x (y - x))
  have hbound (x w : E) (t : ℝ) (ht : 0 < t) :
      fderiv ℝ u x w ≤ (u (x + t • w) - u x) / t := by
    apply (le_div_iff₀ ht).2
    have h := hsupport x (x + t • w)
    simpa only [add_sub_cancel_left, map_smul, smul_eq_mul, mul_comm] using h
  -- For fixed direction, positive difference quotients give continuous upper bounds.
  have hupper (w x : E) (a : ℝ) (ha : fderiv ℝ u x w < a) :
      ∀ᶠ z in nhds x, fderiv ℝ u z w < a := by
    have hlim :
        Filter.Tendsto (fun t : ℝ => (u (x + t • w) - u x) / t)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (fderiv ℝ u x w)) := by
      simpa only [zero_add, zero_smul, add_zero, smul_eq_mul,
        div_eq_mul_inv, mul_comm] using
        (hline x w).tendsto_slope_zero.mono_left
          (nhdsGT_le_nhdsNE (0 : ℝ))
    have hev := (hlim.eventually_lt_const ha).and
      (self_mem_nhdsWithin :
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t)
    obtain ⟨t, ht, htpos⟩ := hev.exists
    have hc : Continuous (fun z : E => (u (z + t • w) - u z) / t) :=
      ((hdiff.continuous.comp (continuous_id.add continuous_const)).sub
        hdiff.continuous).div_const t
    exact (hc.continuousAt.eventually_lt continuousAt_const ht).mono
      (fun z hz => lt_of_le_of_lt (hbound z w t htpos) hz)
  -- Applying the upper bound to the negative direction also gives a lower bound.
  have heval (w : E) : Continuous (fun x => fderiv ℝ u x w) := by
    apply continuous_iff_continuousAt.2
    intro x
    apply tendsto_order.2
    constructor
    · intro a ha
      have hn : fderiv ℝ u x (-w) < -a := by
        simpa only [map_neg] using neg_lt_neg ha
      exact (hupper (-w) x (-a) hn).mono fun z hz => by
        simpa only [map_neg, neg_lt_neg_iff] using hz
    · intro a ha
      exact hupper w x a ha
  -- In finite dimension, continuity on a basis gives continuity in operator norm.
  apply contDiff_one_iff_fderiv.2
  refine ⟨hdiff, ?_⟩
  let b := Module.finBasis ℝ E
  let L : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ) :=
    (b.constr ℝ).trans LinearMap.toContinuousLinearMap
  have hL : Continuous L := L.toLinearMap.continuous_of_finiteDimensional
  have heq (x : E) :
      L (fun i => fderiv ℝ u x (b i)) = fderiv ℝ u x := by
    apply ContinuousLinearMap.ext
    intro w
    exact congrArg (fun f : E →ₗ[ℝ] ℝ => f w)
      (b.constr_self ℝ (fderiv ℝ u x).toLinearMap)
  exact (hL.comp (continuous_pi (fun i => heval (b i)))).congr heq

end ConvexC1

end FunctionalInequalities.Analysis
section UniqueSubgradientDifferentiable

open scoped RealInnerProductSpace

/-! A unique subgradient gives differentiability. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma convex_line_slope_mono [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (x v : E) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (u (x + a • v) - u x) / a ≤ (u (x + b • v) - u x) / b := by
  have hline : ConvexOn ℝ Set.univ (fun t : ℝ => u (t • v + x)) := by
    simpa only [Set.preimage_univ, Function.comp_def,
      AffineMap.lineMap_apply_module', add_sub_cancel_left] using
      hconv.comp_affineMap (AffineMap.lineMap x (x + v))
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h :=
    hline.slope_mono (show (0 : ℝ) ∈ Set.univ by simp)
      (show a ∈ Set.univ \ {0} by simp [ne_of_gt ha])
      (show b ∈ Set.univ \ {0} by simp [ne_of_gt hb]) hab
  simpa only [slope_def_field, zero_smul, add_zero, sub_zero, add_comm] using h

section FiniteDimensional

variable [FiniteDimensional ℝ E]

private lemma hasFDerivAt_of_convexOn_of_unique_subgradient {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (x g : E)
    (hg : ∀ y, u x + ⟪g, y - x⟫ ≤ u y)
    (huniq : ∀ q, (∀ y, u x + ⟪q, y - x⟫ ≤ u y) → q = g) :
    HasFDerivAt u ((InnerProductSpace.toDual ℝ E) g) x := by
  classical
  have hu : Continuous u :=
    continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  let R : E → ℝ := fun h => u (x + h) - u x - ⟪g, h⟫
  have hR_nonneg : ∀ h, 0 ≤ R h := by
    intro h
    have hh := hg (x + h)
    have hh' : u x + ⟪g, h⟫ ≤ u (x + h) := by
      simpa only [add_sub_cancel_left] using hh
    dsimp [R]
    linarith
  have hF_cont (t : ℝ) :
      Continuous (fun v : E =>
        (u (x + t • v) - u x) / t - ⟪g, v⟫) := by
    have harg : Continuous (fun v : E => x + t • v) :=
      continuous_const.add (continuous_const.smul continuous_id)
    have hinner : Continuous (fun v : E => ⟪g, v⟫) :=
      continuous_const.inner continuous_id
    exact (((hu.comp harg).sub continuous_const).div_const t).sub hinner
  have hlittle :
      R =o[nhds 0] fun h : E => h := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    by_cases hS : (Metric.sphere (0 : E) 1).Nonempty
    · let S : Set E := Metric.sphere (0 : E) 1
      have hSc : IsCompact S := by
        exact isCompact_sphere (0 : E) 1
      let I := {v : E // v ∈ S}
      let H : ∀ v : I, ∃ q : E,
          (∀ y, u x + ⟪q, y - x⟫ ≤ u y) ∧
            ∀ ε > 0, ∃ t > 0,
              (u (x + t • (v : E)) - u x) / t ≤ ⟪q, (v : E)⟫ + ε :=
        fun v => exists_subgradient_slope_le_inner_add hconv x (v : E)
      let T : I → ℝ := fun v =>
        Classical.choose ((H v).choose_spec.2 (ε / 2) (by linarith))
      have hT_pos (v : I) : 0 < T v := by
        exact (Classical.choose_spec
          ((H v).choose_spec.2 (ε / 2) (by linarith))).1
      have hT_bound (v : I) :
          (u (x + T v • (v : E)) - u x) / T v -
              ⟪g, v⟫ ≤ ε / 2 := by
        have hqg : (H v).choose = g :=
          huniq _ (H v).choose_spec.1
        have hchosen :=
          Classical.choose_spec ((H v).choose_spec.2 (ε / 2) (by linarith))
        have hchosen' :
            (u (x + T v • (v : E)) - u x) / T v ≤
              ⟪g, v⟫ + ε / 2 := by
          simpa only [T, hqg] using hchosen.2
        linarith
      let U : I → Set E := fun v =>
        {w | (u (x + T v • w) - u x) / T v - ⟪g, w⟫ < ε}
      have hU_open : ∀ v : I, IsOpen (U v) := by
        intro v
        exact isOpen_Iio.preimage (hF_cont (T v))
      have hU_cover : S ⊆ ⋃ v : I, U v := by
        intro v hv
        let w : I := ⟨v, hv⟩
        have hw : (w : E) ∈ U w := by
          change (u (x + T w • (w : E)) - u x) / T w -
              ⟪g, w⟫ < ε
          exact (hT_bound w).trans_lt (by linarith)
        exact Set.mem_iUnion.2 ⟨w, hw⟩
      obtain ⟨K, hK⟩ := hSc.elim_finite_subcover U hU_open hU_cover
      have hK_nonempty : K.Nonempty := by
        obtain ⟨v, hv⟩ := hS
        have hv' := hK hv
        rcases Set.mem_iUnion.mp hv' with ⟨w, hv'⟩
        rcases Set.mem_iUnion.mp hv' with ⟨hwK, _⟩
        exact ⟨w, hwK⟩
      obtain ⟨v₀, hv₀⟩ := hK_nonempty
      let K' : Finset ℝ := K.image T
      have hK'_nonempty : K'.Nonempty := by
        refine ⟨T v₀, ?_⟩
        exact Finset.mem_image.mpr ⟨v₀, hv₀, rfl⟩
      let δ : ℝ := K'.min' hK'_nonempty
      have hδ : 0 < δ := by
        have hδmem : δ ∈ K' := by
          dsimp [δ]
          exact Finset.min'_mem K' hK'_nonempty
        rcases Finset.mem_image.mp hδmem with ⟨v, _, heq⟩
        rw [← heq]
        exact hT_pos v
      have hδ_le (v : I) (hv : v ∈ K) : δ ≤ T v := by
        have hmem : T v ∈ K' := Finset.mem_image.mpr ⟨v, hv, rfl⟩
        change K'.min' hK'_nonempty ≤ T v
        exact Finset.min'_le K' (T v) hmem
      have hsmall :
          ∀ᶠ h : E in nhds 0, ‖h‖ < δ := by
        exact Metric.eventually_nhds_iff.2 ⟨δ, hδ, by
          intro h hh
          simpa [dist_zero_right] using hh⟩
      filter_upwards [hsmall] with h hh
      by_cases hz : h = 0
      · simp [R, hz]
      · let s : ℝ := ‖h‖
        let w : E := s⁻¹ • h
        have hs : 0 < s := by
          exact norm_pos_iff.mpr hz
        have hw : ‖w‖ = 1 := by
          calc
            ‖w‖ = ‖s⁻¹‖ * ‖h‖ := norm_smul _ _
            _ = s⁻¹ * ‖h‖ := by
              rw [Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
            _ = 1 := inv_mul_cancel₀ (ne_of_gt hs)
        have hwS : w ∈ S := by
          rw [Metric.mem_sphere]
          simpa [dist_zero_right] using hw
        have hwI : ∃ v : I, v ∈ K ∧ (w : E) ∈ U v := by
          have hcover := hK hwS
          rcases Set.mem_iUnion.mp hcover with ⟨v, hcover⟩
          rcases Set.mem_iUnion.mp hcover with ⟨hvK, hwv⟩
          exact ⟨v, hvK, hwv⟩
        obtain ⟨v, hvK, hwv⟩ := hwI
        have hsδ : s < δ := by
          exact hh
        have hst : s ≤ T v := by
          exact hsδ.le.trans (hδ_le v hvK)
        have hmono :
            (u (x + s • w) - u x) / s ≤
              (u (x + T v • w) - u x) / T v := by
          exact convex_line_slope_mono hconv x w hs hst
        have hU := hwv
        change (u (x + T v • w) - u x) / T v -
            ⟪g, w⟫ < ε at hU
        have hmono' :
            u (x + s • w) - u x ≤
              ((u (x + T v • w) - u x) / T v) * s := by
          exact (div_le_iff₀ hs).mp hmono
        have hupper :
            u (x + s • w) - u x - ⟪g, s • w⟫ ≤ ε * s := by
          have hscale : ⟪g, s • w⟫ = s * ⟪g, w⟫ := by
            simp [real_inner_smul_right]
          rw [hscale]
          calc
            u (x + s • w) - u x - s * ⟪g, w⟫ ≤
                ((u (x + T v • w) - u x) / T v) * s -
                  s * ⟪g, w⟫ := by
                    exact sub_le_sub_right hmono' _
            _ = ((u (x + T v • w) - u x) / T v -
                  ⟪g, w⟫) * s := by ring
            _ ≤ ε * s := by
              exact mul_le_mul_of_nonneg_right (by linarith) hs.le
        have heq : s • w = h := by
          dsimp [w, s]
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
        have hnorm : ‖s • w‖ = s := by
          rw [norm_smul, Real.norm_of_nonneg hs.le, hw, mul_one]
        have hupper' :
            R h ≤ ε * ‖h‖ := by
          rw [← heq]
          change u (x + s • w) - u x - ⟪g, s • w⟫ ≤ ε * ‖s • w‖
          rw [hnorm]
          exact hupper
        rw [Real.norm_of_nonneg (hR_nonneg h)]
        exact hupper'
    · have hzero : ∀ v : E, v = 0 := by
        intro v
        by_contra hv
        let w : E := ‖v‖⁻¹ • v
        have hw : ‖w‖ = 1 := by
          calc
            ‖w‖ = ‖‖v‖⁻¹‖ * ‖v‖ := norm_smul _ _
            _ = ‖v‖⁻¹ * ‖v‖ := by
              rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
            _ = 1 := inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr hv))
        exact hS ⟨w, by
          rw [Metric.mem_sphere]
          simpa [dist_zero_right] using hw⟩
      exact Filter.Eventually.of_forall (fun h => by
        simp [R, hzero h])
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa only [InnerProductSpace.toDual_apply_apply, R] using hlittle

/-- **A convex function with a unique subgradient at every point is differentiable** ("singleton
subdifferential ⇒ C¹", differentiability half): on a finite-dimensional
inner product space, if the subgradient inequality `u x + ⟪g, y - x⟫ ≤ u y` (all `y`) is satisfied
by exactly one `g` at every `x`, then `u` is differentiable (with that `g` as gradient; `C¹` then
follows
from `contDiff_one_of_convexOn_of_differentiable`). -/
theorem differentiable_of_convexOn_of_unique_subgradient {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hsub : ∀ x, ∃! g : E, ∀ y, u x + ⟪g, y - x⟫ ≤ u y) :
    Differentiable ℝ u := by
  intro x
  obtain ⟨g, hg, huniq⟩ := hsub x
  exact (hasFDerivAt_of_convexOn_of_unique_subgradient hconv x g hg huniq).differentiableAt

end FiniteDimensional

end InnerProduct

end FunctionalInequalities.Analysis

end UniqueSubgradientDifferentiable
section UniqueSubgradientC1

open scoped RealInnerProductSpace

/-! Unique subgradients everywhere give a `C¹` function. -/

namespace FunctionalInequalities.Analysis

/-- **Singleton subdifferential ⇒ `C¹`**: a
convex function on a finite-dimensional inner product space with exactly one subgradient at every
point is continuously differentiable. -/
theorem contDiff_one_of_convexOn_of_unique_subgradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hsub : ∀ x, ∃! g : E, ∀ y, u x + ⟪g, y - x⟫ ≤ u y) :
    ContDiff ℝ 1 u := by
  exact contDiff_one_of_convexOn_of_differentiable hconv
    (differentiable_of_convexOn_of_unique_subgradient hconv hsub)

end FunctionalInequalities.Analysis

end UniqueSubgradientC1
section StrictConvexGradient

open Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- A differentiable strictly convex function has an injective gradient. This is
an elementary prerequisite for the moment-map inverse in Letwin Lemma 2.2. -/
theorem injective_gradient_of_strictConvexOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u : E → ℝ} (hu : Differentiable ℝ u) (hstrict : StrictConvexOn ℝ univ u) :
    Function.Injective (gradient u) := by
  intro x y hxy
  by_contra hne
  let l : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hinj : Function.Injective l := AffineMap.lineMap_injective ℝ hne
  have hc : StrictConvexOn ℝ univ (u ∘ l) := by
    refine ⟨convex_univ, ?_⟩
    intro r _ s _ hrs a b ha hb hab
    change u (l (a • r + b • s)) < a • u (l r) + b • u (l s)
    rw [Convex.combo_affine_apply hab]
    exact hstrict.2 (mem_univ _) (mem_univ _) (fun he => hrs (hinj he)) ha hb hab
  have hlineConv : StrictConvexOn ℝ univ (fun t : ℝ => u (x + t • (y - x))) := by
    simpa only [Function.comp_def, l, AffineMap.lineMap_apply_module', add_comm] using hc
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => u (x + s • (y - x)))
      (fderiv ℝ u (x + t • (y - x)) (y - x)) t := by
    have hp : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) t := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id t).smul_const (y - x)).const_add x
    exact (hu (x + t • (y - x))).hasFDerivAt.comp_hasDerivAt t hp
  have hfd : fderiv ℝ u x = fderiv ℝ u y := by
    simpa only [toDual_gradient] using
      congrArg (InnerProductSpace.toDual ℝ E) hxy
  have hlt :=
    (hlineConv.lt_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one (hline 0)).trans
      (hlineConv.slope_lt_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one (hline 1))
  have hlt' : fderiv ℝ u x (y - x) < fderiv ℝ u y (y - x) := by
    simpa only [zero_smul, one_smul, add_zero, add_sub_cancel] using hlt
  rw [hfd] at hlt'
  exact (lt_irrefl _) hlt'

end FunctionalInequalities.Analysis

end StrictConvexGradient
namespace FunctionalInequalities.Analysis
open Set Metric Filter
open scoped RealInnerProductSpace Topology

/--
Generic compact-range closed-relation continuity, shared by compact affine-tilt optimizers and local
support selections. -/
theorem continuous_of_compact_closed_relation {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] (R : Set (Y × X)) (hR : IsClosed R) (f : X → Y)
    (hf : ∀ x, (f x, x) ∈ R) (huniq : ∀ x y, (y, x) ∈ R → y = f x) : Continuous f := by
  apply continuous_iff_isClosed.mpr
  intro A hA
  have he : f ⁻¹' A = Prod.snd '' (R ∩ Prod.fst ⁻¹' A) := by
    ext x
    constructor
    · intro hx
      exact ⟨(f x, x), ⟨hf x, hx⟩, rfl⟩
    · rintro ⟨⟨y, z⟩, ⟨hy, hA'⟩, hz⟩
      change z = x at hz
      subst z
      change f x ∈ A
      rw [← huniq x y hy]
      exact hA'
  rw [he]
  exact isClosedMap_snd_of_compactSpace _ (hR.inter (hA.preimage continuous_fst))

/-- Actual continuous variational remainders give a genuine Frechet derivative.
Shared by compact-conjugate values and local convex primal derivatives. -/
theorem hasFDerivAt_of_variational_remainder {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E → ℝ} {g : E → E} {x : E} (hg : ContinuousAt g x)
    (hb :
      ∀ᶠ y in 𝓝 x,
        0 ≤ u y - u x - ⟪g x, y - x⟫ ∧ u y - u x - ⟪g x, y - x⟫ ≤ ⟪y - x, g y - g x⟫) :
    HasFDerivAt u (innerSL ℝ (g x)) x := by
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hn : ContinuousAt (fun y => ‖g y - g x‖) x := (hg.sub continuousAt_const).norm
  have hev : ∀ᶠ y in 𝓝 x, ‖g y - g x‖ < c :=
    hn.eventually_lt continuousAt_const (by simpa using hc)
  filter_upwards [hb, hev] with y hy hgy
  change ‖u y - u x - ⟪g x, y - x⟫‖ ≤ c * ‖y - x‖
  rw [Real.norm_eq_abs, abs_of_nonneg hy.1]
  calc
    _ ≤ ⟪y - x, g y - g x⟫ := hy.2
    _ ≤ ‖y - x‖ * ‖g y - g x‖ := real_inner_le_norm _ _
    _ ≤ c * ‖y - x‖ := by nlinarith [norm_nonneg (y - x)]

/-- Local C0 convexity/actual unique domain supports GENERATE a continuous
actual slope selection; compact local bounds/closed graph are not inputs. -/
theorem exists_continuous_supports {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u)
    (hC : ContinuousOn u Ω)
    (hs :
      ∀ x ∈ Ω,
        ∃ p : E,
          (∀ y ∈ Ω, u x + ⟪p, y - x⟫ ≤ u y) ∧
            ∀ q : E, (∀ y ∈ Ω, u x + ⟪q, y - x⟫ ≤ u y) → q = p) :
    ∃ g : E → E,
      ContinuousOn g Ω ∧
        ∀ x ∈ Ω,
          (∀ y ∈ Ω, u x + ⟪g x, y - x⟫ ≤ u y) ∧
            ∀ q : E, (∀ y ∈ Ω, u x + ⟪q, y - x⟫ ≤ u y) → q = g x := by
  classical
  let g : E → E := fun x => if hx : x ∈ Ω then (hs x hx).choose else 0
  have hspec (x : E) (hx : x ∈ Ω) :
    (∀ y ∈ Ω, u x + ⟪g x, y - x⟫ ≤ u y) ∧
      ∀ q : E, (∀ y ∈ Ω, u x + ⟪q, y - x⟫ ≤ u y) → q = g x := by
    simpa only [g, dite_eq_left hx] using (hs x hx).choose_spec
  refine ⟨g, ?_, hspec⟩
  apply continuousOn_of_forall_continuousAt
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx)
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hKΩ : closedBall x r ⊆ Ω := by
    intro y hy
    apply hball
    exact mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (by dsimp [r]; linarith))
  let T : Set E := ball x r
  have hTΩ : T ⊆ Ω := ball_subset_closedBall.trans hKΩ
  obtain ⟨R, _hR, _hsex, hcap⟩ :=
    exists_uniform_subgradient_bound_on_compact hΩ hu hC (isCompact_closedBall x r) hKΩ
  let B : Set E := closedBall 0 R
  have hB : IsCompact B := isCompact_closedBall 0 R
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  have hbound (y : E) (hy : y ∈ T) : g y ∈ B := by
    have hh := hcap y (ball_subset_closedBall hy) (g y) (hspec y (hTΩ hy)).1
    simpa only [B, mem_closedBall, dist_zero_right] using hh
  let f : T → B := fun y => ⟨g y.val, hbound y.val y.property⟩
  let Rel : Set (B × T) := {q | ∀ y ∈ T, u q.2.val + ⟪q.1.val, y - q.2.val⟫ ≤ u y}
  have hGraph0 : IsClosed {q : T × E | ∀ y ∈ T, u q.1.val + ⟪q.2, y - q.1.val⟫ ≤ u y} :=
    isClosed_subgradient_graphOn (hC.mono hTΩ)
  have hGraph : IsClosed Rel :=
    hGraph0.preimage (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
  have hf (y : T) : (f y, y) ∈ Rel := by
    intro z hz
    exact (hspec y.val (hTΩ y.property)).1 z (hTΩ hz)
  have huniq (y : T) (p : B) (hp : (p, y) ∈ Rel) : p = f y := by
    apply Subtype.ext
    have hpΩ : ∀ z ∈ Ω, u y.val + ⟪p.val, z - y.val⟫ ≤ u z :=
      subgradient_le_on_of_isOpen hu isOpen_ball hTΩ y.property hp
    exact (hspec y.val (hTΩ y.property)).2 p.val hpΩ
  have hfC : Continuous f := continuous_of_compact_closed_relation Rel hGraph f hf huniq
  have hgT : ContinuousOn g T :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hfC)
  exact hgT.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))

/-- Actual local convex C0/unique domain supports produce genuine local C1,
actual Frechet derivatives and actual gradient values, no AE shortcut. -/
theorem exists_c1_of_unique_supports {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u)
    (hC : ContinuousOn u Ω)
    (hs :
      ∀ x ∈ Ω,
        ∃ p : E,
          (∀ y ∈ Ω, u x + ⟪p, y - x⟫ ≤ u y) ∧
            ∀ q : E, (∀ y ∈ Ω, u x + ⟪q, y - x⟫ ≤ u y) → q = p) :
    ∃ g : E → E,
      ContinuousOn g Ω ∧
        (∀ x ∈ Ω, HasFDerivAt u (innerSL ℝ (g x)) x) ∧
          ContDiffOn ℝ 1 u Ω ∧
            (∀ x ∈ Ω, gradient u x = g x) ∧
              ∀ x ∈ Ω,
                (∀ y ∈ Ω, u x + ⟪g x, y - x⟫ ≤ u y) ∧
                  ∀ q : E, (∀ y ∈ Ω, u x + ⟪q, y - x⟫ ≤ u y) → q = g x := by
  obtain ⟨g, hg, hsp⟩ := exists_continuous_supports hΩ hu hC hs
  have hd (x : E) (hx : x ∈ Ω) : HasFDerivAt u (innerSL ℝ (g x)) x := by
    apply hasFDerivAt_of_variational_remainder (hg.continuousAt (hΩ.mem_nhds hx))
    filter_upwards [hΩ.mem_nhds hx] with y hy
    have hp := (hsp x hx).1 y hy
    have hq := (hsp y hy).1 x hx
    simp only [inner_sub_left, inner_sub_right] at hp hq ⊢
    simp only [real_inner_comm] at hp hq ⊢
    constructor <;> linarith
  have hdf : ContinuousOn (fderiv ℝ u) Ω := by
    have hc : ContinuousOn (fun x => innerSL ℝ (g x)) Ω :=
      (innerSL ℝ).continuous.comp_continuousOn hg
    apply hc.congr
    intro x hx
    exact (hd x hx).fderiv
  have hC1 : ContDiffOn ℝ 1 u Ω := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hΩ).2
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact contDiffOn_zero.mpr hdf
  exact
    ⟨g, hg, hd, hC1, fun x hx => (hasGradientAt_iff_hasFDerivAt.mpr (hd x hx)).gradient, hsp⟩

end FunctionalInequalities.Analysis
