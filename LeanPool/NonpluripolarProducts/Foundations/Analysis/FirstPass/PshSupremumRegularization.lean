/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.DiscPshSupremum
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocallyUniformUpperBounds
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.UscSupremumRecovery

/-!
# Regularized suprema of locally uniformly bounded PSH families

This file combines the topological recovery sequence for a regularized
supremum with the moving-center Fatou theorem.  A finite prefix of the
recovery sequence is discarded so that all moving affine discs remain in the
open domain.  The remaining centers, together with their limit, form a
compact set; its product with the compact complex parameter disc supplies a
single upper bound for the whole family.
-/

@[expose] public section

open Filter InnerProductSpace Metric Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
/-- Local uniform boundedness on an open set prevents the regularized
pointwise supremum from taking the value `⊤` there. -/
theorem LocallyUniformlyBoundedAbove.uscRegularization_sSup_lt_top
    {F : Set (E → EReal)} {Ω : Set E}
    (hF : LocallyUniformlyBoundedAbove F Ω) (hΩ : IsOpen Ω)
    {x : E} (hx : x ∈ Ω) :
    uscRegularization (sSup F) x < ⊤ := by
  obtain ⟨U, hU, C, hC⟩ := hF x hx
  obtain ⟨V, hV, hVU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hU
  have hVΩ : V ∩ Ω ∈ 𝓝 x := inter_mem hV (hΩ.mem_nhds hx)
  refine (uscRegularization_le_localSup (sSup F) hVΩ).trans_lt ?_
  refine (iSup_le fun y => iSup_le fun hy => ?_).trans_lt (EReal.coe_lt_top C)
  rw [sSup_apply, iSup_subtype]
  exact iSup_le fun f => iSup_le fun hf => hC f hf y ⟨hVU hy, hy.2⟩

omit [NormedSpace ℂ E] in
theorem LocallyUniformlyBoundedAbove.uscRegularization_sSup_ne_top
    {F : Set (E → EReal)} {Ω : Set E}
    (hF : LocallyUniformlyBoundedAbove F Ω) (hΩ : IsOpen Ω)
    {x : E} (hx : x ∈ Ω) :
    uscRegularization (sSup F) x ≠ ⊤ :=
  ne_of_lt (hF.uscRegularization_sSup_lt_top hΩ hx)

/-- If one affine closed disc lies in an open set, then affine closed discs
with the same direction and radius also lie there for all sufficiently close
centers. -/
theorem eventually_affineClosedDisc_subset_of_tendsto
    {Ω : Set E} (hΩ : IsOpen Ω) {x : E} (centers : ℕ → E)
    (hcenters : Tendsto centers atTop (𝓝 x)) (v : E) {r : ℝ}
    (hD : affineClosedDisc x v r ⊆ Ω) :
    ∀ᶠ n : ℕ in atTop, affineClosedDisc (centers n) v r ⊆ Ω := by
  let φ : E × ℂ → E := fun p => p.1 + p.2 • v
  have hφ : Continuous φ := by
    dsimp [φ]
    fun_prop
  have hlocal : ∀ z ∈ closedBall (0 : ℂ) r,
      ∀ᶠ p : E × ℂ in 𝓝 (x, z), φ p ∈ Ω := by
    intro z hz
    exact hφ.continuousAt (hΩ.mem_nhds (hD ⟨z, hz, rfl⟩))
  have hnear : ∀ᶠ c : E in 𝓝 x,
      ∀ z ∈ closedBall (0 : ℂ) r, φ (c, z) ∈ Ω :=
    (isCompact_closedBall (0 : ℂ) r).eventually_forall_of_forall_eventually hlocal
  filter_upwards [hcenters.eventually hnear] with c hc
  rintro y ⟨z, hz, rfl⟩
  exact hc z hz

/-- A convergent sequence of centers whose fixed-radius discs lie in `Ω`
admits one real upper bound for every member of a locally uniformly bounded
family on every one of those discs. -/
theorem LocallyUniformlyBoundedAbove.exists_uniform_upper_bound_on_moving_discs
    {F : Set (E → EReal)} {Ω : Set E}
    (hF : LocallyUniformlyBoundedAbove F Ω) {x : E}
    (centers : ℕ → E) (hcenters : Tendsto centers atTop (𝓝 x))
    (v : E) {r : ℝ} (hD : affineClosedDisc x v r ⊆ Ω)
    (hDn : ∀ n, affineClosedDisc (centers n) v r ⊆ Ω) :
    ∃ C : ℝ, ∀ n, ∀ f ∈ F, ∀ y ∈ affineClosedDisc (centers n) v r,
      f y ≤ (C : EReal) := by
  let S : Set E := insert x (range centers)
  let L : Set (E × ℂ) := S ×ˢ closedBall (0 : ℂ) r
  let φ : E × ℂ → E := fun p => p.1 + p.2 • v
  have hS : IsCompact S := hcenters.isCompact_insert_range
  have hL : IsCompact L := hS.prod (isCompact_closedBall (0 : ℂ) r)
  have hφ : ContinuousOn φ L := by
    apply Continuous.continuousOn
    dsimp [φ]
    fun_prop
  have hφΩ : MapsTo φ L Ω := by
    rintro ⟨c, z⟩ ⟨hc, hz⟩
    rcases hc with rfl | ⟨n, rfl⟩
    · exact hD ⟨z, hz, rfl⟩
    · exact hDn n ⟨z, hz, rfl⟩
  obtain ⟨C, hC⟩ := hF.exists_uniform_upper_bound_on_compact_image
    hL hφ hφΩ
  refine ⟨C, ?_⟩
  intro n f hf y hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact hC f hf (centers n, z) ⟨Or.inr ⟨n, rfl⟩, hz⟩

/-- The upper-semicontinuous regularization of a locally uniformly bounded
family of germwise PSH functions is again germwise PSH on an open domain. -/
theorem plurisubharmonicOn_uscRegularization_sSup
    {F : Set (E → EReal)} {Ω : Set E} (hΩ : IsOpen Ω)
    (_hne : F.Nonempty)
    (hpsh : ∀ f ∈ F, PlurisubharmonicOn f Ω)
    (hF : LocallyUniformlyBoundedAbove F Ω) :
    PlurisubharmonicOn (uscRegularization (sSup F)) Ω := by
  let w : E → EReal := uscRegularization (sSup F)
  have hwusc : UpperSemicontinuous w := upperSemicontinuous_uscRegularization (sSup F)
  have hwtop : ∀ x ∈ Ω, w x ≠ ⊤ := fun x hx =>
    hF.uscRegularization_sSup_ne_top hΩ hx
  have hwdisc : DiscPshOn w Ω := by
    refine ⟨hwtop, hwusc.upperSemicontinuousOn Ω, ?_⟩
    intro x v r hr hD C hC
    by_cases hxbot : w x = ⊥
    · have hpos : 0 < ENNReal.ofReal (2 * Real.pi) :=
        ENNReal.ofReal_pos.mpr Real.two_pi_pos
      rw [hxbot]
      rw [EReal.coe_sub_bot, EReal.toENNReal_top]
      rw [ENNReal.mul_top hpos.ne']
      exact le_top
    let a : ℝ := (w x).toReal
    have hxa : w x = (a : EReal) :=
      (EReal.coe_toReal (hwtop x (hD (center_mem_affineClosedDisc x v hr.le))) hxbot).symm
    obtain ⟨rawCenters, rawPotential, hrawCenters, hrawF, hrawValues⟩ :=
      exists_sequences_tendsto_uscRegularization_sSup_eq_coe hxa
    have hevent : ∀ᶠ n : ℕ in atTop,
        affineClosedDisc (rawCenters n) v r ⊆ Ω :=
      eventually_affineClosedDisc_subset_of_tendsto hΩ rawCenters hrawCenters v hD
    obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
    let centers : ℕ → E := fun n => rawCenters (n + N)
    let potential : ℕ → E → EReal := fun n => rawPotential (n + N)
    have hcenters : Tendsto centers atTop (𝓝 x) := by
      exact (tendsto_add_atTop_iff_nat N).mpr hrawCenters
    have hpotentialF : ∀ n, potential n ∈ F := fun n => hrawF (n + N)
    have hdisc : ∀ n, affineClosedDisc (centers n) v r ⊆ Ω := by
      intro n
      exact hN (n + N) (by omega)
    have hcenter : Tendsto (fun n => potential n (centers n)) atTop (𝓝 (w x)) := by
      simpa [potential, centers, hxa] using
        ((tendsto_add_atTop_iff_nat N).mpr hrawValues)
    obtain ⟨C₀, hC₀⟩ :=
      hF.exists_uniform_upper_bound_on_moving_discs centers hcenters v hD hdisc
    let B : ℝ := max C C₀
    have hCB : C ≤ B := le_max_left _ _
    have hpotentialB : ∀ n, ∀ y ∈ affineClosedDisc (centers n) v r,
        potential n y ≤ (B : EReal) := by
      intro n y hy
      exact (hC₀ n (potential n) (hpotentialF n) y hy).trans <|
        EReal.coe_le_coe_iff.mpr (le_max_right _ _)
    have hdiscPsh : ∀ n, DiscPshOn (potential n) Ω := fun n =>
      SGPT.Foundations.Analysis.PlurisubharmonicOn.discPshOn
        (hpsh (potential n) (hpotentialF n))
    have hboundary : ∀ t : ℝ,
        limsup (fun n => potential n
          (centers n + circleMap 0 r t • v)) atTop ≤
          w (x + circleMap 0 r t • v) := by
      intro t
      let zseq : ℕ → E := fun n => centers n + circleMap 0 r t • v
      let z : E := x + circleMap 0 r t • v
      have hzseq : Tendsto zseq atTop (𝓝 z) := by
        exact hcenters.add tendsto_const_nhds
      have hle : ∀ n, potential n (zseq n) ≤ w (zseq n) := fun n =>
        (le_sSup (hpotentialF n) (zseq n)).trans
          (le_uscRegularization (sSup F) (zseq n))
      have hseqB : ∀ n, potential n (zseq n) ≤ (B : EReal) := fun n =>
        hpotentialB n (zseq n)
          (circle_mem_affineClosedDisc (centers n) v hr.le t)
      apply (limsup_le_iff (u := fun n => potential n (zseq n))
        (f := atTop) (x := w z)
        (isCoboundedUnder_le_of_le atTop fun _ => bot_le)
        (isBoundedUnder_of_eventually_le (Eventually.of_forall hseqB))).2
      intro b hwb
      filter_upwards [hzseq.eventually (hwusc z b hwb)] with n hn
      exact (hle n).trans_lt hn
    have hFatou : circleDeficit w x v r B ≤
        ENNReal.ofReal (2 * Real.pi) * ((B : EReal) - w x).toENNReal :=
      circleSubmean_of_moving_discPsh hdiscPsh x centers v hr hdisc B
        hpotentialB hcenter hboundary
    have hshift : 0 ≤ B - C := sub_nonneg.mpr hCB
    apply (discSubmean_add_bound_iff x v hr.le C (B - C) hshift hC).mp
    convert hFatou using 1
    · dsimp [B]
      ring_nf
    · rw [show C + (B - C) = B by linarith]
  exact hwdisc.plurisubharmonicOn hΩ

end

end SGPT.Foundations.Analysis.FirstPass
