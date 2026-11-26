/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar
public import LeanPool.GraphMinor.Surface.PasteDisc
public import LeanPool.GraphMinor.Surface.DiscGrow
public import LeanPool.GraphMinor.Surface.DiscMerge
public import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# A thin disc along a line of the boundary

Let `K` be a line in the boundary of a surface, and let `Z` be a closed set that meets `K` at most
in its ends. We find a closed disc that
has `K` in its boundary, meets the boundary of the surface exactly in `K`, and meets `Z` at most in
the ends of `K` (`exists_wedge`). The
disc is a wedge in a collar of the cuff of `K`: paste a disc on the cuff, and use the collar of that
disc from `exists_disc_collar`. The
height of the wedge above a point of `K` is less than the distance to `Z`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

universe u

/-- An injective continuous map on a closed disc carries it to a closed disc. -/
theorem isClosedDisc_image_injOn {A T : Type*} [TopologicalSpace A] [Nonempty A] [TopologicalSpace
  T] [T2Space T] {Δ : Set A} (hΔ : IsClosedDisc Δ) (hc : IsCompact Δ)
    {f : A → T} (hf : ContinuousOn f Δ) (hi : InjOn f Δ) : IsClosedDisc (f '' Δ) ∧ discBd (f '' Δ)
      = f '' discBd Δ := by
  have hl : LeftInvOn (Function.invFunOn f Δ) f Δ := hi.leftInvOn_invFunOn
  refine hΔ.image hf ?_ hl
  have hcomp : CompactSpace Δ := isCompact_iff_compactSpace.mp hc
  let g : Δ → f '' Δ := fun x => ⟨f x, x.1, x.2, rfl⟩
  have hg : Continuous g := (continuousOn_iff_continuous_domRestrict.mp hf).subtype_mk _
  have hgb : Function.Bijective g := by
    constructor
    · intro x y h
      exact Subtype.ext (hi x.2 y.2 (congrArg Subtype.val h))
    · rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let e : Δ ≃ₜ f '' Δ := hg.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hgb)
  have hr : (f '' Δ).domRestrict (Function.invFunOn f Δ) = fun y => (e.symm y).1 := by
    funext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [e.symm_apply_apply]
    exact hl x.2
  rw [continuousOn_iff_continuous_domRestrict, hr]
  exact continuous_subtype_val.comp e.symm.continuous

/-- The first coordinate of the wedge. -/
noncomputable def wedgeT (z : ℂ) : unitInterval := projIcc 0 1 zero_le_one ((z.re + 1) / 2)

/-- The height of the wedge at `z`, as a fraction. -/
noncomputable def wedgeTau (z : ℂ) : ℝ := (z.im + √(1 - z.re ^ 2)) / (2 * √(1 - z.re ^ 2))

theorem wedgeTau_mem {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) : 0 ≤ wedgeTau z ∧ wedgeTau z ≤ 1 := by
  have h1 : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have h2 : ‖z‖ ≤ 1 := by simpa using hz
    have h3 := Complex.sq_norm z
    rw [Complex.normSq_apply] at h3
    nlinarith [norm_nonneg z]
  have hw : |z.im| ≤ √(1 - z.re ^ 2) := by
    apply Real.abs_le_sqrt
    linarith
  obtain ⟨h4, h5⟩ := abs_le.mp hw
  rcases (Real.sqrt_nonneg (1 - z.re ^ 2)).eq_or_lt with h | h
  · rw [wedgeTau, ← h]
    simp
  · rw [wedgeTau]
    constructor
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by linarith)]
      linarith

theorem re_of_wedgeT {z z' : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) (hz' : z' ∈ closedBall (0 : ℂ) 1)
  (h : wedgeT z = wedgeT z') : z.re = z'.re := by
  have hb : ∀ {w : ℂ}, w ∈ closedBall (0 : ℂ) 1 → (w.re + 1) / 2 ∈ Icc (0 : ℝ) 1 := fun {w} hw => by
    have h2 : ‖w‖ ≤ 1 := by simpa using hw
    have h3 := abs_le.mp ((Complex.abs_re_le_norm w).trans h2)
    constructor <;> linarith [h3.1, h3.2]
  have h1 := congrArg Subtype.val h
  simp only [wedgeT, projIcc_of_mem _ (hb hz), projIcc_of_mem _ (hb hz')] at h1
  linarith

theorem continuous_wedgeT : Continuous wedgeT := continuous_projIcc.comp (by fun_prop)

theorem wedgeT_coe {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) : (wedgeT z : ℝ) = (z.re + 1) / 2 := by
  have h2 : ‖z‖ ≤ 1 := by simpa using hz
  have h3 := abs_le.mp ((Complex.abs_re_le_norm z).trans h2)
  rw [wedgeT, projIcc_of_mem _ (show (z.re + 1) / 2 ∈ Icc (0 : ℝ) 1 by constructor
    <;> linarith [h3.1, h3.2])]

/-- The height function of a wedge is continuous on the unit disc, where `ρ` vanishes at the two
ends. -/
theorem continuousOn_wedge {ρ : unitInterval → ℝ} (hρ : Continuous ρ) (h0 : ρ 0 = 0) (h1 : ρ 1 = 0)
  (hnn : ∀ t, 0 ≤ ρ t) :
    ContinuousOn (fun z => ρ (wedgeT z) * wedgeTau z) (closedBall (0 : ℂ) 1) := by
  have htc := continuous_wedgeT
  intro z hz
  by_cases hw : √(1 - z.re ^ 2) = 0
  · have hval : ρ (wedgeT z) = 0 := by
      have h2 : 1 - z.re ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp hw
      have h3 : ‖z‖ ≤ 1 := by simpa using hz
      have h4 := abs_le.mp ((Complex.abs_re_le_norm z).trans h3)
      have h5 : z.re = 1 ∨ z.re = -1 := by
        have h6 : (z.re - 1) * (z.re + 1) = 0 := by nlinarith [h4.1, h4.2]
        rcases mul_eq_zero.mp h6 with h7 | h7
        · exact .inl (by linarith)
        · exact .inr (by linarith)
      rcases h5 with h5 | h5
      · have : wedgeT z = 1 := by
          simp only [wedgeT, h5]
          norm_num
        rw [this, h1]
      · have : wedgeT z = 0 := by
          simp only [wedgeT, h5]
          norm_num
        rw [this, h0]
    have ht : Tendsto (fun z => ρ (wedgeT z)) (𝓝[closedBall (0 : ℂ) 1] z) (𝓝 0) := by
      rw [← hval]
      exact ((hρ.comp htc).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    change Tendsto _ _ _
    simp only [hval, zero_mul]
    refine squeeze_zero' ?_ ?_ ht
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact mul_nonneg (hnn _) (wedgeTau_mem hy).1
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact mul_le_of_le_one_right (hnn _) (wedgeTau_mem hy).2
  · have h2 : ContinuousAt wedgeTau z := by
      unfold wedgeTau
      refine ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using hw)
    exact (((hρ.comp htc).continuousAt).mul h2).continuousWithinAt

private theorem exists_boundary_arc_strip {Y : Type} [TopologicalSpace Y]
    (hY : IsSurface Y) {a : unitInterval → Y} (ha : IsArcMap a) (hKb : range a ⊆ bd Y) :
    ∃ E : unitInterval × unitInterval → Y, Continuous E ∧ Function.Injective E ∧
      (∀ t, E (t, 0) = a t) ∧
      ∀ q, 0 < (q.2 : ℝ) → (q.2 : ℝ) < 1 → E q ∉ bd Y := by
  have hC : connectedComponentIn (bd Y) (a 0) ∈ cuffs Y := ⟨a 0, hKb (mem_range_self 0), rfl⟩
  set C := connectedComponentIn (bd Y) (a 0) with hCdef
  have hKC : range a ⊆ C :=
    (isPreconnected_range ha.1).subset_connectedComponentIn (mem_range_self 0) hKb
  obtain ⟨T, tT, ι, Δ, hT, hι, hΔ, hun, hmeet, hbdΔ, hbdT⟩ := paste_disc.{0} Y C hY hC
  have ht2T : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := hT.2.2
  have hint : ∀ x ∈ discBd Δ, IsInteriorPoint x := fun x hx => by
    by_contra hn
    have h1 : x ∈ bd T := hn
    rw [hbdT] at h1
    rw [hbdΔ] at hx
    obtain ⟨y, hy, rfl⟩ := h1
    obtain ⟨y', hy', he⟩ := hx
    exact hy.2 (hι.injective he ▸ hy')
  obtain ⟨Δ', hΔ', hin, -⟩ := exists_disc_around hman hΔ hint isOpen_univ (subset_univ _)
  obtain ⟨p⟩ := hΔ.isOArc_discBd
  obtain ⟨c, c', hcc, hc'c, hmc, hmc', hl, -, hcΔ, hcb, hcp⟩ := exists_disc_collar hΔ hΔ' hin p
  have hιa : ∀ t, ι (a t) ∈ discBd Δ := fun t => hbdΔ ▸ mem_image_of_mem _ (hKC (mem_range_self t))
  let b : unitInterval → Circle := fun t => p.symm ⟨ι (a t), hιa t⟩
  have hbc : Continuous b := p.symm.continuous.comp ((hι.continuous.comp ha.1).subtype_mk _)
  have hpb : ∀ t, c (b t) = ι (a t) := fun t => by
    rw [hcp, p.apply_symm_apply]
  let P := unitInterval × unitInterval
  let zz : P → ℂ := fun q => (1 + (q.2 : ℝ)) * (b q.1 : ℂ)
  have hzzc : Continuous zz := by
    have h1 : Continuous fun q : P => ((b q.1 : Circle) : ℂ) := continuous_subtype_val.comp
      (hbc.comp continuous_fst)
    have h2 : Continuous fun q : P => (((q.2 : unitInterval) : ℝ) : ℂ)
      := Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)
    exact (continuous_const.add h2).mul h1
  have hzzn : ∀ q, ‖zz q‖ = 1 + (q.2 : ℝ) := fun q => by
    simp only [zz, norm_mul, Circle.norm_coe, mul_one]
    rw [show (1 + ((q.2 : unitInterval) : ℂ)) = ((1 + (q.2 : ℝ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by linarith [q.2.2.1])]
  have hzz2 : ∀ q, zz q ∈ closedBall (0 : ℂ) 2 := fun q => by
    simp only [mem_closedBall, dist_zero_right, hzzn]
    linarith [q.2.2.2]
  have hzzi : Function.Injective zz := by
    intro q q' h
    have h1 := congrArg norm h
    rw [hzzn, hzzn] at h1
    have h2 : (q.2 : ℝ) = q'.2 := by linarith
    have h3 : (1 + ((q.2 : ℝ) : ℂ)) ≠ 0 := by
      rw [show (1 + (((q.2 : ℝ)) : ℂ)) = ((1 + (q.2 : ℝ) : ℝ) : ℂ) by push_cast; rfl]
      exact_mod_cast (by linarith [q.2.2.1] : (1 + (q.2 : ℝ)) ≠ 0)
    have h4 : (b q.1 : ℂ) = b q'.1 := by
      have h5 : (1 + ((q.2 : ℝ) : ℂ)) * (b q.1 : ℂ) = (1 + ((q.2 : ℝ) : ℂ)) * (b q'.1 : ℂ) := by
        simpa only [zz, h2] using h
      exact mul_left_cancel₀ h3 h5
    have h6 : b q.1 = b q'.1 := Circle.ext h4
    have h7 : q.1 = q'.1 := by
      have h8 := p.symm.injective h6
      exact ha.2 (hι.injective (congrArg Subtype.val h8))
    exact Prod.ext h7 (Subtype.ext h2)
  have hoff : ∀ q : P, 0 < (q.2 : ℝ) → c (zz q) ∉ Δ := fun q hq hmem => by
    rw [← hcΔ] at hmem
    obtain ⟨w, hw, he⟩ := hmem
    have h1 := hl (hzz2 q)
    have h2 := hl (closedBall_subset_closedBall (by norm_num) hw)
    rw [he] at h2
    rw [h1] at h2
    have h3 : ‖zz q‖ ≤ 1 := by
      rw [h2]
      simpa using hw
    rw [hzzn] at h3
    linarith
  have hrange : ∀ q : P, c (zz q) ∈ range ι := fun q => by
    by_cases hq : (q.2 : ℝ) = 0
    · have h1 : zz q = b q.1 := by
        simp [zz, hq]
      rw [h1, hpb]
      exact mem_range_self _
    · exact (hun.symm ▸ mem_univ (c (zz q)) : c (zz q) ∈ range ι ∪ Δ).resolve_right (hoff q
      (lt_of_le_of_ne q.2.2.1 (Ne.symm hq)))
  choose E hE using fun q => hrange q
  have hEc : Continuous E := by
    rw [hι.isInducing.continuous_iff]
    have : ι ∘ E = c ∘ zz := funext hE
    rw [this]
    exact hcc.comp_continuous hzzc hzz2
  have hEi : Function.Injective E := fun q q' h => by
    have h1 : c (zz q) = c (zz q') := by rw [← hE, ← hE, h]
    exact hzzi (by rw [← hl (hzz2 q), ← hl (hzz2 q'), h1])
  have hE0 : ∀ t, E (t, 0) = a t := fun t => by
    apply hι.injective
    rw [hE]
    have h1 : zz (t, 0) = b t := by simp [zz]
    rw [h1, hpb]
  have hEint : ∀ q : P, 0 < (q.2 : ℝ) → (q.2 : ℝ) < 1 → E q ∉ bd Y := fun q h0 h1 hb => by
    have hin2 : c (zz q) ∈ discInt Δ' := by
      refine ⟨hmc (hzz2 q), fun h => ?_⟩
      rw [← hcb] at h
      obtain ⟨w, hw, he⟩ := h
      have h2 := hl (hzz2 q)
      have h3 := hl (sphere_subset_closedBall hw)
      rw [he, h2] at h3
      have h4 : ‖zz q‖ = 2 := by
        rw [h3]
        simpa using hw
      rw [hzzn] at h4
      linarith
    have h3 := isInteriorPoint_of_mem_discInt hman hΔ' hin2
    by_cases hmemC : E q ∈ C
    · apply hoff q h0
      rw [← hE]
      exact discBd_subset Δ (hbdΔ ▸ mem_image_of_mem _ hmemC)
    · have h4 : ι (E q) ∈ bd T := hbdT ▸ mem_image_of_mem _ ⟨hb, hmemC⟩
      rw [hE] at h4
      exact h4 h3
  exact ⟨E, hEc, hEi, hE0, hEint⟩

/-- A closed disc along a line `K` of the boundary. It meets the boundary exactly in `K` and it
meets the closed set `Z` at most in the
ends of `K`. -/
theorem exists_wedge {Y : Type} [TopologicalSpace Y] (hY : IsSurface Y) {K Z : Set Y} {u v : Y}
  (hK : IsLineWithEnds K u v) (hKb : K ⊆ bd Y) (hZ : IsClosed Z)
    (hZK : Z ∩ K ⊆ {u, v}) : ∃ D, IsClosedDisc D ∧ K ⊆ discBd D ∧ D ∩ Z ⊆ {u, v} ∧ D ∩ bd Y = K
      := by
  have ht2 : T2Space Y := hY.2.1
  obtain ⟨a, ha, hr, rfl, rfl⟩ := hK.exists_arc
  obtain ⟨E, hEc, hEi, hE0, hEint⟩ := exists_boundary_arc_strip hY ha (hr ▸ hKb)
  let P := unitInterval × unitInterval
  classical
  let A : Set P := E ⁻¹' (Z ∪ {a 0, a 1})
  have hAc : IsClosed A := (hZ.union (toFinite _).isClosed).preimage hEc
  have hA0 : ((0, 0) : P) ∈ A := by
    change E (0, 0) ∈ Z ∪ {a 0, a 1}
    rw [hE0]
    exact .inr (.inl rfl)
  have hA1 : ((1, 0) : P) ∈ A := by
    change E (1, 0) ∈ Z ∪ {a 0, a 1}
    rw [hE0]
    exact .inr (.inr rfl)
  have hAne : A.Nonempty := ⟨_, hA0⟩
  let ρ : unitInterval → ℝ := fun t => min (1 / 2) (infDist ((t, 0) : P) A / 2)
  have hρc : Continuous ρ := by
    refine continuous_const.min ((continuous_infDist_pt A).comp (by fun_prop) |>.div_const 2)
  have hρ0 : ρ 0 = 0 := by
    simp only [ρ, infDist_zero_of_mem hA0]
    norm_num
  have hρ1 : ρ 1 = 0 := by
    simp only [ρ, infDist_zero_of_mem hA1]
    norm_num
  have hρnn : ∀ t, 0 ≤ ρ t := fun t => le_min (by norm_num) (div_nonneg infDist_nonneg
    (by norm_num))
  have hρle : ∀ t, ρ t ≤ 1 / 2 := fun t => min_le_left _ _
  have hρpos : ∀ t, t ≠ 0 → t ≠ 1 → 0 < ρ t := by
    intro t h0 h1
    have h2 : ((t, 0) : P) ∉ A := by
      rintro (h | h | h)
      · have h3 : a t ∈ Z := by
          have := hE0 t
          rwa [show E (t, 0) = a t from this] at h
        rcases hZK ⟨h3, hr ▸ mem_range_self t⟩ with h4 | h4
        · exact h0 (ha.2 h4)
        · exact h1 (ha.2 h4)
      · rw [hE0] at h
        exact h0 (ha.2 h)
      · rw [hE0] at h
        exact h1 (ha.2 h)
    have h3 := (hAc.notMem_iff_infDist_pos hAne).mp h2
    exact lt_min (by norm_num) (by positivity)
  have hoffA : ∀ t (s : unitInterval), (s : ℝ) ≤ ρ t → 0 < ρ t → ((t, s) : P) ∉ A := by
    intro t s hs hpos hmem
    have h1 := infDist_le_dist_of_mem (x := ((t, 0) : P)) hmem
    have h2 : dist ((t, 0) : P) (t, s) = (s : ℝ) := by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Subtype.dist_eq, Real.dist_eq]
      simp [abs_of_nonneg s.2.1]
    have h3 : ρ t ≤ infDist ((t, 0) : P) A / 2 := min_le_right _ _
    rw [h2] at h1
    linarith
  let f : ℂ → ℝ := fun z => ρ (wedgeT z) * wedgeTau z
  have hfc : ContinuousOn f (closedBall (0 : ℂ) 1) := continuousOn_wedge hρc hρ0 hρ1 hρnn
  have hf0 : ∀ z ∈ closedBall (0 : ℂ) 1, 0 ≤ f z := fun z hz => mul_nonneg (hρnn _)
    (wedgeTau_mem hz).1
  have hf1 : ∀ z ∈ closedBall (0 : ℂ) 1, f z ≤ ρ (wedgeT z) := fun z hz => mul_le_of_le_one_right
    (hρnn _) (wedgeTau_mem hz).2
  let ss : ℂ → unitInterval := fun z => projIcc 0 1 zero_le_one (f z)
  have hss : ∀ z ∈ closedBall (0 : ℂ) 1, (ss z : ℝ) = f z := fun z hz => by
    have h1 := hf1 z hz
    have h2 := hρle (wedgeT z)
    simp only [ss]
    rw [projIcc_of_mem _ (show f z ∈ Icc (0 : ℝ) 1 from ⟨hf0 z hz, by linarith⟩)]
  let Ψ : ℂ → Y := fun z => E (wedgeT z, ss z)
  have hΨc : ContinuousOn Ψ (closedBall (0 : ℂ) 1) :=
    hEc.comp_continuousOn (continuous_wedgeT.continuousOn.prodMk
      (continuous_projIcc.comp_continuousOn hfc))
  have hsq : ∀ z ∈ closedBall (0 : ℂ) 1, z.re ^ 2 + z.im ^ 2 ≤ 1 := fun z hz => by
    have h2 : ‖z‖ ≤ 1 := by simpa using hz
    have h3 := Complex.sq_norm z
    rw [Complex.normSq_apply] at h3
    nlinarith [norm_nonneg z]
  have hend : ∀ z ∈ closedBall (0 : ℂ) 1, (wedgeT z = 0 ∨ wedgeT z = 1) → z.re ^ 2 = 1 ∧ z.im = 0
    := fun z hz h => by
    have h1 := wedgeT_coe hz
    have h2 : z.re = -1 ∨ z.re = 1 := by
      rcases h with h | h
      · rw [h] at h1
        left
        have h3 : (((0 : unitInterval) : ℝ)) = 0 := rfl
        linarith
      · rw [h] at h1
        right
        have h3 : (((1 : unitInterval) : ℝ)) = 1 := rfl
        linarith
    have h3 : z.re ^ 2 = 1 := by
      rcases h2 with h2 | h2 <;> rw [h2] <;> norm_num
    exact ⟨h3, by nlinarith [hsq z hz, sq_nonneg z.im]⟩
  have hΨi : InjOn Ψ (closedBall (0 : ℂ) 1) := by
    intro z hz z' hz' h
    have h1 := hEi h
    have h2 : wedgeT z = wedgeT z' := congrArg Prod.fst h1
    have h3 : ss z = ss z' := congrArg Prod.snd h1
    have hre := re_of_wedgeT hz hz' h2
    by_cases hend0 : wedgeT z = 0 ∨ wedgeT z = 1
    · have h4 := hend z hz hend0
      have h5 := hend z' hz' (h2 ▸ hend0)
      exact Complex.ext hre (h4.2.trans h5.2.symm)
    · push Not at hend0
      have hp := hρpos _ hend0.1 hend0.2
      have h4 : f z = f z' := by rw [← hss z hz, ← hss z' hz', h3]
      have h5 : wedgeTau z = wedgeTau z' := by
        simp only [f, ← h2] at h4
        exact mul_left_cancel₀ hp.ne' h4
      have hw : 0 < √(1 - z.re ^ 2) := by
        refine lt_of_le_of_ne (Real.sqrt_nonneg _) fun h6 => ?_
        have h7 : 1 - z.re ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp h6.symm
        have h8 : z.re ^ 2 = 1 := by nlinarith [hsq z hz, sq_nonneg z.im]
        have h9 : (z.re - 1) * (z.re + 1) = 0 := by nlinarith
        have h10 := wedgeT_coe hz
        rcases mul_eq_zero.mp h9 with h11 | h11
        · exact hend0.2 (Subtype.ext (by rw [h10]; change _ = (1 : ℝ); linarith))
        · exact hend0.1 (Subtype.ext (by rw [h10]; change _ = (0 : ℝ); linarith))
      simp only [wedgeTau, ← hre] at h5
      rw [div_left_inj₀ (by positivity)] at h5
      exact Complex.ext hre (by linarith)
  obtain ⟨hD, hDb⟩ := isClosedDisc_image_injOn isClosedDisc_closedBall.1
    (isCompact_closedBall 0 1) hΨc hΨi
  rw [isClosedDisc_closedBall.2] at hDb
  have hlow : ∀ t, ∃ z ∈ sphere (0 : ℂ) 1, Ψ z = a t := fun t => by
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hw : 0 ≤ 1 - (2 * (t : ℝ) - 1) ^ 2 := by nlinarith
    let z : ℂ := ⟨2 * t - 1, -√(1 - (2 * (t : ℝ) - 1) ^ 2)⟩
    have hzn : ‖z‖ = 1 := by
      have h3 := Complex.sq_norm z
      rw [Complex.normSq_apply] at h3
      have h4 : z.re * z.re + z.im * z.im = 1 := by
        simp only [z, neg_mul_neg, Real.mul_self_sqrt hw]
        ring
      rw [h4] at h3
      nlinarith [norm_nonneg z]
    have hzb : z ∈ closedBall (0 : ℂ) 1 := by simp [hzn]
    have htz : wedgeT z = t := Subtype.ext (by rw [wedgeT_coe hzb]; simp only [z]; ring)
    have hτ : wedgeTau z = 0 := by
      simp only [wedgeTau, z]
      simp
    have hs0 : ss z = 0 := Subtype.ext (by
      rw [hss z hzb]
      simp only [f, hτ, mul_zero]
      rfl)
    refine ⟨z, by simp [hzn], ?_⟩
    simp only [Ψ, htz, hs0]
    exact hE0 t
  have hzero : ∀ z ∈ closedBall (0 : ℂ) 1, ρ (wedgeT z) = 0 → ss z = 0 := fun z hz h => Subtype.ext
    (by
    rw [hss z hz]
    simp only [f, h, zero_mul]
    rfl)
  have hp0 : ∀ t, ρ t = 0 → t = 0 ∨ t = 1 := fun t h => by
    by_contra hn
    push Not at hn
    exact (hρpos t hn.1 hn.2).ne' h
  have hKD : K ⊆ Ψ '' sphere (0 : ℂ) 1 := by
    rw [← hr]
    rintro _ ⟨t, rfl⟩
    obtain ⟨z, hz, he⟩ := hlow t
    exact ⟨z, hz, he⟩
  refine ⟨Ψ '' closedBall 0 1, hD, hDb ▸ hKD, ?_, ?_⟩
  · rintro _ ⟨⟨z, hz, rfl⟩, hy⟩
    rcases (hρnn (wedgeT z)).eq_or_lt with h | h
    · have h1 := hzero z hz h.symm
      have h2 : Ψ z = a (wedgeT z) := by
        simp only [Ψ, h1]
        exact hE0 _
      rw [h2]
      rcases hp0 _ h.symm with h3 | h3
      · rw [h3]
        exact .inl rfl
      · rw [h3]
        exact .inr rfl
    · exact absurd (Or.inl hy) (hoffA (wedgeT z) (ss z) (by rw [hss z hz]; exact hf1 z hz) h)
  · apply subset_antisymm
    · rintro _ ⟨⟨z, hz, rfl⟩, hy⟩
      rcases (ss z).2.1.eq_or_lt with h | h
      · have h1 : ss z = 0 := Subtype.ext h.symm
        have h2 : Ψ z = a (wedgeT z) := by
          simp only [Ψ, h1]
          exact hE0 _
        rw [h2, ← hr]
        exact mem_range_self _
      · have h1 : (ss z : ℝ) < 1 := by
          rw [hss z hz]
          linarith [hf1 z hz, hρle (wedgeT z)]
        exact absurd hy (hEint (wedgeT z, ss z) h h1)
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := hKD hy
      exact ⟨⟨z, sphere_subset_closedBall hz, rfl⟩, hKb hy⟩

end GraphMinor.Surface
