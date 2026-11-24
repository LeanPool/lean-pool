/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscGrow
public import LeanPool.GraphMinor.Surface.Jordan
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Merging a closed disc with a chart

Let `Y` be a set of a closed surface in which every `O`-arc bounds a closed disc.
`exists_disc_merge`
says that a closed disc of `Y` and a round disc of a chart in `Y` that overlap lie in a common
closed
disc of `Y`, unless `Y` is a whole sphere.

The round circle of the chart meets the boundary of the disc in a wild way, so `exists_tame_pair`
first moves it a little. The new curve still goes around the centre of the chart, since a logarithm
of the coordinate on it would give two different values for the rise of the angle along its two
arcs (`not_hasLogOn_of_two_sides`). Now `exists_disc_cover` swallows the curve.

The file also shows that an `O`-arc has empty interior in a surface, and that a surface is
metrizable.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

local notation "𝕀" => unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The plane does not embed in the circle: a logarithm of the map would be an injective continuous
real function. -/
theorem not_injective_circle {j : ℂ → Circle} (hj : Continuous j) : ¬ Function.Injective j := by
  intro hinj
  obtain ⟨g, hg, hfg⟩ := hasLogOn_univ_of_ne_zero (f := fun z => ((j z : Circle) : ℂ))
    (by fun_prop) (fun z => Circle.coe_ne_zero _)
  have hgc : Continuous g := continuousOn_univ.mp hg
  refine not_injective_real (f := fun z => (g z).im) (by fun_prop) fun x y hxy => ?_
  have hre : ∀ z, (g z).re = 0 := by
    intro z
    have h1 : ‖((j z : Circle) : ℂ)‖ = 1 := Circle.norm_coe _
    have h2 : ((j z : Circle) : ℂ) = Complex.exp (g z) := hfg z (mem_univ _)
    rw [h2, Complex.norm_exp] at h1
    simpa using h1
  have hgg : g x = g y := Complex.ext (by rw [hre, hre]) hxy
  refine hinj (Circle.ext ?_)
  have h2 : ((j x : Circle) : ℂ) = Complex.exp (g x) := hfg x (mem_univ _)
  have h3 : ((j y : Circle) : ℂ) = Complex.exp (g y) := hfg y (mem_univ _)
  rw [h2, h3, hgg]

/-- An `O`-arc contains no embedded open ball of the plane. -/
theorem not_image_ball_subset_oArc {G : Set S} (hG : IsOArc G) {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {g : ℂ → S} (hgc : ContinuousOn g (ball w ρ)) (hgi : InjOn g (ball w ρ)) :
    ¬ g '' ball w ρ ⊆ G := by
  intro hsub
  obtain ⟨φ⟩ := hG
  let k : ℂ → ℂ := fun z => w + ((ρ / (1 + ‖z‖) : ℝ) : ℂ) * z
  have hkc : Continuous k := by
    refine continuous_const.add (Continuous.mul ?_ continuous_id)
    refine Complex.continuous_ofReal.comp (continuous_const.div (by fun_prop) fun z => ?_)
    positivity
  have hkm : ∀ z, k z ∈ ball w ρ := fun z => by
    rw [mem_ball, dist_eq_norm]
    simp only [k, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg z]
  have hki : Function.Injective k := by
    intro z z' he
    have h1 : ((ρ / (1 + ‖z‖) : ℝ) : ℂ) * z = ((ρ / (1 + ‖z'‖) : ℝ) : ℂ) * z' :=
      add_left_cancel he
    have h2 := congrArg norm h1
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h2
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), div_mul_eq_mul_div,
      div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)] at h2
    have h3 : ‖z‖ = ‖z'‖ := by
      have h4 : ρ * (‖z‖ - ‖z'‖) = 0 := by linarith
      have := (mul_eq_zero.mp h4).resolve_left hρ.ne'
      linarith
    rw [h3] at h1
    have h5 : ((ρ / (1 + ‖z'‖) : ℝ) : ℂ) ≠ 0 := by
      have : ρ / (1 + ‖z'‖) ≠ 0 := by positivity
      exact_mod_cast this
    exact mul_left_cancel₀ h5 h1
  let j : ℂ → Circle := fun z => φ.symm ⟨g (k z), hsub ⟨_, hkm z, rfl⟩⟩
  refine not_injective_circle (j := j) ?_ ?_
  · refine φ.symm.continuous.comp (Continuous.subtype_mk ?_ _)
    exact hgc.comp_continuous hkc hkm
  · intro z z' he
    have h1 := congrArg Subtype.val (φ.symm.injective he)
    exact hki (hgi (hkm z) (hkm z') h1)

/-- A compact 2-manifold is second countable. -/
theorem secondCountable_of_manifold [CompactSpace S] (hman : ∀ x : S, IsManifoldPoint x) :
    SecondCountableTopology S := by
  choose U V hU hV hx he using hman
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU fun x _ => mem_iUnion.mpr ⟨x, hx x⟩
  have hsc : ∀ i : t, SecondCountableTopology (U i.1) := fun i => by
    obtain ⟨e⟩ := he i.1
    have : SecondCountableTopology (EuclideanHalfSpace 2) :=
      inferInstanceAs (SecondCountableTopology {x : EuclideanSpace ℝ (Fin 2) // 0 ≤ x 0})
    exact e.secondCountableTopology
  refine @TopologicalSpace.secondCountableTopology_of_countable_cover S _ t _ (fun i => U i.1) hsc
    (fun i => hU i.1) ?_
  rw [eq_univ_iff_forall]
  intro x
  obtain ⟨i, hi⟩ := mem_iUnion.mp (ht (mem_univ x))
  obtain ⟨hi', hxi⟩ := mem_iUnion.mp hi
  exact mem_iUnion.mpr ⟨⟨i, hi'⟩, hxi⟩

/-- Coordinates on an open subset of a surface, onto the ball of radius `R`. -/
structure BallChart (R : ℝ) (U : Set S) (h : S → ℂ) (g : ℂ → S) : Prop where
  isOpen : IsOpen U
  hc : ContinuousOn h U
  gc : ContinuousOn g (ball 0 R)
  hm : MapsTo h U (ball 0 R)
  gm : MapsTo g (ball 0 R) U
  gh : LeftInvOn g h U
  hg : LeftInvOn h g (ball 0 R)

namespace BallChart

variable {R : ℝ} {U : Set S} {h : S → ℂ} {g : ℂ → S}

theorem isOpen_image (c : BallChart R U h g) {V : Set ℂ} (hV : IsOpen V) (hsub : V ⊆ ball 0 R) :
    IsOpen (g '' V) := by
  have : g '' V = U ∩ h ⁻¹' V := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨c.gm (hsub hz), ?_⟩
      change h (g z) ∈ V
      rwa [c.hg (hsub hz)]
    · rintro ⟨h1, h2⟩
      exact ⟨h x, h2, c.gh h1⟩
  rw [this]
  exact c.hc.isOpen_inter_preimage c.isOpen hV

/-- The same chart, turned by `u`. -/
theorem rotate (c : BallChart R U h g) (u : Circle) :
    BallChart R U (fun x => (u⁻¹ : Circle) * h x) (fun z => g ((u : ℂ) * z)) := by
  have hmem : ∀ z : ℂ, z ∈ ball (0 : ℂ) R → (u : ℂ) * z ∈ ball (0 : ℂ) R := fun z hz => by
    simpa [norm_mul] using hz
  have hmem' : ∀ z : ℂ, z ∈ ball (0 : ℂ) R → ((u⁻¹ : Circle) : ℂ) * z ∈ ball (0 : ℂ) R :=
    fun z hz => by simpa [norm_mul] using hz
  have hcan : ∀ z : ℂ, (u : ℂ) * (((u⁻¹ : Circle) : ℂ) * z) = z := fun z => by
    rw [← mul_assoc, ← Circle.coe_mul]
    simp
  have hcan' : ∀ z : ℂ, ((u⁻¹ : Circle) : ℂ) * ((u : ℂ) * z) = z := fun z => by
    rw [← mul_assoc, ← Circle.coe_mul]
    simp
  refine ⟨c.isOpen, ContinuousOn.mul continuousOn_const c.hc, ?_, ?_, ?_, ?_, ?_⟩
  · exact c.gc.comp (by fun_prop) hmem
  · exact fun x hx => hmem' _ (c.hm hx)
  · exact fun z hz => c.gm (hmem z hz)
  · intro x hx
    change g ((u : ℂ) * (((u⁻¹ : Circle) : ℂ) * h x)) = x
    rw [hcan, c.gh hx]
  · intro z hz
    change ((u⁻¹ : Circle) : ℂ) * h (g ((u : ℂ) * z)) = z
    rw [c.hg (hmem z hz), hcan']

/-- A closed subset of the chart ball that is a closed disc gives a closed disc. -/
theorem image_disc (c : BallChart R U h g) {Z : Set ℂ} (hZ : IsClosedDisc Z) (hsub : Z ⊆ ball 0 R) :
    IsClosedDisc (g '' Z) ∧ discBd (g '' Z) = g '' discBd Z :=
  hZ.image (c.gc.mono hsub) (c.hc.mono (image_subset_iff.mpr fun _ hz => c.gm (hsub hz)))
    (c.hg.mono hsub)

end BallChart

/-- Every interior point has a chart inside any open set, with the point at the centre. -/
theorem IsInteriorPoint.exists_ballChart {y : S} (hy : IsInteriorPoint y) {W : Set S}
    (hW : IsOpen W) (hyW : y ∈ W) {R : ℝ} (hR : 0 < R) :
    ∃ U h g, BallChart R U h g ∧ U ⊆ W ∧ g 0 = y := by
  obtain ⟨U₀, hU₀, hyU, hsub, ⟨f⟩⟩ := hy.exists_subset hW hyW
  obtain ⟨b⟩ := exists_homeomorph_ball (0 : ℂ) one_pos
  have : Nonempty S := ⟨y⟩
  obtain ⟨h₀, g₀, h1, h2, h3, h4, h5, h6⟩ := exists_functions_of_homeomorph (f.trans b.symm)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_ball _ (h3 hyU)
  set c := h₀ y with hc
  have hscale : ((ρ / R : ℝ) : ℂ) ≠ 0 := by
    have : ρ / R ≠ 0 := by positivity
    exact_mod_cast this
  let e : ℂ → ℂ := fun z => c + ((ρ / R : ℝ) : ℂ) * z
  let e' : ℂ → ℂ := fun z => ((R / ρ : ℝ) : ℂ) * (z - c)
  have hee' : ∀ z, e (e' z) = z := fun z => by
    simp only [e, e']
    rw [← mul_assoc, ← Complex.ofReal_mul, div_mul_div_comm, mul_comm ρ R, div_self (by positivity)]
    simp
  have he'e : ∀ z, e' (e z) = z := fun z => by
    simp only [e, e', add_sub_cancel_left]
    rw [← mul_assoc, ← Complex.ofReal_mul, div_mul_div_comm, mul_comm R ρ, div_self (by positivity)]
    simp
  have hem : ∀ z ∈ ball (0 : ℂ) R, e z ∈ ball c ρ := fun z hz => by
    rw [mem_ball, dist_eq_norm]
    simp only [e, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity), div_mul_eq_mul_div, div_lt_iff₀ hR]
    have : ‖z‖ < R := mem_ball_zero_iff.mp hz
    nlinarith
  have he'm : ∀ z ∈ ball c ρ, e' z ∈ ball (0 : ℂ) R := fun z hz => by
    rw [mem_ball_zero_iff]
    simp only [e', norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity), div_mul_eq_mul_div, div_lt_iff₀ hρ]
    have : ‖z - c‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hz
    nlinarith
  refine ⟨U₀ ∩ h₀ ⁻¹' ball c ρ, fun x => e' (h₀ x), fun z => g₀ (e z), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    inter_subset_left.trans hsub, ?_⟩
  · exact h1.isOpen_inter_preimage hU₀ isOpen_ball
  · exact ContinuousOn.mul continuousOn_const ((h1.mono inter_subset_left).sub continuousOn_const)
  · refine h2.comp (by fun_prop) fun z hz => hball (hem z hz)
  · exact fun x hx => he'm _ hx.2
  · refine fun z hz => ⟨h4 (hball (hem z hz)), ?_⟩
    change h₀ (g₀ (e z)) ∈ ball c ρ
    rw [h6 (hball (hem z hz))]
    exact hem z hz
  · intro x hx
    change g₀ (e (e' (h₀ x))) = x
    rw [hee', h5 hx.1]
  · intro z hz
    change e' (h₀ (g₀ (e z))) = z
    rw [h6 (hball (hem z hz)), he'e]
  · change g₀ (e 0) = y
    simp only [e, mul_zero, add_zero]
    exact h5 hyU

/-- The coordinate has no logarithm on two sets that join `ρ e^{-iτ}` and `ρ e^{iτ}` on the two
sides of the origin: the rise of the angle along the two sets differs by `2π`. -/
theorem not_hasLogOn_of_two_sides {A B : Set ℂ} (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hAs : ∀ z ∈ A, z ∈ Complex.slitPlane) (hBs : ∀ z ∈ B, -z ∈ Complex.slitPlane) {ρ τ : ℝ}
    (hρ : 0 < ρ) (hτ : τ ∈ Ioo 0 Real.pi) {p q : ℂ}
    (hp : p = ρ * Complex.exp (-τ * Complex.I)) (hq : q = ρ * Complex.exp (τ * Complex.I))
    (hpA : p ∈ A) (hqA : q ∈ A) (hpB : p ∈ B) (hqB : q ∈ B) :
    ¬ HasLogOn (A ∪ B) fun z => z := by
  rintro ⟨f, hfc, hf⟩
  have hpi := Real.pi_pos
  have hlogA : ∀ z ∈ A, Complex.exp (f z - Complex.log z) = 1 := fun z hz => by
    rw [Complex.exp_sub, ← hf z (.inl hz), Complex.exp_log (Complex.slitPlane_ne_zero (hAs z hz)),
      div_self (Complex.slitPlane_ne_zero (hAs z hz))]
  have hne : ∀ z ∈ B, z ≠ 0 := fun z hz h0 => by
    have := Complex.slitPlane_ne_zero (hBs z hz)
    simp [h0] at this
  have hlogB : ∀ z ∈ B, Complex.exp (f z - Complex.log (-z)) = -1 := fun z hz => by
    have h1 := hne z hz
    rw [Complex.exp_sub, ← hf z (.inr hz), Complex.exp_log (Complex.slitPlane_ne_zero (hBs z hz))]
    field_simp
  have hcA : ContinuousOn (fun z => f z - Complex.log z) A :=
    (hfc.mono subset_union_left).sub (continuousOn_id.clog hAs)
  have hcB : ContinuousOn (fun z => f z - Complex.log (-z) - Real.pi * Complex.I) B := by
    refine ((hfc.mono subset_union_right).sub ?_).sub continuousOn_const
    exact (continuousOn_id.neg).clog hBs
  have e1 := eq_of_exp_eq_one hA hcA hlogA hpA hqA
  have e2 := eq_of_exp_eq_one hB hcB (fun z hz => by
    rw [Complex.exp_sub, hlogB z hz, Complex.exp_pi_mul_I]
    simp) hpB hqB
  have hl : ∀ θ : ℝ, -Real.pi < θ → θ ≤ Real.pi →
      Complex.log (ρ * Complex.exp (θ * Complex.I)) = Real.log ρ + θ * Complex.I := fun θ h1 h2
        => by
    rw [Complex.log_ofReal_mul hρ (Complex.exp_ne_zero _), Complex.log_exp (by simpa) (by simpa)]
  have hminus : ∀ θ : ℝ, -(ρ * Complex.exp (θ * Complex.I)) =
      ρ * Complex.exp (((θ - Real.pi : ℝ) : ℂ) * Complex.I) := fun θ => by
    push_cast
    rw [sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I]
    ring
  have hminus' : ∀ θ : ℝ, -(ρ * Complex.exp (θ * Complex.I)) =
      ρ * Complex.exp (((θ + Real.pi : ℝ) : ℂ) * Complex.I) := fun θ => by
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hp' : p = ρ * Complex.exp (((-τ : ℝ) : ℂ) * Complex.I) := by simpa using hp
  have l1 := hl τ (by linarith [hτ.1]) hτ.2.le
  have l2 := hl (-τ) (by linarith [hτ.2]) (by linarith [hτ.1])
  have l3 := hl (τ - Real.pi) (by linarith [hτ.1]) (by linarith [hτ.2])
  have l4 := hl (-τ + Real.pi) (by linarith [hτ.2]) (by linarith [hτ.1])
  rw [← hq] at l1
  rw [← hp'] at l2
  rw [← hminus, ← hq] at l3
  rw [← hminus', ← hp'] at l4
  rw [l1, l2] at e1
  simp only [l3, l4] at e2
  have h0 : (2 * Real.pi : ℂ) * Complex.I = 0 := by
    push_cast at e1 e2
    linear_combination e1 - e2
  have h1 : (2 * Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero]
  exact h1 h0

/-- `P` is an `O`-arc around the centre of the plane: if it lies outside the ball of radius `2`, and
inside the ball of radius `3`, and the coordinate has no logarithm on it, then the ball of radius
`2` lies in the closed domain of `P`, and this domain lies in the ball of radius `3`. -/
theorem closedBall_subset_inner {P : Set ℂ} (hP : Nonempty (Circle ≃ₜ P))
    (h2 : Disjoint P (closedBall 0 2)) (h3 : P ⊆ ball 0 3) (hlog : ¬ HasLogOn P fun z => z) :
    closedBall 0 2 ⊆ inner P ∧ closedInner P ⊆ ball 0 3 := by
  obtain ⟨φ⟩ := id hP
  have J := isJordanParts φ
  -- a slightly smaller radius still contains `P`
  obtain ⟨r, hr, hPr⟩ : ∃ r < (3 : ℝ), 0 ≤ r ∧ P ⊆ closedBall 0 r := by
    by_cases hne : P.Nonempty
    · obtain ⟨z, hz, hmax⟩ := J.isCompact.exists_isMaxOn hne continuous_norm.continuousOn
      refine ⟨‖z‖, mem_ball_zero_iff.mp (h3 hz), norm_nonneg _, fun w hw => ?_⟩
      exact mem_closedBall_zero_iff.mpr (hmax hw)
    · exact ⟨0, by norm_num, le_rfl, fun w hw => absurd ⟨w, hw⟩ hne⟩
  obtain ⟨hr0, hPr⟩ := hPr
  have houter : (closedBall (0 : ℂ) r)ᶜ ⊆ outer P := by
    have hconn := isPreconnected_compl_closedBall r hr0
    have hdisj : (closedBall (0 : ℂ) r)ᶜ ⊆ inner P ∪ outer P := by
      rw [J.union_eq]
      exact fun z hz hzP => hz (hPr hzP)
    rcases hconn.subset_or_subset J.isOpen_inner J.isOpen_outer J.disjoint hdisj with h | h
    · exfalso
      obtain ⟨R, hR⟩ := J.isBounded_inner.subset_closedBall 0
      have hmem : ((max R r + 1 : ℝ) : ℂ) ∈ (closedBall (0 : ℂ) r)ᶜ := by
        have : ‖((max R r + 1 : ℝ) : ℂ)‖ = max R r + 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
          have := le_max_right R r
          linarith
        simp only [mem_compl_iff, mem_closedBall_zero_iff, this, not_le]
        linarith [le_max_right R r]
      have := hR (h hmem)
      simp only [mem_closedBall_zero_iff] at this
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
        have := le_max_right R r
        linarith)] at this
      linarith [le_max_left R r]
    · exact h
  have hinner : inner P ⊆ closedBall 0 r := fun z hz => by
    by_contra hcon
    exact Set.disjoint_left.mp J.disjoint hz (houter hcon)
  have h0P : (0 : ℂ) ∉ P := fun h => Set.disjoint_left.mp h2 h (by simp)
  have hmem : ∀ z ∈ closedBall (0 : ℂ) 2, z ∈ inner P ∪ outer P := fun z hz => by
    rw [J.union_eq]
    exact fun h => Set.disjoint_left.mp h2 h hz
  have hball := (convex_closedBall (0 : ℂ) 2).isPreconnected
  have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) 2 := by simp
  have hc := hball.subset_or_subset J.isOpen_inner J.isOpen_outer J.disjoint hmem
  have hin : closedBall 0 2 ⊆ inner P := by
    rcases hc with h | h
    · exact h
    exfalso
    -- the centre and the far point `4` lie in one component of the complement
    have h4 : (4 : ℂ) ∈ outer P := houter (by
      simp only [mem_compl_iff, mem_closedBall_zero_iff, not_le]
      norm_num
      linarith)
    have h0o : (0 : ℂ) ∈ outer P := h h0mem
    have hcomp : (4 : ℂ) ∈ connectedComponentIn Pᶜ 0 := by
      have hsub : outer P ⊆ Pᶜ := fun z hz => hz.1
      exact J.isConnected_outer.isPreconnected.subset_connectedComponentIn h0o hsub h4
    have hl := hasLogOn_div_of_same_component J.isCompact.isClosed h0P hcomp
    have hl2 : HasLogOn P fun z : ℂ => 4 - z := hasLogOn_of_slitPlane (by fun_prop) fun z hz => by
      left
      have h5 : ‖z‖ < 3 := mem_ball_zero_iff.mp (h3 hz)
      have h6 := (abs_le.mp (Complex.abs_re_le_norm z)).2
      simp only [Complex.sub_re]
      norm_num
      linarith
    have hl3 : HasLogOn P fun _ : ℂ => (-1 : ℂ) := hasLogOn_const (by norm_num)
    refine hlog ((((hl.inv).mul hl2).mul hl3).congr fun z hz => ?_)
    have hz0 : z ≠ 0 := fun h => h0P (h ▸ hz)
    have hz4 : z - 4 ≠ 0 := fun h => by
      have h5 : ‖z‖ < 3 := mem_ball_zero_iff.mp (h3 hz)
      rw [sub_eq_zero.mp h] at h5
      norm_num at h5
    simp only [sub_zero]
    field_simp
    ring
  refine ⟨hin, union_subset ?_ h3⟩
  exact hinner.trans (closedBall_subset_ball hr)

theorem IsOArc.isCompact {F : Set S} (hF : IsOArc F) : IsCompact F := by
  obtain ⟨φ⟩ := hF
  have h : range (fun w : Circle => (φ w).1) = F := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact (φ w).2
    · intro hz
      exact ⟨φ.symm ⟨z, hz⟩, by simp⟩
  rw [← h]
  exact isCompact_range (continuous_subtype_val.comp φ.continuous)

theorem IsOArc.isPreconnected {F : Set S} (hF : IsOArc F) : IsPreconnected F := by
  obtain ⟨φ⟩ := hF
  have h : range (fun w : Circle => (φ w).1) = F := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact (φ w).2
    · intro hz
      exact ⟨φ.symm ⟨z, hz⟩, by simp⟩
  rw [← h]
  exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)

/-- The inclusion of an open set of a space into a subspace that contains it. -/
theorem isOpenEmbedding_inclusion_of_isOpen {Δ V : Set S} (hV : IsOpen V) (hsub : V ⊆ Δ) :
    IsOpenEmbedding (fun v : V => (⟨v.1, hsub v.2⟩ : Δ)) := by
  have he₂ : IsOpenEmbedding (Subtype.val : V → S) := hV.isOpenEmbedding_subtypeVal
  refine .of_continuous_injective_isOpenMap
    (Continuous.subtype_mk continuous_subtype_val _)
    (fun a b h => Subtype.ext (show a.1 = b.1 from congrArg (Subtype.val : Δ → S) h)) fun W hW => ?_
  have h2 : IsOpen ((Subtype.val : V → S) '' W) := he₂.isOpenMap _ hW
  have h3 : (fun v : V => (⟨v.1, hsub v.2⟩ : Δ)) '' W = Subtype.val ⁻¹' ((Subtype.val : V
    → S) '' W) := by
    ext ⟨z, hz⟩
    constructor
    · rintro ⟨w, hw, he⟩
      exact ⟨w, hw, congrArg Subtype.val he⟩
    · rintro ⟨w, hw, he⟩
      exact ⟨w, hw, Subtype.ext he⟩
  rw [h3]
  exact h2.preimage continuous_subtype_val

/-- An open subset of a surface inside a closed disc, made of interior points of the surface, misses
the boundary of the disc. -/
theorem subset_discInt_of_isOpen {Δ V : Set S} (hint : ∀ x ∈ V, IsInteriorPoint x)
    (hV : IsOpen V) (hsub : V ⊆ Δ) : V ⊆ discInt Δ := by
  intro x hx
  refine ⟨hsub hx, ?_⟩
  rintro ⟨y, hy, rfl⟩
  apply hy
  have he₂ : IsOpenEmbedding (Subtype.val : V → S) := hV.isOpenEmbedding_subtypeVal
  have h1 : IsInteriorPoint (⟨y.1, hx⟩ : V) :=
    (isInteriorPoint_iff_of_isOpenEmbedding he₂ (x := ⟨y.1, hx⟩)).mp (hint y.1 hx)
  exact isInteriorPoint_of_isOpenEmbedding (isOpenEmbedding_inclusion_of_isOpen hV hsub) h1

/-- A point in the inside of a closed disc of a surface is an interior point of the surface. -/
theorem isInteriorPoint_of_mem_discInt (hman : ∀ x : S, IsManifoldPoint x) {D : Set S}
    (hD : IsClosedDisc D) {x : S} (hx : x ∈ discInt D) : IsInteriorPoint x := by
  have hV := hD.isOpen_discInt hman
  have hsub : discInt D ⊆ D := discInt_subset D
  have h1 : IsInteriorPoint (⟨x, hx.1⟩ : D) := by
    by_contra hcon
    exact hx.2 ⟨⟨x, hx.1⟩, hcon, rfl⟩
  have h2 : IsInteriorPoint (⟨x, hx⟩ : discInt D) :=
    (isInteriorPoint_iff_of_isOpenEmbedding (isOpenEmbedding_inclusion_of_isOpen hV hsub)
      (x := ⟨x, hx⟩)).mp h1
  exact isInteriorPoint_of_isOpenEmbedding hV.isOpenEmbedding_subtypeVal h2

/-- The inside of a closed disc grows with the disc. -/
theorem discInt_mono (hman : ∀ x : S, IsManifoldPoint x) {D E : Set S} (hD : IsClosedDisc D)
    (h : D ⊆ E) : discInt D ⊆ discInt E :=
  subset_discInt_of_isOpen (fun _ hx => isInteriorPoint_of_mem_discInt hman hD hx)
    (hD.isOpen_discInt hman) ((discInt_subset D).trans h)

/-- A curve around the ball of radius `2` of a chart, in the annulus of the radii `2` and `3`, which
meets the
given arcs in a finite way. It bounds a closed disc in the chart. The chart must show a piece of the
circle of
radius `r` off these arcs. -/
theorem exists_tame_curve [CompactSpace S] [T2Space S] (hman : ∀ x : S, IsManifoldPoint x)
    {U : Set S} {h : S → ℂ} {g : ℂ → S} (c : BallChart 3 U h g) (G : List (𝕀 → S))
      (hG : ∀ γ ∈ G, IsArcMap γ)
    {r ρ : ℝ} (hr2 : 2 < r) (hr3 : r < 3) (hρ : 0 < ρ) (hfree : ∀ z ∈ ball
      (r : ℂ) ρ, ∀ γ ∈ G, g z ∉ range γ) :
    ∃ P E : Set S, IsOArc P ∧ FinConn (P \ ⋃ γ ∈ G, range γ) ∧ IsClosedDisc E ∧ discBd E = P ∧
      g '' closedBall 0 2 ⊆ E ∧ E ⊆ U ∧ Disjoint P (g '' closedBall 0 2) := by
  classical
  have hsc := secondCountable_of_manifold hman
  let : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
  have hpi := Real.pi_pos
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  -- the angle
  set τ : ℝ := min 1 (ρ / (2 * r)) with hτdef
  have hτ0 : 0 < τ := lt_min one_pos (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτ2 : r * τ < ρ := by
    have h3 : τ ≤ ρ / (2 * r) := min_le_right _ _
    have h4 : r * τ ≤ r * (ρ / (2 * r)) := mul_le_mul_of_nonneg_left h3 (by linarith)
    have h5 : r * (ρ / (2 * r)) = ρ / 2 := by
      field_simp
    linarith
  -- the round circle as two arcs
  obtain ⟨a₀, b₀, hab, ha₀, hb₀, -⟩ := circle_two_arcs' (Circle.exp (-τ)) (θ := 2 * τ)
    ⟨by positivity, by nlinarith⟩
  have hrpos : (0 : ℝ) < r := by linarith
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
  let κ : Circle → ℂ := fun w => (r : ℂ) * w
  have hκc : Continuous κ := by fun_prop
  have hκi : Function.Injective κ := fun w w' he =>
    Circle.ext (mul_left_cancel₀ hrc he)
  have hκn : ∀ w, ‖κ w‖ = r := fun w => by
    simp [κ, abs_of_pos hrpos]
  let Ω₀ : Set ℂ := {z | 2 < ‖z‖ ∧ ‖z‖ < 3}
  have hΩ₀ : IsOpen Ω₀ := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hΩ₀b : Ω₀ ⊆ ball 0 3 := fun z hz => mem_ball_zero_iff.mpr hz.2
  have hκΩ : ∀ w, κ w ∈ Ω₀ := fun w => ⟨by rw [hκn]; exact hr2, by rw [hκn]; exact hr3⟩
  have hκb : ∀ w, κ w ∈ ball (0 : ℂ) 3 := fun w => hΩ₀b (hκΩ w)
  have hslit : ∀ w : Circle, (w : ℂ) ≠ -1 → κ w ∈ Complex.slitPlane := fun w hw => by
    have h1 := circle_mem_slitPlane hw
    rw [Complex.mem_slitPlane_iff] at h1 ⊢
    simp only [κ, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, add_zero]
    rcases h1 with h1 | h1
    · exact .inl (mul_pos hrpos h1)
    · exact .inr (mul_ne_zero hrpos.ne' h1)
  have hslit' : ∀ w : Circle, (w : ℂ) ≠ 1 → -κ w ∈ Complex.slitPlane := fun w hw => by
    have h1 : -κ w = κ (-w) := by
      simp [κ]
    rw [h1]
    refine hslit (-w) fun h => hw ?_
    simpa using h
  have ha₀ne : ∀ s, (a₀ s : ℂ) ≠ -1 := fun s he => by
    have h1 : a₀ s = Circle.exp Real.pi := Circle.ext (by simpa using he)
    rw [ha₀, ← Circle.exp_add] at h1
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h1
    have hs0 := s.2.1
    have hs1 := s.2.2
    have h2 : -τ ≤ -τ + s.1 * (2 * τ) := by nlinarith
    have h3 : -τ + s.1 * (2 * τ) ≤ τ := by nlinarith
    rcases le_or_gt 0 m with h | h
    · have h4 : (0 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith
    · have h4 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
      nlinarith
  have hb₀ne : ∀ s, (b₀ s : ℂ) ≠ 1 := fun s he => by
    have h1 : b₀ s = Circle.exp 0 := Circle.ext (by simpa using he)
    rw [hb₀, ← Circle.exp_add] at h1
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h1
    have hs0 := s.2.1
    have hs1 := s.2.2
    have hτ3 : 2 * τ ≤ 2 := by linarith
    have hlow : 2 * τ ≤ 2 * Real.pi - s.1 * (2 * Real.pi - 2 * τ) := by nlinarith
    have hup : 2 * Real.pi - s.1 * (2 * Real.pi - 2 * τ) ≤ 2 * Real.pi := by nlinarith
    rcases le_or_gt m 0 with h | h
    · have h4 : (m : ℝ) ≤ 0 := by exact_mod_cast h
      nlinarith
    · have h4 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      nlinarith
  let a : 𝕀 → S := fun s => g (κ (a₀ s))
  let b : 𝕀 → S := fun s => g (κ (b₀ s))
  have hgκc : Continuous fun w => g (κ w) := c.gc.comp_continuous hκc hκb
  have hgκi : Function.Injective fun w => g (κ w) := fun w w' he =>
    hκi (c.hg.injOn.eq_iff (hκb w) (hκb w') |>.mp he)
  have ha : IsArcMap a := ⟨hgκc.comp hab.1.1, hgκi.comp hab.1.2⟩
  have hb : IsArcMap b := ⟨hgκc.comp hab.2.1, hgκi.comp hab.2.2⟩
  have hp0 : κ (a₀ 0) = (r : ℂ) * Complex.exp (-τ * Complex.I) := by
    simp only [κ, ha₀, Set.Icc.coe_zero, zero_mul, ← Circle.exp_add, Circle.coe_exp]
    congr 2
    push_cast
    ring
  have hq0 : κ (a₀ 1) = (r : ℂ) * Complex.exp (τ * Complex.I) := by
    simp only [κ, ha₀, Set.Icc.coe_one, one_mul, ← Circle.exp_add, Circle.coe_exp]
    congr 2
    push_cast
    ring
  have hnear : ∀ θ : ℝ, |θ| ≤ τ → (r : ℂ) * Complex.exp (θ * Complex.I) ∈ ball (r : ℂ) ρ := by
    intro θ hθ
    rw [mem_ball, dist_eq_norm]
    have h1 : (r : ℂ) * Complex.exp (θ * Complex.I) - r = r * (Complex.exp (θ * Complex.I) - 1)
      := by
      ring
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    have h2 : ‖Complex.exp (θ * Complex.I) - 1‖ ≤ ‖θ‖ := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)
      rwa [mul_comm] at this
    rw [Real.norm_eq_abs] at h2
    calc r * ‖Complex.exp (θ * Complex.I) - 1‖ ≤ r * τ :=
          mul_le_mul_of_nonneg_left (h2.trans hθ) hrpos.le
      _ < ρ := hτ2
  have hpG : ∀ γ ∈ G, g (κ (a₀ 0)) ∉ range γ := fun γ hγ => by
    rw [hp0]
    exact hfree _ (by simpa using hnear (-τ) (by rw [abs_neg, abs_of_pos hτ0])) γ hγ
  have hqG : ∀ γ ∈ G, g (κ (a₀ 1)) ∉ range γ := fun γ hγ => by
    rw [hq0]
    exact hfree _ (hnear τ (by rw [abs_of_pos hτ0])) γ hγ
  let Na : Set ℂ := Ω₀ ∩ Complex.slitPlane
  let Nb : Set ℂ := Ω₀ ∩ (fun z => -z) ⁻¹' Complex.slitPlane
  have hNa : IsOpen Na := hΩ₀.inter Complex.isOpen_slitPlane
  have hNb : IsOpen Nb := hΩ₀.inter (Complex.isOpen_slitPlane.preimage continuous_neg)
  have hNaS : IsOpen (g '' Na) := c.isOpen_image hNa fun z hz => hΩ₀b hz.1
  have hNbS : IsOpen (g '' Nb) := c.isOpen_image hNb fun z hz => hΩ₀b hz.1
  have haN : range a ⊆ g '' Na := by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, ⟨hκΩ _, hslit _ (ha₀ne s)⟩, rfl⟩
  have hbN : range b ⊆ g '' Nb := by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, ⟨hκΩ _, hslit' _ (hb₀ne s)⟩, rfl⟩
  obtain ⟨ε₁, hε₁, hth₁⟩ := (isCompact_range ha.1).exists_thickening_subset_open hNaS haN
  obtain ⟨ε₂, hε₂, hth₂⟩ := (isCompact_range hb.1).exists_thickening_subset_open hNbS hbN
  have hab' : IsTwoArcs a b := ⟨ha, hb, congrArg (fun w => g (κ w)) hab.3,
    congrArg (fun w => g (κ w)) hab.4, fun s t he => hab.5 s t (hgκi he)⟩
  obtain ⟨a', b', ha', hb', ha'0, ha'1, hb'0, hb'1, hm', hra, hrb, htame⟩ :=
    exists_tame_pair G hG ha hb hab'.3 hab'.4 hab'.5 hpG hqG (lt_min hε₁ hε₂)
  have hra' : range a' ⊆ g '' Na :=
    (hra.trans (thickening_mono (min_le_left _ _) _)).trans hth₁
  have hrb' : range b' ⊆ g '' Nb :=
    (hrb.trans (thickening_mono (min_le_right _ _) _)).trans hth₂
  set P : Set S := range a' ∪ range b' with hPdef
  have hPO : IsOArc P := oArc_of_two_arcs ha' hb' (ha'0.trans hb'0.symm) (ha'1.trans hb'1.symm) hm'
  have hPN : P ⊆ g '' Ω₀ := union_subset
    (hra'.trans (image_mono inter_subset_left)) (hrb'.trans (image_mono inter_subset_left))
  have hPU : P ⊆ U := hPN.trans (image_subset_iff.mpr fun z hz => c.gm (hΩ₀b hz))
  have hhP : ∀ x ∈ P, h x ∈ Ω₀ := fun x hx => by
    obtain ⟨z, hz, rfl⟩ := hPN hx
    rwa [c.hg (hΩ₀b hz)]
  have hQ : IsOArc (h '' P) :=
    hPO.image (c.hc.mono hPU) (c.gc.mono fun z hz => by
      obtain ⟨x, hx, rfl⟩ := hz
      exact hΩ₀b (hhP x hx)) (c.gh.mono hPU)
  have hlog : ¬ HasLogOn (h '' P) fun z => z := by
    have hAc : IsPreconnected (h '' range a') := (isPreconnected_range ha'.1).image _
      (c.hc.mono (subset_union_left.trans hPU))
    have hBc : IsPreconnected (h '' range b') := (isPreconnected_range hb'.1).image _
      (c.hc.mono (subset_union_right.trans hPU))
    have hp' : h (a' 0) = (r : ℂ) * Complex.exp (-τ * Complex.I) := by
      rw [ha'0]
      change h (g (κ (a₀ 0))) = _
      rw [c.hg (hκb _), hp0]
    have hq' : h (a' 1) = (r : ℂ) * Complex.exp (τ * Complex.I) := by
      rw [ha'1]
      change h (g (κ (a₀ 1))) = _
      rw [c.hg (hκb _), hq0]
    have := not_hasLogOn_of_two_sides hAc hBc (ρ := r) (τ := τ) ?_ ?_ hrpos ⟨hτ0, by linarith⟩
      hp' hq' ⟨_, ⟨0, rfl⟩, rfl⟩ ⟨_, ⟨1, rfl⟩, rfl⟩ ⟨_, ⟨0, rfl⟩, ?_⟩ ⟨_, ⟨1, rfl⟩, ?_⟩
    · rwa [hPdef, image_union]
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hra' hx
      rw [c.hg (hΩ₀b hz.1)]
      exact hz.2
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hrb' hx
      rw [c.hg (hΩ₀b hz.1)]
      exact hz.2
    · rw [hb'0, ha'0]
    · rw [hb'1, ha'1]
  obtain ⟨hin, hsub3⟩ := closedBall_subset_inner hQ (Set.disjoint_left.mpr fun z hz hz' => by
    obtain ⟨x, hx, rfl⟩ := hz
    have h1 := (hhP x hx).1
    have h2 : ‖h x‖ ≤ 2 := mem_closedBall_zero_iff.mp hz'
    linarith) (fun z hz => by
    obtain ⟨x, hx, rfl⟩ := hz
    exact hΩ₀b (hhP x hx)) hlog
  obtain ⟨hdQ, hdQb⟩ := isClosedDisc_closedInner hQ
  obtain ⟨hE, hEb⟩ := c.image_disc hdQ hsub3
  have hgP : g '' (h '' P) = P := by
    rw [image_image]
    exact (image_congr fun x hx => c.gh (hPU hx)).trans (image_id _)
  rw [hdQb, hgP] at hEb
  set E := g '' closedInner (h '' P) with hEdef
  have hEU : E ⊆ U := image_subset_iff.mpr fun z hz => c.gm (hsub3 hz)
  have hclosedin : g '' closedBall 0 2 ⊆ E := image_mono (hin.trans subset_union_left)
  have hb2 : closedBall (0 : ℂ) 2 ⊆ ball 0 3 := closedBall_subset_ball (by norm_num)
  refine ⟨P, E, hPO, htame, hE, hEb, hclosedin, hEU, Set.disjoint_left.mpr ?_⟩
  rintro x hx ⟨z, hz, rfl⟩
  have h1 := (hhP _ hx).1
  rw [c.hg (hb2 hz)] at h1
  have h2 : ‖z‖ ≤ 2 := mem_closedBall_zero_iff.mp hz
  linarith

/-- The heart of `exists_disc_merge`, when the chart has a small ball around a point `r` of the
positive real axis that misses the boundary of the disc. -/
theorem exists_disc_merge_aux [CompactSpace S] [T2Space S] [ConnectedSpace S]
    (hint : ∀ x : S, IsInteriorPoint x) {Y : Set S}
    (H : ∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    (hns : ¬ (IsSphere S ∧ Y = univ)) {D : Set S} (hDY : D ⊆ Y) (hD : IsClosedDisc D)
    {U : Set S} {h : S → ℂ} {g : ℂ → S} (c : BallChart 3 U h g) (hUY : U ⊆ Y)
    (hz : (discInt D ∩ g '' ball 0 1).Nonempty) {r ρ : ℝ} (hr2 : 2 < r) (hr3 : r < 3) (hρ : 0 < ρ)
    (hfree : ∀ z ∈ ball (r : ℂ) ρ, g z ∉ discBd D) :
    ∃ D' : Set S, D' ⊆ Y ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ g '' closedBall 0 2 ⊆ D' := by
  classical
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hint x).isManifoldPoint
  -- the boundary of `D` as two arcs
  have hG := hD.isOArc_discBd
  obtain ⟨φG⟩ := id hG
  have hne : (φG 1).1 ≠ (φG (Circle.exp Real.pi)).1 := fun he => by
    have h1 := φG.injective (Subtype.ext he)
    have h2 := congrArg (fun w : Circle => (w : ℂ)) h1
    simp at h2
    norm_num at h2
  obtain ⟨α, β, hαβ, -, -, hr⟩ := hG.exists_arcs (φG 1).2 (φG _).2 hne
  obtain ⟨P, E, hPO, htame, hE, hEb, hclosedin, hEU, -⟩ := exists_tame_curve hman c [α, β]
    (by simpa using ⟨hαβ.1, hαβ.2⟩) hr2 hr3 hρ fun z hz γ hγ h1 => hfree z hz (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl
      · exact hr ▸ subset_union_left h1
      · exact hr ▸ subset_union_right h1)
  have hPU : P ⊆ U := (hEb ▸ discBd_subset E).trans hEU
  have hPY : P ⊆ Y := hPU.trans hUY
  have hb2 : closedBall (0 : ℂ) 2 ⊆ ball 0 3 := closedBall_subset_ball (by norm_num)
  by_cases h2 : ∃ x y, x ∈ P ∧ y ∈ P ∧ x ∈ D ∧ y ∈ D ∧ x ≠ y
  · obtain ⟨x, y, hxP, hyP, hxD, hyD, hxy⟩ := h2
    have hU2 : (⋃ g' ∈ [α, β], range g') = discBd D := by
      rw [← hr]
      simp
    rw [hU2] at htame
    obtain ⟨F, hFf, hFc, hFu⟩ := htame
    let F₂ : Set (Set S) := {J ∈ F | Disjoint J D}
    have hF₂ : ⋃₀ F₂ = P \ D := by
      ext w
      constructor
      · rintro ⟨J, ⟨hJ, hJD⟩, hw⟩
        have h3 : w ∈ P \ discBd D := hFu ▸ mem_sUnion_of_mem hw hJ
        exact ⟨h3.1, fun h4 => Set.disjoint_left.mp hJD hw h4⟩
      · rintro ⟨hwP, hwD⟩
        have h3 : w ∈ P \ discBd D := ⟨hwP, fun h4 => hwD (discBd_subset D h4)⟩
        rw [← hFu] at h3
        obtain ⟨J, hJ, hwJ⟩ := h3
        have hJb : Disjoint J (discBd D) := by
          rw [Set.disjoint_left]
          intro v hv hv'
          have : v ∈ P \ discBd D := hFu ▸ mem_sUnion_of_mem hv hJ
          exact this.2 hv'
        rcases hD.side hman (hFc J hJ) hJb with h4 | h4
        · exact absurd (h4 hwJ).1 hwD
        · exact ⟨J, ⟨hJ, h4⟩, hwJ⟩
    obtain ⟨D', hD'Y, hD', hDD', hPD'⟩ := exists_disc_cover hman H hPY hPO hxP hyP hxy _ D F₂ hDY hD
      hxD hyD (hFf.subset fun J hJ => hJ.1) le_rfl (fun J hJ => hFc J hJ.1) hF₂
    obtain ⟨Δ, ⟨hΔD, hΔ, hΔb, -⟩, -⟩ := disc_oArc.{u} D' P hD' hPD' hPO
    have hS : IsSurface S := ⟨inferInstance, inferInstance, hman⟩
    by_cases hEΔ : E = Δ
    · exact ⟨D', hD'Y, hD', hDD', hclosedin.trans (hEΔ ▸ hΔD)⟩
    · exfalso
      have hsph : IsSphere S := by
        by_contra hns'
        exact hEΔ (eq_of_discBd_eq hS hns' hE hΔ (hEb.trans hΔb.symm))
      obtain ⟨Δ₁, Δ₂, -, -, -, -, -, hu, -, -, huniq⟩ := sphere_disc.{u} S hsph P hPO
      have hY : Y = univ := by
        rw [eq_univ_iff_forall]
        intro w
        have hw : w ∈ Δ₁ ∪ Δ₂ := hu ▸ mem_univ w
        have hEY : E ⊆ Y := hEU.trans hUY
        have hΔY : Δ ⊆ Y := hΔD.trans hD'Y
        rcases huniq E hE hEb with h3 | h3 <;> rcases huniq Δ hΔ hΔb with h4 | h4
        · exact absurd (h3.trans h4.symm) hEΔ
        · rcases hw with hw | hw
          · exact hEY (h3 ▸ hw)
          · exact hΔY (h4 ▸ hw)
        · rcases hw with hw | hw
          · exact hΔY (h4 ▸ hw)
          · exact hEY (h3 ▸ hw)
        · exact absurd (h3.trans h4.symm) hEΔ
      exact hns ⟨hsph, hY⟩
  · push Not at h2
    have hdisj : Disjoint (discInt D) P := by
      rw [Set.disjoint_left]
      intro x hx hxP
      have hopen : IsOpen ({x}ᶜ : Set S) := isOpen_compl_singleton
      have hother : ∃ w ∈ P, w ≠ x := by
        obtain ⟨φP⟩ := id hPO
        by_cases h3 : (φP 1).1 = x
        · refine ⟨(φP (Circle.exp Real.pi)).1, (φP _).2, fun h4 => ?_⟩
          have h5 := φP.injective (Subtype.ext (h4.trans h3.symm))
          have h6 := congrArg (fun w : Circle => (w : ℂ)) h5
          simp at h6
          norm_num at h6
        · exact ⟨_, (φP 1).2, h3⟩
      obtain ⟨w, hwP, hwx⟩ := hother
      obtain ⟨v, hvP, hv1, hv2⟩ := hPO.isPreconnected _ _ (hD.isOpen_discInt hman) hopen
        (fun y _ => by
          by_cases h3 : y = x
          · exact .inl (h3 ▸ hx)
          · exact .inr h3) ⟨x, hxP, hx⟩ ⟨w, hwP, hwx⟩
      exact hv2 (h2 x v hxP hvP hx.1 hv1.1).symm
    obtain ⟨z, hzD, w, hw, rfl⟩ := hz
    have hwin : w ∈ closedBall (0 : ℂ) 2 :=
      closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hw)
    have hbdE : Disjoint (discInt D) (discBd E) := hEb ▸ hdisj
    rcases hE.side hman hD.isPreconnected_discInt hbdE with h3 | h3
    · refine ⟨E, hEU.trans hUY, hE, ?_, hclosedin⟩
      exact hD.subset_closure_discInt.trans
        (closure_minimal (h3.trans (discInt_subset E)) hE.isClosed)
    · exact absurd (hclosedin ⟨w, hwin, rfl⟩) (Set.disjoint_left.mp h3 hzD)

/-- **Merging.** A closed disc of `Y` and a chart in `Y` that overlap it: the round disc of radius
`2`
of the chart and the closed disc lie in a common closed disc of `Y`, unless `Y` is a whole sphere.
See
the module docstring. -/
theorem exists_disc_merge [CompactSpace S] [T2Space S] [ConnectedSpace S]
    (hint : ∀ x : S, IsInteriorPoint x) {Y : Set S}
    (H : ∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    (hns : ¬ (IsSphere S ∧ Y = univ)) {D : Set S} (hDY : D ⊆ Y) (hD : IsClosedDisc D)
    {U : Set S} {h : S → ℂ} {g : ℂ → S} (c : BallChart 3 U h g) (hUY : U ⊆ Y)
    (hz : (discInt D ∩ g '' ball 0 1).Nonempty) :
    ∃ D' : Set S, D' ⊆ Y ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ g '' closedBall 0 2 ⊆ D' := by
  have hG := hD.isOArc_discBd
  let Ω₀ : Set ℂ := {z | 2 < ‖z‖ ∧ ‖z‖ < 3}
  have hΩ₀ : IsOpen Ω₀ := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hΩ₀b : Ω₀ ⊆ ball 0 3 := fun z hz => mem_ball_zero_iff.mpr hz.2
  -- a point of the annulus off the boundary of `D`
  have hex : ∃ w ∈ Ω₀, g w ∉ discBd D := by
    by_contra hcon
    push Not at hcon
    have hball : ball ((5 / 2 : ℝ) : ℂ) (1 / 4) ⊆ Ω₀ := fun z hz => by
      have h1 : ‖z - ((5 / 2 : ℝ) : ℂ)‖ < 1 / 4 := by rwa [mem_ball, dist_eq_norm] at hz
      have h2 : ‖((5 / 2 : ℝ) : ℂ)‖ = 5 / 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      have h3 := norm_sub_norm_le z ((5 / 2 : ℝ) : ℂ)
      have h4 := norm_sub_norm_le ((5 / 2 : ℝ) : ℂ) z
      rw [norm_sub_rev ((5 / 2 : ℝ) : ℂ) z] at h4
      exact ⟨by linarith, by linarith⟩
    refine not_image_ball_subset_oArc hG (by norm_num) (g := g)
      (c.gc.mono (hball.trans hΩ₀b)) (c.hg.injOn.mono (hball.trans hΩ₀b)) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hcon z (hball hz)
  obtain ⟨w, hwΩ, hwG⟩ := hex
  have : T2Space S := inferInstance
  have hopen : IsOpen (Ω₀ ∩ g ⁻¹' (discBd D)ᶜ) :=
    (c.gc.mono hΩ₀b).isOpen_inter_preimage hΩ₀ hG.isCompact.isClosed.isOpen_compl
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen w ⟨hwΩ, hwG⟩
  let u : Circle := Circle.exp (Complex.arg w)
  have huw : (u : ℂ) * (‖w‖ : ℝ) = w := by
    have := Complex.norm_mul_exp_arg_mul_I w
    rw [Circle.coe_exp, mul_comm]
    exact this
  have hcan : ∀ z : ℂ, (u : ℂ) * (((u⁻¹ : Circle) : ℂ) * z) = z := fun z => by
    rw [← mul_assoc, ← Circle.coe_mul]
    simp
  have hmulball : ∀ {t : ℝ} {z : ℂ}, z ∈ ball (0 : ℂ) t → ((u⁻¹ : Circle) : ℂ) * z ∈ ball (0 : ℂ) t
    :=
    fun hz => by simpa [norm_mul] using hz
  have hmulcl : ∀ {t : ℝ} {z : ℂ}, z ∈ closedBall (0 : ℂ) t →
      ((u⁻¹ : Circle) : ℂ) * z ∈ closedBall (0 : ℂ) t :=
    fun hz => by simpa [norm_mul] using hz
  obtain ⟨D', h1, h2, h3, h4⟩ := exists_disc_merge_aux hint H hns hDY hD (c.rotate u) hUY
    (by
      obtain ⟨x, hx, z, hz, rfl⟩ := hz
      refine ⟨g z, hx, ((u⁻¹ : Circle) : ℂ) * z, hmulball hz, ?_⟩
      change g ((u : ℂ) * (((u⁻¹ : Circle) : ℂ) * z)) = g z
      rw [hcan])
    (r := ‖w‖) (ρ := ρ) hwΩ.1 hwΩ.2 hρ (fun z hz => by
      show g ((u : ℂ) * z) ∉ discBd D
      refine (hball ?_).2
      rw [mem_ball, ← huw, dist_eq_norm, ← mul_sub, norm_mul, Circle.norm_coe, one_mul,
        ← dist_eq_norm]
      exact hz)
  refine ⟨D', h1, h2, h3, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have := h4 ⟨((u⁻¹ : Circle) : ℂ) * z, hmulcl hz, rfl⟩
  simpa only [hcan] using this

end GraphMinor.Surface
