/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Crossing
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import LeanPool.GraphMinor.Surface.ArcInPath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Domains bounded by an `O`-arc

Let `F` be an `O`-arc in the complex plane. This file proves what the proof of the Schoenflies
theorem needs about the two components of the complement.

* `exists_small_connector`: two nearby points in one component of the complement of `F` are joined
  inside that component by a small connected set. This is *uniform local connectivity*. If the
  segment between the points misses `F`, take the segment. Otherwise cut `F` into a small arc `A`
  near the segment and a far arc `A'`, and let `E` be a small circle around the segment. Then
  `(z - y) / (z - x)` has a logarithm on `F`, because the points lie in one component, and a
  logarithm on `A' ∪ E`, because the segment joins them. The two differ by a constant on the
  connected set `A'`, so they paste to a logarithm on `F ∪ E`, and Eilenberg's criterion joins the
  points off `F ∪ E`, so inside the circle.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Complex

/-- The points of an `O`-arc at parameter `θ` from the point at parameter `t`. -/
noncomputable def arcPoint {F : Set ℂ} (φ : Circle ≃ₜ F) (t : Circle) (θ : ℝ) : ℂ :=
  (φ (t * Circle.exp θ)).1

theorem continuous_arcPoint {F : Set ℂ} (φ : Circle ≃ₜ F) :
    Continuous fun p : Circle × ℝ => arcPoint φ p.1 p.2 := by
  unfold arcPoint
  have : Continuous fun p : Circle × ℝ => p.1 * Circle.exp p.2 := by
    exact continuous_fst.mul (Circle.exp.continuous.comp continuous_snd)
  exact continuous_subtype_val.comp (φ.continuous.comp this)

/-- Every point of the circle is `t * exp θ` with `θ` in `[-η, 2π - η)`. -/
theorem exists_angle_near (t s : Circle) (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ Real.pi) :
    ∃ θ : ℝ, -η ≤ θ ∧ θ ≤ 2 * Real.pi - η ∧ s = t * Circle.exp θ := by
  set a := (t⁻¹ * s) with ha
  have hrep : t⁻¹ * s = Circle.exp (Complex.arg (a : ℂ)) := (Circle.exp_arg a).symm
  have hs : s = t * Circle.exp (Complex.arg (a : ℂ)) := by
    rw [← hrep]
    group
  by_cases h : -η ≤ Complex.arg (a : ℂ)
  · refine ⟨Complex.arg (a : ℂ), h, ?_, hs⟩
    linarith [Complex.arg_le_pi (a : ℂ)]
  · rw [not_le] at h
    refine ⟨Complex.arg (a : ℂ) + 2 * Real.pi, by linarith [Complex.neg_pi_lt_arg (a : ℂ)],
      by linarith, ?_⟩
    rw [Circle.exp_add, Circle.exp_two_pi, mul_one]
    exact hs

/-- Near parameters give near points of the arc, uniformly. Far parameters give far points. -/
theorem exists_arc_constants {F : Set ℂ} (φ : Circle ≃ₜ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ η ρ : ℝ, 0 < η ∧ η < Real.pi ∧ 0 < ρ ∧
      (∀ t θ, |θ| ≤ η → dist (arcPoint φ t θ) (arcPoint φ t 0) < ε) ∧
      (∀ t θ, θ ∈ Icc η (2 * Real.pi - η) → ρ ≤ dist (arcPoint φ t θ) (arcPoint φ t 0)) := by
  have hunif : UniformContinuous fun s : Circle => (φ s).1 :=
    CompactSpace.uniformContinuous_of_continuous (continuous_subtype_val.comp φ.continuous)
  obtain ⟨η₀, hη₀, hη⟩ := Metric.uniformContinuous_iff.mp hunif ε hε
  set η := min (η₀ / 2) 1 with hηdef
  have hηpos : 0 < η := lt_min (by positivity) one_pos
  have hηpi : η < Real.pi := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.two_le_pi])
  have hηle : η < η₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hcomp : IsCompact ((univ : Set Circle) ×ˢ Icc η (2 * Real.pi - η)) :=
    isCompact_univ.prod isCompact_Icc
  have hne : ((univ : Set Circle) ×ˢ Icc η (2 * Real.pi - η)).Nonempty :=
    ⟨(1, η), mem_univ _, by constructor <;> linarith [Real.two_le_pi]⟩
  let G : Circle × ℝ → ℝ := fun p => dist (arcPoint φ p.1 p.2) (arcPoint φ p.1 0)
  have hG : Continuous G := by
    have h1 := continuous_arcPoint φ
    have h2 : Continuous fun p : Circle × ℝ => arcPoint φ p.1 0 :=
      h1.comp (continuous_fst.prodMk continuous_const)
    exact h1.dist h2
  obtain ⟨p, hp, hmin⟩ := hcomp.exists_isMinOn hne hG.continuousOn
  have hpos : 0 < G p := by
    rw [dist_pos]
    intro heq
    have hinj := φ.injective (Subtype.ext heq)
    have h1 : Circle.exp p.2 = 1 := by
      have : p.1 * Circle.exp p.2 = p.1 * Circle.exp 0 := hinj
      simpa using this
    have hθ := hp.2
    have h2 : Circle.exp p.2 = Circle.exp 0 := by simpa using h1
    rw [Circle.exp_eq_exp] at h2
    obtain ⟨m, hm⟩ := h2
    have hle : ((m : ℝ)) * (2 * Real.pi) = p.2 := by linarith
    have hm0 : (0 : ℝ) < m := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [hθ.1, Real.pi_pos]
    have hm1 : (m : ℝ) < 1 := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [hθ.2, Real.pi_pos]
    have h3 : 0 < m := by exact_mod_cast hm0
    have h4 : m < 1 := by exact_mod_cast hm1
    omega
  refine ⟨η, G p, hηpos, hηpi, hpos, fun t θ hθ => ?_, fun t θ hθ => ?_⟩
  · refine hη ?_
    have : dist (t * Circle.exp θ) (t * Circle.exp 0) ≤ |θ| := by
      rw [Circle.exp_zero, mul_one]
      change dist ((t * Circle.exp θ : Circle) : ℂ) (t : ℂ) ≤ |θ|
      have h1 : ((t * Circle.exp θ : Circle) : ℂ) - (t : ℂ) = t * (exp (I * θ) - 1) := by
        rw [Circle.coe_mul, Circle.coe_exp]
        ring_nf
      rw [dist_eq_norm, h1, norm_mul, Circle.norm_coe, one_mul]
      exact Real.norm_exp_I_mul_ofReal_sub_one_le
    exact lt_of_le_of_lt this (lt_of_le_of_lt hθ hηle)
  · exact isMinOn_iff.mp hmin (t, θ) ⟨mem_univ t, hθ⟩

/-- **Uniform local connectivity.** Nearby points in one component of the complement of an `O`-arc
are joined in the complement by a small connected set. -/
theorem exists_small_connector {F : Set ℂ} (φ : Circle ≃ₜ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℂ, x ∉ F → y ∉ F → y ∈ connectedComponentIn Fᶜ x → dist x y < δ →
      ∃ C : Set ℂ, IsPathConnected C ∧ C ⊆ Fᶜ ∧ x ∈ C ∧ y ∈ C ∧ C ⊆ ball x ε := by
  obtain ⟨η, ρ, hη, hηπ, hρ, hnear, hfar⟩ := exists_arc_constants φ (half_pos hε)
  refine ⟨min ρ (ε / 2), lt_min hρ (half_pos hε), fun x y hx hy hxy hdist => ?_⟩
  have hδρ : dist x y < ρ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hδε : dist x y < ε / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
  by_cases hseg : Disjoint (segment ℝ x y) F
  · refine ⟨segment ℝ x y, (convex_segment x y).isPathConnected ⟨x, left_mem_segment ℝ x y⟩, ?_,
      left_mem_segment ℝ x y, right_mem_segment ℝ x y, ?_⟩
    · exact fun z hz hzF => Set.disjoint_left.mp hseg hz hzF
    · refine (convex_ball x ε).segment_subset (mem_ball_self hε) ?_
      rw [mem_ball']
      linarith
  obtain ⟨u, huseg, huF⟩ := not_disjoint_iff.mp hseg
  have hFc : IsCompact F := isCompact_of_oArc φ
  let t : Circle := φ.symm ⟨u, huF⟩
  have hut : arcPoint φ t 0 = u := by
    simp [arcPoint, t]
  have hthetac : Continuous fun θ : ℝ => arcPoint φ t θ :=
    (continuous_arcPoint φ).comp (continuous_const.prodMk continuous_id)
  set A := (fun θ : ℝ => arcPoint φ t θ) '' Icc (-η) η with hA
  set A' := (fun θ : ℝ => arcPoint φ t θ) '' Icc η (2 * Real.pi - η) with hA'
  have hAc : IsCompact A := isCompact_Icc.image hthetac
  have hA'c : IsCompact A' := isCompact_Icc.image hthetac
  have hcover : F = A ∪ A' := by
    ext z
    constructor
    · intro hz
      obtain ⟨θ, h1, h2, h3⟩ := exists_angle_near t (φ.symm ⟨z, hz⟩) η hη.le hηπ.le
      have hzθ : arcPoint φ t θ = z := by
        simp [arcPoint, ← h3]
      by_cases hθ : θ ≤ η
      · exact Or.inl ⟨θ, ⟨h1, hθ⟩, hzθ⟩
      · exact Or.inr ⟨θ, ⟨(not_le.mp hθ).le, h2⟩, hzθ⟩
    · rintro (⟨θ, -, rfl⟩ | ⟨θ, -, rfl⟩) <;> exact (φ _).2
  have hAball : A ⊆ ball u (ε / 2) := by
    rintro _ ⟨θ, hθ, rfl⟩
    rw [mem_ball, ← hut]
    exact hnear t θ (abs_le.mpr hθ)
  have hA'far : ∀ z ∈ A', ρ ≤ dist z u := by
    rintro _ ⟨θ, hθ, rfl⟩
    rw [← hut]
    exact hfar t θ hθ
  have hxu : dist x u ≤ dist x y := by
    have h := (convex_closedBall x (dist x y)).segment_subset
      (mem_closedBall_self dist_nonneg) (mem_closedBall'.mpr le_rfl) huseg
    exact mem_closedBall'.mp h
  have hyu : dist y u ≤ dist x y := by
    have h := (convex_closedBall y (dist x y)).segment_subset
      (mem_closedBall.mpr le_rfl) (mem_closedBall_self dist_nonneg) huseg
    exact mem_closedBall'.mp h
  have hsegball : segment ℝ x y ⊆ ball u (dist x y + (min ρ (ε / 2) - dist x y) / 2) := by
    have hgap : 0 < min ρ (ε / 2) - dist x y := by linarith
    refine (convex_ball _ _).segment_subset ?_ ?_ <;> rw [mem_ball] <;> linarith
  have hsegmin : ∀ w ∈ segment ℝ x y, dist w u < min ρ (ε / 2) := by
    intro w hw
    have := mem_ball.mp (hsegball hw)
    linarith
  set E := sphere u (ε / 2) with hE
  have hEc : IsCompact E := isCompact_sphere u _
  set K := A' ∪ E with hK
  have hKc : IsCompact K := hA'c.union hEc
  have hsegK : segment ℝ x y ⊆ Kᶜ := by
    rintro w hw (h | h)
    · linarith [hA'far w h, hsegmin w hw, min_le_left ρ (ε / 2)]
    · have h' : dist w u = ε / 2 := h
      linarith [hsegmin w hw, min_le_right ρ (ε / 2)]
  have hxseg := left_mem_segment ℝ x y
  have hyseg := right_mem_segment ℝ x y
  have hyK : y ∈ connectedComponentIn Kᶜ x :=
    (convex_segment x y).isPreconnected.subset_connectedComponentIn hxseg hsegK hyseg
  obtain ⟨l₂, hl₂c, hl₂⟩ := hasLogOn_div_of_same_component hKc.isClosed (hsegK hxseg) hyK
  obtain ⟨l₁, hl₁c, hl₁⟩ := hasLogOn_div_of_same_component hFc.isClosed hx hxy
  have hA'F : A' ⊆ F := by rw [hcover]; exact subset_union_right
  have hAF : A ⊆ F := by rw [hcover]; exact subset_union_left
  have hA'pre : IsPreconnected A' := isPreconnected_Icc.image _ hthetac.continuousOn
  have hexp : ∀ z ∈ A', exp (l₂ z - l₁ z) = 1 := by
    intro z hz
    have h1 := hl₁ z (hA'F hz)
    have h2 := hl₂ z (Or.inl hz)
    rw [exp_sub, ← h1, ← h2]
    refine div_self ?_
    rw [h1]
    exact exp_ne_zero _
  have hdiff : ContinuousOn (fun z => l₂ z - l₁ z) A' :=
    (hl₂c.mono subset_union_left).sub (hl₁c.mono hA'F)
  have hp : arcPoint φ t η ∈ A' := ⟨η, ⟨le_rfl, by linarith⟩, rfl⟩
  set k := l₂ (arcPoint φ t η) - l₁ (arcPoint φ t η) with hk
  have hkexp : exp k = 1 := hexp _ hp
  have hlogU : HasLogOn (A ∪ K) fun z => (z - y) / (z - x) := by
    refine hasLogOn_union (gA := fun z => l₁ z + k) (gB := l₂) hAc.isClosed hKc.isClosed
      ((hl₁c.mono hAF).add continuousOn_const) hl₂c (fun z hz => ?_) hl₂ ?_
    · rw [exp_add, hkexp, mul_one]
      exact hl₁ z (hAF hz)
    · rintro z ⟨hzA, hzK⟩
      have hzA' : z ∈ A' := by
        rcases hzK with h | h
        · exact h
        · have h' : dist z u = ε / 2 := h
          exact absurd (mem_ball.mp (hAball hzA)) (by linarith)
      have := eq_of_exp_eq_one hA'pre hdiff hexp hzA' hp
      linear_combination -this
  have hUc : IsCompact (A ∪ K) := hAc.union hKc
  have hset : A ∪ K = F ∪ E := by rw [hK, ← union_assoc, ← hcover]
  rw [hset] at hlogU hUc
  have hxU : x ∉ F ∪ E := fun h => h.elim hx fun h' => hsegK hxseg (Or.inr h')
  have hyU : y ∉ F ∪ E := fun h => h.elim hy fun h' => hsegK hyseg (Or.inr h')
  have hcomp := component_eq_of_hasLogOn hUc hxU hyU
    (hlogU.inv.congr fun z _ => by rw [inv_div])
  have hyin : y ∈ connectedComponentIn (F ∪ E)ᶜ x := hcomp ▸ mem_connectedComponentIn hyU
  have hxin : x ∈ connectedComponentIn (F ∪ E)ᶜ x := mem_connectedComponentIn hxU
  refine ⟨connectedComponentIn (F ∪ E)ᶜ x,
    (isOpen_component hUc.isClosed x).isConnected_iff_isPathConnected.mp
      (isConnected_connectedComponentIn_iff.mpr hxU), ?_, hxin, hyin, ?_⟩
  · exact fun z hz hzF => connectedComponentIn_subset _ _ hz (Or.inl hzF)
  · intro z hz
    have hball : z ∈ ball u (ε / 2) := by
      by_contra hout
      obtain ⟨w, hw1, hw2⟩ := inter_frontier_nonempty_of_isPreconnected (U := ball u (ε / 2))
        (isPreconnected_connectedComponentIn (F := (F ∪ E)ᶜ) (x := x))
        ⟨x, hxin, by rw [mem_ball]; linarith⟩ ⟨z, hz, hout⟩
      exact connectedComponentIn_subset _ _ hw1 (Or.inr (frontier_ball_subset_sphere hw2))
    rw [mem_ball] at hball ⊢
    have := dist_triangle z u x
    rw [dist_comm u x] at this
    linarith

local notation "𝕀" => unitInterval

/-- A sequence of paths, each starting where the last one ends, that tends to a point `L` joins to
a single path ending at `L`. -/
theorem exists_path_of_tendsto {p : ℕ → 𝕀 → ℂ} (hp : ∀ n, Continuous (p n))
    (hlink : ∀ n, p n 1 = p (n + 1) 0) {L : ℂ} {r : ℕ → ℝ} (hr : Filter.Tendsto r Filter.atTop
      (𝓝 0))
    (hclose : ∀ n t, dist (p n t) L ≤ r n) :
    ∃ γ : 𝕀 → ℂ, Continuous γ ∧ γ 0 = p 0 0 ∧ γ 1 = L ∧ ∀ t, t ≠ 1 → ∃ n s, γ t = p n s := by
  classical
  let p' : ℕ → ℝ → ℂ := fun n s => p n (projIcc 0 1 zero_le_one s)
  have hp'c : ∀ n, Continuous (p' n) := fun n => (hp n).comp continuous_projIcc
  have hp'0 : ∀ n, p' n 0 = p n 0 := fun n => by
    simp only [p', projIcc_left]
    rfl
  have hp'1 : ∀ n, p' n 1 = p n 1 := fun n => by
    simp only [p', projIcc_right]
    rfl
  let Γ : ℝ → ℂ := fun s => p' ⌊s⌋₊ (s - ⌊s⌋₊)
  have hstep : ∀ n : ℕ, ContinuousOn Γ (Icc (n : ℝ) (n + 1)) := by
    intro n
    have hc : ContinuousOn (fun s : ℝ => p' n (s - n)) (Icc (n : ℝ) (n + 1)) :=
      ((hp'c n).comp (continuous_id.sub continuous_const)).continuousOn
    refine hc.congr fun s hs => ?_
    rcases eq_or_lt_of_le hs.2 with h | h
    · have hfl : ⌊s⌋₊ = n + 1 := by
        rw [h]
        exact_mod_cast Nat.floor_natCast (R := ℝ) (n + 1)
      simp only [Γ, hfl]
      rw [h]
      push_cast
      rw [show (n : ℝ) + 1 - (n + 1) = 0 by ring, show (n : ℝ) + 1 - n = 1 by ring, hp'0, hp'1,
        hlink]
    · have hfl : ⌊s⌋₊ = n := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg n) hs.1)).mpr ⟨hs.1, h⟩
      simp only [Γ, hfl]
  have hIic : ∀ N : ℕ, ContinuousOn Γ (Iic (N : ℝ)) := by
    intro N
    induction N with
    | zero =>
      have hc : ContinuousOn Γ (Iic (0 : ℝ)) :=
        (continuousOn_const (c := p 0 0)).congr fun s hs => by
          have hs' : s ≤ 0 := hs
          simp only [Γ, Nat.floor_of_nonpos hs', Nat.cast_zero, sub_zero, p']
          rw [projIcc_of_le_left _ hs']
          rfl
      simpa using hc
    | succ N ih =>
      have heq : Iic ((N + 1 : ℕ) : ℝ) = Iic (N : ℝ) ∪ Icc (N : ℝ) (N + 1) := by
        push_cast
        exact (Iic_union_Icc_eq_Iic (by linarith)).symm
      rw [heq]
      exact ih.union_of_isClosed (hstep N) isClosed_Iic isClosed_Icc
  have hΓ : Continuous Γ := by
    rw [continuous_iff_continuousAt]
    intro s
    obtain ⟨N, hN⟩ := exists_nat_gt s
    exact (hIic N).continuousAt (Iic_mem_nhds hN)
  have hΓclose : ∀ s, dist (Γ s) L ≤ r ⌊s⌋₊ := fun s => hclose _ _
  let γ : 𝕀 → ℂ := fun t => if (t : ℝ) < 1 then Γ ((t : ℝ) / (1 - t)) else L
  have hγlt : ∀ t : 𝕀, (t : ℝ) < 1 → γ t = Γ ((t : ℝ) / (1 - t)) := fun t ht => by
    simp only [γ, ht, ite_true]
  have hγ1 : γ 1 = L := by
    simp [γ]
  refine ⟨γ, ?_, ?_, hγ1, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : (t : ℝ) < 1
    · have hev : ∀ᶠ u : 𝕀 in 𝓝 t, γ u = Γ ((u : ℝ) / (1 - u)) := by
        have : IsOpen {u : 𝕀 | (u : ℝ) < 1} := isOpen_lt continuous_subtype_val continuous_const
        filter_upwards [this.mem_nhds ht] with u hu using hγlt u hu
      refine ContinuousAt.congr ?_ (Filter.EventuallyEq.symm hev)
      have h1 : ContinuousAt (fun u : 𝕀 => (u : ℝ) / (1 - u)) t :=
        continuous_subtype_val.continuousAt.div (continuous_const.sub
          continuous_subtype_val).continuousAt
          (by linarith)
      exact hΓ.continuousAt.comp h1
    · have ht1 : t = 1 := Subtype.ext (le_antisymm t.2.2 (not_lt.mp ht))
      subst ht1
      rw [Metric.continuousAt_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp hr).2 ε hε)
      have hNpos : (0 : ℝ) < N + 1 := by positivity
      refine ⟨1 / (N + 1), by positivity, fun u hu => ?_⟩
      rw [hγ1]
      by_cases hu1 : (u : ℝ) < 1
      · rw [hγlt u hu1]
        have hd : 1 - (u : ℝ) < 1 / (N + 1) := by
          have h2 : dist (u : ℝ) 1 < 1 / (N + 1) := hu
          rw [Real.dist_eq, abs_lt] at h2
          linarith [h2.1]
        have hpos : 0 < 1 - (u : ℝ) := by linarith
        have hs : (N : ℝ) ≤ (u : ℝ) / (1 - u) := by
          rw [le_div_iff₀ hpos]
          rw [lt_div_iff₀ hNpos] at hd
          nlinarith
        have hfl : N ≤ ⌊(u : ℝ) / (1 - u)⌋₊ := Nat.le_floor hs
        exact lt_of_le_of_lt (hΓclose _) (hN _ hfl)
      · have hu' : u = 1 := Subtype.ext (le_antisymm u.2.2 (not_lt.mp hu1))
        rw [hu', hγ1, dist_self]
        exact hε
  · rw [hγlt 0 (by simp)]
    simp only [Γ, Icc.coe_zero, zero_div, Nat.floor_zero, Nat.cast_zero, sub_zero, hp'0]
  · intro t ht
    have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h => ht (Subtype.ext h)
    exact ⟨_, _, hγlt t ht1⟩

/-- Each point of an `O`-arc is a limit of points of each component of the complement. -/
theorem subset_closure_component {F : Set ℂ} (φ : Circle ≃ₜ F) {x : ℂ} (hx : x ∉ F) :
    F ⊆ closure (connectedComponentIn Fᶜ x) := by
  obtain ⟨A, B, ⟨-, hcomp, hAf, hBf⟩, -, -⟩ := jordan_complex φ
  rw [← compl_eq_univ_sdiff] at hcomp
  have hx' : connectedComponentIn Fᶜ x ∈ componentsIn Fᶜ := mem_image_of_mem _ hx
  rw [hcomp] at hx'
  rcases hx' with h | h
  · rw [h]
    exact hAf.symm.subset.trans frontier_subset_closure
  · rw [mem_singleton_iff.mp h]
    exact hBf.symm.subset.trans frontier_subset_closure

/-- **Accessibility.** Every point of an `O`-arc is the end of a path that otherwise stays in a
given component of the complement. -/
theorem exists_path_to_boundary {F : Set ℂ} (φ : Circle ≃ₜ F) {x p : ℂ} (hx : x ∉ F) (hp : p ∈ F) :
    ∃ γ : 𝕀 → ℂ, Continuous γ ∧ γ 0 = x ∧ γ 1 = p ∧
      ∀ t, t ≠ 1 → γ t ∈ connectedComponentIn Fᶜ x := by
  classical
  set U := connectedComponentIn Fᶜ x with hU
  have hFc := (isCompact_of_oArc φ).isClosed
  have hε : ∀ n : ℕ, (0 : ℝ) < (1 / 2) ^ n := fun n => by positivity
  choose δ hδ hconn using fun n => exists_small_connector φ (hε n)
  let η : ℕ → ℝ := fun n => min (δ n / 2) ((1 / 2) ^ n)
  have hη : ∀ n, 0 < η n := fun n => lt_min (half_pos (hδ n)) (hε n)
  let e : ℕ → ℝ := fun n => Nat.casesOn n (η 0) fun k => min (η k) (η (k + 1))
  have he : ∀ n, 0 < e n := by
    intro n
    cases n with
    | zero => exact hη 0
    | succ k => exact lt_min (hη k) (hη (k + 1))
  have heη : ∀ n, e n ≤ η n := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ k => exact min_le_right _ _
  have heη' : ∀ n, e (n + 1) ≤ η n := fun n => min_le_left _ _
  have hclosure := subset_closure_component φ hx hp
  choose y hyU hyd using fun n => Metric.mem_closure_iff.mp hclosure (e n) (he n)
  have hUeq : ∀ n, connectedComponentIn Fᶜ (y n) = U := fun n => (connectedComponentIn_eq
    (hyU n)).symm
  have hyF : ∀ n, y n ∉ F := fun n => connectedComponentIn_subset _ _ (hyU n)
  have hdist : ∀ n, dist (y n) (y (n + 1)) < δ n := by
    intro n
    have h1 := hyd n
    have h2 := hyd (n + 1)
    have h3 := dist_triangle_right (y n) (y (n + 1)) p
    have h4 : η n ≤ δ n / 2 := min_le_left _ _
    rw [dist_comm p] at h1 h2
    linarith [heη n, heη' n]
  have hstep : ∀ n, ∃ q : Path (y n) (y (n + 1)), (∀ t, q t ∈ U) ∧ ∀ t, dist (q t) p ≤ 2 *
    (1 / 2) ^ n := by
    intro n
    obtain ⟨C, hC, hCF, h1, h2, h3⟩ := hconn n (y n) (y (n + 1)) (hyF n) (hyF (n + 1))
      (by rw [hUeq]; exact hyU (n + 1)) (hdist n)
    obtain ⟨q, hq⟩ := hC.joinedIn _ h1 _ h2
    refine ⟨q, fun t => ?_, fun t => ?_⟩
    · rw [← hUeq n]
      exact hC.isConnected.isPreconnected.subset_connectedComponentIn h1 hCF (hq t)
    · have h4 : dist (q t) (y n) < (1 / 2) ^ n := h3 (hq t)
      have h5 := hyd n
      have h6 : η n ≤ (1 / 2) ^ n := min_le_right _ _
      have h7 := dist_triangle (q t) (y n) p
      rw [dist_comm p] at h5
      linarith [heη n]
  choose q hqU hqd using hstep
  have hxy : y 0 ∈ U := hyU 0
  have hUopen : IsOpen U := isOpen_component hFc x
  have hUpath : IsPathConnected U :=
    hUopen.isConnected_iff_isPathConnected.mp (isConnected_connectedComponentIn_iff.mpr hx)
  obtain ⟨q₀, hq₀⟩ := hUpath.joinedIn x (mem_connectedComponentIn hx) _ hxy
  obtain ⟨B, hB⟩ := (isCompact_range q₀.continuous).isBounded.subset_closedBall p
  let P : ℕ → 𝕀 → ℂ := fun n => Nat.casesOn n q₀ fun k => q k
  let r : ℕ → ℝ := fun n => Nat.casesOn n B fun k => 2 * (1 / 2) ^ k
  have hr : Filter.Tendsto r Filter.atTop (𝓝 0) := by
    refine (Filter.tendsto_add_atTop_iff_nat 1).mp ?_
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul (2 : ℝ)
    rw [mul_zero] at h
    exact h
  have hPc : ∀ n, Continuous (P n) := by
    intro n
    cases n with
    | zero => exact q₀.continuous
    | succ k => exact (q k).continuous
  have hlink : ∀ n, P n 1 = P (n + 1) 0 := by
    intro n
    cases n with
    | zero => exact q₀.target.trans (q 0).source.symm
    | succ k => exact (q k).target.trans (q (k + 1)).source.symm
  have hclose : ∀ n t, dist (P n t) p ≤ r n := by
    intro n t
    cases n with
    | zero => exact mem_closedBall.mp (hB ⟨t, rfl⟩)
    | succ k => exact hqd k t
  obtain ⟨γ, hγc, hγ0, hγ1, hγU⟩ := exists_path_of_tendsto hPc hlink hr hclose
  refine ⟨γ, hγc, hγ0.trans q₀.source, hγ1, fun t ht => ?_⟩
  obtain ⟨n, s, hs⟩ := hγU t ht
  rw [hs]
  cases n with
  | zero => exact hq₀ s
  | succ k => exact hqU k s

/-- **Cross-cuts.** Two different points of an `O`-arc are joined by an arc whose other points lie
in a given component of the complement. -/
theorem exists_crossCut {F : Set ℂ} (φ : Circle ≃ₜ F) {x p q : ℂ} (hx : x ∉ F) (hp : p ∈ F)
    (hq : q ∈ F) (hpq : p ≠ q) :
    ∃ e : 𝕀 → ℂ, Continuous e ∧ Function.Injective e ∧ e 0 = p ∧ e 1 = q ∧
      ∀ t, t ≠ 0 → t ≠ 1 → e t ∈ connectedComponentIn Fᶜ x := by
  obtain ⟨γ₁, hc₁, h1₀, h1₁, h1U⟩ := exists_path_to_boundary φ hx hp
  obtain ⟨γ₂, hc₂, h2₀, h2₁, h2U⟩ := exists_path_to_boundary φ hx hq
  let P₁ : Path x p := ⟨⟨γ₁, hc₁⟩, h1₀, h1₁⟩
  let P₂ : Path x q := ⟨⟨γ₂, hc₂⟩, h2₀, h2₁⟩
  let P : Path p q := P₁.symm.trans P₂
  obtain ⟨e, hec, hei, he0, he1, her⟩ := exists_arc_of_path P.continuous
    (by rw [P.source, P.target]; exact hpq)
  rw [P.source] at he0
  rw [P.target] at he1
  refine ⟨e, hec, hei, he0, he1, fun t ht0 ht1 => ?_⟩
  have htmem : e t ∈ range P := her ⟨t, rfl⟩
  have hrange : range P = range P₁.symm ∪ range P₂ := Path.trans_range _ _
  have hne0 : e t ≠ p := fun h => ht0 (hei (h.trans he0.symm))
  have hne1 : e t ≠ q := fun h => ht1 (hei (h.trans he1.symm))
  rw [hrange] at htmem
  rcases htmem with ⟨s, hs⟩ | ⟨s, hs⟩
  · have hs' : γ₁ (unitInterval.symm s) = e t := hs
    by_cases h : unitInterval.symm s = 1
    · rw [h, h1₁] at hs'
      exact absurd hs'.symm hne0
    · rw [← hs']
      exact h1U _ h
  · have hs' : γ₂ s = e t := hs
    by_cases h : s = 1
    · rw [h, h2₁] at hs'
      exact absurd hs'.symm hne1
    · rw [← hs']
      exact h2U _ h

end GraphMinor.Surface
