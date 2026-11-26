/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Annulus
import Mathlib.Topology.Order.IntermediateValue

/-!
# A larger closed disc around a closed disc

Let `Δ` be a closed disc of a surface whose boundary consists of interior points of the surface. In
this file we find a closed disc `Δ'` that has `Δ` in its inside, in any neighbourhood of the
boundary
of `Δ` (`exists_disc_around`).

We add caps from `Cap.lean` along the boundary of `Δ`, in two rounds. We cut the boundary into an
even
number of short arcs. The first round adds a cap exactly along every second arc, so the remaining
arcs
stay in the boundary. The second round adds a cap along each remaining arc, a little longer than the
arc.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

local notation "𝕀" => unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- There is no continuous injective map from the circle to the line, by the mean value theorem
applied to the difference between antipodal points. -/
theorem not_injective_circle_real {f : Circle → ℝ} (hf : Continuous f) : ¬ Function.Injective f
  := by
  intro hinj
  let d : ℝ → ℝ := fun θ => f (Circle.exp θ) - f (Circle.exp (θ + Real.pi))
  have hd : Continuous d := by fun_prop
  have h2 : d Real.pi = - d 0 := by
    have : Circle.exp (Real.pi + Real.pi) = Circle.exp 0 := by
      rw [← two_mul, Circle.exp_two_pi, Circle.exp_zero]
    simp only [d, this, zero_add]
    ring
  have hzero : ∃ θ, d θ = 0 := by
    rcases le_total (d 0) 0 with h | h
    · obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc Real.pi_pos.le hd.continuousOn
        (show (0 : ℝ) ∈ Icc (d 0) (d Real.pi) from ⟨h, by rw [h2]; linarith⟩)
      exact ⟨θ, hθ⟩
    · obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc' Real.pi_pos.le hd.continuousOn
        (show (0 : ℝ) ∈ Icc (d Real.pi) (d 0) from ⟨by rw [h2]; linarith, h⟩)
      exact ⟨θ, hθ⟩
  obtain ⟨θ, hθ⟩ := hzero
  have h3 : Circle.exp θ = Circle.exp (θ + Real.pi) := hinj (sub_eq_zero.mp hθ)
  have hpi : Circle.exp Real.pi = -1 := Circle.ext (by simp [Circle.coe_exp, Complex.exp_pi_mul_I])
  have h4 : Circle.exp (θ + Real.pi) = - Circle.exp θ := by
    rw [Circle.exp_add, hpi, mul_neg, mul_one]
  rw [h4] at h3
  have h5 := congrArg (fun w : Circle => (w : ℂ)) h3
  simp only [Circle.coe_neg] at h5
  have h6 : (Circle.exp θ : ℂ) = 0 := by
    linear_combination h5 / 2
  exact Circle.coe_ne_zero _ h6

/-- A chart of a closed disc turned by the angle `ρ`. -/
theorem IsChart.rotate {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g) (ρ : ℝ) :
    IsChart D (fun x => cis' (-ρ) * h x) (fun z => g (cis' ρ * z)) := by
  have hmul : ∀ (θ : ℝ) (z : ℂ), ‖cis' θ * z‖ = ‖z‖ := fun θ z => by rw [norm_mul, norm_cis',
    one_mul]
  have hcan : ∀ (θ : ℝ) (z : ℂ), cis' θ * (cis' (-θ) * z) = z := fun θ z => by
    rw [← mul_assoc, cis', cis', ← Complex.exp_add]
    simp
  have hcan' : ∀ (θ : ℝ) (z : ℂ), cis' (-θ) * (cis' θ * z) = z := fun θ z => by
    have := hcan (-θ) z
    rwa [neg_neg] at this
  have hball : ∀ θ, MapsTo (fun z => cis' θ * z) (closedBall (0 : ℂ) 1) (closedBall 0 1)
    := fun θ z hz => by
    rw [mem_closedBall_zero_iff] at hz ⊢
    change ‖cis' θ * z‖ ≤ 1
    rwa [hmul]
  refine ⟨continuousOn_const.mul c.hc, c.gc.comp (continuousOn_const.mul continuousOn_id) (hball ρ),
    fun x hx => hball (-ρ) (c.hm hx), fun z hz => c.gm (hball ρ hz), fun x hx => ?_, fun z hz
      => ?_, ?_⟩
  · show g (cis' ρ * (cis' (-ρ) * h x)) = x
    rw [hcan]
    exact c.gh hx
  · show cis' (-ρ) * h (g (cis' ρ * z)) = z
    rw [c.hg (hball ρ hz), hcan']
  · have h1 : (fun x => cis' (-ρ) * h x) '' discBd D = (fun z => cis' (-ρ) * z) '' (h '' discBd D)
    := by
      rw [image_image]
    rw [h1, c.bd]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hw ⊢
      change ‖cis' (-ρ) * w‖ = 1
      rwa [hmul]
    · intro hz
      refine ⟨cis' ρ * z, ?_, hcan' ρ z⟩
      rw [mem_sphere_zero_iff_norm] at hz ⊢
      rwa [hmul]

theorem cis'_mul (a b : ℝ) : cis' a * cis' b = cis' (a + b) := by
  rw [cis', cis', cis', ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A line in the boundary of a closed disc is an arc between two angles of a suitable chart. -/
theorem exists_angle_chart {D Q : Set S} {s t : S} (hD : IsClosedDisc D)
    (hQ : IsLineWithEnds Q s t) (hsub : Q ⊆ discBd D) :
    ∃ h g α β, IsChart D h g ∧ -Real.pi < α ∧ α < β ∧ β < Real.pi ∧ angleArc g α β = Q := by
  classical
  obtain ⟨a, ha, har, ha0, ha1⟩ := hQ.exists_arc
  have hst : s ≠ t := fun he => by
    have : (0 : 𝕀) = 1 := ha.2 (by rw [ha0, ha1, he])
    exact zero_ne_one this
  have hQc : IsCompact Q := har ▸ isCompact_range ha.1
  have hQp : IsPreconnected Q := har ▸ isPreconnected_range ha.1
  obtain ⟨hw, hwQ⟩ : ∃ w, w ∈ discBd D ∧ w ∉ Q := by
    by_contra hcon
    push Not at hcon
    obtain ⟨φ⟩ := hD.isOArc_discBd
    obtain ⟨f, -, -⟩ := id hQ
    refine not_injective_circle_real
      (f := fun w => ((f.symm ⟨(φ w).1, hcon _ (φ w).2⟩ : 𝕀) : ℝ))
      (continuous_subtype_val.comp (f.symm.continuous.comp
        (Continuous.subtype_mk (continuous_subtype_val.comp φ.continuous) _))) fun w w' he => ?_
    have h1 := f.symm.injective (Subtype.ext he)
    exact φ.injective (Subtype.ext (congrArg (Subtype.val : Q → S) h1))
  obtain ⟨h₀, g₀, c₀⟩ := hD.exists_isChart
  -- turn the chart so that `w` goes to `-1`
  have hmemS : ∀ {h : S → ℂ} {g : ℂ → S}, IsChart D h g → ∀ {x}, x ∈ discBd D → ‖h x‖ = 1 :=
    fun c x hx => mem_sphere_zero_iff_norm.mp (c.bd ▸ mem_image_of_mem _ hx)
  have hcis : ∀ {z : ℂ}, ‖z‖ = 1 → cis' (Complex.arg z) = z := fun {z} hz => by
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz] at this
    simpa [cis'] using this
  have hvn : ‖h₀ hw‖ = 1 := hmemS c₀ hwQ.1
  set ρ := Complex.arg (h₀ hw) + Real.pi with hρ
  have c₁ := c₀.rotate ρ
  set h₁ : S → ℂ := fun x => cis' (-ρ) * h₀ x with hh₁
  set g₁ : ℂ → S := fun z => g₀ (cis' ρ * z) with hg₁
  have hw1 : h₁ hw = -1 := by
    change cis' (-ρ) * h₀ hw = -1
    conv_lhs => rw [← hcis hvn]
    rw [cis'_mul]
    have : -ρ + Complex.arg (h₀ hw) = -Real.pi := by
      rw [hρ]
      ring
    rw [this, cis']
    simp [Complex.exp_neg]
  have hDQ : Q ⊆ D := hsub.trans (discBd_subset D)
  have hnorm : ∀ x ∈ Q, ‖h₁ x‖ = 1 := fun x hx => hmemS c₁ (hsub hx)
  have hne1 : ∀ x ∈ Q, h₁ x ≠ -1 := fun x hx he => by
    apply hwQ.2
    have h1 : hw = x := by
      rw [← c₁.gh (discBd_subset D hwQ.1), ← c₁.gh (hDQ hx)]
      show g₁ (h₁ hw) = g₁ (h₁ x)
      rw [hw1, he]
    exact h1 ▸ hx
  have hslit : ∀ x ∈ Q, h₁ x ∈ Complex.slitPlane := fun x hx => by
    rw [Complex.mem_slitPlane_iff_arg]
    refine ⟨fun he => hne1 x hx ?_, fun h0 => ?_⟩
    · rw [← hcis (hnorm x hx), he, cis']
      simp
    · have := hnorm x hx
      rw [h0] at this
      simp at this
  have hargc : ContinuousOn Complex.arg Complex.slitPlane :=
    fun u hu => (Complex.continuousAt_arg hu).continuousWithinAt
  have hfc : ContinuousOn (fun x => Complex.arg (h₁ x)) Q := hargc.comp (c₁.hc.mono hDQ) hslit
  let A : Set ℝ := (fun x => Complex.arg (h₁ x)) '' Q
  have hAc : IsCompact A := hQc.image_of_continuousOn hfc
  have hsQ : s ∈ Q := by
    rw [← har, ← ha0]
    exact ⟨0, rfl⟩
  have htQ : t ∈ Q := by
    rw [← har, ← ha1]
    exact ⟨1, rfl⟩
  have hAconn : IsConnected A := ⟨⟨_, s, hsQ, rfl⟩, hQp.image _ hfc⟩
  have hAeq := eq_Icc_of_connected_compact hAconn hAc
  have hαm : sInf A ∈ A := hAc.sInf_mem hAconn.nonempty
  have hβm : sSup A ∈ A := hAc.sSup_mem hAconn.nonempty
  have hle : sInf A ≤ sSup A := csInf_le_csSup hAconn.nonempty hAc.bddBelow hAc.bddAbove
  have hbd : ∀ a ∈ A, -Real.pi < a ∧ a < Real.pi := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Complex.neg_pi_lt_arg _, lt_of_le_of_ne (Complex.arg_le_pi _) ?_⟩
    exact ((Complex.mem_slitPlane_iff_arg.mp (hslit x hx)).1)
  refine ⟨h₁, g₁, sInf A, sSup A, c₁, (hbd _ hαm).1, ?_, (hbd _ hβm).2, ?_⟩
  · refine lt_of_le_of_ne hle fun he => hst ?_
    have h1 : ∀ x ∈ A, x = sInf A := fun x hx => by
      have h2 := hAeq ▸ hx
      exact le_antisymm (h2.2.trans he.symm.le) h2.1
    have hs := h1 _ ⟨s, hsQ, rfl⟩
    have ht := h1 _ ⟨t, htQ, rfl⟩
    have h2 : h₁ s = h₁ t := by
      rw [← hcis (hnorm s hsQ), ← hcis (hnorm t htQ)]
      show cis' (Complex.arg (h₁ s)) = cis' (Complex.arg (h₁ t))
      have hs' : Complex.arg (h₁ s) = sInf A := hs
      have ht' : Complex.arg (h₁ t) = sInf A := ht
      rw [hs', ht']
    calc s = g₁ (h₁ s) := (c₁.gh (hDQ hsQ)).symm
      _ = g₁ (h₁ t) := by rw [h2]
      _ = t := c₁.gh (hDQ htQ)
  · ext z
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      have h1 : θ ∈ A := hAeq ▸ hθ
      obtain ⟨x, hx, he⟩ := h1
      have he' : Complex.arg (h₁ x) = θ := he
      change g₁ (cis' θ) ∈ Q
      rw [← he', hcis (hnorm x hx)]
      have : g₁ (h₁ x) = x := c₁.gh (hDQ hx)
      rwa [this]
    · intro hz
      have h1 : Complex.arg (h₁ z) ∈ Icc (sInf A) (sSup A) := hAeq ▸ ⟨z, hz, rfl⟩
      refine ⟨_, h1, ?_⟩
      change g₁ (cis' (Complex.arg (h₁ z))) = z
      rw [hcis (hnorm z hz)]
      exact c₁.gh (hDQ hz)

/-- Adding a cap along a line of the boundary of a closed disc. -/
theorem exists_disc_add [T2Space S] {D Q : Set S} {s t : S} (hD : IsClosedDisc D)
    (hQ : IsLineWithEnds Q s t) (hsub : Q ⊆ discBd D) {R : ℝ} {U : Set S} {k : S → ℂ} {l : ℂ → S}
    (c : BallChart R U k l) {N : Set S} (hN : IsOpen N) (hQN : Q ⊆ U ∩ N) :
    ∃ D', IsClosedDisc D' ∧ D ⊆ D' ∧ D' ⊆ D ∪ N ∧ discBd D \ (Q \ {s, t}) ⊆ discBd D' ∧
      Q \ {s, t} ⊆ D' \ discBd D' := by
  obtain ⟨h, g, α, β, cD, hα, hαβ, hβ, rfl⟩ := exists_angle_chart hD hQ hsub
  obtain ⟨T, hT, hTN, hTD, hTb⟩ := exists_cap_angle cD c hN hα hαβ hβ hQN
  obtain ⟨h1, h2⟩ := disc_union D T (angleArc g α β) s t hD hT hQ (by rw [inter_comm]; exact hTD)
    hsub hTb
  refine ⟨D ∪ T, h1, subset_union_left, union_subset_union_right _ hTN, ?_, ?_⟩
  · rw [h2]
    exact fun z hz => ⟨.inl hz.1, hz.2⟩
  · rw [h2]
    intro z hz
    exact ⟨.inl (discBd_subset D (hsub hz.1)), fun h3 => h3.2 hz⟩

/-- Adding a cap along a slightly longer line of the boundary. -/
theorem exists_disc_add_wide [T2Space S] {D Q : Set S} {s t : S} (hD : IsClosedDisc D)
    (hQ : IsLineWithEnds Q s t) (hsub : Q ⊆ discBd D) {R : ℝ} {U : Set S} {k : S → ℂ} {l : ℂ → S}
    (c : BallChart R U k l) {N : Set S} (hN : IsOpen N) (hQN : Q ⊆ U ∩ N) :
    ∃ D', IsClosedDisc D' ∧ D ⊆ D' ∧ D' ⊆ D ∪ N ∧ discBd D \ N ⊆ discBd D' ∧ Q ⊆ D' \ discBd D'
      := by
  obtain ⟨h, g, α, β, cD, hα, hαβ, hβ, rfl⟩ := exists_angle_chart hD hQ hsub
  obtain ⟨η, hη, hα₁, hβ₁, O, hO, hOθ, hOg⟩ :=
    cD.exists_margin (c.isOpen.inter hN) hα hαβ.le hβ hQN
  have hL := cD.isLine_angleArc hα₁ (by linarith) hβ₁
  have hLU : angleArc g (α - η) (β + η) ⊆ U ∩ N := by
    rintro _ ⟨θ, hθ, rfl⟩
    exact hOg _ (hOθ θ hθ) (norm_cis' θ).le
  obtain ⟨D', h1, h2, h3, h4, h5⟩ := exists_disc_add hD hL (cD.angleArc_subset _ _) c hN hLU
  refine ⟨D', h1, h2, h3, ?_, ?_⟩
  · rintro z ⟨hz, hzN⟩
    exact h4 ⟨hz, fun h6 => hzN (hLU h6.1).2⟩
  · rintro _ ⟨θ, hθ, rfl⟩
    have hmem : ∀ x ∈ Icc (α - η) (β + η), x ∈ Ioo (-Real.pi) Real.pi :=
      fun x hx => ⟨hα₁.trans_le hx.1, hx.2.trans_lt hβ₁⟩
    have hθ' : θ ∈ Icc (α - η) (β + η) := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hne : ∀ x ∈ Icc (α - η) (β + η), x ≠ θ → g (cis' x) ≠ g (cis' θ) := fun x hx hxθ he => by
      have h6 := cD.injOn (cis'_mem_closedBall x) (cis'_mem_closedBall θ) he
      exact hxθ (cis'_injOn (hmem x hx) (hmem θ hθ') h6)
    refine h5 ⟨⟨θ, hθ', rfl⟩, ?_⟩
    rintro (h6 | h6)
    · exact hne (α - η) ⟨le_rfl, by linarith⟩ (by linarith [hθ.1]) h6.symm
    · exact hne (β + η) ⟨by linarith, le_rfl⟩ (by linarith [hθ.2]) h6.symm

theorem IsChart.isLine_angleArc' [T2Space S] {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g)
    {a b : ℝ} (hab : a < b) (hb : b < a + 2 * Real.pi) :
    IsLineWithEnds (angleArc g a b) (g (cis' a)) (g (cis' b)) := by
  set m := (a + b) / 2 with hm
  have c' := c.rotate m
  have hL := c'.isLine_angleArc (α := a - m) (β := b - m) (by rw [hm]; linarith) (by linarith)
    (by rw [hm]; linarith)
  have hrot : ∀ θ, g (cis' m * cis' (θ - m)) = g (cis' θ) := fun θ => by
    rw [cis'_mul, add_sub_cancel]
  have heq : angleArc (fun z => g (cis' m * z)) (a - m) (b - m) = angleArc g a b := by
    ext x
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      refine ⟨θ + m, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, ?_⟩
      change g (cis' (θ + m)) = g (cis' m * cis' θ)
      rw [cis'_mul, add_comm]
    · rintro ⟨θ, hθ, rfl⟩
      exact ⟨θ - m, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, hrot θ⟩
  rw [heq, hrot a, hrot b] at hL
  exact hL

theorem cis'_period (θ : ℝ) : cis' (θ + 2 * Real.pi) = cis' θ := by
  rw [cis', cis']
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem cis'_ne_of_lt {θ θ' : ℝ} (h1 : θ < θ') (h2 : θ' < θ + 2 * Real.pi) : cis' θ ≠ cis' θ' := by
  intro he
  set m := (θ + θ') / 2 with hm
  have h3 : cis' (θ - m) = cis' (θ' - m) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, ← cis'_mul, ← cis'_mul, he]
  have := cis'_injOn (x₁ := θ - m) (x₂ := θ' - m) ⟨by rw [hm]; linarith, by rw [hm]; linarith⟩
    ⟨by rw [hm]; linarith, by rw [hm]; linarith⟩ h3
  linarith

private theorem add_even_boundary_caps [T2Space S] (hman : ∀ x : S, IsManifoldPoint x)
    {Δ W : Set S} (hΔ : IsClosedDisc Δ) (hW : IsOpen W) (hsub : discBd Δ ⊆ W)
    {n : ℕ} {A : ℕ → Set S} {e₀ e₁ : ℕ → S}
    {U : ℝ → Set S} {k : ℝ → S → ℂ} {l : ℝ → ℂ → S}
    (hc : ∀ θ, BallChart 1 (U θ) (k θ) (l θ))
    (hAU : ∀ j : ℕ, j < 2 * n → ∃ θ, A j ⊆ U θ)
    (hline : ∀ j, IsLineWithEnds (A j) (e₀ j) (e₁ j))
    (hAb : ∀ j, A j ⊆ discBd Δ)
    (hsep : ∀ j j' : ℕ, j < 2 * n → j' < 2 * n → j ≠ j' →
      Disjoint (A j) (A j' \ {e₀ j', e₁ j'})) :
    let Ao : ℕ → Set S := fun j => A j \ {e₀ j, e₁ j}
    ∀ k : ℕ, k ≤ n → ∃ D, IsClosedDisc D ∧ Δ ⊆ D ∧ D ⊆ Δ ∪ W ∧
    (∀ i < k, Ao (2 * i) ⊆ D \ discBd D) ∧ ∀ z ∈ discBd Δ, (∀ i < k, z ∉ Ao (2 * i)) → z ∈ discBd D
      := by
  dsimp only
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨Δ, hΔ, Subset.rfl, subset_union_left, fun i hi => absurd hi (by omega),
      fun z hz _ => hz⟩
  | succ k ih =>
    intro hk
    obtain ⟨D, h1, h2, h3, h4, h5⟩ := ih (by omega)
    have hj : 2 * k < 2 * n := by omega
    obtain ⟨θ, hθ⟩ := hAU _ hj
    have hQ : A (2 * k) ⊆ discBd D := fun z hz => h5 z (hAb _ hz) fun i hi hz' =>
      Set.disjoint_left.mp (hsep (2 * k) (2 * i) hj (by omega) (by omega)) hz hz'
    obtain ⟨D', h6, h7, h8, h9, h10⟩ := exists_disc_add h1 (hline (2 * k)) hQ (hc θ) hW
      fun z hz => ⟨hθ hz, hsub (hAb _ hz)⟩
    refine ⟨D', h6, h2.trans h7, h8.trans (union_subset h3 subset_union_right), ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · exact (h4 i hi').trans (discInt_mono hman h1 h7)
      · exact h10
    · intro z hz hall
      exact h9 ⟨h5 z hz fun i hi => hall i (by omega), hall k (by omega)⟩

private theorem add_odd_boundary_caps [T2Space S] (hman : ∀ x : S, IsManifoldPoint x)
    {Δ D₁ W : Set S} (h1 : IsClosedDisc D₁) (hW : IsOpen W) (hsub : discBd Δ ⊆ W)
    {n : ℕ} {A : ℕ → Set S} {e₀ e₁ : ℕ → S}
    {U : ℝ → Set S} {k : ℝ → S → ℂ} {l : ℝ → ℂ → S}
    (hc : ∀ θ, BallChart 1 (U θ) (k θ) (l θ))
    (hAU : ∀ j : ℕ, j < 2 * n → ∃ θ, A j ⊆ U θ)
    (hline : ∀ j, IsLineWithEnds (A j) (e₀ j) (e₁ j))
    (hAb : ∀ j, A j ⊆ discBd Δ) (hAc : ∀ j, IsClosed (A j))
    (hodd : ∀ i < n, A (2 * i + 1) ⊆ discBd D₁)
    (hsep2 : ∀ i i' : ℕ, i < n → i' < n → i ≠ i' →
      Disjoint (A (2 * i + 1)) (A (2 * i' + 1))) :
    ∀ k : ℕ, k ≤ n → ∃ D, IsClosedDisc D ∧ D₁ ⊆ D ∧ D ⊆ D₁ ∪ W ∧
    (∀ i < k, A (2 * i + 1) ⊆ D \ discBd D) ∧ ∀ i, k ≤ i → i < n → A (2 * i + 1) ⊆ discBd D := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨D₁, h1, Subset.rfl, subset_union_left, fun i hi => absurd hi (by omega),
      fun i _ hi => hodd i hi⟩
  | succ k ih =>
    intro hk
    obtain ⟨D, g1, g2, g3, g4, g5⟩ := ih (by omega)
    have hj : 2 * k + 1 < 2 * n := by omega
    obtain ⟨θ, hθ⟩ := hAU _ hj
    let M : Set S := ⋃ i ∈ {i | i < n ∧ i ≠ k}, A (2 * i + 1)
    have hMc : IsClosed M := by
      refine Set.Finite.isClosed_biUnion ((finite_lt_nat n).subset fun i hi => hi.1) fun i _ => ?_
      exact hAc (2 * i + 1)
    have hN : IsOpen (W \ M) := hW.sdiff hMc
    obtain ⟨D', g6, g7, g8, g9, g10⟩ := exists_disc_add_wide g1 (hline (2 * k + 1))
      (g5 k le_rfl (by omega)) (hc θ) hN fun z hz => ⟨hθ hz, hsub (hAb _ hz), fun hzM => by
        obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzM
        exact Set.disjoint_left.mp (hsep2 k i (by omega) hi.1 hi.2.symm) hz hzi⟩
    refine ⟨D', g6, g2.trans g7, g8.trans (union_subset g3 ?_), ?_, ?_⟩
    · exact (sdiff_subset).trans subset_union_right
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · exact (g4 i hi').trans (discInt_mono hman g1 g7)
      · exact g10
    · intro i hi hin z hz
      refine g9 ⟨g5 i (by omega) hin hz, fun hzN => hzN.2 ?_⟩
      exact mem_iUnion₂.mpr ⟨i, ⟨hin, by omega⟩, hz⟩

/-- **A closed disc around a closed disc.** See the module docstring. -/
theorem exists_disc_around [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {Δ W : Set S}
    (hΔ : IsClosedDisc Δ) (hint : ∀ x ∈ discBd Δ, IsInteriorPoint x) (hW : IsOpen W)
    (hsub : discBd Δ ⊆ W) :
    ∃ Δ', IsClosedDisc Δ' ∧ Δ ⊆ Δ' \ discBd Δ' ∧ Δ' ⊆ Δ ∪ W := by
  classical
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  let P : ℝ → S := fun θ => g (cis' θ)
  have hPc : Continuous P := c.gc.comp_continuous continuous_cis' fun θ => cis'_mem_closedBall θ
  have hPb : ∀ θ, P θ ∈ discBd Δ := fun θ => c.angleArc_subset θ θ ⟨θ, by simp, rfl⟩
  have hch : ∀ θ, ∃ U k l, BallChart 1 U k l ∧ U ⊆ W ∧ l 0 = P θ := fun θ =>
    (hint _ (hPb θ)).exists_ballChart hW (hsub (hPb θ)) one_pos
  choose U k l hc hUW hl0 using hch
  have hmemU : ∀ θ, P θ ∈ U θ := fun θ => by
    rw [← hl0 θ]
    exact (hc θ).gm (by simp)
  have hpi := Real.pi_pos
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := (0 : ℝ))
    (b := 2 * Real.pi)) (c := fun θ => P ⁻¹' U θ) (fun θ => (hc θ).isOpen.preimage hPc)
    fun θ _ => mem_iUnion.mpr ⟨θ, hmemU θ⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.pi / δ + 1)
  have hnpos : (0 : ℝ) < n := by
    have : 0 < Real.pi / δ := by positivity
    linarith
  set τ := Real.pi / n with hτ
  have hτ0 : 0 < τ := by positivity
  have hnτ : (n : ℝ) * τ = Real.pi := by
    rw [hτ]
    field_simp
  have hn1 : (1 : ℝ) ≤ n := by
    have : 0 < Real.pi / δ := by positivity
    linarith
  have hτπ : τ ≤ Real.pi := by nlinarith
  have hτδ : τ < δ := by
    rw [hτ, div_lt_iff₀ hnpos]
    have h1 : Real.pi / δ < n := by linarith
    rw [div_lt_iff₀ hδ] at h1
    linarith
  let E : ℕ → Set ℝ := fun j => Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ)
  let A : ℕ → Set S := fun j => angleArc g ((j : ℝ) * τ) (((j : ℝ) + 1) * τ)
  let e₀ : ℕ → S := fun j => P ((j : ℝ) * τ)
  let e₁ : ℕ → S := fun j => P (((j : ℝ) + 1) * τ)
  let Ao : ℕ → Set S := fun j => A j \ {e₀ j, e₁ j}
  have hline : ∀ j, IsLineWithEnds (A j) (e₀ j) (e₁ j) := fun j =>
    c.isLine_angleArc' (by nlinarith) (by nlinarith)
  have hAb : ∀ j, A j ⊆ discBd Δ := fun j => c.angleArc_subset _ _
  have hAU : ∀ j : ℕ, j < 2 * n → ∃ θ, A j ⊆ U θ := fun j hj => by
    have hj' : (j : ℝ) + 1 ≤ 2 * n := by exact_mod_cast hj
    have hm : (j : ℝ) * τ ∈ Icc 0 (2 * Real.pi) :=
      ⟨by positivity, by nlinarith⟩
    obtain ⟨θ, hθ⟩ := hleb _ hm
    refine ⟨θ, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    refine hθ ?_
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [hx.1]
    · linarith [hx.2]
  have hord : ∀ a b : ℕ, a ≤ b → (a : ℝ) * τ ≤ (b : ℝ) * τ := fun a b hab =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hτ0.le
  have htwo : (2 * (n : ℝ)) * τ = 2 * Real.pi := by rw [mul_assoc, hnτ]
  -- two points of the boundary with different angles
  have hPne : ∀ {θ θ' : ℝ}, θ < θ' → θ' < θ + 2 * Real.pi → P θ ≠ P θ' := fun h1 h2 he =>
    cis'_ne_of_lt h1 h2 (c.injOn (cis'_mem_closedBall _) (cis'_mem_closedBall _) he)
  have hEb : ∀ j : ℕ, j < 2 * n → ∀ θ ∈ E j, 0 ≤ θ ∧ θ ≤ 2 * Real.pi := fun j hj θ hθ => by
    have h1 := hord (j + 1) (2 * n) hj
    push_cast at h1
    have h2 := hθ.2
    have h3 := hθ.1
    constructor
    · have : (0 : ℝ) ≤ (j : ℝ) * τ := by positivity
      linarith
    · linarith
  -- a point of the open arc has an angle strictly inside
  have hAo : ∀ j z, z ∈ Ao j → ∃ θ, (j : ℝ) * τ < θ ∧ θ < ((j : ℝ) + 1) * τ ∧ P θ = z := by
    rintro j _ ⟨⟨θ, hθ, rfl⟩, hne⟩
    refine ⟨θ, lt_of_le_of_ne hθ.1 fun he => hne (.inl ?_), lt_of_le_of_ne hθ.2 fun he => hne
      (.inr ?_),
      rfl⟩
    · change P θ = P _
      rw [he]
    · change P θ = P _
      rw [he]
  -- a closed arc misses the open arcs of the other arcs
  have hsep : ∀ j j' : ℕ, j < 2 * n → j' < 2 * n → j ≠ j' → Disjoint (A j) (Ao j') := by
    intro j j' hj hj' hne
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨θ, hθ, rfl⟩ hz
    obtain ⟨θ', h1, h2, h3⟩ := hAo j' _ hz
    obtain ⟨h4, h5⟩ := hEb j hj θ hθ
    have h6 := (hEb j' hj') θ' ⟨h1.le, h2.le⟩
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h7 := hord (j + 1) j' hlt
      push_cast at h7
      have h8 := hθ.2
      have h9 := hord (j' + 1) (2 * n) hj'
      push_cast at h9
      exact hPne (by linarith) (by linarith) h3.symm
    · have h7 := hord (j' + 1) j hlt
      push_cast at h7
      have h8 := hθ.1
      refine hPne (θ := θ') (θ' := θ) (by linarith) ?_ h3
      have h9 : (0 : ℝ) ≤ (j' : ℝ) * τ := by positivity
      linarith
  -- arcs of the same parity are disjoint
  have hsep2 : ∀ i i' : ℕ, i < n → i' < n → i ≠ i' → Disjoint (A (2 * i + 1)) (A (2 * i' + 1)) := by
    have key : ∀ i i' : ℕ, i < n → i < i' → i' < n → Disjoint (A (2 * i + 1)) (A (2 * i' + 1)) := by
      intro i i' hi hii hi'
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨θ, hθ, rfl⟩ ⟨θ', hθ', he⟩
      have h1 := hord (2 * i + 1 + 1 + 1) (2 * i' + 1) (by omega)
      have h2 := hord (2 * i' + 1 + 1) (2 * n) (by omega)
      have h3 := hord 0 (2 * i + 1) (by omega)
      have h4 := hθ.1
      have h5 := hθ.2
      have h6 := hθ'.1
      have h7 := hθ'.2
      push_cast at h1 h2 h3 h4 h5 h6 h7
      exact hPne (θ := θ) (θ' := θ') (by nlinarith) (by nlinarith) he.symm
    intro i i' hi hi' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i i' hi h hi'
    · exact (key i' i hi' h hi).symm
  obtain ⟨D₁, h1, h2, h3, h4, h5⟩ :=
    add_even_boundary_caps hman hΔ hW hsub hc hAU hline hAb hsep n le_rfl
  have hodd : ∀ i < n, A (2 * i + 1) ⊆ discBd D₁ := fun i hi z hz => h5 z (hAb _ hz) fun i' hi' hz'
    =>
    Set.disjoint_left.mp (hsep (2 * i + 1) (2 * i') (by omega) (by omega) (by omega)) hz hz'
  obtain ⟨D₂, f1, f2, f3, f4, -⟩ :=
    add_odd_boundary_caps hman h1 hW hsub hc hAU hline hAb
      (fun _ => (isCompact_Icc.image hPc).isClosed) hodd hsep2 n le_rfl
  refine ⟨D₂, f1, ?_, f3.trans (union_subset h3 subset_union_right)⟩
  have hD₁D₂ : D₁ \ discBd D₁ ⊆ D₂ \ discBd D₂ := discInt_mono hman h1 f2
  intro x hx
  by_cases hxb : x ∈ discBd Δ
  · -- the angle of `x`
    have hxn : ‖h x‖ = 1 := mem_sphere_zero_iff_norm.mp (c.bd ▸ mem_image_of_mem h hxb)
    have hang : ∃ θ, 0 ≤ θ ∧ θ < 2 * Real.pi ∧ P θ = x := by
      have hcis : cis' (Complex.arg (h x)) = h x := by
        have := Complex.norm_mul_exp_arg_mul_I (h x)
        rw [hxn] at this
        simpa [cis'] using this
      have hgx : g (h x) = x := c.gh hx
      rcases le_or_gt 0 (Complex.arg (h x)) with h0 | h0
      · refine ⟨_, h0, ?_, by change g (cis' _) = x; rw [hcis, hgx]⟩
        linarith [Complex.arg_le_pi (h x)]
      · refine ⟨Complex.arg (h x) + 2 * Real.pi, by linarith [Complex.neg_pi_lt_arg (h x)], by
          linarith, ?_⟩
        change g (cis' _) = x
        rw [cis'_period, hcis, hgx]
    obtain ⟨θ, hθ0, hθ2, hPx⟩ := hang
    subst hPx
    have hdiv : 0 ≤ θ / τ := by positivity
    set j := ⌊θ / τ⌋₊ with hjdef
    have hj1 : (j : ℝ) * τ ≤ θ := by
      have := Nat.floor_le hdiv
      rwa [le_div_iff₀ hτ0] at this
    have hj2 : θ < ((j : ℝ) + 1) * τ := by
      have := Nat.lt_floor_add_one (θ / τ)
      rwa [div_lt_iff₀ hτ0] at this
    have hj3 : j < 2 * n := by
      have h7 : (j : ℝ) * τ < (2 * (n : ℝ)) * τ := by rw [htwo]; linarith
      have h8 : (j : ℝ) < 2 * (n : ℝ) := lt_of_mul_lt_mul_right h7 hτ0.le
      exact_mod_cast h8
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' j
    · by_cases he : (j : ℝ) * τ = θ
      · rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · have hn0 : 0 < n := by omega
          have hθz : θ = 0 := by
            rw [← he, hk]
            simp
          subst hθz
          have h7 : P 0 ∈ A (2 * (n - 1) + 1) := by
            refine ⟨2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
            · calc ((2 * (n - 1) + 1 : ℕ) : ℝ) * τ ≤ ((2 * n : ℕ) : ℝ) * τ := hord _ _ (by omega)
                _ = 2 * Real.pi := by
                  push_cast
                  exact htwo
            · have h8 : ((2 * (n - 1) + 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) := by
                have : 2 * (n - 1) + 1 + 1 = 2 * n := by omega
                exact_mod_cast this
              rw [h8, htwo]
            · change g (cis' _) = g (cis' 0)
              have := cis'_period 0
              rw [zero_add] at this
              rw [this]
          exact f4 (n - 1) (by omega) h7
        · have h7 : P θ ∈ A (2 * (k - 1) + 1) := by
            refine ⟨θ, ⟨?_, ?_⟩, rfl⟩
            · have := hord (2 * (k - 1) + 1) j (by omega)
              linarith
            · have h8 : ((2 * (k - 1) + 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
                have : 2 * (k - 1) + 1 + 1 = j := by omega
                exact_mod_cast this
              rw [h8]
              exact he.symm.le
          exact f4 (k - 1) (by omega) h7
      · have hlt : (j : ℝ) * τ < θ := lt_of_le_of_ne hj1 he
        have h7 : P θ ∈ Ao (2 * k) := by
          rw [← hk]
          refine ⟨⟨θ, ⟨hj1, hj2.le⟩, rfl⟩, ?_⟩
          rintro (h8 | h8)
          · exact hPne (θ := (j : ℝ) * τ) (θ' := θ) hlt (by nlinarith) h8.symm
          · exact hPne (θ := θ) (θ' := ((j : ℝ) + 1) * τ) hj2 (by nlinarith) h8
        exact hD₁D₂ (h4 k (by omega) h7)
    · exact f4 k (by omega) (hk ▸ ⟨θ, ⟨hj1, hj2.le⟩, rfl⟩)
  · have h6 : x ∈ Δ \ discBd Δ := ⟨hx, hxb⟩
    exact hD₁D₂ (discInt_mono hman hΔ h2 h6)

/-- The circle is the unit sphere of the plane. -/
theorem exists_circle_sphere : ∃ o : Circle ≃ₜ sphere (0 : ℂ) 1, ∀ w : Circle, (o w).1 = w := by
  have hemb : IsEmbedding fun w : Circle => (w : ℂ) := IsEmbedding.subtypeVal
  have hr : range (fun w : Circle => (w : ℂ)) = sphere 0 1 := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w)
    · intro hz
      exact ⟨⟨z, by simpa [Submonoid.unitSphere] using hz⟩, rfl⟩
  refine ⟨hemb.toHomeomorph.trans (Homeomorph.setCongr hr), fun w => rfl⟩

/-- **The annulus between two nested closed discs.** Coordinates on the larger disc by the disc of
radius `2`, such that the unit disc is the smaller disc, with a given boundary parametrization. -/
theorem exists_disc_collar {Δ Δ' : Set S} (hΔ : IsClosedDisc Δ) (hΔ' : IsClosedDisc Δ')
    (hin : Δ ⊆ Δ' \ discBd Δ') (p : Circle ≃ₜ discBd Δ) :
    ∃ (c : ℂ → S) (c' : S → ℂ), ContinuousOn c (closedBall 0 2) ∧ ContinuousOn c' Δ' ∧
      MapsTo c (closedBall 0 2) Δ' ∧ MapsTo c' Δ' (closedBall 0 2) ∧
      LeftInvOn c' c (closedBall 0 2) ∧ RightInvOn c' c Δ' ∧ c '' closedBall 0 1 = Δ ∧
      c '' sphere 0 2 = discBd Δ' ∧ ∀ w : Circle, c w = (p w).1 := by
  classical
  obtain ⟨h', g', cD⟩ := hΔ'.exists_isChart
  have hsubD : Δ ⊆ Δ' := fun x hx => (hin hx).1
  have hbdΔ : discBd Δ ⊆ Δ := discBd_subset Δ
  -- the small disc in the coordinates of the large one
  have hg'h : LeftInvOn g' h' Δ := cD.gh.mono hsubD
  have hcont₁ : ContinuousOn g' (h' '' Δ) := cD.gc.mono (cD.image_subset hsubD)
  obtain ⟨hE, hEb⟩ := hΔ.image (cD.hc.mono hsubD) hcont₁ hg'h
  have hFo : Nonempty (Circle ≃ₜ h' '' discBd Δ) := hEb ▸ hE.isOArc_discBd
  have hEeq : h' '' Δ = closedInner (h' '' discBd Δ) := eq_closedInner_of_discBd hFo hE hEb
  obtain ⟨r, hr⟩ := exists_homeomorph_image (cD.hc.mono (hbdΔ.trans hsubD))
    (cD.gc.mono (cD.image_subset (hbdΔ.trans hsubD))) (hg'h.mono hbdΔ)
  obtain ⟨o, ho⟩ := exists_circle_sphere
  obtain ⟨h₀, k₀, m₀, hv₀⟩ := exists_bdMatch ((o.symm.trans p).trans r)
  have hoS : Nonempty (Circle ≃ₜ sphere (0 : ℂ) 1) := ⟨o⟩
  obtain ⟨Ψ, hΨ, hΨi⟩ := exists_plane_homeomorph hoS hFo m₀
  rw [closedInner_sphere, ← hEeq] at hΨi
  have hh₀ : ∀ w : Circle, h₀ w = h' (p w).1 := fun w => by
    have h1 := hv₀ (o w)
    rw [ho w] at h1
    rw [h1]
    simp [hr]
  obtain ⟨hd₂, hd₂b⟩ := isClosedDisc_closedBall.1.image (f := Ψ.symm) (f' := Ψ)
    Ψ.symm.continuous.continuousOn Ψ.continuous.continuousOn fun z _ => Ψ.apply_symm_apply z
  rw [isClosedDisc_closedBall.2] at hd₂b
  have hF₂ : Nonempty (Circle ≃ₜ Ψ.symm '' sphere (0 : ℂ) 1) := hd₂b ▸ hd₂.isOArc_discBd
  have hcl₂ := image_closedBall_of_homeomorph Ψ.symm hF₂ rfl
  have hin₂ : closedBall (0 : ℂ) 1 ⊆ inner (Ψ.symm '' sphere (0 : ℂ) 1) := fun z hz => by
    have h1 : Ψ z ∈ h' '' Δ := hΨi ▸ mem_image_of_mem Ψ hz
    obtain ⟨x, hx, hxe⟩ := h1
    have h2 : x ∈ discInt Δ' := hin hx
    rw [cD.discInt_eq] at h2
    obtain ⟨u, hu, rfl⟩ := h2
    rw [cD.hg (ball_subset_closedBall hu)] at hxe
    have h3 : ‖Ψ z‖ < 1 := by
      rw [← hxe]
      exact mem_ball_zero_iff.mp hu
    have h4 : z ∈ closedInner (Ψ.symm '' sphere (0 : ℂ) 1) := by
      rw [← hcl₂]
      exact ⟨Ψ z, mem_ball_zero_iff.mpr h3 |> ball_subset_closedBall, Ψ.symm_apply_apply z⟩
    rcases h4 with h4 | ⟨w, hw, rfl⟩
    · exact h4
    · rw [Ψ.apply_symm_apply] at h3
      rw [mem_sphere_zero_iff_norm] at hw
      linarith
  obtain ⟨φ₂⟩ := id hF₂
  obtain ⟨Θ, Θ', m, hid, hsph⟩ := exists_annulus φ₂ hin₂
  rw [← hcl₂] at m
  have hΘb : ∀ z ∈ closedBall (0 : ℂ) 2, Ψ (Θ z) ∈ closedBall (0 : ℂ) 1 := fun z hz => by
    obtain ⟨y, hy, he⟩ := m.1 hz
    rw [← he, Ψ.apply_symm_apply]
    exact hy
  have hb₁₂ : closedBall (0 : ℂ) 1 ⊆ closedBall 0 2 := closedBall_subset_closedBall (by norm_num)
  have hc₁ : ContinuousOn (fun z => Ψ (Θ z)) (closedBall 0 2) :=
    Ψ.continuous.comp_continuousOn m.2.2.2.2.1
  refine ⟨fun z => g' (Ψ (Θ z)), fun x => Θ' (Ψ.symm (h' x)), cD.gc.comp hc₁ hΘb, ?_, ?_, ?_, ?_,
    ?_,
    ?_, ?_, ?_⟩
  · refine m.2.2.2.2.2.comp (Ψ.symm.continuous.comp_continuousOn cD.hc) ?_
    exact fun x hx => mem_image_of_mem _ (cD.hm hx)
  · exact fun z hz => cD.gm (hΘb z hz)
  · exact fun x hx => m.2.1 (mem_image_of_mem _ (cD.hm hx))
  · intro z hz
    change Θ' (Ψ.symm (h' (g' (Ψ (Θ z))))) = z
    rw [cD.hg (hΘb z hz), Ψ.symm_apply_apply]
    exact m.2.2.1 hz
  · intro x hx
    change g' (Ψ (Θ (Θ' (Ψ.symm (h' x))))) = x
    have h1 : Ψ.symm (h' x) ∈ Ψ.symm '' closedBall 0 1 := mem_image_of_mem _ (cD.hm hx)
    have h2 : Θ (Θ' (Ψ.symm (h' x))) = Ψ.symm (h' x) := m.2.2.2.1 h1
    rw [h2, Ψ.apply_symm_apply]
    exact cD.gh hx
  · ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h1 : Θ z = z := hid hz
      change g' (Ψ (Θ z)) ∈ Δ
      rw [h1]
      obtain ⟨y, hy, he⟩ : Ψ z ∈ h' '' Δ := hΨi ▸ mem_image_of_mem Ψ hz
      rw [← he, hg'h hy]
      exact hy
    · intro hx
      obtain ⟨z, hz, he⟩ : h' x ∈ Ψ '' closedBall 0 1 := hΨi ▸ mem_image_of_mem h' hx
      refine ⟨z, hz, ?_⟩
      change g' (Ψ (Θ z)) = x
      rw [hid hz]
      change g' (Ψ z) = x
      rw [he]
      exact hg'h hx
  · rw [← cD.g_sphere]
    have h1 : (fun z => Ψ (Θ z)) '' sphere 0 2 = sphere 0 1 := by
      have : (fun z => Ψ (Θ z)) '' sphere 0 2 = Ψ '' (Θ '' sphere 0 2) := by
        rw [image_image]
      rw [this, hsph, image_image]
      simp
    rw [← h1, image_image]
  · intro w
    have hw : (w : ℂ) ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w)
    have hw' : (w : ℂ) ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hw
    change g' (Ψ (Θ w)) = _
    rw [hid hw']
    change g' (Ψ w) = _
    rw [hΨ hw, hh₀, cD.gh (hsubD (hbdΔ (p w).2))]

end GraphMinor.Surface
