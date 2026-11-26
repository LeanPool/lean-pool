/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.GM07.Open
public import LeanPool.GraphMinor.GM07.Section11
import LeanPool.GraphMinor.GM07.Section11b
import LeanPool.GraphMinor.GM07.Section11f
public import LeanPool.GraphMinor.Surface.CutParallel

/-!
# Graph Minors VII, Section 3: Matchings and Forests

This file formalizes Section 3 (pages 218–221) of N. Robertson and P. D. Seymour,
*Graph Minors. VII. Disjoint paths on a surface*, J. Combin. Theory Ser. B 45 (1988) 212–254:
- `(3.1)` (`theorem_3_1`): For any fixed surface `Σ` there are only finitely many similarity
  classes of proper `I`-arcs.
- `(3.2)` (`theorem_3_2_claim_1`, `theorem_3_2`): For any fixed surface `Σ` and `s, t ∈ bd(Σ)`,
  there are only finitely many parallel classes of `I`-arcs with ends `s, t`.
- `(3.3)` (`theorem_3_3`): For any surface `Σ` and finite `X ⊆ bd(Σ)`, there are only finitely many
  congruence classes of `X`-matchings.
- `(3.4)` (`theorem_3_4`): For any surface `Σ` and finite `Y ⊆ bd(Σ)`, there are only finitely many
  homoplasty classes of `Y`-forests.
- `(3.5)` (`theorem_3_5`): For every matching `G` in `Σ` and every homoplasty class `ℬ` there
  exists `H ∈ ℬ` with `U(G) ∩ U(H)` finite.
- `(3.6)` (`theorem_3_6`): Existence of the bound `w(Σ, k, n)` (`wSurface S k n`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Function Topology GraphMinor.Surface GraphMinor.GM11

universe u v w

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Equivalence properties of similarity and parallelism, and Theorem (3.1) -/

theorem AreSimilarIArcs.refl (F : Set S) : AreSimilarIArcs F F :=
  ⟨Homeomorph.refl S, image_id F⟩

theorem AreSimilarIArcs.symm {F F' : Set S} (h : AreSimilarIArcs F F') :
    AreSimilarIArcs F' F := by
  rcases h with ⟨α, rfl⟩
  exact ⟨α.symm, α.symm_image_image F⟩

theorem AreSimilarIArcs.trans {F₁ F₂ F₃ : Set S}
    (h₁₂ : AreSimilarIArcs F₁ F₂) (h₂₃ : AreSimilarIArcs F₂ F₃) :
    AreSimilarIArcs F₁ F₃ := by
  rcases h₁₂ with ⟨α, rfl⟩
  rcases h₂₃ with ⟨β, rfl⟩
  refine ⟨α.trans β, ?_⟩
  ext y
  simp [Homeomorph.trans_apply]

theorem AreParallelIArcs.refl (F : Set S) : AreParallelIArcs F F :=
  ⟨Homeomorph.refl S, image_id F, fun _ _ => rfl⟩

theorem AreParallelIArcs.symm {F F' : Set S} (h : AreParallelIArcs F F') :
    AreParallelIArcs F' F := by
  rcases h with ⟨α, rfl, hbd⟩
  refine ⟨α.symm, α.symm_image_image F, fun x hx => ?_⟩
  exact (α.symm_apply_eq).mpr (hbd x hx).symm

theorem AreParallelIArcs.trans {F₁ F₂ F₃ : Set S}
    (h₁₂ : AreParallelIArcs F₁ F₂) (h₂₃ : AreParallelIArcs F₂ F₃) :
    AreParallelIArcs F₁ F₃ := by
  rcases h₁₂ with ⟨α, rfl, hα⟩
  rcases h₂₃ with ⟨β, rfl, hβ⟩
  refine ⟨α.trans β, ?_, fun x hx => ?_⟩
  · ext y
    simp [Homeomorph.trans_apply]
  · simp [Homeomorph.trans_apply, hα x hx, hβ x hx]

theorem AreParallelIArcs.areSimilarIArcs {F F' : Set S} (h : AreParallelIArcs F F') :
    AreSimilarIArcs F F' := by
  rcases h with ⟨α, hF, -⟩
  exact ⟨α, hF⟩

/-- Graph Minors VII, (3.1) (page 218):
"(3.1) *For any fixed $\Sigma$ there are only finitely many similarity classes.*" -/
theorem theorem_3_1_proof (hS : IsSurface S) :
    ∃ 𝓕 : Set (Set S), 𝓕.Finite ∧ ∀ F : Set S, IsProperIArc F →
      ∃ F₀ ∈ 𝓕, AreSimilarIArcs F₀ F :=
  similarArcsFinite S hS

/-! ## 2. Circle orientation, cuff signatures, and Theorem (3.2) -/

/-- Graph Minors VII, (3.2), Claim (1) (page 219), with the hypothesis of `ParallelArcsStatement`
that `α` fixes `s` and `t` (see the correction to the proof of (3.2) in `corrections/GM07.md`):
"(1) *Let $F, F' \in \mathcal{F}$. If there is a homeomorphism $\alpha \colon \Sigma \to \Sigma$
with $\alpha(F) = F'$ and with null signature, then $F$ is parallel to $F'$.*" -/
theorem theorem_3_2_claim_1 {F F' : Set S} {s t : S} (α : S ≃ₜ S) (hS : IsSurface S)
    (hne : s ≠ t) (hb : F ∩ bd S = {s, t}) (hb' : F' ∩ bd S = {s, t})
    (hl : IsLineWithEnds F s t) (hl' : IsLineWithEnds F' s t)
    (hαF : α '' F = F') (hs : α s = s) (ht : α t = t) (hα : HasNullSignature α) :
    AreParallelIArcs F F' :=
  parallelArcs S F F' s t α hS hne hb hb' hl hl' hαF hs ht hα

/-- Orientation-preserving circle homeomorphisms are closed under composition. -/
theorem PreservesCircleOrientation.trans {h₁ h₂ : Circle ≃ₜ Circle}
    (H₁ : PreservesCircleOrientation h₁) (H₂ : PreservesCircleOrientation h₂) :
    PreservesCircleOrientation (h₁.trans h₂) := by
  rcases H₁ with ⟨l₁, hc₁, hm₁, hl₁⟩
  rcases H₂ with ⟨l₂, hc₂, hm₂, hl₂⟩
  refine ⟨l₂ ∘ l₁, hc₂.comp hc₁, hm₂.comp hm₁, fun t => ?_⟩
  simp [Homeomorph.trans_apply, hl₁ t, hl₂ (l₁ t)]

/-- Orientation-preserving circle homeomorphisms are closed under inversion. -/
theorem PreservesCircleOrientation.symm {h : Circle ≃ₜ Circle}
    (H : PreservesCircleOrientation h) :
    PreservesCircleOrientation h.symm := by
  rcases H with ⟨l, hc, hm, hl⟩
  have hpi := Real.pi_pos
  have hper : ∃ k : ℤ, 1 ≤ k ∧ ∀ t : ℝ, l (t + 2 * Real.pi) = l t + k * (2 * Real.pi) := by
    have h0 : Circle.exp (l (0 + 2 * Real.pi)) = Circle.exp (l 0) := by
      rw [← hl, ← hl, zero_add, Circle.exp_two_pi, Circle.exp_zero]
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp h0
    have hk_pos : (0 : ℝ) < k * (2 * Real.pi) := by
      have : l 0 < l (0 + 2 * Real.pi) := hm (by positivity)
      linarith
    have hk1 : 1 ≤ k := by
      have : (0 : ℝ) < k := pos_of_mul_pos_left hk_pos (by positivity)
      exact_mod_cast this
    refine ⟨k, hk1, fun t => ?_⟩
    set g : ℝ → ℝ := fun x => (l (x + 2 * Real.pi) - l x) / (2 * Real.pi)
    have hg_cont : Continuous g :=
      ((hc.comp (continuous_id.add continuous_const)).sub hc).div_const _
    have hg_int : ∀ x : ℝ, ∃ m : ℤ, g x = m := by
      intro x
      have hx_eq : Circle.exp (l (x + 2 * Real.pi)) = Circle.exp (l x) := by
        rw [← hl, ← hl, Circle.periodic_exp]
      obtain ⟨m, hm_eq⟩ := Circle.exp_eq_exp.mp hx_eq
      refine ⟨m, ?_⟩
      change (l (x + 2 * Real.pi) - l x) / (2 * Real.pi) = m
      have : l (x + 2 * Real.pi) - l x = m * (2 * Real.pi) := by linarith
      rw [this, mul_div_cancel_right₀ _ (by positivity)]
    obtain ⟨m_t, hmt⟩ := hg_int t
    have hk0 : g 0 = k := by
      change (l (0 + 2 * Real.pi) - l 0) / (2 * Real.pi) = k
      have : l (0 + 2 * Real.pi) - l 0 = k * (2 * Real.pi) := by linarith
      rw [this, mul_div_cancel_right₀ _ (by positivity)]
    have hmt_eq : (m_t : ℝ) = (k : ℝ) := by
      by_contra hne
      have hmid_mem : ((m_t : ℝ) + (k : ℝ)) / 2 < (k : ℝ) ∧ (m_t : ℝ) < ((m_t : ℝ) + (k : ℝ)) / 2 ∨
          (k : ℝ) < ((m_t : ℝ) + (k : ℝ)) / 2 ∧ ((m_t : ℝ) + (k : ℝ)) / 2 < (m_t : ℝ) := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · left; constructor <;> linarith
        · right; constructor <;> linarith
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hlt' : m_t < k := by exact_mod_cast hlt
        have hval : (m_t : ℝ) + 1 / 2 ∈ uIcc (g 0) (g t) := by
          rw [hk0, hmt, uIcc_of_ge hlt.le]
          have : (m_t : ℝ) + 1 ≤ k := by exact_mod_cast hlt'
          constructor <;> linarith
        obtain ⟨x, -, hx⟩ := intermediate_value_uIcc hg_cont.continuousOn hval
        obtain ⟨m_x, hmx⟩ := hg_int x
        have : (m_x : ℝ) = (m_t : ℝ) + 1 / 2 := hmx.symm.trans hx
        have h2 : (2 * m_x : ℤ) = (2 * m_t + 1 : ℤ) := by
          exact_mod_cast (show (2 * (m_x : ℝ)) = 2 * (m_t : ℝ) + 1 by linarith)
        omega
      · have hgt' : k < m_t := by exact_mod_cast hgt
        have hval : (k : ℝ) + 1 / 2 ∈ uIcc (g 0) (g t) := by
          rw [hk0, hmt, uIcc_of_le hgt.le]
          have : (k : ℝ) + 1 ≤ m_t := by exact_mod_cast hgt'
          constructor <;> linarith
        obtain ⟨x, -, hx⟩ := intermediate_value_uIcc hg_cont.continuousOn hval
        obtain ⟨m_x, hmx⟩ := hg_int x
        have : (m_x : ℝ) = (k : ℝ) + 1 / 2 := hmx.symm.trans hx
        have h2 : (2 * m_x : ℤ) = (2 * k + 1 : ℤ) := by
          exact_mod_cast (show (2 * (m_x : ℝ)) = 2 * (k : ℝ) + 1 by linarith)
        omega
    have hdiv : (l (t + 2 * Real.pi) - l t) / (2 * Real.pi) = k := hmt.trans hmt_eq
    have := (div_eq_iff (show (2 * Real.pi : ℝ) ≠ 0 by positivity)).mp hdiv
    linarith
  obtain ⟨k, hk1, hper⟩ := hper
  have hn : ∀ n : ℤ, l (n * (2 * Real.pi)) = l 0 + n * (k * (2 * Real.pi)) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ m ih =>
      push_cast at ih ⊢
      have : ((m : ℝ) + 1) * (2 * Real.pi) = (m : ℝ) * (2 * Real.pi) + 2 * Real.pi := by ring
      rw [this, hper, ih]
      ring
    | pred m ih =>
      push_cast at ih ⊢
      have : (-(m : ℝ) - 1) * (2 * Real.pi) + 2 * Real.pi = -(m : ℝ) * (2 * Real.pi) := by ring
      have hp := hper ((-(m : ℝ) - 1) * (2 * Real.pi))
      rw [this, ih] at hp
      linarith
  have hsurj : Surjective l := by
    intro y
    have hpos : (0 : ℝ) < k * (2 * Real.pi) := by
      have : (0 : ℝ) < k := by exact_mod_cast hk1
      positivity
    set n : ℤ := ⌊(y - l 0) / (k * (2 * Real.pi))⌋
    have hn_le : l (n * (2 * Real.pi)) ≤ y := by
      rw [hn n]
      have := Int.floor_le ((y - l 0) / (k * (2 * Real.pi)))
      have hmul := (le_div_iff₀ hpos).mp this
      linarith
    have hy_le : y ≤ l ((n + 1 : ℤ) * (2 * Real.pi)) := by
      rw [hn (n + 1)]
      have := (Int.lt_floor_add_one ((y - l 0) / (k * (2 * Real.pi)))).le
      have hmul := (div_le_iff₀ hpos).mp this
      push_cast
      linarith
    have hle_x : (n : ℝ) * (2 * Real.pi) ≤ ((n + 1 : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      nlinarith
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc hle_x hc.continuousOn ⟨hn_le, hy_le⟩
    exact ⟨x, hx⟩
  let e : ℝ ≃o ℝ := hm.orderIsoOfSurjective l hsurj
  have he : ∀ x, e x = l x := fun _ => rfl
  refine ⟨e.symm, e.symm.continuous, e.symm.strictMono, fun t => ?_⟩
  apply h.injective
  rw [h.apply_symm_apply, hl (e.symm t), ← he, e.apply_symm_apply]

/-- Conjugating an orientation-preserving circle homeomorphism by `Homeomorph.inv Circle` preserves
orientation. -/
theorem PreservesCircleOrientation.conj_inv {h : Circle ≃ₜ Circle}
    (H : PreservesCircleOrientation h) :
    PreservesCircleOrientation ((Homeomorph.inv Circle).trans (h.trans (Homeomorph.inv Circle)))
      := by
  rcases H with ⟨l, hc, hm, hl⟩
  refine ⟨fun t => -l (-t), (hc.comp continuous_neg).neg,
    fun x y hxy => neg_lt_neg (hm (neg_lt_neg hxy)), fun t => ?_⟩
  simp only [Homeomorph.trans_apply]
  change (h ((Circle.exp t)⁻¹))⁻¹ = Circle.exp (-l (-t))
  rw [← Circle.exp_neg, hl (-t), ← Circle.exp_neg]

/-- Every homeomorphism of `Circle` either preserves orientation or preserves orientation after
composing with `Homeomorph.inv Circle`. -/
theorem preservesCircleOrientation_or_trans_inv (h : Circle ≃ₜ Circle) :
    PreservesCircleOrientation h ∨
      PreservesCircleOrientation (h.trans (Homeomorph.inv Circle)) := by
  have hpi := Real.pi_pos
  let φ : Circle ≃ₜ (univ : Set Circle) := (Homeomorph.Set.univ Circle).symm
  have hη : ContinuousOn (fun u : ℝ => (h (ee u) : Circle)) (Icc 0 1) :=
    (h.continuous.comp continuous_ee).continuousOn
  obtain ⟨m, hmc, hm_eq⟩ := exists_lift φ hη (fun _ _ => trivial)
  have hm_val : ∀ u ∈ Icc (0 : ℝ) 1, ee (m u) = h (ee u) := by
    intro u hu
    exact hm_eq u hu
  have hinj_ee : InjOn (fun u => ee (m u)) (Ico 0 1) := by
    intro x hx y hy hxy
    change ee (m x) = ee (m y) at hxy
    rw [hm_val x (Ico_subset_Icc_self hx), hm_val y (Ico_subset_Icc_self hy)] at hxy
    have he := h.injective hxy
    obtain ⟨k, hk⟩ := ee_eq_iff.mp he
    have hk0 : k = 0 := by
      have h1 : (-1 : ℝ) < k := by linarith [hx.1, hy.2]
      have h2 : (k : ℝ) < 1 := by linarith [hx.2, hy.1]
      have h3 : -1 < k := by exact_mod_cast h1
      have h4 : k < 1 := by exact_mod_cast h2
      omega
    rw [hk, hk0]
    simp
  have h01 : ee (m 1) = ee (m 0) := by
    rw [hm_val 1 (by simp), hm_val 0 (by simp)]
    have he10 : ee 1 = ee 0 := by simpa using ee_add_one 0
    rw [he10]
  obtain ⟨k, hk⟩ := ee_eq_iff.mp h01
  rcases lift_mono_loop hmc hinj_ee with hmono | hanti
  · left
    have hk_pos : (0 : ℝ) < k := by
      have := hmono (show (0 : ℝ) ∈ Icc 0 1 by simp) (show (1 : ℝ) ∈ Icc 0 1 by simp) zero_lt_one
      linarith
    have hk1 : 1 ≤ k := by exact_mod_cast hk_pos
    have hk_eq : k = 1 := by
      by_contra hne
      have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      obtain ⟨x, hx, hx_eq⟩ := intermediate_value_Ioo zero_le_one hmc
        (show m 0 + 1 ∈ Ioo (m 0) (m 1) by rw [hk]; constructor <;> linarith)
      have he : ee (m x) = ee (m 0) := by
        rw [hx_eq]
        exact ee_add_one (m 0)
      have hx0 := hinj_ee ⟨hx.1.le, hx.2⟩ ⟨le_rfl, zero_lt_one⟩ he
      linarith [hx.1]
    have hm1 : m 1 = m 0 + 1 := by rw [hk, hk_eq]; push_cast; rfl
    obtain ⟨h', hh'o, hh'⟩ := exists_circle_homeo hmc hmono hm1
    have h_eq : h' = h := by
      apply Homeomorph.ext
      intro z
      obtain ⟨u, hu, rfl⟩ := exists_param z
      rw [hh' u (Ico_subset_Icc_self hu), hm_val u (Ico_subset_Icc_self hu)]
    rwa [← h_eq]
  · right
    have hmc' : ContinuousOn (fun u => -m u) (Icc 0 1) := hmc.neg
    have hmono' : StrictMonoOn (fun u => -m u) (Icc 0 1) :=
      fun x hx y hy hxy => neg_lt_neg (hanti hx hy hxy)
    have hk_neg : (k : ℝ) < 0 := by
      have := hanti (show (0 : ℝ) ∈ Icc 0 1 by simp) (show (1 : ℝ) ∈ Icc 0 1 by simp) zero_lt_one
      linarith
    have hk1 : k ≤ -1 := by
      have : k < 0 := by exact_mod_cast hk_neg
      omega
    have hk_eq : k = -1 := by
      by_contra hne
      have hk2 : (k : ℝ) ≤ -2 := by exact_mod_cast (show k ≤ -2 by omega)
      obtain ⟨x, hx, hx_eq⟩ := intermediate_value_Ioo zero_le_one hmc'
        (show -m 0 + 1 ∈ Ioo (-m 0) (-m 1) by rw [hk]; constructor <;> linarith)
      have hmx : m x = m 0 + (-1 : ℤ) := by push_cast; linarith
      have he : ee (m x) = ee (m 0) := by
        rw [hmx]
        exact ee_add_int (m 0) (-1)
      have hx0 := hinj_ee ⟨hx.1.le, hx.2⟩ ⟨le_rfl, zero_lt_one⟩ he
      linarith [hx.1]
    have hm1 : -m 1 = -m 0 + 1 := by rw [hk, hk_eq]; push_cast; ring
    obtain ⟨h', hh'o, hh'⟩ := exists_circle_homeo hmc' hmono' hm1
    have h_eq : h' = h.trans (Homeomorph.inv Circle) := by
      apply Homeomorph.ext
      intro z
      obtain ⟨u, hu, rfl⟩ := exists_param z
      have hu' := Ico_subset_Icc_self hu
      rw [hh' u hu']
      change ee (-m u) = (h (ee u))⁻¹
      rw [← hm_val u hu']
      unfold ee
      rw [← Circle.exp_neg]
      ring_nf
    rwa [← h_eq]

/-- Conjugating an orientation-preserving circle homeomorphism by ANY circle homeomorphism `ψ`
preserves orientation. -/
theorem PreservesCircleOrientation.conj {h : Circle ≃ₜ Circle}
    (H : PreservesCircleOrientation h) (ψ : Circle ≃ₜ Circle) :
    PreservesCircleOrientation (ψ.symm.trans (h.trans ψ)) := by
  rcases preservesCircleOrientation_or_trans_inv ψ.symm with hψ | hψ
  · exact PreservesCircleOrientation.trans hψ
      (PreservesCircleOrientation.trans H (PreservesCircleOrientation.symm hψ))
  · have h_inv_symm : (Homeomorph.inv Circle).symm = Homeomorph.inv Circle := rfl
    have h_eq : ψ.symm.trans (h.trans ψ) =
        (ψ.symm.trans (Homeomorph.inv Circle)).trans
          (((Homeomorph.inv Circle).trans (h.trans (Homeomorph.inv Circle))).trans
            (ψ.symm.trans (Homeomorph.inv Circle)).symm) := by
      apply Homeomorph.ext
      intro z
      simp only [Homeomorph.trans_apply, Homeomorph.symm_trans_apply, Homeomorph.symm_symm,
        h_inv_symm]
      change ψ (h (ψ.symm z)) = ψ ((h ((ψ.symm z)⁻¹)⁻¹)⁻¹)⁻¹
      rw [inv_inv, inv_inv]
    rw [h_eq]
    exact PreservesCircleOrientation.trans hψ
      (PreservesCircleOrientation.trans (PreservesCircleOrientation.conj_inv H)
        (PreservesCircleOrientation.symm hψ))

/-- If two circle homeomorphisms `h₁, h₂` have the same orientation parity, then `h₁.trans h₂.symm`
preserves orientation. -/
theorem preservesCircleOrientation_trans_symm_of_iff {h₁ h₂ : Circle ≃ₜ Circle}
    (hiff : PreservesCircleOrientation h₁ ↔ PreservesCircleOrientation h₂) :
    PreservesCircleOrientation (h₁.trans h₂.symm) := by
  by_cases h1 : PreservesCircleOrientation h₁
  · exact PreservesCircleOrientation.trans h1 (PreservesCircleOrientation.symm (hiff.mp h1))
  · have h2 : ¬ PreservesCircleOrientation h₂ := fun h => h1 (hiff.mpr h)
    have h1' : PreservesCircleOrientation (h₁.trans (Homeomorph.inv Circle)) :=
      (preservesCircleOrientation_or_trans_inv h₁).resolve_left h1
    have h2' : PreservesCircleOrientation (h₂.trans (Homeomorph.inv Circle)) :=
      (preservesCircleOrientation_or_trans_inv h₂).resolve_left h2
    have hcomb := PreservesCircleOrientation.trans h1' (PreservesCircleOrientation.symm h2')
    have h_inv_symm : (Homeomorph.inv Circle).symm = Homeomorph.inv Circle := rfl
    have h_eq : (h₁.trans (Homeomorph.inv Circle)).trans
        (h₂.trans (Homeomorph.inv Circle)).symm = h₁.trans h₂.symm := by
      apply Homeomorph.ext
      intro z
      simp only [Homeomorph.trans_apply, Homeomorph.symm_trans_apply, h_inv_symm]
      change h₂.symm ((h₁ z)⁻¹)⁻¹ = h₂.symm (h₁ z)
      rw [inv_inv]
    rwa [h_eq] at hcomb

/-- A homeomorphism `α : S ≃ₜ S` maps every cuff of `S` to a cuff of `S`. -/
theorem image_cuff_mem_cuffs (α : S ≃ₜ S) {C : Set S} (hC : C ∈ cuffs S) :
    α '' C ∈ cuffs S := by
  have h1 := image_componentsIn α (bd S)
  rw [image_bd_homeomorph α] at h1
  unfold cuffs at hC ⊢
  rw [← h1]
  exact ⟨C, hC, rfl⟩

/-- If `F₀, F` are lines with ends in `bd S` and `F₀ ∩ bd S = {s, t}` and `F ∩ bd S = {s, t}`, then
any homeomorphism `α : S ≃ₜ S` with `α '' F = F₀` satisfies `(α s = s ∧ α t = t) ∨ (α s = t ∧ α t =
s)`. -/
theorem homeo_ends_cases {F₀ F : Set S} {s t : S} (hne : s ≠ t)
    (hb₀ : F₀ ∩ bd S = {s, t}) (hb : F ∩ bd S = {s, t})
    (α : S ≃ₜ S) (hα : α '' F = F₀) :
    (α s = s ∧ α t = t) ∨ (α s = t ∧ α t = s) := by
  have hst : α '' ({s, t} : Set S) = {s, t} := by
    calc
      α '' ({s, t} : Set S) = α '' (F ∩ bd S) := by rw [hb]
      _ = α '' F ∩ α '' bd S := image_inter α.injective
      _ = F₀ ∩ bd S := by rw [hα, image_bd_homeomorph α]
      _ = {s, t} := hb₀
  have hs_mem : α s ∈ ({s, t} : Set S) := hst ▸ mem_image_of_mem α (mem_insert s {t})
  have ht_mem : α t ∈ ({s, t} : Set S) := hst ▸ mem_image_of_mem α (mem_insert_of_mem s rfl)
  rcases hs_mem with hs_eq | hs_eq
  · left
    refine ⟨hs_eq, ?_⟩
    rcases ht_mem with ht_eq | ht_eq
    · exact absurd (α.injective (hs_eq.trans ht_eq.symm)) hne
    · exact mem_singleton_iff.mp ht_eq
  · right
    have hs_eq' : α s = t := mem_singleton_iff.mp hs_eq
    refine ⟨hs_eq', ?_⟩
    rcases ht_mem with ht_eq | ht_eq
    · exact ht_eq
    · have ht_eq' : α t = t := mem_singleton_iff.mp ht_eq
      exact absurd (α.injective (hs_eq'.trans ht_eq'.symm)) hne

/-- Within a single similarity class of proper `I`-arcs with ends `s, t`, there are only finitely
many parallel classes (Graph Minors VII, proof of (3.2), page 219). -/
theorem finite_parallel_classes_in_similarity_class (hS : IsSurface S) {s t : S} (hne : s ≠ t)
    (B : Set S) :
    ∃ 𝓖₀ : Set (Set S), 𝓖₀.Finite ∧
      (∀ F₀ ∈ 𝓖₀, F₀ ∩ bd S = {s, t} ∧ IsLineWithEnds F₀ s t ∧ AreSimilarIArcs B F₀) ∧
      ∀ F : Set S, F ∩ bd S = {s, t} → IsLineWithEnds F s t → AreSimilarIArcs B F →
        ∃ F₀ ∈ 𝓖₀, AreParallelIArcs F₀ F := by
  classical
  let 𝒮 : Set (Set S) :=
    {F : Set S | F ∩ bd S = {s, t} ∧ IsLineWithEnds F s t ∧ AreSimilarIArcs B F}
  by_cases h𝒮 : 𝒮.Nonempty
  · obtain ⟨F_star, hb_star, hl_star, hsim_star⟩ := h𝒮
    have hsim_to_star : ∀ F ∈ 𝒮, ∃ α : S ≃ₜ S, α '' F = F_star := by
      intro F ⟨_, _, hsimF⟩
      exact hsimF.symm.trans hsim_star
    choose! α_map hα_map using hsim_to_star
    have hcuff := cuff_statement.{u} S hS
    have : Fintype (cuffs S) := hcuff.2.1.fintype
    have hφ_ex : ∀ C : cuffs S, ∃ φ : Circle ≃ₜ C.1, True := by
      intro C
      obtain ⟨φ⟩ := hcuff.2.2 C.1 C.2
      exact ⟨φ, trivial⟩
    choose φ_cuff _ using hφ_ex
    let cuffImg (α : S ≃ₜ S) (C : cuffs S) : cuffs S :=
      ⟨α '' C.1, image_cuff_mem_cuffs α C.2⟩
    let circleAct (α : S ≃ₜ S) (C : cuffs S) : Circle ≃ₜ Circle :=
      ((φ_cuff C).trans (α.image C.1)).trans (φ_cuff (cuffImg α C)).symm
    let SigType := (cuffs S → cuffs S × Bool) × Bool
    let sig (F : Set S) : SigType :=
      (fun C => (cuffImg (α_map F) C,
        decide (PreservesCircleOrientation (circleAct (α_map F) C))),
        decide (α_map F s = s))
    have hSigFin : ( sig '' 𝒮 ).Finite := toFinite (sig '' 𝒮)
    have h_rep : ∀ σ ∈ sig '' 𝒮, ∃ F₀ ∈ 𝒮, sig F₀ = σ := by
      rintro σ ⟨F₀, hF₀, rfl⟩
      exact ⟨F₀, hF₀, rfl⟩
    choose! rep hrep_mem hrep_sig using h_rep
    refine ⟨rep '' (sig '' 𝒮), hSigFin.image rep, ?_, ?_⟩
    · rintro _ ⟨σ, hσ, rfl⟩
      exact hrep_mem σ hσ
    · intro F hb hl hsim
      have hF : F ∈ 𝒮 := ⟨hb, hl, hsim⟩
      have hσ : sig F ∈ sig '' 𝒮 := mem_image_of_mem sig hF
      set F₀ := rep (sig F)
      have hF₀ : F₀ ∈ 𝒮 := hrep_mem (sig F) hσ
      have hsig_eq : sig F₀ = sig F := hrep_sig (sig F) hσ
      refine ⟨F₀, mem_image_of_mem rep hσ, ?_⟩
      set α₁ := α_map F₀
      set α₂ := α_map F
      have hα₁F : α₁ '' F₀ = F_star := hα_map F₀ hF₀
      have hα₂F : α₂ '' F = F_star := hα_map F hF
      let α : S ≃ₜ S := α₁.trans α₂.symm
      have hα_img : α '' F₀ = F := by
        calc
          α '' F₀ = α₂.symm '' (α₁ '' F₀) := by ext y; simp [α, Homeomorph.trans_apply]
          _ = α₂.symm '' (α₂ '' F) := by rw [hα₁F, ← hα₂F]
          _ = F := α₂.symm_image_image F
      have h_ends_iff : α₁ s = s ↔ α₂ s = s :=
        decide_eq_decide.mp (congrArg Prod.snd hsig_eq)
      have h_ends : α s = s ∧ α t = t := by
        rcases homeo_ends_cases hne hb_star hF₀.1 α₁ hα₁F with ⟨hs1, ht1⟩ | ⟨hs1, ht1⟩ <;>
        rcases homeo_ends_cases hne hb_star hF.1 α₂ hα₂F with ⟨hs2, ht2⟩ | ⟨hs2, ht2⟩
        · refine ⟨?_, ?_⟩
          · simp [α, Homeomorph.trans_apply, hs1, (α₂.symm_apply_eq).mpr hs2.symm]
          · simp [α, Homeomorph.trans_apply, ht1, (α₂.symm_apply_eq).mpr ht2.symm]
        · exfalso
          exact hne ((h_ends_iff.mp hs1).symm.trans hs2)
        · exfalso
          exact hne ((h_ends_iff.mpr hs2).symm.trans hs1)
        · refine ⟨?_, ?_⟩
          · simp [α, Homeomorph.trans_apply, hs1, (α₂.symm_apply_eq).mpr hs2.symm]
          · simp [α, Homeomorph.trans_apply, ht1, (α₂.symm_apply_eq).mpr ht2.symm]
      have h_null : HasNullSignature α := by
        intro C φ hC
        let C' : cuffs S := ⟨C, hC⟩
        have hC_sig := congrFun (congrArg Prod.fst hsig_eq) C'
        have hD_eq : cuffImg α₁ C' = cuffImg α₂ C' := congrArg Prod.fst hC_sig
        have horient_eq :
            decide (PreservesCircleOrientation (circleAct α₁ C')) =
              decide (PreservesCircleOrientation (circleAct α₂ C')) :=
          congrArg Prod.snd hC_sig
        have horient_iff :
            PreservesCircleOrientation (circleAct α₁ C') ↔
              PreservesCircleOrientation (circleAct α₂ C') :=
          decide_eq_decide.mp horient_eq
        have h₀_orient :
            PreservesCircleOrientation ((circleAct α₁ C').trans (circleAct α₂ C').symm) :=
          preservesCircleOrientation_trans_symm_of_iff horient_iff
        set h₀ := (circleAct α₁ C').trans (circleAct α₂ C').symm
        have hh₀_val : ∀ z : Circle, (φ_cuff C' (h₀ z)).1 = α (φ_cuff C' z).1 := by
          intro z
          have h1 : (φ_cuff (cuffImg α₁ C') (circleAct α₁ C' z)).1 = α₁ (φ_cuff C' z).1 := by
            simp [circleAct, Homeomorph.trans_apply]
          have h2 : ∀ w : Circle,
              (φ_cuff (cuffImg α₂ C') w).1 = α₂ (φ_cuff C' ((circleAct α₂ C').symm w)).1 := by
            intro w
            have hw := (φ_cuff (cuffImg α₂ C')).apply_symm_apply
              ((α₂.image C'.1) (φ_cuff C' ((circleAct α₂ C').symm w)))
            have hact : circleAct α₂ C' ((circleAct α₂ C').symm w) = w :=
              (circleAct α₂ C').apply_symm_apply w
            have hact' : (φ_cuff (cuffImg α₂ C') (circleAct α₂ C' ((circleAct α₂ C').symm w))).1 =
                α₂ (φ_cuff C' ((circleAct α₂ C').symm w)).1 := by
              simp [circleAct, Homeomorph.trans_apply]
            rw [hact] at hact'
            exact hact'
          have h_same_φ : ∀ w : Circle,
              (φ_cuff (cuffImg α₂ C') w).1 = (φ_cuff (cuffImg α₁ C') w).1 := by
            intro w
            rw [hD_eq]
          have h3 := h2 (circleAct α₁ C' z)
          rw [h_same_φ, h1] at h3
          change (φ_cuff C' ((circleAct α₂ C').symm (circleAct α₁ C' z))).1 =
            α₂.symm (α₁ (φ_cuff C' z).1)
          exact ((α₂.symm_apply_eq).mpr h3).symm
        let ψ : Circle ≃ₜ Circle := (φ_cuff C').trans φ.symm
        let h_final : Circle ≃ₜ Circle := ψ.symm.trans (h₀.trans ψ)
        refine ⟨h_final, PreservesCircleOrientation.conj h₀_orient ψ, fun x => ?_⟩
        have hx1 : (φ_cuff C' (ψ.symm x)).1 = (φ x).1 := by
          simp [ψ]
        have hx2 : (φ (h_final x)).1 = (φ_cuff C' (h₀ (ψ.symm x))).1 := by
          simp [h_final, ψ, Homeomorph.trans_apply]
        rw [hx2, hh₀_val, hx1]
      exact theorem_3_2_claim_1 α hS hne hF₀.1 hb hF₀.2.1 hl hα_img h_ends.1 h_ends.2 h_null
  · refine ⟨∅, finite_empty, by simp, fun F hb hl hsim => ?_⟩
    exact absurd ⟨F, hb, hl, hsim⟩ h𝒮

/-- Graph Minors VII, (3.2) (page 219):
"(3.2) *For any fixed $\Sigma$ and $s, t \in bd(\Sigma)$, there are only finitely many parallel
classes of $I$-arcs with ends $s, t$.*" -/
theorem theorem_3_2_proof (hS : IsSurface S) (s t : S) :
    ∃ 𝓖 : Set (Set S), 𝓖.Finite ∧
      (∀ F₀ ∈ 𝓖, F₀ ∩ bd S = {s, t} ∧ IsLineWithEnds F₀ s t) ∧
      ∀ F : Set S, F ∩ bd S = {s, t} → IsLineWithEnds F s t →
        ∃ F₀ ∈ 𝓖, AreParallelIArcs F₀ F := by
  by_cases hne : s = t
  · subst hne
    refine ⟨∅, finite_empty, by simp, fun F _ hl => ?_⟩
    obtain ⟨f, hf0, hf1⟩ := hl
    have h01 : (0 : unitInterval) = 1 :=
      f.injective (Subtype.ext (hf0.trans hf1.symm))
    exact absurd (congrArg Subtype.val h01) zero_ne_one
  · obtain ⟨𝓕, h𝓕_fin, h𝓕⟩ := theorem_3_1_proof hS
    choose 𝓖_of h𝓖_fin h𝓖_mem h𝓖_cov using
      fun B => finite_parallel_classes_in_similarity_class hS hne B
    refine ⟨⋃ B ∈ 𝓕, 𝓖_of B, h𝓕_fin.biUnion fun B _ => h𝓖_fin B, ?_, ?_⟩
    · rintro F₀ hF₀
      obtain ⟨B, _, hF₀B⟩ := mem_iUnion₂.mp hF₀
      exact ⟨(h𝓖_mem B F₀ hF₀B).1, (h𝓖_mem B F₀ hF₀B).2.1⟩
    · intro F hb hl
      have hprop : IsProperIArc F := ⟨s, t, hne, hb, hl⟩
      obtain ⟨B, hB, hsim⟩ := h𝓕 F hprop
      obtain ⟨F₀, hF₀, hpar⟩ := h𝓖_cov B F hb hl hsim
      exact ⟨F₀, mem_iUnion₂.mpr ⟨B, hB, hF₀⟩, hpar⟩

/-! ## 3. Cutting a general surface along a proper `I`-arc and Theorem (3.3) -/

/-- The disjoint union of two surfaces is a surface. -/
theorem isSurface_sum {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (hA : IsSurface A) (hB : IsSurface B) : IsSurface (A ⊕ B) := by
  have : CompactSpace A := hA.1
  have : CompactSpace B := hB.1
  have : T2Space A := hA.2.1
  have : T2Space B := hB.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  rintro (a | b)
  · obtain ⟨U, V, hU, hV, ha, ⟨e⟩⟩ := hA.2.2 a
    refine ⟨Sum.inl '' U, V, isOpenMap_inl U hU, hV, mem_image_of_mem Sum.inl ha,
      ⟨(IsOpenEmbedding.inl.isEmbedding.homeomorphImage U).symm.trans e⟩⟩
  · obtain ⟨U, V, hU, hV, hb, ⟨e⟩⟩ := hB.2.2 b
    refine ⟨Sum.inr '' U, V, isOpenMap_inr U hU, hV, mem_image_of_mem Sum.inr hb,
      ⟨(IsOpenEmbedding.inr.isEmbedding.homeomorphImage U).symm.trans e⟩⟩

/-- Boundary points of `A` map to boundary points of `A ⊕ B` under `Sum.inl`. -/
theorem mem_bd_inl {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} (ha : a ∈ bd A) : (Sum.inl a : A ⊕ B) ∈ bd (A ⊕ B) := by
  intro hint
  apply ha
  obtain ⟨U, hU, hmem, hsub, ⟨e⟩⟩ :=
    hint.exists_subset isOpen_range_inl (mem_range_self a)
  have hpre : Sum.inl '' (Sum.inl ⁻¹' U) = U :=
    Subset.antisymm (image_preimage_subset Sum.inl U) (by
      intro z hz
      obtain ⟨x, rfl⟩ := hsub hz
      exact ⟨x, hz, rfl⟩)
  refine ⟨Sum.inl ⁻¹' U, hU.preimage continuous_inl, hmem,
    ⟨((IsOpenEmbedding.inl.isEmbedding.homeomorphImage (Sum.inl ⁻¹' U)).trans
      (Homeomorph.setCongr hpre)).trans e⟩⟩

/-- Cutting any (not necessarily connected) surface `S` along a proper `I`-arc `F` with ends
`s, t` gives a surface `Y` and a cutting map `ψ : Y → S`. -/
theorem exists_cut_arc_surface (hS : IsSurface S) {F : Set S} {s t : S}
    (hne : s ≠ t) (hb : F ∩ bd S = {s, t}) (hl : IsLineWithEnds F s t) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (ψ : Y → S),
      IsSurface Y ∧ IsCutting ψ F := by
  have : T2Space S := hS.2.1
  have := hS.locallyConnected
  set W : Set S := connectedComponent s
  have hW : IsClopen W := isClopen_connectedComponent
  have hW_surf : IsSurface W := isSurface_sub hS hW
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hsub : F ⊆ W := by
    obtain ⟨a, ha, rfl, -, -⟩ := hl.exists_arc
    exact (isPreconnected_range ha.1).subset_connectedComponent hl.left_mem
  have hsW : s ∈ W := mem_connectedComponent
  have htW : t ∈ W := hsub hl.right_mem
  let sW : W := ⟨s, hsW⟩
  let tW : W := ⟨t, htW⟩
  let FW : Set W := Subtype.val ⁻¹' F
  have hneW : sW ≠ tW := fun h => hne (congrArg Subtype.val h)
  have hbW : FW ∩ bd W = {sW, tW} := by
    ext y
    have hy_bd : y ∈ bd W ↔ y.1 ∈ bd S := mem_bd_sub hW.2
    have hy_F := Set.ext_iff.mp hb y.1
    simp only [FW, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_preimage,
      hy_bd, Subtype.ext_iff, sW, tW]
    simpa using hy_F
  have hlW : IsLineWithEnds FW sW tW := by
    obtain ⟨u', v', e1, e2, h5⟩ :=
      hl.pull (j := (Subtype.val : W → S)) IsEmbedding.subtypeVal (by rwa [Subtype.range_coe])
    have e3 : u' = sW := Subtype.ext e1
    have e4 : v' = tW := Subtype.ext e2
    rwa [e3, e4] at h5
  obtain ⟨YW, tYW, t2YW, ψW, hYW, hψW, -, -, -⟩ := exists_cut_arc hW_surf hneW hbW hlW
  have hWc_surf : IsSurface ↥Wᶜ := isSurface_sub hS hW.compl
  let Y : Type u := YW ⊕ ↥Wᶜ
  let ψ : Y → S := Sum.elim (Subtype.val ∘ ψW) Subtype.val
  refine ⟨Y, inferInstance, ψ, isSurface_sum hYW hWc_surf, ?_⟩
  refine ⟨continuous_sum_dom.mpr ⟨continuous_subtype_val.comp hψW.1, continuous_subtype_val⟩,
    ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ W
    · obtain ⟨y, hy⟩ := hψW.2.1 ⟨x, hx⟩
      exact ⟨Sum.inl y, congrArg Subtype.val hy⟩
    · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
  · rintro (y₁ | y₁) hy₁ (y₂ | y₂) hy₂ heq
    · congr 1
      exact hψW.2.2.1 hy₁ hy₂ (Subtype.ext heq)
    · exfalso
      change (ψW y₁).1 = y₂.1 at heq
      exact y₂.2 (heq ▸ (ψW y₁).2)
    · exfalso
      change y₁.1 = (ψW y₂).1 at heq
      exact y₁.2 (heq.symm ▸ (ψW y₂).2)
    · congr 1
      exact Subtype.ext heq
  · intro x hx
    have hxW : x ∈ W := hsub hx
    have hpre_eq : ψ ⁻¹' {x} = Sum.inl '' (ψW ⁻¹' {⟨x, hxW⟩}) := by
      ext (y | z)
      · simp only [ψ, Sum.elim_inl, comp_apply, mem_preimage, mem_singleton_iff, mem_image,
          Subtype.ext_iff]
        constructor
        · intro h
          exact ⟨y, h, rfl⟩
        · rintro ⟨y', hy', h_eq⟩
          cases h_eq
          exact hy'
      · simp only [ψ, Sum.elim_inr, mem_preimage, mem_singleton_iff, mem_image, reduceCtorEq,
          and_false, exists_false, iff_false]
        intro hzx
        exact z.2 (hzx ▸ hxW)
    rw [hpre_eq, ncard_image_of_injective _ Sum.inl_injective]
    exact hψW.2.2.2.1 ⟨x, hxW⟩ hx
  · rintro (y | z) hy
    · exact mem_bd_inl (hψW.2.2.2.2 hy)
    · exfalso
      exact z.2 (hsub hy)

/-- A compact line `L` disjoint from `F` lifts along a cutting `ψ : Y → S` to a line `ψ ⁻¹' L`
whose ends map to the ends of `L`. -/
theorem IsLineWithEnds.preimage_cutting {Y : Type u} [TopologicalSpace Y]
    [CompactSpace Y] [T2Space S] {ψ : Y → S} {F L : Set S} {u v : S}
    (hψ : IsCutting ψ F) (hl : IsLineWithEnds L u v) (hdisj : Disjoint L F) :
    ∃ u' v' : Y, ψ u' = u ∧ ψ v' = v ∧ ψ ⁻¹' {u} = {u'} ∧ ψ ⁻¹' {v} = {v'} ∧
      IsLineWithEnds (ψ ⁻¹' L) u' v' := by
  have hLF : ∀ x ∈ L, x ∉ F := Set.disjoint_left.mp hdisj
  have huL : u ∈ L := hl.left_mem
  have hvL : v ∈ L := hl.right_mem
  have hL_cl : IsClosed L := hl.isCompact.isClosed
  have hK_cl : IsClosed (ψ ⁻¹' L) := hL_cl.preimage hψ.1
  have : CompactSpace (ψ ⁻¹' L) := isCompact_iff_compactSpace.mp hK_cl.isCompact
  let g : (ψ ⁻¹' L) → L := fun y => ⟨ψ y.1, y.2⟩
  have hg_cont : Continuous g := (hψ.1.comp continuous_subtype_val).subtype_mk _
  have hg_inj : Injective g := by
    intro a b hab
    apply Subtype.ext
    exact hψ.2.2.1 (hLF _ a.2) (hLF _ b.2) (congrArg Subtype.val hab)
  have hg_surj : Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := hψ.2.1 x
    exact ⟨⟨y, hx⟩, rfl⟩
  let eKL : (ψ ⁻¹' L) ≃ₜ L :=
    hg_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hg_inj, hg_surj⟩)
  have heKL : ∀ y : ψ ⁻¹' L, (eKL y).1 = ψ y.1 := fun _ => rfl
  obtain ⟨f, hf0, hf1⟩ := hl
  let f' : unitInterval ≃ₜ (ψ ⁻¹' L) := f.trans eKL.symm
  let u' : Y := (f' 0).1
  let v' : Y := (f' 1).1
  have hu' : ψ u' = u := by
    have := heKL (f' 0)
    simp only [f', Homeomorph.trans_apply, Homeomorph.apply_symm_apply] at this
    exact this.symm.trans hf0
  have hv' : ψ v' = v := by
    have := heKL (f' 1)
    simp only [f', Homeomorph.trans_apply, Homeomorph.apply_symm_apply] at this
    exact this.symm.trans hf1
  have hpre_pt : ∀ {w : S} {w' : Y}, w ∈ L → ψ w' = w → ψ ⁻¹' {w} = {w'} := by
    intro w w' hw hww'
    ext y
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro hyw
      have hyF : ψ y ∉ F := by rw [hyw]; exact hLF w hw
      have hw'F : ψ w' ∉ F := by rw [hww']; exact hLF w hw
      exact hψ.2.2.1 hyF hw'F (hyw.trans hww'.symm)
    · rintro rfl
      exact hww'
  exact ⟨u', v', hu', hv', hpre_pt huL hu', hpre_pt hvL hv', ⟨f', rfl, rfl⟩⟩

/-- An *`X`-arc matching* on `S` is a finite set `𝒜` of pairwise disjoint proper `I`-arcs whose
ends lie in `X` and cover `X`. -/
def IsArcMatching (X : Set S) (𝒜 : Set (Set S)) : Prop :=
  𝒜.Finite ∧
  (∀ F ∈ 𝒜, ∃ u v : S, u ≠ v ∧ F ∩ bd S = {u, v} ∧ u ∈ X ∧ v ∈ X ∧ IsLineWithEnds F u v) ∧
  (∀ F₁ ∈ 𝒜, ∀ F₂ ∈ 𝒜, F₁ ≠ F₂ → Disjoint F₁ F₂) ∧
  X ⊆ ⋃₀ 𝒜

theorem IsLineWithEnds.symm {L : Set S} {u v : S} (h : IsLineWithEnds L u v) :
    IsLineWithEnds L v u := by
  rcases h with ⟨f, hf0, hf1⟩
  let rev : unitInterval ≃ₜ unitInterval :=
    { toFun := unitInterval.symm
      invFun := unitInterval.symm
      left_inv := unitInterval.symm_symm
      right_inv := unitInterval.symm_symm
      continuous_toFun := unitInterval.continuous_symm
      continuous_invFun := unitInterval.continuous_symm }
  refine ⟨rev.trans f, ?_, ?_⟩
  · simp [rev, hf1]
  · simp [rev, hf0]

private theorem cut_arc_matching_of_complement
    {S : Type u}
    [TopologicalSpace S]
    {X : Set S}
    (hX : X ⊆ bd S)
    [T2Space S]
    (s : S)
    (t : S)
    (F₀ : Set S)
    (Y : Type u)
    [TopologicalSpace Y]
    (ψ : Y → S)
    (hψ : IsCutting ψ F₀)
    [CompactSpace Y]
    (hF₀_cl : IsClosed F₀)
    (hXY_bd : (ψ ⁻¹' (X \ {s, t})) ⊆ bd Y)
    (𝒜 : Set (Set S))
    (h𝒜 : IsArcMatching X 𝒜)
    (F_s : Set S)
    (hFs_mem : F_s ∈ 𝒜)
    (hFs_bd : F_s ∩ bd S = {s, t})
    (hFs_line : IsLineWithEnds F_s s t)
    (α₁ : S ≃ₜ S)
    (h_disj_Fs : ∀ F ∈ (𝒜 \ {F_s}), Disjoint F F_s)
    (hα₁_symm_bd : ∀ x ∈ bd S, α₁.symm x = x)
    (h_disj_F₀ : ∀ F' ∈ ((fun F => ⇑α₁.symm '' F) '' (𝒜 \ {F_s})), Disjoint F' F₀) :
    IsArcMatching (ψ ⁻¹' (X \ {s, t}))
      ((fun F' => ψ ⁻¹' F') '' ((fun F => α₁.symm '' F) '' (𝒜 \ {F_s}))) := by
  let X_Y := ψ ⁻¹' (X \ {s, t})
  let 𝒜_rem := 𝒜 \ {F_s}
  let 𝒜' := (fun F => ⇑α₁.symm '' F) '' 𝒜_rem
  let 𝒜_Y := (fun F' => ψ ⁻¹' F') '' 𝒜'
  refine ⟨((h𝒜.1.sdiff).image _).image _, ?_, ?_, ?_⟩
  · rintro _ ⟨F', ⟨F, hF, rfl⟩, rfl⟩
    obtain ⟨u, v, huv, hF_bd, huX, hvX, hF_line⟩ := h𝒜.2.1 F hF.1
    have hu_bd : u ∈ bd S := hX huX
    have hv_bd : v ∈ bd S := hX hvX
    have hu_not_st : u ∉ ({s, t} : Set S) := by
      intro h_in
      have hu_Fs : u ∈ F_s := by
        have : u ∈ F_s ∩ bd S := hFs_bd.symm ▸ h_in
        exact this.1
      exact Set.disjoint_left.mp (h_disj_Fs F hF) hF_line.left_mem hu_Fs
    have hv_not_st : v ∉ ({s, t} : Set S) := by
      intro h_in
      have hv_Fs : v ∈ F_s := by
        have : v ∈ F_s ∩ bd S := hFs_bd.symm ▸ h_in
        exact this.1
      exact Set.disjoint_left.mp (h_disj_Fs F hF) hF_line.right_mem hv_Fs
    have hF'_bd : α₁.symm '' F ∩ bd S = {u, v} := by
      calc
        α₁.symm '' F ∩ bd S = α₁.symm '' F ∩ α₁.symm '' bd S := by
          rw [image_bd_homeomorph α₁.symm]
        _ = α₁.symm '' (F ∩ bd S) := (image_inter α₁.symm.injective).symm
        _ = α₁.symm '' {u, v} := by rw [hF_bd]
        _ = {u, v} := by
          rw [image_pair, hα₁_symm_bd u hu_bd, hα₁_symm_bd v hv_bd]
    have hF'_line : IsLineWithEnds (α₁.symm '' F) u v := by
      have hl' := hF_line.map_of_embedding α₁.symm.isEmbedding
      rwa [hα₁_symm_bd u hu_bd, hα₁_symm_bd v hv_bd] at hl'
    have hF'_disj : Disjoint (α₁.symm '' F) F₀ :=
      h_disj_F₀ _ ⟨F, hF, rfl⟩
    obtain ⟨u', v', hu', hv', hpre_u, hpre_v, hl_Y⟩ :=
      IsLineWithEnds.preimage_cutting hψ hF'_line hF'_disj
    refine ⟨u', v', fun h => huv (hu'.symm.trans ((congrArg ψ h).trans hv')),
      ?_, ?_, ?_, hl_Y⟩
    · ext y
      simp only [mem_inter_iff, mem_preimage, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hyF', hy_bd⟩
        have hy_not_F₀ : ψ y ∉ F₀ :=
          Set.disjoint_left.mp hF'_disj hyF'
        have hψy_bd : ψ y ∈ bd S := bd_of_bd hψ hF₀_cl hy_bd hy_not_F₀
        have hψy_uv : ψ y ∈ ({u, v} : Set S) := hF'_bd ▸ ⟨hyF', hψy_bd⟩
        rcases hψy_uv with h_eq | h_eq
        · left
          exact mem_singleton_iff.mp (hpre_u ▸ h_eq)
        · right
          exact mem_singleton_iff.mp (hpre_v ▸ mem_singleton_iff.mp h_eq)
      · rintro (rfl | rfl)
        · refine ⟨hF'_line.left_mem |> fun h => by rwa [← hu'] at h, ?_⟩
          exact hXY_bd (show y ∈ X_Y by
            change ψ y ∈ X \ {s, t}
            rw [hu']
            exact ⟨huX, hu_not_st⟩)
        · refine ⟨hF'_line.right_mem |> fun h => by rwa [← hv'] at h, ?_⟩
          exact hXY_bd (show y ∈ X_Y by
            change ψ y ∈ X \ {s, t}
            rw [hv']
            exact ⟨hvX, hv_not_st⟩)
    · change ψ u' ∈ X \ {s, t}
      rw [hu']
      exact ⟨huX, hu_not_st⟩
    · change ψ v' ∈ X \ {s, t}
      rw [hv']
      exact ⟨hvX, hv_not_st⟩
  · rintro _ ⟨F₁', ⟨F₁, hF₁, rfl⟩, rfl⟩ _ ⟨F₂', ⟨F₂, hF₂, rfl⟩, rfl⟩ hne_Y
    have hne_F : F₁ ≠ F₂ := fun h => hne_Y (by rw [h])
    have hdisj_img : Disjoint (α₁.symm '' F₁) (α₁.symm '' F₂) := by
      rw [Set.disjoint_left]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
      exact Set.disjoint_left.mp (h𝒜.2.2.1 F₁ hF₁.1 F₂ hF₂.1 hne_F)
        hx (α₁.symm.injective hyx ▸ hy)
    exact hdisj_img.preimage ψ
  · intro y hy
    have hψy_X' : ψ y ∈ X \ {s, t} := hy
    obtain ⟨F, hF_mem, hψy_F⟩ := h𝒜.2.2.2 hψy_X'.1
    have hF_ne_Fs : F ≠ F_s := by
      rintro rfl
      have : ψ y ∈ ({s, t} : Set S) := hFs_bd ▸ ⟨hψy_F, hX hψy_X'.1⟩
      exact hψy_X'.2 this
    refine ⟨ψ ⁻¹' (α₁.symm '' F), ⟨α₁.symm '' F, ⟨F, ⟨hF_mem, hF_ne_Fs⟩, rfl⟩, rfl⟩, ?_⟩
    change ψ y ∈ α₁.symm '' F
    rw [← hα₁_symm_bd (ψ y) (hX hψy_X'.1)]
    exact mem_image_of_mem α₁.symm hψy_F

/-- By induction on `|X|`, for any surface `S` and finite `X ⊆ bd S`, there are only finitely many
carriers `⋃₀ 𝒜` of `X`-arc matchings up to homeomorphisms of `S` fixing `bd S` pointwise. -/
theorem finite_arcMatching_classes :
    ∀ (n : ℕ) {S : Type u} [TopologicalSpace S], IsSurface S → ∀ {X : Set S},
      X ⊆ bd S → X.Finite → X.ncard = n →
      ∃ 𝓤 : Set (Set S), 𝓤.Finite ∧
        ∀ 𝒜 : Set (Set S), IsArcMatching X 𝒜 →
          ∃ U₀ ∈ 𝓤, ∃ α : S ≃ₜ S, α '' U₀ = ⋃₀ 𝒜 ∧ ∀ x ∈ bd S, α x = x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S _ hS X hX hXfin hn
    have : T2Space S := hS.2.1
    have : CompactSpace S := hS.1
    by_cases hXne : X.Nonempty
    · obtain ⟨s, hsX⟩ := hXne
      have hs_bd : s ∈ bd S := hX hsX
      have hX_diff_fin : (X \ {s}).Finite := hXfin.sdiff
      choose 𝓖_of h𝓖_fin h𝓖_mem h𝓖_cov using fun t : S => theorem_3_2_proof hS s t
      have h_pair_step : ∀ t ∈ X \ {s}, ∀ F₀ ∈ 𝓖_of t,
          ∃ 𝓤_sub : Set (Set S), 𝓤_sub.Finite ∧
            ∀ 𝒜 : Set (Set S), IsArcMatching X 𝒜 →
              (∃ F_s ∈ 𝒜, F_s ∩ bd S = {s, t} ∧ IsLineWithEnds F_s s t ∧ AreParallelIArcs F₀ F_s) →
              ∃ U₀ ∈ 𝓤_sub, ∃ α : S ≃ₜ S, α '' U₀ = ⋃₀ 𝒜 ∧ ∀ x ∈ bd S, α x = x := by
        intro t ht F₀ hF₀_mem
        have hst : s ≠ t := fun h => ht.2 (mem_singleton_iff.mpr h.symm)
        obtain ⟨hb₀, hl₀⟩ := h𝓖_mem t F₀ hF₀_mem
        obtain ⟨Y, tY, ψ, hY, hψ⟩ := exists_cut_arc_surface hS hst hb₀ hl₀
        have : CompactSpace Y := hY.1
        have : T2Space Y := hY.2.1
        have hF₀_cl : IsClosed F₀ := hl₀.isCompact.isClosed
        set X' : Set S := X \ {s, t}
        have hX'_sub_bd : X' ⊆ bd S := sdiff_subset.trans hX
        have hX'_disj_F₀ : Disjoint X' F₀ := by
          rw [Set.disjoint_left]
          intro x hx hxF₀
          have : x ∈ ({s, t} : Set S) := hb₀ ▸ ⟨hxF₀, hX'_sub_bd hx⟩
          exact hx.2 this
        set X_Y : Set Y := ψ ⁻¹' X'
        have hXY_bd : X_Y ⊆ bd Y := by
          intro y hy
          exact bd_lift hψ hF₀_cl (hX'_sub_bd hy) (Set.disjoint_left.mp hX'_disj_F₀ hy)
        have hψ_inj_XY : InjOn ψ X_Y := by
          intro y₁ hy₁ y₂ hy₂ h12
          exact hψ.2.2.1 (Set.disjoint_left.mp hX'_disj_F₀ hy₁)
            (Set.disjoint_left.mp hX'_disj_F₀ hy₂) h12
        have hψ_img_XY : ψ '' X_Y = X' := image_preimage_eq X' hψ.2.1
        have hX'_fin : X'.Finite := hXfin.sdiff
        have hXY_fin : X_Y.Finite := hX'_fin.preimage hψ_inj_XY
        have hXY_card : X_Y.ncard < n := by
          have h1 : X_Y.ncard = X'.ncard := by
            rw [← hψ_img_XY, hψ_inj_XY.ncard_image]
          have h2 : X'.ncard < X.ncard :=
            ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨sdiff_subset, fun h_eq => by
              have : s ∈ X' := h_eq ▸ hsX
              exact this.2 (mem_insert s {t})⟩) hXfin
          omega
        obtain ⟨𝓤_Y, h𝓤Y_fin, h𝓤Y_cov⟩ :=
          ih X_Y.ncard hXY_card hY hXY_bd hXY_fin rfl
        refine ⟨(fun U_Y => F₀ ∪ ψ '' U_Y) '' 𝓤_Y, h𝓤Y_fin.image _, ?_⟩
        intro 𝒜 h𝒜 ⟨F_s, hFs_mem, hFs_bd, hFs_line, α₁, hα₁_F, hα₁_bd⟩
        set 𝒜_rem : Set (Set S) := 𝒜 \ {F_s}
        have h_disj_Fs : ∀ F ∈ 𝒜_rem, Disjoint F F_s :=
          fun F hF => h𝒜.2.2.1 F hF.1 F_s hFs_mem hF.2
        have h_union_𝒜 : ⋃₀ 𝒜 = F_s ∪ ⋃₀ 𝒜_rem := by
          ext x
          simp only [mem_sUnion, mem_union]
          constructor
          · rintro ⟨F, hF, hxF⟩
            by_cases hFF : F = F_s
            · exact Or.inl (hFF ▸ hxF)
            · exact Or.inr ⟨F, ⟨hF, hFF⟩, hxF⟩
          · rintro (hx | ⟨F, ⟨hF, _⟩, hxF⟩)
            · exact ⟨F_s, hFs_mem, hx⟩
            · exact ⟨F, hF, hxF⟩
        set 𝒜' : Set (Set S) := (fun F => α₁.symm '' F) '' 𝒜_rem
        have hα₁_symm_bd : ∀ x ∈ bd S, α₁.symm x = x :=
          fun x hx => (α₁.symm_apply_eq).mpr (hα₁_bd x hx).symm
        have hα₁_symm_Fs : α₁.symm '' F_s = F₀ := by
          rw [← hα₁_F]
          exact α₁.symm_image_image F₀
        have h_disj_F₀ : ∀ F' ∈ 𝒜', Disjoint F' F₀ := by
          rintro _ ⟨F, hF, rfl⟩
          rw [← hα₁_symm_Fs]
          rw [Set.disjoint_left]
          rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
          exact Set.disjoint_left.mp (h_disj_Fs F hF) hx (α₁.symm.injective hyx ▸ hy)
        set 𝒜_Y : Set (Set Y) := (fun F' => ψ ⁻¹' F') '' 𝒜'
        have h𝒜Y_match : IsArcMatching X_Y 𝒜_Y := by
          exact cut_arc_matching_of_complement (S := S) (X := X) hX s t F₀ Y ψ hψ hF₀_cl hXY_bd 𝒜
            h𝒜 F_s hFs_mem hFs_bd hFs_line α₁ h_disj_Fs hα₁_symm_bd h_disj_F₀
        obtain ⟨U_Y, hUY_mem, H, hH_U, hH_bd⟩ := h𝓤Y_cov 𝒜_Y h𝒜Y_match
        have hH_fix_F₀ : ∀ z : Y, ψ z ∈ F₀ → H z = z :=
          fun z hz => hH_bd z (hψ.2.2.2.2 hz)
        obtain ⟨γ, hγ⟩ := exists_descend_cut hψ H hH_fix_F₀
        have hγ_bd : ∀ x ∈ bd S, γ x = x := by
          intro x hx
          obtain ⟨y, rfl⟩ := hψ.2.1 x
          by_cases hyF₀ : ψ y ∈ F₀
          · rw [hγ y, hH_fix_F₀ y hyF₀]
          · rw [hγ y, hH_bd y (bd_lift hψ hF₀_cl hx hyF₀)]
        have hγ_F₀ : γ '' F₀ = F₀ := by
          ext x
          constructor
          · rintro ⟨w, hw, rfl⟩
            obtain ⟨y, rfl⟩ := hψ.2.1 w
            rw [hγ y, hH_fix_F₀ y hw]
            exact hw
          · intro hx
            obtain ⟨y, rfl⟩ := hψ.2.1 x
            exact ⟨ψ y, hx, by rw [hγ y, hH_fix_F₀ y hx]⟩
        have h_sUnion_AY : ψ '' (⋃₀ 𝒜_Y) = ⋃₀ 𝒜' := by
          ext x
          simp only [𝒜_Y, mem_image, mem_sUnion, exists_exists_and_eq_and]
          constructor
          · rintro ⟨y, ⟨F', hF', hy⟩, rfl⟩
            exact ⟨F', hF', hy⟩
          · rintro ⟨F', hF', hx⟩
            obtain ⟨y, rfl⟩ := hψ.2.1 x
            exact ⟨y, ⟨F', hF', hx⟩, rfl⟩
        have hγ_UY : γ '' (ψ '' U_Y) = ⋃₀ 𝒜' := by
          calc
            γ '' (ψ '' U_Y) = ψ '' (H '' U_Y) := by
              ext x
              simp only [mem_image, exists_exists_and_eq_and]
              constructor
              · rintro ⟨y, hy, rfl⟩
                exact ⟨y, hy, (hγ y).symm⟩
              · rintro ⟨y, hy, rfl⟩
                exact ⟨y, hy, hγ y⟩
            _ = ψ '' (⋃₀ 𝒜_Y) := by rw [hH_U]
            _ = ⋃₀ 𝒜' := h_sUnion_AY
        have hα₁_A' : α₁ '' (⋃₀ 𝒜') = ⋃₀ 𝒜_rem := by
          ext x
          simp only [𝒜', mem_image, mem_sUnion, exists_exists_and_eq_and]
          constructor
          · rintro ⟨w, ⟨F, hF, ⟨z, hz, rfl⟩⟩, rfl⟩
            exact ⟨F, hF, by simpa using hz⟩
          · rintro ⟨F, hF, hx⟩
            exact ⟨α₁.symm x, ⟨F, hF, mem_image_of_mem α₁.symm hx⟩, α₁.apply_symm_apply x⟩
        let α : S ≃ₜ S := γ.trans α₁
        refine ⟨F₀ ∪ ψ '' U_Y, mem_image_of_mem _ hUY_mem, α, ?_, fun x hx => ?_⟩
        · calc
            α '' (F₀ ∪ ψ '' U_Y) = α₁ '' (γ '' (F₀ ∪ ψ '' U_Y)) := by
              ext x
              simp [α, Homeomorph.trans_apply]
            _ = α₁ '' (γ '' F₀ ∪ γ '' (ψ '' U_Y)) := by rw [image_union]
            _ = α₁ '' (F₀ ∪ ⋃₀ 𝒜') := by rw [hγ_F₀, hγ_UY]
            _ = α₁ '' F₀ ∪ α₁ '' (⋃₀ 𝒜') := image_union α₁ F₀ (⋃₀ 𝒜')
            _ = F_s ∪ ⋃₀ 𝒜_rem := by rw [hα₁_F, hα₁_A']
            _ = ⋃₀ 𝒜 := h_union_𝒜.symm
        · simp [α, Homeomorph.trans_apply, hγ_bd x hx, hα₁_bd x hx]
      choose 𝓤_sub h𝓤_sub_fin h𝓤_sub_cov using h_pair_step
      refine ⟨⋃ t ∈ X \ {s}, ⋃ (ht : t ∈ X \ {s}), ⋃ F₀ ∈ 𝓖_of t, ⋃ (hF₀ : F₀ ∈ 𝓖_of t),
        𝓤_sub t ht F₀ hF₀, ?_, ?_⟩
      · refine hX_diff_fin.biUnion fun t ht => finite_iUnion fun _ => ?_
        exact (h𝓖_fin t).biUnion fun F₀ hF₀ => finite_iUnion fun _ => h𝓤_sub_fin t ht F₀ hF₀
      · intro 𝒜 h𝒜
        obtain ⟨F_s, hFs_mem, hs_Fs⟩ := h𝒜.2.2.2 hsX
        obtain ⟨u, v, huv, hFs_bd, huX, hvX, hFs_line⟩ := h𝒜.2.1 F_s hFs_mem
        have hs_uv : s ∈ ({u, v} : Set S) := hFs_bd ▸ ⟨hs_Fs, hs_bd⟩
        have h_ex_t : ∃ t ∈ X \ {s}, F_s ∩ bd S = {s, t} ∧ IsLineWithEnds F_s s t := by
          rcases hs_uv with rfl | hs_v
          · exact ⟨v, ⟨hvX, fun h => huv (mem_singleton_iff.mp h).symm⟩, hFs_bd, hFs_line⟩
          · have hsv : s = v := mem_singleton_iff.mp hs_v
            subst hsv
            exact ⟨u, ⟨huX, fun h => huv (mem_singleton_iff.mp h)⟩,
              by rw [pair_comm]; exact hFs_bd, hFs_line.symm⟩
        obtain ⟨t, ht, hFs_bd', hFs_line'⟩ := h_ex_t
        obtain ⟨F₀, hF₀, hpar⟩ := h𝓖_cov t F_s hFs_bd' hFs_line'
        obtain ⟨U₀, hU₀, α, hα_U, hα_bd⟩ :=
          h𝓤_sub_cov t ht F₀ hF₀ 𝒜 h𝒜 ⟨F_s, hFs_mem, hFs_bd', hFs_line', hpar⟩
        refine ⟨U₀, ?_, α, hα_U, hα_bd⟩
        exact mem_iUnion₂.mpr ⟨t, ht, mem_iUnion.mpr ⟨ht,
          mem_iUnion₂.mpr ⟨F₀, hF₀, mem_iUnion.mpr ⟨hF₀, hU₀⟩⟩⟩⟩
    · have hX_emp : X = ∅ := not_nonempty_iff_eq_empty.mp hXne
      subst hX_emp
      refine ⟨{∅}, finite_singleton ∅, fun 𝒜 h𝒜 => ⟨∅, mem_singleton ∅, Homeomorph.refl S, ?_,
        fun _ _ => rfl⟩⟩
      simp only [Homeomorph.refl_apply, image_id]
      ext x
      simp only [mem_empty_iff_false, mem_sUnion, false_iff, not_exists, not_and]
      intro F hF _
      obtain ⟨u, _, _, _, hu, _, _⟩ := h𝒜.2.1 F hF
      exact hu

/-- Every `X`-matching `G` gives an `X`-arc matching `closure '' G.E` with carrier `G.U`. -/
theorem isArcMatching_of_isXMatching {X : Set S} (hX : X ⊆ bd S)
    {G : Drawing S} (hG : IsXMatching X G) :
    IsArcMatching X (closure '' G.E) ∧ ⋃₀ (closure '' G.E) = G.U := by
  rcases hG with ⟨⟨hprop, hV_bd, hval⟩, rfl⟩
  have htilde_eq : ∀ e ∈ G.E, tilde e = closure e ∩ G.V := by
    intro e he
    have hdiff := G.closure_diff_V he
    ext x
    simp only [tilde, mem_sdiff, mem_inter_iff]
    constructor
    · rintro ⟨hxe, hxne⟩
      refine ⟨hxe, ?_⟩
      by_contra hxV
      apply hxne
      rw [← hdiff]
      exact ⟨hxe, hxV⟩
    · rintro ⟨hxe, hxV⟩
      refine ⟨hxe, fun h_in => ?_⟩
      rw [← hdiff] at h_in
      exact h_in.2 hxV
  have h_no_loop : ∀ e ∈ G.E,
      ∃ u v : S, u ≠ v ∧ closure e ∩ G.V = {u, v} ∧ IsLineWithEnds (closure e) u v ∧
        (tilde e).ncard = 2 := by
    intro e he
    rcases G.edge_cond e he with ⟨u, v, huv, hcap, hL⟩ | ⟨u, hcap, _⟩
    · refine ⟨u, v, huv, hcap, hL, ?_⟩
      rw [htilde_eq e he, hcap, ncard_pair huv]
    · exfalso
      have hu_mem : u ∈ closure e ∩ G.V := hcap.symm ▸ mem_singleton u
      have hinc : G.VertexIncident u e := ⟨hu_mem.2, Or.inl he, hu_mem.1⟩
      have htilde1 : (tilde e).ncard = 1 := by
        rw [htilde_eq e he, hcap, ncard_singleton]
      have h_sub : ({e} : Set (Set S)) ⊆ {f ∈ G.E | G.VertexIncident u f ∧ (tilde f).ncard = 1}
        := by
        rintro f rfl
        exact ⟨he, hinc, htilde1⟩
      have h_le : 1 ≤ {f ∈ G.E | G.VertexIncident u f ∧ (tilde f).ncard = 1}.ncard := by
        have := ncard_le_ncard h_sub (G.finite_edges.subset fun _ hf => hf.1)
        simpa using this
      have h_val_u := hval u hu_mem.2
      unfold vertexValency at h_val_u
      omega
  have h_disj_cl : ∀ e₁ ∈ G.E, ∀ e₂ ∈ G.E, e₁ ≠ e₂ → Disjoint (closure e₁) (closure e₂) := by
    intro e₁ he₁ e₂ he₂ hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    by_cases hxV : x ∈ G.V
    · obtain ⟨_, _, _, _, _, ht1⟩ := h_no_loop e₁ he₁
      obtain ⟨_, _, _, _, _, ht2⟩ := h_no_loop e₂ he₂
      have h_sub : ({e₁, e₂} : Set (Set S)) ⊆
          {f ∈ G.E | G.VertexIncident x f ∧ (tilde f).ncard = 2} := by
        rintro f (rfl | rfl)
        · exact ⟨he₁, ⟨hxV, Or.inl he₁, hx1⟩, ht1⟩
        · exact ⟨he₂, ⟨hxV, Or.inl he₂, hx2⟩, ht2⟩
      have h_le : 2 ≤ {f ∈ G.E | G.VertexIncident x f ∧ (tilde f).ncard = 2}.ncard := by
        have := ncard_le_ncard h_sub (G.finite_edges.subset fun _ hf => hf.1)
        rwa [ncard_pair hne] at this
      have h_val_x := hval x hxV
      unfold vertexValency at h_val_x
      omega
    · have hx_e₁ : x ∈ e₁ := by rw [← G.closure_diff_V he₁]; exact ⟨hx1, hxV⟩
      have hx_e₂ : x ∈ e₂ := by rw [← G.closure_diff_V he₂]; exact ⟨hx2, hxV⟩
      exact hne (G.edge_eq_of_mem he₁ he₂ hx_e₁ hx_e₂)
  have hV_sub : G.V ⊆ ⋃₀ (closure '' G.E) := by
    intro v hv
    have h_val_v := hval v hv
    unfold vertexValency at h_val_v
    have h_pos : 0 < {f ∈ G.E | G.VertexIncident v f ∧ (tilde f).ncard = 2}.ncard := by
      by_contra h0
      have h0' : {f ∈ G.E | G.VertexIncident v f ∧ (tilde f).ncard = 2}.ncard = 0 := by omega
      omega
    have hfinite : {f ∈ G.E | G.VertexIncident v f ∧ (tilde f).ncard = 2}.Finite :=
      G.finite_edges.subset fun _ hf => hf.1
    obtain ⟨e, he, hinc, -⟩ := (ncard_pos hfinite).mp h_pos
    exact ⟨closure e, mem_image_of_mem closure he, hinc.2.2⟩
  refine ⟨⟨G.finite_edges.image closure, ?_, ?_, hV_sub⟩, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨u, v, huv, hcap, hL, -⟩ := h_no_loop e he
    have huV : u ∈ G.V := by
      have : u ∈ closure e ∩ G.V := hcap ▸ mem_insert u {v}
      exact this.2
    have hvV : v ∈ G.V := by
      have : v ∈ closure e ∩ G.V := hcap ▸ mem_insert_of_mem u rfl
      exact this.2
    refine ⟨u, v, huv, ?_, huV, hvV, hL⟩
    apply Subset.antisymm
    · intro x ⟨hxe, hx_bd⟩
      have hxV : x ∈ G.V := hprop ⟨hx_bd, G.closure_subset_U he hxe⟩
      rw [← hcap]
      exact ⟨hxe, hxV⟩
    · rintro x (rfl | rfl)
      · exact ⟨hL.left_mem, hV_bd huV⟩
      · exact ⟨hL.right_mem, hV_bd hvV⟩
  · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ hne
    exact h_disj_cl e₁ he₁ e₂ he₂ fun h => hne (congrArg closure h)
  · apply Subset.antisymm
    · rintro x ⟨_, ⟨e, he, rfl⟩, hx⟩
      exact G.closure_subset_U he hx
    · intro x hxU
      by_cases hxV : x ∈ G.V
      · exact hV_sub hxV
      · have he : pathComponentIn (G.U \ G.V) x ∈ G.E :=
          pathComponentIn_mem_arcComponentsIn ⟨hxU, hxV⟩
        exact ⟨closure (pathComponentIn (G.U \ G.V) x), mem_image_of_mem closure he,
          subset_closure (mem_pathComponentIn_self ⟨hxU, hxV⟩)⟩

instance : Inhabited (Drawing S) := ⟨emptyDrawing S⟩

/-- Graph Minors VII, (3.3) (page 219):
"(3.3) *For any surface $\Sigma$ and finite $X \subseteq bd(\Sigma)$, there are only finitely many
congruence classes of $X$-matchings.*" -/
theorem theorem_3_3_proof (hS : IsSurface S) {X : Set S} (hX : X ⊆ bd S) (hXfin : X.Finite) :
    ∃ 𝓜 : Set (Drawing S), 𝓜.Finite ∧
      (∀ G₀ ∈ 𝓜, IsXMatching X G₀) ∧
      ∀ G : Drawing S, IsXMatching X G → ∃ G₀ ∈ 𝓜, AreCongruentMatchings G₀ G := by
  have : T2Space S := hS.2.1
  obtain ⟨𝓤, h𝓤_fin, h𝓤_cov⟩ := finite_arcMatching_classes X.ncard hS hX hXfin rfl
  let good (U₀ : Set S) : Prop :=
    ∃ G₀ : Drawing S, IsXMatching X G₀ ∧
      ∃ α : S ≃ₜ S, α '' U₀ = G₀.U ∧ ∀ x ∈ bd S, α x = x
  set 𝓤' : Set (Set S) := {U₀ ∈ 𝓤 | good U₀}
  have h𝓤'_fin : 𝓤'.Finite := h𝓤_fin.subset (sep_subset 𝓤 good)
  have h_rep : ∀ U₀ ∈ 𝓤', ∃ G₀ : Drawing S, IsXMatching X G₀ ∧
      ∃ α : S ≃ₜ S, α '' U₀ = G₀.U ∧ ∀ x ∈ bd S, α x = x :=
    fun _ h => h.2
  choose! rep hrep_match hrep_congr using h_rep
  refine ⟨rep '' 𝓤', h𝓤'_fin.image rep, ?_, ?_⟩
  · rintro _ ⟨U₀, hU₀, rfl⟩
    exact hrep_match U₀ hU₀
  · intro G hG
    obtain ⟨h𝒜, hU_eq⟩ := isArcMatching_of_isXMatching hX hG
    obtain ⟨U₀, hU₀_mem, α, hα_U, hα_bd⟩ := h𝓤_cov (closure '' G.E) h𝒜
    rw [hU_eq] at hα_U
    have hU₀_good : U₀ ∈ {U₀ ∈ 𝓤 | good U₀} := ⟨hU₀_mem, ⟨G, hG, α, hα_U, hα_bd⟩⟩
    obtain ⟨α₀, hα₀_U, hα₀_bd⟩ := hrep_congr U₀ hU₀_good
    refine ⟨rep U₀, mem_image_of_mem rep hU₀_good, α₀.symm.trans α, ?_, fun x hx => ?_⟩
    · calc
        (α₀.symm.trans α) '' (rep U₀).U = α '' (α₀.symm '' (α₀ '' U₀)) := by
          rw [← hα₀_U]
          ext y
          simp [Homeomorph.trans_apply]
        _ = α '' U₀ := by congr 1; exact α₀.symm_image_image U₀
        _ = G.U := hα_U
    · have hx₀ : α₀.symm x = x := (α₀.symm_apply_eq).mpr (hα₀_bd x hx).symm
      simp [Homeomorph.trans_apply, hx₀, hα_bd x hx]

/-! ## 4. Properties of `CurveTracesWalk` -/

open unitInterval

theorem _root_.GraphMinor.Surface.CurveTracesWalk.endpoints {Γ : Drawing S} {u v : S} {φ : Curve S}
    {W : GraphWalk Γ.toGraph u v} (h : CurveTracesWalk Γ φ W) :
    φ 0 = u ∧ φ 1 = v := by
  induction h with
  | nil _ _ hconst => exact ⟨hconst 0, hconst 1⟩
  | cons _ _ _ _ _ _ hconcat _ =>
    rcases hconcat with ⟨_, _, _, h0, _, h1, _, _⟩
    exact ⟨h0, h1⟩

theorem _root_.GraphMinor.Surface.CurveTracesWalk.range_subset_U {Γ : Drawing S} {u v : S} {φ :
  Curve S}
    {W : GraphWalk Γ.toGraph u v} (h : CurveTracesWalk Γ φ W) :
    range φ ⊆ Γ.U := by
  induction h with
  | nil hv φ hconst =>
    rintro _ ⟨x, rfl⟩
    rw [hconst x]
    exact Γ.V_subset_U hv
  | cons hlink _ _ φ _ _ hconcat ih =>
    rcases hconcat with ⟨t₀, _, _, _, _, _, hle, hge⟩
    rintro _ ⟨x, rfl⟩
    rcases le_total x.1 t₀.1 with hx | hx
    · exact Γ.closure_subset_U hlink.1 (hle x hx)
    · exact ih (hge x hx)

/-- Every edge closure `closure e` (`e ∈ Γ.E`) is path-connected between its ends. -/
theorem isLink_joinedIn_closure {Γ : Drawing S} {e : Set S} {u v : S}
    (hlink : Γ.toGraph.IsLink e u v) : JoinedIn (closure e) u v := by
  have huv_mem : ({u, v} : Set S) ⊆ closure e := by
    have hcap : closure e ∩ Γ.V = {u, v} := hlink.2.2.2
    rw [← hcap]
    exact inter_subset_left
  have hu : u ∈ closure e := huv_mem (mem_insert u {v})
  have hv : v ∈ closure e := huv_mem (mem_insert_of_mem u rfl)
  rcases Γ.edge_cond e hlink.1 with ⟨a, b, _, _, f, _, _⟩ | ⟨a, _, ⟨f⟩⟩
  · let p0 : Path (f.symm ⟨u, hu⟩) (f.symm ⟨v, hv⟩) :=
      { toContinuousMap :=
          ⟨fun t => ⟨(1 - t.1) * (f.symm ⟨u, hu⟩).1 + t.1 * (f.symm ⟨v, hv⟩).1,
            convex_Icc (0 : ℝ) 1 (f.symm ⟨u, hu⟩).2 (f.symm ⟨v, hv⟩).2
              (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel 1 t.1)⟩, by fun_prop⟩
        source' := by ext; simp
        target' := by ext; simp }
    let p : Path u v :=
      { toContinuousMap :=
          ⟨fun t => (f (p0 t)).1, continuous_subtype_val.comp (f.continuous.comp p0.continuous)⟩
        source' := by
          change (f (p0 0)).1 = u
          rw [p0.source, f.apply_symm_apply]
        target' := by
          change (f (p0 1)).1 = v
          rw [p0.target, f.apply_symm_apply] }
    exact ⟨p, fun t => (f (p0 t)).2⟩
  · have hpc : IsPathConnected (closure e) := by
      have hIcc : IsPathConnected (Icc (0 : ℝ) 1) :=
        (convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, left_mem_Icc.mpr zero_le_one⟩
      have himg : (fun t : ℝ => (f (ee t)).1) '' Icc 0 1 = closure e := by
        ext x
        constructor
        · rintro ⟨t, _, rfl⟩
          exact (f _).2
        · intro hx
          obtain ⟨t, ht, ht_eq⟩ := exists_param (f.symm ⟨x, hx⟩)
          refine ⟨t, Ico_subset_Icc_self ht, ?_⟩
          change (f (ee t)).1 = x
          rw [ht_eq, f.apply_symm_apply]
      rw [← himg]
      exact hIcc.image (continuous_subtype_val.comp (f.continuous.comp continuous_ee))
    exact hpc.joinedIn u hu v hv

/-- Concatenation of two curves `φ₁, φ₂ : Curve S` with `φ₁ 1 = φ₂ 0` at `t₀ = 1/2`. -/
noncomputable def concatCurves (φ₁ φ₂ : Curve S) (h : φ₁ 1 = φ₂ 0) : Curve S where
  toFun x :=
    if x.1 ≤ 1 / 2 then φ₁ (projIcc 0 1 zero_le_one (2 * x.1))
    else φ₂ (projIcc 0 1 zero_le_one (2 * x.1 - 1))
  continuous_toFun := by
    refine Continuous.if_le ?_ ?_ continuous_subtype_val continuous_const (fun x hx => ?_)
    · exact φ₁.continuous.comp (continuous_projIcc.comp (by fun_prop))
    · exact φ₂.continuous.comp (continuous_projIcc.comp (by fun_prop))
    · have hp1 : projIcc 0 1 zero_le_one (2 * x.1) = 1 := by
        ext; change max (0 : ℝ) (min 1 (2 * x.1)) = 1; rw [hx]; norm_num
      have hp0 : projIcc 0 1 zero_le_one (2 * x.1 - 1) = 0 := by
        ext; change max (0 : ℝ) (min 1 (2 * x.1 - 1)) = 0; rw [hx]; norm_num
      rw [hp1, hp0, h]

/-- Every walk `W : GraphWalk Γ.toGraph u v` is traced by some curve `φ : Curve S` in the sense of
`CurveTracesWalk`. -/
theorem exists_curveTracesWalk {Γ : Drawing S} {u v : S} (W : GraphWalk Γ.toGraph u v) :
    ∃ φ : Curve S, CurveTracesWalk Γ φ W := by
  induction W with
  | nil hv =>
    exact ⟨ContinuousMap.const unitInterval _, .nil hv _ (fun _ => rfl)⟩
  | @cons u v w e hlink rest ih =>
    obtain ⟨p₁, hp₁⟩ := isLink_joinedIn_closure hlink
    obtain ⟨φ₂, hφ₂⟩ := ih
    obtain ⟨hφ₂0, hφ₂1⟩ := hφ₂.endpoints
    let φ₁ : Curve S := p₁.toContinuousMap
    have h12 : φ₁ 1 = φ₂ 0 := p₁.target.trans hφ₂0.symm
    let φ : Curve S := concatCurves φ₁ φ₂ h12
    refine ⟨φ, .cons hlink φ₁ φ₂ φ ⟨p₁.source, p₁.target, ?_⟩ hφ₂ ?_⟩
    · rintro _ ⟨x, rfl⟩
      exact hp₁ x
    · let t₀ : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
      refine ⟨t₀, by norm_num [t₀], by norm_num [t₀], ?_, ?_, ?_, ?_, ?_⟩
      · change (if ((0 : unitInterval) : ℝ) ≤ 1 / 2 then _ else _) = u
        have hle : ((0 : unitInterval) : ℝ) ≤ 1 / 2 := by norm_num
        simp only [hle, ↓reduceIte]
        have hp : projIcc 0 1 zero_le_one (2 * ((0 : unitInterval) : ℝ)) = 0 := by
          ext; change max (0 : ℝ) (min 1 (2 * 0)) = 0; norm_num
        rw [hp]
        exact p₁.source
      · change (if (1 / 2 : ℝ) ≤ 1 / 2 then _ else _) = v
        simp only [le_refl, ↓reduceIte]
        have hp : projIcc 0 1 zero_le_one (2 * (1 / 2 : ℝ)) = 1 := by
          ext; change max (0 : ℝ) (min 1 (2 * (1 / 2))) = 1; norm_num
        rw [hp]
        exact p₁.target
      · change (if ((1 : unitInterval) : ℝ) ≤ 1 / 2 then _ else _) = w
        have hnot : ¬ (((1 : unitInterval) : ℝ) ≤ 1 / 2) := by norm_num
        simp only [hnot, ↓reduceIte]
        have hp : projIcc 0 1 zero_le_one (2 * ((1 : unitInterval) : ℝ) - 1) = 1 := by
          ext; change max (0 : ℝ) (min 1 (2 * 1 - 1)) = 1; norm_num
        rw [hp]
        exact hφ₂1
      · intro x hx
        change (if x.1 ≤ 1 / 2 then _ else _) ∈ closure e
        have hx' : x.1 ≤ 1 / 2 := hx
        simp only [hx', ↓reduceIte]
        exact hp₁ _
      · intro x hx
        change (if x.1 ≤ 1 / 2 then _ else _) ∈ range φ₂
        by_cases hx' : x.1 ≤ 1 / 2
        · have h_eq : x.1 = 1 / 2 := le_antisymm hx' hx
          simp only [hx', ↓reduceIte]
          have hp : projIcc 0 1 zero_le_one (2 * x.1) = 1 := by
            ext; change max (0 : ℝ) (min 1 (2 * x.1)) = 1; rw [h_eq]; norm_num
          rw [hp, h12]
          exact mem_range_self 0
        · simp only [hx', ↓reduceIte]
          exact mem_range_self _

/-! ## 5. Homeomorphism Transport of Drawings, Walks, Curves, and Homotopy -/

theorem mapDrawingHomeo_E {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S') (Γ : Drawing S) :
    (mapDrawingHomeo α Γ).E = (image α) '' Γ.E := by
  change arcComponentsIn (α '' Γ.U \ α '' Γ.V) = (image α) '' arcComponentsIn (Γ.U \ Γ.V)
  rw [← image_sdiff α.injective, arcComponentsIn_image_homeo]

theorem mapDrawingHomeo_isLink {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S') {Γ : Drawing S}
    {e : Set S} {u v : S} (h : Γ.toGraph.IsLink e u v) :
    (mapDrawingHomeo α Γ).toGraph.IsLink (α '' e) (α u) (α v) := by
  rcases h with ⟨he, hu, hv, hcap⟩
  refine ⟨?_, mem_image_of_mem α hu, mem_image_of_mem α hv, ?_⟩
  · rw [mapDrawingHomeo_E]
    exact mem_image_of_mem (image α) he
  · change closure (α '' e) ∩ α '' Γ.V = {α u, α v}
    rw [← α.image_closure, ← image_inter α.injective, hcap, image_pair]

/-- Transport of a walk `W` in `Γ.toGraph` along a homeomorphism `α : S ≃ₜ S'`. -/
def mapWalkHomeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S') {Γ : Drawing S}
    {u v : S} : GraphWalk Γ.toGraph u v → GraphWalk (mapDrawingHomeo α Γ).toGraph (α u) (α v)
  | .nil hv => .nil (mem_image_of_mem α hv)
  | .cons hlink rest => .cons (mapDrawingHomeo_isLink α hlink) (mapWalkHomeo α rest)

theorem support_mapWalkHomeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {Γ : Drawing S} {u v : S} (W : GraphWalk Γ.toGraph u v) :
    (mapWalkHomeo α W).support = W.support.map α := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih => simp [mapWalkHomeo, GraphWalk.support, ih]

theorem edges_mapWalkHomeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {Γ : Drawing S} {u v : S} (W : GraphWalk Γ.toGraph u v) :
    (mapWalkHomeo α W).edges = W.edges.map (image α) := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih => simp [mapWalkHomeo, GraphWalk.edges, ih]

theorem length_mapWalkHomeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {Γ : Drawing S} {u v : S} (W : GraphWalk Γ.toGraph u v) :
    (mapWalkHomeo α W).length = W.length := by
  simp [GraphWalk.length, edges_mapWalkHomeo]

theorem isSimple_mapWalkHomeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {Γ : Drawing S} {u v : S} {W : GraphWalk Γ.toGraph u v} (hW : W.IsSimple) :
    (mapWalkHomeo α W).IsSimple := by
  unfold GraphWalk.IsSimple at hW ⊢
  rw [support_mapWalkHomeo]
  exact hW.map α.injective

theorem isSimpleClosed_mapWalkHomeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {Γ : Drawing S} {u : S} {W : GraphWalk Γ.toGraph u u} (hW : W.IsSimpleClosed) :
    (mapWalkHomeo α W).IsSimpleClosed := by
  rcases hW with ⟨hs, he⟩
  refine ⟨?_, ?_⟩
  · rw [support_mapWalkHomeo, ← List.map_tail]
    exact hs.map α.injective
  · rw [edges_mapWalkHomeo]
    exact he.map (image_injective.mpr α.injective)

theorem mapDrawingHomeo_symm_mapDrawingHomeo {S' : Type v} [TopologicalSpace S']
    (α : S ≃ₜ S') (Γ : Drawing S) :
    mapDrawingHomeo α.symm (mapDrawingHomeo α Γ) = Γ := by
  cases Γ
  simp only [mapDrawingHomeo, Drawing.mk.injEq]
  exact ⟨α.symm_image_image _, α.symm_image_image _⟩

theorem _root_.GraphMinor.Surface.CurveTracesWalk.map_homeo {S' : Type v} [TopologicalSpace S']
  (α : S ≃ₜ S')
    {Γ : Drawing S} {u v : S} {φ : Curve S} {W : GraphWalk Γ.toGraph u v}
    (h : CurveTracesWalk Γ φ W) :
    CurveTracesWalk (mapDrawingHomeo α Γ)
      (ContinuousMap.comp ⟨α, α.continuous⟩ φ) (mapWalkHomeo α W) := by
  induction h with
  | nil hv φ hconst =>
    have hv' : α _ ∈ (mapDrawingHomeo α Γ).V := mem_image_of_mem α hv
    refine .nil hv' _ (fun x => ?_)
    change α (φ x) = α _
    rw [hconst x]
  | cons hlink φ₁ φ₂ φ hφ₁ hφ₂ hconcat ih =>
    rcases hconcat with ⟨t₀, ht0, ht1, h0, htv, h1, hle, hge⟩
    refine .cons (mapDrawingHomeo_isLink α hlink)
      (ContinuousMap.comp ⟨α, α.continuous⟩ φ₁)
      (ContinuousMap.comp ⟨α, α.continuous⟩ φ₂)
      (ContinuousMap.comp ⟨α, α.continuous⟩ φ)
      ⟨by change α (φ₁ 0) = _; rw [hφ₁.1],
       by change α (φ₁ 1) = _; rw [hφ₁.2.1], ?_⟩
      ih
      ⟨t₀, ht0, ht1,
       by change α (φ 0) = _; rw [h0],
       by change α (φ t₀) = _; rw [htv],
       by change α (φ 1) = _; rw [h1], ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      rw [← α.image_closure]
      exact mem_image_of_mem α (hφ₁.2.2 (mem_range_self x))
    · intro x hx
      rw [← α.image_closure]
      exact mem_image_of_mem α (hle x hx)
    · intro x hx
      obtain ⟨y, hy⟩ := hge x hx
      exact ⟨y, by change α (φ₂ y) = α (φ x); rw [hy]⟩

/-! ## 6. Equivalence of Curve Homotopy and `IsFlat.curvesHomotopic` -/

theorem CurvesHomotopicIn.refl {Z : Set S} {φ : Curve S} (hZ : range φ ⊆ Z) :
    CurvesHomotopicIn Z φ φ :=
  ⟨φ.comp ⟨Prod.fst, continuous_fst⟩,
   fun p => hZ (mem_range_self p.1),
   fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem CurvesHomotopicIn.symm {Z : Set S} {φ₀ φ₁ : Curve S}
    (h : CurvesHomotopicIn Z φ₀ φ₁) : CurvesHomotopicIn Z φ₁ φ₀ := by
  rcases h with ⟨ψ, hZ, h0, h1, hy0, hy0', hy1, hy1'⟩
  refine ⟨ψ.comp ⟨fun p => (p.1, unitInterval.symm p.2), by fun_prop⟩,
    fun p => hZ _, fun x => by simpa using h1 x, fun x => by simpa using h0 x,
    fun y => hy0' _, fun y => hy0 _, fun y => hy1' _, fun y => hy1 _⟩

theorem CurvesHomotopicIn.trans {Z : Set S} {φ₀ φ₁ φ₂ : Curve S}
    (h₁ : CurvesHomotopicIn Z φ₀ φ₁) (h₂ : CurvesHomotopicIn Z φ₁ φ₂) :
    CurvesHomotopicIn Z φ₀ φ₂ := by
  rcases h₁ with ⟨ψ₁, hZ₁, h₁0, h₁1, h₁y0, h₁y0', h₁y1, h₁y1'⟩
  rcases h₂ with ⟨ψ₂, hZ₂, h₂0, h₂1, h₂y0, h₂y0', h₂y1, h₂y1'⟩
  let f₁ : C(unitInterval × unitInterval, S) :=
    ψ₁.comp ⟨fun p => (p.1, projIcc 0 1 zero_le_one (2 * p.2.1)), by fun_prop⟩
  let f₂ : C(unitInterval × unitInterval, S) :=
    ψ₂.comp ⟨fun p => (p.1, projIcc 0 1 zero_le_one (2 * p.2.1 - 1)), by fun_prop⟩
  have hcont : Continuous (fun p : unitInterval × unitInterval =>
      if p.2.1 ≤ 1 / 2 then f₁ p else f₂ p) := by
    refine Continuous.if_le f₁.continuous f₂.continuous
      (continuous_subtype_val.comp continuous_snd) continuous_const (fun p hp => ?_)
    have hp1 : projIcc 0 1 zero_le_one (2 * p.2.1) = 1 := by
      ext; change max (0 : ℝ) (min 1 (2 * p.2.1)) = 1; rw [hp]; norm_num
    have hp0 : projIcc 0 1 zero_le_one (2 * p.2.1 - 1) = 0 := by
      ext; change max (0 : ℝ) (min 1 (2 * p.2.1 - 1)) = 0; rw [hp]; norm_num
    change ψ₁ (p.1, projIcc 0 1 zero_le_one (2 * p.2.1)) =
      ψ₂ (p.1, projIcc 0 1 zero_le_one (2 * p.2.1 - 1))
    rw [hp1, hp0, h₁1 p.1, h₂0 p.1]
  refine ⟨⟨fun p => if p.2.1 ≤ 1 / 2 then f₁ p else f₂ p, hcont⟩,
    fun p => by
      change (if p.2.1 ≤ 1 / 2 then f₁ p else f₂ p) ∈ Z
      by_cases hp : p.2.1 ≤ 1 / 2 <;> simp only [hp, ↓reduceIte]
      · exact hZ₁ _
      · exact hZ₂ _,
    fun x => ?_, fun x => ?_, fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · change (if ((0 : unitInterval) : ℝ) ≤ 1 / 2 then f₁ (x, 0) else f₂ (x, 0)) = φ₀ x
    have hle : ((0 : unitInterval) : ℝ) ≤ 1 / 2 := by norm_num
    simp only [hle, ↓reduceIte, f₁]
    have hp0 : projIcc 0 1 zero_le_one (2 * ((0 : unitInterval) : ℝ)) = 0 := by
      ext; change max (0 : ℝ) (min 1 (2 * 0)) = 0; norm_num
    change ψ₁ (x, projIcc 0 1 zero_le_one (2 * ((0 : unitInterval) : ℝ))) = φ₀ x
    rw [hp0, h₁0 x]
  · change (if ((1 : unitInterval) : ℝ) ≤ 1 / 2 then f₁ (x, 1) else f₂ (x, 1)) = φ₂ x
    have hnot : ¬ (((1 : unitInterval) : ℝ) ≤ 1 / 2) := by norm_num
    simp only [hnot, ↓reduceIte, f₂]
    have hp1 : projIcc 0 1 zero_le_one (2 * ((1 : unitInterval) : ℝ) - 1) = 1 := by
      ext; change max (0 : ℝ) (min 1 (2 * 1 - 1)) = 1; norm_num
    change ψ₂ (x, projIcc 0 1 zero_le_one (2 * ((1 : unitInterval) : ℝ) - 1)) = φ₂ x
    rw [hp1, h₂1 x]
  · change (if y.1 ≤ 1 / 2 then f₁ (0, y) else f₂ (0, y)) = φ₀ 0
    by_cases hy : y.1 ≤ 1 / 2 <;> simp only [hy, ↓reduceIte]
    · exact h₁y0 _
    · exact (h₂y0 _).trans ((h₁y0' 0).symm.trans (h₁y0 0))
  · change (if y.1 ≤ 1 / 2 then f₁ (0, y) else f₂ (0, y)) = φ₂ 0
    by_cases hy : y.1 ≤ 1 / 2 <;> simp only [hy, ↓reduceIte]
    · exact (h₁y0' _).trans ((h₂y0 0).symm.trans (h₂y0' 0))
    · exact h₂y0' _
  · change (if y.1 ≤ 1 / 2 then f₁ (1, y) else f₂ (1, y)) = φ₀ 1
    by_cases hy : y.1 ≤ 1 / 2 <;> simp only [hy, ↓reduceIte]
    · exact h₁y1 _
    · exact (h₂y1 _).trans ((h₁y1' 0).symm.trans (h₁y1 0))
  · change (if y.1 ≤ 1 / 2 then f₁ (1, y) else f₂ (1, y)) = φ₂ 1
    by_cases hy : y.1 ≤ 1 / 2 <;> simp only [hy, ↓reduceIte]
    · exact (h₁y1' _).trans ((h₂y1 0).symm.trans (h₂y1' 0))
    · exact h₂y1' _

theorem CurvesHomotopic.refl (φ : Curve S) : CurvesHomotopic φ φ :=
  CurvesHomotopicIn.refl (subset_univ _)

theorem CurvesHomotopic.symm {φ₀ φ₁ : Curve S} (h : CurvesHomotopic φ₀ φ₁) :
    CurvesHomotopic φ₁ φ₀ :=
  CurvesHomotopicIn.symm h

theorem CurvesHomotopic.trans {φ₀ φ₁ φ₂ : Curve S}
    (h₁ : CurvesHomotopic φ₀ φ₁) (h₂ : CurvesHomotopic φ₁ φ₂) :
    CurvesHomotopic φ₀ φ₂ :=
  CurvesHomotopicIn.trans h₁ h₂

theorem CurvesHomotopic.map_homeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {φ₀ φ₁ : Curve S} (h : CurvesHomotopic φ₀ φ₁) :
    CurvesHomotopic (ContinuousMap.comp ⟨α, α.continuous⟩ φ₀)
      (ContinuousMap.comp ⟨α, α.continuous⟩ φ₁) := by
  rcases h with ⟨ψ, _, h0, h1, hy0, hy0', hy1, hy1'⟩
  refine ⟨ContinuousMap.comp ⟨α, α.continuous⟩ ψ, fun _ => mem_univ _,
    fun x => congrArg α (h0 x), fun x => congrArg α (h1 x),
    fun y => congrArg α (hy0 y), fun y => congrArg α (hy0' y),
    fun y => congrArg α (hy1 y), fun y => congrArg α (hy1' y)⟩

/-- Any curve `φ : Curve S` is homotopic to its 3-interval reparameterization
`x ↦ φ (projIcc 0 1 zero_le_one (3 * x.1 - 1))`. -/
theorem curvesHomotopic_reparam_three (φ : Curve S) :
    CurvesHomotopic φ
      ⟨fun x => φ (projIcc 0 1 zero_le_one (3 * x.1 - 1)),
        φ.continuous.comp (continuous_projIcc.comp (by fun_prop))⟩ := by
  let m : unitInterval → unitInterval := fun x => projIcc 0 1 zero_le_one (3 * x.1 - 1)
  have hm_cont : Continuous m := continuous_projIcc.comp (by fun_prop)
  have hm0 : m 0 = 0 := by ext; change max (0 : ℝ) (min 1 (3 * 0 - 1)) = 0; norm_num
  have hm1 : m 1 = 1 := by ext; change max (0 : ℝ) (min 1 (3 * 1 - 1)) = 1; norm_num
  let interp : unitInterval × unitInterval → unitInterval :=
    fun p => projIcc 0 1 zero_le_one ((1 - p.2.1) * p.1.1 + p.2.1 * (m p.1).1)
  have hinterp_cont : Continuous interp := continuous_projIcc.comp (by fun_prop)
  refine ⟨φ.comp ⟨interp, hinterp_cont⟩, fun _ => mem_univ _,
    fun x => ?_, fun x => ?_, fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · change φ (projIcc 0 1 zero_le_one ((1 - 0) * x.1 + 0 * (m x).1)) = φ x
    congr 1; ext; change max (0 : ℝ) (min 1 ((1 - 0) * x.1 + 0 * (m x).1)) = x.1
    simp [x.2.1, x.2.2]
  · change φ (projIcc 0 1 zero_le_one ((1 - 1) * x.1 + 1 * (m x).1)) = φ (m x)
    congr 1; ext; change max (0 : ℝ) (min 1 ((1 - 1) * x.1 + 1 * (m x).1)) = (m x).1
    simp [(m x).2.1, (m x).2.2]
  · change φ (projIcc 0 1 zero_le_one ((1 - y.1) * 0 + y.1 * (m 0).1)) = φ 0
    rw [hm0]; congr 1; ext; change max (0 : ℝ) (min 1 ((1 - y.1) * 0 + y.1 * 0)) = 0; norm_num
  · change φ (projIcc 0 1 zero_le_one ((1 - y.1) * 0 + y.1 * (m 0).1)) = φ (m 0)
    rw [hm0]; congr 1; ext; change max (0 : ℝ) (min 1 ((1 - y.1) * 0 + y.1 * 0)) = 0; norm_num
  · change φ (projIcc 0 1 zero_le_one ((1 - y.1) * 1 + y.1 * (m 1).1)) = φ 1
    rw [hm1]; congr 1; ext; change max (0 : ℝ) (min 1 ((1 - y.1) * 1 + y.1 * 1))
      = 1; ring_nf; norm_num
  · change φ (projIcc 0 1 zero_le_one ((1 - y.1) * 1 + y.1 * (m 1).1)) = φ (m 1)
    rw [hm1]; congr 1; ext; change max (0 : ℝ) (min 1 ((1 - y.1) * 1 + y.1 * 1))
      = 1; ring_nf; norm_num

/-- In a flat subset `Z ⊆ S` (`IsFlat Z`), any two curves `φ₁, φ₂ : Curve S` with `range φ₁ ⊆ Z`,
`range φ₂ ⊆ Z`, `φ₁ 0 = φ₂ 0`, and `φ₁ 1 = φ₂ 1` are homotopic in `S` (`CurvesHomotopic φ₁ φ₂`). -/
theorem IsFlat.curvesHomotopic {Z : Set S} (hZ : IsFlat Z) {φ₁ φ₂ : Curve S}
    (hφ₁ : range φ₁ ⊆ Z) (hφ₂ : range φ₂ ⊆ Z) (h0 : φ₁ 0 = φ₂ 0) (h1 : φ₁ 1 = φ₂ 1) :
    CurvesHomotopic φ₁ φ₂ := by
  have htwo : 0 < 2 := by decide
  let rev₂ : Curve S := φ₂.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩
  let γ : Fin 2 → Curve S := ![φ₁, rev₂]
  have hmatch : ∀ i : Fin 2, γ i 1 = γ (finNext htwo i) 0 := by
    intro i
    fin_cases i
    · change φ₁ 1 = φ₂ (unitInterval.symm 0)
      simpa using h1
    · change φ₂ (unitInterval.symm 1) = φ₁ 0
      simpa using h0.symm
  let L : C(Circle, S) := concatLoop htwo γ hmatch
  have hL_range : range L ⊆ Z := by
    dsimp [L]
    rw [range_concatLoop]
    refine iUnion_subset fun i => ?_
    fin_cases i
    · exact hφ₁
    · rintro _ ⟨x, rfl⟩
      exact hφ₂ (mem_range_self _)
  obtain ⟨c, _, H, _, hH0, hH1⟩ := hZ L hL_range
  have hH_arc₁ : ∀ t : unitInterval, H (Circle.exp (Real.pi * t.1), 0) = φ₁ t := by
    intro t
    have hp := concatLoop_exp_piece htwo γ hmatch 0 t
    have hexp : 2 * Real.pi * (((0 : Fin 2).1 : ℝ) + t.1) / (2 : ℕ) = Real.pi * t.1 := by
      simp only [Fin.val_zero, Nat.cast_zero, zero_add, Nat.cast_ofNat]
      ring
    rw [hexp] at hp
    exact (hH0 _).trans hp
  have hH_arc₂ : ∀ t : unitInterval, H (Circle.exp (Real.pi * (2 - t.1)), 0) = φ₂ t := by
    intro t
    have hp := concatLoop_exp_piece htwo γ hmatch 1 (unitInterval.symm t)
    have hexp : 2 * Real.pi * (((1 : Fin 2).1 : ℝ) + (unitInterval.symm t).1) / (2 : ℕ) =
        Real.pi * (2 - t.1) := by
      simp only [Fin.val_one, Nat.cast_one, coe_symm_eq, Nat.cast_ofNat]
      ring
    rw [hexp] at hp
    have hγ1 : γ 1 (unitInterval.symm t) = φ₂ t := by
      change φ₂ (unitInterval.symm (unitInterval.symm t)) = φ₂ t
      rw [unitInterval.symm_symm]
    rw [hγ1] at hp
    exact (hH0 _).trans hp
  let m : unitInterval → unitInterval := fun x => projIcc 0 1 zero_le_one (3 * x.1 - 1)
  have hm_cont : Continuous m := continuous_projIcc.comp (by fun_prop)
  have hm0 : m 0 = 0 := by ext; change max (0 : ℝ) (min 1 (3 * 0 - 1)) = 0; norm_num
  have hm1 : m 1 = 1 := by ext; change max (0 : ℝ) (min 1 (3 * 1 - 1)) = 1; norm_num
  let k : unitInterval → ℝ := fun x => min (3 * x.1) (min 1 (3 * (1 - x.1)))
  have hk_cont : Continuous k := by fun_prop
  have hk0 : k 0 = 0 := by change min (3 * (0 : ℝ)) (min 1 (3 * (1 - 0))) = 0; norm_num
  have hk1 : k 1 = 0 := by change min (3 * (1 : ℝ)) (min 1 (3 * (1 - 1))) = 0; norm_num
  let τ : unitInterval × unitInterval → unitInterval :=
    fun p => projIcc 0 1 zero_le_one (k p.1 * p.2.1)
  have hτ_cont : Continuous τ := continuous_projIcc.comp (by fun_prop)
  have hτ_y0 : ∀ x : unitInterval, τ (x, 0) = 0 := by
    intro x; ext; change max (0 : ℝ) (min 1 (k x * 0)) = 0; norm_num
  have hτ_0y : ∀ y : unitInterval, τ (0, y) = 0 := by
    intro y; ext; change max (0 : ℝ) (min 1 (k 0 * y.1)) = 0; rw [hk0]; norm_num
  have hτ_1y : ∀ y : unitInterval, τ (1, y) = 0 := by
    intro y; ext; change max (0 : ℝ) (min 1 (k 1 * y.1)) = 0; rw [hk1]; norm_num
  let φ₁' : Curve S := ⟨fun x => φ₁ (m x), φ₁.continuous.comp hm_cont⟩
  let φ₂' : Curve S := ⟨fun x => φ₂ (m x), φ₂.continuous.comp hm_cont⟩
  let midCurve : Curve S :=
    ⟨fun x => H (Circle.exp (Real.pi * (m x).1), τ (x, 1)),
      H.continuous.comp (Continuous.prodMk (by fun_prop) (hτ_cont.comp (by fun_prop)))⟩
  have hmid_eq : ∀ x : unitInterval,
      H (Circle.exp (Real.pi * (2 - (m x).1)), τ (x, 1)) = midCurve x := by
    intro x
    by_cases hx1 : x.1 ≤ 1 / 3
    · have hmx : (m x).1 = 0 := by
        change max (0 : ℝ) (min 1 (3 * x.1 - 1)) = 0
        have : min 1 (3 * x.1 - 1) ≤ 0 := le_trans (min_le_right _ _) (by linarith)
        exact max_eq_left this
      change H (Circle.exp (Real.pi * (2 - (m x).1)), τ (x, 1)) =
        H (Circle.exp (Real.pi * (m x).1), τ (x, 1))
      rw [hmx]
      have hexp : Circle.exp (Real.pi * (2 - 0)) = Circle.exp (Real.pi * 0) := by
        have h2pi : Real.pi * (2 - 0) = 2 * Real.pi := by ring
        rw [h2pi, mul_zero, Circle.exp_two_pi, Circle.exp_zero]
      rw [hexp]
    · by_cases hx2 : 2 / 3 ≤ x.1
      · have hmx : (m x).1 = 1 := by
          change max (0 : ℝ) (min 1 (3 * x.1 - 1)) = 1
          have hmin : min 1 (3 * x.1 - 1) = 1 := min_eq_left (by linarith)
          rw [hmin]
          exact max_eq_right zero_le_one
        change H (Circle.exp (Real.pi * (2 - (m x).1)), τ (x, 1)) =
          H (Circle.exp (Real.pi * (m x).1), τ (x, 1))
        rw [hmx]
        ring_nf
      · have hkx : k x = 1 := by
          change min (3 * x.1) (min 1 (3 * (1 - x.1))) = 1
          have hmin1 : min 1 (3 * (1 - x.1)) = 1 := min_eq_left (by linarith)
          rw [hmin1]
          exact min_eq_right (by linarith)
        have hτ1 : τ (x, 1) = 1 := by
          ext; change max (0 : ℝ) (min 1 (k x * 1)) = 1
          rw [hkx]; norm_num
        change H (Circle.exp (Real.pi * (2 - (m x).1)), τ (x, 1)) =
          H (Circle.exp (Real.pi * (m x).1), τ (x, 1))
        rw [hτ1, hH1, hH1]
        rfl
  have hmid0 : midCurve 0 = φ₁ 0 := by
    change H (Circle.exp (Real.pi * (m 0).1), τ (0, 1)) = φ₁ 0
    rw [hm0, hτ_0y 1]
    exact hH_arc₁ 0
  have hmid1 : midCurve 1 = φ₁ 1 := by
    change H (Circle.exp (Real.pi * (m 1).1), τ (1, 1)) = φ₁ 1
    rw [hm1, hτ_1y 1]
    exact hH_arc₁ 1
  have hhom₁' : CurvesHomotopic φ₁' midCurve := by
    refine ⟨⟨fun p => H (Circle.exp (Real.pi * (m p.1).1), τ p),
      H.continuous.comp (Continuous.prodMk (by fun_prop) hτ_cont)⟩,
      fun _ => mem_univ _, fun x => ?_, fun _ => rfl,
      fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_⟩
    · change H (Circle.exp (Real.pi * (m x).1), τ (x, 0)) = φ₁ (m x)
      rw [hτ_y0 x]
      exact hH_arc₁ (m x)
    · change H (Circle.exp (Real.pi * (m 0).1), τ (0, y)) = φ₁ (m 0)
      rw [hm0, hτ_0y y]
      exact hH_arc₁ 0
    · change H (Circle.exp (Real.pi * (m 0).1), τ (0, y)) = midCurve 0
      rw [hm0, hτ_0y y, hmid0]
      exact hH_arc₁ 0
    · change H (Circle.exp (Real.pi * (m 1).1), τ (1, y)) = φ₁ (m 1)
      rw [hm1, hτ_1y y]
      exact hH_arc₁ 1
    · change H (Circle.exp (Real.pi * (m 1).1), τ (1, y)) = midCurve 1
      rw [hm1, hτ_1y y, hmid1]
      exact hH_arc₁ 1
  have hhom₂' : CurvesHomotopic φ₂' midCurve := by
    refine ⟨⟨fun p => H (Circle.exp (Real.pi * (2 - (m p.1).1)), τ p),
      H.continuous.comp (Continuous.prodMk (by fun_prop) hτ_cont)⟩,
      fun _ => mem_univ _, fun x => ?_, fun x => hmid_eq x,
      fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_⟩
    · change H (Circle.exp (Real.pi * (2 - (m x).1)), τ (x, 0)) = φ₂ (m x)
      rw [hτ_y0 x]
      exact hH_arc₂ (m x)
    · change H (Circle.exp (Real.pi * (2 - (m 0).1)), τ (0, y)) = φ₂ (m 0)
      rw [hm0, hτ_0y y]
      exact hH_arc₂ 0
    · change H (Circle.exp (Real.pi * (2 - (m 0).1)), τ (0, y)) = midCurve 0
      rw [hm0, hτ_0y y, hmid0, h0]
      exact hH_arc₂ 0
    · change H (Circle.exp (Real.pi * (2 - (m 1).1)), τ (1, y)) = φ₂ (m 1)
      rw [hm1, hτ_1y y]
      exact hH_arc₂ 1
    · change H (Circle.exp (Real.pi * (2 - (m 1).1)), τ (1, y)) = midCurve 1
      rw [hm1, hτ_1y y, hmid1, h1]
      exact hH_arc₂ 1
  exact CurvesHomotopic.trans (curvesHomotopic_reparam_three φ₁)
    (CurvesHomotopic.trans hhom₁'
      (CurvesHomotopic.trans (CurvesHomotopic.symm hhom₂')
        (CurvesHomotopic.symm (curvesHomotopic_reparam_three φ₂))))

/-! ## 7. Equivalence of `ForestsHomotopic` and `ForestsHomoplastic`, and Theorems (3.4)–(3.5) -/

theorem pullback_isLink_homeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S') {Γ : Drawing S}
    {e' : Set S'} {u' v' : S'} (h : (mapDrawingHomeo α Γ).toGraph.IsLink e' u' v') :
    Γ.toGraph.IsLink (α.symm '' e') (α.symm u') (α.symm v') := by
  rcases h with ⟨he', hu', hv', hcap'⟩
  rw [mapDrawingHomeo_E] at he'
  rcases he' with ⟨e, he, rfl⟩
  rcases hu' with ⟨u, hu, rfl⟩
  rcases hv' with ⟨v, hv, rfl⟩
  have h_e : α.symm '' (α '' e) = e := α.symm_image_image e
  rw [h_e, α.symm_apply_apply, α.symm_apply_apply]
  refine ⟨he, hu, hv, ?_⟩
  have h1 : α.symm '' (closure (α '' e) ∩ α '' Γ.V) = α.symm '' {α u, α v} :=
    congrArg (image α.symm) hcap'
  have h2 : α.symm '' (closure (α '' e) ∩ α '' Γ.V) = closure e ∩ Γ.V := by
    rw [← α.image_closure, ← image_inter α.injective]
    exact α.symm_image_image _
  rw [h2, image_pair, α.symm_apply_apply, α.symm_apply_apply] at h1
  exact h1

/-- Pullback of a walk `W'` in `(mapDrawingHomeo α Γ).toGraph` to `Γ.toGraph`. -/
def pullbackWalkHomeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S') {Γ : Drawing S}
    {u' v' : S'} :
    GraphWalk (mapDrawingHomeo α Γ).toGraph u' v' →
      GraphWalk Γ.toGraph (α.symm u') (α.symm v')
  | .nil hv' => .nil (by
      rcases hv' with ⟨v, hv, rfl⟩
      change α.symm (α v) ∈ Γ.V
      rwa [α.symm_apply_apply])
  | .cons hlink rest => .cons (pullback_isLink_homeo α hlink) (pullbackWalkHomeo α rest)

theorem support_pullbackWalkHomeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {Γ : Drawing S} {u' v' : S'} (W' : GraphWalk (mapDrawingHomeo α Γ).toGraph u' v') :
    (pullbackWalkHomeo α W').support = W'.support.map α.symm := by
  induction W' with
  | nil _ => rfl
  | cons _ _ ih => simp [pullbackWalkHomeo, GraphWalk.support, ih]

theorem edges_pullbackWalkHomeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {Γ : Drawing S} {u' v' : S'} (W' : GraphWalk (mapDrawingHomeo α Γ).toGraph u' v') :
    (pullbackWalkHomeo α W').edges = W'.edges.map (image α.symm) := by
  induction W' with
  | nil _ => rfl
  | cons _ _ ih => simp [pullbackWalkHomeo, GraphWalk.edges, ih]

theorem length_pullbackWalkHomeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {Γ : Drawing S} {u' v' : S'} (W' : GraphWalk (mapDrawingHomeo α Γ).toGraph u' v') :
    (pullbackWalkHomeo α W').length = W'.length := by
  simp [GraphWalk.length, edges_pullbackWalkHomeo]

theorem isSimple_pullbackWalkHomeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {Γ : Drawing S} {u' v' : S'} {W' : GraphWalk (mapDrawingHomeo α Γ).toGraph u' v'}
    (hW' : W'.IsSimple) : (pullbackWalkHomeo α W').IsSimple := by
  unfold GraphWalk.IsSimple at hW' ⊢
  rw [support_pullbackWalkHomeo]
  exact hW'.map α.symm.injective

theorem isSimpleClosed_pullbackWalkHomeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {Γ : Drawing S} {u' : S'} {W' : GraphWalk (mapDrawingHomeo α Γ).toGraph u' u'}
    (hW' : W'.IsSimpleClosed) : (pullbackWalkHomeo α W').IsSimpleClosed := by
  rcases hW' with ⟨hs, he⟩
  refine ⟨?_, ?_⟩
  · rw [support_pullbackWalkHomeo, ← List.map_tail]
    exact hs.map α.symm.injective
  · rw [edges_pullbackWalkHomeo]
    exact he.map (image_injective.mpr α.symm.injective)

theorem _root_.GraphMinor.Surface.CurveTracesWalk.pullback_homeo {S' : Type v} [TopologicalSpace
  S'] (α : S ≃ₜ S')
    {Γ : Drawing S} {u' v' : S'} {φ' : Curve S'}
    {W' : GraphWalk (mapDrawingHomeo α Γ).toGraph u' v'}
    (h : CurveTracesWalk (mapDrawingHomeo α Γ) φ' W') :
    CurveTracesWalk Γ
      (ContinuousMap.comp ⟨α.symm, α.symm.continuous⟩ φ') (pullbackWalkHomeo α W') := by
  induction h with
  | @nil w' hv' φ' hconst =>
    have hv : α.symm w' ∈ Γ.V := by
      rcases hv' with ⟨v, hv, rfl⟩
      rwa [α.symm_apply_apply]
    refine .nil hv _ (fun x => ?_)
    change α.symm (φ' x) = α.symm w'
    rw [hconst x]
  | cons hlink φ₁ φ₂ φ hφ₁ hφ₂ hconcat ih =>
    rcases hconcat with ⟨t₀, ht0, ht1, h0, htv, h1, hle, hge⟩
    refine .cons (pullback_isLink_homeo α hlink)
      (ContinuousMap.comp ⟨α.symm, α.symm.continuous⟩ φ₁)
      (ContinuousMap.comp ⟨α.symm, α.symm.continuous⟩ φ₂)
      (ContinuousMap.comp ⟨α.symm, α.symm.continuous⟩ φ)
      ⟨by change α.symm (φ₁ 0) = _; rw [hφ₁.1],
       by change α.symm (φ₁ 1) = _; rw [hφ₁.2.1], ?_⟩
      ih
      ⟨t₀, ht0, ht1,
       by change α.symm (φ 0) = _; rw [h0],
       by change α.symm (φ t₀) = _; rw [htv],
       by change α.symm (φ 1) = _; rw [h1], ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      rw [← α.symm.image_closure]
      exact mem_image_of_mem α.symm (hφ₁.2.2 (mem_range_self x))
    · intro x hx
      rw [← α.symm.image_closure]
      exact mem_image_of_mem α.symm (hle x hx)
    · intro x hx
      obtain ⟨y, hy⟩ := hge x hx
      exact ⟨y, by change α.symm (φ₂ y) = α.symm (φ x); rw [hy]⟩

theorem IsProper.map_homeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S') {Γ : Drawing S}
    (h : Γ.IsProper) : (mapDrawingHomeo α Γ).IsProper := by
  rintro y ⟨hy_bd, x, hxU, rfl⟩
  have hx_bd : x ∈ bd S := by
    have : α x ∈ α '' bd S := by rwa [image_bd_homeomorph α]
    rcases this with ⟨z, hz, hzx⟩
    exact α.injective hzx ▸ hz
  exact mem_image_of_mem α (h ⟨hx_bd, hxU⟩)

theorem IsGraphForest.map_homeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S') {Γ : Drawing S}
    (h : IsGraphForest Γ.toGraph) : IsGraphForest (mapDrawingHomeo α Γ).toGraph := by
  intro u' W' hW'
  rw [← length_pullbackWalkHomeo α W']
  exact h (α.symm u') (pullbackWalkHomeo α W') (isSimpleClosed_pullbackWalkHomeo α hW')

theorem IsSurfaceForest.map_homeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S') {H : Drawing S}
    (h : IsSurfaceForest H) : IsSurfaceForest (mapDrawingHomeo α H) :=
  ⟨IsProper.map_homeo α h.1, IsGraphForest.map_homeo α h.2⟩

theorem ForestsHomotopic.refl {H : Drawing S} (hH : IsSurfaceForest H)
    (hpath : ∀ s ∈ H.V ∩ bd S, ∀ t ∈ H.V ∩ bd S, s ≠ t →
      ∀ (P₁ P₂ : GraphWalk H.toGraph s t) (φ₁ φ₂ : Curve S),
        P₁.IsSimple → P₂.IsSimple →
        CurveTracesWalk H φ₁ P₁ → CurveTracesWalk H φ₂ P₂ →
        CurvesHomotopic φ₁ φ₂) :
    ForestsHomotopic H H :=
  ⟨hH.1, hH.1, hH.2, hH.2, rfl, fun s hs t ht hne => ⟨Iff.rfl, hpath s hs t ht hne⟩⟩

theorem ForestsHomotopic.symm {H₁ H₂ : Drawing S}
    (h : ForestsHomotopic H₁ H₂) : ForestsHomotopic H₂ H₁ := by
  rcases h with ⟨hp1, hp2, hf1, hf2, hbd, hpaths⟩
  refine ⟨hp2, hp1, hf2, hf1, hbd.symm, fun s hs t ht hne => ?_⟩
  have hs1 : s ∈ H₁.V ∩ bd S := hbd.symm ▸ hs
  have ht1 : t ∈ H₁.V ∩ bd S := hbd.symm ▸ ht
  obtain ⟨hiff, hhom⟩ := hpaths s hs1 t ht1 hne
  refine ⟨hiff.symm, fun P₂ P₁ φ₂ φ₁ hP₂ hP₁ hφ₂ hφ₁ => ?_⟩
  exact CurvesHomotopic.symm (hhom P₁ P₂ φ₁ φ₂ hP₁ hP₂ hφ₁ hφ₂)

theorem ForestsHomotopic.trans {H₁ H₂ H₃ : Drawing S}
    (h₁₂ : ForestsHomotopic H₁ H₂) (h₂₃ : ForestsHomotopic H₂ H₃) :
    ForestsHomotopic H₁ H₃ := by
  rcases h₁₂ with ⟨hp1, _, hf1, _, hbd12, hpaths12⟩
  rcases h₂₃ with ⟨_, hp3, _, hf3, hbd23, hpaths23⟩
  refine ⟨hp1, hp3, hf1, hf3, hbd12.trans hbd23, fun s hs1 t ht1 hne => ?_⟩
  have hs2 : s ∈ H₂.V ∩ bd S := hbd12 ▸ hs1
  have ht2 : t ∈ H₂.V ∩ bd S := hbd12 ▸ ht1
  obtain ⟨hiff12, hhom12⟩ := hpaths12 s hs1 t ht1 hne
  obtain ⟨hiff23, hhom23⟩ := hpaths23 s hs2 t ht2 hne
  refine ⟨hiff12.trans hiff23, fun P₁ P₃ φ₁ φ₃ hP₁ hP₃ hφ₁ hφ₃ => ?_⟩
  obtain ⟨P₂, hP₂⟩ := hiff12.mp ⟨P₁, hP₁⟩
  obtain ⟨φ₂, hφ₂⟩ := exists_curveTracesWalk P₂
  exact CurvesHomotopic.trans
    (hhom12 P₁ P₂ φ₁ φ₂ hP₁ hP₂ hφ₁ hφ₂)
    (hhom23 P₂ P₃ φ₂ φ₃ hP₂ hP₃ hφ₂ hφ₃)

theorem pullback_simple_walk_aux {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {Γ : Drawing S} {s t : S} {s' t' : S'} (hs : α.symm s' = s) (ht : α.symm t' = t)
    (P' : GraphWalk (mapDrawingHomeo α Γ).toGraph s' t') (hP' : P'.IsSimple) :
    ∃ P : GraphWalk Γ.toGraph s t, P.IsSimple := by
  subst hs ht
  exact ⟨pullbackWalkHomeo α P', isSimple_pullbackWalkHomeo α hP'⟩

theorem pullback_walk_and_trace_aux {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {Γ : Drawing S} {s t : S} {s' t' : S'} (hs : α.symm s' = s) (ht : α.symm t' = t)
    (P' : GraphWalk (mapDrawingHomeo α Γ).toGraph s' t') (hP' : P'.IsSimple)
    (φ' : Curve S') (hφ' : CurveTracesWalk (mapDrawingHomeo α Γ) φ' P') :
    ∃ P : GraphWalk Γ.toGraph s t, P.IsSimple ∧
      CurveTracesWalk Γ (ContinuousMap.comp ⟨α.symm, α.symm.continuous⟩ φ') P := by
  subst hs ht
  exact ⟨pullbackWalkHomeo α P', isSimple_pullbackWalkHomeo α hP',
    CurveTracesWalk.pullback_homeo α hφ'⟩

theorem ForestsHomotopic.map_homeo {S' : Type v} [TopologicalSpace S'] (α : S ≃ₜ S')
    {H₁ H₂ : Drawing S} (h : ForestsHomotopic H₁ H₂) :
    ForestsHomotopic (mapDrawingHomeo α H₁) (mapDrawingHomeo α H₂) := by
  rcases h with ⟨hp1, hp2, hf1, hf2, hbd, hpaths⟩
  have hbd_img : ∀ H : Drawing S, (mapDrawingHomeo α H).V ∩ bd S' = α '' (H.V ∩ bd S) := by
    intro H
    change α '' H.V ∩ bd S' = α '' (H.V ∩ bd S)
    rw [← image_bd_homeomorph α, ← image_inter α.injective]
  refine ⟨IsProper.map_homeo α hp1, IsProper.map_homeo α hp2,
    IsGraphForest.map_homeo α hf1, IsGraphForest.map_homeo α hf2,
    by rw [hbd_img, hbd_img, hbd], fun s' hs' t' ht' hne' => ?_⟩
  rw [hbd_img] at hs' ht'
  rcases hs' with ⟨s, hs, rfl⟩
  rcases ht' with ⟨t, ht, rfl⟩
  have hne : s ≠ t := fun h_eq => hne' (congrArg α h_eq)
  obtain ⟨hiff, hhom⟩ := hpaths s hs t ht hne
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨P₁', hP₁'⟩
      obtain ⟨P₁, hP₁⟩ := pullback_simple_walk_aux α (α.symm_apply_apply s)
        (α.symm_apply_apply t) P₁' hP₁'
      obtain ⟨P₂, hP₂⟩ := hiff.mp ⟨P₁, hP₁⟩
      exact ⟨mapWalkHomeo α P₂, isSimple_mapWalkHomeo α hP₂⟩
    · rintro ⟨P₂', hP₂'⟩
      obtain ⟨P₂, hP₂⟩ := pullback_simple_walk_aux α (α.symm_apply_apply s)
        (α.symm_apply_apply t) P₂' hP₂'
      obtain ⟨P₁, hP₁⟩ := hiff.mpr ⟨P₂, hP₂⟩
      exact ⟨mapWalkHomeo α P₁, isSimple_mapWalkHomeo α hP₁⟩
  · intro P₁' P₂' φ₁' φ₂' hP₁' hP₂' hφ₁' hφ₂'
    obtain ⟨P₁, hP₁, htr₁⟩ :=
      pullback_walk_and_trace_aux α (α.symm_apply_apply s) (α.symm_apply_apply t) P₁' hP₁' φ₁' hφ₁'
    obtain ⟨P₂, hP₂, htr₂⟩ :=
      pullback_walk_and_trace_aux α (α.symm_apply_apply s) (α.symm_apply_apply t) P₂' hP₂' φ₂' hφ₂'
    have hhom_pull := hhom P₁ P₂ _ _ hP₁ hP₂ htr₁ htr₂
    have hhom_push := CurvesHomotopic.map_homeo α hhom_pull
    have h_comp₁ : ContinuousMap.comp ⟨α, α.continuous⟩
        (ContinuousMap.comp ⟨α.symm, α.symm.continuous⟩ φ₁') = φ₁' := by
      ext x; simp
    have h_comp₂ : ContinuousMap.comp ⟨α, α.continuous⟩
        (ContinuousMap.comp ⟨α.symm, α.symm.continuous⟩ φ₂') = φ₂' := by
      ext x; simp
    rwa [h_comp₁, h_comp₂] at hhom_push

theorem mapDrawingHomeo_trans {S' : Type v} {S'' : Type w} [TopologicalSpace S'] [TopologicalSpace
  S'']
    (α : S ≃ₜ S') (β : S' ≃ₜ S'') (Γ : Drawing S) :
    mapDrawingHomeo β (mapDrawingHomeo α Γ) = mapDrawingHomeo (α.trans β) Γ := by
  cases Γ
  simp only [mapDrawingHomeo, Drawing.mk.injEq]
  constructor <;> ext z <;> simp [Homeomorph.trans_apply]

theorem mapDrawingHomeo_refl (Γ : Drawing S) :
    mapDrawingHomeo (Homeomorph.refl S) Γ = Γ := by
  cases Γ
  simp [mapDrawingHomeo]

theorem ForestsHomoplastic.symm {H₁ H₂ : Drawing S}
    (h : ForestsHomoplastic H₁ H₂) : ForestsHomoplastic H₂ H₁ := by
  rcases h with ⟨α, hα_bd, hhom⟩
  refine ⟨α.symm, fun x hx => (α.symm_apply_eq).mpr (hα_bd x hx).symm, ?_⟩
  have hhom' := ForestsHomotopic.map_homeo α.symm (ForestsHomotopic.symm hhom)
  rwa [mapDrawingHomeo_symm_mapDrawingHomeo] at hhom'

theorem ForestsHomoplastic.trans {H₁ H₂ H₃ : Drawing S}
    (h₁₂ : ForestsHomoplastic H₁ H₂) (h₂₃ : ForestsHomoplastic H₂ H₃) :
    ForestsHomoplastic H₁ H₃ := by
  rcases h₁₂ with ⟨α, hα_bd, hhom₁₂⟩
  rcases h₂₃ with ⟨β, hβ_bd, hhom₂₃⟩
  refine ⟨α.trans β, fun x hx => by simp [Homeomorph.trans_apply, hα_bd x hx, hβ_bd x hx], ?_⟩
  rw [← mapDrawingHomeo_trans]
  exact ForestsHomotopic.trans (ForestsHomotopic.map_homeo β hhom₁₂) hhom₂₃

/-! ## 8. Proof of Theorem (3.4) and Theorem (3.5) -/

/-- For any vertex `s ∈ H.V`, `H.span {s} ∅` is a connected subdrawing of `H` with `V = {s}` and
`U = {s}`. -/
theorem span_singleton_empty [T1Space S] {H : Drawing S} {s : S} (hs : s ∈ H.V) :
    (H.span {s} ∅).V = {s} ∧ (H.span {s} ∅).U = {s} ∧
      (H.span {s} ∅).IsSubdrawing H ∧ (H.span {s} ∅).IsConnected := by
  have hV : (H.span {s} ∅).V = {s} := by
    change ({s} ∩ H.V) ∪ ⋃ e ∈ (∅ : Set (Set S)) ∩ H.E, closure e ∩ H.V = {s}
    simp [inter_eq_self_of_subset_left (singleton_subset_iff.mpr hs)]
  have hU : (H.span {s} ∅).U = {s} := by
    change H.spanV {s} ∅ ∪ ⋃ e ∈ (∅ : Set (Set S)) ∩ H.E, closure e = {s}
    rw [show H.spanV {s} ∅ = (H.span {s} ∅).V from rfl, hV]
    simp
  have hE : (H.span {s} ∅).E = ∅ := by
    rw [H.span_E, empty_inter]
  refine ⟨hV, hU, ⟨by rw [hV]; exact singleton_subset_iff.mpr hs, by rw [hE]; exact empty_subset _⟩,
    ⟨⟨s, by rw [hV]; exact mem_singleton s⟩, ?_⟩⟩
  intro u hu v hv
  have hu' : u = s := by rw [hV] at hu; exact mem_singleton_iff.mp hu
  have hv' : v = s := by rw [hV] at hv; exact mem_singleton_iff.mp hv
  rw [hu', hv']
  have hs' : s ∈ (H.span {s} ∅).toGraph.vertexSet := by
    change s ∈ (H.span {s} ∅).V
    rw [hV]
    exact mem_singleton s
  exact ⟨.nil hs'⟩

/-- Graph Minors VII, (3.4), Claim (2) (page 220):
"(2) *If $G$ is an $X$-matching surrounding $Y$-forests $H, H'$ then $H$ and $H'$ are homotopic.*"
-/
theorem theorem_3_4_claim_2 (hS : IsSurface S) {Y : Set S} {G H₁ H₂ : Drawing S}
    (hH₁ : IsYForest Y H₁) (hH₂ : IsYForest Y H₂)
    (hG₁ : MatchingStrictlySurroundsForest G H₁)
    (hG₂ : MatchingStrictlySurroundsForest G H₂) :
    ForestsHomotopic H₁ H₂ := by
  have : T2Space S := hS.2.1
  rcases hH₁ with ⟨⟨hp₁, hf₁⟩, hY₁⟩
  rcases hH₂ with ⟨⟨hp₂, hf₂⟩, hY₂⟩
  rcases hG₁ with ⟨⟨hdisj₁, hsurr₁⟩, hstrict₁⟩
  rcases hG₂ with ⟨⟨hdisj₂, hsurr₂⟩, hstrict₂⟩
  refine ⟨hp₁, hp₂, hf₁, hf₂, hY₁.trans hY₂.symm, fun s hs t ht hne => ?_⟩
  have hs₂ : s ∈ H₂.V ∩ bd S := hY₂.symm ▸ hY₁ ▸ hs
  have ht₂ : t ∈ H₂.V ∩ bd S := hY₂.symm ▸ hY₁ ▸ ht
  obtain ⟨hVs, hUs, hsub_s, hconn_s⟩ := span_singleton_empty hs.1
  have hne_s : ((H₁.span {s} ∅).V ∩ bd S).Nonempty := ⟨s, by rw [hVs]; exact ⟨rfl, hs.2⟩⟩
  obtain ⟨r, hr_mem, hr_sc, hUs_r⟩ := hsurr₁ (H₁.span {s} ∅) hsub_s hconn_s hne_s
  have hs_r : s ∈ r := hUs_r (by rw [hUs]; exact mem_singleton s)
  have hr_eq : r = connectedComponentIn (univ \ G.U) s := by
    rcases hr_mem with ⟨z, _, rfl⟩
    exact connectedComponentIn_eq hs_r
  have h_curve_in_r : ∀ {H : Drawing S} {P : GraphWalk H.toGraph s t} {φ : Curve S},
      G.U ∩ H.U = ∅ → CurveTracesWalk H φ P → range φ ⊆ r ∧ t ∈ r := by
    intro H P φ hdisj hφ
    have hφ_ends := hφ.endpoints
    have hφ_U : range φ ⊆ univ \ G.U := by
      intro x hx
      refine ⟨mem_univ x, fun hxG => ?_⟩
      exact eq_empty_iff_forall_notMem.mp hdisj x ⟨hxG, hφ.range_subset_U hx⟩
    have hφ_sub_r : range φ ⊆ r := by
      rw [hr_eq]
      exact (isPreconnected_range φ.continuous).subset_connectedComponentIn
        ⟨0, hφ_ends.1⟩ hφ_U
    exact ⟨hφ_sub_r, hφ_sub_r ⟨1, hφ_ends.2⟩⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨P₁, hP₁⟩
    obtain ⟨φ₁, hφ₁⟩ := exists_curveTracesWalk P₁
    have ht_r : t ∈ r := (h_curve_in_r hdisj₁ hφ₁).2
    exact hstrict₂ s hs₂ t ht₂ hne r hr_mem hs_r ht_r
  · rintro ⟨P₂, hP₂⟩
    obtain ⟨φ₂, hφ₂⟩ := exists_curveTracesWalk P₂
    have ht_r : t ∈ r := (h_curve_in_r hdisj₂ hφ₂).2
    exact hstrict₁ s hs t ht hne r hr_mem hs_r ht_r
  · intro P₁ P₂ φ₁ φ₂ _ _ hφ₁ hφ₂
    have hφ₁_r : range φ₁ ⊆ r := (h_curve_in_r hdisj₁ hφ₁).1
    have hφ₂_r : range φ₂ ⊆ r := (h_curve_in_r hdisj₂ hφ₂).1
    have hr_flat : IsFlat r := IsSimplyConnectedSubset.isFlat hS hr_sc
    exact IsFlat.curvesHomotopic hr_flat hφ₁_r hφ₂_r
      (hφ₁.endpoints.1.trans hφ₂.endpoints.1.symm)
      (hφ₁.endpoints.2.trans hφ₂.endpoints.2.symm)

/-- Transport of `MatchingStrictlySurroundsForest` along a homeomorphism `α : S ≃ₜ S'`. -/
theorem MatchingStrictlySurroundsForest.map_homeo {S' : Type v} [TopologicalSpace S'] [T2Space S]
    (α : S ≃ₜ S') {G : Drawing S} {G' : Drawing S'} {H : Drawing S}
    (hU : α '' G.U = G'.U) (hsurr : MatchingStrictlySurroundsForest G H) :
    MatchingStrictlySurroundsForest G' (mapDrawingHomeo α H) := by
  have : T2Space S' := α.symm.isEmbedding.t2Space
  rcases hsurr with ⟨⟨hdisj, hcomp⟩, hstrict⟩
  have hR_eq : ∀ r' ∈ G'.R, ∃ r ∈ G.R, r' = α '' r := by
    rintro r' ⟨y', hy', rfl⟩
    let y := α.symm y'
    have hy : y ∈ univ \ G.U := by
      refine ⟨mem_univ y, fun hyG => hy'.2 ?_⟩
      rw [← hU]
      exact ⟨y, hyG, α.apply_symm_apply y'⟩
    refine ⟨connectedComponentIn (univ \ G.U) y, ⟨y, hy, rfl⟩, ?_⟩
    apply Subset.antisymm
    · have hpre : IsPreconnected (α.symm '' connectedComponentIn (univ \ G'.U) y') :=
        isPreconnected_connectedComponentIn.image α.symm α.symm.continuous.continuousOn
      have hsub : α.symm '' connectedComponentIn (univ \ G'.U) y' ⊆ univ \ G.U := by
        rintro _ ⟨z', hz', rfl⟩
        have hz'_compl : z' ∈ univ \ G'.U := connectedComponentIn_subset _ _ hz'
        refine ⟨mem_univ _, fun hzG => hz'_compl.2 ?_⟩
        rw [← hU]
        exact ⟨α.symm z', hzG, α.apply_symm_apply z'⟩
      have hmem : y ∈ α.symm '' connectedComponentIn (univ \ G'.U) y' :=
        mem_image_of_mem α.symm (mem_connectedComponentIn hy')
      have h_in := hpre.subset_connectedComponentIn hmem hsub
      intro z' hz'
      exact ⟨α.symm z', h_in (mem_image_of_mem α.symm hz'), α.apply_symm_apply z'⟩
    · have hpre : IsPreconnected (α '' connectedComponentIn (univ \ G.U) y) :=
        isPreconnected_connectedComponentIn.image α α.continuous.continuousOn
      have hsub : α '' connectedComponentIn (univ \ G.U) y ⊆ univ \ G'.U := by
        rintro _ ⟨z, hz, rfl⟩
        have hz_compl : z ∈ univ \ G.U := connectedComponentIn_subset _ _ hz
        refine ⟨mem_univ _, fun hzG' => hz_compl.2 ?_⟩
        rw [← hU] at hzG'
        rcases hzG' with ⟨w, hw, hwz⟩
        exact α.injective hwz ▸ hw
      have hmem : y' ∈ α '' connectedComponentIn (univ \ G.U) y :=
        ⟨y, mem_connectedComponentIn hy, α.apply_symm_apply y'⟩
      exact hpre.subset_connectedComponentIn hmem hsub
  have hR_img : ∀ r ∈ G.R, α '' r ∈ G'.R := by
    rintro r ⟨z, hz, rfl⟩
    have hαz : α z ∈ univ \ G'.U := by
      refine ⟨mem_univ _, fun h_in => hz.2 ?_⟩
      rw [← hU] at h_in
      rcases h_in with ⟨w, hw, hwz⟩
      exact α.injective hwz ▸ hw
    refine ⟨α z, hαz, ?_⟩
    apply Subset.antisymm
    · have hpre : IsPreconnected (α.symm '' connectedComponentIn (univ \ G'.U) (α z)) :=
        isPreconnected_connectedComponentIn.image α.symm α.symm.continuous.continuousOn
      have hsub : α.symm '' connectedComponentIn (univ \ G'.U) (α z) ⊆ univ \ G.U := by
        rintro _ ⟨w', hw', rfl⟩
        have hw'_c := connectedComponentIn_subset _ _ hw'
        refine ⟨mem_univ _, fun hw => hw'_c.2 ?_⟩
        rw [← hU]
        exact ⟨α.symm w', hw, α.apply_symm_apply w'⟩
      have hz_in : z ∈ α.symm '' connectedComponentIn (univ \ G'.U) (α z) :=
        ⟨α z, mem_connectedComponentIn hαz, α.symm_apply_apply z⟩
      intro y' hy'
      exact ⟨α.symm y', hpre.subset_connectedComponentIn hz_in hsub (mem_image_of_mem α.symm hy'),
        α.apply_symm_apply y'⟩
    · have hpre : IsPreconnected (α '' connectedComponentIn (univ \ G.U) z) :=
        isPreconnected_connectedComponentIn.image α α.continuous.continuousOn
      have hsub : α '' connectedComponentIn (univ \ G.U) z ⊆ univ \ G'.U := by
        rintro _ ⟨w, hw, rfl⟩
        have hw_c := connectedComponentIn_subset _ _ hw
        refine ⟨mem_univ _, fun hαw => hw_c.2 ?_⟩
        rw [← hU] at hαw
        rcases hαw with ⟨q, hq, hqw⟩
        exact α.injective hqw ▸ hq
      exact hpre.subset_connectedComponentIn
        (mem_image_of_mem α (mem_connectedComponentIn hz)) hsub
  have hsc_map : ∀ {r : Set S}, IsSimplyConnectedSubset r → IsSimplyConnectedSubset (α '' r) := by
    rintro r ⟨harc, hoarc⟩
    refine ⟨?_, ?_⟩
    · rintro a' ⟨a, ha, rfl⟩ b' ⟨b, hb, rfl⟩ hne'
      obtain ⟨L, hLr, hL⟩ := harc a ha b hb (fun h => hne' (congrArg α h))
      refine ⟨α '' L, image_mono hLr, ?_⟩
      obtain ⟨γ, hγ, rfl, rfl, rfl⟩ := hL.exists_arc
      have h1 : IsArcMap (α ∘ γ) := ⟨α.continuous.comp hγ.1, α.injective.comp hγ.2⟩
      simpa [range_comp] using h1.isLineWithEnds
    · intro F' ⟨f'⟩ hF'r
      have hF_sub : α.symm '' F' ⊆ r := by
        rintro _ ⟨y', hy', rfl⟩
        rcases hF'r hy' with ⟨x, hx, rfl⟩
        simpa using hx
      have hF_oarc : IsOArc (α.symm '' F') := ⟨f'.trans (α.symm.image F')⟩
      obtain ⟨Δ, ⟨eΔ⟩, hbdΔ, hΔr⟩ := hoarc (α.symm '' F') hF_oarc hF_sub
      refine ⟨α '' Δ, ⟨eΔ.trans (α.image Δ)⟩, ?_, image_mono hΔr⟩
      calc
        discBd (α '' Δ) = α '' discBd Δ := by
          unfold discBd
          have hbd_eq := image_bd_homeomorph (α.image Δ)
          ext z
          simp only [mem_image, Subtype.exists]
          constructor
          · rintro ⟨w, hw, hw_bd, rfl⟩
            have : ⟨w, hw⟩ ∈ (α.image Δ) '' bd Δ := hbd_eq ▸ hw_bd
            rcases this with ⟨⟨x, hx⟩, hx_bd, hxw⟩
            refine ⟨x, ⟨x, hx, hx_bd, rfl⟩, ?_⟩
            exact congrArg Subtype.val hxw
          · rintro ⟨_, ⟨x, hx, hx_bd, rfl⟩, rfl⟩
            refine ⟨α x, mem_image_of_mem α hx, ?_, rfl⟩
            rw [← hbd_eq]
            exact ⟨⟨x, hx⟩, hx_bd, rfl⟩
        _ = α '' (α.symm '' F') := by rw [hbdΔ]
        _ = F' := α.image_symm_image F'
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← hU]
    change α '' G.U ∩ α '' H.U = ∅
    rw [← image_inter α.injective, hdisj, image_empty]
  · intro H' hsub' hconn' ⟨s', hs'V, hs'bd⟩
    let H₀ := mapDrawingHomeo α.symm H'
    have hH₀_sub : H₀.IsSubdrawing H := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨y', hy'V, rfl⟩
        rcases hsub'.1 hy'V with ⟨x, hx, rfl⟩
        simpa using hx
      · rw [mapDrawingHomeo_E]
        rintro _ ⟨e', he'E, rfl⟩
        have he' := hsub'.2 he'E
        rw [mapDrawingHomeo_E] at he'
        rcases he' with ⟨e, he, rfl⟩
        have : α.symm '' (α '' e) = e := α.symm_image_image e
        rwa [this]
    have hH₀_conn : H₀.IsConnected := by
      refine ⟨hconn'.1.image α.symm, ?_⟩
      rintro _ ⟨u', hu', rfl⟩ _ ⟨v', hv', rfl⟩
      obtain ⟨W'⟩ := hconn'.2 u' hu' v' hv'
      exact ⟨mapWalkHomeo α.symm W'⟩
    have hH₀_bd : (H₀.V ∩ bd S).Nonempty := by
      refine ⟨α.symm s', mem_image_of_mem α.symm hs'V, ?_⟩
      have : α.symm s' ∈ α.symm '' bd S' := mem_image_of_mem α.symm hs'bd
      rwa [image_bd_homeomorph α.symm] at this
    obtain ⟨r, hr_mem, hr_sc, hH₀_r⟩ := hcomp H₀ hH₀_sub hH₀_conn hH₀_bd
    refine ⟨α '' r, hR_img r hr_mem, hsc_map hr_sc, ?_⟩
    calc
      H'.U = α '' (α.symm '' H'.U) := (α.image_symm_image H'.U).symm
      _ = α '' H₀.U := rfl
      _ ⊆ α '' r := image_mono hH₀_r
  · intro s' hs' t' ht' hne' r' hr' hs'r' ht'r'
    obtain ⟨r, hr, rfl⟩ := hR_eq r' hr'
    rcases hs' with ⟨⟨s, hsV, rfl⟩, hs'_bd⟩
    rcases ht' with ⟨⟨t, htV, rfl⟩, ht'_bd⟩
    have hs_bd : s ∈ bd S := by
      have : α s ∈ α '' bd S := by rwa [image_bd_homeomorph α]
      rcases this with ⟨z, hz, hzs⟩
      exact α.injective hzs ▸ hz
    have ht_bd : t ∈ bd S := by
      have : α t ∈ α '' bd S := by rwa [image_bd_homeomorph α]
      rcases this with ⟨z, hz, hzt⟩
      exact α.injective hzt ▸ hz
    rcases hs'r' with ⟨s₁, hs₁r, hs₁_eq⟩
    rcases ht'r' with ⟨t₁, ht₁r, ht₁_eq⟩
    have hs_r : s ∈ r := α.injective hs₁_eq ▸ hs₁r
    have ht_r : t ∈ r := α.injective ht₁_eq ▸ ht₁r
    obtain ⟨P, hP⟩ := hstrict s ⟨hsV, hs_bd⟩ t ⟨htV, ht_bd⟩
      (fun h => hne' (congrArg α h)) r hr hs_r ht_r
    exact ⟨mapWalkHomeo α P, isSimple_mapWalkHomeo α hP⟩

/-- Graph Minors VII, (3.4), Claim (3) (page 220):
"(3) *If $H, H'$ are $Y$-forests surrounded by $X$-matchings $G, G'$, respectively, and $G$ and $G'$
are congruent, then $H$ and $H'$ are homoplastic.*" -/
theorem theorem_3_4_claim_3 (hS : IsSurface S) {Y : Set S} (hY : Y ⊆ bd S)
    {G G' H H' : Drawing S} (hH : IsYForest Y H) (hH' : IsYForest Y H')
    (hsurr : MatchingStrictlySurroundsForest G H)
    (hsurr' : MatchingStrictlySurroundsForest G' H')
    (hcongr : AreCongruentMatchings G G') :
    ForestsHomoplastic H H' := by
  have : T2Space S := hS.2.1
  rcases hcongr with ⟨α, hU, hα_bd⟩
  have hαH_Y : IsYForest Y (mapDrawingHomeo α H) := by
    refine ⟨IsSurfaceForest.map_homeo α hH.1, ?_⟩
    calc
      (mapDrawingHomeo α H).V ∩ bd S = α '' H.V ∩ α '' bd S := by
        rw [image_bd_homeomorph α]; rfl
      _ = α '' (H.V ∩ bd S) := (image_inter α.injective).symm
      _ = α '' Y := by rw [hH.2]
      _ = Y := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [hα_bd x (hY hx)]
          exact hx
        · intro hy
          exact ⟨y, hy, hα_bd y (hY hy)⟩
  have hsurr_α : MatchingStrictlySurroundsForest G' (mapDrawingHomeo α H) :=
    MatchingStrictlySurroundsForest.map_homeo α hU hsurr
  exact ⟨α, hα_bd, theorem_3_4_claim_2 hS hαH_Y hH' hsurr_α hsurr'⟩

/-! ## 9. Canonical Boundary Subsets and Proof of Theorem (3.6) -/

/-- Finite hierarchy of canonical parameters in `Ico (0 : ℝ) 1` closed under taking midpoints with
`insert 1 (canonParams m)`. -/
noncomputable def canonParams : ℕ → Set ℝ
  | 0 => ∅
  | m + 1 =>
      insert 0 (canonParams m ∪
        (fun p : ℝ × ℝ => (p.1 + p.2) / 2) '' (canonParams m ×ˢ insert 1 (canonParams m)))

theorem canonParams_finite (m : ℕ) : (canonParams m).Finite := by
  induction m with
  | zero => exact finite_empty
  | succ m ih =>
    exact (ih.union ((ih.prod (ih.insert 1)).image _)).insert 0

theorem canonParams_subset_Ico (m : ℕ) : canonParams m ⊆ Ico (0 : ℝ) 1 := by
  induction m with
  | zero => exact empty_subset _
  | succ m ih =>
    rintro x (rfl | hx | ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩)
    · exact ⟨le_rfl, zero_lt_one⟩
    · exact ih hx
    · have ha' := ih ha
      have hb' : b ∈ Icc (0 : ℝ) 1 := by
        rcases hb with rfl | hb
        · exact ⟨zero_le_one, le_rfl⟩
        · exact Ico_subset_Icc_self (ih hb)
      exact ⟨by linarith [ha'.1, hb'.1], by linarith [ha'.2, hb'.2]⟩

theorem canonParams_mono {m n : ℕ} (h : m ≤ n) : canonParams m ⊆ canonParams n := by
  induction h with
  | refl => exact Subset.rfl
  | @step k _ ih =>
    exact ih.trans (subset_union_left.trans (subset_insert 0 _))

/-- Piecewise linear homeomorphism of `ℝ` fixing `(-∞, a] ∪ [b, ∞)` and mapping `u₀ ∈ (a, b)` to
`(a + b) / 2`. -/
noncomputable def bumpMid (a u₀ b u : ℝ) : ℝ :=
  if u ≤ a then u
  else if u ≤ u₀ then a + (b - a) / 2 * ((u - a) / (u₀ - a))
  else if u ≤ b then (a + b) / 2 + (b - a) / 2 * ((u - u₀) / (b - u₀))
  else u

theorem continuous_bumpMid {a u₀ b : ℝ} (ha : a < u₀) (hb : u₀ < b) :
    Continuous (bumpMid a u₀ b) := by
  have hau : u₀ - a ≠ 0 := by linarith
  have hbu : b - u₀ ≠ 0 := by linarith
  unfold bumpMid
  refine Continuous.if_le continuous_id ?_ continuous_id continuous_const (fun x hx => ?_)
  · refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const (fun x hx => ?_)
    · refine Continuous.if_le (by fun_prop) continuous_id continuous_id continuous_const
        (fun x hx => ?_)
      rw [hx, div_self hbu]
      ring
    · simp only [hx, hb.le, ↓reduceIte, div_self hau, sub_self, zero_div]
      ring
  · simp only [hx, ha.le, ↓reduceIte, sub_self, zero_div]
    ring

theorem strictMono_bumpMid {a u₀ b : ℝ} (ha : a < u₀) (hb : u₀ < b) :
    StrictMono (bumpMid a u₀ b) := by
  have hau : 0 < u₀ - a := by linarith
  have hbu : 0 < b - u₀ := by linarith
  have hba : 0 < (b - a) / 2 := by linarith
  have h_val_a : bumpMid a u₀ b a = a := by simp [bumpMid]
  have h_val_u₀ : bumpMid a u₀ b u₀ = (a + b) / 2 := by
    unfold bumpMid
    have h1 : ¬ (u₀ ≤ a) := by linarith
    simp [h1, div_self hau.ne']
    ring
  have h_val_b : bumpMid a u₀ b b = b := by
    unfold bumpMid
    have h1 : ¬ (b ≤ a) := by linarith
    have h2 : ¬ (b ≤ u₀) := by linarith
    simp [h1, h2, div_self hbu.ne']
    ring
  have h_piece1 : ∀ {x y : ℝ}, x < y → y ≤ a → bumpMid a u₀ b x < bumpMid a u₀ b y := by
    intro x y hxy hy
    have hx : x ≤ a := hxy.le.trans hy
    simp [bumpMid, hx, hy, hxy]
  have h_piece2 : ∀ {x y : ℝ}, a ≤ x → x < y → y ≤ u₀ → bumpMid a u₀ b x < bumpMid a u₀ b y := by
    intro x y hx hxy hy
    rcases eq_or_lt_of_le hx with rfl | hx'
    · rw [h_val_a]
      have hy_not_a : ¬ (y ≤ a) := by linarith
      unfold bumpMid
      simp only [hy_not_a, hy, ↓reduceIte]
      have hpos : 0 < (b - a) / 2 * ((y - a) / (u₀ - a)) :=
        mul_pos hba (div_pos (by linarith) hau)
      linarith
    · have hx_not_a : ¬ (x ≤ a) := by linarith
      have hy_not_a : ¬ (y ≤ a) := by linarith
      have hx_u₀ : x ≤ u₀ := hxy.le.trans hy
      unfold bumpMid
      simp only [hx_not_a, hy_not_a, hx_u₀, hy, ↓reduceIte]
      have hdiv : (x - a) / (u₀ - a) < (y - a) / (u₀ - a) :=
        div_lt_div_of_pos_right (by linarith) hau
      have hmul : (b - a) / 2 * ((x - a) / (u₀ - a)) < (b - a) / 2 * ((y - a) / (u₀ - a)) :=
        mul_lt_mul_of_pos_left hdiv hba
      linarith
  have h_piece3 : ∀ {x y : ℝ}, u₀ ≤ x → x < y → y ≤ b → bumpMid a u₀ b x < bumpMid a u₀ b y := by
    intro x y hx hxy hy
    rcases eq_or_lt_of_le hx with rfl | hx'
    · rw [h_val_u₀]
      have hy_not_a : ¬ (y ≤ a) := by linarith
      have hy_not_u₀ : ¬ (y ≤ u₀) := by linarith
      unfold bumpMid
      simp only [hy_not_a, hy_not_u₀, hy, ↓reduceIte]
      have hpos : 0 < (b - a) / 2 * ((y - u₀) / (b - u₀)) :=
        mul_pos hba (div_pos (by linarith) hbu)
      linarith
    · have hx_not_a : ¬ (x ≤ a) := by linarith
      have hy_not_a : ¬ (y ≤ a) := by linarith
      have hx_not_u₀ : ¬ (x ≤ u₀) := by linarith
      have hy_not_u₀ : ¬ (y ≤ u₀) := by linarith
      have hx_b : x ≤ b := hxy.le.trans hy
      unfold bumpMid
      simp only [hx_not_a, hy_not_a, hx_not_u₀, hy_not_u₀, hx_b, hy, ↓reduceIte]
      have hdiv : (x - u₀) / (b - u₀) < (y - u₀) / (b - u₀) :=
        div_lt_div_of_pos_right (by linarith) hbu
      have hmul : (b - a) / 2 * ((x - u₀) / (b - u₀)) < (b - a) / 2 * ((y - u₀) / (b - u₀)) :=
        mul_lt_mul_of_pos_left hdiv hba
      linarith
  have h_piece4 : ∀ {x y : ℝ}, b ≤ x → x < y → bumpMid a u₀ b x < bumpMid a u₀ b y := by
    intro x y hx hxy
    rcases eq_or_lt_of_le hx with rfl | hx'
    · rw [h_val_b]
      have hy_not_a : ¬ (y ≤ a) := by linarith
      have hy_not_u₀ : ¬ (y ≤ u₀) := by linarith
      have hy_not_b : ¬ (y ≤ b) := by linarith
      unfold bumpMid
      simp [hy_not_a, hy_not_u₀, hy_not_b, hxy]
    · have hx_not_a : ¬ (x ≤ a) := by linarith
      have hy_not_a : ¬ (y ≤ a) := by linarith
      have hx_not_u₀ : ¬ (x ≤ u₀) := by linarith
      have hy_not_u₀ : ¬ (y ≤ u₀) := by linarith
      have hx_not_b : ¬ (x ≤ b) := by linarith
      have hy_not_b : ¬ (y ≤ b) := by linarith
      unfold bumpMid
      simp [hx_not_a, hy_not_a, hx_not_u₀, hy_not_u₀, hx_not_b, hy_not_b, hxy]
  intro x y hxy
  by_cases hy_a : y ≤ a
  · exact h_piece1 hxy hy_a
  · by_cases hy_u₀ : y ≤ u₀
    · by_cases hx_a : x < a
      · exact (h_piece1 hx_a le_rfl).trans (h_piece2 le_rfl (by linarith) hy_u₀)
      · exact h_piece2 (not_lt.mp hx_a) hxy hy_u₀
    · by_cases hy_b : y ≤ b
      · by_cases hx_u₀ : x < u₀
        · have h1 : bumpMid a u₀ b x < bumpMid a u₀ b u₀ := by
            by_cases hx_a : x < a
            · exact (h_piece1 hx_a le_rfl).trans (h_piece2 le_rfl ha le_rfl)
            · exact h_piece2 (not_lt.mp hx_a) hx_u₀ le_rfl
          exact h1.trans (h_piece3 le_rfl (by linarith) hy_b)
        · exact h_piece3 (not_lt.mp hx_u₀) hxy hy_b
      · by_cases hx_b : x < b
        · have h1 : bumpMid a u₀ b x < bumpMid a u₀ b b := by
            by_cases hx_u₀ : x < u₀
            · have h0 : bumpMid a u₀ b x < bumpMid a u₀ b u₀ := by
                by_cases hx_a : x < a
                · exact (h_piece1 hx_a le_rfl).trans (h_piece2 le_rfl ha le_rfl)
                · exact h_piece2 (not_lt.mp hx_a) hx_u₀ le_rfl
              exact h0.trans (h_piece3 le_rfl hb le_rfl)
            · exact h_piece3 (not_lt.mp hx_u₀) hx_b le_rfl
          exact h1.trans (h_piece4 le_rfl (by linarith))
        · exact h_piece4 (not_lt.mp hx_b) hxy

theorem bumpMid_apply_u₀ {a u₀ b : ℝ} (ha : a < u₀) :
    bumpMid a u₀ b u₀ = (a + b) / 2 := by
  have hau : u₀ - a ≠ 0 := by linarith
  have h1 : ¬ (u₀ ≤ a) := by linarith
  unfold bumpMid
  simp [h1, div_self hau]
  ring

theorem bumpMid_fix {a u₀ b z : ℝ} (ha : a < u₀) (hb : u₀ < b) (hz : z ≤ a ∨ b ≤ z) :
    bumpMid a u₀ b z = z := by
  rcases hz with hza | hbz
  · simp [bumpMid, hza]
  · rcases eq_or_lt_of_le hbz with rfl | hbz'
    · have h1 : ¬ (b ≤ a) := by linarith
      have h2 : ¬ (b ≤ u₀) := by linarith
      have hbu : b - u₀ ≠ 0 := by linarith
      unfold bumpMid
      simp [h1, h2, div_self hbu]
      ring
    · have h1 : ¬ (z ≤ a) := by linarith
      have h2 : ¬ (z ≤ u₀) := by linarith
      have h3 : ¬ (z ≤ b) := by linarith
      simp [bumpMid, h1, h2, h3]

theorem exists_Ico_param_of_mem_cuff {C : Set S} (φ : Circle ≃ₜ C) {x : S} (hx : x ∈ C) :
    ∃ u ∈ Ico (0 : ℝ) 1, (φ (ee u)).1 = x := by
  obtain ⟨r, hr⟩ := ee_surjective (φ.symm ⟨x, hx⟩)
  refine ⟨Int.fract r, ⟨Int.fract_nonneg r, Int.fract_lt_one r⟩, ?_⟩
  have h1 : ee (Int.fract r) = ee r := by
    have h2 := (Int.fract_add_floor r).symm
    have h3 := ee_add_int (Int.fract r) ⌊r⌋
    rw [← h2] at h3
    exact h3.symm
  rw [h1, hr]
  simp

theorem move_one_point_on_cuff (hS : IsSurface S) {C U : Set S} (hC : IsCuff C) (hU : IsOpen U)
    (hCU : C ⊆ U) (φ : Circle ≃ₜ C) (m : ℕ) {F : Set ℝ}
    (hF : F ⊆ canonParams m) (hF0 : 0 < m → 0 ∈ F) {x₀ : S} (hx₀ : x₀ ∈ C) :
    ∃ (α : S ≃ₜ S) (F' : Set ℝ),
      F ⊆ F' ∧ F' ⊆ canonParams (m + 1) ∧ 0 ∈ F' ∧
      α x₀ ∈ (fun u => (φ (ee u)).1) '' F' ∧
      (∀ y ∈ (fun u => (φ (ee u)).1) '' F, α y = y) ∧
      (∀ x ∈ C, α x ∈ C) ∧
      (∀ x ∉ U, α x = x) := by
  let ψ : ℝ → S := fun u => (φ (ee u)).1
  have hC_map : ∀ {τ : ℝ → ℝ} {α : S ≃ₜ S},
      (∀ u ∈ Icc (0 : ℝ) 1, α (ψ u) = ψ (τ u)) → ∀ x ∈ C, α x ∈ C := by
    intro τ α hα x hx
    obtain ⟨u, hu, rfl⟩ := exists_Ico_param_of_mem_cuff φ hx
    rw [hα u (Ico_subset_Icc_self hu)]
    exact (φ _).2
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hF_empty : F = ∅ := subset_empty_iff.mp hF
    obtain ⟨u₀, hu₀, hψu₀⟩ := exists_Ico_param_of_mem_cuff φ hx₀
    let τ : ℝ → ℝ := fun u => u - u₀
    have hc : ContinuousOn τ (Icc 0 1) := by fun_prop
    have hm_tau : StrictMonoOn τ (Icc 0 1) := fun a _ b _ hab => sub_lt_sub_right hab u₀
    have h1 : τ 1 = τ 0 + 1 := by dsimp [τ]; ring
    obtain ⟨α, hα_cuff, hα_out⟩ := exists_move_loop hS hC hU hCU φ hc hm_tau h1
    refine ⟨α, {0}, by simp [hF_empty], ?_, mem_singleton 0, ?_, ?_, hC_map hα_cuff, hα_out⟩
    · intro z hz
      rw [mem_singleton_iff.mp hz]
      exact mem_insert 0 _
    · refine ⟨0, mem_singleton 0, ?_⟩
      have hαx₀ := hα_cuff u₀ (Ico_subset_Icc_self hu₀)
      rw [hψu₀] at hαx₀
      dsimp [τ] at hαx₀
      rw [sub_self] at hαx₀
      exact hαx₀.symm
    · simp [hF_empty]
  · have h0F : (0 : ℝ) ∈ F := hF0 hm
    by_cases hx₀_in : x₀ ∈ ψ '' F
    · refine ⟨Homeomorph.refl S, F, Subset.rfl, hF.trans (canonParams_mono (Nat.le_succ m)),
        h0F, hx₀_in, fun y _ => rfl, fun x hx => hx, fun x _ => rfl⟩
    · obtain ⟨u₀, hu₀, hψu₀⟩ := exists_Ico_param_of_mem_cuff φ hx₀
      have hu₀_not_F : u₀ ∉ F := fun huF => hx₀_in ⟨u₀, huF, hψu₀⟩
      have hu₀_pos : 0 < u₀ := lt_of_le_of_ne hu₀.1 (fun h => hu₀_not_F (h ▸ h0F))
      have hu₀_lt_one : u₀ < 1 := hu₀.2
      have hF_fin : F.Finite := (canonParams_finite m).subset hF
      let F_left := {z ∈ F | z < u₀}
      have hFl_fin : F_left.Finite := hF_fin.subset (fun z hz => hz.1)
      have hFl_ne : F_left.Nonempty := ⟨0, h0F, hu₀_pos⟩
      let a := hFl_fin.toFinset.max' (hFl_fin.toFinset_nonempty.mpr hFl_ne)
      have ha_mem : a ∈ F_left := hFl_fin.mem_toFinset.mp (Finset.max'_mem _ _)
      have ha_F : a ∈ F := ha_mem.1
      have ha_lt : a < u₀ := ha_mem.2
      have ha_ge : ∀ z ∈ F, z < u₀ → z ≤ a := fun z hz hzu =>
        Finset.le_max' _ _ (hFl_fin.mem_toFinset.mpr ⟨hz, hzu⟩)
      let F_right := insert (1 : ℝ) {z ∈ F | u₀ < z}
      have hFr : {z ∈ F | u₀ < z}.Finite := hF_fin.subset fun _ hz => hz.1
      have hFr_fin : F_right.Finite := hFr.insert 1
      have hFr_ne : F_right.Nonempty := ⟨1, mem_insert 1 _⟩
      let b := hFr_fin.toFinset.min' (hFr_fin.toFinset_nonempty.mpr hFr_ne)
      have hb_mem : b ∈ F_right := hFr_fin.mem_toFinset.mp (Finset.min'_mem _ _)
      have hb_gt : u₀ < b := by
        rcases hb_mem with hb1 | hb'
        · exact hb1.symm ▸ hu₀_lt_one
        · exact hb'.2
      have hb_le_one : b ≤ 1 :=
        Finset.min'_le _ _ (hFr_fin.mem_toFinset.mpr (mem_insert 1 _))
      have hb_le : ∀ z ∈ F, u₀ < z → b ≤ z := fun z hz huz =>
        Finset.min'_le _ _ (hFr_fin.mem_toFinset.mpr (Or.inr ⟨hz, huz⟩))
      have ha_nonneg : 0 ≤ a := (canonParams_subset_Ico m (hF ha_F)).1
      let τ := bumpMid a u₀ b
      have hc : ContinuousOn τ (Icc 0 1) := (continuous_bumpMid ha_lt hb_gt).continuousOn
      have hm_tau : StrictMonoOn τ (Icc 0 1) := (strictMono_bumpMid ha_lt hb_gt).strictMonoOn _
      have hτ0 : τ 0 = 0 := bumpMid_fix ha_lt hb_gt (Or.inl ha_nonneg)
      have hτ1 : τ 1 = 1 := bumpMid_fix ha_lt hb_gt (Or.inr hb_le_one)
      have h1 : τ 1 = τ 0 + 1 := by rw [hτ0, hτ1, zero_add]
      obtain ⟨α, hα_cuff, hα_out⟩ := exists_move_loop hS hC hU hCU φ hc hm_tau h1
      let mid := (a + b) / 2
      have hmid_mem : mid ∈ canonParams (m + 1) := by
        refine Or.inr (Or.inr ⟨(a, b), ⟨hF ha_F, ?_⟩, rfl⟩)
        rcases hb_mem with hb1 | hb'
        · exact Or.inl hb1
        · exact Or.inr (hF hb'.1)
      refine ⟨α, insert mid F, subset_insert mid F, ?_, Or.inr h0F, ?_, ?_, hC_map hα_cuff, hα_out⟩
      · rintro z (rfl | hz)
        · exact hmid_mem
        · exact canonParams_mono (Nat.le_succ m) (hF hz)
      · refine ⟨mid, mem_insert mid F, ?_⟩
        have hαx₀ := hα_cuff u₀ (Ico_subset_Icc_self hu₀)
        rw [hψu₀] at hαx₀
        dsimp [τ] at hαx₀
        rw [bumpMid_apply_u₀ ha_lt] at hαx₀
        exact hαx₀.symm
      · rintro _ ⟨z, hzF, rfl⟩
        have hz_Ico := canonParams_subset_Ico m (hF hzF)
        have hαz := hα_cuff z (Ico_subset_Icc_self hz_Ico)
        change α (ψ z) = ψ (τ z) at hαz
        have hz_ne : z ≠ u₀ := fun h => hu₀_not_F (h ▸ hzF)
        have hz_fix : τ z = z := by
          rcases lt_or_gt_of_ne hz_ne with hlt | hgt
          · exact bumpMid_fix ha_lt hb_gt (Or.inl (ha_ge z hzF hlt))
          · exact bumpMid_fix ha_lt hb_gt (Or.inr (hb_le z hzF hgt))
        rw [hαz, hz_fix]

theorem move_finite_set_on_cuff (hS : IsSurface S) {C U : Set S} (hC : IsCuff C) (hU : IsOpen U)
    (hCU : C ⊆ U) (φ : Circle ≃ₜ C) :
    ∀ (k : ℕ) {Z : Set S}, Z ⊆ C → Z.Finite → Z.ncard ≤ k →
      ∃ (α : S ≃ₜ S) (F : Set ℝ),
        F ⊆ canonParams k ∧ (0 < k → 0 ∈ F) ∧
        α '' Z ⊆ (fun u => (φ (ee u)).1) '' F ∧
        (∀ x ∈ C, α x ∈ C) ∧
        (∀ x ∉ U, α x = x) := by
  intro k
  induction k with
  | zero =>
    intro Z _ hZfin hZcard
    have hZ_empty : Z = ∅ := (ncard_eq_zero hZfin).mp (Nat.le_zero.mp hZcard)
    refine ⟨Homeomorph.refl S, ∅, Subset.rfl, fun h => (lt_irrefl 0 h).elim, ?_,
      fun x hx => hx, fun x _ => rfl⟩
    simp [hZ_empty]
  | succ k ih =>
    intro Z hZC hZfin hZcard
    rcases Z.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · refine ⟨Homeomorph.refl S, {0}, ?_, fun _ => mem_singleton 0, by simp,
        fun x hx => hx, fun x _ => rfl⟩
      intro z hz
      rw [mem_singleton_iff.mp hz]
      exact mem_insert 0 _
    · let Z' := Z \ {x₀}
      have hZ'C : Z' ⊆ C := sdiff_subset.trans hZC
      have hZ'fin : Z'.Finite := hZfin.sdiff
      have hZ'card : Z'.ncard ≤ k := by
        have h1 : (insert x₀ Z').ncard ≤ k + 1 := by
          rwa [insert_sdiff_singleton, insert_eq_of_mem hx₀]
        have hx₀_not_Z' : x₀ ∉ Z' := fun h => h.2 rfl
        rw [ncard_insert_of_notMem hx₀_not_Z' hZ'fin] at h1
        exact Nat.le_of_succ_le_succ h1
      obtain ⟨α₁, F₁, hF₁_sub, hF₁_0, hα₁_Z', hα₁_C, hα₁_out⟩ := ih hZ'C hZ'fin hZ'card
      have hα₁x₀ : α₁ x₀ ∈ C := hα₁_C x₀ (hZC hx₀)
      obtain ⟨α₂, F', hF₁_F', hF'_sub, hF'_0, hα₂_x₀, hα₂_fix, hα₂_C, hα₂_out⟩ :=
        move_one_point_on_cuff hS hC hU hCU φ k hF₁_sub hF₁_0 hα₁x₀
      refine ⟨α₁.trans α₂, F', hF'_sub, fun _ => hF'_0, ?_,
        fun x hx => hα₂_C (α₁ x) (hα₁_C x hx),
        fun x hx => by simp [Homeomorph.trans_apply, hα₁_out x hx, hα₂_out x hx]⟩
      rintro _ ⟨z, hz, rfl⟩
      simp only [Homeomorph.trans_apply]
      by_cases hzx₀ : z = x₀
      · subst hzx₀
        exact hα₂_x₀
      · have hz' : z ∈ Z' := ⟨hz, hzx₀⟩
        have hα₁z : α₁ z ∈ (fun u => (φ (ee u)).1) '' F₁ := hα₁_Z' (mem_image_of_mem α₁ hz')
        rw [hα₂_fix (α₁ z) hα₁z]
        exact image_mono hF₁_F' hα₁z

theorem isClosed_of_mem_cuffs (hS : IsSurface S) {C : Set S} (hC : C ∈ cuffs S) :
    IsClosed C := by
  have : T2Space S := hS.2.1
  have ⟨φ⟩ := (cuff_statement.{u} S hS).2.2 C hC
  have h_eq : C = range (Subtype.val ∘ φ) := by
    ext x
    constructor
    · intro hx
      exact ⟨φ.symm ⟨x, hx⟩, by simp⟩
    · rintro ⟨z, rfl⟩
      exact (φ z).2
  rw [h_eq]
  exact (isCompact_range (continuous_subtype_val.comp φ.continuous)).isClosed

theorem disjoint_of_mem_cuffs {C₁ C₂ : Set S} (hC₁ : C₁ ∈ cuffs S) (hC₂ : C₂ ∈ cuffs S)
    (hne : C₁ ≠ C₂) : Disjoint C₁ C₂ := by
  rw [disjoint_iff_inter_eq_empty]
  by_contra h
  obtain ⟨z, hz₁, hz₂⟩ := nonempty_iff_ne_empty.mpr h
  rcases hC₁ with ⟨x₁, _, rfl⟩
  rcases hC₂ with ⟨x₂, _, rfl⟩
  have e₁ := connectedComponentIn_eq hz₁
  have e₂ := connectedComponentIn_eq hz₂
  exact hne (e₁.trans e₂.symm)

/-- For any surface `S` and bound `M : ℕ`, there exists a finite canonical subset
`Z_canon ⊆ bd S` such that any subset `Z ⊆ bd S` of cardinality at most `M` can be mapped into
`Z_canon` by a self-homeomorphism of `S`. -/
theorem exists_canon_bd_homeo (hS : IsSurface S) (M : ℕ) :
    ∃ Z_canon : Set S, Z_canon ⊆ bd S ∧ Z_canon.Finite ∧
      ∀ Z : Set S, Z ⊆ bd S → Z.Finite → Z.ncard ≤ M →
        ∃ β : S ≃ₜ S, β '' Z ⊆ Z_canon := by
  classical
  have hcuffs := cuff_statement.{u} S hS
  have hcuffs_fin := hcuffs.2.1
  have hcuffs_oarc := hcuffs.2.2
  let cuffCanon (C : Set S) : Set S :=
    if hC : C ∈ cuffs S then
      (fun u => ((hcuffs_oarc C hC).some (ee u)).1) '' canonParams M
    else ∅
  have hcuffCanon_sub : ∀ C ∈ cuffs S, cuffCanon C ⊆ C := by
    intro C hC
    dsimp [cuffCanon]
    rw [dite_eq_left_of_eq_true (eq_true hC)]
    rintro _ ⟨u, _, rfl⟩
    exact ((hcuffs_oarc C hC).some (ee u)).2
  have hcuffCanon_fin : ∀ C, (cuffCanon C).Finite := by
    intro C
    dsimp [cuffCanon]
    split_ifs with hC
    · exact (canonParams_finite M).image _
    · exact finite_empty
  have hC_sub_bd : ∀ C ∈ cuffs S, C ⊆ bd S := by
    rintro C ⟨x, _, rfl⟩
    exact connectedComponentIn_subset (bd S) x
  let Z_canon := ⋃ C ∈ cuffs S, cuffCanon C
  refine ⟨Z_canon, iUnion₂_subset (fun C hC => (hcuffCanon_sub C hC).trans (hC_sub_bd C hC)),
    hcuffs_fin.biUnion (fun C _ => hcuffCanon_fin C), ?_⟩
  intro Z hZ_bd hZ_fin hZ_card
  have h_ind : ∀ (𝒜 : Finset (Set S)), (∀ C ∈ 𝒜, C ∈ cuffs S) →
      ∃ α : S ≃ₜ S,
        α '' (Z ∩ ⋃ C ∈ 𝒜, C) ⊆ ⋃ C ∈ 𝒜, cuffCanon C ∧
        ∀ x ∈ bd S \ (⋃ C ∈ 𝒜, C), α x = x := by
    intro 𝒜
    induction 𝒜 using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨Homeomorph.refl S, by simp, fun x _ => rfl⟩
    | @insert C₀ 𝒜 hC₀_not_mem ih =>
      intro h𝒜_cuffs
      have hC₀ : C₀ ∈ cuffs S := h𝒜_cuffs C₀ (Finset.mem_insert_self C₀ 𝒜)
      have h𝒜 : ∀ C ∈ 𝒜, C ∈ cuffs S :=
        fun C hC => h𝒜_cuffs C (Finset.mem_insert_of_mem hC)
      obtain ⟨α₁, hα₁_img, hα₁_fix⟩ := ih h𝒜
      have hC₀_disj_𝒜 : Disjoint C₀ (⋃ C ∈ 𝒜, C) := by
        rw [disjoint_iUnion₂_right]
        intro C hC
        exact disjoint_of_mem_cuffs hC₀ (h𝒜 C hC) (fun h => hC₀_not_mem (h ▸ hC))
      have hα₁_fix_C₀ : ∀ x ∈ C₀, α₁ x = x := by
        intro x hx
        exact hα₁_fix x ⟨hC_sub_bd C₀ hC₀ hx,
          disjoint_left.mp hC₀_disj_𝒜 hx⟩
      let U := (bd S \ C₀)ᶜ
      have hU_open : IsOpen U := (isClosed_bd_diff_cuff hS hC₀).isOpen_compl
      have hC₀_U : C₀ ⊆ U := fun x hx h => h.2 hx
      let φ₀ : Circle ≃ₜ C₀ := (hcuffs_oarc C₀ hC₀).some
      have hZC₀_sub : Z ∩ C₀ ⊆ C₀ := inter_subset_right
      have hZC₀_fin : (Z ∩ C₀).Finite := hZ_fin.subset inter_subset_left
      have hZC₀_card : (Z ∩ C₀).ncard ≤ M :=
        (ncard_le_ncard inter_subset_left hZ_fin).trans hZ_card
      obtain ⟨α₂, F₀, hF₀_sub, _, hα₂_Z, _, hα₂_out⟩ :=
        move_finite_set_on_cuff hS hC₀ hU_open hC₀_U φ₀ M hZC₀_sub hZC₀_fin hZC₀_card
      have hα₂_fix_other : ∀ x ∈ bd S \ C₀, α₂ x = x :=
        fun x hx => hα₂_out x (not_not.mpr hx)
      have hα₂_C₀ : α₂ '' (Z ∩ C₀) ⊆ cuffCanon C₀ := by
        dsimp [cuffCanon]
        rw [dite_eq_left_of_eq_true (eq_true hC₀)]
        exact hα₂_Z.trans (image_mono hF₀_sub)
      refine ⟨α₁.trans α₂, ?_, ?_⟩
      · rintro _ ⟨z, ⟨hzZ, hz_union⟩, rfl⟩
        simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, mem_union] at hz_union ⊢
        simp only [Homeomorph.trans_apply]
        rcases hz_union with hz_C₀ | hz_𝒜
        · rw [hα₁_fix_C₀ z hz_C₀]
          exact Or.inl (hα₂_C₀ (mem_image_of_mem α₂ ⟨hzZ, hz_C₀⟩))
        · have hα₁z : α₁ z ∈ ⋃ C ∈ 𝒜, cuffCanon C :=
            hα₁_img (mem_image_of_mem α₁ ⟨hzZ, hz_𝒜⟩)
          have hα₁z_other : α₁ z ∈ bd S \ C₀ := by
            have h_in_𝒜 : α₁ z ∈ ⋃ C ∈ 𝒜, C :=
              iUnion₂_mono (fun C hC => hcuffCanon_sub C (h𝒜 C hC)) hα₁z
            refine ⟨iUnion₂_subset (fun C hC => hC_sub_bd C (h𝒜 C hC)) h_in_𝒜, ?_⟩
            exact disjoint_right.mp hC₀_disj_𝒜 h_in_𝒜
          rw [hα₂_fix_other (α₁ z) hα₁z_other]
          exact Or.inr hα₁z
      · intro x hx
        simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, mem_sdiff, mem_union, not_or] at hx
        have hx₁ : α₁ x = x := hα₁_fix x ⟨hx.1, hx.2.2⟩
        have hx₂ : α₂ x = x := hα₂_fix_other x ⟨hx.1, hx.2.1⟩
        simp [Homeomorph.trans_apply, hx₁, hx₂]
  obtain ⟨β, hβ_img, _⟩ := h_ind hcuffs_fin.toFinset (fun C hC => hcuffs_fin.mem_toFinset.mp hC)
  refine ⟨β, ?_⟩
  have hZ_eq : Z ∩ (⋃ C ∈ hcuffs_fin.toFinset, C) = Z := by
    rw [inter_eq_left]
    intro x hx
    have hx_bd : x ∈ bd S := hZ_bd hx
    refine mem_iUnion₂.mpr ⟨connectedComponentIn (bd S) x, ?_, mem_connectedComponentIn hx_bd⟩
    exact hcuffs_fin.mem_toFinset.mpr ⟨x, hx_bd, rfl⟩
  rw [hZ_eq] at hβ_img
  refine hβ_img.trans (iUnion₂_mono' fun C hC => ⟨C, hcuffs_fin.mem_toFinset.mp hC, Subset.rfl⟩)

theorem vertexValency_mapDrawingHomeo {S' : Type v} [TopologicalSpace S']
    (β : S ≃ₜ S') (G : Drawing S) (v : S) :
    vertexValency (mapDrawingHomeo β G) (β v) = vertexValency G v := by
  unfold vertexValency
  have h_tilde : ∀ e : Set S, tilde (β '' e) = β '' tilde e := by
    intro e
    unfold tilde
    rw [← β.image_closure, ← image_sdiff β.injective]
  have h_inc : ∀ e ∈ G.E,
      (mapDrawingHomeo β G).VertexIncident (β v) (β '' e) ↔ G.VertexIncident v e := by
    intro e he
    unfold Drawing.VertexIncident
    have he' : β '' e ∈ (mapDrawingHomeo β G).E := by
      rw [mapDrawingHomeo_E]
      exact mem_image_of_mem (image β) he
    have hV_iff : β v ∈ (mapDrawingHomeo β G).V ↔ v ∈ G.V :=
      β.injective.mem_set_image
    have hcl_iff : β v ∈ closure (β '' e) ↔ v ∈ closure e := by
      rw [← β.image_closure]
      exact β.injective.mem_set_image
    exact ⟨fun ⟨hV, _, hcl⟩ => ⟨hV_iff.mp hV, Or.inl he, hcl_iff.mp hcl⟩,
      fun ⟨hV, _, hcl⟩ => ⟨hV_iff.mpr hV, Or.inl he', hcl_iff.mpr hcl⟩⟩
  have h_set : ∀ k : ℕ,
      {e' ∈ (mapDrawingHomeo β G).E |
        (mapDrawingHomeo β G).VertexIncident (β v) e' ∧ (tilde e').ncard = k} =
      (image β) '' {e ∈ G.E | G.VertexIncident v e ∧ (tilde e).ncard = k} := by
    intro k
    ext e'
    simp only [mem_sep_iff, mem_image]
    constructor
    · rintro ⟨he'E, hinc', hcard'⟩
      rw [mapDrawingHomeo_E] at he'E
      rcases he'E with ⟨e, heE, rfl⟩
      rw [h_inc e heE] at hinc'
      rw [h_tilde, ncard_image_of_injective _ β.injective] at hcard'
      exact ⟨e, ⟨heE, hinc', hcard'⟩, rfl⟩
    · rintro ⟨e, ⟨heE, hinc, hcard⟩, rfl⟩
      rw [mapDrawingHomeo_E, h_inc e heE, h_tilde, ncard_image_of_injective _ β.injective]
      exact ⟨mem_image_of_mem (image β) heE, hinc, hcard⟩
  rw [h_set 2, h_set 1,
    ncard_image_of_injective _ (image_injective.mpr β.injective),
    ncard_image_of_injective _ (image_injective.mpr β.injective)]

theorem IsMatching.map_homeo {S' : Type v} [TopologicalSpace S'] (β : S ≃ₜ S')
    {G : Drawing S} (hG : IsMatching G) : IsMatching (mapDrawingHomeo β G) := by
  rcases hG with ⟨hprop, hV_bd, hval⟩
  refine ⟨IsProper.map_homeo β hprop, ?_, ?_⟩
  · rw [← image_bd_homeomorph β]
    exact image_mono hV_bd
  · rintro _ ⟨v, hv, rfl⟩
    rw [vertexValency_mapDrawingHomeo]
    exact hval v hv

theorem IsXMatching.map_homeo {S' : Type v} [TopologicalSpace S'] (β : S ≃ₜ S')
    {X : Set S} {G : Drawing S} (hG : IsXMatching X G) :
    IsXMatching (β '' X) (mapDrawingHomeo β G) :=
  ⟨hG.1.map_homeo β, congrArg (image β) hG.2⟩

theorem IsYForest.map_homeo {S' : Type v} [TopologicalSpace S'] (β : S ≃ₜ S')
    {Y : Set S} {H : Drawing S} (hH : IsYForest Y H) :
    IsYForest (β '' Y) (mapDrawingHomeo β H) := by
  refine ⟨IsSurfaceForest.map_homeo β hH.1, ?_⟩
  calc
    (mapDrawingHomeo β H).V ∩ bd S' = β '' H.V ∩ β '' bd S := by
      rw [image_bd_homeomorph β]; rfl
    _ = β '' (H.V ∩ bd S) := (image_inter β.injective).symm
    _ = β '' Y := by rw [hH.2]

theorem ForestsHomoplastic.map_right {H₀ H₁ : Drawing S}
    (h : ForestsHomoplastic H₀ H₁) (α : S ≃ₜ S) (hα : ∀ x ∈ bd S, α x = x) :
    ForestsHomoplastic H₀ (mapDrawingHomeo α H₁) := by
  rcases h with ⟨β, hβ_bd, hhom⟩
  refine ⟨β.trans α, fun x hx => by simp [Homeomorph.trans_apply, hβ_bd x hx, hα x hx], ?_⟩
  rw [← mapDrawingHomeo_trans]
  exact ForestsHomotopic.map_homeo α hhom

theorem ForestsHomoplastic.conj_homeo {S' : Type v} [TopologicalSpace S'] (β : S ≃ₜ S')
    {H : Drawing S} {H' : Drawing S'}
    (h : ForestsHomoplastic (mapDrawingHomeo β H) H') :
    ForestsHomoplastic H (mapDrawingHomeo β.symm H') := by
  rcases h with ⟨α₀, hα₀_bd, hhom⟩
  refine ⟨(β.trans α₀).trans β.symm, fun x hx => ?_, ?_⟩
  · have hβx : β x ∈ bd S' := by
      rw [← image_bd_homeomorph β]
      exact mem_image_of_mem β hx
    have hα₀ : α₀ (β x) = β x := hα₀_bd (β x) hβx
    simp [Homeomorph.trans_apply, hα₀]
  · have hhom' := ForestsHomotopic.map_homeo β.symm hhom
    rwa [mapDrawingHomeo_trans, mapDrawingHomeo_trans] at hhom'

/-- Transport of `IsSurface` along a homeomorphism. -/
theorem isSurface_of_homeo {S' : Type v} [TopologicalSpace S'] (e : S ≃ₜ S') (h : IsSurface S) :
    IsSurface S' := by
  have : CompactSpace S := h.1
  have : T2Space S := h.2.1
  refine ⟨e.surjective.compactSpace e.continuous, e.symm.isEmbedding.t2Space, fun x => ?_⟩
  simpa using isManifoldPoint_of_isOpenEmbedding e.isOpenEmbedding (h.2.2 (e.symm x))

/-- Every surface `S : Type u` is homeomorphic to a topological space `S₀ : Type 0`. -/
theorem exists_homeo_type_zero (hS : IsSurface S) :
    ∃ (S₀ : Type 0) (_ : TopologicalSpace S₀), Nonempty (S ≃ₜ S₀) := by
  classical
  have : CompactSpace S := hS.1
  choose U V hU _ hx hφ using hS.2.2
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover U (fun x _ => (hU x).mem_nhds (hx x))
  have hcov : ∀ s : S, ∃ i : ↥t, s ∈ U i.1 := fun s => by
    obtain ⟨x, hxt, hsx⟩ := mem_iUnion₂.mp (ht.2 (mem_univ s))
    exact ⟨⟨x, hxt⟩, hsx⟩
  choose idx hidx using hcov
  let g : S → Fin t.card × EuclideanHalfSpace 2 := fun s =>
    (t.equivFin (idx s), ((hφ (idx s).1).some ⟨s, hidx s⟩).1)
  have hginj : Function.Injective g := by
    intro s₁ s₂ h
    have h2 : ∀ (i₁ i₂ : ↥t) (h₁ : s₁ ∈ U i₁.1) (h₂ : s₂ ∈ U i₂.1),
        i₁ = i₂ →
        ((hφ i₁.1).some ⟨s₁, h₁⟩).1 = ((hφ i₂.1).some ⟨s₂, h₂⟩).1 → s₁ = s₂ := by
      rintro i₁ _ h₁ h₂ rfl heq
      exact congrArg Subtype.val ((hφ i₁.1).some.injective (Subtype.ext heq))
    exact h2 (idx s₁) (idx s₂) (hidx s₁) (hidx s₂)
      (t.equivFin.injective (Prod.ext_iff.mp h).1) (Prod.ext_iff.mp h).2
  let S₀ : Type 0 := Set.range g
  let e₀ : S ≃ S₀ := Equiv.ofInjective g hginj
  let τ₀ : TopologicalSpace S₀ := TopologicalSpace.induced e₀.symm inferInstance
  let _ : TopologicalSpace S₀ := τ₀
  have hind : Topology.IsInducing e₀ := by
    refine ⟨?_⟩
    change _ = TopologicalSpace.induced e₀ (TopologicalSpace.induced e₀.symm _)
    rw [induced_compose]
    have hcomp : e₀.symm ∘ e₀ = id := funext e₀.symm_apply_apply
    rw [hcomp, induced_id]
  exact ⟨S₀, τ₀, ⟨e₀.toHomeomorphOfIsInducing hind⟩⟩

end GraphMinor.GM07
