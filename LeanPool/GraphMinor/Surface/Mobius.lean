/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutCyl

/-!
# The Möbius band

The unit disc with four sides is mapped onto the Möbius band as in `CutCyl.lean`, by way of the
square `|x| + |y| ≤ 1`. Two opposite sides of this square are pasted with a half turn.
This shows that the word `t r t r'` presents the Möbius band (`presents_mob`), and its normal form
is `Σ(0, 1, 1)` (`nonempty_mob_homeo`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

open scoped unitInterval

/-- Two pairs are glued in the Möbius band exactly if they are equal or are glued by one step. -/
theorem mobius_rel {p q : unitInterval × unitInterval} (h : mobiusSetoid p q) :
    p = q ∨ (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = unitInterval.symm p.2) ∨ (q.1 = 0 ∧ p.1 = 1 ∧ p.2
      = unitInterval.symm q.2) := by
  change Relation.EqvGen _ p q at h
  induction h with
  | rel x y h => exact .inr (.inl h)
  | refl x => exact .inl rfl
  | symm x y _ ih =>
    rcases ih with rfl | h | h
    · exact .inl rfl
    · exact .inr (.inr h)
    · exact .inr (.inl h)
  | trans x y z _ _ h1 h2 =>
    rcases h1 with rfl | h1 | h1
    · exact h2
    · rcases h2 with rfl | h2 | h2
      · exact .inr (.inl h1)
      · exact absurd (h1.2.1.symm.trans h2.1) (by simp)
      · left
        refine Prod.ext (h1.1.trans h2.1.symm) ?_
        have := congrArg unitInterval.symm (h1.2.2.symm.trans h2.2.2)
        simpa using this
    · rcases h2 with rfl | h2 | h2
      · exact .inr (.inr h1)
      · left
        refine Prod.ext (h1.2.1.trans h2.2.1.symm) ?_
        rw [h1.2.2, h2.2.2]
      · exact absurd (h1.1.symm.trans h2.2.1) (by simp)

/-- The Möbius band is a Hausdorff space. -/
instance : T2Space MobiusBand := by
  refine t2Space_quotient_of_isClosed mobiusSetoid ?_
  have e : {p : (I × I) × (I × I) | mobiusSetoid p.1 p.2} = {p | p.1 = p.2} ∪ ({p | p.1.1 = 0
    ∧ p.2.1 = 1 ∧ p.2.2 = unitInterval.symm p.1.2} ∪ {p | p.2.1 = 0 ∧ p.1.1 = 1 ∧ p.1.2
      = unitInterval.symm p.2.2}) := by
    ext p
    constructor
    · intro h
      rcases mobius_rel h with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · have h' : p.1 = p.2 := h
        change mobiusSetoid p.1 p.2
        rw [h']
      · exact Relation.EqvGen.rel _ _ h
      · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h)
  rw [e]
  have c1 : Continuous fun p : (I × I) × (I × I) => p.1.1 := by fun_prop
  have c2 : Continuous fun p : (I × I) × (I × I) => p.2.1 := by fun_prop
  have c3 : Continuous fun p : (I × I) × (I × I) => p.1.2 := by fun_prop
  have c4 : Continuous fun p : (I × I) × (I × I) => p.2.2 := by fun_prop
  refine (isClosed_eq continuous_fst continuous_snd).union (IsClosed.union ?_ ?_)
  · exact (isClosed_eq c1 continuous_const).inter ((isClosed_eq c2 continuous_const).inter
      (isClosed_eq c4 (unitInterval.continuous_symm.comp c3)))
  · exact (isClosed_eq c2 continuous_const).inter ((isClosed_eq c1 continuous_const).inter
      (isClosed_eq c3 (unitInterval.continuous_symm.comp c4)))

/-- The first coordinate on the square. -/
noncomputable def mobU (z : ℂ) : ℝ := (1 - cylS z) / 2

/-- The second coordinate on the square. -/
noncomputable def mobV (z : ℂ) : ℝ := (1 + (nu z).re - (nu z).im) / 2

theorem mobU_mem {z : ℂ} (hz : ‖z‖ ≤ 1) : mobU z ∈ Icc (0 : ℝ) 1 := by
  have := cylS_mem hz
  simp only [mobU]
  exact ⟨by linarith [this.2], by linarith [this.1]⟩

theorem mobV_mem {z : ℂ} (hz : ‖z‖ ≤ 1) : mobV z ∈ Icc (0 : ℝ) 1 := by
  have := cylR_mem hz
  have e : mobV z = cylR z - 1 := by
    simp only [mobV, cylR]
    ring
  rw [e]
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- The point of the square of a point of the disc. -/
noncomputable def mobP (z : ℂ) : unitInterval × unitInterval :=
  (projIcc 0 1 zero_le_one (mobU z), projIcc 0 1 zero_le_one (mobV z))

/-- The map from the disc to the Möbius band. -/
noncomputable def mobG (z : ℂ) : MobiusBand := Quotient.mk mobiusSetoid (mobP z)

theorem mobP_fst {z : ℂ} (hz : ‖z‖ ≤ 1) : ((mobP z).1 : ℝ) = mobU z := by
  simp only [mobP]
  rw [projIcc_of_mem zero_le_one (mobU_mem hz)]

theorem mobP_snd {z : ℂ} (hz : ‖z‖ ≤ 1) : ((mobP z).2 : ℝ) = mobV z := by
  simp only [mobP]
  rw [projIcc_of_mem zero_le_one (mobV_mem hz)]

theorem continuous_mobG : Continuous mobG := by
  have h1 : Continuous mobU := by
    unfold mobU cylS
    have := continuous_nu
    fun_prop
  have h2 : Continuous mobV := by
    unfold mobV
    have := continuous_nu
    fun_prop
  exact continuous_quotient_mk'.comp ((continuous_projIcc.comp h1).prodMk
    (continuous_projIcc.comp h2))

theorem mobG_surj (y : MobiusBand) : ∃ z : ℂ, ‖z‖ ≤ 1 ∧ mobG z = y := by
  obtain ⟨⟨u, v⟩, rfl⟩ := Quotient.exists_rep y
  set s : ℝ := 1 - 2 * u with hs
  set d : ℝ := 2 * v - 1 with hd
  have hs1 : s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [u.2.2], by linarith [u.2.1]⟩
  have hd1 : d ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [v.2.1], by linarith [v.2.2]⟩
  let w : ℂ := ⟨(s + d) / 2, (s - d) / 2⟩
  have hw : nn w ≤ 1 := by
    simp only [nn, w]
    rcases abs_cases ((s + d) / 2) with h1 | h1 <;> rcases abs_cases ((s - d) / 2) with h2 | h2 <;>
      linarith [hs1.1, hs1.2, hd1.1, hd1.2]
  have hz : ‖mu w‖ ≤ 1 := by rw [norm_mu]; exact hw
  refine ⟨mu w, hz, ?_⟩
  have e : mobP (mu w) = (u, v) := by
    apply Prod.ext
    · apply Subtype.ext
      rw [mobP_fst hz]
      simp only [mobU, cylS, nu_mu, w]
      linarith
    · apply Subtype.ext
      rw [mobP_snd hz]
      simp only [mobV, nu_mu, w]
      linarith
  simp only [mobG, e]

theorem nu_neg (z : ℂ) : nu (-z) = - nu z := by
  have h1 : nn (-z) = nn z := by simp [nn]
  simp only [nu, norm_neg, h1, mul_neg]

theorem per_two {t : ℝ} : per 4 (2 + t) = - per 4 t := by
  have e : (2 : ℝ) * Real.pi * (2 + t) / (4 : ℕ) = 2 * Real.pi * t / (4 : ℕ) + Real.pi := by
    push_cast
    ring
  simp only [per, cis', e]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

/-- The word of the Möbius band. -/
def mobW : List Letter := [(0, true), (1, true), (0, true), (2, true)]

theorem sdPt_two' {t : ℝ} : sdPt 4 2 true t = per 4 (2 + t) := by
  simp [sdPt]

theorem mobG_side {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : mobG (per 4 t) = mobG (per 4 (2 + t)) := by
  obtain ⟨h1, h2⟩ := per_quad ht
  have h3 := cylS_quad h1 h2
  rw [norm_per4] at h3
  apply Quotient.sound
  have hn1 := (norm_per4 t).le
  have hn2 := (norm_per4 (2 + t)).le
  refine Relation.EqvGen.rel _ _ ⟨?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [mobP_fst hn1]
    simp [mobU, h3]
  · apply Subtype.ext
    rw [mobP_fst hn2, per_two]
    simp only [mobU, cylS, nu_neg, Complex.neg_re, Complex.neg_im]
    have : (nu (per 4 t)).re + (nu (per 4 t)).im = 1 := h3
    simp only [Icc.coe_one]
    linarith
  · apply Subtype.ext
    rw [mobP_snd hn2]
    simp only [unitInterval.coe_symm_eq]
    rw [mobP_snd hn1, per_two]
    simp only [mobV, nu_neg, Complex.neg_re, Complex.neg_im]
    ring

theorem mobG_fib {z z' : ℂ} (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1) (he : mobG z = mobG z') :
    z = z' ∨ ∃ t ∈ Icc (0 : ℝ) 1, (z = per 4 t ∧ z' = per 4 (2 + t)) ∨ (z' = per 4 t ∧ z = per 4
      (2 + t)) := by
  have key : ∀ {x y : ℂ}, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → (mobP x).1 = 0 → (mobP y).1 = 1 → (mobP y).2
    = unitInterval.symm (mobP x).2 →
      ∃ t ∈ Icc (0 : ℝ) 1, x = per 4 t ∧ y = per 4 (2 + t) := by
    intro x y hx hy h1 h2 h3
    have e1 : cylS x = 1 := by
      have := congrArg (Subtype.val) h1
      rw [mobP_fst hx] at this
      simp only [mobU, Icc.coe_zero] at this
      linarith
    have e2 : cylS y = -1 := by
      have := congrArg (Subtype.val) h2
      rw [mobP_fst hy] at this
      simp only [mobU, Icc.coe_one] at this
      linarith
    have e3 : mobV y = 1 - mobV x := by
      have := congrArg (Subtype.val) h3
      rw [mobP_snd hy] at this
      simp only [unitInterval.coe_symm_eq] at this
      rw [mobP_snd hx] at this
      exact this
    obtain ⟨t, ht, rfl⟩ := exists_side hx e1
    refine ⟨t, ht, rfl, ?_⟩
    rw [per_two]
    apply nu_injective
    rw [nu_neg]
    have e4 : (nu (per 4 t)).re + (nu (per 4 t)).im = 1 := e1
    have e5 : (nu y).re + (nu y).im = -1 := e2
    simp only [mobV] at e3
    apply Complex.ext
    · simp only [Complex.neg_re]
      linarith
    · simp only [Complex.neg_im]
      linarith
  rcases mobius_rel (Quotient.exact he) with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left
    apply nu_injective
    have e1 : mobU z = mobU z' := by rw [← mobP_fst hz, ← mobP_fst hz', h]
    have e2 : mobV z = mobV z' := by rw [← mobP_snd hz, ← mobP_snd hz', h]
    simp only [mobU, cylS, mobV] at e1 e2
    apply Complex.ext <;> linarith
  · obtain ⟨t, ht, h4, h5⟩ := key hz hz' h1 h2 h3
    exact .inr ⟨t, ht, .inl ⟨h4, h5⟩⟩
  · obtain ⟨t, ht, h4, h5⟩ := key hz' hz h1 h2 h3
    exact .inr ⟨t, ht, .inr ⟨h4, h5⟩⟩

theorem mobW_stp {a b : ℕ × ℂ} (h : Stp (sW mobW) a b) : mobG a.2 = mobG b.2 := by
  obtain ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩ := h
  obtain ⟨rfl, h4⟩ := sW_get h1
  obtain ⟨rfl, h5⟩ := sW_get h2
  rw [sW_zero]
  have hlen : mobW.length = 4 := rfl
  simp only [hlen]
  have key : mobG (sdPt 4 0 true t) = mobG (sdPt 4 2 true t) := by
    rw [sdPt_zero, sdPt_two']
    exact mobG_side ht
  rcases p with _ | _ | _ | _ | p <;> rcases q with _ | _ | _ | _ | q <;>
    simp only [mobW, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.some.injEq, reduceCtorEq, Prod.mk.injEq, zero_add, Nat.reduceAdd] at h4 h5 h3
  all_goals obtain ⟨e1, e2⟩ := h4
  all_goals obtain ⟨e3, e4⟩ := h5
  all_goals subst e2 e4
  all_goals first
    | rfl
    | omega
    | exact key.symm

/-- The word `t r t r'` presents the Möbius band. -/
theorem presents_mob : Presents (sW mobW) fun a => mobG a.2 := by
  have hD : ∀ a, a ∈ Dsk (sW mobW) ↔ a.1 = 0 ∧ ‖a.2‖ ≤ 1 := fun a => by
    constructor
    · intro h
      have := mem_Dsk_sW h
      exact ⟨this.1, this.2.2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [h1, sW_zero]
      simp [mobW]
  refine ⟨(continuous_mobG.comp continuous_snd).continuousOn, ?_, ?_⟩
  · refine eq_univ_of_forall fun y => ?_
    obtain ⟨z, hz, rfl⟩ := mobG_surj y
    exact ⟨(0, z), (hD _).mpr ⟨rfl, hz⟩, rfl⟩
  · intro a ha b hb
    obtain ⟨h1, h2⟩ := (hD _).mp ha
    obtain ⟨h3, h4⟩ := (hD _).mp hb
    have ea : a = (0, a.2) := Prod.ext h1 rfl
    have eb : b = (0, b.2) := Prod.ext h3 rfl
    constructor
    · intro he
      rcases mobG_fib h2 h4 he with h5 | ⟨t, ht, ⟨h5, h6⟩ | ⟨h5, h6⟩⟩
      · rw [show a = b from Prod.ext (h1.trans h3.symm) h5]
        exact .refl _
      · rw [ea, eb, h5, h6]
        refine .rel _ _ ⟨0, 0, 0, 2, 0, true, true, t, rfl, rfl, by simp, ht, ?_, ?_⟩
        · simp [sW_zero, mobW, sdPt_zero]
        · simp [sW_zero, mobW, sdPt_two']
      · rw [ea, eb, h5, h6]
        refine .symm _ _ (.rel _ _ ⟨0, 0, 0, 2, 0, true, true, t, rfl, rfl, by simp, ht, ?_, ?_⟩)
        · simp [sW_zero, mobW, sdPt_zero]
        · simp [sW_zero, mobW, sdPt_two']
    · intro hp
      clear ha hb h1 h2 h3 h4 ea eb
      induction hp with
      | rel x y hs => exact mobW_stp hs
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ h1 h2 => exact h1.trans h2

/-- The model with one cross-cap and one hole is the Möbius band. -/
theorem nonempty_mob_homeo : Nonempty (SurfaceModel 0 1 1 ≃ₜ MobiusBand) := by
  have hI : Inv mobW [] [] [] 0 0 0 := by
    refine ⟨.nil, .nil, .nil, by simp [DisjL], by simp [DisjL], by simp [DisjL], by simp [DisjL],
      by simp [DisjL], by simp [DisjL], ?_⟩
    intro k
    simp only [mobW, cnt_cons, cnt_nil]
    split_ifs <;> omega
  have s1 := step_cap.{0} (P := []) (x := (0, true)) (Q := [(1, true)]) (S := [(2, true)]) hI rfl
  obtain ⟨u, s2, s3⟩ := step_last.{0} (q := (2, true)) (Q := winv [(1, true)]) s1.1 (by simp) (by
    intro l hl
    simp only [winv, linv, List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hl ⊢
    rcases hl with rfl | rfl <;> simp [cnt_cons, cnt_nil])
  have : Nonempty MobiusBand := ⟨mobG 0⟩
  obtain ⟨e⟩ := homeo_of_nf presents_mob s2.isNF (s1.2.trans (by simpa using s3))
  exact ⟨e.symm⟩

end GraphMinor.Surface
