/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Certificates.Model
public import LeanPool.ConwaySoifer.Geometry.Support
public import LeanPool.ConwaySoifer.Geometry.Owners
import Mathlib.Tactic

/-!
# Soundness of the contact-sensitive checker

The semantic context of one exclusion problem at a real parameter `x` is `Ctx`: a triangle `U`
of positive side `< 1` containing the real mandatory points, satisfying the contact condition of
every cap for every orientation of `U`, and (when `ord = some i`) the non-overfull condition of
side owner `i`.  The main results are `excluded_sound` (the checker never accepts a satisfiable
problem) and `replay_sound` (a checked forced-point trace excludes every configuration whose
initial model holds).  Everything is proved from the leaf-test semantics of `IntPoly.lean`, the
support and contact lemmas of `Support.lean`, the ray lemmas of `Rays.lean` and convexity.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

@[expose] public section

namespace ConwaySoifer.Certificates
open IPoly

noncomputable section

/-! ## Evaluation -/

/-- Evaluate both integer-polynomial coordinates at a real interval parameter. -/
def evalF (u : IPoint) (x : ℝ) : Point := (evalR u.1 x, evalR u.2 x)

/-- The real point represented by a scaled integer point. -/
def realPt (den : ℝ) (P : IPoint) (x : ℝ) : Point := den⁻¹ • evalF P x

theorem evalR_detP (u v : IPoint) (x : ℝ) : evalR (detP u v) x = cross (evalF u x) (evalF v x) := by
  simp [detP, evalR_sub, evalR_mul, cross, evalF]

theorem evalR_normP (u : IPoint) (x : ℝ) : evalR (normP u) x = normSq (evalF u x) := by
  simp only [normP, evalR_add, evalR_mul, normSq, evalF]; ring

theorem evalF_rotP (u : IPoint) (x : ℝ) : evalF (rotP u) x = rot (evalF u x) := by
  apply Prod.ext <;> simp [rotP, evalF, rot, evalR_sub, evalR_smul]

theorem evalF_negP (u : IPoint) (x : ℝ) : evalF (negP u) x = -evalF u x := by
  apply Prod.ext <;> simp [negP, evalF, evalR_smul]

theorem evalF_psub (p q : IPoint) (x : ℝ) : evalF (psub p q) x = evalF p x - evalF q x := by
  apply Prod.ext <;> simp [psub, evalF, evalR_sub]

theorem evalF_padd (p q : IPoint) (x : ℝ) : evalF (padd p q) x = evalF p x + evalF q x := by
  apply Prod.ext <;> simp [padd, evalF, evalR_add]

theorem evalF_eastP (x : ℝ) : evalF eastP x = eastDir := by
  simp [eastP, evalF, eastDir]

theorem evalF_rotEastP (x : ℝ) : evalF rotEastP x = rot eastDir := by
  apply Prod.ext <;> simp [rotEastP, evalF, eastDir, rot]

theorem evalR_supportNumP (u P₀ P₁ P₂ : IPoint) (x : ℝ) :
    evalR (supportNumP u P₀ P₁ P₂) x =
      supportNum (evalF u x) (evalF P₀ x) (evalF P₁ x) (evalF P₂ x) := by
  simp [supportNumP, evalR_add, evalR_detP, evalF_rotP, supportNum]

theorem evalR_gapP (den : Int) (u P₀ P₁ P₂ : IPoint) (x : ℝ) :
    evalR (gapP den u P₀ P₁ P₂) x =
      supportNum (evalF u x) (evalF P₀ x) (evalF P₁ x) (evalF P₂ x) ^ 2 -
        (den : ℝ) ^ 2 * normSq (evalF u x) := by
  simp only [gapP, evalR_sub, evalR_mul, evalR_smul, evalR_supportNumP, evalR_normP]
  push_cast; ring

theorem evalR_neg (p : IPoly) (x : ℝ) : evalR (smul (-1) p) x = -evalR p x := by
  simp [evalR_smul]

theorem supportNum_smul_pts (c : ℝ) (e p₀ p₁ p₂ : Point) :
    supportNum e (c • p₀) (c • p₁) (c • p₂) = c * supportNum e p₀ p₁ p₂ := by
  simp only [supportNum, cross_smul_right]; ring

theorem cross_realPt (den : ℝ) (e : Point) (P : IPoint) (x : ℝ) :
    cross e (realPt den P x) = den⁻¹ * cross e (evalF P x) := by
  simp [realPt, cross_smul_right]

theorem realPt_sub (den : ℝ) (P Q : IPoint) (x : ℝ) :
    realPt den P x - realPt den Q x = den⁻¹ • (evalF P x - evalF Q x) := by
  simp [realPt, smul_sub]

/-! ## The semantic context -/

/-- The contact condition of a cap on the face with outward direction `n`. -/
def FaceOK (U : EquilateralTriangle) (den x : ℝ) (n : Point) (c : Cap) : Prop :=
  0 < cross n (evalF c.dv x) ∧
    ∀ q ∈ U.carrier, cross n q ≤ cross n (realPt den c.p x) ∧
      (c.strict = true → cross n q < cross n (realPt den c.p x))

/-- The geometric hypotheses of one exclusion problem at parameter `x`. -/
structure Ctx (U : EquilateralTriangle) (den x : ℝ) (Ps : List IPoint) (caps : List Cap)
    (ord : Option (Fin 6)) : Prop where
  side_pos : 0 < U.side
  side_lt : U.side < 1
  mem : ∀ P ∈ Ps, realPt den P x ∈ U.carrier
  cap : ∀ c ∈ caps, ∀ O : Orientation U, ∃ j : Fin 3, FaceOK U den x (rotPow j O.dir) c
  ord : ∀ i, ord = some i → vertex i ∈ U.carrier ∧
    rayLen U (vertex i) (sideDirection i false) + rayLen U (vertex i) (sideDirection i true) ≤
        U.side

variable {U : EquilateralTriangle} {den x : ℝ} {Ps : List IPoint} {caps : List Cap}
  {ord : Option (Fin 6)}

theorem Ctx.mono {Ps' : List IPoint} (C : Ctx U den x Ps caps ord) (h : ∀ P ∈ Ps', P ∈ Ps) :
    Ctx U den x Ps' caps ord :=
  ⟨C.side_pos, C.side_lt, fun P hP => C.mem P (h P hP), C.cap, C.ord⟩

/-! ## Support certificates -/

theorem nth_mem {α : Type} : ∀ (l : List α) (i : Nat) {a : α}, nth l i = some a → a ∈ l
  | [], _, _, h => by simp [nth] at h
  | _ :: _, 0, _, h => by
      simp only [nth, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
  | _ :: l, i + 1, _, h => by
      simp only [nth] at h
      exact List.mem_cons_of_mem _ (nth_mem l i h)

/-- The support bound at direction `e` for the real points. -/
def HasBound (den : ℝ) (Ps : List IPoint) (x : ℝ) (e : Point) : Prop :=
  ∃ P₀ ∈ Ps, ∃ P₁ ∈ Ps, ∃ P₂ ∈ Ps,
    len e ≤ supportNum e (realPt den P₀ x) (realPt den P₁ x) (realPt den P₂ x)

theorem supportOK_sound {denI : Int} (hden : 0 < denI) {u : IPoint} {T : Triple}
    {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : supportOK Ps denI u T a b d fuel = true) (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d) :
    HasBound (denI : ℝ) Ps x (evalF u x) := by
  unfold supportOK at h
  split at h
  · next P₀ P₁ P₂ h₀ h₁ h₂ =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨hn, hg⟩ := h
    have hn' := nonnegOn_sound _ a b d fuel hn hd x hlo hhi
    have hg' := nonnegOn_sound _ a b d fuel hg hd x hlo hhi
    rw [evalR_supportNumP] at hn'
    rw [evalR_gapP] at hg'
    have hdenR : (0 : ℝ) < denI := by
      exact_mod_cast hden
    refine ⟨P₀, nth_mem _ _ h₀, P₁, nth_mem _ _ h₁, P₂, nth_mem _ _ h₂, ?_⟩
    simp only [realPt]
    rw [supportNum_smul_pts]
    set N := supportNum (evalF u x) (evalF P₀ x) (evalF P₁ x) (evalF P₂ x)
    have hsq : ((denI : ℝ) * len (evalF u x)) ^ 2 ≤ N ^ 2 := by
      rw [mul_pow, len_sq]; linarith
    have hl : (denI : ℝ) * len (evalF u x) ≤ N := by
      have hpos : 0 ≤ (denI : ℝ) * len (evalF u x) := mul_nonneg hdenR.le (len_nonneg _)
      nlinarith [hsq, hn', hpos]
    rw [le_inv_mul_iff₀ hdenR]
    exact hl
  · simp at h

theorem HasBound.smul {e : Point} {t : ℝ} (ht : 0 ≤ t) (h : HasBound den Ps x e) :
    HasBound den Ps x (t • e) := by
  obtain ⟨P₀, h₀, P₁, h₁, P₂, h₂, hb⟩ := h
  refine ⟨P₀, h₀, P₁, h₁, P₂, h₂, ?_⟩
  rw [len_smul_nonneg ht, supportNum_smul]
  exact mul_le_mul_of_nonneg_left hb ht

/-- A support bound for the real points at the orientation direction is impossible. -/
theorem HasBound.false (C : Ctx U den x Ps caps ord) (O : Orientation U)
    (h : HasBound den Ps x O.dir) : False := by
  obtain ⟨P₀, h₀, P₁, h₁, P₂, h₂, hb⟩ := h
  have := O.one_le_side_of_bound (C.mem P₀ h₀) (C.mem P₁ h₁) (C.mem P₂ h₂) hb
  linarith [C.side_lt]

/-- Two support bounds with a common triple propagate to positive combinations. -/
theorem supportOK_cone {denI : Int} (hden : 0 < denI) {u v : IPoint} {T : Triple}
    {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (hu : supportOK Ps denI u T a b d fuel = true) (hv : supportOK Ps denI v T a b d fuel = true)
    (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    HasBound (denI : ℝ) Ps x (α • evalF u x + β • evalF v x) := by
  -- the same triple is used at both ends: extract it once
  unfold supportOK at hu hv
  split at hu
  · next P₀ P₁ P₂ h₀ h₁ h₂ =>
    rw [h₀, h₁, h₂] at hv
    simp only [Bool.and_eq_true] at hu hv
    have hdenR : (0 : ℝ) < denI := by
      exact_mod_cast hden
    have key : ∀ w : IPoint, nonnegOn (supportNumP w P₀ P₁ P₂) a b d fuel = true →
        nonnegOn (gapP denI w P₀ P₁ P₂) a b d fuel = true →
        len (evalF w x) ≤ supportNum (evalF w x) (realPt denI P₀ x) (realPt denI P₁ x)
          (realPt denI P₂ x) := by
      intro w hn hg
      have hn' := nonnegOn_sound _ a b d fuel hn hd x hlo hhi
      have hg' := nonnegOn_sound _ a b d fuel hg hd x hlo hhi
      rw [evalR_supportNumP] at hn'
      rw [evalR_gapP] at hg'
      simp only [realPt]
      rw [supportNum_smul_pts]
      set N := supportNum (evalF w x) (evalF P₀ x) (evalF P₁ x) (evalF P₂ x)
      have hsq : ((denI : ℝ) * len (evalF w x)) ^ 2 ≤ N ^ 2 := by
        rw [mul_pow, len_sq]; linarith
      have hl : (denI : ℝ) * len (evalF w x) ≤ N := by
        have hpos : 0 ≤ (denI : ℝ) * len (evalF w x) := mul_nonneg hdenR.le (len_nonneg _)
        nlinarith [hsq, hn', hpos]
      rw [le_inv_mul_iff₀ hdenR]
      exact hl
    have bu := key u hu.1 hu.2
    have bv := key v hv.1 hv.2
    refine ⟨P₀, nth_mem _ _ h₀, P₁, nth_mem _ _ h₁, P₂, nth_mem _ _ h₂, ?_⟩
    calc len (α • evalF u x + β • evalF v x)
        ≤ len (α • evalF u x) + len (β • evalF v x) := len_add_le _ _
      _ = α * len (evalF u x) + β * len (evalF v x) := by
          rw [len_smul_nonneg hα, len_smul_nonneg hβ]
      _ ≤ α * supportNum (evalF u x) _ _ _ + β * supportNum (evalF v x) _ _ _ :=
          add_le_add (mul_le_mul_of_nonneg_left bu hα) (mul_le_mul_of_nonneg_left bv hβ)
      _ = supportNum (α • evalF u x + β • evalF v x) _ _ _ := by
          rw [supportNum_add, supportNum_smul, supportNum_smul]
  · simp at hu

/-! ## Contact certificates -/

theorem badFace_sound (C : Ctx U den x Ps caps ord) {denI : Int} (hden : (denI : ℝ) = den)
    (hdpos : 0 < denI) {e : IPoint} {c : Cap} {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : badFace Ps e c a b d fuel = true) (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) {t : ℝ} (ht : 0 < t)
    (hF : FaceOK U den x (t • evalF e x) c) : False := by
  have hdenR : (0 : ℝ) < den := by
    rw [← hden]; exact_mod_cast hdpos
  unfold badFace at h
  simp only [Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨h1, h2⟩ := hF
  rcases h with h | ⟨q, hq, hbad⟩
  · have := nonnegOn_sound _ a b d fuel h hd x hlo hhi
    rw [evalR_neg, evalR_detP] at this
    rw [cross_smul_left] at h1
    nlinarith
  · have hqU := C.mem q hq
    obtain ⟨hle, hlt⟩ := h2 _ hqU
    rw [cross_smul_left, cross_smul_left, cross_realPt, cross_realPt] at hle hlt
    have hdiff : cross (evalF e x) (evalF c.p x) - cross (evalF e x) (evalF q x) =
        cross (evalF e x) (evalF c.p x - evalF q x) := by
          rw [cross_sub_right]
    by_cases hs : c.strict = true
    · rw [ite_eq_left hs] at hbad
      have := nonnegOn_sound _ a b d fuel hbad hd x hlo hhi
      rw [evalR_neg, evalR_detP, evalF_psub, ← hdiff] at this
      have := hlt hs
      have hpos : 0 < t * den⁻¹ := by
        positivity
      nlinarith
    · rw [ite_eq_right hs] at hbad
      have := posOn_sound _ a b d fuel hbad hd x hx hlo hhi
      rw [evalR_neg, evalR_detP, evalF_psub, ← hdiff] at this
      have hpos : 0 < t * den⁻¹ := by
        positivity
      nlinarith

theorem badFaceCone_sound (C : Ctx U den x Ps caps ord) {denI : Int} (hden : (denI : ℝ) = den)
    (hdpos : 0 < denI) {eu ev : IPoint} {c : Cap} {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : badFaceCone Ps eu ev c a b d fuel = true) (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hF : FaceOK U den x (α • evalF eu x + β • evalF ev x) c) : False := by
  have hdenR : (0 : ℝ) < den := by
    rw [← hden]; exact_mod_cast hdpos
  unfold badFaceCone at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨h1, h2⟩ := hF
  rcases h with ⟨hu, hv⟩ | ⟨q, hq, ⟨hfu, hfv⟩, hrest⟩
  · have hu' := nonnegOn_sound _ a b d fuel hu hd x hlo hhi
    have hv' := nonnegOn_sound _ a b d fuel hv hd x hlo hhi
    rw [evalR_neg, evalR_detP] at hu' hv'
    rw [cross_add_left, cross_smul_left, cross_smul_left] at h1
    nlinarith
  · have hqU := C.mem q hq
    obtain ⟨hle, hlt⟩ := h2 _ hqU
    simp only [cross_add_left, cross_smul_left, cross_realPt] at hle hlt
    have hfu' := nonnegOn_sound _ a b d fuel hfu hd x hlo hhi
    have hfv' := nonnegOn_sound _ a b d fuel hfv hd x hlo hhi
    rw [evalR_neg, evalR_detP, evalF_psub, cross_sub_right] at hfu' hfv'
    set A := cross (evalF eu x) (evalF c.p x) - cross (evalF eu x) (evalF q x) with hA
    set B := cross (evalF ev x) (evalF c.p x) - cross (evalF ev x) (evalF q x) with hB
    have hA0 : A ≤ 0 := by
      linarith
    have hB0 : B ≤ 0 := by
      linarith
    have hi : 0 < den⁻¹ := inv_pos.mpr hdenR
    rcases hrest with hs | hpos
    · have := hlt hs
      have hprod : 0 ≤ den⁻¹ * (α * (-A) + β * (-B)) :=
        mul_nonneg hi.le (add_nonneg (mul_nonneg hα.le (by linarith)) (mul_nonneg hβ.le (by
            linarith)))
      have hexp : den⁻¹ * (α * (-A) + β * (-B)) =
          (α * (den⁻¹ * cross (evalF eu x) (evalF q x)) + β * (den⁻¹ * cross (evalF ev x) (evalF q
              x))) -
          (α * (den⁻¹ * cross (evalF eu x) (evalF c.p x)) + β * (den⁻¹ * cross (evalF ev x) (evalF
              c.p x))) := by
        rw [hA, hB]; ring
      linarith
    · have hp := posOn_sound _ a b d fuel hpos hd x hx hlo hhi
      rw [evalR_add, evalR_mul, evalR_mul, evalR_neg, evalR_neg, evalR_detP, evalR_detP,
        evalF_psub, cross_sub_right] at hp
      simp only [cross_sub_right] at hp
      have hAB : 0 < A * A + B * B := by
        rw [hA, hB]; nlinarith [hp]
      have hcomb : α * A + β * B < 0 := by
        rcases lt_or_eq_of_le hA0 with hA' | hA'
        · nlinarith
        · rw [hA'] at hAB ⊢
          have hB' : B < 0 := by
            rcases lt_or_eq_of_le hB0 with h | h
            · exact h
            · rw [h] at hAB; simp at hAB
          nlinarith
      have hprod : den⁻¹ * (α * A + β * B) < 0 := mul_neg_of_pos_of_neg hi hcomb
      have hexp : den⁻¹ * (α * A + β * B) =
          (α * (den⁻¹ * cross (evalF eu x) (evalF c.p x)) + β * (den⁻¹ * cross (evalF ev x) (evalF
              c.p x))) -
          (α * (den⁻¹ * cross (evalF eu x) (evalF q x)) + β * (den⁻¹ * cross (evalF ev x) (evalF q
              x))) := by
        rw [hA, hB]; ring
      linarith

theorem rotPow_eval (j : Fin 3) (u : IPoint) (x : ℝ) :
    ∃ w : IPoint, rotPow j (evalF u x) = evalF w x ∧
      (j = 0 → w = u) ∧ (j = 1 → w = rotP u) ∧ (j = 2 → w = rotP (rotP u)) := by
  fin_cases j
  · exact ⟨u, rfl, fun _ => rfl, fun h => by simp at h, fun h => by simp at h⟩
  · exact ⟨rotP u, by simp [evalF_rotP], fun h => by simp at h, fun _ => rfl, fun h => by simp at h⟩
  · exact ⟨rotP (rotP u), by simp [evalF_rotP], fun h => by simp at h, fun h => by simp at h,
      fun _ => rfl⟩

theorem capNode_sound (C : Ctx U den x Ps caps ord) {denI : Int} (hden : (denI : ℝ) = den)
    (hdpos : 0 < denI) {u : IPoint} {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : capNode Ps caps u a b d fuel = true) (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) (O : Orientation U) {t : ℝ} (ht : 0 < t)
    (hdir : O.dir = t • evalF u x) : False := by
  unfold capNode at h
  simp only [List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨c, hc, ⟨h0, h1⟩, h2⟩ := h
  obtain ⟨j, hF⟩ := C.cap c hc O
  rw [hdir, rotPow_smul] at hF
  obtain hj | hj | hj : j = 0 ∨ j = 1 ∨ j = 2 := by
    fin_cases j <;> simp
  · subst hj
    exact badFace_sound C hden hdpos hd h0 hx hlo hhi ht hF
  · subst hj
    simp only [rotPow_one] at hF
    rw [← evalF_rotP] at hF
    exact badFace_sound C hden hdpos hd h1 hx hlo hhi ht hF
  · subst hj
    simp only [rotPow_two] at hF
    rw [← evalF_rotP, ← evalF_rotP] at hF
    exact badFace_sound C hden hdpos hd h2 hx hlo hhi ht hF

theorem capCone_sound (C : Ctx U den x Ps caps ord) {denI : Int} (hden : (denI : ℝ) = den)
    (hdpos : 0 < denI) {u v : IPoint} {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : capCone Ps caps u v a b d fuel = true) (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) (O : Orientation U) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hdir : O.dir = α • evalF u x + β • evalF v x) : False := by
  unfold capCone at h
  simp only [List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨c, hc, ⟨h0, h1⟩, h2⟩ := h
  obtain ⟨j, hF⟩ := C.cap c hc O
  rw [hdir, rotPow_add, rotPow_smul, rotPow_smul] at hF
  obtain hj | hj | hj : j = 0 ∨ j = 1 ∨ j = 2 := by
    fin_cases j <;> simp
  · subst hj
    exact badFaceCone_sound C hden hdpos hd h0 hx hlo hhi hα hβ hF
  · subst hj
    simp only [rotPow_one] at hF
    rw [← evalF_rotP, ← evalF_rotP] at hF
    exact badFaceCone_sound C hden hdpos hd h1 hx hlo hhi hα hβ hF
  · subst hj
    simp only [rotPow_two] at hF
    rw [← evalF_rotP, ← evalF_rotP, ← evalF_rotP, ← evalF_rotP] at hF
    exact badFaceCone_sound C hden hdpos hd h2 hx hlo hhi hα hβ hF

/-! ## Nodes and cones -/

theorem nodeCheck_sound (C : Ctx U den x Ps caps ord) {denI : Int} (hden : (denI : ℝ) = den)
    (hdpos : 0 < denI) {N : Nat} {u : IPoint} {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : nodeCheck Ps denI caps N u a b d fuel = true) (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) (O : Orientation U) {t : ℝ} (ht : 0 < t)
    (hdir : O.dir = t • evalF u x) : False := by
  unfold nodeCheck at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · unfold supportNode at h
    simp only [Bool.or_eq_true] at h
    have hb : HasBound (denI : ℝ) Ps x (evalF u x) := by
      rcases h with (h | h) | h <;> exact supportOK_sound hdpos hd h hlo hhi
    rw [hden] at hb
    have hb' : HasBound den Ps x O.dir := by
      rw [hdir]; exact hb.smul ht.le
    exact hb'.false C O
  · exact capNode_sound C hden hdpos hd h hx hlo hhi O ht hdir

theorem coneCheck_sound (C : Ctx U den x Ps caps ord) {denI : Int} (hden : (denI : ℝ) = den)
    (hdpos : 0 < denI) {N : Nat} {u v : IPoint} {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : coneCheck Ps denI caps N u v a b d fuel = true) (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) (O : Orientation U) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hdir : O.dir = α • evalF u x + β • evalF v x) : False := by
  unfold coneCheck at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · unfold supportCone at h
    simp only [List.any_eq_true, Bool.and_eq_true] at h
    obtain ⟨T, -, hu, hv⟩ := h
    have hb := supportOK_cone hdpos hd hu hv hlo hhi hα.le hβ.le
    rw [hden] at hb
    have hb' : HasBound den Ps x O.dir := by
      rw [hdir]; exact hb
    exact hb'.false C O
  · exact capCone_sound C hden hdpos hd h hx hlo hhi O hα hβ hdir

/-- The direction of a node lies in the first cone and is nonzero (from `nodeCond`). -/
def InArc (e : Point) : Prop := 0 ≤ cross eastDir e ∧ 0 ≤ cross e (rot eastDir)

theorem nodeCond_sound {u : IPoint} {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : nodeCond u a b d fuel = true) (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) : InArc (evalF u x) ∧ evalF u x ≠ 0 := by
  unfold nodeCond at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h1' := nonnegOn_sound _ a b d fuel h1 hd x hlo hhi
  have h2' := nonnegOn_sound _ a b d fuel h2 hd x hlo hhi
  have h3' := posOn_sound _ a b d fuel h3 hd x hx hlo hhi
  rw [evalR_detP, evalF_eastP] at h1'
  rw [evalR_detP, evalF_rotEastP] at h2'
  rw [evalR_normP, normSq_pos_iff] at h3'
  exact ⟨⟨h1', h2'⟩, h3'⟩

/-- Every direction of the closed cone `(u, v)` is rejected, given that `u` and `v` satisfy the
node conditions and the node/cone checks hold. -/
theorem cone_rejects (C : Ctx U den x Ps caps ord) {denI : Int} (hden : (denI : ℝ) = den)
    (hdpos : 0 < denI) {N : Nat} {u v : IPoint} {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d)
    (hu : nodeCheck Ps denI caps N u a b d fuel = true)
    (hv : nodeCheck Ps denI caps N v a b d fuel = true)
    (huv : coneCheck Ps denI caps N u v a b d fuel = true)
    (hdet : 0 ≤ cross (evalF u x) (evalF v x))
    (hu' : InArc (evalF u x)) (hu0 : evalF u x ≠ 0) (hv' : InArc (evalF v x)) (hv0 : evalF v x ≠ 0)
    (O : Orientation U) (hO : InArc O.dir)
    (h1 : 0 ≤ cross (evalF u x) O.dir) (h2 : 0 ≤ cross O.dir (evalF v x)) : False := by
  have hO0 : O.dir ≠ 0 := by
    intro h0; have := O.dir_pos; rw [h0] at this; simp [normSq] at this
  rcases lt_or_eq_of_le hdet with hpos | hzero
  · obtain ⟨α, β, hα, hβ, hdir⟩ := exists_nonneg_combo_of_cross hpos h1 h2
    rcases lt_or_eq_of_le hα with hα' | hα'
    · rcases lt_or_eq_of_le hβ with hβ' | hβ'
      · exact coneCheck_sound C hden hdpos hd huv hx hlo hhi O hα' hβ' hdir
      · rw [← hβ', zero_smul, add_zero] at hdir
        exact nodeCheck_sound C hden hdpos hd hu hx hlo hhi O hα' hdir
    · rw [← hα', zero_smul, zero_add] at hdir
      rcases lt_or_eq_of_le hβ with hβ' | hβ'
      · exact nodeCheck_sound C hden hdpos hd hv hx hlo hhi O hβ' hdir
      · rw [← hβ', zero_smul] at hdir
        exact hO0 hdir
  · -- degenerate cone: `v` is a positive multiple of `u`, hence so is `O.dir`
    have hpar : cross (evalF u x) O.dir = 0 := by
      obtain ⟨c, hc, hcv⟩ := pos_of_parallel_in_arc hu0 hv0 hu'.1 hu'.2 hv'.1 hv'.2 hzero.symm
      rw [hcv, cross_smul_right] at h2
      have : cross O.dir (evalF u x) = -cross (evalF u x) O.dir := cross_anticomm _ _
      nlinarith
    obtain ⟨t, ht, hdir⟩ := pos_of_parallel_in_arc hu0 hO0 hu'.1 hu'.2 hO.1 hO.2 hpar
    exact nodeCheck_sound C hden hdpos hd hu hx hlo hhi O ht hdir

theorem inArc_rotEast : InArc (rot eastDir) := by
  simp [InArc, cross, eastDir, rot]

theorem rotEast_ne_zero : rot eastDir ≠ 0 := by
  simp [eastDir, rot]

theorem nodesOK_sound (C : Ctx U den x Ps caps ord) {denI : Int} (hden : (denI : ℝ) = den)
    (hdpos : 0 < denI) {N : Nat} {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d) (O : Orientation U)
    (hO : InArc O.dir) (ns : List IPoint) :
    ∀ u : IPoint, nodesOK Ps denI caps N a b d fuel u ns = true →
      InArc (evalF u x) → evalF u x ≠ 0 →
      0 ≤ cross (evalF u x) O.dir → 0 ≤ cross O.dir (rot eastDir) → False := by
  induction ns with
  | nil => intro u h; simp [nodesOK] at h
  | cons v rest ih =>
    intro u h hu' hu0 h1 h2
    cases rest with
    | nil =>
      rw [nodesOK] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hnu, hc⟩, hdet⟩, hv⟩, hnv⟩ := h
      subst hv
      have hdet' := nonnegOn_sound _ a b d fuel hdet hd x hlo hhi
      rw [evalR_detP] at hdet'
      exact cone_rejects C hden hdpos hd hx hlo hhi hnu hnv hc hdet' hu' hu0
        (by rw [evalF_rotEastP]; exact inArc_rotEast) (by rw [evalF_rotEastP]; exact
            rotEast_ne_zero)
        O hO h1 (by rw [evalF_rotEastP]; exact h2)
    | cons w rest' =>
      rw [nodesOK] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨hnu, hc⟩, hdet⟩, hcond⟩, hrest⟩ := h
      have hdet' := nonnegOn_sound _ a b d fuel hdet hd x hlo hhi
      rw [evalR_detP] at hdet'
      obtain ⟨hv', hv0⟩ := nodeCond_sound hd hcond hx hlo hhi
      rcases le_total (cross (evalF v x) O.dir) 0 with hle | hge
      · -- `O.dir` lies in the cone `(u, v)`
        have h2' : 0 ≤ cross O.dir (evalF v x) := by
          rw [cross_anticomm]; linarith
        -- `v` passes its node check (from the recursive call)
        have hnv : nodeCheck Ps denI caps N v a b d fuel = true := by
          cases rest' with
          | nil =>
            rw [nodesOK] at hrest
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
            exact hrest.1.1.1.1
          | cons _ _ =>
            rw [nodesOK] at hrest
            simp only [Bool.and_eq_true] at hrest
            exact hrest.1.1.1.1
        exact cone_rejects C hden hdpos hd hx hlo hhi hnu hnv hc hdet' hu' hu0 hv' hv0 O hO h1 h2'
      · exact ih v hrest hv' hv0 hge h2

theorem fanCheck_sound (C : Ctx U den x Ps caps ord) {denI : Int} (hden : (denI : ℝ) = den)
    (hdpos : 0 < denI) {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : fanCheck Ps denI caps a b d fuel = true) (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) : False := by
  obtain ⟨O, hO1, hO2⟩ := U.exists_orientation_in_arc C.side_pos
  unfold fanCheck at h
  refine nodesOK_sound C hden hdpos hd hx hlo hhi O ⟨hO1, hO2⟩ _ eastP h ?_ ?_ ?_ hO2
  · rw [evalF_eastP]; simp [InArc, cross, eastDir, rot]
  · rw [evalF_eastP]; simp [eastDir]
  · rw [evalF_eastP]; exact hO1

/-! ## Diameter -/

theorem mem_pairDirs {e : IPoint} : ∀ {Ps : List IPoint}, e ∈ pairDirs Ps →
    ∃ P ∈ Ps, ∃ Q ∈ Ps, e = psub Q P := by
  intro Ps
  induction Ps with
  | nil => intro h; simp [pairDirs] at h
  | cons P Ps ih =>
    intro h
    simp only [pairDirs, List.mem_append, List.mem_map] at h
    rcases h with ⟨Q, hQ, rfl⟩ | h
    · exact ⟨P, List.mem_cons_self .., Q, List.mem_cons_of_mem _ hQ, rfl⟩
    · obtain ⟨P', hP', Q', hQ', rfl⟩ := ih h
      exact ⟨P', List.mem_cons_of_mem _ hP', Q', List.mem_cons_of_mem _ hQ', rfl⟩

theorem sqDist_realPt (den : ℝ) (P Q : IPoint) (x : ℝ) :
    sqDist (realPt den P x) (realPt den Q x) = den⁻¹ ^ 2 * normSq (evalF P x - evalF Q x) := by
  rw [sqDist_eq_normSq_sub, realPt_sub, normSq_smul]

theorem diamCheck_sound (C : Ctx U den x Ps caps ord) {denI : Int} (hden : (denI : ℝ) = den)
    (hdpos : 0 < denI) {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : diamCheck Ps denI a b d fuel = true) (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d) :
    False := by
  unfold diamCheck at h
  simp only [List.any_eq_true] at h
  obtain ⟨e, he, hb⟩ := h
  obtain ⟨P, hP, Q, hQ, rfl⟩ := mem_pairDirs he
  have := nonnegOn_sound _ a b d fuel hb hd x hlo hhi
  rw [evalR_sub, evalR_normP, evalF_psub] at this
  simp only [evalR_cons, evalR_nil, mul_zero, add_zero] at this
  push_cast at this
  have hdenR : (0 : ℝ) < den := by
    rw [← hden]; exact_mod_cast hdpos
  have hdist : 1 ≤ sqDist (realPt den Q x) (realPt den P x) := by
    rw [sqDist_realPt]
    have : normSq (evalF Q x - evalF P x) ≥ den ^ 2 := by
      rw [← hden]; linarith
    calc
      (1 : ℝ) = den⁻¹ ^ 2 * den ^ 2 := by
        field_simp
      _ ≤ den⁻¹ ^ 2 * normSq (evalF Q x - evalF P x) :=
          mul_le_mul_of_nonneg_left this (by positivity)
  exact U.cannot_contain_unit_chord C.side_lt hdist (C.mem Q hQ) (C.mem P hP)

/-! ## Non-overfull owners -/

theorem evalF_vertexP (den : Int) (i : Fin 6) (x : ℝ) :
    evalF (vertexP den i) x = (den : ℝ) • vertex i := by
  fin_cases i <;> apply Prod.ext <;> simp [vertexP, evalF, vertex]

theorem realPt_vertexP {denI : Int} (hden : (denI : ℝ) = den) (hdpos : 0 < denI) (i : Fin 6)
    (x : ℝ) : realPt den (vertexP denI i) x = vertex i := by
  have hdenR : (0 : ℝ) < den := by
    rw [← hden]; exact_mod_cast hdpos
  rw [realPt, evalF_vertexP, hden, smul_smul, inv_mul_cancel₀ hdenR.ne', one_smul]

/-- Cramer's rule for the crossing of the segment `[A, B]` with the ray `V + t • D`
(polynomial form). -/
theorem cramer_scaled (AA BB VV DV : Point) :
    cross (BB - AA) DV • AA + cross (VV - AA) DV • (BB - AA) =
      cross (BB - AA) DV • VV + cross (BB - AA) (AA - VV) • DV := by
  obtain ⟨a₁, a₂⟩ := AA
  obtain ⟨b₁, b₂⟩ := BB
  obtain ⟨v₁, v₂⟩ := VV
  obtain ⟨d₁, d₂⟩ := DV
  apply Prod.ext <;> simp [cross] <;> ring

theorem cramer_identity {AA BB VV DV : Point} (hne : cross (BB - AA) DV ≠ 0) :
    AA + (cross (VV - AA) DV / cross (BB - AA) DV) • (BB - AA) =
      VV + (cross (BB - AA) (AA - VV) / cross (BB - AA) DV) • DV := by
  have h := congrArg (fun p : Point => (cross (BB - AA) DV)⁻¹ • p) (cramer_scaled AA BB VV DV)
  simp only [smul_add, smul_smul, inv_mul_cancel₀ hne, one_smul] at h
  rw [div_eq_inv_mul, div_eq_inv_mul]
  exact h

/-- A verified crossing pair gives a lower bound for the full ray length. -/
theorem crossesRay_sound (C : Ctx U den x Ps caps ord) {denI : Int} (hden : (denI : ℝ) = den)
    (hdpos : 0 < denI) {i : Fin 6} {right : Bool} {A B : IPoint} (hA : A ∈ Ps) (hB : B ∈ Ps)
    (hv : vertex i ∈ U.carrier) {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : crossesRay (vertexP denI i) (psub (vertexP denI (neighbor i right)) (vertexP denI i)) A B
      a b d fuel = true) (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d) :
    0 < evalR (detP (psub B A) (psub (vertexP denI (neighbor i right)) (vertexP denI i))) x ∧
      0 ≤ evalR (detP (psub B A) (psub A (vertexP denI i))) x ∧
      evalR (detP (psub B A) (psub A (vertexP denI i))) x /
        evalR (detP (psub B A) (psub (vertexP denI (neighbor i right)) (vertexP denI i))) x ≤
          rayLen U (vertex i) (sideDirection i right) := by
  unfold crossesRay at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hdd, hmu⟩, hdm⟩, hnm⟩ := h
  have hdd' := posOn_sound _ a b d fuel hdd hd x hx hlo hhi
  have hmu' := nonnegOn_sound _ a b d fuel hmu hd x hlo hhi
  have hdm' := nonnegOn_sound _ a b d fuel hdm hd x hlo hhi
  have hnm' := nonnegOn_sound _ a b d fuel hnm hd x hlo hhi
  rw [evalR_sub] at hdm'
  refine ⟨hdd', hnm', ?_⟩
  have hdenR : (0 : ℝ) < den := by
    rw [← hden]; exact_mod_cast hdpos
  -- the real vectors
  set AA := evalF A x with hAA
  set BB := evalF B x with hBB
  set VV := evalF (vertexP denI i) x with hVV
  set DV := evalF (psub (vertexP denI (neighbor i right)) (vertexP denI i)) x with hDV
  have eDD : evalR (detP (psub B A) (psub (vertexP denI (neighbor i right)) (vertexP denI i))) x =
      cross (BB - AA) DV := by
        rw [evalR_detP, evalF_psub]
  have eMU : evalR (detP (psub (vertexP denI i) A)
      (psub (vertexP denI (neighbor i right)) (vertexP denI i))) x = cross (VV - AA) DV := by
    rw [evalR_detP, evalF_psub]
  have eNM : evalR (detP (psub B A) (psub A (vertexP denI i))) x = cross (BB - AA) (AA - VV) := by
    rw [evalR_detP, evalF_psub, evalF_psub]
  rw [eDD] at hdd' hdm' ⊢
  rw [eMU] at hmu' hdm'
  rw [eNM] at hnm' ⊢
  have hAU := C.mem A hA
  have hBU := C.mem B hB
  -- the crossing point lies in `U`
  have hlam0 : 0 ≤ cross (VV - AA) DV / cross (BB - AA) DV := div_nonneg hmu' hdd'.le
  have hlam1 : cross (VV - AA) DV / cross (BB - AA) DV ≤ 1 := by
    rw [div_le_one hdd']; linarith
  have hmem : realPt den A x + (cross (VV - AA) DV / cross (BB - AA) DV) •
      (realPt den B x - realPt den A x) ∈ U.carrier :=
    U.convex_carrier.add_smul_sub_mem hAU hBU ⟨hlam0, hlam1⟩
  -- and equals `vertex i + t • dir`
  have hdir : sideDirection i right = den⁻¹ • DV := by
    rw [hDV, evalF_psub, evalF_vertexP, evalF_vertexP, ← smul_sub, smul_smul, hden,
      inv_mul_cancel₀ hdenR.ne', one_smul]
    rfl
  have hvert : vertex i = den⁻¹ • VV := by
    rw [hVV, evalF_vertexP, smul_smul, hden, inv_mul_cancel₀ hdenR.ne', one_smul]
  have hident : realPt den A x + (cross (VV - AA) DV / cross (BB - AA) DV) •
      (realPt den B x - realPt den A x) =
      linePoint (vertex i) (sideDirection i right)
        (cross (BB - AA) (AA - VV) / cross (BB - AA) DV) := by
    rw [linePoint, hdir, hvert]
    simp only [realPt, ← hAA, ← hBB]
    rw [← smul_sub, smul_comm _ den⁻¹, ← smul_add, smul_comm _ den⁻¹, ← smul_add]
    congr 1
    exact cramer_identity hdd'.ne'
  rw [hident] at hmem
  exact (linePoint_mem_iff_le_rayLen U hv (sideDirection_unit i right)
    (div_nonneg hnm' hdd'.le)).mp hmem

theorem ordinaryExclusion_sound (C : Ctx U den x Ps caps ord) {denI : Int}
    (hden : (denI : ℝ) = den) (hdpos : 0 < denI) {i : Fin 6} (hi : ord = some i)
    {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : ordinaryExclusion Ps denI i a b d fuel = true) (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) : False := by
  obtain ⟨hv, hsum⟩ := C.ord i hi
  unfold ordinaryExclusion rayBoundsSum at h
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨A, B⟩, -, ⟨A', B'⟩, -, ⟨⟨⟨⟨⟨⟨hA, hB⟩, hA'⟩, hB'⟩, hc1⟩, hc2⟩, hgap⟩⟩ := h
  have h1 := crossesRay_sound C hden hdpos (right := false) hA hB hv hd hc1 hx hlo hhi
  have h2 := crossesRay_sound C hden hdpos (right := true) hA' hB' hv hd hc2 hx hlo hhi
  obtain ⟨hdd1, hnm1, hr1⟩ := h1
  obtain ⟨hdd2, hnm2, hr2⟩ := h2
  have hg := nonnegOn_sound _ a b d fuel hgap hd x hlo hhi
  simp only [evalR_sub, evalR_add, evalR_mul] at hg
  simp only [neighbor, Bool.false_eq_true, ↓reduceIte] at hg hr1 hr2 hdd1 hdd2 hnm1 hnm2
  set NM1 := evalR (detP (psub B A) (psub A (vertexP denI i))) x
  set DD1 := evalR (detP (psub B A) (psub (vertexP denI (i + 5)) (vertexP denI i))) x
  set NM2 := evalR (detP (psub B' A') (psub A' (vertexP denI i))) x
  set DD2 := evalR (detP (psub B' A') (psub (vertexP denI (i + 1)) (vertexP denI i))) x
  have hsum1 : 1 ≤ NM1 / DD1 + NM2 / DD2 := by
    rw [div_add_div _ _ hdd1.ne' hdd2.ne', le_div_iff₀ (mul_pos hdd1 hdd2)]
    linarith
  have := C.side_lt
  linarith

theorem ordinaryCheck_sound (C : Ctx U den x Ps caps ord) {denI : Int}
    (hden : (denI : ℝ) = den) (hdpos : 0 < denI) {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : ordinaryCheck Ps denI ord a b d fuel = true) (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) : False := by
  match hord : ord with
  | none => simp [ordinaryCheck] at h
  | some i =>
    exact ordinaryExclusion_sound C hden hdpos rfl hd (by simpa [ordinaryCheck] using h)
      hx hlo hhi

/-! ## The exclusion decision -/

theorem excluded_sound {denI : Int} (hden : (denI : ℝ) = den) (hdpos : 0 < denI) {fuel : Nat}
    (depth : Nat) :
    ∀ (a b d : Int), 0 < d → excluded Ps denI caps ord fuel depth a b d = true →
      0 < x → (a : ℝ) / d ≤ x → x ≤ (b : ℝ) / d → Ctx U den x Ps caps ord → False := by
  induction depth with
  | zero =>
    intro a b d hd h hx hlo hhi C
    unfold excluded at h
    simp only [Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · exact ordinaryCheck_sound C hden hdpos hd h hx hlo hhi
    · exact diamCheck_sound C hden hdpos hd h hlo hhi
    · exact fanCheck_sound C hden hdpos hd h hx hlo hhi
    · simp at h
  | succ depth ih =>
    intro a b d hd h hx hlo hhi C
    unfold excluded at h
    simp only [Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · exact ordinaryCheck_sound C hden hdpos hd h hx hlo hhi
    · exact diamCheck_sound C hden hdpos hd h hlo hhi
    · exact fanCheck_sound C hden hdpos hd h hx hlo hhi
    · obtain ⟨a', b', d', hd', hf, hlo', hhi'⟩ :=
        chainCheck_sound _ (b, d) hd x hhi _ (a, d) hd h hlo
      exact ih a' b' d' hd' hf hx hlo' hhi' C

end

end ConwaySoifer.Certificates

namespace ConwaySoifer.Certificates
open IPoly

noncomputable section

/-! ## Replay of a forced-point trace -/

/-- Semantic content of a replay state for a configuration `T` at parameter `x`. -/
structure ModelHolds (M : Model) (T : Configuration) (den x : ℝ) : Prop where
  side_pos : ∀ j, 0 < (T j).side
  side_lt : ∀ j, (T j).side < 1
  covers : Covers T
  mem : ∀ j, ∀ P ∈ M.B j, realPt den P x ∈ (T j).carrier
  cap : ∀ j, ∀ c ∈ M.caps j, ∀ O : Orientation (T j), ∃ k : Fin 3, FaceOK (T j) den x (rotPow k
      O.dir) c
  ord : ∀ j i, M.ord j = some i → vertex i ∈ (T j).carrier ∧
    rayLen (T j) (vertex i) (sideDirection i false) + rayLen (T j) (vertex i) (sideDirection i true)
        ≤
      (T j).side

theorem ModelHolds.ctx {M : Model} {T : Configuration} {den x : ℝ} (H : ModelHolds M T den x)
    (j : Fin 10) : Ctx (T j) den x (M.B j) (M.caps j) (M.ord j) :=
  ⟨H.side_pos j, H.side_lt j, H.mem j, H.cap j, H.ord j⟩

theorem inTarget_sound {q : IPoint} {denI : Int} {den : ℝ} (hden : (denI : ℝ) = den)
    (hdpos : 0 < denI) {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : inTarget q denI a b d fuel = true) {x : ℝ} (hlo : (a : ℝ) / d ≤ x)
    (hhi : x ≤ (b : ℝ) / d) : realPt den q x ∈ target := by
  unfold inTarget at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have e1 := nonnegOn_sound _ a b d fuel h1 hd x hlo hhi
  have e2 := nonnegOn_sound _ a b d fuel h2 hd x hlo hhi
  have e3 := nonnegOn_sound _ a b d fuel h3 hd x hlo hhi
  simp only [evalR_sub, evalR_add, evalR_cons, evalR_nil, mul_zero, add_zero] at e1 e2 e3
  have hdenR : (0 : ℝ) < den := by
    rw [← hden]; exact_mod_cast hdpos
  simp only [realPt, evalF, target, Set.mem_ofPred_eq, Prod.smul_mk, smul_eq_mul]
  rw [hden] at e1 e2 e3
  refine ⟨?_, ?_, ?_⟩
  · rw [inv_mul_le_iff₀ hdenR]; linarith
  · rw [inv_mul_le_iff₀ hdenR]; linarith
  · rw [← mul_add, le_inv_mul_iff₀ hdenR]; linarith

theorem mem_thinHullChecked {L : List IPoint} {P : IPoint} (h : P ∈ thinHullChecked L) : P ∈ L := by
  unfold thinHullChecked at h
  simp only [List.mem_filter, decide_eq_true_eq] at h
  exact h.2

theorem stepCheck_sound {M : Model} {T : Configuration} {den x : ℝ} {denI : Int}
    (hden : (denI : ℝ) = den) (hdpos : 0 < denI) {st : Step} {a b d : Int} (hd : 0 < d)
    {fuel depth : Nat} (h : stepCheck M denI st a b d fuel depth = true) (hx : 0 < x)
    (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d) (H : ModelHolds M T den x) :
    ModelHolds (M.insert st) T den x := by
  unfold stepCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hin, hall⟩ := h
  have hq : realPt den st.q x ∈ (T st.owner).carrier := by
    obtain ⟨j, hj⟩ := H.covers _ (inTarget_sound hden hdpos hd hin hlo hhi)
    rcases hall j with hj' | hex
    · rw [← hj']; exact hj
    · exfalso
      refine excluded_sound (U := T j) hden hdpos depth a b d hd hex hx hlo hhi ?_
      refine ⟨H.side_pos j, H.side_lt j, ?_, H.cap j, H.ord j⟩
      intro P hP
      rcases List.mem_append.mp hP with hP | hP
      · exact H.mem j P hP
      · rw [List.mem_singleton] at hP; subst hP; exact hj
  refine ⟨H.side_pos, H.side_lt, H.covers, ?_, H.cap, H.ord⟩
  intro j P hP
  simp only [Model.insert] at hP
  split_ifs at hP with hj
  · subst hj
    rcases List.mem_append.mp (mem_thinHullChecked hP) with hP | hP
    · exact H.mem _ P hP
    · rw [List.mem_singleton] at hP; subst hP; exact hq
  · exact H.mem j P hP

theorem replay_sound {T : Configuration} {den x : ℝ} {denI : Int} (hden : (denI : ℝ) = den)
    (hdpos : 0 < denI) {a b d : Int} (hd : 0 < d) {fuel depth : Nat} (hx : 0 < x)
    (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d) (steps : List Step) :
    ∀ (M : Model) (last : Fin 10), replay M denI a b d fuel depth steps last = true →
      ModelHolds M T den x → False := by
  induction steps with
  | nil =>
    intro M last h H
    unfold replay at h
    exact excluded_sound hden hdpos depth a b d hd h hx hlo hhi (H.ctx last)
  | cons st rest ih =>
    intro M last h H
    unfold replay at h
    rw [Bool.and_eq_true] at h
    exact ih _ last h.2 (stepCheck_sound hden hdpos hd h.1 hx hlo hhi H)

/-- The complete certificate: for every parameter `s ∈ (lo, hi]` and every configuration whose
initial model holds at `x = s - lo`, contradiction. -/
theorem CertData.check_sound (C : CertData) {fuel depth : Nat} (h : C.check fuel depth = true) :
    0 < C.den ∧ 0 ≤ C.lo ∧ C.lo < C.hi ∧ C.hi ≤ 11 / 25 ∧
      ∃ M, initModel C.case C.lo C.hi C.den = some M ∧
        ∀ (T : Configuration) (x : ℝ), 0 < x → x ≤ ((C.hi - C.lo : Rat) : ℝ) →
          ModelHolds M T (C.den : ℝ) x → False := by
  unfold CertData.check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hden, hlo⟩, hlt⟩, hhi⟩, h⟩ := h
  refine ⟨hden, hlo, hlt, hhi, ?_⟩
  split at h
  · simp at h
  · next M hM =>
    refine ⟨M, hM, ?_⟩
    intro T x hx hxw H
    have hw : 0 < C.hi - C.lo := sub_pos.mpr hlt
    have hwd : 0 < ((C.hi - C.lo).den : Int) := by
      exact_mod_cast (C.hi - C.lo).den_pos
    have hcast : (((C.hi - C.lo).num : Int) : ℝ) / (((C.hi - C.lo).den : Int) : ℝ) =
        ((C.hi - C.lo : Rat) : ℝ) := by
      rw [Rat.cast_def]; push_cast; rfl
    refine replay_sound rfl hden hwd hx ?_ ?_ C.steps M C.last h H
    · simp only [Int.cast_zero, zero_div]; exact hx.le
    · rw [hcast]; exact hxw

end

end ConwaySoifer.Certificates
