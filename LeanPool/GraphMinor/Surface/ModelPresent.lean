/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ModelSides
import LeanPool.GraphMinor.Surface.WordTrack

/-!
# The model surfaces are presented by their words

`presents_model` shows that the two discs of `modelW` map onto $\Sigma(a, b, c)$, and that two
points have the same
image exactly when they are related by the pasting of sides.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

open scoped OnePoint

theorem pw_length (a k : ℕ) : (pw a k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [pw, ih]
    omega

theorem qw_length (a b k : ℕ) : (qw a b k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [qw, ih]
    omega

theorem pw_even (a k j : ℕ) (h : j < k) : (pw a k)[2 * j]? = some (segL j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [pw]
    by_cases hj : j < k
    · rw [List.getElem?_append_left (by rw [pw_length]; omega), ih hj]
    · obtain rfl : j = k := by omega
      rw [List.getElem?_append_right (by rw [pw_length]), pw_length]
      simp

theorem pw_odd (a k j : ℕ) (h : j < k) : (pw a k)[2 * j + 1]? = some (holeA a j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [pw]
    by_cases hj : j < k
    · rw [List.getElem?_append_left (by rw [pw_length]; omega), ih hj]
    · obtain rfl : j = k := by omega
      rw [List.getElem?_append_right (by rw [pw_length]; omega), pw_length]
      simp

theorem qw_even (a b k j : ℕ) (h : j < k) : (qw a b k)[2 * j]? = some (segL j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [qw]
    by_cases hj : j < k
    · rw [List.getElem?_append_left (by rw [qw_length]; omega), ih hj]
    · obtain rfl : j = k := by omega
      rw [List.getElem?_append_right (by rw [qw_length]), qw_length]
      simp

theorem qw_odd (a b k j : ℕ) (h : j < k) : (qw a b k)[2 * j + 1]? = some (holeB a b j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [qw]
    by_cases hj : j < k
    · rw [List.getElem?_append_left (by rw [qw_length]; omega), ih hj]
    · obtain rfl : j = k := by omega
      rw [List.getElem?_append_right (by rw [qw_length]; omega), qw_length]
      simp

section

variable {a b n : ℕ}

theorem modelW_zero : modelW a b n 0 = pw a n ++ [segL n, zL] := by
  simp [modelW, dW, sW, Function.update]

theorem modelW_one : modelW a b n 1 = qw a b n ++ [segL n, zL] := by simp [modelW, dW]

theorem modelW_other {i : ℕ} (h0 : i ≠ 0) (h1 : i ≠ 1) : modelW a b n i = [] := by
  simp [modelW, dW, sW, Function.update_of_ne h0, Function.update_of_ne h1, nW]

theorem modelW_len {i : ℕ} (h : i ≤ 1) : (modelW a b n i).length = 2 * n + 2 := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · simp [modelW_zero, pw_length]
  · simp [modelW_one, qw_length]

theorem modelW_slot {i : ℕ} (h : modelW a b n i ≠ []) : i ≤ 1 := by
  by_contra h'
  exact h (modelW_other (by omega) (by omega))

theorem modelW_seg {i k : ℕ} (hi : i ≤ 1) (hk : k ≤ n) : (modelW a b n i)[2 * k]? = some (segL k)
  := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · rw [modelW_zero]
    rcases Nat.lt_or_ge k n with h | h
    · rw [List.getElem?_append_left (by rw [pw_length]; omega), pw_even a n k h]
    · obtain rfl : k = n := by omega
      rw [List.getElem?_append_right (by rw [pw_length]), pw_length]
      simp
  · rw [modelW_one]
    rcases Nat.lt_or_ge k n with h | h
    · rw [List.getElem?_append_left (by rw [qw_length]; omega), qw_even a b n k h]
    · obtain rfl : k = n := by omega
      rw [List.getElem?_append_right (by rw [qw_length]), qw_length]
      simp

theorem modelW_top {i : ℕ} (hi : i ≤ 1) : (modelW a b n i)[2 * n + 1]? = some zL := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · rw [modelW_zero, List.getElem?_append_right (by rw [pw_length]; omega), pw_length]
    simp
  · rw [modelW_one, List.getElem?_append_right (by rw [qw_length]; omega), qw_length]
    simp

theorem modelW_holeA {k : ℕ} (hk : k < n) : (modelW a b n 0)[2 * k + 1]? = some (holeA a k) := by
  rw [modelW_zero, List.getElem?_append_left (by rw [pw_length]; omega), pw_odd a n k hk]

theorem modelW_holeB {k : ℕ} (hk : k < n) : (modelW a b n 1)[2 * k + 1]? = some (holeB a b k) := by
  rw [modelW_one, List.getElem?_append_left (by rw [qw_length]; omega), qw_odd a b n k hk]

/-- Each position is on the axis or on a circle. -/
theorem modelW_cases {i p : ℕ} {l : Letter} (hi : i ≤ 1) (h : (modelW a b n i)[p]? = some l) :
    (∃ k, k ≤ n ∧ p = 2 * k ∧ l = segL k) ∨ (p = 2 * n + 1 ∧ l = zL) ∨
      (∃ k, k < n ∧ p = 2 * k + 1 ∧ ((i = 0 ∧ l = holeA a k) ∨ (i = 1 ∧ l = holeB a b k))) := by
  have hp : p < 2 * n + 2 := by
    have := (List.getElem?_eq_some_iff.mp h).1
    rwa [modelW_len hi] at this
  rcases Nat.even_or_odd' p with ⟨k, rfl | rfl⟩
  · refine .inl ⟨k, by omega, rfl, ?_⟩
    rw [modelW_seg hi (by omega)] at h
    exact (Option.some.inj h).symm
  · by_cases hk : k < n
    · refine .inr (.inr ⟨k, hk, rfl, ?_⟩)
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · rw [modelW_holeA hk] at h
        exact .inl ⟨rfl, (Option.some.inj h).symm⟩
      · rw [modelW_holeB hk] at h
        exact .inr ⟨rfl, (Option.some.inj h).symm⟩
    · obtain rfl : k = n := by omega
      rw [modelW_top hi] at h
      exact .inr (.inl ⟨rfl, (Option.some.inj h).symm⟩)

end

/-- The base with a default point. -/
noncomputable def retB (n : ℕ) (x : OnePoint EuclideanPlane) : modelBase n :=
  open Classical in if h : x ∈ modelBase n then ⟨x, h⟩ else ⟨∞, fun _i _ _u he => absurd he
    (OnePoint.infty_ne_coe _)⟩

theorem retB_val {n : ℕ} {x : OnePoint EuclideanPlane} (h : x ∈ modelBase n) : (retB n x).1 = x
  := by
  simp [retB, h]

theorem continuousOn_retB (n : ℕ) : ContinuousOn (retB n) (modelBase n) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_induced_rng.mpr ?_
  have : (Subtype.val ∘ (modelBase n).domRestrict (retB n)) = Subtype.val := by
    funext x
    exact retB_val x.2
  rw [this]
  exact continuous_subtype_val

theorem mem_modelBase_coe {n : ℕ} {u : EuclideanPlane} :
    (u : OnePoint EuclideanPlane) ∈ modelBase n ↔ ∀ i < n, 1 ≤ dist u (modelCentre i) := by
  constructor
  · intro h i hi
    exact h i hi u rfl
  · intro h i hi x he
    rw [← OnePoint.coe_injective he]
    exact h i hi

theorem mem_modelBase_pt {n : ℕ} {x y : ℝ} :
    ((pt x y : EuclideanPlane) : OnePoint EuclideanPlane) ∈ modelBase n ↔
      ∀ i < n, 1 ≤ (x - 3 * i) ^ 2 + y ^ 2 := by
  rw [mem_modelBase_coe]
  refine forall₂_congr fun i _ => ?_
  rw [modelCentre_eq]
  have h := dist_pt_sq x y (3 * i) 0
  rw [sub_zero] at h
  rw [← h]
  exact (one_le_sq_iff₀ dist_nonneg).symm

theorem mirO_base {n : ℕ} {p : OnePoint EuclideanPlane} (h : p ∈ modelBase n) : mirO p ∈ modelBase
  n := by
  induction p using OnePoint.rec with
  | infty => exact h
  | coe u =>
    rw [mirO_coe]
    rw [← pt_ext u, mem_modelBase_pt] at h
    have e : modelMirror u = pt (u 0) (-(u 1)) := rfl
    rw [e, mem_modelBase_pt]
    simpa using h

/-- Points above the graph of the height lie in the base. -/
theorem pt_above_base {n : ℕ} {x y : ℝ} (h : hgt n x ≤ y) :
    ((pt x y : EuclideanPlane) : OnePoint EuclideanPlane) ∈ modelBase n := by
  rw [mem_modelBase_pt]
  intro i hi
  have h1 := hgt_ge n x hi
  have h2 := hgt_nonneg n x
  by_contra hcon
  push Not at hcon
  have h3 : 0 < 1 - (x - 3 * i) ^ 2 := by nlinarith [sq_nonneg y]
  have h4 := Real.sq_sqrt h3.le
  nlinarith [Real.sqrt_nonneg (1 - (x - 3 * i) ^ 2)]

theorem upE_base {n : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1) : upE n z ∈ modelBase n := by
  by_cases h : z = 1
  · subst h
    rw [upE_one]
    exact fun i _ u he => absurd he (OnePoint.infty_ne_coe _)
  · rw [upE_ne h]
    exact pt_above_base (upE_above hz h)

/-- Points in the base above the axis lie above the graph of the height. -/
theorem hgt_le_of_base {n : ℕ} {x y : ℝ} (h : ((pt x y : EuclideanPlane) : OnePoint EuclideanPlane)
  ∈ modelBase n)
    (hy : 0 ≤ y) : hgt n x ≤ y := by
  rw [mem_modelBase_pt] at h
  by_cases hc : ∃ i < n, |x - 3 * i| ≤ 1
  · obtain ⟨i, hi, h1⟩ := hc
    rw [hgt_eq hi h1]
    refine Real.sqrt_le_iff.mpr ⟨hy, ?_⟩
    have := h i hi
    linarith
  · push Not at hc
    rw [hgt_eq_zero fun i hi => (hc i hi).le]
    exact hy

section poly

variable {n : ℕ} {Φ Φ' : ℂ → ℂ}

/-- The map of the two discs to the sphere with holes. -/
noncomputable def Fv (n : ℕ) (Φ : ℂ → ℂ) (a : ℕ × ℂ) : OnePoint EuclideanPlane :=
  if a.1 = 0 then upE n (Φ a.2) else mirO (upE n (Φ a.2))

theorem Fv_zero (z : ℂ) : Fv n Φ (0, z) = upE n (Φ z) := by simp [Fv]

theorem Fv_one (z : ℂ) : Fv n Φ (1, z) = mirO (upE n (Φ z)) := by simp [Fv]

theorem Fv_base (hm : BdMatch (closedBall 0 1) (closedBall 0 1) Φ Φ') {a : ℕ × ℂ} (ha : ‖a.2‖ ≤ 1) :
    Fv n Φ a ∈ modelBase n := by
  have h1 : Φ a.2 ∈ closedBall (0 : ℂ) 1 := hm.1 (mem_closedBall_zero_iff.mpr ha)
  have h2 : ‖Φ a.2‖ ≤ 1 := mem_closedBall_zero_iff.mp h1
  unfold Fv
  split_ifs
  · exact upE_base h2
  · exact mirO_base (upE_base h2)

theorem continuousOn_Fv (hm : BdMatch (closedBall 0 1) (closedBall 0 1) Φ Φ') {W : ℕ
  → List Letter} :
    ContinuousOn (Fv n Φ) (Dsk W) := by
  rw [continuousOn_prod_of_discrete_left]
  intro s
  have hmp : MapsTo Φ {z | (s, z) ∈ Dsk W} (closedBall 0 1) := fun z hz =>
    hm.1 (mem_closedBall_zero_iff.mpr hz.2)
  have hc : ContinuousOn Φ {z | (s, z) ∈ Dsk W} :=
    hm.2.2.2.2.1.mono fun z hz => mem_closedBall_zero_iff.mpr hz.2
  have h1 := (continuousOn_upE n).comp hc hmp
  by_cases hs : s = 0
  · subst hs
    simpa [Fv, Function.comp_def] using h1
  · have := mirO.continuous.comp_continuousOn h1
    simpa [Fv, hs, Function.comp_def] using this

theorem hole_AA {a k k' : ℕ} (h : (holeA a k).1 = (holeA a k').1) : k = k' := by
  simp only [holeA] at h
  split_ifs at h <;> simp at h <;> omega

theorem hole_BB {a b k k' : ℕ} (h : (holeB a b k).1 = (holeB a b k').1) : k = k' := by
  simp only [holeB] at h
  split_ifs at h <;> simp at h <;> omega

theorem hole_AB {a b k k' : ℕ} (h : (holeA a k).1 = (holeB a b k').1) :
    (k % 2 = 0 ∧ k + 1 < 2 * a ∧ k' = k + 1) ∨ (k % 2 = 1 ∧ k < 2 * a ∧ k' + 1 = k) ∨
      (2 * a ≤ k ∧ k < 2 * a + b ∧ k' = k) := by
  simp only [holeA, holeB] at h
  split_ifs at h <;> simp at h <;> omega

theorem holeA_sign (a k : ℕ) : (holeA a k).2 = true := by
  simp only [holeA]
  split_ifs <;> rfl

theorem holeB_sign {a b k : ℕ} (h : ¬ (2 * a ≤ k ∧ k < 2 * a + b)) : (holeB a b k).2 = true := by
  simp only [holeB]
  split_ifs <;> first | rfl | omega

theorem holeB_sign' {a b k : ℕ} (h : 2 * a ≤ k ∧ k < 2 * a + b) : (holeB a b k).2 = false := by
  simp only [holeB]
  rw [ite_eq_right (by omega), ite_eq_left h.2]

theorem hole_ne_seg_A {a k j : ℕ} : (holeA a k).1 ≠ (segL j).1 := by
  simp only [holeA, segL]
  split_ifs <;> simp <;> omega

theorem hole_ne_seg_B {a b k j : ℕ} : (holeB a b k).1 ≠ (segL j).1 := by
  simp only [holeB, segL]
  split_ifs <;> simp <;> omega

theorem hole_ne_z_A {a k : ℕ} : (holeA a k).1 ≠ zL.1 := by
  simp only [holeA, zL]
  split_ifs <;> simp; omega

theorem hole_ne_z_B {a b k : ℕ} : (holeB a b k).1 ≠ zL.1 := by
  simp only [holeB, zL]
  split_ifs <;> simp <;> omega

theorem seg_ne_z {j : ℕ} : (segL j).1 ≠ zL.1 := by
  simp only [segL, zL]
  omega

theorem modelMirror_add (i : ℕ) (u : EuclideanPlane) :
    modelMirror (modelCentre i + u) = modelCentre i + modelMirror u := by
  ext j
  fin_cases j <;> simp [modelMirror, modelCentre_eq]

variable {a b : ℕ}

/-- The hypotheses on the polygon map. -/
def IsPoly (n : ℕ) (Φ Φ' : ℂ → ℂ) : Prop :=
  BdMatch (closedBall 0 1) (closedBall 0 1) Φ Φ' ∧
    ∀ x ∈ Icc (0 : ℝ) (2 * n + 2 : ℕ), Φ (per (2 * n + 2) x) = cis' (angL n x)

theorem sdPt_false (m p : ℕ) (t : ℝ) : sdPt m p false t = per m (p + (1 - t)) := by simp [sdPt]

theorem side_mem {n k : ℕ} (hk : k < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (2 * (k : ℝ) + 1 + t) ∈ Icc (0 : ℝ) (2 * n + 2 : ℕ) := by
  have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- The value on the circle `k` of the upper disc. -/
theorem Fv_hole0 (hΦ : IsPoly n Φ Φ') {k : ℕ} (hk : k < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Fv n Φ (0, per (2 * n + 2) (2 * k + 1 + t)) =
      ((modelCentre k + pt (axPhi t) (axPsi t) : EuclideanPlane) : OnePoint EuclideanPlane) := by
  rw [Fv_zero, hΦ.2 _ (side_mem hk ht), upE_hole hk ht]

/-- The value on the circle `k` of the lower disc. -/
theorem Fv_hole1 (hΦ : IsPoly n Φ Φ') {k : ℕ} (hk : k < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Fv n Φ (1, per (2 * n + 2) (2 * k + 1 + t)) =
      ((modelCentre k + modelMirror (pt (axPhi t) (axPsi t)) : EuclideanPlane) : OnePoint
        EuclideanPlane) := by
  rw [Fv_one, hΦ.2 _ (side_mem hk ht), upE_hole hk ht, mirO_coe, modelMirror_add]

/-- The sides on the axis have equal values in both discs. -/
theorem Fv_ax (hΦ : IsPoly n Φ Φ') {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (2 * n + 2 : ℕ))
    (h : IsAx n (upE n (cis' (angL n y)))) :
    Fv n Φ (0, per (2 * n + 2) y) = Fv n Φ (1, per (2 * n + 2) y) := by
  rw [Fv_zero, Fv_one, hΦ.2 _ hy, h.mirO]

theorem isAx_pos {n : ℕ} {p : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (h : (∃ k, k ≤ n ∧ p = 2 * k) ∨ p = 2 * n + 1) :
    ((p : ℝ) + t) ∈ Icc (0 : ℝ) (2 * n + 2 : ℕ) ∧ IsAx n (upE n (cis' (angL n (p + t)))) := by
  have hmem : ((p : ℝ) + t) ∈ Icc (0 : ℝ) (2 * n + 2 : ℕ) := by
    have h1 : (p : ℝ) + 1 ≤ 2 * n + 2 := by
      have : p + 1 ≤ 2 * n + 2 := by omega
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    push_cast
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨hmem, ?_⟩
  rcases h with ⟨k, hk, rfl⟩ | rfl
  · rcases Nat.lt_or_ge k n with h | h
    · have := isAx_seg h ht
      simpa using this
    · obtain rfl : k = n := by omega
      refine isAx_top ?_ hmem.2
      push_cast
      linarith [ht.1]
  · refine isAx_top ?_ hmem.2
    push_cast
    linarith [ht.1]

section glue

variable (a b)

/-- Two points of the sphere with holes that are glued in the model. -/
def Gl (n : ℕ) (x y : OnePoint EuclideanPlane) : Prop :=
  ∀ p q : modelBase n, p.1 = x → q.1 = y → Relation.EqvGen (ModelGlue a b n) p q

variable {a b}

theorem Gl.of_eq {n : ℕ} {x y : OnePoint EuclideanPlane} (h : x = y) : Gl a b n x y
  := fun p q hp hq => by
  have : p = q := Subtype.ext (by rw [hp, hq, h])
  rw [this]
  exact .refl _

theorem Gl.symm {n : ℕ} {x y : OnePoint EuclideanPlane} (h : Gl a b n x y) : Gl a b n y x
  := fun p q hp hq =>
  (h q p hq hp).symm

theorem norm_axU {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖pt (axPhi t) (axPsi t)‖ = 1 := by
  have h := norm_pt_sq (axPhi t) (axPsi t)
  rw [axPsi_sq ht] at h
  have h2 : ‖pt (axPhi t) (axPsi t)‖ ^ 2 = 1 := by rw [h]; ring
  have := norm_nonneg (pt (axPhi t) (axPsi t))
  nlinarith

theorem norm_mirror (u : EuclideanPlane) : ‖modelMirror u‖ = ‖u‖ := by
  have h1 := norm_pt_sq (u 0) (u 1)
  have h2 := norm_pt_sq (u 0) (-(u 1))
  rw [pt_ext] at h1
  have e : pt (u 0) (-(u 1)) = modelMirror u := rfl
  rw [e] at h2
  have h3 : ‖modelMirror u‖ ^ 2 = ‖u‖ ^ 2 := by rw [h1, h2]; ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3

/-- The glued pairs of a handle. -/
theorem gl_handle {n : ℕ} {h : ℕ} (hh : h < a) {u : EuclideanPlane} (hu : ‖u‖ = 1) :
    Gl a b n ((modelCentre (2 * h) + u : EuclideanPlane) : OnePoint EuclideanPlane)
      ((modelCentre (2 * h + 1) + modelMirror u : EuclideanPlane) : OnePoint EuclideanPlane) :=
  fun p q hp hq => .rel _ _ (.handle h hh u hu p q hp hq)

/-- The glued pairs of a cross-cap. -/
theorem gl_cap {n : ℕ} {i : ℕ} (hi : i < b) {u : EuclideanPlane} (hu : ‖u‖ = 1) :
    Gl a b n ((modelCentre (2 * a + i) + u : EuclideanPlane) : OnePoint EuclideanPlane)
      ((modelCentre (2 * a + i) - u : EuclideanPlane) : OnePoint EuclideanPlane) :=
  fun p q hp hq => .rel _ _ (.crosscap i hi u hu p q hp hq)

theorem axU_neg (t : ℝ) : pt (axPhi (1 - t)) (axPsi (1 - t)) = - modelMirror (pt (axPhi t)
  (axPsi t)) := by
  rw [axPhi_neg, axPsi_neg]
  ext j
  fin_cases j <;> simp [modelMirror]

/-- Sides of the two discs on circles with the same label are glued. -/
theorem gl_holes (hΦ : IsPoly n Φ Φ') {k k' : ℕ} (hk : k < n) (hk' : k' < n)
    (hl : (holeA a k).1 = (holeB a b k').1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {ε' : Bool}
    (hs : ε' = (holeB a b k').2) :
    Gl a b n (Fv n Φ (0, sdPt (2 * n + 2) (2 * k + 1) true t))
      (Fv n Φ (1, sdPt (2 * n + 2) (2 * k' + 1) ε' t)) := by
  have e0 : sdPt (2 * n + 2) (2 * k + 1) true t = per (2 * n + 2) (2 * k + 1 + t) := by
    rw [sdPt_true]
    push_cast
    rfl
  rw [e0]
  rcases hole_AB hl with ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩
  · rw [holeB_sign (by omega)] at hs
    subst hs
    have e1 : sdPt (2 * n + 2) (2 * (k + 1) + 1) true t = per (2 * n + 2) (2 * (k + 1 : ℕ) + 1 + t)
      := by
      rw [sdPt_true]
      push_cast
      rfl
    rw [e1, Fv_hole0 hΦ hk ht, Fv_hole1 hΦ hk' ht]
    obtain ⟨h, rfl⟩ : ∃ h, k = 2 * h := ⟨k / 2, by omega⟩
    exact gl_handle (by omega) (norm_axU ht)
  · rw [holeB_sign (by omega)] at hs
    subst hs
    have e1 : sdPt (2 * n + 2) (2 * k' + 1) true t = per (2 * n + 2) (2 * k' + 1 + t) := by
      rw [sdPt_true]
      push_cast
      rfl
    rw [e1, Fv_hole0 hΦ hk ht, Fv_hole1 hΦ hk' ht]
    obtain ⟨h, rfl⟩ : ∃ h, k' = 2 * h := ⟨k' / 2, by omega⟩
    have := gl_handle (a := a) (b := b) (n := n) (h := h) (by omega) (u := modelMirror (pt
      (axPhi t) (axPsi t)))
      (by rw [norm_mirror]; exact norm_axU ht)
    rw [modelMirror_mirror] at this
    exact this.symm
  · rw [holeB_sign' ⟨h1, h2⟩] at hs
    subst hs
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have e1 : sdPt (2 * n + 2) (2 * k' + 1) false t = per (2 * n + 2) (2 * k' + 1 + (1 - t)) := by
      rw [sdPt_false]
      push_cast
      rfl
    rw [e1, Fv_hole0 hΦ hk' ht, Fv_hole1 hΦ hk' ht', axU_neg, ]
    obtain ⟨i, rfl⟩ : ∃ i, k' = 2 * a + i := ⟨k' - 2 * a, by omega⟩
    have := gl_cap (a := a) (b := b) (n := n) (i := i) (by omega) (norm_axU ht)
    have e2 : modelMirror (-modelMirror (pt (axPhi t) (axPsi t))) = - pt (axPhi t) (axPsi t) := by
      ext j
      fin_cases j <;> simp [modelMirror]
    rw [e2, ← sub_eq_add_neg]
    exact this

end glue

theorem sdPt_hole (n k : ℕ) (t : ℝ) :
    sdPt (2 * n + 2) (2 * k + 1) true t = per (2 * n + 2) (2 * k + 1 + t) := by
  rw [sdPt_true]
  push_cast
  rfl

theorem sdPt_hole' (n k : ℕ) (t : ℝ) :
    sdPt (2 * n + 2) (2 * k + 1) false t = per (2 * n + 2) (2 * k + 1 + (1 - t)) := by
  rw [sdPt_false]
  push_cast
  rfl

/-- Points on sides with the same label in the two discs are one step apart. -/
theorem stp_holes {n k k' : ℕ} (hk : k < n) (hk' : k' < n) (hl : (holeA a k).1 =
  (holeB a b k').1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Stp (modelW a b n) (0, sdPt (2 * n + 2) (2 * k + 1) true t)
      (1, sdPt (2 * n + 2) (2 * k' + 1) (holeB a b k').2 t) := by
  refine ⟨0, 1, 2 * k + 1, 2 * k' + 1, (holeA a k).1, true, (holeB a b k').2, t, ?_, ?_, by simp,
    ht, ?_, ?_⟩
  · rw [modelW_holeA hk]
    exact congrArg some (Prod.ext rfl (holeA_sign a k))
  · rw [modelW_holeB hk', hl]
  · rw [modelW_len (by omega)]
  · rw [modelW_len (by omega)]

/-- Points with the same parameter on a side on the axis are one step apart. -/
theorem stp_ax {n p : ℕ} (h : (∃ k, k ≤ n ∧ p = 2 * k) ∨ p = 2 * n + 1) {t : ℝ} (ht : t ∈ Icc
  (0 : ℝ) 1) :
    Stp (modelW a b n) (0, per (2 * n + 2) (p + t)) (1, per (2 * n + 2) (p + t)) := by
  have hl : ∃ m, ∀ i ≤ 1, (modelW a b n i)[p]? = some (m, true) := by
    rcases h with ⟨k, hk, rfl⟩ | rfl
    · exact ⟨_, fun i hi => modelW_seg hi hk⟩
    · exact ⟨_, fun i hi => modelW_top hi⟩
  obtain ⟨m, hm⟩ := hl
  refine ⟨0, 1, p, p, m, true, true, t, hm 0 (by omega), hm 1 le_rfl, by simp, ht, ?_, ?_⟩
  · rw [modelW_len (by omega), sdPt_true]
  · rw [modelW_len (by omega), sdPt_true]

theorem Fv_ax_eq (hΦ : IsPoly n Φ Φ') {p : ℕ} (h : (∃ k, k ≤ n ∧ p = 2 * k) ∨ p = 2 * n + 1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {i j : ℕ} (hi : i ≤ 1) (hj : j ≤ 1) :
    Fv n Φ (i, sdPt (2 * n + 2) p true t) = Fv n Φ (j, sdPt (2 * n + 2) p true t) := by
  obtain ⟨h1, h2⟩ := isAx_pos ht h
  have e := Fv_ax hΦ h1 h2
  rw [sdPt_true]
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · rfl
    · exact e
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · exact e.symm
    · rfl

theorem fst_of {m : ℕ} {ε : Bool} {l : Letter} (h : ((m, ε) : Letter) = l) : m = l.1
  := congrArg Prod.fst h

theorem snd_of {m : ℕ} {ε : Bool} {l : Letter} (h : ((m, ε) : Letter) = l) : ε = l.2
  := congrArg Prod.snd h

/-- Steps go to points that are glued. -/
theorem Fv_stp (hΦ : IsPoly n Φ Φ') {x y : ℕ × ℂ} (h : Stp (modelW a b n) x y) :
    Gl a b n (Fv n Φ x) (Fv n Φ y) := by
  obtain ⟨i, j, p, q, l, ε, ε', t, h1, h2, hne, ht, rfl, rfl⟩ := h
  have hi : i ≤ 1 := modelW_slot fun he => by rw [he] at h1; exact absurd h1 (by simp)
  have hj : j ≤ 1 := modelW_slot fun he => by rw [he] at h2; exact absurd h2 (by simp)
  rw [modelW_len hi, modelW_len hj]
  rcases modelW_cases hi h1 with ⟨k, hk, rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨k, hk, rfl, hl⟩ <;>
    rcases modelW_cases hj h2 with ⟨k', hk', rfl, hl'⟩ | ⟨rfl, hl'⟩ | ⟨k', hk', rfl, hl'⟩
  · have e : k = k' := by
      have := (fst_of hl).symm.trans (fst_of hl')
      simpa [segL] using this
    subst e
    obtain rfl : ε = true := snd_of hl
    obtain rfl : ε' = true := snd_of hl'
    exact Gl.of_eq (Fv_ax_eq hΦ (.inl ⟨k, hk, rfl⟩) ht hi hj)
  · exact absurd ((fst_of hl).symm.trans (fst_of hl')) seg_ne_z
  · exfalso
    have e0 := fst_of hl
    rcases hl' with ⟨-, hl'⟩ | ⟨-, hl'⟩
    · exact hole_ne_seg_A ((fst_of hl').symm.trans e0)
    · exact hole_ne_seg_B ((fst_of hl').symm.trans e0)
  · exact absurd ((fst_of hl').symm.trans (fst_of hl)) seg_ne_z
  · obtain rfl : ε = true := snd_of hl
    obtain rfl : ε' = true := snd_of hl'
    exact Gl.of_eq (Fv_ax_eq hΦ (.inr rfl) ht hi hj)
  · exfalso
    have e0 := fst_of hl
    rcases hl' with ⟨-, hl'⟩ | ⟨-, hl'⟩
    · exact hole_ne_z_A ((fst_of hl').symm.trans e0)
    · exact hole_ne_z_B ((fst_of hl').symm.trans e0)
  · exfalso
    have e0 := fst_of hl'
    rcases hl with ⟨-, hl⟩ | ⟨-, hl⟩
    · exact hole_ne_seg_A ((fst_of hl).symm.trans e0)
    · exact hole_ne_seg_B ((fst_of hl).symm.trans e0)
  · exfalso
    have e0 := fst_of hl'
    rcases hl with ⟨-, hl⟩ | ⟨-, hl⟩
    · exact hole_ne_z_A ((fst_of hl).symm.trans e0)
    · exact hole_ne_z_B ((fst_of hl).symm.trans e0)
  · rcases hl with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ <;> rcases hl' with ⟨rfl, hl'⟩ | ⟨rfl, hl'⟩
    · obtain rfl : k = k' := hole_AA ((fst_of hl).symm.trans (fst_of hl'))
      exact absurd rfl hne
    · obtain rfl : ε = true := (snd_of hl).trans (holeA_sign a k)
      exact gl_holes hΦ hk hk' ((fst_of hl).symm.trans (fst_of hl')) ht
        (snd_of hl')
    · obtain rfl : ε' = true := (snd_of hl').trans (holeA_sign a k')
      exact (gl_holes hΦ hk' hk ((fst_of hl').symm.trans (fst_of hl)) ht
        (snd_of hl)).symm
    · obtain rfl : k = k' := hole_BB ((fst_of hl).symm.trans (fst_of hl'))
      exact absurd rfl hne

theorem isPoly_inj (hΦ : IsPoly n Φ Φ') {z z' : ℂ} (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1) (h : Φ z
  = Φ z') : z = z' := by
  have h1 := hΦ.1.2.2.1 (mem_closedBall_zero_iff.mpr hz)
  have h2 := hΦ.1.2.2.1 (mem_closedBall_zero_iff.mpr hz')
  rw [← h1, ← h2, h]

theorem isPoly_mem (hΦ : IsPoly n Φ Φ') {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖Φ z‖ ≤ 1 :=
  mem_closedBall_zero_iff.mp (hΦ.1.1 (mem_closedBall_zero_iff.mpr hz))

theorem isPoly_right (hΦ : IsPoly n Φ Φ') {w : ℂ} (hw : ‖w‖ ≤ 1) : ∃ z, ‖z‖ ≤ 1 ∧ Φ z = w :=
  ⟨Φ' w, mem_closedBall_zero_iff.mp (hΦ.1.2.1 (mem_closedBall_zero_iff.mpr hw)),
    hΦ.1.2.2.2.1 (mem_closedBall_zero_iff.mpr hw)⟩

/-- A point with the same image under `upE` and its mirror lies on the circle, and its image lies on
the axis. -/
theorem upE_mirror {w w' : ℂ} (hw : ‖w‖ ≤ 1) (hw' : ‖w'‖ ≤ 1) (h : upE n w = mirO (upE n w')) :
    w = w' ∧ ‖w‖ = 1 ∧ (w = 1 ∨ hgt n (cay w).re = 0) := by
  by_cases h1 : w = 1
  · subst h1
    rw [upE_one] at h
    by_cases h2 : w' = 1
    · exact ⟨h2.symm, by simp, .inl rfl⟩
    · rw [upE_ne h2, mirO_coe] at h
      exact absurd h (OnePoint.infty_ne_coe _)
  · by_cases h2 : w' = 1
    · subst h2
      rw [upE_one, mirO_infty, upE_ne h1] at h
      exact absurd h (OnePoint.coe_ne_infty _)
    · rw [upE_ne h1, upE_ne h2, mirO_coe, modelMirror_pt] at h
      have e := OnePoint.coe_injective h
      have e1 := congrFun (congrArg (fun u : EuclideanPlane => (u : Fin 2 → ℝ)) e) 0
      have e2 := congrFun (congrArg (fun u : EuclideanPlane => (u : Fin 2 → ℝ)) e) 1
      simp only [pt_zero, pt_one] at e1 e2
      have i1 := cay_im_nonneg h1 hw
      have i2 := cay_im_nonneg h2 hw'
      have g1 := hgt_nonneg n (cay w).re
      have g2 := hgt_nonneg n (cay w').re
      rw [← e1] at e2 g2
      have i3 : (cay w).im = 0 := by linarith
      have i4 : (cay w').im = 0 := by linarith
      have g3 : hgt n (cay w).re = 0 := by linarith
      have e3 : cay w = cay w' := Complex.ext e1 (by rw [i3, i4])
      refine ⟨by rw [← cayI_cay h1, ← cayI_cay h2, e3], ?_, .inr g3⟩
      have := (norm_cayI_eq_iff (cay_add_I_ne h1)).mpr i3
      rwa [cayI_cay h1] at this

theorem Fv_fiber_cross (hΦ : IsPoly n Φ Φ') {z z' : ℂ} (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1)
    (h : Fv n Φ (0, z) = Fv n Φ (1, z')) : PRel (modelW a b n) (0, z) (1, z') := by
  rw [Fv_zero, Fv_one] at h
  obtain ⟨e, h1, h2⟩ := upE_mirror (isPoly_mem hΦ hz) (isPoly_mem hΦ hz') h
  obtain rfl := isPoly_inj hΦ hz hz' e
  obtain ⟨y, hy, hyw⟩ := exists_loop_param n h1
  have hzy : z = per (2 * n + 2) y := by
    have hpb : ‖per (2 * n + 2) y‖ ≤ 1 := (norm_per _ _).le
    refine isPoly_inj hΦ hz hpb ?_
    have := hΦ.2 y hy
    rw [hyw] at this
    exact this.symm
  have hpos : (2 * (n : ℝ) ≤ y) ∨ hgt n (axS y) = 0 := by
    by_cases hc : 2 * (n : ℝ) ≤ y
    · exact .inl hc
    right
    have hle : y ≤ 2 * n := (not_le.mp hc).le
    rw [angL_le hle] at hyw
    obtain ⟨e1, e2⟩ := cay_cis (axS y)
    rw [hyw] at e1 e2
    rcases h2 with h2 | h2
    · exact absurd h2 e1
    · rw [e2] at h2
      simpa using h2
  have key : ∃ p : ℕ, ∃ t ∈ Icc (0 : ℝ) 1, y = p + t ∧ ((∃ k, k ≤ n ∧ p = 2 * k) ∨ p = 2 * n + 1)
    := by
    rcases exists_side_of_ax hy (hpos.symm) with ⟨k, t, hk, ht, e⟩ | h3
    · exact ⟨2 * k, t, ht, by rw [e]; push_cast; ring, .inl ⟨k, hk.le, rfl⟩⟩
    · by_cases h4 : y ≤ 2 * n + 1
      · exact ⟨2 * n, y - 2 * n, ⟨by linarith, by linarith⟩, by push_cast; ring, .inl ⟨n, le_rfl,
        rfl⟩⟩
      · have h5 := hy.2
        push_cast at h5
        push Not at h4
        exact ⟨2 * n + 1, y - (2 * n + 1), ⟨by linarith, by linarith⟩, by push_cast; ring, .inr rfl⟩
  obtain ⟨p, t, ht, rfl, hp⟩ := key
  rw [hzy]
  exact .rel _ _ (stp_ax hp ht)

theorem Fv_fiber (hΦ : IsPoly n Φ Φ') {x y : ℕ × ℂ} (hx : x ∈ Dsk (modelW a b n)) (hy : y ∈ Dsk
  (modelW a b n))
    (h : Fv n Φ x = Fv n Φ y) : PRel (modelW a b n) x y := by
  obtain ⟨i, z⟩ := x
  obtain ⟨j, z'⟩ := y
  have hi : i ≤ 1 := modelW_slot hx.1
  have hj : j ≤ 1 := modelW_slot hy.1
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · rw [Fv_zero, Fv_zero] at h
      have e1 := injOn_upE n (mem_closedBall_zero_iff.mpr (isPoly_mem hΦ hx.2))
        (mem_closedBall_zero_iff.mpr (isPoly_mem hΦ hy.2)) h
      have e2 : z = z' := isPoly_inj hΦ hx.2 hy.2 e1
      rw [e2]
      exact .refl _
    · exact Fv_fiber_cross hΦ hx.2 hy.2 h
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · exact (Fv_fiber_cross hΦ hy.2 hx.2 h.symm).symm
    · rw [Fv_one, Fv_one] at h
      have e1 := injOn_upE n (mem_closedBall_zero_iff.mpr (isPoly_mem hΦ hx.2))
        (mem_closedBall_zero_iff.mpr (isPoly_mem hΦ hy.2)) (mirO.injective h)
      have e2 : z = z' := isPoly_inj hΦ hx.2 hy.2 e1
      rw [e2]
      exact .refl _

theorem modelW_zero_ne : modelW a b n 0 ≠ [] := by simp [modelW_zero]

theorem modelW_one_ne : modelW a b n 1 ≠ [] := by simp [modelW_one]

theorem Fv_surj (hΦ : IsPoly n Φ Φ') {p : OnePoint EuclideanPlane} (hp : p ∈ modelBase n) :
    ∃ x ∈ Dsk (modelW a b n), Fv n Φ x = p := by
  have up : ∀ q : OnePoint EuclideanPlane, (∃ z ∈ closedBall (0 : ℂ) 1, upE n z = q) →
      ∃ z, ‖z‖ ≤ 1 ∧ upE n (Φ z) = q := fun q ⟨w, hw, he⟩ => by
    obtain ⟨z, hz, e⟩ := isPoly_right hΦ (mem_closedBall_zero_iff.mp hw)
    exact ⟨z, hz, by rw [e, he]⟩
  induction p using OnePoint.rec with
  | infty =>
    obtain ⟨z, hz, e⟩ := up ∞ ⟨1, by simp, upE_one n⟩
    exact ⟨(0, z), ⟨modelW_zero_ne, hz⟩, by rw [Fv_zero, e]⟩
  | coe u =>
    rw [← pt_ext u] at hp ⊢
    rcases le_total 0 (u 1) with h | h
    · obtain ⟨z, hz, e⟩ := up _ (exists_upE (hgt_le_of_base hp h))
      exact ⟨(0, z), ⟨modelW_zero_ne, hz⟩, by rw [Fv_zero, e]⟩
    · have h1 := mirO_base hp
      rw [mirO_coe, modelMirror_pt] at h1
      obtain ⟨z, hz, e⟩ := up _ (exists_upE (hgt_le_of_base h1 (by linarith)))
      refine ⟨(1, z), ⟨modelW_one_ne, hz⟩, ?_⟩
      rw [Fv_one, e, mirO_coe, modelMirror_pt]
      simp

theorem exists_axU {u : EuclideanPlane} (hu : ‖u‖ = 1) (h : 0 ≤ u 1) :
    ∃ t ∈ Icc (0 : ℝ) 1, u = pt (axPhi t) (axPsi t) := by
  have hn := norm_pt_sq (u 0) (u 1)
  rw [pt_ext, hu] at hn
  have h1 : -1 ≤ u 0 := by nlinarith [sq_nonneg (u 1)]
  have h2 : u 0 ≤ 1 := by nlinarith [sq_nonneg (u 1)]
  have hiv := intermediate_value_Icc (a := 0) (b := 1) (by norm_num) continuous_axPhi.continuousOn
  rw [axPhi_zero, axPhi_one] at hiv
  obtain ⟨t, ht, e⟩ := hiv ⟨h1, h2⟩
  refine ⟨t, ht, ?_⟩
  rw [← pt_ext u]
  have e2 : axPsi t = u 1 := by
    unfold axPsi
    rw [e, show 1 - u 0 ^ 2 = u 1 ^ 2 by linarith, Real.sqrt_sq h]
  simp only [Fin.isValue]
  rw [e, e2]

/-- The two sides of a glued pair. -/
def HolePair (n : ℕ) (a b : ℕ) (Φ : ℂ → ℂ) (P Q : OnePoint EuclideanPlane) : Prop :=
  ∃ k k' t, k < n ∧ k' < n ∧ (holeA a k).1 = (holeB a b k').1 ∧ t ∈ Icc (0 : ℝ) 1 ∧
    P = Fv n Φ (0, sdPt (2 * n + 2) (2 * k + 1) true t) ∧
    Q = Fv n Φ (1, sdPt (2 * n + 2) (2 * k' + 1) (holeB a b k').2 t)

theorem Fv_up (hΦ : IsPoly n Φ Φ') {k : ℕ} (hk : k < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Fv n Φ (0, sdPt (2 * n + 2) (2 * k + 1) true t) =
      ((modelCentre k + pt (axPhi t) (axPsi t) : EuclideanPlane) : OnePoint EuclideanPlane) := by
  rw [sdPt_hole]
  exact_mod_cast Fv_hole0 hΦ hk ht

theorem Fv_down (hΦ : IsPoly n Φ Φ') {k : ℕ} (hk : k < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Fv n Φ (1, sdPt (2 * n + 2) (2 * k + 1) true t) =
      ((modelCentre k + modelMirror (pt (axPhi t) (axPsi t)) : EuclideanPlane) : OnePoint
        EuclideanPlane) := by
  rw [sdPt_hole]
  exact_mod_cast Fv_hole1 hΦ hk ht

theorem Fv_anti (hΦ : IsPoly n Φ Φ') {k : ℕ} (hk : k < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Fv n Φ (1, sdPt (2 * n + 2) (2 * k + 1) false t) =
      ((modelCentre k - pt (axPhi t) (axPsi t) : EuclideanPlane) : OnePoint EuclideanPlane) := by
  have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [sdPt_hole']
  have := Fv_hole1 hΦ hk ht'
  rw [show (2 * (k : ℝ) + 1 + (1 - t)) = 2 * k + 1 + (1 - t) from rfl, axU_neg] at this
  have e2 : modelMirror (-modelMirror (pt (axPhi t) (axPsi t))) = - pt (axPhi t) (axPsi t) := by
    ext j
    fin_cases j <;> simp [modelMirror]
  rw [e2, ← sub_eq_add_neg] at this
  exact_mod_cast this

theorem holePair_of_glue (hΦ : IsPoly n Φ Φ') (hn : 2 * a + b ≤ n) {p q : modelBase n}
    (h : ModelGlue a b n p q) : HolePair n a b Φ p.1 q.1 ∨ HolePair n a b Φ q.1 p.1 := by
  cases h with
  | handle i hi u hu p q hp hq =>
    have k0 : 2 * i < n := by omega
    have k1 : 2 * i + 1 < n := by omega
    have lA0 : holeA a (2 * i) = (4 * (2 * i) + 1, true) := by simp [holeA]
    have lA1 : holeA a (2 * i + 1) = (4 * (2 * i) + 2, true) := by
      simp only [holeA]
      rw [ite_eq_left (by omega)]
      simp
    have lB0 : holeB a b (2 * i) = (4 * (2 * i) + 2, true) := by
      simp only [holeB]
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    have lB1 : holeB a b (2 * i + 1) = (4 * (2 * i) + 1, true) := by
      simp only [holeB]
      rw [ite_eq_left (by omega), ite_eq_right (by omega)]
      simp
    rcases le_total 0 (u 1) with h | h
    · obtain ⟨t, ht, rfl⟩ := exists_axU hu h
      refine .inl ⟨2 * i, 2 * i + 1, t, k0, k1, by rw [lA0, lB1], ht, ?_, ?_⟩
      · rw [Fv_up hΦ k0 ht, hp]
      · rw [lB1, Fv_down hΦ k1 ht, hq]
    · have hm : 0 ≤ (modelMirror u) 1 := by
        have : (modelMirror u) 1 = - u 1 := rfl
        rw [this]
        linarith
      obtain ⟨t, ht, e⟩ := exists_axU (u := modelMirror u) (by rw [norm_mirror, hu]) hm
      refine .inr ⟨2 * i + 1, 2 * i, t, k1, k0, by rw [lA1, lB0], ht, ?_, ?_⟩
      · rw [Fv_up hΦ k1 ht, hq, e]
      · rw [lB0, Fv_down hΦ k0 ht, hp, ← e, modelMirror_mirror]
  | crosscap i hi u hu p q hp hq =>
    set k := 2 * a + i with hk
    have k0 : k < n := by omega
    have lA : (holeA a k) = (4 * k + 1, true) := by
      simp only [holeA]
      rw [ite_eq_right (by omega)]
    have lB : (holeB a b k) = (4 * k + 1, false) := by
      simp only [holeB]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    rcases le_total 0 (u 1) with h | h
    · obtain ⟨t, ht, rfl⟩ := exists_axU hu h
      refine .inl ⟨k, k, t, k0, k0, by rw [lA, lB], ht, ?_, ?_⟩
      · rw [Fv_up hΦ k0 ht, hp]
      · rw [lB, Fv_anti hΦ k0 ht, hq]
    · have hm : 0 ≤ (-u) 1 := by
        have : (-u) 1 = - u 1 := rfl
        rw [this]
        linarith
      obtain ⟨t, ht, e⟩ := exists_axU (u := -u) (by rw [norm_neg, hu]) hm
      refine .inr ⟨k, k, t, k0, k0, by rw [lA, lB], ht, ?_, ?_⟩
      · rw [Fv_up hΦ k0 ht, hq, ← e, sub_eq_add_neg]
      · rw [lB, Fv_anti hΦ k0 ht, hp, ← e, sub_neg_eq_add]

/-- The map from the two discs to the model surface. -/
noncomputable def toModel (a b n : ℕ) (Φ : ℂ → ℂ) (x : ℕ × ℂ) : Quot (ModelGlue a b n) :=
  Quot.mk _ (retB n (Fv n Φ x))

theorem presents_of_isPoly (hΦ : IsPoly n Φ Φ') (hn : 2 * a + b ≤ n) :
    Presents (modelW a b n) (toModel a b n Φ) := by
  have hbase : ∀ x ∈ Dsk (modelW a b n), Fv n Φ x ∈ modelBase n := fun x hx => Fv_base hΦ.1 hx.2
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContinuousOn (fun x => retB n (Fv n Φ x)) (Dsk (modelW a b n)) :=
      (continuousOn_retB n).comp (continuousOn_Fv hΦ.1) hbase
    exact continuous_quot_mk.comp_continuousOn h1
  · refine eq_univ_of_forall fun q => ?_
    obtain ⟨p, rfl⟩ := Quot.exists_rep q
    obtain ⟨x, hx, e⟩ := Fv_surj (a := a) (b := b) hΦ p.2
    refine ⟨x, hx, ?_⟩
    have : retB n (Fv n Φ x) = p := Subtype.ext (by rw [retB_val (hbase x hx), e])
    simp [toModel, this]
  · intro x hx y hy
    constructor
    · intro h
      have hq := Quot.eqvGen_exact h
      have key : ∀ p q, Relation.EqvGen (ModelGlue a b n) p q → ∀ x ∈ Dsk (modelW a b n),
          ∀ y ∈ Dsk (modelW a b n), Fv n Φ x = p.1 → Fv n Φ y = q.1 → PRel (modelW a b n) x y := by
        intro p q hpq
        induction hpq with
        | rel p q h =>
          intro x hx y hy e1 e2
          rcases holePair_of_glue hΦ hn h with ⟨k, k', t, hk, hk', hl, ht, h1, h2⟩ | ⟨k, k', t, hk,
            hk', hl, ht, h1, h2⟩
          · have s := stp_holes (a := a) (b := b) hk hk' hl ht
            exact ((Fv_fiber hΦ hx s.mem_Dsk.1 (e1.trans h1)).trans _ _ _ (.rel _ _ s)).trans _ _ _
              (Fv_fiber hΦ s.mem_Dsk.2 hy (h2.symm.trans e2.symm))
          · have s := stp_holes (a := a) (b := b) hk hk' hl ht
            exact ((Fv_fiber hΦ hx s.mem_Dsk.2 (e1.trans h2)).trans _ _ _ (.symm _ _
              (.rel _ _ s))).trans _ _ _
              (Fv_fiber hΦ s.mem_Dsk.1 hy (h1.symm.trans e2.symm))
        | refl p =>
          intro x hx y hy e1 e2
          exact Fv_fiber hΦ hx hy (e1.trans e2.symm)
        | symm p q _ ih =>
          intro x hx y hy e1 e2
          exact (ih y hy x hx e2 e1).symm
        | trans p q r _ _ ih1 ih2 =>
          intro x hx y hy e1 e2
          obtain ⟨w, hw, e⟩ := Fv_surj (a := a) (b := b) hΦ q.2
          exact (ih1 x hx w hw e1 e).trans _ _ _ (ih2 w hw y hy e e2)
      exact key _ _ hq x hx y hy (retB_val (hbase x hx)).symm (retB_val (hbase y hy)).symm
    · intro h
      have key : ∀ x y, PRel (modelW a b n) x y → x ∈ Dsk (modelW a b n) →
          Relation.EqvGen (ModelGlue a b n) (retB n (Fv n Φ x)) (retB n (Fv n Φ y)) := by
        intro x y hxy
        induction hxy with
        | rel x y h =>
          intro hx
          obtain ⟨h1, h2⟩ := h.mem_Dsk
          exact Fv_stp hΦ h _ _ (retB_val (hbase _ h1)) (retB_val (hbase _ h2))
        | refl x => exact fun _ => .refl _
        | symm x y h ih =>
          intro hx
          exact (ih ((prel_mem_iff h).mpr hx)).symm
        | trans x y z h1 h2 ih1 ih2 =>
          intro hx
          exact (ih1 hx).trans _ _ _ (ih2 ((prel_mem_iff h1).mp hx))
      exact Quot.eqvGen_sound (key x y h hx)

end poly

/-- The model surface is presented by its word. -/
theorem presents_model (a b c : ℕ) :
    ∃ f : ℕ × ℂ → SurfaceModel a b c, Presents (modelW a b (2 * a + b + c)) f := by
  obtain ⟨Φ, Φ', h⟩ := exists_modelPoly (2 * a + b + c)
  exact ⟨toModel a b _ Φ, presents_of_isPoly (Φ' := Φ') h (by omega)⟩

end GraphMinor.Surface
