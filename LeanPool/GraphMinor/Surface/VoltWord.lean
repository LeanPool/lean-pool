/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.WordCover
public import LeanPool.GraphMinor.Surface.CircleMove

/-!
# Voltages on words

Give each label of a family of words a value in a finite group `A`, which need not be commutative,
such that the values along
each word add up to zero. The partial sums along a word give a function on the discs with constant
jumps on pasted sides
(`sideConst_gW`), so `exists_cocycle` gives a local cocycle with this function as a primitive. The
main result is `volt_zero`.
A closed curve that is null-homotopic has a primitive that closes up, so a side of the word that
runs along such a curve has
value zero. This is how we show below that an `O`-arc is not null-homotopic.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

universe u

section words

variable {A : Type} [AddGroup A]

/-- The value of a letter. -/
def lVal (V : ℕ → A) (l : Letter) : A := if l.2 then V l.1 else -V l.1

/-- The sum of the values along a word. -/
def wv (V : ℕ → A) (w : List Letter) : A := (w.map (lVal V)).sum

@[simp] theorem wv_nil (V : ℕ → A) : wv V [] = 0 := rfl

@[simp] theorem wv_cons (V : ℕ → A) (l : Letter) (w : List Letter) : wv V (l :: w)
  = lVal V l + wv V w := by
  simp [wv]

@[simp] theorem wv_append (V : ℕ → A) (w w' : List Letter) : wv V (w ++ w') = wv V w + wv V w' := by
  simp [wv]

theorem lVal_linv (V : ℕ → A) (l : Letter) : lVal V (linv l) = -lVal V l := by
  obtain ⟨k, e⟩ := l
  cases e <;> simp [lVal, linv]

theorem wv_congr {V V' : ℕ → A} {w : List Letter} (h : ∀ l ∈ w, V l.1 = V' l.1) : wv V w = wv V' w
  := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [wv_cons, wv_cons, ih fun l' hl' => h l' (.tail _ hl')]
    have := h l (.head _)
    simp only [lVal, this]

theorem wv_zero {V : ℕ → A} {w : List Letter} (h : ∀ l ∈ w, V l.1 = 0) : wv V w = 0 := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [wv_cons, ih fun l' hl' => h l' (.tail _ hl')]
    have := h l (.head _)
    simp [lVal, this]

/-- The sum of the values of the first `j` letters. -/
def pr (V : ℕ → A) (w : List Letter) (j : ℕ) : A := wv V (w.take j)

theorem pr_zero (V : ℕ → A) (w : List Letter) : pr V w 0 = 0 := by simp [pr]

theorem pr_succ (V : ℕ → A) {w : List Letter} {p : ℕ} {l : Letter} (h : w[p]? = some l) : pr V w
  (p + 1) = pr V w p + lVal V l := by
  obtain ⟨hp, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [pr, pr, List.take_succ_eq_append_getElem hp, wv_append, wv_cons, wv_nil, add_zero]

theorem pr_length (V : ℕ → A) (w : List Letter) : pr V w w.length = wv V w := by
  rw [pr, List.take_length]

open Classical in
/-- The value at the point of the side `p` at the distance `u` from its start. It jumps at the
middle of the side. -/
noncomputable def gs (V : ℕ → A) (w : List Letter) (p : ℕ) (u : ℝ) : A :=
  match w[p]? with
  | some l => pr V w (if l.2 then p else p + 1) + if ofs l.2 u < 1 / 2 then 0 else V l.1
  | none => 0

theorem gs_zero (V : ℕ → A) {w : List Letter} {p : ℕ} {l : Letter} (h : w[p]?
  = some l) : gs V w p 0 = pr V w p := by
  obtain ⟨k, e⟩ := l
  simp only [gs, h]
  cases e
  · simp only [Bool.false_eq_true, ite_false, ofs]
    rw [pr_succ V h]
    norm_num [lVal]
  · simp only [ite_true, ofs]
    norm_num

theorem gs_one (V : ℕ → A) {w : List Letter} {p : ℕ} {l : Letter} (h : w[p]? = some l) : gs V w p 1
  = pr V w (p + 1) := by
  obtain ⟨k, e⟩ := l
  simp only [gs, h]
  cases e
  · simp only [Bool.false_eq_true, ite_false, ofs]
    norm_num
  · simp only [ite_true, ofs]
    rw [pr_succ V h]
    norm_num [lVal]

theorem gs_congr (V : ℕ → A) {w : List Letter} (hV : wv V w = 0) {p p' : ℕ} {u u' : ℝ}
  (hp : p < w.length) (hp' : p' < w.length)
    (hu : u ∈ Icc (0 : ℝ) 1) (hu' : u' ∈ Icc (0 : ℝ) 1) (he : per w.length (p + u) = per w.length
      (p' + u')) :
    gs V w p u = gs V w p' u' := by
  set n := w.length with hn
  by_cases h1 : u ∈ Ioo (0 : ℝ) 1
  · obtain ⟨rfl, rfl⟩ := side_unique hp hp' h1 hu' he
    rfl
  by_cases h2 : u' ∈ Ioo (0 : ℝ) 1
  · obtain ⟨rfl, rfl⟩ := side_unique hp' hp h2 hu he.symm
    rfl
  have hend : ∀ v ∈ Icc (0 : ℝ) 1, v ∉ Ioo (0 : ℝ) 1 → v = 0 ∨ v = 1 := fun v hv hv' => by
    by_contra hc
    push Not at hc
    exact hv' ⟨lt_of_le_of_ne hv.1 (Ne.symm hc.1), lt_of_le_of_ne hv.2 hc.2⟩
  have key : ∀ (q : ℕ) (v : ℝ), q < n → v = 0 ∨ v = 1 → ∃ j : ℕ, (j : ℝ) = q + v ∧ j ≤ q + 1
    ∧ gs V w q v = pr V w j := by
    rintro q v hq (rfl | rfl)
    · exact ⟨q, by simp, by omega, gs_zero V (List.getElem?_eq_getElem hq)⟩
    · exact ⟨q + 1, by simp, le_rfl, gs_one V (List.getElem?_eq_getElem hq)⟩
  obtain ⟨j, hj, hj1, hj2⟩ := key p u hp (hend u hu h1)
  obtain ⟨j', hj', hj1', hj2'⟩ := key p' u' hp' (hend u' hu' h2)
  rw [hj2, hj2']
  rw [← hj, ← hj'] at he
  obtain ⟨m, hm⟩ := per_eq (show 0 < n by omega) he
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm' : (j : ℤ) = j' + m * n := by exact_mod_cast hm
  have hjn : (j : ℤ) ≤ n := by exact_mod_cast (show j ≤ n by omega)
  have hjn' : (j' : ℤ) ≤ n := by exact_mod_cast (show j' ≤ n by omega)
  have hj0 : (0 : ℤ) ≤ j := by positivity
  have hj0' : (0 : ℤ) ≤ j' := by positivity
  have hmb : m = 0 ∨ m = 1 ∨ m = -1 := by
    have h3 : m < 2 := by
      by_contra hc
      have : 2 * (n : ℤ) ≤ m * n := by nlinarith
      omega
    have h4 : -2 < m := by
      by_contra hc
      have : m * (n : ℤ) ≤ -2 * n := by nlinarith
      omega
    omega
  have hT : pr V w n = 0 := by rw [hn, pr_length, hV]
  rcases hmb with rfl | rfl | rfl
  · have : j = j' := by omega
    rw [this]
  · have h3 : j = n := by omega
    have h4 : j' = 0 := by omega
    rw [h3, h4, hT, pr_zero]
  · have h3 : j = 0 := by omega
    have h4 : j' = n := by omega
    rw [h3, h4, hT, pr_zero]

open Classical in
/-- The function on one disc. -/
noncomputable def gz' (V : ℕ → A) (w : List Letter) (z : ℂ) : A :=
  if h : ∃ x : ℕ × ℝ, x.1 < w.length ∧ x.2 ∈ Icc (0 : ℝ) 1 ∧ per w.length (x.1 + x.2)
    = z then gs V w h.choose.1 h.choose.2 else 0

theorem gz'_per (V : ℕ → A) {w : List Letter} (hV : wv V w = 0) {p : ℕ} {u : ℝ} (hp : p < w.length)
  (hu : u ∈ Icc (0 : ℝ) 1) :
    gz' V w (per w.length (p + u)) = gs V w p u := by
  have hex : ∃ x : ℕ × ℝ, x.1 < w.length ∧ x.2 ∈ Icc (0 : ℝ) 1 ∧ per w.length (x.1 + x.2)
    = per w.length (p + u) :=
    ⟨(p, u), hp, hu, rfl⟩
  rw [gz', dite_eq_left hex]
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  exact gs_congr V hV h1 hp h2 hu h3

/-- The function on the discs. -/
noncomputable def gW (W : ℕ → List Letter) (V : ℕ → A) (x : ℕ × ℂ) : A := gz' V (W x.1) x.2

theorem sideConst_gW {W : ℕ → List Letter} {V : ℕ → A} (hV : ∀ i, wv V (W i) = 0) : SideConst W
  (gW W V) := by
  intro i p j q k e e' h1 h2 _
  have hp : p < (W i).length := (List.getElem?_eq_some_iff.mp h1).1
  have hq : q < (W j).length := (List.getElem?_eq_some_iff.mp h2).1
  refine ⟨pr V (W j) (if e' then q else q + 1) + -pr V (W i) (if e then p else p + 1),
    fun u hu => ?_⟩
  simp only [gW, spt]
  rw [gz'_per V (hV j) hq (flp_mem hu), gz'_per V (hV i) hp hu]
  have e1 : ofs e' (flp e e' u) = ofs e u := by rw [← ofs_flp, ofs_ofs]
  simp only [gs, h1, h2, e1, add_assoc, neg_add_cancel_left]

end words

section homotopy

variable {Y : Type u} [TopologicalSpace Y]

/-- A homotopy of a closed curve to a constant gives a map of the closed disc. -/
theorem exists_disc_map (H : C(Circle × unitInterval, Y)) {c₀ : Y} (h1 : ∀ x, H (x, 1)
  = c₀) :
    ∃ P : ℂ → Y, ContinuousOn P (closedBall 0 1) ∧ ∀ x : Circle, P x = H (x, 0) := by
  classical
  have mem : ∀ p : Circle × unitInterval, ((1 - p.2.1 : ℝ) : ℂ) * (p.1 : ℂ) ∈ closedBall (0 : ℂ) 1
    := fun p => by
    have h2 := p.2.2
    simp only [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Circle.norm_coe,
      mul_one, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith [h2.2])]
    linarith [h2.1]
  let π : Circle × unitInterval → closedBall (0 : ℂ) 1 := fun p => ⟨_, mem p⟩
  have hπ : Continuous π := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hsurj : Function.Surjective π := by
    rintro ⟨w, hw⟩
    have hw' : ‖w‖ ≤ 1 := by simpa using hw
    by_cases h0 : w = 0
    · subst h0
      exact ⟨(1, 1), Subtype.ext (by simp [π])⟩
    · refine ⟨(Circle.exp (Complex.arg w), ⟨1 - ‖w‖, by linarith [norm_nonneg w],
        by linarith [norm_nonneg w]⟩), Subtype.ext ?_⟩
      have h3 := Complex.norm_mul_exp_arg_mul_I w
      simp only [π, sub_sub_cancel, Circle.coe_exp]
      exact h3
  have hq : IsQuotientMap π := hπ.isClosedMap.isQuotientMap hπ hsurj
  have hfib : ∀ p p', π p = π p' → H p = H p' := by
    rintro ⟨x, t⟩ ⟨x', t'⟩ he
    have he' : ((1 - t.1 : ℝ) : ℂ) * (x : ℂ) = ((1 - t'.1 : ℝ) : ℂ) * (x' : ℂ)
      := congrArg Subtype.val he
    have n1 := congrArg norm he'
    have h2 := t.2
    have h3 := t'.2
    simp only [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_eq_abs] at n1
    rw [abs_of_nonneg (by linarith [h2.2]), abs_of_nonneg (by linarith [h3.2])] at n1
    have ht : t = t' := Subtype.ext (by linarith)
    subst ht
    by_cases h4 : t = 1
    · subst h4
      rw [h1, h1]
    · have h5 : (1 - t.1 : ℝ) ≠ 0 := fun h => h4 (Subtype.ext (by change t.1 = (1 : ℝ); linarith))
      have h6 : ((1 - t.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h5
      have h7 : (x : ℂ) = x' := mul_left_cancel₀ h6 he'
      rw [Circle.ext h7]
  let P₀ : closedBall (0 : ℂ) 1 → Y := fun w => H (Function.surjInv hsurj w)
  have hP₀ : ∀ p, P₀ (π p) = H p := fun p => hfib _ _ (Function.surjInv_eq hsurj (π p))
  have cP₀ : Continuous P₀ := by
    rw [hq.continuous_iff]
    have : P₀ ∘ π = H := funext hP₀
    rw [this]
    exact H.continuous
  refine ⟨fun z => if h : z ∈ closedBall (0 : ℂ) 1 then P₀ ⟨z, h⟩ else c₀, ?_, fun x => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (closedBall (0 : ℂ) 1).domRestrict (fun z => if h : z ∈ closedBall
      (0 : ℂ) 1 then P₀ ⟨z, h⟩ else c₀) = P₀ := by
      funext w
      simp only [Set.domRestrict_apply, w.2, dite_true]
    rw [this]
    exact cP₀
  · have hx : (x : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
    have e : π (x, 0) = ⟨x, hx⟩ := Subtype.ext (by simp [π])
    simp only [hx, dite_true]
    rw [← e, hP₀]

end homotopy

section prim

variable {Y : Type u} [TopologicalSpace Y] {A : Type} [AddGroup A]

omit [TopologicalSpace Y] in
/-- Two primitives along two paths with the same image in `Y` change by the same amount. -/
theorem prim_path {φ : Y → Y → A} {F₁ F₂ : ℂ → Y} {g₁ g₂ : ℂ → A} (h₁ : IsPrim φ F₁ g₁)
  (h₂ : IsPrim φ F₂ g₂) {γ₁ γ₂ : ℝ → ℂ}
    (c₁ : ContinuousOn γ₁ (Icc 0 1)) (c₂ : ContinuousOn γ₂ (Icc 0 1)) (m₁ : ∀ t ∈ Icc
      (0 : ℝ) 1, γ₁ t ∈ closedBall (0 : ℂ) 1)
    (m₂ : ∀ t ∈ Icc (0 : ℝ) 1, γ₂ t ∈ closedBall (0 : ℂ) 1) (he : ∀ t ∈ Icc (0 : ℝ) 1, F₁ (γ₁ t)
      = F₂ (γ₂ t)) :
    g₁ (γ₁ 1) + -g₂ (γ₂ 1) = g₁ (γ₁ 0) + -g₂ (γ₂ 0) := by
  obtain ⟨ε, h0, e1⟩ := h₁
  obtain ⟨ε', h0', e2⟩ := h₂
  obtain ⟨δ, hδ, d1⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous c₁) ε h0
  obtain ⟨δ', hδ', d2⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous c₂) ε' h0'
  have hv := const_of_near (A := A) (v := fun t => g₁ (γ₁ t) + -g₂ (γ₂ t)) (ε := min δ δ')
    (lt_min hδ hδ') (fun s hs t ht hst => by
    have hd : dist t s < min δ δ' := by
      rw [Real.dist_eq, abs_sub_comm]
      exact hst
    have n1 := d1 t ht s hs (lt_of_lt_of_le hd (min_le_left _ _))
    have n2 := d2 t ht s hs (lt_of_lt_of_le hd (min_le_right _ _))
    rw [dist_eq_norm] at n1 n2
    have e3 := e1 _ (m₁ t ht) _ (m₁ s hs) n1
    have e4 := e2 _ (m₂ t ht) _ (m₂ s hs) n2
    rw [he t ht, he s hs, e4] at e3
    have e5 := neg_add_eq_iff_eq_add.mp e3.symm
    change g₁ (γ₁ s) + -g₂ (γ₂ s) = g₁ (γ₁ t) + -g₂ (γ₂ t)
    rw [e5]
    simp only [add_assoc, add_neg_cancel, add_zero])
  exact hv 1 ⟨zero_le_one, le_rfl⟩

/-- **Null-homotopic curves have zero voltage.** Let a side of the word `W 0` with label `k` run
along a closed curve `c`, and let
`c` be homotopic to a constant. Then the value of `k` is zero. The cocycle from `exists_cocycle` has
a primitive on the disc
of the homotopy (`exists_prim`), and this primitive closes up along `c`. -/
theorem volt_zero {W : ℕ → List Letter} {f : ℕ × ℂ → Y} {V : ℕ → A} [T2Space Y] [Finite A]
  (hW : FinW W) (hP : IsPaired W) (hf : Presents W f)
    (h0 : W 0 ≠ []) (hV : ∀ i, wv V (W i) = 0) (H : C(Circle × unitInterval, Y)) {c : Circle
      → Y} {c₀ : Y} (hH0 : ∀ x, H (x, 0) = c x)
    (hH1 : ∀ x, H (x, 1) = c₀) {p k : ℕ} (hp : (W 0)[p]? = some (k, true)) {m : ℝ → ℝ}
      (hm : ContinuousOn m (Icc 0 1))
    (hee : ee (m 1) = ee (m 0)) (hs : ∀ u ∈ Icc (0 : ℝ) 1, f (0, per (W 0).length (p + u)) = c (ee
      (m u))) : V k = 0 := by
  obtain ⟨φ, hφ, hg₁, -⟩ := exists_cocycle (g := gW W V) hW hP hf (sideConst_gW hV) h0
  obtain ⟨P, cP, hPe⟩ := exists_disc_map H hH1
  obtain ⟨g₂, hg₂⟩ := exists_prim hφ cP
  have hlt : p < (W 0).length := (List.getElem?_eq_some_iff.mp hp).1
  have cc : Continuous fun x : Circle => (x : ℂ) := by fun_prop
  have c₂ : ContinuousOn (fun u => ((ee (m u) : Circle) : ℂ)) (Icc 0 1) :=
    cc.comp_continuousOn (continuous_ee.comp_continuousOn hm)
  have c₁ : ContinuousOn (fun u : ℝ => per (W 0).length (p + u)) (Icc 0 1) :=
    ((continuous_per _).comp (continuous_const.add continuous_id)).continuousOn
  have key : gW W V (0, per (W 0).length (p + 1)) + -g₂ (ee (m 1)) = gW W V (0, per (W 0).length
    (p + 0)) + -g₂ (ee (m 0)) :=
    prim_path hg₁ hg₂ c₁ c₂ (fun t _ => by simp [norm_per]) (fun t _ => by simp) (fun t ht => by
      show f (0, per (W 0).length (p + t)) = P (ee (m t))
      rw [hs t ht, hPe, hH0])
  rw [hee] at key
  have key' := add_right_cancel key
  have m1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have e1 : gW W V (0, per (W 0).length (p + 1)) = pr V (W 0) (p + 1) := by
    simp only [gW]
    rw [gz'_per V (hV 0) hlt m1, gs_one V hp]
  have e2 : gW W V (0, per (W 0).length (p + 0)) = pr V (W 0) p := by
    simp only [gW]
    rw [gz'_per V (hV 0) hlt m0, gs_zero V hp]
  rw [e1, e2, pr_succ V hp] at key'
  simpa [lVal] using key'

end prim

end GraphMinor.Surface
