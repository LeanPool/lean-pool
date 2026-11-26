/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.WordFold

/-!
# Rules for one word

We work with one word in the slot `0` (`sW`). `WEq w w'` says that `w` and `w'` present the same
spaces. The two rules
`ruleA` and `ruleB` move a pair of letters: we cut the word in two and glue the two pieces along the
pair.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Function Metric

universe uu

theorem peq_rot1 {W : ℕ → List Letter} (hW : FinW W) (i : ℕ) (x : Letter) (u : List Letter) :
    PEq.{uu} (update W i (x :: u)) (update W i (u ++ [x])) :=
  IsPolyMap.peq isPolyMap_rot1 (hW.update _ _)

theorem peq_rot {W : ℕ → List Letter} (hW : FinW W) (i : ℕ) (a b : List Letter) :
    PEq.{uu} (update W i (a ++ b)) (update W i (b ++ a)) := by
  induction a generalizing b with
  | nil => simp [PEq.refl]
  | cons x a ih =>
    have h1 := peq_rot1.{uu} hW i x (a ++ b)
    have h2 := ih (b ++ [x])
    simp only [List.cons_append]
    refine h1.trans ?_
    simp only [List.append_assoc] at h2 ⊢
    simpa using h2

theorem peq_rev {W : ℕ → List Letter} (hW : FinW W) (i : ℕ) (w : List Letter) :
    PEq.{uu} (update W i w) (update W i (winv w)) :=
  IsPolyMap.peq isPolyMap_rev (hW.update _ _)

theorem peq_cut {W : ℕ → List Letter} {i j y : ℕ} {u v : List Letter} (hW : FinW W) (e : Bool)
  (hij : j ≠ i)
    (hWj : W j = []) (hu : u ≠ []) (hv : v ≠ []) (hy : FreshIn (update W i (v ++ u)) y) :
    PEq.{uu} (update W i (v ++ u)) (update (update W i ((y, e) :: u)) j ((y, !e) :: v)) := by
  obtain ⟨θ, hθ, -, -⟩ := exists_isPolyMap_cut e hij hWj hu hv hy
  exact hθ.peq ((hW.update _ _).update _ _)

theorem peq_fold {W : ℕ → List Letter} {i y : ℕ} {u : List Letter} (hW : FinW W) (e : Bool)
  (hu : u ≠ [])
    (hy : FreshIn (update W i u) y) :
    PEq.{uu} (update W i u) (update W i ((y, e) :: (y, !e) :: u)) := by
  obtain ⟨θ, hθ⟩ := exists_isPolyMap_fold (e := e) hu hy
  exact hθ.peq (hW.update _ _)

/-- The family with no words. -/
def nW : ℕ → List Letter := fun _ => []

theorem finW_nW : FinW nW := by simp [FinW, nW]

/-- One word, in the slot `0`. -/
def sW (w : List Letter) : ℕ → List Letter := update nW 0 w

/-- Two words, in the slots `0` and `1`. -/
def dW (a b : List Letter) : ℕ → List Letter := update (sW a) 1 b

theorem finW_sW (w : List Letter) : FinW (sW w) := finW_nW.update _ _

theorem dW_comm (a b : List Letter) : dW a b = update (update nW 1 b) 0 a := by
  simp only [dW, sW]
  rw [update_comm (by decide)]

/-- Equivalent single words. -/
def WEq (w w' : List Letter) : Prop := PEq.{uu} (sW w) (sW w')

theorem WEq.refl (w : List Letter) : WEq.{uu} w w := PEq.refl _
theorem WEq.symm {w w' : List Letter} (h : WEq.{uu} w w') : WEq.{uu} w' w := PEq.symm h
theorem WEq.trans {w w' w'' : List Letter} (h : WEq.{uu} w w') (h' : WEq.{uu} w' w'') : WEq.{uu} w
  w'' :=
  PEq.trans h h'

theorem WEq.rot (a b : List Letter) : WEq.{uu} (a ++ b) (b ++ a) := peq_rot finW_nW 0 a b

theorem WEq.rev (w : List Letter) : WEq.{uu} w (winv w) := peq_rev finW_nW 0 w

theorem dW_rot_left (a b c : List Letter) : PEq.{uu} (dW (a ++ b) c) (dW (b ++ a) c) := by
  rw [dW_comm, dW_comm]
  exact peq_rot (finW_nW.update _ _) 0 a b

theorem dW_rot_right (a b c : List Letter) : PEq.{uu} (dW c (a ++ b)) (dW c (b ++ a)) :=
  peq_rot (finW_sW c) 1 a b

theorem dW_rev_left (a c : List Letter) : PEq.{uu} (dW a c) (dW (winv a) c) := by
  rw [dW_comm, dW_comm]
  exact peq_rev (finW_nW.update _ _) 0 a

/-- Labels of a word. -/
def NoLab (w : List Letter) (c : ℕ) : Prop := ∀ l ∈ w, l.1 ≠ c

theorem freshIn_sW {w : List Letter} {y : ℕ} (h : NoLab w y) : FreshIn (sW w) y := by
  intro i l hl
  by_cases hi : i = 0
  · subst hi
    exact h l (by simpa [sW] using hl)
  · simp [sW, update_of_ne hi, nW] at hl

theorem exists_fresh (w : List Letter) : ∃ y, y % 2 = 0 ∧ NoLab w y := by
  refine ⟨2 * (w.map Prod.fst).sum + 2, by omega, fun l hl h => ?_⟩
  have : l.1 ≤ (w.map Prod.fst).sum := List.single_le_sum (by simp) _ (List.mem_map_of_mem hl)
  omega

theorem peq_cut_sW {y : ℕ} {u v : List Letter} (e : Bool) (hu : u ≠ []) (hv : v ≠ [])
    (hy : NoLab (v ++ u) y) : PEq.{uu} (sW (v ++ u)) (dW ((y, e) :: u) ((y, !e) :: v)) := by
  refine peq_cut finW_nW e (by decide) rfl hu hv (freshIn_sW hy)

theorem relab_rename_inj {w : List Letter} {y c : ℕ} (hc : NoLab w c) :
    ∀ i j, ∀ l ∈ sW w i, ∀ l' ∈ sW w j, (fun n => if n = y then c else n) l.1 =
      (fun n => if n = y then c else n) l'.1 → l.1 = l'.1 := by
    intro i j l hl l' hl' he
    have h1 : ∀ i, ∀ l ∈ sW w i, l ∈ w := by
      intro i l hl
      by_cases hi : i = 0
      · subst hi
        simpa [sW] using hl
      · simp [sW, update_of_ne hi, nW] at hl
    have h2 := hc l (h1 _ _ hl)
    have h3 := hc l' (h1 _ _ hl')
    simp only at he
    split_ifs at he with h4 h5 h5
    · rw [h4, h5]
    · exact absurd he.symm h3
    · exact absurd he h2
    · exact he

theorem relab_sW (r : ℕ → ℕ) (w : List Letter) : relab r (sW w) = sW (w.map fun l => (r l.1, l.2))
  := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [relab, sW]
  · simp [relab, sW, update_of_ne hi, nW]

/-- Renaming the label `y` of `w` to a label `c` that does not occur. -/
theorem WEq.rename {w : List Letter} {y c : ℕ} (hc : NoLab w c) :
    WEq.{uu} w (w.map fun l => (if l.1 = y then c else l.1, l.2)) := by
  have h := peq_relab.{uu} (r := fun n => if n = y then c else n) (W := sW w) (relab_rename_inj hc)
  rw [relab_sW] at h
  exact h

theorem map_rename_of_noLab {w : List Letter} {y c : ℕ} (h : NoLab w y) :
    (w.map fun l => (if l.1 = y then c else l.1, l.2)) = w := by
  conv_rhs => rw [← List.map_id w]
  refine List.map_congr_left fun l hl => ?_
  simp [h l hl]

theorem noLab_append {a b : List Letter} {c : ℕ} : NoLab (a ++ b) c ↔ NoLab a c ∧ NoLab b c := by
  simp only [NoLab, List.mem_append]
  constructor
  · intro h
    exact ⟨fun l hl => h l (.inl hl), fun l hl => h l (.inr hl)⟩
  · rintro ⟨h1, h2⟩ l (hl | hl)
    · exact h1 l hl
    · exact h2 l hl

theorem noLab_cons {x : Letter} {b : List Letter} {c : ℕ} : NoLab (x :: b) c ↔ x.1 ≠ c ∧ NoLab b c
  := by
  simp only [NoLab, List.mem_cons]
  constructor
  · intro h
    exact ⟨h x (.inl rfl), fun l hl => h l (.inr hl)⟩
  · rintro ⟨h1, h2⟩ l (rfl | hl)
    · exact h1
    · exact h2 l hl

theorem noLab_nil {c : ℕ} : NoLab [] c := by simp [NoLab]

theorem noLab_winv {a : List Letter} {c : ℕ} : NoLab (winv a) c ↔ NoLab a c := by
  constructor
  · intro h l hl
    exact h (linv l) (List.mem_map.mpr ⟨l, List.mem_reverse.mpr hl, rfl⟩)
  · intro h l hl
    simp only [winv, List.mem_map, List.mem_reverse] at hl
    obtain ⟨m, hm, rfl⟩ := hl
    exact h m hm

theorem winv_append (a b : List Letter) : winv (a ++ b) = winv b ++ winv a := by simp [winv]

theorem winv_cons (x : Letter) (a : List Letter) : winv (x :: a) = winv a ++ [linv x] := by
  simp [winv]

theorem linv_linv (x : Letter) : linv (linv x) = x := by simp [linv]

theorem winv_winv (a : List Letter) : winv (winv a) = a := by
  simp [winv, List.map_reverse, Function.comp_def, linv]

theorem map_rename_append {y c : ℕ} (a b : List Letter) :
    ((a ++ b).map fun l => (if l.1 = y then c else l.1, l.2)) =
      (a.map fun l => (if l.1 = y then c else l.1, l.2)) ++ (b.map fun l => (if l.1
        = y then c else l.1, l.2)) :=
  List.map_append ..

/-- Replace a pair of letters by a fresh label: the core of `ruleA` and `ruleB`. -/
theorem weq_glue {U V : List Letter} {y : ℕ} {x : Letter} {X : List Letter}
    (_hy : NoLab X y) (hcut : PEq.{uu} (sW X) (dW (linv x :: U) (x :: V)))
    (h2 : V ≠ []) (h1 : U ≠ []) (hx1 : NoLab U x.1) (hx2 : NoLab V x.1) :
    WEq.{uu} X ((V ++ U).map fun l => (if l.1 = y then x.1 else l.1, l.2)) := by
  have hc : NoLab (V ++ U) x.1 := noLab_append.mpr ⟨hx2, hx1⟩
  have h3 := peq_cut_sW.{uu} (y := x.1) (!x.2) h1 h2 hc
  have e1 : ((x.1, !x.2) : Letter) = linv x := rfl
  have e2 : ((x.1, !!x.2) : Letter) = x := by simp
  rw [e1, e2] at h3
  exact (hcut.trans h3.symm).trans (WEq.rename hc)

/-- **Rule A.** A pair `x`, `x⁻¹` of letters of a word exchanges the two blocks on each of its
sides. -/
theorem ruleA (x : Letter) {u₁ u₂ v₁ v₂ : List Letter} (h1 : NoLab u₁ x.1) (h2 : NoLab u₂ x.1)
    (h3 : NoLab v₁ x.1) (h4 : NoLab v₂ x.1) :
    WEq.{uu} (u₁ ++ x :: (u₂ ++ v₁ ++ linv x :: v₂)) (u₂ ++ x :: (u₁ ++ v₂ ++ linv x :: v₁)) := by
  set X := u₁ ++ x :: (u₂ ++ v₁ ++ linv x :: v₂) with hX
  obtain ⟨y, -, hy⟩ := exists_fresh X
  have hy' : y ≠ x.1 := fun he => (noLab_append.mp hy).2 x (by simp) he.symm |>.elim
  have hA : NoLab (u₁ ++ x :: u₂) y ∧ NoLab (v₁ ++ linv x :: v₂) y := by
    have e : X = (u₁ ++ x :: u₂) ++ (v₁ ++ linv x :: v₂) := by simp [hX]
    rw [e] at hy
    exact noLab_append.mp hy
  have e : X = (u₁ ++ x :: u₂) ++ (v₁ ++ linv x :: v₂) := by simp [hX]
  have c1 : PEq.{uu} (sW X) (dW ((y, !x.2) :: (v₁ ++ linv x :: v₂)) ((y, x.2) :: (u₁ ++ x :: u₂)))
    := by
    have := peq_cut_sW.{uu} (y := y) (u := v₁ ++ linv x :: v₂) (v := u₁ ++ x :: u₂) (!x.2)
      (by simp) (by simp)
      (by rw [← e]; exact hy)
    rw [← e] at this
    simpa using this
  have c2 : PEq.{uu} (dW ((y, !x.2) :: (v₁ ++ linv x :: v₂)) ((y, x.2) :: (u₁ ++ x :: u₂)))
      (dW (linv x :: (v₂ ++ (y, !x.2) :: v₁)) ((y, x.2) :: (u₁ ++ x :: u₂))) := by
    have := dW_rot_left.{uu} ((y, !x.2) :: v₁) (linv x :: v₂) ((y, x.2) :: (u₁ ++ x :: u₂))
    simpa using this
  have c3 : PEq.{uu} (dW (linv x :: (v₂ ++ (y, !x.2) :: v₁)) ((y, x.2) :: (u₁ ++ x :: u₂)))
      (dW (linv x :: (v₂ ++ (y, !x.2) :: v₁)) (x :: (u₂ ++ (y, x.2) :: u₁))) := by
    have := dW_rot_right.{uu} ((y, x.2) :: u₁) (x :: u₂) (linv x :: (v₂ ++ (y, !x.2) :: v₁))
    simpa using this
  have g := weq_glue (x := x) (y := y) (U := v₂ ++ (y, !x.2) :: v₁) (V := u₂ ++ (y, x.2) :: u₁) hy
    (c1.trans (c2.trans c3)) (by simp) (by simp)
    (noLab_append.mpr ⟨h4, noLab_cons.mpr ⟨hy', h3⟩⟩) (noLab_append.mpr ⟨h2, noLab_cons.mpr ⟨hy',
      h1⟩⟩)
  refine (g.trans ?_)
  have hm : ∀ {a : List Letter}, NoLab a y → (a.map fun l => (if l.1 = y then x.1 else l.1, l.2))
    = a :=
    fun h => map_rename_of_noLab h
  have ha := noLab_append.mp hA.1
  have hb := noLab_append.mp hA.2
  have hu₂ := (noLab_cons.mp ha.2).2
  have hv₂ := (noLab_cons.mp hb.2).2
  have e3 : ((u₂ ++ (y, x.2) :: u₁ ++ (v₂ ++ (y, !x.2) :: v₁)).map
      fun l => (if l.1 = y then x.1 else l.1, l.2)) = u₂ ++ x :: (u₁ ++ v₂ ++ linv x :: v₁) := by
    simp only [List.map_append, List.map_cons, hm ha.1, hm hb.1, hm hu₂, hm hv₂, ite_true, linv,
      List.append_assoc, List.cons_append]
  rw [e3]
  exact WEq.refl _

/-- **Rule B.** The same for a pair `x`, `x` with the same sign: one block is reversed. -/
theorem ruleB (x : Letter) {u₁ u₂ v₁ v₂ : List Letter} (h1 : NoLab u₁ x.1) (h2 : NoLab u₂ x.1)
    (h3 : NoLab v₁ x.1) (h4 : NoLab v₂ x.1) :
    WEq.{uu} (u₁ ++ x :: (u₂ ++ v₁ ++ x :: v₂)) (u₂ ++ x :: (u₁ ++ winv v₁ ++ x :: winv v₂)) := by
  set X := u₁ ++ x :: (u₂ ++ v₁ ++ x :: v₂) with hX
  obtain ⟨y, -, hy⟩ := exists_fresh X
  have hy' : y ≠ x.1 := fun he => (noLab_append.mp hy).2 x (by simp) he.symm |>.elim
  have e : X = (u₁ ++ x :: u₂) ++ (v₁ ++ x :: v₂) := by simp [hX]
  have hA : NoLab (u₁ ++ x :: u₂) y ∧ NoLab (v₁ ++ x :: v₂) y := by
    rw [e] at hy
    exact noLab_append.mp hy
  have c1 : PEq.{uu} (sW X) (dW ((y, !x.2) :: (v₁ ++ x :: v₂)) ((y, x.2) :: (u₁ ++ x :: u₂))) := by
    have := peq_cut_sW.{uu} (y := y) (u := v₁ ++ x :: v₂) (v := u₁ ++ x :: u₂) (!x.2) (by simp)
      (by simp)
      (by rw [← e]; exact hy)
    rw [← e] at this
    simpa using this
  have c0 := dW_rev_left.{uu} ((y, !x.2) :: (v₁ ++ x :: v₂)) ((y, x.2) :: (u₁ ++ x :: u₂))
  have e0 : winv ((y, !x.2) :: (v₁ ++ x :: v₂)) =
      (winv v₂ ++ [linv x] ++ winv v₁) ++ [(y, x.2)] := by
    simp [winv, linv]
  rw [e0] at c0
  have c2 := dW_rot_left.{uu} (winv v₂) ([linv x] ++ winv v₁ ++ [(y, x.2)])
    ((y, x.2) :: (u₁ ++ x :: u₂))
  have e2 : winv v₂ ++ ([linv x] ++ winv v₁ ++ [(y, x.2)]) =
      winv v₂ ++ [linv x] ++ winv v₁ ++ [(y, x.2)] := by simp
  have e4 : [linv x] ++ winv v₁ ++ [(y, x.2)] ++ winv v₂ =
      linv x :: (winv v₁ ++ (y, x.2) :: winv v₂) := by simp
  rw [e2, e4] at c2
  have c3 := dW_rot_right.{uu} ((y, x.2) :: u₁) (x :: u₂)
    (linv x :: (winv v₁ ++ (y, x.2) :: winv v₂))
  have e5 : (y, x.2) :: u₁ ++ x :: u₂ = (y, x.2) :: (u₁ ++ x :: u₂) := by simp
  have e6 : x :: u₂ ++ (y, x.2) :: u₁ = x :: (u₂ ++ (y, x.2) :: u₁) := by simp
  rw [e5, e6] at c3
  have g := weq_glue (x := x) (y := y) (U := winv v₁ ++ (y, x.2) :: winv v₂) (V := u₂ ++
    (y, x.2) :: u₁) hy
    (c1.trans (c0.trans (c2.trans c3))) (by simp) (by simp)
    (noLab_append.mpr ⟨noLab_winv.mpr h3, noLab_cons.mpr ⟨hy', noLab_winv.mpr h4⟩⟩)
    (noLab_append.mpr ⟨h2, noLab_cons.mpr ⟨hy', h1⟩⟩)
  refine (g.trans ?_)
  have hm : ∀ {a : List Letter}, NoLab a y → (a.map fun l => (if l.1 = y then x.1 else l.1, l.2))
    = a :=
    fun h => map_rename_of_noLab h
  have ha := noLab_append.mp hA.1
  have hb := noLab_append.mp hA.2
  have hu₂ := (noLab_cons.mp ha.2).2
  have hv₂ := (noLab_cons.mp hb.2).2
  have e3 : ((u₂ ++ (y, x.2) :: u₁ ++ (winv v₁ ++ (y, x.2) :: winv v₂)).map
      fun l => (if l.1 = y then x.1 else l.1, l.2)) = u₂ ++ x :: (u₁ ++ winv v₁ ++ x :: winv v₂)
        := by
    simp only [List.map_append, List.map_cons, hm ha.1, hm hu₂, hm (noLab_winv.mpr hb.1),
      hm (noLab_winv.mpr hv₂), ite_true, List.append_assoc, List.cons_append]
  rw [e3]
  exact WEq.refl _

theorem per_injOn {n : ℕ} (hn : 0 < n) : InjOn (per n) (Ico 0 n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  intro x hx y hy he
  have h1 : Circle.exp (2 * Real.pi * x / n) = Circle.exp (2 * Real.pi * y / n) :=
    Circle.ext (by simpa [per, cis', Circle.coe_exp] using he)
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp h1
  have h2 : x = y + k * n := by
    field_simp at hk
    nlinarith
  have h3 : (k : ℝ) * n < 1 * n := by nlinarith [hx.2, hy.1]
  have h4 : (-1 : ℝ) * n < k * n := by nlinarith [hx.1, hy.2]
  have h5 : (k : ℝ) < 1 := lt_of_mul_lt_mul_right h3 hn'.le
  have h6 : (-1 : ℝ) < k := lt_of_mul_lt_mul_right h4 hn'.le
  have h7 : k < 1 := by exact_mod_cast h5
  have h8 : -1 < k := by exact_mod_cast h6
  obtain rfl : k = 0 := by omega
  simpa using h2

theorem per_image {n : ℕ} (hn : 0 < n) : per n '' Icc 0 n = Metric.sphere 0 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  ext z
  constructor
  · rintro ⟨x, -, rfl⟩
    exact mem_sphere_zero_iff_norm.mpr (norm_per _ _)
  · intro hz
    have h1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    obtain ⟨t, ht, hw⟩ := exists_circle_angle 1 (⟨z, by simpa [Submonoid.unitSphere] using h1⟩ :
      Circle)
    refine ⟨t * n / (2 * Real.pi), ⟨by have := ht.1; positivity, ?_⟩, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [ht.2]
    · have h2 : (z : ℂ) = Circle.exp t := by
        have := congrArg ((↑) : Circle → ℂ) hw
        simpa using this
      rw [h2, per, cis', Circle.coe_exp]
      congr 2
      push_cast
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
      field_simp

/-- The reparametrisation of the boundary that merges two sides. -/
noncomputable def mergeG (x : ℝ) : ℝ := if x ≤ 2 then x / 2 else x - 1

theorem continuous_mergeG : Continuous mergeG := by
  refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const fun x hx => ?_
  have : x = 2 := hx
  subst this
  norm_num

theorem strictMono_mergeG : StrictMono mergeG := by
  intro x y h
  simp only [mergeG]
  split_ifs <;> linarith

theorem mergeG_ge {x : ℝ} (h : 2 ≤ x) : mergeG x = x - 1 := by
  rcases eq_or_lt_of_le h with rfl | h
  · norm_num [mergeG]
  · exact ite_eq_right (not_le.mpr h)

/-- Two adjacent sides with labels that occur once are merged. -/
theorem exists_isPolyMap_merge {B : List Letter} {p q : ℕ} {e e' : Bool} (hpq : p ≠ q)
    (hp : NoLab B p) (hq : NoLab B q) :
    ∃ θ, IsPolyMap (sW ((p, e) :: B)) (sW ((p, e) :: (q, e') :: B)) θ ∧
      ∀ x ∈ Icc (0 : ℝ) ((B.length + 2 : ℕ) : ℝ), θ (0, per (B.length + 2) x) = (0, per
        (B.length + 1) (mergeG x)) := by
  classical
  set n := B.length + 1 with hn
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) ≤ B.length := Nat.cast_nonneg _
  have hnn : (n : ℝ) = B.length + 1 := by rw [hn]; push_cast; ring
  let β : ℝ → ℂ := fun x => per n (mergeG x)
  have e0 : mergeG 0 = 0 := by norm_num [mergeG]
  have e2 : mergeG ((n + 1 : ℕ) : ℝ) = n := by
    rw [mergeG_ge (by push_cast; linarith)]
    push_cast
    ring
  have himg : mergeG '' Icc 0 ((n + 1 : ℕ) : ℝ) = Icc 0 (n : ℝ) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← e0]
        exact strictMono_mergeG.monotone hx.1
      · rw [← e2]
        exact strictMono_mergeG.monotone hx.2
    · intro y hy
      have := intermediate_value_Icc (a := 0) (b := ((n + 1 : ℕ) : ℝ)) (by positivity)
        continuous_mergeG.continuousOn
      rw [e0, e2] at this
      exact this hy
  obtain ⟨Φ, Φ', m, hv⟩ := exists_polygon_map (K := closedBall (0 : ℂ) 1) isClosedDisc_closedBall.1
    (m := n + 1) (by omega) (β := β) ((continuous_per n).comp continuous_mergeG).continuousOn
    (by
      intro x hx y hy he
      have h1 : ∀ z ∈ Ico 0 ((n + 1 : ℕ) : ℝ), mergeG z ∈ Ico 0 (n : ℝ) := fun z hz =>
        ⟨by rw [← e0]; exact strictMono_mergeG.monotone hz.1,
          by rw [← e2]; exact strictMono_mergeG hz.2⟩
      exact strictMono_mergeG.injective (per_injOn hn0 (h1 x hx) (h1 y hy) he))
    (by
      simp only [β, e0, e2]
      have := per_add_self hn0.ne' 0
      rw [zero_add] at this
      rw [this])
    (by
      rw [isClosedDisc_closedBall.2, ← per_image hn0, ← himg, image_image])
  set W0 := sW ((p, e) :: B) with hW0
  set W1 := sW ((p, e) :: (q, e') :: B) with hW1
  have e3 : W1 0 = (p, e) :: (q, e') :: B := by simp [hW1, sW]
  have e4 : W0 0 = (p, e) :: B := by simp [hW0, sW]
  have e5 : ∀ s, s ≠ 0 → W1 s = [] := fun s h => by simp [hW1, sW, update_of_ne h, nW]
  have e6 : ∀ s, s ≠ 0 → W0 s = [] := fun s h => by simp [hW0, sW, update_of_ne h, nW]
  have s0 : ∀ {V : ℕ → List Letter}, (∀ s, s ≠ 0 → V s = []) → ∀ a ∈ Dsk V, a.1 = 0 := by
    intro V h a ha
    by_contra h'
    exact ha.1 (h _ h')
  have hlen1 : (W1 0).length = n + 1 := by rw [e3]; simp [hn]
  have hlen0 : (W0 0).length = n := by rw [e4]; simp [hn]
  have hball : ∀ {V : ℕ → List Letter} (a : ℕ × ℂ), a ∈ Dsk V → a.2 ∈ closedBall (0 : ℂ) 1 :=
    fun a h => mem_closedBall_zero_iff.mpr h.2
  have hside : ∀ r ε t, r < B.length → t ∈ Icc (0 : ℝ) 1 →
      Φ (sdPt (n + 1) (r + 2) ε t) = sdPt n (r + 1) ε t := by
    intro r ε t hr ht
    have hs := sv_mem ε ht
    have h1 : sdPt (n + 1) (r + 2) ε t = per (n + 1) (((r + 2 : ℕ) : ℝ) + sv ε t) := rfl
    have h2 : sdPt n (r + 1) ε t = per n (((r + 1 : ℕ) : ℝ) + sv ε t) := rfl
    have h3 : ((r + 1 : ℕ) : ℝ) ≤ B.length := by exact_mod_cast hr
    push_cast at h3
    have h4 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    rw [h1, h2, hv _ ⟨by push_cast; linarith [hs.1], by push_cast; rw [hnn]; linarith [hs.2]⟩]
    simp only [β]
    rw [mergeG_ge (by push_cast; linarith [hs.1])]
    congr 1
    push_cast
    ring
  have hone : ∀ {V : ℕ → List Letter} {c : ℕ} (b : List Letter), NoLab b c → V = sW b → ∀ (i r : ℕ)
    (ε : Bool),
      (V i)[r]? = some (c, ε) → False := by
    intro V c b hb hV i r ε h
    rw [hV] at h
    by_cases hi : i = 0
    · subst hi
      have h1 : (sW b 0) = b := by simp [sW]
      rw [h1] at h
      exact hb _ (List.mem_of_getElem? h) rfl
    · simp [sW, update_of_ne hi, nW] at h
  refine ⟨fun a => (a.1, Φ a.2), IsPolyMap.of_sides' (Y := {p, q}) (Z
    := {p}) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,
    fun x hx => ?_⟩
  · exact continuous_fst.continuousOn.prodMk (m.2.2.2.2.1.comp continuous_snd.continuousOn
      fun a ha => hball a ha)
  · rintro ⟨s, z⟩ hz
    obtain rfl : s = 0 := s0 e5 _ hz
    refine ⟨by simp [e4], ?_⟩
    exact mem_closedBall_zero_iff.mp (m.1 (hball _ hz))
  · rintro ⟨s, z⟩ hz
    obtain rfl : s = 0 := s0 e6 _ hz
    refine ⟨(0, Φ' z), ⟨by simp [e3], mem_closedBall_zero_iff.mp (m.2.1 (hball _ hz))⟩, ?_⟩
    simp only [m.2.2.2.1 (hball _ hz)]
  · rintro ⟨s, z⟩ hz ⟨s', z'⟩ hz' he
    obtain rfl : s = 0 := s0 e5 _ hz
    obtain rfl : s' = 0 := s0 e5 _ hz'
    have h1 : Φ z = Φ z' := (Prod.mk.inj he).2
    have h2 : z = z' := by
      have h3 : Φ' (Φ z) = z := m.2.2.1 (hball _ hz)
      have h4 : Φ' (Φ z') = z' := m.2.2.1 (hball _ hz')
      rw [← h3, ← h4, h1]
    rw [h2]
    exact .refl _
  · intro s r c ε h hc
    by_cases hs : s ≠ 0
    · rw [e5 s hs] at h
      simp at h
    obtain rfl : s = 0 := not_not.mp hs
    rw [e3] at h
    match r, h with
    | 0, h =>
      have : (p, e) = (c, ε) := by simpa using h
      exact absurd (.inl (Prod.mk.inj this).1.symm) hc
    | 1, h =>
      have : (q, e') = (c, ε) := by simpa using h
      exact absurd (.inr (Prod.mk.inj this).1.symm) hc
    | r + 2, h =>
      rw [List.getElem?_cons_succ, List.getElem?_cons_succ] at h
      have hr : r < B.length := (List.getElem?_eq_some_iff.mp h).1
      refine ⟨0, r + 1, ε, by rw [e4, List.getElem?_cons_succ]; exact h, fun t ht => ?_⟩
      simp only [hlen1, hlen0, hside r ε t hr ht]
  · intro s r c ε h hc
    by_cases hs : s ≠ 0
    · rw [e6 s hs] at h
      simp at h
    obtain rfl : s = 0 := not_not.mp hs
    rw [e4] at h
    cases r with
    | zero =>
      have : (p, e) = (c, ε) := by simpa using h
      exact absurd (Prod.mk.inj this).1.symm hc
    | succ r =>
      rw [List.getElem?_cons_succ] at h
      have hr : r < B.length := (List.getElem?_eq_some_iff.mp h).1
      refine ⟨0, r + 2, ε, by rw [e3, List.getElem?_cons_succ, List.getElem?_cons_succ]; exact h,
        fun t ht => ?_⟩
      simp only [hlen1, hlen0, hside r ε t hr ht]
  · intro i j r r' k ε ε' hk h1 h2
    obtain rfl : k = p := hk
    have key : ∀ i r ε, (W0 i)[r]? = some (k, ε) → i = 0 ∧ r = 0 := by
      intro i r ε h
      by_cases hi : i = 0
      · subst hi
        rw [e4] at h
        cases r with
        | zero => exact ⟨rfl, rfl⟩
        | succ r =>
          rw [List.getElem?_cons_succ] at h
          exact (hp _ (List.mem_of_getElem? h) rfl).elim
      · rw [e6 i hi] at h
        simp at h
    obtain ⟨rfl, rfl⟩ := key _ _ _ h1
    obtain ⟨rfl, rfl⟩ := key _ _ _ h2
    rfl
  · intro i j r r' k ε ε' t hk h1 h2 _
    have key : ∀ i r ε, (W1 i)[r]? = some (k, ε) →
        i = 0 ∧ ((k = p ∧ r = 0 ∧ ε = e) ∨ (k = q ∧ r = 1 ∧ ε = e')) := by
      intro i r ε h
      by_cases hi : i = 0
      · subst hi
        rw [e3] at h
        match r, h with
        | 0, h =>
          have : (p, e) = (k, ε) := by simpa using h
          exact ⟨rfl, .inl ⟨(Prod.mk.inj this).1.symm, rfl, (Prod.mk.inj this).2.symm⟩⟩
        | 1, h =>
          have : (q, e') = (k, ε) := by simpa using h
          exact ⟨rfl, .inr ⟨(Prod.mk.inj this).1.symm, rfl, (Prod.mk.inj this).2.symm⟩⟩
        | r + 2, h =>
          have h' : B[r]? = some (k, ε) := by
            rwa [List.getElem?_cons_succ, List.getElem?_cons_succ] at h
          have h'' := List.mem_of_getElem? h'
          rcases hk with hk | hk
          · exact (hp _ h'' hk).elim
          · exact (hq _ h'' hk).elim
      · rw [e5 i hi] at h
        simp at h
    obtain ⟨rfl, h3⟩ := key _ _ _ h1
    obtain ⟨rfl, h4⟩ := key _ _ _ h2
    rcases h3 with ⟨h5, rfl, rfl⟩ | ⟨h5, rfl, rfl⟩ <;> rcases h4 with ⟨h6, rfl, rfl⟩ | ⟨h6, rfl,
      rfl⟩
    · rfl
    · exact absurd (h5.symm.trans h6) hpq
    · exact absurd (h6.symm.trans h5) hpq
    · rfl
  · change (0, Φ (per (n + 1) x)) = _
    rw [hv x hx]

theorem WEq.merge {B : List Letter} {p q : ℕ} {e e' : Bool} (hpq : p ≠ q) (hp : NoLab B p)
  (hq : NoLab B q) :
    WEq.{uu} ((p, e) :: B) ((p, e) :: (q, e') :: B) := by
  obtain ⟨θ, hθ, -⟩ := exists_isPolyMap_merge (e := e) (e' := e') hpq hp hq
  exact hθ.peq (finW_sW _)

/-- Sign flips of the labels in `f`. -/
def flipL (f : ℕ → Bool) (l : Letter) : Letter := (l.1, xor (f l.1) l.2)

theorem sdPt_not (n p : ℕ) (b : Bool) (t : ℝ) : sdPt n p (!b) (1 - t) = sdPt n p b t := by
  cases b <;> simp [sdPt]

/-- Flipping the signs of some labels. -/
theorem WEq.flip (w : List Letter) (c : ℕ → Bool) : WEq.{uu} w (w.map (flipL c)) := by
  intro T _ _
  have hlen : ∀ i, (sW (w.map (flipL c)) i).length = (sW w i).length := fun i => by
    by_cases hi : i = 0
    · subst hi
      simp [sW]
    · simp [sW, update_of_ne hi, nW]
  have hD : Dsk (sW (w.map (flipL c))) = Dsk (sW w) := by
    ext a
    have := hlen a.1
    simp only [Dsk, mem_ofPred_eq, ne_eq, ← List.length_eq_zero_iff, this]
  have hget : ∀ i p, (sW (w.map (flipL c)) i)[p]? = ((sW w i)[p]?).map (flipL c) := fun i p => by
    by_cases hi : i = 0
    · subst hi
      have e1 : ∀ v : List Letter, sW v 0 = v := fun v => by simp [sW]
      rw [e1, e1, List.getElem?_map]
    · have e1 : ∀ v : List Letter, sW v i = [] := fun v => by simp [sW, update_of_ne hi, nW]
      rw [e1, e1]
      simp
  have hS : ∀ a b, Stp (sW w) a b → Stp (sW (w.map (flipL c))) a b := by
    rintro _ _ ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
    by_cases hk : c k = true
    · refine ⟨i, j, p, q, k, !ε, !ε', 1 - t, by simp [hget, h1, flipL, hk], by simp [hget, h2,
        flipL, hk], h3,
        ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_, ?_⟩
      · rw [hlen, sdPt_not]
      · rw [hlen, sdPt_not]
    · exact ⟨i, j, p, q, k, ε, ε', t, by simp [hget, h1, flipL, hk], by simp [hget, h2, flipL,
        hk], h3, ht,
        by rw [hlen], by rw [hlen]⟩
  have hS' : ∀ a b, Stp (sW (w.map (flipL c))) a b → Stp (sW w) a b := by
    rintro _ _ ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
    rw [hget, Option.map_eq_some_iff] at h1 h2
    obtain ⟨⟨k₁, ε₁⟩, a1, a2⟩ := h1
    obtain ⟨⟨k₂, ε₂⟩, b1, b2⟩ := h2
    simp only [flipL, Prod.mk.injEq] at a2 b2
    obtain ⟨rfl, a3⟩ := a2
    obtain ⟨hk2, b3⟩ := b2
    subst hk2
    by_cases hk : c k₂ = true
    · simp only [hk, Bool.true_xor] at a3 b3
      subst a3
      subst b3
      refine ⟨i, j, p, q, k₂, ε₁, ε₂, 1 - t, a1, b1, h3, ⟨by linarith [ht.2],
        by linarith [ht.1]⟩, ?_, ?_⟩
      · have := sdPt_not (sW w i).length p ε₁ (1 - t)
        rw [sub_sub_cancel] at this
        rw [hlen, this]
      · have := sdPt_not (sW w j).length q ε₂ (1 - t)
        rw [sub_sub_cancel] at this
        rw [hlen, this]
    · simp only [Bool.not_eq_true] at hk
      simp only [hk, Bool.false_xor] at a3 b3
      subst a3
      subst b3
      exact ⟨i, j, p, q, k₂, ε₁, ε₂, t, a1, b1, h3, ht, by rw [hlen], by rw [hlen]⟩
  have hSe : Stp (sW (w.map (flipL c))) = Stp (sW w) := by
    ext a b
    exact ⟨hS' a b, hS a b⟩
  have hP : ∀ f : ℕ × ℂ → T, Presents (sW w) f ↔ Presents (sW (w.map (flipL c))) f := fun f => by
    unfold Presents PRel
    rw [hD, hSe]
  exact exists_congr hP

end GraphMinor.Surface
