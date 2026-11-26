/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.WordSlide

/-!
# Moves that record sides

`PEq` only says that two families present the same spaces. To choose which hole of a word is a given
cuff we need a
sharper form: `Trk K W W'` says that a presentation by `W` gives a presentation by `W'` in which
each side with a label
in `K` has the same image, with the same parameter. Rotating a word, cutting along a chord and
gluing along a letter
all have this form. So a hole can be moved to the front of a word (`trk_hole_front`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe uu

/-- A presentation by `W` gives one by `W'` that agrees with it on the sides with labels in `K`. -/
def Trk (K : Set ℕ) (W W' : ℕ → List Letter) : Prop :=
  ∀ (T : Type uu) [TopologicalSpace T] [T2Space T] (f : ℕ × ℂ → T), Presents W f →
    ∃ f' : ℕ × ℂ → T, Presents W' f' ∧ ∀ k ∈ K, ∀ i p ε, (W i)[p]? = some (k, ε) →
      ∃ i' p', (W' i')[p']? = some (k, ε) ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        f' (i', sdPt (W' i').length p' ε t) = f (i, sdPt (W i).length p ε t)

theorem Trk.refl (K : Set ℕ) (W : ℕ → List Letter) : Trk.{uu} K W W := fun _ _ _ f hf =>
  ⟨f, hf, fun _ _ i p _ h => ⟨i, p, h, fun _ _ => rfl⟩⟩

theorem Trk.trans {K : Set ℕ} {W W' W'' : ℕ → List Letter} (h : Trk.{uu} K W W')
  (h' : Trk.{uu} K W' W'') :
    Trk.{uu} K W W'' := fun T _ _ f hf => by
  obtain ⟨f₁, h1, h2⟩ := h T f hf
  obtain ⟨f₂, h3, h4⟩ := h' T f₁ h1
  refine ⟨f₂, h3, fun k hk i p ε he => ?_⟩
  obtain ⟨i₁, p₁, a1, a2⟩ := h2 k hk i p ε he
  obtain ⟨i₂, p₂, b1, b2⟩ := h4 k hk i₁ p₁ ε a1
  exact ⟨i₂, p₂, b1, fun t ht => (b2 t ht).trans (a2 t ht)⟩

/-- A smaller set of labels, up to labels that do not occur in the first family. -/
theorem Trk.restrict {K K' : Set ℕ} {W W' : ℕ → List Letter} (h : Trk.{uu} K W W')
    (hK : ∀ k ∈ K', k ∈ K ∨ ∀ i, ∀ l ∈ W i, l.1 ≠ k) : Trk.{uu} K' W W' := fun T _ _ f hf => by
  obtain ⟨f₁, h1, h2⟩ := h T f hf
  refine ⟨f₁, h1, fun k hk i p ε he => ?_⟩
  rcases hK k hk with h3 | h3
  · exact h2 k h3 i p ε he
  · exact absurd rfl (h3 i _ (List.mem_of_getElem? he))

theorem trk_rot1 {W : ℕ → List Letter} {i : ℕ} (x : Letter) (u : List Letter) :
    Trk.{uu} univ (update W i (x :: u)) (update W i (u ++ [x])) := fun T _ _ f hf => by
  refine ⟨_, hf.of_map isPolyMap_rot1, fun k _ j p ε h => ?_⟩
  set n := u.length + 1 with hn
  have hn0 : n ≠ 0 := by omega
  have hlen1 : (update W i (x :: u) i).length = n := by simp [hn]
  have hlen2 : (update W i (u ++ [x]) i).length = n := by simp [hn]
  by_cases hj : j = i
  · subst hj
    rw [update_self] at h
    cases p with
    | zero =>
      refine ⟨j, u.length, ?_, fun t _ => ?_⟩
      · have : (k, ε) = x := by simpa using h.symm
        simp [this]
      · simp only [Function.comp_apply, ite_true]
        rw [hlen1, hlen2]
        simp only [sdPt, per_mul]
        congr 2
        have := per_add_self hn0 (((0 : ℕ) : ℝ) + if ε then t else 1 - t)
        rw [← this]
        congr 1
        rw [hn]
        push_cast
        ring
    | succ p =>
      rw [List.getElem?_cons_succ] at h
      have hp : p < u.length := (List.getElem?_eq_some_iff.mp h).1
      refine ⟨j, p, ?_, fun t _ => ?_⟩
      · rw [update_self, List.getElem?_append_left hp]
        exact h
      · simp only [Function.comp_apply, ite_true]
        rw [hlen1, hlen2]
        simp only [sdPt, per_mul]
        congr 2
        push_cast
        ring_nf
  · refine ⟨j, p, by rw [update_ne hj] at h ⊢; exact h, fun t _ => ?_⟩
    simp only [Function.comp_apply, ite_eq_right hj, update_ne hj]

theorem trk_rot {W : ℕ → List Letter} {i : ℕ} (a b : List Letter) :
    Trk.{uu} univ (update W i (a ++ b)) (update W i (b ++ a)) := by
  induction a generalizing b with
  | nil => simpa using Trk.refl.{uu} univ _
  | cons x a ih =>
    have h1 : Trk.{uu} univ (update W i ((x :: a) ++ b)) (update W i ((a ++ b) ++ [x])) := by
      simpa using trk_rot1 (W := W) (i := i) x (a ++ b)
    have h2 : Trk.{uu} univ (update W i (a ++ (b ++ [x]))) (update W i ((b ++ [x]) ++ a)) := ih
      (b ++ [x])
    have e1 : (a ++ b) ++ [x] = a ++ (b ++ [x]) := by simp
    have e2 : (b ++ [x]) ++ a = b ++ x :: a := by simp
    rw [e1] at h1
    rw [e2] at h2
    exact h1.trans h2

theorem trk_cut {W : ℕ → List Letter} {i j y : ℕ} {u v : List Letter} (e : Bool) (hij : j ≠ i)
    (hWj : W j = []) (hu : u ≠ []) (hv : v ≠ []) (hy : FreshIn (update W i (v ++ u)) y) :
    Trk.{uu} univ (update W i (v ++ u)) (update (update W i ((y, e) :: u)) j ((y, !e) :: v))
      := fun T _ _ f hf => by
  obtain ⟨θ, hθ, -, hup⟩ := exists_isPolyMap_cut (e := e) hij hWj hu hv hy
  refine ⟨_, hf.of_map hθ, fun k _ i' p ε h => ?_⟩
  obtain ⟨s, q, h1, h2⟩ := hup i' p k ε h
  exact ⟨s, q, h1, fun t ht => by simp only [Function.comp_apply, h2 t ht]⟩

theorem trk_glue {W : ℕ → List Letter} {i j y : ℕ} {u v : List Letter} (hW : FinW W) (e : Bool)
  (hij : j ≠ i)
    (hWj : W j = []) (hu : u ≠ []) (hv : v ≠ []) (hy : FreshIn (update W i (v ++ u)) y) :
    Trk.{uu} {y}ᶜ (update (update W i ((y, e) :: u)) j ((y, !e) :: v)) (update W i (v ++ u))
      := fun T _ _ f hf => by
  obtain ⟨θ, hθ, hdown, -⟩ := exists_isPolyMap_cut (e := e) hij hWj hu hv hy
  obtain ⟨g, hg, hval⟩ := hf.map' hθ ((hW.update i _).update j _)
  refine ⟨g, hg, fun k hk i' p ε h => ?_⟩
  obtain ⟨s, q, h1, h2⟩ := hdown i' p k ε h hk
  refine ⟨s, q, h1, fun t ht => ?_⟩
  rw [← h2 t ht]
  refine hval _ ⟨?_, (norm_per _ _).le⟩
  intro he
  simp only [he, List.getElem?_nil, reduceCtorEq] at h

theorem trk_relab {r : ℕ → ℕ} {W : ℕ → List Letter} {K : Set ℕ} (hK : ∀ k ∈ K, r k = k)
    (hr : ∀ i j, ∀ l ∈ W i, ∀ l' ∈ W j, r l.1 = r l'.1 → l.1 = l'.1) : Trk.{uu} K W (relab r W)
      := fun T _ _ f hf => by
  refine ⟨f, (presents_relab hr f).mp hf, fun k hk i p ε h => ⟨i, p, ?_,
    fun t _ => by rw [relab_length]⟩⟩
  have := relab_getElem (r := r) h
  rwa [hK k hk] at this

theorem trk_rot_sW {w w' : List Letter} (a b : List Letter) (h : w = a ++ b) (h' : w' = b ++ a) :
    Trk.{uu} univ (sW w) (sW w') := by
  rw [h, h']
  exact trk_rot a b

theorem trk_cut_sW {y : ℕ} {u v : List Letter} (e : Bool) (hu : u ≠ []) (hv : v ≠ []) (hy : NoLab
  (v ++ u) y) :
    Trk.{uu} univ (sW (v ++ u)) (dW ((y, e) :: u) ((y, !e) :: v)) :=
  trk_cut (W := nW) e (by decide) rfl hu hv (freshIn_sW hy)

theorem trk_glue_sW {y : ℕ} {u v : List Letter} (e : Bool) (hu : u ≠ []) (hv : v ≠ []) (hy : NoLab
  (v ++ u) y) :
    Trk.{uu} {y}ᶜ (dW ((y, e) :: u) ((y, !e) :: v)) (sW (v ++ u)) :=
  trk_glue (W := nW) finW_nW e (by decide) rfl hu hv (freshIn_sW hy)

theorem trk_dW_left (a b c : List Letter) : Trk.{uu} univ (dW (a ++ b) c) (dW (b ++ a) c) := by
  rw [dW_comm, dW_comm]
  exact trk_rot a b

theorem trk_dW_right (a b c : List Letter) : Trk.{uu} univ (dW c (a ++ b)) (dW c (b ++ a)) :=
  trk_rot a b

/-- `ruleA`, keeping all sides with other labels. -/
theorem trk_ruleA (x : Letter) (u₁ u₂ v₁ v₂ : List Letter) (h1 : NoLab u₁ x.1) (h2 : NoLab u₂ x.1)
    (h3 : NoLab v₁ x.1) (h4 : NoLab v₂ x.1) {w w' : List Letter}
    (he : w = u₁ ++ x :: (u₂ ++ v₁ ++ linv x :: v₂)) (he' : w' = u₂ ++ x ::
      (u₁ ++ v₂ ++ linv x :: v₁)) :
    Trk.{uu} {k | k ≠ x.1} (sW w) (sW w') := by
  subst he he'
  set X := u₁ ++ x :: (u₂ ++ v₁ ++ linv x :: v₂) with hX
  obtain ⟨y, -, hy⟩ := exists_fresh X
  have hy' : y ≠ x.1 := fun he => (noLab_append.mp hy).2 x (by simp) he.symm |>.elim
  have e : X = (u₁ ++ x :: u₂) ++ (v₁ ++ linv x :: v₂) := by simp [hX]
  have hA : NoLab (u₁ ++ x :: u₂) y ∧ NoLab (v₁ ++ linv x :: v₂) y := by
    rw [e] at hy
    exact noLab_append.mp hy
  let K : Set ℕ := {k | k ≠ x.1 ∧ k ≠ y}
  have c1 : Trk.{uu} K (sW X) (dW ((y, !x.2) :: (v₁ ++ linv x :: v₂)) ((y, x.2) ::
    (u₁ ++ x :: u₂))) := by
    have := trk_cut_sW.{uu} (y := y) (u := v₁ ++ linv x :: v₂) (v := u₁ ++ x :: u₂) (!x.2)
      (by simp) (by simp)
      (by rw [← e]; exact hy)
    rw [← e] at this
    have h5 := this.restrict (K' := K) fun k _ => .inl (mem_univ _)
    simpa using h5
  have c2 : Trk.{uu} K (dW ((y, !x.2) :: (v₁ ++ linv x :: v₂)) ((y, x.2) :: (u₁ ++ x :: u₂)))
      (dW (linv x :: (v₂ ++ (y, !x.2) :: v₁)) ((y, x.2) :: (u₁ ++ x :: u₂))) := by
    have := (trk_dW_left.{uu} ((y, !x.2) :: v₁) (linv x :: v₂) ((y, x.2) ::
      (u₁ ++ x :: u₂))).restrict (K' := K)
      fun k _ => .inl (mem_univ _)
    simpa using this
  have c3 : Trk.{uu} K (dW (linv x :: (v₂ ++ (y, !x.2) :: v₁)) ((y, x.2) :: (u₁ ++ x :: u₂)))
      (dW (linv x :: (v₂ ++ (y, !x.2) :: v₁)) (x :: (u₂ ++ (y, x.2) :: u₁))) := by
    have := (trk_dW_right.{uu} ((y, x.2) :: u₁) (x :: u₂) (linv x :: (v₂ ++
      (y, !x.2) :: v₁))).restrict (K' := K)
      fun k _ => .inl (mem_univ _)
    simpa using this
  set U := v₂ ++ (y, !x.2) :: v₁ with hU
  set V := u₂ ++ (y, x.2) :: u₁ with hV
  have hx1 : NoLab U x.1 := noLab_append.mpr ⟨h4, noLab_cons.mpr ⟨hy', h3⟩⟩
  have hx2 : NoLab V x.1 := noLab_append.mpr ⟨h2, noLab_cons.mpr ⟨hy', h1⟩⟩
  have hc : NoLab (V ++ U) x.1 := noLab_append.mpr ⟨hx2, hx1⟩
  have c4 : Trk.{uu} K (dW (linv x :: U) (x :: V)) (sW (V ++ U)) := by
    have h5 := trk_glue_sW.{uu} (y := x.1) (u := U) (v := V) (!x.2) (by simp [hU]) (by simp [hV]) hc
    have e1 : ((x.1, !x.2) : Letter) = linv x := rfl
    have e2 : ((x.1, !!x.2) : Letter) = x := by simp
    rw [e1, e2] at h5
    exact h5.restrict fun k hk => .inl hk.1
  have c5 : Trk.{uu} K (sW (V ++ U)) (sW ((V ++ U).map fun l => (if l.1
    = y then x.1 else l.1, l.2))) := by
    have h5 := trk_relab.{uu} (r := fun n => if n = y then x.1 else n) (W := sW (V ++ U)) (K := K)
      (fun k hk => ite_eq_right hk.2) (relab_rename_inj hc)
    rwa [relab_sW] at h5
  have hm : ∀ {a : List Letter}, NoLab a y → (a.map fun l => (if l.1 = y then x.1 else l.1, l.2))
    = a :=
    fun h => map_rename_of_noLab h
  have ha := noLab_append.mp hA.1
  have hb := noLab_append.mp hA.2
  have hu₂ := (noLab_cons.mp ha.2).2
  have hv₂ := (noLab_cons.mp hb.2).2
  have e3 : ((V ++ U).map fun l => (if l.1 = y then x.1 else l.1, l.2)) = u₂ ++ x ::
    (u₁ ++ v₂ ++ linv x :: v₁) := by
    simp only [hU, hV, List.map_append, List.map_cons, hm ha.1, hm hb.1, hm hu₂, hm hv₂, ite_true,
      linv,
      List.append_assoc, List.cons_append]
  rw [e3] at c5
  refine (c1.trans (c2.trans (c3.trans (c4.trans c5)))).restrict fun k hk => ?_
  by_cases hky : k = y
  · refine .inr fun i l hl => ?_
    subst hky
    by_cases hi : i = 0
    · subst hi
      exact hy l (by simpa [sW] using hl)
    · simp [sW, update_of_ne hi, nW] at hl
  · exact .inl ⟨hk, hky⟩

/-- A hole slides, keeping all sides with other labels. -/
theorem trk_slide_hole (t : Letter) {s A B : List Letter} (hs : NoLab s t.1) (hA : NoLab A t.1)
  (hB : NoLab B t.1) :
    Trk.{uu} {k | k ≠ t.1} (sW (A ++ B ++ t :: s ++ [linv t])) (sW (B ++ A ++ t :: s ++ [linv t]))
      := by
  have hAB : NoLab (A ++ B) t.1 := noLab_append.mpr ⟨hA, hB⟩
  have r : ∀ {w w' : List Letter} (a b : List Letter), w = a ++ b → w' = b ++ a →
      Trk.{uu} {k | k ≠ t.1} (sW w) (sW w') := fun a b h h' =>
    (trk_rot_sW a b h h').restrict fun k _ => .inl (mem_univ _)
  have c0 : Trk.{uu} {k | k ≠ t.1} (sW (A ++ B ++ t :: s ++ [linv t])) (sW (t :: s ++ linv t ::
    (A ++ B))) :=
    r (A ++ B) (t :: s ++ [linv t]) (by simp) (by simp)
  have c1 : Trk.{uu} {k | k ≠ t.1} (sW (t :: s ++ linv t :: (A ++ B))) (sW (t ::
    (A ++ B ++ linv t :: s))) :=
    trk_ruleA t [] [] s (A ++ B) noLab_nil noLab_nil hs hAB (by simp) (by simp)
  have c2 : Trk.{uu} {k | k ≠ t.1} (sW (t :: (A ++ B ++ linv t :: s))) (sW (A ++ t ::
    (s ++ linv t :: B))) :=
    trk_ruleA t [] A B s noLab_nil hA hB hs (by simp) (by simp)
  have c3 : Trk.{uu} {k | k ≠ t.1} (sW (A ++ t :: (s ++ linv t :: B))) (sW
    (B ++ A ++ t :: s ++ [linv t])) :=
    r (A ++ t :: s ++ [linv t]) B (by simp) (by simp)
  exact c0.trans (c1.trans (c2.trans c3))

/-- A hole moves to the front of a word, keeping all sides with other labels. -/
theorem trk_hole_front (t : Letter) {s P Q : List Letter} (hs : NoLab s t.1) (hP : NoLab P t.1)
  (hQ : NoLab Q t.1) :
    Trk.{uu} {k | k ≠ t.1} (sW (P ++ (t :: s ++ [linv t]) ++ Q)) (sW (t :: s ++ linv t ::
      (P ++ Q))) := by
  have r : ∀ {w w' : List Letter} (a b : List Letter), w = a ++ b → w' = b ++ a →
      Trk.{uu} {k | k ≠ t.1} (sW w) (sW w') := fun a b h h' =>
    (trk_rot_sW a b h h').restrict fun k _ => .inl (mem_univ _)
  have c0 : Trk.{uu} {k | k ≠ t.1} (sW (P ++ (t :: s ++ [linv t]) ++ Q)) (sW
    (Q ++ P ++ t :: s ++ [linv t])) :=
    r (P ++ (t :: s ++ [linv t])) Q (by simp) (by simp)
  have c2 : Trk.{uu} {k | k ≠ t.1} (sW (P ++ Q ++ t :: s ++ [linv t])) (sW (t :: s ++ linv t ::
    (P ++ Q))) :=
    r (P ++ Q) (t :: s ++ [linv t]) (by simp) (by simp)
  exact c0.trans ((trk_slide_hole t hs hQ hP).trans c2)

/-- The side of `W` with label `k` and sign `true` has parameter `ρ`. -/
def SideVal {T : Type*} (W : ℕ → List Letter) (f : ℕ × ℂ → T) (k : ℕ) (ρ : ℝ → T) : Prop :=
  ∃ i p, (W i)[p]? = some (k, true) ∧ ∀ u ∈ Icc (0 : ℝ) 1, f (i, sdPt (W i).length p true u) = ρ u

/-- Sides that a move keeps. -/
theorem Trk.sideVal {K : Set ℕ} {W W' : ℕ → List Letter} (h : Trk.{uu} K W W') {T : Type uu}
  [TopologicalSpace T]
    [T2Space T] {f : ℕ × ℂ → T} (hf : Presents W f) : ∃ f', Presents W' f'
      ∧ ∀ k ∈ K, ∀ ρ, SideVal W f k ρ → SideVal W' f' k ρ := by
  obtain ⟨f', h1, h2⟩ := h T f hf
  refine ⟨f', h1, fun k hk ρ ⟨i, p, h3, h4⟩ => ?_⟩
  obtain ⟨i', p', h5, h6⟩ := h2 k hk i p true h3
  exact ⟨i', p', h5, fun u hu => (h6 u hu).trans (h4 u hu)⟩

theorem sdPt_true (n p : ℕ) (u : ℝ) : sdPt n p true u = per n (p + u) := by
  simp [sdPt]

/-- A free side with parameter `ρ` at the front of a word is cut into two halves. -/
theorem exists_split_front {T : Type uu} [TopologicalSpace T] {B : List Letter} {p q : ℕ}
  (hpq : p ≠ q)
    (hp : NoLab B p) (hq : NoLab B q) {f : ℕ × ℂ → T} (hf : Presents (sW
      ((p, true) :: B)) f) {ρ : ℝ → T}
    (hρ : SideVal (sW ((p, true) :: B)) f p ρ) :
    ∃ f', Presents (sW ((p, true) :: (q, true) :: B)) f' ∧ SideVal (sW ((p, true) ::
      (q, true) :: B)) f' p (fun u => ρ (u / 2)) ∧
      SideVal (sW ((p, true) :: (q, true) :: B)) f' q (fun u => ρ ((1 + u) / 2)) ∧
      ∀ k, k ≠ p → k ≠ q → ∀ ρ', SideVal (sW ((p, true) :: B)) f k ρ' → SideVal (sW ((p, true) ::
        (q, true) :: B)) f' k ρ' := by
  obtain ⟨θ, hθ, hv⟩ := exists_isPolyMap_merge (e := true) (e' := true) hpq hp hq
  have hS0 : ∀ {w : List Letter} {i p : ℕ} {l : Letter}, (sW w i)[p]? = some l → i = 0 ∧ w[p]?
    = some l := by
    intro w i p l h
    by_cases hi : i = 0
    · subst hi
      exact ⟨rfl, by simpa [sW] using h⟩
    · simp [sW, update_of_ne hi, nW] at h
  have hlen : (B.length : ℝ) = ((B.length : ℕ) : ℝ) := rfl
  have hB0 : (0 : ℝ) ≤ B.length := Nat.cast_nonneg _
  have hbase : ∀ _ : ℕ, (sW ((p, true) :: B) 0).length = B.length + 1 ∧
      (sW ((p, true) :: (q, true) :: B) 0).length = B.length + 2 := by
    intro _
    simp [sW]
  have hρ0 : ∀ u ∈ Icc (0 : ℝ) 1, f (0, per (B.length + 1) u) = ρ u := by
    obtain ⟨i, r, h1, h2⟩ := hρ
    obtain ⟨rfl, h3⟩ := hS0 h1
    cases r with
    | zero =>
      intro u hu
      have := h2 u hu
      rw [(hbase 0).1, sdPt_true] at this
      simpa using this
    | succ r =>
      rw [List.getElem?_cons_succ] at h3
      exact absurd rfl (hp _ (List.mem_of_getElem? h3))
  refine ⟨f ∘ θ, hf.of_map hθ, ⟨0, 0, by simp [sW], fun u hu => ?_⟩, ⟨0, 1, by simp [sW],
    fun u hu => ?_⟩, ?_⟩
  · have hu₀ : ((0 : ℕ) : ℝ) + u ∈ Icc (0 : ℝ) ↑(B.length + 2) := by
      constructor
      · simpa using hu.1
      · push_cast
        linarith [hu.2]
    rw [(hbase 0).2, sdPt_true, Function.comp_apply, hv _ hu₀]
    have : mergeG (((0 : ℕ) : ℝ) + u) = u / 2 := by
      simp only [mergeG, Nat.cast_zero, zero_add]
      rw [ite_eq_left (by linarith [hu.2])]
    rw [this]
    exact hρ0 _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · rw [(hbase 0).2, sdPt_true, Function.comp_apply, hv _ ⟨by push_cast; linarith [hu.1], by
    push_cast; linarith [hu.2]⟩]
    have : mergeG (((1 : ℕ) : ℝ) + u) = (1 + u) / 2 := by
      simp only [mergeG, Nat.cast_one]
      rw [ite_eq_left (by linarith [hu.2])]
    rw [this]
    exact hρ0 _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · rintro k hkp hkq ρ' ⟨i, r, h1, h2⟩
    obtain ⟨rfl, h3⟩ := hS0 h1
    cases r with
    | zero =>
      have : (p, true) = (k, true) := by simpa using h3
      exact absurd (Prod.mk.inj this).1.symm hkp
    | succ r =>
      rw [List.getElem?_cons_succ] at h3
      have hr : r < B.length := (List.getElem?_eq_some_iff.mp h3).1
      refine ⟨0, r + 2, by simpa [sW] using h3, fun u hu => ?_⟩
      have h4 := h2 u hu
      rw [(hbase 0).1, sdPt_true] at h4
      rw [(hbase 0).2, sdPt_true, Function.comp_apply]
      have hr' : ((r + 1 : ℕ) : ℝ) ≤ B.length := by exact_mod_cast hr
      push_cast at hr'
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
      rw [hv _ ⟨by push_cast; linarith [hu.1], by push_cast; linarith [hu.2]⟩,
        mergeG_ge (by push_cast; linarith [hu.1])]
      rw [← h4]
      congr 3
      push_cast
      ring

/-- A free side with parameter `ρ` inside a word is cut into two halves. -/
theorem exists_split {T : Type uu} [TopologicalSpace T] [T2Space T] {A B : List Letter} {p q : ℕ}
  (hpq : p ≠ q)
    (hp : NoLab (B ++ A) p) (hq : NoLab (B ++ A) q) {f : ℕ × ℂ → T} (hf : Presents (sW (A ++
      (p, true) :: B)) f) {ρ : ℝ → T}
    (hρ : SideVal (sW (A ++ (p, true) :: B)) f p ρ) :
    ∃ f', Presents (sW (A ++ (p, true) :: (q, true) :: B)) f' ∧ SideVal (sW (A ++ (p, true) ::
      (q, true) :: B)) f' p (fun u => ρ (u / 2)) ∧
      SideVal (sW (A ++ (p, true) :: (q, true) :: B)) f' q (fun u => ρ ((1 + u) / 2)) ∧
      ∀ k, k ≠ p → k ≠ q → ∀ ρ', SideVal (sW (A ++ (p, true) :: B)) f k ρ' → SideVal (sW (A ++
        (p, true) :: (q, true) :: B)) f' k ρ' := by
  obtain ⟨f₁, h1, h2⟩ := (trk_rot_sW.{uu} (w := A ++ (p, true) :: B) (w' := (p, true) ::
    (B ++ A)) A ((p, true) :: B) rfl (by simp)).sideVal hf
  obtain ⟨f₂, h3, h4, h5, h6⟩ := exists_split_front hpq hp hq h1 (h2 _ (mem_univ _) _ hρ)
  obtain ⟨f₃, h7, h8⟩ := (trk_rot_sW.{uu} (w := (p, true) :: (q, true) :: (B ++ A)) (w' := A ++
    (p, true) :: (q, true) :: B) ((p, true) :: (q, true) :: B) A (by simp) rfl).sideVal h3
  exact ⟨f₃, h7, h8 _ (mem_univ _) _ h4, h8 _ (mem_univ _) _ h5, fun k h9 h10 ρ' h11 =>
    h8 _ (mem_univ _) _ (h6 k h9 h10 ρ' (h2 _ (mem_univ _) _ h11))⟩

end GraphMinor.Surface
