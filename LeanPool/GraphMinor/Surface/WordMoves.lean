/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.PolyMoves

/-!
# Moves on words

`PEq W W'`: the families `W` and `W'` present the same Hausdorff spaces. Each move gives this
through a map of
discs: rotating a word (`peq_rot`), reversing it (`peq_rev`), renaming labels (`peq_rename`),
cutting a word along a
chord or gluing two words along a letter (`peq_cut`), and folding two adjacent letters (`peq_fold`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter Function

universe u

/-- Sides of `W'` go to sides of `W` with the same label, except labels in `Y`, where the two sides
have the
same image. All sides of `W` arise. -/
theorem IsPolyMap.of_sides' {W W' : ℕ → List Letter} {θ : ℕ × ℂ → ℕ × ℂ} {Y Z : Set ℕ}
    (cont : ContinuousOn θ (Dsk W')) (maps : MapsTo θ (Dsk W') (Dsk W)) (surj : Dsk W ⊆ θ '' Dsk W')
    (fib : ∀ a ∈ Dsk W', ∀ b ∈ Dsk W', θ a = θ b → PRel W' a b)
    (down : ∀ i p k ε, (W' i)[p]? = some (k, ε) → k ∉ Y → ∃ i' p' ε', (W i')[p']? = some (k, ε') ∧
      ∀ t ∈ Icc (0 : ℝ) 1, θ (i, sdPt (W' i).length p ε t) = (i', sdPt (W i').length p' ε' t))
    (up : ∀ i' p' k ε', (W i')[p']? = some (k, ε') → k ∉ Z → ∃ i p ε, (W' i)[p]? = some (k, ε) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, θ (i, sdPt (W' i).length p ε t) = (i', sdPt (W i').length p' ε' t))
    (hZ : ∀ (i j p q k : ℕ) (ε ε' : Bool), k ∈ Z → (W i)[p]? = some (k, ε) → (W j)[q]? = some
      (k, ε') → (i, p) = (j, q))
    (hY : ∀ i j p q k ε ε' t, k ∈ Y → (W' i)[p]? = some (k, ε) → (W' j)[q]? = some (k, ε') →
      t ∈ Icc (0 : ℝ) 1 → θ (i, sdPt (W' i).length p ε t) = θ (j, sdPt (W' j).length q ε' t)) :
    IsPolyMap W W' θ := by
  have hmem : ∀ {W : ℕ → List Letter} {i p k ε} (t : ℝ), (W i)[p]? = some (k, ε) →
      (i, sdPt (W i).length p ε t) ∈ Dsk W := fun t h =>
    ⟨fun he => by simp [he] at h, (norm_per _ _).le⟩
  refine ⟨cont, maps, surj, fib, ?_, ?_⟩
  · rintro _ _ ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
    have hk : k ∉ Z := fun hk => h3 (hZ i j p q k ε ε' hk h1 h2)
    obtain ⟨i₁, p₁, ε₁, a1, a2⟩ := up i p k ε h1 hk
    obtain ⟨i₂, p₂, ε₂, b1, b2⟩ := up j q k ε' h2 hk
    refine ⟨_, hmem t a1, _, hmem t b1, a2 t ht, b2 t ht, ?_⟩
    by_cases he : (i₁, p₁) = (i₂, p₂)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [a1] at b1
      have : ε₁ = ε₂ := by simpa using b1
      subst this
      exact .refl _
    · exact .rel _ _ ⟨i₁, i₂, p₁, p₂, k, ε₁, ε₂, t, a1, b1, he, ht, rfl, rfl⟩
  · rintro _ _ ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
    by_cases hk : k ∈ Y
    · rw [hY i j p q k ε ε' t hk h1 h2 ht]
      exact .refl _
    · obtain ⟨i₁, p₁, ε₁, a1, a2⟩ := down i p k ε h1 hk
      obtain ⟨i₂, p₂, ε₂, b1, b2⟩ := down j q k ε' h2 hk
      rw [a2 t ht, b2 t ht]
      by_cases he : (i₁, p₁) = (i₂, p₂)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        rw [a1] at b1
        have : ε₁ = ε₂ := by simpa using b1
        subst this
        exact .refl _
      · exact .rel _ _ ⟨i₁, i₂, p₁, p₂, k, ε₁, ε₂, t, a1, b1, he, ht, rfl, rfl⟩

/-- `IsPolyMap.of_sides'` when all sides of `W` arise. -/
theorem IsPolyMap.of_sides {W W' : ℕ → List Letter} {θ : ℕ × ℂ → ℕ × ℂ} {Y : Set ℕ}
    (cont : ContinuousOn θ (Dsk W')) (maps : MapsTo θ (Dsk W') (Dsk W)) (surj : Dsk W ⊆ θ '' Dsk W')
    (fib : ∀ a ∈ Dsk W', ∀ b ∈ Dsk W', θ a = θ b → PRel W' a b)
    (down : ∀ i p k ε, (W' i)[p]? = some (k, ε) → k ∉ Y → ∃ i' p' ε', (W i')[p']? = some (k, ε') ∧
      ∀ t ∈ Icc (0 : ℝ) 1, θ (i, sdPt (W' i).length p ε t) = (i', sdPt (W i').length p' ε' t))
    (up : ∀ i' p' k ε', (W i')[p']? = some (k, ε') → ∃ i p ε, (W' i)[p]? = some (k, ε) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, θ (i, sdPt (W' i).length p ε t) = (i', sdPt (W i').length p' ε' t))
    (hY : ∀ i j p q k ε ε' t, k ∈ Y → (W' i)[p]? = some (k, ε) → (W' j)[q]? = some (k, ε') →
      t ∈ Icc (0 : ℝ) 1 → θ (i, sdPt (W' i).length p ε t) = θ (j, sdPt (W' j).length q ε' t)) :
    IsPolyMap W W' θ :=
  IsPolyMap.of_sides' (Z := ∅) cont maps surj fib down (fun i' p' k ε' h _ => up i' p' k ε' h)
    (fun _ _ _ _ _ _ _ h => absurd h (notMem_empty _)) hY

/-- `W` and `W'` present the same Hausdorff spaces. -/
def PEq (W W' : ℕ → List Letter) : Prop :=
  ∀ (T : Type u) [TopologicalSpace T] [T2Space T],
    (∃ f : ℕ × ℂ → T, Presents W f) ↔ ∃ f : ℕ × ℂ → T, Presents W' f

theorem PEq.refl (W : ℕ → List Letter) : PEq.{u} W W := fun _ _ _ => Iff.rfl

theorem PEq.symm {W W' : ℕ → List Letter} (h : PEq.{u} W W') : PEq.{u} W' W :=
  fun T _ _ => (h T).symm

theorem PEq.trans {W W' W'' : ℕ → List Letter} (h : PEq.{u} W W') (h' : PEq.{u} W' W'') : PEq.{u} W
  W'' :=
  fun T _ _ => (h T).trans (h' T)

theorem IsPolyMap.peq {W W' : ℕ → List Letter} {θ : ℕ × ℂ → ℕ × ℂ} (hθ : IsPolyMap W W' θ)
    (hW' : {i | W' i ≠ []}.Finite) : PEq.{u} W W' := fun _T _ _ =>
  ⟨fun ⟨_, hf⟩ => ⟨_, hf.of_map hθ⟩, fun ⟨_, hf⟩ => hf.map hθ hW'⟩

/-- The families with finitely many words. -/
def FinW (W : ℕ → List Letter) : Prop := {i | W i ≠ []}.Finite

theorem FinW.update {W : ℕ → List Letter} (h : FinW W) (i : ℕ) (w : List Letter) :
    FinW (Function.update W i w) := by
  refine (h.union (finite_singleton i)).subset fun j hj => ?_
  by_cases he : j = i
  · exact .inr he
  · refine .inl ?_
    simpa [Function.update_of_ne he] using hj

theorem per_mul (m : ℕ) (x y : ℝ) : per m x * per m y = per m (x + y) := by
  simp only [per, cis']
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_per (m : ℕ) (x : ℝ) : (starRingEnd ℂ) (per m x) = per m (-x) := by
  simp only [per, cis']
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem update_ne {W : ℕ → List Letter} {i j : ℕ} {w : List Letter} (h : j ≠ i) :
    Function.update W i w j = W j := Function.update_of_ne h _ _

section rot

variable {W : ℕ → List Letter} {i : ℕ} {x : Letter} {u : List Letter}

/-- Rotating a word by one letter. -/
theorem isPolyMap_rot1 :
    IsPolyMap (update W i (x :: u)) (update W i (u ++ [x]))
      (fun a => if a.1 = i then (i, per (u.length + 1) 1 * a.2) else a) := by
  set n := u.length + 1 with hn
  have hn0 : n ≠ 0 := by omega
  have hlen1 : (update W i (x :: u) i).length = n := by simp [hn]
  have hlen2 : (update W i (u ++ [x]) i).length = n := by simp [hn]
  refine IsPolyMap.of_sides (Y := ∅) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [continuousOn_prod_of_discrete_left]
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [ite_true]
      exact (Continuous.prodMk continuous_const (continuous_const.mul continuous_id)).continuousOn
    · simp only [ite_eq_right hj]
      exact (Continuous.prodMk continuous_const continuous_id).continuousOn
  · rintro ⟨j, z⟩ ⟨h1, h2⟩
    by_cases hj : j = i
    · subst hj
      simp only [ite_true]
      refine ⟨by simp, ?_⟩
      simp only [norm_mul, norm_per, one_mul]
      exact h2
    · simp only [ite_eq_right hj]
      refine ⟨?_, h2⟩
      simpa [update_ne hj] using h1
  · rintro ⟨j, z⟩ ⟨h1, h2⟩
    by_cases hj : j = i
    · subst hj
      refine ⟨(j, per n (-1) * z), ⟨by simp, by simpa [norm_per] using h2⟩, ?_⟩
      simp only [ite_true]
      rw [← mul_assoc, per_mul, add_neg_cancel]
      simp [per, cis']
    · refine ⟨(j, z), ⟨by simpa [update_ne hj] using h1, h2⟩, ?_⟩
      simp [hj]
  · rintro ⟨j, z⟩ ⟨-, h2⟩ ⟨j', z'⟩ ⟨-, h3⟩ he
    have h1 : j = j' := by
      by_cases hj : j = i <;> by_cases hj' : j' = i
      · rw [hj, hj']
      · simp only [ite_eq_left hj, ite_eq_right hj', Prod.mk.injEq] at he
        exact absurd he.1.symm hj'
      · simp only [ite_eq_right hj, ite_eq_left hj', Prod.mk.injEq] at he
        exact absurd he.1 hj
      · simp only [ite_eq_right hj, ite_eq_right hj', Prod.mk.injEq] at he
        exact he.1
    subst h1
    have h4 : z = z' := by
      by_cases hj : j = i
      · simp only [ite_eq_left hj, Prod.mk.injEq, true_and] at he
        exact mul_left_cancel₀ (by
          intro h0
          have := norm_per (u.length + 1) 1
          rw [h0] at this
          simp at this) he
      · simp only [ite_eq_right hj, Prod.mk.injEq] at he
        exact he.2
    rw [h4]
    exact .refl _
  · intro j p k ε h _
    by_cases hj : j = i
    · subst hj
      rw [update_self] at h
      rw [hlen2]
      by_cases hp : p < u.length
      · refine ⟨j, p + 1, ε, ?_, fun t _ => ?_⟩
        · rw [update_self, List.getElem?_cons_succ]
          rwa [List.getElem?_append_left hp] at h
        · simp only [ite_true]
          rw [hlen1]
          simp only [sdPt, per_mul]
          congr 2
          push_cast
          ring
      · have hp' : p = u.length := by
          have := (List.getElem?_eq_some_iff.mp h).1
          simp at this
          omega
        subst hp'
        rw [List.getElem?_append_right le_rfl] at h
        simp only [Nat.sub_self] at h
        refine ⟨j, 0, ε, ?_, fun t _ => ?_⟩
        · rw [update_self]
          simpa using h
        · simp only [ite_true]
          rw [hlen1]
          simp only [sdPt, per_mul]
          rw [Prod.mk.injEq]
          refine ⟨rfl, ?_⟩
          have := per_add_self hn0 (((0 : ℕ) : ℝ) + if ε then t else 1 - t)
          rw [← this]
          congr 1
          rw [hn]
          push_cast
          ring
    · refine ⟨j, p, ε, by rw [update_ne hj] at h ⊢; exact h, fun t _ => ?_⟩
      simp only [ite_eq_right hj, update_ne hj]
  · intro j p k ε h
    by_cases hj : j = i
    · subst hj
      rw [update_self] at h
      rw [hlen1]
      cases p with
      | zero =>
        refine ⟨j, u.length, ε, ?_, fun t _ => ?_⟩
        · rw [update_self, List.getElem?_append_right le_rfl]
          simpa using h
        · simp only [ite_true]
          rw [hlen2]
          simp only [sdPt, per_mul]
          rw [Prod.mk.injEq]
          refine ⟨rfl, ?_⟩
          have := per_add_self hn0 (((0 : ℕ) : ℝ) + if ε then t else 1 - t)
          rw [← this]
          congr 1
          rw [hn]
          push_cast
          ring
      | succ p =>
        rw [List.getElem?_cons_succ] at h
        have hp : p < u.length := (List.getElem?_eq_some_iff.mp h).1
        refine ⟨j, p, ε, ?_, fun t _ => ?_⟩
        · rw [update_self, List.getElem?_append_left hp]
          exact h
        · simp only [ite_true]
          rw [hlen2]
          simp only [sdPt, per_mul]
          congr 2
          push_cast
          ring
    · refine ⟨j, p, ε, by rw [update_ne hj] at h ⊢; exact h, fun t _ => ?_⟩
      simp only [ite_eq_right hj, update_ne hj]
  · intro _ _ _ _ _ _ _ _ h
    exact absurd h (notMem_empty _)

end rot

/-- The inverse of a letter. -/
def linv (l : Letter) : Letter := (l.1, !l.2)

/-- The inverse of a word. -/
def winv (w : List Letter) : List Letter := w.reverse.map linv

theorem conj_sdPt {n p : ℕ} (hp : p < n) (ε : Bool) (t : ℝ) :
    (starRingEnd ℂ) (sdPt n p ε t) = sdPt n (n - 1 - p) (!ε) t := by
  have hn : n ≠ 0 := by omega
  have h1 : ((n - 1 - p : ℕ) : ℝ) = n - 1 - p := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    simp
  rw [sdPt, conj_per, sdPt, ← per_add_self hn, h1]
  congr 1
  cases ε <;> simp <;> ring

section rev

variable {W : ℕ → List Letter} {i : ℕ} {w : List Letter}

/-- Reversing a word. -/
theorem isPolyMap_rev :
    IsPolyMap (update W i w) (update W i (winv w))
      (fun a => if a.1 = i then (i, (starRingEnd ℂ) a.2) else a) := by
  have hlen : (winv w).length = w.length := by simp [winv]
  have hne : winv w ≠ [] ↔ w ≠ [] := by simp [winv]
  have hget : ∀ p, p < w.length → (winv w)[p]? = (w[w.length - 1 - p]?).map linv := fun p hp => by
    rw [winv, List.getElem?_map, List.getElem?_reverse hp]
  refine IsPolyMap.of_sides (Y := ∅) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [continuousOn_prod_of_discrete_left]
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [ite_true]
      exact (Continuous.prodMk continuous_const Complex.continuous_conj).continuousOn
    · simp only [ite_eq_right hj]
      exact (Continuous.prodMk continuous_const continuous_id).continuousOn
  · rintro ⟨j, z⟩ ⟨h1, h2⟩
    by_cases hj : j = i
    · subst hj
      simp only [ite_true]
      refine ⟨by simpa [hne] using h1, by simpa using h2⟩
    · simp only [ite_eq_right hj]
      refine ⟨?_, h2⟩
      simpa [update_ne hj] using h1
  · rintro ⟨j, z⟩ ⟨h1, h2⟩
    by_cases hj : j = i
    · subst hj
      refine ⟨(j, (starRingEnd ℂ) z), ⟨by simpa [hne] using h1, by simpa using h2⟩, ?_⟩
      simp
    · refine ⟨(j, z), ⟨by simpa [update_ne hj] using h1, h2⟩, ?_⟩
      simp [hj]
  · rintro ⟨j, z⟩ ⟨-, h2⟩ ⟨j', z'⟩ ⟨-, h3⟩ he
    have h1 : j = j' := by
      by_cases hj : j = i <;> by_cases hj' : j' = i
      · rw [hj, hj']
      · simp only [ite_eq_left hj, ite_eq_right hj', Prod.mk.injEq] at he
        exact absurd he.1.symm hj'
      · simp only [ite_eq_right hj, ite_eq_left hj', Prod.mk.injEq] at he
        exact absurd he.1 hj
      · simp only [ite_eq_right hj, ite_eq_right hj', Prod.mk.injEq] at he
        exact he.1
    subst h1
    have h4 : z = z' := by
      by_cases hj : j = i
      · simp only [ite_eq_left hj, Prod.mk.injEq, true_and] at he
        exact (starRingEnd ℂ).injective he
      · simp only [ite_eq_right hj, Prod.mk.injEq] at he
        exact he.2
    rw [h4]
    exact .refl _
  · intro j p k ε h _
    by_cases hj : j = i
    · subst hj
      rw [update_self] at h
      have hp : p < w.length := hlen ▸ (List.getElem?_eq_some_iff.mp h).1
      rw [hget p hp] at h
      obtain ⟨l, hl, hl'⟩ := Option.map_eq_some_iff.mp h
      refine ⟨j, w.length - 1 - p, !ε, ?_, fun t _ => ?_⟩
      · rw [update_self, hl]
        obtain ⟨a, b⟩ := l
        simp only [linv, Prod.mk.injEq] at hl'
        simp [← hl'.1, ← hl'.2]
      · simp only [ite_true, update_self, hlen, conj_sdPt hp]
    · refine ⟨j, p, ε, by rw [update_ne hj] at h ⊢; exact h, fun t _ => ?_⟩
      simp only [ite_eq_right hj, update_ne hj]
  · intro j p k ε h
    by_cases hj : j = i
    · subst hj
      rw [update_self] at h
      have hp : p < w.length := (List.getElem?_eq_some_iff.mp h).1
      have hq : w.length - 1 - p < w.length := by omega
      have hq' : w.length - 1 - (w.length - 1 - p) = p := by omega
      refine ⟨j, w.length - 1 - p, !ε, ?_, fun t _ => ?_⟩
      · rw [update_self, hget _ hq, hq', h]
        simp [linv]
      · simp only [ite_true, update_self, hlen]
        rw [conj_sdPt hq, hq']
        simp
    · refine ⟨j, p, ε, by rw [update_ne hj] at h ⊢; exact h, fun t _ => ?_⟩
      simp only [ite_eq_right hj, update_ne hj]
  · intro _ _ _ _ _ _ _ _ h
    exact absurd h (notMem_empty _)

end rev

/-- The label `y` does not occur in `W`. -/
def FreshIn (W : ℕ → List Letter) (y : ℕ) : Prop := ∀ i, ∀ l ∈ W i, l.1 ≠ y

section cut

variable {W : ℕ → List Letter} {i j : ℕ} {u v : List Letter} {y : ℕ}

/-- The values of the map of discs of a cut, on the sides. -/
theorem up_side {a l : ℕ} (ha : 0 < a) {p : ℕ} (_hp : p < l) (ε : Bool) {t : ℝ} (ht : t ∈ Icc
  (0 : ℝ) 1) :
    upLoop a l (a + p + if ε then t else 1 - t) = cis' (Real.pi * (p + if ε then t else 1 - t) / l)
      := by
  have hs : 0 ≤ if ε then t else 1 - t := by
    cases ε
    · simp [ht.2]
    · simp [ht.1]
  rw [upLoop_ge ha (by have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
                       linarith)]
  congr 2
  ring

/-- The value of a side parameter. -/
noncomputable def sv (ε : Bool) (t : ℝ) : ℝ := if ε then t else 1 - t

theorem sv_mem (ε : Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : sv ε t ∈ Icc (0 : ℝ) 1 := by
  cases ε
  · simp only [sv, Bool.false_eq_true, ite_false]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · simpa [sv] using ht

theorem cis'_neg_eq (θ : ℝ) : - cis' θ = cis' (θ - Real.pi) := by
  have := cis'_add_pi (θ - Real.pi)
  rw [sub_add_cancel] at this
  rw [this, neg_neg]

private theorem cut_side_parameters {k l : ℕ} (hl0 : 0 < l) (e : Bool)
    {Φ₁ Φ₂ Ψ Ψ' : ℂ → ℂ}
    (v₁ : ∀ x ∈ Icc (0 : ℝ) (k + 1 : ℕ), Φ₁ (per (k + 1) x) = upLoop 1 k x)
    (v₂ : ∀ x ∈ Icc (0 : ℝ) (l + 1 : ℕ), Φ₂ (per (l + 1) x) = upLoop 1 l x)
    (vΨ : ∀ x ∈ Icc (0 : ℝ) (l + k : ℕ), Ψ (per (l + k) x) = circLoop l k x)
    (m3 : LeftInvOn Ψ' Ψ (closedBall 0 1)) :
    (∀ p ε t, p < k → t ∈ Icc (0 : ℝ) 1 →
      Ψ' (-Φ₁ (sdPt (k + 1) (p + 1) ε t)) = sdPt (l + k) (l + p) ε t) ∧
    (∀ p ε t, p < l → t ∈ Icc (0 : ℝ) 1 →
      Ψ' (Φ₂ (sdPt (l + 1) (p + 1) ε t)) = sdPt (l + k) p ε t) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, -Φ₁ (sdPt (k + 1) 0 e t) = ((1 - 2 * sv e t : ℝ) : ℂ)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, Φ₂ (sdPt (l + 1) 0 (!e) t) = ((1 - 2 * sv e t : ℝ) : ℂ)) := by
  have hsub : ∀ {l : ℕ} {p : ℕ}, p < l → ∀ {s : ℝ}, s ∈ Icc (0 : ℝ) 1 →
      ((p + 1 : ℕ) : ℝ) + s ∈ Icc (0 : ℝ) ((l + 1 : ℕ) : ℝ) := fun {l p} hp {s} hs => by
    have h1 : ((p + 1 : ℕ) : ℝ) ≤ l := by exact_mod_cast hp
    constructor
    · have : (0 : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith [hs.1]
    · push_cast at h1 ⊢
      linarith [hs.2]
  have s₁ : ∀ p ε t, p < k → t ∈ Icc (0 : ℝ) 1 →
      Ψ' (-Φ₁ (sdPt (k + 1) (p + 1) ε t)) = sdPt (l + k) (l + p) ε t := by
    intro p ε t hp ht
    have hs := sv_mem ε ht
    have h1 := v₁ _ (hsub hp hs)
    have h2 := up_side (a := 1) (l := k) one_pos hp ε ht
    have h3 : Ψ (sdPt (l + k) (l + p) ε t) = -Φ₁ (sdPt (k + 1) (p + 1) ε t) := by
      have h4 : ((l + p : ℕ) : ℝ) + sv ε t ∈ Icc (0 : ℝ) ((l + k : ℕ) : ℝ) := by
        have h5 : ((p + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hp
        push_cast at h5 ⊢
        have : (0 : ℝ) ≤ l := Nat.cast_nonneg _
        have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h6 := vΨ _ h4
      have h7 : sdPt (k + 1) (p + 1) ε t = per (k + 1) (((p + 1 : ℕ) : ℝ) + sv ε t) := rfl
      rw [h7, h1]
      have h8 : sdPt (l + k) (l + p) ε t = per (l + k) (((l + p : ℕ) : ℝ) + sv ε t) := rfl
      rw [h8, h6, circLoop_ge hl0 (by
        push_cast
        have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
        linarith [hs.1])]
      have h9 : upLoop 1 k (((p + 1 : ℕ) : ℝ) + sv ε t) = cis' (Real.pi * (p + sv ε t) / k) := by
        have e : ((p + 1 : ℕ) : ℝ) + sv ε t = ((1 : ℕ) : ℝ) + p + if ε then t else 1 - t := by
          unfold sv
          push_cast
          ring
        rw [e, h2]
        rfl
      rw [h9, cis'_neg_eq]
      congr 2
      push_cast
      ring
    rw [← h3]
    exact m3 (mem_closedBall_zero_iff.mpr (norm_per _ _).le)
  have s₂ : ∀ p ε t, p < l → t ∈ Icc (0 : ℝ) 1 →
      Ψ' (Φ₂ (sdPt (l + 1) (p + 1) ε t)) = sdPt (l + k) p ε t := by
    intro p ε t hp ht
    have hs := sv_mem ε ht
    have h1 := v₂ _ (hsub hp hs)
    have h2 := up_side (a := 1) (l := l) one_pos hp ε ht
    have h3 : Ψ (sdPt (l + k) p ε t) = Φ₂ (sdPt (l + 1) (p + 1) ε t) := by
      have h5 : ((p + 1 : ℕ) : ℝ) ≤ l := by exact_mod_cast hp
      have h4 : (p : ℝ) + sv ε t ∈ Icc (0 : ℝ) ((l + k : ℕ) : ℝ) := by
        push_cast at h5 ⊢
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h6 := vΨ _ h4
      have h7 : sdPt (l + 1) (p + 1) ε t = per (l + 1) (((p + 1 : ℕ) : ℝ) + sv ε t) := rfl
      rw [h7, h1]
      have h8 : sdPt (l + k) p ε t = per (l + k) ((p : ℝ) + sv ε t) := rfl
      rw [h8, h6, circLoop_le (by push_cast at h5; linarith [hs.2])]
      have h9 : upLoop 1 l (((p + 1 : ℕ) : ℝ) + sv ε t) = cis' (Real.pi * (p + sv ε t) / l) := by
        have e : ((p + 1 : ℕ) : ℝ) + sv ε t = ((1 : ℕ) : ℝ) + p + if ε then t else 1 - t := by
          unfold sv
          push_cast
          ring
        rw [e, h2]
        rfl
      rw [h9]
    rw [← h3]
    exact m3 (mem_closedBall_zero_iff.mpr (norm_per _ _).le)
  have hv₁ : ∀ t ∈ Icc (0 : ℝ) 1, -Φ₁ (sdPt (k + 1) 0 e t) = ((1 - 2 * sv e t : ℝ) : ℂ) := by
    intro t ht
    have hs := sv_mem e ht
    have h1 : sdPt (k + 1) 0 e t = per (k + 1) (sv e t) := by simp [sdPt, sv]
    rw [h1, v₁ _ ⟨hs.1, by push_cast; linarith [hs.2, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]⟩,
      upLoop_le (by simpa using hs.2)]
    push_cast
    ring
  have hv₂ : ∀ t ∈ Icc (0 : ℝ) 1, Φ₂ (sdPt (l + 1) 0 (!e) t) = ((1 - 2 * sv e t : ℝ) : ℂ) := by
    intro t ht
    have hs := sv_mem e ht
    have h1 : sdPt (l + 1) 0 (!e) t = per (l + 1) (1 - sv e t) := by
      cases e <;> simp [sdPt, sv]
    rw [h1, v₂ (1 - sv e t) ⟨by linarith [hs.2], by
      push_cast
      linarith [hs.1, (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]⟩, upLoop_le (by simpa using hs.1)]
    push_cast
    ring
  exact ⟨s₁, s₂, hv₁, hv₂⟩

private theorem cut_cross_face_relation {W1 : ℕ → List Letter} {k l : ℕ}
    (e : Bool) (hij : j ≠ i) (e1 : W1 i = (y, e) :: u) (e2 : W1 j = (y, !e) :: v)
    (hlen1 : (W1 i).length = k + 1) (hlen2 : (W1 j).length = l + 1)
    {Φ₁ Φ₂ Ψ' : ℂ → ℂ}
    (hDΦ₁ : ∀ z ∈ closedBall (0 : ℂ) 1, -Φ₁ z ∈ closedBall (0 : ℂ) 1 ∧ (-Φ₁ z).im ≤ 0)
    (hDΦ₂ : ∀ z ∈ closedBall (0 : ℂ) 1, Φ₂ z ∈ closedBall (0 : ℂ) 1 ∧ 0 ≤ (Φ₂ z).im)
    (hinj₁ : InjOn Φ₁ (closedBall (0 : ℂ) 1))
    (hinj₂ : InjOn Φ₂ (closedBall (0 : ℂ) 1))
    (hinjΨ : InjOn Ψ' (closedBall (0 : ℂ) 1))
    (hv₁ : ∀ t ∈ Icc (0 : ℝ) 1, -Φ₁ (sdPt (k + 1) 0 e t) = ((1 - 2 * sv e t : ℝ) : ℂ))
    (hv₂ : ∀ t ∈ Icc (0 : ℝ) 1, Φ₂ (sdPt (l + 1) 0 (!e) t) = ((1 - 2 * sv e t : ℝ) : ℂ))
    {z z' : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) (hz' : z' ∈ closedBall (0 : ℂ) 1)
    (he : Ψ' (-Φ₁ z) = Ψ' (Φ₂ z')) : PRel W1 (i, z) (j, z') := by
  have h1 := hinjΨ (hDΦ₁ z hz).1 (hDΦ₂ z' hz').1 he
  have h2 := (hDΦ₁ z hz).2
  have h3 := (hDΦ₂ z' hz').2
  rw [h1] at h2
  have h4 : (Φ₂ z').im = 0 := le_antisymm h2 h3
  have h5 : ‖Φ₂ z'‖ ≤ 1 := mem_closedBall_zero_iff.mp (hDΦ₂ z' hz').1
  have h6 : |(Φ₂ z').re| ≤ 1 := (Complex.abs_re_le_norm _).trans h5
  obtain ⟨h7, h8⟩ := abs_le.mp h6
  have hs0 : (1 - (Φ₂ z').re) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  let t : ℝ := sv e ((1 - (Φ₂ z').re) / 2)
  have ht : t ∈ Icc (0 : ℝ) 1 := sv_mem e hs0
  have hst : sv e t = (1 - (Φ₂ z').re) / 2 := by
    simp only [t]
    cases e <;> simp [sv]
  have h9 : Φ₂ z' = ((1 - 2 * sv e t : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [hst, Complex.ofReal_re]
      ring
    · simp [h4]
  have ha : z = sdPt (k + 1) 0 e t := by
    refine hinj₁ hz (mem_closedBall_zero_iff.mpr (norm_per _ _).le) ?_
    have := hv₁ t ht
    rw [← neg_inj, this, h1, h9]
  have hb : z' = sdPt (l + 1) 0 (!e) t := by
    refine hinj₂ hz' (mem_closedBall_zero_iff.mpr (norm_per _ _).le) ?_
    rw [hv₂ t ht, h9]
  refine .rel _ _ ⟨i, j, 0, 0, y, e, !e, t, by rw [e1]; rfl, by rw [e2]; rfl,
    fun he' => hij (Prod.mk.inj he').1.symm, ht, ?_, ?_⟩
  · rw [hlen1, ha]
  · rw [hlen2, hb]

private theorem cut_uncut_side_correspondence
    {W0 W1 : ℕ → List Letter} (e : Bool) (hWj : W j = [])
    (e1 : W1 i = (y, e) :: u) (e2 : W1 j = (y, !e) :: v)
    (e3 : ∀ s, s ≠ i → s ≠ j → W1 s = W s)
    (e4 : W0 i = v ++ u) (e5 : ∀ s, s ≠ i → W0 s = W s)
    {θ : ℕ × ℂ → ℕ × ℂ} :
    let k := u.length
    let l := v.length
    (∀ p ε t, p < k → t ∈ Icc (0 : ℝ) 1 →
      θ (i, sdPt (k + 1) (p + 1) ε t) = (i, sdPt (l + k) (l + p) ε t)) →
    (∀ p ε t, p < l → t ∈ Icc (0 : ℝ) 1 →
      θ (j, sdPt (l + 1) (p + 1) ε t) = (i, sdPt (l + k) p ε t)) →
    (∀ s z, s ≠ i → s ≠ j → θ (s, z) = (s, z)) →
    (∀ s p c ε, (W1 s)[p]? = some (c, ε) → c ∉ ({y} : Set ℕ) → ∃ i' p', (W0 i')[p']? = some (c, ε) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, θ (s, sdPt (W1 s).length p ε t) = (i', sdPt (W0 i').length p' ε t)) ∧
    (∀ i' p' c ε, (W0 i')[p']? = some (c, ε) → ∃ s p, (W1 s)[p]? = some (c, ε) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, θ (s, sdPt (W1 s).length p ε t) = (i', sdPt (W0 i').length p' ε t)) := by
  intro k l s₁ s₂ θo
  have hlen0 : (W0 i).length = l + k := by rw [e4, List.length_append]
  have hlen1 : (W1 i).length = k + 1 := by rw [e1, List.length_cons]
  have hlen2 : (W1 j).length = l + 1 := by rw [e2, List.length_cons]
  have hdown : ∀ s p c ε, (W1 s)[p]? = some (c, ε) → c ∉ ({y} : Set ℕ) → ∃ i' p', (W0 i')[p']?
    = some (c, ε) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, θ (s, sdPt (W1 s).length p ε t) = (i', sdPt (W0 i').length p' ε t) := by
    intro s p c ε h hc
    by_cases h1 : s = i
    · subst h1
      rw [e1] at h
      cases p with
      | zero =>
        have : (y, e) = (c, ε) := by simpa using h
        exact absurd (Prod.mk.inj this).1.symm hc
      | succ p =>
        rw [List.getElem?_cons_succ] at h
        have hp : p < k := (List.getElem?_eq_some_iff.mp h).1
        refine ⟨s, l + p, ?_, fun t ht => ?_⟩
        · rw [e4, List.getElem?_append_right (by omega)]
          simpa [l] using h
        · rw [hlen1, hlen0, s₁ p ε t hp ht]
    by_cases h2 : s = j
    · subst h2
      rw [e2] at h
      cases p with
      | zero =>
        have : (y, !e) = (c, ε) := by simpa using h
        exact absurd (Prod.mk.inj this).1.symm hc
      | succ p =>
        rw [List.getElem?_cons_succ] at h
        have hp : p < l := (List.getElem?_eq_some_iff.mp h).1
        refine ⟨i, p, ?_, fun t ht => ?_⟩
        · rw [e4, List.getElem?_append_left hp]
          exact h
        · rw [hlen2, hlen0, s₂ p ε t hp ht]
    · refine ⟨s, p, by rwa [e5 s h1, ← e3 s h1 h2], fun t _ => ?_⟩
      rw [θo _ _ h1 h2, e3 s h1 h2, e5 s h1]
  have hup : ∀ i' p' c ε, (W0 i')[p']? = some (c, ε) → ∃ s p, (W1 s)[p]? = some (c, ε) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, θ (s, sdPt (W1 s).length p ε t) = (i', sdPt (W0 i').length p' ε t) := by
    intro s p c ε h
    by_cases h1 : s = i
    · subst h1
      rw [e4] at h
      rw [hlen0]
      by_cases hp : p < l
      · refine ⟨j, p + 1, ?_, fun t ht => ?_⟩
        · rw [e2, List.getElem?_cons_succ]
          rwa [List.getElem?_append_left hp] at h
        · rw [hlen2, s₂ p ε t hp ht]
      · have hp' : l ≤ p := not_lt.mp hp
        obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp'
        rw [List.getElem?_append_right (by omega)] at h
        have h2 : u[q]? = some (c, ε) := by simpa [l] using h
        have hq : q < k := (List.getElem?_eq_some_iff.mp h2).1
        refine ⟨s, q + 1, ?_, fun t ht => ?_⟩
        · rw [e1, List.getElem?_cons_succ]
          exact h2
        · rw [hlen1, s₁ q ε t hq ht]
    by_cases h2 : s = j
    · subst h2
      rw [e5 s h1, hWj] at h
      simp at h
    · refine ⟨s, p, by rwa [e3 s h1 h2, ← e5 s h1], fun t _ => ?_⟩
      rw [θo _ _ h1 h2, e3 s h1 h2, e5 s h1]
  exact ⟨hdown, hup⟩

/-- Cutting a word along a chord, or gluing two words along a letter. -/
theorem exists_isPolyMap_cut (e : Bool) (hij : j ≠ i) (hWj : W j = []) (hu : u ≠ []) (hv : v ≠ [])
    (hy : FreshIn (update W i (v ++ u)) y) :
    ∃ θ, IsPolyMap (update W i (v ++ u)) (update (update W i ((y, e) :: u)) j ((y, !e) :: v)) θ ∧
      (∀ s p c ε, (update (update W i ((y, e) :: u)) j ((y, !e) :: v) s)[p]? = some (c, ε) → c ∉
        ({y} : Set ℕ) →
        ∃ i' p', (update W i (v ++ u) i')[p']? = some (c, ε) ∧ ∀ t ∈ Icc (0 : ℝ) 1,
          θ (s, sdPt (update (update W i ((y, e) :: u)) j ((y, !e) :: v) s).length p ε t) =
            (i', sdPt (update W i (v ++ u) i').length p' ε t)) ∧
      (∀ i' p' c ε, (update W i (v ++ u) i')[p']? = some (c, ε) →
        ∃ s p, (update (update W i ((y, e) :: u)) j ((y, !e) :: v) s)[p]? = some (c, ε) ∧ ∀ t ∈ Icc
          (0 : ℝ) 1,
          θ (s, sdPt (update (update W i ((y, e) :: u)) j ((y, !e) :: v) s).length p ε t) =
            (i', sdPt (update W i (v ++ u) i').length p' ε t)) := by
  classical
  set k := u.length with hk
  set l := v.length with hl
  have hk0 : 0 < k := List.length_pos_iff.mpr hu
  have hl0 : 0 < l := List.length_pos_iff.mpr hv
  obtain ⟨Φ₁, Φ₁', m₁, v₁⟩ := exists_up_map (a := 1) (l := k) one_pos hk0
  obtain ⟨Φ₂, Φ₂', m₂, v₂⟩ := exists_up_map (a := 1) (l := l) one_pos hl0
  obtain ⟨Ψ, Ψ', m, vΨ⟩ := exists_circ_map (l := l) (k := k) hl0 hk0
  rw [Nat.add_comm 1 k] at v₁
  rw [Nat.add_comm 1 l] at v₂
  set W0 := update W i (v ++ u) with hW0
  set W1 := update (update W i ((y, e) :: u)) j ((y, !e) :: v) with hW1
  have e1 : W1 i = (y, e) :: u := by
    rw [hW1, update_of_ne hij.symm, update_self]
  have e2 : W1 j = (y, !e) :: v := by rw [hW1, update_self]
  have e3 : ∀ s, s ≠ i → s ≠ j → W1 s = W s := fun s h1 h2 => by
    rw [hW1, update_of_ne h2, update_of_ne h1]
  have e4 : W0 i = v ++ u := by rw [hW0, update_self]
  have e5 : ∀ s, s ≠ i → W0 s = W s := fun s h => by rw [hW0, update_of_ne h]
  have hyu : ∀ l' ∈ u, l'.1 ≠ y := fun l' h => hy i l' (by rw [e4]; exact List.mem_append_right _ h)
  have hyv : ∀ l' ∈ v, l'.1 ≠ y := fun l' h => hy i l' (by rw [e4]; exact List.mem_append_left _ h)
  have hlen0 : (W0 i).length = l + k := by rw [e4, List.length_append]
  have hlen1 : (W1 i).length = k + 1 := by rw [e1, List.length_cons]
  have hlen2 : (W1 j).length = l + 1 := by rw [e2, List.length_cons]
  have hDΦ₁ : ∀ z ∈ closedBall (0 : ℂ) 1, -Φ₁ z ∈ closedBall (0 : ℂ) 1 ∧ (-Φ₁ z).im ≤ 0 := fun z hz
    => by
    obtain ⟨h1, h2⟩ := m₁.1 hz
    refine ⟨by simpa using h1, ?_⟩
    simp only [one_mul] at h2
    simpa using h2
  have hDΦ₂ : ∀ z ∈ closedBall (0 : ℂ) 1, Φ₂ z ∈ closedBall (0 : ℂ) 1 ∧ 0 ≤ (Φ₂ z).im := fun z hz
    => by
    obtain ⟨h1, h2⟩ := m₂.1 hz
    refine ⟨by simpa using h1, ?_⟩
    simpa using h2
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := id m
  obtain ⟨s₁, s₂, hv₁, hv₂⟩ := cut_side_parameters (Ψ' := Ψ') hl0 e v₁ v₂ vΨ m3
  let θ : ℕ × ℂ → ℕ × ℂ := fun a =>
    if a.1 = i then (i, Ψ' (-Φ₁ a.2)) else if a.1 = j then (i, Ψ' (Φ₂ a.2)) else a
  have θi : ∀ z, θ (i, z) = (i, Ψ' (-Φ₁ z)) := fun z => by simp [θ]
  have θj : ∀ z, θ (j, z) = (i, Ψ' (Φ₂ z)) := fun z => by simp [θ, hij]
  have θo : ∀ s z, s ≠ i → s ≠ j → θ (s, z) = (s, z) := fun s z h1 h2 => by simp [θ, h1, h2]
  have hball : ∀ {V : ℕ → List Letter} {s : ℕ} {z : ℂ}, (s, z) ∈ Dsk V → z ∈ closedBall (0 : ℂ) 1 :=
    fun h => mem_closedBall_zero_iff.mpr h.2
  have hne0 : W0 i ≠ [] := by
    rw [e4]
    simp [hu]
  have hinj₁ : ∀ {z z'}, z ∈ closedBall (0 : ℂ) 1 → z' ∈ closedBall (0 : ℂ) 1 → Φ₁ z = Φ₁ z' → z
    = z' :=
    fun hz hz' he => by rw [← m₁.2.2.1 hz, ← m₁.2.2.1 hz', he]
  have hinj₂ : ∀ {z z'}, z ∈ closedBall (0 : ℂ) 1 → z' ∈ closedBall (0 : ℂ) 1 → Φ₂ z = Φ₂ z' → z
    = z' :=
    fun hz hz' he => by rw [← m₂.2.2.1 hz, ← m₂.2.2.1 hz', he]
  have hinjΨ : ∀ {z z'}, z ∈ closedBall (0 : ℂ) 1 → z' ∈ closedBall (0 : ℂ) 1 → Ψ' z = Ψ' z' → z
    = z' :=
    fun hz hz' he => by rw [← m4 hz, ← m4 hz', he]
  have hmix : ∀ z z', z ∈ closedBall (0 : ℂ) 1 → z' ∈ closedBall (0 : ℂ) 1 →
      Ψ' (-Φ₁ z) = Ψ' (Φ₂ z') → PRel W1 (i, z) (j, z') :=
    fun _ _ => cut_cross_face_relation e hij e1 e2 hlen1 hlen2 hDΦ₁ hDΦ₂
      (fun {_} hz {_} hz' h => hinj₁ hz hz' h) (fun {_} hz {_} hz' h => hinj₂ hz hz' h)
      (fun {_} hz {_} hz' h => hinjΨ hz hz' h) hv₁ hv₂
  obtain ⟨hdown, hup⟩ := cut_uncut_side_correspondence e hWj e1 e2 e3 e4 e5
    (fun p ε t hp ht => by rw [θi, s₁ p ε t hp ht])
    (fun p ε t hp ht => by rw [θj, s₂ p ε t hp ht]) θo
  refine ⟨θ, IsPolyMap.of_sides (Y := {y}) ?_ ?_ ?_ ?_ (fun s p c ε h hc => ?_) (fun i' p' c ε h
    => ?_) ?_, hdown, hup⟩
  · rw [continuousOn_prod_of_discrete_left]
    intro s
    by_cases h1 : s = i
    · subst h1
      have hs : (fun z => θ (s, z)) = fun z => (s, Ψ' (-Φ₁ z)) := funext θi
      rw [hs]
      refine continuousOn_const.prodMk (m6.comp (m₁.2.2.2.2.1.neg.mono fun z hz => hball hz) ?_)
      exact fun z hz => (hDΦ₁ z (hball hz)).1
    by_cases h2 : s = j
    · subst h2
      have hs : (fun z => θ (s, z)) = fun z => (i, Ψ' (Φ₂ z)) := funext θj
      rw [hs]
      refine continuousOn_const.prodMk (m6.comp (m₂.2.2.2.2.1.mono fun z hz => hball hz) ?_)
      exact fun z hz => (hDΦ₂ z (hball hz)).1
    · have hs : (fun z => θ (s, z)) = fun z => (s, z) := funext fun z => θo s z h1 h2
      rw [hs]
      exact (Continuous.prodMk continuous_const continuous_id).continuousOn
  · rintro ⟨s, z⟩ hz
    by_cases h1 : s = i
    · subst h1
      rw [θi]
      exact ⟨hne0, mem_closedBall_zero_iff.mp (m2 (hDΦ₁ z (hball hz)).1)⟩
    by_cases h2 : s = j
    · subst h2
      rw [θj]
      exact ⟨hne0, mem_closedBall_zero_iff.mp (m2 (hDΦ₂ z (hball hz)).1)⟩
    · rw [θo s z h1 h2]
      refine ⟨?_, hz.2⟩
      have := hz.1
      rwa [e3 s h1 h2, ← e5 s h1] at this
  · rintro ⟨s, z⟩ hz
    by_cases h1 : s = i
    · subst h1
      have h3 : Ψ z ∈ closedBall (0 : ℂ) 1 := m1 (hball hz)
      rcases le_total (Ψ z).im 0 with h4 | h4
      · have h5 : - Ψ z ∈ halfD 1 := ⟨by simpa using mem_closedBall_zero_iff.mp h3, by simpa using
        h4⟩
        refine ⟨(s, Φ₁' (- Ψ z)), ⟨by rw [e1]; simp, mem_closedBall_zero_iff.mp (m₁.2.1 h5)⟩, ?_⟩
        rw [θi, m₁.2.2.2.1 h5, neg_neg, m3 (hball hz)]
      · have h5 : Ψ z ∈ halfD 1 := ⟨mem_closedBall_zero_iff.mp h3, by simpa using h4⟩
        refine ⟨(j, Φ₂' (Ψ z)), ⟨by rw [e2]; simp, mem_closedBall_zero_iff.mp (m₂.2.1 h5)⟩, ?_⟩
        rw [θj, m₂.2.2.2.1 h5, m3 (hball hz)]
    by_cases h2 : s = j
    · subst h2
      exact absurd (by rw [e5 s h1]; exact hWj) hz.1
    · refine ⟨(s, z), ⟨?_, hz.2⟩, θo s z h1 h2⟩
      have := hz.1
      rwa [e5 s h1, ← e3 s h1 h2] at this
  · rintro ⟨s, z⟩ hz ⟨s', z'⟩ hz' he
    by_cases h1 : s = i <;> by_cases h2 : s = j <;> by_cases h3 : s' = i <;> by_cases h4 : s' = j
    all_goals try (exfalso; subst_vars; exact hij rfl)
    · subst h1 h3
      rw [θi, θi] at he
      have := hinj₁ (hball hz) (hball hz') (neg_injective (hinjΨ (hDΦ₁ _ (hball hz)).1 (hDΦ₁ _
        (hball hz')).1
        (Prod.mk.inj he).2))
      rw [this]
      exact .refl _
    · subst h1 h4
      rw [θi, θj] at he
      exact hmix _ _ (hball hz) (hball hz') (Prod.mk.inj he).2
    · subst h1
      rw [θi, θo s' z' h3 h4] at he
      exact absurd (Prod.mk.inj he).1.symm h3
    · subst h2 h3
      rw [θj, θi] at he
      exact (hmix _ _ (hball hz') (hball hz) (Prod.mk.inj he).2.symm).symm
    · subst h2 h4
      rw [θj, θj] at he
      have := hinj₂ (hball hz) (hball hz') (hinjΨ (hDΦ₂ _ (hball hz)).1 (hDΦ₂ _ (hball hz')).1
        (Prod.mk.inj he).2)
      rw [this]
      exact .refl _
    · subst h2
      rw [θj, θo s' z' h3 h4] at he
      exact absurd (Prod.mk.inj he).1.symm h3
    · subst h3
      rw [θo s z h1 h2, θi] at he
      exact absurd (Prod.mk.inj he).1 h1
    · subst h4
      rw [θo s z h1 h2, θj] at he
      exact absurd (Prod.mk.inj he).1 h1
    · rw [θo s z h1 h2, θo s' z' h3 h4] at he
      rw [he]
      exact .refl _
  · obtain ⟨a, b, h1, h2⟩ := hdown s p c ε h hc
    exact ⟨a, b, ε, h1, h2⟩
  · obtain ⟨a, b, h1, h2⟩ := hup i' p' c ε h
    exact ⟨a, b, ε, h1, h2⟩
  · have hside : ∀ s q ε, (W1 s)[q]? = some (y, ε) → ∀ t ∈ Icc (0 : ℝ) 1,
        θ (s, sdPt (W1 s).length q ε t) = (i, Ψ' ((1 - 2 * sv e t : ℝ) : ℂ)) := by
      intro s q ε h t ht
      by_cases h1 : s = i
      · subst h1
        rw [e1] at h
        cases q with
        | zero =>
          have : ε = e := by simpa using h.symm
          subst this
          rw [θi, hlen1, hv₁ t ht]
        | succ q =>
          rw [List.getElem?_cons_succ] at h
          exact absurd rfl (hyu _ (List.mem_of_getElem? h))
      by_cases h2 : s = j
      · subst h2
        rw [e2] at h
        cases q with
        | zero =>
          have : ε = !e := by simpa using h.symm
          subst this
          rw [θj, hlen2, hv₂ t ht]
        | succ q =>
          rw [List.getElem?_cons_succ] at h
          exact absurd rfl (hyv _ (List.mem_of_getElem? h))
      · rw [e3 s h1 h2] at h
        have h3 := hy s _ (List.mem_of_getElem? (by rw [e5 s h1]; exact h))
        exact absurd rfl h3
    intro s s' q q' c ε ε' t hc h1 h2 ht
    obtain rfl : c = y := hc
    rw [hside s q ε h1 t ht, hside s' q' ε' h2 t ht]

end cut

end GraphMinor.Surface
