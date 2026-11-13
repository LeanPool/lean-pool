/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.GaussianReflection
public import LeanPool.ApollonianSuperharmonic.GaussianTranslation
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import LeanPool.ApollonianSuperharmonic.SimpleGridPath

-- [TABLET NODE: SimpleGridPathEquivariance]

/-!
# SimpleGridPathEquivariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PathEquivariance

private theorem transport :
    ∀ (p : List GaussianInt) (f : GaussianInt → GaussianInt),
      (∀ a b : GaussianInt,
          b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩ →
            f b = f a + 1 ∨ f b = f a - 1 ∨ f b = f a + ⟨0, 1⟩ ∨ f b = f a - ⟨0, 1⟩) →
        (∀ a b : GaussianInt,
            ∀ l₁ l₂ : List GaussianInt,
              p = l₁ ++ a :: b :: l₂ →
                b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
          ∀ a b : GaussianInt,
            ∀ l₁ l₂ : List GaussianInt,
              p.map f = l₁ ++ a :: b :: l₂ →
                b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩ := by
  classical
  intro p f hstep hp
  induction p with
  | nil =>
    intro a b l₁ l₂ h
    cases l₁ <;> cases l₂ <;> simp_all
  | cons x xs ih =>
    cases xs with
    | nil =>
      intro a b l₁ l₂ h
      cases l₁ <;> cases l₂ <;> simp_all
    | cons y ys =>
      intro a b l₁ l₂ h
      cases l₁ with
      | nil =>
        simp only [List.map_cons, List.nil_append, List.cons.injEq] at h
        rcases h with ⟨rfl, rfl, hys⟩
        exact hstep x y (hp x y [] ys (by simp))
      | cons z zs =>
        simp only [List.map_cons, List.cons_append] at h
        have hz : z = f x := by simpa using (congrArg List.head? h).symm
        subst z
        have htail : (y :: ys).map f = zs ++ a :: b :: l₂ := by
          simpa using h
        apply ih
        · intro c d k m hm
          apply hp c d (x :: k) m
          simp [hm]
        · exact htail

private theorem forward :
    ∀ (f : GaussianInt → GaussianInt),
      Function.Injective f →
        (∀ a b : GaussianInt,
            b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩ →
              f b = f a + 1 ∨ f b = f a - 1 ∨ f b = f a + ⟨0, 1⟩ ∨ f b = f a - ⟨0, 1⟩) →
          ∀ V E,
            SimpleGridPath V E →
              SimpleGridPath (f '' V) ((fun e : Finset GaussianInt => e.image f) '' E) := by
  classical
  have transport := transport
  intro f hf hstep V E path
  rcases path with ⟨p, hnd, hlen, hV, hp, hE⟩
  refine ⟨p.map f, hnd.map hf, ?_, ?_, ?_, ?_⟩
  · simpa using hlen
  · rw [hV]
    ext z
    simp []
  · exact transport p f hstep hp
  · intro e
    constructor
    · rintro ⟨d, hd, rfl⟩
      rcases (hE d).mp hd with ⟨a, b, l₁, l₂, hh, he⟩
      refine ⟨f a, f b, l₁.map f, l₂.map f, ?_, ?_⟩
      · simp [hh]
      · simp [he]
    · rintro ⟨a, b, l₁, l₂, hh, he⟩
      have unmap : ∀ (q : List GaussianInt) (k m : List GaussianInt)
          (a b : GaussianInt),
          q.map f = k ++ f a :: f b :: m →
          ∃ k₀ m₀, q = k₀ ++ a :: b :: m₀ := by
        intro q
        induction q with
        | nil =>
          intro k m a b h
          cases k <;> simp_all
        | cons x xs ih =>
          intro k m a b h
          cases k with
          | nil =>
            simp only [List.map_cons, List.nil_append, List.cons.injEq] at h
            cases xs with
            | nil => simp_all
            | cons y ys =>
              simp only [List.map_cons, List.cons.injEq] at h
              have hxa : x = a := hf h.1
              have hya : y = b := hf h.2.1
              subst a
              subst b
              exact ⟨[], ys, by simp []⟩
          | cons z zs =>
            simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
            have hz : z = f x := h.1.symm
            subst z
            rcases ih zs m a b h.2 with ⟨k₀, m₀, hm⟩
            exact ⟨x :: k₀, m₀, by simp [hm]⟩
      have ha : a ∈ p.map f := by rw [hh]; simp
      have hb : b ∈ p.map f := by rw [hh]; simp
      rcases List.mem_map.mp ha with ⟨a₀, ha₀, haeq⟩
      rcases List.mem_map.mp hb with ⟨b₀, hb₀, hbeq⟩
      rw [← haeq, ← hbeq] at hh he
      rcases unmap p l₁ l₂ a₀ b₀ hh with ⟨k, m, hm⟩
      refine ⟨{a₀, b₀}, (hE {a₀, b₀}).mpr ⟨a₀, b₀, k, m, hm, rfl⟩, ?_⟩
      simp [he]

private theorem backward :
    ∀ (f g : GaussianInt → GaussianInt),
      (∀ x, g (f x) = x) →
        (∀ x, f (g x) = x) →
          (∀ a b : GaussianInt,
              b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩ →
                g b = g a + 1 ∨ g b = g a - 1 ∨ g b = g a + ⟨0, 1⟩ ∨ g b = g a - ⟨0, 1⟩) →
            ∀ V E,
              SimpleGridPath (f '' V) ((fun e : Finset GaussianInt => e.image f) '' E) →
                SimpleGridPath V E := by
  classical
  have forward := forward
  intro f g hgf hfg hstep V E h
  have result := forward g (by
    intro a b hab
    simpa [hfg] using congrArg f hab) hstep (f '' V)
      ((fun e : Finset GaussianInt => e.image f) '' E) h
  simpa [Set.image_image, Finset.image_image, Function.comp_def, hgf, hfg] using result

end PathEquivariance

theorem SimpleGridPathEquivariance :
    ∀ (V : Set GaussianInt) (E : Set (Finset GaussianInt))
      (u : GaussianInt),
    (SimpleGridPath V E ↔
      SimpleGridPath (GaussianTranslation u '' V)
        ((fun e : Finset GaussianInt =>
          e.image (GaussianTranslation u)) '' E)) ∧
    (SimpleGridPath V E ↔
      SimpleGridPath (GaussianQuarterTurn '' V)
        ((fun e : Finset GaussianInt =>
          e.image GaussianQuarterTurn) '' E)) ∧
    (SimpleGridPath V E ↔
      SimpleGridPath (GaussianReflection '' V)
        ((fun e : Finset GaussianInt =>
          e.image GaussianReflection) '' E)) := by
-- BODY
  intro V E u
  have ht : Function.Injective (GaussianTranslation u) := by
    intro a b h
    dsimp [GaussianTranslation] at h
    exact add_right_cancel h
  have hq : Function.Injective GaussianQuarterTurn := by
    intro a b h
    apply Zsqrtd.ext
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.im) h
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.re) h
  have hr : Function.Injective GaussianReflection := by
    intro a b h
    apply Zsqrtd.ext
    · simpa [GaussianReflection] using congrArg (fun z : GaussianInt => z.re) h
    · simpa [GaussianReflection] using congrArg (fun z : GaussianInt => -z.im) h
  have forward := PathEquivariance.forward
  have backward := PathEquivariance.backward
  let qb : GaussianInt → GaussianInt := fun z =>
      ⟨z.im, -z.re⟩
  have hqb : Function.Injective qb := by
    intro a b h
    apply Zsqrtd.ext
    · simpa [qb] using congrArg (fun z : GaussianInt => z.im) h
    · simpa [qb] using congrArg (fun z : GaussianInt => z.re) h
  have transStep : ∀ a b : GaussianInt,
      (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
      (GaussianTranslation u b = GaussianTranslation u a + 1 ∨
       GaussianTranslation u b = GaussianTranslation u a - 1 ∨
       GaussianTranslation u b = GaussianTranslation u a + ⟨0, 1⟩ ∨
       GaussianTranslation u b = GaussianTranslation u a - ⟨0, 1⟩) := by
    intro a b h
    rcases h with h | h | h | h
    · subst b; left; apply Zsqrtd.ext <;> simp [GaussianTranslation]; abel
    · subst b; right; left; apply Zsqrtd.ext <;> simp [GaussianTranslation]; abel
    · subst b; right; right; left; apply Zsqrtd.ext <;> simp [GaussianTranslation]; abel
    · subst b; right; right; right; apply Zsqrtd.ext <;> simp [GaussianTranslation]; abel
  have transBack : ∀ a b : GaussianInt,
      (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
      ((GaussianTranslation (-u)) b = GaussianTranslation (-u) a + 1 ∨
       (GaussianTranslation (-u)) b = GaussianTranslation (-u) a - 1 ∨
       (GaussianTranslation (-u)) b = GaussianTranslation (-u) a + ⟨0, 1⟩ ∨
       (GaussianTranslation (-u)) b = GaussianTranslation (-u) a - ⟨0, 1⟩) := by
    intro a b h
    rcases h with h | h | h | h
    · subst b; left; apply Zsqrtd.ext <;> simp [GaussianTranslation]; abel
    · subst b; right; left; apply Zsqrtd.ext <;> simp [GaussianTranslation]; abel
    · subst b; right; right; left; apply Zsqrtd.ext <;> simp [GaussianTranslation]; abel
    · subst b; right; right; right; apply Zsqrtd.ext <;> simp [GaussianTranslation]; abel
  have transInv₁ : ∀ x, GaussianTranslation (-u) (GaussianTranslation u x) = x := by
    intro x
    simp [GaussianTranslation, add_assoc, add_comm]
  have transInv₂ : ∀ x, GaussianTranslation u (GaussianTranslation (-u) x) = x := by
    intro x
    simp [GaussianTranslation, add_comm]
  have quarterInv₁ : ∀ x, qb (GaussianQuarterTurn x) = x := by
    intro x; apply Zsqrtd.ext <;> simp [qb, GaussianQuarterTurn]
  have quarterInv₂ : ∀ x, GaussianQuarterTurn (qb x) = x := by
    intro x; apply Zsqrtd.ext <;> simp [qb, GaussianQuarterTurn]
  have reflInv : ∀ x, GaussianReflection (GaussianReflection x) = x := by
    intro x; apply Zsqrtd.ext <;> simp [GaussianReflection]
  have reflStep : ∀ a b : GaussianInt,
      (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
      (GaussianReflection b = GaussianReflection a + 1 ∨ GaussianReflection b =
          GaussianReflection a - 1 ∨
       GaussianReflection b = GaussianReflection a + ⟨0, 1⟩ ∨ GaussianReflection b =
           GaussianReflection a - ⟨0, 1⟩) := by
    intro a b h; rcases h with h | h | h | h
    · subst b; left; apply Zsqrtd.ext <;> simp [GaussianReflection]
    · subst b; right; left; apply Zsqrtd.ext <;> simp [GaussianReflection]
    · subst b; right; right; right; apply Zsqrtd.ext <;> simp [GaussianReflection]; abel
    · subst b; right; right; left; apply Zsqrtd.ext <;> simp [GaussianReflection]; abel
  have quarterStep : ∀ a b : GaussianInt,
      (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
      (GaussianQuarterTurn b = GaussianQuarterTurn a + 1 ∨ GaussianQuarterTurn b =
          GaussianQuarterTurn a - 1 ∨
       GaussianQuarterTurn b = GaussianQuarterTurn a + ⟨0, 1⟩ ∨ GaussianQuarterTurn b =
           GaussianQuarterTurn a - ⟨0, 1⟩) := by
    intro a b h; rcases h with h | h | h | h
    · subst b; right; right; left; apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]
    · subst b; right; right; right; apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]
    · subst b; right; left; apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]; abel
    · subst b; left; apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]; abel
  have quarterBackStep : ∀ a b : GaussianInt,
      (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
      (qb b = qb a + 1 ∨ qb b = qb a - 1 ∨ qb b = qb a + ⟨0, 1⟩ ∨ qb b = qb a - ⟨0, 1⟩) := by
    intro a b h; rcases h with h | h | h | h
    · subst b; right; right; right; apply Zsqrtd.ext <;> simp [qb]; abel
    · subst b; right; right; left; apply Zsqrtd.ext <;> simp [qb]; abel
    · subst b; left; apply Zsqrtd.ext <;> simp [qb]
    · subst b; right; left; apply Zsqrtd.ext <;> simp [qb]
  exact ⟨⟨fun h => forward (GaussianTranslation u) ht transStep V E h,
    fun h => backward (GaussianTranslation u) (GaussianTranslation (-u)) transInv₁ transInv₂
        transBack V E h⟩,
    ⟨fun h => forward GaussianQuarterTurn hq quarterStep V E h,
      fun h => backward GaussianQuarterTurn qb quarterInv₁ quarterInv₂ quarterBackStep V E h⟩,
    ⟨fun h => forward GaussianReflection hr reflStep V E h,
      fun h => backward GaussianReflection GaussianReflection reflInv reflInv reflStep V E h⟩⟩

end ApollonianSuperharmonic

end
