/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3723T1AllContactRouting
public import Mathlib.Analysis.Convex.Segment

-- [TABLET NODE: P3913T1RoutedFaceSubdivision]

/-!
# P3913T1RoutedFaceSubdivision

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RoutedSubdivisionProof

private theorem piece_range :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3 : ℕ)),
            Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        ∀ (k : Fin 3), ∀ (r : Fin ((s k).count)), Set.range (fun t : Set.Icc ((s k).time
            r.castSucc) ((s k).time r.succ) =>
            g k ⟨t.1, by
              constructor
              · exact (τ k r.castSucc).property.1.trans t.property.1
              · exact t.property.2.trans (τ k r.succ).property.2⟩) =
            segment Real (w k r.castSucc) (w k r.succ))) := by
  classical
  intro g hi s τ w k r
  let t0 := (s k).time r.castSucc
  let t1 := (s k).time r.succ
  have hlt : t0 < t1 := (s k).strict Fin.castSucc_lt_succ
  let lo := τ k r.castSucc
  let hi := τ k r.succ
  obtain ⟨A, B, hA⟩ := (s k).affine_on r
  have affine (t : Set.Icc t0 t1) :
      g k ⟨t.1, by
        constructor
        · exact lo.property.1.trans t.property.1
        · exact t.property.2.trans hi.property.2⟩ = A + t.1 • B :=
    hA _ t.property.1 t.property.2
  have affine0 : w k r.castSucc = A + t0 • B := by
    exact hA lo (by rfl) hlt.le
  have affine1 : w k r.succ = A + t1 • B := by
    exact hA hi hlt.le (by rfl)
  rw [segment_eq_image]
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    let u := (t.1 - t0) / (t1 - t0)
    have hu0 : 0 ≤ u := by
      dsimp [u]
      apply div_nonneg _ (sub_nonneg.mpr hlt.le)
      linarith [t.property.1]
    have hu1 : u ≤ 1 := by
      dsimp [u]
      rw [div_le_one (sub_pos.mpr hlt)]
      linarith [t.property.2]
    refine ⟨u, ⟨hu0, hu1⟩, ?_⟩
    have hrel : u * (t1 - t0) = t.1 - t0 := by
      dsimp [u]
      exact div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hlt))
    have hlin : t.1 = (1 - u) * t0 + u * t1 := by nlinarith [hrel]
    change (1 - u) • w k r.castSucc + u • w k r.succ =
      g k ⟨t.1, by
        constructor
        · exact lo.property.1.trans t.property.1
        · exact t.property.2.trans hi.property.2⟩
    rw [affine t, affine0, affine1, hlin]
    ext <;> simp [smul_eq_mul] <;> ring
  · rintro ⟨u, hu, hx⟩
    let t : Set.Icc t0 t1 := ⟨t0 + u * (t1 - t0), by
      constructor <;> nlinarith [hu.1, hu.2, hlt]
    ⟩
    refine ⟨t, ?_⟩
    change g k ⟨t.1, by
        constructor
        · exact lo.property.1.trans t.property.1
        · exact t.property.2.trans hi.property.2⟩ = x
    rw [affine t]
    have heq : t.1 = (1 - u) * t0 + u * t1 := by
      dsimp [t]
      ring
    rw [heq]
    have hmid : A + ((1 - u) * t0 + u * t1) • B =
        (1 - u) • (A + t0 • B) + u • (A + t1 • B) := by
      ext <;> simp [smul_eq_mul] <;> ring
    rw [hmid, ← affine0, ← affine1]
    change (fun θ => (1 - θ) • w k r.castSucc + θ • w k r.succ) u = x
    exact hx

private theorem join :
    (by
      classical
      exact
         ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f
             : P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
             (∀ (k : Fin (3 : ℕ)), Function.Injective (g k)) → ((∀ (k : Fin (3 : ℕ)), g k ⟨(0 :
             ℝ), (by norm_num)⟩ = D.position (P.plane.faceVertex f k)) → ((∀ (k : Fin (3 : ℕ)), g
             k ⟨(1 : ℝ), (by norm_num)⟩ = D.position (P.plane.faceVertex f (k +
             (1 : Fin (3 : ℕ))))) → (∀ (s : (k : Fin (3 : ℕ)) → P3723T1PolygonalParameterization
             (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        ∀ (k : Fin (3 : ℕ)), w k (Fin.last (s k).count) = w (k + (1 : Fin (3 : ℕ))) (0 : Fin ((s
            (k + (1 : Fin (3 : ℕ)))).count + (1 : ℕ))))))) := by
  classical
  intro ι P D f g hi h0 h1 s τ w k
  have hlast : τ k (Fin.last (s k).count) = ⟨1, by norm_num⟩ := by
    apply Subtype.ext
    simp [τ, (s k).finish]
  have hfirst : τ (k + 1) 0 = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    simp [τ, (s (k + 1)).start]
  simp only [w, hlast, hfirst]
  exact (h1 k).trans (h0 (k + 1)).symm

private theorem retained :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3 : ℕ)),
            Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m1 := (s 1).count
        let m2 := (s 2).count
        let M := m0 + (m1 + m2)
        let n := M - 3
        ∀ (hM : n + 3 = M),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let q : Fin M → Real × Real :=
          Fin.addCases
            (fun i : Fin m0 => w 0 i.castSucc)
            (Fin.addCases
              (fun i : Fin m1 => w 1 i.castSucc)
              (fun i : Fin m2 => w 2 i.castSucc))
        let p : Fin (n + 3) → Real × Real := fun i => q (Fin.cast hM i)
        (∀ (i : Fin m0), q (Fin.castAdd (m1 + m2) i) = w 0 i.castSucc) → ((∀ (i : Fin m1), q
            (Fin.natAdd m0 (Fin.castAdd m2 i)) = w 1 i.castSucc) → ((∀ (i : Fin m2), q
            (Fin.natAdd m0 (Fin.natAdd m1 i)) = w 2 i.castSucc) → ((∀ (i : Fin M), p (Fin.cast
            hM.symm i) = q i) → ((∀ (k : Fin 3), w k (Fin.last (s k).count) = w (k + 1) 0) → (∀
            (k : Fin (3 : ℕ)), ∀ (i : Fin ((s k).count + (1 : ℕ))), w k i ∈ Set.range p))))))) := by
  classical
  intro g hi s m0 m1 m2 M n hM τ w q p q0 q1 q2 p_at join k i
  fin_cases k
  · refine Fin.lastCases ?_ ?_ i
    · let j : Fin m1 := ⟨0, (s 1).positive⟩
      have hj : j.castSucc = (0 : Fin (m1 + 1)) := by
        apply Fin.ext
        rfl
      refine ⟨Fin.cast hM.symm (Fin.natAdd m0 (Fin.castAdd m2 j)), ?_⟩
      rw [p_at, q1]
      rw [hj]
      exact (join 0).symm
    · intro r
      refine ⟨Fin.cast hM.symm (Fin.castAdd (m1 + m2) r), ?_⟩
      rw [p_at, q0]
      rfl
  · refine Fin.lastCases ?_ ?_ i
    · let j : Fin m2 := ⟨0, (s 2).positive⟩
      have hj : j.castSucc = (0 : Fin (m2 + 1)) := by
        apply Fin.ext
        rfl
      refine ⟨Fin.cast hM.symm (Fin.natAdd m0 (Fin.natAdd m1 j)), ?_⟩
      rw [p_at, q2]
      rw [hj]
      exact (join 1).symm
    · intro r
      refine ⟨Fin.cast hM.symm (Fin.natAdd m0 (Fin.castAdd m2 r)), ?_⟩
      rw [p_at, q1]
      rfl
  · refine Fin.lastCases ?_ ?_ i
    · let j : Fin m0 := ⟨0, (s 0).positive⟩
      have hj : j.castSucc = (0 : Fin (m0 + 1)) := by
        apply Fin.ext
        rfl
      refine ⟨Fin.cast hM.symm (Fin.castAdd (m1 + m2) j), ?_⟩
      rw [p_at, q0]
      rw [hj]
      exact (join 2).symm
    · intro r
      refine ⟨Fin.cast hM.symm (Fin.natAdd m0 (Fin.natAdd m1 r)), ?_⟩
      rw [p_at, q2]
      rfl

private theorem pair_ne :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (f : P.plane.Face), ∀ (g : Fin (3 : ℕ) →
            (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ((k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)) → (
        let v : Fin 3 → ι := P.plane.faceVertex f
        ∀ (i : Fin (3 : ℕ)), ∀ (j : Fin (3 : ℕ)), i ≠ j → ({v i, v (i + (1 : Fin (3 : ℕ)))} : Set
            ι) ≠ {v j, v (j + (1 : Fin (3 : ℕ)))})
    ) := by
  classical
  intro ι P f g s v i j hij he
  rw [Set.pair_eq_pair_iff] at he
  rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact hij (P.plane.face_vertices_distinct f h₁)
  · have hleft : i = j + 1 := P.plane.face_vertices_distinct f h₁
    have hright : i + 1 = j := P.plane.face_vertices_distinct f h₂
    fin_cases i <;> fin_cases j
    all_goals omega

private theorem w_ne_finish :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀
            (k : Fin (3 : ℕ)), Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (k : Fin 3), w k (Fin.last (s k).count) = D.position (v (k + 1))) → (∀ (k : Fin (3 :
            ℕ)), ∀ (i : Fin (s k).count), w k i.castSucc ≠ D.position (v (k + (1 : Fin (3 :
            ℕ))))))) := by
  classical
  intro ι P D f g hi s τ w v w_finish k i h
  have hg : g k (τ k i.castSucc) = g k (τ k (Fin.last (s k).count)) :=
    h.trans (w_finish k).symm
  have ht := hi k hg
  have htime := congrArg Subtype.val ht
  have hidx : i.castSucc = Fin.last (s k).count := (s k).strict.injective htime
  have hv := congrArg Fin.val hidx
  simp at hv
  omega

private theorem q_injective :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3 : ℕ)),
            Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m1 := (s 1).count
        let m2 := (s 2).count
        let M := m0 + (m1 + m2)
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let q : Fin M → Real × Real :=
          Fin.addCases
            (fun i : Fin m0 => w 0 i.castSucc)
            (Fin.addCases
              (fun i : Fin m1 => w 1 i.castSucc)
              (fun i : Fin m2 => w 2 i.castSucc))
        (∀ (i : Fin m0), q (Fin.castAdd (m1 + m2) i) = w 0 i.castSucc) → ((∀ (i : Fin m1), q
            (Fin.natAdd m0 (Fin.castAdd m2 i)) = w 1 i.castSucc) → ((∀ (i : Fin m2), q
            (Fin.natAdd m0 (Fin.natAdd m1 i)) = w 2 i.castSucc) → ((∀ (i : Fin m0), ∀ (j : Fin
            m1), (w 0 i.castSucc = w 1 j.castSucc) → (False)) → ((∀ (i : Fin m1), ∀ (j : Fin m2),
            (w 1 i.castSucc = w 2 j.castSucc) → (False)) → ((∀ (i : Fin m0), ∀ (j : Fin m2), (w 0
            i.castSucc = w 2 j.castSucc) → (False)) → ((∀ (k : Fin 3), Function.Injective (fun i
            : Fin (s k).count => w k i.castSucc)) → (Function.Injective q))))))))) := by
  classical
  intro g hi s m0 m1 m2 M τ w q q0 q1 q2 no_cross01 no_cross12 no_cross02 w_block_injective a b hab
  revert b
  refine Fin.addCases ?_ ?_ a
  · intro i b
    refine Fin.addCases ?_ ?_ b
    · intro j h
      have h' : w 0 i.castSucc = w 0 j.castSucc := by simpa only [q0] using h
      exact congrArg (Fin.castAdd (m1 + m2)) (w_block_injective 0 h')
    · intro r
      refine Fin.addCases ?_ ?_ r
      · intro j h
        have h' : w 0 i.castSucc = w 1 j.castSucc := by simpa only [q0, q1] using h
        exact (no_cross01 i j h').elim
      · intro j h
        have h' : w 0 i.castSucc = w 2 j.castSucc := by simpa only [q0, q2] using h
        exact (no_cross02 i j h').elim
  · intro r b
    refine Fin.addCases ?_ ?_ b
    · intro i h
      revert h
      refine Fin.addCases ?_ ?_ r
      · intro j h
        have h'' : w 1 j.castSucc = w 0 i.castSucc := by
          simpa only [q1, q0] using h
        exact (no_cross01 i j h''.symm).elim
      · intro j h
        have h'' : w 2 j.castSucc = w 0 i.castSucc := by
          simpa only [q2, q0] using h
        exact (no_cross02 i j h''.symm).elim
    · intro r' h
      revert h
      refine Fin.addCases ?_ ?_ r'
      · intro j h
        revert h
        refine Fin.addCases ?_ ?_ r
        · intro i h
          have h' : w 1 i.castSucc = w 1 j.castSucc := by
            simpa only [q1] using h
          exact congrArg (fun z : Fin m1 => Fin.natAdd m0 (Fin.castAdd m2 z))
            (w_block_injective 1 h')
        · intro i h
          have h' : w 2 i.castSucc = w 1 j.castSucc := by
            simpa only [q2, q1] using h
          exact (no_cross12 j i h'.symm).elim
      · intro j h
        revert h
        refine Fin.addCases ?_ ?_ r
        · intro i h
          have h' : w 1 i.castSucc = w 2 j.castSucc := by
            simpa only [q1, q2] using h
          exact (no_cross12 i j h').elim
        · intro i h
          have h' : w 2 i.castSucc = w 2 j.castSucc := by
            simpa only [q2] using h
          exact congrArg (fun z : Fin m2 => Fin.natAdd m0 (Fin.natAdd m1 z))
            (w_block_injective 2 h')

private theorem finite_interval_cover :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ((k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)) → (∀ N, ∀ (a : Fin (N + 1) → Real),
            StrictMono a → ∀ x, a 0 ≤ x → x ≤ a (Fin.last N) → 0 < N → ∃ r : Fin N, a r.castSucc
            ≤ x ∧ x ≤ a r.succ)
    ) := by
  classical
  intro g s N
  induction N with
  | zero =>
      intro a ha x hlo hhi hpos
      omega
  | succ N ih =>
      intro a ha x hlo hhi hpos
      by_cases hN : N = 0
      · subst N
        by_cases hfirst : x ≤ a 1
        · exact ⟨0, by simpa using hlo, hfirst⟩
        · have hlt : a 1 < x := lt_of_not_ge hfirst
          have hlast : Fin.last 1 = (1 : Fin 2) := by ext; rfl
          rw [hlast] at hhi
          exact False.elim ((not_lt_of_ge hhi) hlt)
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
        by_cases hfirst : x ≤ a 1
        · refine ⟨0, ?_, hfirst⟩
          simpa using hlo
        · let tail : Fin (N + 1) → Real := fun i => a i.succ
          have htail : StrictMono tail := fun i j hij => ha (Fin.succ_lt_succ_iff.mpr hij)
          have hlo' : tail 0 ≤ x := by
            dsimp [tail]
            exact le_of_lt (lt_of_not_ge hfirst)
          have hhi' : x ≤ tail (Fin.last N) := by
            simpa [tail] using hhi
          obtain ⟨r, hr₀, hr₁⟩ := ih tail htail x hlo' hhi' hNpos
          refine ⟨r.succ, ?_, ?_⟩
          · simpa using hr₀
          · simpa using hr₁

private theorem arc_covered :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀
            (k : Fin (3 : ℕ)), Function.Injective (g k)) → ((∀ (k : Fin (3 : ℕ)), Set.range (g k)
            = D.edgeArc (P.plane.faceVertex f k) (P.plane.faceVertex f (k + (1 : Fin (3 : ℕ)))))
            → (∀ (s : (k : Fin (3 : ℕ)) → P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        (∀ (k : Fin 3), ∀ (r : Fin ((s k).count)), Set.range (fun t : Set.Icc ((s k).time
            r.castSucc) ((s k).time r.succ) =>
            g k ⟨t.1, by
              constructor
              · exact (τ k r.castSucc).property.1.trans t.property.1
              · exact t.property.2.trans (τ k r.succ).property.2⟩) =
            segment Real (w k r.castSucc) (w k r.succ)) → (
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ N, ∀ (a : Fin (N + 1) → Real), StrictMono a → ∀ x, a 0 ≤ x → x ≤ a (Fin.last N) → 0 <
            N → ∃ r : Fin N, a r.castSucc ≤ x ∧ x ≤ a r.succ) → (∀ (k : Fin (3 : ℕ)), D.edgeArc
            (v k) (v (k + (1 : Fin (3 : ℕ)))) = ⋃ (r : Fin (s k).count), segment ℝ (w k
            r.castSucc) (w k r.succ)))))) := by
  classical
  intro ι P D f g hi hr s τ w piece_range v finite_interval_cover k
  rw [← hr k]
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    have hlo : (s k).time 0 ≤ (t : Real) := by
      rw [(s k).start]
      exact t.property.1
    have hhi : (t : Real) ≤ (s k).time (Fin.last (s k).count) := by
      rw [(s k).finish]
      exact t.property.2
    obtain ⟨r, hlo, hhi⟩ := finite_interval_cover (s k).count (s k).time
      (s k).strict (t : Real) hlo hhi (s k).positive
    refine Set.mem_iUnion.mpr ⟨r, ?_⟩
    rw [← piece_range k r]
    exact ⟨⟨t, ⟨hlo, hhi⟩⟩, rfl⟩
  · intro hx
    obtain ⟨r, hx⟩ := Set.mem_iUnion.mp hx
    rw [← piece_range k r] at hx
    obtain ⟨t, ht⟩ := Set.mem_range.mp hx
    refine ⟨⟨t, by
      constructor
      · exact (τ k r.castSucc).property.1.trans t.property.1
      · exact t.property.2.trans (τ k r.succ).property.2⟩, ?_⟩
    simpa using ht

private theorem q_step :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3 : ℕ)),
            Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m1 := (s 1).count
        let m2 := (s 2).count
        let M := m0 + (m1 + m2)
        let n := M - 3
        (n + 3 = M) → (
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let q : Fin M → Real × Real :=
          Fin.addCases
            (fun i : Fin m0 => w 0 i.castSucc)
            (Fin.addCases
              (fun i : Fin m1 => w 1 i.castSucc)
              (fun i : Fin m2 => w 2 i.castSucc))
        (∀ (i : Fin m0), q (Fin.castAdd (m1 + m2) i) = w 0 i.castSucc) → ((∀ (i : Fin m1), q
            (Fin.natAdd m0 (Fin.castAdd m2 i)) = w 1 i.castSucc) → ((∀ (i : Fin m2), q
            (Fin.natAdd m0 (Fin.natAdd m1 i)) = w 2 i.castSucc) → ((∀ (k : Fin 3), w k (Fin.last
            (s k).count) = w (k + 1) 0) → (
        ∀ (a : Fin M), ∀ (ha : (↑a : ℕ) + (1 : ℕ) < M), ∃ (k : Fin (3 : ℕ)) (r : Fin (s
            k).count), q a = w k r.castSucc ∧ q ⟨(↑a : ℕ) + (1 : ℕ), ha⟩ = w k r.succ))))))) := by
  classical
  intro g hi s m0 m1 m2 M n hM τ w q q0 q1 q2 join a ha
  let b0 (i : Fin m0) : Fin M := Fin.castAdd (m1 + m2) i
  let b1 (i : Fin m1) : Fin M := Fin.natAdd m0 (Fin.castAdd m2 i)
  let b2 (i : Fin m2) : Fin M := Fin.natAdd m0 (Fin.natAdd m1 i)
  revert ha
  refine Fin.addCases ?_ ?_ a
  · intro r ha
    by_cases hr : r.val + 1 < m0
    · let r' : Fin m0 := ⟨r.val + 1, hr⟩
      have hindex : ⟨(b0 r).val + 1, ha⟩ = b0 r' := by
        apply Fin.ext
        change r.val + 1 = r'.val
        rfl
      have htime : r.succ = r'.castSucc := by
        apply Fin.ext
        simp [r']
      refine ⟨0, r, ?_, ?_⟩
      · simpa [b0] using q0 r
      · rw [hindex]
        simpa [b0, htime] using q0 r'
    · have hlt : r.val < m0 := by simp [m0]
      have hr' : r.val + 1 = m0 := by omega
      let j : Fin m1 := ⟨0, (s 1).positive⟩
      have hindex : ⟨(b0 r).val + 1, ha⟩ = b1 j := by
        apply Fin.ext
        simp [b0, b1, hr', j]
      have htime : r.succ = Fin.last m0 := by
        apply Fin.ext
        simp [hr']
      refine ⟨0, r, ?_, ?_⟩
      · simpa [b0] using q0 r
      · rw [hindex, q1, htime]
        simpa [j] using (join 0).symm
  · intro r ha
    revert ha
    refine Fin.addCases ?_ ?_ r
    · intro i ha
      by_cases hi' : i.val + 1 < m1
      · let i' : Fin m1 := ⟨i.val + 1, hi'⟩
        have hindex : ⟨(b1 i).val + 1, ha⟩ = b1 i' := by
          apply Fin.ext
          change m0 + i.val + 1 = m0 + i'.val
          simp [i']; omega
        have htime : i.succ = i'.castSucc := by
          apply Fin.ext
          simp [i']
        refine ⟨1, i, ?_, ?_⟩
        · simpa [b1] using q1 i
        · rw [hindex]
          simpa [b1, htime] using q1 i'
      · have hi'' : i.val + 1 = m1 := by omega
        let j : Fin m2 := ⟨0, (s 2).positive⟩
        have hindex : ⟨(b1 i).val + 1, ha⟩ = b2 j := by
          apply Fin.ext
          simp [b1, b2, j]
          omega
        have htime : i.succ = Fin.last m1 := by
          apply Fin.ext
          simp [hi'']
        refine ⟨1, i, ?_, ?_⟩
        · simpa [b1] using q1 i
        · rw [hindex, q2, htime]
          simpa [j] using (join 1).symm
    · intro i ha
      by_cases hi' : i.val + 1 < m2
      · let i' : Fin m2 := ⟨i.val + 1, hi'⟩
        have hindex : ⟨(b2 i).val + 1, ha⟩ = b2 i' := by
          apply Fin.ext
          change m0 + (m1 + i.val) + 1 = m0 + (m1 + i'.val)
          simp [i']; omega
        have htime : i.succ = i'.castSucc := by
          apply Fin.ext
          simp [i']
        refine ⟨2, i, ?_, ?_⟩
        · simpa [b2] using q2 i
        · rw [hindex]
          simpa [b2, htime] using q2 i'
      · have hi'' : i.val + 1 = m2 := by omega
        have hval : (b2 i).val + 1 = m0 + (m1 + m2) := by
          change m0 + (m1 + i.val) + 1 = m0 + (m1 + m2)
          omega
        have ha' : (b2 i).val + 1 < m0 + (m1 + m2) := by
          exact ha
        omega

private theorem p_edge_piece :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3 : ℕ)),
            Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m1 := (s 1).count
        let m2 := (s 2).count
        let M := m0 + (m1 + m2)
        let n := M - 3
        ∀ (hM : n + 3 = M),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let q : Fin M → Real × Real :=
          Fin.addCases
            (fun i : Fin m0 => w 0 i.castSucc)
            (Fin.addCases
              (fun i : Fin m1 => w 1 i.castSucc)
              (fun i : Fin m2 => w 2 i.castSucc))
        let p : Fin (n + 3) → Real × Real := fun i => q (Fin.cast hM i)
        (∀ (i : Fin m0), q (Fin.castAdd (m1 + m2) i) = w 0 i.castSucc) → ((∀ (i : Fin m2), q
            (Fin.natAdd m0 (Fin.natAdd m1 i)) = w 2 i.castSucc) → ((∀ (k : Fin 3), w k (Fin.last
            (s k).count) = w (k + 1) 0) → (
        (∀ (a : Fin M), ∀ (ha : a.val + 1 < M), ∃ k : Fin 3, ∃ r : Fin (s k).count, q a = w k
            r.castSucc ∧ q ⟨a.val + 1, ha⟩ = w k r.succ) → (∀ (i : Fin (n + (3 : ℕ))), ∃ (k : Fin
            (3 : ℕ)) (r : Fin (s k).count), p i = w k r.castSucc ∧ p (i + (1 : Fin (n + (3 :
            ℕ)))) = w k r.succ)))))) := by
  classical
  intro g hi s m0 m1 m2 M n hM τ w q p q0 q2 join q_step i
  let b0 (i : Fin m0) : Fin M := Fin.castAdd (m1 + m2) i
  let b2 (i : Fin m2) : Fin M := Fin.natAdd m0 (Fin.natAdd m1 i)
  refine Fin.lastCases ?_ ?_ i
  · have hm2 : 0 < m2 := (s 2).positive
    let r : Fin m2 := ⟨m2 - 1, by omega⟩
    have hr : r.val + 1 = m2 := by simp [r]; omega
    have hindex : Fin.cast hM (Fin.last (n + 2)) = b2 r := by
      apply Fin.ext
      change n + 2 = m0 + (m1 + (m2 - 1))
      omega
    have hnext : Fin.last (n + 2) + 1 = (0 : Fin (n + 3)) := by
      apply Fin.ext
      simp []
    have hleft : p (Fin.last (n + 2)) = w 2 r.castSucc := by
      change q (Fin.cast hM (Fin.last (n + 2))) = _
      rw [hindex, q2]
    have hright : p (Fin.last (n + 2) + 1) = w 2 r.succ := by
      rw [hnext]
      have hrLast : r.succ = Fin.last m2 := by
        apply Fin.ext
        simp [hr]
      let z : Fin (n + 3) := ⟨0, by omega⟩
      let zM : Fin M := ⟨0, by omega⟩
      change q (Fin.cast hM z) = w 2 r.succ
      have hz : Fin.cast hM z = zM := by
        apply Fin.ext
        rfl
      have hm0 : 0 < m0 := (s 0).positive
      let z0 : Fin m0 := ⟨0, by omega⟩
      have hz0 : zM = b0 z0 := by
        apply Fin.ext
        rfl
      have hzstart : z0.castSucc = (⟨0, by omega⟩ : Fin (m0 + 1)) := by
        apply Fin.ext
        rfl
      rw [hz, hz0, q0, hzstart, hrLast]
      exact (join 2).symm
    exact ⟨2, r, hleft, hright⟩
  · intro j
    let a : Fin M := Fin.cast hM j.castSucc
    have ha : a.val + 1 < M := by
      change j.val + 1 < M
      have hj := j.isLt
      omega
    obtain ⟨k, r, hleft, hright⟩ := q_step a ha
    have hnext : Fin.cast hM (j.castSucc + 1) = ⟨a.val + 1, ha⟩ := by
      apply Fin.ext
      simp [a]
    have hp0 : p j.castSucc = q a := by
      simp [p, a]
    have hp1 : p (j.castSucc + 1) = q ⟨a.val + 1, ha⟩ := by
      change q (Fin.cast hM (j.castSucc + 1)) = _
      rw [hnext]
    exact ⟨k, r, hp0.trans hleft, hp1.trans hright⟩

private theorem block_edge :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3 : ℕ)),
            Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m1 := (s 1).count
        let m2 := (s 2).count
        let M := m0 + (m1 + m2)
        let n := M - 3
        ∀ (hM : n + 3 = M),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let q : Fin M → Real × Real :=
          Fin.addCases
            (fun i : Fin m0 => w 0 i.castSucc)
            (Fin.addCases
              (fun i : Fin m1 => w 1 i.castSucc)
              (fun i : Fin m2 => w 2 i.castSucc))
        let p : Fin (n + 3) → Real × Real := fun i => q (Fin.cast hM i)
        (∀ (i : Fin m0), q (Fin.castAdd (m1 + m2) i) = w 0 i.castSucc) → ((∀ (i : Fin m1), q
            (Fin.natAdd m0 (Fin.castAdd m2 i)) = w 1 i.castSucc) → ((∀ (i : Fin m2), q
            (Fin.natAdd m0 (Fin.natAdd m1 i)) = w 2 i.castSucc) → ((∀ (k : Fin 3), w k (Fin.last
            (s k).count) = w (k + 1) 0) → (
        (∀ (i : Fin (n + 3)), (i.val + 1 < n + 3) → ((i + 1).val = i.val + 1)) → (∀ (k : Fin (3 :
            ℕ)), ∀ (r : Fin (s k).count), ∃ (i : Fin (n + (3 : ℕ))), p i = w k r.castSucc ∧ p (i
            + (1 : Fin (n + (3 : ℕ)))) = w k r.succ))))))) := by
  classical
  intro g hi s m0 m1 m2 M n hM τ w q p q0 q1 q2 join fin_succ_val k r
  let b0 (i : Fin m0) : Fin M := Fin.castAdd (m1 + m2) i
  let b1 (i : Fin m1) : Fin M := Fin.natAdd m0 (Fin.castAdd m2 i)
  let b2 (i : Fin m2) : Fin M := Fin.natAdd m0 (Fin.natAdd m1 i)
  fin_cases k
  · by_cases hr : r.val + 1 < m0
    · let r' : Fin m0 := ⟨r.val + 1, hr⟩
      let i : Fin (n + 3) := Fin.cast hM.symm (b0 r)
      have hnext : Fin.cast hM (i + 1) = b0 r' := by
        apply Fin.ext
        simp [i, b0, r', Fin.val_add]
        omega
      refine ⟨i, ?_, ?_⟩
      · simpa [i, p, b0] using q0 r
      · change q (Fin.cast hM (i + 1)) = _
        rw [hnext, q0]
        have ht : r.succ = r'.castSucc := by
          apply Fin.ext
          simp [r']
        simp [ht]
    · have hlt : r.val < m0 := by simp [m0]
      have hr' : r.val + 1 = m0 := by omega
      have hm1 : 0 < m1 := (s 1).positive
      let j : Fin m1 := ⟨0, by omega⟩
      let i : Fin (n + 3) := Fin.cast hM.symm (b0 r)
      have hval : i.val = r.val := by simp [i, b0]
      have hbound : i.val + 1 < n + 3 := by
        have hboundM : i.val + 1 < M := by
          change i.val + 1 < m0 + (m1 + m2)
          rw [hval]
          omega
        omega
      have hnext : Fin.cast hM (i + 1) = b1 j := by
        apply Fin.ext
        simp only [Fin.val_cast]
        rw [fin_succ_val i hbound]
        simp [i, b0, b1, j, hr']
      have ht : r.succ = Fin.last m0 := by
        apply Fin.ext
        simp [hr']
      refine ⟨i, ?_, ?_⟩
      · simpa [i, p, b0] using q0 r
      · change q (Fin.cast hM (i + 1)) = _
        rw [hnext, q1]
        rw [ht]
        simpa [j] using (join 0).symm
  · by_cases hr : r.val + 1 < m1
    · let r' : Fin m1 := ⟨r.val + 1, hr⟩
      let i : Fin (n + 3) := Fin.cast hM.symm (b1 r)
      have hval : i.val = m0 + r.val := by simp [i, b1]
      have hbound : i.val + 1 < n + 3 := by
        have hboundM : i.val + 1 < M := by
          change i.val + 1 < m0 + (m1 + m2)
          rw [hval]
          omega
        omega
      have hnext : Fin.cast hM (i + 1) = b1 r' := by
        apply Fin.ext
        simp only [Fin.val_cast]
        rw [fin_succ_val i hbound]
        simp [i, b1, r']; omega
      refine ⟨i, ?_, ?_⟩
      · simpa [i, p, b1] using q1 r
      · change q (Fin.cast hM (i + 1)) = _
        rw [hnext, q1]
        have ht : r.succ = r'.castSucc := by
          apply Fin.ext
          simp [r']
        simp [ht]
    · have hlt : r.val < m1 := by simp [m1]
      have hr' : r.val + 1 = m1 := by omega
      have hm2 : 0 < m2 := (s 2).positive
      let j : Fin m2 := ⟨0, by omega⟩
      let i : Fin (n + 3) := Fin.cast hM.symm (b1 r)
      have hval : i.val = m0 + r.val := by simp [i, b1]
      have hbound : i.val + 1 < n + 3 := by
        have hboundM : i.val + 1 < M := by
          change i.val + 1 < m0 + (m1 + m2)
          rw [hval]
          omega
        omega
      have hnext : Fin.cast hM (i + 1) = b2 j := by
        apply Fin.ext
        simp only [Fin.val_cast]
        rw [fin_succ_val i hbound]
        simp [i, b1, b2, j]; omega
      have ht : r.succ = Fin.last m1 := by
        apply Fin.ext
        simp [hr']
      refine ⟨i, ?_, ?_⟩
      · simpa [i, p, b1] using q1 r
      · change q (Fin.cast hM (i + 1)) = _
        rw [hnext, q2]
        rw [ht]
        simpa [j] using (join 1).symm
  · by_cases hr : r.val + 1 < m2
    · let r' : Fin m2 := ⟨r.val + 1, hr⟩
      let i : Fin (n + 3) := Fin.cast hM.symm (b2 r)
      have hval : i.val = m0 + (m1 + r.val) := by simp [i, b2]
      have hbound : i.val + 1 < n + 3 := by
        have hboundM : i.val + 1 < M := by
          change i.val + 1 < m0 + (m1 + m2)
          rw [hval]
          omega
        omega
      have hnext : Fin.cast hM (i + 1) = b2 r' := by
        apply Fin.ext
        simp only [Fin.val_cast]
        rw [fin_succ_val i hbound]
        simp [i, b2, r']; omega
      refine ⟨i, ?_, ?_⟩
      · simpa [i, p, b2] using q2 r
      · change q (Fin.cast hM (i + 1)) = _
        rw [hnext, q2]
        have ht : r.succ = r'.castSucc := by
          apply Fin.ext
          simp [r']
        simp [ht]
    · have hlt : r.val < m2 := by simp [m2]
      have hr' : r.val + 1 = m2 := by omega
      let i : Fin (n + 3) := Fin.cast hM.symm (b2 r)
      have hval : i.val = m0 + (m1 + r.val) := by simp [i, b2]
      have hlast : i = Fin.last (n + 2) := by
        apply Fin.ext
        change i.val = (Fin.last (n + 2)).val
        simp only [Fin.val_last]
        rw [hval]
        omega
      have hnext : i + 1 = (⟨0, by omega⟩ : Fin (n + 3)) := by
        rw [hlast]
        apply Fin.ext
        simp []
      have ht : r.succ = Fin.last m2 := by
        apply Fin.ext
        simp [hr']
      refine ⟨i, ?_, ?_⟩
      · simpa [i, p, b2] using q2 r
      · rw [hnext]
        change q (Fin.cast hM (⟨0, by omega⟩ : Fin (n + 3))) = w 2 r.succ
        have hm0 : 0 < m0 := (s 0).positive
        let z0 : Fin m0 := ⟨0, by omega⟩
        have hz : Fin.cast hM (⟨0, by omega⟩ : Fin (n + 3)) = b0 z0 := by
          apply Fin.ext
          rfl
        rw [hz, q0]
        have hzstart : z0.castSucc = (⟨0, by omega⟩ : Fin (m0 + 1)) := by
          apply Fin.ext
          rfl
        rw [hzstart, ht]
        exact (join 2).symm

private theorem edge_union :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3 : ℕ)),
            Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m1 := (s 1).count
        let m2 := (s 2).count
        let M := m0 + (m1 + m2)
        let n := M - 3
        ∀ (hM : n + 3 = M),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let q : Fin M → Real × Real :=
          Fin.addCases
            (fun i : Fin m0 => w 0 i.castSucc)
            (Fin.addCases
              (fun i : Fin m1 => w 1 i.castSucc)
              (fun i : Fin m2 => w 2 i.castSucc))
        let p : Fin (n + 3) → Real × Real := fun i => q (Fin.cast hM i)
        (∀ (i : Fin (n + 3)), ∃ k : Fin 3, ∃ r : Fin (s k).count, p i = w k r.castSucc ∧ p (i +
            1) = w k r.succ) → ((∀ (k : Fin 3), ∀ (r : Fin (s k).count), ∃ i : Fin (n + 3), p i =
            w k r.castSucc ∧ p (i + 1) = w k r.succ) → ((⋃ i : Fin (n + 3), segment Real (p i) (p
            (i + 1))) = ⋃ k : Fin 3, ⋃ r : Fin (s k).count, segment Real (w k r.castSucc) (w k
            r.succ))))) := by
  classical
  intro g hi s m0 m1 m2 M n hM τ w q p p_edge_piece block_edge
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hx⟩
    obtain ⟨k, r, hleft, hright⟩ := p_edge_piece i
    exact ⟨k, r, by simpa [hleft, hright] using hx⟩
  · rintro ⟨k, r, hx⟩
    obtain ⟨i, hleft, hright⟩ := block_edge k r
    exact ⟨i, by rw [hleft, hright]; exact hx⟩

private theorem piece_arc_union :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀
            (k : Fin (3 : ℕ)), Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (k : Fin 3), D.edgeArc (v k) (v (k + 1)) = ⋃ r : Fin (s k).count, segment Real (w k
            r.castSucc) (w k r.succ)) → ((⋃ k : Fin 3, ⋃ r : Fin (s k).count, segment Real (w k
            r.castSucc) (w k r.succ)) = ⋃ k : Fin 3, D.edgeArc (v k) (v (k + 1))))) := by
  classical
  intro ι P D f g hi s τ w v arc_covered
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨k, r, hx⟩
    exact ⟨k, (arc_covered k).symm ▸ Set.mem_iUnion.mpr ⟨r, hx⟩⟩
  · rintro ⟨k, hx⟩
    rw [arc_covered k] at hx
    obtain ⟨r, hx⟩ := Set.mem_iUnion.mp hx
    exact ⟨k, r, hx⟩

private theorem arc_union :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face),
        let v : Fin 3 → ι := P.plane.faceVertex f
        (⋃ k : Fin 3, D.edgeArc (v k) (v (k + 1))) = D.edgeArc (v 0) (v 1) ∪ D.edgeArc (v 1) (v
            2) ∪ D.edgeArc (v 2) (v 0)
    ) := by
  classical
  intro ι P D f v
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨k, hx⟩
    fin_cases k
    · exact Or.inl (Or.inl (by simpa using hx))
    · exact Or.inl (Or.inr (by simpa using hx))
    · exact Or.inr (by simpa using hx)
  · intro hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · exact ⟨0, by simpa using hx⟩
      · exact ⟨1, by simpa using hx⟩
    · exact ⟨2, by simpa using hx⟩

private theorem piece_start_corner :
    (by
      classical
      exact
         ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f
             : P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
             (∀ (k : Fin (3 : ℕ)), Function.Injective (g k)) → ((∀ (k : Fin (3 : ℕ)), g k ⟨(0 :
             ℝ), (by norm_num)⟩ = D.position (P.plane.faceVertex f k)) → (∀ (s : (k : Fin
             (3 : ℕ)) → P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        (∀ (k : Fin 3), ∀ (r : Fin ((s k).count)), Set.range (fun t : Set.Icc ((s k).time
            r.castSucc) ((s k).time r.succ) =>
            g k ⟨t.1, by
              constructor
              · exact (τ k r.castSucc).property.1.trans t.property.1
              · exact t.property.2.trans (τ k r.succ).property.2⟩) =
            segment Real (w k r.castSucc) (w k r.succ)) → (
        let v : Fin 3 → ι := P.plane.faceVertex f
        ∀ (k : Fin (3 : ℕ)), ∀ (r : Fin (s k).count), ∀ x ∈ segment ℝ (w k r.castSucc) (w k
            r.succ), x = D.position (v k) → x = w k r.castSucc ∨ x = w k r.succ)))) := by
  classical
  intro ι P D f g hi h0 s τ w piece_range v k r x hx hc
  rw [← piece_range k r] at hx
  obtain ⟨t, ht⟩ := Set.mem_range.mp hx
  let u : Set.Icc (0 : Real) 1 := ⟨t.1,
    (τ k r.castSucc).property.1.trans t.property.1,
    t.property.2.trans (τ k r.succ).property.2⟩
  have htu : g k u = x := by simpa [u] using ht
  have hzero : g k ⟨0, by norm_num⟩ = x := (h0 k).trans hc.symm
  have hu0 : (u : Real) = 0 := by
    have heq := hi k (htu.trans hzero.symm)
    exact congrArg Subtype.val heq
  have ht0 : (s k).time r.castSucc = 0 := by
    have hmono := (s k).strict.monotone (Fin.zero_le r.castSucc)
    rw [(s k).start] at hmono
    have hle : (s k).time r.castSucc ≤ 0 := by
      have htleft : (s k).time r.castSucc ≤ (u : Real) := by
        exact t.property.1
      rw [hu0] at htleft
      exact htleft
    exact le_antisymm hle hmono
  have huτ : u = τ k r.castSucc := by
    apply Subtype.ext
    exact hu0.trans ht0.symm
  rw [huτ] at htu
  left
  change x = g k (τ k r.castSucc)
  exact htu.symm

private theorem piece_finish_corner :
    (by
      classical
      exact
         ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f
             : P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),
             (∀ (k : Fin (3 : ℕ)), Function.Injective (g k)) → ((∀ (k : Fin (3 : ℕ)), g k ⟨(1 :
             ℝ), (by norm_num)⟩ = D.position (P.plane.faceVertex f (k + (1 : Fin (3 :
             ℕ))))) → (∀ (s : (k : Fin (3 : ℕ)) → P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        (∀ (k : Fin 3), ∀ (r : Fin ((s k).count)), Set.range (fun t : Set.Icc ((s k).time
            r.castSucc) ((s k).time r.succ) =>
            g k ⟨t.1, by
              constructor
              · exact (τ k r.castSucc).property.1.trans t.property.1
              · exact t.property.2.trans (τ k r.succ).property.2⟩) =
            segment Real (w k r.castSucc) (w k r.succ)) → (
        let v : Fin 3 → ι := P.plane.faceVertex f
        ∀ (k : Fin (3 : ℕ)), ∀ (r : Fin (s k).count), ∀ x ∈ segment ℝ (w k r.castSucc) (w k
            r.succ), x = D.position (v (k + (1 : Fin (3 : ℕ)))) → x = w k r.castSucc ∨ x = w k
            r.succ)))) := by
  classical
  intro ι P D f g hi h1 s τ w piece_range v k r x hx hc
  rw [← piece_range k r] at hx
  obtain ⟨t, ht⟩ := Set.mem_range.mp hx
  let u : Set.Icc (0 : Real) 1 := ⟨t.1,
    (τ k r.castSucc).property.1.trans t.property.1,
    t.property.2.trans (τ k r.succ).property.2⟩
  have htu : g k u = x := by simpa [u] using ht
  have hone : g k ⟨1, by norm_num⟩ = x := (h1 k).trans hc.symm
  have hu1 : (u : Real) = 1 := by
    have heq := hi k (htu.trans hone.symm)
    exact congrArg Subtype.val heq
  have ht1 : (s k).time r.succ = 1 := by
    have hmono := (s k).strict.monotone (Fin.le_last r.succ)
    rw [(s k).finish] at hmono
    have hle : 1 ≤ (s k).time r.succ := by
      have htright : (u : Real) ≤ (s k).time r.succ := by exact t.property.2
      rw [hu1] at htright
      exact htright
    exact le_antisymm hmono hle
  have huτ : u = τ k r.succ := by
    apply Subtype.ext
    exact hu1.trans ht1.symm
  rw [huτ] at htu
  right
  change x = g k (τ k r.succ)
  exact htu.symm

private theorem piece_overlap_forward :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3 : ℕ)),
            Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        (∀ (k : Fin 3), ∀ (r : Fin ((s k).count)), Set.range (fun t : Set.Icc ((s k).time
            r.castSucc) ((s k).time r.succ) =>
            g k ⟨t.1, by
              constructor
              · exact (τ k r.castSucc).property.1.trans t.property.1
              · exact t.property.2.trans (τ k r.succ).property.2⟩) =
            segment Real (w k r.castSucc) (w k r.succ)) → (∀ (k : Fin (3 : ℕ)), ∀ (r : Fin (s
                k).count), ∀ (r' : Fin (s k).count), (↑r : ℕ) < (↑r' : ℕ) → ∀ x ∈ segment ℝ (w k
                r.castSucc) (w k r.succ), x ∈ segment ℝ (w k r'.castSucc) (w k r'.succ) → (x = w
                k r.castSucc ∨ x = w k r.succ) ∧ (x = w k r'.castSucc ∨ x = w k r'.succ)))) := by
  classical
  intro g hi s τ w piece_range k r r' hlt x hx hx'
  obtain ⟨t, ht⟩ := Set.mem_range.mp ((piece_range k r).symm ▸ hx)
  obtain ⟨t', ht'⟩ := Set.mem_range.mp ((piece_range k r').symm ▸ hx')
  let u : Set.Icc (0 : Real) 1 := ⟨t.1,
    (τ k r.castSucc).property.1.trans t.property.1,
    t.property.2.trans (τ k r.succ).property.2⟩
  let u' : Set.Icc (0 : Real) 1 := ⟨t'.1,
    (τ k r'.castSucc).property.1.trans t'.property.1,
    t'.property.2.trans (τ k r'.succ).property.2⟩
  have htu : g k u = x := by simpa [u] using ht
  have htu' : g k u' = x := by simpa [u'] using ht'
  have hparam : (u : Real) = (u' : Real) := by
    have heq := hi k (htu.trans htu'.symm)
    exact congrArg Subtype.val heq
  have hidx : r.succ ≤ r'.castSucc := by
    apply Fin.le_iff_val_le_val.mpr
    simp
    omega
  have hmono := (s k).strict.monotone hidx
  have hback : (s k).time r'.castSucc ≤ (s k).time r.succ := by
    calc
      (s k).time r'.castSucc ≤ (u' : Real) := t'.property.1
      _ = (u : Real) := hparam.symm
      _ ≤ (s k).time r.succ := t.property.2
  have htime : (s k).time r.succ = (s k).time r'.castSucc := le_antisymm hmono hback
  have hindices : r.succ = r'.castSucc := (s k).strict.injective htime
  have hu : (u : Real) = (s k).time r.succ := by
    apply le_antisymm t.property.2
    calc
      (s k).time r.succ = (s k).time r'.castSucc := htime
      _ ≤ (u' : Real) := t'.property.1
      _ = (u : Real) := hparam.symm
  have hu' : (u' : Real) = (s k).time r'.castSucc := by
    exact hparam.symm.trans (hu.trans htime)
  have huτ : u = τ k r.succ := by
    apply Subtype.ext
    exact hu
  have hu'τ : u' = τ k r'.castSucc := by
    apply Subtype.ext
    exact hu'
  rw [huτ] at htu
  rw [hu'τ] at htu'
  refine ⟨Or.inr ?_, Or.inl ?_⟩
  · change x = g k (τ k r.succ)
    exact htu.symm
  · change x = g k (τ k r'.castSucc)
    exact htu'.symm

private theorem piece_overlap :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3 : ℕ)),
            Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · let hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · let hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        (∀ (k : Fin 3), ∀ (r : Fin (s k).count), ∀ (r' : Fin (s k).count), (r.val < r'.val) → (∀
            (x : Real × Real), (x ∈ segment Real (w k r.castSucc) (w k r.succ)) → ((x ∈ segment
            Real (w k r'.castSucc) (w k r'.succ)) → ((x = w k r.castSucc ∨ x = w k r.succ) ∧ (x =
            w k r'.castSucc ∨ x = w k r'.succ))))) → (∀ (k : Fin (3 : ℕ)), ∀ (r : Fin (s
            k).count), ∀ (r' : Fin (s k).count), r ≠ r' → ∀ x ∈ segment ℝ (w k r.castSucc) (w k
            r.succ), x ∈ segment ℝ (w k r'.castSucc) (w k r'.succ) → (x = w k r.castSucc ∨ x = w
            k r.succ) ∧ (x = w k r'.castSucc ∨ x = w k r'.succ)))) := by
  classical
  intro g hi s τ w piece_overlap_forward k r r' hne x hx hx'
  have hvne : r.val ≠ r'.val := by
    intro hv
    apply hne
    exact Fin.ext hv
  rcases lt_or_gt_of_ne hvne with hlt | hgt
  · exact piece_overlap_forward k r r' hlt x hx hx'
  · have h := piece_overlap_forward k r' r hgt x hx' hx
    exact ⟨h.2, h.1⟩

end RoutedSubdivisionProof

namespace RoutedFaceDetails

private theorem hM :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (s : (k : Fin (3 :
            ℕ)) → P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m1 := (s 1).count
        let m2 := (s 2).count
        let M := m0 + (m1 + m2)
        ((∑ k : Fin 3, (s k).count) = M) → (
        let n := M - 3
        n + 3 = M) ) := by
  classical
  intro g s m0 m1 m2 M hsum n
  dsimp [n]
  have hpos : 3 ≤ M := by
    dsimp [M, m0, m1, m2]
    have h0 := (s 0).positive
    have h1 := (s 1).positive
    have h2 := (s 2).positive
    omega
  omega

private theorem q0 :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3
            : ℕ)), Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m1 := (s 1).count
        let m2 := (s 2).count
        let M := m0 + (m1 + m2)
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let q : Fin M → Real × Real :=
          Fin.addCases
            (fun i : Fin m0 => w 0 i.castSucc)
            (Fin.addCases
              (fun i : Fin m1 => w 1 i.castSucc)
              (fun i : Fin m2 => w 2 i.castSucc))
        ∀ (i : Fin m0), q (Fin.castAdd (m1 + m2) i) = w (0 : Fin (3 : ℕ)) i.castSucc)) := by
  classical
  intro g hi s m0 m1 m2 M τ w q i
  simp [q]

private theorem q1 :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3
            : ℕ)), Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m1 := (s 1).count
        let m2 := (s 2).count
        let M := m0 + (m1 + m2)
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let q : Fin M → Real × Real :=
          Fin.addCases
            (fun i : Fin m0 => w 0 i.castSucc)
            (Fin.addCases
              (fun i : Fin m1 => w 1 i.castSucc)
              (fun i : Fin m2 => w 2 i.castSucc))
        ∀ (i : Fin m1), q (Fin.natAdd m0 (Fin.castAdd m2 i)) = w (1 : Fin (3 : ℕ)) i.castSucc))
            := by
  classical
  intro g hi s m0 m1 m2 M τ w q i
  simp [q]

private theorem q2 :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3
            : ℕ)), Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m1 := (s 1).count
        let m2 := (s 2).count
        let M := m0 + (m1 + m2)
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let q : Fin M → Real × Real :=
          Fin.addCases
            (fun i : Fin m0 => w 0 i.castSucc)
            (Fin.addCases
              (fun i : Fin m1 => w 1 i.castSucc)
              (fun i : Fin m2 => w 2 i.castSucc))
        ∀ (i : Fin m2), q (Fin.natAdd m0 (Fin.natAdd m1 i)) = w (2 : Fin (3 : ℕ)) i.castSucc)) := by
  classical
  intro g hi s m0 m1 m2 M τ w q i
  simp [q]

private theorem cyc_ne :
    (by
      classical
      exact
        ∀ i : Fin 3, i ≠ i + 1 ) := by
  classical
  intro i
  fin_cases i <;> decide

private theorem faceContact :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (f : P.plane.Face),
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ i : Fin 3, i ≠ i + 1) → (∀ (i : Fin (3 : ℕ)), P3723T1EdgeContact P (v i) (v (i + (1
            : Fin (3 : ℕ))))) ) := by
  classical
  intro ι P f v cyc_ne i
  refine ⟨?_, P.adjacent_has_common_edge _ _ ?_⟩
  · intro he
    exact cyc_ne i (P.plane.face_vertices_distinct f he)
  · exact P.plane.face_edges f i (i + 1) (cyc_ne i)

private theorem arc_inter :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face),
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (i : Fin 3), ∀ (j : Fin 3), (i ≠ j) → (({v i, v (i + 1)} : Set ι) ≠ {v j, v (j + 1)}))
            → ((∀ (i : Fin 3), P3723T1EdgeContact P (v i) (v (i + 1))) → (∀ (i : Fin (3 : ℕ)),
            ∀ (j : Fin (3 : ℕ)), i ≠ j → D.edgeArc (v i) (v (i + (1 : Fin (3 : ℕ)))) ∩ D.edgeArc
            (v j) (v (j + (1 : Fin (3 : ℕ)))) = D.position '' ({v i, v (i + (1 : Fin (3 : ℕ)))} ∩
            {v j, v (j + (1 : Fin (3 : ℕ)))}))) ) := by
  classical
  intro ι P D f v pair_ne faceContact i j hij
  exact D.edgeArc_intersections _ _ _ _ (faceContact i) (faceContact j)
    (pair_ne i j hij)

private theorem v_distinct :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (f : P.plane.Face),
        let v : Fin 3 → ι := P.plane.faceVertex f
        ∀ (i : Fin (3 : ℕ)), ∀ (j : Fin (3 : ℕ)), i ≠ j → v i ≠ v j ) := by
  classical
  intro ι P f v i j hij h
  exact hij (P.plane.face_vertices_distinct f h)

private theorem pair_inter :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (f : P.plane.Face),
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (i : Fin 3), ∀ (j : Fin 3), (i ≠ j) → (v i ≠ v j)) → (∀ (i : Fin (3 : ℕ)), ∀ (j : Fin
            (3 : ℕ)), i ≠ j → ({v i, v (i + (1 : Fin (3 : ℕ)))} : Set ι) ∩ ({v j,
                v (j + (1 : Fin (3 : ℕ)))} : Set ι)
            = {v (if i + (1 : Fin (3 : ℕ)) = j then j else i)}) ) := by
  classical
  intro ι P f v v_distinct i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    ext x
    simp only [v, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    all_goals grind

private theorem arc_inter_singleton :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face),
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (i : Fin 3), ∀ (j : Fin 3), (i ≠ j) → (D.edgeArc (v i) (v (i + 1)) ∩ D.edgeArc (v j)
            (v (j + 1)) = D.position '' (({v i, v (i + 1)} : Set ι) ∩ {v j, v (j + 1)}))) → ((∀
            (i : Fin 3), ∀ (j : Fin 3), (i ≠ j) → (({v i, v (i + 1)} : Set ι) ∩ {v j, v (j + 1)}
            = {v (if i + 1 = j then j else i)})) → (∀ (i : Fin (3 : ℕ)), ∀ (j : Fin (3 : ℕ)), i ≠
            j → D.edgeArc (v i) (v (i + (1 : Fin (3 : ℕ)))) ∩ D.edgeArc (v j) (v (j + (1 : Fin (3
            : ℕ)))) = {D.position (v (if i + (1 : Fin (3 : ℕ)) = j then j else i))})) ) := by
  classical
  intro ι P D f v arc_inter pair_inter i j hij
  rw [arc_inter _ _ hij, pair_inter i j hij]
  simp

private theorem w_arc :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀
            (k : Fin (3 : ℕ)), Function.Injective (g k)) → ((∀ (k : Fin (3 : ℕ)), Set.range (g k)
            = D.edgeArc (P.plane.faceVertex f k) (P.plane.faceVertex f (k + (1 :
            Fin (3 : ℕ))))) → (∀ (s : (k : Fin (3 : ℕ)) → P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let v : Fin 3 → ι := P.plane.faceVertex f
        ∀ (k : Fin (3 : ℕ)), ∀ (i : Fin ((s k).count + (1 : ℕ))), w k i ∈ D.edgeArc (v k) (v (k +
            (1 : Fin (3 : ℕ))))))) := by
  classical
  intro ι P D f g hi hr s τ w v k i
  rw [← hr k]
  exact ⟨τ k i, rfl⟩

private theorem w_before_end :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3
            : ℕ)), Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        ∀ (k : Fin (3 : ℕ)), ∀ (i : Fin (s k).count), (↑(τ k i.castSucc) : ℝ) < (1 : ℝ))) := by
  classical
  intro g hi s τ k i
  have hidx : i.castSucc < Fin.last (s k).count := by
    apply Fin.mk_lt_mk.mpr
    simp
  have ht := (s k).strict hidx
  rw [(s k).finish] at ht
  exact ht

private theorem w_finish :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀
            (k : Fin (3 : ℕ)), Function.Injective (g k)) → ((∀ (k : Fin (3 : ℕ)), g
            k ⟨(1 : ℝ), (by norm_num)⟩ = D.position (P.plane.faceVertex
            f (k + (1 : Fin (3 : ℕ))))) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let v : Fin 3 → ι := P.plane.faceVertex f
        ∀ (k : Fin (3 : ℕ)), w k (Fin.last (s k).count) = D.position (v (k + (1 : Fin (3 :
            ℕ))))))) := by
  classical
  intro ι P D f g hi h1 s τ w v k
  have he : τ k (Fin.last (s k).count) = ⟨1, by norm_num⟩ := by
    apply Subtype.ext
    simp [τ, (s k).finish]
  simpa [w, he] using h1 k

private theorem w_start :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀
            (k : Fin (3 : ℕ)), Function.Injective (g k)) → ((∀ (k : Fin (3 : ℕ)), g
            k ⟨(0 : ℝ), (by norm_num)⟩ = D.position (P.plane.faceVertex
            f k)) → (∀ (s : (k : Fin (3 : ℕ)) → P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let v : Fin 3 → ι := P.plane.faceVertex f
        ∀ (k : Fin (3 : ℕ)), w k (0 : Fin ((s k).count + (1 : ℕ))) = D.position (v k)))) := by
  classical
  intro ι P D f g hi h0 s τ w v k
  have he : τ k 0 = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    simp [τ, (s k).start]
  simpa [w, he] using h0 k

private theorem arc01 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face),
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (i : Fin 3), ∀ (j : Fin 3), (i ≠ j) → (D.edgeArc (v i) (v (i + 1)) ∩ D.edgeArc (v j)
            (v (j + 1)) = {D.position (v (if i + 1 = j then j else i))})) → (D.edgeArc (v 0) (v
            1) ∩ D.edgeArc (v 1) (v 2) = {D.position (v 1)}) ) := by
  classical
  intro ι P D f v arc_inter_singleton
  simpa [v] using arc_inter_singleton 0 1 (by decide)

private theorem arc12 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face),
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (i : Fin 3), ∀ (j : Fin 3), (i ≠ j) → (D.edgeArc (v i) (v (i + 1)) ∩ D.edgeArc (v j)
            (v (j + 1)) = {D.position (v (if i + 1 = j then j else i))})) → (D.edgeArc (v 1) (v
            2) ∩ D.edgeArc (v 2) (v 0) = {D.position (v 2)}) ) := by
  classical
  intro ι P D f v arc_inter_singleton
  simpa [v] using arc_inter_singleton 1 2 (by decide)

private theorem arc20 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face),
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (i : Fin 3), ∀ (j : Fin 3), (i ≠ j) → (D.edgeArc (v i) (v (i + 1)) ∩ D.edgeArc (v j)
            (v (j + 1)) = {D.position (v (if i + 1 = j then j else i))})) → (D.edgeArc (v 2) (v
            0) ∩ D.edgeArc (v 0) (v 1) = {D.position (v 0)}) ) := by
  classical
  intro ι P D f v arc_inter_singleton
  simpa [v] using arc_inter_singleton 2 0 (by decide)

private theorem no_cross01 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),  ∀
                (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m1 := (s 1).count
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (k : Fin 3), ∀ (i : Fin ((s k).count + 1)), w k i ∈ D.edgeArc (v k) (v (k + 1))) → ((∀
            (k : Fin 3), ∀ (i : Fin (s k).count), w k i.castSucc ≠ D.position (v (k + 1))) →
            ((D.edgeArc (v 0) (v 1) ∩ D.edgeArc (v 1) (v 2) = {D.position (v 1)}) → (∀ (i : Fin
            m0), ∀ (j : Fin m1), w (0 : Fin (3 : ℕ)) i.castSucc = w (1 : Fin (3 : ℕ)) j.castSucc
            → False))) ) := by
  classical
  intro ι P D f g s m0 m1 τ w v w_arc w_ne_finish arc01 i j h
  have hx : w 0 i.castSucc ∈ D.edgeArc (v 0) (v 1) ∩ D.edgeArc (v 1) (v 2) :=
    ⟨w_arc 0 i.castSucc, h ▸ w_arc 1 j.castSucc⟩
  rw [arc01] at hx
  have heq : w 0 i.castSucc = D.position (v 1) := by simpa using hx
  exact w_ne_finish 0 i (by simpa [v] using heq)

private theorem no_cross12 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),  ∀
                (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let m1 := (s 1).count
        let m2 := (s 2).count
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (k : Fin 3), ∀ (i : Fin ((s k).count + 1)), w k i ∈ D.edgeArc (v k) (v (k + 1))) → ((∀
            (k : Fin 3), ∀ (i : Fin (s k).count), w k i.castSucc ≠ D.position (v (k + 1))) →
            ((D.edgeArc (v 1) (v 2) ∩ D.edgeArc (v 2) (v 0) = {D.position (v 2)}) → (∀ (i : Fin
            m1), ∀ (j : Fin m2), w (1 : Fin (3 : ℕ)) i.castSucc = w (2 : Fin (3 : ℕ)) j.castSucc
            → False))) ) := by
  classical
  intro ι P D f g s m1 m2 τ w v w_arc w_ne_finish arc12 i j h
  have hx : w 1 i.castSucc ∈ D.edgeArc (v 1) (v 2) ∩ D.edgeArc (v 2) (v 0) :=
    ⟨w_arc 1 i.castSucc, h ▸ w_arc 2 j.castSucc⟩
  rw [arc12] at hx
  have heq : w 1 i.castSucc = D.position (v 2) := by simpa using hx
  exact w_ne_finish 1 i (by simpa [v] using heq)

private theorem no_cross02 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ),  ∀
                (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m2 := (s 2).count
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (k : Fin 3), ∀ (i : Fin ((s k).count + 1)), w k i ∈ D.edgeArc (v k) (v (k + 1))) → ((∀
            (k : Fin 3), ∀ (i : Fin (s k).count), w k i.castSucc ≠ D.position (v (k + 1))) →
            ((D.edgeArc (v 2) (v 0) ∩ D.edgeArc (v 0) (v 1) = {D.position (v 0)}) → (∀ (i : Fin
            m0), ∀ (j : Fin m2), w (0 : Fin (3 : ℕ)) i.castSucc = w (2 : Fin (3 : ℕ)) j.castSucc
            → False))) ) := by
  classical
  intro ι P D f g s m0 m2 τ w v w_arc w_ne_finish arc20 i j h
  have hx : w 2 j.castSucc ∈ D.edgeArc (v 2) (v 0) ∩ D.edgeArc (v 0) (v 1) :=
    ⟨w_arc 2 j.castSucc, h.symm ▸ w_arc 0 i.castSucc⟩
  rw [arc20] at hx
  have heq : w 2 j.castSucc = D.position (v 0) := by simpa using hx
  exact w_ne_finish 2 j (by simpa [v] using heq)

private theorem w_block_injective :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3
            : ℕ)), Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        ∀ (k : Fin (3 : ℕ)), Function.Injective fun (i : Fin (s k).count) => w k i.castSucc)) := by
  classical
  intro g hi s τ w k i j h
  have ht := hi k h
  have htime := congrArg Subtype.val ht
  have hidx : i.castSucc = j.castSucc := (s k).strict.injective htime
  exact Fin.castSucc_injective _ hidx

private theorem fin_succ_val :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), ∀ (s : (k : Fin (3 :
            ℕ)) → P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m1 := (s 1).count
        let m2 := (s 2).count
        let M := m0 + (m1 + m2)
        let n := M - 3
        ∀ (i : Fin (n + (3 : ℕ))), (↑i : ℕ) + (1 : ℕ) < n + (3 : ℕ) → (↑(i + (1 : Fin (n + (3 :
            ℕ)))) : ℕ) = (↑i : ℕ) + (1 : ℕ) ) := by
  classical
  intro g s m0 m1 m2 M n i h
  simp [Fin.val_add, Nat.mod_eq_of_lt h]

private theorem piece_subset_arc :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀
            (k : Fin (3 : ℕ)), Function.Injective (g k)) → ((∀ (k : Fin (3 : ℕ)), Set.range (g k)
            = D.edgeArc (P.plane.faceVertex f k) (P.plane.faceVertex f (k + (1 :
            Fin (3 : ℕ))))) → (∀ (s : (k : Fin (3 : ℕ)) → P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        (∀ (k : Fin 3), ∀ (r : Fin ((s k).count)), Set.range (fun t : Set.Icc ((s k).time
            r.castSucc) ((s k).time r.succ) =>
            g k ⟨t.1, by
              constructor
              · exact (τ k r.castSucc).property.1.trans t.property.1
              · exact t.property.2.trans (τ k r.succ).property.2⟩) =
            segment Real (w k r.castSucc) (w k r.succ)) → (
        let v : Fin 3 → ι := P.plane.faceVertex f
        ∀ (k : Fin (3 : ℕ)), ∀ (r : Fin (s k).count), segment ℝ (w k r.castSucc) (w k r.succ) ⊆
            D.edgeArc (v k) (v (k + (1 : Fin (3 : ℕ)))))))) := by
  classical
  intro ι P D f g hi hr s τ w piece_range v k r x hx
  rw [← piece_range k r] at hx
  obtain ⟨t, ht⟩ := Set.mem_range.mp hx
  rw [← hr k]
  refine ⟨⟨t.1, ⟨(τ k r.castSucc).property.1.trans t.property.1,
    t.property.2.trans (τ k r.succ).property.2⟩⟩, ?_⟩
  simpa using ht

private theorem p_injective :
    (by
      classical
      exact
        ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀ (k : Fin (3
            : ℕ)), Function.Injective (g k)) → (∀ (s : (k : Fin (3 : ℕ)) →
            P3723T1PolygonalParameterization (g k)),
        let m0 := (s 0).count
        let m1 := (s 1).count
        let m2 := (s 2).count
        let M := m0 + (m1 + m2)
        let n := M - 3
        ∀ (hM : n + 3 = M),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let q : Fin M → Real × Real :=
          Fin.addCases
            (fun i : Fin m0 => w 0 i.castSucc)
            (Fin.addCases
              (fun i : Fin m1 => w 1 i.castSucc)
              (fun i : Fin m2 => w 2 i.castSucc))
        let p : Fin (n + 3) → Real × Real := fun i => q (Fin.cast hM i)
        (Function.Injective q) → (Function.Injective p))) := by
  classical
  intro g hi s m0 m1 m2 M n hM τ w q p q_injective i j hij
  apply Fin.cast_injective hM
  apply q_injective
  simpa [p] using hij

private theorem endpoint_mem :
    (by
      classical
      exact
        ∀ (a : ℝ × ℝ), ∀ (b : ℝ × ℝ), ∀ (x : ℝ × ℝ), x = a ∨ x = b → x ∈ segment ℝ a b ) := by
  classical
  intro a b x h
  rcases h with h | h
  · subst x
    exact left_mem_segment Real a b
  · subst x
    exact right_mem_segment Real a b

private theorem hxpos :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face),
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (i : Fin 3), ∀ (j : Fin 3), (i ≠ j) → (D.edgeArc (v i) (v (i + 1)) ∩ D.edgeArc (v j)
            (v (j + 1)) = D.position '' (({v i, v (i + 1)} : Set ι) ∩ {v j, v (j + 1)}))) → (∀ (x
            : ℝ × ℝ), ∀ (k : Fin (3 : ℕ)), ∀ (l : Fin (3 : ℕ)), (¬k = l) → ((x ∈ D.edgeArc (v k)
            (v (k + 1)) ∩ D.edgeArc (v l) (v (l + 1))) → (x ∈ D.position '' ({v k, v (k + 1)} ∩
            {v l, v (l + 1)})))) ) := by
  classical
  intro ι P D f v arc_inter x k l hkl hxarc
  rw [← arc_inter k l hkl]
  exact hxarc

private theorem hxi :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀
            (k : Fin (3 : ℕ)), Function.Injective (g k)) → (∀ (k : Fin (3 : ℕ)), ∀ (s : (k
            : Fin (3 : ℕ)) → P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (k : Fin 3), ∀ (r : Fin (s k).count), ∀ (x : Real × Real), (x ∈ segment Real (w k
            r.castSucc) (w k r.succ)) → ((x = D.position (v k)) → (x = w k r.castSucc ∨ x = w k
            r.succ))) → ((∀ (k : Fin 3), ∀ (r : Fin (s k).count), ∀ (x : Real × Real), (x ∈
            segment Real (w k r.castSucc) (w k r.succ)) → ((x = D.position (v (k + 1))) → (x = w
            k r.castSucc ∨ x = w k r.succ))) → (∀ (x : ℝ × ℝ), ∀ (r : Fin (s k).count), (x ∈
            segment ℝ (w k r.castSucc) (w k r.succ)) → (∀ (u : ι), (D.position u = x) → ((u = v k
            ∨ u = v (k + (1 : Fin (3 : ℕ)))) → (x = w k r.castSucc ∨ x = w k r.succ))))))) := by
  classical
  intro ι P D f g hi k s τ w v piece_start_corner piece_finish_corner x r hx1 u hux huk
  rcases huk with huk | huk
  · apply piece_start_corner k r x hx1
    exact hux.symm.trans (congrArg D.position huk)
  · apply piece_finish_corner k r x hx1
    exact hux.symm.trans (congrArg D.position huk)

private theorem hxj :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
            P.plane.Face), ∀ (g : Fin (3 : ℕ) → (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → ℝ × ℝ), (∀
            (k : Fin (3 : ℕ)), Function.Injective (g k)) → ((Fin (3 : ℕ)) → (∀ (s : (k
            : Fin (3 : ℕ)) → P3723T1PolygonalParameterization (g k)),
        let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
          ⟨(s k).time i, by
            constructor
            · have hi := (s k).strict.monotone (Fin.zero_le i)
              rw [(s k).start] at hi
              exact hi
            · have hi := (s k).strict.monotone (Fin.le_last i)
              rw [(s k).finish] at hi
              exact hi⟩
        let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
        let v : Fin 3 → ι := P.plane.faceVertex f
        (∀ (k : Fin 3), ∀ (r : Fin (s k).count), ∀ (x : Real × Real), (x ∈ segment Real (w k
            r.castSucc) (w k r.succ)) → ((x = D.position (v k)) → (x = w k r.castSucc ∨ x = w k
            r.succ))) → ((∀ (k : Fin 3), ∀ (r : Fin (s k).count), ∀ (x : Real × Real), (x ∈
            segment Real (w k r.castSucc) (w k r.succ)) → ((x = D.position (v (k + 1))) → (x = w
            k r.castSucc ∨ x = w k r.succ))) → (∀ (x : ℝ × ℝ), ∀ (l : Fin (3 : ℕ)), ∀ (r' : Fin
            (s l).count), (x ∈ segment ℝ (w l r'.castSucc) (w l r'.succ)) → (∀ (u : ι),
                (D.position u = x) → ((u = v l ∨ u = v (l + (1 : Fin (3 : ℕ)))) → (x = w l
            r'.castSucc ∨ x = w l r'.succ)))))))) := by
  classical
  intro ι P D f g hi k s τ w v piece_start_corner piece_finish_corner x l r' hx2 u hux hul
  rcases hul with hul | hul
  · apply piece_start_corner l r' x hx2
    exact hux.symm.trans (congrArg D.position hul)
  · apply piece_finish_corner l r' x hx2
    exact hux.symm.trans (congrArg D.position hul)

end RoutedFaceDetails

theorem P3913T1RoutedFaceSubdivision :
    ∀ {ι : Type}, ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (f :
        P.plane.Face), ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), (∀ k, Continuous (g
        k)) → ((∀ k, Function.Injective (g k)) → ((∀ k, Set.range (g k) =
      D.edgeArc (P.plane.faceVertex f k) (P.plane.faceVertex f (k + 1))) → ((∀ k, g k ⟨0,
          by norm_num⟩ = D.position (P.plane.faceVertex f k)) → ((∀ k, g k ⟨1, by norm_num⟩ =
          D.position (P.plane.faceVertex f (k + 1))) → (∀ (s : ∀ k,
              P3723T1PolygonalParameterization (g k)), ∃ (n : Nat) (p : Fin (n + 3) → Real ×
              Real),
      n + 3 = ∑ k : Fin 3, (s k).count ∧
      Function.Injective p ∧
      (∀ i j : Fin (n + 3), i ≠ j →
        segment Real (p i) (p (i + 1)) ∩ segment Real (p j) (p (j + 1)) =
          {x | (x = p i ∨ x = p (i + 1)) ∧
            (x = p j ∨ x = p (j + 1))}) ∧
      (⋃ i, segment Real (p i) (p (i + 1))) =
        D.edgeArc (P.plane.faceVertex f 0) (P.plane.faceVertex f 1) ∪
          D.edgeArc (P.plane.faceVertex f 1) (P.plane.faceVertex f 2) ∪
          D.edgeArc (P.plane.faceVertex f 2) (P.plane.faceVertex f 0) ∧
      (∀ k, ∀ (i : Fin ((s k).count + 1)), ∃ t : Set.Icc (0 : Real) 1,
          (t : Real) = (s k).time i ∧ g k t ∈ Set.range p)))))) := by
  intro ι P D f g hc hi hr h0 h1 s
-- BODY
  classical
  let m0 := (s 0).count
  let m1 := (s 1).count
  let m2 := (s 2).count
  let M := m0 + (m1 + m2)
  have hsum : (∑ k : Fin 3, (s k).count) = M := by
    simp [Fin.sum_univ_succ, M, m0, m1, m2]
  let n := M - 3
  have hM := RoutedFaceDetails.hM g s hsum
  let τ (k : Fin 3) (i : Fin ((s k).count + 1)) : Set.Icc (0 : Real) 1 :=
    ⟨(s k).time i, by
      constructor
      · have hi := (s k).strict.monotone (Fin.zero_le i)
        rw [(s k).start] at hi
        exact hi
      · have hi := (s k).strict.monotone (Fin.le_last i)
        rw [(s k).finish] at hi
        exact hi⟩
  let w (k : Fin 3) (i : Fin ((s k).count + 1)) := g k (τ k i)
  let q : Fin M → Real × Real :=
    Fin.addCases
      (fun i : Fin m0 => w 0 i.castSucc)
      (Fin.addCases
        (fun i : Fin m1 => w 1 i.castSucc)
        (fun i : Fin m2 => w 2 i.castSucc))
  let p : Fin (n + 3) → Real × Real := fun i => q (Fin.cast hM i)
  have piece_range (k : Fin 3) (r : Fin ((s k).count)) :
      Set.range (fun t : Set.Icc ((s k).time r.castSucc) ((s k).time r.succ) =>
        g k ⟨t.1, by
          constructor
          · exact (τ k r.castSucc).property.1.trans t.property.1
          · exact t.property.2.trans (τ k r.succ).property.2⟩) =
        segment Real (w k r.castSucc) (w k r.succ) := RoutedSubdivisionProof.piece_range g hi s k r
  have q0 (i : Fin m0) := RoutedFaceDetails.q0 g hi s i
  have q1 (i : Fin m1) := RoutedFaceDetails.q1 g hi s i
  have q2 (i : Fin m2) := RoutedFaceDetails.q2 g hi s i
  have p_at (i : Fin M) : p (Fin.cast hM.symm i) = q i := by
    simp [p]
  have join (k : Fin 3) :
      w k (Fin.last (s k).count) = w (k + 1) 0 := RoutedSubdivisionProof.join ι P D f g hi h0 h1 s k
  let v : Fin 3 → ι := P.plane.faceVertex f
  have arc_inter (i j : Fin 3) (hij : i ≠ j) := RoutedFaceDetails.arc_inter ι P D f
      (RoutedSubdivisionProof.pair_ne ι P f g s)
      (RoutedFaceDetails.faceContact ι P f (RoutedFaceDetails.cyc_ne)) i j hij
  have v_distinct (i j : Fin 3) (hij : i ≠ j) := RoutedFaceDetails.v_distinct ι P f i
      j hij
  have v01 : v 0 ≠ v 1 := v_distinct 0 1 (by decide)
  have v02 : v 0 ≠ v 2 := v_distinct 0 2 (by decide)
  have v12 : v 1 ≠ v 2 := v_distinct 1 2 (by decide)
  have arc_inter_singleton (i j : Fin 3) (hij : i ≠ j) := RoutedFaceDetails.arc_inter_singleton ι
            P D f arc_inter (RoutedFaceDetails.pair_inter ι P f v_distinct) i j hij
  have w_arc (k : Fin 3) (i : Fin ((s k).count + 1)) := RoutedFaceDetails.w_arc ι P D f g hi hr s
      k i
  have w_before_end (k : Fin 3) (i : Fin (s k).count) := RoutedFaceDetails.w_before_end g hi s k i
  have w_start (k : Fin 3) := RoutedFaceDetails.w_start ι P D f g hi
      h0 s k
  have w_ne_finish (k : Fin 3) (i : Fin (s k).count) :
      w k i.castSucc ≠ D.position (v (k + 1)) := RoutedSubdivisionProof.w_ne_finish ι P D f g hi
          s (RoutedFaceDetails.w_finish ι P D f g hi h1 s) k i
  have q_injective : Function.Injective q := RoutedSubdivisionProof.q_injective g hi s q0 q1 q2
      (RoutedFaceDetails.no_cross01 ι P D f g s w_arc w_ne_finish (RoutedFaceDetails.arc01 ι P
          D f arc_inter_singleton)) (RoutedFaceDetails.no_cross12 ι P D f g s w_arc
          w_ne_finish (RoutedFaceDetails.arc12 ι P D f arc_inter_singleton))
          (RoutedFaceDetails.no_cross02 ι P D f g s w_arc w_ne_finish (RoutedFaceDetails.arc20
          ι P D f arc_inter_singleton)) (RoutedFaceDetails.w_block_injective g hi s)
  let b0 (i : Fin m0) : Fin M := Fin.castAdd (m1 + m2) i
  let b1 (i : Fin m1) : Fin M := Fin.natAdd m0 (Fin.castAdd m2 i)
  let b2 (i : Fin m2) : Fin M := Fin.natAdd m0 (Fin.natAdd m1 i)
  have hM' : n + 3 = m0 + (m1 + m2) := by simpa [M] using hM
  have p_edge_piece (i : Fin (n + 3)) :
      ∃ k : Fin 3, ∃ r : Fin (s k).count,
        p i = w k r.castSucc ∧ p (i + 1) = w k r.succ := RoutedSubdivisionProof.p_edge_piece g hi
            s hM q0 q2 join (RoutedSubdivisionProof.q_step g hi s hM q0 q1 q2 join) i
  have piece_subset_arc (k : Fin 3) (r : Fin (s k).count) := RoutedFaceDetails.piece_subset_arc ι
      P D f g hi hr s piece_range k r
  have piece_start_corner (k : Fin 3) (r : Fin (s k).count) (x : Real × Real)
      (hx : x ∈ segment Real (w k r.castSucc) (w k r.succ))
      (hc : x = D.position (v k)) :
      x = w k r.castSucc ∨ x = w k r.succ := RoutedSubdivisionProof.piece_start_corner ι P D f g
          hi h0 s piece_range k r x hx hc
  have piece_finish_corner (k : Fin 3) (r : Fin (s k).count) (x : Real × Real)
      (hx : x ∈ segment Real (w k r.castSucc) (w k r.succ))
      (hc : x = D.position (v (k + 1))) :
      x = w k r.castSucc ∨ x = w k r.succ := RoutedSubdivisionProof.piece_finish_corner ι P D f g
          hi h1 s piece_range k r x hx hc
  have endpoint_mem (a b x : Real × Real) (h : x = a ∨ x = b) := RoutedFaceDetails.endpoint_mem a
      b x h
  refine ⟨n, p, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hsum]
  · intro i j hij
    apply Fin.cast_injective hM
    apply q_injective
    simpa [p] using hij
  · intro i j hij
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx1, hx2⟩
      obtain ⟨k, r, hli, hri⟩ := p_edge_piece i
      obtain ⟨l, r', hlj, hrj⟩ := p_edge_piece j
      rw [hli, hri] at hx1
      rw [hlj, hrj] at hx2
      by_cases hkl : k = l
      · subst l
        by_cases hrr : r = r'
        · subst r'
          have hpi : p i = p j := hli.trans hlj.symm
          exact (hij ((RoutedFaceDetails.p_injective g hi s hM q_injective) hpi)).elim
        · have hend := (RoutedSubdivisionProof.piece_overlap g hi s
            (RoutedSubdivisionProof.piece_overlap_forward g hi s piece_range)) k r r' hrr x hx1 hx2
          simpa [hli, hri, hlj, hrj] using hend
      · have hxarc :
            x ∈ D.edgeArc (v k) (v (k + 1)) ∩ D.edgeArc (v l) (v (l + 1)) :=
          ⟨piece_subset_arc k r hx1, piece_subset_arc l r' hx2⟩
        obtain ⟨u, hu, hux⟩ := (RoutedFaceDetails.hxpos ι P D f arc_inter x k l hkl hxarc)
        rcases hu with ⟨huk, hul⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huk hul
        have hxi := RoutedFaceDetails.hxi ι P D f g hi k s
            piece_start_corner piece_finish_corner x r hx1 u hux huk
        have hxj := RoutedFaceDetails.hxj ι P D f g hi k
            s piece_start_corner piece_finish_corner x l r' hx2 u hux hul
        simpa [hli, hri, hlj, hrj] using And.intro hxi hxj
    · intro hx
      rcases hx with ⟨hxi, hxj⟩
      exact ⟨endpoint_mem (p i) (p (i + 1)) x hxi,
        endpoint_mem (p j) (p (j + 1)) x hxj⟩
  · calc
      (⋃ i : Fin (n + 3), segment Real (p i) (p (i + 1))) =
          ⋃ k : Fin 3, ⋃ r : Fin (s k).count,
            segment Real (w k r.castSucc) (w k r.succ) := (RoutedSubdivisionProof.edge_union g hi
                s hM p_edge_piece (RoutedSubdivisionProof.block_edge g hi s hM q0 q1 q2 join
                (RoutedFaceDetails.fin_succ_val g s)))
      _ = ⋃ k : Fin 3, D.edgeArc (v k) (v (k + 1)) := (RoutedSubdivisionProof.piece_arc_union ι P
          D f g hi s (RoutedSubdivisionProof.arc_covered ι P D f g hi hr s piece_range
          (RoutedSubdivisionProof.finite_interval_cover g s)))
      _ = D.edgeArc (v 0) (v 1) ∪ D.edgeArc (v 1) (v 2) ∪
          D.edgeArc (v 2) (v 0) := (RoutedSubdivisionProof.arc_union ι P D f)
  · intro k i
    refine ⟨τ k i, rfl, ?_⟩
    exact (RoutedSubdivisionProof.retained g hi s hM q0 q1 q2 p_at join) k i

end ApollonianSuperharmonic

end
