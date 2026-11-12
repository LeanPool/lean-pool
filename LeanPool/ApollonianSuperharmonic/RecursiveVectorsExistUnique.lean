/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PrimitiveVectorOrientationUnique
public import LeanPool.ApollonianSuperharmonic.RecursiveVectorSystem
public import LeanPool.ApollonianSuperharmonic.P4981T1PrescriptionCoherence
public import LeanPool.ApollonianSuperharmonic.P4981T1PrescriptionLocality
public import LeanPool.ApollonianSuperharmonic.P4981T1ProperEquations
public import LeanPool.ApollonianSuperharmonic.P4981T1RootEquations

-- [TABLET NODE: RecursiveVectorsExistUnique]

/-!
# RecursiveVectorsExistUnique

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem RecursiveVectorsExistUnique :
    ∃! s : (CircleCoordinates → CircleCoordinates → GaussianInt) ×
      (CircleCoordinates → CircleCoordinates → GaussianInt),
      RecursiveVectorSystem s := by
-- BODY
  classical
  let E := CircleCoordinates × CircleCoordinates
  let V := GaussianInt × GaussianInt
  let rank : E → ℕ := P4981T1EdgeRank
  let ii : GaussianInt := ⟨0, 1⟩
  let turn : V → V := fun x => (ii * x.1, -ii * x.2)
  have source : ∀ {C D}, PrimitiveVectorOrientation C D →
      Nonempty (P4981T1EdgePrescription (C, D)) := by
    intro C D h
    cases h with
    | base32 z => exact ⟨.line⟩
    | base21 z => exact ⟨.left z⟩
    | base31 z => exact ⟨.right z⟩
    | base10 z => exact ⟨.unit z⟩
    | parentChild hq j => exact ⟨.proper _ hq j⟩
  have oriented : ∀ {e : E}, P4981T1EdgePrescription e →
      PrimitiveVectorOrientation e.1 e.2 := by
    intro e p
    cases p with
    | line => exact .base32 0
    | left z => exact .base21 z
    | right z => exact .base31 z
    | unit z => exact .base10 z
    | proper q hq j => exact .parentChild hq j
  let choose := fun C D (h : PrimitiveVectorOrientation C D) =>
    Classical.choice (source h)
  have rank_swap (C D : CircleCoordinates) : rank (D, C) = rank (C, D) := by
    simp only [rank, P4981T1EdgeRank, max_comm]
  have noReverse {C D} (h : PrimitiveVectorOrientation C D) :
      ¬ PrimitiveVectorOrientation D C := by
    rcases ((PrimitiveVectorOrientationUnique C D).2
      ((PrimitiveVectorOrientationUnique C D).1 h)).2 with h' | h'
    · exact h'.2
    · exact (h'.2 h).elim
  have tangent_symm {C D} (h : BandTangency D C) : BandTangency C D := by
    rcases h with ⟨q, hq, i, j, hij, hi, hj⟩
    exact ⟨q, hq, j, i, Ne.symm hij, hj, hi⟩
  -- Recursion calls only lower-rank ordered edges.  A reverse is evaluated
  -- from the same primitive prescription, never by a same-rank call.
  let step : (e : E) → (∀ d : E, rank d < rank e → V) → V := fun e rec =>
    let low : E → V := fun d => if h : rank d < rank e then rec d h else (0, 0)
    if h : PrimitiveVectorOrientation e.1 e.2 then
      P4981T1PrescriptionValue (choose e.1 e.2 h) low
    else if h : PrimitiveVectorOrientation e.2 e.1 then
      turn (P4981T1PrescriptionValue (choose e.2 e.1 h) low)
    else (0, 0)
  let F : E → V := (measure rank).wf.fix step
  have unfoldF (e : E) : F e = step e (fun d _ => F d) :=
    (measure rank).wf.fix_eq step e
  have table {e : E} (p : P4981T1EdgePrescription e) :
      F e = P4981T1PrescriptionValue p F := by
    rw [unfoldF]
    dsimp only [step]
    rw [dite_eq_left (oriented p)]
    trans P4981T1PrescriptionValue p
      (fun d => if _h : rank d < rank e then F d else (0, 0))
    · exact P4981T1PrescriptionCoherence _ p _
    · apply P4981T1PrescriptionLocality
      intro d hd
      exact dite_eq_left hd
  have rev (C D : CircleCoordinates) (h : PrimitiveVectorOrientation C D) :
      F (D, C) = turn (F (C, D)) := by
    rw [unfoldF]
    dsimp only [step]
    rw [dite_eq_right (noReverse h), dite_eq_left h]
    congr 1
    trans P4981T1PrescriptionValue (choose C D h) F
    · apply P4981T1PrescriptionLocality
      intro d hd
      exact dite_eq_left (by simpa only [rank_swap] using hd)
    · exact (table _).symm
  have zero (C D : CircleCoordinates) (h : ¬ BandTangency C D) :
      F (C, D) = (0, 0) := by
    have hn : ¬ PrimitiveVectorOrientation C D :=
      fun hp => h ((PrimitiveVectorOrientationUnique C D).1 hp)
    have hn' : ¬ PrimitiveVectorOrientation D C :=
      fun hp => h (tangent_symm ((PrimitiveVectorOrientationUnique D C).1 hp))
    rw [unfoldF]
    dsimp only [step]
    rw [dite_eq_right hn, dite_eq_right hn']
  have root := (P4981T1RootEquations F rev).mpr
    ⟨table .line, fun z => ⟨table (.left z), table (.right z), table (.unit z)⟩⟩
  have proper := (P4981T1ProperEquations F rev).mp
    (fun q hq j => table (.proper q hq j))
  refine ⟨(fun C D => (F (C, D)).1, fun C D => (F (C, D)).2), ?_, ?_⟩
  · refine ⟨?_, root.1, ?_, ?_⟩
    · intro C D h
      exact ⟨congrArg Prod.fst (zero C D h), congrArg Prod.snd (zero C D h)⟩
    · intro q hq
      change P4981T1Recursion F q
      rcases (SemiProperForestClassification q hq).2 with h | h | h | h
      · obtain ⟨z, rfl⟩ := h
        exact root.2 z 0
      · obtain ⟨z, rfl⟩ := h
        exact root.2 z 1
      · obtain ⟨z, rfl⟩ := h
        exact root.2 z 2
      · exact proper q h
    · intro C D h
      exact ⟨congrArg Prod.fst (rev C D h), congrArg Prod.snd (rev C D h)⟩
  · intro t ht
    rcases ht with ⟨hz, hb, hr, hv⟩
    let G : E → V := fun e => (t.1 e.1 e.2, t.2 e.1 e.2)
    have Grev (C D : CircleCoordinates) (h : PrimitiveVectorOrientation C D) :
        G (D, C) = turn (G (C, D)) :=
      Prod.ext (hv C D h).1 (hv C D h).2
    have Groot := (P4981T1RootEquations G Grev).mp
      ⟨hb, by
        intro z r
        dsimp only [P4981T1Recursion, G]
        apply hr
        fin_cases r
        · convert SemiProperQuadruple.base z using 1
          funext k
          fin_cases k <;> rfl
        · convert SemiProperQuadruple.rotate (SemiProperQuadruple.base z) using 1
          funext k
          fin_cases k <;> rfl
        · convert SemiProperQuadruple.rotate
            (SemiProperQuadruple.rotate (SemiProperQuadruple.base z)) using 1
          funext k
          fin_cases k <;> rfl⟩
    have Gproper := (P4981T1ProperEquations G Grev).mpr
      (fun q hq => hr q hq.1)
    have Gtable {e : E} (p : P4981T1EdgePrescription e) :
        G e = P4981T1PrescriptionValue p G := by
      cases p with
      | line => exact Groot.1
      | left z => exact (Groot.2 z).1
      | right z => exact (Groot.2 z).2.1
      | unit z => exact (Groot.2 z).2.2
      | proper q hq j => exact Gproper q hq j
    have equal : ∀ e, G e = F e := by
      intro e
      induction e using (measure rank).wf.induction with
      | h e ih =>
        by_cases hp : PrimitiveVectorOrientation e.1 e.2
        · rw [Gtable (choose _ _ hp), table (choose _ _ hp)]
          exact P4981T1PrescriptionLocality _ G F ih
        · by_cases hp' : PrimitiveVectorOrientation e.2 e.1
          · have primitive : G (e.2, e.1) = F (e.2, e.1) := by
              rw [Gtable (choose _ _ hp'), table (choose _ _ hp')]
              apply P4981T1PrescriptionLocality
              intro d hd
              apply ih d
              change rank d < rank (e.1, e.2)
              change rank d < rank (e.2, e.1) at hd
              rwa [rank_swap e.1 e.2] at hd
            change G (e.1, e.2) = F (e.1, e.2)
            rw [Grev _ _ hp', rev _ _ hp', primitive]
          · have hn : ¬ BandTangency e.1 e.2 := by
              intro ht
              rcases ((PrimitiveVectorOrientationUnique e.1 e.2).2 ht).2 with h | h
              · exact hp h.1
              · exact hp' h.1
            rw [zero _ _ hn]
            exact Prod.ext (hz _ _ hn).1 (hz _ _ hn).2
    apply Prod.ext
    · funext C D
      exact congrArg Prod.fst (equal (C, D))
    · funext C D
      exact congrArg Prod.snd (equal (C, D))

end ApollonianSuperharmonic

end
