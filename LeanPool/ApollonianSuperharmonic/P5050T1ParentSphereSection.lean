/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4984T1ClosedGap
public import LeanPool.ApollonianSuperharmonic.P4828T1LineSupport
public import LeanPool.ApollonianSuperharmonic.P4953T1LiteralHulls
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity
public import LeanPool.ApollonianSuperharmonic.P5050T1TangentTriangleSection
public import LeanPool.ApollonianSuperharmonic.P5050T1TangentLineSection

-- [TABLET NODE: P5050T1ParentSphereSection]

/-!
# P5050T1ParentSphereSection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ParentSphereProof

private theorem circleDistance :
    (by
      classical
      exact
        ∀ (v : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple v → ∀ (i : Fin (4 : ℕ)), ∀
            (k : Fin (4 : ℕ)), i ≠ k → (0 : ℤ) < (v i).1 → (0 : ℤ) < (v k).1 → dist
            ((GaussianInt.toComplex : GaussianInt → ℂ) (v i).2 / (↑(v i).1 : ℂ))
            ((GaussianInt.toComplex : GaussianInt → ℂ) (v k).2 / (↑(v k).1 : ℂ)) = (1 : ℝ) / (↑(v
            i).1 : ℝ) + (1 : ℝ) / (↑(v k).1 : ℝ) ) := by
  classical
  intro v hv i k hik hi hk
  let w : GaussianInt := (v k).1 • (v i).2 - (v i).1 • (v k).2
  have ht := TangencyCoordinateIdentity v hv.1 i k hik
  have normCast (w : GaussianInt) :
      Complex.normSq (w : Complex) = (Zsqrtd.norm w : Real) := by
    simp [Complex.normSq, Zsqrtd.norm_def]
  have hn : Complex.normSq (w : Complex) =
      (((v i).1 + (v k).1 : ℤ)^2 : Real) := by
    change Complex.normSq
        (((v k).1 • (v i).2 - (v i).1 • (v k).2 : GaussianInt) : Complex) = _
    rw [normCast]
    exact_mod_cast ht
  have hnsq : ‖(w : Complex)‖ ^ 2 =
      (((v i).1 + (v k).1 : ℤ) : Real) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hn]
  have hnorm : ‖(w : Complex)‖ =
      (((v i).1 + (v k).1 : ℤ) : Real) := by
    have hnonneg := norm_nonneg (w : Complex)
    have hsum : 0 ≤ (((v i).1 + (v k).1 : ℤ) : Real) := by positivity
    nlinarith
  have hdiff :
      ((v i).2 : Complex) / (v i).1 - ((v k).2 : Complex) / (v k).1 =
        (w : Complex) / (((v i).1 * (v k).1 : ℤ) : Complex) := by
    dsimp [w]
    push_cast
    simp only [map_sub, map_zsmul]
    have hia : (v i).1 ≠ 0 := ne_of_gt hi
    have hkb : (v k).1 ≠ 0 := ne_of_gt hk
    field_simp [hia, hkb]
    ring
  rw [Complex.dist_eq, hdiff, Complex.norm_div, Complex.norm_intCast, hnorm]
  have ha : 0 < ((v i).1 : Real) := by exact_mod_cast hi
  have hb : 0 < ((v k).1 : Real) := by exact_mod_cast hk
  have hab : 0 < (((v i).1 * (v k).1 : ℤ) : Real) := by
    exact_mod_cast mul_pos hi hk
  rw [abs_of_pos hab]
  push_cast
  field_simp [ne_of_gt ha, ne_of_gt hb]
  ring

private theorem parentHull :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (v : Fin (4 : ℕ) → CircleCoordinates), (∀ (i : Fin (3 : ℕ)), (0 : ℤ) < (v
            i.succ).1) → P4909T1ParentPolygon L v = (convexHull ℝ : Set ℂ → Set ℂ) (Set.range
            fun (i : Fin (3 : ℕ)) => (GaussianInt.toComplex : GaussianInt → ℂ) (v i.succ).2 /
            (↑(↑(v i.succ).1 : ℝ) : ℂ)) ) := by
  classical
  intro L v hv
  unfold P4909T1ParentPolygon
  apply congrArg (convexHull Real)
  ext z
  constructor
  · rintro ⟨i, hi, hz | ⟨k, hk, hz⟩⟩
    · exact ⟨i, hz.symm⟩
    · exact False.elim ((ne_of_gt (hv k)) hk)
  · rintro ⟨i, rfl⟩
    exact ⟨i, hv i, Or.inl rfl⟩

private theorem positiveSection :
    (by
      classical
      exact
        ∀ (L : ℝ), (∀ (v : Fin 4 → CircleCoordinates), (ProperBandQuadruple v) → (∀ (i : Fin 4),
            ∀ (k : Fin 4), (i ≠ k) → ((0 < (v i).1) → ((0 < (v k).1) → (dist (((v i).2 : Complex)
            / (v i).1) (((v k).2 : Complex) / (v k).1) = 1 / (v i).1 + 1 / (v k).1))))) → ((∀ (v
            : Fin 4 → CircleCoordinates), (∀ i : Fin 3, 0 < (v i.succ).1) →
            (P4909T1ParentPolygon L v = convexHull Real (Set.range fun i : Fin 3 => ((v
            i.succ).2 : Complex) / ((v i.succ).1 : Real)))) → (∀ (v : Fin (4 : ℕ) →
            CircleCoordinates), ProperBandQuadruple v → ∀ (m : Fin (3 : ℕ)), (0 : ℤ) < (v
            m.succ).1 → (∀ (i : Fin (3 : ℕ)), (0 : ℤ) < (v i.succ).1) → IsPreconnected
            (P4984T1ClosedGap L v ∩ Metric.sphere ((GaussianInt.toComplex : GaussianInt → ℂ) (v
            m.succ).2 / (↑(↑(v m.succ).1 : ℝ) : ℂ)) ((1 : ℝ) / (↑(v m.succ).1 : ℝ))))) ) := by
  classical
  intro L circleDistance parentHull v hv m hm hall
  let pv (i : Fin 4) : Complex := (v i).2 / ((v i).1 : Real)
  let rv (i : Fin 4) : Real := 1 / ((v i).1 : Real)
  let center := pv m.succ
  let ρ := rv m.succ
  let b : Fin 3 := if m = 0 then 1 else 0
  let c : Fin 3 := if m = 2 then 1 else 2
  have hb : b ≠ m := by fin_cases m <;> simp [b]
  have hc : c ≠ m := by fin_cases m <;> simp [c]
  have hbc : b ≠ c := by fin_cases m <;> simp [b, c]
  have hcenters : Set.range (fun i : Fin 3 => pv i.succ) =
      {center, pv b.succ, pv c.succ} := by
    fin_cases m
    · ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff,
        center, b, c, pv]
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i
        · subst z; exact Or.inl rfl
        · subst z; exact Or.inr (Or.inl rfl)
        · subst z; exact Or.inr (Or.inr rfl)
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
    · ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff,
        center, b, c, pv]
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i
        · subst z; exact Or.inr (Or.inl rfl)
        · subst z; exact Or.inl rfl
        · subst z; exact Or.inr (Or.inr rfl)
      · rintro (rfl | rfl | rfl)
        · exact ⟨1, rfl⟩
        · exact ⟨0, rfl⟩
        · exact ⟨2, rfl⟩
    · ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff,
        center, b, c, pv]
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i
        · subst z; exact Or.inr (Or.inl rfl)
        · subst z; exact Or.inr (Or.inr rfl)
        · subst z; exact Or.inl rfl
      · rintro (rfl | rfl | rfl)
        · exact ⟨2, rfl⟩
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
  have hpoly : P4909T1ParentPolygon L v =
      convexHull Real ({center, pv b.succ, pv c.succ} : Set Complex) := by
    rw [parentHull v hall, ← hcenters]
  have hgapEq : P4984T1ClosedGap L v ∩ Metric.sphere center ρ =
      Metric.sphere center ρ ∩ P4909T1ParentPolygon L v := by
    ext z
    constructor
    · rintro ⟨⟨hzpoly, _⟩, hz⟩
      exact ⟨hz, hzpoly⟩
    · rintro ⟨hz, hzpoly⟩
      refine ⟨⟨hzpoly, ?_⟩, hz⟩
      intro k hk
      by_cases hkm : k = m
      · subst k
        have hdist : dist z center = ρ := Metric.mem_sphere.mp hz
        simpa [pv, rv, center, ρ] using (le_of_eq hdist.symm)
      · have hdist := circleDistance v hv m.succ k.succ
          (fun heq => hkm (Fin.succ_inj.mp heq).symm) hm (hall k)
        have htri := dist_triangle center z (pv k.succ)
        have hcz : dist center z = ρ := by
          simpa [dist_comm] using (Metric.mem_sphere.mp hz)
        rw [hcz] at htri
        have hradDist : dist center (pv k.succ) = ρ + rv k.succ := by
          simpa [center, pv, ρ, rv] using hdist
        rw [hradDist] at htri
        dsimp [P4984T1ClosedGap]
        have hradle : rv k.succ ≤ dist z (pv k.succ) :=
          (add_le_add_iff_left ρ).mp htri
        simpa [rv, pv] using hradle
  have hdistab : dist center (pv b.succ) = ρ + rv b.succ := by
    have hd := circleDistance v hv m.succ b.succ
      (fun heq => hb (Fin.succ_inj.mp heq).symm) hm (hall b)
    simpa [center, ρ, rv, pv] using hd
  have hdistac : dist center (pv c.succ) = ρ + rv c.succ := by
    have hd := circleDistance v hv m.succ c.succ
      (fun heq => hc (Fin.succ_inj.mp heq).symm) hm (hall c)
    simpa [center, ρ, rv, pv] using hd
  have hdistbc : dist (pv b.succ) (pv c.succ) = rv b.succ + rv c.succ := by
    have hd := circleDistance v hv b.succ c.succ
      (fun heq => hbc (Fin.succ_inj.mp heq)) (hall b) (hall c)
    simpa [rv, pv] using hd
  have htri := P5050T1TangentTriangleSection center (pv b.succ) (pv c.succ) ρ
    (rv b.succ) (rv c.succ)
    (one_div_pos.mpr (by exact_mod_cast hm : 0 < ((v m.succ).1 : Real)))
    (le_of_lt (one_div_pos.mpr
      (by exact_mod_cast hall b : 0 < ((v b.succ).1 : Real))))
    (le_of_lt (one_div_pos.mpr
      (by exact_mod_cast hall c : 0 < ((v c.succ).1 : Real))))
    hdistab hdistac hdistbc
  rw [hgapEq, hpoly]
  exact htri

private theorem signed :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin 4 → CircleCoordinates), (P4828T1LineSupport L q) → (∀ (l : Fin (3
            : ℕ)), ((q l.succ).1 = (0 : ℤ)) → (
        let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
        let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
        let h : ℝ := if (q l.succ).2 = -1 then L else L + 2
        let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
        ∀ (i : Fin (4 : ℕ)), (0 : ℤ) < (q i).1 → σ * ((p i).re - h) = r i)) ) := by
  classical
  intro L q hs l hl p r h σ i hi
  have hh := hs.signed l.succ i hl hi
  have hc : ((q i).1 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hi
  have hp : (p i).re = (q i).2.re / (q i).1 := by
    simp [p]
  rcases hs.normals l.succ hl with hn | hn
  · simp [σ, h, hn, hp, r]
    rw [hn] at hh
    norm_num at hh
    field_simp [hc]
    linarith
  · have hne : (q l.succ).2 ≠ -1 := by rw [hn]; norm_num
    simp [σ, h, hne, hp, r]
    rw [hn] at hh
    norm_num at hh
    field_simp [hc]
    linarith

private theorem heq :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (j : Fin 3),
            ((0 : ℤ) < (q j.succ).1) → ((∀ (v : Fin 4 → CircleCoordinates), (ProperBandQuadruple
            v) → (∀ (i : Fin 4), ∀ (k : Fin 4), (i ≠ k) → ((0 < (v i).1) → ((0 < (v k).1) → (dist
            (((v i).2 : Complex) / (v i).1) (((v k).2 : Complex) / (v k).1) = 1 / (v i).1 + 1 /
            (v k).1))))) → (
        let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
        let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
        P4984T1ClosedGap L q ∩ Metric.sphere (p j.succ) (r j.succ) = Metric.sphere (p j.succ)
            (r j.succ) ∩ P4909T1ParentPolygon L q))) ) := by
  classical
  intro L q hq j hj circleDistance p r
  ext z
  constructor
  · rintro ⟨⟨hz, _⟩, hsph⟩
    exact ⟨hsph, hz⟩
  · rintro ⟨hsph, hz⟩
    refine ⟨⟨hz, ?_⟩, hsph⟩
    intro k hk
    have hdist : dist z (p j.succ) = r j.succ := Metric.mem_sphere.mp hsph
    by_cases hkj : k = j
    · subst k
      exact hdist.ge
    · have hd := circleDistance q hq j.succ k.succ
        (fun he => hkj (Fin.succ_inj.mp he).symm) hj hk
      have ht := dist_triangle (p j.succ) z (p k.succ)
      rw [dist_comm (p j.succ) z, hdist] at ht
      change dist (p j.succ) (p k.succ) = r j.succ + r k.succ at hd
      rw [hd] at ht
      change r k.succ ≤ dist z (p k.succ)
      linarith

end ParentSphereProof

theorem P5050T1ParentSphereSection (L : ℝ)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hs : P4828T1LineSupport L q) (j : Fin 3) (hj : 0 < (q j.succ).1) :
    IsPreconnected (P4984T1ClosedGap L q ∩
      Metric.sphere ((q j.succ).2 / ((q j.succ).1 : ℝ))
        (1 / ((q j.succ).1 : ℝ))) := by
-- BODY
  classical
  have circleDistance (v : Fin 4 → CircleCoordinates)
      (hv : ProperBandQuadruple v) (i k : Fin 4) (hik : i ≠ k)
      (hi : 0 < (v i).1) (hk : 0 < (v k).1) :
      dist (((v i).2 : Complex) / (v i).1)
          (((v k).2 : Complex) / (v k).1) =
        1 / (v i).1 + 1 / (v k).1 := ParentSphereProof.circleDistance v hv i k hik hi hk
  have parentHull (v : Fin 4 → CircleCoordinates)
      (hv : ∀ i : Fin 3, 0 < (v i.succ).1) :
      P4909T1ParentPolygon L v =
        convexHull Real (Set.range fun i : Fin 3 =>
          ((v i.succ).2 : Complex) / ((v i.succ).1 : Real)) := ParentSphereProof.parentHull L v hv
  have positiveSection (v : Fin 4 → CircleCoordinates)
      (hv : ProperBandQuadruple v) (m : Fin 3)
      (hm : 0 < (v m.succ).1)
      (hall : ∀ i : Fin 3, 0 < (v i.succ).1) :
      IsPreconnected
        (P4984T1ClosedGap L v ∩
          Metric.sphere ((v m.succ).2 / ((v m.succ).1 : Real))
            (1 / ((v m.succ).1 : Real))) := ParentSphereProof.positiveSection L circleDistance
                parentHull v hv m hm hall
  by_cases hall : ∀ i : Fin 3, 0 < (q i.succ).1
  · exact positiveSection q hq j hj hall
  · have facts := ProperBandCurvatureStructure q hq
    obtain ⟨l, hl⟩ : ∃ l : Fin 3, (q l.succ).1 = 0 := by
      by_contra hn
      push Not at hn
      exact hall (fun i => lt_of_le_of_ne (facts.2.1 i) (Ne.symm (hn i)))
    have hjl : j ≠ l := by
      intro he
      subst j
      omega
    obtain ⟨b, hbl, hbj⟩ : ∃ b : Fin 3, b ≠ l ∧ b ≠ j := by
      fin_cases l <;> fin_cases j
      all_goals try exact (hjl rfl).elim
      all_goals first
        | exact ⟨0, by decide, by decide⟩
        | exact ⟨1, by decide, by decide⟩
        | exact ⟨2, by decide, by decide⟩
    have hb : 0 < (q b.succ).1 := by
      have hn : (q b.succ).1 ≠ 0 := fun he => hbl (facts.2.2 b l he hl)
      exact lt_of_le_of_ne (facts.2.1 b) (Ne.symm hn)
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    let h : ℝ := if (q l.succ).2 = -1 then L else L + 2
    let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
    have hσ : σ ^ 2 = 1 := by
      dsimp [σ]
      split_ifs <;> norm_num
    have signed (i : Fin 4) (hi : 0 < (q i).1) :
        σ * ((p i).re - h) = r i := ParentSphereProof.signed L q hs l hl i hi
    have hab : dist (p j.succ) (p b.succ) = r j.succ + r b.succ :=
      circleDistance q hq j.succ b.succ
        (fun he => hbj (Fin.succ_inj.mp he).symm) hj hb
    have hhull := (P4953T1LiteralHulls L q l j b hjl hbl hbj.symm
      hl hj hb facts.1).1
    have hsec := (P5050T1TangentLineSection h σ (p j.succ) (p b.succ)
      (r j.succ) (r b.succ) hσ
      (one_div_pos.mpr (by exact_mod_cast hj))
      (one_div_pos.mpr (by exact_mod_cast hb))
      (signed j.succ hj) (signed b.succ hb) hab).2.2
    have heq : P4984T1ClosedGap L q ∩ Metric.sphere (p j.succ) (r j.succ) =
        Metric.sphere (p j.succ) (r j.succ) ∩ P4909T1ParentPolygon L q := ParentSphereProof.heq
            L q hq j hj circleDistance
    change IsPreconnected (P4984T1ClosedGap L q ∩
      Metric.sphere (p j.succ) (r j.succ))
    rw [heq, hhull]
    exact hsec

end ApollonianSuperharmonic

end
