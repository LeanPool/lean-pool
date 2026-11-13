/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity

public import LeanPool.ApollonianSuperharmonic.P5023T1ContactVertices
public import LeanPool.ApollonianSuperharmonic.P4828T1Gap
public import LeanPool.ApollonianSuperharmonic.P4828T1LineSupport
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity
public import LeanPool.ApollonianSuperharmonic.P4828T1Disk

-- [TABLET NODE: P5023T1CircularSide]

/-!
# P5023T1CircularSide

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CircularSideProof

private theorem hR :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        (0 < (q 0).1) → (0 < rad 0) ) := by
  classical
  intro q rad hchild
  dsimp [rad]
  exact one_div_pos.mpr (by exact_mod_cast hchild)

private theorem hr :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let rad (a : Fin 4) : ℝ := 1 /
        ((q a).1 : ℝ)
        (0 < (q i.succ).1) → (0 < rad i.succ) ) := by
  classical
  intro q i rad hparent
  dsimp [rad]
  exact one_div_pos.mpr (by exact_mod_cast hparent)

private theorem hRr :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let rad (a : Fin 4) : ℝ := 1 /
        ((q a).1 : ℝ)
        (0 < (q i.succ).1) → (((q i.succ).1 < (q 0).1) → (rad 0 < rad i.succ)) ) := by
  classical
  intro q i rad hparent hless
  dsimp [rad]
  exact (one_div_lt_one_div_of_lt (by exact_mod_cast hparent) (by exact_mod_cast hless))

private theorem hjpos :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let j : Fin 3 := i + 1
        (∀ a : Fin 3, 0 ≤ (q a.succ).1) → (0 < (q j.succ).1 ∨ (q j.succ).1 = 0) ) := by
  classical
  intro q i j other_nonneg
  have h := other_nonneg j
  rcases lt_or_eq_of_le h with hp | hz
  · exact Or.inl hp
  · exact Or.inr hz.symm

private theorem hkpos :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let k : Fin 3 := i + 2
        (∀ a : Fin 3, 0 ≤ (q a.succ).1) → (0 < (q k.succ).1 ∨ (q k.succ).1 = 0) ) := by
  classical
  intro q i k other_nonneg
  have h := other_nonneg k
  rcases lt_or_eq_of_le h with hp | hz
  · exact Or.inl hp
  · exact Or.inr hz.symm

private theorem hnotbothzero :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let j : Fin 3 := i + 1
        let k : Fin 3 := i + 2
        (∀ a b : Fin 3, (q a.succ).1 = 0 → (q b.succ).1 = 0 → a = b) → ((j ≠ k) → (¬ ((q j.succ).1 =
        0 ∧ (q k.succ).1 = 0))) ) := by
  classical
  intro q i j k other_unique hjk hz
  have heq := other_unique j k hz.1 hz.2
  exact hjk heq

private theorem centerDistance :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple q) → (
        let p (a : Fin 4) : ℂ :=
        (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        ∀ (a : Fin (4 : ℕ)), ∀ (b : Fin (4 : ℕ)), a ≠ b → (0 : ℤ) < (q a).1 → (0 : ℤ) < (q b).1 →
        dist (p a) (p b) = rad a + rad b) ) := by
  classical
  intro q hq p rad a b hab ha hb
  let w : GaussianInt := (q b).1 • (q a).2 - (q a).1 • (q b).2
  have ht := TangencyCoordinateIdentity q hq.1 a b hab
  have normCast (z : GaussianInt) : Complex.normSq (z : ℂ) = (Zsqrtd.norm z : ℝ) := by
    simp [Complex.normSq, Zsqrtd.norm_def]
  have hn : Complex.normSq (w : ℂ) = (((q a).1 + (q b).1 : ℤ) ^ 2 : ℝ) := by
    change Complex.normSq (((q b).1 • (q a).2 - (q a).1 • (q b).2 : GaussianInt) : ℂ) = _
    rw [normCast]
    exact_mod_cast ht
  have hnsq : ‖(w : ℂ)‖ ^ 2 = (((q a).1 + (q b).1 : ℤ) : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hn]
  have hsum : 0 ≤ (((q a).1 + (q b).1 : ℤ) : ℝ) := by positivity
  have hnorm : ‖(w : ℂ)‖ = (((q a).1 + (q b).1 : ℤ) : ℝ) := by
    have := norm_nonneg (w : ℂ)
    nlinarith
  have hdiff : p a - p b =
      (w : ℂ) / (((q a).1 * (q b).1 : ℤ) : ℂ) := by
    dsimp [p, w]
    push_cast
    simp only [map_sub, map_zsmul]
    field_simp [ne_of_gt ha, ne_of_gt hb]
    ring
  rw [Complex.dist_eq, hdiff, Complex.norm_div, Complex.norm_intCast, hnorm]
  have haR : 0 < ((q a).1 : ℝ) := by exact_mod_cast ha
  have hbR : 0 < ((q b).1 : ℝ) := by exact_mod_cast hb
  have habR : 0 < (((q a).1 * (q b).1 : ℤ) : ℝ) := by exact_mod_cast mul_pos ha hb
  rw [abs_of_pos habR]
  push_cast
  dsimp [rad]
  field_simp [ne_of_gt haR, ne_of_gt hbR]
  ring

private theorem hchild_parent :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let p (a : Fin 4) : ℂ := (q
        a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        (0 < (q 0).1) → ((0 < (q i.succ).1) → ((∀ (a : Fin 4), ∀ (b : Fin 4), (a ≠ b) → ((0 < (q
        a).1) → ((0 < (q b).1) → (dist (p a) (p b) = rad a + rad b)))) → (dist (p 0) (p i.succ) =
        rad 0 + rad i.succ))) ) := by
  classical
  intro q i p rad hchild hparent centerDistance
  apply centerDistance 0 i.succ
  · exact (Fin.succ_ne_zero i).symm
  · exact hchild
  · exact hparent

private theorem capBound :
    (by
      classical
      exact
        let dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im
        ∀ (x : ℂ), ∀ (y : ℂ), ∀ (e : ℂ), ∀ (t : ℝ), (Complex.normSq : ℂ → ℝ) x = (1 : ℝ) →
            (Complex.normSq : ℂ → ℝ) y = (1
        : ℝ) → (Complex.normSq : ℂ → ℝ) e = (1 : ℝ) → (0 : ℝ) ≤ t → t ≤ (1 : ℝ) → t ≤ dot x e → t
        ≤ dot y e → ‖x - y‖ ≤ (2 : ℝ) * √((1 : ℝ) - t ^ (2 : ℕ)) ) := by
  classical
  intro dot x y e t hx hy he ht0 ht1 hxd hyd
  have hsumdot : 2 * t ≤ dot (x + y) e := by
    dsimp [dot] at hxd hyd ⊢
    nlinarith
  have cauchy2 (v : ℂ) : dot v e ^ 2 ≤ Complex.normSq v := by
    dsimp [dot]
    rw [Complex.normSq_apply]
    have he' := he
    rw [Complex.normSq_apply] at he'
    nlinarith [sq_nonneg (e.re * v.im - e.im * v.re)]
  have hplus : 4 * t ^ 2 ≤ Complex.normSq (x + y) := by
    have := cauchy2 (x + y)
    have hnonneg : 0 ≤ dot (x + y) e := le_trans (by positivity) hsumdot
    nlinarith
  have hsum : Complex.normSq (x - y) + Complex.normSq (x + y) = 4 := by
    repeat rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
    have hx' := hx
    have hy' := hy
    rw [Complex.normSq_apply] at hx' hy'
    nlinarith [hx', hy']
  have hminus : Complex.normSq (x - y) ≤ 4 * (1 - t ^ 2) := by nlinarith
  have hrad : 0 ≤ 1 - t ^ 2 := by nlinarith
  have hminus' := hminus
  rw [Complex.normSq_eq_norm_sq] at hminus'
  have hnorm : ‖x - y‖ ^ 2 ≤ (2 * Real.sqrt (1 - t ^ 2)) ^ 2 := by
    nlinarith [hminus', Real.sq_sqrt hrad]
  have hleft : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hright : 0 ≤ 2 * Real.sqrt (1 - t ^ 2) := by positivity
  nlinarith

private theorem hcenterNorm :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let p (a : Fin 4) : ℂ := (q
        a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        (dist (p 0) (p i.succ) = rad 0 + rad i.succ) → (
        let A : ℂ := p i.succ
        let X : ℂ := p 0
        ‖X - A‖ = rad i.succ + rad 0) ) := by
  classical
  intro q i p rad hchild_parent A X
  rw [dist_eq_norm] at hchild_parent
  simpa [A, X, add_comm] using hchild_parent

private theorem heNorm :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let p (a : Fin 4) : ℂ := (q
        a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        (0 < rad i.succ + rad 0) → (
        let A : ℂ := p i.succ
        let X : ℂ := p 0
        let e : ℂ := (X - A) / ((rad i.succ + rad 0 : ℝ) : ℂ)
        (‖X - A‖ = rad i.succ + rad 0) → (‖e‖ = 1)) ) := by
  classical
  intro q i p rad hden A X e hcenterNorm
  dsimp [e]
  rw [Complex.norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hden, hcenterNorm]
  exact div_self (ne_of_gt hden)

private theorem heSq :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let p (a : Fin 4) : ℂ := (q
        a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        let A : ℂ := p i.succ
        let X : ℂ := p 0
        let e : ℂ := (X - A) / ((rad i.succ + rad 0 : ℝ) : ℂ)
        (‖e‖ = 1) → (Complex.normSq e = 1) ) := by
  classical
  intro q i p rad A X e heNorm
  rw [Complex.normSq_eq_norm_sq, heNorm]
  norm_num

private theorem hv₁ :
    (by
      classical
      exact
        ∀ (L : ℝ) (q : Fin (4 : ℕ) → CircleCoordinates)
          (i : Fin (3 : ℕ)),
          let p := fun (a : Fin (4 : ℕ)) =>
            (GaussianInt.toComplex : GaussianInt → ℂ) (q a).2 / (↑(↑(q a).1 : ℝ) : ℂ);
          let k := i + (2 : Fin (3 : ℕ));
          (q i.succ).1 ≠ (0 : ℤ) →
            let v₁ :=
              P5023T1ContactVertices L q
                (i + (1 : Fin (3 : ℕ)));
            v₁ =
              if (q k.succ).1 = (0 : ℤ) then
                { re := if (q k.succ).2 = (-1 : GaussianInt) then L else L + (2 : ℝ),
                  im := (p i.succ).im }
              else
                ((GaussianInt.toComplex : GaussianInt → ℂ) (q i.succ).2 +
                    (GaussianInt.toComplex : GaussianInt → ℂ) (q k.succ).2) /
                  ((↑(↑(q i.succ).1 : ℝ) : ℂ) + (↑(↑(q k.succ).1 : ℝ) : ℂ))) := by
  classical
  intro L q i p k hparne v₁
  fin_cases i
  · have hp : (q (1 : Fin 4)).1 ≠ 0 := by simpa using hparne
    simp [v₁, P5023T1ContactVertices, p, k, hp, add_comm]
  · have hp : (q (2 : Fin 4)).1 ≠ 0 := by simpa using hparne
    simp [v₁, P5023T1ContactVertices, p, k, hp, add_comm]
  · have hp : (q (3 : Fin 4)).1 ≠ 0 := by simpa using hparne
    simp [v₁, P5023T1ContactVertices, p, k, hp, add_comm]

private theorem hv₂ :
    (by
      classical
      exact
        ∀ (L : ℝ) (q : Fin (4 : ℕ) → CircleCoordinates)
          (i : Fin (3 : ℕ)),
          let p := fun (a : Fin (4 : ℕ)) =>
            (GaussianInt.toComplex : GaussianInt → ℂ) (q a).2 / (↑(↑(q a).1 : ℝ) : ℂ);
          let j := i + (1 : Fin (3 : ℕ));
          (q i.succ).1 ≠ (0 : ℤ) →
            let v₂ :=
              P5023T1ContactVertices L q
                (i + (2 : Fin (3 : ℕ)));
            v₂ =
              if (q j.succ).1 = (0 : ℤ) then
                { re := if (q j.succ).2 = (-1 : GaussianInt) then L else L + (2 : ℝ),
                  im := (p i.succ).im }
              else
                ((GaussianInt.toComplex : GaussianInt → ℂ) (q i.succ).2 +
                    (GaussianInt.toComplex : GaussianInt → ℂ) (q j.succ).2) /
                  ((↑(↑(q i.succ).1 : ℝ) : ℂ) + (↑(↑(q j.succ).1 : ℝ) : ℂ))) := by
  classical
  intro L q i p j hparne v₂
  fin_cases i
  · have hp : (q (1 : Fin 4)).1 ≠ 0 := by simpa using hparne
    simp [v₂, P5023T1ContactVertices, p, j, hp, add_comm]
  · have hp : (q (2 : Fin 4)).1 ≠ 0 := by simpa using hparne
    simp [v₂, P5023T1ContactVertices, p, j, hp]
  · have hp : (q (3 : Fin 4)).1 ≠ 0 := by simpa using hparne
    simp [v₂, P5023T1ContactVertices, p, j, hp, add_comm]

private theorem ht0 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let rad (a : Fin 4) : ℝ := 1 /
        ((q a).1 : ℝ)
        (rad 0 < rad i.succ) → ((0 < rad i.succ + rad 0) → (
        let t : ℝ := (rad i.succ - rad 0) / (rad
        i.succ + rad 0)
        0 ≤ t)) ) := by
  classical
  intro q i rad hRr hden t
  dsimp [t]
  exact (div_nonneg (sub_nonneg.mpr hRr.le) hden.le)

private theorem ht1 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let rad (a : Fin 4) : ℝ := 1 /
        ((q a).1 : ℝ)
        (0 < rad 0) → ((0 < rad i.succ + rad 0) → (
        let t : ℝ := (rad i.succ - rad 0) / (rad i.succ +
        rad 0)
        t ≤ 1)) ) := by
  classical
  intro q i rad hR hden t
  dsimp [t]
  rw [div_le_one hden]
  linarith

private theorem normSqSubDot :
    (by
      classical
      exact
        let dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im
        ∀ (x : ℂ), ∀ (y : ℂ), (Complex.normSq : ℂ → ℝ) (x - y) = (Complex.normSq : ℂ → ℝ) x +
            (Complex.normSq
        : ℂ → ℝ) y - (2 : ℝ) * dot x y ) := by
  classical
  intro dot x y
  rw [Complex.normSq_sub]
  simp [dot, Complex.mul_re, Complex.conj_re, Complex.conj_im]

private theorem dotDiv :
    (by
      classical
      exact
        let dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im
        ∀ (x : ℂ), ∀ (y : ℂ), ∀ (c : ℝ), ∀ (d : ℝ), c ≠ (0 : ℝ) → d ≠ (0 : ℝ) → dot (x / (↑c :
            ℂ)) (y / (↑d : ℂ)) = dot x
        y / (c * d) ) := by
  classical
  intro dot x y c d hc hd
  rw [Complex.div_ofReal, Complex.div_ofReal]
  simp [dot]
  field_simp


private theorem hne4 :
    (by
      classical
      exact
        ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 : ℕ)), a ≠ i → a.succ ≠ i.succ
    ) := by
  classical
  intro i a hne h
  have hv := congrArg Fin.val h
  simp only [Fin.val_succ] at hv
  have heq : a.val = i.val := by omega
  exact hne (Fin.ext heq)

private theorem hrel :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 :
            ℕ)),
        let p (a : Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
        (0 < (q i.succ).1) → (
        let A : ℂ := p i.succ
        ((q i.succ).1 ≠ 0) → (
        let V (a : Fin 3) : ℂ :=
        if (q a.succ).1 = 0 then
        ⟨if (q a.succ).2 = -1 then L else L + 2, A.im⟩
        else
        ((q i.succ).2 + (q a.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q a.succ).1 : ℝ))
        ((0 : ℤ) < (q a.succ).1) → ((0 < (q a.succ).1) → (V a - A = ((q a.succ).1 : ℂ) / ((((q
        i.succ).1 + (q a.succ).1 : ℤ) : ℂ)) * (p a.succ - A))))) ) := by
  classical
  intro L q i a p hparent A hparne V hapos haposZ
  dsimp [V, A, p]
  rw [ite_eq_right haposZ.ne']
  push_cast
  have hsumZ : (q i.succ).1 + (q a.succ).1 ≠ 0 := by omega
  have hsumC : ((q i.succ).1 : ℂ) + (q a.succ).1 ≠ 0 := by
    exact_mod_cast hsumZ
  have hkiC : ((q i.succ).1 : ℂ) ≠ 0 := by exact_mod_cast hparne
  have hkaC : ((q a.succ).1 : ℂ) ≠ 0 := by exact_mod_cast haposZ.ne'
  field_simp [hkiC, hkaC, hsumC]; ring

private theorem hsumRad :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 : ℕ)),
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        (0 < (q i.succ).1) → (((0 : ℤ) < (q a.succ).1) → (rad i.succ + rad a.succ = (((q i.succ).1 +
        (q a.succ).1 : ℤ) : ℝ) / (((q i.succ).1 * (q
        a.succ).1 : ℤ) : ℝ))) ) := by
  classical
  intro q i a rad hparent hapos
  dsimp [rad]
  push_cast
  have hsumZ : (q i.succ).1 + (q a.succ).1 ≠ 0 := by omega
  field_simp [hparent.ne', hapos.ne', hsumZ]; ring

private theorem hunitEq :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 :
            ℕ)),
        let p (a : Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ);
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ);
        (0 < (q i.succ).1) → (
        let A : ℂ := p i.succ;
        (
        let V (a : Fin 3) : ℂ :=
        if (q a.succ).1 = 0 then
        ⟨if (q a.succ).2 = -1 then L else L + 2, A.im⟩
        else
        ((q i.succ).2 + (q a.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q a.succ).1 : ℝ));
        ((0 : ℤ) < (q a.succ).1) → (
        ((V a - A = ((q a.succ).1 : ℂ) / ((((q
        i.succ).1 + (q a.succ).1 : ℤ) : ℂ)) * (p a.succ - A)) → ((rad i.succ + rad a.succ = (((q
        i.succ).1 + (q a.succ).1 : ℤ) : ℝ) / (((q i.succ).1 * (q a.succ).1 : ℤ) : ℝ)) → ((V a -
        A) / (rad i.succ : ℂ) = (p a.succ - A) / ((rad i.succ + rad a.succ : ℝ) : ℂ))))))) ) := by
  classical
  intro L q i a p rad hparent A V hapos hrel hsumRad
  rw [hrel]
  rw [hsumRad]
  dsimp [rad]
  push_cast
  have hsumZ : (q i.succ).1 + (q a.succ).1 ≠ 0 := by omega
  field_simp [hparent.ne', hapos.ne', hsumZ]


private theorem hdistParent :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 : ℕ)),
        let p (a :
        Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        let A : ℂ := p i.succ
        (dist (p a.succ) (p i.succ) = rad a.succ + rad i.succ) → (‖p a.succ - A‖ = rad i.succ + rad
        a.succ) ) := by
  classical
  intro q i a p rad A hcenter
  rw [dist_eq_norm] at hcenter
  simpa [A, add_comm] using hcenter

private theorem hunitNorm :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 :
            ℕ)),
        let p (a : Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        (0 < (q i.succ).1) → (
        let A : ℂ := p i.succ
        let V (a : Fin 3) : ℂ :=
        if (q a.succ).1 = 0 then
        ⟨if (q a.succ).2 = -1 then L else L + 2, A.im⟩
        else
        ((q i.succ).2 + (q a.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q a.succ).1 : ℝ))
        ((0 : ℤ) < (q a.succ).1) → (((V a - A) / (rad i.succ : ℂ) = (p a.succ - A) / ((rad i.succ +
        rad a.succ : ℝ) : ℂ)) → ((‖p a.succ - A‖ = rad i.succ + rad a.succ) → (‖(V a - A) / (rad
        i.succ : ℂ)‖ = 1)))) ) := by
  classical
  intro L q i a p rad hparent A V hapos hunitEq hdistParent
  rw [hunitEq, Complex.norm_div, hdistParent, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < rad i.succ + rad a.succ)]
  exact div_self (ne_of_gt (by positivity : 0 < rad i.succ + rad a.succ))

private theorem hunitSqAt360 :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 :
            ℕ)),
        let p (a : Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        let A : ℂ := p i.succ
        let V (a : Fin 3) : ℂ :=
        if (q a.succ).1 = 0 then
        ⟨if (q a.succ).2 = -1 then L else L + 2, A.im⟩
        else
        ((q i.succ).2 + (q a.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q a.succ).1 : ℝ))
        (‖(V a - A) / (rad i.succ : ℂ)‖ = 1) → (Complex.normSq ((V a - A) / (rad i.succ : ℂ)) =
            1) ) := by
  classical
  intro L q i a p rad A V hunitNorm
  rw [Complex.normSq_eq_norm_sq, hunitNorm]
  norm_num

private theorem hX :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ∀ (i : Fin (3 : ℕ)),
            let p (a : Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
            let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
            dist (p 0) (p i.succ) = rad 0 + rad i.succ →
              let A : ℂ := p i.succ
              let X : ℂ := p 0
              Complex.normSq (X - A) = (rad i.succ + rad 0) ^ 2
    ) := by
  classical
  intro q i p rad hchild_parent A X
  rw [Complex.normSq_eq_norm_sq, ← dist_eq_norm]
  have hh := congrArg (fun x : ℝ => x ^ 2) hchild_parent
  simpa [X, A, add_comm] using hh

private theorem hBX :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (a : Fin (3 : ℕ)),
        let p (a : Fin 4) : ℂ := (q
        a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        (dist (p a.succ) (p 0) = rad a.succ + rad 0) → (
        let X : ℂ := p 0
        Complex.normSq (p a.succ - X) = (rad a.succ + rad 0) ^ 2) ) := by
  classical
  intro q a p rad hchild X
  rw [Complex.normSq_eq_norm_sq, ← dist_eq_norm]
  have hh := congrArg (fun x : ℝ => x ^ 2) hchild
  simpa [X] using hh

private theorem hdotAt373 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 : ℕ)),
        let p (a :
        Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        let dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im
        let A : ℂ := p i.succ
        let X : ℂ := p 0
        (∀ (x : ℂ), ∀ (y : ℂ), Complex.normSq (x - y) = Complex.normSq x + Complex.normSq y - 2 *
            dot
        x y) → ((Complex.normSq (p a.succ - A) = (rad i.succ + rad a.succ) ^ 2) →
        ((Complex.normSq (X - A) = (rad i.succ + rad 0) ^ 2) → ((Complex.normSq (p a.succ - X) =
        (rad a.succ + rad 0) ^ 2) → (dot (p a.succ - A) (X - A) = ((rad i.succ + rad a.succ) ^ 2
        + (rad i.succ + rad 0) ^ 2 - (rad a.succ + rad 0) ^ 2) / 2)))) ) := by
  classical
  intro q i a p rad dot A X normSqSubDot hA hX hBX
  have hsub : (p a.succ - A) - (X - A) = p a.succ - X := by ring
  have hdiff : Complex.normSq ((p a.succ - A) - (X - A)) =
      (rad a.succ + rad 0) ^ 2 := by
    rw [hsub, hBX]
  have hformula := normSqSubDot (p a.succ - A) (X - A)
  rw [hA, hX] at hformula
  rw [hdiff] at hformula
  linear_combination hformula / 2

private theorem hdotUnit :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 :
            ℕ)),
        let p (a : Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        (0 < (q i.succ).1) → ((0 < rad i.succ + rad 0) → (
        let dot (x y : ℂ) : ℝ := x.re * y.re + x.im
        * y.im
        let A : ℂ := p i.succ
        let X : ℂ := p 0
        let e : ℂ := (X - A) / ((rad i.succ + rad 0 : ℝ) : ℂ)
        let V (a : Fin 3) : ℂ :=
        if (q a.succ).1 = 0 then
        ⟨if (q a.succ).2 = -1 then L else L + 2, A.im⟩
        else
        ((q i.succ).2 + (q a.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q a.succ).1 : ℝ))
        (∀ (x : ℂ), ∀ (y : ℂ), ∀ (c : ℝ), ∀ (d : ℝ), (c ≠ 0) → ((d ≠ 0) → (dot (x / (c : ℂ)) (y / (d
        : ℂ)) = dot x y / (c * d)))) → (((0 : ℤ) < (q a.succ).1) → (((V a - A) / (rad i.succ : ℂ)
        = (p a.succ - A) / ((rad i.succ + rad a.succ : ℝ) : ℂ)) → (dot ((V a - A) / (rad i.succ :
        ℂ)) e = dot (p a.succ - A) (X - A) / ((rad i.succ + rad a.succ) * (rad i.succ + rad
        0))))))) ) := by
  classical
  intro L q i a p rad hparent hden dot A X e V dotDiv hapos hunitEq
  rw [hunitEq]
  dsimp [e]
  exact dotDiv (p a.succ - A) (X - A) (rad i.succ + rad a.succ)
    (rad i.succ + rad 0) (by positivity) (ne_of_gt hden)

private theorem hextra :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 : ℕ)),
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ);
        ((0 < (q i.succ).1) → ((0 < rad 0) → ((0 <
        (rad i.succ + rad a.succ) * (rad i.succ + rad 0)) → (0 < (2 * rad i.succ * rad 0) / ((rad
        i.succ + rad a.succ) * (rad i.succ + rad 0)))))) ) := by
  classical
  intro q i a rad hparent hR hposden
  exact div_pos (by positivity) hposden

private theorem hid :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 : ℕ)),
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        (0 < (q i.succ).1) → ((0 < rad i.succ + rad 0) → (
        let t : ℝ := (rad i.succ - rad 0) / (rad i.succ + rad 0)
        ((0 : ℤ) < (q a.succ).1) → ((((rad i.succ + rad a.succ) ^ 2 + (rad i.succ + rad 0) ^ 2 -
            (rad
        a.succ + rad 0) ^ 2) / 2) /
        ((rad i.succ + rad a.succ) * (rad i.succ + rad 0)) = t + 2 * rad i.succ * rad 0 / ((rad
        i.succ + rad a.succ) * (rad i.succ + rad 0))))) ) := by
  classical
  intro q i a rad hparent hden t hapos
  dsimp [t]
  have hdenA : 0 < rad i.succ + rad a.succ := by positivity
  field_simp [ne_of_gt hden, ne_of_gt hdenA]; ring

private theorem signedDistance :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (P4828T1LineSupport L q) → (∀ (a : Fin
        (3 : ℕ)),
        let p (a : Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        ((q a.succ).1 = (0 : ℤ)) → (
        let H : ℝ := if (q a.succ).2 = -1 then L else L + 2
        let σ : ℝ := if (q a.succ).2 = -1 then 1 else -1
        ((q a.succ).2 = (-1 : GaussianInt) ∨ (q a.succ).2 = (1 : GaussianInt)) → (∀ (b : Fin (4 :
        ℕ)), (0 : ℤ) < (q b).1 → σ * ((p b).re - H) = rad b))) ) := by
  classical
  intro L q hs a p rad hazero H σ hnormal b hb
  have hsgn := hs.signed a.succ b hazero hb
  have hbcne : (q b).1 ≠ 0 := ne_of_gt hb
  have hpre : (p b).re = (q b).2.re / (q b).1 := by
    dsimp [p]
    rw [Complex.div_re]
    simp
    field_simp [hbcne]
  have hbre : ((q b).2 : ℂ).re = (q b).2.re := by norm_num
  by_cases hneg : (q a.succ).2 = -1
  · rw [hneg] at hsgn
    norm_num at hsgn
    rw [hbre] at hsgn
    simp only [H, σ, hneg, ite_eq_left, one_mul, rad]
    rw [hpre]
    field_simp [hbcne]
    nlinarith only [hsgn]
  · have hposLine : (q a.succ).2 = 1 := by
      rcases hnormal with hn | hp
      · exact (hneg hn).elim
      · exact hp
    rw [hposLine] at hsgn
    norm_num at hsgn
    rw [hbre] at hsgn
    simp only [H, σ, hneg, ite_false, neg_one_mul, rad]
    rw [hpre]
    field_simp [hbcne]
    nlinarith only [hsgn]

private theorem hσsq :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (a : Fin (3 : ℕ)),
        let σ : ℝ := if (q a.succ).2 = -1 then 1 else -1
        σ * σ = 1 ) := by
  classical
  intro q a σ
  dsimp [σ]
  split_ifs <;> norm_num

private theorem hcontact :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 :
            ℕ)),
        let p (a : Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        (0 < rad i.succ) → (
        let A : ℂ := p i.succ
        let V (a : Fin 3) : ℂ :=
        if (q a.succ).1 = 0 then
        ⟨if (q a.succ).2 = -1 then L else L + 2, A.im⟩
        else
        ((q i.succ).2 + (q a.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q a.succ).1 : ℝ))
        let H : ℝ := if (q a.succ).2 = -1 then L else L + 2
        let σ : ℝ := if (q a.succ).2 = -1 then 1 else -1
        ((q a.succ).2 = (-1 : GaussianInt) ∨ (q a.succ).2 = (1 : GaussianInt)) → ((σ * ((p
            i.succ).re
        - H) = rad i.succ) → ((V a = ⟨H, A.im⟩) → ((V a - A) / (rad i.succ : ℂ) = (-σ : ℂ))))) )
            := by
  classical
  intro L q i a p rad hr A V H σ hnormal hAline hVline
  have hdiff : V a - A = (-(σ * rad i.succ) : ℝ) := by
    apply Complex.ext
    · rw [hVline]
      simp only [Complex.sub_re, Complex.ofReal_re]
      rcases hnormal with hneg | hposLine
      · have hH : H = L := by simp [H, hneg]
        have hS : σ = 1 := by simp [σ, hneg]
        rw [hH, hS] at hAline ⊢
        nlinarith [hAline]
      · have hnotneg : (q a.succ).2 ≠ -1 := by
          rw [hposLine]
          norm_num
        have hH : H = L + 2 := by simp [H, hnotneg]
        have hS : σ = -1 := by simp [σ, hnotneg]
        rw [hH, hS] at hAline ⊢
        linear_combination hAline
    · rw [hVline]
      simp only [Complex.sub_im, Complex.ofReal_im, sub_self]
  rw [hdiff]
  push_cast
  have hrC : (rad i.succ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  field_simp [hrC]


private theorem hunitSqAt473 :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 :
            ℕ)),
        let p (a : Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        let A : ℂ := p i.succ
        let V (a : Fin 3) : ℂ :=
        if (q a.succ).1 = 0 then
        ⟨if (q a.succ).2 = -1 then L else L + 2, A.im⟩
        else
        ((q i.succ).2 + (q a.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q a.succ).1 : ℝ))
        let σ : ℝ := if (q a.succ).2 = -1 then 1 else -1
        (σ * σ = 1) → (((V a - A) / (rad i.succ : ℂ) = (-σ : ℂ)) → (Complex.normSq ((V a - A) / (rad
        i.succ : ℂ)) = 1)) ) := by
  classical
  intro L q i a p rad A V σ hσsq hcontact
  rw [hcontact]
  simp [Complex.normSq_apply, hσsq]

private theorem hdiffSigned :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 :
            ℕ)),
        let p (a : Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        let A : ℂ := p i.succ
        let X : ℂ := p 0
        let H : ℝ := if (q a.succ).2 = -1 then L else L + 2
        let σ : ℝ := if (q a.succ).2 = -1 then 1 else -1
        (σ * ((p i.succ).re - H) = rad i.succ) → ((σ * ((p (0 : Fin (4 : ℕ))).re - H) = rad (0 : Fin
        (4 : ℕ))) → (σ * ((X.re) - A.re) = rad 0 - rad i.succ)) ) := by
  classical
  intro L q i a p rad A X H σ hAline hXline
  calc
    σ * (X.re - A.re) = σ * (X.re - H) - σ * (A.re - H) := by ring
    _ = rad 0 - rad i.succ := by rw [hXline, hAline]

private theorem hdotSigned :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 : ℕ)),
        let p (a :
        Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        let A : ℂ := p i.succ
        let X : ℂ := p 0
        let σ : ℝ := if (q a.succ).2 = -1 then 1 else -1
        (σ * ((X.re) - A.re) = rad 0 - rad i.succ) → ((-σ) * (X.re - A.re) = rad i.succ - rad 0)
            ) := by
  classical
  intro q i a p rad A X σ hdiffSigned
  calc
    (-σ) * (X.re - A.re) = -(σ * (X.re - A.re)) := by ring
    _ = -(rad 0 - rad i.succ) := by rw [hdiffSigned]
    _ = rad i.succ - rad 0 := by abel

private theorem hdotAt485 :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (a : Fin (3 :
            ℕ)),
        let p (a : Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        let dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im
        let A : ℂ := p i.succ
        let X : ℂ := p 0
        let e : ℂ := (X - A) / ((rad i.succ + rad 0 : ℝ) : ℂ)
        let V (a : Fin 3) : ℂ :=
        if (q a.succ).1 = 0 then
        ⟨if (q a.succ).2 = -1 then L else L + 2, A.im⟩
        else
        ((q i.succ).2 + (q a.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q a.succ).1 : ℝ))
        let t : ℝ := (rad i.succ - rad 0) / (rad i.succ + rad 0)
        let σ : ℝ := if (q a.succ).2 = -1 then 1 else -1
        ((V a - A) / (rad i.succ : ℂ) = (-σ : ℂ)) → (((-σ) * (X.re - A.re) = rad i.succ - rad 0) →
        (dot ((V a - A) / (rad i.succ : ℂ)) e = t)) ) := by
  classical
  intro L q i a p rad dot A X e V t σ hcontact hdotSigned
  rw [hcontact]
  dsimp [e]
  have hdotDiv : dot (-σ : ℂ) ((X - A) / ((rad i.succ + rad 0 : ℝ) : ℂ)) =
      ((-σ) * (X.re - A.re)) / (rad i.succ + rad 0) := by
    rw [Complex.div_ofReal]
    simp [dot, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [hdotDiv]
  dsimp [t]
  rw [hdotSigned]

private theorem hn₁ :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let p (a : Fin 4) :
        ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        let k : Fin 3 := i + 2
        let dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im
        let A : ℂ := p i.succ
        let X : ℂ := p 0
        let e : ℂ := (X - A) / ((rad i.succ + rad 0 : ℝ) : ℂ)
        let v₁ : ℂ := P5023T1ContactVertices L q (i + 1)
        let V (a : Fin 3) : ℂ :=
        if (q a.succ).1 = 0 then
        ⟨if (q a.succ).2 = -1 then L else L + 2, A.im⟩
        else
        ((q i.succ).2 + (q a.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q a.succ).1 : ℝ))
        (v₁ = V k) → (
        let t : ℝ := (rad i.succ - rad 0) / (rad i.succ + rad 0)
        ((Complex.normSq : ℂ → ℝ) ((V k - A) / (↑(rad i.succ) : ℂ)) = (1 : ℝ) ∧ t ≤ dot ((V k - A) /
        (↑(rad i.succ) : ℂ)) e) → (Complex.normSq ((v₁ - A) / (rad i.succ : ℂ)) = 1)) ) := by
  classical
  intro L q i p rad k dot A X e v₁ V hv₁V t hkfacts
  rw [hv₁V]
  exact hkfacts.1

private theorem hn₂ :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let p (a : Fin 4) :
        ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        let j : Fin 3 := i + 1
        let dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im
        let A : ℂ := p i.succ
        let X : ℂ := p 0
        let e : ℂ := (X - A) / ((rad i.succ + rad 0 : ℝ) : ℂ)
        let v₂ : ℂ := P5023T1ContactVertices L q (i + 2)
        let V (a : Fin 3) : ℂ :=
        if (q a.succ).1 = 0 then
        ⟨if (q a.succ).2 = -1 then L else L + 2, A.im⟩
        else
        ((q i.succ).2 + (q a.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q a.succ).1 : ℝ))
        (v₂ = V j) → (
        let t : ℝ := (rad i.succ - rad 0) / (rad i.succ + rad 0)
        ((Complex.normSq : ℂ → ℝ) ((V j - A) / (↑(rad i.succ) : ℂ)) = (1 : ℝ) ∧ t ≤ dot ((V j - A) /
        (↑(rad i.succ) : ℂ)) e) → (Complex.normSq ((v₂ - A) / (rad i.succ : ℂ)) = 1)) ) := by
  classical
  intro L q i p rad j dot A X e v₂ V hv₂V t hjfacts
  rw [hv₂V]
  exact hjfacts.1

private theorem hdot₁ :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let p (a : Fin 4) :
        ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        let k : Fin 3 := i + 2
        let dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im
        let A : ℂ := p i.succ
        let X : ℂ := p 0
        let e : ℂ := (X - A) / ((rad i.succ + rad 0 : ℝ) : ℂ)
        let v₁ : ℂ := P5023T1ContactVertices L q (i + 1)
        let V (a : Fin 3) : ℂ :=
        if (q a.succ).1 = 0 then
        ⟨if (q a.succ).2 = -1 then L else L + 2, A.im⟩
        else
        ((q i.succ).2 + (q a.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q a.succ).1 : ℝ))
        (v₁ = V k) → (
        let t : ℝ := (rad i.succ - rad 0) / (rad i.succ + rad 0)
        ((Complex.normSq : ℂ → ℝ) ((V k - A) / (↑(rad i.succ) : ℂ)) = (1 : ℝ) ∧ t ≤ dot ((V k - A) /
        (↑(rad i.succ) : ℂ)) e) → (t ≤ dot ((v₁ - A) / (rad i.succ : ℂ)) e)) ) := by
  classical
  intro L q i p rad k dot A X e v₁ V hv₁V t hkfacts
  rw [hv₁V]
  exact hkfacts.2

private theorem hdot₂ :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let p (a : Fin 4) :
        ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        let j : Fin 3 := i + 1
        let dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im
        let A : ℂ := p i.succ
        let X : ℂ := p 0
        let e : ℂ := (X - A) / ((rad i.succ + rad 0 : ℝ) : ℂ)
        let v₂ : ℂ := P5023T1ContactVertices L q (i + 2)
        let V (a : Fin 3) : ℂ :=
        if (q a.succ).1 = 0 then
        ⟨if (q a.succ).2 = -1 then L else L + 2, A.im⟩
        else
        ((q i.succ).2 + (q a.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q a.succ).1 : ℝ))
        (v₂ = V j) → (
        let t : ℝ := (rad i.succ - rad 0) / (rad i.succ + rad 0)
        ((Complex.normSq : ℂ → ℝ) ((V j - A) / (↑(rad i.succ) : ℂ)) = (1 : ℝ) ∧ t ≤ dot ((V j - A) /
        (↑(rad i.succ) : ℂ)) e) → (t ≤ dot ((v₂ - A) / (rad i.succ : ℂ)) e)) ) := by
  classical
  intro L q i p rad j dot A X e v₂ V hv₂V t hjfacts
  rw [hv₂V]
  exact hjfacts.2

private theorem hchord :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let p (a : Fin 4) :
        ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        let dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im
        (∀ (x : ℂ), ∀ (y : ℂ), ∀ (e : ℂ), ∀ (t : ℝ), (Complex.normSq x = 1) → ((Complex.normSq y
            = 1)
        → ((Complex.normSq e = 1) → ((0 ≤ t) → ((t ≤ 1) → ((t ≤ dot x e) → ((t ≤ dot y e) → (‖x -
        y‖ ≤ 2 * Real.sqrt (1 - t ^ 2))))))))) → (
        let A : ℂ := p i.succ
        let X : ℂ := p 0
        let e : ℂ := (X - A) / ((rad i.succ + rad 0 : ℝ) : ℂ)
        (Complex.normSq e = 1) → (
        let v₁ : ℂ := P5023T1ContactVertices L q (i + 1)
        let v₂ : ℂ := P5023T1ContactVertices L q (i + 2)
        let t : ℝ := (rad i.succ - rad 0) / (rad i.succ + rad 0)
        (0 ≤ t) → ((t ≤ 1) → ((Complex.normSq ((v₁ - A) / (rad i.succ : ℂ)) = 1) → ((Complex.normSq
        ((v₂ - A) / (rad i.succ : ℂ)) = 1) → ((t ≤ dot ((v₁ - A) / (rad i.succ : ℂ)) e) → ((t ≤
        dot ((v₂ - A) / (rad i.succ : ℂ)) e) → (‖(v₁ - A) / (rad i.succ : ℂ) - (v₂ - A) / (rad
        i.succ : ℂ)‖ ≤ 2 * Real.sqrt (1 - t ^ 2))))))))) ) := by
  classical
  intro L q i p rad dot capBound A X e heSq v₁ v₂ t ht0 ht1 hn₁ hn₂ hdot₁ hdot₂
  exact capBound _ _ e t hn₁ hn₂ heSq ht0 ht1 hdot₁ hdot₂

private theorem hscale :
    (by
      classical
      exact
        ∀ (L : ℝ), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let p (a : Fin 4) :
        ℂ := (q a).2 / ((q a).1 : ℝ)
        let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
        (0 < rad i.succ) → (
        let A : ℂ := p i.succ
        let v₁ : ℂ := P5023T1ContactVertices L q (i + 1)
        let v₂ : ℂ := P5023T1ContactVertices L q (i + 2)
        (∀ (x : ℝ), x / rad i.succ * rad i.succ = x) → (dist (P5023T1ContactVertices L q (i + 1))
        (P5023T1ContactVertices L q (i + 2)) = rad i.succ * ‖(v₁ - A) / (rad i.succ : ℂ) - (v₂
        - A) / (rad i.succ : ℂ)‖)) ) := by
  classical
  intro L q i p rad hr A v₁ v₂ cancelRadius
  change dist v₁ v₂ = rad i.succ *
    ‖(v₁ - A) / (rad i.succ : ℂ) - (v₂ - A) / (rad i.succ : ℂ)‖
  rw [dist_eq_norm]
  have hrC : (rad i.succ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hdiff : (v₁ - A) / (rad i.succ : ℂ) - (v₂ - A) / (rad i.succ : ℂ) =
      (v₁ - v₂) / (rad i.succ : ℂ) := by
    field_simp [hrC]; ring
  rw [hdiff, Complex.norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  calc
    ‖v₁ - v₂‖ = (‖v₁ - v₂‖ / rad i.succ) * rad i.succ :=
      (cancelRadius _).symm
    _ = rad i.succ * (‖v₁ - v₂‖ / rad i.succ) := mul_comm _ _

end CircularSideProof

theorem P5023T1CircularSide :
    ∀ (L : ℝ), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) →
        ((P4828T1LineSupport L q) → ((P4828T1Disk (q 0) ⊆ P4828T1Gap L q) → (∀ (i : Fin 3),
        (0 < (q i.succ).1) → (let r : ℝ := 1 / ((q i.succ).1 : ℝ)
    let R : ℝ := 1 / ((q 0).1 : ℝ)
    dist (P5023T1ContactVertices L q (i + 1))
      (P5023T1ContactVertices L q (i + 2)) ≤
        2 * r * Real.sqrt (1 - ((r - R) / (r + R)) ^ 2))))) := by
  intro L q hq hs hi i hpos
-- BODY
  exact ((show
      (let r : ℝ := 1 / ((q i.succ).1 : ℝ)
       let R : ℝ := 1 / ((q 0).1 : ℝ)
       dist (P5023T1ContactVertices L q (i + 1))
         (P5023T1ContactVertices L q (i + 2)) ≤
           2 * r * Real.sqrt (1 - ((r - R) / (r + R)) ^ 2)) from by
  dsimp only []
  let p (a : Fin 4) : ℂ := (q a).2 / ((q a).1 : ℝ)
  let rad (a : Fin 4) : ℝ := 1 / ((q a).1 : ℝ)
  let j : Fin 3 := i + 1
  let k : Fin 3 := i + 2
  have curv := ProperBandCurvatureStructure q hq
  have hchild : 0 < (q 0).1 := curv.1
  have hparent : 0 < (q i.succ).1 := hpos
  have hR : 0 < rad 0 := CircularSideProof.hR q hchild
  have hr : 0 < rad i.succ := CircularSideProof.hr q i hparent
  have hless : (q i.succ).1 < (q 0).1 := hq.2 i
  have hRr : rad 0 < rad i.succ := CircularSideProof.hRr q i hparent hless
  have hden : 0 < rad i.succ + rad 0 := by linarith
  have other_nonneg : ∀ a : Fin 3, 0 ≤ (q a.succ).1 := curv.2.1
  have other_unique : ∀ a b : Fin 3, (q a.succ).1 = 0 →
      (q b.succ).1 = 0 → a = b := curv.2.2
  have hji : j ≠ i := by fin_cases i <;> decide
  have hki : k ≠ i := by fin_cases i <;> decide
  have hjk : j ≠ k := by fin_cases i <;> decide
  have hjpos : 0 < (q j.succ).1 ∨ (q j.succ).1 = 0 := CircularSideProof.hjpos q i other_nonneg
  have hkpos : 0 < (q k.succ).1 ∨ (q k.succ).1 = 0 := CircularSideProof.hkpos q i other_nonneg
  have hnotbothzero : ¬ ((q j.succ).1 = 0 ∧ (q k.succ).1 = 0) := CircularSideProof.hnotbothzero q
      i other_unique hjk
  have centerDistance (a b : Fin 4) (hab : a ≠ b)
      (ha : 0 < (q a).1) (hb : 0 < (q b).1) : dist (p a) (p b) = rad a + rad b :=
          CircularSideProof.centerDistance q hq a b hab ha hb
  have hchild_parent : dist (p 0) (p i.succ) = rad 0 + rad i.succ :=
      CircularSideProof.hchild_parent q i hchild hparent centerDistance
  have hside_nonneg : 0 ≤ (q j.succ).1 ∧ 0 ≤ (q k.succ).1 :=
    ⟨other_nonneg j, other_nonneg k⟩
  let dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im
  have capBound (x y e : ℂ) (t : ℝ)
      (hx : Complex.normSq x = 1) (hy : Complex.normSq y = 1)
      (he : Complex.normSq e = 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
      (hxd : t ≤ dot x e) (hyd : t ≤ dot y e) :
      ‖x - y‖ ≤ 2 * Real.sqrt (1 - t ^ 2) := CircularSideProof.capBound x y e t hx hy he ht0 ht1
          hxd hyd
  let A : ℂ := p i.succ
  let X : ℂ := p 0
  let e : ℂ := (X - A) / ((rad i.succ + rad 0 : ℝ) : ℂ)
  have hcenterNorm : ‖X - A‖ = rad i.succ + rad 0 := CircularSideProof.hcenterNorm q i hchild_parent
  have heNorm : ‖e‖ = 1 := CircularSideProof.heNorm q i hden hcenterNorm
  have heSq : Complex.normSq e = 1 := CircularSideProof.heSq q i heNorm
  have hparne : (q i.succ).1 ≠ 0 := ne_of_gt hparent
  let v₁ : ℂ := P5023T1ContactVertices L q (i + 1)
  let v₂ : ℂ := P5023T1ContactVertices L q (i + 2)
  have hv₁ : v₁ = if (q k.succ).1 = 0 then
      ⟨if (q k.succ).2 = -1 then L else L + 2, (p i.succ).im⟩ else
      ((q i.succ).2 + (q k.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q k.succ).1 : ℝ)) := CircularSideProof.hv₁ L q i hparne
  have hv₂ : v₂ = if (q j.succ).1 = 0 then
      ⟨if (q j.succ).2 = -1 then L else L + 2, (p i.succ).im⟩ else
      ((q i.succ).2 + (q j.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q j.succ).1 : ℝ)) := CircularSideProof.hv₂ L q i hparne
  let V (a : Fin 3) : ℂ :=
    if (q a.succ).1 = 0 then
      ⟨if (q a.succ).2 = -1 then L else L + 2, A.im⟩
    else
      ((q i.succ).2 + (q a.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q a.succ).1 : ℝ))
  have hv₁V : v₁ = V k := by
    simp [hv₁, V, A, p]
  have hv₂V : v₂ = V j := by
    simp [hv₂, V, A, p]
  let t : ℝ := (rad i.succ - rad 0) / (rad i.succ + rad 0)
  have ht0 : 0 ≤ t := CircularSideProof.ht0 q i hRr hden
  have ht1 : t ≤ 1 := CircularSideProof.ht1 q i hR hden
  have normSqSubDot (x y : ℂ) :
      Complex.normSq (x - y) = Complex.normSq x + Complex.normSq y - 2 * dot x y :=
          CircularSideProof.normSqSubDot x y
  have dotDiv (x y : ℂ) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
      dot (x / (c : ℂ)) (y / (d : ℂ)) = dot x y / (c * d) := CircularSideProof.dotDiv x y c d hc hd
  have contactFacts (a : Fin 3) (hne : a ≠ i)
      (ha : 0 < (q a.succ).1 ∨ (q a.succ).1 = 0) :
      Complex.normSq ((V a - A) / (rad i.succ : ℂ)) = 1 ∧
        t ≤ dot ((V a - A) / (rad i.succ : ℂ)) e := by
    as_aux_lemma =>
      clear * - L q hq hs hR i p rad centerDistance normSqSubDot dotDiv hne ha
        V A X e t dot hparent hchild hr hden hparne hchild_parent
      rcases ha with hapos | hazero
      · have haposZ : 0 < (q a.succ).1 := hapos
        have hne4 : a.succ ≠ i.succ := CircularSideProof.hne4 i a hne
        have hcenter : dist (p a.succ) (p i.succ) = rad a.succ + rad i.succ := by
          exact centerDistance a.succ i.succ hne4 haposZ hparent
        have hchild : dist (p a.succ) (p 0) = rad a.succ + rad 0 := by
          exact centerDistance a.succ 0 (by simp) haposZ hchild
        have hrel : V a - A =
            ((q a.succ).1 : ℂ) /
              ((((q i.succ).1 + (q a.succ).1 : ℤ) : ℂ)) *
                (p a.succ - A) := CircularSideProof.hrel L q i a hparent hparne hapos haposZ
        have hsumRad : rad i.succ + rad a.succ =
            (((q i.succ).1 + (q a.succ).1 : ℤ) : ℝ) /
              (((q i.succ).1 * (q a.succ).1 : ℤ) : ℝ) := CircularSideProof.hsumRad q i a hparent
                  hapos
        have hunitEq : (V a - A) / (rad i.succ : ℂ) =
            (p a.succ - A) / ((rad i.succ + rad a.succ : ℝ) : ℂ) := CircularSideProof.hunitEq L q
                i a hparent hapos hrel hsumRad
        have hdistParent : ‖p a.succ - A‖ = rad i.succ + rad a.succ :=
            CircularSideProof.hdistParent q i a hcenter
        have hunitNorm : ‖(V a - A) / (rad i.succ : ℂ)‖ = 1 := CircularSideProof.hunitNorm L q i
            a hparent hapos hunitEq hdistParent
        have hunitSq : Complex.normSq ((V a - A) / (rad i.succ : ℂ)) = 1 :=
            CircularSideProof.hunitSqAt360 L q i a hunitNorm
        have hA : Complex.normSq (p a.succ - A) = (rad i.succ + rad a.succ) ^ 2 := by
          rw [Complex.normSq_eq_norm_sq, hdistParent]
        have hX : Complex.normSq (X - A) = (rad i.succ + rad 0) ^ 2 := CircularSideProof.hX q i
            hchild_parent
        have hBX : Complex.normSq (p a.succ - X) = (rad a.succ + rad 0) ^ 2 :=
            CircularSideProof.hBX q a hchild
        have hdot : dot (p a.succ - A) (X - A) =
            ((rad i.succ + rad a.succ) ^ 2 + (rad i.succ + rad 0) ^ 2 -
              (rad a.succ + rad 0) ^ 2) / 2 := CircularSideProof.hdotAt373 q i a normSqSubDot hA
                  hX hBX
        have hdotUnit : dot ((V a - A) / (rad i.succ : ℂ)) e =
            dot (p a.succ - A) (X - A) /
              ((rad i.succ + rad a.succ) * (rad i.succ + rad 0)) := CircularSideProof.hdotUnit L
                  q i a hparent hden dotDiv hapos hunitEq
        constructor
        · exact hunitSq
        · rw [hdotUnit, hdot]
          dsimp [t]
          have hposden : 0 < (rad i.succ + rad a.succ) * (rad i.succ + rad 0) := by positivity
          have hextra : 0 < (2 * rad i.succ * rad 0) /
              ((rad i.succ + rad a.succ) * (rad i.succ + rad 0)) := CircularSideProof.hextra q i
                  a hparent hR hposden
          have hid : (((rad i.succ + rad a.succ) ^ 2 + (rad i.succ + rad 0) ^ 2 -
              (rad a.succ + rad 0) ^ 2) / 2) /
              ((rad i.succ + rad a.succ) * (rad i.succ + rad 0)) =
              t + 2 * rad i.succ * rad 0 /
                ((rad i.succ + rad a.succ) * (rad i.succ + rad 0)) := CircularSideProof.hid q i a
                    hparent hden hapos
          rw [hid]
          linarith [hextra]
      · let H : ℝ := if (q a.succ).2 = -1 then L else L + 2
        let σ : ℝ := if (q a.succ).2 = -1 then 1 else -1
        have hnormal := hs.normals a.succ hazero
        have signedDistance (b : Fin 4) (hb : 0 < (q b).1) :
            σ * ((p b).re - H) = rad b := CircularSideProof.signedDistance L q hs a hazero
                hnormal b hb
        have hAline := signedDistance i.succ hparent
        have hXline := signedDistance 0 hchild
        have hσsq : σ * σ = 1 := CircularSideProof.hσsq q a
        have hVline : V a = ⟨H, A.im⟩ := by
          simp [V, H, hazero]
        have hcontact : (V a - A) / (rad i.succ : ℂ) = (-σ : ℂ) := CircularSideProof.hcontact L q
            i a hr hnormal hAline hVline
        have hunitSq : Complex.normSq ((V a - A) / (rad i.succ : ℂ)) = 1 :=
            CircularSideProof.hunitSqAt473 L q i a hσsq hcontact
        have hdiffSigned : σ * ((X.re) - A.re) = rad 0 - rad i.succ :=
            CircularSideProof.hdiffSigned L q i a hAline hXline
        have hdotSigned : (-σ) * (X.re - A.re) = rad i.succ - rad 0 :=
            CircularSideProof.hdotSigned q i a hdiffSigned
        have hdot : dot ((V a - A) / (rad i.succ : ℂ)) e = t := CircularSideProof.hdotAt485 L q i
            a hcontact hdotSigned
        exact ⟨hunitSq, le_of_eq hdot.symm⟩
  have hjfacts := contactFacts j hji hjpos
  have hkfacts := contactFacts k hki hkpos
  have hn₁ : Complex.normSq ((v₁ - A) / (rad i.succ : ℂ)) = 1 := CircularSideProof.hn₁ L q i hv₁V
      hkfacts
  have hn₂ : Complex.normSq ((v₂ - A) / (rad i.succ : ℂ)) = 1 := CircularSideProof.hn₂ L q i hv₂V
      hjfacts
  have hdot₁ : t ≤ dot ((v₁ - A) / (rad i.succ : ℂ)) e := CircularSideProof.hdot₁ L q i hv₁V hkfacts
  have hdot₂ : t ≤ dot ((v₂ - A) / (rad i.succ : ℂ)) e := CircularSideProof.hdot₂ L q i hv₂V hjfacts
  have hchord : ‖(v₁ - A) / (rad i.succ : ℂ) - (v₂ - A) / (rad i.succ : ℂ)‖ ≤
      2 * Real.sqrt (1 - t ^ 2) := CircularSideProof.hchord L q i capBound heSq ht0 ht1 hn₁ hn₂
          hdot₁ hdot₂
  have cancelRadius (x : ℝ) : x / rad i.succ * rad i.succ = x :=
    div_mul_cancel₀ x (ne_of_gt hr)
  have rearrange (x y : ℝ) : x * (2 * y) = 2 * x * y := by ring
  have hscale : dist (P5023T1ContactVertices L q (i + 1))
      (P5023T1ContactVertices L q (i + 2)) = rad i.succ *
      ‖(v₁ - A) / (rad i.succ : ℂ) - (v₂ - A) / (rad i.succ : ℂ)‖ := CircularSideProof.hscale L q
          i hr cancelRadius
  rw [hscale]
  calc
    rad i.succ * ‖(v₁ - A) / (rad i.succ : ℂ) - (v₂ - A) / (rad i.succ : ℂ)‖ ≤
        rad i.succ * (2 * Real.sqrt (1 - t ^ 2)) :=
      mul_le_mul_of_nonneg_left hchord hr.le
    _ = 2 * rad i.succ * Real.sqrt (1 - t ^ 2) :=
      rearrange _ _
    ))

end ApollonianSuperharmonic

end
