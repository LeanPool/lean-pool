/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateNormLaw
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinatePolarizationLaw


-- [TABLET NODE: TangencyCoordinateSuccessorPolarization]

/-!
# TangencyCoordinateSuccessorPolarization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SuccessorPolarization

private noncomputable def c (q : Fin 4 → CircleCoordinates) : Fin 4 → ℤ := fun r => (q r).1

private noncomputable def w (q : Fin 4 → CircleCoordinates) : Fin 4 → GaussianInt := fun r => (q
    r).2

private noncomputable def delta (q : Fin 4 → CircleCoordinates) : Fin 4 → Fin 4 → GaussianInt :=
    fun r s => (c q) s • (w q) r - (c q) r • (w q) s

private noncomputable def dot : GaussianInt → GaussianInt → ℤ := fun x y => x.re * y.re + x.im *
    y.im

private noncomputable def P (q : Fin 4 → CircleCoordinates) : Fin 4 → Fin 4 → Fin 4 → ℤ := fun a
    b j => (c q) a * (c q) b + (c q) j * ((c q) a + (c q) b) - (c q) j ^ 2

private theorem hn' (q : Fin 4 → CircleCoordinates) (hn : TangencyCoordinateNormLaw q) : ∀ i j :
    Fin 4, i ≠ j →
      dot ((delta q) i j) ((delta q) i j) = ((c q) i + (c q) j) ^ 2 := by
  classical
  let c : Fin 4 → ℤ := fun r => (q r).1
  let w : Fin 4 → GaussianInt := fun r => (q r).2
  let delta : Fin 4 → Fin 4 → GaussianInt :=
    fun r s => c s • w r - c r • w s
  let dot : GaussianInt → GaussianInt → ℤ :=
    fun x y => x.re * y.re + x.im * y.im
  change (∀ i j : Fin 4, i ≠ j →
      dot (delta i j) (delta i j) = (c i + c j) ^ 2)
  intro i j hij
  have h := hn i j hij
  convert h using 1; simp [dot, delta, c, w, Zsqrtd.norm]; ring

private theorem hp' (q : Fin 4 → CircleCoordinates) (hp : TangencyCoordinatePolarizationLaw q) :
    ∀ a b j : Fin 4, a ≠ b → a ≠ j → b ≠ j →
      dot ((delta q) a j) ((delta q) b j) = (P q) a b j := by
  classical
  let c : Fin 4 → ℤ := fun r => (q r).1
  let w : Fin 4 → GaussianInt := fun r => (q r).2
  let delta : Fin 4 → Fin 4 → GaussianInt :=
    fun r s => c s • w r - c r • w s
  let dot : GaussianInt → GaussianInt → ℤ :=
    fun x y => x.re * y.re + x.im * y.im
  let P : Fin 4 → Fin 4 → Fin 4 → ℤ :=
    fun a b j => c a * c b + c j * (c a + c b) - c j ^ 2
  change (∀ a b j : Fin 4, a ≠ b → a ≠ j → b ≠ j →
      dot (delta a j) (delta b j) = P a b j)
  intro a b j hab haj hbj
  have h := hp a b j hab haj hbj
  simpa [dot, delta, P, c, w] using h

private theorem noncommon (q : Fin 4 → CircleCoordinates) (hn : TangencyCoordinateNormLaw q) (hp
    : TangencyCoordinatePolarizationLaw q) : ∀ j k l : Fin 4, j ≠ k → j ≠ l → k ≠ l →
      j ≠ 1 → k ≠ 1 → l ≠ 1 →
      let d := 2 * ((c q) j + (c q) k + (c q) l) - (c q) 1
      let wd := 2 * (w q) j + 2 * (w q) k + 2 * (w q) l - (w q) 1
      dot ((c q) j • wd - d • (w q) j) ((delta q) k j) =
        d * (c q) k + (c q) j * (d + (c q) k) - (c q) j ^ 2 := by
  classical
  let c : Fin 4 → ℤ := fun r => (q r).1
  let w : Fin 4 → GaussianInt := fun r => (q r).2
  let delta : Fin 4 → Fin 4 → GaussianInt :=
    fun r s => c s • w r - c r • w s
  let dot : GaussianInt → GaussianInt → ℤ :=
    fun x y => x.re * y.re + x.im * y.im
  let P : Fin 4 → Fin 4 → Fin 4 → ℤ :=
    fun a b j => c a * c b + c j * (c a + c b) - c j ^ 2
  have hn' : ∀ i j : Fin 4, i ≠ j →
      dot (delta i j) (delta i j) = (c i + c j) ^ 2 := hn' q hn
  have hp' : ∀ a b j : Fin 4, a ≠ b → a ≠ j → b ≠ j →
      dot (delta a j) (delta b j) = P a b j := hp' q hp
  change (∀ j k l : Fin 4, j ≠ k → j ≠ l → k ≠ l →
      j ≠ 1 → k ≠ 1 → l ≠ 1 →
      let d := 2 * (c j + c k + c l) - c 1
      let wd := 2 * w j + 2 * w k + 2 * w l - w 1
      dot (c j • wd - d • w j) (delta k j) =
        d * c k + c j * (d + c k) - c j ^ 2)
  intro j k l hjk hjl hkl hj1 hk1 hl1
  dsimp only
  calc
    dot (c j • (2 * w j + 2 * w k + 2 * w l - w 1) -
        (2 * (c j + c k + c l) - c 1) • w j) (delta k j) =
        2 * dot (delta k j) (delta k j) +
          2 * dot (delta l j) (delta k j) - dot (delta 1 j) (delta k j) := by
            simp [delta, dot]
            ring
    _ = (2 * (c j + c k + c l) - c 1) * c k +
        c j * (2 * (c j + c k + c l) - c 1 + c k) - c j ^ 2 := by
          rw [hn' k j (Ne.symm hjk),
            hp' l k j (Ne.symm hkl) (Ne.symm hjl) (Ne.symm hjk),
            hp' 1 k j (Ne.symm hk1) (Ne.symm hj1) (Ne.symm hjk)]
          simp [P]
          ring

private theorem common (q : Fin 4 → CircleCoordinates) (hn : TangencyCoordinateNormLaw q) (hp :
    TangencyCoordinatePolarizationLaw q) : ∀ i k l : Fin 4, i ≠ k → i ≠ l → k ≠ l →
      i ≠ 1 → k ≠ 1 → l ≠ 1 →
      let d := 2 * ((c q) i + (c q) k + (c q) l) - (c q) 1
      let wd := 2 * (w q) i + 2 * (w q) k + 2 * (w q) l - (w q) 1
      dot (d • (w q) i - (c q) i • wd) (d • (w q) k - (c q) k • wd) =
        (c q) i * (c q) k + d * ((c q) i + (c q) k) - d ^ 2 := by
  classical
  let c : Fin 4 → ℤ := fun r => (q r).1
  let w : Fin 4 → GaussianInt := fun r => (q r).2
  let delta : Fin 4 → Fin 4 → GaussianInt :=
    fun r s => c s • w r - c r • w s
  let dot : GaussianInt → GaussianInt → ℤ :=
    fun x y => x.re * y.re + x.im * y.im
  let P : Fin 4 → Fin 4 → Fin 4 → ℤ :=
    fun a b j => c a * c b + c j * (c a + c b) - c j ^ 2
  have hn' : ∀ i j : Fin 4, i ≠ j →
      dot (delta i j) (delta i j) = (c i + c j) ^ 2 := hn' q hn
  have hp' : ∀ a b j : Fin 4, a ≠ b → a ≠ j → b ≠ j →
      dot (delta a j) (delta b j) = P a b j := hp' q hp
  change (∀ i k l : Fin 4, i ≠ k → i ≠ l → k ≠ l →
      i ≠ 1 → k ≠ 1 → l ≠ 1 →
      let d := 2 * (c i + c k + c l) - c 1
      let wd := 2 * w i + 2 * w k + 2 * w l - w 1
      dot (d • w i - c i • wd) (d • w k - c k • wd) =
        c i * c k + d * (c i + c k) - d ^ 2)
  intro i k l hik hil hkl hi1 hk1 hl1
  dsimp only
  let d := 2 * (c i + c k + c l) - c 1
  let wd := 2 * w i + 2 * w k + 2 * w l - w 1
  let A := delta i k
  let B := delta i l
  let C := delta i 1
  let E := delta k l
  let F := delta k 1
  let G := delta l 1
  let X0 := -2 * c i * c k + c i * c l + c i * c 1 +
    c k * c l + c k * c 1 - 2 * c l * c 1
  have hBC : dot B C = P l 1 i := by
    convert hp' l 1 i hl1 (Ne.symm hil) (Ne.symm hi1) using 1;
      simp [B, C, delta, dot]; ring
  have hAB : dot A B = P k l i := by
    convert hp' k l i hkl (Ne.symm hik) (Ne.symm hil) using 1;
      simp [A, B, delta, dot]; ring
  have hAC : dot A C = P k 1 i := by
    convert hp' k 1 i hk1 (Ne.symm hik) (Ne.symm hi1) using 1;
      simp [A, C, delta, dot]; ring
  have hEF : dot E F = P l 1 k := by
    convert hp' l 1 k hl1 (Ne.symm hkl) (Ne.symm hk1) using 1;
      simp [E, F, delta, dot]; ring
  have hAF : dot A F = -P i 1 k := by
    have h := hp' i 1 k hi1 hik (Ne.symm hk1)
    convert congrArg Neg.neg h using 1; simp [A, F, delta, dot]; ring
  have hAE : dot A E = -P i l k := by
    have h := hp' i l k hil hik (Ne.symm hkl)
    convert congrArg Neg.neg h using 1; simp [A, E, delta, dot]; ring
  have hGE : dot G E = -P k 1 l := by
    have h := hp' k 1 l hk1 hkl (Ne.symm hl1)
    convert congrArg Neg.neg h using 1; simp [G, E, delta, dot]; ring
  have hCF : dot C F = P i k 1 := by
    simpa [C, F] using hp' i k 1 hik hi1 hk1
  have hBF : dot B F + dot C E = X0 := by
    by_cases hi : c i = 0
    · by_cases hk : c k = 0
      · by_cases hl : c l = 0
        · by_cases h1 : c 1 = 0
          · simp [X0, B, C, E, F, delta, dot, hi, hk, hl, h1]
          · have halg : c 1 * (dot B F + dot C E) =
                2 * c l * dot C F - c i * dot G F - c k * dot C G := by
              simp [B, C, E, F, G, delta, dot]
              ring
            have hs : c 1 * (dot B F + dot C E) = c 1 * X0 := by
              rw [halg, hCF]
              simp [X0, P, hi, hk, hl]
            exact (mul_left_cancel₀ h1) hs
        · have halg : c l * (dot B F + dot C E) =
              2 * c 1 * dot B E + c k * dot B G + c i * dot G E := by
            simp [B, C, E, F, G, delta, dot]
            ring
          have hBE : dot B E = P i k l := by
            simpa [B, E] using hp' i k l hik hil hkl
          have hBG : dot B G = -P i 1 l := by
            have h := hp' i 1 l hi1 hil (Ne.symm hl1)
            convert congrArg Neg.neg h using 1;
              simp [B, G, delta, dot]; ring
          have hs : c l * (dot B F + dot C E) = c l * X0 := by
            rw [halg, hBE, hBG, hGE]
            simp [X0, P, hi, hk]
            ring
          exact (mul_left_cancel₀ hl) hs
      · have halg : c k * (dot B F + dot C E) =
            2 * c i * dot E F + c l * dot A F + c 1 * dot A E := by
          simp [A, B, C, E, F, delta, dot]
          ring
        have hs : c k * (dot B F + dot C E) = c k * X0 := by
          rw [halg, hEF, hAF, hAE]
          simp [X0, P, hi]
          ring
        exact (mul_left_cancel₀ hk) hs
    · have halg : c i * (dot B F + dot C E) =
          2 * c k * dot B C - c 1 * dot A B - c l * dot A C := by
        simp [A, B, C, E, F, delta, dot]
        ring
      have hs : c i * (dot B F + dot C E) = c i * X0 := by
        rw [halg, hBC, hAB, hAC]
        simp [X0, P]
        ring
      exact (mul_left_cancel₀ hi) hs
  have hAA := hn' i k hik
  have hBE : dot B E = P i k l := by
    simpa [B, E] using hp' i k l hik hil hkl
  have hCF' : dot C F = P i k 1 := by
    simpa [C, F] using hp' i k 1 hik hi1 hk1
  change dot (d • w i - c i • wd) (d • w k - c k • wd) =
    c i * c k + d * (c i + c k) - d ^ 2
  calc
    dot (d • w i - c i • wd) (d • w k - c k • wd) =
        -4 * dot A A - 4 * dot A B + 2 * dot A C + 4 * dot A E -
          2 * dot A F + 4 * dot B E - 2 * (dot B F + dot C E) +
          dot C F := by
            simp [d, wd, A, B, C, E, F, delta, dot]
            ring
    _ = c i * c k + d * (c i + c k) - d ^ 2 := by
      rw [hAA, hAB, hAC, hAE, hAF, hBE, hBF, hCF']
      simp [P, X0, d]
      ring

end SuccessorPolarization

private def successorQuadruple (q : Fin 4 → CircleCoordinates) : Fin 4 → CircleCoordinates :=
  ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
          2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
        q 0, q 2, q 3]

private def pairPolarization (q : Fin 4 → CircleCoordinates) (a b j : Fin 4) : Prop :=
  let u := (q j).1 • (q a).2 - (q a).1 • (q j).2
  let v := (q j).1 • (q b).2 - (q b).1 • (q j).2
  u.re * v.re + u.im * v.im =
    (q a).1 * (q b).1 + (q j).1 * ((q a).1 + (q b).1) - (q j).1 ^ 2

private theorem polarizationCase012 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 0 1 2 := by
  convert SuccessorPolarization.noncommon q hn hp 2 0 3 (by decide) (by decide) (by decide) (by
      decide)
    (by decide) (by decide) using 1; simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, SuccessorPolarization.delta, pairPolarization,
      successorQuadruple]; ring

private theorem polarizationCase013 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 0 1 3 := by
  convert SuccessorPolarization.noncommon q hn hp 3 0 2 (by decide) (by decide) (by decide) (by
      decide)
    (by decide) (by decide) using 1; simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, SuccessorPolarization.delta, pairPolarization,
      successorQuadruple]; ring

private theorem polarizationCase021 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 0 2 1 := by
  convert SuccessorPolarization.noncommon q hn hp 0 2 3 (by decide) (by decide) (by decide) (by
      decide)
    (by decide) (by decide) using 1; simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, SuccessorPolarization.delta, pairPolarization,
      successorQuadruple]; ring

private theorem polarizationCase023 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 0 2 3 := by
  convert SuccessorPolarization.noncommon q hn hp 3 2 0 (by decide) (by decide) (by decide) (by
      decide)
    (by decide) (by decide) using 1; simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, SuccessorPolarization.delta, pairPolarization,
      successorQuadruple]; ring

private theorem polarizationCase031 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 0 3 1 := by
  convert SuccessorPolarization.noncommon q hn hp 0 3 2 (by decide) (by decide) (by decide) (by
      decide)
    (by decide) (by decide) using 1; simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, SuccessorPolarization.delta, pairPolarization,
      successorQuadruple]; ring

private theorem polarizationCase032 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 0 3 2 := by
  convert SuccessorPolarization.noncommon q hn hp 2 3 0 (by decide) (by decide) (by decide) (by
      decide)
    (by decide) (by decide) using 1; simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, SuccessorPolarization.delta, pairPolarization,
      successorQuadruple]; ring

private theorem polarizationCase102 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 1 0 2 := by
  convert SuccessorPolarization.noncommon q hn hp 2 0 3 (by decide) (by decide) (by decide) (by
      decide)
    (by decide) (by decide) using 1; simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, SuccessorPolarization.delta, pairPolarization,
      successorQuadruple]; ring

private theorem polarizationCase103 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 1 0 3 := by
  convert SuccessorPolarization.noncommon q hn hp 3 0 2 (by decide) (by decide) (by decide) (by
      decide)
    (by decide) (by decide) using 1; simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, SuccessorPolarization.delta, pairPolarization,
      successorQuadruple]; ring

private theorem polarizationCase120 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 1 2 0 := by
  convert SuccessorPolarization.common q hn hp 0 2 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) using 1; (try simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, pairPolarization, successorQuadruple]); ring

private theorem polarizationCase123 (q : Fin 4 → CircleCoordinates)
    (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 1 2 3 := by
  exact hp 0 2 3 (by decide) (by decide) (by decide)

private theorem polarizationCase130 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 1 3 0 := by
  convert SuccessorPolarization.common q hn hp 0 3 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) using 1; (try simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, pairPolarization, successorQuadruple]); ring

private theorem polarizationCase132 (q : Fin 4 → CircleCoordinates)
    (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 1 3 2 := by
  exact hp 0 3 2 (by decide) (by decide) (by decide)

private theorem polarizationCase201 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 2 0 1 := by
  convert SuccessorPolarization.noncommon q hn hp 0 2 3 (by decide) (by decide) (by decide) (by
      decide)
    (by decide) (by decide) using 1; simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, SuccessorPolarization.delta, pairPolarization,
      successorQuadruple]; ring

private theorem polarizationCase203 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 2 0 3 := by
  convert SuccessorPolarization.noncommon q hn hp 3 2 0 (by decide) (by decide) (by decide) (by
      decide)
    (by decide) (by decide) using 1; simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, SuccessorPolarization.delta, pairPolarization,
      successorQuadruple]; ring

private theorem polarizationCase210 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 2 1 0 := by
  convert SuccessorPolarization.common q hn hp 2 0 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) using 1; (try simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, pairPolarization, successorQuadruple]); ring

private theorem polarizationCase213 (q : Fin 4 → CircleCoordinates)
    (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 2 1 3 := by
  exact hp 2 0 3 (by decide) (by decide) (by decide)

private theorem polarizationCase230 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 2 3 0 := by
  convert SuccessorPolarization.common q hn hp 2 3 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) using 1; (try simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, pairPolarization, successorQuadruple]); ring

private theorem polarizationCase231 (q : Fin 4 → CircleCoordinates)
    (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 2 3 1 := by
  exact hp 2 3 0 (by decide) (by decide) (by decide)

private theorem polarizationCase301 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 3 0 1 := by
  convert SuccessorPolarization.noncommon q hn hp 0 3 2 (by decide) (by decide) (by decide) (by
      decide)
    (by decide) (by decide) using 1; simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, SuccessorPolarization.delta, pairPolarization,
      successorQuadruple]; ring

private theorem polarizationCase302 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 3 0 2 := by
  convert SuccessorPolarization.noncommon q hn hp 2 3 0 (by decide) (by decide) (by decide) (by
      decide)
    (by decide) (by decide) using 1; simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, SuccessorPolarization.delta, pairPolarization,
      successorQuadruple]; ring

private theorem polarizationCase310 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 3 1 0 := by
  convert SuccessorPolarization.common q hn hp 3 0 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) using 1; (try simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, pairPolarization, successorQuadruple]); ring

private theorem polarizationCase312 (q : Fin 4 → CircleCoordinates)
    (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 3 1 2 := by
  exact hp 3 0 2 (by decide) (by decide) (by decide)

private theorem polarizationCase320 (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q) (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 3 2 0 := by
  convert SuccessorPolarization.common q hn hp 3 2 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) using 1; (try simp [SuccessorPolarization.c, SuccessorPolarization.w,
    SuccessorPolarization.dot, pairPolarization, successorQuadruple]); ring

private theorem polarizationCase321 (q : Fin 4 → CircleCoordinates)
    (hp : TangencyCoordinatePolarizationLaw q) :
    pairPolarization (successorQuadruple q) 3 2 1 := by
  exact hp 3 2 0 (by decide) (by decide) (by decide)

theorem TangencyCoordinateSuccessorPolarization
    (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q)
    (hp : TangencyCoordinatePolarizationLaw q) :
    TangencyCoordinatePolarizationLaw
      ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
          2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
        q 0, q 2, q 3] := by
  intro a b j hab haj hbj
  fin_cases a <;> fin_cases b <;> fin_cases j
  all_goals try exact (hab rfl).elim
  all_goals try exact (haj rfl).elim
  all_goals try exact (hbj rfl).elim
  case «0».«1».«2» => exact polarizationCase012 q hn hp
  case «0».«1».«3» => exact polarizationCase013 q hn hp
  case «0».«2».«1» => exact polarizationCase021 q hn hp
  case «0».«2».«3» => exact polarizationCase023 q hn hp
  case «0».«3».«1» => exact polarizationCase031 q hn hp
  case «0».«3».«2» => exact polarizationCase032 q hn hp
  case «1».«0».«2» => exact polarizationCase102 q hn hp
  case «1».«0».«3» => exact polarizationCase103 q hn hp
  case «1».«2».«0» => exact polarizationCase120 q hn hp
  case «1».«2».«3» => exact polarizationCase123 q hp
  case «1».«3».«0» => exact polarizationCase130 q hn hp
  case «1».«3».«2» => exact polarizationCase132 q hp
  case «2».«0».«1» => exact polarizationCase201 q hn hp
  case «2».«0».«3» => exact polarizationCase203 q hn hp
  case «2».«1».«0» => exact polarizationCase210 q hn hp
  case «2».«1».«3» => exact polarizationCase213 q hp
  case «2».«3».«0» => exact polarizationCase230 q hn hp
  case «2».«3».«1» => exact polarizationCase231 q hp
  case «3».«0».«1» => exact polarizationCase301 q hn hp
  case «3».«0».«2» => exact polarizationCase302 q hn hp
  case «3».«1».«0» => exact polarizationCase310 q hn hp
  case «3».«1».«2» => exact polarizationCase312 q hp
  case «3».«2».«0» => exact polarizationCase320 q hn hp
  case «3».«2».«1» => exact polarizationCase321 q hp

end ApollonianSuperharmonic

end
