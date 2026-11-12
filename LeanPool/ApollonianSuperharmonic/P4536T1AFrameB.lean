/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4458T1RestrictionFamily
public import LeanPool.ApollonianSuperharmonic.P4536T1EndpointAlgebra
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P4536T1AFrameB]

/-!
# P4536T1AFrameB

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace AFrameBProof

private theorem hr :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    ProperBandQuadruple r := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r
  have rot : ∀ j : Fin 3, ProperBandQuadruple
      ![F.q 0, F.q j.succ, F.q (j + 1).succ, F.q (j + 2).succ] := by
    intro j
    fin_cases j
    · convert F.proper using 1; funext k; fin_cases k <;> rfl
    · refine ⟨SemiProperQuadruple.rotate F.proper.1, ?_⟩
      intro k
      fin_cases k
      · exact F.proper.2 1
      · exact F.proper.2 2
      · exact F.proper.2 0
    · refine ⟨SemiProperQuadruple.rotate (SemiProperQuadruple.rotate F.proper.1), ?_⟩
      intro k
      fin_cases k
      · exact F.proper.2 2
      · exact F.proper.2 0
      · exact F.proper.2 1
  exact rot a

private theorem hcentJ :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates), (![F.q
        (0 : Fin (4 : ℕ)), F.q a.succ, F.q (a + (1 : Fin (3 : ℕ))).succ, F.q (a + (2 : Fin (3 :
        ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 +
        (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 :
        Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3
        : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p
        (3 : Fin (4 : ℕ))]) → ((F.slot = a + (1 : Fin (3 : ℕ))) → (∀ (J : ProtoTile),
            (TileCentroid J = TileCentroid (D.tiles F.slot false)) → (
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (ProperBandQuadruple r) → ((r 0 = (2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p
        0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2)) → ((r 1 = p 0) → ((r 2 = p 2) → ((r 3 = p 3)
        → ((r 2 = C.1.1) → (
    let I : GaussianInt := ⟨0, 1⟩
    let w := BandVectors.1 (r 3) (r 2)
    let x := BandVectors.1 (r 1) (r 3)
    let y := BandVectors.1 (r 2) (r 1)
    let wa := BandVectors.2 (r 3) (r 2)
    let xa := BandVectors.2 (r 1) (r 3)
    let ya := BandVectors.2 (r 2) (r 1)
    (BandVectors.1 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) + BandVectors.1 (r (1 : Fin (4 :
        ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) =
        (0 : GaussianInt) ∧ BandVectors.2 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
        BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.2 (r (2 : Fin (4
        : ℕ))) (r (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (r (1 : Fin (4 : ℕ))) (r
        (0 : Fin (4 : ℕ))) = BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) - ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) ∧ BandVectors.2
        (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) = BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 :
        Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 :
        ℕ))) ∧ (ProperBandQuadruple r → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (r (0 : Fin (4 : ℕ)))
        (r j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) ∧
        BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r
        j.succ) (r (0 : Fin (4 : ℕ))))) → ((SemiProperQuadruple ![r 0, r 2, r 3, r 1]) →
        ((BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) + BandVectors.1 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)),
        r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧
        BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) + BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)),
        r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧
        BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) = BandVectors.1 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 :
        ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) ∧
        BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) = BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 :
        ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) ∧
        (ProperBandQuadruple ![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r
        (1 : Fin (4 : ℕ))] → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 :
        Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) (![r (0 : Fin
        (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) = ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] j.succ) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) =
        -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 :
        Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r
        (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))))) → ((BandVectors.1 (r 2) (r
        0) = y - I * w) → ((BandVectors.2 (r 2) (r 0) = ya + I * wa) → ((BandVectors.1 (r 0) (r
        2) = I * (y - I * w)) → ((BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa)) →
        ((BandVectors.1 (p 0) (p 2) = I * y) → ((BandVectors.2 (p 0) (p 2) = -I * ya) → ((-(w - I
        * w) - (x - I * y - I * (x - I * y)) = (2 : GaussianInt) * y ∧ x - I * y + I * (x - I *
        y) + (w - I * w) = (2 : GaussianInt) * I * x ∧ -(x - I * x) - (w - I * w) = y - I * y ∧ y
        - I * w + I * (y - I * w) - (w - I * w) = y + I * y ∧ w - I * x - I * (w - I * x) - (w -
        I * w) = -I * x - x ∧ -(y - I * y) - (w - I * w) = -I * x + x ∧ y - I * w - I * (y - I *
        w) - (y - I * y) = -I * w - w ∧ -(x - I * x) - (y - I * y) = -I * w + w ∧ -(y - I * y) -
        (x - I * x) = w - I * w ∧ w - I * x + I * (w - I * x) - (x - I * x) = w + I * w) → ((-(wa
        - -I * wa) - (xa - -I * ya - -I * (xa - -I * ya)) = (2 : GaussianInt) * ya ∧ xa - -I * ya
        + -I * (xa - -I * ya) + (wa - -I * wa) = (2 : GaussianInt) * -I * xa ∧ -(xa - -I * xa) -
        (wa - -I * wa) = ya - -I * ya ∧ ya - -I * wa + -I * (ya - -I * wa) - (wa - -I * wa) = ya
        + -I * ya ∧ wa - -I * xa - -I * (wa - -I * xa) - (wa - -I * wa) = - -I * xa - xa ∧ -(ya -
        -I * ya) - (wa - -I * wa) = - -I * xa + xa ∧ ya - -I * wa - -I * (ya - -I * wa) - (ya -
        -I * ya) = - -I * wa - wa ∧ -(xa - -I * xa) - (ya - -I * ya) = - -I * wa + wa ∧ -(ya - -I
        * ya) - (xa - -I * xa) = wa - -I * wa ∧ wa - -I * xa + -I * (wa - -I * xa) - (xa - -I *
        xa) = wa + -I * wa) → ((-(xa - -I * xa) - (wa - -I * wa) = ya - -I * ya) → ((ya - -I * wa
        + -I * (ya - -I * wa) - (wa - -I * wa) = ya + -I * ya) → ((BandVectors.1 (r 0) (r 2) = I
        * (y - I * w)) → ((BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa)) → (TileCentroid J -
        TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (-(x - I *
        x)))))))))))))))))))))))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hstep hslot J hcent r hr hcoord hA
      hB hE hparent I w x y wa xa ya laws hrot rlaws hv ha hflipv hflipa hvp hap vAlg aAlg aThird
      aFourth vflip aflip
  have h := (D.occurrences F.slot false).2.2
  rw [hslot] at h
  rw [hslot] at hcent
  rw [← hcent] at h
  fin_cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, one_div, Fin.mk_one, Fin.isValue,
      Fin.reduceAdd, Fin.succ_one_eq_two, Fin.succ_zero_eq_one, neg_smul, one_smul,
      Fin.reduceSucc, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val,
      Int.reduceNeg, neg_sub, x, r, I, Fin.reduceFinMk, zero_add, Fin.zero_eta] at h ⊢
  all_goals
    rw [h]
    ext <;> simp [GaussianRealPoint,
      Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

private theorem hcentR :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates), (![F.q
        (0 : Fin (4 : ℕ)), F.q a.succ, F.q (a + (1 : Fin (3 : ℕ))).succ, F.q (a + (2 : Fin (3 :
        ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 +
        (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 :
        Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3
        : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p
        (3 : Fin (4 : ℕ))]) → ((F.slot = a + (1 : Fin (3 : ℕ))) → (∀ (J : ProtoTile),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (ProperBandQuadruple r) → ((r 0 = (2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p
        0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2)) → ((r 1 = p 0) → ((r 2 = p 2) → ((r 3 = p 3)
        → ((r 2 = C.1.1) → (
    let I : GaussianInt := ⟨0, 1⟩
    let w := BandVectors.1 (r 3) (r 2)
    let x := BandVectors.1 (r 1) (r 3)
    let y := BandVectors.1 (r 2) (r 1)
    let wa := BandVectors.2 (r 3) (r 2)
    let xa := BandVectors.2 (r 1) (r 3)
    let ya := BandVectors.2 (r 2) (r 1)
    (BandVectors.1 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) + BandVectors.1 (r (1 : Fin (4 :
        ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) =
        (0 : GaussianInt) ∧ BandVectors.2 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
        BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.2 (r (2 : Fin (4
        : ℕ))) (r (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (r (1 : Fin (4 : ℕ))) (r
        (0 : Fin (4 : ℕ))) = BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) - ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) ∧ BandVectors.2
        (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) = BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 :
        Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 :
        ℕ))) ∧ (ProperBandQuadruple r → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (r (0 : Fin (4 : ℕ)))
        (r j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) ∧
        BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r
        j.succ) (r (0 : Fin (4 : ℕ))))) → ((SemiProperQuadruple ![r 0, r 2, r 3, r 1]) →
        ((BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) + BandVectors.1 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)),
        r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧
        BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) + BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)),
        r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧
        BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) = BandVectors.1 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 :
        ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) ∧
        BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) = BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 :
        ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) ∧
        (ProperBandQuadruple ![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r
        (1 : Fin (4 : ℕ))] → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 :
        Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) (![r (0 : Fin
        (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) = ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] j.succ) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) =
        -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 :
        Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r
        (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))))) → ((BandVectors.1 (r 2) (r
        0) = y - I * w) → ((BandVectors.2 (r 2) (r 0) = ya + I * wa) → ((BandVectors.1 (r 0) (r
        2) = I * (y - I * w)) → ((BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa)) →
        ((BandVectors.1 (p 0) (p 2) = I * y) → ((BandVectors.2 (p 0) (p 2) = -I * ya) → ((-(w - I
        * w) - (x - I * y - I * (x - I * y)) = (2 : GaussianInt) * y ∧ x - I * y + I * (x - I *
        y) + (w - I * w) = (2 : GaussianInt) * I * x ∧ -(x - I * x) - (w - I * w) = y - I * y ∧ y
        - I * w + I * (y - I * w) - (w - I * w) = y + I * y ∧ w - I * x - I * (w - I * x) - (w -
        I * w) = -I * x - x ∧ -(y - I * y) - (w - I * w) = -I * x + x ∧ y - I * w - I * (y - I *
        w) - (y - I * y) = -I * w - w ∧ -(x - I * x) - (y - I * y) = -I * w + w ∧ -(y - I * y) -
        (x - I * x) = w - I * w ∧ w - I * x + I * (w - I * x) - (x - I * x) = w + I * w) → ((-(wa
        - -I * wa) - (xa - -I * ya - -I * (xa - -I * ya)) = (2 : GaussianInt) * ya ∧ xa - -I * ya
        + -I * (xa - -I * ya) + (wa - -I * wa) = (2 : GaussianInt) * -I * xa ∧ -(xa - -I * xa) -
        (wa - -I * wa) = ya - -I * ya ∧ ya - -I * wa + -I * (ya - -I * wa) - (wa - -I * wa) = ya
        + -I * ya ∧ wa - -I * xa - -I * (wa - -I * xa) - (wa - -I * wa) = - -I * xa - xa ∧ -(ya -
        -I * ya) - (wa - -I * wa) = - -I * xa + xa ∧ ya - -I * wa - -I * (ya - -I * wa) - (ya -
        -I * ya) = - -I * wa - wa ∧ -(xa - -I * xa) - (ya - -I * ya) = - -I * wa + wa ∧ -(ya - -I
        * ya) - (xa - -I * xa) = wa - -I * wa ∧ wa - -I * xa + -I * (wa - -I * xa) - (xa - -I *
        xa) = wa + -I * wa) → ((-(xa - -I * xa) - (wa - -I * wa) = ya - -I * ya) → ((ya - -I * wa
        + -I * (ya - -I * wa) - (wa - -I * wa) = ya + -I * ya) → ((BandVectors.1 (r 0) (r 2) = I
        * (y - I * w)) → ((BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa)) → ((TileCentroid J -
        TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (-(x - I * x))) → ((TileCentroid
        (D.tiles a true) - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (w - I * w)) →
        (TileCentroid Rplus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint ((y - I * w)
        + I * (y - I * w))))))))))))))))))))))))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hstep hslot J r hr hcoord hA hB hE
      hparent I w x y wa xa ya laws hrot rlaws hv ha hflipv hflipa hvp hap vAlg aAlg aThird
      aFourth vflip aflip hcentJ hcentK
  have h := F.plus_centroid
  rw [hslot] at h
  fin_cases a
  all_goals
    simp only [one_div, Fin.mk_one, Fin.isValue, Fin.reduceAdd, Fin.reduceSucc,
        Fin.reduceFinMk, Fin.succ_zero_eq_one, Fin.zero_eta, zero_add, Fin.succ_one_eq_two]
        at h ⊢
    have hv' := hv
    have vf' := vflip
    simp only [Fin.isValue, Fin.mk_one, Fin.succ_one_eq_two, Fin.reduceAdd, Fin.reduceSucc,
        Fin.succ_zero_eq_one, Matrix.cons_val, Matrix.cons_val_zero, r, Fin.reduceFinMk,
        Fin.zero_eta, zero_add] at hv' vf'
    rw [hv', vf'] at h
    simpa [y, w, I, r, GaussianRealPoint,
      Zsqrtd.re_mul, Zsqrtd.im_mul] using h

private theorem hcentJK :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (J : ProtoTile),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let w := BandVectors.1 (r 3) (r 2)
    let x := BandVectors.1 (r 1) (r 3)
    let y := BandVectors.1 (r 2) (r 1)
    (-(w - I * w) - (x - I * y - I * (x - I * y)) = (2 : GaussianInt) * y ∧ x - I * y + I * (x -
        I * y) + (w - I * w) = (2 : GaussianInt) * I * x ∧ -(x - I * x) - (w - I * w) = y - I * y
        ∧ y - I * w + I * (y - I * w) - (w - I * w) = y + I * y ∧ w - I * x - I * (w - I * x) -
        (w - I * w) = -I * x - x ∧ -(y - I * y) - (w - I * w) = -I * x + x ∧ y - I * w - I * (y -
        I * w) - (y - I * y) = -I * w - w ∧ -(x - I * x) - (y - I * y) = -I * w + w ∧ -(y - I *
        y) - (x - I * x) = w - I * w ∧ w - I * x + I * (w - I * x) - (x - I * x) = w + I * w) → (
    let halfPoint : GaussianInt → ℝ × ℝ :=
      fun z => (1 / 2 : ℝ) • GaussianRealPoint z
    (∀ (u : GaussianInt), ∀ (v : GaussianInt), halfPoint u - halfPoint v = halfPoint (u - v)) →
        ((TileCentroid J - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (-(x - I * x)))
        → ((TileCentroid (D.tiles a true) - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint
        (w - I * w)) → (TileCentroid J - TileCentroid (D.tiles a true) = (1 / 2 : ℝ) •
        GaussianRealPoint (y - I * y))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a J r I w x y vAlg halfPoint
      halfPoint_sub hcentJ hcentK
  have h := vAlg.2.2.1
  calc
    _ = (TileCentroid J - TileCentroid F.tile) -
        (TileCentroid (D.tiles a true) - TileCentroid F.tile) := by abel
    _ = _ := by
      rw [hcentJ, hcentK]
      change halfPoint (-(x - I * x)) - halfPoint (w - I * w) = _
      rw [halfPoint_sub, vAlg.2.2.1]

private theorem hcentRK :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let w := BandVectors.1 (r 3) (r 2)
    let x := BandVectors.1 (r 1) (r 3)
    let y := BandVectors.1 (r 2) (r 1)
    (-(w - I * w) - (x - I * y - I * (x - I * y)) = (2 : GaussianInt) * y ∧ x - I * y + I * (x -
        I * y) + (w - I * w) = (2 : GaussianInt) * I * x ∧ -(x - I * x) - (w - I * w) = y - I * y
        ∧ y - I * w + I * (y - I * w) - (w - I * w) = y + I * y ∧ w - I * x - I * (w - I * x) -
        (w - I * w) = -I * x - x ∧ -(y - I * y) - (w - I * w) = -I * x + x ∧ y - I * w - I * (y -
        I * w) - (y - I * y) = -I * w - w ∧ -(x - I * x) - (y - I * y) = -I * w + w ∧ -(y - I *
        y) - (x - I * x) = w - I * w ∧ w - I * x + I * (w - I * x) - (x - I * x) = w + I * w) → (
    let halfPoint : GaussianInt → ℝ × ℝ :=
      fun z => (1 / 2 : ℝ) • GaussianRealPoint z
    (∀ (u : GaussianInt), ∀ (v : GaussianInt), halfPoint u - halfPoint v = halfPoint (u - v)) →
        ((TileCentroid (D.tiles a true) - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint
        (w - I * w)) → ((TileCentroid Rplus - TileCentroid F.tile = (1 / 2 : ℝ) •
        GaussianRealPoint ((y - I * w) + I * (y - I * w))) → (TileCentroid Rplus - TileCentroid
        (D.tiles a true) = (1 / 2 : ℝ) • GaussianRealPoint (y + I * y))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a r I w x y vAlg halfPoint halfPoint_sub
      hcentK hcentR
  calc
    _ = (TileCentroid Rplus - TileCentroid F.tile) -
        (TileCentroid (D.tiles a true) - TileCentroid F.tile) := by abel
    _ = _ := by
      rw [hcentR, hcentK]
      change halfPoint ((y - I * w) + I * (y - I * w)) -
        halfPoint (w - I * w) = _
      rw [halfPoint_sub, vAlg.2.2.2.1]

private theorem hslopeJ :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates), (![F.q
        (0 : Fin (4 : ℕ)), F.q a.succ, F.q (a + (1 : Fin (3 : ℕ))).succ, F.q (a + (2 : Fin (3 :
        ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 +
        (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 :
        Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3
        : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p
        (3 : Fin (4 : ℕ))]) → ((F.slot = a + (1 : Fin (3 : ℕ))) → (∀ (J : ProtoTile),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (ProperBandQuadruple r) → ((r 0 = (2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p
        0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2)) → ((r 1 = p 0) → ((r 2 = p 2) → ((r 3 = p 3)
        → ((r 2 = C.1.1) → (
    let I : GaussianInt := ⟨0, 1⟩
    let w := BandVectors.1 (r 3) (r 2)
    let x := BandVectors.1 (r 1) (r 3)
    let y := BandVectors.1 (r 2) (r 1)
    let wa := BandVectors.2 (r 3) (r 2)
    let xa := BandVectors.2 (r 1) (r 3)
    let ya := BandVectors.2 (r 2) (r 1)
    (BandVectors.1 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) + BandVectors.1 (r (1 : Fin (4 :
        ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) =
        (0 : GaussianInt) ∧ BandVectors.2 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
        BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.2 (r (2 : Fin (4
        : ℕ))) (r (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (r (1 : Fin (4 : ℕ))) (r
        (0 : Fin (4 : ℕ))) = BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) - ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) ∧ BandVectors.2
        (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) = BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 :
        Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 :
        ℕ))) ∧ (ProperBandQuadruple r → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (r (0 : Fin (4 : ℕ)))
        (r j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) ∧
        BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r
        j.succ) (r (0 : Fin (4 : ℕ))))) → ((SemiProperQuadruple ![r 0, r 2, r 3, r 1]) →
        ((BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) + BandVectors.1 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)),
        r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧
        BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) + BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)),
        r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧
        BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) = BandVectors.1 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 :
        ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) ∧
        BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) = BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 :
        ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) ∧
        (ProperBandQuadruple ![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r
        (1 : Fin (4 : ℕ))] → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 :
        Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) (![r (0 : Fin
        (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) = ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] j.succ) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) =
        -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 :
        Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r
        (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))))) → ((BandVectors.1 (r 2) (r
        0) = y - I * w) → ((BandVectors.2 (r 2) (r 0) = ya + I * wa) → ((BandVectors.1 (r 0) (r
        2) = I * (y - I * w)) → ((BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa)) →
        ((BandVectors.1 (p 0) (p 2) = I * y) → ((BandVectors.2 (p 0) (p 2) = -I * ya) → ((-(w - I
        * w) - (x - I * y - I * (x - I * y)) = (2 : GaussianInt) * y ∧ x - I * y + I * (x - I *
        y) + (w - I * w) = (2 : GaussianInt) * I * x ∧ -(x - I * x) - (w - I * w) = y - I * y ∧ y
        - I * w + I * (y - I * w) - (w - I * w) = y + I * y ∧ w - I * x - I * (w - I * x) - (w -
        I * w) = -I * x - x ∧ -(y - I * y) - (w - I * w) = -I * x + x ∧ y - I * w - I * (y - I *
        w) - (y - I * y) = -I * w - w ∧ -(x - I * x) - (y - I * y) = -I * w + w ∧ -(y - I * y) -
        (x - I * x) = w - I * w ∧ w - I * x + I * (w - I * x) - (x - I * x) = w + I * w) → ((-(wa
        - -I * wa) - (xa - -I * ya - -I * (xa - -I * ya)) = (2 : GaussianInt) * ya ∧ xa - -I * ya
        + -I * (xa - -I * ya) + (wa - -I * wa) = (2 : GaussianInt) * -I * xa ∧ -(xa - -I * xa) -
        (wa - -I * wa) = ya - -I * ya ∧ ya - -I * wa + -I * (ya - -I * wa) - (wa - -I * wa) = ya
        + -I * ya ∧ wa - -I * xa - -I * (wa - -I * xa) - (wa - -I * wa) = - -I * xa - xa ∧ -(ya -
        -I * ya) - (wa - -I * wa) = - -I * xa + xa ∧ ya - -I * wa - -I * (ya - -I * wa) - (ya -
        -I * ya) = - -I * wa - wa ∧ -(xa - -I * xa) - (ya - -I * ya) = - -I * wa + wa ∧ -(ya - -I
        * ya) - (xa - -I * xa) = wa - -I * wa ∧ wa - -I * xa + -I * (wa - -I * xa) - (xa - -I *
        xa) = wa + -I * wa) → ((-(xa - -I * xa) - (wa - -I * wa) = ya - -I * ya) → ((ya - -I * wa
        + -I * (ya - -I * wa) - (wa - -I * wa) = ya + -I * ya) → ((BandVectors.1 (r 0) (r 2) = I
        * (y - I * w)) → ((BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa)) → ((TileCentroid J -
        TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (-(x - I * x))) → ((TileCentroid
        (D.tiles a true) - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (w - I * w)) →
        ((TileCentroid Rplus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint ((y - I * w)
        + I * (y - I * w))) → ((TileCentroid J - TileCentroid (D.tiles a true) = (1 / 2 : ℝ) •
        GaussianRealPoint (y - I * y)) → ((TileCentroid Rplus - TileCentroid (D.tiles a true) =
        (1 / 2 : ℝ) • GaussianRealPoint (y + I * y)) → ((TileOdometer (p 0) (D.tiles a true)
        (D.functions a true)) → ((BandPrototile (p 0) (D.tiles a true)) → ((F.q a.succ = p 0) →
        ((F.q ((a + 1).succ) = p 2) → ((TileCentroid Rplus - TileCentroid (D.tiles a true) = (1 /
        2 : ℝ) • GaussianRealPoint (BandVectors.1 (p 2) (p 0) + BandVectors.1 (p 0) (p 2))) → (∀
            (sJ : ℝ × ℝ), (sJ.1 - F.outerSlope.1 = (if false = true then (1 : ℝ) else (-1 : ℝ))
            * (1
        / 2 : ℝ) * ((↑(BandVectors.2 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 :
        Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ)
        (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((sJ.2 - F.outerSlope.2 = (if false
        = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (F.slot + (2 :
        Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2
        (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)).re :
        ℝ))) → ((0 < (F.q a.succ).1) → (∀ (sA : ℝ × ℝ), (PartialOdometerSlope (D.functions a
        true) = some sA) → ((sA.1 - F.outerSlope.1 = (if true = true then (1 : ℝ) else (-1 : ℝ))
        * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin
        (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q (a +
        (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((sA.2 - F.outerSlope.2 = (if true = true then (1
        : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ)
        (F.q (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (F.q (a + (2 : Fin (3 :
        ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (sJ - F.outerSlope = (1 / 2 :
        ℝ) • GaussianRealPoint (-(xa - (-I) * xa))))))))))))))))))))))))))))))))))))))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hstep hslot J r hr hcoord hA hB hE
      hparent I w x y wa xa ya laws hrot rlaws hv ha hflipv hflipa hvp hap vAlg aAlg aThird
      aFourth vflip aflip hcentJ hcentK hcentR hcentJK hcentRK hodoK hbandK hAcoord hBcoord
      hcentRnew sJ hreJ himJ hqapos sA hsA hreA himA
  have hJvec : BandVectors.2 (F.q ((F.slot + 2).succ))
      (F.q ((F.slot + 1).succ)) = xa := by
    rw [hslot]
    fin_cases a <;> simp [r, xa]
  rw [hJvec] at hreJ himJ
  have h1 : sJ.1 - F.outerSlope.1 =
      -1 * (1 / 2 : ℝ) * ((xa.re : ℝ) - (xa.im : ℝ)) := by
    simpa using hreJ
  have h2 : sJ.2 - F.outerSlope.2 =
      -1 * (1 / 2 : ℝ) * ((xa.im : ℝ) + (xa.re : ℝ)) := by
    simpa using himJ
  apply Prod.ext
  · change sJ.1 - F.outerSlope.1 =
      (1 / 2 : ℝ) * ((-(xa - (-I) * xa)).re : ℝ)
    rw [h1]
    simp [I, xa, Zsqrtd.re_mul]
    ring
  · change sJ.2 - F.outerSlope.2 =
      (1 / 2 : ℝ) * ((-(xa - (-I) * xa)).im : ℝ)
    rw [h2]
    simp [I, xa, Zsqrtd.im_mul]
    ring

private theorem hslopeA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates), (![F.q
        (0 : Fin (4 : ℕ)), F.q a.succ, F.q (a + (1 : Fin (3 : ℕ))).succ, F.q (a + (2 : Fin (3 :
        ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 +
        (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 :
        Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3
        : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p
        (3 : Fin (4 : ℕ))]) → ((F.slot = a + (1 : Fin (3 : ℕ))) → (∀ (J : ProtoTile),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (ProperBandQuadruple r) → ((r 0 = (2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p
        0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2)) → ((r 1 = p 0) → ((r 2 = p 2) → ((r 3 = p 3)
        → ((r 2 = C.1.1) → (
    let I : GaussianInt := ⟨0, 1⟩
    let w := BandVectors.1 (r 3) (r 2)
    let x := BandVectors.1 (r 1) (r 3)
    let y := BandVectors.1 (r 2) (r 1)
    let wa := BandVectors.2 (r 3) (r 2)
    let xa := BandVectors.2 (r 1) (r 3)
    let ya := BandVectors.2 (r 2) (r 1)
    (BandVectors.1 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) + BandVectors.1 (r (1 : Fin (4 :
        ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) =
        (0 : GaussianInt) ∧ BandVectors.2 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
        BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.2 (r (2 : Fin (4
        : ℕ))) (r (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (r (1 : Fin (4 : ℕ))) (r
        (0 : Fin (4 : ℕ))) = BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) - ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) ∧ BandVectors.2
        (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) = BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 :
        Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 :
        ℕ))) ∧ (ProperBandQuadruple r → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (r (0 : Fin (4 : ℕ)))
        (r j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) ∧
        BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r
        j.succ) (r (0 : Fin (4 : ℕ))))) → ((SemiProperQuadruple ![r 0, r 2, r 3, r 1]) →
        ((BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) + BandVectors.1 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)),
        r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧
        BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) + BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)),
        r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧
        BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) = BandVectors.1 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 :
        ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) ∧
        BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) = BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 :
        ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) ∧
        (ProperBandQuadruple ![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r
        (1 : Fin (4 : ℕ))] → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 :
        Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) (![r (0 : Fin
        (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) = ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] j.succ) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) =
        -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 :
        Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r
        (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))))) → ((BandVectors.1 (r 2) (r
        0) = y - I * w) → ((BandVectors.2 (r 2) (r 0) = ya + I * wa) → ((BandVectors.1 (r 0) (r
        2) = I * (y - I * w)) → ((BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa)) →
        ((BandVectors.1 (p 0) (p 2) = I * y) → ((BandVectors.2 (p 0) (p 2) = -I * ya) → ((-(w - I
        * w) - (x - I * y - I * (x - I * y)) = (2 : GaussianInt) * y ∧ x - I * y + I * (x - I *
        y) + (w - I * w) = (2 : GaussianInt) * I * x ∧ -(x - I * x) - (w - I * w) = y - I * y ∧ y
        - I * w + I * (y - I * w) - (w - I * w) = y + I * y ∧ w - I * x - I * (w - I * x) - (w -
        I * w) = -I * x - x ∧ -(y - I * y) - (w - I * w) = -I * x + x ∧ y - I * w - I * (y - I *
        w) - (y - I * y) = -I * w - w ∧ -(x - I * x) - (y - I * y) = -I * w + w ∧ -(y - I * y) -
        (x - I * x) = w - I * w ∧ w - I * x + I * (w - I * x) - (x - I * x) = w + I * w) → ((-(wa
        - -I * wa) - (xa - -I * ya - -I * (xa - -I * ya)) = (2 : GaussianInt) * ya ∧ xa - -I * ya
        + -I * (xa - -I * ya) + (wa - -I * wa) = (2 : GaussianInt) * -I * xa ∧ -(xa - -I * xa) -
        (wa - -I * wa) = ya - -I * ya ∧ ya - -I * wa + -I * (ya - -I * wa) - (wa - -I * wa) = ya
        + -I * ya ∧ wa - -I * xa - -I * (wa - -I * xa) - (wa - -I * wa) = - -I * xa - xa ∧ -(ya -
        -I * ya) - (wa - -I * wa) = - -I * xa + xa ∧ ya - -I * wa - -I * (ya - -I * wa) - (ya -
        -I * ya) = - -I * wa - wa ∧ -(xa - -I * xa) - (ya - -I * ya) = - -I * wa + wa ∧ -(ya - -I
        * ya) - (xa - -I * xa) = wa - -I * wa ∧ wa - -I * xa + -I * (wa - -I * xa) - (xa - -I *
        xa) = wa + -I * wa) → ((-(xa - -I * xa) - (wa - -I * wa) = ya - -I * ya) → ((ya - -I * wa
        + -I * (ya - -I * wa) - (wa - -I * wa) = ya + -I * ya) → ((BandVectors.1 (r 0) (r 2) = I
        * (y - I * w)) → ((BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa)) → ((TileCentroid J -
        TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (-(x - I * x))) → ((TileCentroid
        (D.tiles a true) - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (w - I * w)) →
        ((TileCentroid Rplus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint ((y - I * w)
        + I * (y - I * w))) → ((TileCentroid J - TileCentroid (D.tiles a true) = (1 / 2 : ℝ) •
        GaussianRealPoint (y - I * y)) → ((TileCentroid Rplus - TileCentroid (D.tiles a true) =
        (1 / 2 : ℝ) • GaussianRealPoint (y + I * y)) → ((TileOdometer (p 0) (D.tiles a true)
        (D.functions a true)) → ((BandPrototile (p 0) (D.tiles a true)) → ((F.q a.succ = p 0) →
        ((F.q ((a + 1).succ) = p 2) → ((TileCentroid Rplus - TileCentroid (D.tiles a true) = (1 /
        2 : ℝ) • GaussianRealPoint (BandVectors.1 (p 2) (p 0) + BandVectors.1 (p 0) (p 2))) → (∀
            (sJ : ℝ × ℝ), (0 < (F.q a.succ).1) → (∀ (sA : ℝ × ℝ), (PartialOdometerSlope (D.functions
        a true) = some sA) → ((sA.1 - F.outerSlope.1 = (if true = true then (1 : ℝ) else (-1 :
        ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 :
        Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q
        (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((sA.2 - F.outerSlope.2 = (if true = true
        then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 :
        ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (F.q (a + (2 :
        Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → ((sJ - F.outerSlope
        = (1 / 2 : ℝ) • GaussianRealPoint (-(xa - (-I) * xa))) → (sA - F.outerSlope = (1 / 2 :
        ℝ) • GaussianRealPoint (wa - (-I) * wa))))))))))))))))))))))))))))))))))))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hstep hslot J r hr hcoord hA hB hE
      hparent I w x y wa xa ya laws hrot rlaws hv ha hflipv hflipa hvp hap vAlg aAlg aThird
      aFourth vflip aflip hcentJ hcentK hcentR hcentJK hcentRK hodoK hbandK hAcoord hBcoord
      hcentRnew sJ hqapos sA hsA hreA himA hslopeJ
  have hslotvec : BandVectors.2 (F.q ((a + 2).succ))
      (F.q ((a + 1).succ)) = wa := by
    fin_cases a <;> simp [r, wa]
  have h1 := hreA
  have h2 := himA
  have h1 : sA.1 - F.outerSlope.1 = (1 / 2 : ℝ) *
    (((BandVectors.2 (F.q ((a + 2).succ))
      (F.q ((a + 1).succ))).re : ℤ) -
      ((BandVectors.2 (F.q ((a + 2).succ))
      (F.q ((a + 1).succ))).im : ℤ)) := by
    simpa using hreA
  have h2 : sA.2 - F.outerSlope.2 = (1 / 2 : ℝ) *
    (((BandVectors.2 (F.q ((a + 2).succ))
      (F.q ((a + 1).succ))).im : ℤ) +
      ((BandVectors.2 (F.q ((a + 2).succ))
      (F.q ((a + 1).succ))).re : ℤ)) := by
    simpa using himA
  rw [hslotvec] at h1 h2
  apply Prod.ext
  · simp only [one_div, Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im,
      Prod.fst_sub, GaussianRealPoint, neg_mul, sub_neg_eq_add, Zsqrtd.re_add, Zsqrtd.re_mul,
      zero_mul, mul_one, one_mul, zero_add, Int.cast_add, Int.cast_neg, Zsqrtd.im_add,
      Zsqrtd.im_mul, Prod.smul_mk, smul_eq_mul, I] at h1 ⊢
    exact_mod_cast h1
  · simp only [one_div, Int.reduceNeg, GaussianInt.intCast_im, GaussianInt.intCast_re,
      Prod.snd_sub, GaussianRealPoint, neg_mul, sub_neg_eq_add, Zsqrtd.re_add, Zsqrtd.re_mul,
      zero_mul, mul_one, one_mul, zero_add, Int.cast_add, Int.cast_neg, Zsqrtd.im_add,
      Zsqrtd.im_mul, Prod.smul_mk, smul_eq_mul, I] at h2 ⊢
    exact_mod_cast h2

private theorem hminusSlope :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wa := BandVectors.2 (r 3) (r 2)
    let xa := BandVectors.2 (r 1) (r 3)
    let ya := BandVectors.2 (r 2) (r 1)
    (-(xa - -I * xa) - (wa - -I * wa) = ya - -I * ya) → (∀ (sJ : ℝ × ℝ), ∀ (sA : ℝ × ℝ), (sJ -
        F.outerSlope = (1 / 2 : ℝ) • GaussianRealPoint (-(xa - (-I) * xa))) → ((sA -
        F.outerSlope = (1 / 2 : ℝ) • GaussianRealPoint (wa - (-I) * wa)) → (sJ - sA = (1 / 2 :
        ℝ) • GaussianRealPoint (ya - (-I) * ya)))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I wa xa ya aThird sJ sA hslopeJ hslopeA
  calc
    _ = (sJ - F.outerSlope) - (sA - F.outerSlope) := by abel
    _ = _ := by
      rw [hslopeJ, hslopeA]
      have h := congrArg (fun z : GaussianInt =>
        (1 / 2 : ℝ) • GaussianRealPoint z) aThird
      simp [GaussianRealPoint, I, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
      constructor <;> nlinarith

private theorem hplusSlopeRoot :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates), (![F.q
        (0 : Fin (4 : ℕ)), F.q a.succ, F.q (a + (1 : Fin (3 : ℕ))).succ, F.q (a + (2 : Fin (3 :
        ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 +
        (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 :
        Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3
        : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p
        (3 : Fin (4 : ℕ))]) → ((F.slot = a + (1 : Fin (3 : ℕ))) → (∀ (J : ProtoTile),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (ProperBandQuadruple r) → ((r 0 = (2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p
        0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2)) → ((r 1 = p 0) → ((r 2 = p 2) → ((r 3 = p 3)
        → ((r 2 = C.1.1) → (
    let I : GaussianInt := ⟨0, 1⟩
    let w := BandVectors.1 (r 3) (r 2)
    let x := BandVectors.1 (r 1) (r 3)
    let y := BandVectors.1 (r 2) (r 1)
    let wa := BandVectors.2 (r 3) (r 2)
    let xa := BandVectors.2 (r 1) (r 3)
    let ya := BandVectors.2 (r 2) (r 1)
    (BandVectors.1 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) + BandVectors.1 (r (1 : Fin (4 :
        ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) =
        (0 : GaussianInt) ∧ BandVectors.2 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
        BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.2 (r (2 : Fin (4
        : ℕ))) (r (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (r (1 : Fin (4 : ℕ))) (r
        (0 : Fin (4 : ℕ))) = BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) - ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) ∧ BandVectors.2
        (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) = BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 :
        Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 :
        ℕ))) ∧ (ProperBandQuadruple r → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (r (0 : Fin (4 : ℕ)))
        (r j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) ∧
        BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r
        j.succ) (r (0 : Fin (4 : ℕ))))) → ((SemiProperQuadruple ![r 0, r 2, r 3, r 1]) →
        ((BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) + BandVectors.1 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)),
        r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧
        BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) + BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)),
        r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧
        BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) = BandVectors.1 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 :
        ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) ∧
        BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) = BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (3 : Fin
        (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 :
        ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) ∧
        (ProperBandQuadruple ![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r
        (1 : Fin (4 : ℕ))] → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 :
        Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) (![r (0 : Fin
        (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) = ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 :
        ℕ)), r (1 : Fin (4 : ℕ))] j.succ) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin
        (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (![r (0 : Fin (4 : ℕ)),
        r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) (![r (0
        : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) =
        -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 :
        Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] j.succ) (![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r
        (3 : Fin (4 : ℕ)), r (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))))) → ((BandVectors.1 (r 2) (r
        0) = y - I * w) → ((BandVectors.2 (r 2) (r 0) = ya + I * wa) → ((BandVectors.1 (r 0) (r
        2) = I * (y - I * w)) → ((BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa)) →
        ((BandVectors.1 (p 0) (p 2) = I * y) → ((BandVectors.2 (p 0) (p 2) = -I * ya) → ((-(w - I
        * w) - (x - I * y - I * (x - I * y)) = (2 : GaussianInt) * y ∧ x - I * y + I * (x - I *
        y) + (w - I * w) = (2 : GaussianInt) * I * x ∧ -(x - I * x) - (w - I * w) = y - I * y ∧ y
        - I * w + I * (y - I * w) - (w - I * w) = y + I * y ∧ w - I * x - I * (w - I * x) - (w -
        I * w) = -I * x - x ∧ -(y - I * y) - (w - I * w) = -I * x + x ∧ y - I * w - I * (y - I *
        w) - (y - I * y) = -I * w - w ∧ -(x - I * x) - (y - I * y) = -I * w + w ∧ -(y - I * y) -
        (x - I * x) = w - I * w ∧ w - I * x + I * (w - I * x) - (x - I * x) = w + I * w) → ((-(wa
        - -I * wa) - (xa - -I * ya - -I * (xa - -I * ya)) = (2 : GaussianInt) * ya ∧ xa - -I * ya
        + -I * (xa - -I * ya) + (wa - -I * wa) = (2 : GaussianInt) * -I * xa ∧ -(xa - -I * xa) -
        (wa - -I * wa) = ya - -I * ya ∧ ya - -I * wa + -I * (ya - -I * wa) - (wa - -I * wa) = ya
        + -I * ya ∧ wa - -I * xa - -I * (wa - -I * xa) - (wa - -I * wa) = - -I * xa - xa ∧ -(ya -
        -I * ya) - (wa - -I * wa) = - -I * xa + xa ∧ ya - -I * wa - -I * (ya - -I * wa) - (ya -
        -I * ya) = - -I * wa - wa ∧ -(xa - -I * xa) - (ya - -I * ya) = - -I * wa + wa ∧ -(ya - -I
        * ya) - (xa - -I * xa) = wa - -I * wa ∧ wa - -I * xa + -I * (wa - -I * xa) - (xa - -I *
        xa) = wa + -I * wa) → ((-(xa - -I * xa) - (wa - -I * wa) = ya - -I * ya) → ((ya - -I * wa
        + -I * (ya - -I * wa) - (wa - -I * wa) = ya + -I * ya) → ((BandVectors.1 (r 0) (r 2) = I
        * (y - I * w)) → ((BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa)) → ((TileCentroid J -
        TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (-(x - I * x))) → ((TileCentroid
        (D.tiles a true) - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (w - I * w)) →
        ((TileCentroid Rplus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint ((y - I * w)
        + I * (y - I * w))) → ((TileCentroid J - TileCentroid (D.tiles a true) = (1 / 2 : ℝ) •
        GaussianRealPoint (y - I * y)) → ((TileCentroid Rplus - TileCentroid (D.tiles a true) =
        (1 / 2 : ℝ) • GaussianRealPoint (y + I * y)) → ((TileOdometer (p 0) (D.tiles a true)
        (D.functions a true)) → ((BandPrototile (p 0) (D.tiles a true)) → ((F.q a.succ = p 0) →
        ((F.q ((a + 1).succ) = p 2) → ((TileCentroid Rplus - TileCentroid (D.tiles a true) = (1 /
        2 : ℝ) • GaussianRealPoint (BandVectors.1 (p 2) (p 0) + BandVectors.1 (p 0) (p 2))) → (∀
            (sJ : ℝ × ℝ), (0 < (F.q a.succ).1) → (∀ (sA : ℝ × ℝ), (PartialOdometerSlope (D.functions
        a true) = some sA) → ((sA.1 - F.outerSlope.1 = (if true = true then (1 : ℝ) else (-1 :
        ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 :
        Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q
        (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((sA.2 - F.outerSlope.2 = (if true = true
        then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 :
        ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (F.q (a + (2 :
        Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → ((sJ - F.outerSlope
        = (1 / 2 : ℝ) • GaussianRealPoint (-(xa - (-I) * xa))) → ((sA - F.outerSlope = (1 / 2 :
        ℝ) • GaussianRealPoint (wa - (-I) * wa)) → ((sJ - sA = (1 / 2 : ℝ) • GaussianRealPoint
        (ya - (-I) * ya)) → (F.plusSlope - F.outerSlope = (1 / 2 : ℝ) • GaussianRealPoint (ya +
        I * wa + (-I) * (ya + I * wa)))))))))))))))))))))))))))))))))))))))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p hstep hslot J r hr hcoord hA hB hE
      hparent I w x y wa xa ya laws hrot rlaws hv ha hflipv hflipa hvp hap vAlg aAlg aThird
      aFourth vflip aflip hcentJ hcentK hcentR hcentJK hcentRK hodoK hbandK hAcoord hBcoord
      hcentRnew sJ hqapos sA hsA hreA himA hslopeJ hslopeA hminusSlope
  have h := F.plus_difference
  rw [hslot] at h
  fin_cases a
  all_goals
    have hIn := ha
    have hFlip := hflipa
    simp only [Fin.isValue, Fin.mk_one, Fin.succ_one_eq_two, Fin.reduceAdd, Fin.reduceSucc,
        Fin.succ_zero_eq_one, Matrix.cons_val, Matrix.cons_val_zero, neg_mul, one_div, r,
        Fin.reduceFinMk, Fin.zero_eta, zero_add] at hIn hFlip h ⊢
    rw [hIn, hFlip] at h
    simpa [I, ya, wa, GaussianRealPoint, Zsqrtd.re_mul,
      Zsqrtd.im_mul] using h

private theorem hplusSlope :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wa := BandVectors.2 (r 3) (r 2)
    let ya := BandVectors.2 (r 2) (r 1)
    let halfPoint : GaussianInt → ℝ × ℝ :=
      fun z => (1 / 2 : ℝ) • GaussianRealPoint z
    (∀ (u : GaussianInt), ∀ (v : GaussianInt), halfPoint u - halfPoint v = halfPoint (u - v)) →
        (∀ (sA : ℝ × ℝ), (sA - F.outerSlope = (1 / 2 : ℝ) • GaussianRealPoint (wa - (-I) * wa))
        → ((F.plusSlope - F.outerSlope = (1 / 2 : ℝ) • GaussianRealPoint (ya + I * wa + (-I) *
        (ya + I * wa))) → (((ya + I * wa + (-I) * (ya + I * wa)) - (wa - (-I) * wa) = ya + (-I) *
        ya) → (F.plusSlope - sA = (1 / 2 : ℝ) • GaussianRealPoint (ya + (-I) * ya))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I wa ya halfPoint halfPoint_sub sA
      hslopeA hplusSlopeRoot hplusDelta
  calc
    _ = (F.plusSlope - F.outerSlope) - (sA - F.outerSlope) := by abel
    _ = halfPoint
        ((ya + I * wa + (-I) * (ya + I * wa)) -
          (wa - (-I) * wa)) := by
      rw [hplusSlopeRoot, hslopeA]
      change halfPoint (ya + I * wa + (-I) * (ya + I * wa)) -
        halfPoint (wa - (-I) * wa) = _
      exact halfPoint_sub _ _
    _ = halfPoint (ya + (-I) * ya) := by rw [hplusDelta]
    _ = _ := rfl

end AFrameBProof

namespace AFrameBDetails

private theorem hcoord :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates), (![F.q (0 : Fin (4 : ℕ)), F.q a.succ, F.q (a + (1 : Fin (3
        : ℕ))).succ, F.q (a + (2 : Fin (3 : ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 +
        (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 :
        ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4
        : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 :
        Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))]) → (
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    r 0 = (2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1, 2 * (p 0).2 + 2 * (p 2).2 + 2 * (p
        3).2 - (p 1).2)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hstep r
  have := congrFun hstep 0
  simpa [r] using this

private theorem hA :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates), (![F.q (0 : Fin (4 : ℕ)), F.q a.succ, F.q (a + (1 : Fin (3
        : ℕ))).succ, F.q (a + (2 : Fin (3 : ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 +
        (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 :
        ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4
        : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 :
        Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))]) → (
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    r 1 = p 0) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hstep r
  have := congrFun hstep 1
  simpa [r] using this

private theorem hB :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates), (![F.q (0 : Fin (4 : ℕ)), F.q a.succ, F.q (a + (1 : Fin (3
        : ℕ))).succ, F.q (a + (2 : Fin (3 : ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 +
        (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 :
        ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4
        : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 :
        Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))]) → (
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    r 2 = p 2) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hstep r
  have := congrFun hstep 2
  simpa [r] using this

private theorem hE :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates), (![F.q (0 : Fin (4 : ℕ)), F.q a.succ, F.q (a + (1 : Fin (3
        : ℕ))).succ, F.q (a + (2 : Fin (3 : ℕ))).succ] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 +
        (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 :
        ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4
        : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 :
        Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))]) → (
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    r 3 = p 3) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hstep r
  have := congrFun hstep 3
  simpa [r] using this

private theorem hparent :
    (by
      classical
      exact
        ∀ (C : BandCircle) (orientation : Bool)
          (base Rminus Rplus : ProtoTile)
          (hminus hplus : PartialOdometer)
          (F :
            P4458T1BoundaryFrame C orientation base Rminus Rplus
              hminus hplus)
          (a : Fin (3 : ℕ)),
          F.slot = a + (1 : Fin (3 : ℕ)) →
            let r :=
              ![F.q (0 : Fin (4 : ℕ)), F.q a.succ, F.q (a + (1 : Fin (3 : ℕ))).succ,
                F.q (a + (2 : Fin (3 : ℕ))).succ];
            r (2 : Fin (4 : ℕ)) =
              C.1.1) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a hslot r
  rw [← F.parent, hslot]
  fin_cases a <;> simp [r]

private theorem hflipv :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (ProperBandQuadruple r) → (
    let I : GaussianInt := ⟨0, 1⟩
    let w := BandVectors.1 (r 3) (r 2)
    let y := BandVectors.1 (r 2) (r 1)
    (BandVectors.1 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) + BandVectors.1 (r (1 : Fin (4 :
        ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) =
        (0 : GaussianInt) ∧ BandVectors.2 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
        BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.2 (r (2 : Fin (4
        : ℕ))) (r (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (r (1 : Fin (4 : ℕ))) (r
        (0 : Fin (4 : ℕ))) = BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) - ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) ∧ BandVectors.2
        (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) = BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 :
        Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 :
        ℕ))) ∧ (ProperBandQuadruple r → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (r (0 : Fin (4 : ℕ)))
        (r j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) ∧
        BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r
        j.succ) (r (0 : Fin (4 : ℕ))))) → ((BandVectors.1 (r 2) (r 0) = y - I * w) →
        (BandVectors.1 (r 0) (r 2) = I * (y - I * w)))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r hr I w y laws hv
  have h := (laws.2.2.2.2 hr 1).1
  simpa [I, hv] using h

private theorem hflipa :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (ProperBandQuadruple r) → (
    let I : GaussianInt := ⟨0, 1⟩
    let wa := BandVectors.2 (r 3) (r 2)
    let ya := BandVectors.2 (r 2) (r 1)
    (BandVectors.1 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) + BandVectors.1 (r (1 : Fin (4 :
        ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) =
        (0 : GaussianInt) ∧ BandVectors.2 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
        BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.2 (r (2 : Fin (4
        : ℕ))) (r (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (r (1 : Fin (4 : ℕ))) (r
        (0 : Fin (4 : ℕ))) = BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) - ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) ∧ BandVectors.2
        (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) = BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 :
        Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 :
        ℕ))) ∧ (ProperBandQuadruple r → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (r (0 : Fin (4 : ℕ)))
        (r j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) ∧
        BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r
        j.succ) (r (0 : Fin (4 : ℕ))))) → ((BandVectors.2 (r 2) (r 0) = ya + I * wa) →
        (BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa)))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r hr I wa ya laws ha
  have h := (laws.2.2.2.2 hr 1).2
  simpa [I, ha] using h

private theorem hvp :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → (
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (r 1 = p 0) → ((r 2 = p 2) → (
    let I : GaussianInt := ⟨0, 1⟩
    let y := BandVectors.1 (r 2) (r 1)
    BandVectors.1 (p 0) (p 2) = I * y))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hp r hA hB I y
  have h := VectorRecursionLaws p hp.1
  have hf := (h.2.2.2.2 hp 1).1
  simpa [I, y, r, hA, hB] using hf

private theorem hap :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → (
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (r 1 = p 0) → ((r 2 = p 2) → (
    let I : GaussianInt := ⟨0, 1⟩
    let ya := BandVectors.2 (r 2) (r 1)
    BandVectors.2 (p 0) (p 2) = -I * ya))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p hp r hA hB I ya
  have h := VectorRecursionLaws p hp.1
  have hf := (h.2.2.2.2 hp 1).2
  simpa [I, ya, r, hA, hB] using hf

private theorem vflip :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (ProperBandQuadruple r) → (
    let I : GaussianInt := ⟨0, 1⟩
    let w := BandVectors.1 (r 3) (r 2)
    let y := BandVectors.1 (r 2) (r 1)
    (BandVectors.1 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) + BandVectors.1 (r (1 : Fin (4 :
        ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) =
        (0 : GaussianInt) ∧ BandVectors.2 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
        BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.2 (r (2 : Fin (4
        : ℕ))) (r (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (r (1 : Fin (4 : ℕ))) (r
        (0 : Fin (4 : ℕ))) = BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) - ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) ∧ BandVectors.2
        (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) = BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 :
        Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 :
        ℕ))) ∧ (ProperBandQuadruple r → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (r (0 : Fin (4 : ℕ)))
        (r j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) ∧
        BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r
        j.succ) (r (0 : Fin (4 : ℕ))))) → ((BandVectors.1 (r 2) (r 0) = y - I * w) →
        (BandVectors.1 (r 0) (r 2) = I * (y - I * w)))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r hr I w y laws hv
  have h := (laws.2.2.2.2 hr 1).1
  simpa [I, hv] using h

private theorem aflip :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (ProperBandQuadruple r) → (
    let I : GaussianInt := ⟨0, 1⟩
    let wa := BandVectors.2 (r 3) (r 2)
    let ya := BandVectors.2 (r 2) (r 1)
    (BandVectors.1 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) + BandVectors.1 (r (1 : Fin (4 :
        ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) =
        (0 : GaussianInt) ∧ BandVectors.2 (r (3 : Fin (4 : ℕ))) (r (2 : Fin (4 : ℕ))) +
        BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) + BandVectors.2 (r (2 : Fin (4
        : ℕ))) (r (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (r (1 : Fin (4 : ℕ))) (r
        (0 : Fin (4 : ℕ))) = BandVectors.1 (r (1 : Fin (4 : ℕ))) (r (3 : Fin (4 : ℕ))) - ⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.1 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 : ℕ))) ∧ BandVectors.2
        (r (1 : Fin (4 : ℕ))) (r (0 : Fin (4 : ℕ))) = BandVectors.2 (r (1 : Fin (4 : ℕ))) (r (3 :
        Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r (2 : Fin (4 : ℕ))) (r (1 : Fin (4 :
        ℕ))) ∧ (ProperBandQuadruple r → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (r (0 : Fin (4 : ℕ)))
        (r j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) ∧
        BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (r
        j.succ) (r (0 : Fin (4 : ℕ))))) → ((BandVectors.2 (r 2) (r 0) = ya + I * wa) →
        (BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa)))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r hr I wa ya laws ha
  have h := (laws.2.2.2.2 hr 1).2
  simpa [I, ha] using h

private theorem halfPoint_sub :
    let halfPoint : GaussianInt → ℝ × ℝ :=
      fun z => (1 / 2 : ℝ) • GaussianRealPoint z
    ∀ (u : GaussianInt), ∀ (v : GaussianInt), halfPoint u - halfPoint v = halfPoint (u - v) := by
  classical
  intro halfPoint u v
  apply Prod.ext <;> simp [halfPoint, GaussianRealPoint] <;> ring

private theorem hcentK :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let w := BandVectors.1 (r 3) (r 2)
    TileCentroid (D.tiles a true) - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (w - I
        * w) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a r I w
  have h := (D.occurrences a true).2.2
  simp only [↓reduceIte, one_div, Fin.isValue, one_smul, Matrix.cons_val, Int.reduceNeg, w, r,
      I] at h ⊢
  rw [h]
  ext <;> simp [GaussianRealPoint, Zsqrtd.re_mul, Zsqrtd.im_mul]

private theorem hodoK :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (r 1 = p 0) → (TileOdometer (p 0) (D.tiles a true) (D.functions a true)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p r hA
  have hqa : F.q a.succ = p 0 := by simpa [r] using hA
  rw [← hqa]
  exact D.odometers a true

private theorem hcentRnew :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (r 1 = p 0) → ((r 2 = p 2) → (
    let I : GaussianInt := ⟨0, 1⟩
    let y := BandVectors.1 (r 2) (r 1)
    (BandVectors.1 (p 0) (p 2) = I * y) → ((TileCentroid Rplus - TileCentroid (D.tiles a true) =
        (1 / 2 : ℝ) • GaussianRealPoint (y + I * y)) → (TileCentroid Rplus - TileCentroid
        (D.tiles a true) = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (p 2) (p 0) +
        BandVectors.1 (p 0) (p 2)))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p r hA hB I y hvp hcentRK
  have h := hcentRK
  rw [← hvp] at h
  simpa [y, r, hA, hB] using h

private theorem hqapos :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (r 1 = p 0) → ((0 < (p 0).1) → (0 < (F.q a.succ).1)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r hA hposA
  have hqa : F.q a.succ = p 0 := by simpa [r] using hA
  rw [hqa]
  exact hposA

private theorem hplusDelta :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wa := BandVectors.2 (r 3) (r 2)
    let ya := BandVectors.2 (r 2) (r 1)
    (ya - -I * wa + -I * (ya - -I * wa) - (wa - -I * wa) = ya + -I * ya) → ((ya + I * wa + (-I) *
        (ya + I * wa)) - (wa - (-I) * wa) = ya + (-I) * ya) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I wa ya aFourth
  convert aFourth using 1; ring

private theorem hya :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let ya := BandVectors.2 (r 2) (r 1)
    (F.q a.succ = p 0) → ((F.q ((a + 1).succ) = p 2) → (BandVectors.2 (p 2) (p 0) = ya)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r ya hAcoord hBcoord
  dsimp [ya, r]
  rw [hBcoord, hAcoord]

private theorem hplusVec :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let ya := BandVectors.2 (r 2) (r 1)
    (BandVectors.2 (p 0) (p 2) = -I * ya) → ((BandVectors.2 (p 2) (p 0) = ya) → (BandVectors.2 (p
        2) (p 0) + BandVectors.2 (p 0) (p 2) = ya + (-I) * ya)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r I ya hap hya
  rw [hya, hap]

private theorem hminusVec :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let ya := BandVectors.2 (r 2) (r 1)
    (BandVectors.2 (p 0) (p 2) = -I * ya) → ((BandVectors.2 (p 2) (p 0) = ya) → (BandVectors.2 (p
        2) (p 0) - BandVectors.2 (p 0) (p 2) = ya - (-I) * ya)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r I ya hap hya
  rw [hya, hap]

private theorem hplusSlopeP :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let ya := BandVectors.2 (r 2) (r 1)
    ∀ (sA : ℝ × ℝ), (F.plusSlope - sA = (1 / 2 : ℝ) • GaussianRealPoint (ya + (-I) * ya)) →
        ((BandVectors.2 (p 2) (p 0) + BandVectors.2 (p 0) (p 2) = ya + (-I) * ya) → (F.plusSlope
        - sA = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (p 2) (p 0) + BandVectors.2 (p 0)
        (p 2)))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r I ya sA hplusSlope hplusVec
  let halfPoint : GaussianInt → ℝ × ℝ :=
    fun z => (1 / 2 : ℝ) • GaussianRealPoint z
  calc
    _ = halfPoint (ya + (-I) * ya) := by
      exact hplusSlope
    _ = _ := congrArg halfPoint hplusVec.symm

private theorem hminusSlopeP :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let ya := BandVectors.2 (r 2) (r 1)
    ∀ (sJ : ℝ × ℝ), ∀ (sA : ℝ × ℝ), (sJ - sA = (1 / 2 : ℝ) • GaussianRealPoint (ya - (-I) * ya))
        → ((BandVectors.2 (p 2) (p 0) - BandVectors.2 (p 0) (p 2) = ya - (-I) * ya) → (sJ - sA =
        (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (p 2) (p 0) - BandVectors.2 (p 0) (p 2))))
            := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r I ya sJ sA hminusSlope hminusVec
  let halfPoint : GaussianInt → ℝ × ℝ :=
    fun z => (1 / 2 : ℝ) • GaussianRealPoint z
  calc
    _ = halfPoint (ya - (-I) * ya) := by
      exact hminusSlope
    _ = _ := congrArg halfPoint hminusVec.symm

private theorem hyv :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let y := BandVectors.1 (r 2) (r 1)
    (F.q a.succ = p 0) → ((F.q ((a + 1).succ) = p 2) → (BandVectors.1 (p 2) (p 0) = y)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r y hAcoord hBcoord
  dsimp [y, r]
  rw [hBcoord, hAcoord]

private theorem hminusCentVec :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let y := BandVectors.1 (r 2) (r 1)
    (BandVectors.1 (p 0) (p 2) = I * y) → ((BandVectors.1 (p 2) (p 0) = y) → (BandVectors.1 (p 2)
        (p 0) - BandVectors.1 (p 0) (p 2) = y - I * y)) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r I y hvp hyv
  rw [hyv, hvp]

private theorem hminusCentP :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates), ∀ (J :
        ProtoTile),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let y := BandVectors.1 (r 2) (r 1)
    (TileCentroid J - TileCentroid (D.tiles a true) = (1 / 2 : ℝ) • GaussianRealPoint (y - I *
        y)) → ((BandVectors.1 (p 2) (p 0) - BandVectors.1 (p 0) (p 2) = y - I * y) →
        (TileCentroid J - TileCentroid (D.tiles a true) = (1 / 2 : ℝ) • GaussianRealPoint
        (BandVectors.1 (p 2) (p 0) - BandVectors.1 (p 0) (p 2)))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a p J r I y hcentJK hminusCentVec
  let halfPoint : GaussianInt → ℝ × ℝ :=
    fun z => (1 / 2 : ℝ) • GaussianRealPoint z
  calc
    _ = halfPoint (y - I * y) := by
      exact hcentJK
    _ = _ := congrArg halfPoint hminusCentVec.symm

end AFrameBDetails

theorem P4536T1AFrameB
    {C : BandCircle} {orientation : Bool} {base Rminus Rplus : ProtoTile}
    {hminus hplus : PartialOdometer}
    (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus)
    (D : P4458T1RestrictionFamily F)
    (a : Fin 3) (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
    (hstep : ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] =
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3])
    (hslot : F.slot = a + 1)
    (hchart : C.1.1.1 = 1 → UnitOccurrenceOrientation p 1 orientation)
    (J : ProtoTile) (hfamily : J ∈ RegularTileFamily base (TilingLattice C))
    (hodo : TileOdometer C.1.1 J (D.functions F.slot false))
    (hcent : TileCentroid J = TileCentroid (D.tiles F.slot false)) :
    ∃ G : P4458T1BoundaryFrame C orientation base J Rplus
        (D.functions F.slot false) hplus,
      G.q = p ∧ G.slot = 1 ∧ G.outer.1.1 = F.q a.succ ∧
      G.tile = D.tiles a true ∧ G.odometer = D.functions a true := by
-- BODY
  exact (show ∃ G : P4458T1BoundaryFrame C orientation base J Rplus
        (D.functions F.slot false) hplus,
      G.q = p ∧ G.slot = 1 ∧ G.outer.1.1 = F.q a.succ ∧
        G.tile = D.tiles a true ∧ G.odometer = D.functions a true from by
      classical
      let r : Fin 4 → CircleCoordinates :=
        ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
      have hr : ProperBandQuadruple r := AFrameBProof.hr C orientation base Rminus Rplus hminus
          hplus F a
      have hcoord : r 0 = (2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
            2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2) := AFrameBDetails.hcoord C
                orientation base Rminus Rplus hminus hplus F a p hstep
      have hA : r 1 = p 0 := AFrameBDetails.hA C orientation base Rminus Rplus hminus hplus F a p
          hstep
      have hB : r 2 = p 2 := AFrameBDetails.hB C orientation base Rminus Rplus hminus hplus F a p
          hstep
      have hE : r 3 = p 3 := AFrameBDetails.hE C orientation base Rminus Rplus hminus hplus F a p
          hstep
      have hparent : r 2 = C.1.1 := AFrameBDetails.hparent C orientation base Rminus Rplus hminus
          hplus F a hslot
      have hpB : p 2 = C.1.1 := hB.symm.trans hparent
      have hposA : 0 < (p 0).1 := (ProperBandCurvatureStructure p hp).1
      have hposB : 0 < (p 2).1 := by rw [hpB]; exact C.2
      let I : GaussianInt := ⟨0, 1⟩
      let w := BandVectors.1 (r 3) (r 2)
      let x := BandVectors.1 (r 1) (r 3)
      let y := BandVectors.1 (r 2) (r 1)
      let wa := BandVectors.2 (r 3) (r 2)
      let xa := BandVectors.2 (r 1) (r 3)
      let ya := BandVectors.2 (r 2) (r 1)
      have laws := VectorRecursionLaws r hr.1
      have hrot : SemiProperQuadruple ![r 0, r 2, r 3, r 1] := by
        exact SemiProperQuadruple.rotate hr.1
      have rlaws := VectorRecursionLaws (![r 0, r 2, r 3, r 1]) hrot
      have hv : BandVectors.1 (r 2) (r 0) = y - I * w := by
        simpa [I, w, x, y, r] using rlaws.2.2.1
      have ha : BandVectors.2 (r 2) (r 0) = ya + I * wa := by
        simpa [I, wa, xa, ya, r] using rlaws.2.2.2.1
      have hflipv : BandVectors.1 (r 0) (r 2) = I * (y - I * w) := AFrameBDetails.hflipv C
          orientation base Rminus Rplus hminus hplus F a hr laws hv
      have hflipa : BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa) := AFrameBDetails.hflipa C
          orientation base Rminus Rplus hminus hplus F a hr laws ha
      have hvp : BandVectors.1 (p 0) (p 2) = I * y := AFrameBDetails.hvp C orientation base
          Rminus Rplus hminus hplus F a p hp hA hB
      have hap : BandVectors.2 (p 0) (p 2) = -I * ya := AFrameBDetails.hap C orientation base
          Rminus Rplus hminus hplus F a p hp hA hB
      have vAlg := P4536T1EndpointAlgebra I w x y (by decide +kernel) laws.1
      have aAlg := P4536T1EndpointAlgebra (-I) wa xa ya (by decide +kernel) laws.2.1
      have aThird := aAlg.2.2.1
      have aFourth := aAlg.2.2.2.1
      have vflip : BandVectors.1 (r 0) (r 2) = I * (y - I * w) := AFrameBDetails.vflip C
          orientation base Rminus Rplus hminus hplus F a hr laws hv
      have aflip : BandVectors.2 (r 0) (r 2) = -I * (ya + I * wa) := AFrameBDetails.aflip C
          orientation base Rminus Rplus hminus hplus F a hr laws ha
      let halfPoint : GaussianInt → ℝ × ℝ :=
        fun z => (1 / 2 : ℝ) • GaussianRealPoint z
      have halfPoint_sub (u v : GaussianInt) :
          halfPoint u - halfPoint v = halfPoint (u - v) := AFrameBDetails.halfPoint_sub u v
      have hcentJ : TileCentroid J - TileCentroid F.tile =
          (1 / 2 : ℝ) • GaussianRealPoint (-(x - I * x)) := AFrameBProof.hcentJ C orientation
              base Rminus Rplus hminus hplus F D a p hstep hslot J hcent hr hcoord hA hB hE
              hparent laws hrot rlaws hv ha hflipv hflipa hvp hap vAlg aAlg aThird aFourth vflip
              aflip
      have hcentK : TileCentroid (D.tiles a true) - TileCentroid F.tile =
          (1 / 2 : ℝ) • GaussianRealPoint (w - I * w) := AFrameBDetails.hcentK C orientation base
              Rminus Rplus hminus hplus F D a
      have hcentR : TileCentroid Rplus - TileCentroid F.tile =
          (1 / 2 : ℝ) • GaussianRealPoint ((y - I * w) + I * (y - I * w)) := AFrameBProof.hcentR
              C orientation base Rminus Rplus hminus hplus F D a p hstep hslot J hr hcoord hA hB
              hE hparent laws hrot rlaws hv ha hflipv hflipa hvp hap vAlg aAlg aThird aFourth
              vflip aflip hcentJ hcentK
      have hcentJK : TileCentroid J - TileCentroid (D.tiles a true) =
          (1 / 2 : ℝ) • GaussianRealPoint (y - I * y) := AFrameBProof.hcentJK C orientation base
              Rminus Rplus hminus hplus F D a J vAlg halfPoint_sub hcentJ hcentK
      have hcentRK : TileCentroid Rplus - TileCentroid (D.tiles a true) =
          (1 / 2 : ℝ) • GaussianRealPoint (y + I * y) := AFrameBProof.hcentRK C orientation base
              Rminus Rplus hminus hplus F D a vAlg halfPoint_sub hcentK hcentR
      let houter : BandCircle :=
        ⟨⟨p 0, ⟨Or.inl hposA, ⟨p, hp.1, ⟨0, rfl⟩⟩⟩⟩, hposA⟩
      have hodoK : TileOdometer (p 0) (D.tiles a true) (D.functions a true) :=
          AFrameBDetails.hodoK C orientation base Rminus Rplus hminus hplus F D a p hA
      have hbandK : BandPrototile (p 0) (D.tiles a true) :=
        TileOdometerBandPrototile _ _ _ hodoK
      have hparentNew : p 2 = C.1.1 := hpB
      have hAcoord : F.q a.succ = p 0 := by simpa [r] using hA
      have hBcoord : F.q ((a + 1).succ) = p 2 := by simpa [r] using hB
      have hfamilyR : Rplus ∈ RegularTileFamily base (TilingLattice C) := by
        exact F.plus_family
      have hfamilyJ : J ∈ RegularTileFamily base (TilingLattice C) := by
        exact hfamily
      have hcentRnew : TileCentroid Rplus - TileCentroid (D.tiles a true) =
          (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (p 2) (p 0) + BandVectors.1 (p 0) (p 2)) := AFrameBDetails.hcentRnew C
                orientation base Rminus Rplus hminus hplus F D a p hA hB hvp hcentRK
      have hslotpos : 0 < (F.q F.slot.succ).1 := F.parent ▸ C.2
      rcases D.slopes F.slot false with hzJ | ⟨rootJ, sJ, hrootJ, hsJ, hreJ, himJ⟩
      · have : (F.q F.slot.succ).1 = 0 := hzJ
        omega
      have hrootJeq : rootJ = F.outerSlope :=
        Option.some.inj (hrootJ.symm.trans F.slope_outer)
      subst rootJ
      have hqapos : 0 < (F.q a.succ).1 := AFrameBDetails.hqapos C orientation base Rminus Rplus
          hminus hplus F a p hA hposA
      rcases D.slopes a true with hzA | ⟨rootA, sA, hrootA, hsA, hreA, himA⟩
      · have : (F.q a.succ).1 = 0 := hzA
        omega
      have hrootAeq : rootA = F.outerSlope :=
        Option.some.inj (hrootA.symm.trans F.slope_outer)
      subst rootA
      have hslopeJ : sJ - F.outerSlope =
          (1 / 2 : ℝ) • GaussianRealPoint (-(xa - (-I) * xa)) := AFrameBProof.hslopeJ C
              orientation base Rminus Rplus hminus hplus F D a p hstep hslot J hr hcoord hA hB hE
              hparent laws hrot rlaws hv ha hflipv hflipa hvp hap vAlg aAlg aThird aFourth vflip
              aflip hcentJ hcentK hcentR hcentJK hcentRK hodoK hbandK hAcoord hBcoord hcentRnew
              sJ hreJ himJ hqapos sA hsA hreA himA
      have hslopeA : sA - F.outerSlope =
          (1 / 2 : ℝ) • GaussianRealPoint (wa - (-I) * wa) := AFrameBProof.hslopeA C orientation
              base Rminus Rplus hminus hplus F D a p hstep hslot J hr hcoord hA hB hE hparent
              laws hrot rlaws hv ha hflipv hflipa hvp hap vAlg aAlg aThird aFourth vflip aflip
              hcentJ hcentK hcentR hcentJK hcentRK hodoK hbandK hAcoord hBcoord hcentRnew sJ
              hqapos sA hsA hreA himA hslopeJ
      have hminusSlope : sJ - sA =
          (1 / 2 : ℝ) • GaussianRealPoint (ya - (-I) * ya) := AFrameBProof.hminusSlope C
              orientation base Rminus Rplus hminus hplus F a aThird sJ sA hslopeJ hslopeA
      have hya : BandVectors.2 (p 2) (p 0) = ya := AFrameBDetails.hya C orientation base Rminus
          Rplus hminus hplus F a p hAcoord hBcoord
      let G : P4458T1BoundaryFrame C orientation base J Rplus
            (D.functions F.slot false) hplus := {
          outer := houter
          q := p
          proper := hp
          slot := 1
          child := by rfl
          parent := hpB
          tile := D.tiles a true
          odometer := D.functions a true
          outer_odo := hodoK
          minus_odo := hodo
          plus_odo := F.plus_odo
          outer_band := hbandK
          base_band := F.base_band
          minus_family := hfamilyJ
          plus_family := hfamilyR
          chart := hchart
          minus_centroid := (AFrameBDetails.hminusCentP C orientation base Rminus Rplus hminus
              hplus F D a p J hcentJK (AFrameBDetails.hminusCentVec C orientation base Rminus
              Rplus hminus hplus F a p hvp (AFrameBDetails.hyv C orientation base Rminus Rplus
              hminus hplus F a p hAcoord hBcoord)))
          plus_centroid := hcentRnew
          outerSlope := sA
          minusSlope := sJ
          plusSlope := F.plusSlope
          slope_outer := hsA
          slope_minus := hsJ
          slope_plus := F.slope_plus
          minus_difference := (AFrameBDetails.hminusSlopeP C orientation base Rminus Rplus hminus
              hplus F a p sJ sA hminusSlope (AFrameBDetails.hminusVec C orientation base Rminus
              Rplus hminus hplus F a p hap hya))
          plus_difference := by
            calc
              _ = F.plusSlope - sA := rfl
              _ = _ := (AFrameBDetails.hplusSlopeP C orientation base Rminus Rplus hminus hplus F
                  a p sA (AFrameBProof.hplusSlope C orientation base Rminus Rplus hminus hplus F
                  a halfPoint_sub sA hslopeA (AFrameBProof.hplusSlopeRoot C orientation base
                  Rminus Rplus hminus hplus F D a p hstep hslot J hr hcoord hA hB hE hparent laws
                  hrot rlaws hv ha hflipv hflipa hvp hap vAlg aAlg aThird aFourth vflip aflip
                  hcentJ hcentK hcentR hcentJK hcentRK hodoK hbandK hAcoord hBcoord hcentRnew sJ
                  hqapos sA hsA hreA himA hslopeJ hslopeA hminusSlope) (AFrameBDetails.hplusDelta
                  C orientation base Rminus Rplus hminus hplus F a aFourth))
                  (AFrameBDetails.hplusVec C orientation base Rminus Rplus hminus hplus F a p hap
                  hya))
      }
      refine ⟨G, ?_⟩
      constructor
      · simp [G]
      constructor
      · simp [G]
      constructor
      · simpa [G, houter] using hAcoord.symm
      constructor
      · simp [G]
      · simp [G])

end ApollonianSuperharmonic

end
