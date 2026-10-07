/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile0Q0
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile0Q1
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile0Q2
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile1Q0
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile1Q1
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile1Q2
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile2Q0
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile2Q1
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile2Q2
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile3Q0
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile3Q1
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile3Q2
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile4Q0
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile4Q1
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile4Q2
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile5Q0
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile5Q1
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile5Q2
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile6Q0
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile6Q1
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile6Q2
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile7Q0
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile7Q1
public import LeanPool.ConwaySoifer.Simplified.Geometry.Profile7Q2
public import LeanPool.ConwaySoifer.Simplified.Geometry.Receiver
import Mathlib.Tactic

/-!
# ProfileWitness

Geometry and verified arithmetic for the Conway–Soifer covering theorem at n = 3.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

@[expose] public section

noncomputable section
namespace ConwaySoifer.Simplified

private theorem profileWitness0 {Q : EquilateralTriangle} {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 10)
    (hq : 0 < Q.side) (n : Fin 3)
    (hw : (1, 1) ∈ Q.carrier)
    (he : (1, (((0 : ℕ) : ℝ) + 1) * s / 4) ∈ Q.carrier)
    (hf : (1 - ((0 : ℕ) : ℝ) * s / 4, 1) ∈ Q.carrier)
    (hp : ((witness s n).2, (witness s n).1) ∈ Q.carrier) : 1 ≤ Q.side := by
  fin_cases n
  · apply profile0q0_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile0q0Point]
      all_goals ring
    · convert hf using 1; norm_num [profile0q0Point]
    · convert hp using 1; norm_num [profile0q0Point, witness]
      all_goals constructor <;> ring
  · apply profile0q1_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile0q1Point]
      all_goals ring
    · convert hf using 1; norm_num [profile0q1Point]
    · convert hp using 1; norm_num [profile0q1Point, witness]
      all_goals constructor <;> ring
  · apply profile0q2_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile0q2Point]
      all_goals ring
    · convert hf using 1; norm_num [profile0q2Point]
    · convert hp using 1; norm_num [profile0q2Point, witness]
      all_goals ring

private theorem profileWitness1 {Q : EquilateralTriangle} {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 10)
    (hq : 0 < Q.side) (n : Fin 3)
    (hw : (1, 1) ∈ Q.carrier)
    (he : (1, (((1 : ℕ) : ℝ) + 1) * s / 4) ∈ Q.carrier)
    (hf : (1 - ((1 : ℕ) : ℝ) * s / 4, 1) ∈ Q.carrier)
    (hp : ((witness s n).2, (witness s n).1) ∈ Q.carrier) : 1 ≤ Q.side := by
  fin_cases n
  · apply profile1q0_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile1q0Point]
      all_goals ring
    · convert hf using 1; norm_num [profile1q0Point]
      all_goals ring
    · convert hp using 1; norm_num [profile1q0Point, witness]
      all_goals constructor <;> ring
  · apply profile1q1_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile1q1Point]
      all_goals ring
    · convert hf using 1; norm_num [profile1q1Point]
      all_goals ring
    · convert hp using 1; norm_num [profile1q1Point, witness]
      all_goals constructor <;> ring
  · apply profile1q2_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile1q2Point]
      all_goals ring
    · convert hf using 1; norm_num [profile1q2Point]
      all_goals ring
    · convert hp using 1; norm_num [profile1q2Point, witness]
      all_goals ring

private theorem profileWitness2 {Q : EquilateralTriangle} {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 10)
    (hq : 0 < Q.side) (n : Fin 3)
    (hw : (1, 1) ∈ Q.carrier)
    (he : (1, (((2 : ℕ) : ℝ) + 1) * s / 4) ∈ Q.carrier)
    (hf : (1 - ((2 : ℕ) : ℝ) * s / 4, 1) ∈ Q.carrier)
    (hp : ((witness s n).2, (witness s n).1) ∈ Q.carrier) : 1 ≤ Q.side := by
  fin_cases n
  · apply profile2q0_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile2q0Point]
      all_goals ring
    · convert hf using 1; norm_num [profile2q0Point]
      all_goals ring
    · convert hp using 1; norm_num [profile2q0Point, witness]
      all_goals constructor <;> ring
  · apply profile2q1_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile2q1Point]
      all_goals ring
    · convert hf using 1; norm_num [profile2q1Point]
      all_goals ring
    · convert hp using 1; norm_num [profile2q1Point, witness]
      all_goals constructor <;> ring
  · apply profile2q2_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile2q2Point]
      all_goals ring
    · convert hf using 1; norm_num [profile2q2Point]
      all_goals ring
    · convert hp using 1; norm_num [profile2q2Point, witness]
      all_goals ring

private theorem profileWitness3 {Q : EquilateralTriangle} {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 10)
    (hq : 0 < Q.side) (n : Fin 3)
    (hw : (1, 1) ∈ Q.carrier)
    (he : (1, (((3 : ℕ) : ℝ) + 1) * s / 4) ∈ Q.carrier)
    (hf : (1 - ((3 : ℕ) : ℝ) * s / 4, 1) ∈ Q.carrier)
    (hp : ((witness s n).2, (witness s n).1) ∈ Q.carrier) : 1 ≤ Q.side := by
  fin_cases n
  · apply profile3q0_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile3q0Point]
    · convert hf using 1; norm_num [profile3q0Point]
      all_goals ring
    · convert hp using 1; norm_num [profile3q0Point, witness]
      all_goals constructor <;> ring
  · apply profile3q1_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile3q1Point]
    · convert hf using 1; norm_num [profile3q1Point]
      all_goals ring
    · convert hp using 1; norm_num [profile3q1Point, witness]
      all_goals constructor <;> ring
  · apply profile3q2_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile3q2Point]
    · convert hf using 1; norm_num [profile3q2Point]
      all_goals ring
    · convert hp using 1; norm_num [profile3q2Point, witness]
      all_goals ring

private theorem profileWitness4 {Q : EquilateralTriangle} {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 10)
    (hq : 0 < Q.side) (n : Fin 3)
    (hw : (1, 1) ∈ Q.carrier)
    (he : (1, (((4 : ℕ) : ℝ) + 1) * s / 4) ∈ Q.carrier)
    (hf : (1 - ((4 : ℕ) : ℝ) * s / 4, 1) ∈ Q.carrier)
    (hp : ((witness s n).2, (witness s n).1) ∈ Q.carrier) : 1 ≤ Q.side := by
  fin_cases n
  · apply profile4q0_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile4q0Point]
      all_goals ring
    · convert hf using 1; norm_num [profile4q0Point]
      all_goals ring
    · convert hp using 1; norm_num [profile4q0Point, witness]
      all_goals constructor <;> ring
  · apply profile4q1_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile4q1Point]
      all_goals ring
    · convert hf using 1; norm_num [profile4q1Point]
      all_goals ring
    · convert hp using 1; norm_num [profile4q1Point, witness]
      all_goals constructor <;> ring
  · apply profile4q2_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile4q2Point]
      all_goals ring
    · convert hf using 1; norm_num [profile4q2Point]
      all_goals ring
    · convert hp using 1; norm_num [profile4q2Point, witness]
      all_goals ring

private theorem profileWitness5 {Q : EquilateralTriangle} {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 10)
    (hq : 0 < Q.side) (n : Fin 3)
    (hw : (1, 1) ∈ Q.carrier)
    (he : (1, (((5 : ℕ) : ℝ) + 1) * s / 4) ∈ Q.carrier)
    (hf : (1 - ((5 : ℕ) : ℝ) * s / 4, 1) ∈ Q.carrier)
    (hp : ((witness s n).2, (witness s n).1) ∈ Q.carrier) : 1 ≤ Q.side := by
  fin_cases n
  · apply profile5q0_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile5q0Point]
      all_goals ring
    · convert hf using 1; norm_num [profile5q0Point]
      all_goals ring
    · convert hp using 1; norm_num [profile5q0Point, witness]
      all_goals constructor <;> ring
  · apply profile5q1_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile5q1Point]
      all_goals ring
    · convert hf using 1; norm_num [profile5q1Point]
      all_goals ring
    · convert hp using 1; norm_num [profile5q1Point, witness]
      all_goals constructor <;> ring
  · apply profile5q2_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile5q2Point]
      all_goals ring
    · convert hf using 1; norm_num [profile5q2Point]
      all_goals ring
    · convert hp using 1; norm_num [profile5q2Point, witness]
      all_goals ring

private theorem profileWitness6 {Q : EquilateralTriangle} {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 10)
    (hq : 0 < Q.side) (n : Fin 3)
    (hw : (1, 1) ∈ Q.carrier)
    (he : (1, (((6 : ℕ) : ℝ) + 1) * s / 4) ∈ Q.carrier)
    (hf : (1 - ((6 : ℕ) : ℝ) * s / 4, 1) ∈ Q.carrier)
    (hp : ((witness s n).2, (witness s n).1) ∈ Q.carrier) : 1 ≤ Q.side := by
  fin_cases n
  · apply profile6q0_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile6q0Point]
      all_goals ring
    · convert hf using 1; norm_num [profile6q0Point]
      all_goals ring
    · convert hp using 1; norm_num [profile6q0Point, witness]
      all_goals constructor <;> ring
  · apply profile6q1_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile6q1Point]
      all_goals ring
    · convert hf using 1; norm_num [profile6q1Point]
      all_goals ring
    · convert hp using 1; norm_num [profile6q1Point, witness]
      all_goals constructor <;> ring
  · apply profile6q2_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile6q2Point]
      all_goals ring
    · convert hf using 1; norm_num [profile6q2Point]
      all_goals ring
    · convert hp using 1; norm_num [profile6q2Point, witness]
      all_goals ring

private theorem profileWitness7 {Q : EquilateralTriangle} {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 10)
    (hq : 0 < Q.side) (n : Fin 3)
    (hw : (1, 1) ∈ Q.carrier)
    (he : (1, (((7 : ℕ) : ℝ) + 1) * s / 4) ∈ Q.carrier)
    (hf : (1 - ((7 : ℕ) : ℝ) * s / 4, 1) ∈ Q.carrier)
    (hp : ((witness s n).2, (witness s n).1) ∈ Q.carrier) : 1 ≤ Q.side := by
  fin_cases n
  · apply profile7q0_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile7q0Point]
      all_goals ring
    · convert hf using 1; norm_num [profile7q0Point]
      all_goals ring
    · convert hp using 1; norm_num [profile7q0Point, witness]
      all_goals constructor <;> ring
  · apply profile7q1_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile7q1Point]
      all_goals ring
    · convert hf using 1; norm_num [profile7q1Point]
      all_goals ring
    · convert hp using 1; norm_num [profile7q1Point, witness]
      all_goals constructor <;> ring
  · apply profile7q2_obstruction hs0 hs hq
    intro i
    fin_cases i
    · exact hw
    · convert he using 1; norm_num [profile7q2Point]
      all_goals ring
    · convert hf using 1; norm_num [profile7q2Point]
      all_goals ring
    · convert hp using 1; norm_num [profile7q2Point, witness]
      all_goals ring

theorem profile_witness {Q : EquilateralTriangle} {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 10)
    (hq : 0 < Q.side) (k : Fin 8) (n : Fin 3)
    (hw : (1, 1) ∈ Q.carrier)
    (he : (1, ((k.val : ℝ) + 1) * s / 4) ∈ Q.carrier)
    (hf : (1 - (k.val : ℝ) * s / 4, 1) ∈ Q.carrier)
    (hp : ((witness s n).2, (witness s n).1) ∈ Q.carrier) : 1 ≤ Q.side := by
  fin_cases k
  · exact profileWitness0 hs0 hs hq n hw he hf hp
  · exact profileWitness1 hs0 hs hq n hw he hf hp
  · exact profileWitness2 hs0 hs hq n hw he hf hp
  · exact profileWitness3 hs0 hs hq n hw he hf hp
  · exact profileWitness4 hs0 hs hq n hw he hf hp
  · exact profileWitness5 hs0 hs hq n hw he hf hp
  · exact profileWitness6 hs0 hs hq n hw he hf hp
  · exact profileWitness7 hs0 hs hq n hw he hf hp

end ConwaySoifer.Simplified
