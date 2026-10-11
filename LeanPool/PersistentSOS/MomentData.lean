/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

/-
Adapted from JD-Jones-ASES/persistent-sos, commit
d432ff9a67594cc0fa7a7af1913320b46d2a86db.
Original MIT notice (retained under the permission to sublicense):

MIT License

Copyright (c) 2026 JD Jones

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

module

public import LeanPool.PersistentSOS.MomentGeneral
public import LeanPool.PersistentSOS.MomentBlockFull0
public import LeanPool.PersistentSOS.MomentBlock1
public import LeanPool.PersistentSOS.MomentBlock2
public import LeanPool.PersistentSOS.MomentBlock3
public import LeanPool.PersistentSOS.MomentBlock4
public import LeanPool.PersistentSOS.MomentBlock5
public import LeanPool.PersistentSOS.MomentBlock6
public import LeanPool.PersistentSOS.MomentBlock7
public import Mathlib.Tactic.FinCases

/-!
# Explicit rational moment data

Every monomial occurrence uses one base-five exponent key. All degree-four
moments are derived from the retained rational certificate. The finite
Gram identities and coverage are proved below by kernel reduction.
-/


@[expose] public section

namespace PersistentSOS


/-- Integer numerator table; unspecified keys have value zero. -/
def momentNumerator (k : ℕ) : ℤ :=
  if k < 19612500 then
    if k < 109376 then
      if k < 15876 then
        if k < 3126 then
          if k < 250 then
            if k < 12 then
              if k < 3 then
                if k < 1 then
                  if k = 0 then (1000000000) else 0
                else
                  if k < 2 then
                    if k = 1 then (423308963) else 0
                  else
                    if k = 2 then (298818064) else 0
              else
                if k < 10 then
                  if k < 4 then
                    if k = 3 then (141743481) else 0
                  else
                    if k = 4 then (95993371) else 0
                else
                  if k < 11 then
                    if k = 10 then (148973087) else 0
                  else
                    if k = 11 then (79751621) else 0
            else
              if k < 51 then
                if k < 20 then
                  if k = 12 then (45340304) else 0
                else
                  if k < 50 then
                    if k = 20 then (65363241) else 0
                  else
                    if k = 50 then (162381159) else 0
              else
                if k < 60 then
                  if k < 52 then
                    if k = 51 then (86495040) else 0
                  else
                    if k = 52 then (48848306) else 0
                else
                  if k < 100 then
                    if k = 60 then (6925782) else 0
                  else
                    if k = 100 then (72654288) else 0
          else
            if k < 1250 then
              if k < 260 then
                if k < 251 then
                  if k = 250 then (162381048) else 0
                else
                  if k < 252 then
                    if k = 251 then (86494935) else 0
                  else
                    if k = 252 then (48848296) else 0
              else
                if k < 500 then
                  if k < 300 then
                    if k = 260 then (6925775) else 0
                  else
                    if k = 300 then (7390663) else 0
                else
                  if k < 780 then
                    if k = 500 then (72654222) else 0
                  else
                    if k = 780 then (9655915) else 0
            else
              if k < 1300 then
                if k < 1252 then
                  if k < 1251 then
                    if k = 1250 then (76574425) else 0
                  else
                    if k = 1251 then (39889758) else 0
                else
                  if k < 1260 then
                    if k = 1252 then (22979581) else 0
                  else
                    if k = 1260 then (12788775) else 0
              else
                if k < 2500 then
                  if k < 1500 then
                    if k = 1300 then (13722116) else 0
                  else
                    if k = 1500 then (13722105) else 0
                else
                  if k < 3125 then
                    if k = 2500 then (6719268) else 0
                  else
                    if k = 3125 then (71951457) else 0
        else
          if k < 6300 then
            if k < 3375 then
              if k < 3135 then
                if k < 3127 then
                  if k = 3126 then (28193221) else 0
                else
                  if k < 3128 then
                    if k = 3127 then (20333252) else 0
                  else
                    if k = 3128 then (9365790) else 0
              else
                if k < 3175 then
                  if k < 3136 then
                    if k = 3135 then (27438237) else 0
                  else
                    if k = 3136 then (14265654) else 0
                else
                  if k < 3176 then
                    if k = 3175 then (3349614) else 0
                  else
                    if k = 3176 then (1411787) else 0
            else
              if k < 6250 then
                if k < 4375 then
                  if k < 3376 then
                    if k = 3375 then (3349612) else 0
                  else
                    if k = 3376 then (1411790) else 0
                else
                  if k < 4376 then
                    if k = 4375 then (5506403) else 0
                  else
                    if k = 4376 then (2769171) else 0
              else
                if k < 6252 then
                  if k < 6251 then
                    if k = 6250 then (23640856) else 0
                  else
                    if k = 6251 then (-9137) else 0
                else
                  if k < 6260 then
                    if k = 6252 then (6095189) else 0
                  else
                    if k = 6260 then (6365418) else 0
          else
            if k < 15626 then
              if k < 9375 then
                if k < 6500 then
                  if k = 6300 then (315848) else 0
                else
                  if k < 7500 then
                    if k = 6500 then (315841) else 0
                  else
                    if k = 7500 then (635359) else 0
              else
                if k < 12500 then
                  if k < 9376 then
                    if k = 9375 then (7589636) else 0
                  else
                    if k = 9376 then (-1081254) else 0
                else
                  if k < 15625 then
                    if k = 12500 then (4795194) else 0
                  else
                    if k = 15625 then (76482650) else 0
            else
              if k < 15636 then
                if k < 15628 then
                  if k < 15627 then
                    if k = 15626 then (31705948) else 0
                  else
                    if k = 15627 then (21494722) else 0
                else
                  if k < 15635 then
                    if k = 15628 then (10300379) else 0
                  else
                    if k = 15635 then (3349856) else 0
              else
                if k < 15676 then
                  if k < 15675 then
                    if k = 15636 then (1432129) else 0
                  else
                    if k = 15675 then (30621436) else 0
                else
                  if k < 15875 then
                    if k = 15676 then (15833908) else 0
                  else
                    if k = 15875 then (3504174) else 0
      else
        if k < 78128 then
          if k < 31252 then
            if k < 18800 then
              if k < 18750 then
                if k < 16875 then
                  if k = 15876 then (1503645) else 0
                else
                  if k < 16876 then
                    if k = 16875 then (5975451) else 0
                  else
                    if k = 16876 then (2933691) else 0
              else
                if k < 18752 then
                  if k < 18751 then
                    if k = 18750 then (-826062) else 0
                  else
                    if k = 18751 then (1864327) else 0
                else
                  if k < 18760 then
                    if k = 18752 then (-273910) else 0
                  else
                    if k = 18760 then (202667) else 0
            else
              if k < 21876 then
                if k < 20000 then
                  if k < 19000 then
                    if k = 18800 then (196997) else 0
                  else
                    if k = 19000 then (310741) else 0
                else
                  if k < 21875 then
                    if k = 20000 then (323085) else 0
                  else
                    if k = 21875 then (-681088) else 0
              else
                if k < 31250 then
                  if k < 25000 then
                    if k = 21876 then (457322) else 0
                  else
                    if k = 25000 then (-1025445) else 0
                else
                  if k < 31251 then
                    if k = 31250 then (25184767) else 0
                  else
                    if k = 31251 then (591274) else 0
          else
            if k < 37500 then
              if k < 31500 then
                if k < 31260 then
                  if k = 31252 then (6477974) else 0
                else
                  if k < 31300 then
                    if k = 31260 then (307820) else 0
                  else
                    if k = 31300 then (7147237) else 0
              else
                if k < 34375 then
                  if k < 32500 then
                    if k = 31500 then (310382) else 0
                  else
                    if k = 32500 then (780189) else 0
                else
                  if k < 34376 then
                    if k = 34375 then (-809987) else 0
                  else
                    if k = 34376 then (519327) else 0
            else
              if k < 62500 then
                if k < 46876 then
                  if k < 46875 then
                    if k = 37500 then (1321273) else 0
                  else
                    if k = 46875 then (7109900) else 0
                else
                  if k < 50000 then
                    if k = 46876 then (-486932) else 0
                  else
                    if k = 50000 then (-1027707) else 0
              else
                if k < 78126 then
                  if k < 78125 then
                    if k = 62500 then (4647223) else 0
                  else
                    if k = 78125 then (76482117) else 0
                else
                  if k < 78127 then
                    if k = 78126 then (31706168) else 0
                  else
                    if k = 78127 then (21494568) else 0
        else
          if k < 82500 then
            if k < 79375 then
              if k < 78175 then
                if k < 78135 then
                  if k = 78128 then (10300417) else 0
                else
                  if k < 78136 then
                    if k = 78135 then (3349854) else 0
                  else
                    if k = 78136 then (1432127) else 0
              else
                if k < 78375 then
                  if k < 78176 then
                    if k = 78175 then (3504174) else 0
                  else
                    if k = 78176 then (1503644) else 0
                else
                  if k < 78376 then
                    if k = 78375 then (30621436) else 0
                  else
                    if k = 78376 then (15833900) else 0
            else
              if k < 81252 then
                if k < 81250 then
                  if k < 79376 then
                    if k = 79375 then (5975450) else 0
                  else
                    if k = 79376 then (2933688) else 0
                else
                  if k < 81251 then
                    if k = 81250 then (-826189) else 0
                  else
                    if k = 81251 then (1864389) else 0
              else
                if k < 81300 then
                  if k < 81260 then
                    if k = 81252 then (-273940) else 0
                  else
                    if k = 81260 then (202668) else 0
                else
                  if k < 81500 then
                    if k = 81300 then (310742) else 0
                  else
                    if k = 81500 then (196996) else 0
          else
            if k < 93760 then
              if k < 87500 then
                if k < 84375 then
                  if k = 82500 then (323085) else 0
                else
                  if k < 84376 then
                    if k = 84375 then (-681283) else 0
                  else
                    if k = 84376 then (457423) else 0
              else
                if k < 93751 then
                  if k < 93750 then
                    if k = 87500 then (-1025493) else 0
                  else
                    if k = 93750 then (-1528158) else 0
                else
                  if k < 93752 then
                    if k = 93751 then (2284387) else 0
                  else
                    if k = 93752 then (-467041) else 0
            else
              if k < 96875 then
                if k < 94000 then
                  if k < 93800 then
                    if k = 93760 then (305587) else 0
                  else
                    if k = 93800 then (236820) else 0
                else
                  if k < 95000 then
                    if k = 94000 then (236820) else 0
                  else
                    if k = 95000 then (321057) else 0
              else
                if k < 100000 then
                  if k < 96876 then
                    if k = 96875 then (957561) else 0
                  else
                    if k = 96876 then (-320360) else 0
                else
                  if k < 109375 then
                    if k = 100000 then (113560) else 0
                  else
                    if k = 109375 then (-612941) else 0
    else
      if k < 2031380 then
        if k < 468780 then
          if k < 175000 then
            if k < 156300 then
              if k < 156250 then
                if k < 112500 then
                  if k = 109376 then (437258) else 0
                else
                  if k < 125000 then
                    if k = 112500 then (354183) else 0
                  else
                    if k = 125000 then (-1001747) else 0
              else
                if k < 156252 then
                  if k < 156251 then
                    if k = 156250 then (25184690) else 0
                  else
                    if k = 156251 then (591309) else 0
                else
                  if k < 156260 then
                    if k = 156252 then (6477980) else 0
                  else
                    if k = 156260 then (307807) else 0
            else
              if k < 159376 then
                if k < 157500 then
                  if k < 156500 then
                    if k = 156300 then (310383) else 0
                  else
                    if k = 156500 then (7147227) else 0
                else
                  if k < 159375 then
                    if k = 157500 then (780185) else 0
                  else
                    if k = 159375 then (-809686) else 0
              else
                if k < 171875 then
                  if k < 162500 then
                    if k = 159376 then (519176) else 0
                  else
                    if k = 162500 then (1321273) else 0
                else
                  if k < 171876 then
                    if k = 171875 then (-613231) else 0
                  else
                    if k = 171876 then (437401) else 0
          else
            if k < 390655 then
              if k < 234376 then
                if k < 187500 then
                  if k = 175000 then (354275) else 0
                else
                  if k < 234375 then
                    if k = 187500 then (1519553) else 0
                  else
                    if k = 234375 then (7109654) else 0
              else
                if k < 250000 then
                  if k < 237500 then
                    if k = 234376 then (-486807) else 0
                  else
                    if k = 237500 then (-1027629) else 0
                else
                  if k < 312500 then
                    if k = 250000 then (-1001921) else 0
                  else
                    if k = 312500 then (4647222) else 0
            else
              if k < 393780 then
                if k < 391375 then
                  if k < 390656 then
                    if k = 390655 then (7457187) else 0
                  else
                    if k = 390656 then (3269119) else 0
                else
                  if k < 391376 then
                    if k = 391375 then (10073398) else 0
                  else
                    if k = 391376 then (4832959) else 0
              else
                if k < 406280 then
                  if k < 394500 then
                    if k = 393780 then (608339) else 0
                  else
                    if k = 394500 then (615867) else 0
                else
                  if k < 407000 then
                    if k = 406280 then (604148) else 0
                  else
                    if k = 407000 then (615337) else 0
        else
          if k < 812500 then
            if k < 781500 then
              if k < 781251 then
                if k < 469500 then
                  if k = 468780 then (604133) else 0
                else
                  if k < 781250 then
                    if k = 469500 then (1128523) else 0
                  else
                    if k = 781250 then (21035273) else 0
              else
                if k < 781260 then
                  if k < 781252 then
                    if k = 781251 then (-2998234) else 0
                  else
                    if k = 781252 then (4872560) else 0
                else
                  if k < 781300 then
                    if k = 781260 then (1189529) else 0
                  else
                    if k = 781300 then (1203533) else 0
            else
              if k < 787500 then
                if k < 784375 then
                  if k < 782500 then
                    if k = 781500 then (1779896) else 0
                  else
                    if k = 782500 then (1311683) else 0
                else
                  if k < 784376 then
                    if k = 784375 then (1370160) else 0
                  else
                    if k = 784376 then (-166144) else 0
              else
                if k < 796876 then
                  if k < 796875 then
                    if k = 787500 then (320428) else 0
                  else
                    if k = 796875 then (1065984) else 0
                else
                  if k < 800000 then
                    if k = 796876 then (-18413) else 0
                  else
                    if k = 800000 then (309873) else 0
          else
            if k < 1953255 then
              if k < 862500 then
                if k < 859375 then
                  if k = 812500 then (323490) else 0
                else
                  if k < 859376 then
                    if k = 859375 then (2353567) else 0
                  else
                    if k = 859376 then (-416068) else 0
              else
                if k < 937500 then
                  if k < 875000 then
                    if k = 862500 then (-128470) else 0
                  else
                    if k = 875000 then (-195351) else 0
                else
                  if k < 1562500 then
                    if k = 937500 then (947187) else 0
                  else
                    if k = 1562500 then (2804403) else 0
            else
              if k < 1956380 then
                if k < 1953775 then
                  if k < 1953256 then
                    if k = 1953255 then (7457187) else 0
                  else
                    if k = 1953256 then (3269121) else 0
                else
                  if k < 1953776 then
                    if k = 1953775 then (10073399) else 0
                  else
                    if k = 1953776 then (4832959) else 0
              else
                if k < 1968880 then
                  if k < 1956900 then
                    if k = 1956380 then (608339) else 0
                  else
                    if k = 1956900 then (615867) else 0
                else
                  if k < 1969400 then
                    if k = 1968880 then (604133) else 0
                  else
                    if k = 1969400 then (1128524) else 0
      else
        if k < 9769380 then
          if k < 3921876 then
            if k < 3906260 then
              if k < 2344380 then
                if k < 2031900 then
                  if k = 2031380 then (604148) else 0
                else
                  if k < 2343900 then
                    if k = 2031900 then (615337) else 0
                  else
                    if k = 2343900 then (1201302) else 0
              else
                if k < 3906251 then
                  if k < 3906250 then
                    if k = 2344380 then (1220643) else 0
                  else
                    if k = 3906250 then (21035497) else 0
                else
                  if k < 3906252 then
                    if k = 3906251 then (-2998344) else 0
                  else
                    if k = 3906252 then (4872616) else 0
            else
              if k < 3909375 then
                if k < 3906500 then
                  if k < 3906300 then
                    if k = 3906260 then (1189513) else 0
                  else
                    if k = 3906300 then (1779888) else 0
                else
                  if k < 3907500 then
                    if k = 3906500 then (1203525) else 0
                  else
                    if k = 3907500 then (1311685) else 0
              else
                if k < 3912500 then
                  if k < 3909376 then
                    if k = 3909375 then (1370265) else 0
                  else
                    if k = 3909376 then (-166195) else 0
                else
                  if k < 3921875 then
                    if k = 3912500 then (320439) else 0
                  else
                    if k = 3921875 then (2353878) else 0
          else
            if k < 4062500 then
              if k < 3984375 then
                if k < 3925000 then
                  if k = 3921876 then (-416222) else 0
                else
                  if k < 3937500 then
                    if k = 3925000 then (-128440) else 0
                  else
                    if k = 3937500 then (947241) else 0
              else
                if k < 3987500 then
                  if k < 3984376 then
                    if k = 3984375 then (1066067) else 0
                  else
                    if k = 3984376 then (-18453) else 0
                else
                  if k < 4000000 then
                    if k = 3987500 then (309875) else 0
                  else
                    if k = 4000000 then (-195332) else 0
            else
              if k < 9765776 then
                if k < 7812500 then
                  if k < 4687500 then
                    if k = 4062500 then (323500) else 0
                  else
                    if k = 4687500 then (2595168) else 0
                else
                  if k < 9765775 then
                    if k = 7812500 then (2804463) else 0
                  else
                    if k = 9765775 then (3462345) else 0
              else
                if k < 9766256 then
                  if k < 9766255 then
                    if k = 9765776 then (1400984) else 0
                  else
                    if k = 9766255 then (4143478) else 0
                else
                  if k < 9768900 then
                    if k = 9766256 then (2022744) else 0
                  else
                    if k = 9768900 then (299603) else 0
        else
          if k < 19531251 then
            if k < 11718780 then
              if k < 9843900 then
                if k < 9781400 then
                  if k = 9769380 then (331233) else 0
                else
                  if k < 9781880 then
                    if k = 9781400 then (297238) else 0
                  else
                    if k = 9781880 then (297189) else 0
              else
                if k < 10156380 then
                  if k < 9844380 then
                    if k = 9843900 then (297238) else 0
                  else
                    if k = 9844380 then (297189) else 0
                else
                  if k < 10156900 then
                    if k = 10156380 then (583593) else 0
                  else
                    if k = 10156900 then (591740) else 0
            else
              if k < 12112500 then
                if k < 12109375 then
                  if k < 11719500 then
                    if k = 11718780 then (583593) else 0
                  else
                    if k = 11719500 then (591740) else 0
                else
                  if k < 12109376 then
                    if k = 12109375 then (2833858) else 0
                  else
                    if k = 12109376 then (-906164) else 0
              else
                if k < 12187500 then
                  if k < 12125000 then
                    if k = 12112500 then (312527) else 0
                  else
                    if k = 12125000 then (231540) else 0
                else
                  if k < 19531250 then
                    if k = 12187500 then (231538) else 0
                  else
                    if k = 19531250 then (5373335) else 0
          else
            if k < 19534376 then
              if k < 19531300 then
                if k < 19531252 then
                  if k = 19531251 then (-1192529) else 0
                else
                  if k < 19531260 then
                    if k = 19531252 then (1188822) else 0
                  else
                    if k = 19531260 then (291310) else 0
              else
                if k < 19532500 then
                  if k < 19531500 then
                    if k = 19531300 then (293178) else 0
                  else
                    if k = 19531500 then (293173) else 0
                else
                  if k < 19534375 then
                    if k = 19532500 then (305822) else 0
                  else
                    if k = 19534375 then (412026) else 0
            else
              if k < 19550000 then
                if k < 19546875 then
                  if k < 19537500 then
                    if k = 19534376 then (-70012) else 0
                  else
                    if k = 19537500 then (194717) else 0
                else
                  if k < 19546876 then
                    if k = 19546875 then (487649) else 0
                  else
                    if k = 19546876 then (-110636) else 0
              else
                if k < 19609375 then
                  if k < 19562500 then
                    if k = 19550000 then (153598) else 0
                  else
                    if k = 19562500 then (200318) else 0
                else
                  if k < 19609376 then
                    if k = 19609375 then (487668) else 0
                  else
                    if k = 19609376 then (-110643) else 0
  else
    if k < 304687500 then
      if k < 97675000 then
        if k < 58593800 then
          if k < 48906400 then
            if k < 48828276 then
              if k < 20312500 then
                if k < 19625000 then
                  if k = 19612500 then (153615) else 0
                else
                  if k < 19687500 then
                    if k = 19625000 then (195058) else 0
                  else
                    if k = 19687500 then (200325) else 0
              else
                if k < 39062500 then
                  if k < 23437500 then
                    if k = 20312500 then (673877) else 0
                  else
                    if k = 23437500 then (673907) else 0
                else
                  if k < 48828275 then
                    if k = 39062500 then (311051) else 0
                  else
                    if k = 48828275 then (5800689) else 0
            else
              if k < 48831400 then
                if k < 48828755 then
                  if k = 48828276 then (2688879) else 0
                else
                  if k < 48828756 then
                    if k = 48828755 then (7594848) else 0
                  else
                    if k = 48828756 then (3598238) else 0
              else
                if k < 48843900 then
                  if k < 48831880 then
                    if k = 48831400 then (451763) else 0
                  else
                    if k = 48831880 then (900626) else 0
                else
                  if k < 48844380 then
                    if k = 48843900 then (449043) else 0
                  else
                    if k = 48844380 then (454472) else 0
          else
            if k < 51171876 then
              if k < 49219400 then
                if k < 48906880 then
                  if k = 48906400 then (449043) else 0
                else
                  if k < 49218880 then
                    if k = 48906880 then (454472) else 0
                  else
                    if k = 49218880 then (883143) else 0
              else
                if k < 50782000 then
                  if k < 50781280 then
                    if k = 49219400 then (918271) else 0
                  else
                    if k = 50781280 then (883142) else 0
                else
                  if k < 51171875 then
                    if k = 50782000 then (918271) else 0
                  else
                    if k = 51171875 then (3953065) else 0
            else
              if k < 58593750 then
                if k < 51187500 then
                  if k < 51175000 then
                    if k = 51171876 then (-1199593) else 0
                  else
                    if k = 51175000 then (399703) else 0
                else
                  if k < 51250000 then
                    if k = 51187500 then (278253) else 0
                  else
                    if k = 51250000 then (278254) else 0
              else
                if k < 58593752 then
                  if k < 58593751 then
                    if k = 58593750 then (6700445) else 0
                  else
                    if k = 58593751 then (-868051) else 0
                else
                  if k < 58593760 then
                    if k = 58593752 then (1563499) else 0
                  else
                    if k = 58593760 then (474628) else 0
        else
          if k < 59375000 then
            if k < 58609376 then
              if k < 58596875 then
                if k < 58594000 then
                  if k = 58593800 then (429020) else 0
                else
                  if k < 58595000 then
                    if k = 58594000 then (429020) else 0
                  else
                    if k = 58595000 then (461335) else 0
              else
                if k < 58600000 then
                  if k < 58596876 then
                    if k = 58596875 then (549857) else 0
                  else
                    if k = 58596876 then (-71505) else 0
                else
                  if k < 58609375 then
                    if k = 58600000 then (89718) else 0
                  else
                    if k = 58609375 then (555248) else 0
            else
              if k < 58671876 then
                if k < 58625000 then
                  if k < 58612500 then
                    if k = 58609376 then (-92651) else 0
                  else
                    if k = 58612500 then (-9261) else 0
                else
                  if k < 58671875 then
                    if k = 58625000 then (77972) else 0
                  else
                    if k = 58671875 then (555251) else 0
              else
                if k < 58687500 then
                  if k < 58675000 then
                    if k = 58671876 then (-92653) else 0
                  else
                    if k = 58675000 then (-9266) else 0
                else
                  if k < 58750000 then
                    if k = 58687500 then (78186) else 0
                  else
                    if k = 58750000 then (77940) else 0
          else
            if k < 97656300 then
              if k < 97656250 then
                if k < 62500000 then
                  if k = 59375000 then (920821) else 0
                else
                  if k < 78125000 then
                    if k = 62500000 then (920821) else 0
                  else
                    if k = 78125000 then (206949) else 0
              else
                if k < 97656252 then
                  if k < 97656251 then
                    if k = 97656250 then (13951051) else 0
                  else
                    if k = 97656251 then (-2410969) else 0
                else
                  if k < 97656260 then
                    if k = 97656252 then (3215208) else 0
                  else
                    if k = 97656260 then (1305861) else 0
            else
              if k < 97659376 then
                if k < 97657500 then
                  if k < 97656500 then
                    if k = 97656300 then (665467) else 0
                  else
                    if k = 97656500 then (665471) else 0
                else
                  if k < 97659375 then
                    if k = 97657500 then (739380) else 0
                  else
                    if k = 97659375 then (2599146) else 0
              else
                if k < 97671875 then
                  if k < 97662500 then
                    if k = 97659376 then (-742651) else 0
                  else
                    if k = 97662500 then (1340107) else 0
                else
                  if k < 97671876 then
                    if k = 97671875 then (390599) else 0
                  else
                    if k = 97671876 then (72861) else 0
      else
        if k < 246095000 then
          if k < 244141276 then
            if k < 98437500 then
              if k < 97734376 then
                if k < 97687500 then
                  if k = 97675000 then (-257922) else 0
                else
                  if k < 97734375 then
                    if k = 97687500 then (215330) else 0
                  else
                    if k = 97734375 then (390534) else 0
              else
                if k < 97750000 then
                  if k < 97737500 then
                    if k = 97734376 then (72892) else 0
                  else
                    if k = 97737500 then (-257943) else 0
                else
                  if k < 97812500 then
                    if k = 97750000 then (210862) else 0
                  else
                    if k = 97812500 then (215328) else 0
            else
              if k < 195312500 then
                if k < 117187500 then
                  if k < 101562500 then
                    if k = 98437500 then (1395420) else 0
                  else
                    if k = 101562500 then (1395424) else 0
                else
                  if k < 156250000 then
                    if k = 117187500 then (375018) else 0
                  else
                    if k = 156250000 then (507092) else 0
              else
                if k < 244140756 then
                  if k < 244140755 then
                    if k = 195312500 then (1483528) else 0
                  else
                    if k = 244140755 then (4162390) else 0
                else
                  if k < 244141275 then
                    if k = 244140756 then (1964657) else 0
                  else
                    if k = 244141275 then (5911137) else 0
          else
            if k < 244531400 then
              if k < 244156380 then
                if k < 244143880 then
                  if k = 244141276 then (2789333) else 0
                else
                  if k < 244144400 then
                    if k = 244143880 then (318997) else 0
                  else
                    if k = 244144400 then (326209) else 0
              else
                if k < 244218880 then
                  if k < 244156900 then
                    if k = 244156380 then (317182) else 0
                  else
                    if k = 244156900 then (777072) else 0
                else
                  if k < 244219400 then
                    if k = 244218880 then (317179) else 0
                  else
                    if k = 244219400 then (326753) else 0
            else
              if k < 246093752 then
                if k < 246093750 then
                  if k < 244531880 then
                    if k = 244531400 then (630690) else 0
                  else
                    if k = 244531880 then (651390) else 0
                else
                  if k < 246093751 then
                    if k = 246093750 then (11656813) else 0
                  else
                    if k = 246093751 then (-1514904) else 0
              else
                if k < 246093800 then
                  if k < 246093760 then
                    if k = 246093752 then (2735057) else 0
                  else
                    if k = 246093760 then (623959) else 0
                else
                  if k < 246094000 then
                    if k = 246093800 then (1136477) else 0
                  else
                    if k = 246094000 then (630686) else 0
        else
          if k < 253906280 then
            if k < 246125000 then
              if k < 246100000 then
                if k < 246096875 then
                  if k = 246095000 then (705658) else 0
                else
                  if k < 246096876 then
                    if k = 246096875 then (455102) else 0
                  else
                    if k = 246096876 then (37777) else 0
              else
                if k < 246109376 then
                  if k < 246109375 then
                    if k = 246100000 then (127655) else 0
                  else
                    if k = 246109375 then (1717831) else 0
                else
                  if k < 246112500 then
                    if k = 246109376 then (-377821) else 0
                  else
                    if k = 246112500 then (-210027) else 0
            else
              if k < 246187500 then
                if k < 246171876 then
                  if k < 246171875 then
                    if k = 246125000 then (739234) else 0
                  else
                    if k = 246171875 then (270288) else 0
                else
                  if k < 246175000 then
                    if k = 246171876 then (127480) else 0
                  else
                    if k = 246175000 then (125128) else 0
              else
                if k < 246875000 then
                  if k < 246250000 then
                    if k = 246187500 then (-262559) else 0
                  else
                    if k = 246250000 then (131225) else 0
                else
                  if k < 250000000 then
                    if k = 246875000 then (1338800) else 0
                  else
                    if k = 250000000 then (1488200) else 0
          else
            if k < 265625000 then
              if k < 254296876 then
                if k < 253907000 then
                  if k = 253906280 then (301842) else 0
                else
                  if k < 254296875 then
                    if k = 253907000 then (318788) else 0
                  else
                    if k = 254296875 then (1418658) else 0
              else
                if k < 254312500 then
                  if k < 254300000 then
                    if k = 254296876 then (-442446) else 0
                  else
                    if k = 254300000 then (124516) else 0
                else
                  if k < 254375000 then
                    if k = 254312500 then (82775) else 0
                  else
                    if k = 254375000 then (79776) else 0
            else
              if k < 293359376 then
                if k < 292969500 then
                  if k < 292968780 then
                    if k = 265625000 then (305305) else 0
                  else
                    if k = 292968780 then (470215) else 0
                else
                  if k < 293359375 then
                    if k = 292969500 then (486284) else 0
                  else
                    if k = 293359375 then (2037393) else 0
              else
                if k < 293375000 then
                  if k < 293362500 then
                    if k = 293359376 then (-607622) else 0
                  else
                    if k = 293362500 then (197247) else 0
                else
                  if k < 293437500 then
                    if k = 293375000 then (129317) else 0
                  else
                    if k = 293437500 then (130613) else 0
    else
      if k < 1225000000 then
        if k < 1220703875 then
          if k < 488312500 then
            if k < 488281500 then
              if k < 488281251 then
                if k < 343750000 then
                  if k = 304687500 then (478133) else 0
                else
                  if k < 488281250 then
                    if k = 343750000 then (775732) else 0
                  else
                    if k = 488281250 then (7733193) else 0
              else
                if k < 488281260 then
                  if k < 488281252 then
                    if k = 488281251 then (-1319551) else 0
                  else
                    if k = 488281252 then (1803902) else 0
                else
                  if k < 488281300 then
                    if k = 488281260 then (335978) else 0
                  else
                    if k = 488281300 then (784189) else 0
            else
              if k < 488287500 then
                if k < 488284375 then
                  if k < 488282500 then
                    if k = 488281500 then (340280) else 0
                  else
                    if k = 488282500 then (389139) else 0
                else
                  if k < 488284376 then
                    if k = 488284375 then (126242) else 0
                  else
                    if k = 488284376 then (78463) else 0
              else
                if k < 488296876 then
                  if k < 488296875 then
                    if k = 488287500 then (149877) else 0
                  else
                    if k = 488296875 then (1403322) else 0
                else
                  if k < 488300000 then
                    if k = 488296876 then (-364320) else 0
                  else
                    if k = 488300000 then (-120319) else 0
          else
            if k < 492187500 then
              if k < 488362500 then
                if k < 488359375 then
                  if k = 488312500 then (807044) else 0
                else
                  if k < 488359376 then
                    if k = 488359375 then (19621) else 0
                  else
                    if k = 488359376 then (131319) else 0
              else
                if k < 488437500 then
                  if k < 488375000 then
                    if k = 488362500 then (156420) else 0
                  else
                    if k = 488375000 then (-143279) else 0
                else
                  if k < 489062500 then
                    if k = 488437500 then (179660) else 0
                  else
                    if k = 489062500 then (741344) else 0
            else
              if k < 734375000 then
                if k < 546875000 then
                  if k < 507812500 then
                    if k = 492187500 then (876780) else 0
                  else
                    if k = 507812500 then (185908) else 0
                else
                  if k < 585937500 then
                    if k = 546875000 then (270806) else 0
                  else
                    if k = 585937500 then (469720) else 0
              else
                if k < 1220703155 then
                  if k < 976562500 then
                    if k = 734375000 then (523496) else 0
                  else
                    if k = 976562500 then (433053) else 0
                else
                  if k < 1220703156 then
                    if k = 1220703155 then (4162390) else 0
                  else
                    if k = 1220703156 then (1964655) else 0
        else
          if k < 1221096875 then
            if k < 1220782000 then
              if k < 1220707000 then
                if k < 1220703876 then
                  if k = 1220703875 then (5911137) else 0
                else
                  if k < 1220706280 then
                    if k = 1220703876 then (2789334) else 0
                  else
                    if k = 1220706280 then (318998) else 0
              else
                if k < 1220719500 then
                  if k < 1220718780 then
                    if k = 1220707000 then (326209) else 0
                  else
                    if k = 1220718780 then (317179) else 0
                else
                  if k < 1220781280 then
                    if k = 1220719500 then (326753) else 0
                  else
                    if k = 1220781280 then (317183) else 0
            else
              if k < 1221093760 then
                if k < 1221093751 then
                  if k < 1221093750 then
                    if k = 1220782000 then (777071) else 0
                  else
                    if k = 1221093750 then (11656848) else 0
                else
                  if k < 1221093752 then
                    if k = 1221093751 then (-1514923) else 0
                  else
                    if k = 1221093752 then (2735066) else 0
              else
                if k < 1221094000 then
                  if k < 1221093800 then
                    if k = 1221093760 then (623959) else 0
                  else
                    if k = 1221093800 then (630687) else 0
                else
                  if k < 1221095000 then
                    if k = 1221094000 then (1136476) else 0
                  else
                    if k = 1221095000 then (705659) else 0
          else
            if k < 1221171875 then
              if k < 1221109375 then
                if k < 1221096876 then
                  if k = 1221096875 then (455296) else 0
                else
                  if k < 1221100000 then
                    if k = 1221096876 then (37680) else 0
                  else
                    if k = 1221100000 then (127678) else 0
              else
                if k < 1221112500 then
                  if k < 1221109376 then
                    if k = 1221109375 then (270523) else 0
                  else
                    if k = 1221109376 then (127362) else 0
                else
                  if k < 1221125000 then
                    if k = 1221112500 then (125148) else 0
                  else
                    if k = 1221125000 then (131237) else 0
            else
              if k < 1221250000 then
                if k < 1221175000 then
                  if k < 1221171876 then
                    if k = 1221171875 then (1717705) else 0
                  else
                    if k = 1221171876 then (-377759) else 0
                else
                  if k < 1221187500 then
                    if k = 1221175000 then (-210023) else 0
                  else
                    if k = 1221187500 then (-262558) else 0
              else
                if k < 1222656400 then
                  if k < 1221875000 then
                    if k = 1221250000 then (739214) else 0
                  else
                    if k = 1221875000 then (1488164) else 0
                else
                  if k < 1222656880 then
                    if k = 1222656400 then (630691) else 0
                  else
                    if k = 1222656880 then (651390) else 0
      else
        if k < 1513750000 then
          if k < 1271562500 then
            if k < 1232500000 then
              if k < 1232421875 then
                if k < 1230468880 then
                  if k = 1225000000 then (1338790) else 0
                else
                  if k < 1230469400 then
                    if k = 1230468880 then (301842) else 0
                  else
                    if k = 1230469400 then (318788) else 0
              else
                if k < 1232425000 then
                  if k < 1232421876 then
                    if k = 1232421875 then (1418815) else 0
                  else
                    if k = 1232421876 then (-442523) else 0
                else
                  if k < 1232437500 then
                    if k = 1232425000 then (124519) else 0
                  else
                    if k = 1232437500 then (79784) else 0
            else
              if k < 1271484375 then
                if k < 1269531380 then
                  if k < 1240625000 then
                    if k = 1232500000 then (82777) else 0
                  else
                    if k = 1240625000 then (305316) else 0
                else
                  if k < 1269531900 then
                    if k = 1269531380 then (470216) else 0
                  else
                    if k = 1269531900 then (486285) else 0
              else
                if k < 1271487500 then
                  if k < 1271484376 then
                    if k = 1271484375 then (2037568) else 0
                  else
                    if k = 1271484376 then (-607709) else 0
                else
                  if k < 1271500000 then
                    if k = 1271487500 then (197239) else 0
                  else
                    if k = 1271500000 then (130616) else 0
          else
            if k < 1474609376 then
              if k < 1464843900 then
                if k < 1279687500 then
                  if k = 1271562500 then (129312) else 0
                else
                  if k < 1318750000 then
                    if k = 1279687500 then (478132) else 0
                  else
                    if k = 1318750000 then (775756) else 0
              else
                if k < 1467187500 then
                  if k < 1464844380 then
                    if k = 1464843900 then (338068) else 0
                  else
                    if k = 1464844380 then (344016) else 0
                else
                  if k < 1474609375 then
                    if k = 1467187500 then (725460) else 0
                  else
                    if k = 1474609375 then (752865) else 0
            else
              if k < 1513671875 then
                if k < 1474625000 then
                  if k < 1474612500 then
                    if k = 1474609376 then (-233311) else 0
                  else
                    if k = 1474612500 then (78020) else 0
                else
                  if k < 1474687500 then
                    if k = 1474625000 then (54692) else 0
                  else
                    if k = 1474687500 then (54684) else 0
              else
                if k < 1513675000 then
                  if k < 1513671876 then
                    if k = 1513671875 then (1065899) else 0
                  else
                    if k = 1513671876 then (-315518) else 0
                else
                  if k < 1513687500 then
                    if k = 1513675000 then (105630) else 0
                  else
                    if k = 1513687500 then (68507) else 0
        else
          if k < 2441437500 then
            if k < 2441406500 then
              if k < 2441406251 then
                if k < 1709375000 then
                  if k = 1513750000 then (68496) else 0
                else
                  if k < 2441406250 then
                    if k = 1709375000 then (395345) else 0
                  else
                    if k = 2441406250 then (7733555) else 0
              else
                if k < 2441406260 then
                  if k < 2441406252 then
                    if k = 2441406251 then (-1319691) else 0
                  else
                    if k = 2441406252 then (1803955) else 0
                else
                  if k < 2441406300 then
                    if k = 2441406260 then (335974) else 0
                  else
                    if k = 2441406300 then (340281) else 0
            else
              if k < 2441412500 then
                if k < 2441409375 then
                  if k < 2441407500 then
                    if k = 2441406500 then (784192) else 0
                  else
                    if k = 2441407500 then (389138) else 0
                else
                  if k < 2441409376 then
                    if k = 2441409375 then (126537) else 0
                  else
                    if k = 2441409376 then (78319) else 0
              else
                if k < 2441421876 then
                  if k < 2441421875 then
                    if k = 2441412500 then (149893) else 0
                  else
                    if k = 2441421875 then (19998) else 0
                else
                  if k < 2441425000 then
                    if k = 2441421876 then (131135) else 0
                  else
                    if k = 2441425000 then (156445) else 0
          else
            if k < 2445312500 then
              if k < 2441487500 then
                if k < 2441484375 then
                  if k = 2441437500 then (179693) else 0
                else
                  if k < 2441484376 then
                    if k = 2441484375 then (1403748) else 0
                  else
                    if k = 2441484376 then (-364529) else 0
              else
                if k < 2441562500 then
                  if k < 2441500000 then
                    if k = 2441487500 then (-120298) else 0
                  else
                    if k = 2441500000 then (-143251) else 0
                else
                  if k < 2442187500 then
                    if k = 2441562500 then (807060) else 0
                  else
                    if k = 2442187500 then (876755) else 0
            else
              if k < 2687500000 then
                if k < 2500000000 then
                  if k < 2460937500 then
                    if k = 2445312500 then (741348) else 0
                  else
                    if k = 2460937500 then (185909) else 0
                else
                  if k < 2539062500 then
                    if k = 2500000000 then (270824) else 0
                  else
                    if k = 2539062500 then (469789) else 0
              else
                if k < 3662500000 then
                  if k < 2929687500 then
                    if k = 2687500000 then (395329) else 0
                  else
                    if k = 2929687500 then (236319) else 0
                else
                  if k < 4882812500 then
                    if k = 3662500000 then (523501) else 0
                  else
                    if k = 4882812500 then (433249) else 0

/-- Dimensions of the eight exact moment-matrix blocks. -/
def blockSize : Fin 8 → ℕ
  | 0 => 28
  | 1 => 11
  | 2 => 11
  | 3 => 16
  | 4 => 11
  | 5 => 16
  | 6 => 16
  | 7 => 11

/-- Pairs of padded variable indices forming each quadratic monomial block. -/
def basisPair : (c : Fin 8) → Fin (blockSize c) → Fin 15 × Fin 15
  | 0 => ![(0, 0), (0, 1), (0, 6), (0, 7), (0, 8), (1, 6), (1, 7), (1, 8), (2, 2), (3, 3), (4, 4),
    (5, 5), (6, 6), (6, 7), (6, 8), (7, 7), (7, 8), (8, 8), (9, 9), (9, 14), (10, 10), (10, 13),
    (11, 11), (11, 12), (12, 12), (13, 13), (14, 14), (1, 1)]
  | 1 => ![(0, 2), (1, 2), (2, 6), (2, 7), (2, 8), (3, 9), (3, 14), (4, 10), (4, 13), (5, 11), (5,
    12)]
  | 2 => ![(0, 3), (1, 3), (2, 9), (2, 14), (3, 6), (3, 7), (3, 8), (4, 11), (4, 12), (5, 10), (5,
    13)]
  | 3 => ![(0, 9), (0, 14), (1, 9), (1, 14), (2, 3), (4, 5), (6, 9), (6, 14), (7, 9), (7, 14), (8,
    9), (8, 14), (10, 11), (10, 12), (11, 13), (12, 13)]
  | 4 => ![(0, 4), (1, 4), (2, 10), (2, 13), (3, 11), (3, 12), (4, 6), (4, 7), (4, 8), (5, 9), (5,
    14)]
  | 5 => ![(0, 10), (0, 13), (1, 10), (1, 13), (2, 4), (3, 5), (6, 10), (6, 13), (7, 10), (7, 13),
    (8, 10), (8, 13), (9, 11), (9, 12), (11, 14), (12, 14)]
  | 6 => ![(0, 11), (0, 12), (1, 11), (1, 12), (2, 5), (3, 4), (6, 11), (6, 12), (7, 11), (7, 12),
    (8, 11), (8, 12), (9, 10), (9, 13), (10, 14), (13, 14)]
  | 7 => ![(0, 5), (1, 5), (2, 11), (2, 12), (3, 10), (3, 13), (4, 9), (4, 14), (5, 6), (5, 7),
    (5, 8)]

/-- Integer moment matrices, with the common denominator kept separate. -/
def blockNumerator : (c : Fin 8) → Fin (blockSize c) → Fin (blockSize c) → ℤ
  | 0 => momentBlockFull0Stage0
  | 1 => momentBlock1Stage0
  | 2 => momentBlock2Stage0
  | 3 => momentBlock3Stage0
  | 4 => momentBlock4Stage0
  | 5 => momentBlock5Stage0
  | 6 => momentBlock6Stage0
  | 7 => momentBlock7Stage0

theorem blockNumerator_psd (c : Fin 8) : IsPSD (fun i j => (blockNumerator c i j : ℝ)) := by
  fin_cases c
  · exact momentBlockFull0Stage0_psd
  · exact momentBlock1Stage0_psd
  · exact momentBlock2Stage0_psd
  · exact momentBlock3Stage0_psd
  · exact momentBlock4Stage0_psd
  · exact momentBlock5Stage0_psd
  · exact momentBlock6Stage0_psd
  · exact momentBlock7Stage0_psd

/-- A zero index pads a monomial of degree less than two. -/
noncomputable def variableExponent (i : Fin 15) : Exponent :=
  if h : i = 0 then 0 else Finsupp.single ⟨i.val - 1, by
    have hi := i.isLt
    have hn : i.val ≠ 0 := by simpa using h
    omega⟩ 1

/-- Base-five key of a variable, with zero representing the constant monomial. -/
def variableKey (i : Fin 15) : ℕ := if i = 0 then 0 else 5 ^ (i.val - 1)

/-- Exponent vector of a quadratic monomial in the complete block basis. -/
noncomputable def momentBasis (b : (c : Fin 8) × Fin (blockSize c)) : Exponent :=
  variableExponent (basisPair b.1 b.2).1 + variableExponent (basisPair b.1 b.2).2

/-- Moment-table key of a quadratic basis monomial. -/
def basisKey (c : Fin 8) (i : Fin (blockSize c)) : ℕ :=
  variableKey (basisPair c i).1 + variableKey (basisPair c i).2

@[simp] theorem exponentKey_variableExponent (i : Fin 15) :
    exponentKey (variableExponent i) = variableKey i := by
  simp only [variableExponent, variableKey]
  split_ifs <;> simp

@[simp] theorem exponentKey_momentBasis (b : (c : Fin 8) × Fin (blockSize c)) :
    exponentKey (momentBasis b) = basisKey b.1 b.2 := by
  simp [momentBasis, basisKey]

theorem moment_block_0 : ∀ i j : Fin (blockSize 0),
    momentNumerator (basisKey 0 i + basisKey 0 j) = blockNumerator 0 i j := by
  decide +kernel

theorem moment_block_1 : ∀ i j : Fin (blockSize 1),
    momentNumerator (basisKey 1 i + basisKey 1 j) = blockNumerator 1 i j := by
  decide +kernel

theorem moment_block_2 : ∀ i j : Fin (blockSize 2),
    momentNumerator (basisKey 2 i + basisKey 2 j) = blockNumerator 2 i j := by
  decide +kernel

theorem moment_block_3 : ∀ i j : Fin (blockSize 3),
    momentNumerator (basisKey 3 i + basisKey 3 j) = blockNumerator 3 i j := by
  decide +kernel

theorem moment_block_4 : ∀ i j : Fin (blockSize 4),
    momentNumerator (basisKey 4 i + basisKey 4 j) = blockNumerator 4 i j := by
  decide +kernel

theorem moment_block_5 : ∀ i j : Fin (blockSize 5),
    momentNumerator (basisKey 5 i + basisKey 5 j) = blockNumerator 5 i j := by
  decide +kernel

theorem moment_block_6 : ∀ i j : Fin (blockSize 6),
    momentNumerator (basisKey 6 i + basisKey 6 j) = blockNumerator 6 i j := by
  decide +kernel

theorem moment_block_7 : ∀ i j : Fin (blockSize 7),
    momentNumerator (basisKey 7 i + basisKey 7 j) = blockNumerator 7 i j := by
  decide +kernel

theorem moment_block : ∀ c (i j : Fin (blockSize c)),
    momentNumerator (basisKey c i + basisKey c j) = blockNumerator c i j := by
  intro c
  fin_cases c
  · exact moment_block_0
  · exact moment_block_1
  · exact moment_block_2
  · exact moment_block_3
  · exact moment_block_4
  · exact moment_block_5
  · exact moment_block_6
  · exact moment_block_7

theorem moment_cross_0 : ∀ d : Fin 8, 0 ≠ d → ∀ (i : Fin (blockSize 0)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 0 i + basisKey d j) = 0 := by
  decide +kernel

theorem moment_cross_1 : ∀ d : Fin 8, 1 ≠ d → ∀ (i : Fin (blockSize 1)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 1 i + basisKey d j) = 0 := by
  decide +kernel

theorem moment_cross_2 : ∀ d : Fin 8, 2 ≠ d → ∀ (i : Fin (blockSize 2)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 2 i + basisKey d j) = 0 := by
  decide +kernel

theorem moment_cross_3 : ∀ d : Fin 8, 3 ≠ d → ∀ (i : Fin (blockSize 3)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 3 i + basisKey d j) = 0 := by
  decide +kernel

theorem moment_cross_4 : ∀ d : Fin 8, 4 ≠ d → ∀ (i : Fin (blockSize 4)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 4 i + basisKey d j) = 0 := by
  decide +kernel

theorem moment_cross_5 : ∀ d : Fin 8, 5 ≠ d → ∀ (i : Fin (blockSize 5)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 5 i + basisKey d j) = 0 := by
  decide +kernel

theorem moment_cross_6 : ∀ d : Fin 8, 6 ≠ d → ∀ (i : Fin (blockSize 6)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 6 i + basisKey d j) = 0 := by
  decide +kernel

theorem moment_cross_7 : ∀ d : Fin 8, 7 ≠ d → ∀ (i : Fin (blockSize 7)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 7 i + basisKey d j) = 0 := by
  decide +kernel

theorem moment_cross : ∀ c d : Fin 8, c ≠ d → ∀ (i : Fin (blockSize c)) (j : Fin (blockSize d)),
    momentNumerator (basisKey c i + basisKey d j) = 0 := by
  intro c
  fin_cases c
  · exact moment_cross_0
  · exact moment_cross_1
  · exact moment_cross_2
  · exact moment_cross_3
  · exact moment_cross_4
  · exact moment_cross_5
  · exact moment_cross_6
  · exact moment_cross_7

theorem moment_quadratic_numerator_sum :
    (∑ i : Fin 14, momentNumerator (2 * 5 ^ i.val)) = 1000000000 := by
  decide +kernel

theorem moment_quartic_numerator_sum :
    (∑ i : Fin 14, ∑ j : Fin 14, momentNumerator (2 * 5 ^ i.val + 2 * 5 ^ j.val)) =
      1000000000 := by
  decide +kernel

end PersistentSOS
