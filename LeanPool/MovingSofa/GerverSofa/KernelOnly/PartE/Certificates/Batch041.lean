/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch001



























































































































































public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch002

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch003














public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch004

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch005

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch002

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch037

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch038

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch039



public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch040









/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.PhiBelow.Leaf00445`.
* `KernelOnly.PartE.PhiBelow.Join00446`.
* `KernelOnly.PartE.PhiBelow.Join00447`.
* `KernelOnly.PartE.PhiBelow.Join00448`.
* `KernelOnly.PartE.PhiBelow.Leaf00450`.
* `KernelOnly.PartE.PhiBelow.Leaf00451`.
* `KernelOnly.PartE.PhiBelow.Leaf00453`.
* `KernelOnly.PartE.PhiBelow.Leaf00454`.
* `KernelOnly.PartE.PhiBelow.Leaf00455`.
* `KernelOnly.PartE.PhiBelow.Leaf00456`.
* `KernelOnly.PartE.PhiBelow.Join00457`.
* `KernelOnly.PartE.PhiBelow.Leaf00458`.
* `KernelOnly.PartE.PhiBelow.Join00459`.
* `KernelOnly.PartE.PhiBelow.Join00460`.
* `KernelOnly.PartE.PhiBelow.Leaf00461`.
* `KernelOnly.PartE.PhiBelow.Join00462`.
* `KernelOnly.PartE.E24KC6PhiBelowReconstruct`.
* `KernelOnly.PartE.ThetaAbove.Leaf00009`.
* `KernelOnly.PartE.ThetaAbove.Leaf00010`.
* `KernelOnly.PartE.ThetaAbove.Leaf00012`.
* `KernelOnly.PartE.ThetaAbove.Leaf00013`.
* `KernelOnly.PartE.ThetaAbove.Leaf00014`.
* `KernelOnly.PartE.ThetaAbove.Leaf00015`.
* `KernelOnly.PartE.ThetaAbove.Join00016`.
* `KernelOnly.PartE.ThetaAbove.Leaf00018`.
* `KernelOnly.PartE.ThetaAbove.Leaf00019`.
* `KernelOnly.PartE.ThetaAbove.Leaf00020`.
* `KernelOnly.PartE.ThetaAbove.Leaf00021`.
* `KernelOnly.PartE.ThetaAbove.Join00022`.
* `KernelOnly.PartE.ThetaAbove.Join00023`.
* `KernelOnly.PartE.ThetaAbove.Leaf00024`.
* `KernelOnly.PartE.ThetaAbove.Leaf00025`.
* `KernelOnly.PartE.ThetaAbove.Leaf00028`.
* `KernelOnly.PartE.ThetaAbove.Leaf00029`.
* `KernelOnly.PartE.ThetaAbove.Leaf00475`.
* `KernelOnly.PartE.ThetaAbove.Leaf00476`.
* `KernelOnly.PartE.ThetaAbove.Leaf00480`.
* `KernelOnly.PartE.ThetaAbove.Leaf00481`.
* `KernelOnly.PartE.ThetaAbove.Leaf00482`.
* `KernelOnly.PartE.ThetaAbove.Leaf00483`.
* `KernelOnly.PartE.ThetaAbove.Join00484`.
* `KernelOnly.PartE.ThetaAbove.Leaf00486`.
* `KernelOnly.PartE.ThetaAbove.Leaf00487`.
* `KernelOnly.PartE.ThetaAbove.Leaf00488`.
* `KernelOnly.PartE.ThetaAbove.Leaf00489`.
* `KernelOnly.PartE.ThetaAbove.Join00490`.
* `KernelOnly.PartE.ThetaAbove.Leaf00491`.
* `KernelOnly.PartE.ThetaAbove.Leaf00492`.
* `KernelOnly.PartE.ThetaAbove.Join00493`.
* `KernelOnly.PartE.ThetaAbove.Leaf00496`.
* `KernelOnly.PartE.ThetaAbove.Leaf00497`.
* `KernelOnly.PartE.ThetaAbove.Leaf00498`.
* `KernelOnly.PartE.ThetaAbove.Leaf00499`.
* `KernelOnly.PartE.ThetaAbove.Join00500`.
* `KernelOnly.PartE.ThetaAbove.Leaf00502`.
* `KernelOnly.PartE.ThetaAbove.Leaf00503`.
-/

@[expose] public section

noncomputable section

namespace GerverSofa.PartE.CoverCertificate68b045bc3f

private abbrev cellRoot : AngleCell :=
  (childHH (childHH phiBelowCell33233223))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell000 : AngleCell :=
  childLL cell00


private abbrev cell001 : AngleCell :=
  childLH cell00


private abbrev cell002 : AngleCell :=
  childHL cell00


private abbrev cell003 : AngleCell :=
  childHH cell00


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33


private abbrev cell2220 : AngleCell :=
  childLL cell222


private abbrev cell2221 : AngleCell :=
  childLH cell222


private abbrev cell2222 : AngleCell :=
  childHL cell222


private abbrev cell2223 : AngleCell :=
  childHH cell222

end GerverSofa.PartE.CoverCertificate68b045bc3f

namespace GerverSofa.PartE.CoverCertificate56f1cababc

private abbrev cellRoot : AngleCell :=
  phiBelowCell33233230


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23

end GerverSofa.PartE.CoverCertificate56f1cababc

namespace GerverSofa.PartE.CoverCertificateb43d9cc590

private abbrev cellRoot : AngleCell :=
  phiBelowCell33233231


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificateb43d9cc590

namespace GerverSofa.PartE.CoverCertificate3c8c170ddf

private abbrev cellRoot : AngleCell :=
  (childLL phiBelowCell33233232)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate3c8c170ddf

namespace GerverSofa.PartE.CoverCertificate31d8f6a3a1

private abbrev cellRoot : AngleCell :=
  (childLH phiBelowCell33233232)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate31d8f6a3a1

namespace GerverSofa.PartE.CoverCertificate3406557cb6

private abbrev cellRoot : AngleCell :=
  (childHL phiBelowCell33233232)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell000 : AngleCell :=
  childLL cell00


private abbrev cell001 : AngleCell :=
  childLH cell00


private abbrev cell002 : AngleCell :=
  childHL cell00


private abbrev cell003 : AngleCell :=
  childHH cell00


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate3406557cb6

namespace GerverSofa.PartE.CoverCertificated5f4efe538

private abbrev cellRoot : AngleCell :=
  (childHH phiBelowCell33233232)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificated5f4efe538

namespace GerverSofa.PartE.CoverCertificatecb887b449d

private abbrev cellRoot : AngleCell :=
  phiBelowCell33233233


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23

end GerverSofa.PartE.CoverCertificatecb887b449d

namespace GerverSofa.PartE.CoverCertificateb1645a3287

private abbrev cellRoot : AngleCell :=
  (childHH (childHH phiBelowCell3323))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell000 : AngleCell :=
  childLL cell00


private abbrev cell001 : AngleCell :=
  childLH cell00


private abbrev cell002 : AngleCell :=
  childHL cell00


private abbrev cell003 : AngleCell :=
  childHH cell00


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33


private abbrev cell2020 : AngleCell :=
  childLL cell202


private abbrev cell2021 : AngleCell :=
  childLH cell202


private abbrev cell2022 : AngleCell :=
  childHL cell202


private abbrev cell2023 : AngleCell :=
  childHH cell202


private abbrev cell2200 : AngleCell :=
  childLL cell220


private abbrev cell2201 : AngleCell :=
  childLH cell220


private abbrev cell2202 : AngleCell :=
  childHL cell220


private abbrev cell2203 : AngleCell :=
  childHH cell220


private abbrev cell2210 : AngleCell :=
  childLL cell221


private abbrev cell2211 : AngleCell :=
  childLH cell221


private abbrev cell2212 : AngleCell :=
  childHL cell221


private abbrev cell2213 : AngleCell :=
  childHH cell221


private abbrev cell2220 : AngleCell :=
  childLL cell222


private abbrev cell2221 : AngleCell :=
  childLH cell222


private abbrev cell2222 : AngleCell :=
  childHL cell222


private abbrev cell2223 : AngleCell :=
  childHH cell222


private abbrev cell2230 : AngleCell :=
  childLL cell223


private abbrev cell2231 : AngleCell :=
  childLH cell223


private abbrev cell2232 : AngleCell :=
  childHL cell223


private abbrev cell2233 : AngleCell :=
  childHH cell223


private abbrev cell2320 : AngleCell :=
  childLL cell232


private abbrev cell2321 : AngleCell :=
  childLH cell232


private abbrev cell2322 : AngleCell :=
  childHL cell232


private abbrev cell2323 : AngleCell :=
  childHH cell232

end GerverSofa.PartE.CoverCertificateb1645a3287

namespace GerverSofa.PartE.CoverCertificatef6f28b19e8

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childHH thetaAboveCell000022002011)))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificatef6f28b19e8

namespace GerverSofa.PartE.CoverCertificate15902c79ec

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHH thetaAboveCell000022002011)))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate15902c79ec

namespace GerverSofa.PartE.CoverCertificate36f48ed6fa

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020113120


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate36f48ed6fa

namespace GerverSofa.PartE.CoverCertificate80e1d488d9

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020113121


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate80e1d488d9

namespace GerverSofa.PartE.CoverCertificate24ddeb8618

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020113122


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate24ddeb8618

namespace GerverSofa.PartE.CoverCertificatea600465144

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020113123


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatea600465144

namespace GerverSofa.PartE.CoverCertificatefdcad14d68

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020113130


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificatefdcad14d68

namespace GerverSofa.PartE.CoverCertificate3ad1ac00a7

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020113131


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate3ad1ac00a7

namespace GerverSofa.PartE.CoverCertificatea3bd708439

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020113132


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatea3bd708439

namespace GerverSofa.PartE.CoverCertificateaf7d47a996

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020113133


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateaf7d47a996

namespace GerverSofa.PartE.CoverCertificatec662ef9997

private abbrev cellRoot : AngleCell :=
  (childHL (childHH thetaAboveCell000022002011))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatec662ef9997

namespace GerverSofa.PartE.CoverCertificate32e68ad46a

private abbrev cellRoot : AngleCell :=
  (childHH (childHH thetaAboveCell000022002011))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate32e68ad46a

namespace GerverSofa.PartE.CoverCertificate713bbdaba3

private abbrev cellRoot : AngleCell :=
  thetaAboveCell000022002012


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1

end GerverSofa.PartE.CoverCertificate713bbdaba3

namespace GerverSofa.PartE.CoverCertificate5832573e8a

private abbrev cellRoot : AngleCell :=
  thetaAboveCell000022002013


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1

end GerverSofa.PartE.CoverCertificate5832573e8a

namespace GerverSofa.PartE.CoverCertificatec47ffcf2f2

private abbrev cellRoot : AngleCell :=
  (childLL thetaAboveCell000022002000)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificatec47ffcf2f2

namespace GerverSofa.PartE.CoverCertificate535ad25afd

private abbrev cellRoot : AngleCell :=
  (childLH thetaAboveCell000022002000)


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate535ad25afd

namespace GerverSofa.PartE.CoverCertificate746010fa88

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002000


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate746010fa88

namespace GerverSofa.PartE.CoverCertificate1f629121b3

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002001


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate1f629121b3

namespace GerverSofa.PartE.CoverCertificatec4d5c9280e

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002002


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificatec4d5c9280e

namespace GerverSofa.PartE.CoverCertificate68a7675d0f

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002003


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate68a7675d0f

namespace GerverSofa.PartE.CoverCertificateaaac1ef041

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002010


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateaaac1ef041

namespace GerverSofa.PartE.CoverCertificateeac308265d

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002011


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateeac308265d

namespace GerverSofa.PartE.CoverCertificateee7e82afcc

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002012


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificateee7e82afcc

namespace GerverSofa.PartE.CoverCertificatec74fdabb9c

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002013


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificatec74fdabb9c

namespace GerverSofa.PartE.CoverCertificateb0390aea72

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHL thetaAboveCell000022002000)))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell000 : AngleCell :=
  childLL cell00


private abbrev cell001 : AngleCell :=
  childLH cell00


private abbrev cell002 : AngleCell :=
  childHL cell00


private abbrev cell003 : AngleCell :=
  childHH cell00


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell100 : AngleCell :=
  childLL cell10


private abbrev cell101 : AngleCell :=
  childLH cell10


private abbrev cell102 : AngleCell :=
  childHL cell10


private abbrev cell103 : AngleCell :=
  childHH cell10


private abbrev cell110 : AngleCell :=
  childLL cell11


private abbrev cell111 : AngleCell :=
  childLH cell11


private abbrev cell112 : AngleCell :=
  childHL cell11


private abbrev cell113 : AngleCell :=
  childHH cell11

end GerverSofa.PartE.CoverCertificateb0390aea72

namespace GerverSofa.PartE.CoverCertificate1f25ee1c58

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHL thetaAboveCell000022002000)))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell000 : AngleCell :=
  childLL cell00


private abbrev cell001 : AngleCell :=
  childLH cell00


private abbrev cell002 : AngleCell :=
  childHL cell00


private abbrev cell003 : AngleCell :=
  childHH cell00


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell100 : AngleCell :=
  childLL cell10


private abbrev cell101 : AngleCell :=
  childLH cell10


private abbrev cell102 : AngleCell :=
  childHL cell10


private abbrev cell103 : AngleCell :=
  childHH cell10


private abbrev cell110 : AngleCell :=
  childLL cell11


private abbrev cell111 : AngleCell :=
  childLH cell11


private abbrev cell112 : AngleCell :=
  childHL cell11


private abbrev cell113 : AngleCell :=
  childHH cell11


private abbrev cell1000 : AngleCell :=
  childLL cell100


private abbrev cell1001 : AngleCell :=
  childLH cell100


private abbrev cell1002 : AngleCell :=
  childHL cell100


private abbrev cell1003 : AngleCell :=
  childHH cell100


private abbrev cell1010 : AngleCell :=
  childLL cell101


private abbrev cell1011 : AngleCell :=
  childLH cell101


private abbrev cell1012 : AngleCell :=
  childHL cell101


private abbrev cell1013 : AngleCell :=
  childHH cell101


private abbrev cell1100 : AngleCell :=
  childLL cell110


private abbrev cell1101 : AngleCell :=
  childLH cell110


private abbrev cell1102 : AngleCell :=
  childHL cell110


private abbrev cell1103 : AngleCell :=
  childHH cell110


private abbrev cell1110 : AngleCell :=
  childLL cell111


private abbrev cell1111 : AngleCell :=
  childLH cell111


private abbrev cell1112 : AngleCell :=
  childHL cell111


private abbrev cell1113 : AngleCell :=
  childHH cell111

end GerverSofa.PartE.CoverCertificate1f25ee1c58

namespace GerverSofa.PartE.CoverCertificate64365f01f0

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002100


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate64365f01f0

namespace GerverSofa.PartE.CoverCertificatea308b70bb8

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002101


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatea308b70bb8

namespace GerverSofa.PartE.CoverCertificate181aa5f0fe

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002102


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate181aa5f0fe

namespace GerverSofa.PartE.CoverCertificatee52fd52368

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002103


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell220 : AngleCell :=
  childLL cell22


private abbrev cell221 : AngleCell :=
  childLH cell22


private abbrev cell222 : AngleCell :=
  childHL cell22


private abbrev cell223 : AngleCell :=
  childHH cell22


private abbrev cell230 : AngleCell :=
  childLL cell23


private abbrev cell231 : AngleCell :=
  childLH cell23


private abbrev cell232 : AngleCell :=
  childHL cell23


private abbrev cell233 : AngleCell :=
  childHH cell23


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31


private abbrev cell320 : AngleCell :=
  childLL cell32


private abbrev cell321 : AngleCell :=
  childLH cell32


private abbrev cell322 : AngleCell :=
  childHL cell32


private abbrev cell323 : AngleCell :=
  childHH cell32


private abbrev cell330 : AngleCell :=
  childLL cell33


private abbrev cell331 : AngleCell :=
  childLH cell33


private abbrev cell332 : AngleCell :=
  childHL cell33


private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificatee52fd52368

namespace GerverSofa.PartE.CoverCertificate5b77908b1d

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002110


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate5b77908b1d

namespace GerverSofa.PartE.CoverCertificatea6ac82148c

private abbrev cellRoot : AngleCell :=
  thetaAboveCell0000220020002111


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatea6ac82148c

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33233_c2_c2_c3_c3_c3_4_00445
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd112ae8b34

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `33233223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233223 : AngleCell :=
  childHH (childHL (childHL (childHH phiBelowCell3323)))

end CertificateCellsd112ae8b34

open CertificateCellsd112ae8b34
namespace CoverCertificate68b045bc3f










































































private theorem checked2220 : adaptiveCoverCheck 0 cell2220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2220 (by decide +kernel)

private theorem checked2221 : adaptiveCoverCheck 0 cell2221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2221 (by decide +kernel)

private theorem checked2222 : adaptiveCoverCheck 0 cell2222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2222 (by decide +kernel)

private theorem checked2223 : adaptiveCoverCheck 0 cell2223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2223 (by decide +kernel)

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 1 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 1 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 1 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 1 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 1 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 1 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 1 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 1 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell222
    checked2220 checked2221 checked2222 checked2223

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 1 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 1 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 1 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 1 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell303 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate68b045bc3f

theorem e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c3 :
    adaptiveCoverCheck 4 (childHH (childHH phiBelowCell33233223)) = true := by
  exact CoverCertificate68b045bc3f.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c3_c3_5_00446
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa21caf16f2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `33233223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233223 : AngleCell :=
  childHH (childHL (childHL (childHH phiBelowCell3323)))

end CertificateCellsa21caf16f2

open CertificateCellsa21caf16f2

theorem e24KC2PhiBelowLeaf33233_c2_c2_c3_c3 :
    adaptiveCoverCheck 5 (childHH phiBelowCell33233223) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childHH phiBelowCell33233223)
    e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c0 e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c2 e24KC2PhiBelowLeaf33233_c2_c2_c3_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_c3_6_00447
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells21943a9b83

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `33233223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233223 : AngleCell :=
  childHH (childHL (childHL (childHH phiBelowCell3323)))

end CertificateCells21943a9b83

open CertificateCells21943a9b83

theorem e24KC2PhiBelowLeaf33233_c2_c2_c3 :
    adaptiveCoverCheck 6 phiBelowCell33233223 = true :=
  adaptiveCoverCheck_succ_of_children 5 phiBelowCell33233223
    e24KC2PhiBelowLeaf33233_c2_c2_c3_c0 e24KC2PhiBelowLeaf33233_c2_c2_c3_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c3_c2 e24KC2PhiBelowLeaf33233_c2_c2_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c2_7_00448
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells62ff50a4e8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells62ff50a4e8

open CertificateCells62ff50a4e8

theorem e24KC2PhiBelowLeaf33233_c2_c2 :
    adaptiveCoverCheck 7 (childHL (childHL (childHH phiBelowCell3323))) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childHH phiBelowCell3323)))
    e24KC2PhiBelowLeaf33233_c2_c2_c0 e24KC2PhiBelowLeaf33233_c2_c2_c1
      e24KC2PhiBelowLeaf33233_c2_c2_c2 e24KC2PhiBelowLeaf33233_c2_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33233_c2_c3_c0_6_00450
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells005204f093

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `33233230` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233230 : AngleCell :=
  childLL (childHH (childHL (childHH phiBelowCell3323)))

end CertificateCells005204f093

open CertificateCells005204f093
namespace CoverCertificate56f1cababc


































private theorem checked200 : adaptiveCoverCheck 3 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 3 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 3 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 3 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell203 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 3 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 3 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 3 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 3 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 3 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 3 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 3 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 3 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell233 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 4 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 4 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 4 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 4 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 4 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 4 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 4 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 4 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 4 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 4 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 4 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 4 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 4 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 4 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 4 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 4 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 5 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 5 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 5 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 5 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 6 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate56f1cababc

theorem e24KC2PhiBelowLeaf33233_c2_c3_c0 :
    adaptiveCoverCheck 6 phiBelowCell33233230 = true := by
  exact CoverCertificate56f1cababc.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33233_c2_c3_c1_6_00451
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1db372ce58

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `33233231` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233231 : AngleCell :=
  childLH (childHH (childHL (childHH phiBelowCell3323)))

end CertificateCells1db372ce58

open CertificateCells1db372ce58
namespace CoverCertificateb43d9cc590






















private theorem checked00 : adaptiveCoverCheck 4 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 4 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 4 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 4 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 4 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 4 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 4 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 4 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 4 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 4 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 4 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 4 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 4 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 4 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 4 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 4 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 5 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 5 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 5 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 5 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 6 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateb43d9cc590

theorem e24KC2PhiBelowLeaf33233_c2_c3_c1 :
    adaptiveCoverCheck 6 phiBelowCell33233231 = true := by
  exact CoverCertificateb43d9cc590.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33233_c2_c3_c2_c0_5_00453
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells747d0e3511

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `33233232` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233232 : AngleCell :=
  childHL (childHH (childHL (childHH phiBelowCell3323)))

end CertificateCells747d0e3511

open CertificateCells747d0e3511
namespace CoverCertificate3c8c170ddf






















private theorem checked00 : adaptiveCoverCheck 3 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 3 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 3 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 3 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 3 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 3 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 3 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 3 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 3 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 3 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 3 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 3 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 3 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 3 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 3 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 3 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3c8c170ddf

theorem e24KC2PhiBelowLeaf33233_c2_c3_c2_c0 :
    adaptiveCoverCheck 5 (childLL phiBelowCell33233232) = true := by
  exact CoverCertificate3c8c170ddf.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33233_c2_c3_c2_c1_5_00454
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2c20a17ff6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `33233232` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233232 : AngleCell :=
  childHL (childHH (childHL (childHH phiBelowCell3323)))

end CertificateCells2c20a17ff6

open CertificateCells2c20a17ff6
namespace CoverCertificate31d8f6a3a1


















private theorem checked00 : adaptiveCoverCheck 3 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 3 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 3 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 3 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell03 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 3 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 3 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 3 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 3 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 3 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 3 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 3 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 3 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate31d8f6a3a1

theorem e24KC2PhiBelowLeaf33233_c2_c3_c2_c1 :
    adaptiveCoverCheck 5 (childLH phiBelowCell33233232) = true := by
  exact CoverCertificate31d8f6a3a1.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33233_c2_c3_c2_c2_5_00455
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6d9a408f54

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `33233232` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233232 : AngleCell :=
  childHL (childHH (childHL (childHH phiBelowCell3323)))

end CertificateCells6d9a408f54

open CertificateCells6d9a408f54
namespace CoverCertificate3406557cb6






























































private theorem checked000 : adaptiveCoverCheck 2 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 2 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 2 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 2 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell003 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 2 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 2 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 2 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 2 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 2 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 2 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 2 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 2 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell033 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 2 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 2 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 2 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 2 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 2 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 2 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 2 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 2 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 2 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 2 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 2 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 2 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 2 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 2 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 2 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 2 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 2 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 2 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 2 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 2 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell303 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 2 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 2 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 2 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 2 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 2 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 2 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 2 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 2 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 3 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 3 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 3 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 3 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 3 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 3 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 3 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 3 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 3 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 3 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 3 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 3 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 3 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 3 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 3 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 3 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3406557cb6

theorem e24KC2PhiBelowLeaf33233_c2_c3_c2_c2 :
    adaptiveCoverCheck 5 (childHL phiBelowCell33233232) = true := by
  exact CoverCertificate3406557cb6.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33233_c2_c3_c2_c3_5_00456
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells26c5fe31ab

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `33233232` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233232 : AngleCell :=
  childHL (childHH (childHL (childHH phiBelowCell3323)))

end CertificateCells26c5fe31ab

open CertificateCells26c5fe31ab
namespace CoverCertificated5f4efe538






















private theorem checked00 : adaptiveCoverCheck 3 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 3 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 3 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 3 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 3 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 3 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 3 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 3 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 3 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 3 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 3 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 3 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 3 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 3 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 3 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 3 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated5f4efe538

theorem e24KC2PhiBelowLeaf33233_c2_c3_c2_c3 :
    adaptiveCoverCheck 5 (childHH phiBelowCell33233232) = true := by
  exact CoverCertificated5f4efe538.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c3_c2_6_00457
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6677fc4b7c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `33233232` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233232 : AngleCell :=
  childHL (childHH (childHL (childHH phiBelowCell3323)))

end CertificateCells6677fc4b7c

open CertificateCells6677fc4b7c

theorem e24KC2PhiBelowLeaf33233_c2_c3_c2 :
    adaptiveCoverCheck 6 phiBelowCell33233232 = true :=
  adaptiveCoverCheck_succ_of_children 5 phiBelowCell33233232
    e24KC2PhiBelowLeaf33233_c2_c3_c2_c0 e24KC2PhiBelowLeaf33233_c2_c3_c2_c1
      e24KC2PhiBelowLeaf33233_c2_c3_c2_c2 e24KC2PhiBelowLeaf33233_c2_c3_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33233_c2_c3_c3_6_00458
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8faba9c99a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `33233233` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell33233233 : AngleCell :=
  childHH (childHH (childHL (childHH phiBelowCell3323)))

end CertificateCells8faba9c99a

open CertificateCells8faba9c99a
namespace CoverCertificatecb887b449d


































private theorem checked200 : adaptiveCoverCheck 3 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 3 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 3 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 3 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell203 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 3 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 3 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 3 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 3 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 3 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 3 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 3 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 3 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell233 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 4 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 4 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 4 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 4 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 4 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 4 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 4 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 4 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 4 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 4 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 4 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 4 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 4 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 4 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 4 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 4 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 5 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 5 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 5 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 5 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 6 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatecb887b449d

theorem e24KC2PhiBelowLeaf33233_c2_c3_c3 :
    adaptiveCoverCheck 6 phiBelowCell33233233 = true := by
  exact CoverCertificatecb887b449d.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_c3_7_00459
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells07875eeb47

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells07875eeb47

open CertificateCells07875eeb47

theorem e24KC2PhiBelowLeaf33233_c2_c3 :
    adaptiveCoverCheck 7 (childHH (childHL (childHH phiBelowCell3323))) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childHH phiBelowCell3323)))
    e24KC2PhiBelowLeaf33233_c2_c3_c0 e24KC2PhiBelowLeaf33233_c2_c3_c1
      e24KC2PhiBelowLeaf33233_c2_c3_c2 e24KC2PhiBelowLeaf33233_c2_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_c2_8_00460
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5ed2775b48

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells5ed2775b48

open CertificateCells5ed2775b48

theorem e24KC2PhiBelowLeaf33233_c2 :
    adaptiveCoverCheck 8 (childHL (childHH phiBelowCell3323)) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childHL (childHH phiBelowCell3323))
    e24KC2PhiBelowLeaf33233_c2_c0 e24KC2PhiBelowLeaf33233_c2_c1 e24KC2PhiBelowLeaf33233_c2_c2
      e24KC2PhiBelowLeaf33233_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Below Leaf33233_c3_8_00461
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd0acf0005e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCellsd0acf0005e

open CertificateCellsd0acf0005e
namespace CoverCertificateb1645a3287


































































































private theorem checked2020 : adaptiveCoverCheck 4 cell2020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2020 (by decide +kernel)

private theorem checked2021 : adaptiveCoverCheck 4 cell2021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2021 (by decide +kernel)

private theorem checked2022 : adaptiveCoverCheck 4 cell2022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2022 (by decide +kernel)

private theorem checked2023 : adaptiveCoverCheck 4 cell2023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2023 (by decide +kernel)

private theorem checked2200 : adaptiveCoverCheck 4 cell2200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2200 (by decide +kernel)

private theorem checked2201 : adaptiveCoverCheck 4 cell2201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2201 (by decide +kernel)

private theorem checked2202 : adaptiveCoverCheck 4 cell2202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2202 (by decide +kernel)

private theorem checked2203 : adaptiveCoverCheck 4 cell2203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2203 (by decide +kernel)

private theorem checked2210 : adaptiveCoverCheck 4 cell2210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2210 (by decide +kernel)

private theorem checked2211 : adaptiveCoverCheck 4 cell2211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2211 (by decide +kernel)

private theorem checked2212 : adaptiveCoverCheck 4 cell2212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2212 (by decide +kernel)

private theorem checked2213 : adaptiveCoverCheck 4 cell2213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2213 (by decide +kernel)

private theorem checked2220 : adaptiveCoverCheck 4 cell2220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2220 (by decide +kernel)

private theorem checked2221 : adaptiveCoverCheck 4 cell2221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2221 (by decide +kernel)

private theorem checked2222 : adaptiveCoverCheck 4 cell2222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2222 (by decide +kernel)

private theorem checked2223 : adaptiveCoverCheck 4 cell2223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2223 (by decide +kernel)

private theorem checked2230 : adaptiveCoverCheck 4 cell2230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2230 (by decide +kernel)

private theorem checked2231 : adaptiveCoverCheck 4 cell2231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2231 (by decide +kernel)

private theorem checked2232 : adaptiveCoverCheck 4 cell2232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2232 (by decide +kernel)

private theorem checked2233 : adaptiveCoverCheck 4 cell2233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2233 (by decide +kernel)

private theorem checked2320 : adaptiveCoverCheck 4 cell2320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2320 (by decide +kernel)

private theorem checked2321 : adaptiveCoverCheck 4 cell2321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2321 (by decide +kernel)

private theorem checked2322 : adaptiveCoverCheck 4 cell2322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2322 (by decide +kernel)

private theorem checked2323 : adaptiveCoverCheck 4 cell2323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2323 (by decide +kernel)

private theorem checked000 : adaptiveCoverCheck 5 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 5 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 5 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 5 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 5 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 5 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 5 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 5 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 5 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 5 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 5 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 5 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 5 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 5 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 5 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 5 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell033 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 5 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 5 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 5 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 5 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell123 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 5 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 5 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 5 cell202 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell202
    checked2020 checked2021 checked2022 checked2023

private theorem checked203 : adaptiveCoverCheck 5 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 5 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 5 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 5 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 5 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 5 cell220 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell220
    checked2200 checked2201 checked2202 checked2203

private theorem checked221 : adaptiveCoverCheck 5 cell221 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell221
    checked2210 checked2211 checked2212 checked2213

private theorem checked222 : adaptiveCoverCheck 5 cell222 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell222
    checked2220 checked2221 checked2222 checked2223

private theorem checked223 : adaptiveCoverCheck 5 cell223 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell223
    checked2230 checked2231 checked2232 checked2233

private theorem checked230 : adaptiveCoverCheck 5 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 5 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 5 cell232 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell232
    checked2320 checked2321 checked2322 checked2323

private theorem checked233 : adaptiveCoverCheck 5 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 5 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 5 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 5 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 5 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 5 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 5 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 5 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 5 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 5 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 5 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 5 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 5 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 5 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 5 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 5 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 5 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 6 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 6 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 6 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 6 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 6 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 6 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 6 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 6 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 6 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 6 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 6 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 6 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 6 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 6 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 6 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 6 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 7 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 7 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 7 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 7 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 8 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateb1645a3287

theorem e24KC2PhiBelowLeaf33233_c3 :
    adaptiveCoverCheck 8 (childHH (childHH phiBelowCell3323)) = true := by
  exact CoverCertificateb1645a3287.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Below Leaf33233_9_00462
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells83d9ff7319

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))

end CertificateCells83d9ff7319

open CertificateCells83d9ff7319

theorem e24KC2PhiBelowLeaf33233 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3323) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childHH phiBelowCell3323)
    e24KC2PhiBelowLeaf33233_c0 e24KC2PhiBelowLeaf33233_c1 e24KC2PhiBelowLeaf33233_c2
      e24KC2PhiBelowLeaf33233_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC6Phi Below Reconstruct
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells240a9bf558

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3000` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3000 : AngleCell :=
  childLL (childLL (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3001` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3001 : AngleCell :=
  childLH (childLL (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3002` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3002 : AngleCell :=
  childHL (childLL (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3003` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3003 : AngleCell :=
  childHH (childLL (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3010` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3010 : AngleCell :=
  childLL (childLH (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3011` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3011 : AngleCell :=
  childLH (childLH (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3012` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3012 : AngleCell :=
  childHL (childLH (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3013` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3013 : AngleCell :=
  childHH (childLH (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3020` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3020 : AngleCell :=
  childLL (childHL (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3021` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3021 : AngleCell :=
  childLH (childHL (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3022` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3022 : AngleCell :=
  childHL (childHL (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3023` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3023 : AngleCell :=
  childHH (childHL (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3030` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3030 : AngleCell :=
  childLL (childHH (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3031` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3031 : AngleCell :=
  childLH (childHH (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3032` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3032 : AngleCell :=
  childHL (childHH (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3033` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3033 : AngleCell :=
  childHH (childHH (childLL (childHH e24PhiBelowRoot)))
/-- Subcell `3100` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3100 : AngleCell :=
  childLL (childLL (childLH (childHH e24PhiBelowRoot)))
/-- Subcell `3101` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3101 : AngleCell :=
  childLH (childLL (childLH (childHH e24PhiBelowRoot)))
/-- Subcell `3102` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3102 : AngleCell :=
  childHL (childLL (childLH (childHH e24PhiBelowRoot)))
/-- Subcell `3103` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3103 : AngleCell :=
  childHH (childLL (childLH (childHH e24PhiBelowRoot)))
/-- Subcell `3112` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3112 : AngleCell :=
  childHL (childLH (childLH (childHH e24PhiBelowRoot)))
/-- Subcell `3120` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3120 : AngleCell :=
  childLL (childHL (childLH (childHH e24PhiBelowRoot)))
/-- Subcell `3121` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3121 : AngleCell :=
  childLH (childHL (childLH (childHH e24PhiBelowRoot)))
/-- Subcell `3122` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3122 : AngleCell :=
  childHL (childHL (childLH (childHH e24PhiBelowRoot)))
/-- Subcell `3123` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3123 : AngleCell :=
  childHH (childHL (childLH (childHH e24PhiBelowRoot)))
/-- Subcell `3130` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3130 : AngleCell :=
  childLL (childHH (childLH (childHH e24PhiBelowRoot)))
/-- Subcell `3131` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3131 : AngleCell :=
  childLH (childHH (childLH (childHH e24PhiBelowRoot)))
/-- Subcell `3132` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3132 : AngleCell :=
  childHL (childHH (childLH (childHH e24PhiBelowRoot)))
/-- Subcell `3133` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3133 : AngleCell :=
  childHH (childHH (childLH (childHH e24PhiBelowRoot)))
/-- Subcell `3200` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3200 : AngleCell :=
  childLL (childLL (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3201` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3201 : AngleCell :=
  childLH (childLL (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3202` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3202 : AngleCell :=
  childHL (childLL (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3203` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3203 : AngleCell :=
  childHH (childLL (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3210` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3210 : AngleCell :=
  childLL (childLH (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3211` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3211 : AngleCell :=
  childLH (childLH (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3212` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3212 : AngleCell :=
  childHL (childLH (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3213` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3213 : AngleCell :=
  childHH (childLH (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3220` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3220 : AngleCell :=
  childLL (childHL (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3221` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3221 : AngleCell :=
  childLH (childHL (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3222` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3222 : AngleCell :=
  childHL (childHL (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3223 : AngleCell :=
  childHH (childHL (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3230` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3230 : AngleCell :=
  childLL (childHH (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3231` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3231 : AngleCell :=
  childLH (childHH (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3232` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3232 : AngleCell :=
  childHL (childHH (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3233` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3233 : AngleCell :=
  childHH (childHH (childHL (childHH e24PhiBelowRoot)))
/-- Subcell `3300` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3300 : AngleCell :=
  childLL (childLL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3301` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3301 : AngleCell :=
  childLH (childLL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3302` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3302 : AngleCell :=
  childHL (childLL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3303` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3303 : AngleCell :=
  childHH (childLL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3310` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3310 : AngleCell :=
  childLL (childLH (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3311` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3311 : AngleCell :=
  childLH (childLH (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3312` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3312 : AngleCell :=
  childHL (childLH (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3313` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3313 : AngleCell :=
  childHH (childLH (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3320` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3320 : AngleCell :=
  childLL (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3321` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3321 : AngleCell :=
  childLH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3322` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3322 : AngleCell :=
  childHL (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3323` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3323 : AngleCell :=
  childHH (childHL (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3330` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3330 : AngleCell :=
  childLL (childHH (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3331` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3331 : AngleCell :=
  childLH (childHH (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3332` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3332 : AngleCell :=
  childHL (childHH (childHH (childHH e24PhiBelowRoot)))
/-- Subcell `3333` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3333 : AngleCell :=
  childHH (childHH (childHH (childHH e24PhiBelowRoot)))

end CertificateCells240a9bf558

open CertificateCells240a9bf558

theorem e24KC2PhiBelowNode3000 :
    adaptiveCoverCheck 10 phiBelowCell3000 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3000
    e24KC2PhiBelowLeaf30000 e24KC2PhiBelowLeaf30001 e24KC2PhiBelowLeaf30002 e24KC2PhiBelowLeaf30003

theorem e24KC2PhiBelowNode3001 :
    adaptiveCoverCheck 10 phiBelowCell3001 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3001
    e24KC2PhiBelowLeaf30010 e24KC2PhiBelowLeaf30011 e24KC2PhiBelowLeaf30012 e24KC2PhiBelowLeaf30013

theorem e24KC2PhiBelowNode3002 :
    adaptiveCoverCheck 10 phiBelowCell3002 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3002
    e24KC2PhiBelowLeaf30020 e24KC2PhiBelowLeaf30021 e24KC2PhiBelowLeaf30022 e24KC2PhiBelowLeaf30023

theorem e24KC2PhiBelowNode3003 :
    adaptiveCoverCheck 10 phiBelowCell3003 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3003
    e24KC2PhiBelowLeaf30030 e24KC2PhiBelowLeaf30031 e24KC2PhiBelowLeaf30032 e24KC2PhiBelowLeaf30033

theorem e24KC2PhiBelowNode3010 :
    adaptiveCoverCheck 10 phiBelowCell3010 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3010
    e24KC2PhiBelowLeaf30100 e24KC2PhiBelowLeaf30101 e24KC2PhiBelowLeaf30102 e24KC2PhiBelowLeaf30103

theorem e24KC2PhiBelowNode3011 :
    adaptiveCoverCheck 10 phiBelowCell3011 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3011
    e24KC2PhiBelowLeaf30110 e24KC2PhiBelowLeaf30111 e24KC2PhiBelowLeaf30112 e24KC2PhiBelowLeaf30113

theorem e24KC2PhiBelowNode3012 :
    adaptiveCoverCheck 10 phiBelowCell3012 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3012
    e24KC2PhiBelowLeaf30120 e24KC2PhiBelowLeaf30121 e24KC2PhiBelowLeaf30122 e24KC2PhiBelowLeaf30123

theorem e24KC2PhiBelowNode3013 :
    adaptiveCoverCheck 10 phiBelowCell3013 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3013
    e24KC2PhiBelowLeaf30130 e24KC2PhiBelowLeaf30131 e24KC2PhiBelowLeaf30132 e24KC2PhiBelowLeaf30133

theorem e24KC2PhiBelowNode3020 :
    adaptiveCoverCheck 10 phiBelowCell3020 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3020
    e24KC2PhiBelowLeaf30200 e24KC2PhiBelowLeaf30201 e24KC2PhiBelowLeaf30202 e24KC2PhiBelowLeaf30203

theorem e24KC2PhiBelowNode3021 :
    adaptiveCoverCheck 10 phiBelowCell3021 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3021
    e24KC2PhiBelowLeaf30210 e24KC2PhiBelowLeaf30211 e24KC2PhiBelowLeaf30212 e24KC2PhiBelowLeaf30213

theorem e24KC2PhiBelowNode3022 :
    adaptiveCoverCheck 10 phiBelowCell3022 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3022
    e24KC2PhiBelowLeaf30220 e24KC2PhiBelowLeaf30221 e24KC2PhiBelowLeaf30222 e24KC2PhiBelowLeaf30223

theorem e24KC2PhiBelowNode3023 :
    adaptiveCoverCheck 10 phiBelowCell3023 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3023
    e24KC2PhiBelowLeaf30230 e24KC2PhiBelowLeaf30231 e24KC2PhiBelowLeaf30232 e24KC2PhiBelowLeaf30233

theorem e24KC2PhiBelowNode3030 :
    adaptiveCoverCheck 10 phiBelowCell3030 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3030
    e24KC2PhiBelowLeaf30300 e24KC2PhiBelowLeaf30301 e24KC2PhiBelowLeaf30302 e24KC2PhiBelowLeaf30303

theorem e24KC2PhiBelowNode3031 :
    adaptiveCoverCheck 10 phiBelowCell3031 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3031
    e24KC2PhiBelowLeaf30310 e24KC2PhiBelowLeaf30311 e24KC2PhiBelowLeaf30312 e24KC2PhiBelowLeaf30313

theorem e24KC2PhiBelowNode3032 :
    adaptiveCoverCheck 10 phiBelowCell3032 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3032
    e24KC2PhiBelowLeaf30320 e24KC2PhiBelowLeaf30321 e24KC2PhiBelowLeaf30322 e24KC2PhiBelowLeaf30323

theorem e24KC2PhiBelowNode3033 :
    adaptiveCoverCheck 10 phiBelowCell3033 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3033
    e24KC2PhiBelowLeaf30330 e24KC2PhiBelowLeaf30331 e24KC2PhiBelowLeaf30332 e24KC2PhiBelowLeaf30333

theorem e24KC2PhiBelowNode3100 :
    adaptiveCoverCheck 10 phiBelowCell3100 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3100
    e24KC2PhiBelowLeaf31000 e24KC2PhiBelowLeaf31001 e24KC2PhiBelowLeaf31002 e24KC2PhiBelowLeaf31003

theorem e24KC2PhiBelowNode3101 :
    adaptiveCoverCheck 10 phiBelowCell3101 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3101
    e24KC2PhiBelowLeaf31010 e24KC2PhiBelowLeaf31011 e24KC2PhiBelowLeaf31012 e24KC2PhiBelowLeaf31013

theorem e24KC2PhiBelowNode3102 :
    adaptiveCoverCheck 10 phiBelowCell3102 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3102
    e24KC2PhiBelowLeaf31020 e24KC2PhiBelowLeaf31021 e24KC2PhiBelowLeaf31022 e24KC2PhiBelowLeaf31023

theorem e24KC2PhiBelowNode3103 :
    adaptiveCoverCheck 10 phiBelowCell3103 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3103
    e24KC2PhiBelowLeaf31030 e24KC2PhiBelowLeaf31031 e24KC2PhiBelowLeaf31032 e24KC2PhiBelowLeaf31033

theorem e24KC2PhiBelowNode3112 :
    adaptiveCoverCheck 10 phiBelowCell3112 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3112
    e24KC2PhiBelowLeaf31120 e24KC2PhiBelowLeaf31121 e24KC2PhiBelowLeaf31122 e24KC2PhiBelowLeaf31123

theorem e24KC2PhiBelowNode3120 :
    adaptiveCoverCheck 10 phiBelowCell3120 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3120
    e24KC2PhiBelowLeaf31200 e24KC2PhiBelowLeaf31201 e24KC2PhiBelowLeaf31202 e24KC2PhiBelowLeaf31203

theorem e24KC2PhiBelowNode3121 :
    adaptiveCoverCheck 10 phiBelowCell3121 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3121
    e24KC2PhiBelowLeaf31210 e24KC2PhiBelowLeaf31211 e24KC2PhiBelowLeaf31212 e24KC2PhiBelowLeaf31213

theorem e24KC2PhiBelowNode3122 :
    adaptiveCoverCheck 10 phiBelowCell3122 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3122
    e24KC2PhiBelowLeaf31220 e24KC2PhiBelowLeaf31221 e24KC2PhiBelowLeaf31222 e24KC2PhiBelowLeaf31223

theorem e24KC2PhiBelowNode3123 :
    adaptiveCoverCheck 10 phiBelowCell3123 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3123
    e24KC2PhiBelowLeaf31230 e24KC2PhiBelowLeaf31231 e24KC2PhiBelowLeaf31232 e24KC2PhiBelowLeaf31233

theorem e24KC2PhiBelowNode3130 :
    adaptiveCoverCheck 10 phiBelowCell3130 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3130
    e24KC2PhiBelowLeaf31300 e24KC2PhiBelowLeaf31301 e24KC2PhiBelowLeaf31302 e24KC2PhiBelowLeaf31303

theorem e24KC2PhiBelowNode3131 :
    adaptiveCoverCheck 10 phiBelowCell3131 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3131
    e24KC2PhiBelowLeaf31310 e24KC2PhiBelowLeaf31311 e24KC2PhiBelowLeaf31312 e24KC2PhiBelowLeaf31313

theorem e24KC2PhiBelowNode3132 :
    adaptiveCoverCheck 10 phiBelowCell3132 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3132
    e24KC2PhiBelowLeaf31320 e24KC2PhiBelowLeaf31321 e24KC2PhiBelowLeaf31322 e24KC2PhiBelowLeaf31323

theorem e24KC2PhiBelowNode3133 :
    adaptiveCoverCheck 10 phiBelowCell3133 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3133
    e24KC2PhiBelowLeaf31330 e24KC2PhiBelowLeaf31331 e24KC2PhiBelowLeaf31332 e24KC2PhiBelowLeaf31333

theorem e24KC2PhiBelowNode3200 :
    adaptiveCoverCheck 10 phiBelowCell3200 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3200
    e24KC2PhiBelowLeaf32000 e24KC2PhiBelowLeaf32001 e24KC2PhiBelowLeaf32002 e24KC2PhiBelowLeaf32003

theorem e24KC2PhiBelowNode3201 :
    adaptiveCoverCheck 10 phiBelowCell3201 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3201
    e24KC2PhiBelowLeaf32010 e24KC2PhiBelowLeaf32011 e24KC2PhiBelowLeaf32012 e24KC2PhiBelowLeaf32013

theorem e24KC2PhiBelowNode3202 :
    adaptiveCoverCheck 10 phiBelowCell3202 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3202
    e24KC2PhiBelowLeaf32020 e24KC2PhiBelowLeaf32021 e24KC2PhiBelowLeaf32022 e24KC2PhiBelowLeaf32023

theorem e24KC2PhiBelowNode3203 :
    adaptiveCoverCheck 10 phiBelowCell3203 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3203
    e24KC2PhiBelowLeaf32030 e24KC2PhiBelowLeaf32031 e24KC2PhiBelowLeaf32032 e24KC2PhiBelowLeaf32033

theorem e24KC2PhiBelowNode3210 :
    adaptiveCoverCheck 10 phiBelowCell3210 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3210
    e24KC2PhiBelowLeaf32100 e24KC2PhiBelowLeaf32101 e24KC2PhiBelowLeaf32102 e24KC2PhiBelowLeaf32103

theorem e24KC2PhiBelowNode3211 :
    adaptiveCoverCheck 10 phiBelowCell3211 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3211
    e24KC2PhiBelowLeaf32110 e24KC2PhiBelowLeaf32111 e24KC2PhiBelowLeaf32112 e24KC2PhiBelowLeaf32113

theorem e24KC2PhiBelowNode3212 :
    adaptiveCoverCheck 10 phiBelowCell3212 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3212
    e24KC2PhiBelowLeaf32120 e24KC2PhiBelowLeaf32121 e24KC2PhiBelowLeaf32122 e24KC2PhiBelowLeaf32123

theorem e24KC2PhiBelowNode3213 :
    adaptiveCoverCheck 10 phiBelowCell3213 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3213
    e24KC2PhiBelowLeaf32130 e24KC2PhiBelowLeaf32131 e24KC2PhiBelowLeaf32132 e24KC2PhiBelowLeaf32133

theorem e24KC2PhiBelowNode3220 :
    adaptiveCoverCheck 10 phiBelowCell3220 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3220
    e24KC2PhiBelowLeaf32200 e24KC2PhiBelowLeaf32201 e24KC2PhiBelowLeaf32202 e24KC2PhiBelowLeaf32203

theorem e24KC2PhiBelowNode3221 :
    adaptiveCoverCheck 10 phiBelowCell3221 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3221
    e24KC2PhiBelowLeaf32210 e24KC2PhiBelowLeaf32211 e24KC2PhiBelowLeaf32212 e24KC2PhiBelowLeaf32213

theorem e24KC2PhiBelowNode3222 :
    adaptiveCoverCheck 10 phiBelowCell3222 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3222
    e24KC2PhiBelowLeaf32220 e24KC2PhiBelowLeaf32221 e24KC2PhiBelowLeaf32222 e24KC2PhiBelowLeaf32223

theorem e24KC2PhiBelowNode3223 :
    adaptiveCoverCheck 10 phiBelowCell3223 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3223
    e24KC2PhiBelowLeaf32230 e24KC2PhiBelowLeaf32231 e24KC2PhiBelowLeaf32232 e24KC2PhiBelowLeaf32233

theorem e24KC2PhiBelowNode3230 :
    adaptiveCoverCheck 10 phiBelowCell3230 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3230
    e24KC2PhiBelowLeaf32300 e24KC2PhiBelowLeaf32301 e24KC2PhiBelowLeaf32302 e24KC2PhiBelowLeaf32303

theorem e24KC2PhiBelowNode3231 :
    adaptiveCoverCheck 10 phiBelowCell3231 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3231
    e24KC2PhiBelowLeaf32310 e24KC2PhiBelowLeaf32311 e24KC2PhiBelowLeaf32312 e24KC2PhiBelowLeaf32313

theorem e24KC2PhiBelowNode3232 :
    adaptiveCoverCheck 10 phiBelowCell3232 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3232
    e24KC2PhiBelowLeaf32320 e24KC2PhiBelowLeaf32321 e24KC2PhiBelowLeaf32322 e24KC2PhiBelowLeaf32323

theorem e24KC2PhiBelowNode3233 :
    adaptiveCoverCheck 10 phiBelowCell3233 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3233
    e24KC2PhiBelowLeaf32330 e24KC2PhiBelowLeaf32331 e24KC2PhiBelowLeaf32332 e24KC2PhiBelowLeaf32333

theorem e24KC2PhiBelowNode3300 :
    adaptiveCoverCheck 10 phiBelowCell3300 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3300
    e24KC2PhiBelowLeaf33000 e24KC2PhiBelowLeaf33001 e24KC2PhiBelowLeaf33002 e24KC2PhiBelowLeaf33003

theorem e24KC2PhiBelowNode3301 :
    adaptiveCoverCheck 10 phiBelowCell3301 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3301
    e24KC2PhiBelowLeaf33010 e24KC2PhiBelowLeaf33011 e24KC2PhiBelowLeaf33012 e24KC2PhiBelowLeaf33013

theorem e24KC2PhiBelowNode3302 :
    adaptiveCoverCheck 10 phiBelowCell3302 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3302
    e24KC2PhiBelowLeaf33020 e24KC2PhiBelowLeaf33021 e24KC2PhiBelowLeaf33022 e24KC2PhiBelowLeaf33023

theorem e24KC2PhiBelowNode3303 :
    adaptiveCoverCheck 10 phiBelowCell3303 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3303
    e24KC2PhiBelowLeaf33030 e24KC2PhiBelowLeaf33031 e24KC2PhiBelowLeaf33032 e24KC2PhiBelowLeaf33033

theorem e24KC2PhiBelowNode3310 :
    adaptiveCoverCheck 10 phiBelowCell3310 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3310
    e24KC2PhiBelowLeaf33100 e24KC2PhiBelowLeaf33101 e24KC2PhiBelowLeaf33102 e24KC2PhiBelowLeaf33103

theorem e24KC2PhiBelowNode3311 :
    adaptiveCoverCheck 10 phiBelowCell3311 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3311
    e24KC2PhiBelowLeaf33110 e24KC2PhiBelowLeaf33111 e24KC2PhiBelowLeaf33112 e24KC2PhiBelowLeaf33113

theorem e24KC2PhiBelowNode3312 :
    adaptiveCoverCheck 10 phiBelowCell3312 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3312
    e24KC2PhiBelowLeaf33120 e24KC2PhiBelowLeaf33121 e24KC2PhiBelowLeaf33122 e24KC2PhiBelowLeaf33123

theorem e24KC2PhiBelowNode3313 :
    adaptiveCoverCheck 10 phiBelowCell3313 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3313
    e24KC2PhiBelowLeaf33130 e24KC2PhiBelowLeaf33131 e24KC2PhiBelowLeaf33132 e24KC2PhiBelowLeaf33133

theorem e24KC2PhiBelowNode3320 :
    adaptiveCoverCheck 10 phiBelowCell3320 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3320
    e24KC2PhiBelowLeaf33200 e24KC2PhiBelowLeaf33201 e24KC2PhiBelowLeaf33202 e24KC2PhiBelowLeaf33203

theorem e24KC2PhiBelowNode3321 :
    adaptiveCoverCheck 10 phiBelowCell3321 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3321
    e24KC2PhiBelowLeaf33210 e24KC2PhiBelowLeaf33211 e24KC2PhiBelowLeaf33212 e24KC2PhiBelowLeaf33213

theorem e24KC2PhiBelowNode3322 :
    adaptiveCoverCheck 10 phiBelowCell3322 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3322
    e24KC2PhiBelowLeaf33220 e24KC2PhiBelowLeaf33221 e24KC2PhiBelowLeaf33222 e24KC2PhiBelowLeaf33223

theorem e24KC2PhiBelowNode3323 :
    adaptiveCoverCheck 10 phiBelowCell3323 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3323
    e24KC2PhiBelowLeaf33230 e24KC2PhiBelowLeaf33231 e24KC2PhiBelowLeaf33232 e24KC2PhiBelowLeaf33233

theorem e24KC2PhiBelowNode3330 :
    adaptiveCoverCheck 10 phiBelowCell3330 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3330
    e24KC2PhiBelowLeaf33300 e24KC2PhiBelowLeaf33301 e24KC2PhiBelowLeaf33302 e24KC2PhiBelowLeaf33303

theorem e24KC2PhiBelowNode3331 :
    adaptiveCoverCheck 10 phiBelowCell3331 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3331
    e24KC2PhiBelowLeaf33310 e24KC2PhiBelowLeaf33311 e24KC2PhiBelowLeaf33312 e24KC2PhiBelowLeaf33313

theorem e24KC2PhiBelowNode3332 :
    adaptiveCoverCheck 10 phiBelowCell3332 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3332
    e24KC2PhiBelowLeaf33320 e24KC2PhiBelowLeaf33321 e24KC2PhiBelowLeaf33322 e24KC2PhiBelowLeaf33323

theorem e24KC2PhiBelowNode3333 :
    adaptiveCoverCheck 10 phiBelowCell3333 = true :=
  adaptiveCoverCheck_succ_of_children 9 phiBelowCell3333
    e24KC2PhiBelowLeaf33330 e24KC2PhiBelowLeaf33331 e24KC2PhiBelowLeaf33332 e24KC2PhiBelowLeaf33333

theorem e24KC2PhiBelowNode300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3000 e24KC2PhiBelowNode3001 e24KC2PhiBelowNode3002 e24KC2PhiBelowNode3003

theorem e24KC2PhiBelowNode301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3010 e24KC2PhiBelowNode3011 e24KC2PhiBelowNode3012 e24KC2PhiBelowNode3013

theorem e24KC2PhiBelowNode302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3020 e24KC2PhiBelowNode3021 e24KC2PhiBelowNode3022 e24KC2PhiBelowNode3023

theorem e24KC2PhiBelowNode303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3030 e24KC2PhiBelowNode3031 e24KC2PhiBelowNode3032 e24KC2PhiBelowNode3033

theorem e24KC2PhiBelowNode310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3100 e24KC2PhiBelowNode3101 e24KC2PhiBelowNode3102 e24KC2PhiBelowNode3103

theorem e24KC2PhiBelowNode311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowLeaf3110 e24KC2PhiBelowLeaf3111 e24KC2PhiBelowNode3112 e24KC2PhiBelowLeaf3113

theorem e24KC2PhiBelowNode312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3120 e24KC2PhiBelowNode3121 e24KC2PhiBelowNode3122 e24KC2PhiBelowNode3123

theorem e24KC2PhiBelowNode313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3130 e24KC2PhiBelowNode3131 e24KC2PhiBelowNode3132 e24KC2PhiBelowNode3133

theorem e24KC2PhiBelowNode320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3200 e24KC2PhiBelowNode3201 e24KC2PhiBelowNode3202 e24KC2PhiBelowNode3203

theorem e24KC2PhiBelowNode321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3210 e24KC2PhiBelowNode3211 e24KC2PhiBelowNode3212 e24KC2PhiBelowNode3213

theorem e24KC2PhiBelowNode322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3220 e24KC2PhiBelowNode3221 e24KC2PhiBelowNode3222 e24KC2PhiBelowNode3223

theorem e24KC2PhiBelowNode323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHL (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3230 e24KC2PhiBelowNode3231 e24KC2PhiBelowNode3232 e24KC2PhiBelowNode3233

theorem e24KC2PhiBelowNode330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3300 e24KC2PhiBelowNode3301 e24KC2PhiBelowNode3302 e24KC2PhiBelowNode3303

theorem e24KC2PhiBelowNode331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3310 e24KC2PhiBelowNode3311 e24KC2PhiBelowNode3312 e24KC2PhiBelowNode3313

theorem e24KC2PhiBelowNode332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3320 e24KC2PhiBelowNode3321 e24KC2PhiBelowNode3322 e24KC2PhiBelowNode3323

theorem e24KC2PhiBelowNode333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH e24PhiBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHH (childHH e24PhiBelowRoot)))
    e24KC2PhiBelowNode3330 e24KC2PhiBelowNode3331 e24KC2PhiBelowNode3332 e24KC2PhiBelowNode3333

theorem e24KC2PhiBelowNode30 :
    adaptiveCoverCheck 12 (childLL (childHH e24PhiBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH e24PhiBelowRoot))
    e24KC2PhiBelowNode300 e24KC2PhiBelowNode301 e24KC2PhiBelowNode302 e24KC2PhiBelowNode303

theorem e24KC2PhiBelowNode31 :
    adaptiveCoverCheck 12 (childLH (childHH e24PhiBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH e24PhiBelowRoot))
    e24KC2PhiBelowNode310 e24KC2PhiBelowNode311 e24KC2PhiBelowNode312 e24KC2PhiBelowNode313

theorem e24KC2PhiBelowNode32 :
    adaptiveCoverCheck 12 (childHL (childHH e24PhiBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH e24PhiBelowRoot))
    e24KC2PhiBelowNode320 e24KC2PhiBelowNode321 e24KC2PhiBelowNode322 e24KC2PhiBelowNode323

theorem e24KC2PhiBelowNode33 :
    adaptiveCoverCheck 12 (childHH (childHH e24PhiBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH e24PhiBelowRoot))
    e24KC2PhiBelowNode330 e24KC2PhiBelowNode331 e24KC2PhiBelowNode332 e24KC2PhiBelowNode333

theorem e24KC2PhiBelowNode3 :
    adaptiveCoverCheck 13 (childHH e24PhiBelowRoot) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH e24PhiBelowRoot)
    e24KC2PhiBelowNode30 e24KC2PhiBelowNode31 e24KC2PhiBelowNode32 e24KC2PhiBelowNode33

theorem e24KC2PhiBelowNodeROOT :
    adaptiveCoverCheck 14 e24PhiBelowRoot = true :=
  adaptiveCoverCheck_succ_of_children 13 e24PhiBelowRoot
    e24PhiBelowKernelLL e24PhiBelowKernelLH e24PhiBelowKernelHL e24KC2PhiBelowNode3

theorem e24PhiBelowKernelCheck :
    adaptiveCoverCheck 14 e24PhiBelowRoot = true :=
  e24KC2PhiBelowNodeROOT

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c0_4_00009
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd9f8181f0f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsd9f8181f0f

open CertificateCellsd9f8181f0f
namespace CoverCertificatef6f28b19e8






























private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatef6f28b19e8

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c0 :
    adaptiveCoverCheck 4 (childLL (childLH (childHH thetaAboveCell000022002011))) = true := by
  exact CoverCertificatef6f28b19e8.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c1_4_00010
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc3ac49754f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsc3ac49754f

open CertificateCellsc3ac49754f
namespace CoverCertificate15902c79ec






























private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate15902c79ec

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c1 :
    adaptiveCoverCheck 4 (childLH (childLH (childHH thetaAboveCell000022002011))) = true := by
  exact CoverCertificate15902c79ec.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c2_c0_3_00012
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa708f81b81

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022002011)))

end CertificateCellsa708f81b81

open CertificateCellsa708f81b81
namespace CoverCertificate36f48ed6fa






















private theorem checked00 : adaptiveCoverCheck 1 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 1 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 1 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 1 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 1 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 1 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 1 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 1 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 1 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 1 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 1 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 1 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 1 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 1 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 1 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 1 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate36f48ed6fa

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020113120 = true := by
  exact CoverCertificate36f48ed6fa.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c2_c1_3_00013
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd0cc56b48c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022002011)))

end CertificateCellsd0cc56b48c

open CertificateCellsd0cc56b48c
namespace CoverCertificate80e1d488d9






















private theorem checked00 : adaptiveCoverCheck 1 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 1 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 1 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 1 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 1 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 1 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 1 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 1 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 1 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 1 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 1 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 1 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 1 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 1 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 1 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 1 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate80e1d488d9

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020113121 = true := by
  exact CoverCertificate80e1d488d9.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c2_c2_3_00014
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsecda937af3

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022002011)))

end CertificateCellsecda937af3

open CertificateCellsecda937af3
namespace CoverCertificate24ddeb8618






private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate24ddeb8618

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020113122 = true := by
  exact CoverCertificate24ddeb8618.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c2_c3_3_00015
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsefa0cf83b9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022002011)))

end CertificateCellsefa0cf83b9

open CertificateCellsefa0cf83b9
namespace CoverCertificatea600465144






private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatea600465144

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020113123 = true := by
  exact CoverCertificatea600465144.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c2_4_00016
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells22695df69a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells22695df69a

open CertificateCells22695df69a

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022002011))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH thetaAboveCell000022002011)))
    e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2_c0
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2_c2
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c3_c0_3_00018
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells38fe0cae80

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022002011)))

end CertificateCells38fe0cae80

open CertificateCells38fe0cae80
namespace CoverCertificatefdcad14d68






















private theorem checked00 : adaptiveCoverCheck 1 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 1 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 1 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 1 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 1 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 1 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 1 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 1 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 1 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 1 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 1 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 1 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 1 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 1 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 1 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 1 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatefdcad14d68

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020113130 = true := by
  exact CoverCertificatefdcad14d68.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c3_c1_3_00019
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells32c7b8b1fa

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022002011)))

end CertificateCells32c7b8b1fa

open CertificateCells32c7b8b1fa
namespace CoverCertificate3ad1ac00a7






















private theorem checked00 : adaptiveCoverCheck 1 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 1 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 1 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 1 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 1 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 1 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 1 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 1 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 1 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 1 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 1 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 1 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 1 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 1 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 1 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 1 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3ad1ac00a7

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020113131 = true := by
  exact CoverCertificate3ad1ac00a7.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c3_c2_3_00020
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb136ba3941

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022002011)))

end CertificateCellsb136ba3941

open CertificateCellsb136ba3941
namespace CoverCertificatea3bd708439






private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatea3bd708439

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020113132 = true := by
  exact CoverCertificatea3bd708439.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c3_c3_3_00021
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8ac48dda13

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022002011)))

end CertificateCells8ac48dda13

open CertificateCells8ac48dda13
namespace CoverCertificateaf7d47a996






private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateaf7d47a996

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020113133 = true := by
  exact CoverCertificateaf7d47a996.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_c3_4_00022
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells782ac45202

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells782ac45202

open CertificateCells782ac45202

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022002011))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH thetaAboveCell000022002011)))
    e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3_c0
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3_c2
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c1_5_00023
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb8f48433cf

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsb8f48433cf

open CertificateCellsb8f48433cf

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022002011)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022002011))
    e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c0 e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c2 e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c2_5_00024
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsde5c2f11fb

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsde5c2f11fb

open CertificateCellsde5c2f11fb
namespace CoverCertificatec662ef9997






private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec662ef9997

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c2 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022002011)) = true := by
  exact CoverCertificatec662ef9997.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c1_c3_c3_5_00025
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc44d408296

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsc44d408296

open CertificateCellsc44d408296
namespace CoverCertificate32e68ad46a






private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate32e68ad46a

theorem e24KC2ThetaAboveLeaf0000220020_c1_c1_c3_c3 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022002011)) = true := by
  exact CoverCertificate32e68ad46a.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above Leaf0000220020_c1_c2_7_00028
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells057d5ed82d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells057d5ed82d

open CertificateCells057d5ed82d
namespace CoverCertificate713bbdaba3














private theorem checked00 : adaptiveCoverCheck 5 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 5 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 5 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 5 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 5 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 5 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 5 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 5 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate713bbdaba3

theorem e24KC2ThetaAboveLeaf0000220020_c1_c2 :
    adaptiveCoverCheck 7 thetaAboveCell000022002012 = true := by
  exact CoverCertificate713bbdaba3.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above Leaf0000220020_c1_c3_7_00029
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc56edf0af2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsc56edf0af2

open CertificateCellsc56edf0af2
namespace CoverCertificate5832573e8a














private theorem checked00 : adaptiveCoverCheck 5 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 5 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 5 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 5 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 5 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 5 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 5 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 5 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate5832573e8a

theorem e24KC2ThetaAboveLeaf0000220020_c1_c3 :
    adaptiveCoverCheck 7 thetaAboveCell000022002013 = true := by
  exact CoverCertificate5832573e8a.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c0_6_00475
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells38f587bebf

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells38f587bebf

open CertificateCells38f587bebf
namespace CoverCertificatec47ffcf2f2














private theorem checked20 : adaptiveCoverCheck 4 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 4 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 4 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 4 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 4 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 4 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 4 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 4 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 5 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 5 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 5 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 5 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 6 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec47ffcf2f2

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c0 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022002000) = true := by
  exact CoverCertificatec47ffcf2f2.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c1_6_00476
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc330c6667b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsc330c6667b

open CertificateCellsc330c6667b
namespace CoverCertificate535ad25afd














private theorem checked20 : adaptiveCoverCheck 4 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 4 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 4 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 4 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 4 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 4 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 4 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 4 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 5 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 5 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 5 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 5 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 6 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate535ad25afd

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c1 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022002000) = true := by
  exact CoverCertificate535ad25afd.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c0_c0_3_00480
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8addf3ec0f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022002000)))

end CertificateCells8addf3ec0f

open CertificateCells8addf3ec0f
namespace CoverCertificate746010fa88






private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate746010fa88

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002000 = true := by
  exact CoverCertificate746010fa88.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c0_c1_3_00481
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells06b0cdd59e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022002000)))

end CertificateCells06b0cdd59e

open CertificateCells06b0cdd59e
namespace CoverCertificate1f629121b3






private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate1f629121b3

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002001 = true := by
  exact CoverCertificate1f629121b3.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c0_c2_3_00482
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf1a599f1e1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022002000)))

end CertificateCellsf1a599f1e1

open CertificateCellsf1a599f1e1
namespace CoverCertificatec4d5c9280e






















































private theorem checked200 : adaptiveCoverCheck 0 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 0 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 0 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 0 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 0 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 0 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 0 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 0 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 0 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 0 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 0 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 0 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 0 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 0 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 0 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 0 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 0 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 0 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 0 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 0 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 0 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 0 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 0 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 0 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 0 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 0 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 0 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 0 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 0 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 0 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 0 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 0 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 1 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 1 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 1 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 1 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 1 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 1 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 1 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 1 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 1 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 1 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 1 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 1 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 1 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 1 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 1 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 1 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec4d5c9280e

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002002 = true := by
  exact CoverCertificatec4d5c9280e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c0_c3_3_00483
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells260222ce28

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022002000)))

end CertificateCells260222ce28

open CertificateCells260222ce28
namespace CoverCertificate68a7675d0f






















































private theorem checked200 : adaptiveCoverCheck 0 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 0 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 0 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 0 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 0 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 0 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 0 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 0 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 0 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 0 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 0 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 0 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 0 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 0 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 0 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 0 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 0 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 0 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 0 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 0 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 0 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 0 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 0 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 0 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 0 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 0 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 0 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 0 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 0 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 0 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 0 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 0 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 1 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 1 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 1 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 1 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 1 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 1 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 1 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 1 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 1 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 1 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 1 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 1 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 1 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 1 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 1 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 1 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate68a7675d0f

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002003 = true := by
  exact CoverCertificate68a7675d0f.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c0_4_00484
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5bc1aa1a31

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells5bc1aa1a31

open CertificateCells5bc1aa1a31

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0 :
    adaptiveCoverCheck 4 (childLL (childLL (childHL thetaAboveCell000022002000))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL thetaAboveCell000022002000)))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c1_c0_3_00486
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5c03b20b81

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022002000)))

end CertificateCells5c03b20b81

open CertificateCells5c03b20b81
namespace CoverCertificateaaac1ef041






private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateaaac1ef041

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002010 = true := by
  exact CoverCertificateaaac1ef041.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c1_c1_3_00487
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells36e0f7722b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022002000)))

end CertificateCells36e0f7722b

open CertificateCells36e0f7722b
namespace CoverCertificateeac308265d






private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateeac308265d

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002011 = true := by
  exact CoverCertificateeac308265d.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c1_c2_3_00488
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb7dd59a80a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022002000)))

end CertificateCellsb7dd59a80a

open CertificateCellsb7dd59a80a
namespace CoverCertificateee7e82afcc






















































private theorem checked200 : adaptiveCoverCheck 0 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 0 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 0 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 0 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 0 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 0 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 0 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 0 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 0 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 0 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 0 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 0 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 0 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 0 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 0 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 0 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 0 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 0 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 0 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 0 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 0 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 0 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 0 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 0 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 0 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 0 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 0 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 0 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 0 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 0 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 0 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 0 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 1 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 1 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 1 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 1 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 1 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 1 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 1 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 1 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 1 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 1 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 1 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 1 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 1 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 1 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 1 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 1 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateee7e82afcc

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002012 = true := by
  exact CoverCertificateee7e82afcc.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c1_c3_3_00489
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsef0079dc28

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022002000)))

end CertificateCellsef0079dc28

open CertificateCellsef0079dc28
namespace CoverCertificatec74fdabb9c






















































private theorem checked200 : adaptiveCoverCheck 0 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 0 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 0 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 0 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 0 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 0 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 0 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 0 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 0 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 0 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 0 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 0 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 0 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 0 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 0 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 0 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 0 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 0 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 0 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 0 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 0 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 0 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 0 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 0 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 0 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 0 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 0 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 0 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 0 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 0 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 0 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 0 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 1 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 1 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 1 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 1 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 1 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 1 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 1 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 1 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 1 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 1 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 1 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 1 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 1 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 1 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 1 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 1 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec74fdabb9c

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002013 = true := by
  exact CoverCertificatec74fdabb9c.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c1_4_00490
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells29b43c6eb7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells29b43c6eb7

open CertificateCells29b43c6eb7

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1 :
    adaptiveCoverCheck 4 (childLH (childLL (childHL thetaAboveCell000022002000))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL thetaAboveCell000022002000)))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c2_4_00491
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells58fa53de1e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells58fa53de1e

open CertificateCells58fa53de1e
namespace CoverCertificateb0390aea72






























private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateb0390aea72

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c2 :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022002000))) = true := by
  exact CoverCertificateb0390aea72.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_c3_4_00492
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5c48ba0580

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells5c48ba0580

open CertificateCells5c48ba0580
namespace CoverCertificate1f25ee1c58














































private theorem checked1000 : adaptiveCoverCheck 0 cell1000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1000 (by decide +kernel)

private theorem checked1001 : adaptiveCoverCheck 0 cell1001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1001 (by decide +kernel)

private theorem checked1002 : adaptiveCoverCheck 0 cell1002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1002 (by decide +kernel)

private theorem checked1003 : adaptiveCoverCheck 0 cell1003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1003 (by decide +kernel)

private theorem checked1010 : adaptiveCoverCheck 0 cell1010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1010 (by decide +kernel)

private theorem checked1011 : adaptiveCoverCheck 0 cell1011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1011 (by decide +kernel)

private theorem checked1012 : adaptiveCoverCheck 0 cell1012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1012 (by decide +kernel)

private theorem checked1013 : adaptiveCoverCheck 0 cell1013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1013 (by decide +kernel)

private theorem checked1100 : adaptiveCoverCheck 0 cell1100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1100 (by decide +kernel)

private theorem checked1101 : adaptiveCoverCheck 0 cell1101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1101 (by decide +kernel)

private theorem checked1102 : adaptiveCoverCheck 0 cell1102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1102 (by decide +kernel)

private theorem checked1103 : adaptiveCoverCheck 0 cell1103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1103 (by decide +kernel)

private theorem checked1110 : adaptiveCoverCheck 0 cell1110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1110 (by decide +kernel)

private theorem checked1111 : adaptiveCoverCheck 0 cell1111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1111 (by decide +kernel)

private theorem checked1112 : adaptiveCoverCheck 0 cell1112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1112 (by decide +kernel)

private theorem checked1113 : adaptiveCoverCheck 0 cell1113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1113 (by decide +kernel)

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell100
    checked1000 checked1001 checked1002 checked1003

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell101
    checked1010 checked1011 checked1012 checked1013

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell110
    checked1100 checked1101 checked1102 checked1103

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell111
    checked1110 checked1111 checked1112 checked1113

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate1f25ee1c58

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c3 :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022002000))) = true := by
  exact CoverCertificate1f25ee1c58.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c0_5_00493
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells64bf70ad53

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells64bf70ad53

open CertificateCells64bf70ad53

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022002000)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022002000))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c0 e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c2 e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_c0_c0_3_00496
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells35af4df13c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022002000)))

end CertificateCells35af4df13c

open CertificateCells35af4df13c
namespace CoverCertificate64365f01f0






private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate64365f01f0

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002100 = true := by
  exact CoverCertificate64365f01f0.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_c0_c1_3_00497
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsbb596d2a3e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022002000)))

end CertificateCellsbb596d2a3e

open CertificateCellsbb596d2a3e
namespace CoverCertificatea308b70bb8






private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatea308b70bb8

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002101 = true := by
  exact CoverCertificatea308b70bb8.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_c0_c2_3_00498
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8645eca0c5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022002000)))

end CertificateCells8645eca0c5

open CertificateCells8645eca0c5
namespace CoverCertificate181aa5f0fe






















































private theorem checked200 : adaptiveCoverCheck 0 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 0 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 0 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 0 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 0 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 0 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 0 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 0 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 0 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 0 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 0 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 0 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 0 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 0 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 0 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 0 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 0 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 0 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 0 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 0 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 0 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 0 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 0 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 0 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 0 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 0 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 0 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 0 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 0 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 0 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 0 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 0 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 1 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 1 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 1 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 1 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 1 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 1 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 1 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 1 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 1 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 1 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 1 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 1 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 1 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 1 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 1 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 1 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate181aa5f0fe

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002102 = true := by
  exact CoverCertificate181aa5f0fe.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_c0_c3_3_00499
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsbe94e44cff

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022002000)))

end CertificateCellsbe94e44cff

open CertificateCellsbe94e44cff
namespace CoverCertificatee52fd52368






















































private theorem checked200 : adaptiveCoverCheck 0 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 0 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 0 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 0 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 0 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 0 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 0 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 0 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 0 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 0 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 0 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 0 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 0 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 0 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 0 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 0 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 0 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 0 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 0 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 0 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 0 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 0 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 0 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 0 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 0 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 0 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 0 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 0 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 0 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 0 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 0 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 0 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 1 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 1 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 1 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 1 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 1 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 1 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 1 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 1 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 1 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 1 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 1 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 1 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 1 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 1 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 1 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 1 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatee52fd52368

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002103 = true := by
  exact CoverCertificatee52fd52368.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_c0_4_00500
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc935d550f9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsc935d550f9

open CertificateCellsc935d550f9

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0 :
    adaptiveCoverCheck 4 (childLL (childLH (childHL thetaAboveCell000022002000))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL thetaAboveCell000022002000)))
    e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_c1_c0_3_00502
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd01cbbb894

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell000022002000)))

end CertificateCellsd01cbbb894

open CertificateCellsd01cbbb894
namespace CoverCertificate5b77908b1d






private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate5b77908b1d

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c1_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002110 = true := by
  exact CoverCertificate5b77908b1d.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_c1_c1_3_00503
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells768f9f5a16

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell000022002000)))

end CertificateCells768f9f5a16

open CertificateCells768f9f5a16
namespace CoverCertificatea6ac82148c






private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatea6ac82148c

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c1_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002111 = true := by
  exact CoverCertificatea6ac82148c.checkedRoot

end PartE
end GerverSofa

end

end

end
