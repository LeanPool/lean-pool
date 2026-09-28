/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch042




/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.ThetaAbove.Leaf00567`.
* `KernelOnly.PartE.ThetaAbove.Leaf00568`.
* `KernelOnly.PartE.ThetaAbove.Join00569`.
* `KernelOnly.PartE.ThetaAbove.Leaf00572`.
* `KernelOnly.PartE.ThetaAbove.Leaf00573`.
* `KernelOnly.PartE.ThetaAbove.Leaf00574`.
* `KernelOnly.PartE.ThetaAbove.Leaf00575`.
* `KernelOnly.PartE.ThetaAbove.Join00576`.
* `KernelOnly.PartE.ThetaAbove.Leaf00577`.
* `KernelOnly.PartE.ThetaAbove.Leaf00578`.
* `KernelOnly.PartE.ThetaAbove.Leaf00579`.
* `KernelOnly.PartE.ThetaAbove.Join00580`.
* `KernelOnly.PartE.ThetaAbove.Leaf00581`.
* `KernelOnly.PartE.ThetaAbove.Leaf00582`.
* `KernelOnly.PartE.ThetaAbove.Join00583`.
* `KernelOnly.PartE.ThetaAbove.Leaf00586`.
* `KernelOnly.PartE.ThetaAbove.Leaf00587`.
* `KernelOnly.PartE.ThetaAbove.Leaf00588`.
* `KernelOnly.PartE.ThetaAbove.Leaf00589`.
* `KernelOnly.PartE.ThetaAbove.Join00590`.
* `KernelOnly.PartE.ThetaAbove.Leaf00592`.
* `KernelOnly.PartE.ThetaAbove.Leaf00593`.
* `KernelOnly.PartE.ThetaAbove.Leaf00594`.
* `KernelOnly.PartE.ThetaAbove.Leaf00595`.
* `KernelOnly.PartE.ThetaAbove.Join00596`.
* `KernelOnly.PartE.ThetaAbove.Leaf00597`.
* `KernelOnly.PartE.ThetaAbove.Leaf00598`.
* `KernelOnly.PartE.ThetaAbove.Join00599`.
* `KernelOnly.PartE.ThetaAbove.Join00600`.
* `KernelOnly.PartE.ThetaAbove.Leaf00601`.
* `KernelOnly.PartE.ThetaAbove.Leaf00602`.
* `KernelOnly.PartE.ThetaAbove.Join00603`.
* `KernelOnly.PartE.ThetaAbove.Leaf00606`.
* `KernelOnly.PartE.ThetaAbove.Leaf00607`.
* `KernelOnly.PartE.ThetaAbove.Leaf00610`.
* `KernelOnly.PartE.ThetaAbove.Leaf00611`.
* `KernelOnly.PartE.ThetaAbove.Leaf00612`.
* `KernelOnly.PartE.ThetaAbove.Leaf00613`.
* `KernelOnly.PartE.ThetaAbove.Join00614`.
* `KernelOnly.PartE.ThetaAbove.Leaf00616`.
* `KernelOnly.PartE.ThetaAbove.Leaf00617`.
* `KernelOnly.PartE.ThetaAbove.Leaf00618`.
* `KernelOnly.PartE.ThetaAbove.Leaf00619`.
* `KernelOnly.PartE.ThetaAbove.Join00620`.
* `KernelOnly.PartE.ThetaAbove.Leaf00621`.
* `KernelOnly.PartE.ThetaAbove.Leaf00622`.
* `KernelOnly.PartE.ThetaAbove.Join00623`.
* `KernelOnly.PartE.ThetaAbove.Leaf00626`.
* `KernelOnly.PartE.ThetaAbove.Leaf00627`.
* `KernelOnly.PartE.ThetaAbove.Leaf00628`.
* `KernelOnly.PartE.ThetaAbove.Leaf00629`.
* `KernelOnly.PartE.ThetaAbove.Join00630`.
* `KernelOnly.PartE.ThetaAbove.Leaf00632`.
* `KernelOnly.PartE.ThetaAbove.Leaf00633`.
* `KernelOnly.PartE.ThetaAbove.Leaf00634`.
* `KernelOnly.PartE.ThetaAbove.Leaf00635`.
* `KernelOnly.PartE.ThetaAbove.Join00636`.
* `KernelOnly.PartE.ThetaAbove.Leaf00637`.
* `KernelOnly.PartE.ThetaAbove.Leaf00638`.
* `KernelOnly.PartE.ThetaAbove.Join00639`.
* `KernelOnly.PartE.ThetaAbove.Join00640`.
-/

@[expose] public section

noncomputable section

namespace GerverSofa.PartE.CoverCertificate19031d0370

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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


private abbrev cell0000 : AngleCell :=
  childLL cell000


private abbrev cell0001 : AngleCell :=
  childLH cell000


private abbrev cell0002 : AngleCell :=
  childHL cell000


private abbrev cell0003 : AngleCell :=
  childHH cell000


private abbrev cell0010 : AngleCell :=
  childLL cell001


private abbrev cell0011 : AngleCell :=
  childLH cell001


private abbrev cell0012 : AngleCell :=
  childHL cell001


private abbrev cell0013 : AngleCell :=
  childHH cell001


private abbrev cell0100 : AngleCell :=
  childLL cell010


private abbrev cell0101 : AngleCell :=
  childLH cell010


private abbrev cell0102 : AngleCell :=
  childHL cell010


private abbrev cell0103 : AngleCell :=
  childHH cell010


private abbrev cell0110 : AngleCell :=
  childLL cell011


private abbrev cell0111 : AngleCell :=
  childLH cell011


private abbrev cell0112 : AngleCell :=
  childHL cell011


private abbrev cell0113 : AngleCell :=
  childHH cell011


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

end GerverSofa.PartE.CoverCertificate19031d0370

namespace GerverSofa.PartE.CoverCertificate30936f26ba

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate30936f26ba

namespace GerverSofa.PartE.CoverCertificate953a140331

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLH (childHL (childLH (childLL (childLL (childHL (childLL (childLL
    (childHL (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate953a140331

namespace GerverSofa.PartE.CoverCertificatec0f3040bb9

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLH (childHL (childLH (childLL (childLL (childHL (childLL (childLL
    (childHL (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))))


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

end GerverSofa.PartE.CoverCertificatec0f3040bb9

namespace GerverSofa.PartE.CoverCertificatec5d26eacb3

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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


private abbrev cell2300 : AngleCell :=
  childLL cell230


private abbrev cell2301 : AngleCell :=
  childLH cell230


private abbrev cell2302 : AngleCell :=
  childHL cell230


private abbrev cell2303 : AngleCell :=
  childHH cell230


private abbrev cell2310 : AngleCell :=
  childLL cell231


private abbrev cell2311 : AngleCell :=
  childLH cell231


private abbrev cell2312 : AngleCell :=
  childHL cell231


private abbrev cell2313 : AngleCell :=
  childHH cell231


private abbrev cell3200 : AngleCell :=
  childLL cell320


private abbrev cell3201 : AngleCell :=
  childLH cell320


private abbrev cell3202 : AngleCell :=
  childHL cell320


private abbrev cell3203 : AngleCell :=
  childHH cell320


private abbrev cell3210 : AngleCell :=
  childLL cell321


private abbrev cell3211 : AngleCell :=
  childLH cell321


private abbrev cell3212 : AngleCell :=
  childHL cell321


private abbrev cell3213 : AngleCell :=
  childHH cell321


private abbrev cell3300 : AngleCell :=
  childLL cell330


private abbrev cell3301 : AngleCell :=
  childLH cell330


private abbrev cell3302 : AngleCell :=
  childHL cell330


private abbrev cell3303 : AngleCell :=
  childHH cell330


private abbrev cell3310 : AngleCell :=
  childLL cell331


private abbrev cell3311 : AngleCell :=
  childLH cell331


private abbrev cell3312 : AngleCell :=
  childHL cell331


private abbrev cell3313 : AngleCell :=
  childHH cell331

end GerverSofa.PartE.CoverCertificatec5d26eacb3

namespace GerverSofa.PartE.CoverCertificate3612aa63be

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate3612aa63be

namespace GerverSofa.PartE.CoverCertificateba32fc9e0a

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificateba32fc9e0a

namespace GerverSofa.PartE.CoverCertificate2170ad4ca0

private abbrev cellRoot : AngleCell :=
  (childHL (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate2170ad4ca0

namespace GerverSofa.PartE.CoverCertificate513511aa15

private abbrev cellRoot : AngleCell :=
  (childHH (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate513511aa15

namespace GerverSofa.PartE.CoverCertificate3743e2f873

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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


private abbrev cell2300 : AngleCell :=
  childLL cell230


private abbrev cell2301 : AngleCell :=
  childLH cell230


private abbrev cell2302 : AngleCell :=
  childHL cell230


private abbrev cell2303 : AngleCell :=
  childHH cell230

end GerverSofa.PartE.CoverCertificate3743e2f873

namespace GerverSofa.PartE.CoverCertificate3e2742ca77

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate3e2742ca77

namespace GerverSofa.PartE.CoverCertificate05d280259b

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate05d280259b

namespace GerverSofa.PartE.CoverCertificate73ec5d89dc

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate73ec5d89dc

namespace GerverSofa.PartE.CoverCertificated1fc30835b

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificated1fc30835b

namespace GerverSofa.PartE.CoverCertificatec03bec1842

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificatec03bec1842

namespace GerverSofa.PartE.CoverCertificate854ce4fcce

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate854ce4fcce

namespace GerverSofa.PartE.CoverCertificate756063c6fb

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate756063c6fb

namespace GerverSofa.PartE.CoverCertificatebb637b4eef

private abbrev cellRoot : AngleCell :=
  (childHL (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatebb637b4eef

namespace GerverSofa.PartE.CoverCertificate7fa5919613

private abbrev cellRoot : AngleCell :=
  (childHH (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate7fa5919613

namespace GerverSofa.PartE.CoverCertificateb766a036ce

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL
    (childLL (childLL (e24ThetaAboveRoot)))))))))))))


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

end GerverSofa.PartE.CoverCertificateb766a036ce

namespace GerverSofa.PartE.CoverCertificate61295956d2

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL
    (childLL (childLL (e24ThetaAboveRoot)))))))))))))


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

end GerverSofa.PartE.CoverCertificate61295956d2

namespace GerverSofa.PartE.CoverCertificate828511f0b8

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLL
    (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))


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

end GerverSofa.PartE.CoverCertificate828511f0b8

namespace GerverSofa.PartE.CoverCertificated54c339469

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLL
    (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))


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

end GerverSofa.PartE.CoverCertificated54c339469

namespace GerverSofa.PartE.CoverCertificate4dd8dcfac0

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate4dd8dcfac0

namespace GerverSofa.PartE.CoverCertificate4ee27c37fd

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate4ee27c37fd

namespace GerverSofa.PartE.CoverCertificated7b655454c

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificated7b655454c

namespace GerverSofa.PartE.CoverCertificate34bc1a6525

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate34bc1a6525

namespace GerverSofa.PartE.CoverCertificate6e40ca0512

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate6e40ca0512

namespace GerverSofa.PartE.CoverCertificateefd035cf65

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificateefd035cf65

namespace GerverSofa.PartE.CoverCertificatea4b667aaa0

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificatea4b667aaa0

namespace GerverSofa.PartE.CoverCertificateccad0dc048

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificateccad0dc048

namespace GerverSofa.PartE.CoverCertificate89deca0334

private abbrev cellRoot : AngleCell :=
  (childHL (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate89deca0334

namespace GerverSofa.PartE.CoverCertificate8778f820bd

private abbrev cellRoot : AngleCell :=
  (childHH (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate8778f820bd

namespace GerverSofa.PartE.CoverCertificatef14d24461a

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificatef14d24461a

namespace GerverSofa.PartE.CoverCertificate79980b2e6c

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate79980b2e6c

namespace GerverSofa.PartE.CoverCertificateed2ff1f24e

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificateed2ff1f24e

namespace GerverSofa.PartE.CoverCertificate4bcf50db3e

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificate4bcf50db3e

namespace GerverSofa.PartE.CoverCertificate1e4788169b

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate1e4788169b

namespace GerverSofa.PartE.CoverCertificate4f5a63a5df

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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

end GerverSofa.PartE.CoverCertificate4f5a63a5df

namespace GerverSofa.PartE.CoverCertificate89bb9fd21e

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificate89bb9fd21e

namespace GerverSofa.PartE.CoverCertificate5c80136736

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificate5c80136736

namespace GerverSofa.PartE.CoverCertificate645f79320a

private abbrev cellRoot : AngleCell :=
  (childHL (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate645f79320a

namespace GerverSofa.PartE.CoverCertificate3e0a4a2c6f

private abbrev cellRoot : AngleCell :=
  (childHH (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate3e0a4a2c6f

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c2_4_00567
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6deb17ad88

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells6deb17ad88

open CertificateCells6deb17ad88
namespace CoverCertificate19031d0370






















































private theorem checked0000 : adaptiveCoverCheck 0 cell0000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0000 (by decide +kernel)

private theorem checked0001 : adaptiveCoverCheck 0 cell0001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0001 (by decide +kernel)

private theorem checked0002 : adaptiveCoverCheck 0 cell0002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0002 (by decide +kernel)

private theorem checked0003 : adaptiveCoverCheck 0 cell0003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0003 (by decide +kernel)

private theorem checked0010 : adaptiveCoverCheck 0 cell0010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0010 (by decide +kernel)

private theorem checked0011 : adaptiveCoverCheck 0 cell0011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0011 (by decide +kernel)

private theorem checked0012 : adaptiveCoverCheck 0 cell0012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0012 (by decide +kernel)

private theorem checked0013 : adaptiveCoverCheck 0 cell0013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0013 (by decide +kernel)

private theorem checked0100 : adaptiveCoverCheck 0 cell0100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0100 (by decide +kernel)

private theorem checked0101 : adaptiveCoverCheck 0 cell0101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0101 (by decide +kernel)

private theorem checked0102 : adaptiveCoverCheck 0 cell0102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0102 (by decide +kernel)

private theorem checked0103 : adaptiveCoverCheck 0 cell0103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0103 (by decide +kernel)

private theorem checked0110 : adaptiveCoverCheck 0 cell0110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0110 (by decide +kernel)

private theorem checked0111 : adaptiveCoverCheck 0 cell0111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0111 (by decide +kernel)

private theorem checked0112 : adaptiveCoverCheck 0 cell0112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0112 (by decide +kernel)

private theorem checked0113 : adaptiveCoverCheck 0 cell0113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0113 (by decide +kernel)

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

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell000
    checked0000 checked0001 checked0002 checked0003

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell001
    checked0010 checked0011 checked0012 checked0013

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell010
    checked0100 checked0101 checked0102 checked0103

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell011
    checked0110 checked0111 checked0112 checked0113

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

end CoverCertificate19031d0370

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c2 :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022002001))) = true := by
  exact CoverCertificate19031d0370.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c3_4_00568
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells21b7c7dcb8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells21b7c7dcb8

open CertificateCells21b7c7dcb8
namespace CoverCertificate30936f26ba






























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

end CoverCertificate30936f26ba

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c3 :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022002001))) = true := by
  exact CoverCertificate30936f26ba.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_5_00569
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb9eba9ae01

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsb9eba9ae01

open CertificateCellsb9eba9ae01

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022002001)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022002001))
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c0_c0_3_00572
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells51629e8703

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020012100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022002001)))

end CertificateCells51629e8703

open CertificateCells51629e8703
theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012100 = true := by
  decide +kernel

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c0_c1_3_00573
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse4c4271ea3

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020012101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022002001)))

end CertificateCellse4c4271ea3

open CertificateCellse4c4271ea3
theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012101 = true := by
  decide +kernel

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c0_c2_3_00574
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells07d8bdd7d9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020012102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022002001)))

end CertificateCells07d8bdd7d9

open CertificateCells07d8bdd7d9
namespace CoverCertificate953a140331






















































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

end CoverCertificate953a140331

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012102 = true := by
  exact CoverCertificate953a140331.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c0_c3_3_00575
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2bf9eb5708

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))
/-- Subcell `0000220020012103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022002001)))

end CertificateCells2bf9eb5708

open CertificateCells2bf9eb5708
namespace CoverCertificatec0f3040bb9


































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

private theorem checked00 : adaptiveCoverCheck 1 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 1 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 1 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 1 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell03 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 1 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 1 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 1 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 1 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 1 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 1 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 1 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 1 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec0f3040bb9

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012103 = true := by
  exact CoverCertificatec0f3040bb9.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c0_4_00576
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5ae8bbaf2e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells5ae8bbaf2e

open CertificateCells5ae8bbaf2e

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0 :
    adaptiveCoverCheck 4 (childLL (childLH (childHL thetaAboveCell000022002001))) = true :=
  adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL thetaAboveCell000022002001)))
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c0
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c2
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c1_4_00577
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells7eefa0b856

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells7eefa0b856

open CertificateCells7eefa0b856
namespace CoverCertificatec5d26eacb3






























































private theorem checked2200 : adaptiveCoverCheck 0 cell2200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2200 (by decide +kernel)

private theorem checked2201 : adaptiveCoverCheck 0 cell2201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2201 (by decide +kernel)

private theorem checked2202 : adaptiveCoverCheck 0 cell2202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2202 (by decide +kernel)

private theorem checked2203 : adaptiveCoverCheck 0 cell2203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2203 (by decide +kernel)

private theorem checked2210 : adaptiveCoverCheck 0 cell2210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2210 (by decide +kernel)

private theorem checked2211 : adaptiveCoverCheck 0 cell2211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2211 (by decide +kernel)

private theorem checked2212 : adaptiveCoverCheck 0 cell2212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2212 (by decide +kernel)

private theorem checked2213 : adaptiveCoverCheck 0 cell2213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2213 (by decide +kernel)

private theorem checked2300 : adaptiveCoverCheck 0 cell2300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2300 (by decide +kernel)

private theorem checked2301 : adaptiveCoverCheck 0 cell2301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2301 (by decide +kernel)

private theorem checked2302 : adaptiveCoverCheck 0 cell2302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2302 (by decide +kernel)

private theorem checked2303 : adaptiveCoverCheck 0 cell2303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2303 (by decide +kernel)

private theorem checked2310 : adaptiveCoverCheck 0 cell2310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2310 (by decide +kernel)

private theorem checked2311 : adaptiveCoverCheck 0 cell2311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2311 (by decide +kernel)

private theorem checked2312 : adaptiveCoverCheck 0 cell2312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2312 (by decide +kernel)

private theorem checked2313 : adaptiveCoverCheck 0 cell2313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2313 (by decide +kernel)

private theorem checked3200 : adaptiveCoverCheck 0 cell3200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3200 (by decide +kernel)

private theorem checked3201 : adaptiveCoverCheck 0 cell3201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3201 (by decide +kernel)

private theorem checked3202 : adaptiveCoverCheck 0 cell3202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3202 (by decide +kernel)

private theorem checked3203 : adaptiveCoverCheck 0 cell3203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3203 (by decide +kernel)

private theorem checked3210 : adaptiveCoverCheck 0 cell3210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3210 (by decide +kernel)

private theorem checked3211 : adaptiveCoverCheck 0 cell3211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3211 (by decide +kernel)

private theorem checked3212 : adaptiveCoverCheck 0 cell3212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3212 (by decide +kernel)

private theorem checked3213 : adaptiveCoverCheck 0 cell3213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3213 (by decide +kernel)

private theorem checked3300 : adaptiveCoverCheck 0 cell3300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3300 (by decide +kernel)

private theorem checked3301 : adaptiveCoverCheck 0 cell3301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3301 (by decide +kernel)

private theorem checked3302 : adaptiveCoverCheck 0 cell3302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3302 (by decide +kernel)

private theorem checked3303 : adaptiveCoverCheck 0 cell3303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3303 (by decide +kernel)

private theorem checked3310 : adaptiveCoverCheck 0 cell3310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3310 (by decide +kernel)

private theorem checked3311 : adaptiveCoverCheck 0 cell3311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3311 (by decide +kernel)

private theorem checked3312 : adaptiveCoverCheck 0 cell3312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3312 (by decide +kernel)

private theorem checked3313 : adaptiveCoverCheck 0 cell3313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3313 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell220
    checked2200 checked2201 checked2202 checked2203

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell221
    checked2210 checked2211 checked2212 checked2213

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell230
    checked2300 checked2301 checked2302 checked2303

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell231
    checked2310 checked2311 checked2312 checked2313

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell320
    checked3200 checked3201 checked3202 checked3203

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell321
    checked3210 checked3211 checked3212 checked3213

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell330
    checked3300 checked3301 checked3302 checked3303

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell331
    checked3310 checked3311 checked3312 checked3313

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

end CoverCertificatec5d26eacb3

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c1 :
    adaptiveCoverCheck 4 (childLH (childLH (childHL thetaAboveCell000022002001))) = true := by
  exact CoverCertificatec5d26eacb3.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c2_4_00578
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdb6ef42c13

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsdb6ef42c13

open CertificateCellsdb6ef42c13
namespace CoverCertificate3612aa63be






























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

end CoverCertificate3612aa63be

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022002001))) = true := by
  exact CoverCertificate3612aa63be.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c3_4_00579
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells91885e0374

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells91885e0374

open CertificateCells91885e0374
namespace CoverCertificateba32fc9e0a






























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

end CoverCertificateba32fc9e0a

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c3 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022002001))) = true := by
  exact CoverCertificateba32fc9e0a.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_5_00580
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsbec28e0304

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsbec28e0304

open CertificateCellsbec28e0304

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022002001)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022002001))
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c2_5_00581
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsba71b1d520

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsba71b1d520

open CertificateCellsba71b1d520
namespace CoverCertificate2170ad4ca0






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

end CoverCertificate2170ad4ca0

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c2 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022002001)) = true := by
  exact CoverCertificate2170ad4ca0.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c3_5_00582
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells54caf0dec0

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells54caf0dec0

open CertificateCells54caf0dec0
namespace CoverCertificate513511aa15






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

end CoverCertificate513511aa15

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c3 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022002001)) = true := by
  exact CoverCertificate513511aa15.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c0_c1_c2_6_00583
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1b578c3d10

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells1b578c3d10

open CertificateCells1b578c3d10

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022002001) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022002001)
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c0_c0_4_00586
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells22ecf07105

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells22ecf07105

open CertificateCells22ecf07105
namespace CoverCertificate3743e2f873










































private theorem checked2200 : adaptiveCoverCheck 0 cell2200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2200 (by decide +kernel)

private theorem checked2201 : adaptiveCoverCheck 0 cell2201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2201 (by decide +kernel)

private theorem checked2202 : adaptiveCoverCheck 0 cell2202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2202 (by decide +kernel)

private theorem checked2203 : adaptiveCoverCheck 0 cell2203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2203 (by decide +kernel)

private theorem checked2210 : adaptiveCoverCheck 0 cell2210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2210 (by decide +kernel)

private theorem checked2211 : adaptiveCoverCheck 0 cell2211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2211 (by decide +kernel)

private theorem checked2212 : adaptiveCoverCheck 0 cell2212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2212 (by decide +kernel)

private theorem checked2213 : adaptiveCoverCheck 0 cell2213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2213 (by decide +kernel)

private theorem checked2300 : adaptiveCoverCheck 0 cell2300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2300 (by decide +kernel)

private theorem checked2301 : adaptiveCoverCheck 0 cell2301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2301 (by decide +kernel)

private theorem checked2302 : adaptiveCoverCheck 0 cell2302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2302 (by decide +kernel)

private theorem checked2303 : adaptiveCoverCheck 0 cell2303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2303 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell220
    checked2200 checked2201 checked2202 checked2203

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell221
    checked2210 checked2211 checked2212 checked2213

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell230
    checked2300 checked2301 checked2302 checked2303

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

end CoverCertificate3743e2f873

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c0 :
    adaptiveCoverCheck 4 (childLL (childLL (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificate3743e2f873.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c0_c1_4_00587
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2d236bc977

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells2d236bc977

open CertificateCells2d236bc977
namespace CoverCertificate3e2742ca77






























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

end CoverCertificate3e2742ca77

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c1 :
    adaptiveCoverCheck 4 (childLH (childLL (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificate3e2742ca77.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c0_c2_4_00588
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsfbf08c6815

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsfbf08c6815

open CertificateCellsfbf08c6815
namespace CoverCertificate05d280259b






























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

end CoverCertificate05d280259b

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c2 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificate05d280259b.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c0_c3_4_00589
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb2588049db

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsb2588049db

open CertificateCellsb2588049db
namespace CoverCertificate73ec5d89dc






























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

end CoverCertificate73ec5d89dc

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c3 :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificate73ec5d89dc.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c0_5_00590
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2bc65b7190

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells2bc65b7190

open CertificateCells2bc65b7190

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022002001)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022002001))
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c1_c0_4_00592
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells80702a4342

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells80702a4342

open CertificateCells80702a4342
namespace CoverCertificated1fc30835b






























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

end CoverCertificated1fc30835b

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c0 :
    adaptiveCoverCheck 4 (childLL (childLH (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificated1fc30835b.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c1_c1_4_00593
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsfcacd99e70

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsfcacd99e70

open CertificateCellsfcacd99e70
namespace CoverCertificatec03bec1842






























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

end CoverCertificatec03bec1842

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c1 :
    adaptiveCoverCheck 4 (childLH (childLH (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificatec03bec1842.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c1_c2_4_00594
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc63c49e043

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsc63c49e043

open CertificateCellsc63c49e043
namespace CoverCertificate854ce4fcce






























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

end CoverCertificate854ce4fcce

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificate854ce4fcce.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c1_c3_4_00595
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse2c2881509

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCellse2c2881509

open CertificateCellse2c2881509
namespace CoverCertificate756063c6fb






























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

end CoverCertificate756063c6fb

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c3 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificate756063c6fb.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c1_5_00596
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc46dbfc77b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsc46dbfc77b

open CertificateCellsc46dbfc77b

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022002001)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022002001))
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c2_5_00597
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1273bfc545

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells1273bfc545

open CertificateCells1273bfc545
namespace CoverCertificatebb637b4eef






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

end CoverCertificatebb637b4eef

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c2 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022002001)) = true := by
  exact CoverCertificatebb637b4eef.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c3_5_00598
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells758d72a450

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells758d72a450

open CertificateCells758d72a450
namespace CoverCertificate7fa5919613






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

end CoverCertificate7fa5919613

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c3 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022002001)) = true := by
  exact CoverCertificate7fa5919613.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c0_c1_c3_6_00599
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells752b604750

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells752b604750

open CertificateCells752b604750

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022002001) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022002001)
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c0_c1_7_00600
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse66f3ce3f5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCellse66f3ce3f5

open CertificateCellse66f3ce3f5

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1 :
    adaptiveCoverCheck 7 thetaAboveCell000022002001 = true :=
  adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002001
    e24KC2ThetaAboveLeaf0000220020_c0_c1_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c1_c2 e24KC2ThetaAboveLeaf0000220020_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above Leaf0000220020_c0_c2_7_00601
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells898eeb07c6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells898eeb07c6

open CertificateCells898eeb07c6
namespace CoverCertificateb766a036ce














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

end CoverCertificateb766a036ce

theorem e24KC2ThetaAboveLeaf0000220020_c0_c2 :
    adaptiveCoverCheck 7 thetaAboveCell000022002002 = true := by
  exact CoverCertificateb766a036ce.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above Leaf0000220020_c0_c3_7_00602
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3b9ec898a9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00002200)))

end CertificateCells3b9ec898a9

open CertificateCells3b9ec898a9
namespace CoverCertificate61295956d2














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

end CoverCertificate61295956d2

theorem e24KC2ThetaAboveLeaf0000220020_c0_c3 :
    adaptiveCoverCheck 7 thetaAboveCell000022002003 = true := by
  exact CoverCertificate61295956d2.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c0_8_00603
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells45a373af38

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

end CertificateCells45a373af38

open CertificateCells45a373af38

theorem e24KC2ThetaAboveLeaf0000220020_c0 :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00002200))) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00002200)))
    e24KC2ThetaAboveLeaf0000220020_c0_c0 e24KC2ThetaAboveLeaf0000220020_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c0_c2 e24KC2ThetaAboveLeaf0000220020_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c0_6_00606
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellscbef0a66a7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellscbef0a66a7

open CertificateCellscbef0a66a7
namespace CoverCertificate828511f0b8














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

end CoverCertificate828511f0b8

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c0 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022002010) = true := by
  exact CoverCertificate828511f0b8.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c1_6_00607
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0e30799078

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells0e30799078

open CertificateCells0e30799078
namespace CoverCertificated54c339469














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

end CoverCertificated54c339469

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c1 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022002010) = true := by
  exact CoverCertificated54c339469.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c0_c0_4_00610
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsaa7ab31314

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsaa7ab31314

open CertificateCellsaa7ab31314
namespace CoverCertificate4dd8dcfac0






























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

end CoverCertificate4dd8dcfac0

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c0 :
    adaptiveCoverCheck 4 (childLL (childLL (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificate4dd8dcfac0.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c0_c1_4_00611
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa4a7cbe7b2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsa4a7cbe7b2

open CertificateCellsa4a7cbe7b2
namespace CoverCertificate4ee27c37fd






























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

end CoverCertificate4ee27c37fd

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c1 :
    adaptiveCoverCheck 4 (childLH (childLL (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificate4ee27c37fd.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c0_c2_4_00612
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9f358cc74d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells9f358cc74d

open CertificateCells9f358cc74d
namespace CoverCertificated7b655454c






























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

end CoverCertificated7b655454c

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c2 :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificated7b655454c.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c0_c3_4_00613
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf2bd9cd8f9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsf2bd9cd8f9

open CertificateCellsf2bd9cd8f9
namespace CoverCertificate34bc1a6525






























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

end CoverCertificate34bc1a6525

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c3 :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificate34bc1a6525.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c0_5_00614
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdabf824b24

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsdabf824b24

open CertificateCellsdabf824b24

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022002010)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022002010))
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c1_c0_4_00616
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse30fe464b6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellse30fe464b6

open CertificateCellse30fe464b6
namespace CoverCertificate6e40ca0512






























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

end CoverCertificate6e40ca0512

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c0 :
    adaptiveCoverCheck 4 (childLL (childLH (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificate6e40ca0512.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c1_c1_4_00617
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells50e57ae8a7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells50e57ae8a7

open CertificateCells50e57ae8a7
namespace CoverCertificateefd035cf65






























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

end CoverCertificateefd035cf65

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c1 :
    adaptiveCoverCheck 4 (childLH (childLH (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificateefd035cf65.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c1_c2_4_00618
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6831b5295c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells6831b5295c

open CertificateCells6831b5295c
namespace CoverCertificatea4b667aaa0






























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

end CoverCertificatea4b667aaa0

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificatea4b667aaa0.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c1_c3_4_00619
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6ec7ee0b32

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells6ec7ee0b32

open CertificateCells6ec7ee0b32
namespace CoverCertificateccad0dc048










































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

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

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

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

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

end CoverCertificateccad0dc048

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c3 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificateccad0dc048.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c1_5_00620
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells11c2c46ea8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells11c2c46ea8

open CertificateCells11c2c46ea8

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022002010)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022002010))
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c2_5_00621
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellscdb025ab65

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellscdb025ab65

open CertificateCellscdb025ab65
namespace CoverCertificate89deca0334






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

end CoverCertificate89deca0334

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c2 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022002010)) = true := by
  exact CoverCertificate89deca0334.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c3_5_00622
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells251eb00cd5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells251eb00cd5

open CertificateCells251eb00cd5
namespace CoverCertificate8778f820bd






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

end CoverCertificate8778f820bd

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c3 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022002010)) = true := by
  exact CoverCertificate8778f820bd.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c1_c0_c2_6_00623
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsfc2738963a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsfc2738963a

open CertificateCellsfc2738963a

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022002010) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022002010)
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c0_c0_4_00626
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb46fd93863

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsb46fd93863

open CertificateCellsb46fd93863
namespace CoverCertificatef14d24461a






























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

end CoverCertificatef14d24461a

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c0 :
    adaptiveCoverCheck 4 (childLL (childLL (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificatef14d24461a.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c0_c1_4_00627
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells02c02b7fd3

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells02c02b7fd3

open CertificateCells02c02b7fd3
namespace CoverCertificate79980b2e6c






























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

end CoverCertificate79980b2e6c

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c1 :
    adaptiveCoverCheck 4 (childLH (childLL (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificate79980b2e6c.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c0_c2_4_00628
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells969e2199d5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells969e2199d5

open CertificateCells969e2199d5
namespace CoverCertificateed2ff1f24e














































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

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

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

end CoverCertificateed2ff1f24e

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c2 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificateed2ff1f24e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c0_c3_4_00629
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells99f6185557

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells99f6185557

open CertificateCells99f6185557
namespace CoverCertificate4bcf50db3e














































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

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

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

end CoverCertificate4bcf50db3e

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c3 :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificate4bcf50db3e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c0_5_00630
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2c3b2a68a2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells2c3b2a68a2

open CertificateCells2c3b2a68a2

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022002010)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022002010))
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c1_c0_4_00632
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsea3eb05dc6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsea3eb05dc6

open CertificateCellsea3eb05dc6
namespace CoverCertificate1e4788169b






























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

end CoverCertificate1e4788169b

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c0 :
    adaptiveCoverCheck 4 (childLL (childLH (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificate1e4788169b.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c1_c1_4_00633
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1daa3566d0

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells1daa3566d0

open CertificateCells1daa3566d0
namespace CoverCertificate4f5a63a5df






























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

end CoverCertificate4f5a63a5df

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c1 :
    adaptiveCoverCheck 4 (childLH (childLH (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificate4f5a63a5df.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c1_c2_4_00634
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells04b8a575e1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells04b8a575e1

open CertificateCells04b8a575e1
namespace CoverCertificate89bb9fd21e














































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

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

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

end CoverCertificate89bb9fd21e

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificate89bb9fd21e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c1_c3_4_00635
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb52fa9450d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsb52fa9450d

open CertificateCellsb52fa9450d
namespace CoverCertificate5c80136736


















































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

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate5c80136736

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c3 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificate5c80136736.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c1_5_00636
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells024fe9d391

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells024fe9d391

open CertificateCells024fe9d391

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022002010)) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022002010))
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c2_5_00637
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells75262755f1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells75262755f1

open CertificateCells75262755f1
namespace CoverCertificate645f79320a






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

end CoverCertificate645f79320a

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c2 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022002010)) = true := by
  exact CoverCertificate645f79320a.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c3_5_00638
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells88775d9be2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells88775d9be2

open CertificateCells88775d9be2
namespace CoverCertificate3e0a4a2c6f






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

end CoverCertificate3e0a4a2c6f

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c3 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022002010)) = true := by
  exact CoverCertificate3e0a4a2c6f.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c1_c0_c3_6_00639
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells95bf7ab700

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCells95bf7ab700

open CertificateCells95bf7ab700

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022002010) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022002010)
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Theta Above Leaf0000220020_c1_c0_7_00640
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb2f77f238f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))
/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))
/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end CertificateCellsb2f77f238f

open CertificateCellsb2f77f238f

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0 :
    adaptiveCoverCheck 7 thetaAboveCell000022002010 = true :=
  adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002010
    e24KC2ThetaAboveLeaf0000220020_c1_c0_c0 e24KC2ThetaAboveLeaf0000220020_c1_c0_c1
      e24KC2ThetaAboveLeaf0000220020_c1_c0_c2 e24KC2ThetaAboveLeaf0000220020_c1_c0_c3

end PartE
end GerverSofa

end

end

end
