import FleetSignUncertaintyData

/-! Descartes-leaf positivity certificates for `Q`, part 3 (kernel evaluation, natural numbers only). -/

namespace FleetSignUncertainty

theorem sigLeaves32 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 225
    [(225, 32)]
    257 = true := by decide +kernel

theorem sigLeaves33 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 257
    [(257, 32)]
    289 = true := by decide +kernel

theorem sigLeaves34 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 289
    [(289, 63)]
    352 = true := by decide +kernel

theorem sigLeaves35 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 352
    [(352, 64)]
    416 = true := by decide +kernel

theorem sigLeaves36 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 416
    [(416, 64)]
    480 = true := by decide +kernel

theorem sigLeaves37 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 480
    [(480, 64)]
    544 = true := by decide +kernel

theorem sigLeaves38 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 544
    [(544, 63)]
    607 = true := by decide +kernel

theorem sigLeaves39 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 607
    [(607, 64)]
    671 = true := by decide +kernel

theorem sigLeaves40 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 671
    [(671, 128)]
    799 = true := by decide +kernel

theorem sigLeaves41 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 799
    [(799, 127)]
    926 = true := by decide +kernel

theorem sigLeaves42 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 926
    [(926, 128)]
    1054 = true := by decide +kernel

theorem sigLeaves43 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 1054
    [(1054, 127)]
    1181 = true := by decide +kernel

theorem sigLeaves44 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 1181
    [(1181, 128)]
    1309 = true := by decide +kernel

theorem sigLeaves45 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 1309
    [(1309, 127)]
    1436 = true := by decide +kernel

theorem sigLeaves46 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 1436
    [(1436, 128)]
    1564 = true := by decide +kernel

theorem sigLeaves47 : leavesOK (scaleUpN 1 sigP) (scaleUpN 1 sigN) 1564
    [(1564, 510)]
    2074 = true := by decide +kernel

theorem sigTail : tailOKP (compLinN 2074 (scaleUpN 1 sigP)) (compLinN 2074 (scaleUpN 1 sigN)) = true := by
  decide +kernel

end FleetSignUncertainty
