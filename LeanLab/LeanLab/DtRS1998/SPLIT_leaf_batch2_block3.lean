/-
Split of leaf_batch2_block3 into eight single-candidate leaves.

The target asks for primality of the eight candidates at positions 153
through 160 of the fixed candidate list, that is of the block
(qs.drop 152).take 8 of the list of 209 candidates at row 10^90.

This file reads that block as eight one-entry windows at block starts 152,
153, ..., 159 of the candidate list, proves that the block is exactly those
eight windows nested on the right, and closes the block entry by entry from
eight leaves. Each leaf is the primality check of one candidate instead of
eight, so it is strictly easier than the block; no leaf restates or assumes
the block. The windows are inhabited, the list having 209 entries, so no leaf
is vacuous.

The private results below are fully proved, and the assembly
leaf_batch2_block3_split is proved outright from the eight leaves.
-/
import LeanLab.DtRS1998.SPLIT_batch2_prime
import LeanLab.DtRS1998.PocklingtonB7Lucas

namespace LeanLab.DtRS1998.Decomp395a

open Decomp372a

set_option maxRecDepth 100000

/-- Peeling one candidate off the front of a window: the first `k + 1` entries
of a suffix are the first entry followed by the next `k` entries. List algebra
only, no arithmetic on the candidates. -/
private theorem window_peel (l : List ℕ) (n k : ℕ) :
    (l.drop n).take (1 + k) = (l.drop n).take 1 ++ (l.drop (n + 1)).take k := by
  rw [List.take_add (l := l.drop n) (i := 1) (j := k), List.drop_drop (i := 1) (j := n) (l := l)]

/-- The block of eight starting at 152 is the eight one-entry windows at 152,
153, ..., 159, nested on the right so that each step peels one candidate.
List algebra only, no primality. -/
private theorem block3_windows :
    (qs.drop 152).take 8
      = (qs.drop 152).take 1 ++ ((qs.drop 153).take 1 ++
        ((qs.drop 154).take 1 ++ ((qs.drop 155).take 1 ++
        ((qs.drop 156).take 1 ++ ((qs.drop 157).take 1 ++
        ((qs.drop 158).take 1 ++ (qs.drop 159).take 1)))))) := by
  rw [window_peel (l := qs) (n := 152) (k := 7),
    window_peel (l := qs) (n := 153) (k := 6),
    window_peel (l := qs) (n := 154) (k := 5),
    window_peel (l := qs) (n := 155) (k := 4),
    window_peel (l := qs) (n := 156) (k := 3),
    window_peel (l := qs) (n := 157) (k := 2),
    window_peel (l := qs) (n := 158) (k := 1)]

/-- Every window of the block is inhabited, so primality of a window is not a
vacuous requirement. Finite data only, no primality. -/
private theorem block3_window_length :
    ((qs.drop 152).take 8).length = 8 := by
  simp [Decomp372a.qs, Decomp372a.offsets]

/-- The candidate at index 152 of `Decomp372a.qs` is `10 ^ 90 - 32447`; the kernel
checked Pocklington / BLS chain below (copied from the row-90 certificate module)
certifies it. -/
private theorem cert_32447 : (10 ^ 90 - 32447).Prime :=
  LeanLab.DtRS1998.PocklingtonB7.lastP2_prime [(44252797, 2, 0, [(2, 2), (3, 1), (7, 1), (397, 1)], 0, 0, 0, 0, 0, []),
    (1172329, 13, 0, [(2, 3), (3, 1), (48847, 1)], 0, 0, 0, 0, 0, []),
    (56271793, 11, 0, [(2, 4), (3, 1), (1172329, 1)], 0, 0, 0, 0, 0, []),
    (27429221, 2, 0, [(2, 2), (5, 1), (7, 2), (13, 1)], 0, 0, 0, 0, 0, []),
    (10528048179547, 2, 0, [(2, 1), (3, 1), (17, 1), (53, 1), (71, 1), (27429221, 1)], 0, 0, 0, 0, 0, []),
    (269581201685480483, 2, 0, [(2, 1), (7, 1), (31, 1), (59, 1), (10528048179547, 1)], 0, 0, 0, 0, 0, []),
    (23492477, 2, 0, [(2, 2), (7, 1), (23, 1), (36479, 1)], 0, 0, 0, 0, 0, []),
    (262627, 5, 0, [(2, 1), (3, 1), (7, 1), (13, 2)], 0, 0, 0, 0, 0, []),
    (59878957, 2, 0, [(2, 2), (3, 1), (19, 1), (262627, 1)], 0, 0, 0, 0, 0, []),
    (166477573, 2, 0, [(2, 2), (3, 3), (47, 1), (32797, 1)], 0, 0, 0, 0, 0, []),
    (665910293, 2, 0, [(2, 2), (166477573, 1)], 0, 0, 0, 0, 0, []),
    (9322744103, 5, 0, [(2, 1), (7, 1), (665910293, 1)], 0, 0, 0, 0, 0, []),
    (130518417443, 2, 0, [(2, 1), (7, 1), (9322744103, 1)], 0, 0, 0, 0, 0, []),
    (343407829612868932139161273501482793201049069899529, 3, 0, [(2, 3), (17, 1), (19, 1), (307, 1), (23492477, 1), (59878957, 1), (130518417443, 1)], 0, 0, 0, 0, 0, []),
    (686815659225737864278322547002965586402098139799059, 2, 0, [(2, 1), (343407829612868932139161273501482793201049069899529, 1)], 0, 0, 0, 0, 0, []),
    (999999999999999999999999999999999999999999999999999999999999999999999999999999999999967553, 3, 0, [(2, 6), (33889, 1), (44252797, 1), (56271793, 1), (269581201685480483, 1), (686815659225737864278322547002965586402098139799059, 1)], 0, 0, 0, 0, 0, [])] (by decide +kernel)

/-- The window `(qs.drop 152).take 1` is the single candidate `10 ^ 90 - 32447`. -/
private theorem window_152 : (qs.drop 152).take 1 = [10 ^ 90 - 32447] := by
  decide +kernel

/-- The candidate at index 153 of `Decomp372a.qs` is `10 ^ 90 - 32361`; the kernel
checked Pocklington / BLS chain below (copied from the row-90 certificate module)
certifies it. -/
private theorem cert_32361 : (10 ^ 90 - 32361).Prime :=
  LeanLab.DtRS1998.PocklingtonB7.lastP2_prime [(10884529, 7, 0, [(2, 4), (3, 2), (131, 1)], 0, 0, 0, 0, 0, []),
    (163021, 2, 0, [(2, 2), (3, 1), (5, 1), (11, 1)], 0, 0, 0, 0, 0, []),
    (520036991, 26, 0, [(2, 1), (5, 1), (11, 1), (29, 1), (163021, 1)], 0, 0, 0, 0, 0, []),
    (6791383, 3, 0, [(2, 1), (3, 2), (13, 1), (29023, 1)], 0, 0, 0, 0, 0, []),
    (492714836651, 2, 0, [(2, 1), (5, 2), (1451, 1), (6791383, 1)], 0, 0, 0, 0, 0, []),
    (5912578039813, 2, 0, [(2, 2), (3, 1), (492714836651, 1)], 0, 0, 0, 0, 0, []),
    (298861, 7, 0, [(2, 2), (3, 1), (5, 1), (17, 1)], 0, 0, 0, 0, 0, []),
    (2403013, 2, 0, [(2, 2), (3, 1), (43, 1), (4657, 1)], 0, 0, 0, 0, 0, []),
    (4868504339, 2, 0, [(2, 1), (1013, 1), (2403013, 1)], 0, 0, 0, 0, 0, []),
    (120503410606774193, 3, 0, [(2, 4), (29, 1), (439, 1), (2333, 1)], 0, 0, 0, 0, 0, []),
    (2597268607262665261051484099524201961, 3, 0, [(2, 3), (5, 1), (120503410606774193, 1)], 0, 0, 0, 0, 0, []),
    (5820842566480649623152923074807669982875541, 2, 0, [(2, 2), (5, 1), (11, 1), (61, 1), (167, 1), (2597268607262665261051484099524201961, 1)], 0, 0, 0, 0, 0, []),
    (711426348977316809074175882449838922228140361119745077553277, 2, 0, [(2, 2), (3, 1), (7, 1), (298861, 1), (4868504339, 1), (5820842566480649623152923074807669982875541, 1)], 0, 0, 0, 0, 0, []),
    (999999999999999999999999999999999999999999999999999999999999999999999999999999999999967639, 3, 0, [(2, 1), (3, 1), (7, 1), (10884529, 1), (520036991, 1), (5912578039813, 1), (711426348977316809074175882449838922228140361119745077553277, 1)], 0, 0, 0, 0, 0, [])] (by decide +kernel)

/-- The window `(qs.drop 153).take 1` is the single candidate `10 ^ 90 - 32361`. -/
private theorem window_153 : (qs.drop 153).take 1 = [10 ^ 90 - 32361] := by
  decide +kernel

/-- The candidate at index 154 of `Decomp372a.qs` is `10 ^ 90 - 32123`; the kernel
checked Pocklington / BLS chain below (copied from the row-90 certificate module)
certifies it. -/
private theorem cert_32123 : (10 ^ 90 - 32123).Prime :=
  LeanLab.DtRS1998.PocklingtonB7.lastP2_prime [(943757, 2, 0, [(2, 2), (11, 1), (89, 1)], 0, 0, 0, 0, 0, []),
    (3724883, 2, 0, [(2, 1), (7, 2), (191, 1)], 0, 0, 0, 0, 0, []),
    (11061307, 2, 0, [(2, 1), (3, 3), (19, 1), (10781, 1)], 0, 0, 0, 0, 0, []),
    (707923649, 3, 0, [(2, 6), (11061307, 1)], 0, 0, 0, 0, 0, []),
    (72269, 3, 0, [(2, 2), (7, 1), (29, 1)], 0, 0, 0, 0, 0, []),
    (144539, 2, 0, [(2, 1), (72269, 1)], 0, 0, 0, 0, 0, []),
    (739493, 2, 0, [(2, 2), (13, 1), (14221, 1)], 0, 0, 0, 0, 0, []),
    (1478987, 2, 0, [(2, 1), (739493, 1)], 0, 0, 0, 0, 0, []),
    (1810280089, 23, 0, [(2, 3), (3, 2), (17, 1), (1478987, 1)], 0, 0, 0, 0, 0, []),
    (21723361069, 6, 0, [(2, 2), (3, 1), (1810280089, 1)], 0, 0, 0, 0, 0, []),
    (9709231333842218443253117894351, 11, 0, [(2, 1), (5, 2), (2393, 1), (144539, 1), (21723361069, 1)], 0, 0, 0, 0, 0, []),
    (2910974697144230191402291847639537775875837474320982257877030578054252580640199487, 5, 0, [(2, 1), (43, 1), (3724883, 1), (707923649, 1), (9709231333842218443253117894351, 1)], 0, 0, 0, 0, 0, []),
    (999999999999999999999999999999999999999999999999999999999999999999999999999999999999967877, 3, 0, [(2, 2), (7, 1), (13, 1), (943757, 1), (2910974697144230191402291847639537775875837474320982257877030578054252580640199487, 1)], 0, 0, 0, 0, 0, [])] (by decide +kernel)

/-- The window `(qs.drop 154).take 1` is the single candidate `10 ^ 90 - 32123`. -/
private theorem window_154 : (qs.drop 154).take 1 = [10 ^ 90 - 32123] := by
  decide +kernel

/-- The candidate at index 155 of `Decomp372a.qs` is `10 ^ 90 - 32039`; the kernel
checked Pocklington / BLS chain below (copied from the row-90 certificate module)
certifies it. -/
private theorem cert_32039 : (10 ^ 90 - 32039).Prime :=
  LeanLab.DtRS1998.PocklingtonB7.lastP2_prime [(7766009, 3, 0, [(2, 3), (17, 2), (3359, 1)], 0, 0, 0, 0, 0, []),
    (9856313, 3, 0, [(2, 3), (113, 1), (10903, 1)], 0, 0, 0, 0, 0, []),
    (29516807, 5, 0, [(2, 1), (11, 1), (107, 1), (12539, 1)], 0, 0, 0, 0, 0, []),
    (9939607656409, 13, 0, [(2, 3), (3, 3), (1559, 1), (29516807, 1)], 0, 0, 0, 0, 0, []),
    (17305917247533491, 2, 0, [(2, 1), (5, 1), (47, 1), (131, 1), (3533, 1)], 0, 0, 0, 0, 0, []),
    (928047931471, 3, 0, [(2, 1), (3, 6), (5, 1), (11, 1), (727, 1)], 0, 0, 0, 0, 0, []),
    (763224499883, 2, 0, [(2, 1), (13, 1), (37, 1), (43, 1), (67, 1)], 0, 0, 0, 0, 0, []),
    (1526448999767, 5, 0, [(2, 1), (763224499883, 1)], 0, 0, 0, 0, 0, []),
    (92718683752996276357797212755937749552771, 2, 0, [(2, 1), (3, 1), (5, 1), (13, 1), (928047931471, 1), (1526448999767, 1)], 0, 0, 0, 0, 0, []),
    (155948355688843878504364372598445431132647876514665139952777295798983877342409, 6, 0, [(2, 3), (7, 1), (17, 1), (10271, 1), (9939607656409, 1), (17305917247533491, 1), (92718683752996276357797212755937749552771, 1)], 0, 0, 0, 0, 0, []),
    (999999999999999999999999999999999999999999999999999999999999999999999999999999999999967961, 3, 0, [(2, 3), (5, 1), (7, 1), (59, 1), (1093, 1), (7766009, 1)], 26, 19, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999967942, 263157894736842105263157894736842105263157894736842105263157894736842105263157894736833674, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999967961, [(2, 1), (3, 1), (29, 1), (3739, 1), (9856313, 1), (155948355688843878504364372598445431132647876514665139952777295798983877342409, 1)])] (by decide +kernel)

/-- The window `(qs.drop 155).take 1` is the single candidate `10 ^ 90 - 32039`. -/
private theorem window_155 : (qs.drop 155).take 1 = [10 ^ 90 - 32039] := by
  decide +kernel

/-- The candidate at index 156 of `Decomp372a.qs` is `10 ^ 90 - 31269`; the kernel
checked Pocklington / BLS chain below (copied from the row-90 certificate module)
certifies it. -/
private theorem cert_31269 : (10 ^ 90 - 31269).Prime :=
  LeanLab.DtRS1998.PocklingtonB7.lastP2_prime [(1997921, 3, 0, [(2, 5), (5, 1), (12487, 1)], 0, 0, 0, 0, 0, []),
    (3995843, 2, 0, [(2, 1), (1997921, 1)], 0, 0, 0, 0, 0, []),
    (11492044469, 2, 0, [(2, 2), (719, 1), (3995843, 1)], 0, 0, 0, 0, 0, []),
    (2279857, 5, 0, [(2, 4), (3, 1), (47497, 1)], 0, 0, 0, 0, 0, []),
    (3223717799, 7, 0, [(2, 1), (7, 1), (101, 1), (2279857, 1)], 0, 0, 0, 0, 0, []),
    (47240419, 2, 0, [(2, 1), (3, 1), (71, 1), (173, 1)], 0, 0, 0, 0, 0, []),
    (95641043732821, 2, 0, [(2, 2), (3, 2), (5, 1), (37, 1), (56519, 1)], 0, 0, 0, 0, 0, []),
    (17074046039, 7, 0, [(2, 1), (7, 1), (19, 1), (2437, 1)], 0, 0, 0, 0, 0, []),
    (224399136649, 11, 0, [(2, 3), (3, 1), (73, 1), (83, 1), (157, 1)], 0, 0, 0, 0, 0, []),
    (45976814283082538199733, 2, 0, [(2, 2), (3, 1), (17074046039, 1), (224399136649, 1)], 0, 0, 0, 0, 0, []),
    (97302650427427471721101265173608618488695069368812071969642268268392033079461, 3, 0, [(2, 2), (5, 1), (29, 1), (47240419, 1), (95641043732821, 1), (45976814283082538199733, 1)], 0, 0, 0, 0, 0, []),
    (999999999999999999999999999999999999999999999999999999999999999999999999999999999999968731, 2, 0, [(2, 1), (3, 1), (5, 1), (7, 2), (257, 1), (11492044469, 1)], 25, 19, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999968712, 157894736842105263157894736842105263157894736842105263157894736842105263157894736842100326, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999968731, [(2, 2), (797, 1), (3223717799, 1), (97302650427427471721101265173608618488695069368812071969642268268392033079461, 1)])] (by decide +kernel)

/-- The window `(qs.drop 156).take 1` is the single candidate `10 ^ 90 - 31269`. -/
private theorem window_156 : (qs.drop 156).take 1 = [10 ^ 90 - 31269] := by
  decide +kernel

/-- The candidate at index 157 of `Decomp372a.qs` is `10 ^ 90 - 30861`; the kernel
checked Pocklington / BLS chain below (copied from the row-90 certificate module)
certifies it. -/
private theorem cert_30861 : (10 ^ 90 - 30861).Prime :=
  LeanLab.DtRS1998.PocklingtonB7.lastP2_prime [(4415549, 2, 0, [(2, 2), (349, 1), (3163, 1)], 0, 0, 0, 0, 0, []),
    (341057, 3, 0, [(2, 6), (73, 2)], 0, 0, 0, 0, 0, []),
    (6436271, 7, 0, [(2, 1), (5, 1), (239, 1), (2693, 1)], 0, 0, 0, 0, 0, []),
    (13170811670683, 2, 0, [(2, 1), (3, 1), (341057, 1), (6436271, 1)], 0, 0, 0, 0, 0, []),
    (585258187398469789, 6, 0, [(2, 2), (3, 1), (7, 1), (23, 2), (13170811670683, 1)], 0, 0, 0, 0, 0, []),
    (999999999999999999999999999999999999999999999999999999999999999999999999999999999999969139, 3, 13177318724769943763064429377, [(2, 1), (3, 4), (53, 1), (71, 1), (4415549, 1), (585258187398469789, 1)], 0, 0, 0, 0, 0, [])] (by decide +kernel)

/-- The window `(qs.drop 157).take 1` is the single candidate `10 ^ 90 - 30861`. -/
private theorem window_157 : (qs.drop 157).take 1 = [10 ^ 90 - 30861] := by
  decide +kernel

/-- The candidate at index 158 of `Decomp372a.qs` is `10 ^ 90 - 30261`; the kernel
checked Pocklington / BLS chain below (copied from the row-90 certificate module)
certifies it. -/
private theorem cert_30261 : (10 ^ 90 - 30261).Prime :=
  LeanLab.DtRS1998.PocklingtonB7.lastP2_prime [(1052993, 3, 0, [(2, 6), (16453, 1)], 0, 0, 0, 0, 0, []),
    (48142839961, 11, 0, [(2, 3), (3, 2), (5, 1), (127, 1), (1052993, 1)], 0, 0, 0, 0, 0, []),
    (83791, 3, 0, [(2, 1), (3, 2), (5, 1), (7, 2)], 0, 0, 0, 0, 0, []),
    (61670177, 3, 0, [(2, 5), (23, 1), (83791, 1)], 0, 0, 0, 0, 0, []),
    (10643975149, 2, 0, [(2, 2), (3, 1), (37, 1), (907, 1)], 0, 0, 0, 0, 0, []),
    (23741483, 2, 0, [(2, 1), (59, 1), (173, 1)], 0, 0, 0, 0, 0, []),
    (617278559, 14, 0, [(2, 1), (13, 1), (23741483, 1)], 0, 0, 0, 0, 0, []),
    (310781, 2, 0, [(2, 2), (5, 1), (41, 1)], 0, 0, 0, 0, 0, []),
    (903129587, 2, 0, [(2, 1), (1453, 1), (310781, 1)], 0, 0, 0, 0, 0, []),
    (8053026400670946847, 3, 0, [(2, 1), (3, 1), (47, 1), (613, 1), (12641, 1), (58207, 1)], 0, 0, 0, 0, 0, []),
    (53873058389216133090594884686875667813, 2, 0, [(2, 2), (3, 1), (617278559, 1), (903129587, 1), (8053026400670946847, 1)], 0, 0, 0, 0, 0, []),
    (89685722530111040283780678864126741992706595278231556631, 11, 0, [(2, 1), (5, 1), (31, 1), (239, 1), (2111, 1), (10643975149, 1), (53873058389216133090594884686875667813, 1)], 0, 0, 0, 0, 0, []),
    (440784329987473992397288150538692033183290267964447902534818713902390515731, 2, 0, [(2, 1), (3, 1), (5, 1), (7, 2), (83, 1), (641, 1), (1019, 1), (61670177, 1), (89685722530111040283780678864126741992706595278231556631, 1)], 0, 0, 0, 0, 0, []),
    (127323656735421441303794244970715558950853068500127323656735421441303794244970715558947, 3, 0, [(2, 1), (3, 1), (48142839961, 1), (440784329987473992397288150538692033183290267964447902534818713902390515731, 1)], 0, 0, 0, 0, 0, []),
    (999999999999999999999999999999999999999999999999999999999999999999999999999999999999969739, 2, 0, [(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (127323656735421441303794244970715558950853068500127323656735421441303794244970715558947, 1)], 0, 0, 0, 0, 0, [])] (by decide +kernel)

/-- The window `(qs.drop 158).take 1` is the single candidate `10 ^ 90 - 30261`. -/
private theorem window_158 : (qs.drop 158).take 1 = [10 ^ 90 - 30261] := by
  decide +kernel

/-- The candidate at index 159 of `Decomp372a.qs` is `10 ^ 90 - 29969`; the kernel
checked Pocklington / BLS chain below (copied from the row-90 certificate module)
certifies it. -/
private theorem cert_29969 : (10 ^ 90 - 29969).Prime :=
  LeanLab.DtRS1998.PocklingtonB7.lastP2_prime [(8625359, 14, 0, [(2, 1), (7, 1), (17, 1), (36241, 1)], 0, 0, 0, 0, 0, []),
    (17250719, 13, 0, [(2, 1), (8625359, 1)], 0, 0, 0, 0, 0, []),
    (334836455791, 3, 0, [(2, 1), (3, 1), (5, 1), (647, 1), (17250719, 1)], 0, 0, 0, 0, 0, []),
    (86209, 11, 0, [(2, 6), (3, 1), (449, 1)], 0, 0, 0, 0, 0, []),
    (76553593, 5, 0, [(2, 3), (3, 1), (37, 1), (86209, 1)], 0, 0, 0, 0, 0, []),
    (3367133234513, 3, 0, [(2, 4), (2749, 1), (76553593, 1)], 0, 0, 0, 0, 0, []),
    (119254321761899, 2, 0, [(2, 1), (47, 1), (127, 1), (26981, 1)], 0, 0, 0, 0, 0, []),
    (22626360976528621069, 2, 0, [(2, 2), (3, 1), (97, 1), (163, 1), (119254321761899, 1)], 0, 0, 0, 0, 0, []),
    (90505443906114484277, 2, 0, [(2, 2), (22626360976528621069, 1)], 0, 0, 0, 0, 0, []),
    (999999999999999999999999999999999999999999999999999999999999999999999999999999999999970031, 23, 0, [(2, 1), (5, 1), (334836455791, 1), (3367133234513, 1)], 37, 41, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999969990, 658536585365853658536585365853658536585365853658536585365853658536585365853658536585346118, 51957502021253627171034055568354346644906699711, [(2, 4), (3, 1), (7, 1), (90505443906114484277, 1)])] (by decide +kernel)

/-- The window `(qs.drop 159).take 1` is the single candidate `10 ^ 90 - 29969`. -/
private theorem window_159 : (qs.drop 159).take 1 = [10 ^ 90 - 29969] := by
  decide +kernel

/-- LEAF: the first step of the block, the primality of the single candidate
at position 153 of the fixed candidate list, the integer 10 ^ 90 - 32447.
One candidate, not the eight of the block. -/
theorem leaf_block3_window152 : ∀ q ∈ (qs.drop 152).take 1, q.Prime := by
  intro q hq
  rw [window_152, List.mem_singleton] at hq
  rw [hq]
  exact cert_32447

/-- LEAF: the second step of the block, the primality of the single candidate
at position 154 of the fixed candidate list, the integer 10 ^ 90 - 32361.
One candidate, not the eight of the block. -/
theorem leaf_block3_window153 : ∀ q ∈ (qs.drop 153).take 1, q.Prime := by
  intro q hq
  rw [window_153, List.mem_singleton] at hq
  rw [hq]
  exact cert_32361

/-- LEAF: the third step of the block, the primality of the single candidate
at position 155 of the fixed candidate list, the integer 10 ^ 90 - 32123.
One candidate, not the eight of the block. -/
theorem leaf_block3_window154 : ∀ q ∈ (qs.drop 154).take 1, q.Prime := by
  intro q hq
  rw [window_154, List.mem_singleton] at hq
  rw [hq]
  exact cert_32123

/-- LEAF: the fourth step of the block, the primality of the single candidate
at position 156 of the fixed candidate list, the integer 10 ^ 90 - 32039.
One candidate, not the eight of the block. -/
theorem leaf_block3_window155 : ∀ q ∈ (qs.drop 155).take 1, q.Prime := by
  intro q hq
  rw [window_155, List.mem_singleton] at hq
  rw [hq]
  exact cert_32039

/-- LEAF: the fifth step of the block, the primality of the single candidate
at position 157 of the fixed candidate list, the integer 10 ^ 90 - 31269.
One candidate, not the eight of the block. -/
theorem leaf_block3_window156 : ∀ q ∈ (qs.drop 156).take 1, q.Prime := by
  intro q hq
  rw [window_156, List.mem_singleton] at hq
  rw [hq]
  exact cert_31269

/-- LEAF: the sixth step of the block, the primality of the single candidate
at position 158 of the fixed candidate list, the integer 10 ^ 90 - 30861.
One candidate, not the eight of the block. -/
theorem leaf_block3_window157 : ∀ q ∈ (qs.drop 157).take 1, q.Prime := by
  intro q hq
  rw [window_157, List.mem_singleton] at hq
  rw [hq]
  exact cert_30861

/-- LEAF: the seventh step of the block, the primality of the single candidate
at position 159 of the fixed candidate list, the integer 10 ^ 90 - 30261.
One candidate, not the eight of the block. -/
theorem leaf_block3_window158 : ∀ q ∈ (qs.drop 158).take 1, q.Prime := by
  intro q hq
  rw [window_158, List.mem_singleton] at hq
  rw [hq]
  exact cert_30261

/-- LEAF: the eighth step of the block, the primality of the single candidate
at position 160 of the fixed candidate list, the integer 10 ^ 90 - 29969.
One candidate, not the eight of the block. -/
theorem leaf_block3_window159 : ∀ q ∈ (qs.drop 159).take 1, q.Prime := by
  intro q hq
  rw [window_159, List.mem_singleton] at hq
  rw [hq]
  exact cert_29969

/-- The block, proved from the eight single-candidate leaves: the block is the
eight one-entry windows nested on the right, and each entry of the block falls
in the window that starts at it, whose primality is the corresponding leaf. -/
theorem leaf_batch2_block3_split :
    ∀ q ∈ (qs.drop 152).take 8, q.Prime := by
  intro q hq
  rw [block3_windows] at hq
  rcases List.mem_append.mp hq with h | h
  · exact leaf_block3_window152 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_block3_window153 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_block3_window154 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_block3_window155 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_block3_window156 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_block3_window157 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_block3_window158 q h
  · exact leaf_block3_window159 q h

end LeanLab.DtRS1998.Decomp395a
