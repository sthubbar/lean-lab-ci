/-
Ported from Prove2Me, mission 0814790f.
Source Def_axler_theta_base. Author recorded as None in the pulled header. Apache 2.0.
Lean 4.33.1 source adapted for Lean 4.35.0.
Only the dependency slice for the Axler theta chain is included.
Derived certificates for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Ring.GeomSum
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

set_option autoImplicit false
set_option Elab.async false

open Finset


namespace LeanLab.Ported.Prove2Me.Task666
namespace RosserBitSieve


def periodicMask (d count : ℕ) : ℕ :=
  (2 ^ (d * count) - 1) / (2 ^ d - 1)

def divisorMask (a len d : ℕ) : ℕ :=
  periodicMask d ((len + d - 1) / d) * 2 ^ ((d - a % d) % d)

def compositeMask (divisors : List ℕ) (a len : ℕ) : ℕ :=
  divisors.foldl (fun mask d => mask ||| divisorMask a len d) 0

def candidateMask (divisors : List ℕ) (a len : ℕ) : ℕ :=
  (2 ^ len - 1) ^^^ (compositeMask divisors a len % 2 ^ len)

/-- Enumerate a bit interval by halving it, skipping empty subtrees. -/
def enumBits : ℕ → ℕ → ℕ → List ℕ
  | 0, start, mask => if mask % 2 == 1 then [start] else []
  | depth + 1, start, mask =>
    if mask == 0 then [] else
    let half := 2 ^ depth
    enumBits depth start (mask % 2 ^ half) ++
      enumBits depth (start + half) (mask / 2 ^ half)

def offsets (divisors : List ℕ) (depth a len : ℕ) : List ℕ :=
  enumBits depth 0 (candidateMask divisors a len)

/-- Reuse one sieve mask for many short blocks. Offsets here start at one. -/
def windowOffsets (depth mask shift len : ℕ) : List ℕ :=
  (enumBits depth 0 (mask / 2 ^ shift % 2 ^ len)).map (· + 1)

end RosserBitSieve

namespace AlternativeProductMoments


def firstMoment (ds : List ℕ) : ℕ := ds.sum

def secondMoment (ds : List ℕ) : ℕ := (ds.map (fun (d : ℕ) => d ^ 2)).sum

def lowerNumerator (a : ℕ) (ds : List ℕ) : ℕ :=
  ds.length * a - firstMoment ds

def upperNumerator (a : ℕ) (ds : List ℕ) : ℕ :=
  ds.length * a ^ 2 - a * firstMoment ds + secondMoment ds

def pairNumerator (a : ℕ) (ds : List ℕ) : ℕ :=
  lowerNumerator a ds ^ 2 - ds.length * a ^ 2

def factorNumerator (a : ℕ) (ds : List ℕ) : ℕ :=
  (a ^ 3 - upperNumerator a ds) * (2 * a ^ 4 + pairNumerator a ds)

def factorDenominator (a : ℕ) : ℕ := 2 * a ^ 7

/-- One downward-rounded update for a whole candidate block. -/
def momentStep (v a : ℕ) (ds : List ℕ) : ℕ :=
  v * factorNumerator a ds / factorDenominator a

end AlternativeProductMoments

namespace RosserBitMoments

open RosserBitSieve AlternativeProductMoments

abbrev Moments := ℕ × ℕ × ℕ
namespace Moments
abbrev count (s : Moments) : ℕ := s.1
abbrev first (s : Moments) : ℕ := s.2.1
abbrev second (s : Moments) : ℕ := s.2.2
theorem ext {s t : Moments} (hc : s.1 = t.1) (hf : s.2.1 = t.2.1)
    (hs : s.2.2 = t.2.2) : s = t := Prod.ext hc (Prod.ext hf hs)
end Moments

def moments (ds : List ℕ) : Moments :=
  ⟨ds.length, ds.sum, (ds.map (fun (d : ℕ) => d ^ 2)).sum⟩

def merge (s t : Moments) : Moments :=
  ⟨s.1 + t.1, s.2.1 + t.2.1, s.2.2 + t.2.2⟩

def translate (offset : ℕ) (s : Moments) : Moments :=
  ⟨s.1, s.2.1 + offset * s.1,
    s.2.2 + 2 * offset * s.2.1 + offset ^ 2 * s.1⟩

def packedTable : ℕ := 18472300896970103792108295030754343311462210589054640814582099618958825816112921765637552819554960025580043253363337196071510397018042133440073613070599528214959555081087759177994513208873881398958301422300628985358844335629703824674989009933744813385983504668349668413339407645329016240118311102009327559169919361752210702429893649728293932236557803946372391347786424282478245140012004923246019750498074272682481869124019625063780294997972415480522849467413156748308598193741959980512364680419185912142662080168720543223372130422252685000667222028691552391144914476582653820543415241442522565567827850971540414084963023662461454138479593909733901640282571543659792227281002640358593405226625400471739963595439608037996346958976031522266509217418626068981435972643586956604265934825153588078474541062083601584565110669452202573339800164169103872550900181154149463648375952255080306757167758906906382736410940812007907700484645358916007966298027371443379797534272791198303638115965305949698405311795153919406852986359475633446763175764573556098103639551525890208319167226087125167594382204144161586295123540456912808096572570872821701693833155843103822148960692081668132802646373741121271338591023149542977379459365527447593127745781442122554270427974619422849735484296339832731170084457029930842499657049873841177855047761694425403274812125429077333590092198933962090340380251846202809362383975418479306463890842278375332614640909801129604954946001702919968537917515644728884667828251078535570507012846902588218779713741378512607411980300476879133811456575684021346503785234617675182982977540462331832399895301441454472653688500254658691068207975085644854631617042755709815233293970628383901959051862306499230180026929443703650068362443283922131960509713762221413633617444652901862094089062362383582693974422591379320268703353694406511098994725224448

def byteMoments (byte : ℕ) : Moments :=
  if byte == 0 then ⟨0, 0, 0⟩ else
  if byte &&& (byte - 1) == 0 then
    let bit := Nat.log2 byte
    ⟨1, bit, bit ^ 2⟩
  else
    let word := packedTable / 2 ^ (24 * byte) % 2 ^ 24
    ⟨word % 256, word / 256 % 256, word / 65536 % 256⟩

/-- Depth d represents 2^(d+3) bits. Empty subtrees are skipped. -/
def fastMoments : ℕ → ℕ → ℕ → Moments
  | 0, start, mask => translate start (byteMoments (mask % 256))
  | depth + 1, start, mask =>
    if mask == 0 then ⟨0, 0, 0⟩ else
    let half := 2 ^ (depth + 3)
    merge (fastMoments depth start (mask % 2 ^ half))
      (fastMoments depth (start + half) (mask / 2 ^ half))

def windowMoments (mask shift len : ℕ) : Moments :=
  fastMoments 10 1 (mask / 2 ^ shift % 2 ^ len)

def stepFromMoments (v a : ℕ) (s : Moments) : ℕ :=
  let ell := s.1 * a - s.2.1
  let u := s.1 * a ^ 2 - a * s.2.1 + s.2.2
  let e := ell ^ 2 - s.1 * a ^ 2
  v * ((a ^ 3 - u) * (2 * a ^ 4 + e)) / (2 * a ^ 7)

def fastMomentStep (v a mask shift len : ℕ) : ℕ :=
  stepFromMoments v a (windowMoments mask shift len)

end RosserBitMoments
namespace RosserScan
def forceNat {α : Type} (n : ℕ) (f : ℕ → α) : α :=
  match n with
  | 0 => f 0
  | n + 1 => f (n + 1)


end RosserScan
namespace RosserSieveData

open RosserBitSieve RosserScan

def divisors : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973]

def smallDivisors (base : ℕ) := divisors.filter (fun d => decide (d ≤ base))

def mask (base top : ℕ) := candidateMask (smallDivisors base) (base + 1) (top - base)

end RosserSieveData
namespace RosserProductCertificate
def referencePrimes (B : ℕ) : List ℕ :=
  (List.range (B + 1)).filter (fun p => decide (2 ≤ p ∧ Nat.minFac p = p))

theorem referencePrimes_toFinset (B : ℕ) :
    (referencePrimes B).toFinset = Nat.primesLE B := by
  ext p
  simp [referencePrimes, Nat.mem_primesLE, Nat.prime_def_minFac]

theorem referencePrimes_nodup (B : ℕ) : (referencePrimes B).Nodup :=
  List.nodup_range.filter _


end RosserProductCertificate
namespace RosserBitSieve

theorem periodicMask_eq_sum (d count : ℕ) (hd : 0 < d) :
    periodicMask d count = ∑ i ∈ Finset.range count, (2 ^ d) ^ i := by
  rw [Nat.geomSum_eq (Nat.one_lt_two_pow (Nat.ne_of_gt hd)), periodicMask, pow_mul]

theorem periodicMask_succ (d count : ℕ) (hd : 0 < d) :
    periodicMask d (count + 1) = 2 ^ d * periodicMask d count + 1 := by
  rw [periodicMask_eq_sum d (count + 1) hd, periodicMask_eq_sum d count hd,
    geom_sum_succ]

/-- Every set bit in a periodic mask has index divisible by d. -/
theorem periodicMask_bit_dvd (d count i : ℕ) (hd : 0 < d)
    (hbit : (periodicMask d count).testBit i = true) : d ∣ i := by
  induction count generalizing i with
  | zero => simp [periodicMask] at hbit
  | succ count ih =>
    rw [periodicMask_succ d count hd,
      Nat.testBit_two_pow_mul_add _ (Nat.one_lt_two_pow (Nat.ne_of_gt hd))] at hbit
    split at hbit
    · have hone : (1 : ℕ).testBit i = decide (i = 0) := by
        simpa only [Nat.pow_zero, eq_comm] using (Nat.testBit_two_pow (n := 0) (m := i))
      rw [hone] at hbit
      have hi : i = 0 := of_decide_eq_true hbit
      subst i
      exact dvd_zero d
    · rename_i hi
      have hdiv := ih (i - d) hbit
      have heq : i = (i - d) + d := by omega
      rw [heq]
      exact dvd_add hdiv (dvd_refl d)

theorem first_multiple (a d : ℕ) (hd : 0 < d) :
    d ∣ a + (d - a % d) % d := by
  apply Nat.dvd_of_mod_eq_zero
  by_cases hz : a % d = 0
  · simp [hz]
  · have hm := Nat.mod_lt a hd
    have hsmall : d - a % d < d := by omega
    rw [Nat.mod_eq_of_lt hsmall, Nat.add_mod]
    rw [Nat.mod_eq_of_lt hsmall, Nat.add_sub_of_le hm.le, Nat.mod_self]

theorem divisorMask_bit_dvd (a len d i : ℕ) (hd : 0 < d)
    (hbit : (divisorMask a len d).testBit i = true) : d ∣ a + i := by
  unfold divisorMask at hbit
  rw [Nat.testBit_mul_two_pow, Bool.and_eq_true] at hbit
  obtain ⟨hoffset, hperiodic⟩ := hbit
  have hoffset' : (d - a % d) % d ≤ i := of_decide_eq_true hoffset
  have hp := periodicMask_bit_dvd d _ _ hd hperiodic
  have hfirst := first_multiple a d hd
  have heq : a + i = (a + (d - a % d) % d) + (i - (d - a % d) % d) := by omega
  rw [heq]
  exact dvd_add hfirst hp

theorem divisorMask_preserves_prime (a len d i : ℕ)
    (hd : 2 ≤ d) (hda : d < a) (hp : Nat.Prime (a + i)) :
    (divisorMask a len d).testBit i = false := by
  apply Bool.eq_false_iff.mpr
  intro hbit
  have hdiv := divisorMask_bit_dvd a len d i (by omega) hbit
  rcases hp.eq_one_or_self_of_dvd d hdiv with h | h <;> omega

theorem compositeMask_preserves_prime (divisors : List ℕ) (a len i : ℕ)
    (hds : ∀ d ∈ divisors, 2 ≤ d ∧ d < a) (hp : Nat.Prime (a + i)) :
    (compositeMask divisors a len).testBit i = false := by
  suffices h : ∀ mask : ℕ, mask.testBit i = false →
      (divisors.foldl (fun mask d => mask ||| divisorMask a len d) mask).testBit i = false by
    exact h 0 (by simp)
  induction divisors with
  | nil => simp
  | cons d ds ih =>
    intro mask hmask
    apply ih (fun q hq => hds q (by simp [hq]))
    rw [Nat.testBit_or, hmask, divisorMask_preserves_prime a len d i
      (hds d (by simp)).1 (hds d (by simp)).2 hp]
    rfl

theorem candidateMask_preserves_prime (divisors : List ℕ) (a len i : ℕ)
    (hds : ∀ d ∈ divisors, 2 ≤ d ∧ d < a) (hi : i < len)
    (hp : Nat.Prime (a + i)) :
    (candidateMask divisors a len).testBit i = true := by
  simp [candidateMask, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, hi, compositeMask_preserves_prime divisors a len i hds hp]

theorem mem_enumBits (depth start mask x : ℕ) :
    x ∈ enumBits depth start mask ↔
      start ≤ x ∧ x < start + 2 ^ depth ∧ mask.testBit (x - start) = true := by
  induction depth generalizing start mask with
  | zero =>
    simp only [enumBits, Nat.pow_zero]
    split
    · rename_i h
      have hm : mask % 2 = 1 := by simpa using h
      constructor
      · intro hx
        have hx' : x = start := by simpa using hx
        subst x
        simp [Nat.testBit_eq_decide_div_mod_eq, hm]
      · intro hx
        have hx' : x = start := by omega
        simp [hx']
    · rename_i h
      have hm : mask % 2 ≠ 1 := by simpa using h
      constructor
      · simp
      · intro hx
        have hx' : x = start := by omega
        subst x
        simp [Nat.testBit_eq_decide_div_mod_eq, hm] at hx
  | succ depth ih =>
    by_cases hm : mask = 0
    · subst mask
      simp [enumBits]
    · simp only [enumBits, beq_iff_eq, hm, if_false, List.mem_append, ih,
        Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Bool.and_eq_true,
        decide_eq_true_eq, Nat.pow_succ]
      constructor
      · intro hx
        rcases hx with ⟨hlo, hhi, _, hb⟩ | ⟨hlo, hhi, hb⟩
        · exact ⟨hlo, by omega, hb⟩
        · refine ⟨by omega, by omega, ?_⟩
          have heq : x - (start + 2 ^ depth) + 2 ^ depth = x - start := by omega
          simpa only [heq] using hb
      · intro ⟨hlo, hhi, hb⟩
        by_cases hleft : x < start + 2 ^ depth
        · exact Or.inl ⟨hlo, hleft, by omega, hb⟩
        · right
          refine ⟨by omega, by omega, ?_⟩
          have heq : x - (start + 2 ^ depth) + 2 ^ depth = x - start := by omega
          simpa only [heq] using hb

theorem enumBits_nodup (depth start mask : ℕ) : (enumBits depth start mask).Nodup := by
  induction depth generalizing start mask with
  | zero => simp only [enumBits]; split <;> simp
  | succ depth ih =>
    simp only [enumBits]
    split
    · simp
    · apply List.Nodup.append (ih _ _) (ih _ _)
      apply List.disjoint_left.mpr
      intro x hx hx'
      have hleft := (mem_enumBits _ _ _ _).mp hx
      have hright := (mem_enumBits _ _ _ _).mp hx'
      omega

theorem candidateMask_bit (divisors : List ℕ) (a len i : ℕ) :
    (candidateMask divisors a len).testBit i =
      (decide (i < len) && !(compositeMask divisors a len).testBit i) := by
  by_cases hi : i < len <;>
    simp [candidateMask, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
      Nat.testBit_mod_two_pow, hi]

theorem offsets_lt (divisors : List ℕ) (depth a len i : ℕ)
    (hi : i ∈ offsets divisors depth a len) : i < len := by
  have hb := (mem_enumBits _ _ _ _).mp hi
  simp only [Nat.sub_zero, candidateMask_bit, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact hb.2.2.1

theorem offsets_preserve_primes (divisors : List ℕ) (depth a len p : ℕ)
    (hds : ∀ d ∈ divisors, 2 ≤ d ∧ d < a) (hlen : len ≤ 2 ^ depth)
    (hpa : a ≤ p) (hpB : p < a + len) (hp : Nat.Prime p) :
    p - a ∈ offsets divisors depth a len := by
  apply (mem_enumBits _ _ _ _).mpr
  refine ⟨Nat.zero_le _, by omega, ?_⟩
  simp only [Nat.sub_zero]
  apply candidateMask_preserves_prime divisors a len (p - a) hds (by omega)
  simpa only [Nat.add_sub_of_le hpa] using hp

theorem offsets_nodup (divisors : List ℕ) (depth a len : ℕ) :
    (offsets divisors depth a len).Nodup := enumBits_nodup _ _ _

theorem mem_windowOffsets (depth mask shift len d : ℕ) :
    d ∈ windowOffsets depth mask shift len ↔
      0 < d ∧ d ≤ len ∧ d ≤ 2 ^ depth ∧ mask.testBit (d - 1 + shift) = true := by
  simp only [windowOffsets, List.mem_map, mem_enumBits, Nat.zero_add, Nat.sub_zero,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨_, hi, hlen, hb⟩, rfl⟩
    exact ⟨by omega, by omega, by omega, by simpa using hb⟩
  · rintro ⟨hd, hlen, hdepth, hb⟩
    exact ⟨d - 1, ⟨Nat.zero_le _, by omega, by omega, hb⟩, by omega⟩

theorem windowOffsets_nodup (depth mask shift len : ℕ) :
    (windowOffsets depth mask shift len).Nodup := by
  apply List.Nodup.map _ (enumBits_nodup _ _ _)
  intro a b h
  change a + 1 = b + 1 at h
  omega

end RosserBitSieve
namespace RosserPackedBarrier

theorem forceNat_eq {α : Sort _} (n : ℕ) (f : ℕ → α) :
    RosserScan.forceNat n f = f n := by
  cases n <;> rfl

def candidateCount (mask d : ℕ) : ℕ :=
  ((List.range d).filter (fun i => mask.testBit i)).length

/-- Little-endian packing with a fixed number of digits. -/
def pack (q : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + q * pack q n (fun i => f (i + 1))

theorem pack_congr (q n : ℕ) {f g : ℕ → ℕ}
    (h : ∀ i < n, f i = g i) : pack q n f = pack q n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [pack]
    rw [h 0 (by omega), ih (fun i hi => h (i + 1) (by omega))]

theorem pack_add (q n : ℕ) (f g : ℕ → ℕ) :
    pack q n (fun i => f i + g i) = pack q n f + pack q n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [pack, ih]; ring

theorem pack_mul (q n c : ℕ) (f : ℕ → ℕ) :
    pack q n (fun i => c * f i) = c * pack q n f := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih => simp only [pack, ih]; ring

theorem pack_mono (q n : ℕ) {f g : ℕ → ℕ}
    (h : ∀ i < n, f i ≤ g i) : pack q n f ≤ pack q n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    exact Nat.add_le_add (h 0 (by omega))
      (Nat.mul_le_mul_left q (ih (fun i hi => h (i + 1) (by omega))))

theorem pack_sub (q n : ℕ) {f g : ℕ → ℕ}
    (h : ∀ i < n, g i ≤ f i) :
    pack q n (fun i => f i - g i) = pack q n f - pack q n g := by
  have heq : pack q n (fun i => f i - g i) + pack q n g = pack q n f := by
    rw [← pack_add]
    exact pack_congr q n (fun i hi => Nat.sub_add_cancel (h i hi))
  omega

theorem pack_lt (q n : ℕ) (hq : 0 < q) {f : ℕ → ℕ}
    (h : ∀ i < n, f i < q) : pack q n f < q ^ n := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    have htail := ih (fun i hi => h (i + 1) (by omega))
    have hhead := h 0 (by omega)
    simp only [pack, pow_succ]
    nlinarith

theorem pack_mod (q n : ℕ) (hq : 0 < q) {f : ℕ → ℕ}
    (h : f 0 < q) : pack q (n + 1) f % q = f 0 := by
  simp [pack, Nat.mod_eq_of_lt h]

theorem pack_div (q n : ℕ) (hq : 0 < q) {f : ℕ → ℕ}
    (h : f 0 < q) : pack q (n + 1) f / q = pack q n (fun i => f (i + 1)) := by
  simp [pack, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt h]

theorem pack_digit (q n i : ℕ) (hq : 0 < q) {f : ℕ → ℕ}
    (h : ∀ j < n, f j < q) (hi : i < n) :
    pack q n f / q ^ i % q = f i := by
  induction i generalizing n f with
  | zero =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa using pack_mod q n hq (h 0 (by omega))
  | succ i ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ', ← Nat.div_div_eq_div_mul, pack_div q n hq (h 0 (by omega))]
    exact ih n (fun j hj => h (j + 1) (by omega)) (by omega)

theorem pack_eq_sum (q n : ℕ) (f : ℕ → ℕ) :
    pack q n f = ∑ i ∈ Finset.range n, f i * q ^ i := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack, ih, Finset.sum_range_succ']
    simp only [pow_zero, Nat.mul_one, Finset.mul_sum, pow_succ]
    rw [Nat.add_comm (f 0)]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem pack_const_one (q n : ℕ) (hq : 1 < q) :
    pack q n (fun _ => 1) = (q ^ n - 1) / (q - 1) := by
  rw [pack_eq_sum]
  simp only [Nat.one_mul]
  exact Nat.geomSum_eq hq n

theorem pack_const (q n c : ℕ) :
    pack q n (fun _ => c) = c * pack q n (fun _ => 1) := by
  simpa using pack_mul q n c (fun _ => 1)

theorem pack_one_identity (q n : ℕ) (hq : 1 ≤ q) :
    (q - 1) * pack q n (fun _ => 1) + 1 = q ^ n := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    simp only [pack, pow_succ]
    have hq' := Nat.sub_add_cancel hq
    nlinarith

def prefixSum (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, f i

@[simp] theorem prefixSum_one (f : ℕ → ℕ) : prefixSum f 1 = f 0 := by
  simp [prefixSum]

theorem prefixSum_shift (f : ℕ → ℕ) (n : ℕ) :
    prefixSum f (n + 1) = f 0 + prefixSum (fun i => f (i + 1)) n := by
  simp [prefixSum, Finset.sum_range_succ', Nat.add_comm]

theorem pack_prefix_identity (q n : ℕ) (f : ℕ → ℕ) (hq : 1 ≤ q) :
    (q - 1) * pack q n (fun i => prefixSum f (i + 1)) + pack q n f =
      q ^ n * prefixSum f n := by
  induction n generalizing f with
  | zero => simp [pack, prefixSum]
  | succ n ih =>
    have hy : pack q (n + 1) (fun i => prefixSum f (i + 1)) =
        f 0 + q * (f 0 * pack q n (fun _ => 1) +
          pack q n (fun i => prefixSum (fun j => f (j + 1)) (i + 1))) := by
      rw [pack, prefixSum_one, ← pack_const, ← pack_add]
      congr 2
      apply pack_congr
      intro i hi
      exact prefixSum_shift f (i + 1)
    rw [hy, pack, prefixSum_shift, pow_succ]
    have htail := congrArg (fun x => q * x) (ih (fun i => f (i + 1)))
    have hr := congrArg (fun x => q * f 0 * x) (pack_one_identity q n hq)
    have hq' := Nat.sub_add_cancel hq
    nlinarith

theorem prefixSum_mono (f : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) :
    prefixSum f a ≤ prefixSum f b := by
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- Multiplication by a repunit packs all cumulative digit sums at once. -/
theorem pack_prefix_mod (q n : ℕ) (f : ℕ → ℕ) (hq : 1 < q)
    (hsum : prefixSum f n < q) :
    (pack q n f * pack q n (fun _ => 1)) % q ^ n =
      pack q n (fun i => prefixSum f (i + 1)) := by
  have hcop : Nat.Coprime (q ^ n) (q - 1) := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_self_sub_right (by omega : 1 ≤ q)).mpr (by simp)
  have hx : (q - 1) * (pack q n f * pack q n (fun _ => 1)) + pack q n f =
      q ^ n * pack q n f := by
    have := congrArg (fun x => pack q n f * x) (pack_one_identity q n (by omega))
    nlinarith
  have heq :
      (q - 1) * (pack q n f * pack q n (fun _ => 1)) + pack q n f ≡
      (q - 1) * pack q n (fun i => prefixSum f (i + 1)) + pack q n f [MOD q ^ n] := by
    rw [hx, pack_prefix_identity q n f (by omega)]
    simp [Nat.ModEq]
  have heq' := Nat.ModEq.add_right_cancel (Nat.ModEq.refl (pack q n f)) heq
  have hc := Nat.ModEq.cancel_left_of_coprime hcop heq'
  rw [Nat.ModEq, Nat.mod_eq_of_lt (pack_lt q n (by omega) (fun i hi =>
    (prefixSum_mono f (by omega : i + 1 ≤ n)).trans_lt hsum))] at hc
  exact hc

theorem pack_testBit (w n i j : ℕ) {f : ℕ → ℕ}
    (h : ∀ k < n, f k < 2 ^ w) (hi : i < n) (hj : j < w) :
    (pack (2 ^ w) n f).testBit (w * i + j) = (f i).testBit j := by
  have hd := pack_digit (2 ^ w) n i (by positivity) h hi
  have hb := congrArg (fun x : ℕ => x.testBit j) hd
  rw [Nat.testBit_mod_two_pow, show decide (j < w) = true by simp [hj],
    Bool.true_and] at hb
  simpa only [← pow_mul, Nat.testBit_div_two_pow, Nat.add_comm] using hb

theorem pack_testBit_all (w n k : ℕ) (hw : 0 < w) {f : ℕ → ℕ}
    (h : ∀ i < n, f i < 2 ^ w) :
    (pack (2 ^ w) n f).testBit k =
      if k / w < n then (f (k / w)).testBit (k % w) else false := by
  have hdecomp := Nat.mod_add_div k w
  by_cases hi : k / w < n
  · rw [if_pos hi]
    have hk : k = w * (k / w) + k % w := by omega
    simpa only [← hk] using pack_testBit w n (k / w) (k % w) h hi (Nat.mod_lt k hw)
  · rw [if_neg hi]
    have hkn : w * n ≤ k := by
      have := Nat.mul_le_mul_left w (by omega : n ≤ k / w)
      omega
    apply Nat.testBit_eq_false_of_lt
    apply (pack_lt (2 ^ w) n (by positivity) h).trans_le
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) hkn

theorem pack_and (w n : ℕ) (hw : 0 < w) (f g : ℕ → ℕ)
    (hf : ∀ i < n, f i < 2 ^ w) (hg : ∀ i < n, g i < 2 ^ w) :
    pack (2 ^ w) n f &&& pack (2 ^ w) n g =
      pack (2 ^ w) n (fun i => f i &&& g i) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, pack_testBit_all w n k hw hf, pack_testBit_all w n k hw hg,
    pack_testBit_all w n k hw (fun i hi => Nat.and_le_left.trans_lt (hf i hi))]
  split_ifs <;> simp [Nat.testBit_and]

/-- A low mask discards exactly the bits shifted in from the next digit. -/
theorem pack_shift_and (w n s : ℕ) (hw : 0 < w) (hs : s ≤ w) (f g : ℕ → ℕ)
    (hf : ∀ i < n, f i < 2 ^ w) (hg : ∀ i < n, g i < 2 ^ (w - s)) :
    (pack (2 ^ w) n f >>> s) &&& pack (2 ^ w) n g =
      pack (2 ^ w) n (fun i => (f i >>> s) &&& g i) := by
  have hg' : ∀ i < n, g i < 2 ^ w := fun i hi =>
    (hg i hi).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hout : ∀ i < n, ((f i >>> s) &&& g i) < 2 ^ w := fun i hi =>
    Nat.and_le_right.trans_lt (hg' i hi)
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, pack_testBit_all w n k hw hg', pack_testBit_all w n k hw hout]
  by_cases hi : k / w < n
  · rw [if_pos hi, if_pos hi, Nat.testBit_and]
    by_cases hb : (g (k / w)).testBit (k % w) = true
    · have hsmall : k % w < w - s := by
        by_contra hh
        have hfals := Nat.testBit_eq_false_of_lt ((hg (k / w) hi).trans_le
          (Nat.pow_le_pow_right (by omega) (by omega : w - s ≤ k % w)))
        simp [hb] at hfals
      have hd := Nat.mod_add_div k w
      have heq : s + k = w * (k / w) + (k % w + s) := by omega
      rw [Nat.testBit_shiftRight, heq, pack_testBit w n (k / w) (k % w + s) hf hi
        (by omega), Nat.testBit_shiftRight]
      simp [Nat.add_comm]
    · simp [Bool.eq_false_iff.mpr hb]
  · simp [hi]

theorem pack_pair (q n : ℕ) (f : ℕ → ℕ) :
    pack q (2 * n) f = pack (q * q) n (fun i => f (2 * i) + q * f (2 * i + 1)) := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    simp only [pack]
    rw [ih]
    have heq :
        pack (q * q) n (fun i => f (2 * i + 1 + 1) + q * f (2 * i + 1 + 1 + 1)) =
        pack (q * q) n (fun i => f (2 * (i + 1)) + q * f (2 * (i + 1) + 1)) := by
      apply pack_congr
      intro i hi
      congr 2 <;> omega
    rw [heq]
    ring

theorem pack_digits (w n mask : ℕ) (hw : 0 < w) (hm : mask < 2 ^ (w * n)) :
    pack (2 ^ w) n (fun i => mask / 2 ^ (w * i) % 2 ^ w) = mask := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [pack_testBit_all w n k hw (fun i hi => Nat.mod_lt _ (by positivity))]
  by_cases hi : k / w < n
  · rw [if_pos hi, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    have hj := Nat.mod_lt k hw
    simp only [show decide (k % w < w) = true by simp [hj], Bool.true_and]
    rw [Nat.mod_add_div]
  · rw [if_neg hi]
    symm
    apply Nat.testBit_eq_false_of_lt
    apply hm.trans_le (Nat.pow_le_pow_right (by omega) ?_)
    have hdecomp := Nat.mod_add_div k w
    have := Nat.mul_le_mul_left w (by omega : n ≤ k / w)
    omega

theorem stripe_eq (w n : ℕ) (hw : 0 < w) :
    (2 ^ (2 * w * n) - 1) / (2 ^ w + 1) =
      pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1) := by
  have hq : 1 ≤ 2 ^ w := Nat.succ_le_of_lt (Nat.two_pow_pos w)
  have hr := pack_one_identity (2 ^ (2 * w)) n
    (Nat.succ_le_of_lt (Nat.two_pow_pos (2 * w)))
  have hpow : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by
    rw [two_mul, pow_add]
  have hsub : 2 ^ (2 * w) - 1 = (2 ^ w + 1) * (2 ^ w - 1) := by
    have := Nat.sub_add_cancel hq
    rw [hpow]
    have hs := Nat.sub_add_cancel (show 1 ≤ 2 ^ w * 2 ^ w by nlinarith)
    nlinarith
  have hall : 2 ^ (2 * w * n) - 1 =
      (2 ^ w + 1) * ((2 ^ w - 1) * pack (2 ^ (2 * w)) n (fun _ => 1)) := by
    rw [pow_mul, ← hr, Nat.add_sub_cancel, hsub]
    ring
  rw [hall, Nat.mul_div_cancel_left _ (by positivity)]
  exact (pack_const _ _ _).symm

/-- One parallel pairwise population-count step. -/
def mergeCounts (w n x : ℕ) : ℕ :=
  RosserScan.forceNat ((2 ^ (2 * w * n) - 1) / (2 ^ w + 1)) fun stripe =>
    (x &&& stripe) + ((x >>> w) &&& stripe)

theorem mergeCounts_sound (w n : ℕ) (hw : 0 < w) (f : ℕ → ℕ)
    (hf : ∀ i < 2 * n, f i < 2 ^ w) :
    mergeCounts w n (pack (2 ^ w) (2 * n) f) =
      pack (2 ^ (2 * w)) n (fun i => f (2 * i) + f (2 * i + 1)) := by
  have hq : 0 < 2 ^ w := by positivity
  have hpow : 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by rw [two_mul, pow_add]
  let g := fun i => f (2 * i) + 2 ^ w * f (2 * i + 1)
  have hg : ∀ i < n, g i < 2 ^ (2 * w) := by
    intro i hi
    have h0 := hf (2 * i) (by omega)
    have h1 := hf (2 * i + 1) (by omega)
    dsimp [g]
    rw [← hpow]
    nlinarith
  have hm : ∀ i < n, 2 ^ w - 1 < 2 ^ (2 * w - w) := by
    intro i hi
    rw [show 2 * w - w = w by omega]
    omega
  have hlo : ∀ i < n, (g i &&& (2 ^ w - 1)) = f (2 * i) := by
    intro i hi
    simp only [g, Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hf (2 * i) (by omega))]
  have hhi : ∀ i < n, ((g i >>> w) &&& (2 ^ w - 1)) = f (2 * i + 1) := by
    intro i hi
    simp only [g, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ hq,
      Nat.div_eq_of_lt (hf (2 * i) (by omega)), Nat.zero_add,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hf (2 * i + 1) (by omega))]
  simp only [mergeCounts, forceNat_eq, stripe_eq w n hw, pack_pair, hpow]
  change (pack (2 ^ (2 * w)) n g &&& pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1)) +
    ((pack (2 ^ (2 * w)) n g >>> w) &&& pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1)) = _
  rw [pack_and (2 * w) n (by omega) g _ hg (fun i hi => (hm i hi).trans_le
    (Nat.pow_le_pow_right (by omega) (by omega))),
    pack_shift_and (2 * w) n w (by omega) (by omega) g _ hg hm, ← pack_add]
  apply pack_congr
  intro i hi
  rw [hlo i hi, hhi i hi]

def bitValue (mask i : ℕ) : ℕ := (mask.testBit i).toNat

theorem bitValue_le_one (mask i : ℕ) : bitValue mask i ≤ 1 := by
  unfold bitValue
  cases mask.testBit i <;> decide

theorem bitValue_eq_digit (mask i : ℕ) : bitValue mask i = mask / 2 ^ i % 2 := by
  simp only [bitValue, Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_lt (mask / 2 ^ i) (by omega : 0 < 2)
  by_cases heq : mask / 2 ^ i % 2 = 1
  · simp [heq]
  · have hz : mask / 2 ^ i % 2 = 0 := by omega
    simp [hz]

theorem candidateCount_eq_sum (mask d : ℕ) :
    candidateCount mask d = prefixSum (bitValue mask) d := by
  induction d with
  | zero => simp [candidateCount, prefixSum]
  | succ d ih =>
    simp only [candidateCount, List.range_succ, List.filter_append, List.length_append,
      prefixSum, Finset.sum_range_succ] at *
    rw [ih]
    cases h : mask.testBit d <;> simp [List.filter, bitValue, h]

def blockSum (f : ℕ → ℕ) (w j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range w, f (w * j + i)

@[simp] theorem blockSum_one (f : ℕ → ℕ) (j : ℕ) : blockSum f 1 j = f j := by
  simp [blockSum]

theorem blockSum_le (f : ℕ → ℕ) (hf : ∀ i, f i ≤ 1) (w j : ℕ) :
    blockSum f w j ≤ w := by
  calc
    _ ≤ ∑ _i ∈ Finset.range w, 1 := Finset.sum_le_sum (fun i hi => hf _)
    _ = _ := by simp

theorem blockSum_pair (f : ℕ → ℕ) (w j : ℕ) :
    blockSum f (2 * w) j = blockSum f w (2 * j) + blockSum f w (2 * j + 1) := by
  unfold blockSum
  rw [show 2 * w = w + w by omega, Finset.sum_range_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> congr 1 <;> ring

theorem prefixSum_blocks (f : ℕ → ℕ) (w n : ℕ) :
    prefixSum (blockSum f w) n = prefixSum f (w * n) := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    change (∑ i ∈ Finset.range (n + 1), blockSum f w i) = _
    rw [Finset.sum_range_succ]
    change prefixSum (blockSum f w) n + blockSum f w n = _
    rw [ih, Nat.mul_add, Nat.mul_one]
    simp only [prefixSum, blockSum, Finset.sum_range_add]

theorem mergeCounts_blocks (w n : ℕ) (hw : 0 < w) (f : ℕ → ℕ)
    (hf : ∀ i, f i ≤ 1) :
    mergeCounts w n (pack (2 ^ w) (2 * n) (blockSum f w)) =
      pack (2 ^ (2 * w)) n (blockSum f (2 * w)) := by
  rw [mergeCounts_sound w n hw _ (fun i hi =>
    (blockSum_le f hf w i).trans_lt Nat.lt_two_pow_self)]
  apply pack_congr
  intro i hi
  exact (blockSum_pair f w i).symm

/-- Five pairwise merge stages give one population count per 32-bit digit. -/
def packedCounts32 (mask n : ℕ) : ℕ :=
  RosserScan.forceNat (mergeCounts 1 (16 * n) mask) fun x =>
  RosserScan.forceNat (mergeCounts 2 (8 * n) x) fun x =>
  RosserScan.forceNat (mergeCounts 4 (4 * n) x) fun x =>
  RosserScan.forceNat (mergeCounts 8 (2 * n) x) fun x =>
    mergeCounts 16 n x

theorem packedCounts32_sound (mask n : ℕ) (hm : mask < 2 ^ (32 * n)) :
    packedCounts32 mask n = pack (2 ^ 32) n (blockSum (bitValue mask) 32) := by
  have hzero : pack 2 (32 * n) (blockSum (bitValue mask) 1) = mask := by
    calc
      _ = pack 2 (32 * n) (fun i => mask / 2 ^ i % 2) := by
        apply pack_congr
        intro i hi
        rw [blockSum_one, bitValue_eq_digit]
      _ = mask := by
        simpa only [Nat.one_mul, pow_one] using
          pack_digits 1 (32 * n) mask (by omega) (by simpa using hm)
  have h1 := mergeCounts_blocks 1 (16 * n) (by omega) (bitValue mask) (bitValue_le_one mask)
  have h2 := mergeCounts_blocks 2 (8 * n) (by omega) (bitValue mask) (bitValue_le_one mask)
  have h4 := mergeCounts_blocks 4 (4 * n) (by omega) (bitValue mask) (bitValue_le_one mask)
  have h8 := mergeCounts_blocks 8 (2 * n) (by omega) (bitValue mask) (bitValue_le_one mask)
  have h16 := mergeCounts_blocks 16 n (by omega) (bitValue mask) (bitValue_le_one mask)
  norm_num only [← Nat.mul_assoc, Nat.reduceMul] at h1 h2 h4 h8 h16
  rw [hzero] at h1
  simp only [packedCounts32, forceNat_eq, h1, h2, h4, h8, h16]
  norm_num

/-- With half-width guards, subtraction is digitwise and every comparison is checked. -/
theorem guard_sound32 (n : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ i < n, f i < 2 ^ 31) (hg : ∀ i < n, g i < 2 ^ 31)
    (hcheck :
      ((pack (2 ^ 32) n g + pack (2 ^ 32) n (fun _ => 2 ^ 31) -
        pack (2 ^ 32) n f) &&& pack (2 ^ 32) n (fun _ => 2 ^ 31)) =
          pack (2 ^ 32) n (fun _ => 2 ^ 31)) :
    ∀ i < n, f i ≤ g i := by
  have hsub :
      pack (2 ^ 32) n g + pack (2 ^ 32) n (fun _ => 2 ^ 31) - pack (2 ^ 32) n f =
        pack (2 ^ 32) n (fun i => g i + 2 ^ 31 - f i) := by
    rw [← pack_add, pack_sub]
    intro i hi
    have := hf i hi
    omega
  rw [hsub] at hcheck
  have hout : ∀ i < n, g i + 2 ^ 31 - f i < 2 ^ 32 := by
    intro i hi
    have := hg i hi
    omega
  intro i hi
  have hb := congrArg (fun x : ℕ => x.testBit (32 * i + 31)) hcheck
  rw [Nat.testBit_and, pack_testBit 32 n i 31 hout hi (by omega),
    pack_testBit 32 n i 31 (by intro j hj; norm_num) hi (by omega)] at hb
  have hguard : (2 ^ 31 : ℕ).testBit 31 = true := by decide
  simp only [hguard, Bool.and_true] at hb
  simp only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb
  have := hout i hi
  omega

theorem pack_index_identity (q n : ℕ) (hq : 1 ≤ q) (hn : 0 < n) :
    (q - 1) * pack q n (fun i => i) + pack q n (fun _ => 1) =
      (n - 1) * q ^ n + 1 := by
  have hprefix := pack_prefix_identity q n (fun _ => 1) hq
  have heq : pack q n (fun i => prefixSum (fun _ => 1) (i + 1)) =
      pack q n (fun i => i) + pack q n (fun _ => 1) := by
    rw [← pack_add]
    apply pack_congr
    intro i hi
    simp [prefixSum]
  rw [heq] at hprefix
  simp [prefixSum] at hprefix
  have hr := pack_one_identity q n hq
  have hn' := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hn'' := congrArg (fun x => x * q ^ n) hn'
  nlinarith

theorem pack_index_eq (q n : ℕ) (hq : 1 < q) (hn : 0 < n) :
    pack q n (fun i => i) =
      ((n - 1) * q ^ n + 1 - pack q n (fun _ => 1)) / (q - 1) := by
  have h := pack_index_identity q n (by omega) hn
  have heq : (n - 1) * q ^ n + 1 - pack q n (fun _ => 1) =
      (q - 1) * pack q n (fun i => i) := by omega
  rw [heq, Nat.mul_div_cancel_left _ (by omega)]

def checkFromCounts (counts n intercept slope : ℕ) : Bool :=
  RosserScan.forceNat (32 * n) fun L =>
  RosserScan.forceNat ((2 ^ L - 1) / (2 ^ 32 - 1)) fun R =>
  RosserScan.forceNat ((((counts <<< L) - counts) / (2 ^ 32 - 1)) % 2 ^ L) fun pref =>
  RosserScan.forceNat (32 * (((n - 1) * 2 ^ L + 1 - R) / (2 ^ 32 - 1))) fun pos =>
  RosserScan.forceNat (16384 * pref) fun lhs =>
  RosserScan.forceNat (intercept * R + slope * pos) fun rhs =>
  RosserScan.forceNat (2 ^ 31 * R) fun guard =>
    decide (((rhs + guard - lhs) &&& guard) = guard)

theorem packed_prefix_formula (n : ℕ) (f : ℕ → ℕ)
    (hsum : prefixSum f n < 2 ^ 32) :
    ((((pack (2 ^ 32) n f <<< (32 * n)) - pack (2 ^ 32) n f) /
      (2 ^ 32 - 1)) % 2 ^ (32 * n)) =
      pack (2 ^ 32) n (fun i => prefixSum f (i + 1)) := by
  have hr := pack_one_identity (2 ^ 32) n (by norm_num)
  have hp : 2 ^ (32 * n) - 1 =
      (2 ^ 32 - 1) * pack (2 ^ 32) n (fun _ => 1) := by
    rw [pow_mul]
    omega
  rw [Nat.shiftLeft_eq]
  have hnum : pack (2 ^ 32) n f * 2 ^ (32 * n) - pack (2 ^ 32) n f =
      (pack (2 ^ 32) n f * pack (2 ^ 32) n (fun _ => 1)) * (2 ^ 32 - 1) := by
    calc
      _ = pack (2 ^ 32) n f * (2 ^ (32 * n) - 1) := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = _ := by rw [hp]; ring
  rw [hnum, Nat.mul_div_cancel _ (by norm_num), pow_mul]
  exact pack_prefix_mod (2 ^ 32) n f (by norm_num) hsum

/-- The prefix/guard stage, with a semantic specification for its packed count input. -/
theorem checkFromCounts_sound (n intercept slope : ℕ) (f : ℕ → ℕ)
    (hn : 0 < n) (hcount : 16384 * prefixSum f n < 2 ^ 31)
    (hrhs : intercept + slope * (32 * (n - 1)) < 2 ^ 31)
    (hcheck : checkFromCounts (pack (2 ^ 32) n f) n intercept slope = true) :
    ∀ i < n, 16384 * prefixSum f (i + 1) ≤ intercept + slope * (32 * i) := by
  have hsum : prefixSum f n < 2 ^ 32 := by omega
  have hR : (2 ^ (32 * n) - 1) / (2 ^ 32 - 1) =
      pack (2 ^ 32) n (fun _ => 1) := by
    rw [pack_const_one _ _ (by norm_num), pow_mul]
  have hpos : ((n - 1) * 2 ^ (32 * n) + 1 - pack (2 ^ 32) n (fun _ => 1)) /
      (2 ^ 32 - 1) = pack (2 ^ 32) n (fun i => i) := by
    rw [pack_index_eq _ _ (by norm_num) hn, pow_mul]
  simp only [checkFromCounts, forceNat_eq, decide_eq_true_eq] at hcheck
  rw [hR, packed_prefix_formula n f hsum, hpos] at hcheck
  have hguard := guard_sound32 n
    (fun i => 16384 * prefixSum f (i + 1))
    (fun i => intercept + slope * (32 * i))
  apply hguard
  · intro i hi
    exact (Nat.mul_le_mul_left _ (prefixSum_mono f (by omega))).trans_lt hcount
  · intro i hi
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left slope
      (Nat.mul_le_mul_left 32 (by omega : i ≤ n - 1))) intercept).trans_lt hrhs
  · simp only [pack_add, pack_mul, pack_const (2 ^ 32) n intercept,
      pack_const (2 ^ 32) n (2 ^ 31)]
    rw [show pack (2 ^ 32) n (HMul.hMul 32) =
      32 * pack (2 ^ 32) n (fun i => i) from pack_mul (2 ^ 32) n 32 (fun i => i)]
    exact hcheck

theorem candidateCount_mono (mask : ℕ) {a b : ℕ} (h : a ≤ b) :
    candidateCount mask a ≤ candidateCount mask b := by
  rw [candidateCount_eq_sum, candidateCount_eq_sum]
  exact prefixSum_mono _ h

theorem bitValue_eq_zero (mask len i : ℕ) (hm : mask < 2 ^ len) (hi : len ≤ i) :
    bitValue mask i = 0 := by
  have hb := Nat.testBit_eq_false_of_lt
    (hm.trans_le (Nat.pow_le_pow_right (by omega) hi))
  simp [bitValue, hb]

theorem candidateCount_pad (mask len top : ℕ) (hm : mask < 2 ^ len) (hl : len ≤ top) :
    candidateCount mask top = candidateCount mask len := by
  rw [candidateCount_eq_sum, candidateCount_eq_sum]
  have ht : top = len + (top - len) := by omega
  rw [ht]
  simp only [prefixSum, Finset.sum_range_add]
  have hz : ∑ i ∈ Finset.range (top - len), bitValue mask (len + i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact bitValue_eq_zero mask len (len + i) hm (by omega)
  rw [hz, Nat.add_zero]

def packedCheck (mask len intercept slope : ℕ) : Bool :=
  RosserScan.forceNat ((len + 31) / 32) fun n =>
  RosserScan.forceNat (packedCounts32 mask n) fun counts =>
    checkFromCounts counts n intercept slope

/-- A successful packed test bounds every candidate prefix, including a partial final bucket. -/
theorem packedCheck_sound (mask len intercept slope : ℕ)
    (hlen : 0 < len) (hm : mask < 2 ^ len)
    (hcount : 16384 * candidateCount mask len < 2 ^ 31)
    (hrhs : intercept + slope * (32 * ((len + 31) / 32 - 1)) < 2 ^ 31)
    (hcheck : packedCheck mask len intercept slope = true) :
    ∀ d ≤ len, 16384 * candidateCount mask d ≤
      intercept + slope * 32 * ((d - 1) / 32) := by
  let n := (len + 31) / 32
  have hn : 0 < n := by dsimp [n]; omega
  have hl : len ≤ 32 * n := by dsimp [n]; omega
  have hm32 : mask < 2 ^ (32 * n) :=
    hm.trans_le (Nat.pow_le_pow_right (by omega) hl)
  have hsum : prefixSum (blockSum (bitValue mask) 32) n = candidateCount mask len := by
    rw [prefixSum_blocks, ← candidateCount_eq_sum, candidateCount_pad mask len _ hm hl]
  have hc : checkFromCounts (pack (2 ^ 32) n (blockSum (bitValue mask) 32))
      n intercept slope = true := by
    simp only [packedCheck, forceNat_eq] at hcheck
    change checkFromCounts (packedCounts32 mask n) n intercept slope = true at hcheck
    rw [packedCounts32_sound mask n hm32] at hcheck
    exact hcheck
  have hbound := checkFromCounts_sound n intercept slope (blockSum (bitValue mask) 32)
    hn (by simpa only [hsum] using hcount) hrhs hc
  intro d hd
  by_cases hz : d = 0
  · subst d
    simp [candidateCount]
  · have hi : (d - 1) / 32 < n := by dsimp [n]; omega
    have hend : d ≤ 32 * ((d - 1) / 32 + 1) := by omega
    have hb := hbound ((d - 1) / 32) hi
    rw [prefixSum_blocks, ← candidateCount_eq_sum] at hb
    exact (Nat.mul_le_mul_left 16384 (candidateCount_mono mask hend)).trans
      (by simpa only [Nat.mul_assoc] using hb)

end RosserPackedBarrier
namespace RosserBitMoments

open RosserBitSieve AlternativeProductMoments

theorem moments_append (xs ys : List ℕ) :
    moments (xs ++ ys) = merge (moments xs) (moments ys) := by
  simp [moments, merge, List.map_append, List.sum_append]

theorem moments_shift (ds : List ℕ) (offset : ℕ) :
    moments (ds.map (fun d => offset + d)) = translate offset (moments ds) := by
  induction ds with
  | nil => simp [moments, translate]
  | cons d ds ih =>
    have hi := congrArg (fun s : Moments => s.2.1) ih
    have hj := congrArg (fun s : Moments => s.2.2) ih
    simp only [moments, translate] at hi hj
    apply Moments.ext
    · simp [moments, translate]
    · simp only [moments, translate, List.map_cons, List.sum_cons, List.length_cons]
      rw [hi]
      ring
    · simp only [moments, translate, List.map_cons, List.sum_cons, List.length_cons]
      rw [hj]
      ring

theorem moments_perm {xs ys : List ℕ} (h : xs.Perm ys) : moments xs = moments ys := by
  apply Moments.ext
  · exact h.length_eq
  · exact h.sum_eq
  · exact (h.map (fun (d : ℕ) => d ^ 2)).sum_eq

theorem enumBits_shift (depth start mask : ℕ) :
    enumBits depth start mask = (enumBits depth 0 mask).map (fun d => start + d) := by
  induction depth generalizing start mask with
  | zero => simp only [enumBits]; split <;> simp
  | succ depth ih =>
    simp only [enumBits]
    split
    · simp
    · rw [ih start, ih (start + 2 ^ depth), ih (0 + 2 ^ depth), List.map_append,
        List.map_map]
      simp only [Nat.zero_add, Function.comp_def, Nat.add_assoc]

theorem enumBits_mod_perm (depth start mask : ℕ) :
    (enumBits depth start (mask % 2 ^ (2 ^ depth))).Perm (enumBits depth start mask) := by
  apply (List.perm_ext_iff_of_nodup (enumBits_nodup _ _ _) (enumBits_nodup _ _ _)).mpr
  intro x
  simp only [mem_enumBits, Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hlo, hhi, _, hb⟩
    exact ⟨hlo, hhi, hb⟩
  · rintro ⟨hlo, hhi, hb⟩
    exact ⟨hlo, hhi, by omega, hb⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem byteMoments_table : ∀ byte : Fin 256,
    byteMoments byte = moments (enumBits 3 0 byte) := by decide +kernel

theorem byteMoments_sound (mask : ℕ) :
    byteMoments (mask % 256) = moments (enumBits 3 0 mask) := by
  have h := byteMoments_table ⟨mask % 256, Nat.mod_lt _ (by decide)⟩
  have hm := moments_perm (enumBits_mod_perm 3 0 mask)
  norm_num only [Nat.reducePow] at hm
  exact h.trans hm

theorem fastMoments_sound (depth start mask : ℕ) :
    fastMoments depth start mask = moments (enumBits (depth + 3) start mask) := by
  induction depth generalizing start mask with
  | zero =>
    rw [fastMoments, byteMoments_sound, enumBits_shift 3 start mask, moments_shift]
  | succ depth ih =>
    change (if mask == 0 then _ else _) =
      moments (enumBits ((depth + 3) + 1) start mask)
    rw [enumBits]
    split
    · rfl
    · dsimp only
      rw [moments_append, ih, ih]

theorem windowMoments_sound (mask shift len : ℕ) :
    windowMoments mask shift len = moments (windowOffsets 13 mask shift len) := by
  rw [windowMoments, fastMoments_sound]
  change moments (enumBits 13 1 _) = _
  rw [enumBits_shift]
  simp only [windowOffsets, Nat.add_comm]

theorem stepFromMoments_eq (v a : ℕ) (ds : List ℕ) :
    stepFromMoments v a (moments ds) = momentStep v a ds := by
  rfl

theorem fastMomentStep_eq (v a mask shift len : ℕ) :
    fastMomentStep v a mask shift len =
      momentStep v a (windowOffsets 13 mask shift len) := by
  rw [fastMomentStep, windowMoments_sound, stepFromMoments_eq]

end RosserBitMoments
namespace RosserPrefixBridge

open RosserPackedBarrier

theorem prime_card_le_candidateCount (a b n mask : ℕ)
    (han : a ≤ n) (hnb : n ≤ b)
    (hcover : ∀ p, Nat.Prime p → a < p → p ≤ b →
      mask.testBit (p - (a + 1)) = true) :
    (Nat.primesLE n \ Nat.primesLE a).card ≤
      candidateCount mask (n - a) := by
  let t := Nat.primesLE n \ Nat.primesLE a
  let s := (List.range (n - a)).filter (fun i => mask.testBit i)
  have hmap : Set.MapsTo (fun p : ℕ => p - (a + 1))
      (t : Set ℕ) (s.toFinset : Set ℕ) := by
    intro p hp
    obtain ⟨hpn, hpa⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpn', hpprime⟩ := Nat.mem_primesLE.mp hpn
    have hap : a < p := by
      by_contra h
      exact hpa (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_range.mpr
      change p - (a + 1) < n - a
      omega
    · exact hcover p hpprime hap (by omega)
  have hinj : (t : Set ℕ).InjOn
      (fun p : ℕ => p - (a + 1)) := by
    intro p hp q hq heq
    have hp' := Finset.mem_sdiff.mp hp
    have hq' := Finset.mem_sdiff.mp hq
    have hpprime := (Nat.mem_primesLE.mp hp'.1).2
    have hqprime := (Nat.mem_primesLE.mp hq'.1).2
    have hap : a < p := by
      by_contra h
      exact hp'.2 (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
    have haq : a < q := by
      by_contra h
      exact hq'.2 (Nat.mem_primesLE.mpr ⟨by omega, hqprime⟩)
    change p - (a + 1) = q - (a + 1) at heq
    omega
  have hc := Finset.card_le_card_of_injOn (fun p : ℕ => p - (a + 1)) hmap hinj
  have hs : s.toFinset.card ≤ s.length := List.toFinset_card_le s
  have hfinal := hc.trans hs
  simpa only [t, s, candidateCount] using hfinal

end RosserPrefixBridge
namespace RosserPackedMoments

open RosserBitMoments RosserScan

def strictMoments {α : Type} (s : Moments) (f : Moments → α) : α :=
  forceNat s.1 fun c => forceNat s.2.1 fun a => forceNat s.2.2 fun b =>
    f ⟨c, a, b⟩

def bytes (mask stripe : Nat) : Nat → Moments → Moments
  | 0, s => s
  | j + 1, s =>
    forceNat ((mask >>> j) &&& stripe) fun bit =>
      strictMoments ⟨s.1 + bit, s.2.1 + j * bit, s.2.2 + j * j * bit⟩
        (bytes mask stripe j)

def combine (bits half : Nat) (s : Moments) : Moments :=
  let stripe := RosserBitSieve.periodicMask (2 * half) (bits / (2 * half)) *
    (2 ^ half - 1)
  forceNat stripe fun stripe =>
  forceNat ((s.1 >>> half) &&& stripe) fun cr =>
  forceNat ((s.2.1 >>> half) &&& stripe) fun fr =>
    ⟨(s.1 &&& stripe) + cr,
     (s.2.1 &&& stripe) + fr + half * cr,
     (s.2.2 &&& stripe) + ((s.2.2 >>> half) &&& stripe) +
       2 * half * fr + half * half * cr⟩

def reduce (bits : Nat) : Nat → Nat → Moments → Moments
  | 0, _, s => s
  | fuel + 1, half, s =>
    strictMoments (combine bits half s) (reduce bits fuel (2 * half))

def packedMoments (depth mask : Nat) : Moments :=
  let bits := 2 ^ (depth + 3)
  forceNat (RosserBitSieve.periodicMask 8 (bits / 8)) fun stripe =>
    strictMoments (bytes mask stripe 8 ⟨0, 0, 0⟩) fun s =>
      translate 1 (reduce bits depth 8 s)



open RosserPackedBarrier

theorem strictMoments_eq {α : Type} (s : Moments) (f : Moments → α) :
    strictMoments s f = f s := by
  rcases s with ⟨c, u, t⟩
  simp only [strictMoments, RosserPackedBarrier.forceNat_eq]

def packed (w n : ℕ) (f : ℕ → Moments) : Moments :=
  ⟨pack (2 ^ w) n (fun i => (f i).1),
   pack (2 ^ w) n (fun i => (f i).2.1),
   pack (2 ^ w) n (fun i => (f i).2.2)⟩

def lane (mask w i : ℕ) : Moments :=
  ⟨∑ j ∈ Finset.range w, bitValue mask (w * i + j),
   ∑ j ∈ Finset.range w, j * bitValue mask (w * i + j),
   ∑ j ∈ Finset.range w, j * j * bitValue mask (w * i + j)⟩

theorem pair_extract (w n : ℕ) (hw : 0 < w) (f : ℕ → ℕ)
    (hf : ∀ i < 2 * n, f i < 2 ^ w) :
    let stripe := pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1)
    (pack (2 ^ w) (2 * n) f &&& stripe =
      pack (2 ^ (2 * w)) n (fun i => f (2 * i))) ∧
    ((pack (2 ^ w) (2 * n) f >>> w) &&& stripe =
      pack (2 ^ (2 * w)) n (fun i => f (2 * i + 1))) := by
  dsimp only
  have hq : 0 < 2 ^ w := by positivity
  have hpow : 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by rw [two_mul, pow_add]
  let g := fun i => f (2 * i) + 2 ^ w * f (2 * i + 1)
  have hg : ∀ i < n, g i < 2 ^ (2 * w) := by
    intro i hi
    have h0 := hf (2 * i) (by omega)
    have h1 := hf (2 * i + 1) (by omega)
    dsimp [g]
    rw [← hpow]
    nlinarith
  have hm : ∀ i < n, 2 ^ w - 1 < 2 ^ (2 * w - w) := by
    intro i hi
    rw [show 2 * w - w = w by omega]
    omega
  rw [pack_pair, hpow]
  change (_ &&& _) = _ ∧ (_ >>> w &&& _) = _
  constructor
  · rw [pack_and (2 * w) n (by omega) g _ hg (fun i hi => (hm i hi).trans_le
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    apply pack_congr
    intro i hi
    simp only [g, Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hf (2 * i) (by omega))]
  · rw [pack_shift_and (2 * w) n w (by omega) (by omega) g _ hg hm]
    apply pack_congr
    intro i hi
    simp only [g, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ hq,
      Nat.div_eq_of_lt (hf (2 * i) (by omega)), Nat.zero_add,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hf (2 * i + 1) (by omega))]

theorem combine_sound (w n : ℕ) (hw : 0 < w) (f : ℕ → Moments)
    (hc : ∀ i < 2 * n, (f i).1 < 2 ^ w)
    (hf : ∀ i < 2 * n, (f i).2.1 < 2 ^ w)
    (hs : ∀ i < 2 * n, (f i).2.2 < 2 ^ w) :
    combine (2 * w * n) w (packed w (2 * n) f) =
      packed (2 * w) n (fun i => merge (f (2 * i)) (translate w (f (2 * i + 1)))) := by
  have hstripe : RosserBitSieve.periodicMask (2 * w) ((2 * w * n) / (2 * w)) *
      (2 ^ w - 1) = pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1) := by
    rw [Nat.mul_div_cancel_left _ (by omega), pack_const]
    unfold RosserBitSieve.periodicMask
    rw [pack_const_one _ _ (Nat.one_lt_two_pow (by omega)), pow_mul]
    ring
  obtain ⟨hcl, hcr⟩ := pair_extract w n hw (fun i => (f i).1) hc
  obtain ⟨hfl, hfr⟩ := pair_extract w n hw (fun i => (f i).2.1) hf
  obtain ⟨hsl, hsr⟩ := pair_extract w n hw (fun i => (f i).2.2) hs
  simp only [combine, RosserPackedBarrier.forceNat_eq, hstripe, packed]
  rw [hcl, hcr, hfl, hfr, hsl, hsr]
  apply Moments.ext <;> simp only [merge, translate, pack_add, pack_mul] <;> ring

theorem lane_pair (mask w i : ℕ) :
    lane mask (2 * w) i = merge (lane mask w (2 * i))
      (translate w (lane mask w (2 * i + 1))) := by
  apply Moments.ext
  · exact blockSum_pair (bitValue mask) w i
  · simp only [lane, merge, translate]
    rw [show 2 * w = w + w by omega, Finset.sum_range_add]
    have hpos : ∀ j : ℕ, (w + w) * i + (w + j) = w * (2 * i + 1) + j := by
      intro j; ring
    have hpos' : ∀ j : ℕ, (w + w) * i + j = w * (2 * i) + j := by
      intro j; ring
    simp only [hpos, hpos']
    have hsum :
        (∑ j ∈ Finset.range w, (w + j) * bitValue mask (w * (2 * i + 1) + j)) =
        w * (∑ j ∈ Finset.range w, bitValue mask (w * (2 * i + 1) + j)) +
        (∑ j ∈ Finset.range w, j * bitValue mask (w * (2 * i + 1) + j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    ring
  · simp only [lane, merge, translate]
    rw [show 2 * w = w + w by omega, Finset.sum_range_add]
    have hpos : ∀ j : ℕ, (w + w) * i + (w + j) = w * (2 * i + 1) + j := by
      intro j; ring
    have hpos' : ∀ j : ℕ, (w + w) * i + j = w * (2 * i) + j := by
      intro j; ring
    simp only [hpos, hpos']
    have hsum :
        (∑ j ∈ Finset.range w, (w + j) * (w + j) * bitValue mask (w * (2 * i + 1) + j)) =
        (∑ j ∈ Finset.range w, j * j * bitValue mask (w * (2 * i + 1) + j)) +
        2 * w * (∑ j ∈ Finset.range w, j * bitValue mask (w * (2 * i + 1) + j)) +
        w * w * (∑ j ∈ Finset.range w, bitValue mask (w * (2 * i + 1) + j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    ring

theorem bytes_eq (mask stripe j : ℕ) (s : Moments) :
    bytes mask stripe j s =
      ⟨s.1 + ∑ i ∈ Finset.range j, ((mask >>> i) &&& stripe),
       s.2.1 + ∑ i ∈ Finset.range j, i * ((mask >>> i) &&& stripe),
       s.2.2 + ∑ i ∈ Finset.range j, i * i * ((mask >>> i) &&& stripe)⟩ := by
  induction j generalizing s with
  | zero => simp [bytes]
  | succ j ih =>
    simp only [bytes, RosserPackedBarrier.forceNat_eq, strictMoments_eq, ih, Finset.sum_range_succ]
    apply Moments.ext <;> dsimp only <;> ring

theorem pack_sum (q n terms : ℕ) (f : ℕ → ℕ → ℕ) :
    pack q n (fun i => ∑ j ∈ Finset.range terms, f i j) =
      ∑ j ∈ Finset.range terms, pack q n (fun i => f i j) := by
  induction terms with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; rw [pack_const q n 0]; simp
  | succ terms ih => simp only [Finset.sum_range_succ, pack_add, ih]

theorem byte_plane (mask n j : ℕ) (hj : j < 8) (hm : mask < 2 ^ (8 * n)) :
    ((mask >>> j) &&& RosserBitSieve.periodicMask 8 n) =
      pack 256 n (fun i => bitValue mask (8 * i + j)) := by
  let f := fun i => mask / 2 ^ (8 * i) % 2 ^ 8
  have hf : ∀ i < n, f i < 2 ^ 8 := fun i hi => Nat.mod_lt _ (by positivity)
  have hp : pack (2 ^ 8) n f = mask := pack_digits 8 n mask (by omega) hm
  have hs : RosserBitSieve.periodicMask 8 n = pack (2 ^ 8) n (fun _ => 1) := by
    unfold RosserBitSieve.periodicMask
    rw [pack_const_one _ _ (by norm_num), pow_mul]
  rw [← hp, hs, pack_shift_and 8 n j (by omega) (by omega) f _ hf
    (fun i hi => Nat.one_lt_two_pow (by omega))]
  have hbase : (2 ^ 8 : ℕ) = 256 := by norm_num
  rw [hbase]
  apply pack_congr
  intro i hi
  have hb := pack_testBit 8 n i j hf hi hj
  rw [hp] at hb
  simp only [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [← bitValue_eq_digit]
  rw [← hbase, hp]
  exact (congrArg Bool.toNat hb).symm

theorem bytes_sound (mask n : ℕ) (hm : mask < 2 ^ (8 * n)) :
    bytes mask (RosserBitSieve.periodicMask 8 n) 8 ⟨0, 0, 0⟩ =
      packed 8 n (lane mask 8) := by
  rw [bytes_eq]
  apply Moments.ext <;> simp only [packed, lane, Nat.zero_add, pack_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    exact byte_plane mask n j (Finset.mem_range.mp hj) hm
  · apply Finset.sum_congr rfl
    intro j hj
    rw [byte_plane mask n j (Finset.mem_range.mp hj) hm, pack_mul]
    norm_num
  · apply Finset.sum_congr rfl
    intro j hj
    rw [byte_plane mask n j (Finset.mem_range.mp hj) hm, pack_mul]
    norm_num


def laneBudget (w : ℕ) : ℕ := ∑ j ∈ Finset.range w, (j + 1) ^ 2

theorem lane_le_budget (mask w i : ℕ) :
    (lane mask w i).1 ≤ laneBudget w ∧
    (lane mask w i).2.1 ≤ laneBudget w ∧
    (lane mask w i).2.2 ≤ laneBudget w := by
  have hb := fun j => bitValue_le_one mask (w * i + j)
  dsimp only [lane, laneBudget]
  constructor
  · apply Finset.sum_le_sum
    intro j hj
    exact (hb j).trans (Nat.succ_le_of_lt (by positivity))
  constructor
  · apply Finset.sum_le_sum
    intro j hj
    have := hb j
    nlinarith
  · apply Finset.sum_le_sum
    intro j hj
    have h := Nat.mul_le_mul_left (j * j) (hb j)
    simp only [Nat.mul_one] at h
    nlinarith

theorem laneBudget_le_cube (w : ℕ) : laneBudget w ≤ w ^ 3 := by
  calc
    laneBudget w ≤ ∑ j ∈ Finset.range w, w ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have h := Finset.mem_range.mp hj
      exact Nat.pow_le_pow_left (by omega) 2
    _ = w ^ 3 := by simp; ring

theorem triple_lt_power (d : ℕ) : 3 * (d + 4) < 2 ^ (d + 4) := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [show d + 1 + 4 = (d + 4) + 1 by omega, pow_succ]
    omega

theorem laneBudget_lt (d : ℕ) : laneBudget (2 ^ (d + 3)) < 2 ^ (2 ^ (d + 3)) := by
  cases d with
  | zero => decide
  | succ d =>
    have h := laneBudget_le_cube (2 ^ (d + 4))
    have hp : (2 ^ (d + 4)) ^ 3 < 2 ^ (2 ^ (d + 4)) := by
      rw [← pow_mul]
      apply Nat.pow_lt_pow_right (by omega)
      simpa only [Nat.mul_comm] using triple_lt_power d
    simpa only [Nat.add_assoc] using h.trans_lt hp

theorem packed_congr (w n : ℕ) {f g : ℕ → Moments}
    (h : ∀ i < n, f i = g i) : packed w n f = packed w n g := by
  apply Moments.ext <;> apply pack_congr <;> intro i hi <;> rw [h i hi]

theorem combine_lane (d n mask : ℕ) :
    combine (2 * 2 ^ (d + 3) * n) (2 ^ (d + 3))
      (packed (2 ^ (d + 3)) (2 * n) (lane mask (2 ^ (d + 3)))) =
      packed (2 * 2 ^ (d + 3)) n (lane mask (2 * 2 ^ (d + 3))) := by
  have hb := laneBudget_lt d
  rw [combine_sound _ _ (by positivity) _
    (fun i hi => ((lane_le_budget mask _ i).1).trans_lt hb)
    (fun i hi => ((lane_le_budget mask _ i).2.1).trans_lt hb)
    (fun i hi => ((lane_le_budget mask _ i).2.2).trans_lt hb)]
  apply packed_congr
  intro i hi
  exact (lane_pair mask _ i).symm

theorem reduce_sound (fuel d mask : ℕ) :
    reduce (2 ^ (fuel + d + 3)) fuel (2 ^ (d + 3))
      (packed (2 ^ (d + 3)) (2 ^ fuel) (lane mask (2 ^ (d + 3)))) =
      lane mask (2 ^ (fuel + d + 3)) 0 := by
  induction fuel generalizing d with
  | zero => simp [reduce, packed, pack]
  | succ fuel ih =>
    have hbits : 2 ^ (fuel + 1 + d + 3) = 2 * 2 ^ (d + 3) * 2 ^ fuel := by
      rw [show fuel + 1 + d + 3 = 1 + (d + 3) + fuel by omega]
      simp only [pow_add, pow_one]
    have hnext : 2 * 2 ^ (d + 3) = 2 ^ ((d + 1) + 3) := by
      rw [show d + 1 + 3 = 1 + (d + 3) by omega]
      simp only [pow_add, pow_one]
    simp only [reduce, strictMoments_eq]
    rw [hbits, show 2 ^ (fuel + 1) = 2 * 2 ^ fuel by rw [pow_succ]; omega,
      combine_lane, hnext]
    rw [← pow_add]
    convert ih (d + 1) using 1 <;> congr 2 <;> omega

theorem moments_filter_range (mask w : ℕ) :
    moments ((List.range w).filter (fun i => mask.testBit i)) = lane mask w 0 := by
  induction w with
  | zero => simp [moments, lane]
  | succ w ih =>
    have hc := congrArg (fun s : Moments => s.1) ih
    have hf := congrArg (fun s : Moments => s.2.1) ih
    have hs := congrArg (fun s : Moments => s.2.2) ih
    simp only [moments, lane, Nat.mul_zero, Nat.zero_add] at hc hf hs
    apply Moments.ext <;>
      simp only [moments, List.range_succ, List.filter_append,
        List.length_append, List.sum_append, List.map_append, lane,
        Nat.mul_zero, Nat.zero_add, Finset.sum_range_succ]
    · rw [hc]
      cases h : mask.testBit w <;> simp [List.filter, h, bitValue]
    · rw [hf]
      cases h : mask.testBit w <;> simp [List.filter, h, bitValue]
    · rw [hs]
      cases h : mask.testBit w <;> simp [List.filter, h, bitValue, pow_two]

theorem enumBits_perm_filter (depth mask : ℕ) :
    (RosserBitSieve.enumBits depth 0 mask).Perm
      ((List.range (2 ^ depth)).filter (fun i => mask.testBit i)) := by
  apply (List.perm_ext_iff_of_nodup (RosserBitSieve.enumBits_nodup _ _ _)
    ((List.nodup_range).filter _)).mpr
  intro x
  simp only [RosserBitSieve.mem_enumBits, Nat.zero_le, Nat.zero_add, Nat.sub_zero,
    true_and, List.mem_filter, List.mem_range]

theorem lane_eq_moments (depth mask : ℕ) :
    lane mask (2 ^ depth) 0 = moments (RosserBitSieve.enumBits depth 0 mask) := by
  rw [moments_perm (enumBits_perm_filter depth mask), moments_filter_range]

/-- All three SWAR moments are exactly the moments of the selected offsets. -/
theorem packedMoments_sound (depth mask : ℕ) (hm : mask < 2 ^ (2 ^ (depth + 3))) :
    packedMoments depth mask =
      moments (RosserBitSieve.enumBits (depth + 3) 1 mask) := by
  have hbits : 2 ^ (depth + 3) = 8 * 2 ^ depth := by
    rw [pow_add]
    norm_num
    omega
  have hdiv : 2 ^ (depth + 3) / 8 = 2 ^ depth := by
    rw [hbits, Nat.mul_div_cancel_left _ (by omega)]
  have hmask : mask < 2 ^ (8 * 2 ^ depth) := by rwa [← hbits]
  simp only [packedMoments, RosserPackedBarrier.forceNat_eq, strictMoments_eq, hdiv]
  rw [bytes_sound mask (2 ^ depth) hmask]
  have hr := reduce_sound depth 0 mask
  simp only [Nat.add_zero, Nat.zero_add] at hr
  norm_num only [Nat.reducePow] at hr
  rw [hr, lane_eq_moments, enumBits_shift (depth + 3) 1 mask, moments_shift]

/-- Padding a mask adds no selected offsets. -/
theorem candidateCount_eq_enumBits_length (depth mask len : ℕ)
    (hm : mask < 2 ^ len) (hlen : len ≤ 2 ^ (depth + 3)) :
    candidateCount mask len = (RosserBitSieve.enumBits (depth + 3) 1 mask).length := by
  rw [enumBits_shift, List.length_map]
  rw [← candidateCount_pad mask len (2 ^ (depth + 3)) hm hlen]
  exact (enumBits_perm_filter (depth + 3) mask).length_eq.symm

theorem packedMoments_eq_fastMoments (depth mask : ℕ)
    (hm : mask < 2 ^ (2 ^ (depth + 3))) :
    packedMoments depth mask = fastMoments depth 1 mask := by
  rw [packedMoments_sound depth mask hm, fastMoments_sound]

#print axioms packedMoments_sound
#print axioms candidateCount_eq_enumBits_length

end RosserPackedMoments
namespace RosserFastCompute
open RosserScan RosserBitMoments
def strictMoments {α : Type} (s : Moments) (f : Moments → α) : α :=
  forceNat s.1 fun c => forceNat s.2.1 fun u => forceNat s.2.2 fun t =>
    f ⟨c, u, t⟩

theorem strictMoments_eq {α : Type} (s : Moments) (f : Moments → α) :
    strictMoments s f = f s := by
  rcases s with ⟨c, u, t⟩
  simp only [strictMoments, RosserPackedBarrier.forceNat_eq]

def depthFor (len : ℕ) : ℕ :=
  if len ≤ 8 then 0 else Nat.log2 ((len - 1) / 8) + 1


end RosserFastCompute

end LeanLab.Ported.Prove2Me.Task666
