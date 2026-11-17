/-
AI wrote the Lean code. Goldbach is open.
Task616, U-1690. Rational step iteration for Buchstab pp. 381 to 385.
The finite arithmetic certificate does not prove either analytic transfer.
-/
import Mathlib

namespace LeanLab.AlmostPrimeSums.Certificate616

/-- The integer scale of the outward rounded rational coefficients. -/
def scale : ℕ := 1000000

/-- Lower coefficients at u = 2 + i / 500 from the two P0072 p. 63 seeds. -/
def initialLower : Array ℕ := (List.range 6501).toArray.map fun i =>
  if i < 4000 then 0 else if i < 6500 then 98 * scale else 2249997 * scale / 10000

/-- Upper seeds on 2 to 14. Entries above 14 are unused sentinels. -/
def initialUpper : Array ℕ := (List.range 6501).toArray.map fun i =>
  if i ≤ 4000 then 1016 * scale / 10 else
    if i ≤ 5000 then 1441328 * scale / 10000 else
      if i ≤ 6000 then 1960022 * scale / 10000 else 1000000 * scale

/-- Prefix sums of upper rectangle masses for 2 times U z times z plus one over z squared.
The left cell endpoint bounds the decreasing kernel. The upper coefficient uses the right endpoint.
Each cell is rounded up to the integer scale. -/
def upperPrefix (hi : Array ℕ) : Array ℕ :=
  ((List.range 6500).map fun i =>
    let k := i + 1000
    (hi[i + 1]! * 2 * (k + 500) + k * k - 1) / (k * k)).scanl (· + ·) 0 |>.toArray

/-- Prefix sums of lower rectangle masses, rounded down.
The coefficient uses the left endpoint and the decreasing kernel uses the right endpoint. -/
def lowerPrefix (lo : Array ℕ) : Array ℕ :=
  ((List.range 6500).map fun i =>
    let k := i + 1001
    lo[i]! * 2 * (k + 500) / (k * k)).scanl (· + ·) 0 |>.toArray

/-- A certificate row contains lower and upper coefficients and their upper and lower mass prefixes. -/
abbrev Row := ℕ × ℕ × ℕ × ℕ
/-- Read a certificate row. All certified indices are in range. -/
def row (t : List Row) (i : ℕ) : Row := t[i]?.getD (0, 0, 0, 0)
/-- Check lower monotonicity, upper monotonicity from three and each rounded cell mass equation. -/
def checkCells : ℕ → List Row → Bool
  | _, [] => true
  | _, [_] => true
  | i, a :: b :: rest =>
    let k := i + 1000
    (a.1 ≤ b.1) && (if i < 500 then true else a.2.1 ≤ b.2.1) &&
    (b.2.2.1 == a.2.2.1 + (b.2.1 * 2 * (k + 500) + k * k - 1) / (k * k)) &&
    (b.2.2.2 == a.2.2.2 + a.1 * 2 * (k + 501) / ((k + 1) * (k + 1))) &&
    checkCells (i + 1) (b :: rest)
/-- Check the initial seeds and zero prefixes at the left endpoint. -/
def checkSeeds : ℕ → List Row → Bool
  | _, [] => true
  | i, a :: rest =>
    (a.1 == (if i < 4000 then 0 else if i < 6500 then 98000000 else 224999700)) &&
    (a.2.1 == (if i ≤ 4000 then 101600000 else if i ≤ 5000 then 144132800 else
      if i ≤ 6000 then 196002200 else 1000000000000)) && checkSeeds (i + 1) rest
/-- Check the two lower anchor updates and the three upper anchor updates row by row.
The second list starts one exponent unit before the first list. Upper subtractions are checked for underflow. -/
def checkUpdates (a6500 a6000 a5500 a5000 a4500 a4000 a3500 : Row) : ℕ → List Row → List Row → List Row → Bool
  | _, [], _, [] => true
  | i, a :: old, start :: starts, b :: fresh =>
    let low15 := a6500.1 - (a6000.2.2.1 - start.2.2.1)
    let low10 := if i ≤ 4000 then
      a4000.1 - (a3500.2.2.1 - start.2.2.1) else 0
    let upper14 := a6000.2.1 - (a5500.2.2.2 - start.2.2.2)
    let upper12 := if i ≤ 5000 then
      a5000.2.1 - (a4500.2.2.2 - start.2.2.2) else a.2.1
    let upper10 := if i ≤ 4000 then
      a4000.2.1 - (a3500.2.2.2 - start.2.2.2) else a.2.1
    (if i ≤ 6000 then a5500.2.2.2 - start.2.2.2 ≤ a6000.2.1 else true) &&
    (if i ≤ 5000 then a4500.2.2.2 - start.2.2.2 ≤ a5000.2.1 else true) &&
    (if i ≤ 4000 then a3500.2.2.2 - start.2.2.2 ≤ a4000.2.1 else true) &&
    (b.1 == max a.1 (max low10 low15)) &&
    (b.2.1 == if i ≤ 6000 then min a.2.1 (min upper10 (min upper12 upper14)) else a.2.1) &&
    checkUpdates a6500 a6000 a5500 a5000 a4500 a4000 a3500 (i + 1) old starts fresh
  | _, _, _, _ => false
/-- Read and cache the seven anchors once before the row check. -/
def checkTransition (old fresh : List Row) (a6500 a6000 a5500 a5000 a4500 a4000 a3500 : Row) : Bool :=
  old.length == 6501 && fresh.length == 6501 &&
  row old 6500 == a6500 &&
  row old 6000 == a6000 &&
  row old 5500 == a5500 &&
  row old 5000 == a5000 &&
  row old 4500 == a4500 &&
  row old 4000 == a4000 &&
  row old 3500 == a3500 &&

  (row fresh 0).2.2.1 == 0 && (row fresh 0).2.2.2 == 0 &&
  checkCells 0 fresh &&
  (old.take 500).map (fun a => (a.1, a.2.1)) ==
    (fresh.take 500).map (fun a => (a.1, a.2.1)) &&
  checkUpdates a6500 a6000 a5500 a5000 a4500 a4000 a3500 500 (old.drop 500) old (fresh.drop 500)
/-- The exact rational target at the integer scale. -/
theorem threshold : (26461200 : ℚ) / scale = 26.4612 := by norm_num [scale]
end LeanLab.AlmostPrimeSums.Certificate616
