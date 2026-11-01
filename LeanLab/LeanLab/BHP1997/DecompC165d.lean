/-
P0069, Section 5, pages 43 to 53. The two short weight constructions
are separate leaves. Their order comes from densities below and above 1.
The exact final statement is CONDITIONAL on both OPEN leaves.
AI wrote the Lean code. CODEX task165. Goldbach is open.
-/
import LeanLab.BHP1997.SieveConditionsC165
import LeanLab.BHP1997.DecompC165a
import LeanLab.BHP1997.Decomp132
import LeanLab.BHP1997.NormalizationC165
import LeanLab.ChenDoubleSieve.I2Range

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- Page 53. Removing a nonnegative part of the negative fourth term
raises the four-term weight and preserves the upper sandwich. -/
theorem upper_four_term_sandwich {ρ g h j k kept : ℝ}
    (hρ : ρ ≤ g - h + j - k) (hkeep : kept ≤ k) :
    ρ ≤ g - h + j - kept := by
  exact hρ.trans (sub_le_sub_left hkeep _)


/-- Page 51. Subtracting two nonnegative discarded sums lowers the prime weight. -/
theorem lower_two_discard_sandwich {ρ d2 d4 : ℝ}
    (h2 : 0 ≤ d2) (h4 : 0 ≤ d4) : ρ - d2 - d4 ≤ ρ := by
  linarith


/-- Page 53. Integer numerators of a uniform rational grid.
The denominator is 400000 and each of the 64 cells has width 879. -/
def upperGridPoint (i : ℕ) : ℕ := 49996 + 879 * i

/-- Page 48, Lemma 33. A sufficient whole-cell test for the R, P1 and P2 regions.
All arguments are integer numerators with denominator 400000.
The margin 49991 is smaller than 400000 times theta2 minus epsilon. -/
def upperGridGood (m M n N : ℕ) : Bool :=
  decide (N ≤ m ∧ M ≤ 200000 ∧ N ≤ 90882 ∧
    ((2 * N ≤ m + 49991 ∧ M ≤ 90882) ∨
     (800000 ≤ 4 * m + 3 * n + 49991 ∧ 4 * M + 3 * N ≤ 849991) ∨
     (800000 ≤ 4 * m + n + 49991 ∧ 4 * M + N ≤ 849991)))

/-- Page 53. Test twelve disjoint nonempty groupings of the three prime factors.
The remaining factor always stays in L. -/
def upperGridCovered (a A b B c C : ℕ) : Bool :=
  upperGridGood a A b B || upperGridGood b B a A ||
  upperGridGood a A c C || upperGridGood c C a A ||
  upperGridGood b B c C || upperGridGood c C b B ||
  upperGridGood (a+b) (A+B) c C || upperGridGood c C (a+b) (A+B) ||
  upperGridGood (a+c) (A+C) b B || upperGridGood b B (a+c) (A+C) ||
  upperGridGood (b+c) (B+C) a A || upperGridGood a A (b+c) (B+C)

/-- Upward integer division for the rational interval certificate. -/
def upperGridCeil (n d : ℕ) : ℕ := (n + d - 1) / d

/-- Page 53. Whole-cell upper weight for the deleted Buchstab integral.
Zero means the cell is outside the ordered support or covered by Lemma 33.
The three quotients majorize 1, 0.567144 and the reciprocal Buchstab argument,
each divided by beta1 times beta2 times beta3 squared. -/
def upperGridWeight (i j k : ℕ) : ℕ :=
  let a := upperGridPoint i
  let b := upperGridPoint j
  let c := upperGridPoint k
  let A := a + 879
  let B := b + 879
  let C := c + 879
  if A < b ∨ B < c ∨ 400000 < a + b + 2*c then 0
  else if upperGridCovered a A b B c C then 0
  else
    let d := a*b*c*c
    let r := 400000 - (A+B+C)
    min (upperGridCeil (400000^4) d)
      (max (upperGridCeil (567144 * 400000^4) (1000000*d))
        (upperGridCeil (C * 400000^4) (r*d)))

/-- Page 53. Explicit rational upper sum for the deleted subset. -/
def upperGridTotal : ℕ :=
  ∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64,
    upperGridWeight i j k

/-- Page 53. Row totals of the integer upper sum, checked independently below. -/
def upperGridRowTotal : ℕ → ℕ
  | 0 => 11191
  | 1 => 19386
  | 2 => 26892
  | 3 => 27122
  | 4 => 35404
  | 5 => 34946
  | 6 => 43751
  | 7 => 42661
  | 8 => 51801
  | 9 => 50135
  | 10 => 59449
  | 11 => 57273
  | 12 => 66658
  | 13 => 64024
  | 14 => 73389
  | 15 => 70350
  | 16 => 79632
  | 17 => 76241
  | 18 => 85378
  | 19 => 81680
  | 20 => 89322
  | 21 => 80769
  | 22 => 81631
  | 23 => 65587
  | 24 => 58917
  | 25 => 39243
  | 26 => 33593
  | 27 => 19586
  | 28 => 14938
  | 29 => 6151
  | 30 => 5505
  | 31 => 4943
  | 32 => 10252
  | 33 => 16690
  | 34 => 22465
  | 35 => 32407
  | 36 => 43893
  | 37 => 56570
  | 38 => 61578
  | 39 => 64094
  | 40 => 61517
  | 41 => 54283
  | 42 => 47468
  | 43 => 41339
  | 44 => 37994
  | 45 => 31102
  | 46 => 100763
  | 47 => 96354
  | 48 => 91443
  | 49 => 87387
  | 50 => 84389
  | 51 => 86212
  | 52 => 93782
  | 53 => 106183
  | 54 => 125806
  | 55 => 150887
  | 56 => 180689
  | 57 => 211246
  | 58 => 241539
  | 59 => 269614
  | 60 => 296350
  | 61 => 320917
  | 62 => 344440
  | 63 => 350027
  | _ => 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Page 53. Full rational grid certificate, checked row by row in the kernel. -/
theorem upper_grid_total : upperGridTotal = 5377228 := by
  have h0 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 0 j k) = 11191 := by decide +kernel
  have h1 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 1 j k) = 19386 := by decide +kernel
  have h2 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 2 j k) = 26892 := by decide +kernel
  have h3 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 3 j k) = 27122 := by decide +kernel
  have h4 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 4 j k) = 35404 := by decide +kernel
  have h5 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 5 j k) = 34946 := by decide +kernel
  have h6 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 6 j k) = 43751 := by decide +kernel
  have h7 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 7 j k) = 42661 := by decide +kernel
  have h8 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 8 j k) = 51801 := by decide +kernel
  have h9 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 9 j k) = 50135 := by decide +kernel
  have h10 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 10 j k) = 59449 := by decide +kernel
  have h11 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 11 j k) = 57273 := by decide +kernel
  have h12 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 12 j k) = 66658 := by decide +kernel
  have h13 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 13 j k) = 64024 := by decide +kernel
  have h14 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 14 j k) = 73389 := by decide +kernel
  have h15 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 15 j k) = 70350 := by decide +kernel
  have h16 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 16 j k) = 79632 := by decide +kernel
  have h17 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 17 j k) = 76241 := by decide +kernel
  have h18 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 18 j k) = 85378 := by decide +kernel
  have h19 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 19 j k) = 81680 := by decide +kernel
  have h20 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 20 j k) = 89322 := by decide +kernel
  have h21 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 21 j k) = 80769 := by decide +kernel
  have h22 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 22 j k) = 81631 := by decide +kernel
  have h23 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 23 j k) = 65587 := by decide +kernel
  have h24 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 24 j k) = 58917 := by decide +kernel
  have h25 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 25 j k) = 39243 := by decide +kernel
  have h26 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 26 j k) = 33593 := by decide +kernel
  have h27 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 27 j k) = 19586 := by decide +kernel
  have h28 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 28 j k) = 14938 := by decide +kernel
  have h29 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 29 j k) = 6151 := by decide +kernel
  have h30 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 30 j k) = 5505 := by decide +kernel
  have h31 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 31 j k) = 4943 := by decide +kernel
  have h32 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 32 j k) = 10252 := by decide +kernel
  have h33 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 33 j k) = 16690 := by decide +kernel
  have h34 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 34 j k) = 22465 := by decide +kernel
  have h35 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 35 j k) = 32407 := by decide +kernel
  have h36 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 36 j k) = 43893 := by decide +kernel
  have h37 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 37 j k) = 56570 := by decide +kernel
  have h38 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 38 j k) = 61578 := by decide +kernel
  have h39 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 39 j k) = 64094 := by decide +kernel
  have h40 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 40 j k) = 61517 := by decide +kernel
  have h41 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 41 j k) = 54283 := by decide +kernel
  have h42 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 42 j k) = 47468 := by decide +kernel
  have h43 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 43 j k) = 41339 := by decide +kernel
  have h44 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 44 j k) = 37994 := by decide +kernel
  have h45 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 45 j k) = 31102 := by decide +kernel
  have h46 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 46 j k) = 100763 := by decide +kernel
  have h47 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 47 j k) = 96354 := by decide +kernel
  have h48 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 48 j k) = 91443 := by decide +kernel
  have h49 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 49 j k) = 87387 := by decide +kernel
  have h50 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 50 j k) = 84389 := by decide +kernel
  have h51 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 51 j k) = 86212 := by decide +kernel
  have h52 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 52 j k) = 93782 := by decide +kernel
  have h53 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 53 j k) = 106183 := by decide +kernel
  have h54 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 54 j k) = 125806 := by decide +kernel
  have h55 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 55 j k) = 150887 := by decide +kernel
  have h56 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 56 j k) = 180689 := by decide +kernel
  have h57 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 57 j k) = 211246 := by decide +kernel
  have h58 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 58 j k) = 241539 := by decide +kernel
  have h59 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 59 j k) = 269614 := by decide +kernel
  have h60 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 60 j k) = 296350 := by decide +kernel
  have h61 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 61 j k) = 320917 := by decide +kernel
  have h62 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 62 j k) = 344440 := by decide +kernel
  have h63 : (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight 63 j k) = 350027 := by decide +kernel
  have hrows : ∀ i ∈ Finset.range 64,
      (∑ j ∈ Finset.range 64, ∑ k ∈ Finset.range 64, upperGridWeight i j k) = upperGridRowTotal i := by
    intro i hi
    have hi' : i < 64 := Finset.mem_range.mp hi
    interval_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9
    · exact h10
    · exact h11
    · exact h12
    · exact h13
    · exact h14
    · exact h15
    · exact h16
    · exact h17
    · exact h18
    · exact h19
    · exact h20
    · exact h21
    · exact h22
    · exact h23
    · exact h24
    · exact h25
    · exact h26
    · exact h27
    · exact h28
    · exact h29
    · exact h30
    · exact h31
    · exact h32
    · exact h33
    · exact h34
    · exact h35
    · exact h36
    · exact h37
    · exact h38
    · exact h39
    · exact h40
    · exact h41
    · exact h42
    · exact h43
    · exact h44
    · exact h45
    · exact h46
    · exact h47
    · exact h48
    · exact h49
    · exact h50
    · exact h51
    · exact h52
    · exact h53
    · exact h54
    · exact h55
    · exact h56
    · exact h57
    · exact h58
    · exact h59
    · exact h60
    · exact h61
    · exact h62
    · exact h63
  calc
    upperGridTotal = ∑ i ∈ Finset.range 64, upperGridRowTotal i :=
      Finset.sum_congr rfl hrows
    _ = 5377228 := by decide +kernel

/-- Pages 47 and 53. The small epsilon interval fits inside the rational grid.
The reciprocal c4 lies above 2 and the c2 endpoint used by the grid is safe. -/
theorem upper_grid_parameters {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 10^8) :
    (49996 : ℝ) / 400000 < (1 + 7 * (2 * (1 / 16 - 1 / 10^5))) / 15 - ε ∧
    (1 / 4 + (2 * (1 / 16 - 1 / 10^5)) / 8 - ε : ℝ) < 106252 / 400000 ∧
    (90882 : ℝ) / 400000 ≤ (36 * (2 * (1 / 16 - 1 / 10^5)) - 2) / 11 - ε ∧
    (49991 : ℝ) / 400000 ≤ 2 * (1 / 16 - 1 / 10^5) - ε ∧
    (26562249 : ℝ) / 10^8 ≤ 1 / 4 + (2 * (1 / 16 - 1 / 10^5)) / 8 - ε ∧
    (1 / 4 + (2 * (1 / 16 - 1 / 10^5)) / 8 - ε : ℝ) ≤ 1 / 2 := by
  norm_num at *
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith


/-- Page 53. The certified grid allowance plus the global Buchstab base
bound leaves a strict margin below 2.2. This statement is rational arithmetic. -/
theorem upper_grid_budget :
    (567144 / 1000000 : ℝ) / (26562249 / 10^8) +
      5377228 * (879 / 400000 : ℝ)^3 < 2.2 := by
  norm_num


/-- Page 53. The base term is uniformly bounded at every epsilon in the grid range.
CONDITIONAL on the defining Buchstab equations, with no existence assertion. -/
theorem upper_base_enclosure {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 10^8) :
    let c4 : ℝ := 1 / 4 + (2 * (1 / 16 - 1 / 10^5)) / 8 - ε
    ω (1 / c4) / c4 ≤ (567144 / 1000000 : ℝ) / (26562249 / 10^8) := by
  intro c4
  have hp := upper_grid_parameters hε hε'
  have hc : (26562249 : ℝ) / 10^8 ≤ c4 := hp.2.2.2.2.1
  have hc0 : 0 < c4 := by linarith
  have hc2 : c4 ≤ 1 / 2 := hp.2.2.2.2.2
  have hu : 2 ≤ 1 / c4 := (le_div_iff₀ hc0).2 (by linarith)
  have hbound := LeanLab.ChenDoubleSieve.Wu04Buchstab.buchstab_le_567144 hω hu
  exact (div_le_div_of_nonneg_right hbound hc0.le).trans
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc)

/-- Page 53. Integrating a panelwise constant upper bound over a finite partition.
This is the elementary Riemann sum comparison used by the certificate. -/
theorem integral_le_panel_sum (p : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ) (w : ℕ → ℝ)
    (hp : ∀ i < n, p i ≤ p (i+1))
    (hi : ∀ i < n, IntervalIntegrable f MeasureTheory.volume (p i) (p (i+1)))
    (hb : ∀ i < n, ∀ x ∈ Set.Icc (p i) (p (i+1)), f x ≤ w i) :
    (∫ x in p 0..p n, f x) ≤ ∑ i ∈ Finset.range n, (p (i+1)-p i) * w i := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hi]
  apply Finset.sum_le_sum
  intro i hi'
  have hin : i < n := Finset.mem_range.mp hi'
  calc
    (∫ x in p i..p (i+1), f x) ≤ ∫ x in p i..p (i+1), w i :=
      intervalIntegral.integral_mono_on (hp i hin) (hi i hin)
        intervalIntegrable_const (hb i hin)
    _ = (p (i+1)-p i) * w i := by simp [mul_comm]


/-- Page 53. Real endpoints of the certified rational grid. -/
noncomputable def upperGridReal (i : ℕ) : ℝ := (upperGridPoint i : ℝ) / 400000

/-- Page 53. Every grid cell has the same positive rational width. -/
theorem upper_grid_step (i : ℕ) :
    upperGridReal (i+1) - upperGridReal i = (879 : ℝ) / 400000 := by
  simp [upperGridReal, upperGridPoint, Nat.cast_add, Nat.cast_mul]
  ring


/-- Page 53. The Riemann sum bounds any integrable function with the certified cell bounds.
The integrability hypotheses concern actual panels, so the statement makes no existence claim.
All three integrations range over the rational grid box. -/
theorem upper_integral_of_cells (f : ℝ → ℝ → ℝ → ℝ)
    (h1 : ∀ i < 64, IntervalIntegrable
      (fun a => ∫ b in upperGridReal 0..upperGridReal 64,
        ∫ c in upperGridReal 0..upperGridReal 64, f a b c)
      MeasureTheory.volume (upperGridReal i) (upperGridReal (i+1)))
    (h2 : ∀ a ∈ Set.Icc (upperGridReal 0) (upperGridReal 64), ∀ j < 64,
      IntervalIntegrable (fun b => ∫ c in upperGridReal 0..upperGridReal 64, f a b c)
        MeasureTheory.volume (upperGridReal j) (upperGridReal (j+1)))
    (h3 : ∀ a ∈ Set.Icc (upperGridReal 0) (upperGridReal 64),
      ∀ b ∈ Set.Icc (upperGridReal 0) (upperGridReal 64), ∀ k < 64,
      IntervalIntegrable (fun c => f a b c)
        MeasureTheory.volume (upperGridReal k) (upperGridReal (k+1)))
    (hb : ∀ i < 64, ∀ j < 64, ∀ k < 64,
      ∀ a ∈ Set.Icc (upperGridReal i) (upperGridReal (i+1)),
      ∀ b ∈ Set.Icc (upperGridReal j) (upperGridReal (j+1)),
      ∀ c ∈ Set.Icc (upperGridReal k) (upperGridReal (k+1)),
      f a b c ≤ (upperGridWeight i j k : ℝ)) :
    (∫ a in upperGridReal 0..upperGridReal 64,
      ∫ b in upperGridReal 0..upperGridReal 64,
        ∫ c in upperGridReal 0..upperGridReal 64, f a b c) ≤
      5377228 * (879 / 400000 : ℝ)^3 := by
  let s : ℝ := 879 / 400000
  have hs : 0 ≤ s := by norm_num [s]
  have hm (i : ℕ) : upperGridReal i ≤ upperGridReal (i+1) := by
    have := upper_grid_step i
    linarith
  have hbox {i : ℕ} (hi : i < 64) {a : ℝ}
      (ha : a ∈ Set.Icc (upperGridReal i) (upperGridReal (i+1))) :
      a ∈ Set.Icc (upperGridReal 0) (upperGridReal 64) := by
    norm_num [upperGridReal, upperGridPoint, Nat.cast_add, Nat.cast_mul] at ha ⊢
    have hiR : (i : ℝ) ≤ 63 := by exact_mod_cast (by omega : i ≤ 63)
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    constructor <;> linarith [ha.1, ha.2]
  have inner (i j : ℕ) (hi : i < 64) (hj : j < 64)
      (a b : ℝ) (ha : a ∈ Set.Icc (upperGridReal i) (upperGridReal (i+1)))
      (hb' : b ∈ Set.Icc (upperGridReal j) (upperGridReal (j+1))) :
      (∫ c in upperGridReal 0..upperGridReal 64, f a b c) ≤
        ∑ k ∈ Finset.range 64, s * (upperGridWeight i j k : ℝ) := by
    have hi3 := integral_le_panel_sum upperGridReal 64 (f a b)
      (fun k => (upperGridWeight i j k : ℝ)) (fun k _ => hm k)
      (h3 a (hbox hi ha) b (hbox hj hb'))
      (fun k hk c hc => hb i hi j hj k hk a ha b hb' c hc)
    simpa only [upper_grid_step] using hi3
  have middle (i : ℕ) (hi : i < 64) (a : ℝ)
      (ha : a ∈ Set.Icc (upperGridReal i) (upperGridReal (i+1))) :
      (∫ b in upperGridReal 0..upperGridReal 64,
        ∫ c in upperGridReal 0..upperGridReal 64, f a b c) ≤
        ∑ j ∈ Finset.range 64, s * (∑ k ∈ Finset.range 64,
          s * (upperGridWeight i j k : ℝ)) := by
    have hi2 := integral_le_panel_sum upperGridReal 64
      (fun b => ∫ c in upperGridReal 0..upperGridReal 64, f a b c)
      (fun j => ∑ k ∈ Finset.range 64, s * (upperGridWeight i j k : ℝ))
      (fun j _ => hm j) (h2 a (hbox hi ha))
      (fun j hj b hb' => inner i j hi hj a b ha hb')
    simpa only [upper_grid_step] using hi2
  have hi1 := integral_le_panel_sum upperGridReal 64
    (fun a => ∫ b in upperGridReal 0..upperGridReal 64,
      ∫ c in upperGridReal 0..upperGridReal 64, f a b c)
    (fun i => ∑ j ∈ Finset.range 64, s * (∑ k ∈ Finset.range 64,
      s * (upperGridWeight i j k : ℝ))) (fun i _ => hm i) h1 middle
  simp only [upper_grid_step] at hi1
  have he : (∑ i ∈ Finset.range 64, s * (∑ j ∈ Finset.range 64,
      s * (∑ k ∈ Finset.range 64, s * (upperGridWeight i j k : ℝ)))) =
      (upperGridTotal : ℝ) * s^3 := by
    simp only [← Finset.mul_sum]
    simp only [upperGridTotal, Nat.cast_sum]
    ring
  rw [he, upper_grid_total] at hi1
  exact hi1

/-- Page 53. The integer ceilings in the rational certificate are upward bounds. -/
theorem upper_grid_ceil_bound {n d : ℕ} (hd : 0 < d) :
    (n : ℝ) / (d : ℝ) ≤ (upperGridCeil n d : ℝ) := by
  apply (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).2
  have hn : n ≤ d * upperGridCeil n d := by
    exact (ceilDiv_le_iff_le_mul hd).1 le_rfl
  exact_mod_cast (by simpa [Nat.mul_comm] using hn : n ≤ upperGridCeil n d * d)


/-- Pages 51 and 53. On a rational cell the Buchstab integrand is bounded by
three elementary interval envelopes. The value below one is zero by convention.
CONDITIONAL on the defining Buchstab equations and the zero extension. -/
theorem buchstab_cell_envelope {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {a A b B c C x y z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : 0 < 1-A-B-C)
    (hx : x ∈ Set.Icc a A) (hy : y ∈ Set.Icc b B) (hz' : z ∈ Set.Icc c C) :
    ω ((1-x-y-z)/z) / (x*y*z^2) ≤
      min (1/(a*b*c^2))
        (max ((567144/1000000 : ℝ)/(a*b*c^2))
          ((C/(1-A-B-C))/(a*b*c^2))) := by
  let u := (1-x-y-z)/z
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have hy0 : 0 < y := lt_of_lt_of_le hb hy.1
  have hz0 : 0 < z := lt_of_lt_of_le hc hz'.1
  have hC0 : 0 < C := lt_of_lt_of_le hz0 hz'.2
  have hd : 0 < a*b*c^2 := by positivity
  have hd' : 0 < x*y*z^2 := by positivity
  have hdd : a*b*c^2 ≤ x*y*z^2 := by gcongr <;> linarith [hx.1, hy.1, hz'.1]
  have h1 : ω u ≤ 1 :=
    LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz u
  have hbase : ω u / (x*y*z^2) ≤ 1/(a*b*c^2) :=
    (div_le_div_of_nonneg_right h1 hd'.le).trans
      (div_le_div_of_nonneg_left zero_le_one hd hdd)
  refine le_min hbase ?_
  by_cases hu : 2 ≤ u
  · have hC := LeanLab.ChenDoubleSieve.Wu04Buchstab.buchstab_le_567144 hω hu
    apply le_trans _ (le_max_left _ _)
    exact (div_le_div_of_nonneg_right hC hd'.le).trans
      (div_le_div_of_nonneg_left (by norm_num) hd hdd)
  · by_cases hu1 : u < 1
    · have hw : ω u = 0 := hz u hu1
      rw [hw, zero_div]
      exact le_trans (by positivity) (le_max_left _ _)
    · have huu : 1 ≤ u := le_of_not_gt hu1
      have hw : ω u = 1/u := hω.2.1 u huu (le_of_not_ge hu)
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one huu
      have huLow : (1-A-B-C)/C ≤ u := by
        dsimp [u]
        apply (div_le_div_of_nonneg_left hr.le hz0 hz'.2).trans
        apply div_le_div_of_nonneg_right _ hz0.le
        linarith [hx.2, hy.2, hz'.2]
      have hrec : 1/u ≤ C/(1-A-B-C) := by
        have hh := one_div_le_one_div_of_le (div_pos hr hC0) huLow
        simpa only [one_div_div] using hh
      apply le_trans _ (le_max_right _ _)
      exact (div_le_div_of_nonneg_right (hw.le.trans hrec) hd'.le).trans
        (div_le_div_of_nonneg_left (by positivity) hd hdd)

/-- Page 48, Lemma 33. The R, P1 and P2 alternatives for an ordered pair.
The R boundary at n equal to c1 is also covered by case 5.13 for small epsilon.
This paper Prop requires Claude review before merge. -/
def upperPairRegion (ε m n : ℝ) : Prop :=
  n ≤ m ∧ m ≤ 1/2 ∧ (1+7*(2*(1/16-1/10^5)))/15-ε ≤ n ∧
    n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε ∧
    ((2*n-(2*(1/16-1/10^5))+ε ≤ m ∧
        m ≤ (36*(2*(1/16-1/10^5))-2)/11-ε) ∨
      |4*m+3*n-2| ≤ 2*(1/16-1/10^5)-ε ∨
      |4*m+n-2| ≤ 2*(1/16-1/10^5)-ε)

/-- Page 53. Twelve legal prime groupings for Lemma 33, leaving the residual factor in L.
This paper Prop requires Claude review before merge. -/
def upperPrimeCovered (ε a b c : ℝ) : Prop :=
  upperPairRegion ε a b ∨ upperPairRegion ε b a ∨
  upperPairRegion ε a c ∨ upperPairRegion ε c a ∨
  upperPairRegion ε b c ∨ upperPairRegion ε c b ∨
  upperPairRegion ε (a+b) c ∨ upperPairRegion ε c (a+b) ∨
  upperPairRegion ε (a+c) b ∨ upperPairRegion ε b (a+c) ∨
  upperPairRegion ε (b+c) a ∨ upperPairRegion ε a (b+c)

/-- Page 53. A conservative deleted integrand. It retains every point not covered
by the twelve prime groupings, even if a further legal grouping exists.
The explicit zero below one is the usual Buchstab extension convention. -/
noncomputable def upperDeletedIntegrand (ω : ℝ → ℝ) (ε a b c : ℝ) : ℝ :=
  if (1+7*(2*(1/16-1/10^5)))/15-ε ≤ c ∧ c ≤ b ∧ b ≤ a ∧
      a ≤ 1/4+(2*(1/16-1/10^5))/8-ε ∧ ¬upperPrimeCovered ε a b c then
    if (1-a-b-c)/c < 1 then 0 else ω ((1-a-b-c)/c)/(a*b*c^2)
  else 0

/-- Page 48. A true integer whole-cell test implies the actual Lemma 33 region.
The lower c1 condition is supplied by the ordered prime support. -/
theorem upper_grid_good_sound {ε m M n N x y : ℝ}
    {im iM inn iN : ℕ}
    (hm : m = (im : ℝ)/400000) (hM : M = (iM : ℝ)/400000)
    (hn : n = (inn : ℝ)/400000) (hN : N = (iN : ℝ)/400000)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8)
    (hx : x ∈ Set.Icc m M) (hy : y ∈ Set.Icc n N)
    (hc1 : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ y)
    (ht : upperGridGood im iM inn iN = true) : upperPairRegion ε x y := by
  simp only [upperGridGood, decide_eq_true_eq] at ht
  obtain ⟨hNM, hM2, hNc2, cases⟩ := ht
  have hrNM : (iN : ℝ) ≤ im := by exact_mod_cast hNM
  have hrM2 : (iM : ℝ) ≤ 200000 := by exact_mod_cast hM2
  have hrNc2 : (iN : ℝ) ≤ 90882 := by exact_mod_cast hNc2
  have hp := upper_grid_parameters hε hε'
  have hmargin := hp.2.2.2.1
  have hc2 := hp.2.2.1
  refine ⟨?_, ?_, hc1, ?_, ?_⟩
  · rw [hm] at hx
    rw [hN] at hy
    linarith [hx.1, hy.2]
  · rw [hM] at hx
    linarith [hx.2]
  · rw [hN] at hy
    linarith [hy.2]
  rcases cases with hR | hP1 | hP2
  · have hR1 : 2*(iN : ℝ) ≤ im+49991 := by exact_mod_cast hR.1
    have hR2 : (iM : ℝ) ≤ 90882 := by exact_mod_cast hR.2
    left
    rw [hm, hM] at hx
    rw [hn, hN] at hy
    constructor <;> linarith [hx.1, hx.2, hy.2]
  · have hPlo : (800000 : ℝ) ≤ 4*im+3*inn+49991 := by exact_mod_cast hP1.1
    have hPhi : 4*(iM : ℝ)+3*iN ≤ 849991 := by exact_mod_cast hP1.2
    right; left
    rw [abs_le]
    rw [hm, hM] at hx
    rw [hn, hN] at hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  · have hPlo : (800000 : ℝ) ≤ 4*im+inn+49991 := by exact_mod_cast hP2.1
    have hPhi : 4*(iM : ℝ)+iN ≤ 849991 := by exact_mod_cast hP2.2
    right; right
    rw [abs_le]
    rw [hm, hM] at hx
    rw [hn, hN] at hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]


/-- Page 53. Every Boolean grouping certificate is a legal real prime grouping. -/
theorem upper_grid_covered_sound {ε a b c : ℝ} {ia iA ib iB ic iC : ℕ}
    (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8)
    (ha : a ∈ Set.Icc ((ia : ℝ)/400000) ((iA : ℝ)/400000))
    (hb : b ∈ Set.Icc ((ib : ℝ)/400000) ((iB : ℝ)/400000))
    (hc : c ∈ Set.Icc ((ic : ℝ)/400000) ((iC : ℝ)/400000))
    (hca : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ a)
    (hcb : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ b)
    (hcc : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ c)
    (ht : upperGridCovered ia iA ib iB ic iC = true) :
    upperPrimeCovered ε a b c := by
  have hsum {a b : ℝ} {ia iA ib iB : ℕ}
      (ha : a ∈ Set.Icc ((ia : ℝ)/400000) ((iA : ℝ)/400000))
      (hb : b ∈ Set.Icc ((ib : ℝ)/400000) ((iB : ℝ)/400000)) :
      a+b ∈ Set.Icc (((ia+ib : ℕ) : ℝ)/400000) (((iA+iB : ℕ) : ℝ)/400000) := by
    push_cast
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hcpos : (0 : ℝ) ≤ (1+7*(2*(1/16-1/10^5)))/15-ε := by
    norm_num at hε' ⊢
    linarith
  have hcAB : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ a+b := by linarith
  have hcAC : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ a+c := by linarith
  have hcBC : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ b+c := by linarith
  have pair {im iM inn iN : ℕ} {x y : ℝ}
      (hx : x ∈ Set.Icc ((im : ℝ)/400000) ((iM : ℝ)/400000))
      (hy : y ∈ Set.Icc ((inn : ℝ)/400000) ((iN : ℝ)/400000))
      (hcy : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ y)
      (ht : upperGridGood im iM inn iN = true) : upperPairRegion ε x y :=
    upper_grid_good_sound rfl rfl rfl rfl hε hε' hx hy hcy ht
  have hAB := pair ha hb hcb
  have hBA := pair hb ha hca
  have hAC := pair ha hc hcc
  have hCA := pair hc ha hca
  have hBC := pair hb hc hcc
  have hCB := pair hc hb hcb
  have hABC := pair (hsum ha hb) hc hcc
  have hCAB := pair hc (hsum ha hb) hcAB
  have hACB := pair (hsum ha hc) hb hcb
  have hBAC := pair hb (hsum ha hc) hcAC
  have hBCA := pair (hsum hb hc) ha hca
  have hABC' := pair ha (hsum hb hc) hcBC
  simp only [upperGridCovered, Bool.or_eq_true, or_assoc] at ht
  unfold upperPrimeCovered
  rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
  · exact Or.inl (hAB ht)
  · exact Or.inr (Or.inl (hBA ht))
  · exact Or.inr (Or.inr (Or.inl (hAC ht)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hCA ht))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hBC ht)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hCB ht))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hABC ht)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hCAB ht))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hACB ht)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hBAC ht))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hBCA ht)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hABC' ht)))))))))))


set_option maxRecDepth 100000 in
/-- Page 53. Each unevaluated cell envelope lies below the integer weight.
This is an interval bound with rational endpoints, not a floating point estimate. -/
theorem upper_grid_raw_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {i j k : ℕ} (hi : i < 64) (hj : j < 64) (hk : k < 64)
    {x y z : ℝ}
    (hx : x ∈ Set.Icc (upperGridReal i) (upperGridReal (i+1)))
    (hy : y ∈ Set.Icc (upperGridReal j) (upperGridReal (j+1)))
    (hz' : z ∈ Set.Icc (upperGridReal k) (upperGridReal (k+1))) :
    let a := upperGridPoint i
    let b := upperGridPoint j
    let c := upperGridPoint k
    let C := c+879
    let d := a*b*c*c
    let r := 400000-((a+879)+(b+879)+C)
    ω ((1-x-y-z)/z)/(x*y*z^2) ≤
      (min (upperGridCeil (400000^4) d)
        (max (upperGridCeil (567144*400000^4) (1000000*d))
          (upperGridCeil (C*400000^4) (r*d))) : ℕ) := by
  intro a b c C d r
  have ha : 0 < a := by dsimp [a, upperGridPoint]; omega
  have hb : 0 < b := by dsimp [b, upperGridPoint]; omega
  have hc : 0 < c := by dsimp [c, upperGridPoint]; omega
  have hd : 0 < d := by dsimp [d]; positivity
  have hsum : (a+879)+(b+879)+C ≤ 400000 := by
    dsimp [a, b, c, C, upperGridPoint]
    omega
  have hr : 0 < r := by
    dsimp [r, a, b, c, C, upperGridPoint]
    omega
  have hrCast : (r : ℝ) = 400000-((a+879 : ℕ):ℝ)-((b+879 : ℕ):ℝ)-(C : ℝ) := by
    dsimp [r]
    rw [Nat.cast_sub hsum]
    push_cast
    ring
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he (i : ℕ) : upperGridPoint (i+1) = upperGridPoint i+879 := by
    unfold upperGridPoint
    omega
  have hx' : x ∈ Set.Icc ((a:ℝ)/400000) (((a+879:ℕ):ℝ)/400000) := by
    simpa only [upperGridReal, he] using hx
  have hy' : y ∈ Set.Icc ((b:ℝ)/400000) (((b+879:ℕ):ℝ)/400000) := by
    simpa only [upperGridReal, he] using hy
  have hz'' : z ∈ Set.Icc ((c:ℝ)/400000) ((C:ℝ)/400000) := by
    simpa only [upperGridReal, he] using hz'
  have hrest : 0 < 1-(((a+879:ℕ):ℝ)/400000)-(((b+879:ℕ):ℝ)/400000)-(C:ℝ)/400000 := by
    linarith [hrCast]
  have hh := buchstab_cell_envelope hω hz (by positivity : 0 < (a:ℝ)/400000)
    (by positivity : 0 < (b:ℝ)/400000) (by positivity : 0 < (c:ℝ)/400000)
    hrest hx' hy' hz''
  have hdEq : (d:ℝ) = (a:ℝ)*b*c*c := by dsimp [d]; push_cast; ring
  have hone : 1/((a:ℝ)/400000*((b:ℝ)/400000)*((c:ℝ)/400000)^2) =
      (400000:ℝ)^4/d := by rw [hdEq]; field_simp <;> ring
  have hconst : (567144/1000000:ℝ)/((a:ℝ)/400000*((b:ℝ)/400000)*((c:ℝ)/400000)^2) =
      (567144:ℝ)*400000^4/(1000000*d) := by rw [hdEq]; field_simp <;> ring
  have hrec : (((C:ℝ)/400000)/
      (1-(((a+879:ℕ):ℝ)/400000)-(((b+879:ℕ):ℝ)/400000)-(C:ℝ)/400000))/
      ((a:ℝ)/400000*((b:ℝ)/400000)*((c:ℝ)/400000)^2) =
      (C:ℝ)*400000^4/(r*d) := by
    have hden : 1-(((a+879:ℕ):ℝ)/400000)-(((b+879:ℕ):ℝ)/400000)-(C:ℝ)/400000 =
        (r:ℝ)/400000 := by linarith [hrCast]
    rw [hden, hdEq]
    field_simp <;> ring
  rw [hone, hconst, hrec] at hh
  apply hh.trans
  push_cast
  apply min_le_min
  · convert upper_grid_ceil_bound hd using 1 <;> norm_num
  · apply max_le_max
    · convert upper_grid_ceil_bound (Nat.mul_pos (by norm_num : 0 < 1000000) hd) using 1 <;> push_cast <;> norm_num
    · convert upper_grid_ceil_bound (Nat.mul_pos hr hd) using 1 <;> push_cast <;> norm_num

set_option maxRecDepth 100000 in
/-- Page 53. Every value of the conservative deleted integrand is bounded by
its rational grid weight. The proof checks support, whole-cell grouping and
Buchstab envelopes separately. -/
theorem upper_deleted_cell_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8)
    {i j k : ℕ} (hi : i < 64) (hj : j < 64) (hk : k < 64)
    {a b c : ℝ}
    (ha : a ∈ Set.Icc (upperGridReal i) (upperGridReal (i+1)))
    (hb : b ∈ Set.Icc (upperGridReal j) (upperGridReal (j+1)))
    (hc : c ∈ Set.Icc (upperGridReal k) (upperGridReal (k+1))) :
    upperDeletedIntegrand ω ε a b c ≤ (upperGridWeight i j k : ℝ) := by
  unfold upperDeletedIntegrand
  split_ifs with hdom hu
  · exact Nat.cast_nonneg _
  · obtain ⟨hcc, hcb, hba, hac4, hnot⟩ := hdom
    have he (i : ℕ) : upperGridPoint (i+1) = upperGridPoint i+879 := by
      unfold upperGridPoint
      omega
    have ha' : a ∈ Set.Icc ((upperGridPoint i : ℝ)/400000)
        (((upperGridPoint i+879 : ℕ):ℝ)/400000) := by
      simpa only [upperGridReal, he] using ha
    have hb' : b ∈ Set.Icc ((upperGridPoint j : ℝ)/400000)
        (((upperGridPoint j+879 : ℕ):ℝ)/400000) := by
      simpa only [upperGridReal, he] using hb
    have hc' : c ∈ Set.Icc ((upperGridPoint k : ℝ)/400000)
        (((upperGridPoint k+879 : ℕ):ℝ)/400000) := by
      simpa only [upperGridReal, he] using hc
    have hca : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ a := le_trans hcc (le_trans hcb hba)
    have hcb' : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ b := le_trans hcc hcb
    have hcover : upperGridCovered (upperGridPoint i) (upperGridPoint i+879)
        (upperGridPoint j) (upperGridPoint j+879)
        (upperGridPoint k) (upperGridPoint k+879) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hnot (upper_grid_covered_sound hε hε' ha' hb' hc' hca hcb' hcc ht)
    have hc0 : 0 < c := by
      have hpoint : (0 : ℝ) < upperGridPoint k := by
        dsimp [upperGridPoint]
        positivity
      linarith [hc'.1]
    have hsupport : a+b+2*c ≤ 1 := by
      have hu1 := (le_div_iff₀ hc0).1 (le_of_not_gt hu)
      linarith
    have hout : ¬(upperGridPoint i+879 < upperGridPoint j ∨
        upperGridPoint j+879 < upperGridPoint k ∨
        400000 < upperGridPoint i+upperGridPoint j+2*upperGridPoint k) := by
      intro ht
      rcases ht with hab | hbc | hsum
      · have hR : ((upperGridPoint i+879 : ℕ):ℝ) < upperGridPoint j := by exact_mod_cast hab
        linarith [ha'.2, hb'.1]
      · have hR : ((upperGridPoint j+879 : ℕ):ℝ) < upperGridPoint k := by exact_mod_cast hbc
        linarith [hb'.2, hc'.1]
      · have hR : (400000:ℝ) < upperGridPoint i+upperGridPoint j+2*upperGridPoint k := by exact_mod_cast hsum
        linarith [ha'.1, hb'.1, hc'.1]
    simpa only [upperGridWeight, if_neg hout, hcover, Bool.false_eq_true,
      ↓reduceIte] using upper_grid_raw_bound hω hz hi hj hk ha hb hc
  · exact Nat.cast_nonneg _

/-- Page 53. A nonnegative panel upper sum also bounds the totalized Bochner integral.
If the function is integrable, use the genuine panel integrals. Otherwise its
interval integral is zero. This theorem does not assert integrability. -/
theorem integral_le_nonnegative_panel_sum (p : ℕ → ℝ) (n : ℕ)
    (f : ℝ → ℝ) (w : ℕ → ℝ) (hp : Monotone p)
    (hw : ∀ i < n, 0 ≤ w i)
    (hb : ∀ i < n, ∀ x ∈ Set.Icc (p i) (p (i+1)), f x ≤ w i) :
    (∫ x in p 0..p n, f x) ≤ ∑ i ∈ Finset.range n, (p (i+1)-p i)*w i := by
  by_cases hint : IntervalIntegrable f MeasureTheory.volume (p 0) (p n)
  · apply integral_le_panel_sum p n f w (fun i _ => hp (by omega))
    · intro i hi
      apply hint.mono_set
      rw [Set.uIcc_of_le (hp (by omega : i ≤ i+1)),
        Set.uIcc_of_le (hp (Nat.zero_le n))]
      exact Set.Icc_subset_Icc (hp (Nat.zero_le i)) (hp (by omega))
    · exact hb
  · rw [intervalIntegral.integral_undef hint]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (sub_nonneg.mpr (hp (by omega))) (hw i (Finset.mem_range.mp hi))


/-- Page 53. The certified grid bounds the totalized threefold Bochner integral
without regularity premises. This proves an upper bound, not integrability. -/
theorem upper_integral_of_cells_total (f : ℝ → ℝ → ℝ → ℝ)
    (hb : ∀ i < 64, ∀ j < 64, ∀ k < 64,
      ∀ a ∈ Set.Icc (upperGridReal i) (upperGridReal (i+1)),
      ∀ b ∈ Set.Icc (upperGridReal j) (upperGridReal (j+1)),
      ∀ c ∈ Set.Icc (upperGridReal k) (upperGridReal (k+1)),
      f a b c ≤ (upperGridWeight i j k : ℝ)) :
    (∫ a in upperGridReal 0..upperGridReal 64,
      ∫ b in upperGridReal 0..upperGridReal 64,
        ∫ c in upperGridReal 0..upperGridReal 64, f a b c) ≤
      5377228 * (879 / 400000 : ℝ)^3 := by
  let s : ℝ := 879 / 400000
  have hs : 0 ≤ s := by norm_num [s]
  have hp : Monotone upperGridReal := by
    intro i j hij
    norm_num [upperGridReal, upperGridPoint, Nat.cast_add, Nat.cast_mul]
    have hR : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have inner (i j : ℕ) (hi : i < 64) (hj : j < 64)
      (a b : ℝ) (ha : a ∈ Set.Icc (upperGridReal i) (upperGridReal (i+1)))
      (hb' : b ∈ Set.Icc (upperGridReal j) (upperGridReal (j+1))) :
      (∫ c in upperGridReal 0..upperGridReal 64, f a b c) ≤
        ∑ k ∈ Finset.range 64, s * (upperGridWeight i j k : ℝ) := by
    have h := integral_le_nonnegative_panel_sum upperGridReal 64 (f a b)
      (fun k => (upperGridWeight i j k : ℝ)) hp (by intros; positivity)
      (fun k hk c hc => hb i hi j hj k hk a ha b hb' c hc)
    simpa only [upper_grid_step] using h
  have middle (i : ℕ) (hi : i < 64) (a : ℝ)
      (ha : a ∈ Set.Icc (upperGridReal i) (upperGridReal (i+1))) :
      (∫ b in upperGridReal 0..upperGridReal 64,
        ∫ c in upperGridReal 0..upperGridReal 64, f a b c) ≤
        ∑ j ∈ Finset.range 64, s * (∑ k ∈ Finset.range 64,
          s * (upperGridWeight i j k : ℝ)) := by
    have h := integral_le_nonnegative_panel_sum upperGridReal 64
      (fun b => ∫ c in upperGridReal 0..upperGridReal 64, f a b c)
      (fun j => ∑ k ∈ Finset.range 64, s * (upperGridWeight i j k : ℝ))
      hp (by intros; positivity) (fun j hj b hb' => inner i j hi hj a b ha hb')
    simpa only [upper_grid_step] using h
  have h := integral_le_nonnegative_panel_sum upperGridReal 64
    (fun a => ∫ b in upperGridReal 0..upperGridReal 64,
      ∫ c in upperGridReal 0..upperGridReal 64, f a b c)
    (fun i => ∑ j ∈ Finset.range 64, s * (∑ k ∈ Finset.range 64,
      s * (upperGridWeight i j k : ℝ))) hp (by intros; positivity) middle
  simp only [upper_grid_step] at h
  have he : (∑ i ∈ Finset.range 64, s * (∑ j ∈ Finset.range 64,
      s * (∑ k ∈ Finset.range 64, s * (upperGridWeight i j k : ℝ)))) =
      (upperGridTotal : ℝ) * s^3 := by
    simp only [← Finset.mul_sum]
    simp only [upperGridTotal, Nat.cast_sum]
    ring
  rw [he, upper_grid_total] at h
  exact h

/-- Page 53. The conservative deleted Buchstab integral on the explicit rational box. -/
noncomputable def upperDeletedIntegral (ω : ℝ → ℝ) (ε : ℝ) : ℝ :=
  ∫ a in upperGridReal 0..upperGridReal 64,
    ∫ b in upperGridReal 0..upperGridReal 64,
      ∫ c in upperGridReal 0..upperGridReal 64, upperDeletedIntegrand ω ε a b c

/-- Page 53. The actual conservative deleted integral has the certified upper sum.
CONDITIONAL on Buchstab's defining equations and its extension convention.
This is the totalized Bochner integral. Integrability is not asserted. -/
theorem upper_deleted_integral_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) :
    upperDeletedIntegral ω ε ≤ 5377228 * (879/400000 : ℝ)^3 := by
  apply upper_integral_of_cells_total (upperDeletedIntegrand ω ε)
  intro i hi j hj k hk a ha b hb c hc
  exact upper_deleted_cell_bound hω hz hε hε' hi hj hk ha hb hc


/-- Page 53. The density formula is below 2.2 once its deleted integral has
our upper bound. CONDITIONAL on the defining Buchstab equations, the zero
extension and the density comparison with the conservative deleted integral. -/
theorem upper_density_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε v1 : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8)
    (hv : v1 ≤
      ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) /
        (1/4+(2*(1/16-1/10^5))/8-ε) + upperDeletedIntegral ω ε) :
    v1 < 2.2 := by
  have hI := upper_deleted_integral_bound hω hz hε hε'
  have hbase := upper_base_enclosure hω hε hε'
  have hbudget := upper_grid_budget
  linarith

/-- Pages 51 and 53. The defining Buchstab equations force nonnegativity above one.
This supplies the sign needed when discarded regions are enlarged.
CONDITIONAL on the defining equations, not on a cited sign estimate. -/
theorem buchstab_nonneg {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    {u : ℝ} (hu : 1 ≤ u) : 0 ≤ ω u := by
  have step : ∀ n : ℕ, ∀ u : ℝ, 1 ≤ u → u ≤ (n : ℝ)+2 → 0 ≤ ω u := by
    intro n
    induction n with
    | zero =>
      intro u hu hu2
      have hu0 : 0 < u := by linarith
      rw [hω.2.1 u hu (by simpa using hu2)]
      positivity
    | succ n ih =>
      intro u hu huMax
      push_cast at huMax
      by_cases hsmall : u ≤ (n : ℝ)+2
      · exact ih u hu hsmall
      let b : ℝ := n+2
      have hb2 : 2 ≤ b := by dsimp [b]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hbu : b ≤ u := (lt_of_not_ge hsmall).le
      have hwb : 0 ≤ ω b := ih b (by linarith) le_rfl
      have hcont : ContinuousOn (fun t : ℝ => t*ω t) (Set.Icc b u) :=
        continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
      have hci : ContinuousOn (fun t : ℝ => ω (t-1)) (Set.uIcc b u) := by
        rw [Set.uIcc_of_le hbu]
        apply hω.1.comp (by fun_prop)
        intro t ht
        change 1 ≤ t-1
        linarith [ht.1]
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hbu hcont
        (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
      have hI : 0 ≤ ∫ t in b..u, ω (t-1) := by
        apply intervalIntegral.integral_nonneg hbu
        intro t ht
        apply ih (t-1) (by linarith [ht.1])
        dsimp [b] at hbu
        linarith [ht.2]
      have hbω : 0 ≤ b*ω b := mul_nonneg (by linarith) hwb
      have huω : 0 ≤ u*ω u := by linarith
      exact nonneg_of_mul_nonneg_right huω (by linarith)
  exact step ⌈u⌉₊ u hu (by linarith [Nat.le_ceil u])


/-- Page 53. The conservative deleted contribution is nonnegative everywhere.
The support and the zero cutoff handle arguments outside the Buchstab domain. -/
theorem upper_deleted_nonneg {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) (a b c : ℝ) :
    0 ≤ upperDeletedIntegrand ω ε a b c := by
  unfold upperDeletedIntegrand
  split_ifs with hdom hu
  · exact le_rfl
  · obtain ⟨hcc, hcb, hba, hac4, hnot⟩ := hdom
    have hp := upper_grid_parameters hε hε'
    have hc0 : 0 < c := by linarith [hp.1]
    have hb0 : 0 < b := lt_of_lt_of_le hc0 hcb
    have ha0 : 0 < a := lt_of_lt_of_le hb0 hba
    exact div_nonneg (buchstab_nonneg hω (le_of_not_gt hu)) (by positivity)
  · exact le_rfl

/-- LEAF. Pages 43 to 53, Lemmas 29 to 35 and displays 5.18 to 5.23.
Construct the actual upper weight, its divisor and distribution bounds,
its centered moment bounds and its density comparison with the conservative
page 53 deleted integral. The numerical bound for this integral is proved
separately. The functional moment estimates, Buchstab identity, prime number
asymptotic and the NormalizationC165 input estimates remain OPEN. -/
theorem upper_short_weight_analytic
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω ∧
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω ∧
      ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
        ∃ (v1 : ℝ) (b1 : ℝ → ℕ → ℝ),
          1 ≤ v1 ∧
          v1 ≤ ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) /
              (1/4+(2*(1/16-1/10^5))/8-ε) + upperDeletedIntegral ω ε ∧
          RightConditions ε B v1 b1 ∧
          ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
            ∀ m ∈ rightInterval ε x, primeWeight m ≤ b1 x m := by
  sorry

/-- LEAF. Pages 43 to 52, the lower short weight b0. Lemmas 29 to 35
supply the moment estimates, the discarded E2 and E4 integrals on page 51
supply v0 above 0.05, and 5.18 to 5.23 on page 52 normalize condition iv.
The density is at most 1 because the discarded integrals are nonnegative.
Reuse the exponent lemmas and NormalizationC165. The analytic inputs and
certified discarded integrals remain OPEN. -/
theorem lower_short_weight (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
        0.05 < v0 ∧ v0 ≤ 1 ∧ RightConditions ε B v0 b0 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  sorry

/-- LEAF. Page 53, the upper short weight b1. The four-term Buchstab
identity is gm minus hm plus jm minus km. Delete only km terms where
Lemma 33 is unavailable. The printed integral formula gives v1 below 2.2.
The upper sandwich and the density asymptotic give v1 at least 1.
Repeat the page 52 normalization. The analytic estimates and certified
Buchstab integral remain OPEN. -/
theorem upper_short_weight (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v1 : ℝ) (b1 : ℝ → ℕ → ℝ),
        1 ≤ v1 ∧ v1 < 2.2 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, primeWeight m ≤ b1 x m := by
  obtain ⟨ω, hω, hz, B0, η, hη, hweight⟩ := upper_short_weight_analytic h4 h9
  refine ⟨B0, min η (1/10^8), lt_min hη (by norm_num), ?_⟩
  intro B ε hB hε hεη
  have hεsmall : ε ≤ 1/10^8 :=
    (lt_of_lt_of_le hεη (min_le_right _ _)).le
  obtain ⟨v1, b1, hv1, hdensity, hright, X, hsandwich⟩ :=
    hweight B ε hB hε (lt_of_lt_of_le hεη (min_le_left _ _))
  exact ⟨v1, b1, hv1, upper_density_bound hω hz hε.le hεsmall hdensity,
    hright, X, hsandwich⟩

/-- Pages 43 to 53, combine the two short constructions at one common
divisor exponent and epsilon cutoff. This is the exact statement of
DecompC165b.section5_weights. CONDITIONAL on both OPEN leaves. -/
theorem section5_weights (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v0 v1 : ℝ) (b0 b1 : ℝ → ℕ → ℝ),
        0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
        RightConditions ε B v0 b0 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x,
            b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m := by
  obtain ⟨B0, η0, hη0, h0⟩ := lower_short_weight h4 h9
  obtain ⟨B1, η1, hη1, h1⟩ := upper_short_weight h4 h9
  refine ⟨max B0 B1, min η0 η1, lt_min hη0 hη1, ?_⟩
  intro B ε hB hε hεη
  obtain ⟨v0, b0, hv0, hv01, hb0, X0, hs0⟩ := h0 B ε
    (le_trans (le_max_left _ _) hB) hε (lt_of_lt_of_le hεη (min_le_left _ _))
  obtain ⟨v1, b1, hv11, hv1, hb1, X1, hs1⟩ := h1 B ε
    (le_trans (le_max_right _ _) hB) hε (lt_of_lt_of_le hεη (min_le_right _ _))
  refine ⟨v0, v1, b0, b1, hv0, le_trans hv01 hv11, hv1, hb0, hb1,
    max X0 X1, ?_⟩
  intro x hx m hm
  exact ⟨hs0 x (le_trans (le_max_left _ _) hx) m hm,
    hs1 x (le_trans (le_max_right _ _) hx) m hm⟩

end LeanLab.BHP1997.DecompC165d
