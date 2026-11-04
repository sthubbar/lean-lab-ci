/-
P0069, Section 5, pages 43 to 53. The two short weight constructions
are separate leaves. Their order comes from densities below and above 1.
The exact final statement is CONDITIONAL on both OPEN leaves.
AI wrote the Lean code. CODEX task165. Goldbach is open.
-/
import LeanLab.BHP1997.SieveConditionsC165
import LeanLab.BHP1997.DensityMono1609
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
asymptotic and the NormalizationC165 input estimates remain OPEN.
U-1609 dropped `1 ≤ v1`, which display 1.5 does not print. `v0 ≤ v1` now comes from
`right_density_mono`. -/
theorem upper_short_weight_analytic
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω ∧
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω ∧
      ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
        ∃ (v1 : ℝ) (b1 : ℝ → ℕ → ℝ),
          v1 ≤ ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) /
              (1/4+(2*(1/16-1/10^5))/8-ε) + upperDeletedIntegral ω ε ∧
          RightConditions ε B v1 b1 ∧
          ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
            ∀ m ∈ rightInterval ε x, primeWeight m ≤ b1 x m := by
  sorry

/-- Page 51. Numerators of the four-prime grid, with denominator 400000. -/
def lowerFourGridPoint (i : ℕ) : ℕ := 49996+587*i

/-- Page 51. Real endpoints of the four-prime grid. -/
noncomputable def lowerFourGridReal (i : ℕ) : ℝ := (lowerFourGridPoint i : ℝ)/400000

/-- Page 51. A sufficient grouping test for four explicit prime factors.
The residual factor stays in L. -/
def lowerFourGridCovered (a A b B c C d D : ℕ) : Bool :=
  upperGridCovered a A b B c C || upperGridCovered a A b B d D ||
  upperGridCovered a A c C d D || upperGridCovered b B c C d D ||
  upperGridGood (a+b+c) (A+B+C) d D || upperGridGood (a+b+d) (A+B+D) c C ||
  upperGridGood (a+c+d) (A+C+D) b B || upperGridGood (b+c+d) (B+C+D) a A

/-- Page 51. The same sufficient prime groupings in real exponent coordinates.
This paper Prop requires Claude review before merge. -/
def lowerFourCovered (ε a b c d : ℝ) : Prop :=
  upperPrimeCovered ε a b c ∨ upperPrimeCovered ε a b d ∨
  upperPrimeCovered ε a c d ∨ upperPrimeCovered ε b c d ∨
  upperPairRegion ε (a+b+c) d ∨ upperPairRegion ε (a+b+d) c ∨
  upperPairRegion ε (a+c+d) b ∨ upperPairRegion ε (b+c+d) a

/-- Page 51. Conservative four-prime discarded integrand after the second decomposition.
The last prime and the residual rough factor are both at least the fourth prime.
The triple product cutoff is the condition for taking that decomposition. -/
noncomputable def lowerFourDeletedIntegrand (ω : ℝ → ℝ) (ε a b c d : ℝ) : ℝ :=
  if (1+7*(2*(1/16-1/10^5)))/15-ε ≤ d ∧ d ≤ c ∧ c ≤ b ∧ b ≤ a ∧
      a+2*b ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε ∧
      a+b+c ≤ 1/2+(2*(1/16-1/10^5))/4-2*ε ∧ ¬lowerFourCovered ε a b c d then
    if (1-a-b-c-d)/d < 1 then 0 else ω ((1-a-b-c-d)/d)/(a*b*c*d^2)
  else 0

/-- Page 51. Upward integer cell bound, with whole-cell support and grouping exclusions. -/
def lowerFourCellWeight (i j k l : ℕ) : ℕ :=
  if i+2 ≤ j ∨ j+2 ≤ k ∨ k+2 ≤ l then 0 else
    let a := lowerFourGridPoint i
    let b := lowerFourGridPoint j
    let c := lowerFourGridPoint k
    let d := lowerFourGridPoint l
    if 224998 < a+2*b ∨ 212498 < a+b+c ∨ 400000 < a+b+c+2*d then 0 else
      if lowerFourGridCovered a (a+587) b (b+587) c (c+587) d (d+587) then 0 else
        upperGridCeil (400000^5) (a*b*c*d*d)

/-- Page 51. A computationally pruned row of the four-dimensional upper sum.
The pruning removes only cells already assigned weight zero. -/
def lowerFourRow (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min 128 (i+2)),
    if 224998 < lowerFourGridPoint i+2*lowerFourGridPoint j then 0 else
      ∑ k ∈ Finset.range (min 128 (j+2)),
        if 212498 < lowerFourGridPoint i+lowerFourGridPoint j+lowerFourGridPoint k then 0 else
          ∑ l ∈ Finset.range (min 128 (k+2)), lowerFourCellWeight i j k l

/-- Page 51. The explicit integer upper sum for the four-prime discard. -/
def lowerFourTotal : ℕ := ∑ i ∈ Finset.range 128, lowerFourRow i
/-- Page 51. Each four-prime whole-cell grouping test gives a legal real grouping. -/
theorem lower_four_covered_sound {ε a b c d : ℝ} {ia iA ib iB ic iC id iD : ℕ}
    (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8)
    (ha : a ∈ Set.Icc ((ia:ℝ)/400000) ((iA:ℝ)/400000))
    (hb : b ∈ Set.Icc ((ib:ℝ)/400000) ((iB:ℝ)/400000))
    (hc : c ∈ Set.Icc ((ic:ℝ)/400000) ((iC:ℝ)/400000))
    (hd : d ∈ Set.Icc ((id:ℝ)/400000) ((iD:ℝ)/400000))
    (hca : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ a)
    (hcb : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ b)
    (hcc : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ c)
    (hcd : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ d)
    (ht : lowerFourGridCovered ia iA ib iB ic iC id iD = true) :
    lowerFourCovered ε a b c d := by
  have hsum {x y z : ℝ} {ix iX iy iY iz iZ : ℕ}
      (hx : x ∈ Set.Icc ((ix:ℝ)/400000) ((iX:ℝ)/400000))
      (hy : y ∈ Set.Icc ((iy:ℝ)/400000) ((iY:ℝ)/400000))
      (hz : z ∈ Set.Icc ((iz:ℝ)/400000) ((iZ:ℝ)/400000)) :
      x+y+z ∈ Set.Icc (((ix+iy+iz:ℕ):ℝ)/400000) (((iX+iY+iZ:ℕ):ℝ)/400000) := by
    push_cast
    constructor <;> linarith [hx.1,hx.2,hy.1,hy.2,hz.1,hz.2]
  have h1 := upper_grid_covered_sound hε hε' ha hb hc hca hcb hcc
  have h2 := upper_grid_covered_sound hε hε' ha hb hd hca hcb hcd
  have h3 := upper_grid_covered_sound hε hε' ha hc hd hca hcc hcd
  have h4 := upper_grid_covered_sound hε hε' hb hc hd hcb hcc hcd
  have h5 := upper_grid_good_sound rfl rfl rfl rfl hε hε' (hsum ha hb hc) hd hcd
  have h6 := upper_grid_good_sound rfl rfl rfl rfl hε hε' (hsum ha hb hd) hc hcc
  have h7 := upper_grid_good_sound rfl rfl rfl rfl hε hε' (hsum ha hc hd) hb hcb
  have h8 := upper_grid_good_sound rfl rfl rfl rfl hε hε' (hsum hb hc hd) ha hca
  simp only [lowerFourGridCovered, Bool.or_eq_true, or_assoc] at ht
  unfold lowerFourCovered
  rcases ht with ht|ht|ht|ht|ht|ht|ht|ht
  · exact Or.inl (h1 ht)
  · exact Or.inr (Or.inl (h2 ht))
  · exact Or.inr (Or.inr (Or.inl (h3 ht)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h4 ht))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h5 ht)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h6 ht))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h7 ht)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h8 ht)))))))


/-- Page 51. Every four-prime grid cell has width 587 divided by 400000. -/
theorem lower_four_grid_step (i : ℕ) :
    lowerFourGridReal (i+1)-lowerFourGridReal i = (587:ℝ)/400000 := by
  simp [lowerFourGridReal,lowerFourGridPoint,Nat.cast_add,Nat.cast_mul]
  ring


/-- Page 51. The computational row pruning removes only zero weights. -/
theorem lower_four_row_full (i : ℕ) : lowerFourRow i =
    ∑ j ∈ Finset.range 128, ∑ k ∈ Finset.range 128,
      ∑ l ∈ Finset.range 128, lowerFourCellWeight i j k l := by
  have cut (n m : ℕ) (f : ℕ → ℕ) (hf : ∀ r, m ≤ r → f r = 0) :
      (∑ r ∈ Finset.range n, f r) = ∑ r ∈ Finset.range (min n m), f r := by
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.min_le_left n m))
    intro r hr hr'
    simp only [Finset.mem_range] at hr hr'
    exact hf r (by omega)
  symm
  unfold lowerFourRow
  rw [cut 128 (i+2) _ (by
    intro j hj
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro l hl
    simp [lowerFourCellWeight,hj])]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases ho : 224998 < lowerFourGridPoint i+2*lowerFourGridPoint j
  · rw [if_pos ho]
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro l hl
    simp [lowerFourCellWeight,ho]
  · rw [if_neg ho]
    rw [cut 128 (j+2) _ (by
      intro k hk
      apply Finset.sum_eq_zero
      intro l hl
      simp [lowerFourCellWeight,hk])]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hq : 212498 < lowerFourGridPoint i+lowerFourGridPoint j+lowerFourGridPoint k
    · rw [if_pos hq]
      apply Finset.sum_eq_zero
      intro l hl
      simp [lowerFourCellWeight,hq]
    · rw [if_neg hq]
      apply cut
      intro l hl
      simp [lowerFourCellWeight,hl]

/-- Page 51. A four-prime cell is bounded by its upward rational weight.
CONDITIONAL on the defining Buchstab equations and zero extension. -/
theorem lower_four_raw_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {i j k l : ℕ} {a b c d : ℝ}
    (ha : a ∈ Set.Icc (lowerFourGridReal i) (lowerFourGridReal (i+1)))
    (hb : b ∈ Set.Icc (lowerFourGridReal j) (lowerFourGridReal (j+1)))
    (hc : c ∈ Set.Icc (lowerFourGridReal k) (lowerFourGridReal (k+1)))
    (hd : d ∈ Set.Icc (lowerFourGridReal l) (lowerFourGridReal (l+1))) :
    ω ((1-a-b-c-d)/d)/(a*b*c*d^2) ≤
      (upperGridCeil (400000^5) (lowerFourGridPoint i*lowerFourGridPoint j*
        lowerFourGridPoint k*lowerFourGridPoint l*lowerFourGridPoint l) : ℕ) := by
  have hp (i : ℕ) : (0:ℝ) < lowerFourGridPoint i := by
    unfold lowerFourGridPoint
    positivity
  have hlow (i : ℕ) : 0 < lowerFourGridReal i := by
    exact div_pos (hp i) (by norm_num)
  have hpi := hlow i
  have hpj := hlow j
  have hpk := hlow k
  have hpl := hlow l
  have ha0 : 0 < a := lt_of_lt_of_le (hlow i) ha.1
  have hb0 : 0 < b := lt_of_lt_of_le (hlow j) hb.1
  have hc0 : 0 < c := lt_of_lt_of_le (hlow k) hc.1
  have hd0 : 0 < d := lt_of_lt_of_le (hlow l) hd.1
  have hden : lowerFourGridReal i*lowerFourGridReal j*lowerFourGridReal k*
      lowerFourGridReal l^2 ≤ a*b*c*d^2 := by gcongr <;> linarith [hpi,hpj,hpk,hpl,ha.1,hb.1,hc.1,hd.1]
  have hbound := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz ((1-a-b-c-d)/d)
  have hceil := upper_grid_ceil_bound (n:=400000^5)
    (d:=lowerFourGridPoint i*lowerFourGridPoint j*lowerFourGridPoint k*
      lowerFourGridPoint l*lowerFourGridPoint l) (by unfold lowerFourGridPoint; positivity)
  have he : 1/(lowerFourGridReal i*lowerFourGridReal j*lowerFourGridReal k*lowerFourGridReal l^2) =
      (400000:ℝ)^5/(lowerFourGridPoint i*lowerFourGridPoint j*
        lowerFourGridPoint k*lowerFourGridPoint l*lowerFourGridPoint l : ℕ) := by
    unfold lowerFourGridReal
    push_cast
    field_simp <;> ring
  calc
    _ ≤ 1/(a*b*c*d^2) := div_le_div_of_nonneg_right hbound (by positivity)
    _ ≤ 1/(lowerFourGridReal i*lowerFourGridReal j*lowerFourGridReal k*lowerFourGridReal l^2) :=
      div_le_div_of_nonneg_left zero_le_one (by positivity) hden
    _ = _ := he
    _ ≤ _ := by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hceil


set_option maxRecDepth 100000 in
/-- Page 51. Whole-cell support and grouping checks bound the conservative E4 integrand.
CONDITIONAL on the defining Buchstab equations and zero extension. -/
theorem lower_four_cell_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8)
    {i j k l : ℕ} {a b c d : ℝ}
    (ha : a ∈ Set.Icc (lowerFourGridReal i) (lowerFourGridReal (i+1)))
    (hb : b ∈ Set.Icc (lowerFourGridReal j) (lowerFourGridReal (j+1)))
    (hc : c ∈ Set.Icc (lowerFourGridReal k) (lowerFourGridReal (k+1)))
    (hd : d ∈ Set.Icc (lowerFourGridReal l) (lowerFourGridReal (l+1))) :
    lowerFourDeletedIntegrand ω ε a b c d ≤ (lowerFourCellWeight i j k l : ℝ) := by
  unfold lowerFourDeletedIntegrand
  split_ifs with hdom hu
  · exact Nat.cast_nonneg _
  · obtain ⟨hcd1,hdc,hcb,hba,hD,hTriple,hnot⟩ := hdom
    have he (i : ℕ) : lowerFourGridPoint (i+1) = lowerFourGridPoint i+587 := by
      unfold lowerFourGridPoint
      omega
    have ha' : a ∈ Set.Icc ((lowerFourGridPoint i:ℝ)/400000) (((lowerFourGridPoint i+587:ℕ):ℝ)/400000) := by
      simpa only [lowerFourGridReal,he] using ha
    have hb' : b ∈ Set.Icc ((lowerFourGridPoint j:ℝ)/400000) (((lowerFourGridPoint j+587:ℕ):ℝ)/400000) := by
      simpa only [lowerFourGridReal,he] using hb
    have hc' : c ∈ Set.Icc ((lowerFourGridPoint k:ℝ)/400000) (((lowerFourGridPoint k+587:ℕ):ℝ)/400000) := by
      simpa only [lowerFourGridReal,he] using hc
    have hd' : d ∈ Set.Icc ((lowerFourGridPoint l:ℝ)/400000) (((lowerFourGridPoint l+587:ℕ):ℝ)/400000) := by
      simpa only [lowerFourGridReal,he] using hd
    have hcc1 := le_trans hcd1 hdc
    have hcb1 := le_trans hcc1 hcb
    have hca1 := le_trans hcb1 hba
    have hcover : lowerFourGridCovered (lowerFourGridPoint i) (lowerFourGridPoint i+587)
        (lowerFourGridPoint j) (lowerFourGridPoint j+587)
        (lowerFourGridPoint k) (lowerFourGridPoint k+587)
        (lowerFourGridPoint l) (lowerFourGridPoint l+587) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hnot (lower_four_covered_sound hε hε' ha' hb' hc' hd' hca1 hcb1 hcc1 hcd1 ht)
    have haR := ha
    have hbR := hb
    have hcR := hc
    have hdR := hd
    norm_num [lowerFourGridReal,lowerFourGridPoint,Nat.cast_add,Nat.cast_mul] at haR hbR hcR hdR
    have hindex : ¬(i+2 ≤ j ∨ j+2 ≤ k ∨ k+2 ≤ l) := by
      intro hout
      rcases hout with hij | hjk | hkl
      · have hR : (i:ℝ)+2 ≤ j := by exact_mod_cast hij
        linarith [haR.2,hbR.1]
      · have hR : (j:ℝ)+2 ≤ k := by exact_mod_cast hjk
        linarith [hbR.2,hcR.1]
      · have hR : (k:ℝ)+2 ≤ l := by exact_mod_cast hkl
        linarith [hcR.2,hdR.1]
    have hp := upper_grid_parameters hε hε'
    have hd0 : 0 < d := by linarith [hp.1]
    have hsupport : a+b+c+2*d ≤ 1 := by
      have hh := (le_div_iff₀ hd0).1 (le_of_not_gt hu)
      linarith
    have hout : ¬(224998 < lowerFourGridPoint i+2*lowerFourGridPoint j ∨
        212498 < lowerFourGridPoint i+lowerFourGridPoint j+lowerFourGridPoint k ∨
        400000 < lowerFourGridPoint i+lowerFourGridPoint j+lowerFourGridPoint k+2*lowerFourGridPoint l) := by
      intro h
      rcases h with h|h|h
      · have hR : (224998:ℝ) < lowerFourGridPoint i+2*lowerFourGridPoint j := by exact_mod_cast h
        norm_num [lowerFourGridPoint,Nat.cast_add,Nat.cast_mul] at hR hD
        linarith [haR.1,hbR.1]
      · have hR : (212498:ℝ) < lowerFourGridPoint i+lowerFourGridPoint j+lowerFourGridPoint k := by exact_mod_cast h
        norm_num [lowerFourGridPoint,Nat.cast_add,Nat.cast_mul] at hR hTriple
        linarith [haR.1,hbR.1,hcR.1]
      · have hR : (400000:ℝ) < lowerFourGridPoint i+lowerFourGridPoint j+lowerFourGridPoint k+2*lowerFourGridPoint l := by exact_mod_cast h
        norm_num [lowerFourGridPoint,Nat.cast_add,Nat.cast_mul] at hR
        linarith [haR.1,hbR.1,hcR.1,hdR.1]
    simpa only [lowerFourCellWeight,if_neg hindex,if_neg hout,hcover,Bool.false_eq_true,↓reduceIte]
      using lower_four_raw_bound hω hz ha hb hc hd
  · exact Nat.cast_nonneg _

/-- Page 51. A fourfold nonnegative grid upper sum bounds the totalized Bochner integral.
This theorem asserts an upper bound and does not assert integrability. -/
theorem lower_four_integral_of_cells (f : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hb : ∀ i < 128, ∀ j < 128, ∀ k < 128, ∀ l < 128,
      ∀ a ∈ Set.Icc (lowerFourGridReal i) (lowerFourGridReal (i+1)),
      ∀ b ∈ Set.Icc (lowerFourGridReal j) (lowerFourGridReal (j+1)),
      ∀ c ∈ Set.Icc (lowerFourGridReal k) (lowerFourGridReal (k+1)),
      ∀ d ∈ Set.Icc (lowerFourGridReal l) (lowerFourGridReal (l+1)),
      f a b c d ≤ (lowerFourCellWeight i j k l : ℝ)) :
    (∫ a in lowerFourGridReal 0..lowerFourGridReal 128,
      ∫ b in lowerFourGridReal 0..lowerFourGridReal 128,
        ∫ c in lowerFourGridReal 0..lowerFourGridReal 128,
          ∫ d in lowerFourGridReal 0..lowerFourGridReal 128, f a b c d) ≤
      (lowerFourTotal : ℝ)*(587/400000 : ℝ)^4 := by
  let s : ℝ := 587/400000
  have hs : 0 ≤ s := by norm_num [s]
  have hp : Monotone lowerFourGridReal := by
    intro i j hij
    norm_num [lowerFourGridReal,lowerFourGridPoint,Nat.cast_add,Nat.cast_mul]
    have hR : (i:ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have h1 (i j k : ℕ) (hi : i < 128) (hj : j < 128) (hk : k < 128)
      (a b c : ℝ)
      (ha : a ∈ Set.Icc (lowerFourGridReal i) (lowerFourGridReal (i+1)))
      (hb' : b ∈ Set.Icc (lowerFourGridReal j) (lowerFourGridReal (j+1)))
      (hc : c ∈ Set.Icc (lowerFourGridReal k) (lowerFourGridReal (k+1))) :
      (∫ d in lowerFourGridReal 0..lowerFourGridReal 128, f a b c d) ≤
        ∑ l ∈ Finset.range 128, s*(lowerFourCellWeight i j k l : ℝ) := by
    have h := integral_le_nonnegative_panel_sum lowerFourGridReal 128 (f a b c)
      (fun l => (lowerFourCellWeight i j k l:ℝ)) hp (by intros; positivity)
      (fun l hl d hd => hb i hi j hj k hk l hl a ha b hb' c hc d hd)
    simpa only [lower_four_grid_step] using h
  have h2 (i j : ℕ) (hi : i < 128) (hj : j < 128) (a b : ℝ)
      (ha : a ∈ Set.Icc (lowerFourGridReal i) (lowerFourGridReal (i+1)))
      (hb' : b ∈ Set.Icc (lowerFourGridReal j) (lowerFourGridReal (j+1))) :
      (∫ c in lowerFourGridReal 0..lowerFourGridReal 128,
        ∫ d in lowerFourGridReal 0..lowerFourGridReal 128, f a b c d) ≤
        ∑ k ∈ Finset.range 128, s*(∑ l ∈ Finset.range 128,
          s*(lowerFourCellWeight i j k l:ℝ)) := by
    have h := integral_le_nonnegative_panel_sum lowerFourGridReal 128
      (fun c => ∫ d in lowerFourGridReal 0..lowerFourGridReal 128, f a b c d)
      (fun k => ∑ l ∈ Finset.range 128,s*(lowerFourCellWeight i j k l:ℝ))
      hp (by intros; positivity) (fun k hk c hc => h1 i j k hi hj hk a b c ha hb' hc)
    simpa only [lower_four_grid_step] using h
  have h3 (i : ℕ) (hi : i < 128) (a : ℝ)
      (ha : a ∈ Set.Icc (lowerFourGridReal i) (lowerFourGridReal (i+1))) :
      (∫ b in lowerFourGridReal 0..lowerFourGridReal 128,
        ∫ c in lowerFourGridReal 0..lowerFourGridReal 128,
          ∫ d in lowerFourGridReal 0..lowerFourGridReal 128, f a b c d) ≤
        ∑ j ∈ Finset.range 128,s*(∑ k ∈ Finset.range 128,
          s*(∑ l ∈ Finset.range 128,s*(lowerFourCellWeight i j k l:ℝ))) := by
    have h := integral_le_nonnegative_panel_sum lowerFourGridReal 128
      (fun b => ∫ c in lowerFourGridReal 0..lowerFourGridReal 128,
        ∫ d in lowerFourGridReal 0..lowerFourGridReal 128,f a b c d)
      (fun j => ∑ k ∈ Finset.range 128,s*(∑ l ∈ Finset.range 128,s*(lowerFourCellWeight i j k l:ℝ)))
      hp (by intros; positivity) (fun j hj b hb' => h2 i j hi hj a b ha hb')
    simpa only [lower_four_grid_step] using h
  have h := integral_le_nonnegative_panel_sum lowerFourGridReal 128
    (fun a => ∫ b in lowerFourGridReal 0..lowerFourGridReal 128,
      ∫ c in lowerFourGridReal 0..lowerFourGridReal 128,
        ∫ d in lowerFourGridReal 0..lowerFourGridReal 128,f a b c d)
    (fun i => ∑ j ∈ Finset.range 128,s*(∑ k ∈ Finset.range 128,
      s*(∑ l ∈ Finset.range 128,s*(lowerFourCellWeight i j k l:ℝ))))
    hp (by intros; positivity) h3
  simp only [lower_four_grid_step] at h
  have hfull : (∑ i ∈ Finset.range 128,∑ j ∈ Finset.range 128,
      ∑ k ∈ Finset.range 128,∑ l ∈ Finset.range 128,lowerFourCellWeight i j k l) = lowerFourTotal := by
    unfold lowerFourTotal
    apply Finset.sum_congr rfl
    intro i hi
    exact (lower_four_row_full i).symm
  have hcast : (∑ i ∈ Finset.range 128,∑ j ∈ Finset.range 128,
      ∑ k ∈ Finset.range 128,∑ l ∈ Finset.range 128,(lowerFourCellWeight i j k l:ℝ)) = (lowerFourTotal:ℝ) := by
    have hh := congrArg (fun n : ℕ => (n:ℝ)) hfull
    simpa only [Nat.cast_sum] using hh
  have he : (∑ i ∈ Finset.range 128,s*(∑ j ∈ Finset.range 128,
      s*(∑ k ∈ Finset.range 128,s*(∑ l ∈ Finset.range 128,s*(lowerFourCellWeight i j k l:ℝ)))) ) =
      (lowerFourTotal:ℝ)*s^4 := by
    calc
      _ = (∑ i ∈ Finset.range 128,∑ j ∈ Finset.range 128,
          ∑ k ∈ Finset.range 128,∑ l ∈ Finset.range 128,(lowerFourCellWeight i j k l:ℝ))*s^4 := by
        simp only [← Finset.mul_sum]
        ring
      _ = _ := by rw [hcast]
  rw [he] at h
  exact h


/-- Page 51. The conservative four-prime discarded integral on the rational box. -/
noncomputable def lowerFourDeletedIntegral (ω : ℝ → ℝ) (ε : ℝ) : ℝ :=
  ∫ a in lowerFourGridReal 0..lowerFourGridReal 128,
    ∫ b in lowerFourGridReal 0..lowerFourGridReal 128,
      ∫ c in lowerFourGridReal 0..lowerFourGridReal 128,
        ∫ d in lowerFourGridReal 0..lowerFourGridReal 128,lowerFourDeletedIntegrand ω ε a b c d

/-- Page 51. The actual conservative four-prime integrand has the explicit integer upper sum.
CONDITIONAL on the defining Buchstab equations and zero extension. -/
theorem lower_four_integral_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) :
    lowerFourDeletedIntegral ω ε ≤ (lowerFourTotal:ℝ)*(587/400000:ℝ)^4 := by
  apply lower_four_integral_of_cells
  intro i hi j hj k hk l hl a ha b hb c hc d hd
  exact lower_four_cell_bound hω hz hε hε' ha hb hc hd

/-- Page 51. The entire ordered four-prime decomposition domain lies in the rational box.
The upper endpoint follows from D and the lower c1 bound, not from numerical sampling. -/
theorem lower_four_domain_box {ε a b c d : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8)
    (hd : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ d)
    (hdc : d ≤ c) (hcb : c ≤ b) (hba : b ≤ a)
    (hD : a+2*b ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε) :
    a ∈ Set.Icc (lowerFourGridReal 0) (lowerFourGridReal 128) ∧
    b ∈ Set.Icc (lowerFourGridReal 0) (lowerFourGridReal 128) ∧
    c ∈ Set.Icc (lowerFourGridReal 0) (lowerFourGridReal 128) ∧
    d ∈ Set.Icc (lowerFourGridReal 0) (lowerFourGridReal 128) := by
  norm_num [lowerFourGridReal,lowerFourGridPoint] at *
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith

/-- Page 51. Rational nodes for auxiliary Buchstab tangent envelopes. -/
noncomputable def buchstabLogNode (i : Fin 7) : ℝ := ![1,11/10,6/5,13/10,7/5,3/2,8/5] i

/-- Page 51. Upward rational logarithm enclosures for the tangent nodes. -/
noncomputable def buchstabLogCap (i : Fin 7) : ℝ :=
  ![0,95311/1000000,182322/1000000,262365/1000000,336473/1000000,405466/1000000,470004/1000000] i

set_option maxHeartbeats 1000000 in
/-- Page 51. All logarithm caps and tangent signs follow from rational interval arithmetic.
The logarithm remainder is supplied by the proved finite-series enclosure. -/
theorem buchstab_log_nodes (i : Fin 7) :
    0 < buchstabLogNode i ∧ Real.log (buchstabLogNode i) ≤ buchstabLogCap i ∧
    buchstabLogCap i ≤ 1/buchstabLogNode i ∧
    (567144/1000000:ℝ) ≤ 1/buchstabLogNode i +
      (buchstabLogCap i-1/buchstabLogNode i)/3 := by
  have ha : 1 ≤ buchstabLogNode i := by fin_cases i <;> norm_num [buchstabLogNode]
  have hlog := (LeanLab.ChenDoubleSieve.Wu04Integral.log_bounds 8 ha).2
  have hcap : LeanLab.ChenDoubleSieve.Wu04Integral.logUpper 8 (buchstabLogNode i) ≤ buchstabLogCap i := by
    fin_cases i <;> norm_num [buchstabLogNode,buchstabLogCap,
      LeanLab.ChenDoubleSieve.Wu04Integral.logUpper,LeanLab.ChenDoubleSieve.Wu04Integral.logLower,
      Finset.sum_range_succ]
  refine ⟨by linarith, hlog.trans hcap, ?_, ?_⟩ <;>
    fin_cases i <;> norm_num [buchstabLogNode,buchstabLogCap]


/-- Page 51. A certified logarithm tangent bounds Buchstab above two.
The third-point condition connects the explicit two-to-three formula to the global envelope.
CONDITIONAL on the defining Buchstab equations. -/
theorem buchstab_tangent_upper {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    {a L u : ℝ} (ha : 0 < a) (hL : Real.log a ≤ L)
    (hneg : L-1/a ≤ 0) (hthree : (567144/1000000:ℝ) ≤ 1/a+(L-1/a)/3)
    (hu : 2 ≤ u) : ω u ≤ 1/a+(L-1/a)/u := by
  by_cases hu3 : u ≤ 3
  · rw [LeanLab.ChenDoubleSieve.Wu04Buchstab.formula_two_three hω ⟨hu,hu3⟩]
    have hu0 : 0 < u := by linarith
    have hu1 : 0 < u-1 := by linarith
    have hh := Real.log_le_sub_one_of_pos (div_pos hu1 ha)
    rw [Real.log_div hu1.ne' ha.ne'] at hh
    apply (div_le_iff₀ hu0).2
    have he : (1/a+(L-1/a)/u)*u = (u-1)/a+L := by field_simp <;> ring
    rw [he]
    linarith
  · apply (LeanLab.ChenDoubleSieve.Wu04Buchstab.buchstab_le_567144 hω hu).trans
    have hrec : 1/u ≤ (1/3:ℝ) := one_div_le_one_div_of_le (by norm_num) (le_of_not_ge hu3)
    have hm := mul_le_mul_of_nonpos_left hrec hneg
    have hs : 1/a+(L-1/a)/3 ≤ 1/a+(L-1/a)/u := by
      simpa only [div_eq_mul_inv,one_div,one_mul] using add_le_add (le_refl (1/a)) hm
    exact hthree.trans hs


/-- Page 51. A whole interval above two has an explicit rational tangent upper bound.
This is the pointwise estimate needed for rational E2 boxes without floating point logs.
CONDITIONAL on the defining Buchstab equations. -/
theorem buchstab_tangent_cell_upper {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (i : Fin 7) {u U : ℝ} (hu : 2 ≤ u) (hU : u ≤ U) :
    ω u ≤ 1/buchstabLogNode i+(buchstabLogCap i-1/buchstabLogNode i)/U := by
  obtain ⟨ha,hL,hneg,hthree⟩ := buchstab_log_nodes i
  have ht := buchstab_tangent_upper hω ha hL (sub_nonpos.mpr hneg) hthree hu
  have hu0 : 0 < u := by linarith
  have hrec : 1/U ≤ 1/u := one_div_le_one_div_of_le hu0 hU
  have hm := mul_le_mul_of_nonpos_left hrec (sub_nonpos.mpr hneg)
  have hs : 1/buchstabLogNode i+(buchstabLogCap i-1/buchstabLogNode i)/u ≤
      1/buchstabLogNode i+(buchstabLogCap i-1/buchstabLogNode i)/U := by
    simpa only [div_eq_mul_inv,one_div,one_mul] using add_le_add (le_refl (1/buchstabLogNode i)) hm
  exact ht.trans hs

/-- Page 51. Row totals of the explicit four-prime certificate. -/
def lowerFourRowTotal : ℕ → ℕ
  | 0 => 32782
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 18053
  | 10 => 197858
  | 11 => 717255
  | 12 => 1555810
  | 13 => 2138393
  | 14 => 2488030
  | 15 => 2233272
  | 16 => 1952656
  | 17 => 1077892
  | 18 => 849843
  | 19 => 295254
  | 20 => 156545
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | 24 => 0
  | 25 => 86788
  | 26 => 302138
  | 27 => 703907
  | 28 => 1401753
  | 29 => 2209216
  | 30 => 3100319
  | 31 => 3670541
  | 32 => 4057791
  | 33 => 3641142
  | 34 => 2881702
  | 35 => 2138023
  | 36 => 1821164
  | 37 => 1129546
  | 38 => 724712
  | 39 => 408677
  | 40 => 336383
  | 41 => 154838
  | 42 => 64857
  | 43 => 8070
  | 44 => 0
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 0
  | 54 => 0
  | 55 => 0
  | 56 => 0
  | 57 => 0
  | 58 => 0
  | 59 => 0
  | 60 => 0
  | 61 => 0
  | 62 => 0
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 0
  | 68 => 0
  | 69 => 1028505
  | 70 => 961698
  | 71 => 881428
  | 72 => 732894
  | 73 => 700788
  | 74 => 698204
  | 75 => 634625
  | 76 => 570867
  | 77 => 503946
  | 78 => 421323
  | 79 => 307792
  | 80 => 280961
  | 81 => 270296
  | 82 => 257917
  | 83 => 145992
  | 84 => 65255
  | 85 => 16408
  | 86 => 0
  | 87 => 0
  | 88 => 0
  | 89 => 0
  | 90 => 0
  | 91 => 0
  | 92 => 0
  | 93 => 0
  | 94 => 0
  | 95 => 0
  | 96 => 0
  | 97 => 0
  | 98 => 0
  | 99 => 0
  | 100 => 0
  | 101 => 0
  | 102 => 0
  | 103 => 0
  | 104 => 0
  | 105 => 0
  | 106 => 0
  | 107 => 0
  | 108 => 0
  | 109 => 0
  | 110 => 0
  | 111 => 0
  | 112 => 0
  | 113 => 0
  | 114 => 0
  | 115 => 0
  | 116 => 0
  | 117 => 0
  | 118 => 0
  | 119 => 0
  | 120 => 0
  | 121 => 0
  | 122 => 0
  | 123 => 0
  | 124 => 0
  | 125 => 0
  | 126 => 0
  | 127 => 0
  | _ => 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Page 51. The pruned integer upper sum is checked by kernel reduction. -/
theorem lower_four_total : lowerFourTotal = 51034109 := by
  have h0 : lowerFourRow 0 = 32782 := by decide +kernel
  have h1 : lowerFourRow 1 = 0 := by decide +kernel
  have h2 : lowerFourRow 2 = 0 := by decide +kernel
  have h3 : lowerFourRow 3 = 0 := by decide +kernel
  have h4 : lowerFourRow 4 = 0 := by decide +kernel
  have h5 : lowerFourRow 5 = 0 := by decide +kernel
  have h6 : lowerFourRow 6 = 0 := by decide +kernel
  have h7 : lowerFourRow 7 = 0 := by decide +kernel
  have h8 : lowerFourRow 8 = 0 := by decide +kernel
  have h9 : lowerFourRow 9 = 18053 := by decide +kernel
  have h10 : lowerFourRow 10 = 197858 := by decide +kernel
  have h11 : lowerFourRow 11 = 717255 := by decide +kernel
  have h12 : lowerFourRow 12 = 1555810 := by decide +kernel
  have h13 : lowerFourRow 13 = 2138393 := by decide +kernel
  have h14 : lowerFourRow 14 = 2488030 := by decide +kernel
  have h15 : lowerFourRow 15 = 2233272 := by decide +kernel
  have h16 : lowerFourRow 16 = 1952656 := by decide +kernel
  have h17 : lowerFourRow 17 = 1077892 := by decide +kernel
  have h18 : lowerFourRow 18 = 849843 := by decide +kernel
  have h19 : lowerFourRow 19 = 295254 := by decide +kernel
  have h20 : lowerFourRow 20 = 156545 := by decide +kernel
  have h21 : lowerFourRow 21 = 0 := by decide +kernel
  have h22 : lowerFourRow 22 = 0 := by decide +kernel
  have h23 : lowerFourRow 23 = 0 := by decide +kernel
  have h24 : lowerFourRow 24 = 0 := by decide +kernel
  have h25 : lowerFourRow 25 = 86788 := by decide +kernel
  have h26 : lowerFourRow 26 = 302138 := by decide +kernel
  have h27 : lowerFourRow 27 = 703907 := by decide +kernel
  have h28 : lowerFourRow 28 = 1401753 := by decide +kernel
  have h29 : lowerFourRow 29 = 2209216 := by decide +kernel
  have h30 : lowerFourRow 30 = 3100319 := by decide +kernel
  have h31 : lowerFourRow 31 = 3670541 := by decide +kernel
  have h32 : lowerFourRow 32 = 4057791 := by decide +kernel
  have h33 : lowerFourRow 33 = 3641142 := by decide +kernel
  have h34 : lowerFourRow 34 = 2881702 := by decide +kernel
  have h35 : lowerFourRow 35 = 2138023 := by decide +kernel
  have h36 : lowerFourRow 36 = 1821164 := by decide +kernel
  have h37 : lowerFourRow 37 = 1129546 := by decide +kernel
  have h38 : lowerFourRow 38 = 724712 := by decide +kernel
  have h39 : lowerFourRow 39 = 408677 := by decide +kernel
  have h40 : lowerFourRow 40 = 336383 := by decide +kernel
  have h41 : lowerFourRow 41 = 154838 := by decide +kernel
  have h42 : lowerFourRow 42 = 64857 := by decide +kernel
  have h43 : lowerFourRow 43 = 8070 := by decide +kernel
  have h44 : lowerFourRow 44 = 0 := by decide +kernel
  have h45 : lowerFourRow 45 = 0 := by decide +kernel
  have h46 : lowerFourRow 46 = 0 := by decide +kernel
  have h47 : lowerFourRow 47 = 0 := by decide +kernel
  have h48 : lowerFourRow 48 = 0 := by decide +kernel
  have h49 : lowerFourRow 49 = 0 := by decide +kernel
  have h50 : lowerFourRow 50 = 0 := by decide +kernel
  have h51 : lowerFourRow 51 = 0 := by decide +kernel
  have h52 : lowerFourRow 52 = 0 := by decide +kernel
  have h53 : lowerFourRow 53 = 0 := by decide +kernel
  have h54 : lowerFourRow 54 = 0 := by decide +kernel
  have h55 : lowerFourRow 55 = 0 := by decide +kernel
  have h56 : lowerFourRow 56 = 0 := by decide +kernel
  have h57 : lowerFourRow 57 = 0 := by decide +kernel
  have h58 : lowerFourRow 58 = 0 := by decide +kernel
  have h59 : lowerFourRow 59 = 0 := by decide +kernel
  have h60 : lowerFourRow 60 = 0 := by decide +kernel
  have h61 : lowerFourRow 61 = 0 := by decide +kernel
  have h62 : lowerFourRow 62 = 0 := by decide +kernel
  have h63 : lowerFourRow 63 = 0 := by decide +kernel
  have h64 : lowerFourRow 64 = 0 := by decide +kernel
  have h65 : lowerFourRow 65 = 0 := by decide +kernel
  have h66 : lowerFourRow 66 = 0 := by decide +kernel
  have h67 : lowerFourRow 67 = 0 := by decide +kernel
  have h68 : lowerFourRow 68 = 0 := by decide +kernel
  have h69 : lowerFourRow 69 = 1028505 := by decide +kernel
  have h70 : lowerFourRow 70 = 961698 := by decide +kernel
  have h71 : lowerFourRow 71 = 881428 := by decide +kernel
  have h72 : lowerFourRow 72 = 732894 := by decide +kernel
  have h73 : lowerFourRow 73 = 700788 := by decide +kernel
  have h74 : lowerFourRow 74 = 698204 := by decide +kernel
  have h75 : lowerFourRow 75 = 634625 := by decide +kernel
  have h76 : lowerFourRow 76 = 570867 := by decide +kernel
  have h77 : lowerFourRow 77 = 503946 := by decide +kernel
  have h78 : lowerFourRow 78 = 421323 := by decide +kernel
  have h79 : lowerFourRow 79 = 307792 := by decide +kernel
  have h80 : lowerFourRow 80 = 280961 := by decide +kernel
  have h81 : lowerFourRow 81 = 270296 := by decide +kernel
  have h82 : lowerFourRow 82 = 257917 := by decide +kernel
  have h83 : lowerFourRow 83 = 145992 := by decide +kernel
  have h84 : lowerFourRow 84 = 65255 := by decide +kernel
  have h85 : lowerFourRow 85 = 16408 := by decide +kernel
  have h86 : lowerFourRow 86 = 0 := by decide +kernel
  have h87 : lowerFourRow 87 = 0 := by decide +kernel
  have h88 : lowerFourRow 88 = 0 := by decide +kernel
  have h89 : lowerFourRow 89 = 0 := by decide +kernel
  have h90 : lowerFourRow 90 = 0 := by decide +kernel
  have h91 : lowerFourRow 91 = 0 := by decide +kernel
  have h92 : lowerFourRow 92 = 0 := by decide +kernel
  have h93 : lowerFourRow 93 = 0 := by decide +kernel
  have h94 : lowerFourRow 94 = 0 := by decide +kernel
  have h95 : lowerFourRow 95 = 0 := by decide +kernel
  have h96 : lowerFourRow 96 = 0 := by decide +kernel
  have h97 : lowerFourRow 97 = 0 := by decide +kernel
  have h98 : lowerFourRow 98 = 0 := by decide +kernel
  have h99 : lowerFourRow 99 = 0 := by decide +kernel
  have h100 : lowerFourRow 100 = 0 := by decide +kernel
  have h101 : lowerFourRow 101 = 0 := by decide +kernel
  have h102 : lowerFourRow 102 = 0 := by decide +kernel
  have h103 : lowerFourRow 103 = 0 := by decide +kernel
  have h104 : lowerFourRow 104 = 0 := by decide +kernel
  have h105 : lowerFourRow 105 = 0 := by decide +kernel
  have h106 : lowerFourRow 106 = 0 := by decide +kernel
  have h107 : lowerFourRow 107 = 0 := by decide +kernel
  have h108 : lowerFourRow 108 = 0 := by decide +kernel
  have h109 : lowerFourRow 109 = 0 := by decide +kernel
  have h110 : lowerFourRow 110 = 0 := by decide +kernel
  have h111 : lowerFourRow 111 = 0 := by decide +kernel
  have h112 : lowerFourRow 112 = 0 := by decide +kernel
  have h113 : lowerFourRow 113 = 0 := by decide +kernel
  have h114 : lowerFourRow 114 = 0 := by decide +kernel
  have h115 : lowerFourRow 115 = 0 := by decide +kernel
  have h116 : lowerFourRow 116 = 0 := by decide +kernel
  have h117 : lowerFourRow 117 = 0 := by decide +kernel
  have h118 : lowerFourRow 118 = 0 := by decide +kernel
  have h119 : lowerFourRow 119 = 0 := by decide +kernel
  have h120 : lowerFourRow 120 = 0 := by decide +kernel
  have h121 : lowerFourRow 121 = 0 := by decide +kernel
  have h122 : lowerFourRow 122 = 0 := by decide +kernel
  have h123 : lowerFourRow 123 = 0 := by decide +kernel
  have h124 : lowerFourRow 124 = 0 := by decide +kernel
  have h125 : lowerFourRow 125 = 0 := by decide +kernel
  have h126 : lowerFourRow 126 = 0 := by decide +kernel
  have h127 : lowerFourRow 127 = 0 := by decide +kernel
  have hrows : ∀ i ∈ Finset.range 128, lowerFourRow i = lowerFourRowTotal i := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
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
    · exact h64
    · exact h65
    · exact h66
    · exact h67
    · exact h68
    · exact h69
    · exact h70
    · exact h71
    · exact h72
    · exact h73
    · exact h74
    · exact h75
    · exact h76
    · exact h77
    · exact h78
    · exact h79
    · exact h80
    · exact h81
    · exact h82
    · exact h83
    · exact h84
    · exact h85
    · exact h86
    · exact h87
    · exact h88
    · exact h89
    · exact h90
    · exact h91
    · exact h92
    · exact h93
    · exact h94
    · exact h95
    · exact h96
    · exact h97
    · exact h98
    · exact h99
    · exact h100
    · exact h101
    · exact h102
    · exact h103
    · exact h104
    · exact h105
    · exact h106
    · exact h107
    · exact h108
    · exact h109
    · exact h110
    · exact h111
    · exact h112
    · exact h113
    · exact h114
    · exact h115
    · exact h116
    · exact h117
    · exact h118
    · exact h119
    · exact h120
    · exact h121
    · exact h122
    · exact h123
    · exact h124
    · exact h125
    · exact h126
    · exact h127
  calc
    lowerFourTotal = ∑ i ∈ Finset.range 128, lowerFourRowTotal i :=
      Finset.sum_congr rfl hrows
    _ = 51034109 := by decide +kernel

/-- Page 51. The conservative four-prime discarded integral is below one divided by 4000.
CONDITIONAL on the defining Buchstab equations and zero extension.
The finite certificate, whole-cell geometry and integral comparison are proved above. -/
theorem lower_four_discard_small {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) :
    lowerFourDeletedIntegral ω ε < 1/4000 := by
  have hI := lower_four_integral_bound hω hz hε hε'
  have he : (lowerFourTotal:ℝ)*(587/400000:ℝ)^4 = (51034109:ℝ)*(587/400000:ℝ)^4 :=
    congrArg (fun n : ℕ => (n:ℝ)*(587/400000:ℝ)^4) lower_four_total
  have hb : (51034109:ℝ)*(587/400000:ℝ)^4 < 1/4000 := by norm_num
  exact hI.trans_lt (lt_of_eq_of_lt he hb)


/-- Page 51. The remaining numeric E2 input alone gives the lower density margin
once the certified four-prime discard is subtracted. This is CONDITIONAL on
that E2 bound and the actual lower density comparison. -/
theorem lower_density_of_e2_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε e2 v0 : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8)
    (h2 : e2 ≤ 3799/4000) (hv : 1-e2-lowerFourDeletedIntegral ω ε ≤ v0) :
    0.05 < v0 := by
  have h4 := lower_four_discard_small hω hz hε hε'
  linarith

/-- Page 51. The set `E₂`: `c₁ ≤ β₂ ≤ β₁ ≤ 1/2`, `β₁ + 2β₂ ≤ 1`, off `D ∪ Q₁ ∪ Q₂ ∪ P₁ ∪ P₂ ∪ R`.
`upperPairRegion` is `P₁ ∪ P₂ ∪ R`. Page 50 prints `4β₁ + 5β₂ ≤ 2 + c₁` for `Q₂`, while its proof
needs `2 + θ₂ - ε`, the smaller set, used here. Both give the same integral to six places.
This paper Prop requires Claude review before merge. -/
def lowerTwoDiscarded (ε a b : ℝ) : Prop :=
  (1+7*(2*(1/16-1/10^5)))/15-ε ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ a+2*b ≤ 1 ∧
    ¬(a+2*b ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε ∨
      (4*a+7*b ≤ 2+2*(1/16-1/10^5)-ε ∧
        1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ a+b) ∨
      (b ≤ (36*(2*(1/16-1/10^5))-2)/11-ε ∧ 4*a+5*b ≤ 2+2*(1/16-1/10^5)-ε ∧
        1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ a+b) ∨
      upperPairRegion ε a b)

/-- Page 51. The usual Buchstab integrand of the sum over `p₁p₂n₃` deleted on `E₂`. -/
noncomputable def lowerTwoDeletedIntegrand (ω : ℝ → ℝ) (ε a b : ℝ) : ℝ :=
  if lowerTwoDiscarded ε a b then ω ((1-a-b)/b)/(a*b^2) else 0

/-- Page 51. The integral over `E₂` subtracted from 1 in `v₀`. The box contains `E₂` for small `ε`. -/
noncomputable def lowerTwoDeletedIntegral (ω : ℝ → ℝ) (ε : ℝ) : ℝ :=
  ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), lowerTwoDeletedIntegrand ω ε a b

/-- Page 51. The deleted pair lies in a fixed positive box. -/
theorem lower_two_domain_box {ε a b : ℝ} (hε : ε ≤ 1/10^8)
    (h : lowerTwoDiscarded ε a b) :
    (12499/100000:ℝ) ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ a+2*b ≤ 1 := by
  obtain ⟨hc, hba, ha, hs, _⟩ := h
  exact ⟨by linarith, hba, ha, hs⟩

/-- Page 51. Integer numerators of the 4096-cell E2 grid, denominator 409600000. -/
def lowerTwoGridPoint (i : ℕ) : ℕ := 51195904 + 37501*i
/-- Page 51. Sufficient whole-cell tests for D and the two repaired Q regions. -/
def lowerTwoGridDQ (a A b B : ℕ) : Bool := decide (
  150000000*(A+2*B) ≤ 84373897*409600000 ∨
  (100000000*(4*A+7*B) ≤ 212497999*409600000 ∧
    150004807*409600000 ≤ 400000000*(a+b)) ∨
  (1100000000*B ≤ 249927989*409600000 ∧
    100000000*(4*A+5*B) ≤ 212497999*409600000 ∧
    105001763*409600000 ≤ 240000000*(a+b)))
/-- Page 48. Sufficient whole-cell tests for R, P1 and P2 on the E2 grid. -/
def lowerTwoGridRP (a A b B : ℕ) : Bool := decide (
  B ≤ a ∧ 2*A ≤ 409600000 ∧ 1100000000*B ≤ 249927989*409600000 ∧
    ((100000000*(2*B) ≤ 100000000*a+12497999*409600000 ∧
        1100000000*A ≤ 249927989*409600000) ∨
      (187502001*409600000 ≤ 100000000*(4*a+3*b) ∧
        100000000*(4*A+3*B) ≤ 212497999*409600000) ∨
      (187502001*409600000 ≤ 100000000*(4*a+b) ∧
        100000000*(4*A+B) ≤ 212497999*409600000)))
/-- Page 51. Upward integer division of a rational tangent cell envelope, scale 10000. -/
def lowerTwoTangentWeight (p cap a b : ℕ) : ℕ :=
  let r := 409600000-a-b
  let num := 10000000*r-(10000000-p*cap)*b
  (10000*409600000^3*num + p*1000000*r*a*b*b-1)/(p*1000000*r*a*b*b)
/-- Page 51. Integer ceiling of the three basic Buchstab envelopes. -/
def lowerTwoBaseWeight (a A b B : ℕ) : ℕ :=
  let d := a*b*b
  let ceil := fun n den : ℕ => (n+den-1)/den
  if A+B < 409600000 then
    min (ceil (10000*409600000^3) d)
      (max (ceil (10000*567144*409600000^3) (1000000*d))
        (ceil (10000*B*409600000^3) ((409600000-A-B)*d)))
  else ceil (10000*409600000^3) d
/-- Page 51. Whole-cell integer majorant for the E2 Buchstab integrand, scale 10000. -/
def lowerTwoGridWeight (i j : ℕ) : ℕ :=
  let a := lowerTwoGridPoint i
  let b := lowerTwoGridPoint j
  let A := a+37501
  let B := b+37501
  if A < b ∨ 409600000 < a+2*b then 0
  else if lowerTwoGridDQ a A b B || lowerTwoGridRP a A b B then 0
  else
    let base := lowerTwoBaseWeight a A b B
    if 3*B ≤ 409600000-A then
      min base (min (lowerTwoTangentWeight 10 0 a b)
        (min (lowerTwoTangentWeight 11 95311 a b)
        (min (lowerTwoTangentWeight 12 182322 a b)
        (min (lowerTwoTangentWeight 13 262365 a b)
        (min (lowerTwoTangentWeight 14 336473 a b)
        (min (lowerTwoTangentWeight 15 405466 a b)
          (lowerTwoTangentWeight 16 470004 a b)))))))
    else base

/-- Page 51. The real endpoints of the 4096-cell E2 grid. -/
noncomputable def lowerTwoGridReal (i : ℕ) : ℝ := (lowerTwoGridPoint i:ℝ)/409600000

/-- Page 51. The full integer E2 cell sum. Its scale is 10000. -/
def lowerTwoGridTotal : ℕ :=
  ∑ i ∈ Finset.range 4096, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight i j

/-- Page 51. Eight-row blocks of the exact E2 integer sum. -/
def lowerTwoGridBlock (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (8*k+i) j


set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Page 51. The actual E2 integral is bounded by the explicit whole-cell sum.
This is the complete geometric and integral bridge, without the remaining arithmetic certificate. -/
theorem lower_two_integral_grid_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) :
    lowerTwoDeletedIntegral ω ε ≤
      (lowerTwoGridTotal:ℝ)*(37501/409600000:ℝ)^2/10000 := by
  /- Page 51. The discarded integrand vanishes on either lower cutoff strip. -/
  have lower_two_cutoff_zero (ω : ℝ → ℝ) {ε a b : ℝ} (hε : ε ≤ 1/10^8)
      (h : a ≤ 12499/100000 ∨ b ≤ 12499/100000) :
      lowerTwoDeletedIntegrand ω ε a b = 0 := by
    unfold lowerTwoDeletedIntegrand
    split_ifs with hd
    · obtain ⟨hc,hba,_,_,_⟩ := hd
      rcases h with h | h <;> linarith
    · rfl
  /- Page 51. Removing zero cutoff strips leaves the actual E2 integral unchanged. -/
  have lower_two_integral_trimmed (ω : ℝ → ℝ) {ε : ℝ} (hε : ε ≤ 1/10^8) :
      lowerTwoDeletedIntegral ω ε =
        ∫ a in (12499/100000:ℝ)..(1/2:ℝ),
          ∫ b in (12499/100000:ℝ)..(1/2:ℝ), lowerTwoDeletedIntegrand ω ε a b := by
    have hi (a : ℝ) :
        (∫ b in (1/10:ℝ)..(1/2:ℝ), lowerTwoDeletedIntegrand ω ε a b) =
          ∫ b in (12499/100000:ℝ)..(1/2:ℝ), lowerTwoDeletedIntegrand ω ε a b := by
      rw [intervalIntegral.integral_of_le (by norm_num : (1/10:ℝ) ≤ 1/2),
        intervalIntegral.integral_of_le (by norm_num : (12499/100000:ℝ) ≤ 1/2)]
      apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
        (Set.Ioc_subset_Ioc (by norm_num) le_rfl)
      intro b hb
      have hc : b ≤ 12499/100000 := by
        by_contra hn
        exact hb.2 ⟨lt_of_not_ge hn,hb.1.2⟩
      exact lower_two_cutoff_zero ω hε (Or.inr hc)
    unfold lowerTwoDeletedIntegral
    simp_rw [hi]
    rw [intervalIntegral.integral_of_le (by norm_num : (1/10:ℝ) ≤ 1/2),
      intervalIntegral.integral_of_le (by norm_num : (12499/100000:ℝ) ≤ 1/2)]
    apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      (Set.Ioc_subset_Ioc (by norm_num) le_rfl)
    intro a ha
    have hc : a ≤ 12499/100000 := by
      by_contra hn
      exact ha.2 ⟨lt_of_not_ge hn,ha.1.2⟩
    have hz : (fun b => lowerTwoDeletedIntegrand ω ε a b) = (fun _ => (0:ℝ)) :=
      funext (fun b => lower_two_cutoff_zero ω hε (Or.inl hc))
    simp_rw [hz]
    simp

  /- Page 51. A whole cell covered by D or the two Q regions has no deleted pair. -/
  have lower_two_covered_real {ε a A b B x y : ℝ}
      (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8)
      (hx : x ∈ Set.Icc a A) (hy : y ∈ Set.Icc b B)
      (hc : A+2*B ≤ 84373897/150000000 ∨
        (4*A+7*B ≤ 212497999/100000000 ∧ 150004807/400000000 ≤ a+b) ∨
        (B ≤ 249927989/1100000000 ∧ 4*A+5*B ≤ 212497999/100000000 ∧
          105001763/240000000 ≤ a+b)) :
      ¬ lowerTwoDiscarded ε x y := by
    intro hd
    obtain ⟨_, _, _, _, hn⟩ := hd
    apply hn
    rcases hc with hD | hQ1 | hQ2
    · left
      linarith [hx.2, hy.2]
    · right; left
      constructor <;> linarith [hx.1,hx.2,hy.1,hy.2,hQ1.1,hQ1.2]
    · right; right; left
      refine ⟨?_, ?_, ?_⟩ <;> linarith [hx.1,hx.2,hy.1,hy.2,hQ2.1,hQ2.2.1,hQ2.2.2]

  /- Page 48. A whole E2 cell covered by R or either P region has no deleted pair. -/
  have lower_two_rp_real {ε a A b B x y : ℝ}
      (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8)
      (hx : x ∈ Set.Icc a A) (hy : y ∈ Set.Icc b B)
      (hc : B ≤ a ∧ 2*A ≤ 1 ∧ B ≤ 249927989/1100000000 ∧
        ((2*B ≤ a+12497999/100000000 ∧ A ≤ 249927989/1100000000) ∨
          (187502001/100000000 ≤ 4*a+3*b ∧ 4*A+3*B ≤ 212497999/100000000) ∨
          (187502001/100000000 ≤ 4*a+b ∧ 4*A+B ≤ 212497999/100000000))) :
      ¬ lowerTwoDiscarded ε x y := by
    intro hd
    obtain ⟨hyc, _, _, _, hn⟩ := hd
    apply hn
    right; right; right
    refine ⟨?_, ?_, hyc, ?_, ?_⟩
    · linarith [hc.1,hx.1,hy.2]
    · linarith [hc.2.1,hx.2]
    · linarith [hc.2.2.1,hy.2]
    rcases hc.2.2.2 with hr | hp | hp
    · left
      constructor <;> linarith [hr.1,hr.2,hx.1,hx.2,hy.2]
    · right; left
      rw [abs_le]
      constructor <;> linarith [hp.1,hp.2,hx.1,hx.2,hy.1,hy.2]
    · right; right
      rw [abs_le]
      constructor <;> linarith [hp.1,hp.2,hx.1,hx.2,hy.1,hy.2]

  /- Page 51. Two-variable Buchstab envelopes on a positive rational cell. -/
  have lower_two_cell_envelope {ω : ℝ → ℝ}
      (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
      (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
      {a A b B x y : ℝ} (ha : 0 < a) (hb : 0 < b)
      (hr : 0 < 1-A-B) (hx : x ∈ Set.Icc a A) (hy : y ∈ Set.Icc b B) :
      ω ((1-x-y)/y)/(x*y^2) ≤
        min (1/(a*b^2))
          (max ((567144/1000000:ℝ)/(a*b^2)) ((B/(1-A-B))/(a*b^2))) := by
    let u := (1-x-y)/y
    have hx0 : 0 < x := ha.trans_le hx.1
    have hy0 : 0 < y := hb.trans_le hy.1
    have hB0 : 0 < B := hy0.trans_le hy.2
    have hd : 0 < a*b^2 := by positivity
    have hd' : 0 < x*y^2 := by positivity
    have hdd : a*b^2 ≤ x*y^2 := by gcongr <;> linarith [hx.1,hy.1]
    have h1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz u
    refine le_min ((div_le_div_of_nonneg_right h1 hd'.le).trans
      (div_le_div_of_nonneg_left zero_le_one hd hdd)) ?_
    by_cases hu : 2 ≤ u
    · apply le_trans _ (le_max_left _ _)
      exact (div_le_div_of_nonneg_right
        (LeanLab.ChenDoubleSieve.Wu04Buchstab.buchstab_le_567144 hω hu) hd'.le).trans
        (div_le_div_of_nonneg_left (by norm_num) hd hdd)
    · by_cases hu1 : u < 1
      · rw [show ω u = 0 from hz u hu1, zero_div]
        exact le_trans (by positivity) (le_max_left _ _)
      · have huu : 1 ≤ u := le_of_not_gt hu1
        have hw := hω.2.1 u huu (le_of_not_ge hu)
        have hl : (1-A-B)/B ≤ u := by
          apply (div_le_div_of_nonneg_left hr.le hy0 hy.2).trans
          apply div_le_div_of_nonneg_right _ hy0.le
          linarith [hx.2,hy.2]
        have hrec : 1/u ≤ B/(1-A-B) := by
          simpa only [one_div_div] using one_div_le_one_div_of_le (div_pos hr hB0) hl
        apply le_trans _ (le_max_right _ _)
        exact (div_le_div_of_nonneg_right (hw.le.trans hrec) hd'.le).trans
          (div_le_div_of_nonneg_left (by positivity) hd hdd)

  /- Page 51. A two-variable cell above argument two has every certified tangent bound. -/
  have lower_two_tangent_envelope {ω : ℝ → ℝ}
      (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
      (i : Fin 7) {a A b B x y : ℝ}
      (ha : 0 < a) (hb : 0 < b) (hx : x ∈ Set.Icc a A)
      (hy : y ∈ Set.Icc b B) (hu : 2*B ≤ 1-A-B) :
      ω ((1-x-y)/y)/(x*y^2) ≤
        (1/buchstabLogNode i+(buchstabLogCap i-1/buchstabLogNode i)/((1-a-b)/b))/(a*b^2) := by
    have hx0 : 0 < x := ha.trans_le hx.1
    have hy0 : 0 < y := hb.trans_le hy.1
    have hB0 : 0 < B := hy0.trans_le hy.2
    have hlow : 2 ≤ (1-x-y)/y := by
      apply (le_div_iff₀ hy0).2
      linarith [hx.2, hy.2]
    have hnum : 0 ≤ 1-a-b := by linarith [hx.1, hx.2,hy.1,hy.2]
    have hupper : (1-x-y)/y ≤ (1-a-b)/b := by
      apply (div_le_div_of_nonneg_right
        (show 1-x-y ≤ 1-a-b by linarith [hx.1,hy.1]) hy0.le).trans
      exact div_le_div_of_nonneg_left hnum hb hy.1
    have ht := buchstab_tangent_cell_upper hω i hlow hupper
    have hcap0 : 0 ≤ 1/buchstabLogNode i+
        (buchstabLogCap i-1/buchstabLogNode i)/((1-a-b)/b) :=
      (buchstab_nonneg hω (by linarith : 1 ≤ (1-x-y)/y)).trans ht
    have hd : 0 < a*b^2 := by positivity
    have hdd : a*b^2 ≤ x*y^2 := by gcongr <;> linarith [hx.1,hy.1]
    exact (div_le_div_of_nonneg_right ht (by positivity : 0 ≤ x*y^2)).trans
      (div_le_div_of_nonneg_left hcap0 hd hdd)

  /- Page 51. Clearing denominators connects the integer tangent certificate to its real envelope. -/
  have lower_two_tangent_integer {a b p cap : ℕ}
      (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hc : p*cap ≤ 10000000)
      (hr : a+3*b ≤ 409600000) :
      (10/(p:ℝ)+((cap:ℝ)/1000000-10/p)/
        ((1-(a:ℝ)/409600000-(b:ℝ)/409600000)/((b:ℝ)/409600000))) /
        (((a:ℝ)/409600000)*((b:ℝ)/409600000)^2) ≤
        (lowerTwoTangentWeight p cap a b:ℝ)/10000 := by
    have har : (0:ℝ) < a := by exact_mod_cast ha
    have hbr : (0:ℝ) < b := by exact_mod_cast hb
    have hpr : (0:ℝ) < p := by exact_mod_cast hp
    have hcr : (p:ℝ)*cap ≤ 10000000 := by exact_mod_cast hc
    have hrr : (a:ℝ)+3*b ≤ 409600000 := by exact_mod_cast hr
    have hab : a+b ≤ 409600000 := by omega
    have hR : 0 < 409600000-a-b := by omega
    have hRr : ((409600000-a-b:ℕ):ℝ) = 409600000-a-b := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      norm_num
    have hpc : ((10000000-p*cap:ℕ):ℝ) = 10000000-(p:ℝ)*cap := by
      rw [Nat.cast_sub hc]
      norm_num
    have hn : (10000000-p*cap)*b ≤ 10000000*(409600000-a-b) := by
      calc
        (10000000-p*cap)*b ≤ 10000000*b := Nat.mul_le_mul_right b (Nat.sub_le _ _)
        _ ≤ 10000000*(409600000-a-b) := Nat.mul_le_mul_left _ (by omega)
    have hncast : ((10000000*(409600000-a-b)-(10000000-p*cap)*b:ℕ):ℝ) =
        10000000*(409600000-(a:ℝ)-b)-(10000000-(p:ℝ)*cap)*b := by
      rw [Nat.cast_sub hn]
      push_cast
      rw [hRr, hpc]
    have hd : 0 < p*1000000*(409600000-a-b)*a*b*b := by positivity
    have hq := upper_grid_ceil_bound (n := 10000*409600000^3*
      (10000000*(409600000-a-b)-(10000000-p*cap)*b)) hd
    have heq : lowerTwoTangentWeight p cap a b =
        upperGridCeil (10000*409600000^3*(10000000*(409600000-a-b)-(10000000-p*cap)*b))
          (p*1000000*(409600000-a-b)*a*b*b) := rfl
    rw [← heq] at hq
    have he :
        (10/(p:ℝ)+((cap:ℝ)/1000000-10/p)/
          ((1-(a:ℝ)/409600000-(b:ℝ)/409600000)/((b:ℝ)/409600000))) /
          (((a:ℝ)/409600000)*((b:ℝ)/409600000)^2) =
        ((10000*409600000^3*(10000000*(409600000-a-b)-(10000000-p*cap)*b):ℕ):ℝ)/
          ((p*1000000*(409600000-a-b)*a*b*b:ℕ):ℝ)/10000 := by
      push_cast
      rw [hncast, hRr]
      have hr0 : (409600000:ℝ)-a-b ≠ 0 := by linarith
      field_simp
      <;> ring
    rw [he]
    exact div_le_div_of_nonneg_right hq (by norm_num)

  /- Page 51. Integer ceilings bound the two-variable basic Buchstab envelope. -/
  have lower_two_base_integer {ω : ℝ → ℝ}
      (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
      (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
      {a A b B : ℕ} {x y : ℝ}
      (ha : 0 < a) (hb : 0 < b)
      (hx : x ∈ Set.Icc ((a:ℝ)/409600000) ((A:ℝ)/409600000))
      (hy : y ∈ Set.Icc ((b:ℝ)/409600000) ((B:ℝ)/409600000)) :
      ω ((1-x-y)/y)/(x*y^2) ≤ (lowerTwoBaseWeight a A b B:ℝ)/10000 := by
    have har : (0:ℝ) < a := by exact_mod_cast ha
    have hbr : (0:ℝ) < b := by exact_mod_cast hb
    have hx0 : 0 < x := (div_pos har (by norm_num)).trans_le hx.1
    have hy0 : 0 < y := (div_pos hbr (by norm_num)).trans_le hy.1
    have hdd : ((a:ℝ)/409600000)*((b:ℝ)/409600000)^2 ≤ x*y^2 := by
      gcongr <;> linarith [hx.1,hy.1]
    have hd : 0 < a*b*b := by positivity
    have hc0 := upper_grid_ceil_bound (n := 10000*409600000^3) hd
    have he0 : 1/(((a:ℝ)/409600000)*((b:ℝ)/409600000)^2) =
        ((10000*409600000^3:ℕ):ℝ)/((a*b*b:ℕ):ℝ)/10000 := by
      push_cast
      field_simp
      <;> ring
    have h0 : 1/(((a:ℝ)/409600000)*((b:ℝ)/409600000)^2) ≤
        (upperGridCeil (10000*409600000^3) (a*b*b):ℝ)/10000 := by
      rw [he0]
      exact div_le_div_of_nonneg_right hc0 (by norm_num)
    unfold lowerTwoBaseWeight
    split_ifs with hr
    · have hrr : (A:ℝ)+B < 409600000 := by exact_mod_cast hr
      have hR : ((409600000-A-B:ℕ):ℝ) = 409600000-A-B := by
        rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
        norm_num
      have hr0 : 0 < 409600000-A-B := by omega
      have hc1 := upper_grid_ceil_bound (n := 10000*567144*409600000^3)
        (show 0 < 1000000*(a*b*b) by positivity)
      have hc2 := upper_grid_ceil_bound (n := 10000*B*409600000^3)
        (show 0 < (409600000-A-B)*(a*b*b) by positivity)
      have he1 : ((567144/1000000:ℝ)/(((a:ℝ)/409600000)*((b:ℝ)/409600000)^2)) =
          ((10000*567144*409600000^3:ℕ):ℝ)/((1000000*(a*b*b):ℕ):ℝ)/10000 := by
        push_cast
        field_simp
        <;> ring
      have he2 : (((B:ℝ)/409600000/(1-(A:ℝ)/409600000-(B:ℝ)/409600000)) /
          (((a:ℝ)/409600000)*((b:ℝ)/409600000)^2)) =
          ((10000*B*409600000^3:ℕ):ℝ)/(((409600000-A-B)*(a*b*b):ℕ):ℝ)/10000 := by
        push_cast
        rw [hR]
        have hr' : (409600000:ℝ)-A-B ≠ 0 := by linarith
        field_simp
        <;> ring
      have h1 := div_le_div_of_nonneg_right hc1 (by norm_num : (0:ℝ) ≤ 10000)
      have h2 := div_le_div_of_nonneg_right hc2 (by norm_num : (0:ℝ) ≤ 10000)
      rw [← he1] at h1
      rw [← he2] at h2
      have he := lower_two_cell_envelope hω hz (div_pos har (by norm_num))
        (div_pos hbr (by norm_num)) (by linarith : 0 < 1-(A:ℝ)/409600000-(B:ℝ)/409600000) hx hy
      apply he.trans
      push_cast
      rw [← min_div_div_right (by norm_num : (0:ℝ) ≤ 10000),
        ← max_div_div_right (by norm_num : (0:ℝ) ≤ 10000)]
      exact min_le_min h0 (max_le_max h1 h2)
    · have hw := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz ((1-x-y)/y)
      exact ((div_le_div_of_nonneg_right hw (by positivity : 0 ≤ x*y^2)).trans
        (div_le_div_of_nonneg_left zero_le_one (by positivity) hdd)).trans h0

  /- Pages 48, 50 and 51. The integer whole-cell tests exclude every deleted pair in the cell. -/
  have lower_two_grid_covered_sound {ε x y : ℝ} {a A b B : ℕ}
      (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8)
      (hx : x ∈ Set.Icc ((a:ℝ)/409600000) ((A:ℝ)/409600000))
      (hy : y ∈ Set.Icc ((b:ℝ)/409600000) ((B:ℝ)/409600000))
      (ht : lowerTwoGridDQ a A b B || lowerTwoGridRP a A b B = true) :
      ¬ lowerTwoDiscarded ε x y := by
    simp only [Bool.or_eq_true] at ht
    rcases ht with hd | hr
    · simp only [lowerTwoGridDQ, decide_eq_true_eq] at hd
      have hh :
          150000000*((A:ℝ)+2*B) ≤ 84373897*409600000 ∨
          (100000000*(4*(A:ℝ)+7*B) ≤ 212497999*409600000 ∧
            150004807*409600000 ≤ 400000000*((a:ℝ)+b)) ∨
          (1100000000*(B:ℝ) ≤ 249927989*409600000 ∧
            100000000*(4*(A:ℝ)+5*B) ≤ 212497999*409600000 ∧
            105001763*409600000 ≤ 240000000*((a:ℝ)+b)) := by exact_mod_cast hd
      apply lower_two_covered_real hε hε' hx hy
      rcases hh with hh | hh | hh
      · left; linarith
      · right; left; constructor <;> linarith [hh.1,hh.2]
      · right; right; refine ⟨?_,?_,?_⟩ <;> linarith [hh.1,hh.2.1,hh.2.2]
    · simp only [lowerTwoGridRP, decide_eq_true_eq] at hr
      have hh : (B:ℝ) ≤ a ∧ 2*(A:ℝ) ≤ 409600000 ∧
          1100000000*(B:ℝ) ≤ 249927989*409600000 ∧
          ((100000000*(2*(B:ℝ)) ≤ 100000000*(a:ℝ)+12497999*409600000 ∧
              1100000000*(A:ℝ) ≤ 249927989*409600000) ∨
            (187502001*409600000 ≤ 100000000*(4*(a:ℝ)+3*b) ∧
              100000000*(4*(A:ℝ)+3*B) ≤ 212497999*409600000) ∨
            (187502001*409600000 ≤ 100000000*(4*(a:ℝ)+b) ∧
              100000000*(4*(A:ℝ)+B) ≤ 212497999*409600000)) := by exact_mod_cast hr
      apply lower_two_rp_real hε hε' hx hy
      refine ⟨?_,?_,?_,?_⟩
      · linarith [hh.1]
      · linarith [hh.2.1]
      · linarith [hh.2.2.1]
      rcases hh.2.2.2 with hh | hh | hh
      · left; constructor <;> linarith [hh.1,hh.2]
      · right; left; constructor <;> linarith [hh.1,hh.2]
      · right; right; constructor <;> linarith [hh.1,hh.2]

  /- Page 51. The rational integer majorant bounds the actual deleted integrand on every cell. -/
  have lower_two_grid_cell_bound {ω : ℝ → ℝ}
      (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
      (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
      {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8)
      (i j : ℕ) {x y : ℝ}
      (hx : x ∈ Set.Icc ((lowerTwoGridPoint i:ℝ)/409600000)
        (((lowerTwoGridPoint i+37501:ℕ):ℝ)/409600000))
      (hy : y ∈ Set.Icc ((lowerTwoGridPoint j:ℝ)/409600000)
        (((lowerTwoGridPoint j+37501:ℕ):ℝ)/409600000)) :
      lowerTwoDeletedIntegrand ω ε x y ≤ (lowerTwoGridWeight i j:ℝ)/10000 := by
    let a := lowerTwoGridPoint i
    let b := lowerTwoGridPoint j
    let A := a+37501
    let B := b+37501
    have ha : 0 < a := by dsimp [a,lowerTwoGridPoint]; omega
    have hb : 0 < b := by dsimp [b,lowerTwoGridPoint]; omega
    change x ∈ Set.Icc ((a:ℝ)/409600000) ((A:ℝ)/409600000) at hx
    change y ∈ Set.Icc ((b:ℝ)/409600000) ((B:ℝ)/409600000) at hy
    unfold lowerTwoDeletedIntegrand
    split_ifs with hd
    · have hs := lower_two_domain_box hε' hd
      change ω ((1-x-y)/y)/(x*y^2) ≤
        ((if A < b ∨ 409600000 < a+2*b then 0
        else if lowerTwoGridDQ a A b B || lowerTwoGridRP a A b B then 0
        else if 3*B ≤ 409600000-A then
          min (lowerTwoBaseWeight a A b B) (min (lowerTwoTangentWeight 10 0 a b)
            (min (lowerTwoTangentWeight 11 95311 a b)
            (min (lowerTwoTangentWeight 12 182322 a b)
            (min (lowerTwoTangentWeight 13 262365 a b)
            (min (lowerTwoTangentWeight 14 336473 a b)
            (min (lowerTwoTangentWeight 15 405466 a b)
              (lowerTwoTangentWeight 16 470004 a b)))))))
        else lowerTwoBaseWeight a A b B : ℕ):ℝ)/10000
      split_ifs with hout hcover htwo
      · exfalso
        rcases hout with hout | hout
        · have hh : (A:ℝ) < b := by exact_mod_cast hout
          linarith [hx.2,hy.1,hs.2.1]
        · have hh : (409600000:ℝ) < a+2*b := by exact_mod_cast hout
          linarith [hx.1,hy.1,hs.2.2.2]
      · exact False.elim (lower_two_grid_covered_sound hε hε' hx hy hcover hd)
      · have hbas := lower_two_base_integer hω hz ha hb hx hy
        have hB0 : 0 < B := by dsimp [B]; omega
        have hAD : A < 409600000 := Nat.sub_pos_iff_lt.mp
          ((Nat.mul_pos (by decide : 0 < 3) hB0).trans_le htwo)
        have hAB : A+3*B ≤ 409600000 := by
          simpa only [Nat.add_comm] using (Nat.le_sub_iff_add_le hAD.le).mp htwo
        have hthree : a+3*b ≤ 409600000 := by dsimp [A,B] at hAB; omega
        have hreal : (a:ℝ)+3*b ≤ 409600000 := by exact_mod_cast hthree
        have hU : 2*((B:ℝ)/409600000) ≤ 1-(A:ℝ)/409600000-(B:ℝ)/409600000 := by
          have hh : (A:ℝ)+3*B ≤ 409600000 := by exact_mod_cast hAB
          linarith
        have ht (k : Fin 7) (p cap : ℕ) (hp : 0 < p) (hc : p*cap ≤ 10000000)
            (hnode : buchstabLogNode k = (p:ℝ)/10)
            (hcap : buchstabLogCap k = (cap:ℝ)/1000000) :
            ω ((1-x-y)/y)/(x*y^2) ≤ (lowerTwoTangentWeight p cap a b:ℝ)/10000 := by
          have hh := lower_two_tangent_envelope hω k
            (show 0 < (a:ℝ)/409600000 by positivity)
            (show 0 < (b:ℝ)/409600000 by positivity) hx hy hU
          have hi := lower_two_tangent_integer ha hb hp hc hthree
          rw [hnode,hcap] at hh
          simp only [one_div_div, one_mul] at hh
          exact hh.trans hi
        apply (le_div_iff₀ (by norm_num : (0:ℝ) < 10000)).2
        push_cast
        refine le_min ((le_div_iff₀ (by norm_num : (0:ℝ) < 10000)).1 hbas) ?_
        repeat' apply le_min
        all_goals apply (le_div_iff₀ (by norm_num : (0:ℝ) < 10000)).1
        · exact ht 0 10 0 (by norm_num) (by norm_num) (by norm_num [buchstabLogNode]) (by norm_num [buchstabLogCap])
        · exact ht 1 11 95311 (by norm_num) (by norm_num) (by norm_num [buchstabLogNode]) (by norm_num [buchstabLogCap])
        · exact ht 2 12 182322 (by norm_num) (by norm_num) (by norm_num [buchstabLogNode]) (by norm_num [buchstabLogCap])
        · exact ht 3 13 262365 (by norm_num) (by norm_num) (by norm_num [buchstabLogNode]) (by norm_num [buchstabLogCap])
        · exact ht 4 14 336473 (by norm_num) (by norm_num) (by norm_num [buchstabLogNode]) (by norm_num [buchstabLogCap])
        · exact ht 5 15 405466 (by norm_num) (by norm_num) (by norm_num [buchstabLogNode]) (by norm_num [buchstabLogCap])
        · exact ht 6 16 470004 (by norm_num) (by norm_num) (by norm_num [buchstabLogNode]) (by norm_num [buchstabLogCap])
      · exact lower_two_base_integer hω hz ha hb hx hy
    · positivity

  /- Page 51. A nonnegative cell majorant bounds the totalized double integral. -/
  have lower_two_integral_of_cells (p : ℕ → ℝ) (n : ℕ)
      (f : ℝ → ℝ → ℝ) (w : ℕ → ℕ → ℝ)
      (hp : Monotone p) (hw : ∀ i < n, ∀ j < n, 0 ≤ w i j)
      (hb : ∀ i < n, ∀ j < n, ∀ a ∈ Set.Icc (p i) (p (i+1)),
        ∀ b ∈ Set.Icc (p j) (p (j+1)), f a b ≤ w i j) :
      (∫ a in p 0..p n, ∫ b in p 0..p n, f a b) ≤
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          (p (i+1)-p i)*(p (j+1)-p j)*w i j := by
    have hr (i : ℕ) (hi : i < n) (a : ℝ) (ha : a ∈ Set.Icc (p i) (p (i+1))) :=
      integral_le_nonnegative_panel_sum p n (f a) (w i) hp (hw i hi)
        (fun j hj b hb' => hb i hi j hj a ha b hb')
    have hn (i : ℕ) (hi : i < n) :
        0 ≤ ∑ j ∈ Finset.range n, (p (j+1)-p j)*w i j := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (sub_nonneg.mpr (hp (by omega))) (hw i hi j (Finset.mem_range.mp hj))
    have hh := integral_le_nonnegative_panel_sum p n
      (fun a => ∫ b in p 0..p n, f a b)
      (fun i => ∑ j ∈ Finset.range n, (p (j+1)-p j)*w i j) hp hn hr
    simpa only [Finset.mul_sum, mul_assoc] using hh

  /- Page 51. Exact E2 grid width and endpoints. -/
  have lower_two_grid_parameters :
      Monotone lowerTwoGridReal ∧ lowerTwoGridReal 0 = 12499/100000 ∧
        lowerTwoGridReal 4096 = 1/2 ∧
        ∀ i, lowerTwoGridReal (i+1)-lowerTwoGridReal i = 37501/409600000 := by
    refine ⟨?_,by norm_num [lowerTwoGridReal,lowerTwoGridPoint],
      by norm_num [lowerTwoGridReal,lowerTwoGridPoint],?_⟩
    · intro i j hij
      dsimp [lowerTwoGridReal,lowerTwoGridPoint]
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_left 37501 hij) 51195904) (by norm_num)
    · intro i
      simp [lowerTwoGridReal,lowerTwoGridPoint,Nat.cast_add,Nat.cast_mul]
      ring

  /- Page 51. The actual discarded integral is bounded by the explicit finite cell sum. -/
  have lower_two_integral_grid_bound {ω : ℝ → ℝ}
      (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
      (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
      {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) :
      lowerTwoDeletedIntegral ω ε ≤
        (lowerTwoGridTotal:ℝ)*(37501/409600000:ℝ)^2/10000 := by
    have hp := lower_two_grid_parameters
    have hh := lower_two_integral_of_cells lowerTwoGridReal 4096
      (lowerTwoDeletedIntegrand ω ε) (fun i j => (lowerTwoGridWeight i j:ℝ)/10000)
      hp.1 (fun i _ j _ => by positivity)
      (fun i _ j _ x hx y hy => by
        apply lower_two_grid_cell_bound hω hz hε hε' i j
        · simpa [lowerTwoGridReal,lowerTwoGridPoint,Nat.cast_add,Nat.cast_mul,
            Nat.mul_add,Nat.add_assoc] using hx
        · simpa [lowerTwoGridReal,lowerTwoGridPoint,Nat.cast_add,Nat.cast_mul,
            Nat.mul_add,Nat.add_assoc] using hy)
    rw [hp.2.1,hp.2.2.1] at hh
    rw [lower_two_integral_trimmed ω hε']
    apply hh.trans_eq
    simp only [hp.2.2.2,lowerTwoGridTotal,Nat.cast_sum,Finset.sum_mul,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring

  exact lower_two_integral_grid_bound hω hz hε hε'

/-- LEAF, OPEN. Page 51. The exact integer sum for the conservative E2 grid.
The full candidate kernel proof exceeded the bounded shift verification reserve.
The candidate is retained as text and is not proof evidence. This replaces the old E2 leaf. -/
theorem lower_two_grid_total : lowerTwoGridTotal = 1132433915806 := by
  sorry

/-- LEAF, OPEN. Page 51, "A computer calculation yields". The numeric `E₂` input of
`lower_density_of_e2_bound`, a floating point quadrature gives about 0.9389. -/
theorem lower_two_integral_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) :
    lowerTwoDeletedIntegral ω ε ≤ 3799/4000 := by
  have hh := lower_two_integral_grid_bound hω hz hε hε'
  rw [lower_two_grid_total] at hh
  exact hh.trans (by norm_num)

/-- LEAF, OPEN. Pages 43 to 52, the lower short weight b0, with the page 51 formula for its density:
`v₀` is 1 minus the integrals over `E₂` and `E₄`. Since `lowerFourDeletedIntegral` is the
conservative superset of `E₄`, that formula is stated as a lower bound for `v₀`.
Lemmas 29 to 35 supply the moment estimates and 5.18 to 5.23 on page 52 normalize condition iv. -/
theorem lower_short_weight_analytic (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω ∧
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω ∧
      ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
        ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
          1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
          RightConditions ε B v0 b0 ∧
          ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
            ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  sorry

/-- Pages 43 to 52, the lower short weight b0. `0.05 < v0` is now derived from the page 51 density
formula, `lower_two_integral_bound` and the proved `lower_four_discard_small`, by
`lower_density_of_e2_bound`. CONDITIONAL on the two OPEN leaves above. U-1609 dropped the unprinted
`v0 ≤ 1`. -/
theorem lower_short_weight (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
        0.05 < v0 ∧ RightConditions ε B v0 b0 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  obtain ⟨ω, hω, hz, B0, η, hη, hweight⟩ := lower_short_weight_analytic h4 h9
  refine ⟨B0, min η (1/10^8), lt_min hη (by norm_num), ?_⟩
  intro B ε hB hε hεη
  have hεsmall : ε ≤ 1/10^8 :=
    (lt_of_lt_of_le hεη (min_le_right _ _)).le
  obtain ⟨v0, b0, hv0, hright, X, hsandwich⟩ :=
    hweight B ε hB hε (lt_of_lt_of_le hεη (min_le_left _ _))
  exact ⟨v0, b0, lower_density_of_e2_bound hω hz hε.le hεsmall
    (lower_two_integral_bound hω hz hε.le hεsmall) hv0, hright, X, hsandwich⟩

/-- Pages 2 and 3. Two short weights in order on the interval have their densities in the same
order. PROVED in DensityMono1609. This replaces the unprinted `v0 ≤ 1 ≤ v1`. -/
theorem right_density_mono {ε B0 B1 v0 v1 : ℝ} {b0 b1 : ℝ → ℕ → ℝ} (hε : 0 < ε)
    (h0 : RightConditions ε B0 v0 b0) (h1 : RightConditions ε B1 v1 b1)
    (hs : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, b0 x m ≤ b1 x m) : v0 ≤ v1 :=
  DecompC165b.right_density_mono hε h0 h1 hs

/-- LEAF. Page 53, the upper short weight b1. The four-term Buchstab
identity is gm minus hm plus jm minus km. Delete only km terms where
Lemma 33 is unavailable. The printed integral formula gives v1 below 2.2.
Repeat the page 52 normalization. The analytic estimates and certified
Buchstab integral remain OPEN. U-1609 dropped the unprinted `1 ≤ v1`. -/
theorem upper_short_weight (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v1 : ℝ) (b1 : ℝ → ℕ → ℝ),
        v1 < 2.2 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, primeWeight m ≤ b1 x m := by
  obtain ⟨ω, hω, hz, B0, η, hη, hweight⟩ := upper_short_weight_analytic h4 h9
  refine ⟨B0, min η (1/10^8), lt_min hη (by norm_num), ?_⟩
  intro B ε hB hε hεη
  have hεsmall : ε ≤ 1/10^8 :=
    (lt_of_lt_of_le hεη (min_le_right _ _)).le
  obtain ⟨v1, b1, hdensity, hright, X, hsandwich⟩ :=
    hweight B ε hB hε (lt_of_lt_of_le hεη (min_le_left _ _))
  exact ⟨v1, b1, upper_density_bound hω hz hε.le hεsmall hdensity,
    hright, X, hsandwich⟩

/-- Pages 43 to 53, combine the two short constructions at one common
divisor exponent and epsilon cutoff. This is the exact statement of
DecompC165b.section5_weights. CONDITIONAL on the OPEN leaves above. -/
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
  obtain ⟨v0, b0, hv0, hb0, X0, hs0⟩ := h0 B ε
    (le_trans (le_max_left _ _) hB) hε (lt_of_lt_of_le hεη (min_le_left _ _))
  obtain ⟨v1, b1, hv1, hb1, X1, hs1⟩ := h1 B ε
    (le_trans (le_max_right _ _) hB) hε (lt_of_lt_of_le hεη (min_le_right _ _))
  have hsand : ∀ x : ℝ, max X0 X1 ≤ x → ∀ m ∈ rightInterval ε x,
      b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m := fun x hx m hm =>
    ⟨hs0 x (le_trans (le_max_left _ _) hx) m hm,
      hs1 x (le_trans (le_max_right _ _) hx) m hm⟩
  have hmono : v0 ≤ v1 := right_density_mono hε hb0 hb1
    ⟨max X0 X1, fun x hx m hm => (hsand x hx m hm).1.trans (hsand x hx m hm).2⟩
  exact ⟨v0, v1, b0, b1, hv0, hmono, hv1, hb0, hb1, max X0 X1, hsand⟩

end LeanLab.BHP1997.DecompC165d
